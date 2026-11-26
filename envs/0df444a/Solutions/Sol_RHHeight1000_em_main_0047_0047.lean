-- Prove2me | solution 1 for RHHeight1000.em_main_0047_0047
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-20T08:33:59.611398+00:00
-- url     : https://prove2.me/submissions/7c1aef0b-e887-4fe0-bed3-f354c8d393cc

import Definitions.Def_RHT1000_Support_20261118_S005
/- Copyright (c) 2026 Salvatore Mercuri, Bhavik Mehta.
Apache 2.0 license; see the source project LICENSE. -/
set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable def EMRow47.d0 := @PSigma Zeta.Certificates.ZIntervalEM fun (I : Zeta.Certificates.ZIntervalEM) => Zeta.Certificates.ZIntervalEM.Certificate I

noncomputable def EMRow47.d1 := @NonemptyInterval Real Real.instLE

noncomputable def EMRow47.d2 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @NonemptyInterval.mk Real Real.instLE (@Prod.mk Real Real a b) h

noncomputable def EMRow47.d3 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) (fc sc fb sb : Nat) => Zeta.Certificates.ZIntervalEM.mk (EMRow47.d2 a b h) fc sc fb sb

noncomputable def ep0 := nat_lit 26986075409044028275299783

noncomputable def ep1 := nat_lit 4294967296000000000000000

noncomputable def ep2 := nat_lit 26986075409044045455168967

noncomputable abbrev qz267 := (@instHMul Real Real.instMul)

noncomputable abbrev qz0 := qz267

noncomputable abbrev qz268 := (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 2 1) Real.pi)

noncomputable def ep3 := @BSN.isNear_log_image_fff qz268 884279719003555 140737488355328 1 500000000000000 ep0 ep1 ep2 ep1 4138529546116343 2251799813685248 250000000196463 98231500000000000000 4138529546116343 2251799813685248 250000000196463 98231500000000000000 963576 524288

noncomputable abbrev qz269 := (@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 2 1) Real.pi 2 1 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 140737488355328 1 500000000000000 (Enclosure.Real.IsNear.const Bool.false 2 1) BSN.pi_near_15 rfl)

noncomputable def ep4 := @ep3 2 524288 qz269 rfl rfl rfl rfl

noncomputable def ep5 := nat_lit 53972150818088056550599566

noncomputable def ep6 := nat_lit 34359738368000000000000000

noncomputable def ep7 := nat_lit 9806206225044028275299783

noncomputable def ep8 := nat_lit 44165944593044028275299783

noncomputable def ep9 := nat_lit 13681445815609410487519367394620474863599256634174726093703677122907123617368241606644861540940610176751640793056574796245399519365549113997355475306157239709119582688278313060810592403844863400465080549957745

noncomputable def ep10 := nat_lit 231714499556395493334623298703961145503103241611736774613091488581016477543539392410113701224645713379230392133956226737605624599560350113120270717249177907454870984269546186598262646369758174842349131395304

noncomputable def ep11 := nat_lit 8978369550011295664474073352761810093897501552430546263638635096022803738134167562509900960712119243631997923545019968443113540909076206607473711060286601587364321108377403290080403445693385008949995305

noncomputable def ep12 := BSN.log_dyadic_bound ep7 ep8 5 4 ep9 1048576 392926 ep10 ep11 473518 ep5 ep6 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP ep7) (BSN.artanhQ ep8) 0 4 ep10 ep9 ep11 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz270 := (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))

noncomputable abbrev qz1 := qz270

noncomputable def ep13 := ep4 rfl rfl rfl rfl (BSN.isNear_log_sfrac ep0 ep1 4138529546116343 2251799813685248 250000000196463 98231500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep0) (@Nat.cast Real Real.instNatCast ep1))) Bool.false 69433004117575847641088 37778931862957161709568 1000000000785852 392926000000000000000 4138529546116343 2251799813685248 250000000196463 98231500000000000000 (BSN.log_rat_reduce_isNear ep0 ep1 2 ep5 ep6 473518 1048576 24973259072661432 36028797018963968 392926 1000000000000000 rfl rfl rfl rfl (ep12 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep14 := nat_lit 53972150818088090910337934

noncomputable def ep15 := nat_lit 9806206225044045455168967

noncomputable def ep16 := nat_lit 44165944593044045455168967

noncomputable def ep17 := nat_lit 13681445815609453062485491347592146866046743284321690683909457683007658987562290830600045658905080811372395010565947827677605470036294121079488508864180301737865471494204890974265645509835068840465080549957745

noncomputable def ep18 := nat_lit 231714499556396865510889920206523150079811393376960301632499817942333196803513131357563499488546302200815366867712007119763002650772307103678175657719139104636874731038771518520299266622696414842349131395304

noncomputable def ep19 := nat_lit 8978369550011421500876706511871067098718760264493934208903156435737864998391937547068187824077011975074541700434630537294838404525415248443919841847024664017658842168336182958576672102333385008949995305

noncomputable def ep20 := BSN.log_dyadic_bound ep15 ep16 5 4 ep17 1048576 392926 ep18 ep19 473518 ep14 ep6 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP ep15) (BSN.artanhQ ep16) 0 4 ep18 ep17 ep19 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep21 := ep13 (BSN.isNear_log_sfrac ep2 ep1 4138529546116343 2251799813685248 250000000196463 98231500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep2) (@Nat.cast Real Real.instNatCast ep1))) Bool.false 69433004117575847641088 37778931862957161709568 1000000000785852 392926000000000000000 4138529546116343 2251799813685248 250000000196463 98231500000000000000 (BSN.log_rat_reduce_isNear ep2 ep1 2 ep14 ep6 473518 1048576 24973259072661432 36028797018963968 392926 1000000000000000 rfl rfl rfl rfl (ep20 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable abbrev qz2 := (Real.log (@HMul.hMul Real Real Real qz267 (2 : Real) Real.pi))

theorem EMRow47.d4 : Enclosure.Real.IsNear qz2 Bool.false 120447 65536 1 262144 := @Enclosure.Real.IsNear.of_eq qz2 (Real.log qz268) Bool.false 120447 65536 1 262144 BSN.log_two_pi_eq (@Enclosure.Real.IsNear.recentre' (Real.log qz268) Bool.false 963576 524288 2 524288 120447 65536 1 262144 (ep21 rfl rfl rfl rfl rfl rfl rfl rfl) rfl)

noncomputable def ep22 := nat_lit 8589934592000000000000000

noncomputable def ep23 := @BSN.isNear_log_image_fff Real.pi 226375608064910080 72057594037927936 1 1000000000000000 ep0 ep22 ep2 ep22 1200336 1048576 1 392926 1200336 1048576 1 392926 600168 524288 2 524288 BSN.pi_near_15 rfl rfl rfl

noncomputable def ep24 := nat_lit 17179869184000000000000000

noncomputable def ep25 := nat_lit 18396140817044028275299783

noncomputable def ep26 := nat_lit 35576010001044028275299783

noncomputable def ep27 := nat_lit 145019262663961446558303139663424756232419223153299357158415217874016130572233056993847515999529612750616182853355499335896178729185698845314776375864537073527142908641610750276034469165612529925303649396973267518946591078603565291376312767403717761600170009932259137778521478520425507632472584532570900560707662248426541531715360699177249902784721815296292248142738824858695953661559845440650653128788875447728828657762006237171740033404723254477174341920697506370253193455781322964835857351124092897592956162654178130575

noncomputable def ep28 := nat_lit 15500762873619990602332184736899274490522931101512051618692838888825382235673431503644115344741331161500627469184702974962114537943617674254904297224139410345221262767191485292268260077615645253784097850065864022184521411511133693085443040736512010941548648374196772723338837137976260321103066698629790037694560548409922339907589559883712609967105556007429010014773911317423638534096849366294542840133852248768895750397896505791271178551667935288585787166713880920071720072716082683081155281219708172458141800988558163320

noncomputable def ep29 := nat_lit 12900190794487083783367107939442176642390171280542213571554777169279725287102813254708993369099729304728646904879886535518616983985412662170766446331701281703998252143668221340329975389245922410714088123244705567402747658401492589451585970559635763980329972215329212888079422466283203384882259392047898400615815810081169907384366653346471604103896809335921621947903075223769953790093549808584241881353287841076643853121427928248525828402335494512605306631304432120211393210317325496757155861061354331245840675149075

noncomputable def ep30 := BSN.log_dyadic_bound ep25 ep26 11 10 ep27 1048576 392926 ep28 ep29 1200336 ep5 ep24 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base10 (BSN.artanhP ep25) (BSN.artanhQ ep26) 0 10 ep28 ep27 ep29 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep31 := nat_lit 18396140817044045455168967

noncomputable def ep32 := nat_lit 35576010001044045455168967

noncomputable def ep33 := nat_lit 145019262663962847171784895425483977818796535899227200426399035286881207006285364467913811844950531107314785650583974625982406238691319033447632878979985852280879486690814033867010958364699188952871572448188560932645032521756218245629809291975913196623825614492380080480004685076434733043183791438169545293975334857826316990371107134320667652578346815517853870648072772035977941843998949310557583393428557296298890786965786350523173236912472938174255438182435383147950274229549088258679583524155427309880956162654178130575

noncomputable def ep34 := nat_lit 15500762873620157189619721156942591192100275120160672416764593300158228469749443299607348495591439275767946573253526107895503597951484257520435868240203420954375895980141891044871083424251900562230440202302413072793440172565998181227591194192658878334739610458454844032013325963992941389843551995646587189684848765634635122388286241104146031552341815777883628509454807838726994150833304950745987647656768534710890974432620160470644835720379148964170536679305861738540146791997074363921127776563807649880221800988558163320

noncomputable def ep35 := nat_lit 12900190794487324729109480814509220959173684627296055849229843377126536688487849343376525559792931631054411655715865486295286288812423905434305314401904993536755333953308594664509631000767632482919425633906965368325056855874260596615770736441041599390097968820060635361729170158825410327022636428624381203910573184452046894301676992229743752846881064485858738985580654099214803581683226335297196686880535448467637789069028262446657986458573827723305156755787640135484017403116612632808333639900906331245840675149075

noncomputable def ep36 := BSN.log_dyadic_bound ep31 ep32 11 10 ep33 1048576 392926 ep34 ep35 1200336 ep14 ep24 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base10 (BSN.artanhP ep31) (BSN.artanhQ ep32) 0 10 ep34 ep33 ep35 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep37 := @Enclosure.Real.IsNear.recentre' (Real.log Real.pi) Bool.false 600168 524288 2 524288 75021 65536 1 262144 (ep23 rfl rfl rfl rfl rfl (BSN.isNear_log_sfrac ep0 ep22 1200336 1048576 1 392926 Bool.false (BSN.logfrac_isNear ep5 ep24 1 ep0 ep22 1200336 1048576 392926 rfl rfl rfl (ep30 rfl))) (BSN.isNear_log_sfrac ep2 ep22 1200336 1048576 1 392926 Bool.false (BSN.logfrac_isNear ep14 ep24 1 ep2 ep22 1200336 1048576 392926 rfl rfl rfl (ep36 rfl))) rfl rfl rfl rfl rfl rfl rfl rfl) rfl

theorem EMRow47.d5 : Enclosure.Real.IsNear (Real.log Real.pi) Bool.false 75021 65536 1 262144 := ep37

noncomputable abbrev qz712 := (@HAdd.hAdd Complex Complex Complex (@instHAdd Complex Complex.instAdd) (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (2 : Complex)) (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul) Complex.I ↑(Enclosure.sfrac Bool.false 136442 1000)))

noncomputable abbrev qz533 := qz712

noncomputable abbrev qz271 := qz533

noncomputable abbrev qz3 := (BSN.headSumC qz271 9)

noncomputable abbrev qz713 := (@instHAdd Complex Complex.instAdd)

noncomputable abbrev qz534 := qz713

noncomputable abbrev qz272 := qz534

noncomputable abbrev qz4 := qz272

noncomputable abbrev qz5 := qz271

noncomputable abbrev qz535 := (@instHPow Complex Complex Complex.instPow)

noncomputable abbrev qz273 := qz535

noncomputable abbrev qz6 := qz273

noncomputable abbrev qz536 := (@Neg.neg Complex Complex.instNeg qz712)

noncomputable abbrev qz274 := qz536

noncomputable abbrev qz7 := qz274

noncomputable abbrev qz537 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 8) qz7)

noncomputable def ep38 := @Enclosure.Complex.IsNear.of_eq qz3 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 8) qz537) Bool.false 3712078734803 1099511627776 511165889282155 216013352927756288 Bool.true 427701602855 1099511627776 511092725282177 216013352927756288

noncomputable def ep39 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 8) qz537 Bool.false 873871946853 274877906944 114391535592323 54003338231939072 Bool.true 104896257783 1099511627776 457436691130425 216013352927756288 Bool.false

noncomputable abbrev qz538 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 7) qz7)

noncomputable def ep40 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 8) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 7) qz538) Bool.false 873871946853 274877906944 114391535592323 54003338231939072 Bool.true 104896257783 1099511627776 457436691130425 216013352927756288

noncomputable def ep41 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 7) qz538 Bool.false 877930314853 274877906944 50037779876037 27001669115969536 Bool.false 77590792273 274877906944 99993746468521 54003338231939072 Bool.true

noncomputable abbrev qz539 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 6) qz7)

noncomputable def ep42 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 7) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 6) qz539) Bool.false 877930314853 274877906944 50037779876037 27001669115969536 Bool.false 77590792273 274877906944 99993746468521 54003338231939072

noncomputable def ep43 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 6) qz539 Bool.false 3134569533805 1099511627776 338285901048737 216013352927756288 Bool.false 66963014719 1099511627776 338020031993023 216013352927756288 Bool.false

noncomputable def ep44 := nat_lit 3861178358231672880627712

noncomputable abbrev qz540 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 5) qz7)

noncomputable def ep45 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 6) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 5) qz540) Bool.false 3134569533805 1099511627776 338285901048737 216013352927756288 Bool.false 66963014719 1099511627776 338020031993023 216013352927756288

noncomputable def ep46 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 5) qz540 Bool.false 1333662463719 549755813888 135218206761545 108006676463878144 Bool.true 86226510819 1099511627776 270302119078347 216013352927756288 Bool.false

noncomputable def ep47 := nat_lit 1723247825245496504483840

noncomputable abbrev qz541 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 4) qz7)

noncomputable def ep48 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 5) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 4) qz541) Bool.false 1333662463719 549755813888 135218206761545 108006676463878144 Bool.true 86226510819 1099511627776 270302119078347 216013352927756288

noncomputable def ep49 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 4) qz541 Bool.false 2230703432421 1099511627776 194633717143193 216013352927756288 Bool.false 30978327655 137438953472 1519827012039 1687604319748096 Bool.false

noncomputable def ep50 := nat_lit 2932754772774856465317888

noncomputable abbrev qz542 := (@Nat.cast Complex Complex.instNatCast 3)

noncomputable abbrev qz275 := qz542

noncomputable abbrev qz8 := qz275

noncomputable def ep51 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 4) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 3) (@HPow.hPow Complex Complex Complex qz6 qz8 qz7)) Bool.false 2230703432421 1099511627776 194633717143193 216013352927756288 Bool.false 30978327655 137438953472 1519827012039 1687604319748096

noncomputable def ep52 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 3) (@HPow.hPow Complex Complex Complex qz6 qz8 qz7) Bool.false 1835931406871 1099511627776 107165062309735 216013352927756288 Bool.true 124646741505 549755813888 53517994336377 108006676463878144 Bool.false

noncomputable def ep53 := nat_lit 1226342181033362061262848

noncomputable abbrev qz543 := (@Nat.cast Complex Complex.instNatCast 2)

noncomputable abbrev qz276 := qz543

noncomputable abbrev qz9 := qz276

noncomputable def ep54 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 3) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 2) (@HPow.hPow Complex Complex Complex qz6 qz9 qz7)) Bool.false 1835931406871 1099511627776 107165062309735 216013352927756288 Bool.true 124646741505 549755813888 53517994336377 108006676463878144

noncomputable def ep55 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 2) (@HPow.hPow Complex Complex Complex qz6 qz9 qz7) Bool.false 1 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable abbrev qz544 := (Enclosure.sfrac Bool.false 0 1)

noncomputable abbrev qz10 := qz544

noncomputable def ep56 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 2) (Complex.mk (Enclosure.sfrac Bool.false 1 1) qz10) Bool.false 1 1 0 1 Bool.false 0 1 0 1 (BSN.head_sum_c_two qz5)

noncomputable abbrev qz714 := (Enclosure.sfrac Bool.false 136442 1000)

noncomputable abbrev qz545 := qz714

noncomputable abbrev qz277 := qz545

noncomputable abbrev qz278 := (Enclosure.sfrac Bool.false 2 1)

noncomputable abbrev qz11 := (@HMul.hMul Real Real Real qz267 qz277 (Real.log qz278))

noncomputable abbrev qz12 := qz277

noncomputable abbrev qz279 := (@Eq.refl Real qz545)

noncomputable abbrev qz13 := qz279

noncomputable abbrev qz280 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 2)))

noncomputable def ep57 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz9 qz7) (Complex.mk (@HMul.hMul Real Real Real qz0 qz280 (Real.cos qz11)) (@HMul.hMul Real Real Real qz0 qz280 (@Neg.neg Real Real.instNeg (Real.sin qz11)))) Bool.false 736419779095 1099511627776 107165062309735 216013352927756288 Bool.true 124646741505 549755813888 53517994336377 108006676463878144 (BSN.cpow_neg_s_mk qz12 136442 1000 2 qz13 rfl)

noncomputable abbrev qz14 := (@Nat.cast Real Real.instNatCast 1)

noncomputable abbrev qz281 := (Real.sqrt (@Nat.cast Real Real.instNatCast 2))

noncomputable abbrev qz282 := (@Nat.cast Real Real.instNatCast 2)

noncomputable def ep58 := @Enclosure.Real.IsNear.inv_image qz281 1482911 1048576 1 1048576 370727 370728 524288 (@Enclosure.Real.IsNear.of_eq qz281 (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz282 qz14)) Bool.false 1482911 1048576 1 1048576 (BSN.sqrt_natCast_div_one 2) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz282 qz14)) Bool.false 1482911 1048576 1 1048576 1482911 1048576 1 1048576 (BSN.sqrt_enclosure 2 1 741455 741456 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep59 := BSN.log_dyadic_bound 1 3 6 5 613814355 524288 196463 24381081 945 363408 4 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 1) (BSN.artanhQ 3) 0 5 24381081 613814355 945 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep60 := nat_lit 241427238327395654956160053858533376

noncomputable def ep61 := nat_lit 510423550381407695195061911147652317184

noncomputable def ep62 := nat_lit 7656353255721115427925928667214784757760

noncomputable abbrev qz15 := (BSN.cosEvenQ 2147483648)

noncomputable abbrev qz16 := (BSN.cosOddQ 2147483648)

noncomputable def ep63 := BSN.cos_dyadic_bound_f 700965376 2147483648 2 1 1048576 393310 ep60 ep61 ep60 ep60 ep62 ep60 993209 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 700965376) qz15 0 1 ep60 ep61 ep60 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 700965376) qz16 0 1 ep60 ep62 ep60 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz17 := (@Nat.cast Real Real.instNatCast 262144)

noncomputable abbrev qz18 := (Enclosure.Real.IsNear.const Bool.false 136442 1000)

noncomputable abbrev qz283 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 24792057) qz17)

noncomputable abbrev qz284 := (BSN.isNear_log_sfrac 2 1 363408 524288 1 196463 Bool.false (BSN.logfrac_isNear 4 2 1 2 1 363408 524288 196463 rfl rfl rfl (ep59 rfl)))

noncomputable abbrev qz285 := (@Nat.cast Real Real.instNatCast 37778931862957161709568)

noncomputable def ep64 := @Enclosure.Real.IsNear.cos_image qz11 qz283 Bool.false 24792057 262144 729 1048576 Bool.false 993209 1048576 1 196463 (@Enclosure.Real.IsNear.recentre' qz11 Bool.false 1549503573 16384000 68221 98231500 24792057 262144 729 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz12 (Real.log qz278) 136442 1000 0 1 363408 524288 1 196463 1549503573 16384000 68221 98231500 qz18 qz284 rfl) rfl) (Enclosure.sfrac_false_div 24792057 262144) (BSN.cos_reduce0 qz283 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 12331513308271821717504) qz285) 226375608064910080 72057594037927936 Bool.false 993209 1048576 15 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q0 24792057 262144 226375608064910080 72057594037927936 15 12331513308271821717504 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 993209 1048576 12331513308271821717504 37778931862957161709568 700965376 2147483648 393310 392926 (ep63 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep65 := nat_lit 2552117751907038475975309555738261585920

noncomputable def ep66 := nat_lit 17864824263349269331827166890167831101440

noncomputable abbrev qz19 := (BSN.sinEvenQ 2147483648)

noncomputable abbrev qz20 := (BSN.sinOddQ 2147483648)

noncomputable def ep67 := BSN.sin_dyadic_bound_f 700965376 2147483648 2 1 1048576 393310 ep60 ep65 ep60 ep60 ep66 ep60 336222 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 700965376) qz19 0 1 ep60 ep65 ep60 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 700965376) qz20 0 1 ep60 ep66 ep60 rfl rfl rfl rfl) rfl rfl

noncomputable def ep68 := @Enclosure.Real.IsNear.sin_image qz11 qz283 Bool.false 24792057 262144 729 1048576 Bool.false 336222 1048576 1 196463 (@Enclosure.Real.IsNear.recentre' qz11 Bool.false 1549503573 16384000 68221 98231500 24792057 262144 729 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz12 (Real.log qz278) 136442 1000 0 1 363408 524288 1 196463 1549503573 16384000 68221 98231500 qz18 qz284 rfl) rfl) (Enclosure.sfrac_false_div 24792057 262144) (BSN.sin_reduce0 qz283 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 12331513308271821717504) qz285) 226375608064910080 72057594037927936 Bool.false 336222 1048576 15 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q0 24792057 262144 226375608064910080 72057594037927936 15 12331513308271821717504 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 336222 1048576 12331513308271821717504 37778931862957161709568 700965376 2147483648 393310 392926 (ep67 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz286 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 2))) Bool.false 741455 1048576 1 1048576 741455 1048576 1 1048576 (ep58 rfl rfl) rfl)

noncomputable def ep69 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz280 (Real.cos qz11)) (@HMul.hMul Real Real Real qz0 qz280 (@Neg.neg Real Real.instNeg (Real.sin qz11))) Bool.false 736419779095 1099511627776 107165062309735 216013352927756288 Bool.true 124646741505 549755813888 53517994336377 108006676463878144 (@Enclosure.Real.IsNear.mulLit_ff qz280 (Real.cos qz11) 741455 1048576 1 1048576 993209 1048576 144270103 206006386688 736419779095 1099511627776 107165062309735 216013352927756288 qz286 (@Enclosure.Real.IsNear.recentre' (Real.cos qz11) Bool.false 993209 1048576 144270103 206006386688 993209 1048576 144270103 206006386688 (ep64 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz280 (@Neg.neg Real Real.instNeg (Real.sin qz11)) 741455 1048576 1 1048576 168111 524288 144270103 206006386688 124646741505 549755813888 53517994336377 108006676463878144 qz286 (@Enclosure.Real.IsNear.neg (Real.sin qz11) Bool.false 168111 524288 144270103 206006386688 (@Enclosure.Real.IsNear.recentre' (Real.sin qz11) Bool.false 336222 1048576 144270103 206006386688 168111 524288 144270103 206006386688 (ep68 rfl rfl) rfl)) rfl)

noncomputable abbrev qz546 := (Enclosure.Real.IsNear.const Bool.false 0 1)

noncomputable abbrev qz21 := qz546

noncomputable def ep70 := @ep55 736419779095 1099511627776 107165062309735 216013352927756288 Bool.true 124646741505 549755813888 53517994336377 108006676463878144 Bool.false 1835931406871 1835931406871 1099511627776 107165062309735 216013352927756288 Bool.true 124646741505 124646741505 549755813888 53517994336377 108006676463878144 (ep56 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 1) qz10 Bool.false 1 1 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 1) qz21)) (ep57 ep69) rfl rfl

noncomputable abbrev qz547 := (Real.log (Enclosure.sfrac Bool.false 3 1))

noncomputable abbrev qz22 := (@HMul.hMul Real Real Real qz267 qz277 qz547)

noncomputable abbrev qz287 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 3)))

noncomputable def ep71 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz8 qz7) (Complex.mk (@HMul.hMul Real Real Real qz0 qz287 (Real.cos qz22)) (@HMul.hMul Real Real Real qz0 qz287 (@Neg.neg Real Real.instNeg (Real.sin qz22)))) Bool.false 197386012775 549755813888 43734327416729 108006676463878144 Bool.false 248560052125 549755813888 43750934434119 108006676463878144 (BSN.cpow_neg_s_mk qz12 136442 1000 3 qz13 rfl)

noncomputable abbrev qz288 := (Real.sqrt (@Nat.cast Real Real.instNatCast 3))

noncomputable abbrev qz289 := (@Nat.cast Real Real.instNatCast 3)

noncomputable def ep72 := @Enclosure.Real.IsNear.inv_image qz288 1816187 1048576 1 1048576 302697 302698 524288 (@Enclosure.Real.IsNear.of_eq qz288 (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz289 qz14)) Bool.false 1816187 1048576 1 1048576 (BSN.sqrt_natCast_div_one 3) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz289 qz14)) Bool.false 1816187 1048576 1 1048576 1816187 1048576 1 1048576 (BSN.sqrt_enclosure 3 1 908093 908094 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep73 := BSN.log_dyadic_bound 1 2 10 9 171633298636800 524288 196463 16925142283965 34459425 575989 3 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base9 (BSN.artanhP 1) (BSN.artanhQ 2) 0 9 16925142283965 171633298636800 34459425 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep74 := nat_lit 4315020842981120942940302001135420081

noncomputable def ep75 := BSN.sin_dyadic_bound_f 1441271253 2147483648 2 1 1048576 393310 ep74 ep65 ep74 ep74 ep66 ep74 652090 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1441271253) qz19 0 1 ep74 ep65 ep74 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1441271253) qz20 0 1 ep74 ep66 ep74 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz23 := (@Nat.cast Real Real.instNatCast 524288)

noncomputable abbrev qz24 := (@Nat.cast Real Real.instNatCast 75557863725914323419136)

noncomputable abbrev qz290 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 78589091) qz23)

noncomputable abbrev qz291 := (BSN.isNear_log_sfrac 3 1 575989 524288 1 196463 Bool.false (BSN.logfrac_isNear 3 1 2 3 1 575989 524288 196463 rfl rfl rfl (ep73 rfl)))

noncomputable def ep76 := @Enclosure.Real.IsNear.cos_image qz22 qz290 Bool.false 78589091 524288 729 1048576 Bool.false 652090 1048576 1 196463 (@Enclosure.Real.IsNear.recentre' qz22 Bool.false 39294545569 262144000 68221 98231500 78589091 524288 729 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz12 qz547 136442 1000 0 1 575989 524288 1 196463 39294545569 262144000 68221 98231500 qz18 qz291 rfl) rfl) (Enclosure.sfrac_false_div 78589091 524288) (BSN.cos_reduce3 qz290 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 50710224067672305303552) qz24) 226375608064910080 72057594037927936 Bool.false 652090 1048576 23 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q3 78589091 524288 226375608064910080 72057594037927936 23 50710224067672305303552 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 652090 1048576 50710224067672305303552 75557863725914323419136 1441271253 2147483648 393310 392926 (ep75 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep77 := nat_lit 154192797509969255741650903349098866367004262957124852118673521648342986079841

noncomputable def ep78 := nat_lit 18237254054877300779212430138868345486890022584838388836214569481246317918289920

noncomputable def ep79 := nat_lit 18619404875361503599582790098023357963001761096212148151298102760338046561

noncomputable def ep80 := nat_lit 462541153720157044217753544467100552385086785349182132059717968739508282146401

noncomputable def ep81 := nat_lit 820676432469478535064559356249075546910051016317727497629655626656084306323046400

noncomputable def ep82 := BSN.cos_dyadic_bound_f 1441271253 2147483648 3 2 1048576 393310 ep77 ep78 ep79 ep80 ep81 ep79 821150 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1441271253) qz15 0 2 ep77 ep78 ep79 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1441271253) qz16 0 2 ep80 ep81 ep79 rfl rfl rfl rfl) rfl rfl

noncomputable def ep83 := @Enclosure.Real.IsNear.sin_image qz22 qz290 Bool.false 78589091 524288 729 1048576 Bool.true 821150 1048576 1 196463 (@Enclosure.Real.IsNear.recentre' qz22 Bool.false 39294545569 262144000 68221 98231500 78589091 524288 729 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz12 qz547 136442 1000 0 1 575989 524288 1 196463 39294545569 262144000 68221 98231500 qz18 qz291 rfl) rfl) (Enclosure.sfrac_false_div 78589091 524288) (BSN.sin_reduce3 qz290 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 50710224067672305303552) qz24) 226375608064910080 72057594037927936 Bool.false 821150 1048576 23 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q3 78589091 524288 226375608064910080 72057594037927936 23 50710224067672305303552 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 821150 1048576 50710224067672305303552 75557863725914323419136 1441271253 2147483648 393310 392926 (ep82 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz292 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 3))) Bool.false 605395 1048576 1 1048576 605395 1048576 1 1048576 (ep72 rfl rfl) rfl)

noncomputable def ep84 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz287 (Real.cos qz22)) (@HMul.hMul Real Real Real qz0 qz287 (@Neg.neg Real Real.instNeg (Real.sin qz22))) Bool.false 197386012775 549755813888 43734327416729 108006676463878144 Bool.false 248560052125 549755813888 43750934434119 108006676463878144 (@Enclosure.Real.IsNear.mulLit_ff qz287 (Real.cos qz22) 605395 1048576 1 1048576 326045 524288 144270103 206006386688 197386012775 549755813888 43734327416729 108006676463878144 qz292 (@Enclosure.Real.IsNear.recentre' (Real.cos qz22) Bool.false 652090 1048576 144270103 206006386688 326045 524288 144270103 206006386688 (ep76 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz287 (@Neg.neg Real Real.instNeg (Real.sin qz22)) 605395 1048576 1 1048576 410575 524288 144270103 206006386688 248560052125 549755813888 43750934434119 108006676463878144 qz292 (@Enclosure.Real.IsNear.neg (Real.sin qz22) Bool.true 410575 524288 144270103 206006386688 (@Enclosure.Real.IsNear.recentre' (Real.sin qz22) Bool.true 821150 1048576 144270103 206006386688 410575 524288 144270103 206006386688 (ep83 rfl rfl) rfl)) rfl)

noncomputable def ep85 := @ep52 197386012775 549755813888 43734327416729 108006676463878144 Bool.false 248560052125 549755813888 43750934434119 108006676463878144 Bool.false ep53 2230703432421 1099511627776 194633717143193 216013352927756288 Bool.false 68122062931454653890560 30978327655 137438953472 1519827012039 1687604319748096 (ep54 (BSN.head_sum_c_succ qz5 2 3 rfl rfl) (ep70 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep71 ep84) rfl rfl

noncomputable abbrev qz548 := (Real.log (Enclosure.sfrac Bool.false 4 1))

noncomputable abbrev qz25 := (@HMul.hMul Real Real Real qz267 qz277 qz548)

noncomputable abbrev qz293 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 4)))

noncomputable def ep86 := @Enclosure.Complex.IsNear.of_eq qz541 (Complex.mk (@HMul.hMul Real Real Real qz0 qz293 (Real.cos qz25)) (@HMul.hMul Real Real Real qz0 qz293 (@Neg.neg Real Real.instNeg (Real.sin qz25)))) Bool.false 436621495017 1099511627776 75802696379897 216013352927756288 Bool.true 334053132059 1099511627776 75764261537355 216013352927756288 (BSN.cpow_neg_s_mk qz12 136442 1000 4 qz13 rfl)

noncomputable abbrev qz294 := (Real.sqrt (@Nat.cast Real Real.instNatCast 4))

noncomputable abbrev qz295 := (@Nat.cast Real Real.instNatCast 4)

noncomputable def ep87 := @Enclosure.Real.IsNear.inv_image qz294 2097153 1048576 1 1048576 262143 262144 524288 (@Enclosure.Real.IsNear.of_eq qz294 (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz295 qz14)) Bool.false 2097153 1048576 1 1048576 (BSN.sqrt_natCast_div_one 4) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz295 qz14)) Bool.false 2097153 1048576 1 1048576 2097153 1048576 1 1048576 (BSN.sqrt_enclosure 4 1 1048576 1048577 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep88 := nat_lit 318077276165597140789031982421875

noncomputable def ep89 := nat_lit 49379992292270016474244603430625

noncomputable def ep90 := nat_lit 20095619060363156210525625

noncomputable def ep91 := BSN.log_dyadic_bound 3 5 14 13 ep88 524288 196463 ep89 ep90 726817 8 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base13 (BSN.artanhP 3) (BSN.artanhQ 5) 0 13 ep89 ep88 ep90 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep92 := nat_lit 138253845932458374874815337210966712694435648564332196224362550603886798831616

noncomputable def ep93 := nat_lit 14969348644931008899452658144144147519195055637041654323787504687394062336

noncomputable def ep94 := nat_lit 414731599100085262606647106316611849788268555581722505364440076802285608370176

noncomputable def ep95 := BSN.cos_dyadic_bound_f 1402491904 2147483648 3 2 1048576 393310 ep92 ep78 ep93 ep94 ep81 ep93 832791 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1402491904) qz15 0 2 ep92 ep78 ep93 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1402491904) qz16 0 2 ep94 ep81 ep93 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz296 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 99168365) qz23)

noncomputable abbrev qz297 := (BSN.isNear_log_sfrac 4 1 726817 524288 1 196463 Bool.false (BSN.logfrac_isNear 8 2 1 4 1 726817 524288 196463 rfl rfl rfl (ep91 rfl)))

noncomputable def ep96 := @Enclosure.Real.IsNear.cos_image qz25 qz296 Bool.false 99168365 524288 729 1048576 Bool.false 832791 1048576 1 196463 (@Enclosure.Real.IsNear.recentre' qz25 Bool.false 49584182557 262144000 68221 98231500 99168365 524288 729 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz12 qz548 136442 1000 0 1 726817 524288 1 196463 49584182557 262144000 68221 98231500 qz18 qz297 rfl) rfl) (Enclosure.sfrac_false_div 99168365 524288) (BSN.cos_reduce0 qz296 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 49345797013853679124480) qz24) 226375608064910080 72057594037927936 Bool.false 832791 1048576 30 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q0 99168365 524288 226375608064910080 72057594037927936 30 49345797013853679124480 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 832791 1048576 49345797013853679124480 75557863725914323419136 1402491904 2147483648 393310 392926 (ep95 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep97 := nat_lit 3869024249721240620212570566380486656

noncomputable def ep98 := BSN.sin_dyadic_bound_f 1402491904 2147483648 2 1 1048576 393310 ep97 ep65 ep97 ep97 ep66 ep97 637157 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1402491904) qz19 0 1 ep97 ep65 ep97 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1402491904) qz20 0 1 ep97 ep66 ep97 rfl rfl rfl rfl) rfl rfl

noncomputable def ep99 := @Enclosure.Real.IsNear.sin_image qz25 qz296 Bool.false 99168365 524288 729 1048576 Bool.false 637157 1048576 1 196463 (@Enclosure.Real.IsNear.recentre' qz25 Bool.false 49584182557 262144000 68221 98231500 99168365 524288 729 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz12 qz548 136442 1000 0 1 726817 524288 1 196463 49584182557 262144000 68221 98231500 qz18 qz297 rfl) rfl) (Enclosure.sfrac_false_div 99168365 524288) (BSN.sin_reduce0 qz296 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 49345797013853679124480) qz24) 226375608064910080 72057594037927936 Bool.false 637157 1048576 30 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q0 99168365 524288 226375608064910080 72057594037927936 30 49345797013853679124480 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 637157 1048576 49345797013853679124480 75557863725914323419136 1402491904 2147483648 393310 392926 (ep98 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz298 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 4))) Bool.false 524287 1048576 1 1048576 524287 1048576 1 1048576 (ep87 rfl rfl) rfl)

noncomputable def ep100 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz293 (Real.cos qz25)) (@HMul.hMul Real Real Real qz0 qz293 (@Neg.neg Real Real.instNeg (Real.sin qz25))) Bool.false 436621495017 1099511627776 75802696379897 216013352927756288 Bool.true 334053132059 1099511627776 75764261537355 216013352927756288 (@Enclosure.Real.IsNear.mulLit_ff qz293 (Real.cos qz25) 524287 1048576 1 1048576 832791 1048576 144270103 206006386688 436621495017 1099511627776 75802696379897 216013352927756288 qz298 (@Enclosure.Real.IsNear.recentre' (Real.cos qz25) Bool.false 832791 1048576 144270103 206006386688 832791 1048576 144270103 206006386688 (ep96 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz293 (@Neg.neg Real Real.instNeg (Real.sin qz25)) 524287 1048576 1 1048576 637157 1048576 144270103 206006386688 334053132059 1099511627776 75764261537355 216013352927756288 qz298 (@Enclosure.Real.IsNear.neg (Real.sin qz25) Bool.false 637157 1048576 144270103 206006386688 (@Enclosure.Real.IsNear.recentre' (Real.sin qz25) Bool.false 637157 1048576 144270103 206006386688 637157 1048576 144270103 206006386688 (ep99 rfl rfl) rfl)) rfl)

noncomputable def ep101 := @ep49 436621495017 1099511627776 75802696379897 216013352927756288 Bool.true 334053132059 1099511627776 75764261537355 216013352927756288 Bool.false ep50 1333662463719 549755813888 135218206761545 108006676463878144 Bool.true 11850881408505445613568 86226510819 1099511627776 270302119078347 216013352927756288 (ep51 (BSN.head_sum_c_succ qz5 3 4 rfl rfl) (ep85 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep86 ep100) rfl rfl

noncomputable abbrev qz549 := (Real.log (Enclosure.sfrac Bool.false 5 1))

noncomputable abbrev qz26 := (@HMul.hMul Real Real Real qz267 qz277 qz549)

noncomputable abbrev qz299 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 5)))

noncomputable def ep102 := @Enclosure.Complex.IsNear.of_eq qz540 (Complex.mk (@HMul.hMul Real Real Real qz0 qz299 (Real.cos qz26)) (@HMul.hMul Real Real Real qz0 qz299 (@Neg.neg Real Real.instNeg (Real.sin qz26)))) Bool.false 467244606367 1099511627776 67849487525647 216013352927756288 Bool.false 76594762769 549755813888 16929478228669 54003338231939072 (BSN.cpow_neg_s_mk qz12 136442 1000 5 qz13 rfl)

noncomputable abbrev qz300 := (Real.sqrt (@Nat.cast Real Real.instNatCast 5))

noncomputable abbrev qz301 := (@Nat.cast Real Real.instNatCast 5)

noncomputable def ep103 := @Enclosure.Real.IsNear.inv_image qz300 2344687 1048576 1 1048576 234468 234469 524288 (@Enclosure.Real.IsNear.of_eq qz300 (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz301 qz14)) Bool.false 2344687 1048576 1 1048576 (BSN.sqrt_natCast_div_one 5) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz301 qz14)) Bool.false 2344687 1048576 1 1048576 2344687 1048576 1 1048576 (BSN.sqrt_enclosure 5 1 1172343 1172344 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep104 := nat_lit 3696382175741467532940033205863946875

noncomputable def ep105 := nat_lit 765440954430599474856563326857688500

noncomputable def ep106 := nat_lit 108794268166472120024432640000

noncomputable def ep107 := BSN.log_dyadic_bound 2 3 18 17 ep104 524288 196463 ep105 ep106 843808 5 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_rec (BSN.artanhP 2) (BSN.artanhQ 3) 0 17 8 307084260767580 1483365253795425 132843110400 1663129201793174588340 2491889415829100854875 818968088287641600 ep105 ep104 ep106 rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.artanhP 2) (BSN.artanhQ 3) 0 8 307084260767580 1483365253795425 132843110400 rfl rfl rfl rfl) (@BSN.binarySplit_of_base9 (BSN.artanhP 2) (BSN.artanhQ 3) 8 17 1663129201793174588340 2491889415829100854875 818968088287641600 rfl rfl rfl rfl)) rfl rfl

noncomputable def ep108 := nat_lit 3384859505521550207687678558621497185584373502503074039535490538403380631668545

noncomputable def ep109 := nat_lit 164135286493895707012911871249815109382010203263545499525931125331216861264609280

noncomputable def ep110 := nat_lit 2765469409712732092303958860175275117076961588090998341476971082251463001921

noncomputable def ep111 := nat_lit 8860630802083572787223046958235065993007615521127332296706750599780446904747841

noncomputable def ep112 := nat_lit 3009146919054754628570050972913277005336853726498334157975403964405642456517836800

noncomputable def ep113 := BSN.sin_dyadic_bound_f 2692905463 2147483648 3 2 1048576 393310 ep108 ep109 ep110 ep111 ep112 ep110 996391 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2692905463) qz19 0 2 ep108 ep109 ep110 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2692905463) qz20 0 2 ep111 ep112 ep110 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz302 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 115130851) qz23)

noncomputable abbrev qz303 := (BSN.isNear_log_sfrac 5 1 843808 524288 1 196463 Bool.false (BSN.logfrac_isNear 5 1 2 5 1 843808 524288 196463 rfl rfl rfl (ep107 rfl rfl)))

noncomputable def ep114 := @Enclosure.Real.IsNear.cos_image qz26 qz302 Bool.false 115130851 524288 729 1048576 Bool.false 996391 1048576 1 196463 (@Enclosure.Real.IsNear.recentre' qz26 Bool.false 1798919549 8192000 68221 98231500 115130851 524288 729 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz12 qz549 136442 1000 0 1 843808 524288 1 196463 1798919549 8192000 68221 98231500 qz18 qz303 rfl) rfl) (Enclosure.sfrac_false_div 115130851 524288) (BSN.cos_reduce3 qz302 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 94748187840494029504512) qz24) 226375608064910080 72057594037927936 Bool.false 996391 1048576 34 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q3 115130851 524288 226375608064910080 72057594037927936 34 94748187840494029504512 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 996391 1048576 94748187840494029504512 75557863725914323419136 2692905463 2147483648 393310 392926 (ep113 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep115 := nat_lit 1881706600582955774089734292060909669821130595429748243449262286260656556705601

noncomputable def ep116 := nat_lit 5639588862929441858084594958462378459229237863113062733664832916617466744112961

noncomputable def ep117 := BSN.cos_dyadic_bound_f 2692905463 2147483648 3 2 1048576 393310 ep115 ep78 ep110 ep116 ep81 ep110 326674 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2692905463) qz15 0 2 ep115 ep78 ep110 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2692905463) qz16 0 2 ep116 ep81 ep110 rfl rfl rfl rfl) rfl rfl

noncomputable def ep118 := @Enclosure.Real.IsNear.sin_image qz26 qz302 Bool.false 115130851 524288 729 1048576 Bool.true 326674 1048576 1 196463 (@Enclosure.Real.IsNear.recentre' qz26 Bool.false 1798919549 8192000 68221 98231500 115130851 524288 729 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz12 qz549 136442 1000 0 1 843808 524288 1 196463 1798919549 8192000 68221 98231500 qz18 qz303 rfl) rfl) (Enclosure.sfrac_false_div 115130851 524288) (BSN.sin_reduce3 qz302 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 94748187840494029504512) qz24) 226375608064910080 72057594037927936 Bool.false 326674 1048576 34 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q3 115130851 524288 226375608064910080 72057594037927936 34 94748187840494029504512 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 326674 1048576 94748187840494029504512 75557863725914323419136 2692905463 2147483648 393310 392926 (ep117 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz304 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 5))) Bool.false 468937 1048576 1 1048576 468937 1048576 1 1048576 (ep103 rfl rfl) rfl)

noncomputable def ep119 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz299 (Real.cos qz26)) (@HMul.hMul Real Real Real qz0 qz299 (@Neg.neg Real Real.instNeg (Real.sin qz26))) Bool.false 467244606367 1099511627776 67849487525647 216013352927756288 Bool.false 76594762769 549755813888 16929478228669 54003338231939072 (@Enclosure.Real.IsNear.mulLit_ff qz299 (Real.cos qz26) 468937 1048576 1 1048576 996391 1048576 144270103 206006386688 467244606367 1099511627776 67849487525647 216013352927756288 qz304 (@Enclosure.Real.IsNear.recentre' (Real.cos qz26) Bool.false 996391 1048576 144270103 206006386688 996391 1048576 144270103 206006386688 (ep114 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz299 (@Neg.neg Real Real.instNeg (Real.sin qz26)) 468937 1048576 1 1048576 163337 524288 144270103 206006386688 76594762769 549755813888 16929478228669 54003338231939072 qz304 (@Enclosure.Real.IsNear.neg (Real.sin qz26) Bool.true 163337 524288 144270103 206006386688 (@Enclosure.Real.IsNear.recentre' (Real.sin qz26) Bool.true 326674 1048576 144270103 206006386688 163337 524288 144270103 206006386688 (ep118 rfl rfl) rfl)) rfl)

noncomputable def ep120 := @ep46 467244606367 1099511627776 67849487525647 216013352927756288 Bool.false 76594762769 549755813888 16929478228669 54003338231939072 Bool.false ep47 3134569533805 1099511627776 338285901048737 216013352927756288 Bool.false 36813306657237968617472 66963014719 1099511627776 338020031993023 216013352927756288 (ep48 (BSN.head_sum_c_succ qz5 4 5 rfl rfl) (ep101 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep102 ep119) rfl rfl

noncomputable abbrev qz550 := (Real.log (Enclosure.sfrac Bool.false 6 1))

noncomputable abbrev qz27 := (@HMul.hMul Real Real Real qz267 qz277 qz550)

noncomputable abbrev qz305 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 6)))

noncomputable def ep121 := @Enclosure.Complex.IsNear.of_eq qz539 (Complex.mk (@HMul.hMul Real Real Real qz0 qz305 (Real.cos qz27)) (@HMul.hMul Real Real Real qz0 qz305 (@Neg.neg Real Real.instNeg (Real.sin qz27)))) Bool.false 377151725607 1099511627776 62016337959559 216013352927756288 Bool.false 243400154373 1099511627776 61954953881061 216013352927756288 (BSN.cpow_neg_s_mk qz12 136442 1000 6 qz13 rfl)

noncomputable abbrev qz306 := (Real.sqrt (@Nat.cast Real Real.instNatCast 6))

noncomputable abbrev qz307 := (@Nat.cast Real Real.instNatCast 6)

noncomputable abbrev qz551 := (@HDiv.hDiv Real Real Real qz1 qz307 qz14)

noncomputable def ep122 := @Enclosure.Real.IsNear.inv_image qz306 2568477 1048576 1 1048576 214039 214040 524288 (@Enclosure.Real.IsNear.of_eq qz306 (Real.sqrt qz551) Bool.false 2568477 1048576 1 1048576 (BSN.sqrt_natCast_div_one 6) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz551) Bool.false 2568477 1048576 1 1048576 2568477 1048576 1 1048576 (BSN.sqrt_enclosure 6 1 1284238 1284239 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep123 := BSN.log_dyadic_bound 2 10 4 3 105000000 524288 196463 1434560 960 212580 12 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 2) (BSN.artanhQ 10) 0 3 1434560 105000000 960 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep124 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz550 136442 1000 0 1 4034681531866359 2251799813685248 500000000196463 98231500000000000000 275250008785454877339 1125899906842624000 34110500013402902323 49115750000000000000000 qz18 (BSN.isNear_log_sfrac 6 1 4034681531866359 2251799813685248 500000000196463 98231500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz551) Bool.false 33845361775666394038272 18889465931478580854784 1000000000392926 196463000000000000000 4034681531866359 2251799813685248 500000000196463 98231500000000000000 (BSN.log_rat_reduce_isNear 6 1 2 12 8 212580 524288 24973259072661432 36028797018963968 196463 1000000000000000 rfl rfl rfl rfl (ep123 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep125 := nat_lit 1355623625989327179279200175746651030373767045559460747695503410633656874700385

noncomputable def ep126 := nat_lit 444008438234424883379085756939605081033210607996477823917129332557792546401

noncomputable def ep127 := nat_lit 3549723959167286876872434321444279052276288492623736232249500247025912531521121

noncomputable def ep128 := BSN.sin_dyadic_bound_f 2142515157 2147483648 3 2 1048576 393310 ep125 ep109 ep126 ep127 ep112 ep126 881033 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2142515157) qz19 0 2 ep125 ep109 ep126 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2142515157) qz20 0 2 ep127 ep112 ep126 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz308 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 128173273) qz23)

noncomputable def ep129 := @Enclosure.Real.IsNear.cos_image qz27 qz308 Bool.false 128173273 524288 365 524288 Bool.false 881033 1048576 1 196463 (@Enclosure.Real.IsNear.recentre' qz27 Bool.false 275250008785454877339 1125899906842624000 34110500013402902323 49115750000000000000000 128173273 524288 365 524288 (ep124 rfl) rfl) (Enclosure.sfrac_false_div 128173273 524288) (BSN.cos_reduce3 qz308 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 75383050517005106937856) qz24) 226375608064910080 72057594037927936 Bool.false 881033 1048576 38 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q3 128173273 524288 226375608064910080 72057594037927936 38 75383050517005106937856 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 881033 1048576 75383050517005106937856 75557863725914323419136 2142515157 2147483648 393310 392926 (ep128 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep130 := nat_lit 753321573744397066214390802417890396910329785581032183308131730055390615965281

noncomputable def ep131 := nat_lit 2259076704356722348876414235739791980568922935527103594276560931501056262803041

noncomputable def ep132 := BSN.cos_dyadic_bound_f 2142515157 2147483648 3 2 1048576 393310 ep130 ep78 ep126 ep131 ep81 ep126 568587 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2142515157) qz15 0 2 ep130 ep78 ep126 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2142515157) qz16 0 2 ep131 ep81 ep126 rfl rfl rfl rfl) rfl rfl

noncomputable def ep133 := @Enclosure.Real.IsNear.sin_image qz27 qz308 Bool.false 128173273 524288 365 524288 Bool.true 568587 1048576 1 196463 (@Enclosure.Real.IsNear.recentre' qz27 Bool.false 275250008785454877339 1125899906842624000 34110500013402902323 49115750000000000000000 128173273 524288 365 524288 (ep124 rfl) rfl) (Enclosure.sfrac_false_div 128173273 524288) (BSN.sin_reduce3 qz308 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 75383050517005106937856) qz24) 226375608064910080 72057594037927936 Bool.false 568587 1048576 38 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q3 128173273 524288 226375608064910080 72057594037927936 38 75383050517005106937856 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 568587 1048576 75383050517005106937856 75557863725914323419136 2142515157 2147483648 393310 392926 (ep132 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz309 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 6))) Bool.false 428079 1048576 1 1048576 428079 1048576 1 1048576 (ep122 rfl rfl) rfl)

noncomputable def ep134 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz305 (Real.cos qz27)) (@HMul.hMul Real Real Real qz0 qz305 (@Neg.neg Real Real.instNeg (Real.sin qz27))) Bool.false 377151725607 1099511627776 62016337959559 216013352927756288 Bool.false 243400154373 1099511627776 61954953881061 216013352927756288 (@Enclosure.Real.IsNear.mulLit_ff qz305 (Real.cos qz27) 428079 1048576 1 1048576 881033 1048576 72233283 103003193344 377151725607 1099511627776 62016337959559 216013352927756288 qz309 (@Enclosure.Real.IsNear.recentre' (Real.cos qz27) Bool.false 881033 1048576 72233283 103003193344 881033 1048576 72233283 103003193344 (ep129 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz305 (@Neg.neg Real Real.instNeg (Real.sin qz27)) 428079 1048576 1 1048576 568587 1048576 72233283 103003193344 243400154373 1099511627776 61954953881061 216013352927756288 qz309 (@Enclosure.Real.IsNear.neg (Real.sin qz27) Bool.true 568587 1048576 72233283 103003193344 (@Enclosure.Real.IsNear.recentre' (Real.sin qz27) Bool.true 568587 1048576 72233283 103003193344 568587 1048576 72233283 103003193344 (ep133 rfl rfl) rfl)) rfl)

noncomputable def ep135 := @ep43 377151725607 1099511627776 62016337959559 216013352927756288 Bool.false 243400154373 1099511627776 61954953881061 216013352927756288 Bool.false ep44 877930314853 274877906944 50037779876037 27001669115969536 Bool.false 341247913250062851899392 77590792273 274877906944 99993746468521 54003338231939072 (ep45 (BSN.head_sum_c_succ qz5 5 6 rfl rfl) (ep120 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep121 ep134) rfl rfl

noncomputable abbrev qz552 := (Real.log (Enclosure.sfrac Bool.false 7 1))

noncomputable abbrev qz28 := (@HMul.hMul Real Real Real qz267 qz277 qz552)

noncomputable abbrev qz310 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 7)))

noncomputable def ep136 := @Enclosure.Complex.IsNear.of_eq qz538 (Complex.mk (@HMul.hMul Real Real Real qz0 qz310 (Real.cos qz28)) (@HMul.hMul Real Real Real qz0 qz310 (@Neg.neg Real Real.instNeg (Real.sin qz28)))) Bool.true 1981625 134217728 14315975840249 54003338231939072 Bool.true 415259426875 1099511627776 57461705256341 216013352927756288 (BSN.cpow_neg_s_mk qz12 136442 1000 7 qz13 rfl)

noncomputable abbrev qz311 := (Real.sqrt (@Nat.cast Real Real.instNatCast 7))

noncomputable abbrev qz312 := (@Nat.cast Real Real.instNatCast 7)

noncomputable abbrev qz553 := (@HDiv.hDiv Real Real Real qz1 qz312 qz14)

noncomputable def ep137 := @Enclosure.Real.IsNear.inv_image qz311 2774271 1048576 1 1048576 198162 198163 524288 (@Enclosure.Real.IsNear.of_eq qz311 (Real.sqrt qz553) Bool.false 2774271 1048576 1 1048576 (BSN.sqrt_natCast_div_one 7) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz553) Bool.false 2774271 1048576 1 1048576 2774271 1048576 1 1048576 (BSN.sqrt_enclosure 7 1 1387135 1387136 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep138 := BSN.log_dyadic_bound 3 11 5 4 202569142545 524288 196463 5259111624 688905 293399 14 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 3) (BSN.artanhQ 11) 0 4 5259111624 202569142545 688905 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep139 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz552 136442 1000 0 1 4381796493761783 2251799813685248 500000000196463 98231500000000000000 298930538600922598043 1125899906842624000 34110500013402902323 49115750000000000000000 qz18 (BSN.isNear_log_sfrac 7 1 4381796493761783 2251799813685248 500000000196463 98231500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz553) Bool.false 36757173121942042968064 18889465931478580854784 1000000000392926 196463000000000000000 4381796493761783 2251799813685248 500000000196463 98231500000000000000 (BSN.log_rat_reduce_isNear 7 1 2 14 8 293399 524288 24973259072661432 36028797018963968 196463 1000000000000000 rfl rfl rfl rfl (ep138 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep140 := BSN.sin_dyadic_bound_f 83909367 2147483648 1 0 1048576 393310 0 1 1 0 1 1 40960 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 83909367) qz19 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 83909367) qz20 0 0 rfl) rfl rfl

noncomputable abbrev qz313 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 139200379) qz23)

noncomputable def ep141 := @Enclosure.Real.IsNear.cos_image qz28 qz313 Bool.false 139200379 524288 365 524288 Bool.true 40960 1048576 1 196463 (@Enclosure.Real.IsNear.recentre' qz28 Bool.false 298930538600922598043 1125899906842624000 34110500013402902323 49115750000000000000000 139200379 524288 365 524288 (ep139 rfl) rfl) (Enclosure.sfrac_false_div 139200379 524288) (BSN.cos_reduce1 qz313 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 2952298423505783881728) qz24) 226375608064910080 72057594037927936 Bool.false 40960 1048576 42 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q1 139200379 524288 226375608064910080 72057594037927936 42 2952298423505783881728 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 40960 1048576 2952298423505783881728 75557863725914323419136 83909367 2147483648 393310 392926 (ep140 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep142 := BSN.cos_dyadic_bound_f 83909367 2147483648 1 0 1048576 393310 0 1 1 0 1 1 1047775 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 83909367) qz15 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 83909367) qz16 0 0 rfl) rfl rfl

noncomputable def ep143 := @Enclosure.Real.IsNear.sin_image qz28 qz313 Bool.false 139200379 524288 365 524288 Bool.false 1047775 1048576 1 196463 (@Enclosure.Real.IsNear.recentre' qz28 Bool.false 298930538600922598043 1125899906842624000 34110500013402902323 49115750000000000000000 139200379 524288 365 524288 (ep139 rfl) rfl) (Enclosure.sfrac_false_div 139200379 524288) (BSN.sin_reduce1 qz313 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 2952298423505783881728) qz24) 226375608064910080 72057594037927936 Bool.false 1047775 1048576 42 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q1 139200379 524288 226375608064910080 72057594037927936 42 2952298423505783881728 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1047775 1048576 2952298423505783881728 75557863725914323419136 83909367 2147483648 393310 392926 (ep142 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz314 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 7))) Bool.false 396325 1048576 1 1048576 396325 1048576 1 1048576 (ep137 rfl rfl) rfl)

noncomputable def ep144 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz310 (Real.cos qz28)) (@HMul.hMul Real Real Real qz0 qz310 (@Neg.neg Real Real.instNeg (Real.sin qz28))) Bool.true 1981625 134217728 14315975840249 54003338231939072 Bool.true 415259426875 1099511627776 57461705256341 216013352927756288 (@Enclosure.Real.IsNear.mulLit_ft qz310 (Real.cos qz28) 396325 1048576 1 1048576 5 128 72233283 103003193344 1981625 134217728 14315975840249 54003338231939072 qz314 (@Enclosure.Real.IsNear.recentre' (Real.cos qz28) Bool.true 40960 1048576 72233283 103003193344 5 128 72233283 103003193344 (ep141 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz310 (@Neg.neg Real Real.instNeg (Real.sin qz28)) 396325 1048576 1 1048576 1047775 1048576 72233283 103003193344 415259426875 1099511627776 57461705256341 216013352927756288 qz314 (@Enclosure.Real.IsNear.neg (Real.sin qz28) Bool.false 1047775 1048576 72233283 103003193344 (@Enclosure.Real.IsNear.recentre' (Real.sin qz28) Bool.false 1047775 1048576 72233283 103003193344 1047775 1048576 72233283 103003193344 (ep143 rfl rfl) rfl)) rfl)

noncomputable def ep145 := @ep41 1981625 134217728 14315975840249 54003338231939072 Bool.true 415259426875 1099511627776 57461705256341 216013352927756288 Bool.false 117289107269546409984 873871946853 274877906944 114391535592323 54003338231939072 Bool.true 28833663785649309745152 104896257783 1099511627776 457436691130425 216013352927756288 (ep42 (BSN.head_sum_c_succ qz5 6 7 rfl rfl) (ep135 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep136 ep144) rfl rfl

noncomputable abbrev qz554 := (Real.log (Enclosure.sfrac Bool.false 8 1))

noncomputable abbrev qz29 := (@HMul.hMul Real Real Real qz267 qz277 qz554)

noncomputable abbrev qz315 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 8)))

noncomputable def ep146 := @Enclosure.Complex.IsNear.of_eq qz537 (Complex.mk (@HMul.hMul Real Real Real qz0 qz315 (Real.cos qz29)) (@HMul.hMul Real Real Real qz0 qz315 (@Neg.neg Real Real.instNeg (Real.sin qz29)))) Bool.false 216590947391 1099511627776 53599746912863 216013352927756288 Bool.true 20175334067 68719476736 6707004268969 27001669115969536 (BSN.cpow_neg_s_mk qz12 136442 1000 8 qz13 rfl)

noncomputable abbrev qz316 := (Real.sqrt (@Nat.cast Real Real.instNatCast 8))

noncomputable abbrev qz317 := (@Nat.cast Real Real.instNatCast 8)

noncomputable abbrev qz555 := (@HDiv.hDiv Real Real Real qz1 qz317 qz14)

noncomputable def ep147 := @Enclosure.Real.IsNear.inv_image qz316 2965821 1048576 1 1048576 185363 185364 524288 (@Enclosure.Real.IsNear.of_eq qz316 (Real.sqrt qz555) Bool.false 2965821 1048576 1 1048576 (BSN.sqrt_natCast_div_one 8) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz555) Bool.false 2965821 1048576 1 1048576 2965821 1048576 1 1048576 (BSN.sqrt_enclosure 8 1 1482910 1482911 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep148 := BSN.log_dyadic_bound 0 16 1 0 1 524288 196463 0 1 0 16 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 0) (BSN.artanhQ 16) 0 0 rfl) rfl rfl rfl

noncomputable def ep149 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz554 136442 1000 0 1 9364972152248037 4503599627370496 1000000000589389 196463000000000000000 638887765198513332177 2251799813685248000 68221000040208706969 98231500000000000000000 qz18 (BSN.isNear_log_sfrac 8 1 9364972152248037 4503599627370496 1000000000589389 196463000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz555) Bool.false 39279540158062550581248 18889465931478580854784 1000000000589389 196463000000000000000 9364972152248037 4503599627370496 1000000000589389 196463000000000000000 (BSN.log_rat_reduce_isNear 8 1 3 16 16 0 524288 24973259072661432 36028797018963968 196463 1000000000000000 rfl rfl rfl rfl (ep148 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep150 := nat_lit 700774670939596730895245583234290372436542405016541704899985509099572335476736

noncomputable def ep151 := nat_lit 384257981795400481341978565148420520194773571676314631940521142684961734656

noncomputable def ep152 := nat_lit 2101555496855199391723052792572574276269237667906272485436075485013347082960896

noncomputable def ep153 := BSN.cos_dyadic_bound_f 2104155648 2147483648 3 2 1048576 393310 ep150 ep78 ep151 ep152 ep81 ep151 584233 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2104155648) qz15 0 2 ep150 ep78 ep151 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2104155648) qz16 0 2 ep152 ep81 ep151 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz30 := (@Nat.cast Real Real.instNatCast 1048576)

noncomputable abbrev qz31 := (@Nat.cast Real Real.instNatCast 151115727451828646838272)

noncomputable abbrev qz318 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 297505299) qz30)

noncomputable def ep154 := @Enclosure.Real.IsNear.cos_image qz29 qz318 Bool.false 297505299 1048576 729 1048576 Bool.false 584233 1048576 1 196463 (@Enclosure.Real.IsNear.recentre' qz29 Bool.false 638887765198513332177 2251799813685248000 68221000040208706969 98231500000000000000000 297505299 1048576 729 1048576 (ep149 rfl) rfl) (Enclosure.sfrac_false_div 297505299 1048576) (BSN.cos_reduce0 qz318 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 148066790539928511971328) qz31) 226375608064910080 72057594037927936 Bool.false 584233 1048576 45 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q0 297505299 1048576 226375608064910080 72057594037927936 45 148066790539928511971328 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 584233 1048576 148066790539928511971328 151115727451828646838272 2104155648 2147483648 393310 392926 (ep153 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep155 := nat_lit 1261087001305837795226368466969603933969620510172434017114421499465082234470400

noncomputable def ep156 := nat_lit 3302224776211430243861173257719674765268690750383184583038438321510868295090176

noncomputable def ep157 := BSN.sin_dyadic_bound_f 2104155648 2147483648 3 2 1048576 393310 ep155 ep109 ep151 ep156 ep112 ep151 870736 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2104155648) qz19 0 2 ep155 ep109 ep151 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2104155648) qz20 0 2 ep156 ep112 ep151 rfl rfl rfl rfl) rfl rfl

noncomputable def ep158 := @Enclosure.Real.IsNear.sin_image qz29 qz318 Bool.false 297505299 1048576 729 1048576 Bool.false 870736 1048576 1 196463 (@Enclosure.Real.IsNear.recentre' qz29 Bool.false 638887765198513332177 2251799813685248000 68221000040208706969 98231500000000000000000 297505299 1048576 729 1048576 (ep149 rfl) rfl) (Enclosure.sfrac_false_div 297505299 1048576) (BSN.sin_reduce0 qz318 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 148066790539928511971328) qz31) 226375608064910080 72057594037927936 Bool.false 870736 1048576 45 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q0 297505299 1048576 226375608064910080 72057594037927936 45 148066790539928511971328 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 870736 1048576 148066790539928511971328 151115727451828646838272 2104155648 2147483648 393310 392926 (ep157 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz319 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 8))) Bool.false 370727 1048576 1 1048576 370727 1048576 1 1048576 (ep147 rfl rfl) rfl)

noncomputable def ep159 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz315 (Real.cos qz29)) (@HMul.hMul Real Real Real qz0 qz315 (@Neg.neg Real Real.instNeg (Real.sin qz29))) Bool.false 216590947391 1099511627776 53599746912863 216013352927756288 Bool.true 20175334067 68719476736 6707004268969 27001669115969536 (@Enclosure.Real.IsNear.mulLit_ff qz315 (Real.cos qz29) 370727 1048576 1 1048576 584233 1048576 144270103 206006386688 216590947391 1099511627776 53599746912863 216013352927756288 qz319 (@Enclosure.Real.IsNear.recentre' (Real.cos qz29) Bool.false 584233 1048576 144270103 206006386688 584233 1048576 144270103 206006386688 (ep154 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz315 (@Neg.neg Real Real.instNeg (Real.sin qz29)) 370727 1048576 1 1048576 54421 65536 144270103 206006386688 20175334067 68719476736 6707004268969 27001669115969536 qz319 (@Enclosure.Real.IsNear.neg (Real.sin qz29) Bool.false 54421 65536 144270103 206006386688 (@Enclosure.Real.IsNear.recentre' (Real.sin qz29) Bool.false 870736 1048576 144270103 206006386688 54421 65536 144270103 206006386688 (ep158 rfl rfl) rfl)) rfl)

noncomputable def ep160 := @ep39 216590947391 1099511627776 53599746912863 216013352927756288 Bool.true 20175334067 68719476736 6707004268969 27001669115969536 Bool.false 1020368433033980288172032 3712078734803 1099511627776 511165889282155 216013352927756288 Bool.true 29391430347344083681280 427701602855 1099511627776 511092725282177 216013352927756288 (ep40 (BSN.head_sum_c_succ qz5 7 8 rfl rfl) (ep145 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep146 ep159) rfl rfl

theorem EMRow47.d6 : Enclosure.Complex.IsNear qz3 Bool.false 3712078734803 1099511627776 511165889282155 216013352927756288 Bool.true 427701602855 1099511627776 511092725282177 216013352927756288 := ep38 (BSN.head_sum_c_succ qz5 8 9 rfl rfl) (ep160 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable abbrev qz32 := (BSN.headSumC qz271 17)

noncomputable abbrev qz556 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 16) qz7)

noncomputable def ep161 := @Enclosure.Complex.IsNear.of_eq qz32 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 16) qz556) Bool.false 4552428540229 1099511627776 859176159714893 216013352927756288 Bool.true 124410818961 1099511627776 859322998125723 216013352927756288

noncomputable def ep162 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 16) qz556 Bool.false 4480604503945 1099511627776 821302789329617 216013352927756288 Bool.false 35229108015 274877906944 410652303404415 108006676463878144 Bool.false

noncomputable def ep163 := nat_lit 1251362028650276822450176

noncomputable abbrev qz557 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 15) qz7)

noncomputable def ep164 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 16) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 15) qz557) Bool.false 4480604503945 1099511627776 821302789329617 216013352927756288 Bool.false 35229108015 274877906944 410652303404415 108006676463878144

noncomputable def ep165 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 15) qz557 Bool.false 4382087810347 1099511627776 782118133754131 216013352927756288 Bool.true 62667028857 549755813888 48874889708261 13500834557984768 Bool.false

noncomputable def ep166 := nat_lit 2463238375776521981788160

noncomputable abbrev qz558 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 14) qz7)

noncomputable def ep167 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 15) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 14) qz558) Bool.false 4382087810347 1099511627776 782118133754131 216013352927756288 Bool.true 62667028857 549755813888 48874889708261 13500834557984768

noncomputable def ep168 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 14) qz558 Bool.false 1121791581103 274877906944 370779290323931 108006676463878144 Bool.false 74546109289 549755813888 185329990449025 54003338231939072 Bool.true

noncomputable abbrev qz559 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 13) qz7)

noncomputable def ep169 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 14) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 13) qz559) Bool.false 1121791581103 274877906944 370779290323931 108006676463878144 Bool.false 74546109289 549755813888 185329990449025 54003338231939072

noncomputable def ep170 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 13) qz559 Bool.false 4583383078201 1099511627776 699479237649169 216013352927756288 Bool.true 17535092243 137438953472 349555066885117 108006676463878144 Bool.true

noncomputable def ep171 := nat_lit 4933691549455889006067712

noncomputable abbrev qz560 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 12) qz7)

noncomputable def ep172 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 13) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 12) qz560) Bool.false 4583383078201 1099511627776 699479237649169 216013352927756288 Bool.true 17535092243 137438953472 349555066885117 108006676463878144

noncomputable def ep173 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 12) qz560 Bool.false 2137788427769 549755813888 163887429488781 54003338231939072 Bool.true 108865304273 549755813888 81916265621651 27001669115969536 Bool.false

noncomputable def ep174 := nat_lit 2519741494516877505855488

noncomputable abbrev qz561 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 11) qz7)

noncomputable def ep175 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 12) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 11) qz561) Bool.false 2137788427769 549755813888 163887429488781 54003338231939072 Bool.true 108865304273 549755813888 81916265621651 27001669115969536

noncomputable def ep176 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 11) qz561 Bool.false 3976758853889 1099511627776 609751882351159 216013352927756288 Bool.true 37085018993 549755813888 304814383914947 108006676463878144 Bool.false

noncomputable def ep177 := nat_lit 4701046468113977980223488

noncomputable abbrev qz562 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 10) qz7)

noncomputable def ep178 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 11) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 10) qz562) Bool.false 3976758853889 1099511627776 609751882351159 216013352927756288 Bool.true 37085018993 549755813888 304814383914947 108006676463878144

noncomputable def ep179 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 10) qz562 Bool.false 3629079829253 1099511627776 561707362726777 216013352927756288 Bool.true 35360093015 549755813888 17555881261721 6750417278992384 Bool.false

noncomputable abbrev qz563 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 9) qz7)

noncomputable def ep180 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 10) (@HAdd.hAdd Complex Complex Complex qz4 qz3 qz563) Bool.false 3629079829253 1099511627776 561707362726777 216013352927756288 Bool.true 35360093015 549755813888 17555881261721 6750417278992384

noncomputable def ep181 := @Enclosure.Complex.IsNear.addLitP qz3 qz563 Bool.false 3712078734803 1099511627776 511165889282155 216013352927756288 Bool.true 427701602855 1099511627776 511092725282177 216013352927756288 Bool.true

noncomputable def ep182 := nat_lit 1995107735195507086065664

noncomputable abbrev qz564 := (Real.log (Enclosure.sfrac Bool.false 9 1))

noncomputable abbrev qz33 := (@HMul.hMul Real Real Real qz267 qz277 qz564)

noncomputable abbrev qz320 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 9)))

noncomputable def ep183 := @Enclosure.Complex.IsNear.of_eq qz563 (Complex.mk (@HMul.hMul Real Real Real qz0 qz320 (Real.cos qz33)) (@HMul.hMul Real Real Real qz0 qz320 (@Neg.neg Real Real.instNeg (Real.sin qz33)))) Bool.true 41499452775 549755813888 25270736722311 108006676463878144 Bool.false 356981416825 1099511627776 50695475092895 216013352927756288 (BSN.cpow_neg_s_mk qz12 136442 1000 9 qz13 rfl)

noncomputable abbrev qz321 := (Real.sqrt (@Nat.cast Real Real.instNatCast 9))

noncomputable abbrev qz322 := (@Nat.cast Real Real.instNatCast 9)

noncomputable abbrev qz565 := (@HDiv.hDiv Real Real Real qz1 qz322 qz14)

noncomputable def ep184 := @Enclosure.Real.IsNear.inv_image qz321 3145729 1048576 1 1048576 174762 174763 524288 (@Enclosure.Real.IsNear.of_eq qz321 (Real.sqrt qz565) Bool.false 3145729 1048576 1 1048576 (BSN.sqrt_natCast_div_one 9) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz565) Bool.false 3145729 1048576 1 1048576 3145729 1048576 1 1048576 (BSN.sqrt_enclosure 9 1 1572864 1572865 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep185 := BSN.log_dyadic_bound 1 17 3 2 1252815 524288 196463 1448 3 61752 18 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 1) (BSN.artanhQ 17) 0 2 1448 1252815 3 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep186 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz564 136442 1000 0 1 9895417793173221 4503599627370496 1000000000589389 196463000000000000000 675075297268070309841 2251799813685248000 68221000040208706969 98231500000000000000000 qz18 (BSN.isNear_log_sfrac 9 1 9895417793173221 4503599627370496 1000000000589389 196463000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz565) Bool.false 41504390431577613533184 18889465931478580854784 1000000000589389 196463000000000000000 9895417793173221 4503599627370496 1000000000589389 196463000000000000000 (BSN.log_rat_reduce_isNear 9 1 3 18 16 61752 524288 24973259072661432 36028797018963968 196463 1000000000000000 rfl rfl rfl rfl (ep185 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep187 := nat_lit 2472024969907422443113057700826012873762457234917599819123581858405494980862561

noncomputable def ep188 := nat_lit 4768383165036304083800207840500505590937922320768589152794164159337281872481

noncomputable def ep189 := nat_lit 7406538143392194721171572686797037610105495860111262279065157246897810378842721

noncomputable def ep190 := BSN.cos_dyadic_bound_f 2882679723 2147483648 3 2 1048576 393310 ep187 ep78 ep188 ep189 ep81 ep188 237462 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2882679723) qz15 0 2 ep187 ep78 ep188 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2882679723) qz16 0 2 ep189 ep81 ep188 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz323 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 314356431) qz30)

noncomputable def ep191 := @Enclosure.Real.IsNear.cos_image qz33 qz323 Bool.false 314356431 1048576 365 524288 Bool.true 237462 1048576 1 196463 (@Enclosure.Real.IsNear.recentre' qz33 Bool.false 675075297268070309841 2251799813685248000 68221000040208706969 98231500000000000000000 314356431 1048576 365 524288 (ep186 rfl) rfl) (Enclosure.sfrac_false_div 314356431 1048576) (BSN.cos_reduce2 qz323 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 202850551988290303557632) qz31) 226375608064910080 72057594037927936 Bool.false 237462 1048576 47 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q2 314356431 1048576 226375608064910080 72057594037927936 47 202850551988290303557632 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 237462 1048576 202850551988290303557632 151115727451828646838272 2882679723 2147483648 393310 392926 (ep190 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep192 := nat_lit 4445830239301331354336463695214422768299672684995064803100212013802421140054625

noncomputable def ep193 := nat_lit 11636120863521999530936014103343630241256671824562972959015079008462652148540001

noncomputable def ep194 := BSN.sin_dyadic_bound_f 2882679723 2147483648 3 2 1048576 393310 ep192 ep109 ep188 ep193 ep112 ep188 1021333 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2882679723) qz19 0 2 ep192 ep109 ep188 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2882679723) qz20 0 2 ep193 ep112 ep188 rfl rfl rfl rfl) rfl rfl

noncomputable def ep195 := @Enclosure.Real.IsNear.sin_image qz33 qz323 Bool.false 314356431 1048576 365 524288 Bool.true 1021333 1048576 1 196463 (@Enclosure.Real.IsNear.recentre' qz33 Bool.false 675075297268070309841 2251799813685248000 68221000040208706969 98231500000000000000000 314356431 1048576 365 524288 (ep186 rfl) rfl) (Enclosure.sfrac_false_div 314356431 1048576) (BSN.sin_reduce2 qz323 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 202850551988290303557632) qz31) 226375608064910080 72057594037927936 Bool.false 1021333 1048576 47 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q2 314356431 1048576 226375608064910080 72057594037927936 47 202850551988290303557632 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1021333 1048576 202850551988290303557632 151115727451828646838272 2882679723 2147483648 393310 392926 (ep194 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz324 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 9))) Bool.false 349525 1048576 1 1048576 349525 1048576 1 1048576 (ep184 rfl rfl) rfl)

noncomputable def ep196 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz320 (Real.cos qz33)) (@HMul.hMul Real Real Real qz0 qz320 (@Neg.neg Real Real.instNeg (Real.sin qz33))) Bool.true 41499452775 549755813888 25270736722311 108006676463878144 Bool.false 356981416825 1099511627776 50695475092895 216013352927756288 (@Enclosure.Real.IsNear.mulLit_ft qz320 (Real.cos qz33) 349525 1048576 1 1048576 118731 524288 72233283 103003193344 41499452775 549755813888 25270736722311 108006676463878144 qz324 (@Enclosure.Real.IsNear.recentre' (Real.cos qz33) Bool.true 237462 1048576 72233283 103003193344 118731 524288 72233283 103003193344 (ep191 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz320 (@Neg.neg Real Real.instNeg (Real.sin qz33)) 349525 1048576 1 1048576 1021333 1048576 72233283 103003193344 356981416825 1099511627776 50695475092895 216013352927756288 qz324 (@Enclosure.Real.IsNear.neg (Real.sin qz33) Bool.true 1021333 1048576 72233283 103003193344 (@Enclosure.Real.IsNear.recentre' (Real.sin qz33) Bool.true 1021333 1048576 72233283 103003193344 1021333 1048576 72233283 103003193344 (ep195 rfl rfl) rfl)) rfl)

noncomputable def ep197 := @ep181 41499452775 549755813888 25270736722311 108006676463878144 Bool.false 356981416825 1099511627776 50695475092895 216013352927756288 Bool.false ep182 3629079829253 1099511627776 561707362726777 216013352927756288 Bool.true 77757666858466835169280 35360093015 549755813888 17555881261721 6750417278992384 EMRow47.d6 (ep183 ep196) rfl rfl

noncomputable abbrev qz34 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 10)))

noncomputable abbrev qz566 := (Real.log (Enclosure.sfrac Bool.false 10 1))

noncomputable abbrev qz35 := (@HMul.hMul Real Real Real qz267 qz277 qz566)

noncomputable def ep198 := @Enclosure.Complex.IsNear.of_eq qz562 (Complex.mk (@HMul.hMul Real Real Real qz0 qz34 (Real.cos qz35)) (@HMul.hMul Real Real Real qz0 qz34 (@Neg.neg Real Real.instNeg (Real.sin qz35)))) Bool.false 86919756159 274877906944 24022259812191 108006676463878144 Bool.true 862462989 274877906944 23920283727411 108006676463878144 (BSN.cpow_neg_s_mk qz12 136442 1000 10 qz13 rfl)

noncomputable abbrev qz325 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 10) qz14)

noncomputable def ep199 := @Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 10)) 3315889 1048576 1 1048576 165794 165795 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 10)) (Real.sqrt qz325) Bool.false 3315889 1048576 1 1048576 (BSN.sqrt_natCast_div_one 10) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz325) Bool.false 3315889 1048576 1 1048576 3315889 1048576 1 1048576 (BSN.sqrt_enclosure 10 1 1657944 1657945 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep200 := BSN.log_dyadic_bound 2 18 3 2 1574640 524288 196463 6528 48 116991 20 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 2) (BSN.artanhQ 18) 0 2 6528 1574640 48 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep201 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz566 136442 1000 0 1 10369917190100709 4503599627370496 1000000000589389 196463000000000000000 707446120625860468689 2251799813685248000 68221000040208706969 98231500000000000000000 qz18 (BSN.isNear_log_sfrac 10 1 10369917190100709 4503599627370496 1000000000589389 196463000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz325) Bool.false 43494585150108164161536 18889465931478580854784 1000000000589389 196463000000000000000 10369917190100709 4503599627370496 1000000000589389 196463000000000000000 (BSN.log_rat_reduce_isNear 10 1 3 20 16 116991 524288 24973259072661432 36028797018963968 196463 1000000000000000 rfl rfl rfl rfl (ep200 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep202 := BSN.cos_dyadic_bound_f 21309781 2147483648 1 0 1048576 393310 0 1 1 0 1 1 1048524 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 21309781) qz15 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 21309781) qz16 0 0 rfl) rfl rfl

noncomputable abbrev qz326 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 329430271) qz30)

noncomputable def ep203 := @Enclosure.Real.IsNear.cos_image qz35 qz326 Bool.false 329430271 1048576 729 1048576 Bool.false 1048524 1048576 1 196463 (@Enclosure.Real.IsNear.recentre' qz35 Bool.false 707446120625860468689 2251799813685248000 68221000040208706969 98231500000000000000000 329430271 1048576 729 1048576 (ep201 rfl) rfl) (Enclosure.sfrac_false_div 329430271 1048576) (BSN.cos_reduce0 qz326 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 1499542590938060685312) qz31) 226375608064910080 72057594037927936 Bool.false 1048524 1048576 50 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q0 329430271 1048576 226375608064910080 72057594037927936 50 1499542590938060685312 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1048524 1048576 1499542590938060685312 151115727451828646838272 21309781 2147483648 393310 392926 (ep202 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep204 := BSN.sin_dyadic_bound_f 21309781 2147483648 1 0 1048576 393310 0 1 1 0 1 1 10404 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 21309781) qz19 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 21309781) qz20 0 0 rfl) rfl rfl

noncomputable def ep205 := @Enclosure.Real.IsNear.sin_image qz35 qz326 Bool.false 329430271 1048576 729 1048576 Bool.false 10404 1048576 1 196463 (@Enclosure.Real.IsNear.recentre' qz35 Bool.false 707446120625860468689 2251799813685248000 68221000040208706969 98231500000000000000000 329430271 1048576 729 1048576 (ep201 rfl) rfl) (Enclosure.sfrac_false_div 329430271 1048576) (BSN.sin_reduce0 qz326 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 1499542590938060685312) qz31) 226375608064910080 72057594037927936 Bool.false 10404 1048576 50 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q0 329430271 1048576 226375608064910080 72057594037927936 50 1499542590938060685312 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 10404 1048576 1499542590938060685312 151115727451828646838272 21309781 2147483648 393310 392926 (ep204 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz327 := (@Enclosure.Real.IsNear.recentre' qz34 Bool.false 331589 1048576 1 1048576 331589 1048576 1 1048576 (ep199 rfl rfl) rfl)

noncomputable def ep206 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz34 (Real.cos qz35)) (@HMul.hMul Real Real Real qz0 qz34 (@Neg.neg Real Real.instNeg (Real.sin qz35))) Bool.false 86919756159 274877906944 24022259812191 108006676463878144 Bool.true 862462989 274877906944 23920283727411 108006676463878144 (@Enclosure.Real.IsNear.mulLit_ff qz34 (Real.cos qz35) 331589 1048576 1 1048576 262131 262144 144270103 206006386688 86919756159 274877906944 24022259812191 108006676463878144 qz327 (@Enclosure.Real.IsNear.recentre' (Real.cos qz35) Bool.false 1048524 1048576 144270103 206006386688 262131 262144 144270103 206006386688 (ep203 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz34 (@Neg.neg Real Real.instNeg (Real.sin qz35)) 331589 1048576 1 1048576 2601 262144 144270103 206006386688 862462989 274877906944 23920283727411 108006676463878144 qz327 (@Enclosure.Real.IsNear.neg (Real.sin qz35) Bool.false 2601 262144 144270103 206006386688 (@Enclosure.Real.IsNear.recentre' (Real.sin qz35) Bool.false 10404 1048576 144270103 206006386688 2601 262144 144270103 206006386688 (ep205 rfl rfl) rfl)) rfl)

noncomputable def ep207 := @ep179 86919756159 274877906944 24022259812191 108006676463878144 Bool.true 862462989 274877906944 23920283727411 108006676463878144 Bool.false 1093123150178028634505216 3976758853889 1099511627776 609751882351159 216013352927756288 Bool.true 10193852399774326587392 37085018993 549755813888 304814383914947 108006676463878144 (ep180 (BSN.head_sum_c_succ qz5 9 10 rfl rfl) (ep197 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep198 ep206) rfl rfl

noncomputable abbrev qz36 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 11)))

noncomputable abbrev qz567 := (Real.log (Enclosure.sfrac Bool.false 11 1))

noncomputable abbrev qz37 := (@HMul.hMul Real Real Real qz267 qz277 qz567)

noncomputable def ep208 := @Enclosure.Complex.IsNear.of_eq qz561 (Complex.mk (@HMul.hMul Real Real Real qz0 qz36 (Real.cos qz37)) (@HMul.hMul Real Real Real qz0 qz36 (@Neg.neg Real Real.instNeg (Real.sin qz37)))) Bool.false 298818001649 1099511627776 45797835603965 216013352927756288 Bool.true 2243133915 17179869184 22850678571657 108006676463878144 (BSN.cpow_neg_s_mk qz12 136442 1000 11 qz13 rfl)

noncomputable abbrev qz328 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 11) qz14)

noncomputable def ep209 := @Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 11)) 3477733 1048576 1 1048576 158078 158079 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 11)) (Real.sqrt qz328) Bool.false 3477733 1048576 1 1048576 (BSN.sqrt_natCast_div_one 11) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz328) Bool.false 3477733 1048576 1 1048576 3477733 1048576 1 1048576 (BSN.sqrt_enclosure 11 1 1738866 1738867 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep210 := BSN.log_dyadic_bound 3 19 4 3 4939817505 524288 196463 41676111 10935 166961 22 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 3) (BSN.artanhQ 19) 0 3 41676111 4939817505 10935 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep211 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz567 136442 1000 0 1 10799156221662949 4503599627370496 1000000000589389 196463000000000000000 736729236598068043729 2251799813685248000 68221000040208706969 98231500000000000000000 qz18 (BSN.isNear_log_sfrac 11 1 10799156221662949 4503599627370496 1000000000589389 196463000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz328) Bool.false 45294944137145793642496 18889465931478580854784 1000000000589389 196463000000000000000 10799156221662949 4503599627370496 1000000000589389 196463000000000000000 (BSN.log_rat_reduce_isNear 11 1 3 22 16 166961 524288 24973259072661432 36028797018963968 196463 1000000000000000 rfl rfl rfl rfl (ep210 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep212 := nat_lit 855695436178912961615703379798016256

noncomputable def ep213 := BSN.cos_dyadic_bound_f 961788996 2147483648 2 1 1048576 393310 ep212 ep61 ep212 ep212 ep62 ep212 945157 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 961788996) qz15 0 1 ep212 ep61 ep212 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 961788996) qz16 0 1 ep212 ep62 ep212 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz329 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 85766571) qz17)

noncomputable def ep214 := @Enclosure.Real.IsNear.cos_image qz37 qz329 Bool.false 85766571 262144 729 1048576 Bool.false 945157 1048576 1 196463 (@Enclosure.Real.IsNear.recentre' qz37 Bool.false 736729236598068043729 2251799813685248000 68221000040208706969 98231500000000000000000 85766571 262144 729 1048576 (ep211 rfl) rfl) (Enclosure.sfrac_false_div 85766571 262144) (BSN.cos_reduce0 qz329 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 16919970968146125258752) qz285) 226375608064910080 72057594037927936 Bool.false 945157 1048576 52 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q0 85766571 262144 226375608064910080 72057594037927936 52 16919970968146125258752 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 945157 1048576 16919970968146125258752 37778931862957161709568 961788996 2147483648 393310 392926 (ep213 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep215 := BSN.sin_dyadic_bound_f 961788996 2147483648 2 1 1048576 393310 ep212 ep65 ep212 ep212 ep66 ep212 454080 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 961788996) qz19 0 1 ep212 ep65 ep212 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 961788996) qz20 0 1 ep212 ep66 ep212 rfl rfl rfl rfl) rfl rfl

noncomputable def ep216 := @Enclosure.Real.IsNear.sin_image qz37 qz329 Bool.false 85766571 262144 729 1048576 Bool.false 454080 1048576 1 196463 (@Enclosure.Real.IsNear.recentre' qz37 Bool.false 736729236598068043729 2251799813685248000 68221000040208706969 98231500000000000000000 85766571 262144 729 1048576 (ep211 rfl) rfl) (Enclosure.sfrac_false_div 85766571 262144) (BSN.sin_reduce0 qz329 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 16919970968146125258752) qz285) 226375608064910080 72057594037927936 Bool.false 454080 1048576 52 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q0 85766571 262144 226375608064910080 72057594037927936 52 16919970968146125258752 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 454080 1048576 16919970968146125258752 37778931862957161709568 961788996 2147483648 393310 392926 (ep215 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz330 := (@Enclosure.Real.IsNear.recentre' qz36 Bool.false 316157 1048576 1 1048576 316157 1048576 1 1048576 (ep209 rfl rfl) rfl)

noncomputable def ep217 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz36 (Real.cos qz37)) (@HMul.hMul Real Real Real qz0 qz36 (@Neg.neg Real Real.instNeg (Real.sin qz37))) Bool.false 298818001649 1099511627776 45797835603965 216013352927756288 Bool.true 2243133915 17179869184 22850678571657 108006676463878144 (@Enclosure.Real.IsNear.mulLit_ff qz36 (Real.cos qz37) 316157 1048576 1 1048576 945157 1048576 144270103 206006386688 298818001649 1099511627776 45797835603965 216013352927756288 qz330 (@Enclosure.Real.IsNear.recentre' (Real.cos qz37) Bool.false 945157 1048576 144270103 206006386688 945157 1048576 144270103 206006386688 (ep214 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz36 (@Neg.neg Real Real.instNeg (Real.sin qz37)) 316157 1048576 1 1048576 7095 16384 144270103 206006386688 2243133915 17179869184 22850678571657 108006676463878144 qz330 (@Enclosure.Real.IsNear.neg (Real.sin qz37) Bool.false 7095 16384 144270103 206006386688 (@Enclosure.Real.IsNear.recentre' (Real.sin qz37) Bool.false 454080 1048576 144270103 206006386688 7095 16384 144270103 206006386688 (ep216 rfl rfl) rfl)) rfl)

noncomputable def ep218 := @ep176 298818001649 1099511627776 45797835603965 216013352927756288 Bool.true 2243133915 17179869184 22850678571657 108006676463878144 Bool.false ep177 2137788427769 549755813888 163887429488781 54003338231939072 Bool.true 1870291686086496223232 108865304273 549755813888 81916265621651 27001669115969536 (ep178 (BSN.head_sum_c_succ qz5 10 11 rfl rfl) (ep207 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep208 ep217) rfl rfl

noncomputable abbrev qz568 := (@Nat.cast Real Real.instNatCast 12)

noncomputable abbrev qz38 := (@Inv.inv Real Real.instInv (Real.sqrt qz568))

noncomputable abbrev qz569 := (Real.log (Enclosure.sfrac Bool.false 12 1))

noncomputable abbrev qz39 := (@HMul.hMul Real Real Real qz267 qz277 qz569)

noncomputable def ep219 := @Enclosure.Complex.IsNear.of_eq qz560 (Complex.mk (@HMul.hMul Real Real Real qz0 qz38 (Real.cos qz39)) (@HMul.hMul Real Real Real qz0 qz38 (@Neg.neg Real Real.instNeg (Real.sin qz39)))) Bool.false 307806222663 1099511627776 43929519694045 216013352927756288 Bool.false 38724935301 549755813888 21890004398513 108006676463878144 (BSN.cpow_neg_s_mk qz12 136442 1000 12 qz13 rfl)

noncomputable abbrev qz570 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 12) qz14)

noncomputable def ep220 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz568) 3632373 1048576 1 1048576 151348 151349 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz568) (Real.sqrt qz570) Bool.false 3632373 1048576 1 1048576 (BSN.sqrt_natCast_div_one 12) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz570) Bool.false 3632373 1048576 1 1048576 3632373 1048576 1 1048576 (BSN.sqrt_enclosure 12 1 1816186 1816187 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep221 := BSN.log_dyadic_bound 4 20 4 3 6720000000 524288 196463 91811840 61440 212580 24 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 4) (BSN.artanhQ 20) 0 3 91811840 6720000000 61440 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep222 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz569 136442 1000 0 1 11191020447815397 4503599627370496 1000000000589389 196463000000000000000 763462605970414198737 2251799813685248000 68221000040208706969 98231500000000000000000 qz18 (BSN.isNear_log_sfrac 12 1 11191020447815397 4503599627370496 1000000000589389 196463000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz570) Bool.false 46938541828353910898688 18889465931478580854784 1000000000589389 196463000000000000000 11191020447815397 4503599627370496 1000000000589389 196463000000000000000 (BSN.log_rat_reduce_isNear 12 1 3 24 16 212580 524288 24973259072661432 36028797018963968 196463 1000000000000000 rfl rfl rfl rfl (ep221 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep223 := nat_lit 4211145537045777202707707397688831714284135860617803045025450116819083250441825

noncomputable def ep224 := nat_lit 4278731413360620197036541421151222099455568163685599793867757835369348406881

noncomputable def ep225 := nat_lit 11022263222355404050582126879265076320678380143638755099209916793268905758498401

noncomputable def ep226 := BSN.sin_dyadic_bound_f 2843900373 2147483648 3 2 1048576 393310 ep223 ep109 ep224 ep225 ep112 ep224 1016879 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2843900373) qz19 0 2 ep223 ep109 ep224 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2843900373) qz20 0 2 ep225 ep112 ep224 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz331 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 355514979) qz30)

noncomputable def ep227 := @Enclosure.Real.IsNear.cos_image qz39 qz331 Bool.false 355514979 1048576 365 524288 Bool.false 1016879 1048576 1 196463 (@Enclosure.Real.IsNear.recentre' qz39 Bool.false 763462605970414198737 2251799813685248000 68221000040208706969 98231500000000000000000 355514979 1048576 365 524288 (ep222 rfl) rfl) (Enclosure.sfrac_false_div 355514979 1048576) (BSN.cos_reduce3 qz331 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 200121697880653051199488) qz31) 226375608064910080 72057594037927936 Bool.false 1016879 1048576 53 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q3 355514979 1048576 226375608064910080 72057594037927936 53 200121697880653051199488 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1016879 1048576 200121697880653051199488 151115727451828646838272 2843900373 2147483648 393310 392926 (ep226 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep228 := nat_lit 2341426956764703166036298128236529273313166841749306402700302401715210405092961

noncomputable def ep229 := nat_lit 7015723407467388257714821301867285375740589388920548008513171689474892518465121

noncomputable def ep230 := BSN.cos_dyadic_bound_f 2843900373 2147483648 3 2 1048576 393310 ep228 ep78 ep224 ep229 ep81 ep224 255866 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2843900373) qz15 0 2 ep228 ep78 ep224 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2843900373) qz16 0 2 ep229 ep81 ep224 rfl rfl rfl rfl) rfl rfl

noncomputable def ep231 := @Enclosure.Real.IsNear.sin_image qz39 qz331 Bool.false 355514979 1048576 365 524288 Bool.true 255866 1048576 1 196463 (@Enclosure.Real.IsNear.recentre' qz39 Bool.false 763462605970414198737 2251799813685248000 68221000040208706969 98231500000000000000000 355514979 1048576 365 524288 (ep222 rfl) rfl) (Enclosure.sfrac_false_div 355514979 1048576) (BSN.sin_reduce3 qz331 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 200121697880653051199488) qz31) 226375608064910080 72057594037927936 Bool.false 255866 1048576 53 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q3 355514979 1048576 226375608064910080 72057594037927936 53 200121697880653051199488 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 255866 1048576 200121697880653051199488 151115727451828646838272 2843900373 2147483648 393310 392926 (ep230 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz332 := (@Enclosure.Real.IsNear.recentre' qz38 Bool.false 302697 1048576 1 1048576 302697 1048576 1 1048576 (ep220 rfl rfl) rfl)

noncomputable def ep232 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz38 (Real.cos qz39)) (@HMul.hMul Real Real Real qz0 qz38 (@Neg.neg Real Real.instNeg (Real.sin qz39))) Bool.false 307806222663 1099511627776 43929519694045 216013352927756288 Bool.false 38724935301 549755813888 21890004398513 108006676463878144 (@Enclosure.Real.IsNear.mulLit_ff qz38 (Real.cos qz39) 302697 1048576 1 1048576 1016879 1048576 72233283 103003193344 307806222663 1099511627776 43929519694045 216013352927756288 qz332 (@Enclosure.Real.IsNear.recentre' (Real.cos qz39) Bool.false 1016879 1048576 72233283 103003193344 1016879 1048576 72233283 103003193344 (ep227 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz38 (@Neg.neg Real Real.instNeg (Real.sin qz39)) 302697 1048576 1 1048576 127933 524288 72233283 103003193344 38724935301 549755813888 21890004398513 108006676463878144 qz332 (@Enclosure.Real.IsNear.neg (Real.sin qz39) Bool.true 127933 524288 72233283 103003193344 (@Enclosure.Real.IsNear.recentre' (Real.sin qz39) Bool.true 255866 1048576 72233283 103003193344 127933 524288 72233283 103003193344 (ep231 rfl rfl) rfl)) rfl)

noncomputable def ep233 := @ep173 307806222663 1099511627776 43929519694045 216013352927756288 Bool.false 38724935301 549755813888 21890004398513 108006676463878144 Bool.false ep174 4583383078201 1099511627776 699479237649169 216013352927756288 Bool.true 38560075630606481883136 17535092243 137438953472 349555066885117 108006676463878144 (ep175 (BSN.head_sum_c_succ qz5 11 12 rfl rfl) (ep218 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep219 ep232) rfl rfl

noncomputable abbrev qz571 := (@Nat.cast Real Real.instNatCast 13)

noncomputable abbrev qz40 := (@Inv.inv Real Real.instInv (Real.sqrt qz571))

noncomputable abbrev qz572 := (Real.log (Enclosure.sfrac Bool.false 13 1))

noncomputable abbrev qz41 := (@HMul.hMul Real Real Real qz267 qz277 qz572)

noncomputable def ep234 := @Enclosure.Complex.IsNear.of_eq qz559 (Complex.mk (@HMul.hMul Real Real Real qz0 qz40 (Real.cos qz41)) (@HMul.hMul Real Real Real qz0 qz40 (@Neg.neg Real Real.instNeg (Real.sin qz41)))) Bool.true 96216753789 1099511627776 42079342998693 216013352927756288 Bool.false 144686478261 549755813888 21104914012933 108006676463878144 (BSN.cpow_neg_s_mk qz12 136442 1000 13 qz13 rfl)

noncomputable abbrev qz573 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 13) qz14)

noncomputable def ep235 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz571) 3780695 1048576 1 1048576 145411 145412 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz571) (Real.sqrt qz573) Bool.false 3780695 1048576 1 1048576 (BSN.sqrt_natCast_div_one 13) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz573) Bool.false 3780695 1048576 1 1048576 3780695 1048576 1 1048576 (BSN.sqrt_enclosure 13 1 1890347 1890348 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep236 := BSN.log_dyadic_bound 5 21 5 4 35742602096145 524288 196463 699352521000 41015625 254545 26 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 5) (BSN.artanhQ 21) 0 4 699352521000 35742602096145 41015625 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep237 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz572 136442 1000 0 1 11551497052968677 4503599627370496 1000000000589389 196463000000000000000 788054680450576113617 2251799813685248000 68221000040208706969 98231500000000000000000 qz18 (BSN.isNear_log_sfrac 13 1 11551497052968677 4503599627370496 1000000000589389 196463000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz573) Bool.false 48450490295254733815808 18889465931478580854784 1000000000589389 196463000000000000000 11551497052968677 4503599627370496 1000000000589389 196463000000000000000 (BSN.log_rat_reduce_isNear 13 1 3 26 16 254545 524288 24973259072661432 36028797018963968 196463 1000000000000000 rfl rfl rfl rfl (ep236 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep238 := nat_lit 1856664510774473501968463985899086396049335811328749978057023897466444485284801

noncomputable def ep239 := nat_lit 2692457634467286037726465649089352356112363173774719950443913060009488733121

noncomputable def ep240 := nat_lit 5564608617054485933829939026399080483435782707638700494270183866279314478388161

noncomputable def ep241 := BSN.cos_dyadic_bound_f 2683914087 2147483648 3 2 1048576 393310 ep238 ep78 ep239 ep240 ep81 ep239 330843 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2683914087) qz15 0 2 ep238 ep78 ep239 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2683914087) qz16 0 2 ep240 ep81 ep239 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz333 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 91741639) qz17)

noncomputable def ep242 := @Enclosure.Real.IsNear.cos_image qz41 qz333 Bool.false 91741639 262144 365 524288 Bool.true 330843 1048576 1 196463 (@Enclosure.Real.IsNear.recentre' qz41 Bool.false 788054680450576113617 2251799813685248000 68221000040208706969 98231500000000000000000 91741639 262144 365 524288 (ep237 rfl) rfl) (Enclosure.sfrac_false_div 91741639 262144) (BSN.cos_reduce2 qz333 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 47215915946225086496768) qz285) 226375608064910080 72057594037927936 Bool.false 330843 1048576 55 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q2 91741639 262144 226375608064910080 72057594037927936 55 47215915946225086496768 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 330843 1048576 47215915946225086496768 37778931862957161709568 2683914087 2147483648 393310 392926 (ep241 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep243 := nat_lit 3339842153286478474713054002099084031003914569852730184542287884991592482526145

noncomputable def ep244 := nat_lit 8742846422437353732568346203970503986909880047332943793881463839547488758191041

noncomputable def ep245 := BSN.sin_dyadic_bound_f 2683914087 2147483648 3 2 1048576 393310 ep243 ep109 ep239 ep244 ep112 ep239 995014 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2683914087) qz19 0 2 ep243 ep109 ep239 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2683914087) qz20 0 2 ep244 ep112 ep239 rfl rfl rfl rfl) rfl rfl

noncomputable def ep246 := @Enclosure.Real.IsNear.sin_image qz41 qz333 Bool.false 91741639 262144 365 524288 Bool.true 995014 1048576 1 196463 (@Enclosure.Real.IsNear.recentre' qz41 Bool.false 788054680450576113617 2251799813685248000 68221000040208706969 98231500000000000000000 91741639 262144 365 524288 (ep237 rfl) rfl) (Enclosure.sfrac_false_div 91741639 262144) (BSN.sin_reduce2 qz333 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 47215915946225086496768) qz285) 226375608064910080 72057594037927936 Bool.false 995014 1048576 55 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q2 91741639 262144 226375608064910080 72057594037927936 55 47215915946225086496768 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 995014 1048576 47215915946225086496768 37778931862957161709568 2683914087 2147483648 393310 392926 (ep245 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz334 := (@Enclosure.Real.IsNear.recentre' qz40 Bool.false 290823 1048576 1 1048576 290823 1048576 1 1048576 (ep235 rfl rfl) rfl)

noncomputable def ep247 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz40 (Real.cos qz41)) (@HMul.hMul Real Real Real qz0 qz40 (@Neg.neg Real Real.instNeg (Real.sin qz41))) Bool.true 96216753789 1099511627776 42079342998693 216013352927756288 Bool.false 144686478261 549755813888 21104914012933 108006676463878144 (@Enclosure.Real.IsNear.mulLit_ft qz40 (Real.cos qz41) 290823 1048576 1 1048576 330843 1048576 72233283 103003193344 96216753789 1099511627776 42079342998693 216013352927756288 qz334 (@Enclosure.Real.IsNear.recentre' (Real.cos qz41) Bool.true 330843 1048576 72233283 103003193344 330843 1048576 72233283 103003193344 (ep242 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz40 (@Neg.neg Real Real.instNeg (Real.sin qz41)) 290823 1048576 1 1048576 497507 524288 72233283 103003193344 144686478261 549755813888 21104914012933 108006676463878144 qz334 (@Enclosure.Real.IsNear.neg (Real.sin qz41) Bool.true 497507 524288 72233283 103003193344 (@Enclosure.Real.IsNear.recentre' (Real.sin qz41) Bool.true 995014 1048576 72233283 103003193344 497507 524288 72233283 103003193344 (ep246 rfl rfl) rfl)) rfl)

noncomputable def ep248 := @ep170 96216753789 1099511627776 42079342998693 216013352927756288 Bool.false 144686478261 549755813888 21104914012933 108006676463878144 Bool.false ep171 1121791581103 274877906944 370779290323931 108006676463878144 Bool.false 10245539246089498001408 74546109289 549755813888 185329990449025 54003338231939072 (ep172 (BSN.head_sum_c_succ qz5 12 13 rfl rfl) (ep233 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep234 ep247) rfl rfl

noncomputable abbrev qz574 := (@Nat.cast Real Real.instNatCast 14)

noncomputable abbrev qz42 := (@Inv.inv Real Real.instInv (Real.sqrt qz574))

noncomputable abbrev qz575 := (Real.log (Enclosure.sfrac Bool.false 14 1))

noncomputable abbrev qz43 := (@HMul.hMul Real Real Real qz267 qz277 qz575)

noncomputable def ep249 := @Enclosure.Complex.IsNear.of_eq qz558 (Complex.mk (@HMul.hMul Real Real Real qz0 qz42 (Real.cos qz43)) (@HMul.hMul Real Real Real qz0 qz42 (@Neg.neg Real Real.instNeg (Real.sin qz43)))) Bool.true 105078514065 1099511627776 40559553106269 216013352927756288 Bool.true 68606569073 274877906944 10169568384019 54003338231939072 (BSN.cpow_neg_s_mk qz12 136442 1000 14 qz13 rfl)

noncomputable abbrev qz576 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 14) qz14)

noncomputable def ep250 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz574) 3923413 1048576 1 1048576 140121 140122 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz574) (Real.sqrt qz576) Bool.false 3923413 1048576 1 1048576 (BSN.sqrt_natCast_div_one 14) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz576) Bool.false 3923413 1048576 1 1048576 3923413 1048576 1 1048576 (BSN.sqrt_enclosure 14 1 1961706 1961707 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep251 := BSN.log_dyadic_bound 6 22 5 4 51857700491520 524288 196463 1346332575744 176359680 293399 28 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 6) (BSN.artanhQ 22) 0 4 1346332575744 51857700491520 176359680 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep252 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz575 136442 1000 0 1 11885250371606245 4503599627370496 1000000000589389 196463000000000000000 162164733120269928029 450359962737049600 68221000040208706969 98231500000000000000000 qz18 (BSN.isNear_log_sfrac 14 1 11885250371606245 4503599627370496 1000000000589389 196463000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz576) Bool.false 49850353174629559828480 18889465931478580854784 1000000000589389 196463000000000000000 11885250371606245 4503599627370496 1000000000589389 196463000000000000000 (BSN.log_rat_reduce_isNear 14 1 3 28 16 293399 524288 24973259072661432 36028797018963968 196463 1000000000000000 rfl rfl rfl rfl (ep251 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep253 := nat_lit 380303575840080256894935001179099136

noncomputable def ep254 := BSN.sin_dyadic_bound_f 785294584 2147483648 2 1 1048576 393310 ep253 ep65 ep253 ep253 ep66 ep253 374955 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 785294584) qz19 0 1 ep253 ep65 ep253 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 785294584) qz20 0 1 ep253 ep66 ep253 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz335 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 377569191) qz30)

noncomputable def ep255 := @Enclosure.Real.IsNear.cos_image qz43 qz335 Bool.false 377569191 1048576 365 524288 Bool.true 374955 1048576 1 196463 (@Enclosure.Real.IsNear.recentre' qz43 Bool.false 162164733120269928029 450359962737049600 68221000040208706969 98231500000000000000000 377569191 1048576 365 524288 (ep252 rfl) rfl) (Enclosure.sfrac_false_div 377569191 1048576) (BSN.cos_reduce1 qz335 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 55260193693654405087232) qz31) 226375608064910080 72057594037927936 Bool.false 374955 1048576 57 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q1 377569191 1048576 226375608064910080 72057594037927936 57 55260193693654405087232 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 374955 1048576 55260193693654405087232 151115727451828646838272 785294584 2147483648 393310 392926 (ep254 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep256 := BSN.cos_dyadic_bound_f 785294584 2147483648 2 1 1048576 393310 ep253 ep61 ep253 ep253 ep62 ep253 979244 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 785294584) qz15 0 1 ep253 ep61 ep253 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 785294584) qz16 0 1 ep253 ep62 ep253 rfl rfl rfl rfl) rfl rfl

noncomputable def ep257 := @Enclosure.Real.IsNear.sin_image qz43 qz335 Bool.false 377569191 1048576 365 524288 Bool.false 979244 1048576 1 196463 (@Enclosure.Real.IsNear.recentre' qz43 Bool.false 162164733120269928029 450359962737049600 68221000040208706969 98231500000000000000000 377569191 1048576 365 524288 (ep252 rfl) rfl) (Enclosure.sfrac_false_div 377569191 1048576) (BSN.sin_reduce1 qz335 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 55260193693654405087232) qz31) 226375608064910080 72057594037927936 Bool.false 979244 1048576 57 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q1 377569191 1048576 226375608064910080 72057594037927936 57 55260193693654405087232 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 979244 1048576 55260193693654405087232 151115727451828646838272 785294584 2147483648 393310 392926 (ep256 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz336 := (@Enclosure.Real.IsNear.recentre' qz42 Bool.false 280243 1048576 1 1048576 280243 1048576 1 1048576 (ep250 rfl rfl) rfl)

noncomputable def ep258 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz42 (Real.cos qz43)) (@HMul.hMul Real Real Real qz0 qz42 (@Neg.neg Real Real.instNeg (Real.sin qz43))) Bool.true 105078514065 1099511627776 40559553106269 216013352927756288 Bool.true 68606569073 274877906944 10169568384019 54003338231939072 (@Enclosure.Real.IsNear.mulLit_ft qz42 (Real.cos qz43) 280243 1048576 1 1048576 374955 1048576 72233283 103003193344 105078514065 1099511627776 40559553106269 216013352927756288 qz336 (@Enclosure.Real.IsNear.recentre' (Real.cos qz43) Bool.true 374955 1048576 72233283 103003193344 374955 1048576 72233283 103003193344 (ep255 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz42 (@Neg.neg Real Real.instNeg (Real.sin qz43)) 280243 1048576 1 1048576 244811 262144 72233283 103003193344 68606569073 274877906944 10169568384019 54003338231939072 qz336 (@Enclosure.Real.IsNear.neg (Real.sin qz43) Bool.false 244811 262144 72233283 103003193344 (@Enclosure.Real.IsNear.recentre' (Real.sin qz43) Bool.false 979244 1048576 72233283 103003193344 244811 262144 72233283 103003193344 (ep257 rfl rfl) rfl)) rfl)

noncomputable def ep259 := @ep168 105078514065 1099511627776 40559553106269 216013352927756288 Bool.true 68606569073 274877906944 10169568384019 54003338231939072 Bool.false 1204539125352999386349568 4382087810347 1099511627776 782118133754131 216013352927756288 Bool.true 17225781726611408683008 62667028857 549755813888 48874889708261 13500834557984768 (ep169 (BSN.head_sum_c_succ qz5 13 14 rfl rfl) (ep248 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep249 ep258) rfl rfl

noncomputable abbrev qz577 := (@Nat.cast Real Real.instNatCast 15)

noncomputable abbrev qz44 := (@Inv.inv Real Real.instInv (Real.sqrt qz577))

noncomputable abbrev qz578 := (Real.log (Enclosure.sfrac Bool.false 15 1))

noncomputable abbrev qz45 := (@HMul.hMul Real Real Real qz267 qz277 qz578)

noncomputable def ep260 := @Enclosure.Complex.IsNear.of_eq qz557 (Complex.mk (@HMul.hMul Real Real Real qz0 qz44 (Real.cos qz45)) (@HMul.hMul Real Real Real qz0 qz44 (@Neg.neg Real Real.instNeg (Real.sin qz45)))) Bool.false 49258346799 549755813888 19592327787743 108006676463878144 Bool.false 133125244887 549755813888 19653185738327 108006676463878144 (BSN.cpow_neg_s_mk qz12 136442 1000 15 qz13 rfl)

noncomputable abbrev qz579 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 15) qz14)

noncomputable def ep261 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz577) 4061117 1048576 1 1048576 135370 135371 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz577) (Real.sqrt qz579) Bool.false 4061117 1048576 1 1048576 (BSN.sqrt_natCast_div_one 15) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz579) Bool.false 4061117 1048576 1 1048576 4061117 1048576 1 1048576 (BSN.sqrt_enclosure 15 1 2030558 2030559 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep262 := BSN.log_dyadic_bound 7 23 6 5 430628584065881355 524288 196463 14087658153505881 266939110305 329571 30 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 7) (BSN.artanhQ 23) 0 5 14087658153505881 430628584065881355 266939110305 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep263 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz578 136442 1000 0 1 12195965485668069 4503599627370496 1000000000589389 196463000000000000000 832020961397761335249 2251799813685248000 68221000040208706969 98231500000000000000000 qz18 (BSN.isNear_log_sfrac 15 1 12195965485668069 4503599627370496 1000000000589389 196463000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz579) Bool.false 51153586820399524478976 18889465931478580854784 1000000000589389 196463000000000000000 12195965485668069 4503599627370496 1000000000589389 196463000000000000000 (BSN.log_rat_reduce_isNear 15 1 3 30 16 329571 524288 24973259072661432 36028797018963968 196463 1000000000000000 rfl rfl rfl rfl (ep262 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep264 := nat_lit 335477230320517512955641587420276401

noncomputable def ep265 := BSN.sin_dyadic_bound_f 761054507 2147483648 2 1 1048576 393310 ep264 ep65 ep264 ep264 ep66 ep264 363878 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 761054507) qz19 0 1 ep264 ep65 ep264 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 761054507) qz20 0 1 ep264 ep66 ep264 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz337 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 387439951) qz30)

noncomputable def ep266 := @Enclosure.Real.IsNear.cos_image qz45 qz337 Bool.false 387439951 1048576 365 524288 Bool.false 363878 1048576 1 196463 (@Enclosure.Real.IsNear.recentre' qz45 Bool.false 832020961397761335249 2251799813685248000 68221000040208706969 98231500000000000000000 387439951 1048576 365 524288 (ep263 rfl) rfl) (Enclosure.sfrac_false_div 387439951 1048576) (BSN.cos_reduce3 qz337 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 53554449931662599913472) qz31) 226375608064910080 72057594037927936 Bool.false 363878 1048576 58 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q3 387439951 1048576 226375608064910080 72057594037927936 58 53554449931662599913472 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 363878 1048576 53554449931662599913472 151115727451828646838272 761054507 2147483648 393310 392926 (ep265 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep267 := BSN.cos_dyadic_bound_f 761054507 2147483648 2 1 1048576 393310 ep264 ep61 ep264 ep264 ep62 ep264 983414 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 761054507) qz15 0 1 ep264 ep61 ep264 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 761054507) qz16 0 1 ep264 ep62 ep264 rfl rfl rfl rfl) rfl rfl

noncomputable def ep268 := @Enclosure.Real.IsNear.sin_image qz45 qz337 Bool.false 387439951 1048576 365 524288 Bool.true 983414 1048576 1 196463 (@Enclosure.Real.IsNear.recentre' qz45 Bool.false 832020961397761335249 2251799813685248000 68221000040208706969 98231500000000000000000 387439951 1048576 365 524288 (ep263 rfl) rfl) (Enclosure.sfrac_false_div 387439951 1048576) (BSN.sin_reduce3 qz337 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 53554449931662599913472) qz31) 226375608064910080 72057594037927936 Bool.false 983414 1048576 58 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q3 387439951 1048576 226375608064910080 72057594037927936 58 53554449931662599913472 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 983414 1048576 53554449931662599913472 151115727451828646838272 761054507 2147483648 393310 392926 (ep267 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz338 := (@Enclosure.Real.IsNear.recentre' qz44 Bool.false 270741 1048576 1 1048576 270741 1048576 1 1048576 (ep261 rfl rfl) rfl)

noncomputable def ep269 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz44 (Real.cos qz45)) (@HMul.hMul Real Real Real qz0 qz44 (@Neg.neg Real Real.instNeg (Real.sin qz45))) Bool.false 49258346799 549755813888 19592327787743 108006676463878144 Bool.false 133125244887 549755813888 19653185738327 108006676463878144 (@Enclosure.Real.IsNear.mulLit_ff qz44 (Real.cos qz45) 270741 1048576 1 1048576 181939 524288 72233283 103003193344 49258346799 549755813888 19592327787743 108006676463878144 qz338 (@Enclosure.Real.IsNear.recentre' (Real.cos qz45) Bool.false 363878 1048576 72233283 103003193344 181939 524288 72233283 103003193344 (ep266 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz44 (@Neg.neg Real Real.instNeg (Real.sin qz45)) 270741 1048576 1 1048576 491707 524288 72233283 103003193344 133125244887 549755813888 19653185738327 108006676463878144 qz338 (@Enclosure.Real.IsNear.neg (Real.sin qz45) Bool.true 491707 524288 72233283 103003193344 (@Enclosure.Real.IsNear.recentre' (Real.sin qz45) Bool.true 983414 1048576 72233283 103003193344 491707 524288 72233283 103003193344 (ep268 rfl rfl) rfl)) rfl)

noncomputable def ep270 := @ep165 49258346799 549755813888 19592327787743 108006676463878144 Bool.false 133125244887 549755813888 19653185738327 108006676463878144 Bool.false ep166 4480604503945 1099511627776 821302789329617 216013352927756288 Bool.false 38734813898669178224640 35229108015 274877906944 410652303404415 108006676463878144 (ep167 (BSN.head_sum_c_succ qz5 14 15 rfl rfl) (ep259 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep260 ep269) rfl rfl

noncomputable abbrev qz580 := (@Nat.cast Real Real.instNatCast 16)

noncomputable abbrev qz46 := (@Inv.inv Real Real.instInv (Real.sqrt qz580))

noncomputable abbrev qz581 := (Real.log (Enclosure.sfrac Bool.false 16 1))

noncomputable abbrev qz47 := (@HMul.hMul Real Real Real qz267 qz277 qz581)

noncomputable def ep271 := @Enclosure.Complex.IsNear.of_eq qz556 (Complex.mk (@HMul.hMul Real Real Real qz0 qz46 (Real.cos qz47)) (@HMul.hMul Real Real Real qz0 qz46 (@Neg.neg Real Real.instNeg (Real.sin qz47)))) Bool.false 17956009071 274877906944 9468342596319 54003338231939072 Bool.true 265327251021 1099511627776 38018391316893 216013352927756288 (BSN.cpow_neg_s_mk qz12 136442 1000 16 qz13 rfl)

noncomputable abbrev qz582 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 16) qz14)

noncomputable def ep272 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz580) 4194305 1048576 1 1048576 131071 131072 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz580) (Real.sqrt qz582) Bool.false 4194305 1048576 1 1048576 (BSN.sqrt_natCast_div_one 16) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz582) Bool.false 4194305 1048576 1 1048576 4194305 1048576 1 1048576 (BSN.sqrt_enclosure 16 1 2097152 2097153 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep273 := BSN.log_dyadic_bound 0 32 1 0 1 524288 196463 0 1 0 32 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 0) (BSN.artanhQ 32) 0 0 rfl) rfl rfl rfl

noncomputable def ep274 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz581 136442 1000 0 1 3121657384082679 1125899906842624 250000000196463 49115750000000000000 212962588399504444059 562949953421312000 17055250013402902323 24557875000000000000000 qz18 (BSN.isNear_log_sfrac 16 1 3121657384082679 1125899906842624 250000000196463 49115750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz582) Bool.false 52372720210750067441664 18889465931478580854784 1000000000785852 196463000000000000000 3121657384082679 1125899906842624 250000000196463 49115750000000000000 (BSN.log_rat_reduce_isNear 16 1 4 32 32 0 524288 24973259072661432 36028797018963968 196463 1000000000000000 rfl rfl rfl rfl (ep273 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep275 := nat_lit 2217417822616660837282111424122068953231042396956882744751872407236856917262336

noncomputable def ep276 := nat_lit 3838245861140583134465463686262290384314080291629165633112939126200526176256

noncomputable def ep277 := nat_lit 6644576976127701345577403344993682278924499030287389902989391343458169699434496

noncomputable def ep278 := BSN.cos_dyadic_bound_f 2805540864 2147483648 3 2 1048576 393310 ep275 ep78 ep276 ep277 ep81 ep276 273988 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2805540864) qz15 0 2 ep275 ep78 ep276 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2805540864) qz16 0 2 ep277 ep81 ep276 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz339 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 99168433) qz17)

noncomputable def ep279 := @Enclosure.Real.IsNear.cos_image qz47 qz339 Bool.false 99168433 262144 729 1048576 Bool.false 273988 1048576 1 196463 (@Enclosure.Real.IsNear.recentre' qz47 Bool.false 212962588399504444059 562949953421312000 17055250013402902323 24557875000000000000000 99168433 262144 729 1048576 (ep274 rfl) rfl) (Enclosure.sfrac_false_div 99168433 262144) (BSN.cos_reduce0 qz339 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 49355596846642837323776) qz285) 226375608064910080 72057594037927936 Bool.false 273988 1048576 60 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q0 99168433 262144 226375608064910080 72057594037927936 60 49355596846642837323776 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 273988 1048576 49355596846642837323776 37778931862957161709568 2805540864 2147483648 393310 392926 (ep278 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep280 := nat_lit 3988281484021077040600228192470714283508425050289085608046879981725382030131200

noncomputable def ep281 := nat_lit 10439284821994307495544796420026493700947461858856396038621550431647866369867776

noncomputable def ep282 := BSN.sin_dyadic_bound_f 2805540864 2147483648 3 2 1048576 393310 ep280 ep109 ep276 ep281 ep112 ep276 1012147 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2805540864) qz19 0 2 ep280 ep109 ep276 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2805540864) qz20 0 2 ep281 ep112 ep276 rfl rfl rfl rfl) rfl rfl

noncomputable def ep283 := @Enclosure.Real.IsNear.sin_image qz47 qz339 Bool.false 99168433 262144 729 1048576 Bool.false 1012147 1048576 1 196463 (@Enclosure.Real.IsNear.recentre' qz47 Bool.false 212962588399504444059 562949953421312000 17055250013402902323 24557875000000000000000 99168433 262144 729 1048576 (ep274 rfl) rfl) (Enclosure.sfrac_false_div 99168433 262144) (BSN.sin_reduce0 qz339 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 49355596846642837323776) qz285) 226375608064910080 72057594037927936 Bool.false 1012147 1048576 60 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q0 99168433 262144 226375608064910080 72057594037927936 60 49355596846642837323776 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1012147 1048576 49355596846642837323776 37778931862957161709568 2805540864 2147483648 393310 392926 (ep282 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz340 := (@Enclosure.Real.IsNear.recentre' qz46 Bool.false 262143 1048576 1 1048576 262143 1048576 1 1048576 (ep272 rfl rfl) rfl)

noncomputable def ep284 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz46 (Real.cos qz47)) (@HMul.hMul Real Real Real qz0 qz46 (@Neg.neg Real Real.instNeg (Real.sin qz47))) Bool.false 17956009071 274877906944 9468342596319 54003338231939072 Bool.true 265327251021 1099511627776 38018391316893 216013352927756288 (@Enclosure.Real.IsNear.mulLit_ff qz46 (Real.cos qz47) 262143 1048576 1 1048576 68497 262144 144270103 206006386688 17956009071 274877906944 9468342596319 54003338231939072 qz340 (@Enclosure.Real.IsNear.recentre' (Real.cos qz47) Bool.false 273988 1048576 144270103 206006386688 68497 262144 144270103 206006386688 (ep279 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz46 (@Neg.neg Real Real.instNeg (Real.sin qz47)) 262143 1048576 1 1048576 1012147 1048576 144270103 206006386688 265327251021 1099511627776 38018391316893 216013352927756288 qz340 (@Enclosure.Real.IsNear.neg (Real.sin qz47) Bool.false 1012147 1048576 144270103 206006386688 (@Enclosure.Real.IsNear.recentre' (Real.sin qz47) Bool.false 1012147 1048576 144270103 206006386688 1012147 1048576 144270103 206006386688 (ep283 rfl rfl) rfl)) rfl)

noncomputable def ep285 := @ep162 17956009071 274877906944 9468342596319 54003338231939072 Bool.true 265327251021 1099511627776 38018391316893 216013352927756288 Bool.false ep163 4552428540229 1099511627776 859176159714893 216013352927756288 Bool.true 34197785517188588765184 124410818961 1099511627776 859322998125723 216013352927756288 (ep164 (BSN.head_sum_c_succ qz5 15 16 rfl rfl) (ep270 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep271 ep284) rfl rfl

theorem EMRow47.d7 : Enclosure.Complex.IsNear qz32 Bool.false 4552428540229 1099511627776 859176159714893 216013352927756288 Bool.true 124410818961 1099511627776 859322998125723 216013352927756288 := ep161 (BSN.head_sum_c_succ qz5 16 17 rfl rfl) (ep285 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable abbrev qz48 := (BSN.headSumC qz271 25)

noncomputable abbrev qz583 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 24) qz7)

noncomputable def ep286 := @Enclosure.Complex.IsNear.of_eq qz48 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 24) qz583) Bool.false 5548594187443 1099511627776 1129279422605069 216013352927756288 Bool.true 273137132885 1099511627776 1128895353157109 216013352927756288

noncomputable def ep287 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 24) qz583 Bool.false 665609730267 137438953472 549076226568405 108006676463878144 Bool.true 15948610157 68719476736 137244655593691 27001669115969536 Bool.false

noncomputable abbrev qz584 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 23) qz7)

noncomputable def ep288 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 24) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 23) qz584) Bool.false 665609730267 137438953472 549076226568405 108006676463878144 Bool.true 15948610157 68719476736 137244655593691 27001669115969536

noncomputable def ep289 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 23) qz584 Bool.false 2565088343961 549755813888 8331513365843 1687604319748096 Bool.true 67063470067 549755813888 533152340697549 108006676463878144 Bool.false

noncomputable def ep290 := nat_lit 1463691275978826930192384

noncomputable abbrev qz585 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 22) qz7)

noncomputable def ep291 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 23) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 22) qz585) Bool.false 2565088343961 549755813888 8331513365843 1687604319748096 Bool.true 67063470067 549755813888 533152340697549 108006676463878144

noncomputable def ep292 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 22) qz585 Bool.false 4962618704409 1099511627776 1033989803479409 216013352927756288 Bool.false 14905045325 549755813888 516931978078907 108006676463878144 Bool.false

noncomputable def ep293 := nat_lit 5640688920915606578921472

noncomputable abbrev qz586 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 21) qz7)

noncomputable def ep294 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 22) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 21) qz586) Bool.false 4962618704409 1099511627776 1033989803479409 216013352927756288 Bool.false 14905045325 549755813888 516931978078907 108006676463878144

noncomputable def ep295 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 21) qz586 Bool.false 4780717089493 1099511627776 1000665557272137 216013352927756288 Bool.false 46567415241 274877906944 250145849749889 54003338231939072 Bool.false

noncomputable def ep296 := nat_lit 1364114242429090944516096

noncomputable abbrev qz587 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 20) qz7)

noncomputable def ep297 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 21) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 20) qz587) Bool.false 4780717089493 1099511627776 1000665557272137 216013352927756288 Bool.false 46567415241 274877906944 250145849749889 54003338231939072

noncomputable def ep298 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 20) qz587 Bool.false 4548649989929 1099511627776 966644095788699 216013352927756288 Bool.false 267455724559 1099511627776 966688361653081 216013352927756288 Bool.false

noncomputable def ep299 := nat_lit 1314113507251247374139392

noncomputable abbrev qz588 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 19) qz7)

noncomputable def ep300 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 20) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 19) qz588) Bool.false 4548649989929 1099511627776 966644095788699 216013352927756288 Bool.false 267455724559 1099511627776 966688361653081 216013352927756288

noncomputable def ep301 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 19) qz588 Bool.false 4314280572999 1099511627776 931747071804009 216013352927756288 Bool.false 87096101527 549755813888 116488322244077 27001669115969536 Bool.false

noncomputable def ep302 := nat_lit 2500646777305060398333952

noncomputable abbrev qz589 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 18) qz7)

noncomputable def ep303 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 19) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 18) qz589) Bool.false 4314280572999 1099511627776 931747071804009 216013352927756288 Bool.false 87096101527 549755813888 116488322244077 27001669115969536

noncomputable def ep304 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 18) qz589 Bool.false 4288881359031 1099511627776 896070237197769 216013352927756288 Bool.true 83716538523 1099511627776 896044919010959 216013352927756288 Bool.false

noncomputable abbrev qz590 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 17) qz7)

noncomputable def ep305 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 18) (@HAdd.hAdd Complex Complex Complex qz4 qz32 qz590) Bool.false 4288881359031 1099511627776 896070237197769 216013352927756288 Bool.true 83716538523 1099511627776 896044919010959 216013352927756288

noncomputable def ep306 := @Enclosure.Complex.IsNear.addLitP qz32 qz590 Bool.false 4552428540229 1099511627776 859176159714893 216013352927756288 Bool.true 124410818961 1099511627776 859322998125723 216013352927756288 Bool.true

noncomputable def ep307 := nat_lit 2357837462203158944022528

noncomputable abbrev qz591 := (@Nat.cast Real Real.instNatCast 17)

noncomputable abbrev qz49 := (@Inv.inv Real Real.instInv (Real.sqrt qz591))

noncomputable abbrev qz592 := (Real.log (Enclosure.sfrac Bool.false 17 1))

noncomputable abbrev qz50 := (@HMul.hMul Real Real Real qz267 qz277 qz592)

noncomputable def ep308 := @Enclosure.Complex.IsNear.of_eq qz590 (Complex.mk (@HMul.hMul Real Real Real qz0 qz49 (Real.cos qz50)) (@HMul.hMul Real Real Real qz0 qz49 (@Neg.neg Real Real.instNeg (Real.sin qz50)))) Bool.true 131773590599 549755813888 9223519370719 54003338231939072 Bool.false 20347140219 549755813888 9180480221309 54003338231939072 (BSN.cpow_neg_s_mk qz12 136442 1000 17 qz13 rfl)

noncomputable abbrev qz593 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 17) qz14)

noncomputable def ep309 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz591) 4323389 1048576 1 1048576 127158 127159 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz591) (Real.sqrt qz593) Bool.false 4323389 1048576 1 1048576 (BSN.sqrt_natCast_div_one 17) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz593) Bool.false 4323389 1048576 1 1048576 4323389 1048576 1 1048576 (BSN.sqrt_enclosure 17 1 2161694 2161695 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep310 := BSN.log_dyadic_bound 1 33 2 1 3267 524288 196463 1 1 31784 34 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 1) (BSN.artanhQ 33) 0 1 1 3267 1 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep311 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz592 136442 1000 0 1 3189913004350711 1125899906842624 250000000196463 49115750000000000000 217619055069809855131 562949953421312000 17055250013402902323 24557875000000000000000 qz18 (BSN.isNear_log_sfrac 17 1 3189913004350711 1125899906842624 250000000196463 49115750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz593) Bool.false 53517859495200818200576 18889465931478580854784 1000000000785852 196463000000000000000 3189913004350711 1125899906842624 250000000196463 49115750000000000000 (BSN.log_rat_reduce_isNear 17 1 4 34 32 31784 524288 24973259072661432 36028797018963968 196463 1000000000000000 rfl rfl rfl rfl (ep310 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep312 := nat_lit 11715382927125475251611270423640721

noncomputable def ep313 := BSN.cos_dyadic_bound_f 328994867 2147483648 2 1 1048576 393310 ep312 ep61 ep312 ep312 ep62 ep312 1036294 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 328994867) qz15 0 1 ep312 ep61 ep312 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 328994867) qz16 0 1 ep312 ep62 ep312 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz341 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 405347077) qz30)

noncomputable def ep314 := @Enclosure.Real.IsNear.cos_image qz50 qz341 Bool.false 405347077 1048576 729 1048576 Bool.true 1036294 1048576 1 196463 (@Enclosure.Real.IsNear.recentre' qz50 Bool.false 217619055069809855131 562949953421312000 17055250013402902323 24557875000000000000000 405347077 1048576 729 1048576 (ep311 rfl) rfl) (Enclosure.sfrac_false_div 405347077 1048576) (BSN.cos_reduce2 qz341 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 23150955694728585150464) qz31) 226375608064910080 72057594037927936 Bool.false 1036294 1048576 61 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q2 405347077 1048576 226375608064910080 72057594037927936 61 23150955694728585150464 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1036294 1048576 23150955694728585150464 151115727451828646838272 328994867 2147483648 393310 392926 (ep313 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep315 := BSN.sin_dyadic_bound_f 328994867 2147483648 2 1 1048576 393310 ep312 ep65 ep312 ep312 ep66 ep312 160014 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 328994867) qz19 0 1 ep312 ep65 ep312 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 328994867) qz20 0 1 ep312 ep66 ep312 rfl rfl rfl rfl) rfl rfl

noncomputable def ep316 := @Enclosure.Real.IsNear.sin_image qz50 qz341 Bool.false 405347077 1048576 729 1048576 Bool.true 160014 1048576 1 196463 (@Enclosure.Real.IsNear.recentre' qz50 Bool.false 217619055069809855131 562949953421312000 17055250013402902323 24557875000000000000000 405347077 1048576 729 1048576 (ep311 rfl) rfl) (Enclosure.sfrac_false_div 405347077 1048576) (BSN.sin_reduce2 qz341 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 23150955694728585150464) qz31) 226375608064910080 72057594037927936 Bool.false 160014 1048576 61 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q2 405347077 1048576 226375608064910080 72057594037927936 61 23150955694728585150464 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 160014 1048576 23150955694728585150464 151115727451828646838272 328994867 2147483648 393310 392926 (ep315 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz342 := (@Enclosure.Real.IsNear.recentre' qz49 Bool.false 254317 1048576 1 1048576 254317 1048576 1 1048576 (ep309 rfl rfl) rfl)

noncomputable def ep317 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz49 (Real.cos qz50)) (@HMul.hMul Real Real Real qz0 qz49 (@Neg.neg Real Real.instNeg (Real.sin qz50))) Bool.true 131773590599 549755813888 9223519370719 54003338231939072 Bool.false 20347140219 549755813888 9180480221309 54003338231939072 (@Enclosure.Real.IsNear.mulLit_ft qz49 (Real.cos qz50) 254317 1048576 1 1048576 518147 524288 144270103 206006386688 131773590599 549755813888 9223519370719 54003338231939072 qz342 (@Enclosure.Real.IsNear.recentre' (Real.cos qz50) Bool.true 1036294 1048576 144270103 206006386688 518147 524288 144270103 206006386688 (ep314 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz49 (@Neg.neg Real Real.instNeg (Real.sin qz50)) 254317 1048576 1 1048576 80007 524288 144270103 206006386688 20347140219 549755813888 9180480221309 54003338231939072 qz342 (@Enclosure.Real.IsNear.neg (Real.sin qz50) Bool.true 80007 524288 144270103 206006386688 (@Enclosure.Real.IsNear.recentre' (Real.sin qz50) Bool.true 160014 1048576 144270103 206006386688 80007 524288 144270103 206006386688 (ep316 rfl rfl) rfl)) rfl)

noncomputable def ep318 := @ep306 131773590599 549755813888 9223519370719 54003338231939072 Bool.false 20347140219 549755813888 9180480221309 54003338231939072 Bool.false ep307 4288881359031 1099511627776 896070237197769 216013352927756288 Bool.true 46023653771597970407424 83716538523 1099511627776 896044919010959 216013352927756288 EMRow47.d7 (ep308 ep317) rfl rfl

noncomputable abbrev qz594 := (@Nat.cast Real Real.instNatCast 18)

noncomputable abbrev qz51 := (@Inv.inv Real Real.instInv (Real.sqrt qz594))

noncomputable abbrev qz595 := (Real.log (Enclosure.sfrac Bool.false 18 1))

noncomputable abbrev qz52 := (@HMul.hMul Real Real Real qz267 qz277 qz595)

noncomputable def ep319 := @Enclosure.Complex.IsNear.of_eq qz589 (Complex.mk (@HMul.hMul Real Real Real qz0 qz51 (Real.cos qz52)) (@HMul.hMul Real Real Real qz0 qz51 (@Neg.neg Real Real.instNeg (Real.sin qz52)))) Bool.false 1587450873 68719476736 1114901081445 6750417278992384 Bool.false 257908741577 1099511627776 35861658941657 216013352927756288 (BSN.cpow_neg_s_mk qz12 136442 1000 18 qz13 rfl)

noncomputable abbrev qz596 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 18) qz14)

noncomputable def ep320 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz594) 4448731 1048576 1 1048576 123575 123576 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz594) (Real.sqrt qz596) Bool.false 4448731 1048576 1 1048576 (BSN.sqrt_natCast_div_one 18) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz596) Bool.false 4448731 1048576 1 1048576 4448731 1048576 1 1048576 (BSN.sqrt_enclosure 18 1 2224365 2224366 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep321 := BSN.log_dyadic_bound 2 34 3 2 20045040 524288 196463 23168 48 61752 36 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 2) (BSN.artanhQ 34) 0 2 23168 20045040 48 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep322 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz595 136442 1000 0 1 3254268794313975 1125899906842624 250000000196463 49115750000000000000 8880378856675747539 22517998136852480 17055250013402902323 24557875000000000000000 qz18 (BSN.isNear_log_sfrac 18 1 3254268794313975 1125899906842624 250000000196463 49115750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz596) Bool.false 54597570484265130393600 18889465931478580854784 1000000000785852 196463000000000000000 3254268794313975 1125899906842624 250000000196463 49115750000000000000 (BSN.log_rat_reduce_isNear 18 1 4 36 32 61752 524288 24973259072661432 36028797018963968 196463 1000000000000000 rfl rfl rfl rfl (ep321 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep323 := BSN.sin_dyadic_bound_f 210807561 2147483648 1 0 1048576 393310 0 1 1 0 1 1 102768 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 210807561) qz19 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 210807561) qz20 0 0 rfl) rfl rfl

noncomputable abbrev qz343 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 413524865) qz30)

noncomputable def ep324 := @Enclosure.Real.IsNear.cos_image qz52 qz343 Bool.false 413524865 1048576 729 1048576 Bool.false 102768 1048576 1 196463 (@Enclosure.Real.IsNear.recentre' qz52 Bool.false 8880378856675747539 22517998136852480 17055250013402902323 24557875000000000000000 413524865 1048576 729 1048576 (ep322 rfl) rfl) (Enclosure.sfrac_false_div 413524865 1048576) (BSN.cos_reduce3 qz343 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 14834263347850064691200) qz31) 226375608064910080 72057594037927936 Bool.false 102768 1048576 62 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q3 413524865 1048576 226375608064910080 72057594037927936 62 14834263347850064691200 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 102768 1048576 14834263347850064691200 151115727451828646838272 210807561 2147483648 393310 392926 (ep323 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep325 := nat_lit 1974898292651105452769105039975841

noncomputable def ep326 := BSN.cos_dyadic_bound_f 210807561 2147483648 2 1 1048576 393310 ep325 ep61 ep325 ep325 ep62 ep325 1043527 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 210807561) qz15 0 1 ep325 ep61 ep325 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 210807561) qz16 0 1 ep325 ep62 ep325 rfl rfl rfl rfl) rfl rfl

noncomputable def ep327 := @Enclosure.Real.IsNear.sin_image qz52 qz343 Bool.false 413524865 1048576 729 1048576 Bool.true 1043527 1048576 1 196463 (@Enclosure.Real.IsNear.recentre' qz52 Bool.false 8880378856675747539 22517998136852480 17055250013402902323 24557875000000000000000 413524865 1048576 729 1048576 (ep322 rfl) rfl) (Enclosure.sfrac_false_div 413524865 1048576) (BSN.sin_reduce3 qz343 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 14834263347850064691200) qz31) 226375608064910080 72057594037927936 Bool.false 1043527 1048576 62 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q3 413524865 1048576 226375608064910080 72057594037927936 62 14834263347850064691200 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1043527 1048576 14834263347850064691200 151115727451828646838272 210807561 2147483648 393310 392926 (ep326 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz344 := (@Enclosure.Real.IsNear.recentre' qz51 Bool.false 247151 1048576 1 1048576 247151 1048576 1 1048576 (ep320 rfl rfl) rfl)

noncomputable def ep328 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz51 (Real.cos qz52)) (@HMul.hMul Real Real Real qz0 qz51 (@Neg.neg Real Real.instNeg (Real.sin qz52))) Bool.false 1587450873 68719476736 1114901081445 6750417278992384 Bool.false 257908741577 1099511627776 35861658941657 216013352927756288 (@Enclosure.Real.IsNear.mulLit_ff qz51 (Real.cos qz52) 247151 1048576 1 1048576 6423 65536 144270103 206006386688 1587450873 68719476736 1114901081445 6750417278992384 qz344 (@Enclosure.Real.IsNear.recentre' (Real.cos qz52) Bool.false 102768 1048576 144270103 206006386688 6423 65536 144270103 206006386688 (ep324 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz51 (@Neg.neg Real Real.instNeg (Real.sin qz52)) 247151 1048576 1 1048576 1043527 1048576 144270103 206006386688 257908741577 1099511627776 35861658941657 216013352927756288 qz344 (@Enclosure.Real.IsNear.neg (Real.sin qz52) Bool.true 1043527 1048576 144270103 206006386688 (@Enclosure.Real.IsNear.recentre' (Real.sin qz52) Bool.true 1043527 1048576 144270103 206006386688 1043527 1048576 144270103 206006386688 (ep327 rfl rfl) rfl)) rfl)

noncomputable def ep329 := @ep304 1587450873 68719476736 1114901081445 6750417278992384 Bool.false 257908741577 1099511627776 35861658941657 216013352927756288 Bool.false 296475103468781530251264 4314280572999 1099511627776 931747071804009 216013352927756288 Bool.false 191526352725791058427904 87096101527 549755813888 116488322244077 27001669115969536 (ep305 (BSN.head_sum_c_succ qz5 17 18 rfl rfl) (ep318 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep319 ep328) rfl rfl

noncomputable abbrev qz597 := (@Nat.cast Real Real.instNatCast 19)

noncomputable abbrev qz53 := (@Inv.inv Real Real.instInv (Real.sqrt qz597))

noncomputable abbrev qz598 := (Real.log (Enclosure.sfrac Bool.false 19 1))

noncomputable abbrev qz54 := (@HMul.hMul Real Real Real qz267 qz277 qz598)

noncomputable def ep330 := @Enclosure.Complex.IsNear.of_eq qz588 (Complex.mk (@HMul.hMul Real Real Real qz0 qz53 (Real.cos qz54)) (@HMul.hMul Real Real Real qz0 qz53 (@Neg.neg Real Real.instNeg (Real.sin qz54)))) Bool.false 117184708465 549755813888 17448511992345 108006676463878144 Bool.false 93263521505 1099511627776 34781783700465 216013352927756288 (BSN.cpow_neg_s_mk qz12 136442 1000 19 qz13 rfl)

noncomputable abbrev qz599 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 19) qz14)

noncomputable def ep331 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz597) 4570637 1048576 1 1048576 120279 120280 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz597) (Real.sqrt qz599) Bool.false 4570637 1048576 1 1048576 (BSN.sqrt_natCast_div_one 19) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz599) Bool.false 4570637 1048576 1 1048576 4570637 1048576 1 1048576 (BSN.sqrt_enclosure 19 1 2285318 2285319 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep332 := BSN.log_dyadic_bound 3 35 3 2 22509375 524288 196463 55368 243 90099 38 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 3) (BSN.artanhQ 35) 0 2 55368 22509375 243 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep333 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz598 136442 1000 0 1 3315143513283831 1125899906842624 250000000196463 49115750000000000000 226162405619736234651 562949953421312000 17055250013402902323 24557875000000000000000 qz18 (BSN.isNear_log_sfrac 19 1 3315143513283831 1125899906842624 250000000196463 49115750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz599) Bool.false 55618878793361701994496 18889465931478580854784 1000000000785852 196463000000000000000 3315143513283831 1125899906842624 250000000196463 49115750000000000000 (BSN.log_rat_reduce_isNear 19 1 4 38 32 90099 524288 24973259072661432 36028797018963968 196463 1000000000000000 rfl rfl rfl rfl (ep332 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep334 := nat_lit 2763888605976758637063693460834036870366094621263294845556061167668208850698240

noncomputable def ep335 := nat_lit 1844415430992203116217800236545567161070599824513428630363778669417632628736

noncomputable def ep336 := nat_lit 7235769676384190006311987387515689456507562084545131425340523606999585108525056

noncomputable def ep337 := BSN.sin_dyadic_bound_f 2559955072 2147483648 3 2 1048576 393310 ep334 ep109 ep335 ep336 ep112 ep335 974270 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2559955072) qz19 0 2 ep334 ep109 ep335 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2559955072) qz20 0 2 ep336 ep112 ep335 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz345 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 421260307) qz30)

noncomputable def ep338 := @Enclosure.Real.IsNear.cos_image qz54 qz345 Bool.false 421260307 1048576 729 1048576 Bool.false 974270 1048576 1 196463 (@Enclosure.Real.IsNear.recentre' qz54 Bool.false 226162405619736234651 562949953421312000 17055250013402902323 24557875000000000000000 421260307 1048576 729 1048576 (ep333 rfl) rfl) (Enclosure.sfrac_false_div 421260307 1048576) (BSN.cos_reduce3 qz345 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 180140823618640154722304) qz31) 226375608064910080 72057594037927936 Bool.false 974270 1048576 63 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q3 421260307 1048576 226375608064910080 72057594037927936 63 180140823618640154722304 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 974270 1048576 180140823618640154722304 151115727451828646838272 2559955072 2147483648 393310 392926 (ep337 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep339 := nat_lit 1536313410178640221975926500568485180052750611734947549144640105890968309334016

noncomputable def ep340 := nat_lit 4605251399673936259695343901232364405836110635555815790173192760334069662744576

noncomputable def ep341 := BSN.cos_dyadic_bound_f 2559955072 2147483648 3 2 1048576 393310 ep339 ep78 ep335 ep340 ep81 ep335 387695 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2559955072) qz15 0 2 ep339 ep78 ep335 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2559955072) qz16 0 2 ep340 ep81 ep335 rfl rfl rfl rfl) rfl rfl

noncomputable def ep342 := @Enclosure.Real.IsNear.sin_image qz54 qz345 Bool.false 421260307 1048576 729 1048576 Bool.true 387695 1048576 1 196463 (@Enclosure.Real.IsNear.recentre' qz54 Bool.false 226162405619736234651 562949953421312000 17055250013402902323 24557875000000000000000 421260307 1048576 729 1048576 (ep333 rfl) rfl) (Enclosure.sfrac_false_div 421260307 1048576) (BSN.sin_reduce3 qz345 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 180140823618640154722304) qz31) 226375608064910080 72057594037927936 Bool.false 387695 1048576 63 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q3 421260307 1048576 226375608064910080 72057594037927936 63 180140823618640154722304 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 387695 1048576 180140823618640154722304 151115727451828646838272 2559955072 2147483648 393310 392926 (ep341 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz346 := (@Enclosure.Real.IsNear.recentre' qz53 Bool.false 240559 1048576 1 1048576 240559 1048576 1 1048576 (ep331 rfl rfl) rfl)

noncomputable def ep343 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz53 (Real.cos qz54)) (@HMul.hMul Real Real Real qz0 qz53 (@Neg.neg Real Real.instNeg (Real.sin qz54))) Bool.false 117184708465 549755813888 17448511992345 108006676463878144 Bool.false 93263521505 1099511627776 34781783700465 216013352927756288 (@Enclosure.Real.IsNear.mulLit_ff qz53 (Real.cos qz54) 240559 1048576 1 1048576 487135 524288 144270103 206006386688 117184708465 549755813888 17448511992345 108006676463878144 qz346 (@Enclosure.Real.IsNear.recentre' (Real.cos qz54) Bool.false 974270 1048576 144270103 206006386688 487135 524288 144270103 206006386688 (ep338 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz53 (@Neg.neg Real Real.instNeg (Real.sin qz54)) 240559 1048576 1 1048576 387695 1048576 144270103 206006386688 93263521505 1099511627776 34781783700465 216013352927756288 qz346 (@Enclosure.Real.IsNear.neg (Real.sin qz54) Bool.true 387695 1048576 144270103 206006386688 (@Enclosure.Real.IsNear.recentre' (Real.sin qz54) Bool.true 387695 1048576 144270103 206006386688 387695 1048576 144270103 206006386688 (ep342 rfl rfl) rfl)) rfl)

noncomputable def ep344 := @ep301 117184708465 549755813888 17448511992345 108006676463878144 Bool.false 93263521505 1099511627776 34781783700465 216013352927756288 Bool.false ep302 4548649989929 1099511627776 966644095788699 216013352927756288 Bool.false 147035339533937794875392 267455724559 1099511627776 966688361653081 216013352927756288 (ep303 (BSN.head_sum_c_succ qz5 18 19 rfl rfl) (ep329 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep330 ep343) rfl rfl

noncomputable abbrev qz600 := (@Nat.cast Real Real.instNatCast 20)

noncomputable abbrev qz55 := (@Inv.inv Real Real.instInv (Real.sqrt qz600))

noncomputable abbrev qz601 := (Real.log (Enclosure.sfrac Bool.false 20 1))

noncomputable abbrev qz56 := (@HMul.hMul Real Real Real qz267 qz277 qz601)

noncomputable def ep345 := @Enclosure.Complex.IsNear.of_eq qz587 (Complex.mk (@HMul.hMul Real Real Real qz0 qz55 (Real.cos qz56)) (@HMul.hMul Real Real Real qz0 qz55 (@Neg.neg Real Real.instNeg (Real.sin qz56)))) Bool.false 58016774891 274877906944 17010730741719 108006676463878144 Bool.true 81186063595 1099511627776 33895037346475 216013352927756288 (BSN.cpow_neg_s_mk qz12 136442 1000 20 qz13 rfl)

noncomputable abbrev qz602 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 20) qz14)

noncomputable def ep346 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz600) 4689375 1048576 1 1048576 117234 117235 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz600) (Real.sqrt qz602) Bool.false 4689375 1048576 1 1048576 (BSN.sqrt_natCast_div_one 20) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz602) Bool.false 4689375 1048576 1 1048576 4689375 1048576 1 1048576 (BSN.sqrt_enclosure 20 1 2344687 2344688 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep347 := BSN.log_dyadic_bound 4 36 3 2 25194240 524288 196463 104448 768 116991 40 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 4) (BSN.artanhQ 36) 0 2 104448 25194240 768 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep348 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz601 136442 1000 0 1 3372893643545847 1125899906842624 250000000196463 49115750000000000000 230102177256341228187 562949953421312000 17055250013402902323 24557875000000000000000 qz18 (BSN.isNear_log_sfrac 20 1 3372893643545847 1125899906842624 250000000196463 49115750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz602) Bool.false 56587765202795681021952 18889465931478580854784 1000000000785852 196463000000000000000 3372893643545847 1125899906842624 250000000196463 49115750000000000000 (BSN.log_rat_reduce_isNear 20 1 4 40 32 116991 524288 24973259072661432 36028797018963968 196463 1000000000000000 rfl rfl rfl rfl (ep347 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep349 := nat_lit 272784817758766611022719489473760016

noncomputable def ep350 := BSN.cos_dyadic_bound_f 722694998 2147483648 2 1 1048576 393310 ep349 ep61 ep349 ep349 ep62 ep349 989756 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 722694998) qz15 0 1 ep349 ep61 ep349 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 722694998) qz16 0 1 ep349 ep62 ep349 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz347 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 26787419) (@Nat.cast Real Real.instNatCast 65536))

noncomputable abbrev qz603 := (@Nat.cast Real Real.instNatCast 9444732965739290427392)

noncomputable def ep351 := @Enclosure.Real.IsNear.cos_image qz56 qz347 Bool.false 26787419 65536 729 1048576 Bool.false 989756 1048576 1 196463 (@Enclosure.Real.IsNear.recentre' qz56 Bool.false 230102177256341228187 562949953421312000 17055250013402902323 24557875000000000000000 26787419 65536 729 1048576 (ep348 rfl) rfl) (Enclosure.sfrac_false_div 26787419 65536) (BSN.cos_reduce0 qz347 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 3178446214848806125568) qz603) 226375608064910080 72057594037927936 Bool.false 989756 1048576 65 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q0 26787419 65536 226375608064910080 72057594037927936 65 3178446214848806125568 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 989756 1048576 3178446214848806125568 9444732965739290427392 722694998 2147483648 393310 392926 (ep350 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep352 := BSN.sin_dyadic_bound_f 722694998 2147483648 2 1 1048576 393310 ep349 ep65 ep349 ep349 ep66 ep349 346255 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 722694998) qz19 0 1 ep349 ep65 ep349 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 722694998) qz20 0 1 ep349 ep66 ep349 rfl rfl rfl rfl) rfl rfl

noncomputable def ep353 := @Enclosure.Real.IsNear.sin_image qz56 qz347 Bool.false 26787419 65536 729 1048576 Bool.false 346255 1048576 1 196463 (@Enclosure.Real.IsNear.recentre' qz56 Bool.false 230102177256341228187 562949953421312000 17055250013402902323 24557875000000000000000 26787419 65536 729 1048576 (ep348 rfl) rfl) (Enclosure.sfrac_false_div 26787419 65536) (BSN.sin_reduce0 qz347 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 3178446214848806125568) qz603) 226375608064910080 72057594037927936 Bool.false 346255 1048576 65 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q0 26787419 65536 226375608064910080 72057594037927936 65 3178446214848806125568 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 346255 1048576 3178446214848806125568 9444732965739290427392 722694998 2147483648 393310 392926 (ep352 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz348 := (@Enclosure.Real.IsNear.recentre' qz55 Bool.false 234469 1048576 1 1048576 234469 1048576 1 1048576 (ep346 rfl rfl) rfl)

noncomputable def ep354 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz55 (Real.cos qz56)) (@HMul.hMul Real Real Real qz0 qz55 (@Neg.neg Real Real.instNeg (Real.sin qz56))) Bool.false 58016774891 274877906944 17010730741719 108006676463878144 Bool.true 81186063595 1099511627776 33895037346475 216013352927756288 (@Enclosure.Real.IsNear.mulLit_ff qz55 (Real.cos qz56) 234469 1048576 1 1048576 247439 262144 144270103 206006386688 58016774891 274877906944 17010730741719 108006676463878144 qz348 (@Enclosure.Real.IsNear.recentre' (Real.cos qz56) Bool.false 989756 1048576 144270103 206006386688 247439 262144 144270103 206006386688 (ep351 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz55 (@Neg.neg Real Real.instNeg (Real.sin qz56)) 234469 1048576 1 1048576 346255 1048576 144270103 206006386688 81186063595 1099511627776 33895037346475 216013352927756288 qz348 (@Enclosure.Real.IsNear.neg (Real.sin qz56) Bool.false 346255 1048576 144270103 206006386688 (@Enclosure.Real.IsNear.recentre' (Real.sin qz56) Bool.false 346255 1048576 144270103 206006386688 346255 1048576 144270103 206006386688 (ep353 rfl rfl) rfl)) rfl)

noncomputable def ep355 := @ep298 58016774891 274877906944 17010730741719 108006676463878144 Bool.true 81186063595 1099511627776 33895037346475 216013352927756288 Bool.false ep299 4780717089493 1099511627776 1000665557272137 216013352927756288 Bool.false 204805658131811285336064 46567415241 274877906944 250145849749889 54003338231939072 (ep300 (BSN.head_sum_c_succ qz5 19 20 rfl rfl) (ep344 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep345 ep354) rfl rfl

noncomputable abbrev qz604 := (@Nat.cast Real Real.instNatCast 21)

noncomputable abbrev qz57 := (@Inv.inv Real Real.instInv (Real.sqrt qz604))

noncomputable abbrev qz605 := (Real.log (Enclosure.sfrac Bool.false 21 1))

noncomputable abbrev qz58 := (@HMul.hMul Real Real Real qz267 qz277 qz605)

noncomputable def ep356 := @Enclosure.Complex.IsNear.of_eq qz586 (Complex.mk (@HMul.hMul Real Real Real qz0 qz57 (Real.cos qz58)) (@HMul.hMul Real Real Real qz0 qz57 (@Neg.neg Real Real.instNeg (Real.sin qz58)))) Bool.false 45475403729 274877906944 4165530775909 27001669115969536 Bool.true 78229785157 549755813888 16640278579129 108006676463878144 (BSN.cpow_neg_s_mk qz12 136442 1000 21 qz13 rfl)

noncomputable abbrev qz606 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 21) qz14)

noncomputable def ep357 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz604) 4805179 1048576 1 1048576 114408 114410 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz604) (Real.sqrt qz606) Bool.false 4805179 1048576 1 1048576 (BSN.sqrt_natCast_div_one 21) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz606) Bool.false 4805179 1048576 1 1048576 4805179 1048576 1 1048576 (BSN.sqrt_enclosure 21 1 2402589 2402590 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep358 := BSN.log_dyadic_bound 5 37 4 3 269401272945 524288 196463 1658093375 234375 142571 42 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 5) (BSN.artanhQ 37) 0 3 1658093375 269401272945 234375 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep359 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz605 136442 1000 0 1 3427826275261687 1125899906842624 250000000196463 49115750000000000000 233849736324627548827 562949953421312000 17055250013402902323 24557875000000000000000 qz18 (BSN.isNear_log_sfrac 21 1 3427826275261687 1125899906842624 250000000196463 49115750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz606) Bool.false 57509381830540779323392 18889465931478580854784 1000000000785852 196463000000000000000 3427826275261687 1125899906842624 250000000196463 49115750000000000000 (BSN.log_rat_reduce_isNear 21 1 4 42 32 142571 524288 24973259072661432 36028797018963968 196463 1000000000000000 rfl rfl rfl rfl (ep358 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep360 := nat_lit 193508131521247856950787472103272416552670685790600878379700894346664163716641

noncomputable def ep361 := nat_lit 29323062099879836172333825778493563401854981705936684108724455433748131361

noncomputable def ep362 := nat_lit 580465748439543811180017748658260262531208347408390761770885234129124994887201

noncomputable def ep363 := BSN.cos_dyadic_bound_f 1525461197 2147483648 3 2 1048576 393310 ep360 ep78 ep361 ep362 ep81 ep361 794962 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1525461197) qz15 0 2 ep360 ep78 ep361 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1525461197) qz16 0 2 ep362 ep81 ep361 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz349 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 435579077) qz30)

noncomputable def ep364 := @Enclosure.Real.IsNear.cos_image qz58 qz349 Bool.false 435579077 1048576 729 1048576 Bool.false 794962 1048576 1 196463 (@Enclosure.Real.IsNear.recentre' qz58 Bool.false 233849736324627548827 562949953421312000 17055250013402902323 24557875000000000000000 435579077 1048576 729 1048576 (ep359 rfl) rfl) (Enclosure.sfrac_false_div 435579077 1048576) (BSN.cos_reduce0 qz349 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 107344788763122570625024) qz31) 226375608064910080 72057594037927936 Bool.false 794962 1048576 66 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q0 435579077 1048576 226375608064910080 72057594037927936 66 107344788763122570625024 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 794962 1048576 107344788763122570625024 151115727451828646838272 1525461197 2147483648 393310 392926 (ep363 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep365 := nat_lit 5415077293989425242018873567807950481

noncomputable def ep366 := BSN.sin_dyadic_bound_f 1525461197 2147483648 2 1 1048576 393310 ep365 ep65 ep365 ep365 ep66 ep365 683773 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1525461197) qz19 0 1 ep365 ep65 ep365 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1525461197) qz20 0 1 ep365 ep66 ep365 rfl rfl rfl rfl) rfl rfl

noncomputable def ep367 := @Enclosure.Real.IsNear.sin_image qz58 qz349 Bool.false 435579077 1048576 729 1048576 Bool.false 683773 1048576 1 196463 (@Enclosure.Real.IsNear.recentre' qz58 Bool.false 233849736324627548827 562949953421312000 17055250013402902323 24557875000000000000000 435579077 1048576 729 1048576 (ep359 rfl) rfl) (Enclosure.sfrac_false_div 435579077 1048576) (BSN.sin_reduce0 qz349 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 107344788763122570625024) qz31) 226375608064910080 72057594037927936 Bool.false 683773 1048576 66 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q0 435579077 1048576 226375608064910080 72057594037927936 66 107344788763122570625024 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 683773 1048576 107344788763122570625024 151115727451828646838272 1525461197 2147483648 393310 392926 (ep366 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz350 := (@Enclosure.Real.IsNear.recentre' qz57 Bool.false 228818 1048576 2 1048576 114409 524288 1 524288 (ep357 rfl rfl) rfl)

noncomputable def ep368 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz57 (Real.cos qz58)) (@HMul.hMul Real Real Real qz0 qz57 (@Neg.neg Real Real.instNeg (Real.sin qz58))) Bool.false 45475403729 274877906944 4165530775909 27001669115969536 Bool.true 78229785157 549755813888 16640278579129 108006676463878144 (@Enclosure.Real.IsNear.mulLit_ff qz57 (Real.cos qz58) 114409 524288 1 524288 397481 524288 144270103 206006386688 45475403729 274877906944 4165530775909 27001669115969536 qz350 (@Enclosure.Real.IsNear.recentre' (Real.cos qz58) Bool.false 794962 1048576 144270103 206006386688 397481 524288 144270103 206006386688 (ep364 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz57 (@Neg.neg Real Real.instNeg (Real.sin qz58)) 114409 524288 1 524288 683773 1048576 144270103 206006386688 78229785157 549755813888 16640278579129 108006676463878144 qz350 (@Enclosure.Real.IsNear.neg (Real.sin qz58) Bool.false 683773 1048576 144270103 206006386688 (@Enclosure.Real.IsNear.recentre' (Real.sin qz58) Bool.false 683773 1048576 144270103 206006386688 683773 1048576 144270103 206006386688 (ep367 rfl rfl) rfl)) rfl)

noncomputable def ep369 := @ep295 45475403729 274877906944 4165530775909 27001669115969536 Bool.true 78229785157 549755813888 16640278579129 108006676463878144 Bool.false ep296 4962618704409 1099511627776 1033989803479409 216013352927756288 Bool.false 4097067661841452236800 14905045325 549755813888 516931978078907 108006676463878144 (ep297 (BSN.head_sum_c_succ qz5 20 21 rfl rfl) (ep355 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep356 ep368) rfl rfl

noncomputable abbrev qz607 := (@Nat.cast Real Real.instNatCast 22)

noncomputable abbrev qz59 := (@Inv.inv Real Real.instInv (Real.sqrt qz607))

noncomputable abbrev qz608 := (Real.log (Enclosure.sfrac Bool.false 22 1))

noncomputable abbrev qz60 := (@HMul.hMul Real Real Real qz267 qz277 qz608)

noncomputable def ep370 := @Enclosure.Complex.IsNear.of_eq qz585 (Complex.mk (@HMul.hMul Real Real Real qz0 qz59 (Real.cos qz60)) (@HMul.hMul Real Real Real qz0 qz59 (@Neg.neg Real Real.instNeg (Real.sin qz60)))) Bool.false 167557983513 1099511627776 32443907348495 216013352927756288 Bool.true 1280758053 8589934592 8110181309321 54003338231939072 (BSN.cpow_neg_s_mk qz12 136442 1000 22 qz13 rfl)

noncomputable abbrev qz609 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 22) qz14)

noncomputable def ep371 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz607) 4918257 1048576 1 1048576 111778 111779 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz607) (Real.sqrt qz609) Bool.false 4918257 1048576 1 1048576 (BSN.sqrt_natCast_div_one 22) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz609) Bool.false 4918257 1048576 1 1048576 4918257 1048576 1 1048576 (BSN.sqrt_enclosure 22 1 2459128 2459129 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep372 := BSN.log_dyadic_bound 6 38 4 3 316148320320 524288 196463 2667271104 699840 166961 44 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 6) (BSN.artanhQ 38) 0 3 2667271104 316148320320 699840 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep373 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz608 136442 1000 0 1 3480203401436407 1125899906842624 250000000196463 49115750000000000000 237422956249393121947 562949953421312000 17055250013402902323 24557875000000000000000 qz18 (BSN.isNear_log_sfrac 22 1 3480203401436407 1125899906842624 250000000196463 49115750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz609) Bool.false 58388124189833310502912 18889465931478580854784 1000000000785852 196463000000000000000 3480203401436407 1125899906842624 250000000196463 49115750000000000000 (BSN.log_rat_reduce_isNear 22 1 4 44 32 166961 524288 24973259072661432 36028797018963968 196463 1000000000000000 rfl rfl rfl rfl (ep372 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep374 := nat_lit 273446714889077401244435136413407185769637819188023327388082569647265384005601

noncomputable def ep375 := nat_lit 58546635456168549874515476835956924203071754258004582140550469794178301921

noncomputable def ep376 := nat_lit 820223051396319866633556378286549643460507314055553972999966608002207795412961

noncomputable def ep377 := BSN.cos_dyadic_bound_f 1663174213 2147483648 3 2 1048576 393310 ep374 ep78 ep375 ep376 ep81 ep375 749509 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1663174213) qz15 0 2 ep374 ep78 ep375 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1663174213) qz16 0 2 ep376 ep81 ep375 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz351 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 442234717) qz30)

noncomputable def ep378 := @Enclosure.Real.IsNear.cos_image qz60 qz351 Bool.false 442234717 1048576 365 524288 Bool.false 749509 1048576 1 196463 (@Enclosure.Real.IsNear.recentre' qz60 Bool.false 237422956249393121947 562949953421312000 17055250013402902323 24557875000000000000000 442234717 1048576 365 524288 (ep373 rfl) rfl) (Enclosure.sfrac_false_div 442234717 1048576) (BSN.cos_reduce0 qz351 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 117035480719227338358784) qz31) 226375608064910080 72057594037927936 Bool.false 749509 1048576 67 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q0 442234717 1048576 226375608064910080 72057594037927936 67 117035480719227338358784 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 749509 1048576 117035480719227338358784 151115727451828646838272 1663174213 2147483648 393310 392926 (ep377 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep379 := nat_lit 7651577318185352420330931910229858161

noncomputable def ep380 := BSN.sin_dyadic_bound_f 1663174213 2147483648 2 1 1048576 393310 ep379 ep65 ep379 ep379 ep66 ep379 733312 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1663174213) qz19 0 1 ep379 ep65 ep379 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1663174213) qz20 0 1 ep379 ep66 ep379 rfl rfl rfl rfl) rfl rfl

noncomputable def ep381 := @Enclosure.Real.IsNear.sin_image qz60 qz351 Bool.false 442234717 1048576 365 524288 Bool.false 733312 1048576 1 196463 (@Enclosure.Real.IsNear.recentre' qz60 Bool.false 237422956249393121947 562949953421312000 17055250013402902323 24557875000000000000000 442234717 1048576 365 524288 (ep373 rfl) rfl) (Enclosure.sfrac_false_div 442234717 1048576) (BSN.sin_reduce0 qz351 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 117035480719227338358784) qz31) 226375608064910080 72057594037927936 Bool.false 733312 1048576 67 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q0 442234717 1048576 226375608064910080 72057594037927936 67 117035480719227338358784 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 733312 1048576 117035480719227338358784 151115727451828646838272 1663174213 2147483648 393310 392926 (ep380 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz352 := (@Enclosure.Real.IsNear.recentre' qz59 Bool.false 223557 1048576 1 1048576 223557 1048576 1 1048576 (ep371 rfl rfl) rfl)

noncomputable def ep382 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz59 (Real.cos qz60)) (@HMul.hMul Real Real Real qz0 qz59 (@Neg.neg Real Real.instNeg (Real.sin qz60))) Bool.false 167557983513 1099511627776 32443907348495 216013352927756288 Bool.true 1280758053 8589934592 8110181309321 54003338231939072 (@Enclosure.Real.IsNear.mulLit_ff qz59 (Real.cos qz60) 223557 1048576 1 1048576 749509 1048576 72233283 103003193344 167557983513 1099511627776 32443907348495 216013352927756288 qz352 (@Enclosure.Real.IsNear.recentre' (Real.cos qz60) Bool.false 749509 1048576 72233283 103003193344 749509 1048576 72233283 103003193344 (ep378 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz59 (@Neg.neg Real Real.instNeg (Real.sin qz60)) 223557 1048576 1 1048576 5729 8192 72233283 103003193344 1280758053 8589934592 8110181309321 54003338231939072 qz352 (@Enclosure.Real.IsNear.neg (Real.sin qz60) Bool.false 5729 8192 72233283 103003193344 (@Enclosure.Real.IsNear.recentre' (Real.sin qz60) Bool.false 733312 1048576 72233283 103003193344 5729 8192 72233283 103003193344 (ep381 rfl rfl) rfl)) rfl)

noncomputable def ep383 := @ep292 167557983513 1099511627776 32443907348495 216013352927756288 Bool.true 1280758053 8589934592 8110181309321 54003338231939072 Bool.false ep293 2565088343961 549755813888 8331513365843 1687604319748096 Bool.true 576070821388079857664 67063470067 549755813888 533152340697549 108006676463878144 (ep294 (BSN.head_sum_c_succ qz5 21 22 rfl rfl) (ep369 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep370 ep382) rfl rfl

noncomputable abbrev qz610 := (@Nat.cast Real Real.instNatCast 23)

noncomputable abbrev qz61 := (@Inv.inv Real Real.instInv (Real.sqrt qz610))

noncomputable abbrev qz611 := (Real.log (Enclosure.sfrac Bool.false 23 1))

noncomputable abbrev qz62 := (@HMul.hMul Real Real Real qz267 qz277 qz611)

noncomputable def ep384 := @Enclosure.Complex.IsNear.of_eq qz584 (Complex.mk (@HMul.hMul Real Real Real qz0 qz61 (Real.cos qz62)) (@HMul.hMul Real Real Real qz0 qz61 (@Neg.neg Real Real.instNeg (Real.sin qz62)))) Bool.false 97350577107 549755813888 15859371154453 108006676463878144 Bool.true 60525411189 549755813888 15826281677215 108006676463878144 (BSN.cpow_neg_s_mk qz12 136442 1000 23 qz13 rfl)

noncomputable abbrev qz612 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 23) qz14)

noncomputable def ep385 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz610) 5028793 1048576 1 1048576 109321 109322 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz610) (Real.sqrt qz612) Bool.false 5028793 1048576 1 1048576 (BSN.sqrt_natCast_div_one 23) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz612) Bool.false 5028793 1048576 1 1048576 5028793 1048576 1 1048576 (BSN.sqrt_enclosure 23 1 2514396 2514397 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep386 := BSN.log_dyadic_bound 7 39 4 3 369468094905 524288 196463 4046006391 1764735 190266 46 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 7) (BSN.artanhQ 39) 0 3 4046006391 369468094905 1764735 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep387 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz611 136442 1000 0 1 3530250507853047 1125899906842624 250000000196463 49115750000000000000 240837219896242719387 562949953421312000 17055250013402902323 24557875000000000000000 qz18 (BSN.isNear_log_sfrac 23 1 3530250507853047 1125899906842624 250000000196463 49115750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz612) Bool.false 59227775304360265777152 18889465931478580854784 1000000000785852 196463000000000000000 3530250507853047 1125899906842624 250000000196463 49115750000000000000 (BSN.log_rat_reduce_isNear 23 1 4 46 32 190266 524288 24973259072661432 36028797018963968 196463 1000000000000000 rfl rfl rfl rfl (ep386 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep388 := nat_lit 2035977395687974993810609851556577536

noncomputable def ep389 := BSN.cos_dyadic_bound_f 1194519484 2147483648 2 1 1048576 393310 ep388 ep61 ep388 ep388 ep62 ep388 890498 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1194519484) qz15 0 1 ep388 ep61 ep388 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1194519484) qz16 0 1 ep388 ep62 ep388 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz353 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 448594279) qz30)

noncomputable def ep390 := @Enclosure.Real.IsNear.cos_image qz62 qz353 Bool.false 448594279 1048576 729 1048576 Bool.false 890498 1048576 1 196463 (@Enclosure.Real.IsNear.recentre' qz62 Bool.false 240837219896242719387 562949953421312000 17055250013402902323 24557875000000000000000 448594279 1048576 729 1048576 (ep387 rfl) rfl) (Enclosure.sfrac_false_div 448594279 1048576) (BSN.cos_reduce0 qz353 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 84056836020208851222528) qz31) 226375608064910080 72057594037927936 Bool.false 890498 1048576 68 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q0 448594279 1048576 226375608064910080 72057594037927936 68 84056836020208851222528 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 890498 1048576 84056836020208851222528 151115727451828646838272 1194519484 2147483648 393310 392926 (ep389 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep391 := BSN.sin_dyadic_bound_f 1194519484 2147483648 2 1 1048576 393310 ep388 ep65 ep388 ep388 ep66 ep388 553646 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1194519484) qz19 0 1 ep388 ep65 ep388 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1194519484) qz20 0 1 ep388 ep66 ep388 rfl rfl rfl rfl) rfl rfl

noncomputable def ep392 := @Enclosure.Real.IsNear.sin_image qz62 qz353 Bool.false 448594279 1048576 729 1048576 Bool.false 553646 1048576 1 196463 (@Enclosure.Real.IsNear.recentre' qz62 Bool.false 240837219896242719387 562949953421312000 17055250013402902323 24557875000000000000000 448594279 1048576 729 1048576 (ep387 rfl) rfl) (Enclosure.sfrac_false_div 448594279 1048576) (BSN.sin_reduce0 qz353 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 84056836020208851222528) qz31) 226375608064910080 72057594037927936 Bool.false 553646 1048576 68 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q0 448594279 1048576 226375608064910080 72057594037927936 68 84056836020208851222528 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 553646 1048576 84056836020208851222528 151115727451828646838272 1194519484 2147483648 393310 392926 (ep391 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz354 := (@Enclosure.Real.IsNear.recentre' qz61 Bool.false 218643 1048576 1 1048576 218643 1048576 1 1048576 (ep385 rfl rfl) rfl)

noncomputable def ep393 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz61 (Real.cos qz62)) (@HMul.hMul Real Real Real qz0 qz61 (@Neg.neg Real Real.instNeg (Real.sin qz62))) Bool.false 97350577107 549755813888 15859371154453 108006676463878144 Bool.true 60525411189 549755813888 15826281677215 108006676463878144 (@Enclosure.Real.IsNear.mulLit_ff qz61 (Real.cos qz62) 218643 1048576 1 1048576 445249 524288 144270103 206006386688 97350577107 549755813888 15859371154453 108006676463878144 qz354 (@Enclosure.Real.IsNear.recentre' (Real.cos qz62) Bool.false 890498 1048576 144270103 206006386688 445249 524288 144270103 206006386688 (ep390 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz61 (@Neg.neg Real Real.instNeg (Real.sin qz62)) 218643 1048576 1 1048576 276823 524288 144270103 206006386688 60525411189 549755813888 15826281677215 108006676463878144 qz354 (@Enclosure.Real.IsNear.neg (Real.sin qz62) Bool.false 276823 524288 144270103 206006386688 (@Enclosure.Real.IsNear.recentre' (Real.sin qz62) Bool.false 553646 1048576 144270103 206006386688 276823 524288 144270103 206006386688 (ep392 rfl rfl) rfl)) rfl)

noncomputable def ep394 := @ep289 97350577107 549755813888 15859371154453 108006676463878144 Bool.true 60525411189 549755813888 15826281677215 108006676463878144 Bool.false ep290 665609730267 137438953472 549076226568405 108006676463878144 Bool.true 70142729257951667683328 15948610157 68719476736 137244655593691 27001669115969536 (ep291 (BSN.head_sum_c_succ qz5 22 23 rfl rfl) (ep383 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep384 ep393) rfl rfl

noncomputable abbrev qz613 := (@Nat.cast Real Real.instNatCast 24)

noncomputable abbrev qz63 := (@Inv.inv Real Real.instInv (Real.sqrt qz613))

noncomputable abbrev qz614 := (Real.log (Enclosure.sfrac Bool.false 24 1))

noncomputable abbrev qz64 := (@HMul.hMul Real Real Real qz267 qz277 qz614)

noncomputable def ep395 := @Enclosure.Complex.IsNear.of_eq qz583 (Complex.mk (@HMul.hMul Real Real Real qz0 qz63 (Real.cos qz64)) (@HMul.hMul Real Real Real qz0 qz63 (@Neg.neg Real Real.instNeg (Real.sin qz64)))) Bool.false 223716345307 1099511627776 31126969468259 216013352927756288 Bool.true 17959370373 1099511627776 30938108407581 216013352927756288 (BSN.cpow_neg_s_mk qz12 136442 1000 24 qz13 rfl)

noncomputable abbrev qz615 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 24) qz14)

noncomputable def ep396 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz613) 5136953 1048576 1 1048576 107019 107020 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz613) (Real.sqrt qz615) Bool.false 5136953 1048576 1 1048576 (BSN.sqrt_natCast_div_one 24) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz615) Bool.false 5136953 1048576 1 1048576 5136953 1048576 1 1048576 (BSN.sqrt_enclosure 24 1 2568476 2568477 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep397 := BSN.log_dyadic_bound 8 40 4 3 430080000000 524288 196463 5875957760 3932160 212580 48 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 8) (BSN.artanhQ 40) 0 3 5875957760 430080000000 3932160 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep398 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz614 136442 1000 0 1 3578169457974519 1125899906842624 250000000196463 49115750000000000000 244106298592479660699 562949953421312000 17055250013402902323 24557875000000000000000 qz18 (BSN.isNear_log_sfrac 24 1 3578169457974519 1125899906842624 250000000196463 49115750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz615) Bool.false 60031721881041427759104 18889465931478580854784 1000000000785852 196463000000000000000 3578169457974519 1125899906842624 250000000196463 49115750000000000000 (BSN.log_rat_reduce_isNear 24 1 4 48 32 212580 524288 24973259072661432 36028797018963968 196463 1000000000000000 rfl rfl rfl rfl (ep397 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep399 := nat_lit 875745693774361621130136903599761

noncomputable def ep400 := BSN.cos_dyadic_bound_f 172026163 2147483648 2 1 1048576 393310 ep399 ep61 ep399 ep399 ep62 ep399 1045213 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 172026163) qz15 0 1 ep399 ep61 ep399 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 172026163) qz16 0 1 ep399 ep62 ep399 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz355 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 113670853) qz17)

noncomputable def ep401 := @Enclosure.Real.IsNear.cos_image qz64 qz355 Bool.false 113670853 262144 365 524288 Bool.false 1045213 1048576 1 196463 (@Enclosure.Real.IsNear.recentre' qz64 Bool.false 244106298592479660699 562949953421312000 17055250013402902323 24557875000000000000000 113670853 262144 365 524288 (ep398 rfl) rfl) (Enclosure.sfrac_false_div 113670853 262144) (BSN.cos_reduce0 qz355 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 3026316281256184119296) qz285) 226375608064910080 72057594037927936 Bool.false 1045213 1048576 69 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q0 113670853 262144 226375608064910080 72057594037927936 69 3026316281256184119296 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1045213 1048576 3026316281256184119296 37778931862957161709568 172026163 2147483648 393310 392926 (ep400 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep402 := BSN.sin_dyadic_bound_f 172026163 2147483648 1 0 1048576 393310 0 1 1 0 1 1 83907 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 172026163) qz19 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 172026163) qz20 0 0 rfl) rfl rfl

noncomputable def ep403 := @Enclosure.Real.IsNear.sin_image qz64 qz355 Bool.false 113670853 262144 365 524288 Bool.false 83907 1048576 1 196463 (@Enclosure.Real.IsNear.recentre' qz64 Bool.false 244106298592479660699 562949953421312000 17055250013402902323 24557875000000000000000 113670853 262144 365 524288 (ep398 rfl) rfl) (Enclosure.sfrac_false_div 113670853 262144) (BSN.sin_reduce0 qz355 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 3026316281256184119296) qz285) 226375608064910080 72057594037927936 Bool.false 83907 1048576 69 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q0 113670853 262144 226375608064910080 72057594037927936 69 3026316281256184119296 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 83907 1048576 3026316281256184119296 37778931862957161709568 172026163 2147483648 393310 392926 (ep402 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz356 := (@Enclosure.Real.IsNear.recentre' qz63 Bool.false 214039 1048576 1 1048576 214039 1048576 1 1048576 (ep396 rfl rfl) rfl)

noncomputable def ep404 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz63 (Real.cos qz64)) (@HMul.hMul Real Real Real qz0 qz63 (@Neg.neg Real Real.instNeg (Real.sin qz64))) Bool.false 223716345307 1099511627776 31126969468259 216013352927756288 Bool.true 17959370373 1099511627776 30938108407581 216013352927756288 (@Enclosure.Real.IsNear.mulLit_ff qz63 (Real.cos qz64) 214039 1048576 1 1048576 1045213 1048576 72233283 103003193344 223716345307 1099511627776 31126969468259 216013352927756288 qz356 (@Enclosure.Real.IsNear.recentre' (Real.cos qz64) Bool.false 1045213 1048576 72233283 103003193344 1045213 1048576 72233283 103003193344 (ep401 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz63 (@Neg.neg Real Real.instNeg (Real.sin qz64)) 214039 1048576 1 1048576 83907 1048576 72233283 103003193344 17959370373 1099511627776 30938108407581 216013352927756288 qz356 (@Enclosure.Real.IsNear.neg (Real.sin qz64) Bool.false 83907 1048576 72233283 103003193344 (@Enclosure.Real.IsNear.recentre' (Real.sin qz64) Bool.false 83907 1048576 72233283 103003193344 83907 1048576 72233283 103003193344 (ep403 rfl rfl) rfl)) rfl)

noncomputable def ep405 := @ep287 223716345307 1099511627776 31126969468259 216013352927756288 Bool.true 17959370373 1099511627776 30938108407581 216013352927756288 Bool.false 762592978362988123652096 5548594187443 1099511627776 1129279422605069 216013352927756288 Bool.true 18769840849028498063360 273137132885 1099511627776 1128895353157109 216013352927756288 (ep288 (BSN.head_sum_c_succ qz5 23 24 rfl rfl) (ep394 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep395 ep404) rfl rfl

theorem EMRow47.d8 : Enclosure.Complex.IsNear qz48 Bool.false 5548594187443 1099511627776 1129279422605069 216013352927756288 Bool.true 273137132885 1099511627776 1128895353157109 216013352927756288 := ep286 (BSN.head_sum_c_succ qz5 24 25 rfl rfl) (ep405 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable abbrev qz65 := (BSN.headSumC qz271 33)

noncomputable abbrev qz616 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 32) qz7)

noncomputable def ep406 := @Enclosure.Complex.IsNear.of_eq qz65 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 32) qz616) Bool.false 5485948446639 1099511627776 1357569411645329 216013352927756288 Bool.true 22980239781 274877906944 21209302815645 3375208639496192

noncomputable def ep407 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 32) qz616 Bool.false 5498038562951 1099511627776 1330814114170125 216013352927756288 Bool.false 25517394087 274877906944 332611822413729 54003338231939072 Bool.true

noncomputable abbrev qz617 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 31) qz7)

noncomputable def ep408 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 32) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 31) qz617) Bool.false 5498038562951 1099511627776 1330814114170125 216013352927756288 Bool.false 25517394087 274877906944 332611822413729 54003338231939072

noncomputable def ep409 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 31) qz617 Bool.false 5676478407161 1099511627776 1303457578944265 216013352927756288 Bool.false 8737036419 549755813888 325797162985489 54003338231939072 Bool.true

noncomputable def ep410 := nat_lit 3022578664962736928063488

noncomputable abbrev qz618 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 30) qz7)

noncomputable def ep411 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 31) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 30) qz618) Bool.false 5676478407161 1099511627776 1303457578944265 216013352927756288 Bool.false 8737036419 549755813888 325797162985489 54003338231939072

noncomputable def ep412 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 30) qz618 Bool.false 5550096544939 1099511627776 1275708237510231 216013352927756288 Bool.true 17311386661 137438953472 637704475736729 108006676463878144 Bool.false

noncomputable def ep413 := nat_lit 3120677006746453402451968

noncomputable abbrev qz619 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 29) qz7)

noncomputable def ep414 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 30) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 29) qz619) Bool.false 5550096544939 1099511627776 1275708237510231 216013352927756288 Bool.true 17311386661 137438953472 637704475736729 108006676463878144

noncomputable def ep415 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 29) qz619 Bool.false 1350802980421 274877906944 311857520601421 54003338231939072 Bool.false 3324319657 1099511627776 1247135911086653 216013352927756288 Bool.false

noncomputable def ep416 := nat_lit 1525598921609958356156416

noncomputable abbrev qz620 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 28) qz7)

noncomputable def ep417 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 29) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 28) qz620) Bool.false 1350802980421 274877906944 311857520601421 54003338231939072 Bool.false 3324319657 1099511627776 1247135911086653 216013352927756288

noncomputable def ep418 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 28) qz620 Bool.false 5535843804725 1099511627776 1218670515759719 216013352927756288 Bool.false 81638665917 549755813888 4759176787867 843802159874048 Bool.true

noncomputable def ep419 := nat_lit 5940894335229463871094784

noncomputable abbrev qz621 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 27) qz7)

noncomputable def ep420 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 28) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 27) qz621) Bool.false 5535843804725 1099511627776 1218670515759719 216013352927756288 Bool.false 81638665917 549755813888 4759176787867 843802159874048

noncomputable def ep421 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 27) qz621 Bool.false 5727052393205 1099511627776 1189370656352559 216013352927756288 Bool.false 36321875281 549755813888 74321707117143 13500834557984768 Bool.true

noncomputable abbrev qz622 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 26) qz7)

noncomputable def ep422 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 27) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 26) qz622) Bool.false 5727052393205 1099511627776 1189370656352559 216013352927756288 Bool.false 36321875281 549755813888 74321707117143 13500834557984768

noncomputable def ep423 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 26) qz622 Bool.false 715730427251 137438953472 579850610142625 108006676463878144 Bool.true 142985067875 1099511627776 1159273029766139 216013352927756288 Bool.false

noncomputable abbrev qz623 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 25) qz7)

noncomputable def ep424 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 26) (@HAdd.hAdd Complex Complex Complex qz4 qz48 qz623) Bool.false 715730427251 137438953472 579850610142625 108006676463878144 Bool.true 142985067875 1099511627776 1159273029766139 216013352927756288

noncomputable def ep425 := @Enclosure.Complex.IsNear.addLitP qz48 qz623 Bool.false 5548594187443 1099511627776 1129279422605069 216013352927756288 Bool.true 273137132885 1099511627776 1128895353157109 216013352927756288 Bool.false

noncomputable def ep426 := nat_lit 6295631416924471671390208

noncomputable abbrev qz624 := (@Nat.cast Real Real.instNatCast 25)

noncomputable abbrev qz66 := (@Inv.inv Real Real.instInv (Real.sqrt qz624))

noncomputable abbrev qz625 := (Real.log (Enclosure.sfrac Bool.false 25 1))

noncomputable abbrev qz67 := (@HMul.hMul Real Real Real qz267 qz277 qz625)

noncomputable def ep427 := @Enclosure.Complex.IsNear.of_eq qz623 (Complex.mk (@HMul.hMul Real Real Real qz0 qz66 (Real.cos qz67)) (@HMul.hMul Real Real Real qz0 qz66 (@Neg.neg Real Real.instNeg (Real.sin qz67)))) Bool.false 177249230565 1099511627776 30421797680181 216013352927756288 Bool.false 65076032505 549755813888 15188838304515 108006676463878144 (BSN.cpow_neg_s_mk qz12 136442 1000 25 qz13 rfl)

noncomputable abbrev qz626 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 25) qz14)

noncomputable def ep428 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz624) 5242881 1048576 1 1048576 104857 104858 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz624) (Real.sqrt qz626) Bool.false 5242881 1048576 1 1048576 (BSN.sqrt_natCast_div_one 25) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz626) Bool.false 5242881 1048576 1 1048576 5242881 1048576 1 1048576 (BSN.sqrt_enclosure 25 1 2621440 2621441 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep429 := BSN.log_dyadic_bound 9 41 5 4 7545754341519345 524288 196463 124828057765224 4519905705 233982 50 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 9) (BSN.artanhQ 41) 0 4 124828057765224 7545754341519345 4519905705 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep430 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz625 136442 1000 0 1 3624129903009015 1125899906842624 250000000196463 49115750000000000000 49448353222635602463 112589990684262400 17055250013402902323 24557875000000000000000 qz18 (BSN.isNear_log_sfrac 25 1 3624129903009015 1125899906842624 250000000196463 49115750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz626) Bool.false 60802810194841294602240 18889465931478580854784 1000000000785852 196463000000000000000 3624129903009015 1125899906842624 250000000196463 49115750000000000000 (BSN.log_rat_reduce_isNear 25 1 4 50 32 233982 524288 24973259072661432 36028797018963968 196463 1000000000000000 rfl rfl rfl rfl (ep429 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep431 := nat_lit 1056527777456805462910739536237746499482175205399979519366684465004298784113185

noncomputable def ep432 := nat_lit 269735159096721942184679021579506744015100935411788251643217235664447636001

noncomputable def ep433 := nat_lit 2766659845938810091145542638397254963915386803104517750695798866153516281266721

noncomputable def ep434 := BSN.sin_dyadic_bound_f 2013108557 2147483648 3 2 1048576 393310 ep431 ep109 ep432 ep433 ep112 ep432 845191 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2013108557) qz19 0 2 ep431 ep109 ep432 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2013108557) qz20 0 2 ep433 ep112 ep432 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz357 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 115130919) qz17)

noncomputable def ep435 := @Enclosure.Real.IsNear.cos_image qz67 qz357 Bool.false 115130919 262144 729 1048576 Bool.false 845191 1048576 1 196463 (@Enclosure.Real.IsNear.recentre' qz67 Bool.false 49448353222635602463 112589990684262400 17055250013402902323 24557875000000000000000 115130919 262144 729 1048576 (ep430 rfl) rfl) (Enclosure.sfrac_false_div 115130919 262144) (BSN.cos_reduce3 qz357 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 35414980272715399692288) qz285) 226375608064910080 72057594037927936 Bool.false 845191 1048576 69 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q3 115130919 262144 226375608064910080 72057594037927936 69 35414980272715399692288 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 845191 1048576 35414980272715399692288 37778931862957161709568 2013108557 2147483648 393310 392926 (ep434 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep436 := nat_lit 587079758657823800258048488586116724931881825637949416648888354884905745678881

noncomputable def ep437 := nat_lit 1760699805655277956889776107715191161307615275043024673443378630183388341764641

noncomputable def ep438 := BSN.cos_dyadic_bound_f 2013108557 2147483648 3 2 1048576 393310 ep436 ep78 ep432 ep437 ep81 ep432 620614 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2013108557) qz15 0 2 ep436 ep78 ep432 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2013108557) qz16 0 2 ep437 ep81 ep432 rfl rfl rfl rfl) rfl rfl

noncomputable def ep439 := @Enclosure.Real.IsNear.sin_image qz67 qz357 Bool.false 115130919 262144 729 1048576 Bool.true 620614 1048576 1 196463 (@Enclosure.Real.IsNear.recentre' qz67 Bool.false 49448353222635602463 112589990684262400 17055250013402902323 24557875000000000000000 115130919 262144 729 1048576 (ep430 rfl) rfl) (Enclosure.sfrac_false_div 115130919 262144) (BSN.sin_reduce3 qz357 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 35414980272715399692288) qz285) 226375608064910080 72057594037927936 Bool.false 620614 1048576 69 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q3 115130919 262144 226375608064910080 72057594037927936 69 35414980272715399692288 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 620614 1048576 35414980272715399692288 37778931862957161709568 2013108557 2147483648 393310 392926 (ep438 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz358 := (@Enclosure.Real.IsNear.recentre' qz66 Bool.false 209715 1048576 1 1048576 209715 1048576 1 1048576 (ep428 rfl rfl) rfl)

noncomputable def ep440 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz66 (Real.cos qz67)) (@HMul.hMul Real Real Real qz0 qz66 (@Neg.neg Real Real.instNeg (Real.sin qz67))) Bool.false 177249230565 1099511627776 30421797680181 216013352927756288 Bool.false 65076032505 549755813888 15188838304515 108006676463878144 (@Enclosure.Real.IsNear.mulLit_ff qz66 (Real.cos qz67) 209715 1048576 1 1048576 845191 1048576 144270103 206006386688 177249230565 1099511627776 30421797680181 216013352927756288 qz358 (@Enclosure.Real.IsNear.recentre' (Real.cos qz67) Bool.false 845191 1048576 144270103 206006386688 845191 1048576 144270103 206006386688 (ep435 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz66 (@Neg.neg Real Real.instNeg (Real.sin qz67)) 209715 1048576 1 1048576 310307 524288 144270103 206006386688 65076032505 549755813888 15188838304515 108006676463878144 qz358 (@Enclosure.Real.IsNear.neg (Real.sin qz67) Bool.true 310307 524288 144270103 206006386688 (@Enclosure.Real.IsNear.recentre' (Real.sin qz67) Bool.true 620614 1048576 144270103 206006386688 310307 524288 144270103 206006386688 (ep439 rfl rfl) rfl)) rfl)

noncomputable def ep441 := @ep425 177249230565 1099511627776 30421797680181 216013352927756288 Bool.false 65076032505 549755813888 15188838304515 108006676463878144 Bool.false ep426 715730427251 137438953472 579850610142625 108006676463878144 Bool.true 78606872363451547648000 142985067875 1099511627776 1159273029766139 216013352927756288 EMRow47.d8 (ep427 ep440) rfl rfl

noncomputable abbrev qz627 := (@Nat.cast Real Real.instNatCast 26)

noncomputable abbrev qz68 := (@Inv.inv Real Real.instInv (Real.sqrt qz627))

noncomputable abbrev qz628 := (Real.log (Enclosure.sfrac Bool.false 26 1))

noncomputable abbrev qz69 := (@HMul.hMul Real Real Real qz267 qz277 qz628)

noncomputable def ep442 := @Enclosure.Complex.IsNear.of_eq qz622 (Complex.mk (@HMul.hMul Real Real Real qz0 qz68 (Real.cos qz69)) (@HMul.hMul Real Real Real qz0 qz68 (@Neg.neg Real Real.instNeg (Real.sin qz69)))) Bool.false 1208975197 1099511627776 29669436067309 216013352927756288 Bool.false 215628818437 1099511627776 29874284108149 216013352927756288 (BSN.cpow_neg_s_mk qz12 136442 1000 26 qz13 rfl)

noncomputable abbrev qz629 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 26) qz14)

noncomputable def ep443 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz627) 5346709 1048576 1 1048576 102821 102822 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz627) (Real.sqrt qz629) Bool.false 5346709 1048576 1 1048576 (BSN.sqrt_natCast_div_one 26) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz629) Bool.false 5346709 1048576 1 1048576 5346709 1048576 1 1048576 (BSN.sqrt_enclosure 26 1 2673354 2673355 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep444 := BSN.log_dyadic_bound 10 42 5 4 9150106136613120 524288 196463 179034245376000 10500000000 254545 52 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 10) (BSN.artanhQ 42) 0 4 179034245376000 9150106136613120 10500000000 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep445 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz628 136442 1000 0 1 3668288609262839 1125899906842624 250000000196463 49115750000000000000 250254317212520139419 562949953421312000 17055250013402902323 24557875000000000000000 qz18 (BSN.isNear_log_sfrac 26 1 3668288609262839 1125899906842624 250000000196463 49115750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz629) Bool.false 61543670347942250676224 18889465931478580854784 1000000000785852 196463000000000000000 3668288609262839 1125899906842624 250000000196463 49115750000000000000 (BSN.log_rat_reduce_isNear 26 1 4 52 32 254545 524288 24973259072661432 36028797018963968 196463 1000000000000000 rfl rfl rfl rfl (ep444 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep446 := BSN.sin_dyadic_bound_f 12041925 2147483648 1 0 1048576 393310 0 1 1 0 1 1 5879 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 12041925) qz19 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 12041925) qz20 0 0 rfl) rfl rfl

noncomputable abbrev qz359 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 233067495) qz23)

noncomputable def ep447 := @Enclosure.Real.IsNear.cos_image qz69 qz359 Bool.false 233067495 524288 729 1048576 Bool.false 5879 1048576 1 196463 (@Enclosure.Real.IsNear.recentre' qz69 Bool.false 250254317212520139419 562949953421312000 17055250013402902323 24557875000000000000000 233067495 524288 729 1048576 (ep445 rfl) rfl) (Enclosure.sfrac_false_div 233067495 524288) (BSN.cos_reduce3 qz359 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 423687572230053560320) qz24) 226375608064910080 72057594037927936 Bool.false 5879 1048576 70 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q3 233067495 524288 226375608064910080 72057594037927936 70 423687572230053560320 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 5879 1048576 423687572230053560320 75557863725914323419136 12041925 2147483648 393310 392926 (ep446 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep448 := BSN.cos_dyadic_bound_f 12041925 2147483648 1 0 1048576 393310 0 1 1 0 1 1 1048559 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 12041925) qz15 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 12041925) qz16 0 0 rfl) rfl rfl

noncomputable def ep449 := @Enclosure.Real.IsNear.sin_image qz69 qz359 Bool.false 233067495 524288 729 1048576 Bool.true 1048559 1048576 1 196463 (@Enclosure.Real.IsNear.recentre' qz69 Bool.false 250254317212520139419 562949953421312000 17055250013402902323 24557875000000000000000 233067495 524288 729 1048576 (ep445 rfl) rfl) (Enclosure.sfrac_false_div 233067495 524288) (BSN.sin_reduce3 qz359 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 423687572230053560320) qz24) 226375608064910080 72057594037927936 Bool.false 1048559 1048576 70 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q3 233067495 524288 226375608064910080 72057594037927936 70 423687572230053560320 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1048559 1048576 423687572230053560320 75557863725914323419136 12041925 2147483648 393310 392926 (ep448 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz360 := (@Enclosure.Real.IsNear.recentre' qz68 Bool.false 205643 1048576 1 1048576 205643 1048576 1 1048576 (ep443 rfl rfl) rfl)

noncomputable def ep450 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz68 (Real.cos qz69)) (@HMul.hMul Real Real Real qz0 qz68 (@Neg.neg Real Real.instNeg (Real.sin qz69))) Bool.false 1208975197 1099511627776 29669436067309 216013352927756288 Bool.false 215628818437 1099511627776 29874284108149 216013352927756288 (@Enclosure.Real.IsNear.mulLit_ff qz68 (Real.cos qz69) 205643 1048576 1 1048576 5879 1048576 144270103 206006386688 1208975197 1099511627776 29669436067309 216013352927756288 qz360 (@Enclosure.Real.IsNear.recentre' (Real.cos qz69) Bool.false 5879 1048576 144270103 206006386688 5879 1048576 144270103 206006386688 (ep447 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz68 (@Neg.neg Real Real.instNeg (Real.sin qz69)) 205643 1048576 1 1048576 1048559 1048576 144270103 206006386688 215628818437 1099511627776 29874284108149 216013352927756288 qz360 (@Enclosure.Real.IsNear.neg (Real.sin qz69) Bool.true 1048559 1048576 144270103 206006386688 (@Enclosure.Real.IsNear.recentre' (Real.sin qz69) Bool.true 1048559 1048576 144270103 206006386688 1048559 1048576 144270103 206006386688 (ep449 rfl rfl) rfl)) rfl)

noncomputable def ep451 := @ep423 1208975197 1099511627776 29669436067309 216013352927756288 Bool.false 215628818437 1099511627776 29874284108149 216013352927756288 Bool.false 787120087401408243957760 5727052393205 1099511627776 1189370656352559 216013352927756288 Bool.false 79872648428178334810112 36321875281 549755813888 74321707117143 13500834557984768 (ep424 (BSN.head_sum_c_succ qz5 25 26 rfl rfl) (ep441 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep442 ep450) rfl rfl

noncomputable abbrev qz630 := (Real.log (Enclosure.sfrac Bool.false 27 1))

noncomputable abbrev qz70 := (@HMul.hMul Real Real Real qz267 qz277 qz630)

noncomputable abbrev qz361 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 27)))

noncomputable def ep452 := @Enclosure.Complex.IsNear.of_eq qz621 (Complex.mk (@HMul.hMul Real Real Real qz0 qz361 (Real.cos qz70)) (@HMul.hMul Real Real Real qz0 qz361 (@Neg.neg Real Real.instNeg (Real.sin qz70)))) Bool.true 2987634195 17179869184 3662482425895 27001669115969536 Bool.false 11329197659 137438953472 1825121488729 13500834557984768 (BSN.cpow_neg_s_mk qz12 136442 1000 27 qz13 rfl)

noncomputable abbrev qz362 := (Real.sqrt (@Nat.cast Real Real.instNatCast 27))

noncomputable abbrev qz363 := (@Nat.cast Real Real.instNatCast 27)

noncomputable abbrev qz631 := (@HDiv.hDiv Real Real Real qz1 qz363 qz14)

noncomputable def ep453 := @Enclosure.Real.IsNear.inv_image qz362 5448561 1048576 1 1048576 100899 100900 524288 (@Enclosure.Real.IsNear.of_eq qz362 (Real.sqrt qz631) Bool.false 5448561 1048576 1 1048576 (BSN.sqrt_natCast_div_one 27) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz631) Bool.false 5448561 1048576 1 1048576 5448561 1048576 1 1048576 (BSN.sqrt_enclosure 27 1 2724280 2724281 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep454 := BSN.log_dyadic_bound 11 43 5 4 11045349262332945 524288 196463 250863800262504 22507682505 274332 54 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 11) (BSN.artanhQ 43) 0 4 250863800262504 11045349262332945 22507682505 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep455 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz630 136442 1000 0 1 3710780868205815 1125899906842624 250000000196463 49115750000000000000 50630636321973781023 112589990684262400 17055250013402902323 24557875000000000000000 qz18 (BSN.isNear_log_sfrac 27 1 3710780868205815 1125899906842624 250000000196463 49115750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz631) Bool.false 62256572154556490711040 18889465931478580854784 1000000000785852 196463000000000000000 3710780868205815 1125899906842624 250000000196463 49115750000000000000 (BSN.log_rat_reduce_isNear 27 1 4 54 32 274332 524288 24973259072661432 36028797018963968 196463 1000000000000000 rfl rfl rfl rfl (ep454 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep456 := nat_lit 816401967159590804570493314987033616

noncomputable def ep457 := BSN.cos_dyadic_bound_f 950552286 2147483648 2 1 1048576 393310 ep456 ep61 ep456 ep456 ep62 ep456 947520 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 950552286) qz15 0 1 ep456 ep61 ep456 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 950552286) qz16 0 1 ep456 ep62 ep456 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz364 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 471534545) qz30)

noncomputable def ep458 := @Enclosure.Real.IsNear.cos_image qz70 qz364 Bool.false 471534545 1048576 729 1048576 Bool.true 947520 1048576 1 196463 (@Enclosure.Real.IsNear.recentre' qz70 Bool.false 50630636321973781023 112589990684262400 17055250013402902323 24557875000000000000000 471534545 1048576 729 1048576 (ep455 rfl) rfl) (Enclosure.sfrac_false_div 471534545 1048576) (BSN.cos_reduce2 qz364 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 66889170688574603919360) qz31) 226375608064910080 72057594037927936 Bool.false 947520 1048576 71 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q2 471534545 1048576 226375608064910080 72057594037927936 71 66889170688574603919360 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 947520 1048576 66889170688574603919360 151115727451828646838272 950552286 2147483648 393310 392926 (ep457 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep459 := BSN.sin_dyadic_bound_f 950552286 2147483648 2 1 1048576 393310 ep456 ep65 ep456 ep456 ep66 ep456 449128 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 950552286) qz19 0 1 ep456 ep65 ep456 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 950552286) qz20 0 1 ep456 ep66 ep456 rfl rfl rfl rfl) rfl rfl

noncomputable def ep460 := @Enclosure.Real.IsNear.sin_image qz70 qz364 Bool.false 471534545 1048576 729 1048576 Bool.true 449128 1048576 1 196463 (@Enclosure.Real.IsNear.recentre' qz70 Bool.false 50630636321973781023 112589990684262400 17055250013402902323 24557875000000000000000 471534545 1048576 729 1048576 (ep455 rfl) rfl) (Enclosure.sfrac_false_div 471534545 1048576) (BSN.sin_reduce2 qz364 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 66889170688574603919360) qz31) 226375608064910080 72057594037927936 Bool.false 449128 1048576 71 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q2 471534545 1048576 226375608064910080 72057594037927936 71 66889170688574603919360 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 449128 1048576 66889170688574603919360 151115727451828646838272 950552286 2147483648 393310 392926 (ep459 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz365 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 27))) Bool.false 201799 1048576 1 1048576 201799 1048576 1 1048576 (ep453 rfl rfl) rfl)

noncomputable def ep461 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz361 (Real.cos qz70)) (@HMul.hMul Real Real Real qz0 qz361 (@Neg.neg Real Real.instNeg (Real.sin qz70))) Bool.true 2987634195 17179869184 3662482425895 27001669115969536 Bool.false 11329197659 137438953472 1825121488729 13500834557984768 (@Enclosure.Real.IsNear.mulLit_ft qz361 (Real.cos qz70) 201799 1048576 1 1048576 14805 16384 144270103 206006386688 2987634195 17179869184 3662482425895 27001669115969536 qz365 (@Enclosure.Real.IsNear.recentre' (Real.cos qz70) Bool.true 947520 1048576 144270103 206006386688 14805 16384 144270103 206006386688 (ep458 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz361 (@Neg.neg Real Real.instNeg (Real.sin qz70)) 201799 1048576 1 1048576 56141 131072 144270103 206006386688 11329197659 137438953472 1825121488729 13500834557984768 qz365 (@Enclosure.Real.IsNear.neg (Real.sin qz70) Bool.true 56141 131072 144270103 206006386688 (@Enclosure.Real.IsNear.recentre' (Real.sin qz70) Bool.true 449128 1048576 144270103 206006386688 56141 131072 144270103 206006386688 (ep460 rfl rfl) rfl)) rfl)

noncomputable def ep462 := @ep421 2987634195 17179869184 3662482425895 27001669115969536 Bool.false 11329197659 137438953472 1825121488729 13500834557984768 Bool.false 95105072388232341094400 5535843804725 1099511627776 1218670515759719 216013352927756288 Bool.false 11220332806482715213824 81638665917 549755813888 4759176787867 843802159874048 (ep422 (BSN.head_sum_c_succ qz5 26 27 rfl rfl) (ep451 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep452 ep461) rfl rfl

noncomputable abbrev qz632 := (Real.log (Enclosure.sfrac Bool.false 28 1))

noncomputable abbrev qz71 := (@HMul.hMul Real Real Real qz267 qz277 qz632)

noncomputable abbrev qz366 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 28)))

noncomputable def ep463 := @Enclosure.Complex.IsNear.of_eq qz620 (Complex.mk (@HMul.hMul Real Real Real qz0 qz366 (Real.cos qz71)) (@HMul.hMul Real Real Real qz0 qz366 (@Neg.neg Real Real.instNeg (Real.sin qz71)))) Bool.true 132631883041 1099511627776 28759566645965 216013352927756288 Bool.true 159953012177 1099511627776 28786653392701 216013352927756288 (BSN.cpow_neg_s_mk qz12 136442 1000 28 qz13 rfl)

noncomputable abbrev qz367 := (Real.sqrt (@Nat.cast Real Real.instNatCast 28))

noncomputable abbrev qz368 := (@Nat.cast Real Real.instNatCast 28)

noncomputable abbrev qz633 := (@HDiv.hDiv Real Real Real qz1 qz368 qz14)

noncomputable def ep464 := @Enclosure.Real.IsNear.inv_image qz367 5548543 1048576 1 1048576 99081 99082 524288 (@Enclosure.Real.IsNear.of_eq qz367 (Real.sqrt qz633) Bool.false 5548543 1048576 1 1048576 (BSN.sqrt_natCast_div_one 28) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz633) Bool.false 5548543 1048576 1 1048576 5548543 1048576 1 1048576 (BSN.sqrt_enclosure 28 1 2774271 2774272 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep465 := BSN.log_dyadic_bound 12 44 5 4 13275571325829120 524288 196463 344661139390464 45148078080 293399 56 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 12) (BSN.artanhQ 44) 0 4 344661139390464 13275571325829120 45148078080 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep466 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz632 136442 1000 0 1 3751726938922231 1125899906842624 250000000196463 49115750000000000000 255946563500213521051 562949953421312000 17055250013402902323 24557875000000000000000 qz18 (BSN.isNear_log_sfrac 28 1 3751726938922231 1125899906842624 250000000196463 49115750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz633) Bool.false 62943533227317076688896 18889465931478580854784 1000000000785852 196463000000000000000 3751726938922231 1125899906842624 250000000196463 49115750000000000000 (BSN.log_rat_reduce_isNear 28 1 4 56 32 293399 524288 24973259072661432 36028797018963968 196463 1000000000000000 rfl rfl rfl rfl (ep465 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep467 := nat_lit 4885058425572200446988202241600000000

noncomputable def ep468 := BSN.sin_dyadic_bound_f 1486679800 2147483648 2 1 1048576 393310 ep467 ep65 ep467 ep467 ep66 ep467 669307 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1486679800) qz19 0 1 ep467 ep65 ep467 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1486679800) qz20 0 1 ep467 ep66 ep467 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz634 := (@Nat.cast Real Real.instNatCast 131072)

noncomputable abbrev qz369 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 59592203) qz634)

noncomputable abbrev qz370 := (@Nat.cast Real Real.instNatCast 18889465931478580854784)

noncomputable def ep469 := @Enclosure.Real.IsNear.cos_image qz71 qz369 Bool.false 59592203 131072 365 524288 Bool.true 669307 1048576 1 196463 (@Enclosure.Real.IsNear.recentre' qz71 Bool.false 255946563500213521051 562949953421312000 17055250013402902323 24557875000000000000000 59592203 131072 365 524288 (ep466 rfl) rfl) (Enclosure.sfrac_false_div 59592203 131072) (BSN.cos_reduce1 qz369 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 13076973817537155301376) qz370) 226375608064910080 72057594037927936 Bool.false 669307 1048576 72 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q1 59592203 131072 226375608064910080 72057594037927936 72 13076973817537155301376 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 669307 1048576 13076973817537155301376 18889465931478580854784 1486679800 2147483648 393310 392926 (ep468 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep470 := nat_lit 174565284373903308537635134397769110535345156278653085138556969975808000000000

noncomputable def ep471 := nat_lit 23863795821253945854024379823397429403739983177503264770560000000000000000

noncomputable def ep472 := nat_lit 523648125530067417721197354433660536747227988869604248886129789927424000000000

noncomputable def ep473 := BSN.cos_dyadic_bound_f 1486679800 2147483648 3 2 1048576 393310 ep470 ep78 ep471 ep472 ep81 ep471 807179 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1486679800) qz15 0 2 ep470 ep78 ep471 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1486679800) qz16 0 2 ep472 ep81 ep471 rfl rfl rfl rfl) rfl rfl

noncomputable def ep474 := @Enclosure.Real.IsNear.sin_image qz71 qz369 Bool.false 59592203 131072 365 524288 Bool.false 807179 1048576 1 196463 (@Enclosure.Real.IsNear.recentre' qz71 Bool.false 255946563500213521051 562949953421312000 17055250013402902323 24557875000000000000000 59592203 131072 365 524288 (ep466 rfl) rfl) (Enclosure.sfrac_false_div 59592203 131072) (BSN.sin_reduce1 qz369 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 13076973817537155301376) qz370) 226375608064910080 72057594037927936 Bool.false 807179 1048576 72 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q1 59592203 131072 226375608064910080 72057594037927936 72 13076973817537155301376 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 807179 1048576 13076973817537155301376 18889465931478580854784 1486679800 2147483648 393310 392926 (ep473 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz371 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 28))) Bool.false 198163 1048576 1 1048576 198163 1048576 1 1048576 (ep464 rfl rfl) rfl)

noncomputable def ep475 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz366 (Real.cos qz71)) (@HMul.hMul Real Real Real qz0 qz366 (@Neg.neg Real Real.instNeg (Real.sin qz71))) Bool.true 132631883041 1099511627776 28759566645965 216013352927756288 Bool.true 159953012177 1099511627776 28786653392701 216013352927756288 (@Enclosure.Real.IsNear.mulLit_ft qz366 (Real.cos qz71) 198163 1048576 1 1048576 669307 1048576 72233283 103003193344 132631883041 1099511627776 28759566645965 216013352927756288 qz371 (@Enclosure.Real.IsNear.recentre' (Real.cos qz71) Bool.true 669307 1048576 72233283 103003193344 669307 1048576 72233283 103003193344 (ep469 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz366 (@Neg.neg Real Real.instNeg (Real.sin qz71)) 198163 1048576 1 1048576 807179 1048576 72233283 103003193344 159953012177 1099511627776 28786653392701 216013352927756288 qz371 (@Enclosure.Real.IsNear.neg (Real.sin qz71) Bool.false 807179 1048576 72233283 103003193344 (@Enclosure.Real.IsNear.recentre' (Real.sin qz71) Bool.false 807179 1048576 72233283 103003193344 807179 1048576 72233283 103003193344 (ep474 rfl rfl) rfl)) rfl)

noncomputable def ep476 := @ep418 132631883041 1099511627776 28759566645965 216013352927756288 Bool.true 159953012177 1099511627776 28786653392701 216013352927756288 Bool.false ep419 1350802980421 274877906944 311857520601421 54003338231939072 Bool.false 1827564058657911996416 3324319657 1099511627776 1247135911086653 216013352927756288 (ep420 (BSN.head_sum_c_succ qz5 27 28 rfl rfl) (ep462 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep463 ep475) rfl rfl

noncomputable abbrev qz635 := (Real.log (Enclosure.sfrac Bool.false 29 1))

noncomputable abbrev qz72 := (@HMul.hMul Real Real Real qz267 qz277 qz635)

noncomputable abbrev qz372 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 29)))

noncomputable def ep477 := @Enclosure.Complex.IsNear.of_eq qz619 (Complex.mk (@HMul.hMul Real Real Real qz0 qz372 (Real.cos qz72)) (@HMul.hMul Real Real Real qz0 qz372 (@Neg.neg Real Real.instNeg (Real.sin qz72)))) Bool.false 146884623255 1099511627776 28278155104547 216013352927756288 Bool.true 141815412945 1099511627776 28273040386805 216013352927756288 (BSN.cpow_neg_s_mk qz12 136442 1000 29 qz13 rfl)

noncomputable abbrev qz373 := (Real.sqrt (@Nat.cast Real Real.instNatCast 29))

noncomputable abbrev qz374 := (@Nat.cast Real Real.instNatCast 29)

noncomputable abbrev qz636 := (@HDiv.hDiv Real Real Real qz1 qz374 qz14)

noncomputable def ep478 := @Enclosure.Real.IsNear.inv_image qz373 5646755 1048576 1 1048576 97357 97358 524288 (@Enclosure.Real.IsNear.of_eq qz373 (Real.sqrt qz636) Bool.false 5646755 1048576 1 1048576 (BSN.sqrt_natCast_div_one 29) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz636) Bool.false 5646755 1048576 1 1048576 5646755 1048576 1 1048576 (BSN.sqrt_enclosure 29 1 2823377 2823378 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep479 := BSN.log_dyadic_bound 13 45 6 5 353956287581982421875 524288 196463 10371179520995104305 130276274797305 311797 58 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 13) (BSN.artanhQ 45) 0 5 10371179520995104305 353956287581982421875 130276274797305 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep480 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz635 136442 1000 0 1 3791236343078135 1125899906842624 250000000196463 49115750000000000000 51728386912226689567 112589990684262400 17055250013402902323 24557875000000000000000 qz18 (BSN.isNear_log_sfrac 29 1 3791236343078135 1125899906842624 250000000196463 49115750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz636) Bool.false 63606391034871975772160 18889465931478580854784 1000000000785852 196463000000000000000 3791236343078135 1125899906842624 250000000196463 49115750000000000000 (BSN.log_rat_reduce_isNear 29 1 4 58 32 311797 524288 24973259072661432 36028797018963968 196463 1000000000000000 rfl rfl rfl rfl (ep479 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep481 := nat_lit 264194495063880631931641993079636646236390764659435752395169014517494535099521

noncomputable def ep482 := nat_lit 54652538776822879751393596944183351055504973935460566117185404340381095041

noncomputable def ep483 := nat_lit 792474180114088250035423192045021572007061284030436336053272672743802843108481

noncomputable def ep484 := BSN.cos_dyadic_bound_f 1648926481 2147483648 3 2 1048576 393310 ep481 ep78 ep482 ep483 ep81 ep482 754357 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1648926481) qz15 0 2 ep481 ep78 ep482 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1648926481) qz16 0 2 ep483 ep81 ep482 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz375 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 7527471) (@Nat.cast Real Real.instNatCast 16384))

noncomputable def ep485 := @Enclosure.Real.IsNear.cos_image qz72 qz375 Bool.false 7527471 16384 365 524288 Bool.false 754357 1048576 1 196463 (@Enclosure.Real.IsNear.recentre' qz72 Bool.false 51728386912226689567 112589990684262400 17055250013402902323 24557875000000000000000 7527471 16384 365 524288 (ep480 rfl) rfl) (Enclosure.sfrac_false_div 7527471 16384) (BSN.cos_reduce0 qz375 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 1813013840188745449472) (@Nat.cast Real Real.instNatCast 2361183241434822606848)) 226375608064910080 72057594037927936 Bool.false 754357 1048576 73 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q0 7527471 16384 226375608064910080 72057594037927936 73 1813013840188745449472 2361183241434822606848 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 754357 1048576 1813013840188745449472 2361183241434822606848 1648926481 2147483648 393310 392926 (ep484 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep486 := nat_lit 7392735540841622704028532594326176321

noncomputable def ep487 := BSN.sin_dyadic_bound_f 1648926481 2147483648 2 1 1048576 393310 ep486 ep65 ep486 ep486 ep66 ep486 728323 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1648926481) qz19 0 1 ep486 ep65 ep486 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1648926481) qz20 0 1 ep486 ep66 ep486 rfl rfl rfl rfl) rfl rfl

noncomputable def ep488 := @Enclosure.Real.IsNear.sin_image qz72 qz375 Bool.false 7527471 16384 365 524288 Bool.false 728323 1048576 1 196463 (@Enclosure.Real.IsNear.recentre' qz72 Bool.false 51728386912226689567 112589990684262400 17055250013402902323 24557875000000000000000 7527471 16384 365 524288 (ep480 rfl) rfl) (Enclosure.sfrac_false_div 7527471 16384) (BSN.sin_reduce0 qz375 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 1813013840188745449472) (@Nat.cast Real Real.instNatCast 2361183241434822606848)) 226375608064910080 72057594037927936 Bool.false 728323 1048576 73 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q0 7527471 16384 226375608064910080 72057594037927936 73 1813013840188745449472 2361183241434822606848 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 728323 1048576 1813013840188745449472 2361183241434822606848 1648926481 2147483648 393310 392926 (ep487 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz376 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 29))) Bool.false 194715 1048576 1 1048576 194715 1048576 1 1048576 (ep478 rfl rfl) rfl)

noncomputable def ep489 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz372 (Real.cos qz72)) (@HMul.hMul Real Real Real qz0 qz372 (@Neg.neg Real Real.instNeg (Real.sin qz72))) Bool.false 146884623255 1099511627776 28278155104547 216013352927756288 Bool.true 141815412945 1099511627776 28273040386805 216013352927756288 (@Enclosure.Real.IsNear.mulLit_ff qz372 (Real.cos qz72) 194715 1048576 1 1048576 754357 1048576 72233283 103003193344 146884623255 1099511627776 28278155104547 216013352927756288 qz376 (@Enclosure.Real.IsNear.recentre' (Real.cos qz72) Bool.false 754357 1048576 72233283 103003193344 754357 1048576 72233283 103003193344 (ep485 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz372 (@Neg.neg Real Real.instNeg (Real.sin qz72)) 194715 1048576 1 1048576 728323 1048576 72233283 103003193344 141815412945 1099511627776 28273040386805 216013352927756288 qz376 (@Enclosure.Real.IsNear.neg (Real.sin qz72) Bool.false 728323 1048576 72233283 103003193344 (@Enclosure.Real.IsNear.recentre' (Real.sin qz72) Bool.false 728323 1048576 72233283 103003193344 728323 1048576 72233283 103003193344 (ep488 rfl rfl) rfl)) rfl)

noncomputable def ep490 := @ep415 146884623255 1099511627776 28278155104547 216013352927756288 Bool.true 141815412945 1099511627776 28273040386805 216013352927756288 Bool.false ep416 5550096544939 1099511627776 1275708237510231 216013352927756288 Bool.true 152272567413566747967488 17311386661 137438953472 637704475736729 108006676463878144 (ep417 (BSN.head_sum_c_succ qz5 28 29 rfl rfl) (ep476 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep477 ep489) rfl rfl

noncomputable abbrev qz637 := (Real.log (Enclosure.sfrac Bool.false 30 1))

noncomputable abbrev qz73 := (@HMul.hMul Real Real Real qz267 qz277 qz637)

noncomputable abbrev qz377 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 30)))

noncomputable def ep491 := @Enclosure.Complex.IsNear.of_eq qz618 (Complex.mk (@HMul.hMul Real Real Real qz0 qz377 (Real.cos qz73)) (@HMul.hMul Real Real Real qz0 qz377 (@Neg.neg Real Real.instNeg (Real.sin qz73)))) Bool.false 63190931111 549755813888 13874670717017 108006676463878144 Bool.false 77982583063 549755813888 13889850234249 108006676463878144 (BSN.cpow_neg_s_mk qz12 136442 1000 30 qz13 rfl)

noncomputable abbrev qz378 := (Real.sqrt (@Nat.cast Real Real.instNatCast 30))

noncomputable abbrev qz379 := (@Nat.cast Real Real.instNatCast 30)

noncomputable abbrev qz638 := (@HDiv.hDiv Real Real Real qz1 qz379 qz14)

noncomputable def ep492 := @Enclosure.Real.IsNear.inv_image qz378 5743287 1048576 1 1048576 95721 95722 524288 (@Enclosure.Real.IsNear.of_eq qz378 (Real.sqrt qz638) Bool.false 5743287 1048576 1 1048576 (BSN.sqrt_natCast_div_one 30) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz638) Bool.false 5743287 1048576 1 1048576 5743287 1048576 1 1048576 (BSN.sqrt_enclosure 30 1 2871643 2871644 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep493 := BSN.log_dyadic_bound 14 46 6 5 440963670083462507520 524288 196463 14425761949190022144 273345648952320 329571 60 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 14) (BSN.artanhQ 46) 0 5 14425761949190022144 440963670083462507520 273345648952320 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep494 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz637 136442 1000 0 1 3829405717437687 1125899906842624 250000000196463 49115750000000000000 261245887449316444827 562949953421312000 17055250013402902323 24557875000000000000000 qz18 (BSN.isNear_log_sfrac 30 1 3829405717437687 1125899906842624 250000000196463 49115750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz638) Bool.false 64246766873087041339392 18889465931478580854784 1000000000785852 196463000000000000000 3829405717437687 1125899906842624 250000000196463 49115750000000000000 (BSN.log_rat_reduce_isNear 30 1 4 60 32 329571 524288 24973259072661432 36028797018963968 196463 1000000000000000 rfl rfl rfl rfl (ep493 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep495 := nat_lit 4574191393524788902644470864329506481

noncomputable def ep496 := BSN.sin_dyadic_bound_f 1462441771 2147483648 2 1 1048576 393310 ep495 ep65 ep495 ep495 ep66 ep495 660154 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1462441771) qz19 0 1 ep495 ep65 ep495 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1462441771) qz20 0 1 ep495 ep66 ep495 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz380 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 486608385) qz30)

noncomputable def ep497 := @Enclosure.Real.IsNear.cos_image qz73 qz380 Bool.false 486608385 1048576 729 1048576 Bool.false 660154 1048576 1 196463 (@Enclosure.Real.IsNear.recentre' qz73 Bool.false 261245887449316444827 562949953421312000 17055250013402902323 24557875000000000000000 486608385 1048576 729 1048576 (ep494 rfl) rfl) (Enclosure.sfrac_false_div 486608385 1048576) (BSN.cos_reduce3 qz380 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 102910190893493513093120) qz31) 226375608064910080 72057594037927936 Bool.false 660154 1048576 73 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q3 486608385 1048576 226375608064910080 72057594037927936 73 102910190893493513093120 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 660154 1048576 102910190893493513093120 151115727451828646838272 1462441771 2147483648 393310 392926 (ep496 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep498 := nat_lit 163455174011394705553376648674180778251436557206498490360893163853284717868641

noncomputable def ep499 := nat_lit 20923226904596250212511910525649386441596124105701368873115913689021003361

noncomputable def ep500 := nat_lit 490323675580374924159704922201491035981426479371284068344933259732476111599201

noncomputable def ep501 := BSN.cos_dyadic_bound_f 1462441771 2147483648 3 2 1048576 393310 ep498 ep78 ep499 ep500 ep81 ep499 814682 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1462441771) qz15 0 2 ep498 ep78 ep499 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1462441771) qz16 0 2 ep500 ep81 ep499 rfl rfl rfl rfl) rfl rfl

noncomputable def ep502 := @Enclosure.Real.IsNear.sin_image qz73 qz380 Bool.false 486608385 1048576 729 1048576 Bool.true 814682 1048576 1 196463 (@Enclosure.Real.IsNear.recentre' qz73 Bool.false 261245887449316444827 562949953421312000 17055250013402902323 24557875000000000000000 486608385 1048576 729 1048576 (ep494 rfl) rfl) (Enclosure.sfrac_false_div 486608385 1048576) (BSN.sin_reduce3 qz380 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 102910190893493513093120) qz31) 226375608064910080 72057594037927936 Bool.false 814682 1048576 73 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q3 486608385 1048576 226375608064910080 72057594037927936 73 102910190893493513093120 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 814682 1048576 102910190893493513093120 151115727451828646838272 1462441771 2147483648 393310 392926 (ep501 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz381 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 30))) Bool.false 191443 1048576 1 1048576 191443 1048576 1 1048576 (ep492 rfl rfl) rfl)

noncomputable def ep503 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz377 (Real.cos qz73)) (@HMul.hMul Real Real Real qz0 qz377 (@Neg.neg Real Real.instNeg (Real.sin qz73))) Bool.false 63190931111 549755813888 13874670717017 108006676463878144 Bool.false 77982583063 549755813888 13889850234249 108006676463878144 (@Enclosure.Real.IsNear.mulLit_ff qz377 (Real.cos qz73) 191443 1048576 1 1048576 330077 524288 144270103 206006386688 63190931111 549755813888 13874670717017 108006676463878144 qz381 (@Enclosure.Real.IsNear.recentre' (Real.cos qz73) Bool.false 660154 1048576 144270103 206006386688 330077 524288 144270103 206006386688 (ep497 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz377 (@Neg.neg Real Real.instNeg (Real.sin qz73)) 191443 1048576 1 1048576 407341 524288 144270103 206006386688 77982583063 549755813888 13889850234249 108006676463878144 qz381 (@Enclosure.Real.IsNear.neg (Real.sin qz73) Bool.true 407341 524288 144270103 206006386688 (@Enclosure.Real.IsNear.recentre' (Real.sin qz73) Bool.true 814682 1048576 144270103 206006386688 407341 524288 144270103 206006386688 (ep502 rfl rfl) rfl)) rfl)

noncomputable def ep504 := @ep412 63190931111 549755813888 13874670717017 108006676463878144 Bool.false 77982583063 549755813888 13889850234249 108006676463878144 Bool.false ep413 5676478407161 1099511627776 1303457578944265 216013352927756288 Bool.false 1200809141874110496768 8737036419 549755813888 325797162985489 54003338231939072 (ep414 (BSN.head_sum_c_succ qz5 29 30 rfl rfl) (ep490 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep491 ep503) rfl rfl

noncomputable abbrev qz639 := (Real.log (Enclosure.sfrac Bool.false 31 1))

noncomputable abbrev qz74 := (@HMul.hMul Real Real Real qz267 qz277 qz639)

noncomputable abbrev qz382 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 31)))

noncomputable def ep505 := @Enclosure.Complex.IsNear.of_eq qz617 (Complex.mk (@HMul.hMul Real Real Real qz0 qz382 (Real.cos qz74)) (@HMul.hMul Real Real Real qz0 qz382 (@Neg.neg Real Real.instNeg (Real.sin qz74)))) Bool.true 89219922105 549755813888 6839133806465 54003338231939072 Bool.false 42297751755 549755813888 425916214265 3375208639496192 (BSN.cpow_neg_s_mk qz12 136442 1000 31 qz13 rfl)

noncomputable abbrev qz383 := (Real.sqrt (@Nat.cast Real Real.instNatCast 31))

noncomputable abbrev qz384 := (@Nat.cast Real Real.instNatCast 31)

noncomputable abbrev qz640 := (@HDiv.hDiv Real Real Real qz1 qz384 qz14)

noncomputable def ep506 := @Enclosure.Real.IsNear.inv_image qz383 5838225 1048576 1 1048576 94164 94165 524288 (@Enclosure.Real.IsNear.of_eq qz383 (Real.sqrt qz640) Bool.false 5838225 1048576 1 1048576 (BSN.sqrt_natCast_div_one 31) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz640) Bool.false 5838225 1048576 1 1048576 5838225 1048576 1 1048576 (BSN.sqrt_enclosure 31 1 2919112 2919113 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep507 := BSN.log_dyadic_bound 15 47 6 5 546767979591453359355 524288 196463 19788004106328479625 544934619140625 346763 62 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 15) (BSN.artanhQ 47) 0 5 19788004106328479625 546767979591453359355 544934619140625 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep508 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz639 136442 1000 0 1 3866325256314103 1125899906842624 250000000196463 49115750000000000000 263764575311004420763 562949953421312000 17055250013402902323 24557875000000000000000 qz18 (BSN.isNear_log_sfrac 31 1 3866325256314103 1125899906842624 250000000196463 49115750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz640) Bool.false 64866173951437069877248 18889465931478580854784 1000000000785852 196463000000000000000 3866325256314103 1125899906842624 250000000196463 49115750000000000000 (BSN.log_rat_reduce_isNear 31 1 4 62 32 346763 524288 24973259072661432 36028797018963968 196463 1000000000000000 rfl rfl rfl rfl (ep507 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep509 := nat_lit 816887904660395162074109163032914801

noncomputable def ep510 := BSN.cos_dyadic_bound_f 950693701 2147483648 2 1 1048576 393310 ep509 ep61 ep509 ep509 ep62 ep509 947490 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 950693701) qz15 0 1 ep509 ep61 ep509 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 950693701) qz16 0 1 ep509 ep62 ep509 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz385 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 245649903) qz23)

noncomputable def ep511 := @Enclosure.Real.IsNear.cos_image qz74 qz385 Bool.false 245649903 524288 729 1048576 Bool.true 947490 1048576 1 196463 (@Enclosure.Real.IsNear.recentre' qz74 Bool.false 263764575311004420763 562949953421312000 17055250013402902323 24557875000000000000000 245649903 524288 729 1048576 (ep508 rfl) rfl) (Enclosure.sfrac_false_div 245649903 524288) (BSN.cos_reduce2 qz385 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 33449560922349943914496) qz24) 226375608064910080 72057594037927936 Bool.false 947490 1048576 74 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q2 245649903 524288 226375608064910080 72057594037927936 74 33449560922349943914496 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 947490 1048576 33449560922349943914496 75557863725914323419136 950693701 2147483648 393310 392926 (ep510 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep512 := BSN.sin_dyadic_bound_f 950693701 2147483648 2 1 1048576 393310 ep509 ep65 ep509 ep509 ep66 ep509 449190 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 950693701) qz19 0 1 ep509 ep65 ep509 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 950693701) qz20 0 1 ep509 ep66 ep509 rfl rfl rfl rfl) rfl rfl

noncomputable def ep513 := @Enclosure.Real.IsNear.sin_image qz74 qz385 Bool.false 245649903 524288 729 1048576 Bool.true 449190 1048576 1 196463 (@Enclosure.Real.IsNear.recentre' qz74 Bool.false 263764575311004420763 562949953421312000 17055250013402902323 24557875000000000000000 245649903 524288 729 1048576 (ep508 rfl) rfl) (Enclosure.sfrac_false_div 245649903 524288) (BSN.sin_reduce2 qz385 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 33449560922349943914496) qz24) 226375608064910080 72057594037927936 Bool.false 449190 1048576 74 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q2 245649903 524288 226375608064910080 72057594037927936 74 33449560922349943914496 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 449190 1048576 33449560922349943914496 75557863725914323419136 950693701 2147483648 393310 392926 (ep512 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz386 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 31))) Bool.false 188329 1048576 1 1048576 188329 1048576 1 1048576 (ep506 rfl rfl) rfl)

noncomputable def ep514 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz382 (Real.cos qz74)) (@HMul.hMul Real Real Real qz0 qz382 (@Neg.neg Real Real.instNeg (Real.sin qz74))) Bool.true 89219922105 549755813888 6839133806465 54003338231939072 Bool.false 42297751755 549755813888 425916214265 3375208639496192 (@Enclosure.Real.IsNear.mulLit_ft qz382 (Real.cos qz74) 188329 1048576 1 1048576 473745 524288 144270103 206006386688 89219922105 549755813888 6839133806465 54003338231939072 qz386 (@Enclosure.Real.IsNear.recentre' (Real.cos qz74) Bool.true 947490 1048576 144270103 206006386688 473745 524288 144270103 206006386688 (ep511 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz382 (@Neg.neg Real Real.instNeg (Real.sin qz74)) 188329 1048576 1 1048576 224595 524288 144270103 206006386688 42297751755 549755813888 425916214265 3375208639496192 qz386 (@Enclosure.Real.IsNear.neg (Real.sin qz74) Bool.true 224595 524288 144270103 206006386688 (@Enclosure.Real.IsNear.recentre' (Real.sin qz74) Bool.true 449190 1048576 144270103 206006386688 224595 524288 144270103 206006386688 (ep513 rfl rfl) rfl)) rfl)

noncomputable def ep515 := @ep409 89219922105 549755813888 6839133806465 54003338231939072 Bool.false 42297751755 549755813888 425916214265 3375208639496192 Bool.false ep410 5498038562951 1099511627776 1330814114170125 216013352927756288 Bool.false 28056671509199047360512 25517394087 274877906944 332611822413729 54003338231939072 (ep411 (BSN.head_sum_c_succ qz5 30 31 rfl rfl) (ep504 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep505 ep514) rfl rfl

noncomputable abbrev qz641 := (Real.log (Enclosure.sfrac Bool.false 32 1))

noncomputable abbrev qz75 := (@HMul.hMul Real Real Real qz267 qz277 qz641)

noncomputable abbrev qz387 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 32)))

noncomputable def ep516 := @Enclosure.Complex.IsNear.of_eq qz616 (Complex.mk (@HMul.hMul Real Real Real qz0 qz387 (Real.cos qz75)) (@HMul.hMul Real Real Real qz0 qz387 (@Neg.neg Real Real.instNeg (Real.sin qz75)))) Bool.true 1511264539 137438953472 6688824368801 54003338231939072 Bool.true 12124408467 68719476736 6737022636591 54003338231939072 (BSN.cpow_neg_s_mk qz12 136442 1000 32 qz13 rfl)

noncomputable abbrev qz388 := (Real.sqrt (@Nat.cast Real Real.instNatCast 32))

noncomputable abbrev qz389 := (@Nat.cast Real Real.instNatCast 32)

noncomputable abbrev qz642 := (@HDiv.hDiv Real Real Real qz1 qz389 qz14)

noncomputable def ep517 := @Enclosure.Real.IsNear.inv_image qz388 5931641 1048576 1 1048576 92681 92682 524288 (@Enclosure.Real.IsNear.of_eq qz388 (Real.sqrt qz642) Bool.false 5931641 1048576 1 1048576 (BSN.sqrt_natCast_div_one 32) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz642) Bool.false 5931641 1048576 1 1048576 5931641 1048576 1 1048576 (BSN.sqrt_enclosure 32 1 2965820 2965821 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep518 := BSN.log_dyadic_bound 0 64 1 0 1 524288 196463 0 1 0 64 64 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 0) (BSN.artanhQ 64) 0 0 rfl) rfl rfl rfl

noncomputable def ep519 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz641 136442 1000 0 1 15608286920413395 4503599627370496 200000000196463 39292600000000000000 212962588399504444059 450359962737049600 13644200013402902323 19646300000000000000000 qz18 (BSN.isNear_log_sfrac 32 1 15608286920413395 4503599627370496 200000000196463 39292600000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz642) Bool.false 65465900263437584302080 18889465931478580854784 1000000000982315 196463000000000000000 15608286920413395 4503599627370496 200000000196463 39292600000000000000 (BSN.log_rat_reduce_isNear 32 1 5 64 64 0 524288 24973259072661432 36028797018963968 196463 1000000000000000 rfl rfl rfl rfl (ep518 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep520 := BSN.sin_dyadic_bound_f 133666654 2147483648 1 0 1048576 393310 0 1 1 0 1 1 65224 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 133666654) qz19 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 133666654) qz20 0 0 rfl) rfl rfl

noncomputable abbrev qz390 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 495842165) qz30)

noncomputable def ep521 := @Enclosure.Real.IsNear.cos_image qz75 qz390 Bool.false 495842165 1048576 729 1048576 Bool.true 65224 1048576 1 196463 (@Enclosure.Real.IsNear.recentre' qz75 Bool.false 212962588399504444059 450359962737049600 13644200013402902323 19646300000000000000000 495842165 1048576 729 1048576 (ep519 rfl) rfl) (Enclosure.sfrac_false_div 495842165 1048576) (BSN.cos_reduce1 qz390 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 9405954630943034572800) qz31) 226375608064910080 72057594037927936 Bool.false 65224 1048576 75 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q1 495842165 1048576 226375608064910080 72057594037927936 75 9405954630943034572800 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 65224 1048576 9405954630943034572800 151115727451828646838272 133666654 2147483648 393310 392926 (ep520 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep522 := BSN.cos_dyadic_bound_f 133666654 2147483648 1 0 1048576 393310 0 1 1 0 1 1 1046544 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 133666654) qz15 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 133666654) qz16 0 0 rfl) rfl rfl

noncomputable def ep523 := @Enclosure.Real.IsNear.sin_image qz75 qz390 Bool.false 495842165 1048576 729 1048576 Bool.false 1046544 1048576 1 196463 (@Enclosure.Real.IsNear.recentre' qz75 Bool.false 212962588399504444059 450359962737049600 13644200013402902323 19646300000000000000000 495842165 1048576 729 1048576 (ep519 rfl) rfl) (Enclosure.sfrac_false_div 495842165 1048576) (BSN.sin_reduce1 qz390 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 9405954630943034572800) qz31) 226375608064910080 72057594037927936 Bool.false 1046544 1048576 75 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q1 495842165 1048576 226375608064910080 72057594037927936 75 9405954630943034572800 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1046544 1048576 9405954630943034572800 151115727451828646838272 133666654 2147483648 393310 392926 (ep522 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz391 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 32))) Bool.false 185363 1048576 1 1048576 185363 1048576 1 1048576 (ep517 rfl rfl) rfl)

noncomputable def ep524 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz387 (Real.cos qz75)) (@HMul.hMul Real Real Real qz0 qz387 (@Neg.neg Real Real.instNeg (Real.sin qz75))) Bool.true 1511264539 137438953472 6688824368801 54003338231939072 Bool.true 12124408467 68719476736 6737022636591 54003338231939072 (@Enclosure.Real.IsNear.mulLit_ft qz387 (Real.cos qz75) 185363 1048576 1 1048576 8153 131072 144270103 206006386688 1511264539 137438953472 6688824368801 54003338231939072 qz391 (@Enclosure.Real.IsNear.recentre' (Real.cos qz75) Bool.true 65224 1048576 144270103 206006386688 8153 131072 144270103 206006386688 (ep521 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz387 (@Neg.neg Real Real.instNeg (Real.sin qz75)) 185363 1048576 1 1048576 65409 65536 144270103 206006386688 12124408467 68719476736 6737022636591 54003338231939072 qz391 (@Enclosure.Real.IsNear.neg (Real.sin qz75) Bool.false 65409 65536 144270103 206006386688 (@Enclosure.Real.IsNear.recentre' (Real.sin qz75) Bool.false 1046544 1048576 144270103 206006386688 65409 65536 144270103 206006386688 (ep523 rfl rfl) rfl)) rfl)

noncomputable def ep525 := @ep407 1511264539 137438953472 6688824368801 54003338231939072 Bool.true 12124408467 68719476736 6737022636591 54003338231939072 Bool.false 753983013307408195780608 5485948446639 1099511627776 1357569411645329 216013352927756288 Bool.true 1579190053018131234816 22980239781 274877906944 21209302815645 3375208639496192 (ep408 (BSN.head_sum_c_succ qz5 31 32 rfl rfl) (ep515 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep516 ep524) rfl rfl

theorem EMRow47.d9 : Enclosure.Complex.IsNear qz65 Bool.false 5485948446639 1099511627776 1357569411645329 216013352927756288 Bool.true 22980239781 274877906944 21209302815645 3375208639496192 := ep406 (BSN.head_sum_c_succ qz5 32 33 rfl rfl) (ep525 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

theorem EMRow47.d10 : @Eq Nat (BSN.factNat (Nat.mul 2 1)) 2 := @Eq.refl Nat 2

theorem EMRow47.d11 : @Eq Nat (Nat.pow 35 1) 35 := @Eq.refl Nat 35

noncomputable def ep526 := nat_lit 1888652484726300530870449734183869

noncomputable def ep527 := nat_lit 375612272943443776847866757120000

noncomputable def ep528 := nat_lit 73335809921021076906888305665047226621943

noncomputable def ep529 := nat_lit 8698664233267690809725657320092617146368000

noncomputable abbrev qz715 := (@instHMul Complex Complex.instMul)

noncomputable abbrev qz643 := qz715

noncomputable abbrev qz392 := qz643

noncomputable abbrev qz76 := qz392

noncomputable abbrev qz644 := (@instHSub Complex Complex.instSub)

noncomputable abbrev qz393 := qz644

noncomputable abbrev qz77 := qz393

noncomputable abbrev qz716 := (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (4 : Complex))

noncomputable abbrev qz717 := (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid))

noncomputable abbrev qz645 := (@HAdd.hAdd Complex Complex Complex qz713 (@HAdd.hAdd Complex Complex Complex qz713 qz716 (@HMul.hMul Complex Complex Complex qz715 Complex.I (@HDiv.hDiv Complex Complex Complex qz717 (↑qz714) (2 : Complex)))) (@Nat.cast Complex Complex.instNatCast 2))

noncomputable abbrev qz394 := qz645

noncomputable abbrev qz78 := (Complex.Stirling.logGammaStirling 1 qz394)

noncomputable abbrev qz646 := (@HAdd.hAdd Complex Complex Complex qz713 qz716 (@HMul.hMul Complex Complex Complex qz715 Complex.I (@HDiv.hDiv Complex Complex Complex qz717 (↑qz714) (2 : Complex))))

noncomputable abbrev qz395 := qz646

noncomputable abbrev qz79 := qz395

noncomputable abbrev qz80 := (@HMul.hMul Real Real Real qz267 (@HDiv.hDiv Real Real Real qz270 qz277 (2 : Real)) (Real.log Real.pi))

noncomputable abbrev qz396 := (@instHSub Real Real.instSub)

noncomputable def ep530 := Complex.re (@HMul.hMul Complex Complex Complex qz76 (Complex.exp (@HMul.hMul Complex Complex Complex qz76 Complex.I ↑(@HSub.hSub Real Real Real qz396 (Complex.im (@HSub.hSub Complex Complex Complex qz77 qz78 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz79 (@Nat.cast Complex Complex.instNatCast j))))) qz80))) (zetaApproximant qz5 1 35))

noncomputable def ep531 := @Enclosure.Real.IsNear.of_eq ep530 (@HSub.hSub Real Real Real qz396 (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz396 (Complex.im (@HSub.hSub Complex Complex Complex qz77 qz78 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz79 (@Nat.cast Complex Complex.instNatCast j))))) qz80)) (Complex.re (zetaApproximant qz5 1 35))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz396 (Complex.im (@HSub.hSub Complex Complex Complex qz77 qz78 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz79 (@Nat.cast Complex Complex.instNatCast j))))) qz80)) (Complex.im (zetaApproximant qz5 1 35))))

noncomputable def ep532 := nat_lit 2158458405135842099941999534351

noncomputable def ep533 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz396 (Complex.im (@HSub.hSub Complex Complex Complex qz77 qz78 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz79 (@Nat.cast Complex Complex.instNatCast j))))) qz80)) (Complex.re (zetaApproximant qz5 1 35))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz396 (Complex.im (@HSub.hSub Complex Complex Complex qz77 qz78 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz79 (@Nat.cast Complex Complex.instNatCast j))))) qz80)) (Complex.im (zetaApproximant qz5 1 35))) ep532

noncomputable def ep534 := nat_lit 429271169078221459254704865280

noncomputable def ep535 := nat_lit 366311371558065895454024977806989708829121

noncomputable def ep536 := nat_lit 43493321166338454048628286600463085731840000

noncomputable def ep537 := nat_lit 172529054836677650017703343

noncomputable def ep538 := nat_lit 46951534117930472105983344640000

noncomputable def ep539 := nat_lit 61279674506581513402758419707737380099

noncomputable def ep540 := nat_lit 7248886861056409008104714433410514288640000

noncomputable def ep541 := nat_lit 101343007512618353414049245603619932394379473515398145549271040

noncomputable def ep542 := @Enclosure.Real.IsNear.mulLit_tf (Real.cos (@HSub.hSub Real Real Real qz396 (Complex.im (@HSub.hSub Complex Complex Complex qz77 qz78 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz79 (@Nat.cast Complex Complex.instNatCast j))))) qz80)) (Complex.re (zetaApproximant qz5 1 35)) 1048575 1048576 74722201

noncomputable def ep543 := nat_lit 154385123033820334735855771

noncomputable def ep544 := nat_lit 30703866654268845981696000

noncomputable def ep545 := nat_lit 464198735447088428178596346547

noncomputable def ep546 := nat_lit 70375360469138903361189314560000

noncomputable def ep547 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HSub.hSub Real Real Real qz396 (Complex.im (@HSub.hSub Complex Complex Complex qz77 qz78 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz79 (@Nat.cast Complex Complex.instNatCast j))))) qz80)) Bool.true 1048575 1048576 74722201

noncomputable abbrev qz397 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 74119761) qz23)

noncomputable def ep548 := @Enclosure.Real.IsNear.cos_image (@HSub.hSub Real Real Real qz396 (Complex.im (@HSub.hSub Complex Complex Complex qz77 qz78 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz79 (@Nat.cast Complex Complex.instNatCast j))))) qz80) qz397 Bool.false 74119761 524288 375

noncomputable def ep549 := nat_lit 110192531825183792215222807

noncomputable def ep550 := nat_lit 309009580032000000000000000000

noncomputable def ep551 := @Enclosure.Real.IsNear.recentre' (@HSub.hSub Real Real Real qz396 (Complex.im (@HSub.hSub Complex Complex Complex qz77 qz78 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz79 (@Nat.cast Complex Complex.instNatCast j))))) qz80) Bool.false 318341950578292382489 2251799813685248000 ep549 ep550

noncomputable def ep552 := nat_lit 29775117887183792215222807

noncomputable def ep553 := @Enclosure.Real.IsNear.subLit_ff_p (Complex.im (@HSub.hSub Complex Complex Complex qz77 qz78 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz79 (@Nat.cast Complex Complex.instNatCast j))))) qz80 494195354088477252377 2251799813685248000 ep552 ep550 5118007641 65536000

noncomputable def ep554 := nat_lit 20862858073098969578799104000

noncomputable def ep555 := nat_lit 9285856663256137827853381

noncomputable def ep556 := nat_lit 51501596672000000000000000000

noncomputable def ep557 := @Enclosure.Complex.IsNear.im_isNear (@HSub.hSub Complex Complex Complex qz77 qz78 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz79 (@Nat.cast Complex Complex.instNatCast j)))) Bool.true 24161380568997306931 225179981368524800 ep555 ep556 Bool.false 494195354088477252377 2251799813685248000

noncomputable def ep558 := nat_lit 9154784662638118667789381

noncomputable def ep559 := nat_lit 28202253886874782635190807

noncomputable def ep560 := @Enclosure.Complex.IsNear.subLitP qz78 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz79 (@Nat.cast Complex Complex.instNatCast j))) Bool.true 22259582799370534731 225179981368524800 ep558 ep556 Bool.false 501220088047451996377 2251799813685248000 ep559

noncomputable def ep561 := nat_lit 27203296131823253528436835241426944

noncomputable def ep562 := nat_lit 139103625782568530044462908217229312

noncomputable abbrev qz718 := (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (2 : Complex))

noncomputable abbrev qz647 := qz718

noncomputable abbrev qz398 := (@HSub.hSub Complex Complex Complex qz644 qz645 qz647)

noncomputable abbrev qz399 := (Complex.log qz645)

noncomputable abbrev qz81 := (@HSub.hSub Complex Complex Complex qz393 (@HMul.hMul Complex Complex Complex qz392 qz398 qz399) qz394)

noncomputable abbrev qz400 := qz647

noncomputable abbrev qz82 := (@HMul.hMul Complex Complex Complex qz392 qz400 ↑(Real.log (@HMul.hMul Real Real Real qz267 (2 : Real) Real.pi)))

noncomputable abbrev qz648 := qz717

noncomputable abbrev qz401 := qz648

noncomputable abbrev qz83 := qz401

noncomputable abbrev qz84 := (@instHMul Nat instMulNat)

noncomputable abbrev qz649 := (@instHPow Complex Int (@ZPow.toPow Complex (@DivInvMonoid.toZPow Complex Complex.instDivInvMonoid)))

noncomputable abbrev qz402 := qz649

noncomputable abbrev qz85 := qz402

noncomputable abbrev qz86 := qz394

noncomputable abbrev qz87 := (@OfNat.ofNat Int 1 (@instOfNat 1))

noncomputable abbrev qz88 := (@OfNat.ofNat Int 2 (@instOfNat 2))

noncomputable abbrev qz403 := (@instHSub Int Int.instSub)

noncomputable abbrev qz404 := (@instHMul Int Int.instMul)

noncomputable def ep563 := @Enclosure.Complex.IsNear.of_eq qz78 (@HAdd.hAdd Complex Complex Complex qz4 (@HAdd.hAdd Complex Complex Complex qz4 qz81 qz82) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz84 2 k))) (@HMul.hMul Complex Complex Complex qz76 (@HMul.hMul Complex Complex Complex qz76 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz77 (@HMul.hMul Complex Complex Complex qz76 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz85 qz86 (@HSub.hSub Int Int Int qz403 qz87 (@HMul.hMul Int Int Int qz404 qz88 (@Nat.cast Int instNatCastInt k)))))) Bool.true 22259582799370534731

noncomputable def ep564 := @Enclosure.Complex.IsNear.addLitP (@HAdd.hAdd Complex Complex Complex qz4 qz81 qz82) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz84 2 k))) (@HMul.hMul Complex Complex Complex qz76 (@HMul.hMul Complex Complex Complex qz76 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz77 (@HMul.hMul Complex Complex Complex qz76 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz85 qz86 (@HSub.hSub Int Int Int qz403 qz87 (@HMul.hMul Int Int Int qz404 qz88 (@Nat.cast Int instNatCastInt k))))) Bool.true 22259591861337997131 225179981368524800

noncomputable def ep565 := nat_lit 1529666882334409216890834518016

noncomputable def ep566 := nat_lit 8610895545048187282276501946368000

noncomputable def ep567 := @ep564 34922723443212554849 196463000000000000000000 Bool.false 501222835676262007001 2251799813685248000 17930250080589319063 196463000000000000000000 Bool.false 2765493 68719476736 3 68719476736 Bool.true 20962744217 17179869184000 68221 51539607552000 Bool.true ep565 22259582799370534731 225179981368524800 ep558 ep556 Bool.false ep566

noncomputable def ep568 := @Enclosure.Complex.IsNear.addLitP qz81 qz82 Bool.true 22466518231698521931 225179981368524800 69096000017528625323 392926000000000000000000

noncomputable def ep569 := nat_lit 2917609224449293959954432

noncomputable def ep570 := @ep568 Bool.false 501222835676262007001 2251799813685248000 17930250080589319063 196463000000000000000000 Bool.false 120447 131072 1 524288 Bool.false 0 1 0 1 Bool.true ep569 22259591861337997131 225179981368524800 34922723443212554849 196463000000000000000000 Bool.false 501222835676262007001 501222835676262007001 2251799813685248000

noncomputable abbrev qz89 := (@HMul.hMul Complex Complex Complex qz392 qz398 qz399)

noncomputable def ep571 := @Enclosure.Complex.IsNear.subLitP qz89 qz86 Bool.true 21959863273619341131 225179981368524800 69096000017528625323 392926000000000000000000 Bool.false 654842870765683310809

noncomputable def ep572 := nat_lit 2004891342705048028004000

noncomputable def ep573 := @ep571 2251799813685248000 17930250080589319063 196463000000000000000000 Bool.false 9000 4000 0 1 Bool.false 272884 4000 0 1 Bool.true 89866072926794087724000 22466518231698521931 225179981368524800 69096000017528625323 392926000000000000000000 Bool.false ep572 501222835676262007001 2251799813685248000 17930250080589319063 196463000000000000000000

noncomputable abbrev qz90 := qz398

noncomputable abbrev qz91 := qz399

noncomputable def ep574 := @Enclosure.Complex.IsNear.mul qz90 qz91 Bool.true 21959863273619341131 225179981368524800 69096000017528625323 392926000000000000000000 Bool.false 654842870765683310809 2251799813685248000 17930250080589319063

noncomputable abbrev qz92 := (Complex.re qz398)

noncomputable abbrev qz93 := (Complex.re qz399)

noncomputable abbrev qz94 := (Complex.im qz398)

noncomputable abbrev qz95 := (Complex.im qz399)

noncomputable def ep575 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 qz92 qz93) (@HMul.hMul Real Real Real qz0 qz94 qz95) 66570114933416003 9007199254740992 875000004125723 392926000000000000000 11812058073477370603 112589990684262400

noncomputable def ep576 := nat_lit 98898432056179105160980229548670976

noncomputable def ep577 := @Enclosure.Real.IsNear.mulLit_ff qz92 qz93 7000 4000 0 1 9510016419059429 2251799813685248 125000000589389 98231500000000000000

noncomputable def ep578 := @Enclosure.Complex.IsNear.re_isNear qz90 Bool.false 7000 4000 0 1 Bool.false 272884 4000 0 1

noncomputable abbrev qz650 := (Enclosure.sfrac Bool.false 272884 4000)

noncomputable abbrev qz405 := qz650

noncomputable def ep579 := @Enclosure.Complex.IsNear.of_eq qz90 (Complex.mk (Enclosure.sfrac Bool.false 7000 4000) qz405) Bool.false 7000 4000 0 1 Bool.false 272884 4000 0

noncomputable abbrev qz651 := (Enclosure.sfrac Bool.false 9000 4000)

noncomputable abbrev qz406 := (Complex.log (Complex.mk qz651 qz650))

noncomputable def ep580 := @Enclosure.Complex.IsNear.of_eq qz91 qz406 Bool.false 9510016419059429 2251799813685248 125000000589389 98231500000000000000 Bool.false 865720091575715 562949953421312 1000000000196463 392926000000000000000

noncomputable def ep581 := nat_lit 5776024079034667283742391421032082668546621440

noncomputable def ep582 := nat_lit 7986023435776163732566930409507362680864768

noncomputable def ep583 := nat_lit 19776572740358283312076458036500685324288

noncomputable def ep584 := BSN.log_dyadic_bound 9010677456 140082677456 3 2 ep581 1048576 392926 ep582 ep583 135083 149093354912 131072000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 9010677456) (BSN.artanhQ 140082677456) 0 2 ep582 ep581 ep583 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz96 := (Enclosure.sfrac Bool.false 1 2)

noncomputable abbrev qz407 := (Enclosure.Real.IsNear.const Bool.false 1 2)

noncomputable abbrev qz652 := (Real.log (Enclosure.sfrac Bool.false 74546677456 16000000))

noncomputable abbrev qz653 := (@Nat.cast Real Real.instNatCast 16000000)

noncomputable def ep585 := @Enclosure.Real.IsNear.mulLit_ff qz96 qz652 1 2 0 1 9510016419059429 1125899906842624 125000000589389 49115750000000000000 9510016419059429 2251799813685248 125000000589389 98231500000000000000 qz407 (BSN.isNear_log_sfrac 74546677456 16000000 9510016419059429 1125899906842624 125000000589389 49115750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 74546677456) qz653)) Bool.false 319103199252213114339328 37778931862957161709568 1000000004715112 392926000000000000000 9510016419059429 1125899906842624 125000000589389 49115750000000000000 (BSN.log_rat_reduce_isNear 74546677456 16000000 12 149093354912 131072000000 135083 1048576 24973259072661432 36028797018963968 392926 1000000000000000 rfl rfl rfl rfl (ep584 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep586 := BSN.arctan_dyadic_bound_f 9000 272884 1 0 1048576 392926 0 1 1 0 1 1 34570 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 9000) (BSN.arctanEvenQ 272884) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 9000) (BSN.arctanOddQ 272884) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz97 := (@HMul.hMul Real Real Real qz267 (Enclosure.sfrac Bool.false 1 2) Real.pi)

noncomputable abbrev qz98 := (@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 2) Real.pi 1 2 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 qz407 BSN.pi_near_15 rfl)

noncomputable abbrev qz408 := (Real.arctan (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 9000) (@Nat.cast Real Real.instNatCast 272884)))

noncomputable def ep587 := @Enclosure.Real.IsNear.subLit_ff_p qz97 qz408 884279719003555 562949953421312 1 2000000000000000 34570 1048576 1 392926 907773310744096931840 865720091575715 562949953421312 1000000000196463 392926000000000000000 qz98 (ep586 rfl) rfl rfl

noncomputable abbrev qz409 := (Complex.mk qz651 qz650)

noncomputable abbrev qz410 := (Real.arctan (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 272884) (@Nat.cast Real Real.instNatCast 9000)))

noncomputable def ep588 := @Enclosure.Complex.IsNear.re_isNear qz91 Bool.false 9510016419059429 2251799813685248 125000000589389 98231500000000000000 Bool.false 865720091575715 562949953421312 1000000000196463 392926000000000000000 (ep580 (@congrArg Complex Complex qz86 qz409 Complex.log (BSN.w_shift_mk qz12 Bool.false 136442 1000 2 qz13 rfl)) (@Enclosure.Complex.IsNear.of_parts qz406 Bool.false 9510016419059429 2251799813685248 125000000589389 98231500000000000000 Bool.false 865720091575715 562949953421312 1000000000196463 392926000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz406) (@HMul.hMul Real Real Real qz0 qz96 qz652) Bool.false 9510016419059429 2251799813685248 125000000589389 98231500000000000000 (Enclosure.clog_re_eq 9000 272884 4000 74546677456 16000000 rfl rfl rfl) (ep585 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz406) qz410 Bool.false 865720091575715 562949953421312 1000000000196463 392926000000000000000 (Enclosure.clog_im_eq 9000 272884 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz410 (@HSub.hSub Real Real Real qz396 qz97 qz408) Bool.false 865720091575715 562949953421312 1000000000196463 392926000000000000000 (BSN.arctan_recip 272884 9000 rfl rfl) ep587))))

noncomputable def ep589 := @Enclosure.Real.IsNear.mulLit_ff qz94 qz95 272884 4000 0 1 865720091575715 562949953421312 1000000000196463 392926000000000000000

noncomputable def ep590 := @Enclosure.Complex.IsNear.im_isNear qz90 Bool.false 7000 4000 0 1 Bool.false 272884 4000 0 1

noncomputable def ep591 := @Enclosure.Complex.IsNear.im_isNear qz91 Bool.false 9510016419059429 2251799813685248 125000000589389 98231500000000000000 Bool.false 865720091575715 562949953421312 1000000000196463 392926000000000000000 (ep580 (@congrArg Complex Complex qz86 qz409 Complex.log (BSN.w_shift_mk qz12 Bool.false 136442 1000 2 qz13 rfl)) (@Enclosure.Complex.IsNear.of_parts qz406 Bool.false 9510016419059429 2251799813685248 125000000589389 98231500000000000000 Bool.false 865720091575715 562949953421312 1000000000196463 392926000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz406) (@HMul.hMul Real Real Real qz0 qz96 qz652) Bool.false 9510016419059429 2251799813685248 125000000589389 98231500000000000000 (Enclosure.clog_re_eq 9000 272884 4000 74546677456 16000000 rfl rfl rfl) (ep585 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz406) qz410 Bool.false 865720091575715 562949953421312 1000000000196463 392926000000000000000 (Enclosure.clog_im_eq 9000 272884 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz410 (@HSub.hSub Real Real Real qz396 qz97 qz408) Bool.false 865720091575715 562949953421312 1000000000196463 392926000000000000000 (BSN.arctan_recip 272884 9000 rfl rfl) ep587))))

noncomputable abbrev qz99 := (@ep579 1 (BSN.w_sub_half_mk qz277 Bool.false 136442 1000 2 qz279 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7000 4000) qz405 Bool.false 7000 4000 0 1 Bool.false 272884 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 7000 4000) (Enclosure.Real.IsNear.const Bool.false 272884 4000)))

noncomputable def ep592 := @ep575 68221000013402902323 392926000000000000000000 ep576 21959863273619341131 225179981368524800 69096000017528625323 392926000000000000000000 (@ep577 66570114933416003 9007199254740992 875000004125723 392926000000000000000 (ep578 qz99) ep588 rfl) (@ep589 11812058073477370603 112589990684262400 68221000013402902323 392926000000000000000000 (ep590 qz99) ep591 rfl) rfl

noncomputable def ep593 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz92 qz95) (@HMul.hMul Real Real Real qz0 qz94 qz93) 6060040641030005 2251799813685248 7000000001375241 1571704000000000000000 648782830124653305809 2251799813685248000

noncomputable def ep594 := nat_lit 1474575054383278613603370036082245632

noncomputable def ep595 := @Enclosure.Real.IsNear.mulLit_ff qz92 qz95 7000 4000 0 1 865720091575715 562949953421312 1000000000196463 392926000000000000000

noncomputable def ep596 := @Enclosure.Real.IsNear.mulLit_ff qz94 qz93 272884 4000 0 1 9510016419059429 2251799813685248 125000000589389 98231500000000000000

noncomputable def ep597 := @ep593 8527625040208706969 98231500000000000000000 ep594 654842870765683310809 2251799813685248000 17930250080589319063 196463000000000000000000 (@ep595 6060040641030005 2251799813685248 7000000001375241 1571704000000000000000 (ep578 qz99) ep591 rfl) (@ep596 648782830124653305809 2251799813685248000 8527625040208706969 98231500000000000000000 (ep590 qz99) ep588 rfl) rfl

noncomputable def ep598 := @Enclosure.Complex.IsNear.of_eq qz86 qz409 Bool.false 9000 4000 0 1 Bool.false 272884 4000 0 1 (BSN.w_shift_mk qz12 Bool.false 136442 1000 2 qz13 rfl)

noncomputable abbrev qz411 := (ep598 (@Enclosure.Complex.IsNear.mk qz651 qz650 Bool.false 9000 4000 0 1 Bool.false 272884 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 9000 4000) (Enclosure.Real.IsNear.const Bool.false 272884 4000)))

noncomputable abbrev qz100 := qz411

noncomputable def ep599 := ep573 (@ep574 196463000000000000000000 (ep592 rfl) (ep597 rfl)) qz100 rfl rfl rfl rfl rfl rfl

noncomputable abbrev qz101 := qz400

noncomputable def ep600 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re qz101) (Complex.re ↑qz2)) (@HMul.hMul Real Real Real qz0 (Complex.im qz101) (Complex.im ↑qz2)) 120447 131072 1 524288 0 1 0 1 120447 120447

noncomputable def ep601 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re qz101) (Complex.re ↑qz2) 1 2 0 1 120447 65536 1 262144 120447 131072 1 524288

noncomputable abbrev qz102 := (@Enclosure.Complex.IsNear.of_eq qz400 (Complex.mk (Enclosure.sfrac Bool.false 1 2) qz544) Bool.false 1 2 0 1 Bool.false 0 1 0 1 BSN.half_c_mk (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 2) qz544 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz407 qz546))

noncomputable def ep602 := ep601 (@Enclosure.Complex.IsNear.re_isNear qz101 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz102) (@Enclosure.Real.IsNear.of_eq (Complex.re ↑qz2) qz2 Bool.false 120447 65536 1 262144 (Complex.ofReal_re qz2) EMRow47.d4)

noncomputable def ep603 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz101) (Complex.im ↑qz2) 0 1 0 1 0 1 0 1 0 1 0 1

noncomputable def ep604 := ep603 (@Enclosure.Complex.IsNear.im_isNear qz101 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz102) (@Enclosure.Real.IsNear.of_eq (Complex.im ↑qz2) qz10 Bool.false 0 1 0 1 (@Eq.trans Real (Complex.im ↑qz2) (0 : Real) qz10 (Complex.ofReal_im qz2) Enclosure.sfrac_zero_eq) qz21)

noncomputable def ep605 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re qz101) (Complex.im ↑qz2)) (@HMul.hMul Real Real Real qz0 (Complex.im qz101) (Complex.re ↑qz2)) 0 1 0 1 0 1 0 1 0 0

noncomputable def ep606 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re qz101) (Complex.im ↑qz2) 1 2 0 1 0 1 0 1 0 1 0 1

noncomputable def ep607 := ep606 (@Enclosure.Complex.IsNear.re_isNear qz101 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz102) (@Enclosure.Real.IsNear.of_eq (Complex.im ↑qz2) qz10 Bool.false 0 1 0 1 (@Eq.trans Real (Complex.im ↑qz2) (0 : Real) qz10 (Complex.ofReal_im qz2) Enclosure.sfrac_zero_eq) qz21)

noncomputable def ep608 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz101) (Complex.re ↑qz2) 0 1 0 1 120447 65536 1 262144 0 1 0 1

noncomputable def ep609 := ep608 (@Enclosure.Complex.IsNear.im_isNear qz101 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz102) (@Enclosure.Real.IsNear.of_eq (Complex.re ↑qz2) qz2 Bool.false 120447 65536 1 262144 (Complex.ofReal_re qz2) EMRow47.d4)

noncomputable def ep610 := @ep570 17930250080589319063 196463000000000000000000 (ep599 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@Enclosure.Complex.IsNear.mul qz101 (↑qz2) Bool.false 120447 131072 1 524288 Bool.false 0 1 0 1 (@ep600 131072 1 524288 (ep602 rfl) (ep604 rfl) rfl rfl) (@ep605 1 0 1 (ep607 rfl) (ep609 rfl) rfl rfl))

noncomputable abbrev qz103 := (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 1)

noncomputable abbrev qz412 := (@Nat.cast Complex Complex.instNatCast 1)

noncomputable abbrev qz104 := (@HMul.hMul Complex Complex Complex qz392 (@HMul.hMul Complex Complex Complex qz392 (2 : Complex) qz412) (@HSub.hSub Complex Complex Complex qz393 (@HMul.hMul Complex Complex Complex qz392 (2 : Complex) qz412) (1 : Complex)))

noncomputable abbrev qz413 := (@HPow.hPow Complex Int Complex qz649 qz645 (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) (@OfNat.ofNat Int 1 (@instOfNat 1)) (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (@OfNat.ofNat Int 2 (@instOfNat 2)) (@Nat.cast Int instNatCastInt 1))))

noncomputable abbrev qz105 := qz413

noncomputable def ep611 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz84 2 k))) (@HMul.hMul Complex Complex Complex qz76 (@HMul.hMul Complex Complex Complex qz76 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz77 (@HMul.hMul Complex Complex Complex qz76 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz85 qz86 (@HSub.hSub Int Int Int qz403 qz87 (@HMul.hMul Int Int Int qz404 qz88 (@Nat.cast Int instNatCastInt k))))) (@HAdd.hAdd Complex Complex Complex qz4 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz84 2 k))) (@HMul.hMul Complex Complex Complex qz76 (@HMul.hMul Complex Complex Complex qz76 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz77 (@HMul.hMul Complex Complex Complex qz76 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz85 qz86 (@HSub.hSub Int Int Int qz403 qz87 (@HMul.hMul Int Int Int qz404 qz88 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 (@Rat.cast Complex Complex.instRatCast (bernoulli qz103)) qz104) qz105)) Bool.false 2765493 68719476736 3 68719476736

noncomputable def ep612 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz84 2 k))) (@HMul.hMul Complex Complex Complex qz76 (@HMul.hMul Complex Complex Complex qz76 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz77 (@HMul.hMul Complex Complex Complex qz76 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz85 qz86 (@HSub.hSub Int Int Int qz403 qz87 (@HMul.hMul Int Int Int qz404 qz88 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 (@Rat.cast Complex Complex.instRatCast (bernoulli qz103)) qz104) qz105) Bool.false 0 1 0 1 Bool.false

noncomputable def ep613 := @ep612 0 1 0 1 Bool.false 2765493 68719476736 3 68719476736 Bool.true 20962744217 17179869184000 68221 51539607552000 Bool.false 2765493 2765493 68719476736 3 68719476736 Bool.true 20962744217 20962744217 17179869184000 68221

noncomputable def ep614 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz84 2 k))) (@HMul.hMul Complex Complex Complex qz76 (@HMul.hMul Complex Complex Complex qz76 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz77 (@HMul.hMul Complex Complex Complex qz76 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz85 qz86 (@HSub.hSub Int Int Int qz403 qz87 (@HMul.hMul Int Int Int qz404 qz88 (@Nat.cast Int instNatCastInt k))))) (Complex.mk qz10 qz10) Bool.false 0 1 0 1 Bool.false

noncomputable def ep615 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz83 (@Rat.cast Complex Complex.instRatCast (bernoulli qz103)) qz104) qz105 Bool.false 2765493 68719476736 3 68719476736 Bool.true 20962744217 17179869184000 68221 51539607552000

noncomputable abbrev qz106 := (Complex.re qz413)

noncomputable abbrev qz107 := (Complex.im qz413)

noncomputable def ep616 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz83 (@Rat.cast Complex Complex.instRatCast (bernoulli qz103)) qz104)) qz106) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz83 (@Rat.cast Complex Complex.instRatCast (bernoulli qz103)) qz104)) qz107) 2765493 68719476736 3 68719476736 0 1 0

noncomputable def ep617 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz83 (@Rat.cast Complex Complex.instRatCast (bernoulli qz103)) qz104)) qz106 1 12 0 1 8296479 17179869184 9 17179869184 2765493

noncomputable def ep618 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz83 (@Rat.cast Complex Complex.instRatCast (bernoulli qz103)) qz104) (Complex.mk (Enclosure.sfrac Bool.false 1 12) qz10) Bool.false 1 12 0 1 Bool.false 0 1 0 1

noncomputable abbrev qz414 := (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 12) qz10 Bool.false 1 12 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 12) qz21)

noncomputable def ep619 := @Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz83 (@Rat.cast Complex Complex.instRatCast (bernoulli qz103)) qz104) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (ep618 (BSN.stirling_coeff_mk 1 1 6 Bool.false BSN.bern_real_1 rfl rfl) qz414)

noncomputable def ep620 := @Enclosure.Complex.IsNear.re_isNear qz105 Bool.false 8296479 17179869184 9 17179869184 Bool.true 62888232651 4294967296000 68221 4294967296000

noncomputable abbrev qz654 := (@instHPow Complex Nat (@NPow.toPow Complex (@Monoid.toNPow Complex (@Semiring.toMonoid Complex Complex.instSemiring))))

noncomputable abbrev qz415 := (@HPow.hPow Complex Nat Complex qz654 qz645 1)

noncomputable abbrev qz108 := (@Inv.inv Complex Complex.instInv qz415)

noncomputable def ep621 := @Enclosure.Complex.IsNear.of_eq qz105 qz108 Bool.false 8296479 17179869184 9 17179869184 Bool.true 62888232651 4294967296000 68221

noncomputable def ep622 := @Enclosure.Complex.IsNear.of_parts qz108 Bool.false 8296479 17179869184 9 17179869184 Bool.true 62888232651 4294967296000 68221

noncomputable abbrev qz109 := (Complex.re qz415)

noncomputable abbrev qz110 := (@MonoidWithZeroHom Complex Real (@instMulZeroOneClassOfSemiring Complex Complex.instSemiring) (@instMulZeroOneClassOfSemiring Real Real.semiring))

noncomputable abbrev qz111 := (@MonoidWithZeroHom.funLike Complex Real (@instMulZeroOneClassOfSemiring Complex Complex.instSemiring) (@instMulZeroOneClassOfSemiring Real Real.semiring))

noncomputable abbrev qz112 := qz415

noncomputable def ep623 := @Enclosure.Real.IsNear.mulLit_ff qz109 (@Inv.inv Real Real.instInv (@DFunLike.coe qz110 Complex (fun (x : Complex) => Real) qz111 Complex.normSq qz112)) 9000 4000 0 1 921831 4294967296 1 4294967296

noncomputable def ep624 := @Enclosure.Complex.IsNear.re_isNear qz112 Bool.false 9000 4000 0 1 Bool.false 272884 4000 0 1

noncomputable def ep625 := @Enclosure.Complex.IsNear.of_eq qz112 qz86 Bool.false 9000 4000 0 1 Bool.false 272884 4000 0

noncomputable def ep626 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (@DFunLike.coe qz110 Complex (fun (x : Complex) => Real) qz111 Complex.normSq qz112)) Bool.false 921831 4294967296 1 4294967296 921831 4294967296 1

noncomputable abbrev qz113 := (Complex.im qz415)

noncomputable abbrev qz416 := (@instHAdd Real Real.instAdd)

noncomputable def ep627 := @Enclosure.Real.IsNear.of_eq (@DFunLike.coe qz110 Complex (fun (x : Complex) => Real) qz111 Complex.normSq qz112) (@HAdd.hAdd Real Real Real qz416 (@HMul.hMul Real Real Real qz0 qz109 qz109) (@HMul.hMul Real Real Real qz0 qz113 qz113)) Bool.false 4659167341 1000000 0 1

noncomputable def ep628 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz109 qz109) (@HMul.hMul Real Real Real qz0 qz113 qz113) 81 16 0 1 4654104841 1000000

noncomputable def ep629 := @Enclosure.Real.IsNear.mulLit_ff qz109 qz109 9000 4000 0 1 9000 4000 0 1

noncomputable def ep630 := @Enclosure.Real.IsNear.mulLit_ff qz113 qz113 272884 4000 0 1 272884 4000 0 1

noncomputable def ep631 := @Enclosure.Complex.IsNear.im_isNear qz112 Bool.false 9000 4000 0 1 Bool.false 272884 4000 0 1

noncomputable abbrev qz114 := (ep624 (@ep625 1 (BSN.pow_one_c qz394) qz411))

noncomputable abbrev qz115 := (ep631 (@ep625 1 (BSN.pow_one_c qz394) qz411))

noncomputable def ep632 := @ep628 0 1 74546677456 4659167341 1000000 0 1 (@ep629 81 16 0 1 qz114 qz114 rfl) (@ep630 4654104841 1000000 0 1 qz115 qz115 rfl)

noncomputable def ep633 := @Enclosure.Real.IsNear.inv_image (@DFunLike.coe qz110 Complex (fun (x : Complex) => Real) qz111 Complex.normSq qz112) 4659167341 1000000 0 1 460915 460916 2147483648 (ep627 (Enclosure.Complex.normSq_eq_mul_add_mul qz112) (ep632 rfl rfl)) rfl

noncomputable def ep634 := @Enclosure.Real.IsNear.of_eq (Complex.re qz108) (@HMul.hMul Real Real Real qz0 qz109 (@Inv.inv Real Real.instInv (@DFunLike.coe qz110 Complex (fun (x : Complex) => Real) qz111 Complex.normSq qz112))) Bool.false 8296479 17179869184 9 17179869184 (Enclosure.Complex.inv_re_eq_mul qz112) (@ep623 8296479 17179869184 9 17179869184 qz114 (@ep626 4294967296 (ep633 rfl rfl rfl rfl rfl) rfl) rfl)

noncomputable def ep635 := @Enclosure.Real.IsNear.of_eq (Complex.im qz108) (@HMul.hMul Real Real Real qz0 (@Neg.neg Real Real.instNeg qz113) (@Inv.inv Real Real.instInv (@DFunLike.coe qz110 Complex (fun (x : Complex) => Real) qz111 Complex.normSq qz112))) Bool.true 62888232651 4294967296000 68221 4294967296000 (Enclosure.Complex.inv_im_eq_mul qz112)

noncomputable def ep636 := @Enclosure.Real.IsNear.mulLit_tf (@Neg.neg Real Real.instNeg qz113) (@Inv.inv Real Real.instInv (@DFunLike.coe qz110 Complex (fun (x : Complex) => Real) qz111 Complex.normSq qz112)) 272884 4000 0 1 921831 4294967296 1

noncomputable def ep637 := @ep636 4294967296 62888232651 4294967296000 68221 4294967296000 (@Enclosure.Real.IsNear.neg qz113 Bool.false 272884 4000 0 1 qz115) (@ep626 4294967296 (ep633 rfl rfl rfl rfl rfl) rfl) rfl

noncomputable def ep638 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz83 (@Rat.cast Complex Complex.instRatCast (bernoulli qz103)) qz104)) qz107 0 1 0 1 62888232651 4294967296000 68221 4294967296000 0

noncomputable def ep639 := @Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz83 (@Rat.cast Complex Complex.instRatCast (bernoulli qz103)) qz104) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (ep618 (BSN.stirling_coeff_mk 1 1 6 Bool.false BSN.bern_real_1 rfl rfl) qz414)

noncomputable def ep640 := @Enclosure.Complex.IsNear.im_isNear qz105 Bool.false 8296479 17179869184 9 17179869184 Bool.true 62888232651 4294967296000 68221 4294967296000

noncomputable abbrev qz116 := (@ep621 4294967296000 (BSN.zpow_one_sub_two_mul qz394 1 1 rfl rfl) (@ep622 4294967296000 ep634 (ep635 ep637)))

noncomputable def ep641 := @ep616 1 2765493 2765493 68719476736 3 68719476736 (@ep617 68719476736 3 68719476736 ep619 (ep620 qz116) rfl) (@ep638 1 0 1 ep639 (ep640 qz116) rfl) rfl

noncomputable def ep642 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz83 (@Rat.cast Complex Complex.instRatCast (bernoulli qz103)) qz104)) qz107) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz83 (@Rat.cast Complex Complex.instRatCast (bernoulli qz103)) qz104)) qz106) 20962744217 17179869184000 68221 51539607552000 0 1 0

noncomputable def ep643 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HDiv.hDiv Complex Complex Complex qz83 (@Rat.cast Complex Complex.instRatCast (bernoulli qz103)) qz104)) qz107 1 12 0 1 62888232651 4294967296000 68221 4294967296000 20962744217

noncomputable def ep644 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz83 (@Rat.cast Complex Complex.instRatCast (bernoulli qz103)) qz104)) qz106 0 1 0 1 8296479 17179869184 9 17179869184 0

noncomputable def ep645 := @ep642 1 20962744217 20962744217 17179869184000 68221 51539607552000 (@ep643 17179869184000 68221 51539607552000 ep619 (ep640 qz116) rfl) (@ep644 1 0 1 ep639 (ep620 qz116) rfl) rfl

noncomputable abbrev qz117 := (@Enclosure.Complex.IsNear.mk qz544 qz544 Bool.false 0 1 0 1 Bool.false 0 1 0 1 qz546 qz546)

noncomputable def ep646 := @ep613 51539607552000 (@ep614 0 1 0 1 (BSN.stirling_sum_base qz86) qz117) (ep615 (ep641 rfl) (ep645 rfl)) rfl rfl rfl rfl rfl

noncomputable def ep647 := @ep567 501220088047451996377 2251799813685248000 ep559 ep550 (ep610 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep611 Bool.true 20962744217 17179869184000 68221 51539607552000 (BSN.stirling_sum_succ qz86 0 1 rfl) (ep646 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl

noncomputable def ep648 := @Enclosure.Complex.IsNear.of_eq (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz79 (@Nat.cast Complex Complex.instNatCast j))) (BSN.logSumC qz12 2) Bool.false 9508988848133861 1125899906842624 125000000589389 49115750000000000000 Bool.false 878091744871843 281474976710656

noncomputable abbrev qz118 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz272 qz395 qz412))

noncomputable def ep649 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz12 2) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.logSumC qz12 1) qz118) Bool.false 9508988848133861 1125899906842624 125000000589389 49115750000000000000 Bool.false 878091744871843 281474976710656 1000000000196463 196463000000000000000

noncomputable def ep650 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz12 1) qz118 Bool.false 9508807385765605 2251799813685248 125000000589389 98231500000000000000 Bool.false 882217060959651 562949953421312 1000000000196463 392926000000000000000 Bool.false

noncomputable def ep651 := nat_lit 42824678633125858377948049965056

noncomputable def ep652 := nat_lit 988643413750485194177649836032

noncomputable abbrev qz119 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz272 qz395 (@Nat.cast Complex Complex.instNatCast 0)))

noncomputable def ep653 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz12 1) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.logSumC qz12 0) qz119) Bool.false 9508807385765605 2251799813685248 125000000589389 98231500000000000000 Bool.false 882217060959651 562949953421312 1000000000196463 392926000000000000000

noncomputable def ep654 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz12 0) qz119 Bool.false 0 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable abbrev qz417 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz650))

noncomputable def ep655 := @Enclosure.Complex.IsNear.of_eq qz119 qz417 Bool.false 9508807385765605 2251799813685248 125000000589389 98231500000000000000 Bool.false 882217060959651 562949953421312 1000000000196463 392926000000000000000

noncomputable def ep656 := nat_lit 5762840829001712625676678332612075551746621440

noncomputable def ep657 := nat_lit 7835568486786402939904292521930233720864768

noncomputable def ep658 := nat_lit 19083537062349093953791102995077325324288

noncomputable def ep659 := BSN.log_dyadic_bound 8930677456 140002677456 3 2 ep656 1048576 392926 ep657 ep658 133957 148933354912 131072000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 8930677456) (BSN.artanhQ 140002677456) 0 2 ep657 ep656 ep658 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep660 := @Enclosure.Real.IsNear.mulLit_ff qz96 (Real.log (Enclosure.sfrac Bool.false 74466677456 16000000)) 1 2 0 1 9508807385765605 1125899906842624 125000000589389 49115750000000000000 9508807385765605 2251799813685248 125000000589389 98231500000000000000 qz407 (BSN.isNear_log_sfrac 74466677456 16000000 9508807385765605 1125899906842624 125000000589389 49115750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 74466677456) qz653)) Bool.false 319062630826769760911360 37778931862957161709568 1000000004715112 392926000000000000000 9508807385765605 1125899906842624 125000000589389 49115750000000000000 (BSN.log_rat_reduce_isNear 74466677456 16000000 12 148933354912 131072000000 133957 1048576 24973259072661432 36028797018963968 392926 1000000000000000 rfl rfl rfl rfl (ep659 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep661 := BSN.arctan_dyadic_bound_f 1000 272884 1 0 1048576 392926 0 1 1 0 1 1 3842 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 272884) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 272884) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz418 := (@Nat.cast Real Real.instNatCast 1000)

noncomputable abbrev qz419 := (@Nat.cast Real Real.instNatCast 272884)

noncomputable def ep662 := @Enclosure.Real.IsNear.subLit_ff_p qz97 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz418 qz419)) 884279719003555 562949953421312 1 2000000000000000 3842 1048576 1 392926 925071636912827006976 882217060959651 562949953421312 1000000000196463 392926000000000000000 qz98 (ep661 rfl) rfl rfl

noncomputable abbrev qz120 := (@HAdd.hAdd Complex Complex Complex qz272 qz395 (@Nat.cast Complex Complex.instNatCast 0))

noncomputable abbrev qz420 := (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz650)

noncomputable def ep663 := @ep654 9508807385765605 2251799813685248 125000000589389 98231500000000000000 Bool.false 882217060959651 562949953421312 1000000000196463 392926000000000000000 Bool.false 9508807385765605 9508807385765605 2251799813685248 125000000589389 98231500000000000000 Bool.false 882217060959651 882217060959651 562949953421312 1000000000196463 392926000000000000000 (@Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz12 0) (Complex.mk qz10 qz10) Bool.false 0 1 0 1 Bool.false 0 1 0 1 (BSN.log_sum_c_base qz12) qz117) (ep655 (@congrArg Complex Complex qz120 qz420 Complex.log (BSN.w_shift_mk qz12 Bool.false 136442 1000 0 qz13 rfl)) (@Enclosure.Complex.IsNear.of_parts qz417 Bool.false 9508807385765605 2251799813685248 125000000589389 98231500000000000000 Bool.false 882217060959651 562949953421312 1000000000196463 392926000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz417) (@HMul.hMul Real Real Real qz0 qz96 (Real.log (Enclosure.sfrac Bool.false 74466677456 16000000))) Bool.false 9508807385765605 2251799813685248 125000000589389 98231500000000000000 (Enclosure.clog_re_eq 1000 272884 4000 74466677456 16000000 rfl rfl rfl) (ep660 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz417) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz419 qz418)) Bool.false 882217060959651 562949953421312 1000000000196463 392926000000000000000 (Enclosure.clog_im_eq 1000 272884 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz419 qz418)) (@HSub.hSub Real Real Real qz396 qz97 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz418 qz419))) Bool.false 882217060959651 562949953421312 1000000000196463 392926000000000000000 (BSN.arctan_recip 272884 1000 rfl rfl) ep662)))) rfl rfl

noncomputable abbrev qz421 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz650))

noncomputable def ep664 := @Enclosure.Complex.IsNear.of_eq qz118 qz421 Bool.false 9509170310502117 2251799813685248 125000000589389 98231500000000000000 Bool.false 873966428784035 562949953421312 1000000000196463 392926000000000000000

noncomputable def ep665 := nat_lit 5766793431930595736183705260159517686786621440

noncomputable def ep666 := nat_lit 7880536957180591413186412432971372408864768

noncomputable def ep667 := nat_lit 19289503269010993087364913795504333324288

noncomputable def ep668 := BSN.log_dyadic_bound 8954677456 140026677456 3 2 ep665 1048576 392926 ep666 ep667 134295 148981354912 131072000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 8954677456) (BSN.artanhQ 140026677456) 0 2 ep666 ep665 ep667 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep669 := @Enclosure.Real.IsNear.mulLit_ff qz96 (Real.log (Enclosure.sfrac Bool.false 74490677456 16000000)) 1 2 0 1 9509170310502117 1125899906842624 125000000589389 49115750000000000000 9509170310502117 2251799813685248 125000000589389 98231500000000000000 qz407 (BSN.isNear_log_sfrac 74490677456 16000000 9509170310502117 1125899906842624 125000000589389 49115750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 74490677456) qz653)) Bool.false 319074808560162170732544 37778931862957161709568 1000000004715112 392926000000000000000 9509170310502117 1125899906842624 125000000589389 49115750000000000000 (BSN.log_rat_reduce_isNear 74490677456 16000000 12 148981354912 131072000000 134295 1048576 24973259072661432 36028797018963968 392926 1000000000000000 rfl rfl rfl rfl (ep668 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep670 := BSN.arctan_dyadic_bound_f 5000 272884 1 0 1048576 392926 0 1 1 0 1 1 19210 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 5000) (BSN.arctanEvenQ 272884) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 5000) (BSN.arctanOddQ 272884) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz422 := (@Nat.cast Real Real.instNatCast 5000)

noncomputable def ep671 := @Enclosure.Real.IsNear.subLit_ff_p qz97 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz422 qz419)) 884279719003555 562949953421312 1 2000000000000000 19210 1048576 1 392926 916420222028648284160 873966428784035 562949953421312 1000000000196463 392926000000000000000 qz98 (ep670 rfl) rfl rfl

noncomputable abbrev qz121 := (@HAdd.hAdd Complex Complex Complex qz272 qz395 qz412)

noncomputable abbrev qz423 := (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz650)

noncomputable def ep672 := @ep650 9509170310502117 2251799813685248 125000000589389 98231500000000000000 Bool.false 873966428784035 562949953421312 1000000000196463 392926000000000000000 Bool.false ep651 9508988848133861 1125899906842624 125000000589389 49115750000000000000 Bool.false ep652 878091744871843 281474976710656 1000000000196463 196463000000000000000 (ep653 (BSN.log_sum_c_succ qz12 0 1 rfl) (ep663 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep664 (@congrArg Complex Complex qz121 qz423 Complex.log (BSN.w_shift_mk qz12 Bool.false 136442 1000 1 qz13 rfl)) (@Enclosure.Complex.IsNear.of_parts qz421 Bool.false 9509170310502117 2251799813685248 125000000589389 98231500000000000000 Bool.false 873966428784035 562949953421312 1000000000196463 392926000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz421) (@HMul.hMul Real Real Real qz0 qz96 (Real.log (Enclosure.sfrac Bool.false 74490677456 16000000))) Bool.false 9509170310502117 2251799813685248 125000000589389 98231500000000000000 (Enclosure.clog_re_eq 5000 272884 4000 74490677456 16000000 rfl rfl rfl) (ep669 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz421) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz419 qz422)) Bool.false 873966428784035 562949953421312 1000000000196463 392926000000000000000 (Enclosure.clog_im_eq 5000 272884 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz419 qz422)) (@HSub.hSub Real Real Real qz396 qz97 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz422 qz419))) Bool.false 873966428784035 562949953421312 1000000000196463 392926000000000000000 (BSN.arctan_recip 272884 5000 rfl rfl) ep671)))) rfl rfl

noncomputable def ep673 := @ep560 ep550 Bool.false 9508988848133861 1125899906842624 125000000589389 49115750000000000000 Bool.false 878091744871843 281474976710656 1000000000196463 196463000000000000000 Bool.true ep561 24161380568997306931 225179981368524800 ep555 ep556 Bool.false ep562 494195354088477252377 2251799813685248000 ep552 ep550 (@ep563 225179981368524800 ep558 ep556 Bool.false 501220088047451996377 2251799813685248000 ep559 ep550 (BSN.logGammaStirling_unfold 1 qz86) (ep647 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (@ep648 1000000000196463 196463000000000000000 (BSN.log_sum_c_eq qz12 2) (ep649 (BSN.log_sum_c_succ qz12 1 2 rfl) (ep672 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)))

noncomputable abbrev qz122 := (@HDiv.hDiv Real Real Real qz270 qz277 (2 : Real))

noncomputable def ep674 := @Enclosure.Real.IsNear.mulLit_ff qz122 (Real.log Real.pi) 136442 2000 0 1 75021 65536 1 262144 5118007641 65536000 68221 262144000 (@Enclosure.Real.IsNear.of_eq qz122 (Enclosure.sfrac Bool.false 136442 2000) Bool.false 136442 2000 0 1 (BSN.t_half_eq qz12 Bool.false 136442 1000 qz13) (Enclosure.Real.IsNear.const Bool.false 136442 2000)) EMRow47.d5 rfl

noncomputable def ep675 := @ep553 68221 262144000 ep554 318341950578292382489 2251799813685248000 ep549 ep550 (@ep557 ep552 ep550 (ep673 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) ep674 rfl rfl

noncomputable def ep676 := BSN.cos_dyadic_bound_f 1192704 2147483648 1 0 1048576 393310 0 1 1 0 1 1 1048575 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 1192704) qz15 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 1192704) qz16 0 0 rfl) rfl rfl

noncomputable def ep677 := @ep548 1048576 Bool.true 1048575 1048576 1 196463 (@ep551 74119761 524288 375 1048576 ep675 rfl) (Enclosure.sfrac_false_div 74119761 524288) (BSN.cos_reduce2 qz397 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 41964550285261012992) qz24) 226375608064910080 72057594037927936 Bool.false 1048575 1048576 22 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q2 74119761 524288 226375608064910080 72057594037927936 22 41964550285261012992 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1048575 1048576 41964550285261012992 75557863725914323419136 1192704 2147483648 393310 392926 (ep676 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep678 := nat_lit 89552944408284134113280000

noncomputable def ep679 := nat_lit 232051164675531598887886777903

noncomputable def ep680 := nat_lit 35187680234569451680594657280000

noncomputable abbrev qz655 := (@Nat.cast Complex Complex.instNatCast 35)

noncomputable abbrev qz424 := (@HPow.hPow Complex Complex Complex qz535 qz655 qz536)

noncomputable abbrev qz123 := qz424

noncomputable abbrev qz425 := qz655

noncomputable abbrev qz124 := (@HAdd.hAdd Complex Complex Complex qz272 (@HDiv.hDiv Complex Complex Complex qz401 qz425 (@HSub.hSub Complex Complex Complex qz393 qz271 (1 : Complex))) qz400)

noncomputable abbrev qz125 := (@instHSub Nat instSubNat)

noncomputable abbrev qz426 := qz654

noncomputable abbrev qz126 := qz426

noncomputable abbrev qz127 := qz425

noncomputable def ep681 := @Enclosure.Complex.IsNear.of_eq (zetaApproximant qz5 1 35) (@HAdd.hAdd Complex Complex Complex qz4 (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 35, @HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast n) qz7) (@HMul.hMul Complex Complex Complex qz76 qz123 (@HAdd.hAdd Complex Complex Complex qz4 qz124 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz76 (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz84 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz84 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz84 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz126 qz127 (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz84 2 k) 1))))))) Bool.false ep543 ep544 ep545

noncomputable def ep682 := @Enclosure.Complex.IsNear.addLitP (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 35, @HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast n) qz7) (@HMul.hMul Complex Complex Complex qz76 qz123 (@HAdd.hAdd Complex Complex Complex qz4 qz124 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz76 (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz84 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz84 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz84 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz126 qz127 (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz84 2 k) 1)))))) Bool.false 1372720869279 274877906944 705125829242589 108006676463878144

noncomputable def ep683 := nat_lit 4750430641192359566577486547

noncomputable def ep684 := nat_lit 6999509925146544045715673

noncomputable def ep685 := nat_lit 2385185453695476662752952903

noncomputable def ep686 := nat_lit 42437059482828456936337493441143373824

noncomputable def ep687 := nat_lit 651882137189450889342829683433013248

noncomputable def ep688 := @ep682 Bool.false 78659171519 1099511627776 1409894539635095 216013352927756288 Bool.false 1052179719241486324519771 ep544 ep683 ep546 Bool.true ep684 ep678 ep685 ep680 Bool.false ep686 ep543 ep544 ep545 ep546 Bool.true ep687 592883349954218728583173 ep678

noncomputable def ep689 := @Enclosure.Complex.IsNear.of_eq (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 35, @HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast n) qz7) (BSN.headSumC qz5 35) Bool.false 1372720869279 274877906944 705125829242589 108006676463878144 Bool.false 78659171519 1099511627776 1409894539635095

noncomputable abbrev qz656 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 34) qz7)

noncomputable def ep690 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 35) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 34) qz656) Bool.false 1372720869279 274877906944 705125829242589 108006676463878144 Bool.false 78659171519 1099511627776 1409894539635095 216013352927756288

noncomputable def ep691 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 34) qz656 Bool.false 2829077868681 549755813888 692062410544063 108006676463878144 Bool.true 8383819009 1099511627776 1383855352633789 216013352927756288 Bool.true

noncomputable def ep692 := nat_lit 1509322557463039001493504

noncomputable abbrev qz657 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 33) qz7)

noncomputable def ep693 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 34) (@HAdd.hAdd Complex Complex Complex qz4 qz65 qz657) Bool.false 2829077868681 549755813888 692062410544063 108006676463878144 Bool.true 8383819009 1099511627776 1383855352633789 216013352927756288

noncomputable def ep694 := @Enclosure.Complex.IsNear.addLitP qz65 qz657 Bool.false 5485948446639 1099511627776 1357569411645329 216013352927756288 Bool.true 22980239781 274877906944 21209302815645 3375208639496192 Bool.false

noncomputable def ep695 := nat_lit 6221208024997006160166912

noncomputable abbrev qz658 := (Real.log (Enclosure.sfrac Bool.false 33 1))

noncomputable abbrev qz128 := (@HMul.hMul Real Real Real qz267 qz277 qz658)

noncomputable abbrev qz427 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 33)))

noncomputable def ep696 := @Enclosure.Complex.IsNear.of_eq qz657 (Complex.mk (@HMul.hMul Real Real Real qz0 qz427 (Real.cos qz128)) (@HMul.hMul Real Real Real qz0 qz427 (@Neg.neg Real Real.instNeg (Real.sin qz128)))) Bool.false 172207290723 1099511627776 26555409442797 216013352927756288 Bool.false 83537140115 1099511627776 26459972432509 216013352927756288 (BSN.cpow_neg_s_mk qz12 136442 1000 33 qz13 rfl)

noncomputable abbrev qz428 := (Real.sqrt (@Nat.cast Real Real.instNatCast 33))

noncomputable abbrev qz429 := (@Nat.cast Real Real.instNatCast 33)

noncomputable abbrev qz659 := (@HDiv.hDiv Real Real Real qz1 qz429 qz14)

noncomputable def ep697 := @Enclosure.Real.IsNear.inv_image qz428 6023611 1048576 1 1048576 91266 91267 524288 (@Enclosure.Real.IsNear.of_eq qz428 (Real.sqrt qz659) Bool.false 6023611 1048576 1 1048576 (BSN.sqrt_natCast_div_one 33) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz659) Bool.false 6023611 1048576 1 1048576 6023611 1048576 1 1048576 (BSN.sqrt_enclosure 33 1 3011805 3011806 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep698 := BSN.log_dyadic_bound 1 65 2 1 12675 524288 196463 1 1 16133 66 64 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 1) (BSN.artanhQ 65) 0 1 1 12675 1 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep699 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz658 136442 1000 0 1 15746868335186131 4503599627370496 200000000196463 39292600000000000000 1074267104694733042951 2251799813685248000 13644200013402902323 19646300000000000000000 qz18 (BSN.isNear_log_sfrac 33 1 15746868335186131 4503599627370496 200000000196463 39292600000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz659) Bool.false 66047152845744529997824 18889465931478580854784 1000000000982315 196463000000000000000 15746868335186131 4503599627370496 200000000196463 39292600000000000000 (BSN.log_rat_reduce_isNear 33 1 5 66 64 16133 524288 24973259072661432 36028797018963968 196463 1000000000000000 rfl rfl rfl rfl (ep698 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep700 := nat_lit 2146774642700603876655858174267028354812940234418626726816825514368941298295040

noncomputable def ep701 := nat_lit 1113063524563695013961360234653503277833843991645425859942983187084057518336

noncomputable def ep702 := nat_lit 5620702913747526075504643492224206685869779152252786928366063898187186354790656

noncomputable def ep703 := BSN.sin_dyadic_bound_f 2403338778 2147483648 3 2 1048576 393310 ep700 ep109 ep701 ep702 ep112 ep701 943431 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2403338778) qz19 0 2 ep700 ep109 ep701 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2403338778) qz20 0 2 ep702 ep112 ep701 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz430 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 250122301) qz23)

noncomputable def ep704 := @Enclosure.Real.IsNear.cos_image qz128 qz430 Bool.false 250122301 524288 365 524288 Bool.false 943431 1048576 1 196463 (@Enclosure.Real.IsNear.recentre' qz128 Bool.false 1074267104694733042951 2251799813685248000 13644200013402902323 19646300000000000000000 250122301 524288 365 524288 (ep699 rfl) rfl) (Enclosure.sfrac_false_div 250122301 524288) (BSN.cos_reduce3 qz430 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 84559965836753714020352) qz24) 226375608064910080 72057594037927936 Bool.false 943431 1048576 75 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q3 250122301 524288 226375608064910080 72057594037927936 75 84559965836753714020352 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 943431 1048576 84559965836753714020352 75557863725914323419136 2403338778 2147483648 393310 392926 (ep703 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep705 := nat_lit 1193147274177919351481681812474861754130670727562190593058211056065893635727616

noncomputable def ep706 := nat_lit 3577215695484630664417122716955278255836344494703280927454747201823512792146176

noncomputable def ep707 := BSN.cos_dyadic_bound_f 2403338778 2147483648 3 2 1048576 393310 ep705 ep78 ep701 ep706 ep81 ep701 457655 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2403338778) qz15 0 2 ep705 ep78 ep701 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2403338778) qz16 0 2 ep706 ep81 ep701 rfl rfl rfl rfl) rfl rfl

noncomputable def ep708 := @Enclosure.Real.IsNear.sin_image qz128 qz430 Bool.false 250122301 524288 365 524288 Bool.true 457655 1048576 1 196463 (@Enclosure.Real.IsNear.recentre' qz128 Bool.false 1074267104694733042951 2251799813685248000 13644200013402902323 19646300000000000000000 250122301 524288 365 524288 (ep699 rfl) rfl) (Enclosure.sfrac_false_div 250122301 524288) (BSN.sin_reduce3 qz430 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 84559965836753714020352) qz24) 226375608064910080 72057594037927936 Bool.false 457655 1048576 75 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q3 250122301 524288 226375608064910080 72057594037927936 75 84559965836753714020352 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 457655 1048576 84559965836753714020352 75557863725914323419136 2403338778 2147483648 393310 392926 (ep707 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz431 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 33))) Bool.false 182533 1048576 1 1048576 182533 1048576 1 1048576 (ep697 rfl rfl) rfl)

noncomputable def ep709 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz427 (Real.cos qz128)) (@HMul.hMul Real Real Real qz0 qz427 (@Neg.neg Real Real.instNeg (Real.sin qz128))) Bool.false 172207290723 1099511627776 26555409442797 216013352927756288 Bool.false 83537140115 1099511627776 26459972432509 216013352927756288 (@Enclosure.Real.IsNear.mulLit_ff qz427 (Real.cos qz128) 182533 1048576 1 1048576 943431 1048576 72233283 103003193344 172207290723 1099511627776 26555409442797 216013352927756288 qz431 (@Enclosure.Real.IsNear.recentre' (Real.cos qz128) Bool.false 943431 1048576 72233283 103003193344 943431 1048576 72233283 103003193344 (ep704 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz427 (@Neg.neg Real Real.instNeg (Real.sin qz128)) 182533 1048576 1 1048576 457655 1048576 72233283 103003193344 83537140115 1099511627776 26459972432509 216013352927756288 qz431 (@Enclosure.Real.IsNear.neg (Real.sin qz128) Bool.true 457655 1048576 72233283 103003193344 (@Enclosure.Real.IsNear.recentre' (Real.sin qz128) Bool.true 457655 1048576 72233283 103003193344 457655 1048576 72233283 103003193344 (ep708 rfl rfl) rfl)) rfl)

noncomputable def ep710 := @ep694 172207290723 1099511627776 26555409442797 216013352927756288 Bool.false 83537140115 1099511627776 26459972432509 216013352927756288 Bool.false ep695 2829077868681 549755813888 692062410544063 108006676463878144 Bool.true 2304526621391240298496 8383819009 1099511627776 1383855352633789 216013352927756288 EMRow47.d9 (ep696 ep709) rfl rfl

noncomputable abbrev qz660 := (Real.log (Enclosure.sfrac Bool.false 34 1))

noncomputable abbrev qz129 := (@HMul.hMul Real Real Real qz267 qz277 qz660)

noncomputable abbrev qz432 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 34)))

noncomputable def ep711 := @Enclosure.Complex.IsNear.of_eq qz656 (Complex.mk (@HMul.hMul Real Real Real qz0 qz432 (Real.cos qz129)) (@HMul.hMul Real Real Real qz0 qz432 (@Neg.neg Real Real.instNeg (Real.sin qz129)))) Bool.true 83636130123 549755813888 6531709349263 54003338231939072 Bool.false 1360046727 17179869184 13019593500653 108006676463878144 (BSN.cpow_neg_s_mk qz12 136442 1000 34 qz13 rfl)

noncomputable abbrev qz433 := (Real.sqrt (@Nat.cast Real Real.instNatCast 34))

noncomputable abbrev qz434 := (@Nat.cast Real Real.instNatCast 34)

noncomputable abbrev qz661 := (@HDiv.hDiv Real Real Real qz1 qz434 qz14)

noncomputable def ep712 := @Enclosure.Real.IsNear.inv_image qz433 6114197 1048576 1 1048576 89914 89915 524288 (@Enclosure.Real.IsNear.of_eq qz433 (Real.sqrt qz661) Bool.false 6114197 1048576 1 1048576 (BSN.sqrt_natCast_div_one 34) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz661) Bool.false 6114197 1048576 1 1048576 6114197 1048576 1 1048576 (BSN.sqrt_enclosure 34 1 3057098 3057099 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep713 := BSN.log_dyadic_bound 2 66 2 1 13068 524288 196463 4 4 31784 68 64 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 2) (BSN.artanhQ 66) 0 1 4 13068 4 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep714 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz660 136442 1000 0 1 15881309401485523 4503599627370496 200000000196463 39292600000000000000 1083438808678743864583 2251799813685248000 13644200013402902323 19646300000000000000000 qz18 (BSN.isNear_log_sfrac 34 1 15881309401485523 4503599627370496 200000000196463 39292600000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz661) Bool.false 66611039547888335060992 18889465931478580854784 1000000000982315 196463000000000000000 15881309401485523 4503599627370496 200000000196463 39292600000000000000 (BSN.log_rat_reduce_isNear 34 1 5 68 64 31784 524288 24973259072661432 36028797018963968 196463 1000000000000000 rfl rfl rfl rfl (ep713 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep715 := nat_lit 1127171041992687515064568959839867136

noncomputable def ep716 := BSN.cos_dyadic_bound_f 1030380084 2147483648 2 1 1048576 393310 ep715 ep61 ep715 ep715 ep62 ep715 930174 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1030380084) qz15 0 1 ep715 ep61 ep715 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1030380084) qz16 0 1 ep715 ep62 ep715 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz435 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 252257755) qz23)

noncomputable def ep717 := @Enclosure.Real.IsNear.cos_image qz129 qz435 Bool.false 252257755 524288 729 1048576 Bool.true 930174 1048576 1 196463 (@Enclosure.Real.IsNear.recentre' qz129 Bool.false 1083438808678743864583 2251799813685248000 13644200013402902323 19646300000000000000000 252257755 524288 729 1048576 (ep714 rfl) rfl) (Enclosure.sfrac_false_div 252257755 524288) (BSN.cos_reduce2 qz435 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 36253276270685711237120) qz24) 226375608064910080 72057594037927936 Bool.false 930174 1048576 76 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q2 252257755 524288 226375608064910080 72057594037927936 76 36253276270685711237120 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 930174 1048576 36253276270685711237120 75557863725914323419136 1030380084 2147483648 393310 392926 (ep716 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep718 := BSN.sin_dyadic_bound_f 1030380084 2147483648 2 1 1048576 393310 ep715 ep65 ep715 ep715 ep66 ep715 484032 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1030380084) qz19 0 1 ep715 ep65 ep715 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1030380084) qz20 0 1 ep715 ep66 ep715 rfl rfl rfl rfl) rfl rfl

noncomputable def ep719 := @Enclosure.Real.IsNear.sin_image qz129 qz435 Bool.false 252257755 524288 729 1048576 Bool.true 484032 1048576 1 196463 (@Enclosure.Real.IsNear.recentre' qz129 Bool.false 1083438808678743864583 2251799813685248000 13644200013402902323 19646300000000000000000 252257755 524288 729 1048576 (ep714 rfl) rfl) (Enclosure.sfrac_false_div 252257755 524288) (BSN.sin_reduce2 qz435 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 36253276270685711237120) qz24) 226375608064910080 72057594037927936 Bool.false 484032 1048576 76 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q2 252257755 524288 226375608064910080 72057594037927936 76 36253276270685711237120 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 484032 1048576 36253276270685711237120 75557863725914323419136 1030380084 2147483648 393310 392926 (ep718 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz436 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 34))) Bool.false 179829 1048576 1 1048576 179829 1048576 1 1048576 (ep712 rfl rfl) rfl)

noncomputable def ep720 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz432 (Real.cos qz129)) (@HMul.hMul Real Real Real qz0 qz432 (@Neg.neg Real Real.instNeg (Real.sin qz129))) Bool.true 83636130123 549755813888 6531709349263 54003338231939072 Bool.false 1360046727 17179869184 13019593500653 108006676463878144 (@Enclosure.Real.IsNear.mulLit_ft qz432 (Real.cos qz129) 179829 1048576 1 1048576 465087 524288 144270103 206006386688 83636130123 549755813888 6531709349263 54003338231939072 qz436 (@Enclosure.Real.IsNear.recentre' (Real.cos qz129) Bool.true 930174 1048576 144270103 206006386688 465087 524288 144270103 206006386688 (ep717 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz432 (@Neg.neg Real Real.instNeg (Real.sin qz129)) 179829 1048576 1 1048576 7563 16384 144270103 206006386688 1360046727 17179869184 13019593500653 108006676463878144 qz436 (@Enclosure.Real.IsNear.neg (Real.sin qz129) Bool.true 7563 16384 144270103 206006386688 (@Enclosure.Real.IsNear.recentre' (Real.sin qz129) Bool.true 484032 1048576 144270103 206006386688 7563 16384 144270103 206006386688 (ep719 rfl rfl) rfl)) rfl)

noncomputable def ep721 := @ep691 83636130123 549755813888 6531709349263 54003338231939072 Bool.false 1360046727 17179869184 13019593500653 108006676463878144 Bool.false ep692 1372720869279 274877906944 705125829242589 108006676463878144 Bool.false 1351354276818238570496 78659171519 1099511627776 1409894539635095 216013352927756288 (ep693 (BSN.head_sum_c_succ qz5 33 34 rfl rfl) (ep710 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep711 ep720) rfl rfl

noncomputable def ep722 := @Enclosure.Complex.IsNear.mul qz123 (@HAdd.hAdd Complex Complex Complex qz4 qz124 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz76 (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz84 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz84 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz84 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz126 qz127 (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz84 2 k) 1))))) Bool.false 1052179719241486324519771 ep544 ep683 ep546 Bool.true

noncomputable def ep723 := nat_lit 2149270665798819218718720

noncomputable abbrev qz130 := (Complex.re qz424)

noncomputable abbrev qz131 := (Complex.im qz424)

noncomputable def ep724 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 qz130 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz124 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz76 (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz84 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz84 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz84 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz126 qz127 (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz84 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz131 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz124 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz76 (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz84 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz84 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz84 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz126 qz127 (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz84 2 k) 1))))))) 49772343432566174594987 ep723 1044161535944612256931141

noncomputable def ep725 := nat_lit 17593840117284725840297328640

noncomputable def ep726 := nat_lit 2388023691433786812139697

noncomputable def ep727 := nat_lit 214927066579881921871872000

noncomputable def ep728 := nat_lit 573784497413910538852922547

noncomputable def ep729 := nat_lit 15829933039999147926956262026790736228425494691840

noncomputable def ep730 := @Enclosure.Real.IsNear.mulLit_ff qz130 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz124 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz76 (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz84 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz84 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz84 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz126 qz127 (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz84 2 k) 1)))))) 25449503467 549755813888 1601696291343 13500834557984768 1955729450561

noncomputable abbrev qz662 := (Real.log (Enclosure.sfrac Bool.false 35 1))

noncomputable abbrev qz132 := (@HMul.hMul Real Real Real qz267 qz277 qz662)

noncomputable abbrev qz133 := (Real.sin (@HMul.hMul Real Real Real qz267 qz277 qz662))

noncomputable abbrev qz663 := (@Nat.cast Real Real.instNatCast 35)

noncomputable abbrev qz437 := (@Inv.inv Real Real.instInv (Real.sqrt qz663))

noncomputable abbrev qz664 := (@Neg.neg Real Real.instNeg qz133)

noncomputable def ep731 := @Enclosure.Complex.IsNear.of_eq qz123 (Complex.mk (@HMul.hMul Real Real Real qz0 qz437 (Real.cos qz132)) (@HMul.hMul Real Real Real qz0 qz437 qz664)) Bool.false 25449503467 549755813888 1601696291343 13500834557984768 Bool.true 178744889885 1099511627776 25768851584481 216013352927756288 (BSN.cpow_neg_s_mk qz12 136442 1000 35 qz13 rfl)

noncomputable abbrev qz438 := (Real.sqrt qz663)

noncomputable abbrev qz439 := (@HDiv.hDiv Real Real Real qz1 qz663 qz14)

noncomputable def ep732 := @Enclosure.Real.IsNear.inv_image qz438 6203459 1048576 1 1048576 88620 88621 524288 (@Enclosure.Real.IsNear.of_eq qz438 (Real.sqrt qz439) Bool.false 6203459 1048576 1 1048576 (BSN.sqrt_natCast_div_one 35) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz439) Bool.false 6203459 1048576 1 1048576 6203459 1048576 1 1048576 (BSN.sqrt_enclosure 35 1 3101729 3101730 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep733 := BSN.log_dyadic_bound 3 67 2 1 13467 524288 196463 9 9 46982 70 64 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 3) (BSN.artanhQ 67) 0 1 9 13467 9 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz134 := qz662

noncomputable abbrev qz440 := (Real.log (@HDiv.hDiv Real Real Real qz1 qz663 qz14))

noncomputable def ep734 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz134 136442 1000 0 1 16011859227414739 4503599627370496 200000000196463 39292600000000000000 1092345048353460909319 2251799813685248000 13644200013402902323 19646300000000000000000 qz18 (BSN.isNear_log_sfrac 35 1 16011859227414739 4503599627370496 200000000196463 39292600000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' qz440 Bool.false 67158605204982549446656 18889465931478580854784 1000000000982315 196463000000000000000 16011859227414739 4503599627370496 200000000196463 39292600000000000000 (BSN.log_rat_reduce_isNear 35 1 5 70 64 46982 524288 24973259072661432 36028797018963968 196463 1000000000000000 rfl rfl rfl rfl (ep733 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep735 := nat_lit 2129982673196061990148485469218895038626374771039628696619375671134514507953281

noncomputable def ep736 := nat_lit 3542004033425636201562179705755463590624414721352461478797017511024450614401

noncomputable def ep737 := nat_lit 6382864011521334698042332048245174188697875483676181166900532978381494622631041

noncomputable def ep738 := BSN.cos_dyadic_bound_f 2777513199 2147483648 3 2 1048576 393310 ep735 ep78 ep736 ep737 ep81 ep736 287174 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2777513199) qz15 0 2 ep735 ep78 ep736 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2777513199) qz16 0 2 ep737 ep81 ep736 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz441 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 508662801) qz30)

noncomputable def ep739 := @Enclosure.Real.IsNear.cos_image qz132 qz441 Bool.false 508662801 1048576 729 1048576 Bool.false 287174 1048576 1 196463 (@Enclosure.Real.IsNear.recentre' qz132 Bool.false 1092345048353460909319 2251799813685248000 13644200013402902323 19646300000000000000000 508662801 1048576 729 1048576 (ep734 rfl) rfl) (Enclosure.sfrac_false_div 508662801 1048576) (BSN.cos_reduce0 qz441 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 195450115807133493624832) qz31) 226375608064910080 72057594037927936 Bool.false 287174 1048576 77 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q0 508662801 1048576 226375608064910080 72057594037927936 77 195450115807133493624832 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 287174 1048576 195450115807133493624832 151115727451828646838272 2777513199 2147483648 393310 392926 (ep738 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep740 := nat_lit 3831135208526171073306024100829406698654975056094249684731838594033306553824385

noncomputable def ep741 := nat_lit 10028190872942997019094200544553413460187733237364654712855810670307477578069121

noncomputable def ep742 := BSN.sin_dyadic_bound_f 2777513199 2147483648 3 2 1048576 393310 ep740 ep109 ep736 ep741 ep112 ep736 1008485 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2777513199) qz19 0 2 ep740 ep109 ep736 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2777513199) qz20 0 2 ep741 ep112 ep736 rfl rfl rfl rfl) rfl rfl

noncomputable def ep743 := @Enclosure.Real.IsNear.sin_image qz132 qz441 Bool.false 508662801 1048576 729 1048576 Bool.false 1008485 1048576 1 196463 (@Enclosure.Real.IsNear.recentre' qz132 Bool.false 1092345048353460909319 2251799813685248000 13644200013402902323 19646300000000000000000 508662801 1048576 729 1048576 (ep734 rfl) rfl) (Enclosure.sfrac_false_div 508662801 1048576) (BSN.sin_reduce0 qz441 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 195450115807133493624832) qz31) 226375608064910080 72057594037927936 Bool.false 1008485 1048576 77 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q0 508662801 1048576 226375608064910080 72057594037927936 77 195450115807133493624832 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1008485 1048576 195450115807133493624832 151115727451828646838272 2777513199 2147483648 393310 392926 (ep742 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz442 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz663)) Bool.false 177241 1048576 1 1048576 177241 1048576 1 1048576 (ep732 rfl rfl) rfl)

noncomputable def ep744 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz437 (Real.cos qz132)) (@HMul.hMul Real Real Real qz0 qz437 qz664) Bool.false 25449503467 549755813888 1601696291343 13500834557984768 Bool.true 178744889885 1099511627776 25768851584481 216013352927756288 (@Enclosure.Real.IsNear.mulLit_ff qz437 (Real.cos qz132) 177241 1048576 1 1048576 143587 524288 144270103 206006386688 25449503467 549755813888 1601696291343 13500834557984768 qz442 (@Enclosure.Real.IsNear.recentre' (Real.cos qz132) Bool.false 287174 1048576 144270103 206006386688 143587 524288 144270103 206006386688 (ep739 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz437 qz664 177241 1048576 1 1048576 1008485 1048576 144270103 206006386688 178744889885 1099511627776 25768851584481 216013352927756288 qz442 (@Enclosure.Real.IsNear.neg qz133 Bool.false 1008485 1048576 144270103 206006386688 (@Enclosure.Real.IsNear.recentre' qz133 Bool.false 1008485 1048576 144270103 206006386688 1008485 1048576 144270103 206006386688 (ep743 rfl rfl) rfl)) rfl)

noncomputable def ep745 := @ep730 3909500566440 0 1 49772343432566174594987 ep723 1044161535944612256931141 ep725 (@Enclosure.Complex.IsNear.re_isNear qz123 Bool.false 25449503467 549755813888 1601696291343 13500834557984768 Bool.true 178744889885 1099511627776 25768851584481 216013352927756288 (ep731 ep744))

noncomputable def ep746 := @Enclosure.Complex.IsNear.re_isNear (@HAdd.hAdd Complex Complex Complex qz4 qz124 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz76 (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz84 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz84 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz84 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz126 qz127 (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz84 2 k) 1))))) Bool.false 1955729450561 3909500566440 0 1 Bool.false

noncomputable def ep747 := @Enclosure.Complex.IsNear.addLitP qz124 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz76 (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz84 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz84 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz84 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz126 qz127 (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz84 2 k) 1)))) Bool.false 4645417341 9308334682 0 1 Bool.true 1193867500

noncomputable def ep748 := @ep747 4654167341 0 1 Bool.false 1 840 0 1 Bool.false 68221 210000 0 1 Bool.false 3911458901122 1955729450561 3909500566440 0 1 Bool.false 66799775170361 66799775170361 977375141610000 0 1

noncomputable abbrev qz135 := (@HDiv.hDiv Complex Complex Complex qz401 qz425 (@HSub.hSub Complex Complex Complex qz393 qz271 (1 : Complex)))

noncomputable def ep749 := @Enclosure.Complex.IsNear.addLitP qz135 qz101 Bool.true 70000000 74466677456 0 1 Bool.true 19101880000 74466677456 0 1

noncomputable def ep750 := @Enclosure.Complex.IsNear.of_eq qz135 (Complex.mk (Enclosure.sfrac Bool.true 70000000 74466677456) (Enclosure.sfrac Bool.true 19101880000 74466677456)) Bool.true 70000000 74466677456 0 1 Bool.true 19101880000 74466677456 0 1

noncomputable def ep751 := @ep749 Bool.false 1 2 0 1 Bool.false 0 1 0 1 Bool.false 74326677456 4645417341 9308334682 0 1 Bool.true 19101880000 1193867500 4654167341 0 1 (ep750 (BSN.N_div_s_sub_one_mk qz12 136442 1000 35 qz13 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 70000000 74466677456) (Enclosure.sfrac Bool.true 19101880000 74466677456) Bool.true 70000000 74466677456 0 1 Bool.true 19101880000 74466677456 0 1 (Enclosure.Real.IsNear.const Bool.true 70000000 74466677456) (Enclosure.Real.IsNear.const Bool.true 19101880000 74466677456))) qz102 rfl

noncomputable abbrev qz136 := (@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 1)))

noncomputable abbrev qz443 := (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz654 qz655 1))

noncomputable abbrev qz137 := qz443

noncomputable def ep752 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz76 (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz84 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz84 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz84 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz126 qz127 (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz84 2 k) 1)))) (@HAdd.hAdd Complex Complex Complex qz4 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz76 (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz84 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz84 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz84 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz126 qz127 (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz84 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz76 (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz103)) ↑qz136) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz137)) Bool.false 1 840 0 1

noncomputable def ep753 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz76 (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz84 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz84 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz84 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz126 qz127 (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz84 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz76 (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz103)) ↑qz136) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz137) Bool.false 0 1 0 1 Bool.false

noncomputable def ep754 := @ep753 0 1 0 1 Bool.false 1 840 0 1 Bool.false 68221 210000 0 1 Bool.false 1 1 840 0 1 Bool.false 68221 68221 210000 0

noncomputable def ep755 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz76 (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz84 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz84 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz84 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz126 qz127 (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz84 2 k) 1)))) (Complex.mk qz10 qz10) Bool.false 0 1 0 1 Bool.false

noncomputable def ep756 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz103)) ↑qz136) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz137 Bool.false 1 840 0 1 Bool.false 68221 210000 0 1

noncomputable abbrev qz138 := (Complex.re qz443)

noncomputable abbrev qz139 := (Complex.im qz443)

noncomputable def ep757 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz103)) ↑qz136) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) qz138) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz103)) ↑qz136) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) qz139) 1 840 0 1 0 1 0

noncomputable def ep758 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz103)) ↑qz136) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) qz138 1 24 0 1 1 35 0 1 1

noncomputable def ep759 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz103)) ↑qz136)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz103)) ↑qz136)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) 1 24 0 1 0 1 0 1 1

noncomputable def ep760 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz103)) ↑qz136)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 1 2 0 1 1 24 0

noncomputable def ep761 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz103)) ↑qz136) (Complex.mk (Enclosure.sfrac Bool.false 1 12) qz10) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (BSN.bern_coeff_mk 1 1 6 2 Bool.false BSN.bern_real_1 EMRow47.d10 rfl) qz414

noncomputable def ep762 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) qz5 Bool.false 1 2 0 1 Bool.false 136442 1000 0 1 (BSN.ascPochhammer_one_eval qz5)

noncomputable def ep763 := ep762 (@Enclosure.Complex.IsNear.of_eq qz5 (Complex.mk qz96 qz12) Bool.false 1 2 0 1 Bool.false 136442 1000 0 1 (BSN.s_crit_mk qz12 Bool.false 136442 1000 qz13) (@Enclosure.Complex.IsNear.mk qz96 qz12 Bool.false 1 2 0 1 Bool.false 136442 1000 0 1 qz407 qz18))

noncomputable def ep764 := @ep760 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz103)) ↑qz136) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep761) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 136442 1000 0 1 ep763)

noncomputable def ep765 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz103)) ↑qz136)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 136442 1000 0 1 0 1 0

noncomputable def ep766 := @ep765 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz103)) ↑qz136) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep761) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 136442 1000 0 1 ep763)

noncomputable def ep767 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz103)) ↑qz136)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz103)) ↑qz136)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) 68221 6000 0 1 0 1 0 1 68221

noncomputable def ep768 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz103)) ↑qz136)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 136442 1000 0 1 68221 6000 0

noncomputable def ep769 := @ep768 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz103)) ↑qz136) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep761) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 136442 1000 0 1 ep763)

noncomputable def ep770 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz103)) ↑qz136)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 1 2 0 1 0 1 0

noncomputable def ep771 := @ep770 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz103)) ↑qz136) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep761) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 136442 1000 0 1 ep763)

noncomputable def ep772 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz103)) ↑qz136) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 24 0 1 Bool.false 68221 6000 0 1 (@ep759 1 24 0 1 (ep764 rfl) (ep766 rfl) rfl rfl) (@ep767 68221 6000 0 1 (ep769 rfl) (ep771 rfl) rfl rfl)

noncomputable def ep773 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz103)) ↑qz136) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 68221 6000 0 1 ep772

noncomputable abbrev qz140 := (@Enclosure.Complex.IsNear.re_isNear qz443 Bool.false 1 35 0 1 Bool.false 0 1 0 1 (@Enclosure.Complex.IsNear.of_eq qz443 (Complex.mk (Enclosure.sfrac Bool.false 1 35) qz544) Bool.false 1 35 0 1 Bool.false 0 1 0 1 (BSN.natCast_pow_inv_mk 35 1 35 EMRow47.d11 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 35) qz544 Bool.false 1 35 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 35) qz546)))

noncomputable def ep774 := @ep758 840 0 1 ep773 qz140

noncomputable def ep775 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz103)) ↑qz136) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) qz139 68221 6000 0 1 0 1 0 1 0

noncomputable def ep776 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz103)) ↑qz136) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 68221 6000 0 1 ep772

noncomputable abbrev qz141 := (@Enclosure.Complex.IsNear.im_isNear qz443 Bool.false 1 35 0 1 Bool.false 0 1 0 1 (@Enclosure.Complex.IsNear.of_eq qz443 (Complex.mk (Enclosure.sfrac Bool.false 1 35) qz544) Bool.false 1 35 0 1 Bool.false 0 1 0 1 (BSN.natCast_pow_inv_mk 35 1 35 EMRow47.d11 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 35) qz544 Bool.false 1 35 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 35) qz546)))

noncomputable def ep777 := @ep775 1 0 1 ep776 qz141

noncomputable def ep778 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz103)) ↑qz136) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) qz139) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz103)) ↑qz136) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) qz138) 0 1 0 1 68221 210000 0

noncomputable def ep779 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz103)) ↑qz136) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) qz139 1 24 0 1 0 1 0 1 0

noncomputable def ep780 := @ep779 1 0 1 ep773 qz141

noncomputable def ep781 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz103)) ↑qz136) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) qz138 68221 6000 0 1 1 35 0 1 68221

noncomputable def ep782 := @ep781 210000 0 1 ep776 qz140

noncomputable def ep783 := @ep754 1 (@ep755 0 1 0 1 (BSN.bern_sum_base qz5 35) qz117) (ep756 (@ep757 1 1 1 840 0 1 (ep774 rfl) (ep777 rfl) rfl rfl) (@ep778 1 68221 68221 210000 0 1 (ep780 rfl) (ep782 rfl) rfl rfl)) rfl rfl rfl rfl rfl

noncomputable def ep784 := ep748 (ep751 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep752 Bool.false 68221 210000 0 1 (BSN.bern_sum_succ qz5 35 0 1 1 rfl rfl) (ep783 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl rfl

noncomputable def ep785 := @Enclosure.Real.IsNear.mulLit_tf qz131 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz124 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz76 (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz84 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz84 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz84 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz126 qz127 (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz84 2 k) 1)))))) 178744889885 1099511627776 25768851584481 216013352927756288 66799775170361

noncomputable def ep786 := @ep785 977375141610000 0 1 ep726 ep727 ep728 ep546 (@Enclosure.Complex.IsNear.im_isNear qz123 Bool.false 25449503467 549755813888 1601696291343 13500834557984768 Bool.true 178744889885 1099511627776 25768851584481 216013352927756288 (ep731 ep744))

noncomputable def ep787 := @Enclosure.Complex.IsNear.im_isNear (@HAdd.hAdd Complex Complex Complex qz4 qz124 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz76 (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz84 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz84 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz84 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz126 qz127 (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz84 2 k) 1))))) Bool.false 1955729450561 3909500566440 0 1 Bool.false

noncomputable def ep788 := nat_lit 1700021109792922785141587

noncomputable def ep789 := nat_lit 537317666449704804679680000

noncomputable def ep790 := nat_lit 35664317384304476571494941

noncomputable def ep791 := @Enclosure.Real.IsNear.addLit_ft_n (@HMul.hMul Real Real Real qz0 qz130 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz124 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz76 (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz84 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz84 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz84 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz126 qz127 (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz84 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz131 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz124 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz76 (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz84 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz84 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz84 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz126 qz127 (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz84 2 k) 1))))))) ep788 ep789 ep790

noncomputable def ep792 := nat_lit 4398460029321181460074332160000

noncomputable def ep793 := nat_lit 16798967316968326801447947

noncomputable def ep794 := nat_lit 281501441876555613444757258240

noncomputable def ep795 := nat_lit 36105219257004374384175848479284046302577157996544

noncomputable def ep796 := @Enclosure.Real.IsNear.mulLit_ff qz130 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz124 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz76 (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz84 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz84 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz84 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz126 qz127 (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz84 2 k) 1)))))) 25449503467 549755813888 1601696291343 13500834557984768 66799775170361

noncomputable def ep797 := @ep796 977375141610000 0 1 ep788 ep789 ep790 ep792 (@Enclosure.Complex.IsNear.re_isNear qz123 Bool.false 25449503467 549755813888 1601696291343 13500834557984768 Bool.true 178744889885 1099511627776 25768851584481 216013352927756288 (ep731 ep744))

noncomputable def ep798 := @Enclosure.Real.IsNear.mulLit_tf qz131 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz124 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz76 (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz84 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz84 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz84 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz126 qz127 (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz84 2 k) 1)))))) 178744889885 1099511627776 25768851584481 216013352927756288 1955729450561

noncomputable def ep799 := @ep798 3909500566440 0 1 69915329057075499295097 859708266319527687487488 ep793 ep794 (@Enclosure.Complex.IsNear.im_isNear qz123 Bool.false 25449503467 549755813888 1601696291343 13500834557984768 Bool.true 178744889885 1099511627776 25768851584481 216013352927756288 (ep731 ep744))

noncomputable abbrev qz665 := (ep784 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable def ep800 := @ep722 ep684 ep678 ep685 ep680 (@ep724 ep725 ep726 ep727 ep728 ep546 ep729 1052179719241486324519771 ep544 ep683 ep546 (ep745 (@ep746 66799775170361 977375141610000 0 1 qz665) rfl) (ep786 (@ep787 66799775170361 977375141610000 0 1 qz665) rfl) rfl rfl) (@ep791 ep792 69915329057075499295097 859708266319527687487488 ep793 ep794 ep795 ep684 ep678 ep685 ep680 (ep797 (@ep787 66799775170361 977375141610000 0 1 qz665) rfl) (ep799 (@ep746 66799775170361 977375141610000 0 1 qz665) rfl) rfl rfl)

noncomputable def ep801 := @ep688 ep679 ep680 (@ep689 216013352927756288 (BSN.head_sum_c_eq qz5 35) (ep690 (BSN.head_sum_c_succ qz5 34 35 rfl rfl) (ep721 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))) ep800 rfl rfl rfl

noncomputable def ep802 := @Enclosure.Complex.IsNear.re_isNear (zetaApproximant qz5 1 35) Bool.false ep543 ep544 ep545 ep546 Bool.true 592883349954218728583173 ep678 ep679 ep680 (@ep681 ep546 Bool.true 592883349954218728583173 ep678 ep679 ep680 (BSN.zetaApproximant_eq_folded' qz5 1 35 rfl) (ep801 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

noncomputable def ep803 := @Enclosure.Real.IsNear.mulLit_tt (Real.sin (@HSub.hSub Real Real Real qz396 (Complex.im (@HSub.hSub Complex Complex Complex qz77 qz78 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz79 (@Nat.cast Complex Complex.instNatCast j))))) qz80)) (Complex.im (zetaApproximant qz5 1 35)) 291 524288 74722201

noncomputable def ep804 := @Enclosure.Real.IsNear.recentre' (Real.sin (@HSub.hSub Real Real Real qz396 (Complex.im (@HSub.hSub Complex Complex Complex qz77 qz78 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz79 (@Nat.cast Complex Complex.instNatCast j))))) qz80)) Bool.true 582 1048576 74722201

noncomputable def ep805 := @Enclosure.Real.IsNear.sin_image (@HSub.hSub Real Real Real qz396 (Complex.im (@HSub.hSub Complex Complex Complex qz77 qz78 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz79 (@Nat.cast Complex Complex.instNatCast j))))) qz80) qz397 Bool.false 74119761 524288 375

noncomputable def ep806 := BSN.sin_dyadic_bound_f 1192704 2147483648 1 0 1048576 393310 0 1 1 0 1 1 582 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 1192704) qz19 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 1192704) qz20 0 0 rfl) rfl rfl

noncomputable def ep807 := @ep805 1048576 Bool.true 582 1048576 1 196463 (@ep551 74119761 524288 375 1048576 ep675 rfl) (Enclosure.sfrac_false_div 74119761 524288) (BSN.sin_reduce2 qz397 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 41964550285261012992) qz24) 226375608064910080 72057594037927936 Bool.false 582 1048576 22 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q2 74119761 524288 226375608064910080 72057594037927936 22 41964550285261012992 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 582 1048576 41964550285261012992 75557863725914323419136 1192704 2147483648 393310 392926 (ep806 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep808 := @Enclosure.Complex.IsNear.im_isNear (zetaApproximant qz5 1 35) Bool.false ep543 ep544 ep545 ep546 Bool.true 592883349954218728583173 ep678 ep679 ep680 (@ep681 ep546 Bool.true 592883349954218728583173 ep678 ep679 ep680 (BSN.zetaApproximant_eq_folded' qz5 1 35 rfl) (ep801 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

theorem EMRow47.d12 : Enclosure.Real.IsNear (hardyZApproximantEM 1 35 qz12) Bool.true ep526 ep527 ep528 ep529 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantEM 1 35 qz12) ep530 Bool.true ep526 ep527 ep528 ep529 (@Eq.refl Real ep530) (@ep531 Bool.true ep526 ep527 ep528 ep529 (BSN.re_exp_mul (@HSub.hSub Real Real Real qz396 (Complex.im (@HSub.hSub Complex Complex Complex qz77 qz78 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz79 (@Nat.cast Complex Complex.instNatCast j))))) qz80) (zetaApproximant qz5 1 35)) (@ep533 ep534 ep535 ep536 ep537 ep538 ep539 ep540 ep541 ep526 ep527 ep528 ep529 (@ep542 206006386688 ep543 ep544 ep545 ep546 ep532 ep534 ep535 ep536 (@ep547 206006386688 1048575 1048576 74722201 206006386688 (ep677 rfl rfl) rfl) ep802 rfl) (@ep803 206006386688 592883349954218728583173 ep678 ep679 ep680 ep537 ep538 ep539 ep540 (@ep804 206006386688 291 524288 74722201 206006386688 (ep807 rfl rfl) rfl) ep808 rfl) rfl rfl))

noncomputable abbrev qz719 := (@HAdd.hAdd Complex Complex Complex (@instHAdd Complex Complex.instAdd) (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (2 : Complex)) (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul) Complex.I ↑(Enclosure.sfrac Bool.false 138478 1000)))

noncomputable abbrev qz666 := qz719

noncomputable abbrev qz444 := qz666

noncomputable abbrev qz142 := (BSN.headSumC qz444 9)

noncomputable abbrev qz143 := qz444

noncomputable abbrev qz667 := (@Neg.neg Complex Complex.instNeg qz719)

noncomputable abbrev qz445 := qz667

noncomputable abbrev qz144 := qz445

noncomputable abbrev qz668 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 8) qz144)

noncomputable def ep809 := @Enclosure.Complex.IsNear.of_eq qz142 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz143 8) qz668) Bool.false 168028019309 1099511627776 518605038969429 216013352927756288 Bool.true 177612284051 274877906944 1012700223743 421901079937024

noncomputable def ep810 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz143 8) qz668 Bool.true 9371565555 549755813888 232109958534365 108006676463878144 Bool.true 1051376729217 1099511627776 464035699018131 216013352927756288 Bool.false

noncomputable abbrev qz669 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 7) qz144)

noncomputable def ep811 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz143 8) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz143 7) qz669) Bool.true 9371565555 549755813888 232109958534365 108006676463878144 Bool.true 1051376729217 1099511627776 464035699018131 216013352927756288

noncomputable def ep812 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz143 7) qz669 Bool.true 333508805685 1099511627776 406029393807141 216013352927756288 Bool.true 661359329421 549755813888 12683334419425 6750417278992384 Bool.false

noncomputable abbrev qz670 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 6) qz144)

noncomputable def ep813 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz143 7) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz143 6) qz670) Bool.true 333508805685 1099511627776 406029393807141 216013352927756288 Bool.true 661359329421 549755813888 12683334419425 6750417278992384

noncomputable def ep814 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz143 6) qz670 Bool.false 57183353835 549755813888 171569789496013 108006676463878144 Bool.true 646404817635 549755813888 85792177140259 54003338231939072 Bool.true

noncomputable abbrev qz671 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 5) qz144)

noncomputable def ep815 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz143 6) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz143 5) qz671) Bool.false 57183353835 549755813888 171569789496013 108006676463878144 Bool.true 646404817635 549755813888 85792177140259 54003338231939072

noncomputable def ep816 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz143 5) qz671 Bool.false 149499344907 274877906944 34283725978817 27001669115969536 Bool.true 1204006566643 1099511627776 274464351976415 216013352927756288 Bool.true

noncomputable def ep817 := nat_lit 1421459226480214561259520

noncomputable abbrev qz672 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 4) qz144)

noncomputable def ep818 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz143 5) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz143 4) qz672) Bool.false 149499344907 274877906944 34283725978817 27001669115969536 Bool.true 1204006566643 1099511627776 274464351976415 216013352927756288

noncomputable def ep819 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz143 4) qz672 Bool.false 558686953793 549755813888 98651533007273 108006676463878144 Bool.true 1384222882875 1099511627776 197624701682199 216013352927756288 Bool.true

noncomputable def ep820 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz143 4) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz143 3) (@HPow.hPow Complex Complex Complex qz6 qz8 qz144)) Bool.false 558686953793 549755813888 98651533007273 108006676463878144 Bool.true 1384222882875 1099511627776 197624701682199 216013352927756288

noncomputable def ep821 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz143 3) (@HPow.hPow Complex Complex Complex qz6 qz8 qz144) Bool.false 242595697699 274877906944 27151626017901 54003338231939072 Bool.true 191668341865 274877906944 27193858490233 54003338231939072 Bool.false

noncomputable def ep822 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz143 3) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz143 2) (@HPow.hPow Complex Complex Complex qz6 qz9 qz144)) Bool.false 242595697699 274877906944 27151626017901 54003338231939072 Bool.true 191668341865 274877906944 27193858490233 54003338231939072

noncomputable def ep823 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz143 2) (@HPow.hPow Complex Complex Complex qz6 qz9 qz144) Bool.false 1 1 0 1 Bool.false 0 1 0 1 Bool.true

noncomputable def ep824 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz143 2) (Complex.mk (Enclosure.sfrac Bool.false 1 1) qz10) Bool.false 1 1 0 1 Bool.false 0 1 0 1 (BSN.head_sum_c_two qz143)

noncomputable abbrev qz720 := (Enclosure.sfrac Bool.false 138478 1000)

noncomputable abbrev qz673 := qz720

noncomputable abbrev qz446 := qz673

noncomputable abbrev qz145 := (@HMul.hMul Real Real Real qz267 qz446 (Real.log qz278))

noncomputable abbrev qz146 := qz446

noncomputable abbrev qz447 := (@Eq.refl Real qz673)

noncomputable abbrev qz147 := qz447

noncomputable def ep825 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz9 qz144) (Complex.mk (@HMul.hMul Real Real Real qz0 qz280 (Real.cos qz145)) (@HMul.hMul Real Real Real qz0 qz280 (@Neg.neg Real Real.instNeg (Real.sin qz145)))) Bool.true 32282209245 274877906944 27151626017901 54003338231939072 Bool.true 191668341865 274877906944 27193858490233 54003338231939072 (BSN.cpow_neg_s_mk qz146 138478 1000 2 qz147 rfl)

noncomputable def ep826 := nat_lit 16487074697142873510533551335306256

noncomputable def ep827 := BSN.sin_dyadic_bound_f 358332254 2147483648 2 1 1048576 393310 ep826 ep65 ep826 ep826 ep66 ep826 174156 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 358332254) qz19 0 1 ep826 ep65 ep826 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 358332254) qz20 0 1 ep826 ep66 ep826 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz148 := (Enclosure.Real.IsNear.const Bool.false 138478 1000)

noncomputable abbrev qz448 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 50324013) qz23)

noncomputable def ep828 := @Enclosure.Real.IsNear.cos_image qz145 qz448 Bool.false 50324013 524288 185 262144 Bool.true 174156 1048576 1 196463 (@Enclosure.Real.IsNear.recentre' qz145 Bool.false 1572625407 16384000 69239 98231500 50324013 524288 185 262144 (@Enclosure.Real.IsNear.mulLit_ff qz146 (Real.log qz278) 138478 1000 0 1 363408 524288 1 196463 1572625407 16384000 69239 98231500 qz148 qz284 rfl) rfl) (Enclosure.sfrac_false_div 50324013 524288) (BSN.cos_reduce1 qz448 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 12607695357545751248896) qz24) 226375608064910080 72057594037927936 Bool.false 174156 1048576 15 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q1 50324013 524288 226375608064910080 72057594037927936 15 12607695357545751248896 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 174156 1048576 12607695357545751248896 75557863725914323419136 358332254 2147483648 393310 392926 (ep827 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep829 := BSN.cos_dyadic_bound_f 358332254 2147483648 2 1 1048576 393310 ep826 ep61 ep826 ep826 ep62 ep826 1034012 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 358332254) qz15 0 1 ep826 ep61 ep826 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 358332254) qz16 0 1 ep826 ep62 ep826 rfl rfl rfl rfl) rfl rfl

noncomputable def ep830 := @Enclosure.Real.IsNear.sin_image qz145 qz448 Bool.false 50324013 524288 185 262144 Bool.false 1034012 1048576 1 196463 (@Enclosure.Real.IsNear.recentre' qz145 Bool.false 1572625407 16384000 69239 98231500 50324013 524288 185 262144 (@Enclosure.Real.IsNear.mulLit_ff qz146 (Real.log qz278) 138478 1000 0 1 363408 524288 1 196463 1572625407 16384000 69239 98231500 qz148 qz284 rfl) rfl) (Enclosure.sfrac_false_div 50324013 524288) (BSN.sin_reduce1 qz448 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 12607695357545751248896) qz24) 226375608064910080 72057594037927936 Bool.false 1034012 1048576 15 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q1 50324013 524288 226375608064910080 72057594037927936 15 12607695357545751248896 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1034012 1048576 12607695357545751248896 75557863725914323419136 358332254 2147483648 393310 392926 (ep829 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep831 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz280 (Real.cos qz145)) (@HMul.hMul Real Real Real qz0 qz280 (@Neg.neg Real Real.instNeg (Real.sin qz145))) Bool.true 32282209245 274877906944 27151626017901 54003338231939072 Bool.true 191668341865 274877906944 27193858490233 54003338231939072 (@Enclosure.Real.IsNear.mulLit_ft qz280 (Real.cos qz145) 741455 1048576 1 1048576 43539 262144 36607799 51501596672 32282209245 274877906944 27151626017901 54003338231939072 qz286 (@Enclosure.Real.IsNear.recentre' (Real.cos qz145) Bool.true 174156 1048576 36607799 51501596672 43539 262144 36607799 51501596672 (ep828 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz280 (@Neg.neg Real Real.instNeg (Real.sin qz145)) 741455 1048576 1 1048576 258503 262144 36607799 51501596672 191668341865 274877906944 27193858490233 54003338231939072 qz286 (@Enclosure.Real.IsNear.neg (Real.sin qz145) Bool.false 258503 262144 36607799 51501596672 (@Enclosure.Real.IsNear.recentre' (Real.sin qz145) Bool.false 1034012 1048576 36607799 51501596672 258503 262144 36607799 51501596672 (ep830 rfl rfl) rfl)) rfl)

noncomputable def ep832 := @ep823 32282209245 274877906944 27151626017901 54003338231939072 Bool.true 191668341865 274877906944 27193858490233 54003338231939072 Bool.false 242595697699 242595697699 274877906944 27151626017901 54003338231939072 Bool.true 191668341865 191668341865 274877906944 27193858490233 54003338231939072 (ep824 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 1) qz10 Bool.false 1 1 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 1) qz21)) (ep825 ep831) rfl rfl

noncomputable abbrev qz149 := (@HMul.hMul Real Real Real qz267 qz446 qz547)

noncomputable def ep833 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz8 qz144) (Complex.mk (@HMul.hMul Real Real Real qz0 qz287 (Real.cos qz149)) (@HMul.hMul Real Real Real qz0 qz287 (@Neg.neg Real Real.instNeg (Real.sin qz149)))) Bool.false 73495558395 549755813888 44348280971471 108006676463878144 Bool.true 617549515415 1099511627776 88849267721267 216013352927756288 (BSN.cpow_neg_s_mk qz146 138478 1000 3 qz147 rfl)

noncomputable def ep834 := nat_lit 2433644327504810277852847123540029795409192183458304763315065424286659981168161

noncomputable def ep835 := nat_lit 4621741148463991199090852980745755149189750055809302032193309035281770434081

noncomputable def ep836 := nat_lit 7291689500217502851160359664658597875929197050263295685880809654789416402636321

noncomputable def ep837 := BSN.cos_dyadic_bound_f 2871446323 2147483648 3 2 1048576 393310 ep834 ep78 ep835 ep836 ep81 ep835 242802 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2871446323) qz15 0 2 ep834 ep78 ep835 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2871446323) qz16 0 2 ep836 ep81 ep835 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz449 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 159523609) qz30)

noncomputable def ep838 := @Enclosure.Real.IsNear.cos_image qz149 qz449 Bool.false 159523609 1048576 185 262144 Bool.false 242802 1048576 1 196463 (@Enclosure.Real.IsNear.recentre' qz149 Bool.false 39880902371 262144000 69239 98231500 159523609 1048576 185 262144 (@Enclosure.Real.IsNear.mulLit_ff qz146 qz547 138478 1000 0 1 575989 524288 1 196463 39880902371 262144000 69239 98231500 qz148 qz291 rfl) rfl) (Enclosure.sfrac_false_div 159523609 1048576) (BSN.cos_reduce0 qz449 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 202060071756263868858368) qz31) 226375608064910080 72057594037927936 Bool.false 242802 1048576 24 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q0 159523609 1048576 226375608064910080 72057594037927936 24 202060071756263868858368 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 242802 1048576 202060071756263868858368 151115727451828646838272 2871446323 2147483648 393310 392926 (ep837 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep839 := nat_lit 4376862396589887307175852139987457027617194130180301132341363116487762549755425

noncomputable def ep840 := nat_lit 11455728219685525056852513271331656230660629793239002190937161852363207621037601

noncomputable def ep841 := BSN.sin_dyadic_bound_f 2871446323 2147483648 3 2 1048576 393310 ep839 ep109 ep835 ep840 ep112 ep835 1020077 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2871446323) qz19 0 2 ep839 ep109 ep835 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2871446323) qz20 0 2 ep840 ep112 ep835 rfl rfl rfl rfl) rfl rfl

noncomputable def ep842 := @Enclosure.Real.IsNear.sin_image qz149 qz449 Bool.false 159523609 1048576 185 262144 Bool.false 1020077 1048576 1 196463 (@Enclosure.Real.IsNear.recentre' qz149 Bool.false 39880902371 262144000 69239 98231500 159523609 1048576 185 262144 (@Enclosure.Real.IsNear.mulLit_ff qz146 qz547 138478 1000 0 1 575989 524288 1 196463 39880902371 262144000 69239 98231500 qz148 qz291 rfl) rfl) (Enclosure.sfrac_false_div 159523609 1048576) (BSN.sin_reduce0 qz449 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 202060071756263868858368) qz31) 226375608064910080 72057594037927936 Bool.false 1020077 1048576 24 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q0 159523609 1048576 226375608064910080 72057594037927936 24 202060071756263868858368 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1020077 1048576 202060071756263868858368 151115727451828646838272 2871446323 2147483648 393310 392926 (ep841 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep843 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz287 (Real.cos qz149)) (@HMul.hMul Real Real Real qz0 qz287 (@Neg.neg Real Real.instNeg (Real.sin qz149))) Bool.false 73495558395 549755813888 44348280971471 108006676463878144 Bool.true 617549515415 1099511627776 88849267721267 216013352927756288 (@Enclosure.Real.IsNear.mulLit_ff qz287 (Real.cos qz149) 605395 1048576 1 1048576 121401 524288 36607799 51501596672 73495558395 549755813888 44348280971471 108006676463878144 qz292 (@Enclosure.Real.IsNear.recentre' (Real.cos qz149) Bool.false 242802 1048576 36607799 51501596672 121401 524288 36607799 51501596672 (ep838 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz287 (@Neg.neg Real Real.instNeg (Real.sin qz149)) 605395 1048576 1 1048576 1020077 1048576 36607799 51501596672 617549515415 1099511627776 88849267721267 216013352927756288 qz292 (@Enclosure.Real.IsNear.neg (Real.sin qz149) Bool.false 1020077 1048576 36607799 51501596672 (@Enclosure.Real.IsNear.recentre' (Real.sin qz149) Bool.false 1020077 1048576 36607799 51501596672 1020077 1048576 36607799 51501596672 (ep842 rfl rfl) rfl)) rfl)

noncomputable def ep844 := @ep821 73495558395 549755813888 44348280971471 108006676463878144 Bool.true 617549515415 1099511627776 88849267721267 216013352927756288 Bool.false 153570700495539081838592 558686953793 549755813888 98651533007273 108006676463878144 Bool.true 380492288788669661184000 1384222882875 1099511627776 197624701682199 216013352927756288 (ep822 (BSN.head_sum_c_succ qz143 2 3 rfl rfl) (ep832 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep833 ep843) rfl rfl

noncomputable abbrev qz150 := (@HMul.hMul Real Real Real qz267 qz446 qz548)

noncomputable def ep845 := @Enclosure.Complex.IsNear.of_eq qz672 (Complex.mk (@HMul.hMul Real Real Real qz0 qz293 (Real.cos qz150)) (@HMul.hMul Real Real Real qz0 qz293 (@Neg.neg Real Real.instNeg (Real.sin qz150)))) Bool.true 259688263979 549755813888 38483370907995 108006676463878144 Bool.false 22527039529 137438953472 9604956286777 27001669115969536 (BSN.cpow_neg_s_mk qz146 138478 1000 4 qz147 rfl)

noncomputable def ep846 := nat_lit 264629439196924653160822057522381056

noncomputable def ep847 := BSN.cos_dyadic_bound_f 717231804 2147483648 2 1 1048576 393310 ep846 ep61 ep846 ep846 ep62 ep846 990634 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 717231804) qz15 0 1 ep846 ep61 ep846 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 717231804) qz16 0 1 ep846 ep62 ep846 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz450 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 201296329) qz30)

noncomputable def ep848 := @Enclosure.Real.IsNear.cos_image qz150 qz450 Bool.false 201296329 1048576 185 262144 Bool.true 990634 1048576 1 196463 (@Enclosure.Real.IsNear.recentre' qz150 Bool.false 50324082263 262144000 69239 98231500 201296329 1048576 185 262144 (@Enclosure.Real.IsNear.mulLit_ff qz146 qz548 138478 1000 0 1 726817 524288 1 196463 50324082263 262144000 69239 98231500 qz148 qz297 rfl) rfl) (Enclosure.sfrac_false_div 201296329 1048576) (BSN.cos_reduce2 qz450 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 50470701337280017072128) qz31) 226375608064910080 72057594037927936 Bool.false 990634 1048576 30 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q2 201296329 1048576 226375608064910080 72057594037927936 30 50470701337280017072128 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 990634 1048576 50470701337280017072128 151115727451828646838272 717231804 2147483648 393310 392926 (ep847 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep849 := BSN.sin_dyadic_bound_f 717231804 2147483648 2 1 1048576 393310 ep846 ep65 ep846 ep846 ep66 ep846 343736 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 717231804) qz19 0 1 ep846 ep65 ep846 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 717231804) qz20 0 1 ep846 ep66 ep846 rfl rfl rfl rfl) rfl rfl

noncomputable def ep850 := @Enclosure.Real.IsNear.sin_image qz150 qz450 Bool.false 201296329 1048576 185 262144 Bool.true 343736 1048576 1 196463 (@Enclosure.Real.IsNear.recentre' qz150 Bool.false 50324082263 262144000 69239 98231500 201296329 1048576 185 262144 (@Enclosure.Real.IsNear.mulLit_ff qz146 qz548 138478 1000 0 1 726817 524288 1 196463 50324082263 262144000 69239 98231500 qz148 qz297 rfl) rfl) (Enclosure.sfrac_false_div 201296329 1048576) (BSN.sin_reduce2 qz450 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 50470701337280017072128) qz31) 226375608064910080 72057594037927936 Bool.false 343736 1048576 30 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q2 201296329 1048576 226375608064910080 72057594037927936 30 50470701337280017072128 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 343736 1048576 50470701337280017072128 151115727451828646838272 717231804 2147483648 393310 392926 (ep849 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep851 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz293 (Real.cos qz150)) (@HMul.hMul Real Real Real qz0 qz293 (@Neg.neg Real Real.instNeg (Real.sin qz150))) Bool.true 259688263979 549755813888 38483370907995 108006676463878144 Bool.false 22527039529 137438953472 9604956286777 27001669115969536 (@Enclosure.Real.IsNear.mulLit_ft qz293 (Real.cos qz150) 524287 1048576 1 1048576 495317 524288 36607799 51501596672 259688263979 549755813888 38483370907995 108006676463878144 qz298 (@Enclosure.Real.IsNear.recentre' (Real.cos qz150) Bool.true 990634 1048576 36607799 51501596672 495317 524288 36607799 51501596672 (ep848 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz293 (@Neg.neg Real Real.instNeg (Real.sin qz150)) 524287 1048576 1 1048576 42967 131072 36607799 51501596672 22527039529 137438953472 9604956286777 27001669115969536 qz298 (@Enclosure.Real.IsNear.neg (Real.sin qz150) Bool.true 42967 131072 36607799 51501596672 (@Enclosure.Real.IsNear.recentre' (Real.sin qz150) Bool.true 343736 1048576 36607799 51501596672 42967 131072 36607799 51501596672 (ep850 rfl rfl) rfl)) rfl)

noncomputable def ep852 := @ep819 259688263979 549755813888 38483370907995 108006676463878144 Bool.false 22527039529 137438953472 9604956286777 27001669115969536 Bool.false 164376268070141225336832 149499344907 274877906944 34283725978817 27001669115969536 Bool.true 165477402492829744234496 1204006566643 1099511627776 274464351976415 216013352927756288 (ep820 (BSN.head_sum_c_succ qz143 3 4 rfl rfl) (ep844 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep845 ep851) rfl rfl

noncomputable abbrev qz151 := (@HMul.hMul Real Real Real qz267 qz446 qz549)

noncomputable def ep853 := @Enclosure.Complex.IsNear.of_eq qz671 (Complex.mk (@HMul.hMul Real Real Real qz0 qz299 (Real.cos qz151)) (@HMul.hMul Real Real Real qz0 qz299 (@Neg.neg Real Real.instNeg (Real.sin qz151)))) Bool.true 241815335979 549755813888 34434885580745 108006676463878144 Bool.true 88803068627 1099511627776 68704356584621 216013352927756288 (BSN.cpow_neg_s_mk qz146 138478 1000 5 qz147 rfl)

noncomputable def ep854 := nat_lit 5100530306677361663330384026289878491557587146732591032060181264767072919573025

noncomputable def ep855 := nat_lit 6274209983247690312210809927629579254158935686435124208175542208071320949281

noncomputable def ep856 := nat_lit 13348373510848784286312188281352567206715518536045414882868190529862599317344801

noncomputable def ep857 := BSN.sin_dyadic_bound_f 2983285939 2147483648 3 2 1048576 393310 ep854 ep109 ep855 ep856 ep112 ep855 1031334 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2983285939) qz19 0 2 ep854 ep109 ep855 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2983285939) qz20 0 2 ep856 ep112 ep855 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz451 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 29212211) qz634)

noncomputable def ep858 := @Enclosure.Real.IsNear.cos_image qz151 qz451 Bool.false 29212211 131072 185 262144 Bool.true 1031334 1048576 1 196463 (@Enclosure.Real.IsNear.recentre' qz151 Bool.false 1825763191 8192000 69239 98231500 29212211 131072 185 262144 (@Enclosure.Real.IsNear.mulLit_ff qz146 qz549 138478 1000 0 1 843808 524288 1 196463 1825763191 8192000 69239 98231500 qz148 qz303 rfl) rfl) (Enclosure.sfrac_false_div 29212211 131072) (BSN.cos_reduce1 qz451 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 26241260636556683640832) qz370) 226375608064910080 72057594037927936 Bool.false 1031334 1048576 35 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q1 29212211 131072 226375608064910080 72057594037927936 35 26241260636556683640832 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1031334 1048576 26241260636556683640832 18889465931478580854784 2983285939 2147483648 393310 392926 (ep857 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep859 := nat_lit 2836416485924422119766751485684434530533841275156521739681512054740849986851361

noncomputable def ep860 := nat_lit 8496701037806770978675832837198044433093205954096694970628185079806407318655521

noncomputable def ep861 := BSN.cos_dyadic_bound_f 2983285939 2147483648 3 2 1048576 393310 ep859 ep78 ep855 ep860 ep81 ep855 189371 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2983285939) qz15 0 2 ep859 ep78 ep855 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2983285939) qz16 0 2 ep860 ep81 ep855 rfl rfl rfl rfl) rfl rfl

noncomputable def ep862 := @Enclosure.Real.IsNear.sin_image qz151 qz451 Bool.false 29212211 131072 185 262144 Bool.false 189371 1048576 1 196463 (@Enclosure.Real.IsNear.recentre' qz151 Bool.false 1825763191 8192000 69239 98231500 29212211 131072 185 262144 (@Enclosure.Real.IsNear.mulLit_ff qz146 qz549 138478 1000 0 1 843808 524288 1 196463 1825763191 8192000 69239 98231500 qz148 qz303 rfl) rfl) (Enclosure.sfrac_false_div 29212211 131072) (BSN.sin_reduce1 qz451 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 26241260636556683640832) qz370) 226375608064910080 72057594037927936 Bool.false 189371 1048576 35 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q1 29212211 131072 226375608064910080 72057594037927936 35 26241260636556683640832 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 189371 1048576 26241260636556683640832 18889465931478580854784 2983285939 2147483648 393310 392926 (ep861 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep863 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz299 (Real.cos qz151)) (@HMul.hMul Real Real Real qz0 qz299 (@Neg.neg Real Real.instNeg (Real.sin qz151))) Bool.true 241815335979 549755813888 34434885580745 108006676463878144 Bool.true 88803068627 1099511627776 68704356584621 216013352927756288 (@Enclosure.Real.IsNear.mulLit_ft qz299 (Real.cos qz151) 468937 1048576 1 1048576 515667 524288 36607799 51501596672 241815335979 549755813888 34434885580745 108006676463878144 qz304 (@Enclosure.Real.IsNear.recentre' (Real.cos qz151) Bool.true 1031334 1048576 36607799 51501596672 515667 524288 36607799 51501596672 (ep858 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz299 (@Neg.neg Real Real.instNeg (Real.sin qz151)) 468937 1048576 1 1048576 189371 1048576 36607799 51501596672 88803068627 1099511627776 68704356584621 216013352927756288 qz304 (@Enclosure.Real.IsNear.neg (Real.sin qz151) Bool.false 189371 1048576 36607799 51501596672 (@Enclosure.Real.IsNear.recentre' (Real.sin qz151) Bool.false 189371 1048576 36607799 51501596672 189371 1048576 36607799 51501596672 (ep862 rfl rfl) rfl)) rfl)

noncomputable def ep864 := @ep816 241815335979 549755813888 34434885580745 108006676463878144 Bool.true 88803068627 1099511627776 68704356584621 216013352927756288 Bool.false 15718440614202955530240 57183353835 549755813888 171569789496013 108006676463878144 Bool.true ep817 646404817635 549755813888 85792177140259 54003338231939072 (ep818 (BSN.head_sum_c_succ qz143 4 5 rfl rfl) (ep852 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep853 ep863) rfl rfl

noncomputable abbrev qz152 := (@HMul.hMul Real Real Real qz267 qz446 qz550)

noncomputable def ep865 := @Enclosure.Complex.IsNear.of_eq qz670 (Complex.mk (@HMul.hMul Real Real Real qz0 qz305 (Real.cos qz152)) (@HMul.hMul Real Real Real qz0 qz305 (@Neg.neg Real Real.instNeg (Real.sin qz152)))) Bool.true 447875513355 1099511627776 62889814815115 216013352927756288 Bool.true 7477255893 274877906944 15674498215141 54003338231939072 (BSN.cpow_neg_s_mk qz146 138478 1000 6 qz147 rfl)

noncomputable def ep866 := @Enclosure.Real.IsNear.mulLit_ff qz146 qz550 138478 1000 0 1 4034681531866359 2251799813685248 500000000196463 98231500000000000000 279357314584894830801 1125899906842624000 34619500013602901657 49115750000000000000000 qz148 (BSN.isNear_log_sfrac 6 1 4034681531866359 2251799813685248 500000000196463 98231500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz551) Bool.false 33845361775666394038272 18889465931478580854784 1000000000392926 196463000000000000000 4034681531866359 2251799813685248 500000000196463 98231500000000000000 (BSN.log_rat_reduce_isNear 6 1 2 12 8 212580 524288 24973259072661432 36028797018963968 196463 1000000000000000 rfl rfl rfl rfl (ep123 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep867 := nat_lit 7012594033229707390347160474741189823952194591356035449101898258055791203577985

noncomputable def ep868 := nat_lit 11849117578777819353163366496023027190104861970029523528853859701430680809601

noncomputable def ep869 := nat_lit 18347133420474069552908870078566697971090816057980997423839208236343803478536321

noncomputable def ep870 := BSN.sin_dyadic_bound_f 3230061201 2147483648 3 2 1048576 393310 ep867 ep109 ep868 ep869 ep112 ep868 1046245 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3230061201) qz19 0 2 ep867 ep109 ep868 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3230061201) qz20 0 2 ep869 ep112 ep868 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz452 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 260171773) qz30)

noncomputable def ep871 := @Enclosure.Real.IsNear.cos_image qz152 qz452 Bool.false 260171773 1048576 185 262144 Bool.true 1046245 1048576 1 196463 (@Enclosure.Real.IsNear.recentre' qz152 Bool.false 279357314584894830801 1125899906842624000 34619500013602901657 49115750000000000000000 260171773 1048576 185 262144 (ep866 rfl) rfl) (Enclosure.sfrac_false_div 260171773 1048576) (BSN.cos_reduce1 qz452 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 227295350367309839466496) qz31) 226375608064910080 72057594037927936 Bool.false 1046245 1048576 39 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q1 260171773 1048576 226375608064910080 72057594037927936 39 227295350367309839466496 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1046245 1048576 227295350367309839466496 151115727451828646838272 3230061201 2147483648 393310 392926 (ep870 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep872 := nat_lit 3901151848495960914349828426632226803169043600517810593291656303231630971236481

noncomputable def ep873 := nat_lit 11679757310330327104343158546904634355126921077613372732817261190292031552090241

noncomputable def ep874 := BSN.cos_dyadic_bound_f 3230061201 2147483648 3 2 1048576 393310 ep872 ep78 ep868 ep873 ep81 ep868 69868 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3230061201) qz15 0 2 ep872 ep78 ep868 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3230061201) qz16 0 2 ep873 ep81 ep868 rfl rfl rfl rfl) rfl rfl

noncomputable def ep875 := @Enclosure.Real.IsNear.sin_image qz152 qz452 Bool.false 260171773 1048576 185 262144 Bool.false 69868 1048576 1 196463 (@Enclosure.Real.IsNear.recentre' qz152 Bool.false 279357314584894830801 1125899906842624000 34619500013602901657 49115750000000000000000 260171773 1048576 185 262144 (ep866 rfl) rfl) (Enclosure.sfrac_false_div 260171773 1048576) (BSN.sin_reduce1 qz452 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 227295350367309839466496) qz31) 226375608064910080 72057594037927936 Bool.false 69868 1048576 39 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q1 260171773 1048576 226375608064910080 72057594037927936 39 227295350367309839466496 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 69868 1048576 227295350367309839466496 151115727451828646838272 3230061201 2147483648 393310 392926 (ep874 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep876 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz305 (Real.cos qz152)) (@HMul.hMul Real Real Real qz0 qz305 (@Neg.neg Real Real.instNeg (Real.sin qz152))) Bool.true 447875513355 1099511627776 62889814815115 216013352927756288 Bool.true 7477255893 274877906944 15674498215141 54003338231939072 (@Enclosure.Real.IsNear.mulLit_ft qz305 (Real.cos qz152) 428079 1048576 1 1048576 1046245 1048576 36607799 51501596672 447875513355 1099511627776 62889814815115 216013352927756288 qz309 (@Enclosure.Real.IsNear.recentre' (Real.cos qz152) Bool.true 1046245 1048576 36607799 51501596672 1046245 1048576 36607799 51501596672 (ep871 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz305 (@Neg.neg Real Real.instNeg (Real.sin qz152)) 428079 1048576 1 1048576 17467 262144 36607799 51501596672 7477255893 274877906944 15674498215141 54003338231939072 qz309 (@Enclosure.Real.IsNear.neg (Real.sin qz152) Bool.false 17467 262144 36607799 51501596672 (@Enclosure.Real.IsNear.recentre' (Real.sin qz152) Bool.false 69868 1048576 36607799 51501596672 17467 262144 36607799 51501596672 (ep875 rfl rfl) rfl)) rfl)

noncomputable def ep877 := @ep814 447875513355 1099511627776 62889814815115 216013352927756288 Bool.true 7477255893 274877906944 15674498215141 54003338231939072 Bool.true 183348404908172016353280 333508805685 1099511627776 406029393807141 216013352927756288 Bool.true 181793068209131879399424 661359329421 549755813888 12683334419425 6750417278992384 (ep815 (BSN.head_sum_c_succ qz143 5 6 rfl rfl) (ep864 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep865 ep876) rfl rfl

noncomputable abbrev qz153 := (@HMul.hMul Real Real Real qz267 qz446 qz552)

noncomputable def ep878 := @Enclosure.Complex.IsNear.of_eq qz669 (Complex.mk (@HMul.hMul Real Real Real qz0 qz310 (Real.cos qz153)) (@HMul.hMul Real Real Real qz0 qz310 (@Neg.neg Real Real.instNeg (Real.sin qz153)))) Bool.false 314765674575 1099511627776 58190523261589 216013352927756288 Bool.false 271341929625 1099511627776 58168997596531 216013352927756288 (BSN.cpow_neg_s_mk qz146 138478 1000 7 qz147 rfl)

noncomputable def ep879 := @Enclosure.Real.IsNear.mulLit_ff qz146 qz552 138478 1000 0 1 4381796493761783 2251799813685248 500000000196463 98231500000000000000 303391207431572093137 1125899906842624000 34619500013602901657 49115750000000000000000 qz148 (BSN.isNear_log_sfrac 7 1 4381796493761783 2251799813685248 500000000196463 98231500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz553) Bool.false 36757173121942042968064 18889465931478580854784 1000000000392926 196463000000000000000 4381796493761783 2251799813685248 500000000196463 98231500000000000000 (BSN.log_rat_reduce_isNear 7 1 2 14 8 293399 524288 24973259072661432 36028797018963968 196463 1000000000000000 rfl rfl rfl rfl (ep138 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep880 := nat_lit 746072682486292815157632969337597667303761795231833925794660036937741038725665

noncomputable def ep881 := nat_lit 134525045803488391945306372525149247190447703226741281073962613332409788961

noncomputable def ep882 := nat_lit 1953782080247085058492555852233429363204877310278150319769037490605831199861281

noncomputable def ep883 := BSN.sin_dyadic_bound_f 1845441971 2147483648 3 2 1048576 393310 ep880 ep109 ep881 ep882 ep112 ep881 794211 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1845441971) qz19 0 2 ep880 ep109 ep881 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1845441971) qz20 0 2 ep882 ep112 ep881 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz453 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 35319385) qz634)

noncomputable def ep884 := @Enclosure.Real.IsNear.cos_image qz153 qz453 Bool.false 35319385 131072 185 262144 Bool.false 794211 1048576 1 196463 (@Enclosure.Real.IsNear.recentre' qz153 Bool.false 303391207431572093137 1125899906842624000 34619500013602901657 49115750000000000000000 35319385 131072 185 262144 (ep879 rfl) rfl) (Enclosure.sfrac_false_div 35319385 131072) (BSN.cos_reduce3 qz453 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 16232679250016872693760) qz370) 226375608064910080 72057594037927936 Bool.false 794211 1048576 42 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q3 35319385 131072 226375608064910080 72057594037927936 42 16232679250016872693760 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 794211 1048576 16232679250016872693760 18889465931478580854784 1845441971 2147483648 393310 392926 (ep883 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep885 := nat_lit 414544612512742003261771785797565437056396751885786288233066226126892759198241

noncomputable def ep886 := nat_lit 1243364787446619033001424744647646012674809360250905382137050753154013458016801

noncomputable def ep887 := BSN.cos_dyadic_bound_f 1845441971 2147483648 3 2 1048576 393310 ep885 ep78 ep881 ep886 ep81 ep881 684645 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1845441971) qz15 0 2 ep885 ep78 ep881 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1845441971) qz16 0 2 ep886 ep81 ep881 rfl rfl rfl rfl) rfl rfl

noncomputable def ep888 := @Enclosure.Real.IsNear.sin_image qz153 qz453 Bool.false 35319385 131072 185 262144 Bool.true 684645 1048576 1 196463 (@Enclosure.Real.IsNear.recentre' qz153 Bool.false 303391207431572093137 1125899906842624000 34619500013602901657 49115750000000000000000 35319385 131072 185 262144 (ep879 rfl) rfl) (Enclosure.sfrac_false_div 35319385 131072) (BSN.sin_reduce3 qz453 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 16232679250016872693760) qz370) 226375608064910080 72057594037927936 Bool.false 684645 1048576 42 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q3 35319385 131072 226375608064910080 72057594037927936 42 16232679250016872693760 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 684645 1048576 16232679250016872693760 18889465931478580854784 1845441971 2147483648 393310 392926 (ep887 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep889 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz310 (Real.cos qz153)) (@HMul.hMul Real Real Real qz0 qz310 (@Neg.neg Real Real.instNeg (Real.sin qz153))) Bool.false 314765674575 1099511627776 58190523261589 216013352927756288 Bool.false 271341929625 1099511627776 58168997596531 216013352927756288 (@Enclosure.Real.IsNear.mulLit_ff qz310 (Real.cos qz153) 396325 1048576 1 1048576 794211 1048576 36607799 51501596672 314765674575 1099511627776 58190523261589 216013352927756288 qz314 (@Enclosure.Real.IsNear.recentre' (Real.cos qz153) Bool.false 794211 1048576 36607799 51501596672 794211 1048576 36607799 51501596672 (ep884 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz310 (@Neg.neg Real Real.instNeg (Real.sin qz153)) 396325 1048576 1 1048576 684645 1048576 36607799 51501596672 271341929625 1099511627776 58168997596531 216013352927756288 qz314 (@Enclosure.Real.IsNear.neg (Real.sin qz153) Bool.true 684645 1048576 36607799 51501596672 (@Enclosure.Real.IsNear.recentre' (Real.sin qz153) Bool.true 684645 1048576 36607799 51501596672 684645 1048576 36607799 51501596672 (ep888 rfl rfl) rfl)) rfl)

noncomputable def ep890 := @ep812 314765674575 1099511627776 58190523261589 216013352927756288 Bool.false 271341929625 1099511627776 58168997596531 216013352927756288 Bool.true 20608290596375085711360 9371565555 549755813888 232109958534365 108006676463878144 Bool.true 578000469473595223965696 1051376729217 1099511627776 464035699018131 216013352927756288 (ep813 (BSN.head_sum_c_succ qz143 6 7 rfl rfl) (ep877 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep878 ep889) rfl rfl

noncomputable abbrev qz154 := (@HMul.hMul Real Real Real qz267 qz446 qz554)

noncomputable def ep891 := @Enclosure.Complex.IsNear.of_eq qz668 (Complex.mk (@HMul.hMul Real Real Real qz0 qz315 (Real.cos qz154)) (@HMul.hMul Real Real Real qz0 qz315 (@Neg.neg Real Real.instNeg (Real.sin qz154)))) Bool.false 186771150419 1099511627776 54385121900699 216013352927756288 Bool.false 340927593013 1099511627776 54466815538285 216013352927756288 (BSN.cpow_neg_s_mk qz146 138478 1000 8 qz147 rfl)

noncomputable def ep892 := @Enclosure.Real.IsNear.mulLit_ff qz146 qz554 138478 1000 0 1 9364972152248037 4503599627370496 1000000000589389 196463000000000000000 648421306849501833843 2251799813685248000 69239000040808704971 98231500000000000000000 qz148 (BSN.isNear_log_sfrac 8 1 9364972152248037 4503599627370496 1000000000589389 196463000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz555) Bool.false 39279540158062550581248 18889465931478580854784 1000000000589389 196463000000000000000 9364972152248037 4503599627370496 1000000000589389 196463000000000000000 (BSN.log_rat_reduce_isNear 8 1 3 16 16 0 524288 24973259072661432 36028797018963968 196463 1000000000000000 rfl rfl rfl rfl (ep148 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep893 := nat_lit 1341794282863462248700823328548501776

noncomputable def ep894 := BSN.sin_dyadic_bound_f 1076270618 2147483648 2 1 1048576 393310 ep893 ep65 ep893 ep893 ep66 ep893 503797 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1076270618) qz19 0 1 ep893 ep65 ep893 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1076270618) qz20 0 1 ep893 ep66 ep893 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz454 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 75486175) qz17)

noncomputable def ep895 := @Enclosure.Real.IsNear.cos_image qz154 qz454 Bool.false 75486175 262144 185 262144 Bool.false 503797 1048576 1 196463 (@Enclosure.Real.IsNear.recentre' qz154 Bool.false 648421306849501833843 2251799813685248000 69239000040808704971 98231500000000000000000 75486175 262144 185 262144 (ep892 rfl) rfl) (Enclosure.sfrac_false_div 75486175 262144) (BSN.cos_reduce3 qz454 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 18933952948064422461440) qz285) 226375608064910080 72057594037927936 Bool.false 503797 1048576 45 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q3 75486175 262144 226375608064910080 72057594037927936 45 18933952948064422461440 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 503797 1048576 18933952948064422461440 37778931862957161709568 1076270618 2147483648 393310 392926 (ep894 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep896 := BSN.cos_dyadic_bound_f 1076270618 2147483648 2 1 1048576 393310 ep893 ep61 ep893 ep893 ep62 ep893 919619 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1076270618) qz15 0 1 ep893 ep61 ep893 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1076270618) qz16 0 1 ep893 ep62 ep893 rfl rfl rfl rfl) rfl rfl

noncomputable def ep897 := @Enclosure.Real.IsNear.sin_image qz154 qz454 Bool.false 75486175 262144 185 262144 Bool.true 919619 1048576 1 196463 (@Enclosure.Real.IsNear.recentre' qz154 Bool.false 648421306849501833843 2251799813685248000 69239000040808704971 98231500000000000000000 75486175 262144 185 262144 (ep892 rfl) rfl) (Enclosure.sfrac_false_div 75486175 262144) (BSN.sin_reduce3 qz454 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 18933952948064422461440) qz285) 226375608064910080 72057594037927936 Bool.false 919619 1048576 45 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q3 75486175 262144 226375608064910080 72057594037927936 45 18933952948064422461440 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 919619 1048576 18933952948064422461440 37778931862957161709568 1076270618 2147483648 393310 392926 (ep896 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep898 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz315 (Real.cos qz154)) (@HMul.hMul Real Real Real qz0 qz315 (@Neg.neg Real Real.instNeg (Real.sin qz154))) Bool.false 186771150419 1099511627776 54385121900699 216013352927756288 Bool.false 340927593013 1099511627776 54466815538285 216013352927756288 (@Enclosure.Real.IsNear.mulLit_ff qz315 (Real.cos qz154) 370727 1048576 1 1048576 503797 1048576 36607799 51501596672 186771150419 1099511627776 54385121900699 216013352927756288 qz319 (@Enclosure.Real.IsNear.recentre' (Real.cos qz154) Bool.false 503797 1048576 36607799 51501596672 503797 1048576 36607799 51501596672 (ep895 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz315 (@Neg.neg Real Real.instNeg (Real.sin qz154)) 370727 1048576 1 1048576 919619 1048576 36607799 51501596672 340927593013 1099511627776 54466815538285 216013352927756288 qz319 (@Enclosure.Real.IsNear.neg (Real.sin qz154) Bool.true 919619 1048576 36607799 51501596672 (@Enclosure.Real.IsNear.recentre' (Real.sin qz154) Bool.true 919619 1048576 36607799 51501596672 919619 1048576 36607799 51501596672 (ep897 rfl rfl) rfl)) rfl)

noncomputable def ep899 := @ep810 186771150419 1099511627776 54385121900699 216013352927756288 Bool.false 340927593013 1099511627776 54466815538285 216013352927756288 Bool.false 92374380511207874363392 168028019309 1099511627776 518605038969429 216013352927756288 Bool.true 781147086199713173602304 177612284051 274877906944 1012700223743 421901079937024 (ep811 (BSN.head_sum_c_succ qz143 7 8 rfl rfl) (ep890 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep891 ep898) rfl rfl

theorem EMRow47.d13 : Enclosure.Complex.IsNear qz142 Bool.false 168028019309 1099511627776 518605038969429 216013352927756288 Bool.true 177612284051 274877906944 1012700223743 421901079937024 := ep809 (BSN.head_sum_c_succ qz143 8 9 rfl rfl) (ep899 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable abbrev qz155 := (BSN.headSumC qz444 17)

noncomputable abbrev qz674 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 16) qz144)

noncomputable def ep900 := @Enclosure.Complex.IsNear.of_eq qz155 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz143 16) qz674) Bool.false 421317563 34359738368 27239421256911 6750417278992384 Bool.true 46481820595 1099511627776 871881049823971 216013352927756288

noncomputable def ep901 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz143 16) qz674 Bool.true 202272799133 1099511627776 833062221683347 216013352927756288 Bool.false 123832486505 1099511627776 833315846771975 216013352927756288 Bool.false

noncomputable abbrev qz675 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 15) qz144)

noncomputable def ep902 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz143 16) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz143 15) qz675) Bool.true 202272799133 1099511627776 833062221683347 216013352927756288 Bool.false 123832486505 1099511627776 833315846771975 216013352927756288

noncomputable def ep903 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz143 15) qz675 Bool.true 43878603811 549755813888 396667024332171 108006676463878144 Bool.true 135938629657 1099511627776 793482269192377 216013352927756288 Bool.true

noncomputable abbrev qz676 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 14) qz144)

noncomputable def ep904 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz143 15) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz143 14) qz676) Bool.true 43878603811 549755813888 396667024332171 108006676463878144 Bool.true 135938629657 1099511627776 793482269192377 216013352927756288

noncomputable def ep905 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz143 14) qz676 Bool.true 59985792193 274877906944 188033959440849 54003338231939072 Bool.false 28859765275 274877906944 188053630102261 54003338231939072 Bool.false

noncomputable abbrev qz677 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 13) qz144)

noncomputable def ep906 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz143 14) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz143 13) qz677) Bool.true 59985792193 274877906944 188033959440849 54003338231939072 Bool.false 28859765275 274877906944 188053630102261 54003338231939072

noncomputable def ep907 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz143 13) qz677 Bool.false 29792663455 549755813888 354673893847225 108006676463878144 Bool.false 58193170957 1099511627776 709590142290157 216013352927756288 Bool.true

noncomputable abbrev qz678 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 12) qz144)

noncomputable def ep908 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz143 13) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz143 12) qz678) Bool.false 29792663455 549755813888 354673893847225 108006676463878144 Bool.false 58193170957 1099511627776 709590142290157 216013352927756288

noncomputable def ep909 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz143 12) qz678 Bool.false 13889568469 549755813888 83117905628035 27001669115969536 Bool.true 64402425263 274877906944 41562579619229 13500834557984768 Bool.false

noncomputable abbrev qz679 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 11) qz144)

noncomputable def ep910 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz143 12) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz143 11) qz679) Bool.false 13889568469 549755813888 83117905628035 27001669115969536 Bool.true 64402425263 274877906944 41562579619229 13500834557984768

noncomputable def ep911 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz143 11) qz679 Bool.true 164192341933 1099511627776 618528558036323 216013352927756288 Bool.true 527885048741 1099511627776 618537928142645 216013352927756288 Bool.false

noncomputable abbrev qz680 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 10) qz144)

noncomputable def ep912 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz143 11) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz143 10) qz680) Bool.true 164192341933 1099511627776 618528558036323 216013352927756288 Bool.true 527885048741 1099511627776 618537928142645 216013352927756288

noncomputable def ep913 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz143 10) qz680 Bool.true 79592176633 549755813888 284985235286997 108006676463878144 Bool.true 218886293201 274877906944 35611051430549 13500834557984768 Bool.true

noncomputable abbrev qz681 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 9) qz144)

noncomputable def ep914 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz143 10) (@HAdd.hAdd Complex Complex Complex qz4 qz142 qz681) Bool.true 79592176633 549755813888 284985235286997 108006676463878144 Bool.true 218886293201 274877906944 35611051430549 13500834557984768

noncomputable def ep915 := @Enclosure.Complex.IsNear.addLitP qz142 qz681 Bool.false 168028019309 1099511627776 518605038969429 216013352927756288 Bool.true 177612284051 274877906944 1012700223743 421901079937024 Bool.true

noncomputable abbrev qz156 := (@HMul.hMul Real Real Real qz267 qz446 qz564)

noncomputable def ep916 := @Enclosure.Complex.IsNear.of_eq qz681 (Complex.mk (@HMul.hMul Real Real Real qz0 qz320 (Real.cos qz156)) (@HMul.hMul Real Real Real qz0 qz320 (@Neg.neg Real Real.instNeg (Real.sin qz156)))) Bool.true 327212372575 1099511627776 51365431604565 216013352927756288 Bool.true 20637004575 137438953472 3204644270773 13500834557984768 (BSN.cpow_neg_s_mk qz146 138478 1000 9 qz147 rfl)

noncomputable def ep917 := @Enclosure.Real.IsNear.mulLit_ff qz146 qz564 138478 1000 0 1 9895417793173221 4503599627370496 1000000000589389 196463000000000000000 685148832581520648819 2251799813685248000 69239000040808704971 98231500000000000000000 qz148 (BSN.isNear_log_sfrac 9 1 9895417793173221 4503599627370496 1000000000589389 196463000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz565) Bool.false 41504390431577613533184 18889465931478580854784 1000000000589389 196463000000000000000 9895417793173221 4503599627370496 1000000000589389 196463000000000000000 (BSN.log_rat_reduce_isNear 9 1 3 18 16 61752 524288 24973259072661432 36028797018963968 196463 1000000000000000 rfl rfl rfl rfl (ep185 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep918 := nat_lit 2029281399354671669204065944662386540736915816064226669025917628268516133109760

noncomputable def ep919 := nat_lit 994617788852217199126816910762094717481873167044238985159745308728743755776

noncomputable def ep920 := nat_lit 5313174283794569829593015008641207072387427914088236317663335153060552858730496

noncomputable def ep921 := BSN.sin_dyadic_bound_f 2369774532 2147483648 3 2 1048576 393310 ep918 ep109 ep919 ep920 ep112 ep919 936163 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2369774532) qz19 0 2 ep918 ep109 ep919 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2369774532) qz20 0 2 ep920 ep112 ep919 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz455 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 319047287) qz30)

noncomputable def ep922 := @Enclosure.Real.IsNear.cos_image qz156 qz455 Bool.false 319047287 1048576 185 262144 Bool.true 936163 1048576 1 196463 (@Enclosure.Real.IsNear.recentre' qz156 Bool.false 685148832581520648819 2251799813685248000 69239000040808704971 98231500000000000000000 319047287 1048576 185 262144 (ep917 rfl) rfl) (Enclosure.sfrac_false_div 319047287 1048576) (BSN.cos_reduce1 qz455 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 166758057858233819725824) qz31) 226375608064910080 72057594037927936 Bool.false 936163 1048576 48 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q1 319047287 1048576 226375608064910080 72057594037927936 48 166758057858233819725824 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 936163 1048576 166758057858233819725824 151115727451828646838272 2369774532 2147483648 393310 392926 (ep921 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep923 := nat_lit 1127820607547640801646315221217220120283834063665478922341136346953055071174656

noncomputable def ep924 := nat_lit 3381472587065217970540692029830136171416538444662348289053089550241707726012416

noncomputable def ep925 := BSN.cos_dyadic_bound_f 2369774532 2147483648 3 2 1048576 393310 ep923 ep78 ep919 ep924 ep81 ep919 472344 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2369774532) qz15 0 2 ep923 ep78 ep919 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2369774532) qz16 0 2 ep924 ep81 ep919 rfl rfl rfl rfl) rfl rfl

noncomputable def ep926 := @Enclosure.Real.IsNear.sin_image qz156 qz455 Bool.false 319047287 1048576 185 262144 Bool.false 472344 1048576 1 196463 (@Enclosure.Real.IsNear.recentre' qz156 Bool.false 685148832581520648819 2251799813685248000 69239000040808704971 98231500000000000000000 319047287 1048576 185 262144 (ep917 rfl) rfl) (Enclosure.sfrac_false_div 319047287 1048576) (BSN.sin_reduce1 qz455 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 166758057858233819725824) qz31) 226375608064910080 72057594037927936 Bool.false 472344 1048576 48 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q1 319047287 1048576 226375608064910080 72057594037927936 48 166758057858233819725824 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 472344 1048576 166758057858233819725824 151115727451828646838272 2369774532 2147483648 393310 392926 (ep925 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep927 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz320 (Real.cos qz156)) (@HMul.hMul Real Real Real qz0 qz320 (@Neg.neg Real Real.instNeg (Real.sin qz156))) Bool.true 327212372575 1099511627776 51365431604565 216013352927756288 Bool.true 20637004575 137438953472 3204644270773 13500834557984768 (@Enclosure.Real.IsNear.mulLit_ft qz320 (Real.cos qz156) 349525 1048576 1 1048576 936163 1048576 36607799 51501596672 327212372575 1099511627776 51365431604565 216013352927756288 qz324 (@Enclosure.Real.IsNear.recentre' (Real.cos qz156) Bool.true 936163 1048576 36607799 51501596672 936163 1048576 36607799 51501596672 (ep922 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz320 (@Neg.neg Real Real.instNeg (Real.sin qz156)) 349525 1048576 1 1048576 59043 131072 36607799 51501596672 20637004575 137438953472 3204644270773 13500834557984768 qz324 (@Enclosure.Real.IsNear.neg (Real.sin qz156) Bool.false 59043 131072 36607799 51501596672 (@Enclosure.Real.IsNear.recentre' (Real.sin qz156) Bool.false 472344 1048576 36607799 51501596672 59043 131072 36607799 51501596672 (ep926 rfl rfl) rfl)) rfl)

noncomputable def ep928 := @ep915 327212372575 1099511627776 51365431604565 216013352927756288 Bool.true 20637004575 137438953472 3204644270773 13500834557984768 Bool.true 175025047375969481916416 79592176633 549755813888 284985235286997 108006676463878144 Bool.true 30083503066910788943872 218886293201 274877906944 35611051430549 13500834557984768 EMRow47.d13 (ep916 ep927) rfl rfl

noncomputable abbrev qz157 := (@HMul.hMul Real Real Real qz267 qz446 qz566)

noncomputable def ep929 := @Enclosure.Complex.IsNear.of_eq qz680 (Complex.mk (@HMul.hMul Real Real Real qz0 qz34 (Real.cos qz157)) (@HMul.hMul Real Real Real qz0 qz34 (@Neg.neg Real Real.instNeg (Real.sin qz157)))) Bool.true 5007988667 1099511627776 48558087462329 216013352927756288 Bool.false 347660124063 1099511627776 48761105253861 216013352927756288 (BSN.cpow_neg_s_mk qz146 138478 1000 10 qz147 rfl)

noncomputable def ep930 := @Enclosure.Real.IsNear.mulLit_ff qz146 qz566 138478 1000 0 1 10369917190100709 4503599627370496 1000000000589389 196463000000000000000 718002696325382990451 2251799813685248000 69239000040808704971 98231500000000000000000 qz148 (BSN.isNear_log_sfrac 10 1 10369917190100709 4503599627370496 1000000000589389 196463000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz325) Bool.false 43494585150108164161536 18889465931478580854784 1000000000589389 196463000000000000000 10369917190100709 4503599627370496 1000000000589389 196463000000000000000 (BSN.log_rat_reduce_isNear 10 1 3 20 16 116991 524288 24973259072661432 36028797018963968 196463 1000000000000000 rfl rfl rfl rfl (ep200 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep931 := nat_lit 4474428356779040574864732354153977835657540867142046050113871295046891600755841

noncomputable def ep932 := nat_lit 15573605258253152388774709699413632268018948831754151159511442859062952082561

noncomputable def ep933 := nat_lit 13392137859820615419816647643063106242436584703762629848022590999422548898102401

noncomputable def ep934 := BSN.cos_dyadic_bound_f 3342324753 2147483648 3 2 1048576 393310 ep931 ep78 ep932 ep933 ep81 ep932 15103 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3342324753) qz15 0 2 ep931 ep78 ep932 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3342324753) qz16 0 2 ep933 ep81 ep932 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz456 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 334346059) qz30)

noncomputable def ep935 := @Enclosure.Real.IsNear.cos_image qz157 qz456 Bool.false 334346059 1048576 185 262144 Bool.true 15103 1048576 1 196463 (@Enclosure.Real.IsNear.recentre' qz157 Bool.false 718002696325382990451 2251799813685248000 69239000040808704971 98231500000000000000000 334346059 1048576 185 262144 (ep930 rfl) rfl) (Enclosure.sfrac_false_div 334346059 1048576) (BSN.cos_reduce2 qz456 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 235195195547431141900288) qz31) 226375608064910080 72057594037927936 Bool.false 15103 1048576 50 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q2 334346059 1048576 226375608064910080 72057594037927936 50 235195195547431141900288 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 15103 1048576 235195195547431141900288 151115727451828646838272 3342324753 2147483648 393310 392926 (ep934 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep936 := nat_lit 8041512157995670512845498469717629198369158401790279569277359176797154519694465

noncomputable def ep937 := nat_lit 21035888862427679572632575033556644876818622278008844531944350746030255152970881

noncomputable def ep938 := BSN.sin_dyadic_bound_f 3342324753 2147483648 3 2 1048576 393310 ep936 ep109 ep932 ep937 ep112 ep932 1048467 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3342324753) qz19 0 2 ep936 ep109 ep932 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3342324753) qz20 0 2 ep937 ep112 ep932 rfl rfl rfl rfl) rfl rfl

noncomputable def ep939 := @Enclosure.Real.IsNear.sin_image qz157 qz456 Bool.false 334346059 1048576 185 262144 Bool.true 1048467 1048576 1 196463 (@Enclosure.Real.IsNear.recentre' qz157 Bool.false 718002696325382990451 2251799813685248000 69239000040808704971 98231500000000000000000 334346059 1048576 185 262144 (ep930 rfl) rfl) (Enclosure.sfrac_false_div 334346059 1048576) (BSN.sin_reduce2 qz456 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 235195195547431141900288) qz31) 226375608064910080 72057594037927936 Bool.false 1048467 1048576 50 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q2 334346059 1048576 226375608064910080 72057594037927936 50 235195195547431141900288 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1048467 1048576 235195195547431141900288 151115727451828646838272 3342324753 2147483648 393310 392926 (ep938 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep940 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz34 (Real.cos qz157)) (@HMul.hMul Real Real Real qz0 qz34 (@Neg.neg Real Real.instNeg (Real.sin qz157))) Bool.true 5007988667 1099511627776 48558087462329 216013352927756288 Bool.false 347660124063 1099511627776 48761105253861 216013352927756288 (@Enclosure.Real.IsNear.mulLit_ft qz34 (Real.cos qz157) 331589 1048576 1 1048576 15103 1048576 36607799 51501596672 5007988667 1099511627776 48558087462329 216013352927756288 qz327 (@Enclosure.Real.IsNear.recentre' (Real.cos qz157) Bool.true 15103 1048576 36607799 51501596672 15103 1048576 36607799 51501596672 (ep935 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz34 (@Neg.neg Real Real.instNeg (Real.sin qz157)) 331589 1048576 1 1048576 1048467 1048576 36607799 51501596672 347660124063 1099511627776 48761105253861 216013352927756288 qz327 (@Enclosure.Real.IsNear.neg (Real.sin qz157) Bool.true 1048467 1048576 36607799 51501596672 (@Enclosure.Real.IsNear.recentre' (Real.sin qz157) Bool.true 1048467 1048576 36607799 51501596672 1048467 1048576 36607799 51501596672 (ep939 rfl rfl) rfl)) rfl)

noncomputable def ep941 := @ep913 5007988667 1099511627776 48558087462329 216013352927756288 Bool.false 347660124063 1099511627776 48761105253861 216013352927756288 Bool.true 90265694573553206165504 164192341933 1099511627776 618528558036323 216013352927756288 Bool.true 145103937304957502357504 527885048741 1099511627776 618537928142645 216013352927756288 (ep914 (BSN.head_sum_c_succ qz143 9 10 rfl rfl) (ep928 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep929 ep940) rfl rfl

noncomputable abbrev qz158 := (@HMul.hMul Real Real Real qz267 qz446 qz567)

noncomputable def ep942 := @Enclosure.Complex.IsNear.of_eq qz679 (Complex.mk (@HMul.hMul Real Real Real qz0 qz36 (Real.cos qz158)) (@HMul.hMul Real Real Real qz0 qz36 (@Neg.neg Real Real.instNeg (Real.sin qz158)))) Bool.false 191971478871 1099511627776 46414686987957 216013352927756288 Bool.false 270275347689 1099511627776 46463345765019 216013352927756288 (BSN.cpow_neg_s_mk qz146 138478 1000 11 qz147 rfl)

noncomputable def ep943 := @Enclosure.Real.IsNear.mulLit_ff qz146 qz567 138478 1000 0 1 10799156221662949 4503599627370496 1000000000589389 196463000000000000000 747722777631720925811 2251799813685248000 69239000040808704971 98231500000000000000000 qz148 (BSN.isNear_log_sfrac 11 1 10799156221662949 4503599627370496 1000000000589389 196463000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz328) Bool.false 45294944137145793642496 18889465931478580854784 1000000000589389 196463000000000000000 10799156221662949 4503599627370496 1000000000589389 196463000000000000000 (BSN.log_rat_reduce_isNear 11 1 3 22 16 166961 524288 24973259072661432 36028797018963968 196463 1000000000000000 rfl rfl rfl rfl (ep210 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep944 := nat_lit 3094048904723950910574855563701048336

noncomputable def ep945 := BSN.sin_dyadic_bound_f 1326269534 2147483648 2 1 1048576 393310 ep944 ep65 ep944 ep944 ep66 ep944 607203 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1326269534) qz19 0 1 ep944 ep65 ep944 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1326269534) qz20 0 1 ep944 ep66 ep944 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz457 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 348185551) qz30)

noncomputable def ep946 := @Enclosure.Real.IsNear.cos_image qz158 qz457 Bool.false 348185551 1048576 185 262144 Bool.false 607203 1048576 1 196463 (@Enclosure.Real.IsNear.recentre' qz158 Bool.false 747722777631720925811 2251799813685248000 69239000040808704971 98231500000000000000000 348185551 1048576 185 262144 (ep943 rfl) rfl) (Enclosure.sfrac_false_div 348185551 1048576) (BSN.cos_reduce3 qz457 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 93327921581293507182592) qz31) 226375608064910080 72057594037927936 Bool.false 607203 1048576 52 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q3 348185551 1048576 226375608064910080 72057594037927936 52 93327921581293507182592 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 607203 1048576 93327921581293507182592 151115727451828646838272 1326269534 2147483648 393310 392926 (ep945 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep947 := BSN.cos_dyadic_bound_f 1326269534 2147483648 2 1 1048576 393310 ep944 ep61 ep944 ep944 ep62 ep944 854877 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1326269534) qz15 0 1 ep944 ep61 ep944 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1326269534) qz16 0 1 ep944 ep62 ep944 rfl rfl rfl rfl) rfl rfl

noncomputable def ep948 := @Enclosure.Real.IsNear.sin_image qz158 qz457 Bool.false 348185551 1048576 185 262144 Bool.true 854877 1048576 1 196463 (@Enclosure.Real.IsNear.recentre' qz158 Bool.false 747722777631720925811 2251799813685248000 69239000040808704971 98231500000000000000000 348185551 1048576 185 262144 (ep943 rfl) rfl) (Enclosure.sfrac_false_div 348185551 1048576) (BSN.sin_reduce3 qz457 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 93327921581293507182592) qz31) 226375608064910080 72057594037927936 Bool.false 854877 1048576 52 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q3 348185551 1048576 226375608064910080 72057594037927936 52 93327921581293507182592 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 854877 1048576 93327921581293507182592 151115727451828646838272 1326269534 2147483648 393310 392926 (ep947 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep949 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz36 (Real.cos qz158)) (@HMul.hMul Real Real Real qz0 qz36 (@Neg.neg Real Real.instNeg (Real.sin qz158))) Bool.false 191971478871 1099511627776 46414686987957 216013352927756288 Bool.false 270275347689 1099511627776 46463345765019 216013352927756288 (@Enclosure.Real.IsNear.mulLit_ff qz36 (Real.cos qz158) 316157 1048576 1 1048576 607203 1048576 36607799 51501596672 191971478871 1099511627776 46414686987957 216013352927756288 qz330 (@Enclosure.Real.IsNear.recentre' (Real.cos qz158) Bool.false 607203 1048576 36607799 51501596672 607203 1048576 36607799 51501596672 (ep946 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz36 (@Neg.neg Real Real.instNeg (Real.sin qz158)) 316157 1048576 1 1048576 854877 1048576 36607799 51501596672 270275347689 1099511627776 46463345765019 216013352927756288 qz330 (@Enclosure.Real.IsNear.neg (Real.sin qz158) Bool.true 854877 1048576 36607799 51501596672 (@Enclosure.Real.IsNear.recentre' (Real.sin qz158) Bool.true 854877 1048576 36607799 51501596672 854877 1048576 36607799 51501596672 (ep948 rfl rfl) rfl)) rfl)

noncomputable def ep950 := @ep911 191971478871 1099511627776 46414686987957 216013352927756288 Bool.false 270275347689 1099511627776 46463345765019 216013352927756288 Bool.false 30543484072912788389888 13889568469 549755813888 83117905628035 27001669115969536 Bool.true 283244861734573259620352 64402425263 274877906944 41562579619229 13500834557984768 (ep912 (BSN.head_sum_c_succ qz143 10 11 rfl rfl) (ep941 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep942 ep949) rfl rfl

noncomputable abbrev qz159 := (@HMul.hMul Real Real Real qz267 qz446 qz569)

noncomputable def ep951 := @Enclosure.Complex.IsNear.of_eq qz678 (Complex.mk (@HMul.hMul Real Real Real qz0 qz38 (Real.cos qz159)) (@HMul.hMul Real Real Real qz0 qz38 (@Neg.neg Real Real.instNeg (Real.sin qz159)))) Bool.false 7951547493 274877906944 22202271335085 108006676463878144 Bool.false 315802872009 1099511627776 44588868382493 216013352927756288 (BSN.cpow_neg_s_mk qz146 138478 1000 12 qz147 rfl)

noncomputable def ep952 := @Enclosure.Real.IsNear.mulLit_ff qz146 qz569 138478 1000 0 1 11191020447815397 4503599627370496 1000000000589389 196463000000000000000 774855064786290272883 2251799813685248000 69239000040808704971 98231500000000000000000 qz148 (BSN.isNear_log_sfrac 12 1 11191020447815397 4503599627370496 1000000000589389 196463000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz570) Bool.false 46938541828353910898688 18889465931478580854784 1000000000589389 196463000000000000000 11191020447815397 4503599627370496 1000000000589389 196463000000000000000 (BSN.log_rat_reduce_isNear 12 1 3 24 16 212580 524288 24973259072661432 36028797018963968 196463 1000000000000000 rfl rfl rfl rfl (ep221 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep953 := BSN.sin_dyadic_bound_f 215557965 2147483648 1 0 1048576 393310 0 1 1 0 1 1 105076 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 215557965) qz19 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 215557965) qz20 0 0 rfl) rfl rfl

noncomputable abbrev qz458 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 180410003) qz23)

noncomputable def ep954 := @Enclosure.Real.IsNear.cos_image qz159 qz458 Bool.false 180410003 524288 741 1048576 Bool.false 105076 1048576 1 196463 (@Enclosure.Real.IsNear.recentre' qz159 Bool.false 774855064786290272883 2251799813685248000 69239000040808704971 98231500000000000000000 180410003 524288 741 1048576 (ep952 rfl) rfl) (Enclosure.sfrac_false_div 180410003 524288) (BSN.cos_reduce3 qz458 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 7584271662030946041856) qz24) 226375608064910080 72057594037927936 Bool.false 105076 1048576 54 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q3 180410003 524288 226375608064910080 72057594037927936 54 7584271662030946041856 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 105076 1048576 7584271662030946041856 75557863725914323419136 215557965 2147483648 393310 392926 (ep953 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep955 := nat_lit 2159018182086113887100877204500625

noncomputable def ep956 := BSN.cos_dyadic_bound_f 215557965 2147483648 2 1 1048576 393310 ep955 ep61 ep955 ep955 ep62 ep955 1043297 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 215557965) qz15 0 1 ep955 ep61 ep955 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 215557965) qz16 0 1 ep955 ep62 ep955 rfl rfl rfl rfl) rfl rfl

noncomputable def ep957 := @Enclosure.Real.IsNear.sin_image qz159 qz458 Bool.false 180410003 524288 741 1048576 Bool.true 1043297 1048576 1 196463 (@Enclosure.Real.IsNear.recentre' qz159 Bool.false 774855064786290272883 2251799813685248000 69239000040808704971 98231500000000000000000 180410003 524288 741 1048576 (ep952 rfl) rfl) (Enclosure.sfrac_false_div 180410003 524288) (BSN.sin_reduce3 qz458 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 7584271662030946041856) qz24) 226375608064910080 72057594037927936 Bool.false 1043297 1048576 54 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q3 180410003 524288 226375608064910080 72057594037927936 54 7584271662030946041856 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1043297 1048576 7584271662030946041856 75557863725914323419136 215557965 2147483648 393310 392926 (ep956 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep958 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz38 (Real.cos qz159)) (@HMul.hMul Real Real Real qz0 qz38 (@Neg.neg Real Real.instNeg (Real.sin qz159))) Bool.false 7951547493 274877906944 22202271335085 108006676463878144 Bool.false 315802872009 1099511627776 44588868382493 216013352927756288 (@Enclosure.Real.IsNear.mulLit_ff qz38 (Real.cos qz159) 302697 1048576 1 1048576 26269 262144 146627659 206006386688 7951547493 274877906944 22202271335085 108006676463878144 qz332 (@Enclosure.Real.IsNear.recentre' (Real.cos qz159) Bool.false 105076 1048576 146627659 206006386688 26269 262144 146627659 206006386688 (ep954 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz38 (@Neg.neg Real Real.instNeg (Real.sin qz159)) 302697 1048576 1 1048576 1043297 1048576 146627659 206006386688 315802872009 1099511627776 44588868382493 216013352927756288 qz332 (@Enclosure.Real.IsNear.neg (Real.sin qz159) Bool.true 1043297 1048576 146627659 206006386688 (@Enclosure.Real.IsNear.recentre' (Real.sin qz159) Bool.true 1043297 1048576 146627659 206006386688 1043297 1048576 146627659 206006386688 (ep957 rfl rfl) rfl)) rfl)

noncomputable def ep959 := @ep909 7951547493 274877906944 22202271335085 108006676463878144 Bool.false 315802872009 1099511627776 44588868382493 216013352927756288 Bool.false 8189344972797399531520 29792663455 549755813888 354673893847225 108006676463878144 Bool.false 15996017031094529425408 58193170957 1099511627776 709590142290157 216013352927756288 (ep910 (BSN.head_sum_c_succ qz143 11 12 rfl rfl) (ep950 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep951 ep958) rfl rfl

noncomputable abbrev qz160 := (@HMul.hMul Real Real Real qz267 qz446 qz572)

noncomputable def ep960 := @Enclosure.Complex.IsNear.of_eq qz677 (Complex.mk (@HMul.hMul Real Real Real qz0 qz40 (Real.cos qz160)) (@HMul.hMul Real Real Real qz0 qz40 (@Neg.neg Real Real.instNeg (Real.sin qz160)))) Bool.true 149764247841 549755813888 21394025034473 108006676463878144 Bool.false 57245890143 1099511627776 42624378118887 216013352927756288 (BSN.cpow_neg_s_mk qz146 138478 1000 13 qz147 rfl)

noncomputable def ep961 := @Enclosure.Real.IsNear.mulLit_ff qz146 qz572 138478 1000 0 1 11551497052968677 4503599627370496 1000000000589389 196463000000000000000 799814104450498226803 2251799813685248000 69239000040808704971 98231500000000000000000 qz148 (BSN.isNear_log_sfrac 13 1 11551497052968677 4503599627370496 1000000000589389 196463000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz573) Bool.false 48450490295254733815808 18889465931478580854784 1000000000589389 196463000000000000000 11551497052968677 4503599627370496 1000000000589389 196463000000000000000 (BSN.log_rat_reduce_isNear 13 1 3 26 16 254545 524288 24973259072661432 36028797018963968 196463 1000000000000000 rfl rfl rfl rfl (ep236 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep962 := nat_lit 27047447097596321965486949329126416

noncomputable def ep963 := BSN.cos_dyadic_bound_f 405538014 2147483648 2 1 1048576 393310 ep962 ep61 ep962 ep962 ep62 ep962 1029934 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 405538014) qz15 0 1 ep962 ep61 ep962 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 405538014) qz16 0 1 ep962 ep62 ep962 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz459 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 372442465) qz30)

noncomputable def ep964 := @Enclosure.Real.IsNear.cos_image qz160 qz459 Bool.false 372442465 1048576 185 262144 Bool.true 1029934 1048576 1 196463 (@Enclosure.Real.IsNear.recentre' qz160 Bool.false 799814104450498226803 2251799813685248000 69239000040808704971 98231500000000000000000 372442465 1048576 185 262144 (ep961 rfl) rfl) (Enclosure.sfrac_false_div 372442465 1048576) (BSN.cos_reduce2 qz459 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 28537200797087589990400) qz31) 226375608064910080 72057594037927936 Bool.false 1029934 1048576 56 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q2 372442465 1048576 226375608064910080 72057594037927936 56 28537200797087589990400 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1029934 1048576 28537200797087589990400 151115727451828646838272 405538014 2147483648 393310 392926 (ep963 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep965 := BSN.sin_dyadic_bound_f 405538014 2147483648 2 1 1048576 393310 ep962 ep65 ep962 ep962 ep66 ep962 196841 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 405538014) qz19 0 1 ep962 ep65 ep962 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 405538014) qz20 0 1 ep962 ep66 ep962 rfl rfl rfl rfl) rfl rfl

noncomputable def ep966 := @Enclosure.Real.IsNear.sin_image qz160 qz459 Bool.false 372442465 1048576 185 262144 Bool.true 196841 1048576 1 196463 (@Enclosure.Real.IsNear.recentre' qz160 Bool.false 799814104450498226803 2251799813685248000 69239000040808704971 98231500000000000000000 372442465 1048576 185 262144 (ep961 rfl) rfl) (Enclosure.sfrac_false_div 372442465 1048576) (BSN.sin_reduce2 qz459 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 28537200797087589990400) qz31) 226375608064910080 72057594037927936 Bool.false 196841 1048576 56 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q2 372442465 1048576 226375608064910080 72057594037927936 56 28537200797087589990400 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 196841 1048576 28537200797087589990400 151115727451828646838272 405538014 2147483648 393310 392926 (ep965 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep967 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz40 (Real.cos qz160)) (@HMul.hMul Real Real Real qz0 qz40 (@Neg.neg Real Real.instNeg (Real.sin qz160))) Bool.true 149764247841 549755813888 21394025034473 108006676463878144 Bool.false 57245890143 1099511627776 42624378118887 216013352927756288 (@Enclosure.Real.IsNear.mulLit_ft qz40 (Real.cos qz160) 290823 1048576 1 1048576 514967 524288 36607799 51501596672 149764247841 549755813888 21394025034473 108006676463878144 qz334 (@Enclosure.Real.IsNear.recentre' (Real.cos qz160) Bool.true 1029934 1048576 36607799 51501596672 514967 524288 36607799 51501596672 (ep964 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz40 (@Neg.neg Real Real.instNeg (Real.sin qz160)) 290823 1048576 1 1048576 196841 1048576 36607799 51501596672 57245890143 1099511627776 42624378118887 216013352927756288 qz334 (@Enclosure.Real.IsNear.neg (Real.sin qz160) Bool.true 196841 1048576 36607799 51501596672 (@Enclosure.Real.IsNear.recentre' (Real.sin qz160) Bool.true 196841 1048576 36607799 51501596672 196841 1048576 36607799 51501596672 (ep966 rfl rfl) rfl)) rfl)

noncomputable def ep968 := @ep907 149764247841 549755813888 21394025034473 108006676463878144 Bool.false 57245890143 1099511627776 42624378118887 216013352927756288 Bool.true 65955076017558302752768 59985792193 274877906944 188033959440849 54003338231939072 Bool.false 126926589978994121113600 28859765275 274877906944 188053630102261 54003338231939072 (ep908 (BSN.head_sum_c_succ qz143 12 13 rfl rfl) (ep959 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep960 ep967) rfl rfl

noncomputable abbrev qz161 := (@HMul.hMul Real Real Real qz267 qz446 qz575)

noncomputable def ep969 := @Enclosure.Complex.IsNear.of_eq qz676 (Complex.mk (@HMul.hMul Real Real Real qz0 qz42 (Real.cos qz161)) (@HMul.hMul Real Real Real qz0 qz42 (@Neg.neg Real Real.instNeg (Real.sin qz161)))) Bool.false 76092980575 549755813888 20599105450473 108006676463878144 Bool.true 251377690757 1099511627776 41267748783333 216013352927756288 (BSN.cpow_neg_s_mk qz146 138478 1000 14 qz147 rfl)

noncomputable def ep970 := @Enclosure.Real.IsNear.mulLit_ff qz146 qz575 138478 1000 0 1 11885250371606245 4503599627370496 1000000000589389 196463000000000000000 164584570095928959511 450359962737049600 69239000040808704971 98231500000000000000000 qz148 (BSN.isNear_log_sfrac 14 1 11885250371606245 4503599627370496 1000000000589389 196463000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz576) Bool.false 49850353174629559828480 18889465931478580854784 1000000000589389 196463000000000000000 11885250371606245 4503599627370496 1000000000589389 196463000000000000000 (BSN.log_rat_reduce_isNear 14 1 3 28 16 293399 524288 24973259072661432 36028797018963968 196463 1000000000000000 rfl rfl rfl rfl (ep251 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep971 := nat_lit 843952706734408117825547094423239563323188968397474158830198517874491223852161

noncomputable def ep972 := nat_lit 557192273786622107584406250772126337599978211807709067791408693016536958081

noncomputable def ep973 := nat_lit 2530743735655651109261472470768174437294366948768807058355012736237440597640321

noncomputable def ep974 := BSN.cos_dyadic_bound_f 2204198161 2147483648 3 2 1048576 393310 ep971 ep78 ep972 ep973 ep81 ep972 543050 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2204198161) qz15 0 2 ep971 ep78 ep972 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2204198161) qz16 0 2 ep973 ep81 ep972 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz460 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 383203313) qz30)

noncomputable def ep975 := @Enclosure.Real.IsNear.cos_image qz161 qz460 Bool.false 383203313 1048576 741 1048576 Bool.false 543050 1048576 1 196463 (@Enclosure.Real.IsNear.recentre' qz161 Bool.false 164584570095928959511 450359962737049600 69239000040808704971 98231500000000000000000 383203313 1048576 741 1048576 (ep970 rfl) rfl) (Enclosure.sfrac_false_div 383203313 1048576) (BSN.cos_reduce0 qz460 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 155106656559158186213376) qz31) 226375608064910080 72057594037927936 Bool.false 543050 1048576 58 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q0 383203313 1048576 226375608064910080 72057594037927936 58 155106656559158186213376 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 543050 1048576 155106656559158186213376 151115727451828646838272 2204198161 2147483648 393310 392926 (ep974 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep976 := nat_lit 1518669118302905314399917244961213512911660160546007318640124205219670973367425

noncomputable def ep977 := nat_lit 3976564617588145101920837079063832900698233789087092400804853494834254346601601

noncomputable def ep978 := BSN.sin_dyadic_bound_f 2204198161 2147483648 3 2 1048576 393310 ep976 ep109 ep972 ep977 ep112 ep972 896999 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2204198161) qz19 0 2 ep976 ep109 ep972 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2204198161) qz20 0 2 ep977 ep112 ep972 rfl rfl rfl rfl) rfl rfl

noncomputable def ep979 := @Enclosure.Real.IsNear.sin_image qz161 qz460 Bool.false 383203313 1048576 741 1048576 Bool.false 896999 1048576 1 196463 (@Enclosure.Real.IsNear.recentre' qz161 Bool.false 164584570095928959511 450359962737049600 69239000040808704971 98231500000000000000000 383203313 1048576 741 1048576 (ep970 rfl) rfl) (Enclosure.sfrac_false_div 383203313 1048576) (BSN.sin_reduce0 qz460 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 155106656559158186213376) qz31) 226375608064910080 72057594037927936 Bool.false 896999 1048576 58 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q0 383203313 1048576 226375608064910080 72057594037927936 58 155106656559158186213376 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 896999 1048576 155106656559158186213376 151115727451828646838272 2204198161 2147483648 393310 392926 (ep978 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep980 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz42 (Real.cos qz161)) (@HMul.hMul Real Real Real qz0 qz42 (@Neg.neg Real Real.instNeg (Real.sin qz161))) Bool.false 76092980575 549755813888 20599105450473 108006676463878144 Bool.true 251377690757 1099511627776 41267748783333 216013352927756288 (@Enclosure.Real.IsNear.mulLit_ff qz42 (Real.cos qz161) 280243 1048576 1 1048576 271525 524288 146627659 206006386688 76092980575 549755813888 20599105450473 108006676463878144 qz336 (@Enclosure.Real.IsNear.recentre' (Real.cos qz161) Bool.false 543050 1048576 146627659 206006386688 271525 524288 146627659 206006386688 (ep975 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz42 (@Neg.neg Real Real.instNeg (Real.sin qz161)) 280243 1048576 1 1048576 896999 1048576 146627659 206006386688 251377690757 1099511627776 41267748783333 216013352927756288 qz336 (@Enclosure.Real.IsNear.neg (Real.sin qz161) Bool.false 896999 1048576 146627659 206006386688 (@Enclosure.Real.IsNear.recentre' (Real.sin qz161) Bool.false 896999 1048576 146627659 206006386688 896999 1048576 146627659 206006386688 (ep979 rfl rfl) rfl)) rfl)

noncomputable def ep981 := @ep905 76092980575 549755813888 20599105450473 108006676463878144 Bool.true 251377690757 1099511627776 41267748783333 216013352927756288 Bool.true 12061258775192701763584 43878603811 549755813888 396667024332171 108006676463878144 Bool.true 37366525992951724638208 135938629657 1099511627776 793482269192377 216013352927756288 (ep906 (BSN.head_sum_c_succ qz143 13 14 rfl rfl) (ep968 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep969 ep980) rfl rfl

noncomputable abbrev qz162 := (@HMul.hMul Real Real Real qz267 qz446 qz578)

noncomputable def ep982 := @Enclosure.Complex.IsNear.of_eq qz675 (Complex.mk (@HMul.hMul Real Real Real qz0 qz44 (Real.cos qz162)) (@HMul.hMul Real Real Real qz0 qz44 (@Neg.neg Real Real.instNeg (Real.sin qz162)))) Bool.true 114515591511 1099511627776 39728173019005 216013352927756288 Bool.false 129885558081 549755813888 19916788789799 108006676463878144 (BSN.cpow_neg_s_mk qz146 138478 1000 15 qz147 rfl)

noncomputable def ep983 := @Enclosure.Real.IsNear.mulLit_ff qz146 qz578 138478 1000 0 1 12195965485668069 4503599627370496 1000000000589389 196463000000000000000 844436454262171429491 2251799813685248000 69239000040808704971 98231500000000000000000 qz148 (BSN.isNear_log_sfrac 15 1 12195965485668069 4503599627370496 1000000000589389 196463000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz579) Bool.false 51153586820399524478976 18889465931478580854784 1000000000589389 196463000000000000000 12195965485668069 4503599627370496 1000000000589389 196463000000000000000 (BSN.log_rat_reduce_isNear 15 1 3 30 16 329571 524288 24973259072661432 36028797018963968 196463 1000000000000000 rfl rfl rfl rfl (ep262 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep984 := nat_lit 1356520984812236138597870855944000388359393995733603058319198886811960292212736

noncomputable def ep985 := nat_lit 1438381377095433872590256024872323996512887800548408037035366641288997830656

noncomputable def ep986 := nat_lit 4066686191682517548048432055782256517085156211599712358883525927153302880976896

noncomputable def ep987 := BSN.cos_dyadic_bound_f 2481614148 2147483648 3 2 1048576 393310 ep984 ep78 ep985 ep986 ep81 ep985 422971 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2481614148) qz15 0 2 ep984 ep78 ep985 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2481614148) qz16 0 2 ep986 ep81 ep985 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz461 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 196610683) qz23)

noncomputable def ep988 := @Enclosure.Real.IsNear.cos_image qz162 qz461 Bool.false 196610683 524288 185 262144 Bool.true 422971 1048576 1 196463 (@Enclosure.Real.IsNear.recentre' qz162 Bool.false 844436454262171429491 2251799813685248000 69239000040808704971 98231500000000000000000 196610683 524288 185 262144 (ep983 rfl) rfl) (Enclosure.sfrac_false_div 196610683 524288) (BSN.cos_reduce2 qz461 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 87314035597211709997056) qz24) 226375608064910080 72057594037927936 Bool.false 422971 1048576 59 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q2 196610683 524288 226375608064910080 72057594037927936 59 87314035597211709997056 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 422971 1048576 87314035597211709997056 75557863725914323419136 2481614148 2147483648 393310 392926 (ep987 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep989 := nat_lit 2440587067560348702378095335879302839849698882080046778544929702948497327718400

noncomputable def ep990 := nat_lit 6389684940428473041863198798500761770278666682342091759367234818874453671346176

noncomputable def ep991 := BSN.sin_dyadic_bound_f 2481614148 2147483648 3 2 1048576 393310 ep989 ep109 ep985 ep990 ep112 ep985 959482 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2481614148) qz19 0 2 ep989 ep109 ep985 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2481614148) qz20 0 2 ep990 ep112 ep985 rfl rfl rfl rfl) rfl rfl

noncomputable def ep992 := @Enclosure.Real.IsNear.sin_image qz162 qz461 Bool.false 196610683 524288 185 262144 Bool.true 959482 1048576 1 196463 (@Enclosure.Real.IsNear.recentre' qz162 Bool.false 844436454262171429491 2251799813685248000 69239000040808704971 98231500000000000000000 196610683 524288 185 262144 (ep983 rfl) rfl) (Enclosure.sfrac_false_div 196610683 524288) (BSN.sin_reduce2 qz461 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 87314035597211709997056) qz24) 226375608064910080 72057594037927936 Bool.false 959482 1048576 59 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q2 196610683 524288 226375608064910080 72057594037927936 59 87314035597211709997056 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 959482 1048576 87314035597211709997056 75557863725914323419136 2481614148 2147483648 393310 392926 (ep991 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep993 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz44 (Real.cos qz162)) (@HMul.hMul Real Real Real qz0 qz44 (@Neg.neg Real Real.instNeg (Real.sin qz162))) Bool.true 114515591511 1099511627776 39728173019005 216013352927756288 Bool.false 129885558081 549755813888 19916788789799 108006676463878144 (@Enclosure.Real.IsNear.mulLit_ft qz44 (Real.cos qz162) 270741 1048576 1 1048576 422971 1048576 36607799 51501596672 114515591511 1099511627776 39728173019005 216013352927756288 qz338 (@Enclosure.Real.IsNear.recentre' (Real.cos qz162) Bool.true 422971 1048576 36607799 51501596672 422971 1048576 36607799 51501596672 (ep988 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz44 (@Neg.neg Real Real.instNeg (Real.sin qz162)) 270741 1048576 1 1048576 479741 524288 36607799 51501596672 129885558081 549755813888 19916788789799 108006676463878144 qz338 (@Enclosure.Real.IsNear.neg (Real.sin qz162) Bool.true 479741 524288 36607799 51501596672 (@Enclosure.Real.IsNear.recentre' (Real.sin qz162) Bool.true 959482 1048576 36607799 51501596672 479741 524288 36607799 51501596672 (ep992 rfl rfl) rfl)) rfl)

noncomputable def ep994 := @ep903 114515591511 1099511627776 39728173019005 216013352927756288 Bool.false 129885558081 549755813888 19916788789799 108006676463878144 Bool.true 111200647314766355759104 202272799133 1099511627776 833062221683347 216013352927756288 Bool.false 68077629404331051581440 123832486505 1099511627776 833315846771975 216013352927756288 (ep904 (BSN.head_sum_c_succ qz143 14 15 rfl rfl) (ep981 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep982 ep993) rfl rfl

noncomputable abbrev qz163 := (@HMul.hMul Real Real Real qz267 qz446 qz581)

noncomputable def ep995 := @Enclosure.Complex.IsNear.of_eq qz674 (Complex.mk (@HMul.hMul Real Real Real qz0 qz46 (Real.cos qz163)) (@HMul.hMul Real Real Real qz0 qz46 (@Neg.neg Real Real.instNeg (Real.sin qz163)))) Bool.false 215754961149 1099511627776 38599258537805 216013352927756288 Bool.true 42578576775 274877906944 9641300762999 54003338231939072 (BSN.cpow_neg_s_mk qz146 138478 1000 16 qz147 rfl)

noncomputable def ep996 := @Enclosure.Real.IsNear.mulLit_ff qz146 qz581 138478 1000 0 1 3121657384082679 1125899906842624 250000000196463 49115750000000000000 216140435616500611281 562949953421312000 17309750013602901657 24557875000000000000000 qz148 (BSN.isNear_log_sfrac 16 1 3121657384082679 1125899906842624 250000000196463 49115750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz582) Bool.false 52372720210750067441664 18889465931478580854784 1000000000785852 196463000000000000000 3121657384082679 1125899906842624 250000000196463 49115750000000000000 (BSN.log_rat_reduce_isNear 16 1 4 32 32 0 524288 24973259072661432 36028797018963968 196463 1000000000000000 rfl rfl rfl rfl (ep273 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep997 := nat_lit 151537578868921088952823708336930840260169608394610771678754583178925882474496

noncomputable def ep998 := nat_lit 17983744104790980864576928442579656970276866142550067756172516113845846016

noncomputable def ep999 := nat_lit 454576769118553684896741971153907361466568271451547214900751404504549955731456

noncomputable def ep1000 := BSN.cos_dyadic_bound_f 1435026808 2147483648 3 2 1048576 393310 ep997 ep78 ep998 ep999 ep81 ep998 823043 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1435026808) qz15 0 2 ep997 ep78 ep998 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1435026808) qz16 0 2 ep999 ep81 ep998 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz462 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 402592933) qz30)

noncomputable def ep1001 := @Enclosure.Real.IsNear.cos_image qz163 qz462 Bool.false 402592933 1048576 741 1048576 Bool.false 823043 1048576 1 196463 (@Enclosure.Real.IsNear.recentre' qz163 Bool.false 216140435616500611281 562949953421312000 17309750013602901657 24557875000000000000000 402592933 1048576 741 1048576 (ep996 rfl) rfl) (Enclosure.sfrac_false_div 402592933 1048576) (BSN.cos_reduce0 qz462 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 100981034351280894509056) qz31) 226375608064910080 72057594037927936 Bool.false 823043 1048576 61 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q0 402592933 1048576 226375608064910080 72057594037927936 61 100981034351280894509056 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 823043 1048576 100981034351280894509056 151115727451828646838272 1435026808 2147483648 393310 392926 (ep1000 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1002 := nat_lit 4240724478764327936608846018963050496

noncomputable def ep1003 := BSN.sin_dyadic_bound_f 1435026808 2147483648 2 1 1048576 393310 ep1002 ep65 ep1002 ep1002 ep66 ep1002 649700 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1435026808) qz19 0 1 ep1002 ep65 ep1002 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1435026808) qz20 0 1 ep1002 ep66 ep1002 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1004 := @Enclosure.Real.IsNear.sin_image qz163 qz462 Bool.false 402592933 1048576 741 1048576 Bool.false 649700 1048576 1 196463 (@Enclosure.Real.IsNear.recentre' qz163 Bool.false 216140435616500611281 562949953421312000 17309750013602901657 24557875000000000000000 402592933 1048576 741 1048576 (ep996 rfl) rfl) (Enclosure.sfrac_false_div 402592933 1048576) (BSN.sin_reduce0 qz462 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 100981034351280894509056) qz31) 226375608064910080 72057594037927936 Bool.false 649700 1048576 61 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q0 402592933 1048576 226375608064910080 72057594037927936 61 100981034351280894509056 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 649700 1048576 100981034351280894509056 151115727451828646838272 1435026808 2147483648 393310 392926 (ep1003 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1005 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz46 (Real.cos qz163)) (@HMul.hMul Real Real Real qz0 qz46 (@Neg.neg Real Real.instNeg (Real.sin qz163))) Bool.false 215754961149 1099511627776 38599258537805 216013352927756288 Bool.true 42578576775 274877906944 9641300762999 54003338231939072 (@Enclosure.Real.IsNear.mulLit_ff qz46 (Real.cos qz163) 262143 1048576 1 1048576 823043 1048576 146627659 206006386688 215754961149 1099511627776 38599258537805 216013352927756288 qz340 (@Enclosure.Real.IsNear.recentre' (Real.cos qz163) Bool.false 823043 1048576 146627659 206006386688 823043 1048576 146627659 206006386688 (ep1001 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz46 (@Neg.neg Real Real.instNeg (Real.sin qz163)) 262143 1048576 1 1048576 162425 262144 146627659 206006386688 42578576775 274877906944 9641300762999 54003338231939072 qz340 (@Enclosure.Real.IsNear.neg (Real.sin qz163) Bool.false 162425 262144 146627659 206006386688 (@Enclosure.Real.IsNear.recentre' (Real.sin qz163) Bool.false 649700 1048576 146627659 206006386688 162425 262144 146627659 206006386688 (ep1004 rfl rfl) rfl)) rfl)

noncomputable def ep1006 := @ep901 215754961149 1099511627776 38599258537805 216013352927756288 Bool.true 42578576775 274877906944 9641300762999 54003338231939072 Bool.false 14823793904151917756416 421317563 34359738368 27239421256911 6750417278992384 Bool.true 12776825556100112711680 46481820595 1099511627776 871881049823971 216013352927756288 (ep902 (BSN.head_sum_c_succ qz143 15 16 rfl rfl) (ep994 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep995 ep1005) rfl rfl

theorem EMRow47.d14 : Enclosure.Complex.IsNear qz155 Bool.false 421317563 34359738368 27239421256911 6750417278992384 Bool.true 46481820595 1099511627776 871881049823971 216013352927756288 := ep900 (BSN.head_sum_c_succ qz143 16 17 rfl rfl) (ep1006 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable abbrev qz164 := (BSN.headSumC qz444 25)

noncomputable abbrev qz682 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 24) qz144)

noncomputable def ep1007 := @Enclosure.Complex.IsNear.of_eq qz164 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz143 24) qz682) Bool.false 443470136011 549755813888 35803525807451 6750417278992384 Bool.true 280073031981 1099511627776 1145467376557549 216013352927756288

noncomputable def ep1008 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz143 24) qz682 Bool.false 335241315661 549755813888 278543002403673 54003338231939072 Bool.true 220763681237 1099511627776 1114070804254261 216013352927756288 Bool.false

noncomputable abbrev qz683 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 23) qz144)

noncomputable def ep1009 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz143 24) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz143 23) qz683) Bool.false 335241315661 549755813888 278543002403673 54003338231939072 Bool.true 220763681237 1099511627776 1114070804254261 216013352927756288

noncomputable def ep1010 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz143 23) qz683 Bool.false 488933946773 1099511627776 1081992575519659 216013352927756288 Bool.true 80756948045 1099511627776 1081928697932765 216013352927756288 Bool.false

noncomputable abbrev qz684 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 22) qz144)

noncomputable def ep1011 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz143 23) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz143 22) qz684) Bool.false 488933946773 1099511627776 1081992575519659 216013352927756288 Bool.true 80756948045 1099511627776 1081928697932765 216013352927756288

noncomputable def ep1012 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz143 22) qz684 Bool.false 323052864317 1099511627776 1049110933086587 216013352927756288 Bool.false 84876433255 1099511627776 1049047273180697 216013352927756288 Bool.false

noncomputable abbrev qz685 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 21) qz144)

noncomputable def ep1013 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz143 22) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz143 21) qz685) Bool.false 323052864317 1099511627776 1049110933086587 216013352927756288 Bool.false 84876433255 1099511627776 1049047273180697 216013352927756288

noncomputable def ep1014 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz143 21) qz685 Bool.false 128589598837 1099511627776 1015270614727507 216013352927756288 Bool.false 225417592945 1099511627776 1015299549798147 216013352927756288 Bool.false

noncomputable abbrev qz686 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 20) qz144)

noncomputable def ep1015 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz143 21) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz143 20) qz686) Bool.false 128589598837 1099511627776 1015270614727507 216013352927756288 Bool.false 225417592945 1099511627776 1015299549798147 216013352927756288

noncomputable def ep1016 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz143 20) qz686 Bool.true 28602404463 274877906944 122591660210123 27001669115969536 Bool.false 131401720263 549755813888 245233625360785 54003338231939072 Bool.false

noncomputable abbrev qz687 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 19) qz144)

noncomputable def ep1017 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz143 20) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz143 19) qz687) Bool.true 28602404463 274877906944 122591660210123 27001669115969536 Bool.false 131401720263 549755813888 245233625360785 54003338231939072

noncomputable def ep1018 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz143 19) qz687 Bool.true 312588136027 1099511627776 945345942040249 216013352927756288 Bool.false 53375446377 549755813888 118197695726697 27001669115969536 Bool.false

noncomputable abbrev qz688 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 18) qz144)

noncomputable def ep1019 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz143 19) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz143 18) qz688) Bool.true 312588136027 1099511627776 945345942040249 216013352927756288 Bool.false 53375446377 549755813888 118197695726697 27001669115969536

noncomputable def ep1020 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz143 18) qz688 Bool.true 235946610927 1099511627776 909094255910157 216013352927756288 Bool.true 140813590869 1099511627776 909194011177185 216013352927756288 Bool.true

noncomputable abbrev qz689 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 17) qz144)

noncomputable def ep1021 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz143 18) (@HAdd.hAdd Complex Complex Complex qz4 qz155 qz689) Bool.true 235946610927 1099511627776 909094255910157 216013352927756288 Bool.true 140813590869 1099511627776 909194011177185 216013352927756288

noncomputable def ep1022 := @Enclosure.Complex.IsNear.addLitP qz155 qz689 Bool.false 421317563 34359738368 27239421256911 6750417278992384 Bool.true 46481820595 1099511627776 871881049823971 216013352927756288 Bool.true

noncomputable abbrev qz165 := (@HMul.hMul Real Real Real qz267 qz446 qz592)

noncomputable def ep1023 := @Enclosure.Complex.IsNear.of_eq qz689 (Complex.mk (@HMul.hMul Real Real Real qz0 qz49 (Real.cos qz165)) (@HMul.hMul Real Real Real qz0 qz49 (@Neg.neg Real Real.instNeg (Real.sin qz165)))) Bool.true 249428772943 1099511627776 37432775689005 216013352927756288 Bool.true 47165885137 549755813888 18656480676607 108006676463878144 (BSN.cpow_neg_s_mk qz146 138478 1000 17 qz147 rfl)

noncomputable def ep1024 := @Enclosure.Real.IsNear.mulLit_ff qz146 qz592 138478 1000 0 1 3189913004350711 1125899906842624 250000000196463 49115750000000000000 220866386508238878929 562949953421312000 17309750013602901657 24557875000000000000000 qz148 (BSN.isNear_log_sfrac 17 1 3189913004350711 1125899906842624 250000000196463 49115750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz593) Bool.false 53517859495200818200576 18889465931478580854784 1000000000785852 196463000000000000000 3189913004350711 1125899906842624 250000000196463 49115750000000000000 (BSN.log_rat_reduce_isNear 17 1 4 34 32 31784 524288 24973259072661432 36028797018963968 196463 1000000000000000 rfl rfl rfl rfl (ep310 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1025 := nat_lit 2926604160612591147742954810157685539611536389702977394387690336566459773491745

noncomputable def ep1026 := nat_lit 2067814364877697529338413603327650431391592384328239131576555121081726540321

noncomputable def ep1027 := nat_lit 7661567768823174829041190880769503074474627966314123645754731697001833754270241

noncomputable def ep1028 := BSN.sin_dyadic_bound_f 2596802637 2147483648 3 2 1048576 393310 ep1025 ep109 ep1026 ep1027 ep112 ep1026 980779 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2596802637) qz19 0 2 ep1025 ep109 ep1026 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2596802637) qz20 0 2 ep1027 ep112 ep1026 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz463 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 411395703) qz30)

noncomputable def ep1029 := @Enclosure.Real.IsNear.cos_image qz165 qz463 Bool.false 411395703 1048576 185 262144 Bool.true 980779 1048576 1 196463 (@Enclosure.Real.IsNear.recentre' qz165 Bool.false 220866386508238878929 562949953421312000 17309750013602901657 24557875000000000000000 411395703 1048576 185 262144 (ep1024 rfl) rfl) (Enclosure.sfrac_false_div 411395703 1048576) (BSN.cos_reduce1 qz463 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 182733740478426928644096) qz31) 226375608064910080 72057594037927936 Bool.false 980779 1048576 62 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q1 411395703 1048576 226375608064910080 72057594037927936 62 182733740478426928644096 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 980779 1048576 182733740478426928644096 151115727451828646838272 2596802637 2147483648 393310 392926 (ep1028 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1030 := nat_lit 1626810228946940725425791967244637588864805368672466658718306433701847308180001

noncomputable def ep1031 := nat_lit 4876295058111066781218699074527257465731632921248743497891766190863378471459361

noncomputable def ep1032 := BSN.cos_dyadic_bound_f 2596802637 2147483648 3 2 1048576 393310 ep1030 ep78 ep1026 ep1031 ep81 ep1026 370922 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2596802637) qz15 0 2 ep1030 ep78 ep1026 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2596802637) qz16 0 2 ep1031 ep81 ep1026 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1033 := @Enclosure.Real.IsNear.sin_image qz165 qz463 Bool.false 411395703 1048576 185 262144 Bool.false 370922 1048576 1 196463 (@Enclosure.Real.IsNear.recentre' qz165 Bool.false 220866386508238878929 562949953421312000 17309750013602901657 24557875000000000000000 411395703 1048576 185 262144 (ep1024 rfl) rfl) (Enclosure.sfrac_false_div 411395703 1048576) (BSN.sin_reduce1 qz463 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 182733740478426928644096) qz31) 226375608064910080 72057594037927936 Bool.false 370922 1048576 62 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q1 411395703 1048576 226375608064910080 72057594037927936 62 182733740478426928644096 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 370922 1048576 182733740478426928644096 151115727451828646838272 2596802637 2147483648 393310 392926 (ep1032 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1034 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz49 (Real.cos qz165)) (@HMul.hMul Real Real Real qz0 qz49 (@Neg.neg Real Real.instNeg (Real.sin qz165))) Bool.true 249428772943 1099511627776 37432775689005 216013352927756288 Bool.true 47165885137 549755813888 18656480676607 108006676463878144 (@Enclosure.Real.IsNear.mulLit_ft qz49 (Real.cos qz165) 254317 1048576 1 1048576 980779 1048576 36607799 51501596672 249428772943 1099511627776 37432775689005 216013352927756288 qz342 (@Enclosure.Real.IsNear.recentre' (Real.cos qz165) Bool.true 980779 1048576 36607799 51501596672 980779 1048576 36607799 51501596672 (ep1029 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz49 (@Neg.neg Real Real.instNeg (Real.sin qz165)) 254317 1048576 1 1048576 185461 524288 36607799 51501596672 47165885137 549755813888 18656480676607 108006676463878144 qz342 (@Enclosure.Real.IsNear.neg (Real.sin qz165) Bool.false 185461 524288 36607799 51501596672 (@Enclosure.Real.IsNear.recentre' (Real.sin qz165) Bool.false 370922 1048576 36607799 51501596672 185461 524288 36607799 51501596672 (ep1033 rfl rfl) rfl)) rfl)

noncomputable def ep1035 := @ep1022 249428772943 1099511627776 37432775689005 216013352927756288 Bool.true 47165885137 549755813888 18656480676607 108006676463878144 Bool.true 8107063820268009947136 235946610927 1099511627776 909094255910157 216013352927756288 Bool.true 77413090254678940188672 140813590869 1099511627776 909194011177185 216013352927756288 EMRow47.d14 (ep1023 ep1034) rfl rfl

noncomputable abbrev qz166 := (@HMul.hMul Real Real Real qz267 qz446 qz595)

noncomputable def ep1036 := @Enclosure.Complex.IsNear.of_eq qz688 (Complex.mk (@HMul.hMul Real Real Real qz0 qz51 (Real.cos qz166)) (@HMul.hMul Real Real Real qz0 qz51 (@Neg.neg Real Real.instNeg (Real.sin qz166)))) Bool.true 19160381275 274877906944 9062921532523 54003338231939072 Bool.false 247564483623 1099511627776 36387554636391 216013352927756288 (BSN.cpow_neg_s_mk qz146 138478 1000 18 qz147 rfl)

noncomputable def ep1037 := @Enclosure.Real.IsNear.mulLit_ff qz146 qz595 138478 1000 0 1 3254268794313975 1125899906842624 250000000196463 49115750000000000000 9012892681980212601 22517998136852480 17309750013602901657 24557875000000000000000 qz148 (BSN.isNear_log_sfrac 18 1 3254268794313975 1125899906842624 250000000196463 49115750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz596) Bool.false 54597570484265130393600 18889465931478580854784 1000000000785852 196463000000000000000 3254268794313975 1125899906842624 250000000196463 49115750000000000000 (BSN.log_rat_reduce_isNear 18 1 4 36 32 61752 524288 24973259072661432 36028797018963968 196463 1000000000000000 rfl rfl rfl rfl (ep321 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1038 := nat_lit 1983432025553671949451249265619236670669733931185702414417092651152197816975616

noncomputable def ep1039 := nat_lit 3072067719024688211037240340867649576483664193860975095940156811420080046336

noncomputable def ep1040 := nat_lit 5944151941222966471931673316175974712856234465169385293059397639833753290834176

noncomputable def ep1041 := BSN.cos_dyadic_bound_f 2728530722 2147483648 3 2 1048576 393310 ep1038 ep78 ep1039 ep1040 ep81 ep1039 310100 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2728530722) qz15 0 2 ep1038 ep78 ep1039 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2728530722) qz16 0 2 ep1040 ep81 ep1039 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz464 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 13115485) (@Nat.cast Real Real.instNatCast 32768))

noncomputable abbrev qz690 := (@Nat.cast Real Real.instNatCast 4722366482869645213696)

noncomputable def ep1042 := @Enclosure.Real.IsNear.cos_image qz166 qz464 Bool.false 13115485 32768 185 262144 Bool.true 310100 1048576 1 196463 (@Enclosure.Real.IsNear.recentre' qz166 Bool.false 9012892681980212601 22517998136852480 17309750013602901657 24557875000000000000000 13115485 32768 185 262144 (ep1037 rfl) rfl) (Enclosure.sfrac_false_div 13115485 32768) (BSN.cos_reduce2 qz464 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 6000102513039282012160) qz690) 226375608064910080 72057594037927936 Bool.false 310100 1048576 63 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q2 13115485 32768 226375608064910080 72057594037927936 63 6000102513039282012160 4722366482869645213696 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 310100 1048576 6000102513039282012160 4722366482869645213696 2728530722 2147483648 393310 392926 (ep1041 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1043 := nat_lit 3567719991821389758443418885841931887544334144779175565874014646624820006519040

noncomputable def ep1044 := nat_lit 9339054726082361776914893930938893034730377780012542046181373344417943696998656

noncomputable def ep1045 := BSN.sin_dyadic_bound_f 2728530722 2147483648 3 2 1048576 393310 ep1043 ep109 ep1039 ep1044 ep112 ep1039 1001673 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2728530722) qz19 0 2 ep1043 ep109 ep1039 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2728530722) qz20 0 2 ep1044 ep112 ep1039 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1046 := @Enclosure.Real.IsNear.sin_image qz166 qz464 Bool.false 13115485 32768 185 262144 Bool.true 1001673 1048576 1 196463 (@Enclosure.Real.IsNear.recentre' qz166 Bool.false 9012892681980212601 22517998136852480 17309750013602901657 24557875000000000000000 13115485 32768 185 262144 (ep1037 rfl) rfl) (Enclosure.sfrac_false_div 13115485 32768) (BSN.sin_reduce2 qz464 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 6000102513039282012160) qz690) 226375608064910080 72057594037927936 Bool.false 1001673 1048576 63 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q2 13115485 32768 226375608064910080 72057594037927936 63 6000102513039282012160 4722366482869645213696 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1001673 1048576 6000102513039282012160 4722366482869645213696 2728530722 2147483648 393310 392926 (ep1045 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1047 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz51 (Real.cos qz166)) (@HMul.hMul Real Real Real qz0 qz51 (@Neg.neg Real Real.instNeg (Real.sin qz166))) Bool.true 19160381275 274877906944 9062921532523 54003338231939072 Bool.false 247564483623 1099511627776 36387554636391 216013352927756288 (@Enclosure.Real.IsNear.mulLit_ft qz51 (Real.cos qz166) 247151 1048576 1 1048576 77525 262144 36607799 51501596672 19160381275 274877906944 9062921532523 54003338231939072 qz344 (@Enclosure.Real.IsNear.recentre' (Real.cos qz166) Bool.true 310100 1048576 36607799 51501596672 77525 262144 36607799 51501596672 (ep1042 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz51 (@Neg.neg Real Real.instNeg (Real.sin qz166)) 247151 1048576 1 1048576 1001673 1048576 36607799 51501596672 247564483623 1099511627776 36387554636391 216013352927756288 qz344 (@Enclosure.Real.IsNear.neg (Real.sin qz166) Bool.true 1001673 1048576 36607799 51501596672 (@Enclosure.Real.IsNear.recentre' (Real.sin qz166) Bool.true 1001673 1048576 36607799 51501596672 1001673 1048576 36607799 51501596672 (ep1046 rfl rfl) rfl)) rfl)

noncomputable def ep1048 := @ep1020 19160381275 274877906944 9062921532523 54003338231939072 Bool.false 247564483623 1099511627776 36387554636391 216013352927756288 Bool.true 85923572566628119871488 312588136027 1099511627776 945345942040249 216013352927756288 Bool.false 117373847858491743535104 53375446377 549755813888 118197695726697 27001669115969536 (ep1021 (BSN.head_sum_c_succ qz143 17 18 rfl rfl) (ep1035 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1036 ep1047) rfl rfl

noncomputable abbrev qz167 := (@HMul.hMul Real Real Real qz267 qz446 qz598)

noncomputable def ep1049 := @Enclosure.Complex.IsNear.of_eq qz687 (Complex.mk (@HMul.hMul Real Real Real qz0 qz53 (Real.cos qz167)) (@HMul.hMul Real Real Real qz0 qz53 (@Neg.neg Real Real.instNeg (Real.sin qz167)))) Bool.false 198178518175 1099511627776 35387339640735 216013352927756288 Bool.false 39013136943 274877906944 8838233907391 54003338231939072 (BSN.cpow_neg_s_mk qz146 138478 1000 19 qz147 rfl)

noncomputable def ep1050 := @Enclosure.Real.IsNear.mulLit_ff qz146 qz598 138478 1000 0 1 3315143513283831 1125899906842624 250000000196463 49115750000000000000 229537221716259174609 562949953421312000 17309750013602901657 24557875000000000000000 qz148 (BSN.isNear_log_sfrac 19 1 3315143513283831 1125899906842624 250000000196463 49115750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz599) Bool.false 55618878793361701994496 18889465931478580854784 1000000000785852 196463000000000000000 3315143513283831 1125899906842624 250000000196463 49115750000000000000 (BSN.log_rat_reduce_isNear 19 1 4 38 32 90099 524288 24973259072661432 36028797018963968 196463 1000000000000000 rfl rfl rfl rfl (ep332 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1051 := nat_lit 912720054376009165190055008522382353190903424846100296541140902842114821324800

noncomputable def ep1052 := nat_lit 201317293518787459169582775555843113983181220767657323246741894650402963456

noncomputable def ep1053 := nat_lit 2390131342985755491040059983541053845696393343096638855274874306280866736766976

noncomputable def ep1054 := BSN.sin_dyadic_bound_f 1940819448 2147483648 3 2 1048576 393310 ep1051 ep109 ep1052 ep1053 ep112 ep1052 823825 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1940819448) qz19 0 2 ep1051 ep109 ep1052 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1940819448) qz20 0 2 ep1053 ep112 ep1052 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz465 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 53443299) qz634)

noncomputable def ep1055 := @Enclosure.Real.IsNear.cos_image qz167 qz465 Bool.false 53443299 131072 185 262144 Bool.false 823825 1048576 1 196463 (@Enclosure.Real.IsNear.recentre' qz167 Bool.false 229537221716259174609 562949953421312000 17309750013602901657 24557875000000000000000 53443299 131072 185 262144 (ep1050 rfl) rfl) (Enclosure.sfrac_false_div 53443299 131072) (BSN.cos_reduce3 qz465 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 17071628405671500709888) qz370) 226375608064910080 72057594037927936 Bool.false 823825 1048576 64 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q3 53443299 131072 226375608064910080 72057594037927936 64 17071628405671500709888 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 823825 1048576 17071628405671500709888 18889465931478580854784 1940819448 2147483648 393310 392926 (ep1054 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1056 := nat_lit 507156171228235663976328152634903904267827761012619123555410164643241746497536

noncomputable def ep1057 := nat_lit 1521065879097669417010645292353600026575516920596322056019737010140424433565696

noncomputable def ep1058 := BSN.cos_dyadic_bound_f 1940819448 2147483648 3 2 1048576 393310 ep1056 ep78 ep1052 ep1057 ep81 ep1052 648708 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1940819448) qz15 0 2 ep1056 ep78 ep1052 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1940819448) qz16 0 2 ep1057 ep81 ep1052 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1059 := @Enclosure.Real.IsNear.sin_image qz167 qz465 Bool.false 53443299 131072 185 262144 Bool.true 648708 1048576 1 196463 (@Enclosure.Real.IsNear.recentre' qz167 Bool.false 229537221716259174609 562949953421312000 17309750013602901657 24557875000000000000000 53443299 131072 185 262144 (ep1050 rfl) rfl) (Enclosure.sfrac_false_div 53443299 131072) (BSN.sin_reduce3 qz465 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 17071628405671500709888) qz370) 226375608064910080 72057594037927936 Bool.false 648708 1048576 64 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q3 53443299 131072 226375608064910080 72057594037927936 64 17071628405671500709888 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 648708 1048576 17071628405671500709888 18889465931478580854784 1940819448 2147483648 393310 392926 (ep1058 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1060 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz53 (Real.cos qz167)) (@HMul.hMul Real Real Real qz0 qz53 (@Neg.neg Real Real.instNeg (Real.sin qz167))) Bool.false 198178518175 1099511627776 35387339640735 216013352927756288 Bool.false 39013136943 274877906944 8838233907391 54003338231939072 (@Enclosure.Real.IsNear.mulLit_ff qz53 (Real.cos qz167) 240559 1048576 1 1048576 823825 1048576 36607799 51501596672 198178518175 1099511627776 35387339640735 216013352927756288 qz346 (@Enclosure.Real.IsNear.recentre' (Real.cos qz167) Bool.false 823825 1048576 36607799 51501596672 823825 1048576 36607799 51501596672 (ep1055 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz53 (@Neg.neg Real Real.instNeg (Real.sin qz167)) 240559 1048576 1 1048576 162177 262144 36607799 51501596672 39013136943 274877906944 8838233907391 54003338231939072 qz346 (@Enclosure.Real.IsNear.neg (Real.sin qz167) Bool.true 162177 262144 36607799 51501596672 (@Enclosure.Real.IsNear.recentre' (Real.sin qz167) Bool.true 648708 1048576 36607799 51501596672 162177 262144 36607799 51501596672 (ep1059 rfl rfl) rfl)) rfl)

noncomputable def ep1061 := @ep1018 198178518175 1099511627776 35387339640735 216013352927756288 Bool.false 39013136943 274877906944 8838233907391 54003338231939072 Bool.true 125794705157682628657152 28602404463 274877906944 122591660210123 27001669115969536 Bool.false 36119429834734433206272 131401720263 549755813888 245233625360785 54003338231939072 (ep1019 (BSN.head_sum_c_succ qz143 18 19 rfl rfl) (ep1048 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1049 ep1060) rfl rfl

noncomputable abbrev qz168 := (@HMul.hMul Real Real Real qz267 qz446 qz601)

noncomputable def ep1062 := @Enclosure.Complex.IsNear.of_eq qz686 (Complex.mk (@HMul.hMul Real Real Real qz0 qz55 (Real.cos qz168)) (@HMul.hMul Real Real Real qz0 qz55 (@Neg.neg Real Real.instNeg (Real.sin qz168)))) Bool.false 242999216689 1099511627776 34537333046523 216013352927756288 Bool.true 37385847581 1099511627776 34365048355007 216013352927756288 (BSN.cpow_neg_s_mk qz146 138478 1000 20 qz147 rfl)

noncomputable def ep1063 := @Enclosure.Real.IsNear.mulLit_ff qz146 qz601 138478 1000 0 1 3372893643545847 1125899906842624 250000000196463 49115750000000000000 233535782985470900433 562949953421312000 17309750013602901657 24557875000000000000000 qz148 (BSN.isNear_log_sfrac 20 1 3372893643545847 1125899906842624 250000000196463 49115750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz602) Bool.false 56587765202795681021952 18889465931478580854784 1000000000785852 196463000000000000000 3372893643545847 1125899906842624 250000000196463 49115750000000000000 (BSN.log_rat_reduce_isNear 20 1 4 40 32 116991 524288 24973259072661432 36028797018963968 196463 1000000000000000 rfl rfl rfl rfl (ep347 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1064 := nat_lit 11549433305940213837168733670100625

noncomputable def ep1065 := BSN.cos_dyadic_bound_f 327823565 2147483648 2 1 1048576 393310 ep1064 ep61 ep1064 ep1064 ep62 ep1064 1036381 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 327823565) qz15 0 1 ep1064 ep61 ep1064 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 327823565) qz16 0 1 ep1064 ep62 ep1064 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz466 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 434994293) qz30)

noncomputable def ep1066 := @Enclosure.Real.IsNear.cos_image qz168 qz466 Bool.false 434994293 1048576 185 262144 Bool.false 1036381 1048576 1 196463 (@Enclosure.Real.IsNear.recentre' qz168 Bool.false 233535782985470900433 562949953421312000 17309750013602901657 24557875000000000000000 434994293 1048576 185 262144 (ep1063 rfl) rfl) (Enclosure.sfrac_false_div 434994293 1048576) (BSN.cos_reduce0 qz466 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 23068532619371270373376) qz31) 226375608064910080 72057594037927936 Bool.false 1036381 1048576 66 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q0 434994293 1048576 226375608064910080 72057594037927936 66 23068532619371270373376 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1036381 1048576 23068532619371270373376 151115727451828646838272 327823565 2147483648 393310 392926 (ep1065 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1067 := BSN.sin_dyadic_bound_f 327823565 2147483648 2 1 1048576 393310 ep1064 ep65 ep1064 ep1064 ep66 ep1064 159449 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 327823565) qz19 0 1 ep1064 ep65 ep1064 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 327823565) qz20 0 1 ep1064 ep66 ep1064 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1068 := @Enclosure.Real.IsNear.sin_image qz168 qz466 Bool.false 434994293 1048576 185 262144 Bool.false 159449 1048576 1 196463 (@Enclosure.Real.IsNear.recentre' qz168 Bool.false 233535782985470900433 562949953421312000 17309750013602901657 24557875000000000000000 434994293 1048576 185 262144 (ep1063 rfl) rfl) (Enclosure.sfrac_false_div 434994293 1048576) (BSN.sin_reduce0 qz466 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 23068532619371270373376) qz31) 226375608064910080 72057594037927936 Bool.false 159449 1048576 66 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q0 434994293 1048576 226375608064910080 72057594037927936 66 23068532619371270373376 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 159449 1048576 23068532619371270373376 151115727451828646838272 327823565 2147483648 393310 392926 (ep1067 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1069 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz55 (Real.cos qz168)) (@HMul.hMul Real Real Real qz0 qz55 (@Neg.neg Real Real.instNeg (Real.sin qz168))) Bool.false 242999216689 1099511627776 34537333046523 216013352927756288 Bool.true 37385847581 1099511627776 34365048355007 216013352927756288 (@Enclosure.Real.IsNear.mulLit_ff qz55 (Real.cos qz168) 234469 1048576 1 1048576 1036381 1048576 36607799 51501596672 242999216689 1099511627776 34537333046523 216013352927756288 qz348 (@Enclosure.Real.IsNear.recentre' (Real.cos qz168) Bool.false 1036381 1048576 36607799 51501596672 1036381 1048576 36607799 51501596672 (ep1066 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz55 (@Neg.neg Real Real.instNeg (Real.sin qz168)) 234469 1048576 1 1048576 159449 1048576 36607799 51501596672 37385847581 1099511627776 34365048355007 216013352927756288 qz348 (@Enclosure.Real.IsNear.neg (Real.sin qz168) Bool.false 159449 1048576 36607799 51501596672 (@Enclosure.Real.IsNear.recentre' (Real.sin qz168) Bool.false 159449 1048576 36607799 51501596672 159449 1048576 36607799 51501596672 (ep1068 rfl rfl) rfl)) rfl)

noncomputable def ep1070 := @ep1016 242999216689 1099511627776 34537333046523 216013352927756288 Bool.true 37385847581 1099511627776 34365048355007 216013352927756288 Bool.false 35346439783083176624128 128589598837 1099511627776 1015270614727507 216013352927756288 Bool.false 123924632274152361820160 225417592945 1099511627776 1015299549798147 216013352927756288 (ep1017 (BSN.head_sum_c_succ qz143 19 20 rfl rfl) (ep1061 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1062 ep1069) rfl rfl

noncomputable abbrev qz169 := (@HMul.hMul Real Real Real qz267 qz446 qz605)

noncomputable def ep1071 := @Enclosure.Complex.IsNear.of_eq qz685 (Complex.mk (@HMul.hMul Real Real Real qz0 qz57 (Real.cos qz169)) (@HMul.hMul Real Real Real qz0 qz57 (@Neg.neg Real Real.instNeg (Real.sin qz169)))) Bool.false 24307908185 137438953472 4230039794885 27001669115969536 Bool.true 70270579845 549755813888 16873861691275 108006676463878144 (BSN.cpow_neg_s_mk qz146 138478 1000 21 qz147 rfl)

noncomputable def ep1072 := @Enclosure.Real.IsNear.mulLit_ff qz146 qz605 138478 1000 0 1 3427826275261687 1125899906842624 250000000196463 49115750000000000000 237339263472843946193 562949953421312000 17309750013602901657 24557875000000000000000 qz148 (BSN.isNear_log_sfrac 21 1 3427826275261687 1125899906842624 250000000196463 49115750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz606) Bool.false 57509381830540779323392 18889465931478580854784 1000000000785852 196463000000000000000 3427826275261687 1125899906842624 250000000196463 49115750000000000000 (BSN.log_rat_reduce_isNear 21 1 4 42 32 142571 524288 24973259072661432 36028797018963968 196463 1000000000000000 rfl rfl rfl rfl (ep358 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1073 := nat_lit 3261990350498980077374697764834924401

noncomputable def ep1074 := BSN.cos_dyadic_bound_f 1343911493 2147483648 2 1 1048576 393310 ep1073 ep61 ep1073 ep1073 ep62 ep1073 849860 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1343911493) qz15 0 1 ep1073 ep61 ep1073 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1343911493) qz16 0 1 ep1073 ep62 ep1073 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz467 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 442078827) qz30)

noncomputable def ep1075 := @Enclosure.Real.IsNear.cos_image qz169 qz467 Bool.false 442078827 1048576 185 262144 Bool.false 849860 1048576 1 196463 (@Enclosure.Real.IsNear.recentre' qz169 Bool.false 237339263472843946193 562949953421312000 17309750013602901657 24557875000000000000000 442078827 1048576 185 262144 (ep1072 rfl) rfl) (Enclosure.sfrac_false_div 442078827 1048576) (BSN.cos_reduce0 qz467 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 94569364050082166472704) qz31) 226375608064910080 72057594037927936 Bool.false 849860 1048576 67 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q0 442078827 1048576 226375608064910080 72057594037927936 67 94569364050082166472704 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 849860 1048576 94569364050082166472704 151115727451828646838272 1343911493 2147483648 393310 392926 (ep1074 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1076 := BSN.sin_dyadic_bound_f 1343911493 2147483648 2 1 1048576 393310 ep1073 ep65 ep1073 ep1073 ep66 ep1073 614205 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1343911493) qz19 0 1 ep1073 ep65 ep1073 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1343911493) qz20 0 1 ep1073 ep66 ep1073 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1077 := @Enclosure.Real.IsNear.sin_image qz169 qz467 Bool.false 442078827 1048576 185 262144 Bool.false 614205 1048576 1 196463 (@Enclosure.Real.IsNear.recentre' qz169 Bool.false 237339263472843946193 562949953421312000 17309750013602901657 24557875000000000000000 442078827 1048576 185 262144 (ep1072 rfl) rfl) (Enclosure.sfrac_false_div 442078827 1048576) (BSN.sin_reduce0 qz467 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 94569364050082166472704) qz31) 226375608064910080 72057594037927936 Bool.false 614205 1048576 67 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q0 442078827 1048576 226375608064910080 72057594037927936 67 94569364050082166472704 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 614205 1048576 94569364050082166472704 151115727451828646838272 1343911493 2147483648 393310 392926 (ep1076 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1078 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz57 (Real.cos qz169)) (@HMul.hMul Real Real Real qz0 qz57 (@Neg.neg Real Real.instNeg (Real.sin qz169))) Bool.false 24307908185 137438953472 4230039794885 27001669115969536 Bool.true 70270579845 549755813888 16873861691275 108006676463878144 (@Enclosure.Real.IsNear.mulLit_ff qz57 (Real.cos qz169) 114409 524288 1 524288 212465 262144 36607799 51501596672 24307908185 137438953472 4230039794885 27001669115969536 qz350 (@Enclosure.Real.IsNear.recentre' (Real.cos qz169) Bool.false 849860 1048576 36607799 51501596672 212465 262144 36607799 51501596672 (ep1075 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz57 (@Neg.neg Real Real.instNeg (Real.sin qz169)) 114409 524288 1 524288 614205 1048576 36607799 51501596672 70270579845 549755813888 16873861691275 108006676463878144 qz350 (@Enclosure.Real.IsNear.neg (Real.sin qz169) Bool.false 614205 1048576 36607799 51501596672 (@Enclosure.Real.IsNear.recentre' (Real.sin qz169) Bool.false 614205 1048576 36607799 51501596672 614205 1048576 36607799 51501596672 (ep1077 rfl rfl) rfl)) rfl)

noncomputable def ep1079 := @ep1014 24307908185 137438953472 4230039794885 27001669115969536 Bool.true 70270579845 549755813888 16873861691275 108006676463878144 Bool.false 44400047587860492058624 323052864317 1099511627776 1049110933086587 216013352927756288 Bool.false 46661312644013034045440 84876433255 1099511627776 1049047273180697 216013352927756288 (ep1015 (BSN.head_sum_c_succ qz143 20 21 rfl rfl) (ep1070 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1071 ep1078) rfl rfl

noncomputable abbrev qz170 := (@HMul.hMul Real Real Real qz267 qz446 qz608)

noncomputable def ep1080 := @Enclosure.Complex.IsNear.of_eq qz684 (Complex.mk (@HMul.hMul Real Real Real qz0 qz59 (Real.cos qz170)) (@HMul.hMul Real Real Real qz0 qz59 (@Neg.neg Real Real.instNeg (Real.sin qz170)))) Bool.false 20735135307 137438953472 2055102652067 13500834557984768 Bool.true 41408345325 274877906944 8220356188017 54003338231939072 (BSN.cpow_neg_s_mk qz146 138478 1000 22 qz147 rfl)

noncomputable def ep1081 := @Enclosure.Real.IsNear.mulLit_ff qz146 qz608 138478 1000 0 1 3480203401436407 1125899906842624 250000000196463 49115750000000000000 240965803312055384273 562949953421312000 17309750013602901657 24557875000000000000000 qz148 (BSN.isNear_log_sfrac 22 1 3480203401436407 1125899906842624 250000000196463 49115750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz609) Bool.false 58388124189833310502912 18889465931478580854784 1000000000785852 196463000000000000000 3480203401436407 1125899906842624 250000000196463 49115750000000000000 (BSN.log_rat_reduce_isNear 22 1 4 44 32 166961 524288 24973259072661432 36028797018963968 196463 1000000000000000 rfl rfl rfl rfl (ep372 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1082 := nat_lit 288106372391829241142742908721666753249780587966506845248633312786414221459456

noncomputable def ep1083 := nat_lit 64990859780937893179396965519938774024145138181796994471927357951222808576

noncomputable def ep1084 := nat_lit 864189135455925847641869932233960382201293473623156941756956083643340218761216

noncomputable def ep1085 := BSN.cos_dyadic_bound_f 1685025724 2147483648 3 2 1048576 393310 ep1082 ep78 ep1083 ep1084 ep81 ep1083 742008 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1685025724) qz15 0 2 ep1082 ep78 ep1083 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1685025724) qz16 0 2 ep1084 ep81 ep1083 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz468 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 56104223) qz634)

noncomputable def ep1086 := @Enclosure.Real.IsNear.cos_image qz170 qz468 Bool.false 56104223 131072 185 262144 Bool.false 742008 1048576 1 196463 (@Enclosure.Real.IsNear.recentre' qz170 Bool.false 240965803312055384273 562949953421312000 17309750013602901657 24557875000000000000000 56104223 131072 185 262144 (ep1081 rfl) rfl) (Enclosure.sfrac_false_div 56104223 131072) (BSN.cos_reduce0 qz468 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 14821643017539588980736) qz370) 226375608064910080 72057594037927936 Bool.false 742008 1048576 68 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q0 56104223 131072 226375608064910080 72057594037927936 68 14821643017539588980736 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 742008 1048576 14821643017539588980736 18889465931478580854784 1685025724 2147483648 393310 392926 (ep1085 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1087 := nat_lit 8061690876046903671638299962862878976

noncomputable def ep1088 := BSN.sin_dyadic_bound_f 1685025724 2147483648 2 1 1048576 393310 ep1087 ep65 ep1087 ep1087 ep66 ep1087 740900 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1685025724) qz19 0 1 ep1087 ep65 ep1087 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1685025724) qz20 0 1 ep1087 ep66 ep1087 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1089 := @Enclosure.Real.IsNear.sin_image qz170 qz468 Bool.false 56104223 131072 185 262144 Bool.false 740900 1048576 1 196463 (@Enclosure.Real.IsNear.recentre' qz170 Bool.false 240965803312055384273 562949953421312000 17309750013602901657 24557875000000000000000 56104223 131072 185 262144 (ep1081 rfl) rfl) (Enclosure.sfrac_false_div 56104223 131072) (BSN.sin_reduce0 qz468 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 14821643017539588980736) qz370) 226375608064910080 72057594037927936 Bool.false 740900 1048576 68 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q0 56104223 131072 226375608064910080 72057594037927936 68 14821643017539588980736 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 740900 1048576 14821643017539588980736 18889465931478580854784 1685025724 2147483648 393310 392926 (ep1088 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1090 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz59 (Real.cos qz170)) (@HMul.hMul Real Real Real qz0 qz59 (@Neg.neg Real Real.instNeg (Real.sin qz170))) Bool.false 20735135307 137438953472 2055102652067 13500834557984768 Bool.true 41408345325 274877906944 8220356188017 54003338231939072 (@Enclosure.Real.IsNear.mulLit_ff qz59 (Real.cos qz170) 223557 1048576 1 1048576 92751 131072 36607799 51501596672 20735135307 137438953472 2055102652067 13500834557984768 qz352 (@Enclosure.Real.IsNear.recentre' (Real.cos qz170) Bool.false 742008 1048576 36607799 51501596672 92751 131072 36607799 51501596672 (ep1086 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz59 (@Neg.neg Real Real.instNeg (Real.sin qz170)) 223557 1048576 1 1048576 185225 262144 36607799 51501596672 41408345325 274877906944 8220356188017 54003338231939072 qz352 (@Enclosure.Real.IsNear.neg (Real.sin qz170) Bool.false 185225 262144 36607799 51501596672 (@Enclosure.Real.IsNear.recentre' (Real.sin qz170) Bool.false 740900 1048576 36607799 51501596672 185225 262144 36607799 51501596672 (ep1089 rfl rfl) rfl)) rfl)

noncomputable def ep1091 := @ep1012 20735135307 137438953472 2055102652067 13500834557984768 Bool.true 41408345325 274877906944 8220356188017 54003338231939072 Bool.false 67198569961415671545856 488933946773 1099511627776 1081992575519659 216013352927756288 Bool.true 22198300849794952724480 80756948045 1099511627776 1081928697932765 216013352927756288 (ep1013 (BSN.head_sum_c_succ qz143 21 22 rfl rfl) (ep1079 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1080 ep1090) rfl rfl

noncomputable abbrev qz171 := (@HMul.hMul Real Real Real qz267 qz446 qz611)

noncomputable def ep1092 := @Enclosure.Complex.IsNear.of_eq qz683 (Complex.mk (@HMul.hMul Real Real Real qz0 qz61 (Real.cos qz171)) (@HMul.hMul Real Real Real qz0 qz61 (@Neg.neg Real Real.instNeg (Real.sin qz171)))) Bool.false 181548684549 1099511627776 32179434095033 216013352927756288 Bool.true 17500841649 137438953472 4017763290187 27001669115969536 (BSN.cpow_neg_s_mk qz146 138478 1000 23 qz147 rfl)

noncomputable def ep1093 := @Enclosure.Real.IsNear.mulLit_ff qz146 qz611 138478 1000 0 1 3530250507853047 1125899906842624 250000000196463 49115750000000000000 244431014913237121233 562949953421312000 17309750013602901657 24557875000000000000000 qz148 (BSN.isNear_log_sfrac 23 1 3530250507853047 1125899906842624 250000000196463 49115750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz612) Bool.false 59227775304360265777152 18889465931478580854784 1000000000785852 196463000000000000000 3530250507853047 1125899906842624 250000000196463 49115750000000000000 (BSN.log_rat_reduce_isNear 23 1 4 46 32 190266 524288 24973259072661432 36028797018963968 196463 1000000000000000 rfl rfl rfl rfl (ep386 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1094 := nat_lit 141528127787456317213331400349179111568439618323197218972695242326309362114081

noncomputable def ep1095 := nat_lit 15686705998747645254568744689669867807267079535858320371822547739493703201

noncomputable def ep1096 := nat_lit 424553009950371456349485063558157994969704320810519940277342081883449098935841

noncomputable def ep1097 := BSN.cos_dyadic_bound_f 1410722099 2147483648 3 2 1048576 393310 ep1094 ep78 ep1095 ep1096 ep81 ep1095 830343 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1410722099) qz15 0 2 ep1094 ep78 ep1095 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1410722099) qz16 0 2 ep1096 ep81 ep1095 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz469 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 113822061) qz17)

noncomputable def ep1098 := @Enclosure.Real.IsNear.cos_image qz171 qz469 Bool.false 113822061 262144 185 262144 Bool.false 830343 1048576 1 196463 (@Enclosure.Real.IsNear.recentre' qz171 Bool.false 244431014913237121233 562949953421312000 17309750013602901657 24557875000000000000000 113822061 262144 185 262144 (ep1093 rfl) rfl) (Enclosure.sfrac_false_div 113822061 262144) (BSN.cos_reduce0 qz469 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 24817685639830198812672) qz285) 226375608064910080 72057594037927936 Bool.false 830343 1048576 69 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q0 113822061 262144 226375608064910080 72057594037927936 69 24817685639830198812672 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 830343 1048576 24817685639830198812672 37778931862957161709568 1410722099 2147483648 393310 392926 (ep1097 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1099 := nat_lit 3960644644341075602748825163583571601

noncomputable def ep1100 := BSN.sin_dyadic_bound_f 1410722099 2147483648 2 1 1048576 393310 ep1099 ep65 ep1099 ep1099 ep66 ep1099 640344 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1410722099) qz19 0 1 ep1099 ep65 ep1099 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1410722099) qz20 0 1 ep1099 ep66 ep1099 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1101 := @Enclosure.Real.IsNear.sin_image qz171 qz469 Bool.false 113822061 262144 185 262144 Bool.false 640344 1048576 1 196463 (@Enclosure.Real.IsNear.recentre' qz171 Bool.false 244431014913237121233 562949953421312000 17309750013602901657 24557875000000000000000 113822061 262144 185 262144 (ep1093 rfl) rfl) (Enclosure.sfrac_false_div 113822061 262144) (BSN.sin_reduce0 qz469 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 24817685639830198812672) qz285) 226375608064910080 72057594037927936 Bool.false 640344 1048576 69 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q0 113822061 262144 226375608064910080 72057594037927936 69 24817685639830198812672 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 640344 1048576 24817685639830198812672 37778931862957161709568 1410722099 2147483648 393310 392926 (ep1100 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1102 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz61 (Real.cos qz171)) (@HMul.hMul Real Real Real qz0 qz61 (@Neg.neg Real Real.instNeg (Real.sin qz171))) Bool.false 181548684549 1099511627776 32179434095033 216013352927756288 Bool.true 17500841649 137438953472 4017763290187 27001669115969536 (@Enclosure.Real.IsNear.mulLit_ff qz61 (Real.cos qz171) 218643 1048576 1 1048576 830343 1048576 36607799 51501596672 181548684549 1099511627776 32179434095033 216013352927756288 qz354 (@Enclosure.Real.IsNear.recentre' (Real.cos qz171) Bool.false 830343 1048576 36607799 51501596672 830343 1048576 36607799 51501596672 (ep1098 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz61 (@Neg.neg Real Real.instNeg (Real.sin qz171)) 218643 1048576 1 1048576 80043 131072 36607799 51501596672 17500841649 137438953472 4017763290187 27001669115969536 qz354 (@Enclosure.Real.IsNear.neg (Real.sin qz171) Bool.false 80043 131072 36607799 51501596672 (@Enclosure.Real.IsNear.recentre' (Real.sin qz171) Bool.false 640344 1048576 36607799 51501596672 80043 131072 36607799 51501596672 (ep1101 rfl rfl) rfl)) rfl)

noncomputable def ep1103 := @ep1010 181548684549 1099511627776 32179434095033 216013352927756288 Bool.true 17500841649 137438953472 4017763290187 27001669115969536 Bool.false 737203449360387902799872 335241315661 549755813888 278543002403673 54003338231939072 Bool.true 30341529313839482404864 220763681237 1099511627776 1114070804254261 216013352927756288 (ep1011 (BSN.head_sum_c_succ qz143 22 23 rfl rfl) (ep1091 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1092 ep1102) rfl rfl

noncomputable abbrev qz172 := (@HMul.hMul Real Real Real qz267 qz446 qz614)

noncomputable def ep1104 := @Enclosure.Complex.IsNear.of_eq qz682 (Complex.mk (@HMul.hMul Real Real Real qz0 qz63 (Real.cos qz172)) (@HMul.hMul Real Real Real qz0 qz63 (@Neg.neg Real Real.instNeg (Real.sin qz172)))) Bool.false 54114410175 274877906944 7885204055935 54003338231939072 Bool.true 7413668843 137438953472 3924571537911 27001669115969536 (BSN.cpow_neg_s_mk qz146 138478 1000 24 qz147 rfl)

noncomputable def ep1105 := @Enclosure.Real.IsNear.mulLit_ff qz146 qz614 138478 1000 0 1 3578169457974519 1125899906842624 250000000196463 49115750000000000000 247748875100697721041 562949953421312000 17309750013602901657 24557875000000000000000 qz148 (BSN.isNear_log_sfrac 24 1 3578169457974519 1125899906842624 250000000196463 49115750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz615) Bool.false 60031721881041427759104 18889465931478580854784 1000000000785852 196463000000000000000 3578169457974519 1125899906842624 250000000196463 49115750000000000000 (BSN.log_rat_reduce_isNear 24 1 4 48 32 212580 524288 24973259072661432 36028797018963968 196463 1000000000000000 rfl rfl rfl rfl (ep397 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1106 := nat_lit 108793832567181640083621215413909681

noncomputable def ep1107 := BSN.cos_dyadic_bound_f 574316203 2147483648 2 1 1048576 393310 ep1106 ep61 ep1106 ep1106 ep62 ep1106 1011300 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 574316203) qz15 0 1 ep1106 ep61 ep1106 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 574316203) qz16 0 1 ep1106 ep62 ep1106 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz470 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 28841765) (@Nat.cast Real Real.instNatCast 65536))

noncomputable def ep1108 := @Enclosure.Real.IsNear.cos_image qz172 qz470 Bool.false 28841765 65536 185 262144 Bool.false 1011300 1048576 1 196463 (@Enclosure.Real.IsNear.recentre' qz172 Bool.false 247748875100697721041 562949953421312000 17309750013602901657 24557875000000000000000 28841765 65536 185 262144 (ep1105 rfl) rfl) (Enclosure.sfrac_false_div 28841765 65536) (BSN.cos_reduce0 qz470 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 2525869374892073287680) qz603) 226375608064910080 72057594037927936 Bool.false 1011300 1048576 70 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q0 28841765 65536 226375608064910080 72057594037927936 70 2525869374892073287680 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1011300 1048576 2525869374892073287680 9444732965739290427392 574316203 2147483648 393310 392926 (ep1107 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1109 := BSN.sin_dyadic_bound_f 574316203 2147483648 2 1 1048576 393310 ep1106 ep65 ep1106 ep1106 ep66 ep1106 277096 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 574316203) qz19 0 1 ep1106 ep65 ep1106 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 574316203) qz20 0 1 ep1106 ep66 ep1106 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1110 := @Enclosure.Real.IsNear.sin_image qz172 qz470 Bool.false 28841765 65536 185 262144 Bool.false 277096 1048576 1 196463 (@Enclosure.Real.IsNear.recentre' qz172 Bool.false 247748875100697721041 562949953421312000 17309750013602901657 24557875000000000000000 28841765 65536 185 262144 (ep1105 rfl) rfl) (Enclosure.sfrac_false_div 28841765 65536) (BSN.sin_reduce0 qz470 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 2525869374892073287680) qz603) 226375608064910080 72057594037927936 Bool.false 277096 1048576 70 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q0 28841765 65536 226375608064910080 72057594037927936 70 2525869374892073287680 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 277096 1048576 2525869374892073287680 9444732965739290427392 574316203 2147483648 393310 392926 (ep1109 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1111 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz63 (Real.cos qz172)) (@HMul.hMul Real Real Real qz0 qz63 (@Neg.neg Real Real.instNeg (Real.sin qz172))) Bool.false 54114410175 274877906944 7885204055935 54003338231939072 Bool.true 7413668843 137438953472 3924571537911 27001669115969536 (@Enclosure.Real.IsNear.mulLit_ff qz63 (Real.cos qz172) 214039 1048576 1 1048576 252825 262144 36607799 51501596672 54114410175 274877906944 7885204055935 54003338231939072 qz356 (@Enclosure.Real.IsNear.recentre' (Real.cos qz172) Bool.false 1011300 1048576 36607799 51501596672 252825 262144 36607799 51501596672 (ep1108 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz63 (@Neg.neg Real Real.instNeg (Real.sin qz172)) 214039 1048576 1 1048576 34637 131072 36607799 51501596672 7413668843 137438953472 3924571537911 27001669115969536 qz356 (@Enclosure.Real.IsNear.neg (Real.sin qz172) Bool.false 34637 131072 36607799 51501596672 (@Enclosure.Real.IsNear.recentre' (Real.sin qz172) Bool.false 277096 1048576 36607799 51501596672 34637 131072 36607799 51501596672 (ep1110 rfl rfl) rfl)) rfl)

noncomputable def ep1112 := @ep1008 54114410175 274877906944 7885204055935 54003338231939072 Bool.true 7413668843 137438953472 3924571537911 27001669115969536 Bool.false 121900142778874681360384 443470136011 549755813888 35803525807451 6750417278992384 Bool.true 38492944411198626988032 280073031981 1099511627776 1145467376557549 216013352927756288 (ep1009 (BSN.head_sum_c_succ qz143 23 24 rfl rfl) (ep1103 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1104 ep1111) rfl rfl

theorem EMRow47.d15 : Enclosure.Complex.IsNear qz164 Bool.false 443470136011 549755813888 35803525807451 6750417278992384 Bool.true 280073031981 1099511627776 1145467376557549 216013352927756288 := ep1007 (BSN.head_sum_c_succ qz143 24 25 rfl rfl) (ep1112 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable abbrev qz173 := (BSN.headSumC qz444 33)

noncomputable abbrev qz691 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 32) qz144)

noncomputable def ep1113 := @Enclosure.Complex.IsNear.of_eq qz173 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz143 32) qz691) Bool.false 106826879495 137438953472 688740301255883 108006676463878144 Bool.true 14291011597 1099511627776 1377240046731287 216013352927756288

noncomputable def ep1114 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz143 32) qz691 Bool.false 998737178179 1099511627776 1350184777759903 216013352927756288 Bool.false 116121127053 1099511627776 1349958752972293 216013352927756288 Bool.true

noncomputable abbrev qz692 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 31) qz144)

noncomputable def ep1115 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz143 32) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz143 31) qz692) Bool.false 998737178179 1099511627776 1350184777759903 216013352927756288 Bool.false 116121127053 1099511627776 1349958752972293 216013352927756288

noncomputable def ep1116 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz143 31) qz692 Bool.false 1079203380035 1099511627776 1322523449049991 216013352927756288 Bool.true 64218580109 1099511627776 1322193237182999 216013352927756288 Bool.true

noncomputable abbrev qz693 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 30) qz144)

noncomputable def ep1117 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz143 31) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz143 30) qz693) Bool.false 1079203380035 1099511627776 1322523449049991 216013352927756288 Bool.true 64218580109 1099511627776 1322193237182999 216013352927756288

noncomputable def ep1118 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz143 30) qz693 Bool.false 110576225323 137438953472 80893148685711 13500834557984768 Bool.true 3547569875 34359738368 161763658350543 27001669115969536 Bool.false

noncomputable abbrev qz694 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 29) qz144)

noncomputable def ep1119 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz143 30) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz143 29) qz694) Bool.false 110576225323 137438953472 80893148685711 13500834557984768 Bool.true 3547569875 34359738368 161763658350543 27001669115969536

noncomputable def ep1120 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz143 29) qz694 Bool.false 837997562879 1099511627776 1265730851522859 216013352927756288 Bool.false 21314798015 274877906944 316349051027679 54003338231939072 Bool.false

noncomputable abbrev qz695 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 28) qz144)

noncomputable def ep1121 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz143 29) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz143 28) qz695) Bool.false 837997562879 1099511627776 1265730851522859 216013352927756288 Bool.false 21314798015 274877906944 316349051027679 54003338231939072

noncomputable def ep1122 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz143 28) qz695 Bool.false 16112016173 17179869184 618260972852611 108006676463878144 Bool.false 161816098339 1099511627776 1236302912446393 216013352927756288 Bool.true

noncomputable abbrev qz696 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 27) qz144)

noncomputable def ep1123 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz143 28) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz143 27) qz696) Bool.false 16112016173 17179869184 618260972852611 108006676463878144 Bool.false 161816098339 1099511627776 1236302912446393 216013352927756288

noncomputable def ep1124 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz143 27) qz696 Bool.false 291913039085 274877906944 603419628069353 108006676463878144 Bool.false 114156041 1099511627776 1206595670898767 216013352927756288 Bool.true

noncomputable abbrev qz697 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 26) qz144)

noncomputable def ep1125 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz143 27) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz143 26) qz697) Bool.false 291913039085 274877906944 603419628069353 108006676463878144 Bool.false 114156041 1099511627776 1206595670898767 216013352927756288

noncomputable def ep1126 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz143 26) qz697 Bool.false 1092518224217 1099511627776 1176614377913167 216013352927756288 Bool.true 202004945511 1099511627776 1176249476181339 216013352927756288 Bool.false

noncomputable def ep1127 := nat_lit 1283847123093549838499840

noncomputable abbrev qz698 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 25) qz144)

noncomputable def ep1128 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz143 26) (@HAdd.hAdd Complex Complex Complex qz4 qz164 qz698) Bool.false 1092518224217 1099511627776 1176614377913167 216013352927756288 Bool.true 202004945511 1099511627776 1176249476181339 216013352927756288

noncomputable def ep1129 := @Enclosure.Complex.IsNear.addLitP qz164 qz698 Bool.false 443470136011 549755813888 35803525807451 6750417278992384 Bool.true 280073031981 1099511627776 1145467376557549 216013352927756288 Bool.false

noncomputable abbrev qz174 := (@HMul.hMul Real Real Real qz267 qz446 qz625)

noncomputable def ep1130 := @Enclosure.Complex.IsNear.of_eq qz698 (Complex.mk (@HMul.hMul Real Real Real qz0 qz66 (Real.cos qz174)) (@HMul.hMul Real Real Real qz0 qz66 (@Neg.neg Real Real.instNeg (Real.sin qz174)))) Bool.false 205577952195 1099511627776 30901552074735 216013352927756288 Bool.false 39034043235 549755813888 15391049811895 108006676463878144 (BSN.cpow_neg_s_mk qz146 138478 1000 25 qz147 rfl)

noncomputable def ep1131 := @Enclosure.Real.IsNear.mulLit_ff qz146 qz625 138478 1000 0 1 3624129903009015 1125899906842624 250000000196463 49115750000000000000 50186226070888237917 112589990684262400 17309750013602901657 24557875000000000000000 qz148 (BSN.isNear_log_sfrac 25 1 3624129903009015 1125899906842624 250000000196463 49115750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz626) Bool.false 60802810194841294602240 18889465931478580854784 1000000000785852 196463000000000000000 3624129903009015 1125899906842624 250000000196463 49115750000000000000 (BSN.log_rat_reduce_isNear 25 1 4 50 32 233982 524288 24973259072661432 36028797018963968 196463 1000000000000000 rfl rfl rfl rfl (ep429 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1132 := nat_lit 2913431517040315854295641807853674580291599231618502894473903490164369047253985

noncomputable def ep1133 := nat_lit 2049254819247405061725790377915724886888481373836641914392977356851603141601

noncomputable def ep1134 := nat_lit 7627098036826807629245791550433474631899226160586057779570253844233683004388321

noncomputable def ep1135 := BSN.sin_dyadic_bound_f 2593877701 2147483648 3 2 1048576 393310 ep1132 ep109 ep1133 ep1134 ep112 ep1133 980273 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2593877701) qz19 0 2 ep1132 ep109 ep1133 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2593877701) qz20 0 2 ep1134 ep112 ep1133 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz471 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 116848913) qz17)

noncomputable def ep1136 := @Enclosure.Real.IsNear.cos_image qz174 qz471 Bool.false 116848913 262144 185 262144 Bool.false 980273 1048576 1 196463 (@Enclosure.Real.IsNear.recentre' qz174 Bool.false 50186226070888237917 112589990684262400 17309750013602901657 24557875000000000000000 116848913 262144 185 262144 (ep1131 rfl) rfl) (Enclosure.sfrac_false_div 116848913 262144) (BSN.cos_reduce3 qz471 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 45631979093636180606976) qz285) 226375608064910080 72057594037927936 Bool.false 980273 1048576 70 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q3 116848913 262144 226375608064910080 72057594037927936 70 45631979093636180606976 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 980273 1048576 45631979093636180606976 37778931862957161709568 2593877701 2147483648 393310 392926 (ep1135 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1137 := nat_lit 1619483844942063210191679133420003977889505564843095671114121040027694627648481

noncomputable def ep1138 := nat_lit 4854353025187694820451585819504180483894739731781613729513577165369380676662241

noncomputable def ep1139 := BSN.cos_dyadic_bound_f 2593877701 2147483648 3 2 1048576 393310 ep1137 ep78 ep1133 ep1138 ep81 ep1133 372258 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2593877701) qz15 0 2 ep1137 ep78 ep1133 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2593877701) qz16 0 2 ep1138 ep81 ep1133 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1140 := @Enclosure.Real.IsNear.sin_image qz174 qz471 Bool.false 116848913 262144 185 262144 Bool.true 372258 1048576 1 196463 (@Enclosure.Real.IsNear.recentre' qz174 Bool.false 50186226070888237917 112589990684262400 17309750013602901657 24557875000000000000000 116848913 262144 185 262144 (ep1131 rfl) rfl) (Enclosure.sfrac_false_div 116848913 262144) (BSN.sin_reduce3 qz471 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 45631979093636180606976) qz285) 226375608064910080 72057594037927936 Bool.false 372258 1048576 70 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q3 116848913 262144 226375608064910080 72057594037927936 70 45631979093636180606976 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 372258 1048576 45631979093636180606976 37778931862957161709568 2593877701 2147483648 393310 392926 (ep1139 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1141 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz66 (Real.cos qz174)) (@HMul.hMul Real Real Real qz0 qz66 (@Neg.neg Real Real.instNeg (Real.sin qz174))) Bool.false 205577952195 1099511627776 30901552074735 216013352927756288 Bool.false 39034043235 549755813888 15391049811895 108006676463878144 (@Enclosure.Real.IsNear.mulLit_ff qz66 (Real.cos qz174) 209715 1048576 1 1048576 980273 1048576 36607799 51501596672 205577952195 1099511627776 30901552074735 216013352927756288 qz358 (@Enclosure.Real.IsNear.recentre' (Real.cos qz174) Bool.false 980273 1048576 36607799 51501596672 980273 1048576 36607799 51501596672 (ep1136 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz66 (@Neg.neg Real Real.instNeg (Real.sin qz174)) 209715 1048576 1 1048576 186129 524288 36607799 51501596672 39034043235 549755813888 15391049811895 108006676463878144 qz358 (@Enclosure.Real.IsNear.neg (Real.sin qz174) Bool.true 186129 524288 36607799 51501596672 (@Enclosure.Real.IsNear.recentre' (Real.sin qz174) Bool.true 372258 1048576 36607799 51501596672 186129 524288 36607799 51501596672 (ep1140 rfl rfl) rfl)) rfl)

noncomputable def ep1142 := @ep1129 205577952195 1099511627776 30901552074735 216013352927756288 Bool.false 39034043235 549755813888 15391049811895 108006676463878144 Bool.false 600618245541889306525696 1092518224217 1099511627776 1176614377913167 216013352927756288 Bool.true 111053393228800897056768 202004945511 1099511627776 1176249476181339 216013352927756288 EMRow47.d15 (ep1130 ep1141) rfl rfl

noncomputable abbrev qz175 := (@HMul.hMul Real Real Real qz267 qz446 qz628)

noncomputable def ep1143 := @Enclosure.Complex.IsNear.of_eq qz697 (Complex.mk (@HMul.hMul Real Real Real qz0 qz68 (Real.cos qz175)) (@HMul.hMul Real Real Real qz0 qz68 (@Neg.neg Real Real.instNeg (Real.sin qz175)))) Bool.false 75133932123 1099511627776 30224878225539 216013352927756288 Bool.false 12632443847 68719476736 7586548679357 54003338231939072 (BSN.cpow_neg_s_mk qz146 138478 1000 26 qz147 rfl)

noncomputable def ep1144 := @Enclosure.Real.IsNear.mulLit_ff qz146 qz628 138478 1000 0 1 3668288609262839 1125899906842624 250000000196463 49115750000000000000 253988635016749709521 562949953421312000 17309750013602901657 24557875000000000000000 qz148 (BSN.isNear_log_sfrac 26 1 3668288609262839 1125899906842624 250000000196463 49115750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz629) Bool.false 61543670347942250676224 18889465931478580854784 1000000000785852 196463000000000000000 3668288609262839 1125899906842624 250000000196463 49115750000000000000 (BSN.log_rat_reduce_isNear 26 1 4 52 32 254545 524288 24973259072661432 36028797018963968 196463 1000000000000000 rfl rfl rfl rfl (ep444 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1145 := nat_lit 341226117361191499380416738216755456

noncomputable def ep1146 := BSN.sin_dyadic_bound_f 764294204 2147483648 2 1 1048576 393310 ep1145 ep65 ep1145 ep1145 ep66 ep1145 365361 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 764294204) qz19 0 1 ep1145 ep65 ep1145 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 764294204) qz20 0 1 ep1145 ep66 ep1145 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz472 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 236545349) qz23)

noncomputable def ep1147 := @Enclosure.Real.IsNear.cos_image qz175 qz472 Bool.false 236545349 524288 741 1048576 Bool.false 365361 1048576 1 196463 (@Enclosure.Real.IsNear.recentre' qz175 Bool.false 253988635016749709521 562949953421312000 17309750013602901657 24557875000000000000000 236545349 524288 741 1048576 (ep1144 rfl) rfl) (Enclosure.sfrac_false_div 236545349 524288) (BSN.cos_reduce3 qz472 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 26891211678055397326848) qz24) 226375608064910080 72057594037927936 Bool.false 365361 1048576 71 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q3 236545349 524288 226375608064910080 72057594037927936 71 26891211678055397326848 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 365361 1048576 26891211678055397326848 75557863725914323419136 764294204 2147483648 393310 392926 (ep1146 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1148 := BSN.cos_dyadic_bound_f 764294204 2147483648 2 1 1048576 393310 ep1145 ep61 ep1145 ep1145 ep62 ep1145 982864 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 764294204) qz15 0 1 ep1145 ep61 ep1145 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 764294204) qz16 0 1 ep1145 ep62 ep1145 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1149 := @Enclosure.Real.IsNear.sin_image qz175 qz472 Bool.false 236545349 524288 741 1048576 Bool.true 982864 1048576 1 196463 (@Enclosure.Real.IsNear.recentre' qz175 Bool.false 253988635016749709521 562949953421312000 17309750013602901657 24557875000000000000000 236545349 524288 741 1048576 (ep1144 rfl) rfl) (Enclosure.sfrac_false_div 236545349 524288) (BSN.sin_reduce3 qz472 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 26891211678055397326848) qz24) 226375608064910080 72057594037927936 Bool.false 982864 1048576 71 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q3 236545349 524288 226375608064910080 72057594037927936 71 26891211678055397326848 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 982864 1048576 26891211678055397326848 75557863725914323419136 764294204 2147483648 393310 392926 (ep1148 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1150 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz68 (Real.cos qz175)) (@HMul.hMul Real Real Real qz0 qz68 (@Neg.neg Real Real.instNeg (Real.sin qz175))) Bool.false 75133932123 1099511627776 30224878225539 216013352927756288 Bool.false 12632443847 68719476736 7586548679357 54003338231939072 (@Enclosure.Real.IsNear.mulLit_ff qz68 (Real.cos qz175) 205643 1048576 1 1048576 365361 1048576 146627659 206006386688 75133932123 1099511627776 30224878225539 216013352927756288 qz360 (@Enclosure.Real.IsNear.recentre' (Real.cos qz175) Bool.false 365361 1048576 146627659 206006386688 365361 1048576 146627659 206006386688 (ep1147 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz68 (@Neg.neg Real Real.instNeg (Real.sin qz175)) 205643 1048576 1 1048576 61429 65536 146627659 206006386688 12632443847 68719476736 7586548679357 54003338231939072 qz360 (@Enclosure.Real.IsNear.neg (Real.sin qz175) Bool.true 61429 65536 146627659 206006386688 (@Enclosure.Real.IsNear.recentre' (Real.sin qz175) Bool.true 982864 1048576 146627659 206006386688 61429 65536 146627659 206006386688 (ep1149 rfl rfl) rfl)) rfl)

noncomputable def ep1151 := @ep1126 75133932123 1099511627776 30224878225539 216013352927756288 Bool.false 12632443847 68719476736 7586548679357 54003338231939072 Bool.false ep1127 291913039085 274877906944 603419628069353 108006676463878144 Bool.false 7844743403773362176 114156041 1099511627776 1206595670898767 216013352927756288 (ep1128 (BSN.head_sum_c_succ qz143 25 26 rfl rfl) (ep1142 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1143 ep1150) rfl rfl

noncomputable abbrev qz176 := (@HMul.hMul Real Real Real qz267 qz446 qz630)

noncomputable def ep1152 := @Enclosure.Complex.IsNear.of_eq qz696 (Complex.mk (@HMul.hMul Real Real Real qz0 qz361 (Real.cos qz176)) (@HMul.hMul Real Real Real qz0 qz361 (@Neg.neg Real Real.instNeg (Real.sin qz176)))) Bool.true 34120780317 274877906944 7420672391629 54003338231939072 Bool.false 80850971149 549755813888 14853620773813 108006676463878144 (BSN.cpow_neg_s_mk qz146 138478 1000 27 qz147 rfl)

noncomputable def ep1153 := @Enclosure.Real.IsNear.mulLit_ff qz146 qz630 138478 1000 0 1 3710780868205815 1125899906842624 250000000196463 49115750000000000000 51386151306740484957 112589990684262400 17309750013602901657 24557875000000000000000 qz148 (BSN.isNear_log_sfrac 27 1 3710780868205815 1125899906842624 250000000196463 49115750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz631) Bool.false 62256572154556490711040 18889465931478580854784 1000000000785852 196463000000000000000 3710780868205815 1125899906842624 250000000196463 49115750000000000000 (BSN.log_rat_reduce_isNear 27 1 4 54 32 274332 524288 24973259072661432 36028797018963968 196463 1000000000000000 rfl rfl rfl rfl (ep454 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1154 := nat_lit 435027646323698915559678553330028137868395457230221898893192990308350396621056

noncomputable def ep1155 := nat_lit 148142745975533645650522503750462085146386293027084123370715225020396626176

noncomputable def ep1156 := nat_lit 1304786653479145679387734614982583489434893599104611528432837540475010396610816

noncomputable def ep1157 := BSN.cos_dyadic_bound_f 1867820118 2147483648 3 2 1048576 393310 ep1154 ep78 ep1155 ep1156 ep81 ep1155 676332 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1867820118) qz15 0 2 ep1154 ep78 ep1155 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1867820118) qz16 0 2 ep1156 ep81 ep1155 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz473 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 478570827) qz30)

noncomputable def ep1158 := @Enclosure.Real.IsNear.cos_image qz176 qz473 Bool.false 478570827 1048576 185 262144 Bool.true 676332 1048576 1 196463 (@Enclosure.Real.IsNear.recentre' qz176 Bool.false 51386151306740484957 112589990684262400 17309750013602901657 24557875000000000000000 478570827 1048576 185 262144 (ep1153 rfl) rfl) (Enclosure.sfrac_false_div 478570827 1048576) (BSN.cos_reduce2 qz473 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 131436156064249302482944) qz31) 226375608064910080 72057594037927936 Bool.false 676332 1048576 72 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q2 478570827 1048576 226375608064910080 72057594037927936 72 131436156064249302482944 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 676332 1048576 131436156064249302482944 151115727451828646838272 1867820118 2147483648 393310 392926 (ep1157 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1159 := nat_lit 782931249185877621090900977991050278494994713979977750709050810375014396616960

noncomputable def ep1160 := nat_lit 2050294373898100048383211239256202362206177720711231210895390012046433253744896

noncomputable def ep1161 := BSN.sin_dyadic_bound_f 1867820118 2147483648 3 2 1048576 393310 ep1159 ep109 ep1155 ep1160 ep112 ep1155 801302 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1867820118) qz19 0 2 ep1159 ep109 ep1155 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1867820118) qz20 0 2 ep1160 ep112 ep1155 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1162 := @Enclosure.Real.IsNear.sin_image qz176 qz473 Bool.false 478570827 1048576 185 262144 Bool.true 801302 1048576 1 196463 (@Enclosure.Real.IsNear.recentre' qz176 Bool.false 51386151306740484957 112589990684262400 17309750013602901657 24557875000000000000000 478570827 1048576 185 262144 (ep1153 rfl) rfl) (Enclosure.sfrac_false_div 478570827 1048576) (BSN.sin_reduce2 qz473 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 131436156064249302482944) qz31) 226375608064910080 72057594037927936 Bool.false 801302 1048576 72 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q2 478570827 1048576 226375608064910080 72057594037927936 72 131436156064249302482944 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 801302 1048576 131436156064249302482944 151115727451828646838272 1867820118 2147483648 393310 392926 (ep1161 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1163 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz361 (Real.cos qz176)) (@HMul.hMul Real Real Real qz0 qz361 (@Neg.neg Real Real.instNeg (Real.sin qz176))) Bool.true 34120780317 274877906944 7420672391629 54003338231939072 Bool.false 80850971149 549755813888 14853620773813 108006676463878144 (@Enclosure.Real.IsNear.mulLit_ft qz361 (Real.cos qz176) 201799 1048576 1 1048576 169083 262144 36607799 51501596672 34120780317 274877906944 7420672391629 54003338231939072 qz365 (@Enclosure.Real.IsNear.recentre' (Real.cos qz176) Bool.true 676332 1048576 36607799 51501596672 169083 262144 36607799 51501596672 (ep1158 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz361 (@Neg.neg Real Real.instNeg (Real.sin qz176)) 201799 1048576 1 1048576 400651 524288 36607799 51501596672 80850971149 549755813888 14853620773813 108006676463878144 qz365 (@Enclosure.Real.IsNear.neg (Real.sin qz176) Bool.true 400651 524288 36607799 51501596672 (@Enclosure.Real.IsNear.recentre' (Real.sin qz176) Bool.true 801302 1048576 36607799 51501596672 400651 524288 36607799 51501596672 (ep1162 rfl rfl) rfl)) rfl)

noncomputable def ep1164 := @ep1124 34120780317 274877906944 7420672391629 54003338231939072 Bool.false 80850971149 549755813888 14853620773813 108006676463878144 Bool.false 70861396516513872084992 16112016173 17179869184 618260972852611 108006676463878144 Bool.false 88959340842537589932032 161816098339 1099511627776 1236302912446393 216013352927756288 (ep1125 (BSN.head_sum_c_succ qz143 26 27 rfl rfl) (ep1151 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1152 ep1163) rfl rfl

noncomputable abbrev qz177 := (@HMul.hMul Real Real Real qz267 qz446 qz632)

noncomputable def ep1165 := @Enclosure.Complex.IsNear.of_eq qz695 (Complex.mk (@HMul.hMul Real Real Real qz0 qz366 (Real.cos qz177)) (@HMul.hMul Real Real Real qz0 qz366 (@Neg.neg Real Real.instNeg (Real.sin qz177)))) Bool.true 193171472193 1099511627776 29208905817637 216013352927756288 Bool.true 76556906279 1099511627776 29093291664323 216013352927756288 (BSN.cpow_neg_s_mk qz146 138478 1000 28 qz147 rfl)

noncomputable def ep1166 := @Enclosure.Real.IsNear.mulLit_ff qz146 qz632 138478 1000 0 1 3751726938922231 1125899906842624 250000000196463 49115750000000000000 259765821524036352209 562949953421312000 17309750013602901657 24557875000000000000000 qz148 (BSN.isNear_log_sfrac 28 1 3751726938922231 1125899906842624 250000000196463 49115750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz633) Bool.false 62943533227317076688896 18889465931478580854784 1000000000785852 196463000000000000000 3751726938922231 1125899906842624 250000000196463 49115750000000000000 (BSN.log_rat_reduce_isNear 28 1 4 56 32 293399 524288 24973259072661432 36028797018963968 196463 1000000000000000 rfl rfl rfl rfl (ep465 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1167 := nat_lit 2776881810162673198757458670528589221606741945894373574201334598265467487123585

noncomputable def ep1168 := nat_lit 1861785931501483666863570013104365902018798012542973439319105726027859228801

noncomputable def ep1169 := nat_lit 7269771373203617880332707880886993273700103232941146927816026348091226884667521

noncomputable def ep1170 := BSN.sin_dyadic_bound_f 2562956399 2147483648 3 2 1048576 393310 ep1167 ep109 ep1168 ep1169 ep112 ep1168 974811 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2562956399) qz19 0 2 ep1167 ep109 ep1168 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2562956399) qz20 0 2 ep1169 ep112 ep1168 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz474 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 483851547) qz30)

noncomputable def ep1171 := @Enclosure.Real.IsNear.cos_image qz177 qz474 Bool.false 483851547 1048576 185 262144 Bool.true 974811 1048576 1 196463 (@Enclosure.Real.IsNear.recentre' qz177 Bool.false 259765821524036352209 562949953421312000 17309750013602901657 24557875000000000000000 483851547 1048576 185 262144 (ep1166 rfl) rfl) (Enclosure.sfrac_false_div 483851547 1048576) (BSN.cos_reduce1 qz474 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 180352023233369466732544) qz31) 226375608064910080 72057594037927936 Bool.false 974811 1048576 73 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q1 483851547 1048576 226375608064910080 72057594037927936 73 180352023233369466732544 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 974811 1048576 180352023233369466732544 151115727451828646838272 2562956399 2147483648 393310 392926 (ep1170 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1172 := nat_lit 1543539577171041325383860848077262619071309435724671084973772157136827652503681

noncomputable def ep1173 := nat_lit 4626895159650121008817855404205579125409890711148927308042678259958427239053441

noncomputable def ep1174 := BSN.cos_dyadic_bound_f 2562956399 2147483648 3 2 1048576 393310 ep1172 ep78 ep1168 ep1173 ep81 ep1168 386333 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2562956399) qz15 0 2 ep1172 ep78 ep1168 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2562956399) qz16 0 2 ep1173 ep81 ep1168 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1175 := @Enclosure.Real.IsNear.sin_image qz177 qz474 Bool.false 483851547 1048576 185 262144 Bool.false 386333 1048576 1 196463 (@Enclosure.Real.IsNear.recentre' qz177 Bool.false 259765821524036352209 562949953421312000 17309750013602901657 24557875000000000000000 483851547 1048576 185 262144 (ep1166 rfl) rfl) (Enclosure.sfrac_false_div 483851547 1048576) (BSN.sin_reduce1 qz474 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 180352023233369466732544) qz31) 226375608064910080 72057594037927936 Bool.false 386333 1048576 73 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q1 483851547 1048576 226375608064910080 72057594037927936 73 180352023233369466732544 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 386333 1048576 180352023233369466732544 151115727451828646838272 2562956399 2147483648 393310 392926 (ep1174 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1176 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz366 (Real.cos qz177)) (@HMul.hMul Real Real Real qz0 qz366 (@Neg.neg Real Real.instNeg (Real.sin qz177))) Bool.true 193171472193 1099511627776 29208905817637 216013352927756288 Bool.true 76556906279 1099511627776 29093291664323 216013352927756288 (@Enclosure.Real.IsNear.mulLit_ft qz366 (Real.cos qz177) 198163 1048576 1 1048576 974811 1048576 36607799 51501596672 193171472193 1099511627776 29208905817637 216013352927756288 qz371 (@Enclosure.Real.IsNear.recentre' (Real.cos qz177) Bool.true 974811 1048576 36607799 51501596672 974811 1048576 36607799 51501596672 (ep1171 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz366 (@Neg.neg Real Real.instNeg (Real.sin qz177)) 198163 1048576 1 1048576 386333 1048576 36607799 51501596672 76556906279 1099511627776 29093291664323 216013352927756288 qz371 (@Enclosure.Real.IsNear.neg (Real.sin qz177) Bool.false 386333 1048576 36607799 51501596672 (@Enclosure.Real.IsNear.recentre' (Real.sin qz177) Bool.false 386333 1048576 36607799 51501596672 386333 1048576 36607799 51501596672 (ep1175 rfl rfl) rfl)) rfl)

noncomputable def ep1177 := @ep1122 193171472193 1099511627776 29208905817637 216013352927756288 Bool.true 76556906279 1099511627776 29093291664323 216013352927756288 Bool.false 14396688506772034420736 837997562879 1099511627776 1265730851522859 216013352927756288 Bool.false 93743473044757214658560 21314798015 274877906944 316349051027679 54003338231939072 (ep1123 (BSN.head_sum_c_succ qz143 27 28 rfl rfl) (ep1164 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1165 ep1176) rfl rfl

noncomputable abbrev qz178 := (@HMul.hMul Real Real Real qz267 qz446 qz635)

noncomputable def ep1178 := @Enclosure.Complex.IsNear.of_eq qz694 (Complex.mk (@HMul.hMul Real Real Real qz0 qz372 (Real.cos qz178)) (@HMul.hMul Real Real Real qz0 qz372 (@Neg.neg Real Real.instNeg (Real.sin qz178)))) Bool.false 46612239705 1099511627776 28559527448517 216013352927756288 Bool.true 49695357015 274877906944 7178265673407 54003338231939072 (BSN.cpow_neg_s_mk qz146 138478 1000 29 qz147 rfl)

noncomputable def ep1179 := @Enclosure.Real.IsNear.mulLit_ff qz146 qz635 138478 1000 0 1 3791236343078135 1125899906842624 250000000196463 49115750000000000000 52500282631677397853 112589990684262400 17309750013602901657 24557875000000000000000 qz148 (BSN.isNear_log_sfrac 29 1 3791236343078135 1125899906842624 250000000196463 49115750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz636) Bool.false 63606391034871975772160 18889465931478580854784 1000000000785852 196463000000000000000 3791236343078135 1125899906842624 250000000196463 49115750000000000000 (BSN.log_rat_reduce_isNear 29 1 4 58 32 311797 524288 24973259072661432 36028797018963968 196463 1000000000000000 rfl rfl rfl rfl (ep479 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1180 := nat_lit 2458139951900893484885533986616055767822696708288279209221030433279876400028481

noncomputable def ep1181 := nat_lit 4715068898001886327984263418153105464631138714263024713731818152738156321601

noncomputable def ep1182 := nat_lit 7364989717906676682000633433011861092538827847436311578235627663534152887442241

noncomputable def ep1183 := BSN.cos_dyadic_bound_f 2878631049 2147483648 3 2 1048576 393310 ep1180 ep78 ep1181 ep1182 ep81 ep1181 239387 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2878631049) qz15 0 2 ep1180 ep78 ep1181 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2878631049) qz16 0 2 ep1182 ep81 ep1181 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz475 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 488946983) qz30)

noncomputable def ep1184 := @Enclosure.Real.IsNear.cos_image qz178 qz475 Bool.false 488946983 1048576 185 262144 Bool.false 239387 1048576 1 196463 (@Enclosure.Real.IsNear.recentre' qz178 Bool.false 52500282631677397853 112589990684262400 17309750013602901657 24557875000000000000000 488946983 1048576 185 262144 (ep1179 rfl) rfl) (Enclosure.sfrac_false_div 488946983 1048576) (BSN.cos_reduce0 qz475 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 202565651895042751594496) qz31) 226375608064910080 72057594037927936 Bool.false 239387 1048576 74 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q0 488946983 1048576 226375608064910080 72057594037927936 74 202565651895042751594496 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 239387 1048576 202565651895042751594496 151115727451828646838272 2878631049 2147483648 393310 392926 (ep1183 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1185 := nat_lit 4420879858303206763731573765174377897709149163947492156826869325381586994993985

noncomputable def ep1186 := nat_lit 11570860945911633708099290101351122799438368823848910751676711003752104162368321

noncomputable def ep1187 := BSN.sin_dyadic_bound_f 2878631049 2147483648 3 2 1048576 393310 ep1185 ep109 ep1181 ep1186 ep112 ep1181 1020884 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2878631049) qz19 0 2 ep1185 ep109 ep1181 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2878631049) qz20 0 2 ep1186 ep112 ep1181 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1188 := @Enclosure.Real.IsNear.sin_image qz178 qz475 Bool.false 488946983 1048576 185 262144 Bool.false 1020884 1048576 1 196463 (@Enclosure.Real.IsNear.recentre' qz178 Bool.false 52500282631677397853 112589990684262400 17309750013602901657 24557875000000000000000 488946983 1048576 185 262144 (ep1179 rfl) rfl) (Enclosure.sfrac_false_div 488946983 1048576) (BSN.sin_reduce0 qz475 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 202565651895042751594496) qz31) 226375608064910080 72057594037927936 Bool.false 1020884 1048576 74 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q0 488946983 1048576 226375608064910080 72057594037927936 74 202565651895042751594496 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1020884 1048576 202565651895042751594496 151115727451828646838272 2878631049 2147483648 393310 392926 (ep1187 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1189 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz372 (Real.cos qz178)) (@HMul.hMul Real Real Real qz0 qz372 (@Neg.neg Real Real.instNeg (Real.sin qz178))) Bool.false 46612239705 1099511627776 28559527448517 216013352927756288 Bool.true 49695357015 274877906944 7178265673407 54003338231939072 (@Enclosure.Real.IsNear.mulLit_ff qz372 (Real.cos qz178) 194715 1048576 1 1048576 239387 1048576 36607799 51501596672 46612239705 1099511627776 28559527448517 216013352927756288 qz376 (@Enclosure.Real.IsNear.recentre' (Real.cos qz178) Bool.false 239387 1048576 36607799 51501596672 239387 1048576 36607799 51501596672 (ep1184 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz372 (@Neg.neg Real Real.instNeg (Real.sin qz178)) 194715 1048576 1 1048576 255221 262144 36607799 51501596672 49695357015 274877906944 7178265673407 54003338231939072 qz376 (@Enclosure.Real.IsNear.neg (Real.sin qz178) Bool.false 255221 262144 36607799 51501596672 (@Enclosure.Real.IsNear.recentre' (Real.sin qz178) Bool.false 1020884 1048576 36607799 51501596672 255221 262144 36607799 51501596672 (ep1188 rfl rfl) rfl)) rfl)

noncomputable def ep1190 := @ep1120 46612239705 1099511627776 28559527448517 216013352927756288 Bool.true 49695357015 274877906944 7178265673407 54003338231939072 Bool.false 972638763985739850973184 110576225323 137438953472 80893148685711 13500834557984768 Bool.true 7801188655820701696000 3547569875 34359738368 161763658350543 27001669115969536 (ep1121 (BSN.head_sum_c_succ qz143 28 29 rfl rfl) (ep1177 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1178 ep1189) rfl rfl

noncomputable abbrev qz179 := (@HMul.hMul Real Real Real qz267 qz446 qz637)

noncomputable def ep1191 := @Enclosure.Complex.IsNear.of_eq qz693 (Complex.mk (@HMul.hMul Real Real Real qz0 qz377 (Real.cos qz179)) (@HMul.hMul Real Real Real qz0 qz377 (@Neg.neg Real Real.instNeg (Real.sin qz179)))) Bool.false 194593577451 1099511627776 28233070078615 216013352927756288 Bool.false 49303655891 1099511627776 28083970378655 216013352927756288 (BSN.cpow_neg_s_mk qz146 138478 1000 30 qz147 rfl)

noncomputable def ep1192 := @Enclosure.Real.IsNear.mulLit_ff qz146 qz637 138478 1000 0 1 3829405717437687 1125899906842624 250000000196463 49115750000000000000 265144222469668010193 562949953421312000 17309750013602901657 24557875000000000000000 qz148 (BSN.isNear_log_sfrac 30 1 3829405717437687 1125899906842624 250000000196463 49115750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz638) Bool.false 64246766873087041339392 18889465931478580854784 1000000000785852 196463000000000000000 3829405717437687 1125899906842624 250000000196463 49115750000000000000 (BSN.log_rat_reduce_isNear 30 1 4 60 32 329571 524288 24973259072661432 36028797018963968 196463 1000000000000000 rfl rfl rfl rfl (ep493 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1193 := nat_lit 4190254738755142704231849022853341567663213895862957421547296143275826864881920

noncomputable def ep1194 := nat_lit 4236427214880912521146040880445675247577550072125440855458329884024550359296

noncomputable def ep1195 := nat_lit 10967617719344137986049177660333268250621863217619542533143604984005411564585216

noncomputable def ep1196 := BSN.sin_dyadic_bound_f 2840370338 2147483648 3 2 1048576 393310 ep1193 ep109 ep1194 ep1195 ep112 ep1194 1016457 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2840370338) qz19 0 2 ep1193 ep109 ep1194 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2840370338) qz20 0 2 ep1195 ep112 ep1194 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz476 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 493869599) qz30)

noncomputable def ep1197 := @Enclosure.Real.IsNear.cos_image qz179 qz476 Bool.false 493869599 1048576 185 262144 Bool.false 1016457 1048576 1 196463 (@Enclosure.Real.IsNear.recentre' qz179 Bool.false 265144222469668010193 562949953421312000 17309750013602901657 24557875000000000000000 493869599 1048576 185 262144 (ep1192 rfl) rfl) (Enclosure.sfrac_false_div 493869599 1048576) (BSN.cos_reduce3 qz476 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 199873293753446624657408) qz31) 226375608064910080 72057594037927936 Bool.false 1016457 1048576 74 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q3 493869599 1048576 226375608064910080 72057594037927936 74 199873293753446624657408 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1016457 1048576 199873293753446624657408 151115727451828646838272 2840370338 2147483648 393310 392926 (ep1196 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1198 := nat_lit 2329802155848359685693758808643165615478486631067032096795368226212803613982976

noncomputable def ep1199 := nat_lit 6980933613115317232038984344168605495940304793056845408675188018870361741230336

noncomputable def ep1200 := BSN.cos_dyadic_bound_f 2840370338 2147483648 3 2 1048576 393310 ep1198 ep78 ep1194 ep1199 ep81 ep1194 257537 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2840370338) qz15 0 2 ep1198 ep78 ep1194 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2840370338) qz16 0 2 ep1199 ep81 ep1194 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1201 := @Enclosure.Real.IsNear.sin_image qz179 qz476 Bool.false 493869599 1048576 185 262144 Bool.true 257537 1048576 1 196463 (@Enclosure.Real.IsNear.recentre' qz179 Bool.false 265144222469668010193 562949953421312000 17309750013602901657 24557875000000000000000 493869599 1048576 185 262144 (ep1192 rfl) rfl) (Enclosure.sfrac_false_div 493869599 1048576) (BSN.sin_reduce3 qz476 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 199873293753446624657408) qz31) 226375608064910080 72057594037927936 Bool.false 257537 1048576 74 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q3 493869599 1048576 226375608064910080 72057594037927936 74 199873293753446624657408 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 257537 1048576 199873293753446624657408 151115727451828646838272 2840370338 2147483648 393310 392926 (ep1200 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1202 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz377 (Real.cos qz179)) (@HMul.hMul Real Real Real qz0 qz377 (@Neg.neg Real Real.instNeg (Real.sin qz179))) Bool.false 194593577451 1099511627776 28233070078615 216013352927756288 Bool.false 49303655891 1099511627776 28083970378655 216013352927756288 (@Enclosure.Real.IsNear.mulLit_ff qz377 (Real.cos qz179) 191443 1048576 1 1048576 1016457 1048576 36607799 51501596672 194593577451 1099511627776 28233070078615 216013352927756288 qz381 (@Enclosure.Real.IsNear.recentre' (Real.cos qz179) Bool.false 1016457 1048576 36607799 51501596672 1016457 1048576 36607799 51501596672 (ep1197 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz377 (@Neg.neg Real Real.instNeg (Real.sin qz179)) 191443 1048576 1 1048576 257537 1048576 36607799 51501596672 49303655891 1099511627776 28083970378655 216013352927756288 qz381 (@Enclosure.Real.IsNear.neg (Real.sin qz179) Bool.true 257537 1048576 36607799 51501596672 (@Enclosure.Real.IsNear.recentre' (Real.sin qz179) Bool.true 257537 1048576 36607799 51501596672 257537 1048576 36607799 51501596672 (ep1201 rfl rfl) rfl)) rfl)

noncomputable def ep1203 := @ep1118 194593577451 1099511627776 28233070078615 216013352927756288 Bool.false 49303655891 1099511627776 28083970378655 216013352927756288 Bool.false 148324583135455498731520 1079203380035 1099511627776 1322523449049991 216013352927756288 Bool.true 2206533610909688922112 64218580109 1099511627776 1322193237182999 216013352927756288 (ep1119 (BSN.head_sum_c_succ qz143 29 30 rfl rfl) (ep1190 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1191 ep1202) rfl rfl

noncomputable abbrev qz180 := (@HMul.hMul Real Real Real qz267 qz446 qz639)

noncomputable def ep1204 := @Enclosure.Complex.IsNear.of_eq qz692 (Complex.mk (@HMul.hMul Real Real Real qz0 qz382 (Real.cos qz180)) (@HMul.hMul Real Real Real qz0 qz382 (@Neg.neg Real Real.instNeg (Real.sin qz180)))) Bool.true 314321101 4294967296 3457666088739 27001669115969536 Bool.false 90169853581 549755813888 13882757894647 108006676463878144 (BSN.cpow_neg_s_mk qz146 138478 1000 31 qz147 rfl)

noncomputable def ep1205 := @Enclosure.Real.IsNear.mulLit_ff qz146 qz639 138478 1000 0 1 3866325256314103 1125899906842624 250000000196463 49115750000000000000 267700494421932177617 562949953421312000 17309750013602901657 24557875000000000000000 qz148 (BSN.isNear_log_sfrac 31 1 3866325256314103 1125899906842624 250000000196463 49115750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz640) Bool.false 64866173951437069877248 18889465931478580854784 1000000000785852 196463000000000000000 3866325256314103 1125899906842624 250000000196463 49115750000000000000 (BSN.log_rat_reduce_isNear 31 1 4 62 32 346763 524288 24973259072661432 36028797018963968 196463 1000000000000000 rfl rfl rfl rfl (ep507 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1206 := nat_lit 1335592195093853519713635885944220202837832199902887190892629415228478041686016

noncomputable def ep1207 := nat_lit 1394385822173933474613858111760290499660797756546523715578998732273955700736

noncomputable def ep1208 := nat_lit 4003987813637212692191679941609140027514175004195568525246730248220886213656576

noncomputable def ep1209 := BSN.cos_dyadic_bound_f 2471996604 2147483648 3 2 1048576 393310 ep1206 ep78 ep1207 ep1208 ep81 ep1207 427264 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2471996604) qz15 0 2 ep1206 ep78 ep1207 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2471996604) qz16 0 2 ep1208 ep81 ep1207 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz477 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 498631027) qz30)

noncomputable def ep1210 := @Enclosure.Real.IsNear.cos_image qz180 qz477 Bool.false 498631027 1048576 185 262144 Bool.true 427264 1048576 1 196463 (@Enclosure.Real.IsNear.recentre' qz180 Bool.false 267700494421932177617 562949953421312000 17309750013602901657 24557875000000000000000 498631027 1048576 185 262144 (ep1205 rfl) rfl) (Enclosure.sfrac_false_div 498631027 1048576) (BSN.cos_reduce2 qz477 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 173951296676279441424384) qz31) 226375608064910080 72057594037927936 Bool.false 427264 1048576 75 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q2 498631027 1048576 226375608064910080 72057594037927936 75 173951296676279441424384 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 427264 1048576 173951296676279441424384 151115727451828646838272 2471996604 2147483648 393310 392926 (ep1209 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1211 := nat_lit 2402950442511197188704853508210188132708369321619959724634269748425441310474240

noncomputable def ep1212 := nat_lit 6291184058102949125744289132179071305808183122160723954693102390785807503917056

noncomputable def ep1213 := BSN.sin_dyadic_bound_f 2471996604 2147483648 3 2 1048576 393310 ep1211 ep109 ep1207 ep1212 ep112 ep1207 957578 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2471996604) qz19 0 2 ep1211 ep109 ep1207 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2471996604) qz20 0 2 ep1212 ep112 ep1207 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1214 := @Enclosure.Real.IsNear.sin_image qz180 qz477 Bool.false 498631027 1048576 185 262144 Bool.true 957578 1048576 1 196463 (@Enclosure.Real.IsNear.recentre' qz180 Bool.false 267700494421932177617 562949953421312000 17309750013602901657 24557875000000000000000 498631027 1048576 185 262144 (ep1205 rfl) rfl) (Enclosure.sfrac_false_div 498631027 1048576) (BSN.sin_reduce2 qz477 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 173951296676279441424384) qz31) 226375608064910080 72057594037927936 Bool.false 957578 1048576 75 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q2 498631027 1048576 226375608064910080 72057594037927936 75 173951296676279441424384 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 957578 1048576 173951296676279441424384 151115727451828646838272 2471996604 2147483648 393310 392926 (ep1213 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1215 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz382 (Real.cos qz180)) (@HMul.hMul Real Real Real qz0 qz382 (@Neg.neg Real Real.instNeg (Real.sin qz180))) Bool.true 314321101 4294967296 3457666088739 27001669115969536 Bool.false 90169853581 549755813888 13882757894647 108006676463878144 (@Enclosure.Real.IsNear.mulLit_ft qz382 (Real.cos qz180) 188329 1048576 1 1048576 1669 4096 36607799 51501596672 314321101 4294967296 3457666088739 27001669115969536 qz386 (@Enclosure.Real.IsNear.recentre' (Real.cos qz180) Bool.true 427264 1048576 36607799 51501596672 1669 4096 36607799 51501596672 (ep1210 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz382 (@Neg.neg Real Real.instNeg (Real.sin qz180)) 188329 1048576 1 1048576 478789 524288 36607799 51501596672 90169853581 549755813888 13882757894647 108006676463878144 qz386 (@Enclosure.Real.IsNear.neg (Real.sin qz180) Bool.true 478789 524288 36607799 51501596672 (@Enclosure.Real.IsNear.recentre' (Real.sin qz180) Bool.true 957578 1048576 36607799 51501596672 478789 524288 36607799 51501596672 (ep1214 rfl rfl) rfl)) rfl)

noncomputable def ep1216 := @ep1116 314321101 4294967296 3457666088739 27001669115969536 Bool.false 90169853581 549755813888 13882757894647 108006676463878144 Bool.false 4289543517578129833984 998737178179 1099511627776 1350184777759903 216013352927756288 Bool.false 63838264712613869912064 116121127053 1099511627776 1349958752972293 216013352927756288 (ep1117 (BSN.head_sum_c_succ qz143 30 31 rfl rfl) (ep1203 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1204 ep1215) rfl rfl

noncomputable abbrev qz181 := (@HMul.hMul Real Real Real qz267 qz446 qz641)

noncomputable def ep1217 := @Enclosure.Complex.IsNear.of_eq qz691 (Complex.mk (@HMul.hMul Real Real Real qz0 qz387 (Real.cos qz181)) (@HMul.hMul Real Real Real qz0 qz387 (@Neg.neg Real Real.instNeg (Real.sin qz181)))) Bool.true 144122142219 1099511627776 27295824751863 216013352927756288 Bool.true 65206069325 549755813888 13640646879497 108006676463878144 (BSN.cpow_neg_s_mk qz146 138478 1000 32 qz147 rfl)

noncomputable def ep1218 := @Enclosure.Real.IsNear.mulLit_ff qz146 qz641 138478 1000 0 1 15608286920413395 4503599627370496 200000000196463 39292600000000000000 216140435616500611281 450359962737049600 13847800013602901657 19646300000000000000000 qz148 (BSN.isNear_log_sfrac 32 1 15608286920413395 4503599627370496 200000000196463 39292600000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz642) Bool.false 65465900263437584302080 18889465931478580854784 1000000000982315 196463000000000000000 15608286920413395 4503599627370496 200000000196463 39292600000000000000 (BSN.log_rat_reduce_isNear 32 1 5 64 64 0 524288 24973259072661432 36028797018963968 196463 1000000000000000 rfl rfl rfl rfl (ep518 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1219 := nat_lit 10353366708870641454975556952031517456

noncomputable def ep1220 := BSN.sin_dyadic_bound_f 1793785046 2147483648 2 1 1048576 393310 ep1219 ep65 ep1219 ep1219 ep66 ep1219 777513 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1793785046) qz19 0 1 ep1219 ep65 ep1219 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1793785046) qz20 0 1 ep1219 ep66 ep1219 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz478 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 503241167) qz30)

noncomputable def ep1221 := @Enclosure.Real.IsNear.cos_image qz181 qz478 Bool.false 503241167 1048576 185 262144 Bool.true 777513 1048576 1 196463 (@Enclosure.Real.IsNear.recentre' qz181 Bool.false 216140435616500611281 450359962737049600 13847800013602901657 19646300000000000000000 503241167 1048576 185 262144 (ep1218 rfl) rfl) (Enclosure.sfrac_false_div 503241167 1048576) (BSN.cos_reduce1 qz478 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 126226401025492175028224) qz31) 226375608064910080 72057594037927936 Bool.false 777513 1048576 76 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q1 503241167 1048576 226375608064910080 72057594037927936 76 126226401025492175028224 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 777513 1048576 126226401025492175028224 151115727451828646838272 1793785046 2147483648 393310 392926 (ep1220 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1222 := nat_lit 370029345778177963429353524758054644945603599607625300073692882622044166185216

noncomputable def ep1223 := nat_lit 107192202208350897773855241144964086354647278286093466498621301574032711936

noncomputable def ep1224 := nat_lit 1109873652930117188492512863791874006664101504266303713288081405262984433131776

noncomputable def ep1225 := BSN.cos_dyadic_bound_f 1793785046 2147483648 3 2 1048576 393310 ep1222 ep78 ep1223 ep1224 ep81 ep1223 703550 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1793785046) qz15 0 2 ep1222 ep78 ep1223 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1793785046) qz16 0 2 ep1224 ep81 ep1223 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1226 := @Enclosure.Real.IsNear.sin_image qz181 qz478 Bool.false 503241167 1048576 185 262144 Bool.false 703550 1048576 1 196463 (@Enclosure.Real.IsNear.recentre' qz181 Bool.false 216140435616500611281 450359962737049600 13847800013602901657 19646300000000000000000 503241167 1048576 185 262144 (ep1218 rfl) rfl) (Enclosure.sfrac_false_div 503241167 1048576) (BSN.sin_reduce1 qz478 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 126226401025492175028224) qz31) 226375608064910080 72057594037927936 Bool.false 703550 1048576 76 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q1 503241167 1048576 226375608064910080 72057594037927936 76 126226401025492175028224 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 703550 1048576 126226401025492175028224 151115727451828646838272 1793785046 2147483648 393310 392926 (ep1225 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1227 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz387 (Real.cos qz181)) (@HMul.hMul Real Real Real qz0 qz387 (@Neg.neg Real Real.instNeg (Real.sin qz181))) Bool.true 144122142219 1099511627776 27295824751863 216013352927756288 Bool.true 65206069325 549755813888 13640646879497 108006676463878144 (@Enclosure.Real.IsNear.mulLit_ft qz387 (Real.cos qz181) 185363 1048576 1 1048576 777513 1048576 36607799 51501596672 144122142219 1099511627776 27295824751863 216013352927756288 qz391 (@Enclosure.Real.IsNear.recentre' (Real.cos qz181) Bool.true 777513 1048576 36607799 51501596672 777513 1048576 36607799 51501596672 (ep1221 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz387 (@Neg.neg Real Real.instNeg (Real.sin qz181)) 185363 1048576 1 1048576 351775 524288 36607799 51501596672 65206069325 549755813888 13640646879497 108006676463878144 qz391 (@Enclosure.Real.IsNear.neg (Real.sin qz181) Bool.false 351775 524288 36607799 51501596672 (@Enclosure.Real.IsNear.recentre' (Real.sin qz181) Bool.false 703550 1048576 36607799 51501596672 351775 524288 36607799 51501596672 (ep1226 rfl rfl) rfl)) rfl)

noncomputable def ep1228 := @ep1114 144122142219 1099511627776 27295824751863 216013352927756288 Bool.true 65206069325 549755813888 13640646879497 108006676463878144 Bool.false 939659169310224374824960 106826879495 137438953472 688740301255883 108006676463878144 Bool.true 7856566711791581659136 14291011597 1099511627776 1377240046731287 216013352927756288 (ep1115 (BSN.head_sum_c_succ qz143 31 32 rfl rfl) (ep1216 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1217 ep1227) rfl rfl

theorem EMRow47.d16 : Enclosure.Complex.IsNear qz173 Bool.false 106826879495 137438953472 688740301255883 108006676463878144 Bool.true 14291011597 1099511627776 1377240046731287 216013352927756288 := ep1113 (BSN.head_sum_c_succ qz143 32 33 rfl rfl) (ep1228 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable def ep1229 := nat_lit 333745458961880063974343388101423

noncomputable def ep1230 := nat_lit 386905599788501083873838366720000

noncomputable def ep1231 := nat_lit 314567656101781086466581427690207402035229

noncomputable def ep1232 := nat_lit 44801010842342377476014969444935705559040000

noncomputable abbrev qz699 := (@HAdd.hAdd Complex Complex Complex qz713 (@HAdd.hAdd Complex Complex Complex qz713 qz716 (@HMul.hMul Complex Complex Complex qz715 Complex.I (@HDiv.hDiv Complex Complex Complex qz717 (↑qz720) (2 : Complex)))) (@Nat.cast Complex Complex.instNatCast 2))

noncomputable abbrev qz479 := qz699

noncomputable abbrev qz182 := (Complex.Stirling.logGammaStirling 1 qz479)

noncomputable abbrev qz700 := (@HAdd.hAdd Complex Complex Complex qz713 qz716 (@HMul.hMul Complex Complex Complex qz715 Complex.I (@HDiv.hDiv Complex Complex Complex qz717 (↑qz720) (2 : Complex))))

noncomputable abbrev qz480 := qz700

noncomputable abbrev qz183 := qz480

noncomputable abbrev qz184 := (@HMul.hMul Real Real Real qz267 (@HDiv.hDiv Real Real Real qz270 qz446 (2 : Real)) (Real.log Real.pi))

noncomputable def ep1233 := Complex.re (@HMul.hMul Complex Complex Complex qz76 (Complex.exp (@HMul.hMul Complex Complex Complex qz76 Complex.I ↑(@HSub.hSub Real Real Real qz396 (Complex.im (@HSub.hSub Complex Complex Complex qz77 qz182 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz183 (@Nat.cast Complex Complex.instNatCast j))))) qz184))) (zetaApproximant qz143 1 35))

noncomputable def ep1234 := @Enclosure.Real.IsNear.of_eq ep1233 (@HSub.hSub Real Real Real qz396 (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz396 (Complex.im (@HSub.hSub Complex Complex Complex qz77 qz182 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz183 (@Nat.cast Complex Complex.instNatCast j))))) qz184)) (Complex.re (zetaApproximant qz143 1 35))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz396 (Complex.im (@HSub.hSub Complex Complex Complex qz77 qz182 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz183 (@Nat.cast Complex Complex.instNatCast j))))) qz184)) (Complex.im (zetaApproximant qz143 1 35))))

noncomputable def ep1235 := nat_lit 2669961968401520549575764654379

noncomputable def ep1236 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz396 (Complex.im (@HSub.hSub Complex Complex Complex qz77 qz182 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz183 (@Nat.cast Complex Complex.instNatCast j))))) qz184)) (Complex.re (zetaApproximant qz143 1 35))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz396 (Complex.im (@HSub.hSub Complex Complex Complex qz77 qz182 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz183 (@Nat.cast Complex Complex.instNatCast j))))) qz184)) (Complex.im (zetaApproximant qz143 1 35))) ep1235

noncomputable def ep1237 := nat_lit 3095244798308008670990706933760

noncomputable def ep1238 := nat_lit 314183288282318780700398104877048145843373

noncomputable def ep1239 := nat_lit 13306980624704835800394003

noncomputable def ep1240 := nat_lit 24181599986781317742114897920000

noncomputable def ep1241 := nat_lit 8007662905464703462152558607484503997

noncomputable def ep1242 := nat_lit 933354392548799530750311863436160532480000

noncomputable def ep1243 := nat_lit 64563993488167390223782861062207823071553843792043778013921280

noncomputable def ep1244 := @Enclosure.Real.IsNear.mulLit_ff (Real.cos (@HSub.hSub Real Real Real qz396 (Complex.im (@HSub.hSub Complex Complex Complex qz77 qz182 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz183 (@Nat.cast Complex Complex.instNatCast j))))) qz184)) (Complex.re (zetaApproximant qz143 1 35)) 1048575 1048576 18926129

noncomputable def ep1245 := nat_lit 190970743752343934595219559

noncomputable def ep1246 := nat_lit 221389160035229349445632000

noncomputable def ep1247 := nat_lit 1455642763416612258162200020693

noncomputable def ep1248 := nat_lit 217473892740006318400685998080000

noncomputable def ep1249 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HSub.hSub Real Real Real qz396 (Complex.im (@HSub.hSub Complex Complex Complex qz77 qz182 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz183 (@Nat.cast Complex Complex.instNatCast j))))) qz184)) Bool.false 1048575 1048576 18926129

noncomputable abbrev qz481 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 151533101) qz30)

noncomputable def ep1250 := @Enclosure.Real.IsNear.cos_image (@HSub.hSub Real Real Real qz396 (Complex.im (@HSub.hSub Complex Complex Complex qz77 qz182 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz183 (@Nat.cast Complex Complex.instNatCast j))))) qz184) qz481 Bool.false 151533101 1048576 95

noncomputable def ep1251 := nat_lit 111792827822566523023027013

noncomputable def ep1252 := @Enclosure.Real.IsNear.recentre' (@HSub.hSub Real Real Real qz396 (Complex.im (@HSub.hSub Complex Complex Complex qz77 qz182 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz183 (@Nat.cast Complex Complex.instNatCast j))))) qz184) Bool.false 976244572639205568817 6755399441055744000 ep1251 ep550

noncomputable def ep1253 := nat_lit 30175417880566523023027013

noncomputable def ep1254 := @Enclosure.Real.IsNear.subLit_ff_p (Complex.im (@HSub.hSub Complex Complex Complex qz77 qz182 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz183 (@Nat.cast Complex Complex.instNatCast j))))) qz184 1511677084870411071793 6755399441055744000 ep1253 ep550 5194379019 65536000

noncomputable def ep1255 := nat_lit 63979164312482976157990912000

noncomputable def ep1256 := nat_lit 9419287959282352140559429

noncomputable def ep1257 := @Enclosure.Complex.IsNear.im_isNear (@HSub.hSub Complex Complex Complex qz77 qz182 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz183 (@Nat.cast Complex Complex.instNatCast j)))) Bool.true 122611472276970241883 1125899906842624000 ep1256 ep556 Bool.false 1511677084870411071793 6755399441055744000

noncomputable def ep1258 := nat_lit 9288215958664332980495429

noncomputable def ep1259 := nat_lit 28602553880257513442995013

noncomputable def ep1260 := @Enclosure.Complex.IsNear.subLitP qz182 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz183 (@Nat.cast Complex Complex.instNatCast j))) Bool.true 113069135155266588883 1125899906842624000 ep1258 ep556 Bool.false 1532753464295754375793 6755399441055744000 ep1259

noncomputable def ep1261 := nat_lit 138048245214477770516776736094420992

noncomputable def ep1262 := nat_lit 425499272257931309968735802604126208

noncomputable abbrev qz482 := (@HSub.hSub Complex Complex Complex qz644 qz699 qz647)

noncomputable abbrev qz483 := (Complex.log qz699)

noncomputable abbrev qz185 := (@HSub.hSub Complex Complex Complex qz393 (@HMul.hMul Complex Complex Complex qz392 qz482 qz483) qz479)

noncomputable abbrev qz186 := qz479

noncomputable def ep1263 := @Enclosure.Complex.IsNear.of_eq qz182 (@HAdd.hAdd Complex Complex Complex qz4 (@HAdd.hAdd Complex Complex Complex qz4 qz185 qz82) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz84 2 k))) (@HMul.hMul Complex Complex Complex qz76 (@HMul.hMul Complex Complex Complex qz76 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz77 (@HMul.hMul Complex Complex Complex qz76 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz85 qz186 (@HSub.hSub Int Int Int qz403 qz87 (@HMul.hMul Int Int Int qz404 qz88 (@Nat.cast Int instNatCastInt k)))))) Bool.true 113069135155266588883

noncomputable def ep1264 := @Enclosure.Complex.IsNear.addLitP (@HAdd.hAdd Complex Complex Complex qz4 qz185 qz82) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz84 2 k))) (@HMul.hMul Complex Complex Complex qz76 (@HMul.hMul Complex Complex Complex qz76 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz77 (@HMul.hMul Complex Complex Complex qz76 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz85 qz186 (@HSub.hSub Int Int Int qz403 qz87 (@HMul.hMul Int Int Int qz404 qz88 (@Nat.cast Int instNatCastInt k))))) Bool.true 113069179143996444883 1125899906842624000

noncomputable def ep1265 := nat_lit 7770051802861982102623394725888

noncomputable def ep1266 := nat_lit 26332504007923874862719316262912000

noncomputable def ep1267 := @ep1264 8857930860828138629 49115750000000000000000 Bool.false 510920528752510569339 2251799813685248000 18184750081789315067 196463000000000000000000 Bool.false 2684859 68719476736 3 68719476736 Bool.true 61965650767 51539607552000 69239 51539607552000 Bool.true ep1265 113069135155266588883 1125899906842624000 ep1258 ep556 Bool.false ep1266

noncomputable def ep1268 := @Enclosure.Complex.IsNear.addLitP qz185 qz82 Bool.true 114103810995799068883 1125899906842624000 70114000017728624657 392926000000000000000000

noncomputable def ep1269 := nat_lit 14820203448761902023704576

noncomputable def ep1270 := @ep1268 Bool.false 510920528752510569339 2251799813685248000 18184750081789315067 196463000000000000000000 Bool.false 120447 131072 1 524288 Bool.false 0 1 0 1 Bool.true ep1269 113069179143996444883 1125899906842624000 8857930860828138629 49115750000000000000000 Bool.false 510920528752510569339 510920528752510569339 2251799813685248000

noncomputable abbrev qz187 := (@HMul.hMul Complex Complex Complex qz392 qz482 qz483)

noncomputable def ep1271 := @Enclosure.Complex.IsNear.subLitP qz187 qz186 Bool.true 111570536205403164883 1125899906842624000 70114000017728624657 392926000000000000000000 Bool.false 666832896052263455611

noncomputable def ep1272 := nat_lit 2043682115010042277356000

noncomputable def ep1273 := @ep1271 2251799813685248000 18184750081789315067 196463000000000000000000 Bool.false 9000 4000 0 1 Bool.false 276956 4000 0 1 Bool.true 456415243983196275532000 114103810995799068883 1125899906842624000 70114000017728624657 392926000000000000000000 Bool.false ep1272 510920528752510569339 2251799813685248000 18184750081789315067 196463000000000000000000

noncomputable abbrev qz188 := qz482

noncomputable abbrev qz189 := qz483

noncomputable def ep1274 := @Enclosure.Complex.IsNear.mul qz188 qz189 Bool.true 111570536205403164883 1125899906842624000 70114000017728624657 392926000000000000000000 Bool.false 666832896052263455611 2251799813685248000 18184750081789315067

noncomputable abbrev qz190 := (Complex.re qz482)

noncomputable abbrev qz191 := (Complex.re qz483)

noncomputable abbrev qz192 := (Complex.im qz482)

noncomputable abbrev qz193 := (Complex.im qz483)

noncomputable def ep1275 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 qz190 qz191) (@HMul.hMul Real Real Real qz0 qz192 qz193) 66803342395007043 9007199254740992 875000004125723 392926000000000000000 59960477002389522629 562949953421312000

noncomputable def ep1276 := nat_lit 502469025280180126133655349617491968

noncomputable def ep1277 := @Enclosure.Real.IsNear.mulLit_ff qz190 qz191 7000 4000 0 1 9543334627858149 2251799813685248 125000000589389 98231500000000000000

noncomputable def ep1278 := @Enclosure.Complex.IsNear.re_isNear qz188 Bool.false 7000 4000 0 1 Bool.false 276956 4000 0 1

noncomputable abbrev qz701 := (Enclosure.sfrac Bool.false 276956 4000)

noncomputable abbrev qz484 := qz701

noncomputable def ep1279 := @Enclosure.Complex.IsNear.of_eq qz188 (Complex.mk (Enclosure.sfrac Bool.false 7000 4000) qz484) Bool.false 7000 4000 0 1 Bool.false 276956 4000 0

noncomputable abbrev qz485 := (Complex.log (Complex.mk qz651 qz701))

noncomputable def ep1280 := @Enclosure.Complex.IsNear.of_eq qz189 qz485 Bool.false 9543334627858149 2251799813685248 125000000589389 98231500000000000000 Bool.false 865992821999011 562949953421312 1000000000196463 392926000000000000000

noncomputable def ep1281 := nat_lit 6154245909262551737093205413832918589323018240

noncomputable def ep1282 := nat_lit 12865094350140633133666140492971966401609728

noncomputable def ep1283 := nat_lit 48047808303382014324489696795746280603648

noncomputable def ep1284 := BSN.log_dyadic_bound 11249625936 142321625936 3 2 ep1281 1048576 392926 ep1282 ep1283 166113 153571251872 131072000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 11249625936) (BSN.artanhQ 142321625936) 0 2 ep1282 ep1281 ep1283 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz702 := (Real.log (Enclosure.sfrac Bool.false 76785625936 16000000))

noncomputable def ep1285 := @Enclosure.Real.IsNear.mulLit_ff qz96 qz702 1 2 0 1 9543334627858149 1125899906842624 125000000589389 49115750000000000000 9543334627858149 2251799813685248 125000000589389 98231500000000000000 qz407 (BSN.isNear_log_sfrac 76785625936 16000000 9543334627858149 1125899906842624 125000000589389 49115750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 76785625936) qz653)) Bool.false 320221172823711566266368 37778931862957161709568 1000000004715112 392926000000000000000 9543334627858149 1125899906842624 125000000589389 49115750000000000000 (BSN.log_rat_reduce_isNear 76785625936 16000000 12 153571251872 131072000000 166113 1048576 24973259072661432 36028797018963968 392926 1000000000000000 rfl rfl rfl rfl (ep1284 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1286 := BSN.arctan_dyadic_bound_f 9000 276956 1 0 1048576 392926 0 1 1 0 1 1 34062 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 9000) (BSN.arctanEvenQ 276956) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 9000) (BSN.arctanOddQ 276956) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz486 := (Real.arctan (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 9000) (@Nat.cast Real Real.instNatCast 276956)))

noncomputable def ep1287 := @Enclosure.Real.IsNear.subLit_ff_p qz97 qz486 884279719003555 562949953421312 1 2000000000000000 34062 1048576 1 392926 908059289320434958336 865992821999011 562949953421312 1000000000196463 392926000000000000000 qz98 (ep1286 rfl) rfl rfl

noncomputable abbrev qz487 := (Complex.mk qz651 qz701)

noncomputable abbrev qz488 := (Real.arctan (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 276956) (@Nat.cast Real Real.instNatCast 9000)))

noncomputable def ep1288 := @Enclosure.Complex.IsNear.re_isNear qz189 Bool.false 9543334627858149 2251799813685248 125000000589389 98231500000000000000 Bool.false 865992821999011 562949953421312 1000000000196463 392926000000000000000 (ep1280 (@congrArg Complex Complex qz186 qz487 Complex.log (BSN.w_shift_mk qz146 Bool.false 138478 1000 2 qz147 rfl)) (@Enclosure.Complex.IsNear.of_parts qz485 Bool.false 9543334627858149 2251799813685248 125000000589389 98231500000000000000 Bool.false 865992821999011 562949953421312 1000000000196463 392926000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz485) (@HMul.hMul Real Real Real qz0 qz96 qz702) Bool.false 9543334627858149 2251799813685248 125000000589389 98231500000000000000 (Enclosure.clog_re_eq 9000 276956 4000 76785625936 16000000 rfl rfl rfl) (ep1285 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz485) qz488 Bool.false 865992821999011 562949953421312 1000000000196463 392926000000000000000 (Enclosure.clog_im_eq 9000 276956 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz488 (@HSub.hSub Real Real Real qz396 qz97 qz486) Bool.false 865992821999011 562949953421312 1000000000196463 392926000000000000000 (BSN.arctan_recip 276956 9000 rfl rfl) ep1287))))

noncomputable def ep1289 := @Enclosure.Real.IsNear.mulLit_ff qz192 qz193 276956 4000 0 1 865992821999011 562949953421312 1000000000196463 392926000000000000000

noncomputable def ep1290 := @Enclosure.Complex.IsNear.im_isNear qz188 Bool.false 7000 4000 0 1 Bool.false 276956 4000 0 1

noncomputable def ep1291 := @Enclosure.Complex.IsNear.im_isNear qz189 Bool.false 9543334627858149 2251799813685248 125000000589389 98231500000000000000 Bool.false 865992821999011 562949953421312 1000000000196463 392926000000000000000 (ep1280 (@congrArg Complex Complex qz186 qz487 Complex.log (BSN.w_shift_mk qz146 Bool.false 138478 1000 2 qz147 rfl)) (@Enclosure.Complex.IsNear.of_parts qz485 Bool.false 9543334627858149 2251799813685248 125000000589389 98231500000000000000 Bool.false 865992821999011 562949953421312 1000000000196463 392926000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz485) (@HMul.hMul Real Real Real qz0 qz96 qz702) Bool.false 9543334627858149 2251799813685248 125000000589389 98231500000000000000 (Enclosure.clog_re_eq 9000 276956 4000 76785625936 16000000 rfl rfl rfl) (ep1285 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz485) qz488 Bool.false 865992821999011 562949953421312 1000000000196463 392926000000000000000 (Enclosure.clog_im_eq 9000 276956 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz488 (@HSub.hSub Real Real Real qz396 qz97 qz486) Bool.false 865992821999011 562949953421312 1000000000196463 392926000000000000000 (BSN.arctan_recip 276956 9000 rfl rfl) ep1287))))

noncomputable abbrev qz194 := (@ep1279 1 (BSN.w_sub_half_mk qz446 Bool.false 138478 1000 2 qz447 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7000 4000) qz484 Bool.false 7000 4000 0 1 Bool.false 276956 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 7000 4000) (Enclosure.Real.IsNear.const Bool.false 276956 4000)))

noncomputable def ep1292 := @ep1275 69239000013602901657 392926000000000000000000 ep1276 111570536205403164883 1125899906842624000 70114000017728624657 392926000000000000000000 (@ep1277 66803342395007043 9007199254740992 875000004125723 392926000000000000000 (ep1278 qz194) ep1288 rfl) (@ep1289 59960477002389522629 562949953421312000 69239000013602901657 392926000000000000000000 (ep1290 qz194) ep1291 rfl) rfl

noncomputable def ep1293 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz190 qz193) (@HMul.hMul Real Real Real qz0 qz192 qz191) 6061949753993077 2251799813685248 7000000001375241 1571704000000000000000 660770946298270378611 2251799813685248000

noncomputable def ep1294 := nat_lit 1501574191089681195925605029173526528

noncomputable def ep1295 := @Enclosure.Real.IsNear.mulLit_ff qz190 qz193 7000 4000 0 1 865992821999011 562949953421312 1000000000196463 392926000000000000000

noncomputable def ep1296 := @Enclosure.Real.IsNear.mulLit_ff qz192 qz191 276956 4000 0 1 9543334627858149 2251799813685248 125000000589389 98231500000000000000

noncomputable def ep1297 := @ep1293 8654875040808704971 98231500000000000000000 ep1294 666832896052263455611 2251799813685248000 18184750081789315067 196463000000000000000000 (@ep1295 6061949753993077 2251799813685248 7000000001375241 1571704000000000000000 (ep1278 qz194) ep1291 rfl) (@ep1296 660770946298270378611 2251799813685248000 8654875040808704971 98231500000000000000000 (ep1290 qz194) ep1288 rfl) rfl

noncomputable def ep1298 := @Enclosure.Complex.IsNear.of_eq qz186 qz487 Bool.false 9000 4000 0 1 Bool.false 276956 4000 0 1 (BSN.w_shift_mk qz146 Bool.false 138478 1000 2 qz147 rfl)

noncomputable abbrev qz489 := (ep1298 (@Enclosure.Complex.IsNear.mk qz651 qz701 Bool.false 9000 4000 0 1 Bool.false 276956 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 9000 4000) (Enclosure.Real.IsNear.const Bool.false 276956 4000)))

noncomputable abbrev qz195 := qz489

noncomputable def ep1299 := ep1273 (@ep1274 196463000000000000000000 (ep1292 rfl) (ep1297 rfl)) qz195 rfl rfl rfl rfl rfl rfl

noncomputable def ep1300 := @ep1270 18184750081789315067 196463000000000000000000 (ep1299 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@Enclosure.Complex.IsNear.mul qz101 (↑qz2) Bool.false 120447 131072 1 524288 Bool.false 0 1 0 1 (@ep600 131072 1 524288 (ep602 rfl) (ep604 rfl) rfl rfl) (@ep605 1 0 1 (ep607 rfl) (ep609 rfl) rfl rfl))

noncomputable abbrev qz490 := (@HPow.hPow Complex Int Complex qz649 qz699 (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) (@OfNat.ofNat Int 1 (@instOfNat 1)) (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (@OfNat.ofNat Int 2 (@instOfNat 2)) (@Nat.cast Int instNatCastInt 1))))

noncomputable abbrev qz196 := qz490

noncomputable def ep1301 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz84 2 k))) (@HMul.hMul Complex Complex Complex qz76 (@HMul.hMul Complex Complex Complex qz76 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz77 (@HMul.hMul Complex Complex Complex qz76 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz85 qz186 (@HSub.hSub Int Int Int qz403 qz87 (@HMul.hMul Int Int Int qz404 qz88 (@Nat.cast Int instNatCastInt k))))) (@HAdd.hAdd Complex Complex Complex qz4 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz84 2 k))) (@HMul.hMul Complex Complex Complex qz76 (@HMul.hMul Complex Complex Complex qz76 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz77 (@HMul.hMul Complex Complex Complex qz76 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz85 qz186 (@HSub.hSub Int Int Int qz403 qz87 (@HMul.hMul Int Int Int qz404 qz88 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 (@Rat.cast Complex Complex.instRatCast (bernoulli qz103)) qz104) qz196)) Bool.false 2684859 68719476736 3 68719476736

noncomputable def ep1302 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz84 2 k))) (@HMul.hMul Complex Complex Complex qz76 (@HMul.hMul Complex Complex Complex qz76 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz77 (@HMul.hMul Complex Complex Complex qz76 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz85 qz186 (@HSub.hSub Int Int Int qz403 qz87 (@HMul.hMul Int Int Int qz404 qz88 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 (@Rat.cast Complex Complex.instRatCast (bernoulli qz103)) qz104) qz196) Bool.false 0 1 0 1 Bool.false

noncomputable def ep1303 := @ep1302 0 1 0 1 Bool.false 2684859 68719476736 3 68719476736 Bool.true 61965650767 51539607552000 69239 51539607552000 Bool.false 2684859 2684859 68719476736 3 68719476736 Bool.true 61965650767 61965650767 51539607552000 69239

noncomputable def ep1304 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz84 2 k))) (@HMul.hMul Complex Complex Complex qz76 (@HMul.hMul Complex Complex Complex qz76 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz77 (@HMul.hMul Complex Complex Complex qz76 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz85 qz186 (@HSub.hSub Int Int Int qz403 qz87 (@HMul.hMul Int Int Int qz404 qz88 (@Nat.cast Int instNatCastInt k))))) (Complex.mk qz10 qz10) Bool.false 0 1 0 1 Bool.false

noncomputable def ep1305 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz83 (@Rat.cast Complex Complex.instRatCast (bernoulli qz103)) qz104) qz196 Bool.false 2684859 68719476736 3 68719476736 Bool.true 61965650767 51539607552000 69239 51539607552000

noncomputable abbrev qz197 := (Complex.re qz490)

noncomputable abbrev qz198 := (Complex.im qz490)

noncomputable def ep1306 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz83 (@Rat.cast Complex Complex.instRatCast (bernoulli qz103)) qz104)) qz197) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz83 (@Rat.cast Complex Complex.instRatCast (bernoulli qz103)) qz104)) qz198) 2684859 68719476736 3 68719476736 0 1 0

noncomputable def ep1307 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz83 (@Rat.cast Complex Complex.instRatCast (bernoulli qz103)) qz104)) qz197 1 12 0 1 8054577 17179869184 9 17179869184 2684859

noncomputable def ep1308 := @Enclosure.Complex.IsNear.re_isNear qz196 Bool.false 8054577 17179869184 9 17179869184 Bool.true 61965650767 4294967296000 69239 4294967296000

noncomputable abbrev qz491 := (@HPow.hPow Complex Nat Complex qz654 qz699 1)

noncomputable abbrev qz199 := (@Inv.inv Complex Complex.instInv qz491)

noncomputable def ep1309 := @Enclosure.Complex.IsNear.of_eq qz196 qz199 Bool.false 8054577 17179869184 9 17179869184 Bool.true 61965650767 4294967296000 69239

noncomputable def ep1310 := @Enclosure.Complex.IsNear.of_parts qz199 Bool.false 8054577 17179869184 9 17179869184 Bool.true 61965650767 4294967296000 69239

noncomputable abbrev qz200 := (Complex.re qz491)

noncomputable abbrev qz201 := qz491

noncomputable def ep1311 := @Enclosure.Real.IsNear.mulLit_ff qz200 (@Inv.inv Real Real.instInv (@DFunLike.coe qz110 Complex (fun (x : Complex) => Real) qz111 Complex.normSq qz201)) 9000 4000 0 1 894953 4294967296 1 4294967296

noncomputable def ep1312 := @Enclosure.Complex.IsNear.re_isNear qz201 Bool.false 9000 4000 0 1 Bool.false 276956 4000 0 1

noncomputable def ep1313 := @Enclosure.Complex.IsNear.of_eq qz201 qz186 Bool.false 9000 4000 0 1 Bool.false 276956 4000 0

noncomputable def ep1314 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (@DFunLike.coe qz110 Complex (fun (x : Complex) => Real) qz111 Complex.normSq qz201)) Bool.false 894953 4294967296 1 4294967296 894953 4294967296 1

noncomputable abbrev qz202 := (Complex.im qz491)

noncomputable def ep1315 := @Enclosure.Real.IsNear.of_eq (@DFunLike.coe qz110 Complex (fun (x : Complex) => Real) qz111 Complex.normSq qz201) (@HAdd.hAdd Real Real Real qz416 (@HMul.hMul Real Real Real qz0 qz200 qz200) (@HMul.hMul Real Real Real qz0 qz202 qz202)) Bool.false 4799101621 1000000 0 1

noncomputable def ep1316 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz200 qz200) (@HMul.hMul Real Real Real qz0 qz202 qz202) 81 16 0 1 4794039121 1000000

noncomputable def ep1317 := @Enclosure.Real.IsNear.mulLit_ff qz200 qz200 9000 4000 0 1 9000 4000 0 1

noncomputable def ep1318 := @Enclosure.Real.IsNear.mulLit_ff qz202 qz202 276956 4000 0 1 276956 4000 0 1

noncomputable def ep1319 := @Enclosure.Complex.IsNear.im_isNear qz201 Bool.false 9000 4000 0 1 Bool.false 276956 4000 0 1

noncomputable abbrev qz203 := (ep1312 (@ep1313 1 (BSN.pow_one_c qz479) qz489))

noncomputable abbrev qz204 := (ep1319 (@ep1313 1 (BSN.pow_one_c qz479) qz489))

noncomputable def ep1320 := @ep1316 0 1 76785625936 4799101621 1000000 0 1 (@ep1317 81 16 0 1 qz203 qz203 rfl) (@ep1318 4794039121 1000000 0 1 qz204 qz204 rfl)

noncomputable def ep1321 := @Enclosure.Real.IsNear.inv_image (@DFunLike.coe qz110 Complex (fun (x : Complex) => Real) qz111 Complex.normSq qz201) 4799101621 1000000 0 1 447476 447477 2147483648 (ep1315 (Enclosure.Complex.normSq_eq_mul_add_mul qz201) (ep1320 rfl rfl)) rfl

noncomputable def ep1322 := @Enclosure.Real.IsNear.of_eq (Complex.re qz199) (@HMul.hMul Real Real Real qz0 qz200 (@Inv.inv Real Real.instInv (@DFunLike.coe qz110 Complex (fun (x : Complex) => Real) qz111 Complex.normSq qz201))) Bool.false 8054577 17179869184 9 17179869184 (Enclosure.Complex.inv_re_eq_mul qz201) (@ep1311 8054577 17179869184 9 17179869184 qz203 (@ep1314 4294967296 (ep1321 rfl rfl rfl rfl rfl) rfl) rfl)

noncomputable def ep1323 := @Enclosure.Real.IsNear.of_eq (Complex.im qz199) (@HMul.hMul Real Real Real qz0 (@Neg.neg Real Real.instNeg qz202) (@Inv.inv Real Real.instInv (@DFunLike.coe qz110 Complex (fun (x : Complex) => Real) qz111 Complex.normSq qz201))) Bool.true 61965650767 4294967296000 69239 4294967296000 (Enclosure.Complex.inv_im_eq_mul qz201)

noncomputable def ep1324 := @Enclosure.Real.IsNear.mulLit_tf (@Neg.neg Real Real.instNeg qz202) (@Inv.inv Real Real.instInv (@DFunLike.coe qz110 Complex (fun (x : Complex) => Real) qz111 Complex.normSq qz201)) 276956 4000 0 1 894953 4294967296 1

noncomputable def ep1325 := @ep1324 4294967296 61965650767 4294967296000 69239 4294967296000 (@Enclosure.Real.IsNear.neg qz202 Bool.false 276956 4000 0 1 qz204) (@ep1314 4294967296 (ep1321 rfl rfl rfl rfl rfl) rfl) rfl

noncomputable def ep1326 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz83 (@Rat.cast Complex Complex.instRatCast (bernoulli qz103)) qz104)) qz198 0 1 0 1 61965650767 4294967296000 69239 4294967296000 0

noncomputable def ep1327 := @Enclosure.Complex.IsNear.im_isNear qz196 Bool.false 8054577 17179869184 9 17179869184 Bool.true 61965650767 4294967296000 69239 4294967296000

noncomputable abbrev qz205 := (@ep1309 4294967296000 (BSN.zpow_one_sub_two_mul qz479 1 1 rfl rfl) (@ep1310 4294967296000 ep1322 (ep1323 ep1325)))

noncomputable def ep1328 := @ep1306 1 2684859 2684859 68719476736 3 68719476736 (@ep1307 68719476736 3 68719476736 ep619 (ep1308 qz205) rfl) (@ep1326 1 0 1 ep639 (ep1327 qz205) rfl) rfl

noncomputable def ep1329 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz83 (@Rat.cast Complex Complex.instRatCast (bernoulli qz103)) qz104)) qz198) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz83 (@Rat.cast Complex Complex.instRatCast (bernoulli qz103)) qz104)) qz197) 61965650767 51539607552000 69239 51539607552000 0 1 0

noncomputable def ep1330 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HDiv.hDiv Complex Complex Complex qz83 (@Rat.cast Complex Complex.instRatCast (bernoulli qz103)) qz104)) qz198 1 12 0 1 61965650767 4294967296000 69239 4294967296000 61965650767

noncomputable def ep1331 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz83 (@Rat.cast Complex Complex.instRatCast (bernoulli qz103)) qz104)) qz197 0 1 0 1 8054577 17179869184 9 17179869184 0

noncomputable def ep1332 := @ep1329 1 61965650767 61965650767 51539607552000 69239 51539607552000 (@ep1330 51539607552000 69239 51539607552000 ep619 (ep1327 qz205) rfl) (@ep1331 1 0 1 ep639 (ep1308 qz205) rfl) rfl

noncomputable def ep1333 := @ep1303 51539607552000 (@ep1304 0 1 0 1 (BSN.stirling_sum_base qz186) qz117) (ep1305 (ep1328 rfl) (ep1332 rfl)) rfl rfl rfl rfl rfl

noncomputable def ep1334 := @ep1267 1532753464295754375793 6755399441055744000 ep1259 ep550 (ep1300 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep1301 Bool.true 61965650767 51539607552000 69239 51539607552000 (BSN.stirling_sum_succ qz186 0 1 rfl) (ep1333 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl

noncomputable def ep1335 := @Enclosure.Complex.IsNear.of_eq (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz183 (@Nat.cast Complex Complex.instNatCast j))) (BSN.logSumC qz146 2) Bool.false 9542337121703653 1125899906842624 125000000589389 49115750000000000000 Bool.false 878182476055971 281474976710656

noncomputable abbrev qz206 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz272 qz480 qz412))

noncomputable def ep1336 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz146 2) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.logSumC qz146 1) qz206) Bool.false 9542337121703653 1125899906842624 125000000589389 49115750000000000000 Bool.false 878182476055971 281474976710656 1000000000196463 196463000000000000000

noncomputable def ep1337 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz146 1) qz206 Bool.false 9542161028044517 2251799813685248 125000000589389 98231500000000000000 Bool.false 882247125730723 562949953421312 1000000000196463 392926000000000000000 Bool.false

noncomputable def ep1338 := nat_lit 42974865905548222989580147621888

noncomputable def ep1339 := nat_lit 988745567982242630342912507904

noncomputable abbrev qz207 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz272 qz480 (@Nat.cast Complex Complex.instNatCast 0)))

noncomputable def ep1340 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz146 1) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.logSumC qz146 0) qz207) Bool.false 9542161028044517 2251799813685248 125000000589389 98231500000000000000 Bool.false 882247125730723 562949953421312 1000000000196463 392926000000000000000

noncomputable def ep1341 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz146 0) qz207 Bool.false 0 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable abbrev qz492 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz701))

noncomputable def ep1342 := @Enclosure.Complex.IsNear.of_eq qz207 qz492 Bool.false 9542161028044517 2251799813685248 125000000589389 98231500000000000000 Bool.false 882247125730723 562949953421312 1000000000196463 392926000000000000000

noncomputable def ep1343 := nat_lit 6140420190125668921255760989378394480523018240

noncomputable def ep1344 := nat_lit 12667896443958242078748252052585775041609728

noncomputable def ep1345 := nat_lit 46695579680797011432370952450924520603648

noncomputable def ep1346 := BSN.log_dyadic_bound 11169625936 142241625936 3 2 ep1343 1048576 392926 ep1344 ep1345 165020 153411251872 131072000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 11169625936) (BSN.artanhQ 142241625936) 0 2 ep1344 ep1343 ep1345 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep1347 := @Enclosure.Real.IsNear.mulLit_ff qz96 (Real.log (Enclosure.sfrac Bool.false 76705625936 16000000)) 1 2 0 1 9542161028044517 1125899906842624 125000000589389 49115750000000000000 9542161028044517 2251799813685248 125000000589389 98231500000000000000 qz407 (BSN.isNear_log_sfrac 76705625936 16000000 9542161028044517 1125899906842624 125000000589389 49115750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 76705625936) qz653)) Bool.false 320181793348569838649344 37778931862957161709568 1000000004715112 392926000000000000000 9542161028044517 1125899906842624 125000000589389 49115750000000000000 (BSN.log_rat_reduce_isNear 76705625936 16000000 12 153411251872 131072000000 165020 1048576 24973259072661432 36028797018963968 392926 1000000000000000 rfl rfl rfl rfl (ep1346 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1348 := BSN.arctan_dyadic_bound_f 1000 276956 1 0 1048576 392926 0 1 1 0 1 1 3786 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 276956) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 276956) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz493 := (@Nat.cast Real Real.instNatCast 276956)

noncomputable def ep1349 := @Enclosure.Real.IsNear.subLit_ff_p qz97 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz418 qz493)) 884279719003555 562949953421312 1 2000000000000000 3786 1048576 1 392926 925103162110218600448 882247125730723 562949953421312 1000000000196463 392926000000000000000 qz98 (ep1348 rfl) rfl rfl

noncomputable abbrev qz208 := (@HAdd.hAdd Complex Complex Complex qz272 qz480 (@Nat.cast Complex Complex.instNatCast 0))

noncomputable abbrev qz494 := (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz701)

noncomputable def ep1350 := @ep1341 9542161028044517 2251799813685248 125000000589389 98231500000000000000 Bool.false 882247125730723 562949953421312 1000000000196463 392926000000000000000 Bool.false 9542161028044517 9542161028044517 2251799813685248 125000000589389 98231500000000000000 Bool.false 882247125730723 882247125730723 562949953421312 1000000000196463 392926000000000000000 (@Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz146 0) (Complex.mk qz10 qz10) Bool.false 0 1 0 1 Bool.false 0 1 0 1 (BSN.log_sum_c_base qz146) qz117) (ep1342 (@congrArg Complex Complex qz208 qz494 Complex.log (BSN.w_shift_mk qz146 Bool.false 138478 1000 0 qz147 rfl)) (@Enclosure.Complex.IsNear.of_parts qz492 Bool.false 9542161028044517 2251799813685248 125000000589389 98231500000000000000 Bool.false 882247125730723 562949953421312 1000000000196463 392926000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz492) (@HMul.hMul Real Real Real qz0 qz96 (Real.log (Enclosure.sfrac Bool.false 76705625936 16000000))) Bool.false 9542161028044517 2251799813685248 125000000589389 98231500000000000000 (Enclosure.clog_re_eq 1000 276956 4000 76705625936 16000000 rfl rfl rfl) (ep1347 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz492) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz493 qz418)) Bool.false 882247125730723 562949953421312 1000000000196463 392926000000000000000 (Enclosure.clog_im_eq 1000 276956 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz493 qz418)) (@HSub.hSub Real Real Real qz396 qz97 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz418 qz493))) Bool.false 882247125730723 562949953421312 1000000000196463 392926000000000000000 (BSN.arctan_recip 276956 1000 rfl rfl) ep1349)))) rfl rfl

noncomputable abbrev qz495 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz701))

noncomputable def ep1351 := @Enclosure.Complex.IsNear.of_eq qz206 qz495 Bool.false 9542513215362789 2251799813685248 125000000589389 98231500000000000000 Bool.false 874117826381219 562949953421312 1000000000196463 392926000000000000000

noncomputable def ep1352 := nat_lit 6144565457328645679243159064142591713163018240

noncomputable def ep1353 := nat_lit 12726873055780653826115451879549632449609728

noncomputable def ep1354 := nat_lit 47098211289686656771484061322371048603648

noncomputable def ep1355 := BSN.log_dyadic_bound 11193625936 142265625936 3 2 ep1352 1048576 392926 ep1353 ep1354 165348 153459251872 131072000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 11193625936) (BSN.artanhQ 142265625936) 0 2 ep1353 ep1352 ep1354 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep1356 := @Enclosure.Real.IsNear.mulLit_ff qz96 (Real.log (Enclosure.sfrac Bool.false 76729625936 16000000)) 1 2 0 1 9542513215362789 1125899906842624 125000000589389 49115750000000000000 9542513215362789 2251799813685248 125000000589389 98231500000000000000 qz407 (BSN.isNear_log_sfrac 76729625936 16000000 9542513215362789 1125899906842624 125000000589389 49115750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 76729625936) qz653)) Bool.false 320193610793992058830848 37778931862957161709568 1000000004715112 392926000000000000000 9542513215362789 1125899906842624 125000000589389 49115750000000000000 (BSN.log_rat_reduce_isNear 76729625936 16000000 12 153459251872 131072000000 165348 1048576 24973259072661432 36028797018963968 392926 1000000000000000 rfl rfl rfl rfl (ep1355 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1357 := BSN.arctan_dyadic_bound_f 5000 276956 1 0 1048576 392926 0 1 1 0 1 1 18928 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 5000) (BSN.arctanEvenQ 276956) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 5000) (BSN.arctanOddQ 276956) 0 0 rfl) rfl rfl rfl

noncomputable def ep1358 := @Enclosure.Real.IsNear.subLit_ff_p qz97 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz422 qz493)) 884279719003555 562949953421312 1 2000000000000000 18928 1048576 1 392926 916578973915513094144 874117826381219 562949953421312 1000000000196463 392926000000000000000 qz98 (ep1357 rfl) rfl rfl

noncomputable abbrev qz209 := (@HAdd.hAdd Complex Complex Complex qz272 qz480 qz412)

noncomputable abbrev qz496 := (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz701)

noncomputable def ep1359 := @ep1337 9542513215362789 2251799813685248 125000000589389 98231500000000000000 Bool.false 874117826381219 562949953421312 1000000000196463 392926000000000000000 Bool.false ep1338 9542337121703653 1125899906842624 125000000589389 49115750000000000000 Bool.false ep1339 878182476055971 281474976710656 1000000000196463 196463000000000000000 (ep1340 (BSN.log_sum_c_succ qz146 0 1 rfl) (ep1350 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1351 (@congrArg Complex Complex qz209 qz496 Complex.log (BSN.w_shift_mk qz146 Bool.false 138478 1000 1 qz147 rfl)) (@Enclosure.Complex.IsNear.of_parts qz495 Bool.false 9542513215362789 2251799813685248 125000000589389 98231500000000000000 Bool.false 874117826381219 562949953421312 1000000000196463 392926000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz495) (@HMul.hMul Real Real Real qz0 qz96 (Real.log (Enclosure.sfrac Bool.false 76729625936 16000000))) Bool.false 9542513215362789 2251799813685248 125000000589389 98231500000000000000 (Enclosure.clog_re_eq 5000 276956 4000 76729625936 16000000 rfl rfl rfl) (ep1356 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz495) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz493 qz422)) Bool.false 874117826381219 562949953421312 1000000000196463 392926000000000000000 (Enclosure.clog_im_eq 5000 276956 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz493 qz422)) (@HSub.hSub Real Real Real qz396 qz97 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz422 qz493))) Bool.false 874117826381219 562949953421312 1000000000196463 392926000000000000000 (BSN.arctan_recip 276956 5000 rfl rfl) ep1358)))) rfl rfl

noncomputable def ep1360 := @ep1260 ep550 Bool.false 9542337121703653 1125899906842624 125000000589389 49115750000000000000 Bool.false 878182476055971 281474976710656 1000000000196463 196463000000000000000 Bool.true ep1261 122611472276970241883 1125899906842624000 ep1256 ep556 Bool.false ep1262 1511677084870411071793 6755399441055744000 ep1253 ep550 (@ep1263 1125899906842624000 ep1258 ep556 Bool.false 1532753464295754375793 6755399441055744000 ep1259 ep550 (BSN.logGammaStirling_unfold 1 qz186) (ep1334 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (@ep1335 1000000000196463 196463000000000000000 (BSN.log_sum_c_eq qz146 2) (ep1336 (BSN.log_sum_c_succ qz146 1 2 rfl) (ep1359 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)))

noncomputable abbrev qz210 := (@HDiv.hDiv Real Real Real qz270 qz446 (2 : Real))

noncomputable def ep1361 := @Enclosure.Real.IsNear.mulLit_ff qz210 (Real.log Real.pi) 138478 2000 0 1 75021 65536 1 262144 5194379019 65536000 69239 262144000 (@Enclosure.Real.IsNear.of_eq qz210 (Enclosure.sfrac Bool.false 138478 2000) Bool.false 138478 2000 0 1 (BSN.t_half_eq qz146 Bool.false 138478 1000 qz147) (Enclosure.Real.IsNear.const Bool.false 138478 2000)) EMRow47.d5 rfl

noncomputable def ep1362 := @ep1254 69239 262144000 ep1255 976244572639205568817 6755399441055744000 ep1251 ep550 (@ep1257 ep1253 ep550 (ep1360 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) ep1361 rfl rfl

noncomputable def ep1363 := nat_lit 8343231273428118467932459542611816567149722528482396249785251209208860551840000

noncomputable def ep1364 := nat_lit 16761747552813805560721483816730768297692462794698407414442072874000100000000

noncomputable def ep1365 := nat_lit 21824181934369087921296225923518145955767295015786287994576085048989110807200000

noncomputable def ep1366 := BSN.sin_dyadic_bound_f 3373183070 2147483648 3 2 1048576 393310 ep1363 ep109 ep1364 ep1365 ep112 ep1364 1048575 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3373183070) qz19 0 2 ep1363 ep109 ep1364 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3373183070) qz20 0 2 ep1365 ep112 ep1364 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1367 := @ep1250 262144 Bool.false 1048575 1048576 1 196463 (@ep1252 151533101 1048576 95 262144 ep1362 rfl) (Enclosure.sfrac_false_div 151533101 1048576) (BSN.cos_reduce3 qz481 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 237366656525988677025792) qz31) 226375608064910080 72057594037927936 Bool.false 1048575 1048576 22 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q3 151533101 1048576 226375608064910080 72057594037927936 22 237366656525988677025792 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1048575 1048576 237366656525988677025792 151115727451828646838272 3373183070 2147483648 393310 392926 (ep1366 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1368 := nat_lit 4435660208234945266798001

noncomputable def ep1369 := nat_lit 276736450044036686807040000

noncomputable def ep1370 := nat_lit 363865674491378847660706392359

noncomputable def ep1371 := nat_lit 54368473185001579600171499520000

noncomputable abbrev qz497 := (@HPow.hPow Complex Complex Complex qz535 qz655 qz667)

noncomputable abbrev qz211 := qz497

noncomputable abbrev qz212 := (@HAdd.hAdd Complex Complex Complex qz272 (@HDiv.hDiv Complex Complex Complex qz401 qz425 (@HSub.hSub Complex Complex Complex qz393 qz444 (1 : Complex))) qz400)

noncomputable def ep1372 := @Enclosure.Complex.IsNear.of_eq (zetaApproximant qz143 1 35) (@HAdd.hAdd Complex Complex Complex qz4 (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 35, @HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast n) qz144) (@HMul.hMul Complex Complex Complex qz76 qz211 (@HAdd.hAdd Complex Complex Complex qz4 qz212 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz76 (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz84 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz84 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz84 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz126 qz127 (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz84 2 k) 1))))))) Bool.false ep1245 ep1246 ep1247

noncomputable def ep1373 := @Enclosure.Complex.IsNear.addLitP (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 35, @HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast n) qz144) (@HMul.hMul Complex Complex Complex qz76 qz211 (@HAdd.hAdd Complex Complex Complex qz4 qz212 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz76 (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz84 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz84 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz84 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz126 qz127 (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz84 2 k) 1)))))) Bool.false 995626035037 1099511627776 1430808143469969 216013352927756288

noncomputable def ep1374 := nat_lit 9500816563844814193814441

noncomputable def ep1375 := nat_lit 15160439027242679141052730693

noncomputable def ep1376 := nat_lit 20482837130446027177224499

noncomputable def ep1377 := nat_lit 3793434391929070815750889859

noncomputable def ep1378 := nat_lit 209974553320733061742190336984202870784

noncomputable def ep1379 := nat_lit 4877059975817635790143336686892875776

noncomputable def ep1380 := @ep1373 Bool.false 99004585649 1099511627776 1430616078097761 216013352927756288 Bool.true ep1374 ep1246 ep1375 ep1248 Bool.true ep1376 ep1369 ep1377 ep1371 Bool.false ep1378 ep1245 ep1246 ep1247 ep1248 Bool.false ep1379 ep1368 ep1369

noncomputable def ep1381 := @Enclosure.Complex.IsNear.of_eq (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 35, @HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast n) qz144) (BSN.headSumC qz143 35) Bool.false 995626035037 1099511627776 1430808143469969 216013352927756288 Bool.false 99004585649 1099511627776 1430616078097761

noncomputable abbrev qz703 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 34) qz144)

noncomputable def ep1382 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz143 35) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz143 34) qz703) Bool.false 995626035037 1099511627776 1430808143469969 216013352927756288 Bool.false 99004585649 1099511627776 1430616078097761 216013352927756288

noncomputable def ep1383 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz143 34) qz703 Bool.false 129009019787 137438953472 702200137099663 108006676463878144 Bool.true 43002014519 549755813888 702022952228001 108006676463878144 Bool.true

noncomputable abbrev qz704 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 33) qz144)

noncomputable def ep1384 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz143 34) (@HAdd.hAdd Complex Complex Complex qz4 qz173 qz704) Bool.false 129009019787 137438953472 702200137099663 108006676463878144 Bool.true 43002014519 549755813888 702022952228001 108006676463878144

noncomputable def ep1385 := @Enclosure.Complex.IsNear.addLitP qz173 qz704 Bool.false 106826879495 137438953472 688740301255883 108006676463878144 Bool.true 14291011597 1099511627776 1377240046731287 216013352927756288 Bool.false

noncomputable abbrev qz213 := (@HMul.hMul Real Real Real qz267 qz446 qz658)

noncomputable def ep1386 := @Enclosure.Complex.IsNear.of_eq qz704 (Complex.mk (@HMul.hMul Real Real Real qz0 qz427 (Real.cos qz213)) (@HMul.hMul Real Real Real qz0 qz427 (@Neg.neg Real Real.instNeg (Real.sin qz213)))) Bool.false 5545535073 34359738368 3364958960945 27001669115969536 Bool.true 71713017441 1099511627776 26805857724715 216013352927756288 (BSN.cpow_neg_s_mk qz146 138478 1000 33 qz147 rfl)

noncomputable def ep1387 := @Enclosure.Real.IsNear.mulLit_ff qz146 qz658 138478 1000 0 1 15746868335186131 4503599627370496 200000000196463 39292600000000000000 1090297416659952524309 2251799813685248000 13847800013602901657 19646300000000000000000 qz148 (BSN.isNear_log_sfrac 33 1 15746868335186131 4503599627370496 200000000196463 39292600000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz659) Bool.false 66047152845744529997824 18889465931478580854784 1000000000982315 196463000000000000000 15746868335186131 4503599627370496 200000000196463 39292600000000000000 (BSN.log_rat_reduce_isNear 33 1 5 66 64 16133 524288 24973259072661432 36028797018963968 196463 1000000000000000 rfl rfl rfl rfl (ep698 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1388 := nat_lit 462664569859208244172870939963650625

noncomputable def ep1389 := BSN.cos_dyadic_bound_f 824739055 2147483648 2 1 1048576 393310 ep1388 ep61 ep1388 ep1388 ep62 ep1388 972192 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 824739055) qz15 0 1 ep1388 ep61 ep1388 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 824739055) qz16 0 1 ep1388 ep62 ep1388 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz498 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 253854649) qz23)

noncomputable def ep1390 := @Enclosure.Real.IsNear.cos_image qz213 qz498 Bool.false 253854649 524288 185 262144 Bool.false 972192 1048576 1 196463 (@Enclosure.Real.IsNear.recentre' qz213 Bool.false 1090297416659952524309 2251799813685248000 13847800013602901657 19646300000000000000000 253854649 524288 185 262144 (ep1387 rfl) rfl) (Enclosure.sfrac_false_div 253854649 524288) (BSN.cos_reduce0 qz498 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 29017925815620346052608) qz24) 226375608064910080 72057594037927936 Bool.false 972192 1048576 77 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q0 253854649 524288 226375608064910080 72057594037927936 77 29017925815620346052608 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 972192 1048576 29017925815620346052608 75557863725914323419136 824739055 2147483648 393310 392926 (ep1389 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1391 := BSN.sin_dyadic_bound_f 824739055 2147483648 2 1 1048576 393310 ep1388 ep65 ep1388 ep1388 ep66 ep1388 392877 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 824739055) qz19 0 1 ep1388 ep65 ep1388 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 824739055) qz20 0 1 ep1388 ep66 ep1388 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1392 := @Enclosure.Real.IsNear.sin_image qz213 qz498 Bool.false 253854649 524288 185 262144 Bool.false 392877 1048576 1 196463 (@Enclosure.Real.IsNear.recentre' qz213 Bool.false 1090297416659952524309 2251799813685248000 13847800013602901657 19646300000000000000000 253854649 524288 185 262144 (ep1387 rfl) rfl) (Enclosure.sfrac_false_div 253854649 524288) (BSN.sin_reduce0 qz498 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 29017925815620346052608) qz24) 226375608064910080 72057594037927936 Bool.false 392877 1048576 77 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q0 253854649 524288 226375608064910080 72057594037927936 77 29017925815620346052608 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 392877 1048576 29017925815620346052608 75557863725914323419136 824739055 2147483648 393310 392926 (ep1391 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1393 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz427 (Real.cos qz213)) (@HMul.hMul Real Real Real qz0 qz427 (@Neg.neg Real Real.instNeg (Real.sin qz213))) Bool.false 5545535073 34359738368 3364958960945 27001669115969536 Bool.true 71713017441 1099511627776 26805857724715 216013352927756288 (@Enclosure.Real.IsNear.mulLit_ff qz427 (Real.cos qz213) 182533 1048576 1 1048576 30381 32768 36607799 51501596672 5545535073 34359738368 3364958960945 27001669115969536 qz431 (@Enclosure.Real.IsNear.recentre' (Real.cos qz213) Bool.false 972192 1048576 36607799 51501596672 30381 32768 36607799 51501596672 (ep1390 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz427 (@Neg.neg Real Real.instNeg (Real.sin qz213)) 182533 1048576 1 1048576 392877 1048576 36607799 51501596672 71713017441 1099511627776 26805857724715 216013352927756288 qz431 (@Enclosure.Real.IsNear.neg (Real.sin qz213) Bool.false 392877 1048576 36607799 51501596672 (@Enclosure.Real.IsNear.recentre' (Real.sin qz213) Bool.false 392877 1048576 36607799 51501596672 392877 1048576 36607799 51501596672 (ep1392 rfl rfl) rfl)) rfl)

noncomputable def ep1394 := @ep1385 5545535073 34359738368 3364958960945 27001669115969536 Bool.true 71713017441 1099511627776 26805857724715 216013352927756288 Bool.false 4432716166993455087616 129009019787 137438953472 702200137099663 108006676463878144 Bool.true 94562429962865751359488 43002014519 549755813888 702022952228001 108006676463878144 EMRow47.d16 (ep1386 ep1393) rfl rfl

noncomputable abbrev qz214 := (@HMul.hMul Real Real Real qz267 qz446 qz660)

noncomputable def ep1395 := @Enclosure.Complex.IsNear.of_eq qz703 (Complex.mk (@HMul.hMul Real Real Real qz0 qz432 (Real.cos qz214)) (@HMul.hMul Real Real Real qz0 qz432 (@Neg.neg Real Real.instNeg (Real.sin qz214)))) Bool.true 36446123259 1099511627776 26407869270643 216013352927756288 Bool.false 185008614687 1099511627776 26570173641759 216013352927756288 (BSN.cpow_neg_s_mk qz146 138478 1000 34 qz147 rfl)

noncomputable def ep1396 := @Enclosure.Real.IsNear.mulLit_ff qz146 qz660 138478 1000 0 1 15881309401485523 4503599627370496 200000000196463 39292600000000000000 1099605981649456126997 2251799813685248000 13847800013602901657 19646300000000000000000 qz148 (BSN.isNear_log_sfrac 34 1 15881309401485523 4503599627370496 200000000196463 39292600000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz661) Bool.false 66611039547888335060992 18889465931478580854784 1000000000982315 196463000000000000000 15881309401485523 4503599627370496 200000000196463 39292600000000000000 (BSN.log_rat_reduce_isNear 34 1 5 68 64 31784 524288 24973259072661432 36028797018963968 196463 1000000000000000 rfl rfl rfl rfl (ep713 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1397 := nat_lit 2732207548387064564019424342318660766216419327570822032107118132885886806065761

noncomputable def ep1398 := nat_lit 5822598755594298064797207192885076286421089850038273729142801077989400707681

noncomputable def ep1399 := nat_lit 8184977447650005095928678612570212146076415803012389548863068796501681616781921

noncomputable def ep1400 := BSN.cos_dyadic_bound_f 2955558827 2147483648 3 2 1048576 393310 ep1397 ep78 ep1398 ep1399 ep81 ep1398 202671 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2955558827) qz15 0 2 ep1397 ep78 ep1398 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2955558827) qz16 0 2 ep1399 ep81 ep1398 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz499 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 16001373) (@Nat.cast Real Real.instNatCast 32768))

noncomputable def ep1401 := @Enclosure.Real.IsNear.cos_image qz214 qz499 Bool.false 16001373 32768 741 1048576 Bool.true 202671 1048576 1 196463 (@Enclosure.Real.IsNear.recentre' qz214 Bool.false 1099605981649456126997 2251799813685248000 13847800013602901657 19646300000000000000000 16001373 32768 741 1048576 (ep1396 rfl) rfl) (Enclosure.sfrac_false_div 16001373 32768) (BSN.cos_reduce2 qz499 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 6499342594920316665856) qz690) 226375608064910080 72057594037927936 Bool.false 202671 1048576 77 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q2 16001373 32768 226375608064910080 72057594037927936 77 6499342594920316665856 4722366482869645213696 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 202671 1048576 6499342594920316665856 4722366482869645213696 2955558827 2147483648 393310 392926 (ep1400 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1402 := nat_lit 4913315508092240776783126050419281318160417917747449038809498398332204730352225

noncomputable def ep1403 := nat_lit 12858780218446811266136610844214399043099269924819447420368169365315220025967201

noncomputable def ep1404 := BSN.sin_dyadic_bound_f 2955558827 2147483648 3 2 1048576 393310 ep1402 ep109 ep1398 ep1403 ep112 ep1398 1028803 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2955558827) qz19 0 2 ep1402 ep109 ep1398 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2955558827) qz20 0 2 ep1403 ep112 ep1398 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1405 := @Enclosure.Real.IsNear.sin_image qz214 qz499 Bool.false 16001373 32768 741 1048576 Bool.true 1028803 1048576 1 196463 (@Enclosure.Real.IsNear.recentre' qz214 Bool.false 1099605981649456126997 2251799813685248000 13847800013602901657 19646300000000000000000 16001373 32768 741 1048576 (ep1396 rfl) rfl) (Enclosure.sfrac_false_div 16001373 32768) (BSN.sin_reduce2 qz499 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 6499342594920316665856) qz690) 226375608064910080 72057594037927936 Bool.false 1028803 1048576 77 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q2 16001373 32768 226375608064910080 72057594037927936 77 6499342594920316665856 4722366482869645213696 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1028803 1048576 6499342594920316665856 4722366482869645213696 2955558827 2147483648 393310 392926 (ep1404 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1406 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz432 (Real.cos qz214)) (@HMul.hMul Real Real Real qz0 qz432 (@Neg.neg Real Real.instNeg (Real.sin qz214))) Bool.true 36446123259 1099511627776 26407869270643 216013352927756288 Bool.false 185008614687 1099511627776 26570173641759 216013352927756288 (@Enclosure.Real.IsNear.mulLit_ft qz432 (Real.cos qz214) 179829 1048576 1 1048576 202671 1048576 146627659 206006386688 36446123259 1099511627776 26407869270643 216013352927756288 qz436 (@Enclosure.Real.IsNear.recentre' (Real.cos qz214) Bool.true 202671 1048576 146627659 206006386688 202671 1048576 146627659 206006386688 (ep1401 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz432 (@Neg.neg Real Real.instNeg (Real.sin qz214)) 179829 1048576 1 1048576 1028803 1048576 146627659 206006386688 185008614687 1099511627776 26570173641759 216013352927756288 qz436 (@Enclosure.Real.IsNear.neg (Real.sin qz214) Bool.true 1028803 1048576 146627659 206006386688 (@Enclosure.Real.IsNear.recentre' (Real.sin qz214) Bool.true 1028803 1048576 146627659 206006386688 1028803 1048576 146627659 206006386688 (ep1405 rfl rfl) rfl)) rfl)

noncomputable def ep1407 := @ep1383 36446123259 1099511627776 26407869270643 216013352927756288 Bool.false 185008614687 1099511627776 26570173641759 216013352927756288 Bool.false 136837800304962084798464 995626035037 1099511627776 1430808143469969 216013352927756288 Bool.false 54428346562110199693312 99004585649 1099511627776 1430616078097761 216013352927756288 (ep1384 (BSN.head_sum_c_succ qz143 33 34 rfl rfl) (ep1394 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1395 ep1406) rfl rfl

noncomputable def ep1408 := @Enclosure.Complex.IsNear.mul qz211 (@HAdd.hAdd Complex Complex Complex qz4 qz212 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz76 (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz84 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz84 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz84 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz126 qz127 (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz84 2 k) 1))))) Bool.true ep1374 ep1246 ep1375 ep1248 Bool.true

noncomputable def ep1409 := nat_lit 26273937000163979219456077

noncomputable abbrev qz215 := (Complex.re qz497)

noncomputable abbrev qz216 := (Complex.im qz497)

noncomputable def ep1410 := @Enclosure.Real.IsNear.subLit_tt_n (@HMul.hMul Real Real Real qz0 qz215 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz212 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz76 (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz84 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz84 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz84 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz126 qz127 (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz84 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz216 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz212 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz76 (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz84 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz84 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz84 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz126 qz127 (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz84 2 k) 1))))))) 39146008044714817930749 737963866784097831485440 ep1409

noncomputable def ep1411 := nat_lit 434947785480012636801371996160

noncomputable def ep1412 := nat_lit 2242985849569631185410259

noncomputable def ep1413 := nat_lit 2023470527160689531324692193

noncomputable def ep1414 := nat_lit 7011259329061324571570646389709649406822753239040

noncomputable def ep1415 := @Enclosure.Real.IsNear.mulLit_tf qz215 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz212 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz76 (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz84 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz84 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz84 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz126 qz127 (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz84 2 k) 1)))))) 58292260767 549755813888 13041493147397 108006676463878144 2014641782441

noncomputable abbrev qz217 := (@HMul.hMul Real Real Real qz267 qz446 qz662)

noncomputable abbrev qz218 := (Real.sin (@HMul.hMul Real Real Real qz267 qz446 qz662))

noncomputable abbrev qz705 := (@Neg.neg Real Real.instNeg qz218)

noncomputable def ep1416 := @Enclosure.Complex.IsNear.of_eq qz211 (Complex.mk (@HMul.hMul Real Real Real qz0 qz437 (Real.cos qz217)) (@HMul.hMul Real Real Real qz0 qz437 qz705)) Bool.true 58292260767 549755813888 13041493147397 108006676463878144 Bool.true 144735886805 1099511627776 26114190709547 216013352927756288 (BSN.cpow_neg_s_mk qz146 138478 1000 35 qz147 rfl)

noncomputable def ep1417 := @Enclosure.Real.IsNear.mulLit_ff qz146 qz134 138478 1000 0 1 16011859227414739 4503599627370496 200000000196463 39292600000000000000 1108645121046969113621 2251799813685248000 13847800013602901657 19646300000000000000000 qz148 (BSN.isNear_log_sfrac 35 1 16011859227414739 4503599627370496 200000000196463 39292600000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' qz440 Bool.false 67158605204982549446656 18889465931478580854784 1000000000982315 196463000000000000000 16011859227414739 4503599627370496 200000000196463 39292600000000000000 (BSN.log_rat_reduce_isNear 35 1 5 70 64 46982 524288 24973259072661432 36028797018963968 196463 1000000000000000 rfl rfl rfl rfl (ep733 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1418 := nat_lit 4496315523050965779592359663853561201

noncomputable def ep1419 := BSN.sin_dyadic_bound_f 1456177093 2147483648 2 1 1048576 393310 ep1418 ep65 ep1418 ep1418 ep66 ep1418 657774 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1456177093) qz19 0 1 ep1418 ep65 ep1418 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1456177093) qz20 0 1 ep1418 ep66 ep1418 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz500 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 258126557) qz23)

noncomputable def ep1420 := @Enclosure.Real.IsNear.cos_image qz217 qz500 Bool.false 258126557 524288 185 262144 Bool.true 657774 1048576 1 196463 (@Enclosure.Real.IsNear.recentre' qz217 Bool.false 1108645121046969113621 2251799813685248000 13847800013602901657 19646300000000000000000 258126557 524288 185 262144 (ep1417 rfl) rfl) (Enclosure.sfrac_false_div 258126557 524288) (BSN.cos_reduce1 qz500 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 51234676672695772381184) qz24) 226375608064910080 72057594037927936 Bool.false 657774 1048576 78 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q1 258126557 524288 226375608064910080 72057594037927936 78 51234676672695772381184 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 657774 1048576 51234676672695772381184 75557863725914323419136 1456177093 2147483648 393310 392926 (ep1419 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1421 := nat_lit 160671990157032537806509701239030563909724535431187939308476489479710411021281

noncomputable def ep1422 := nat_lit 20216853282829079980848444248257115438557485994426985178477037249852562401

noncomputable def ep1423 := nat_lit 481975536764531955259567406828595177498296491321574963955072514364631527939041

noncomputable def ep1424 := BSN.cos_dyadic_bound_f 1456177093 2147483648 3 2 1048576 393310 ep1421 ep78 ep1422 ep1423 ep81 ep1422 816605 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1456177093) qz15 0 2 ep1421 ep78 ep1422 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1456177093) qz16 0 2 ep1423 ep81 ep1422 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1425 := @Enclosure.Real.IsNear.sin_image qz217 qz500 Bool.false 258126557 524288 185 262144 Bool.false 816605 1048576 1 196463 (@Enclosure.Real.IsNear.recentre' qz217 Bool.false 1108645121046969113621 2251799813685248000 13847800013602901657 19646300000000000000000 258126557 524288 185 262144 (ep1417 rfl) rfl) (Enclosure.sfrac_false_div 258126557 524288) (BSN.sin_reduce1 qz500 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 51234676672695772381184) qz24) 226375608064910080 72057594037927936 Bool.false 816605 1048576 78 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q1 258126557 524288 226375608064910080 72057594037927936 78 51234676672695772381184 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 816605 1048576 51234676672695772381184 75557863725914323419136 1456177093 2147483648 393310 392926 (ep1424 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1426 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz437 (Real.cos qz217)) (@HMul.hMul Real Real Real qz0 qz437 qz705) Bool.true 58292260767 549755813888 13041493147397 108006676463878144 Bool.true 144735886805 1099511627776 26114190709547 216013352927756288 (@Enclosure.Real.IsNear.mulLit_ft qz437 (Real.cos qz217) 177241 1048576 1 1048576 328887 524288 36607799 51501596672 58292260767 549755813888 13041493147397 108006676463878144 qz442 (@Enclosure.Real.IsNear.recentre' (Real.cos qz217) Bool.true 657774 1048576 36607799 51501596672 328887 524288 36607799 51501596672 (ep1420 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz437 qz705 177241 1048576 1 1048576 816605 1048576 36607799 51501596672 144735886805 1099511627776 26114190709547 216013352927756288 qz442 (@Enclosure.Real.IsNear.neg qz218 Bool.false 816605 1048576 36607799 51501596672 (@Enclosure.Real.IsNear.recentre' qz218 Bool.false 816605 1048576 36607799 51501596672 816605 1048576 36607799 51501596672 (ep1425 rfl rfl) rfl)) rfl)

noncomputable def ep1427 := @ep1415 4027045361640 0 1 39146008044714817930749 737963866784097831485440 ep1409 ep1411 (@Enclosure.Complex.IsNear.re_isNear qz211 Bool.true 58292260767 549755813888 13041493147397 108006676463878144 Bool.true 144735886805 1099511627776 26114190709547 216013352927756288 (ep1416 ep1426))

noncomputable def ep1428 := @Enclosure.Complex.IsNear.re_isNear (@HAdd.hAdd Complex Complex Complex qz4 qz212 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz76 (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz84 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz84 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz84 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz126 qz127 (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz84 2 k) 1))))) Bool.false 2014641782441 4027045361640 0 1 Bool.false

noncomputable def ep1429 := @Enclosure.Complex.IsNear.addLitP qz212 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz76 (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz84 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz84 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz84 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz126 qz127 (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz84 2 k) 1)))) Bool.false 4785351621 9588203242 0 1 Bool.true 1211682500

noncomputable def ep1430 := @ep1429 4794101621 0 1 Bool.false 1 840 0 1 Bool.false 69239 210000 0 1 Bool.false 4029283564882 2014641782441 4027045361640 0 1 Bool.false 77485477136419 77485477136419 1006761340410000 0 1

noncomputable abbrev qz219 := (@HDiv.hDiv Complex Complex Complex qz401 qz425 (@HSub.hSub Complex Complex Complex qz393 qz444 (1 : Complex)))

noncomputable def ep1431 := @Enclosure.Complex.IsNear.addLitP qz219 qz101 Bool.true 70000000 76705625936 0 1 Bool.true 19386920000 76705625936 0 1

noncomputable def ep1432 := @Enclosure.Complex.IsNear.of_eq qz219 (Complex.mk (Enclosure.sfrac Bool.true 70000000 76705625936) (Enclosure.sfrac Bool.true 19386920000 76705625936)) Bool.true 70000000 76705625936 0 1 Bool.true 19386920000 76705625936 0 1

noncomputable def ep1433 := @ep1431 Bool.false 1 2 0 1 Bool.false 0 1 0 1 Bool.false 76565625936 4785351621 9588203242 0 1 Bool.true 19386920000 1211682500 4794101621 0 1 (ep1432 (BSN.N_div_s_sub_one_mk qz146 138478 1000 35 qz147 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 70000000 76705625936) (Enclosure.sfrac Bool.true 19386920000 76705625936) Bool.true 70000000 76705625936 0 1 Bool.true 19386920000 76705625936 0 1 (Enclosure.Real.IsNear.const Bool.true 70000000 76705625936) (Enclosure.Real.IsNear.const Bool.true 19386920000 76705625936))) qz102 rfl

noncomputable def ep1434 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz76 (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz84 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz84 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz84 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz126 qz127 (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz84 2 k) 1)))) (@HAdd.hAdd Complex Complex Complex qz4 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz76 (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz84 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz84 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz84 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz126 qz127 (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz84 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz76 (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz103)) ↑qz136) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1))) qz137)) Bool.false 1 840 0 1

noncomputable def ep1435 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz76 (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz84 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz84 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz84 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz126 qz127 (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz84 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz76 (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz103)) ↑qz136) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1))) qz137) Bool.false 0 1 0 1 Bool.false

noncomputable def ep1436 := @ep1435 0 1 0 1 Bool.false 1 840 0 1 Bool.false 69239 210000 0 1 Bool.false 1 1 840 0 1 Bool.false 69239 69239 210000 0

noncomputable def ep1437 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz76 (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz84 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz84 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz84 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz126 qz127 (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz84 2 k) 1)))) (Complex.mk qz10 qz10) Bool.false 0 1 0 1 Bool.false

noncomputable def ep1438 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz103)) ↑qz136) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1))) qz137 Bool.false 1 840 0 1 Bool.false 69239 210000 0 1

noncomputable def ep1439 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz103)) ↑qz136) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1)))) qz138) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz103)) ↑qz136) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1)))) qz139) 1 840 0 1 0 1 0

noncomputable def ep1440 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz103)) ↑qz136) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1)))) qz138 1 24 0 1 1 35 0 1 1

noncomputable def ep1441 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz103)) ↑qz136)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz103)) ↑qz136)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1)))) 1 24 0 1 0 1 0 1 1

noncomputable def ep1442 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz103)) ↑qz136)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 1 2 0 1 1 24 0

noncomputable def ep1443 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1)) qz143 Bool.false 1 2 0 1 Bool.false 138478 1000 0 1 (BSN.ascPochhammer_one_eval qz143)

noncomputable def ep1444 := ep1443 (@Enclosure.Complex.IsNear.of_eq qz143 (Complex.mk qz96 qz146) Bool.false 1 2 0 1 Bool.false 138478 1000 0 1 (BSN.s_crit_mk qz146 Bool.false 138478 1000 qz147) (@Enclosure.Complex.IsNear.mk qz96 qz146 Bool.false 1 2 0 1 Bool.false 138478 1000 0 1 qz407 qz148))

noncomputable def ep1445 := @ep1442 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz103)) ↑qz136) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep761) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 138478 1000 0 1 ep1444)

noncomputable def ep1446 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz103)) ↑qz136)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 138478 1000 0 1 0 1 0

noncomputable def ep1447 := @ep1446 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz103)) ↑qz136) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep761) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 138478 1000 0 1 ep1444)

noncomputable def ep1448 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz103)) ↑qz136)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz103)) ↑qz136)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1)))) 69239 6000 0 1 0 1 0 1 69239

noncomputable def ep1449 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz103)) ↑qz136)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 138478 1000 0 1 69239 6000 0

noncomputable def ep1450 := @ep1449 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz103)) ↑qz136) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep761) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 138478 1000 0 1 ep1444)

noncomputable def ep1451 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz103)) ↑qz136)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 1 2 0 1 0 1 0

noncomputable def ep1452 := @ep1451 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz103)) ↑qz136) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep761) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 138478 1000 0 1 ep1444)

noncomputable def ep1453 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz103)) ↑qz136) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 24 0 1 Bool.false 69239 6000 0 1 (@ep1441 1 24 0 1 (ep1445 rfl) (ep1447 rfl) rfl rfl) (@ep1448 69239 6000 0 1 (ep1450 rfl) (ep1452 rfl) rfl rfl)

noncomputable def ep1454 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz103)) ↑qz136) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 69239 6000 0 1 ep1453

noncomputable def ep1455 := @ep1440 840 0 1 ep1454 qz140

noncomputable def ep1456 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz103)) ↑qz136) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1)))) qz139 69239 6000 0 1 0 1 0 1 0

noncomputable def ep1457 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz103)) ↑qz136) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 69239 6000 0 1 ep1453

noncomputable def ep1458 := @ep1456 1 0 1 ep1457 qz141

noncomputable def ep1459 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz103)) ↑qz136) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1)))) qz139) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz103)) ↑qz136) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1)))) qz138) 0 1 0 1 69239 210000 0

noncomputable def ep1460 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz103)) ↑qz136) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1)))) qz139 1 24 0 1 0 1 0 1 0

noncomputable def ep1461 := @ep1460 1 0 1 ep1454 qz141

noncomputable def ep1462 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz103)) ↑qz136) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1)))) qz138 69239 6000 0 1 1 35 0 1 69239

noncomputable def ep1463 := @ep1462 210000 0 1 ep1457 qz140

noncomputable def ep1464 := @ep1436 1 (@ep1437 0 1 0 1 (BSN.bern_sum_base qz143 35) qz117) (ep1438 (@ep1439 1 1 1 840 0 1 (ep1455 rfl) (ep1458 rfl) rfl rfl) (@ep1459 1 69239 69239 210000 0 1 (ep1461 rfl) (ep1463 rfl) rfl rfl)) rfl rfl rfl rfl rfl

noncomputable def ep1465 := ep1430 (ep1433 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep1434 Bool.false 69239 210000 0 1 (BSN.bern_sum_succ qz143 35 0 1 1 rfl rfl) (ep1464 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl rfl

noncomputable def ep1466 := @Enclosure.Real.IsNear.mulLit_tf qz216 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz212 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz76 (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz84 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz84 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz84 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz126 qz127 (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz84 2 k) 1)))))) 144735886805 1099511627776 26114190709547 216013352927756288 77485477136419

noncomputable def ep1467 := @ep1466 1006761340410000 0 1 ep1412 ep1246 ep1413 ep1248 (@Enclosure.Complex.IsNear.im_isNear qz211 Bool.true 58292260767 549755813888 13041493147397 108006676463878144 Bool.true 144735886805 1099511627776 26114190709547 216013352927756288 (ep1416 ep1426))

noncomputable def ep1468 := @Enclosure.Complex.IsNear.im_isNear (@HAdd.hAdd Complex Complex Complex qz4 qz212 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz76 (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz84 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz84 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz84 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz126 qz127 (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz84 2 k) 1))))) Bool.false 2014641782441 4027045361640 0 1 Bool.false

noncomputable def ep1469 := nat_lit 1505601212963850926857791

noncomputable def ep1470 := nat_lit 184490966696024457871360000

noncomputable def ep1471 := nat_lit 1010526319097395307043751343

noncomputable def ep1472 := @Enclosure.Real.IsNear.addLit_tt (@HMul.hMul Real Real Real qz0 qz215 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz212 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz76 (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz84 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz84 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz84 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz126 qz127 (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz84 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz216 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz212 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz76 (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz84 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz84 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz84 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz126 qz127 (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz84 2 k) 1))))))) ep1469 ep1470 ep1471

noncomputable def ep1473 := nat_lit 108736946370003159200342999040000

noncomputable def ep1474 := nat_lit 52610739718085970595664227

noncomputable def ep1475 := nat_lit 869895570960025273602743992320

noncomputable def ep1476 := nat_lit 12092474953194275757358272688628508559098823835648

noncomputable def ep1477 := @Enclosure.Real.IsNear.mulLit_tf qz215 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz212 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz76 (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz84 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz84 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz84 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz126 qz127 (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz84 2 k) 1)))))) 58292260767 549755813888 13041493147397 108006676463878144 77485477136419

noncomputable def ep1478 := @ep1477 1006761340410000 0 1 ep1469 ep1470 ep1471 ep1473 (@Enclosure.Complex.IsNear.re_isNear qz211 Bool.true 58292260767 549755813888 13041493147397 108006676463878144 Bool.true 144735886805 1099511627776 26114190709547 216013352927756288 (ep1416 ep1426))

noncomputable def ep1479 := @Enclosure.Real.IsNear.mulLit_tf qz216 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz212 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz76 (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz84 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz84 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz84 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz126 qz127 (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz84 2 k) 1)))))) 144735886805 1099511627776 26114190709547 216013352927756288 2014641782441

noncomputable def ep1480 := @ep1479 4027045361640 0 1 58318192995200802518201 885556640140917397782528 ep1474 ep1475 (@Enclosure.Complex.IsNear.im_isNear qz211 Bool.true 58292260767 549755813888 13041493147397 108006676463878144 Bool.true 144735886805 1099511627776 26114190709547 216013352927756288 (ep1416 ep1426))

noncomputable abbrev qz706 := (ep1465 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable def ep1481 := @ep1408 ep1376 ep1369 ep1377 ep1371 (@ep1410 ep1411 ep1412 ep1246 ep1413 ep1248 ep1414 ep1374 ep1246 ep1375 ep1248 (ep1427 (@ep1428 77485477136419 1006761340410000 0 1 qz706) rfl) (ep1467 (@ep1468 77485477136419 1006761340410000 0 1 qz706) rfl) rfl rfl) (@ep1472 ep1473 58318192995200802518201 885556640140917397782528 ep1474 ep1475 ep1476 ep1376 ep1369 ep1377 ep1371 (ep1478 (@ep1468 77485477136419 1006761340410000 0 1 qz706) rfl) (ep1480 (@ep1428 77485477136419 1006761340410000 0 1 qz706) rfl) rfl rfl)

noncomputable def ep1482 := @ep1380 ep1370 ep1371 (@ep1381 216013352927756288 (BSN.head_sum_c_eq qz143 35) (ep1382 (BSN.head_sum_c_succ qz143 34 35 rfl rfl) (ep1407 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))) ep1481 rfl rfl rfl

noncomputable def ep1483 := @Enclosure.Complex.IsNear.re_isNear (zetaApproximant qz143 1 35) Bool.false ep1245 ep1246 ep1247 ep1248 Bool.false ep1368 ep1369 ep1370 ep1371 (@ep1372 ep1248 Bool.false ep1368 ep1369 ep1370 ep1371 (BSN.zetaApproximant_eq_folded' qz143 1 35 rfl) (ep1482 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

noncomputable def ep1484 := @Enclosure.Real.IsNear.mulLit_tf (Real.sin (@HSub.hSub Real Real Real qz396 (Complex.im (@HSub.hSub Complex Complex Complex qz77 qz182 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz183 (@Nat.cast Complex Complex.instNatCast j))))) qz184)) (Complex.im (zetaApproximant qz143 1 35)) 9 262144 18926129

noncomputable def ep1485 := @Enclosure.Real.IsNear.recentre' (Real.sin (@HSub.hSub Real Real Real qz396 (Complex.im (@HSub.hSub Complex Complex Complex qz77 qz182 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz183 (@Nat.cast Complex Complex.instNatCast j))))) qz184)) Bool.true 36 1048576 18926129

noncomputable def ep1486 := @Enclosure.Real.IsNear.sin_image (@HSub.hSub Real Real Real qz396 (Complex.im (@HSub.hSub Complex Complex Complex qz77 qz182 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz183 (@Nat.cast Complex Complex.instNatCast j))))) qz184) qz481 Bool.false 151533101 1048576 95

noncomputable def ep1487 := nat_lit 4642578150816871951322798183147333989882153610398974986509336037504478128800000

noncomputable def ep1488 := nat_lit 13894210957344988242846951581808540433051075905607528144699123966765434186400000

noncomputable def ep1489 := BSN.cos_dyadic_bound_f 3373183070 2147483648 3 2 1048576 393310 ep1487 ep78 ep1364 ep1488 ep81 ep1364 36 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3373183070) qz15 0 2 ep1487 ep78 ep1364 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3373183070) qz16 0 2 ep1488 ep81 ep1364 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1490 := @ep1486 262144 Bool.true 36 1048576 1 196463 (@ep1252 151533101 1048576 95 262144 ep1362 rfl) (Enclosure.sfrac_false_div 151533101 1048576) (BSN.sin_reduce3 qz481 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 237366656525988677025792) qz31) 226375608064910080 72057594037927936 Bool.false 36 1048576 22 1000000000000000 392926 196463 (BSN.sin_reduce_arg_pos_rat_q3 151533101 1048576 226375608064910080 72057594037927936 22 237366656525988677025792 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 36 1048576 237366656525988677025792 151115727451828646838272 3373183070 2147483648 393310 392926 (ep1489 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1491 := @Enclosure.Complex.IsNear.im_isNear (zetaApproximant qz143 1 35) Bool.false ep1245 ep1246 ep1247 ep1248 Bool.false ep1368 ep1369 ep1370 ep1371 (@ep1372 ep1248 Bool.false ep1368 ep1369 ep1370 ep1371 (BSN.zetaApproximant_eq_folded' qz143 1 35 rfl) (ep1482 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

theorem EMRow47.d17 : Enclosure.Real.IsNear (hardyZApproximantEM 1 35 qz146) Bool.false ep1229 ep1230 ep1231 ep1232 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantEM 1 35 qz146) ep1233 Bool.false ep1229 ep1230 ep1231 ep1232 (@Eq.refl Real ep1233) (@ep1234 Bool.false ep1229 ep1230 ep1231 ep1232 (BSN.re_exp_mul (@HSub.hSub Real Real Real qz396 (Complex.im (@HSub.hSub Complex Complex Complex qz77 qz182 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz183 (@Nat.cast Complex Complex.instNatCast j))))) qz184) (zetaApproximant qz143 1 35)) (@ep1236 ep1237 ep1238 ep1232 ep1239 ep1240 ep1241 ep1242 ep1243 ep1229 ep1230 ep1231 ep1232 (@ep1244 51501596672 ep1245 ep1246 ep1247 ep1248 ep1235 ep1237 ep1238 ep1232 (@ep1249 51501596672 1048575 1048576 18926129 51501596672 (ep1367 rfl rfl) rfl) ep1483 rfl) (@ep1484 51501596672 ep1368 ep1369 ep1370 ep1371 ep1239 ep1240 ep1241 ep1242 (@ep1485 51501596672 9 262144 18926129 51501596672 (ep1490 rfl rfl) rfl) ep1491 rfl) rfl rfl))

theorem EMRow47.d18 : @Eq Nat (Nat.mul (BSN.factNat (Nat.succ (Nat.mul 2 1))) (Nat.pow 4 (Nat.mul 2 1))) 96 := @Eq.refl Nat 96

theorem EMRow47.d19 : @Eq Nat (Nat.mul (Nat.mul 2 1) (Nat.pow (Nat.succ (Nat.mul 4 2)) (Nat.mul 2 1))) 162 := @Eq.refl Nat 162

theorem EMRow47.d20 : @Eq Nat (BSN.factNat (Nat.mul 2 2)) 24 := @Eq.refl Nat 24

theorem EMRow47.d21 : @Eq Nat (Nat.pow 35 (Nat.succ (Nat.mul 2 3))) 64339296875 := @Eq.refl Nat 64339296875

noncomputable abbrev qz707 := (@HAdd.hAdd Complex Complex Complex qz713 qz712 (@Nat.cast Complex Complex.instNatCast 3))

noncomputable abbrev qz501 := qz707

noncomputable abbrev qz220 := (@HDiv.hDiv Real Real Real qz270 (@Norm.norm Complex Complex.instNorm qz501) (@HAdd.hAdd Real Real Real qz416 (Complex.re qz271) qz289))

noncomputable abbrev qz221 := (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 2)

noncomputable abbrev qz222 := (@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 2)))

noncomputable abbrev qz502 := (@HPow.hPow Complex Complex Complex qz535 qz655 (@HSub.hSub Complex Complex Complex qz644 qz536 qz542))

noncomputable abbrev qz223 := qz502

noncomputable def ep1492 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 35))) (@HMul.hMul Real Real Real qz0 qz220 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz76 (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))) 1094074151 14495514624 11844155 115964116992 2189103603938838799 4035225266123964416 39007057463

noncomputable def ep1493 := nat_lit 36147018961474867241672507392

noncomputable def ep1494 := @Enclosure.Real.IsNear.mulLit_ff (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 35)) 26561 1769472 1 1769472 41191 8192 867 131072 1094074151 14495514624

noncomputable abbrev qz224 := (@HMul.hMul Real Real Real qz267 (2 : Real) Real.pi)

noncomputable abbrev qz708 := (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid)))

noncomputable abbrev qz503 := (@Inv.inv Real Real.instInv (@HPow.hPow Real Nat Real qz708 qz224 2))

noncomputable def ep1495 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 96 162) qz503 96 162 0 1 26561 1048576 1 1048576 26561 1769472 1 1769472

noncomputable def ep1496 := nat_lit 781950621441006189802102638025

noncomputable def ep1497 := nat_lit 19807040628566084398385987584

noncomputable def ep1498 := nat_lit 26986075409044041160201671

noncomputable def ep1499 := nat_lit 1073741824000000000000000000000000000000

noncomputable abbrev qz504 := (@HPow.hPow Real Nat Real qz708 qz224 1)

noncomputable def ep1500 := @Enclosure.Real.IsNear.mulLit_ff qz504 qz224 884279719003555 140737488355328 1 500000000000000 884279719003555 140737488355328 1 500000000000000 ep1496 ep1497 ep1498 ep1499

noncomputable def ep1501 := ep1500 (@Enclosure.Real.IsNear.of_eq qz504 qz224 Bool.false 884279719003555 140737488355328 1 500000000000000 (BSN.pow_one_r qz224) (@Enclosure.Real.IsNear.of_eq qz224 qz268 Bool.false 884279719003555 140737488355328 1 500000000000000 BSN.two_pi_eq qz269)) (@Enclosure.Real.IsNear.of_eq qz224 qz268 Bool.false 884279719003555 140737488355328 1 500000000000000 BSN.two_pi_eq qz269) rfl

noncomputable abbrev qz505 := (@HPow.hPow Real Nat Real qz708 qz224 2)

noncomputable def ep1502 := @Enclosure.Real.IsNear.inv_image qz505 ep1496 ep1497 ep1498 ep1499 13280 13281 524288 (@Enclosure.Real.IsNear.of_eq qz505 (@HMul.hMul Real Real Real qz0 qz504 qz224) Bool.false ep1496 ep1497 ep1498 ep1499 (BSN.pow_succ_r qz224 1 2 rfl) ep1501) rfl rfl rfl

noncomputable def ep1503 := ep1495 (Enclosure.Real.IsNear.const Bool.false 96 162) (@Enclosure.Real.IsNear.recentre' qz503 Bool.false 26561 1048576 1 1048576 26561 1048576 1 1048576 (ep1502 rfl rfl rfl) rfl)

noncomputable def ep1504 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 35)) (Real.sqrt (@HAdd.hAdd Real Real Real qz416 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz5 1 35)) (Complex.re (zetaApproximant qz5 1 35))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz5 1 35)) (Complex.im (zetaApproximant qz5 1 35))))) Bool.false 41191 8192 867 131072

noncomputable def ep1505 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz416 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz5 1 35)) (Complex.re (zetaApproximant qz5 1 35))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz5 1 35)) (Complex.im (zetaApproximant qz5 1 35))))) Bool.false 5272448 1048576 6936 1048576

noncomputable def ep1506 := nat_lit 6273439928272575742696398687651154769622626261

noncomputable def ep1507 := nat_lit 248130549269785036103778101609732505600000000

noncomputable def ep1508 := nat_lit 988161690885895325125647270162717396928244810318572206419487761

noncomputable def ep1509 := nat_lit 14858074083483715944567380182697429839375128936967883980800000000

noncomputable def ep1510 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz416 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz5 1 35)) (Complex.re (zetaApproximant qz5 1 35))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz5 1 35)) (Complex.im (zetaApproximant qz5 1 35)))) ep1506 ep1507 ep1508 ep1509 2632756 2639692

noncomputable def ep1511 := nat_lit 23834766214167842077336346473834998443578743714004441

noncomputable def ep1512 := nat_lit 942727427523122378060987695692242085967036416000000

noncomputable def ep1513 := nat_lit 986218114618043060954518506691060351815116311354458301843515797

noncomputable def ep1514 := nat_lit 351510666652936592872360648551641180867978747929

noncomputable def ep1515 := nat_lit 8019729852193228563366041161270809411872358400000000

noncomputable def ep1516 := nat_lit 161964688987688680927396955971420426094041580342825381330997

noncomputable def ep1517 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz5 1 35)) (Complex.re (zetaApproximant qz5 1 35))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz5 1 35)) (Complex.im (zetaApproximant qz5 1 35))) ep1511 ep1512 ep1513 ep1509 ep1514 ep1515 ep1516

noncomputable def ep1518 := nat_lit 1238172840290309662047281681891452486614594078080656998400000000

noncomputable def ep1519 := nat_lit 191148717506554946740477144324306703774142957061210447237877156941782295868478660897282749171236864000000

noncomputable def ep1520 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (zetaApproximant qz5 1 35)) (Complex.re (zetaApproximant qz5 1 35)) ep543 ep544 ep545 ep546 ep543 ep544 ep545 ep546 ep1511

noncomputable def ep1521 := @Enclosure.Real.IsNear.mulLit_tt (Complex.im (zetaApproximant qz5 1 35)) (Complex.im (zetaApproximant qz5 1 35)) 592883349954218728583173 ep678 ep679 ep680 592883349954218728583173 ep678 ep679 ep680 ep1514

noncomputable def ep1522 := @ep1492 576460752303423488 ep1493 67329069527750587541 108951082185347039232 1590748764731341 15564440312192434176 (@ep1494 11844155 115964116992 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaStirlingErrorBound 1 2) (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 96 162) qz503) Bool.false 26561 1769472 1 1769472 (BSN.theta_err_eq 1 2 96 162 EMRow47.d18 EMRow47.d19 rfl) (ep1503 rfl)) (ep1504 (BSN.norm_eq_sqrt_mul_add (zetaApproximant qz5 1 35)) (@ep1505 41191 8192 867 131072 (@ep1510 524288 (@ep1517 ep1518 ep1519 ep1506 ep1507 ep1508 ep1509 (@ep1520 ep1512 ep1513 ep1509 ep802 ep802 rfl) (@ep1521 ep1515 ep1516 ep1518 ep808 ep808 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl)

noncomputable abbrev qz225 := (@Norm.norm Complex Complex.instNorm qz501)

noncomputable abbrev qz709 := (Enclosure.sfrac Bool.false 2 7)

noncomputable def ep1523 := @Enclosure.Real.IsNear.of_eq (@HMul.hMul Real Real Real qz0 qz220 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz76 (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))) (@HMul.hMul Real Real Real qz0 (@HMul.hMul Real Real Real qz0 qz225 qz709) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz76 (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))) Bool.false 2189103603938838799 4035225266123964416 39007057463 576460752303423488 (BSN.zrb_shape_eq qz225 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz76 (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) qz12 3)

noncomputable def ep1524 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz0 qz225 qz709) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz76 (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) 143116871 3670016 1 3670016 15295915769 1099511627776 1801 1099511627776

noncomputable def ep1525 := @Enclosure.Real.IsNear.mulLit_ff qz225 qz709 143116871 1048576 1 1048576 2 7 0 1 143116871 3670016

noncomputable abbrev qz506 := (Complex.re qz707)

noncomputable abbrev qz507 := (Complex.im qz707)

noncomputable abbrev qz226 := (@HAdd.hAdd Real Real Real qz416 (@HMul.hMul Real Real Real qz267 qz506 qz506) (@HMul.hMul Real Real Real qz267 qz507 qz507))

noncomputable abbrev qz227 := qz501

noncomputable def ep1526 := @Enclosure.Real.IsNear.of_eq qz225 (Real.sqrt qz226) Bool.false 143116871 1048576 1 1048576 (BSN.norm_eq_sqrt_mul_add qz227)

noncomputable def ep1527 := @Enclosure.Real.IsNear.recentre' (Real.sqrt qz226) Bool.false 143116871 1048576 1 1048576 143116871

noncomputable def ep1528 := @Enclosure.Real.IsNear.sqrt_image qz226 4657167341 250000 0 1 71558435 71558436 524288

noncomputable abbrev qz228 := (@HMul.hMul Real Real Real qz267 qz506 qz506)

noncomputable abbrev qz229 := (@HMul.hMul Real Real Real qz267 qz507 qz507)

noncomputable def ep1529 := @Enclosure.Real.IsNear.addLit_ff qz228 qz229 49 4 0 1 4654104841 250000 0 1

noncomputable abbrev qz230 := qz506

noncomputable def ep1530 := @Enclosure.Real.IsNear.mulLit_ff qz230 qz230 7 2 0 1 7 2 0 1 49 4

noncomputable abbrev qz508 := (Enclosure.sfrac Bool.false 7 2)

noncomputable def ep1531 := @Enclosure.Complex.IsNear.of_eq qz227 (Complex.mk qz508 qz12) Bool.false 7 2 0 1 Bool.false 136442 1000 0 1 (BSN.s_add_nat_mk qz12 Bool.false 136442 1000 3 qz13)

noncomputable abbrev qz509 := (ep1531 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7 2) qz12 Bool.false 7 2 0 1 Bool.false 136442 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 7 2) qz18))

noncomputable def ep1532 := @ep1530 0 1 (@Enclosure.Complex.IsNear.re_isNear qz227 Bool.false 7 2 0 1 Bool.false 136442 1000 0 1 qz509)

noncomputable def ep1533 := ep1532 (@Enclosure.Complex.IsNear.re_isNear qz227 Bool.false 7 2 0 1 Bool.false 136442 1000 0 1 qz509)

noncomputable abbrev qz231 := qz507

noncomputable def ep1534 := @Enclosure.Real.IsNear.mulLit_ff qz231 qz231 136442 1000 0 1 136442 1000 0 1 4654104841 250000

noncomputable def ep1535 := @ep1534 0 1 (@Enclosure.Complex.IsNear.im_isNear qz227 Bool.false 7 2 0 1 Bool.false 136442 1000 0 1 qz509)

noncomputable def ep1536 := ep1535 (@Enclosure.Complex.IsNear.im_isNear qz227 Bool.false 7 2 0 1 Bool.false 136442 1000 0 1 qz509)

noncomputable def ep1537 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz76 (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Real.sqrt (@HAdd.hAdd Real Real Real qz416 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz76 (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.re (@HMul.hMul Complex Complex Complex qz76 (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz76 (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.im (@HMul.hMul Complex Complex Complex qz76 (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))))) Bool.false 15295915769 1099511627776

noncomputable def ep1538 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz416 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz76 (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.re (@HMul.hMul Complex Complex Complex qz76 (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz76 (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.im (@HMul.hMul Complex Complex Complex qz76 (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))))) Bool.false 30591831538 2199023255552

noncomputable def ep1539 := nat_lit 18328445216175813446352329316961532789363516738568255999459641449273

noncomputable def ep1540 := nat_lit 94705306099042509099598777160015139673704428784844800000000000000000000

noncomputable def ep1541 := nat_lit 375013257528489513981312777164439493456273876949881038633108250152877320947887817519

noncomputable def ep1542 := nat_lit 8231523262088521679652581674886848790199941630784804151652536811520000000000000000000000000000

noncomputable def ep1543 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz416 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz76 (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.re (@HMul.hMul Complex Complex Complex qz76 (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz76 (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.im (@HMul.hMul Complex Complex Complex qz76 (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)))) ep1539 ep1540 ep1541 ep1542

noncomputable def ep1544 := nat_lit 34512531818446265563234386747024264432335480667282250971721796089321

noncomputable def ep1545 := nat_lit 189410612198085018199197554320030279347408857569689600000000000000000000

noncomputable def ep1546 := nat_lit 695009334074207460309233654528734047852565350689955771670092794139547401123990812519

noncomputable def ep1547 := nat_lit 16463046524177043359305163349773697580399883261569608303305073623040000000000000000000000000000

noncomputable def ep1548 := nat_lit 85774344556214453178810875475952045855662112394170441087899472369

noncomputable def ep1549 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz76 (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.re (@HMul.hMul Complex Complex Complex qz76 (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz76 (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.im (@HMul.hMul Complex Complex Complex qz76 (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))) ep1544 ep1545 ep1546 ep1547 ep1548

noncomputable def ep1550 := nat_lit 7576424487923400727967902172801211173896354302787584000000000000000000

noncomputable def ep1551 := nat_lit 55017180982771567653391899800144939059982403209806305596123706166207240771784822519

noncomputable def ep1552 := nat_lit 277728162322793882294448417822995984655502643985817376475168912105417781616082652494595305530937881897481581147260452864000000000000000000

noncomputable def ep1553 := nat_lit 5874736744607903327256296226278611

noncomputable def ep1554 := nat_lit 435213295061266502894223360000000000

noncomputable def ep1555 := nat_lit 200640803132812158887883743897066594863

noncomputable def ep1556 := nat_lit 128308403949924664937760523341004800000000000000

noncomputable def ep1557 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz76 (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.re (@HMul.hMul Complex Complex Complex qz76 (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) ep1553 ep1554 ep1555 ep1556 ep1553 ep1554 ep1555

noncomputable def ep1558 := nat_lit 292872573922882804951316154485287

noncomputable def ep1559 := nat_lit 87042659012253300578844672000000000

noncomputable def ep1560 := nat_lit 63718662183839557961197292849383472363

noncomputable def ep1561 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz76 (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223) Bool.false ep1553 ep1554 ep1555 ep1556 Bool.false ep1558 ep1559 ep1560

noncomputable def ep1562 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223 Bool.false ep1553 ep1554 ep1555 ep1556 Bool.false ep1558 ep1559 ep1560 ep1556

noncomputable def ep1563 := nat_lit 14571864556034280639788016191

noncomputable def ep1564 := nat_lit 116056878683004400771792896000000

noncomputable def ep1565 := nat_lit 2514387782574627576346875884483359

noncomputable def ep1566 := nat_lit 171077871933232886583680697788006400000000000

noncomputable def ep1567 := nat_lit 5820092252522774774857091165562361

noncomputable def ep1568 := nat_lit 28393573185125884029374798140529153659

noncomputable abbrev qz232 := (Complex.re qz502)

noncomputable abbrev qz233 := (Complex.im qz502)

noncomputable def ep1569 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz232) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz233) ep1563 ep1564 ep1565 ep1566 ep1567 ep1554 ep1568

noncomputable def ep1570 := nat_lit 18329771992846380705394360477286400000000000000

noncomputable def ep1571 := nat_lit 681803609663547644230132378514313494519317537601840486547456000000

noncomputable def ep1572 := nat_lit 4835703278458516698824704

noncomputable def ep1573 := nat_lit 1425648932776940721530672481566720000

noncomputable def ep1574 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz232 13962002023 120000000 0 1 5218400818174083085 ep1572 180087911349146463044233 ep1573 ep1563

noncomputable def ep1575 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) 13962002023 120000000 0 1 0 1 0 1 13962002023

noncomputable def ep1576 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 41886006069 500000 0 1 13962002023 120000000 0

noncomputable def ep1577 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (Complex.mk (Enclosure.sfrac Bool.true 1 720) qz10) Bool.true 1 720 0 1 Bool.false 0 1 0 1 (BSN.bern_coeff_mk 2 1 30 24 Bool.true BSN.bern_real_2 EMRow47.d20 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 1 720) qz10 Bool.true 1 720 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.true 1 720) qz21)

noncomputable abbrev qz510 := (@HAdd.hAdd Complex Complex Complex qz534 qz533 qz543)

noncomputable abbrev qz234 := qz510

noncomputable def ep1578 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) (@HMul.hMul Complex Complex Complex qz76 (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) qz234) Bool.true 41886006069 500000 0 1 Bool.true 317409618670361 125000000 0 1

noncomputable abbrev qz235 := (Complex.re qz510)

noncomputable abbrev qz236 := (Complex.im qz510)

noncomputable def ep1579 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz235) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz236) 4653917341 100000 0 1 4654104841 125000 0 1

noncomputable def ep1580 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz235 4653917341 250000 0 1 5 2 0 1 4653917341 100000

noncomputable abbrev qz511 := (@HAdd.hAdd Complex Complex Complex qz534 qz533 (@Nat.cast Complex Complex.instNatCast 1))

noncomputable abbrev qz237 := qz511

noncomputable def ep1581 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) (@HMul.hMul Complex Complex Complex qz76 (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) qz237) Bool.true 4653917341 250000 0 1 Bool.false 68221 250 0 1

noncomputable abbrev qz238 := (Complex.re qz511)

noncomputable abbrev qz239 := (Complex.im qz511)

noncomputable def ep1582 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz238) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz239) 3 4 0 1 4654104841 250000 0 1

noncomputable def ep1583 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz238 1 2 0 1 3 2 0 1 3 4

noncomputable def ep1584 := @ep1583 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 136442 1000 0 1 ep763)

noncomputable abbrev qz512 := (Enclosure.sfrac Bool.false 3 2)

noncomputable def ep1585 := @Enclosure.Complex.IsNear.of_eq qz237 (Complex.mk qz512 qz12) Bool.false 3 2 0 1 Bool.false 136442 1000 0 1 (BSN.s_add_nat_mk qz12 Bool.false 136442 1000 1 qz13)

noncomputable abbrev qz513 := (ep1585 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 3 2) qz12 Bool.false 3 2 0 1 Bool.false 136442 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 3 2) qz18))

noncomputable def ep1586 := ep1584 (@Enclosure.Complex.IsNear.re_isNear qz237 Bool.false 3 2 0 1 Bool.false 136442 1000 0 1 qz513)

noncomputable def ep1587 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz239 136442 1000 0 1 136442 1000 0 1 4654104841 250000

noncomputable def ep1588 := @ep1587 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 136442 1000 0 1 ep763)

noncomputable def ep1589 := ep1588 (@Enclosure.Complex.IsNear.im_isNear qz237 Bool.false 3 2 0 1 Bool.false 136442 1000 0 1 qz513)

noncomputable def ep1590 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) qz237 Bool.true 4653917341 250000 0 1 Bool.false 68221 250 0 1 (@ep1582 18615669364 4653917341 250000 0 1 (ep1586 rfl) (ep1589 rfl) rfl rfl)

noncomputable def ep1591 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz239) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz238) 68221 1000 0 1 204663 1000 0 1

noncomputable def ep1592 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz239 1 2 0 1 136442 1000 0 1 68221 1000

noncomputable def ep1593 := @ep1592 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 136442 1000 0 1 ep763)

noncomputable def ep1594 := ep1593 (@Enclosure.Complex.IsNear.im_isNear qz237 Bool.false 3 2 0 1 Bool.false 136442 1000 0 1 qz513)

noncomputable def ep1595 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz238 136442 1000 0 1 3 2 0 1 204663 1000

noncomputable def ep1596 := @ep1595 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 136442 1000 0 1 ep763)

noncomputable def ep1597 := ep1596 (@Enclosure.Complex.IsNear.re_isNear qz237 Bool.false 3 2 0 1 Bool.false 136442 1000 0 1 qz513)

noncomputable abbrev qz240 := (ep1581 (BSN.ascPochhammer_succ_eval_c 1 2 qz271 rfl) (ep1590 (@ep1591 272884000 68221 250 0 1 (ep1594 rfl) (ep1597 rfl) rfl rfl)))

noncomputable def ep1598 := @ep1580 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 4653917341 250000 0 1 Bool.false 68221 250 0 1 qz240)

noncomputable abbrev qz514 := (Enclosure.sfrac Bool.false 5 2)

noncomputable def ep1599 := @Enclosure.Complex.IsNear.of_eq qz234 (Complex.mk qz514 qz12) Bool.false 5 2 0 1 Bool.false 136442 1000 0 1 (BSN.s_add_nat_mk qz12 Bool.false 136442 1000 2 qz13)

noncomputable abbrev qz515 := (ep1599 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 5 2) qz12 Bool.false 5 2 0 1 Bool.false 136442 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 5 2) qz18))

noncomputable def ep1600 := ep1598 (@Enclosure.Complex.IsNear.re_isNear qz234 Bool.false 5 2 0 1 Bool.false 136442 1000 0 1 qz515)

noncomputable def ep1601 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz236 68221 250 0 1 136442 1000 0 1 4654104841 125000

noncomputable def ep1602 := @ep1601 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 4653917341 250000 0 1 Bool.false 68221 250 0 1 qz240)

noncomputable def ep1603 := ep1602 (@Enclosure.Complex.IsNear.im_isNear qz234 Bool.false 5 2 0 1 Bool.false 136442 1000 0 1 qz515)

noncomputable def ep1604 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) qz234 Bool.true 41886006069 500000 0 1 Bool.true 317409618670361 125000000 0 1 (@ep1579 1047150151725000 41886006069 500000 0 1 (ep1600 rfl) (ep1603 rfl) rfl rfl)

noncomputable def ep1605 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz236) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz235) 317494894920361 125000000 0 1 68221 100 0 1

noncomputable def ep1606 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz236 4653917341 250000 0 1 136442 1000 0 1 317494894920361 125000000

noncomputable def ep1607 := @ep1606 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 4653917341 250000 0 1 Bool.false 68221 250 0 1 qz240)

noncomputable def ep1608 := ep1607 (@Enclosure.Complex.IsNear.im_isNear qz234 Bool.false 5 2 0 1 Bool.false 136442 1000 0 1 qz515)

noncomputable def ep1609 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz235 68221 250 0 1 5 2 0 1 68221 100

noncomputable def ep1610 := @ep1609 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 4653917341 250000 0 1 Bool.false 68221 250 0 1 qz240)

noncomputable def ep1611 := ep1610 (@Enclosure.Complex.IsNear.re_isNear qz234 Bool.false 5 2 0 1 Bool.false 136442 1000 0 1 qz515)

noncomputable abbrev qz241 := (ep1578 (BSN.ascPochhammer_succ_eval_c 2 3 qz271 rfl) (ep1604 (@ep1605 31740961867036100 317409618670361 125000000 0 1 (ep1608 rfl) (ep1611 rfl) rfl rfl)))

noncomputable def ep1612 := @ep1576 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1577) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 41886006069 500000 0 1 Bool.true 317409618670361 125000000 0 1 qz241)

noncomputable def ep1613 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 317409618670361 125000000 0 1 0 1 0

noncomputable def ep1614 := @ep1613 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1577) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 41886006069 500000 0 1 Bool.true 317409618670361 125000000 0 1 qz241)

noncomputable def ep1615 := @Enclosure.Real.IsNear.addLit_ft_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) 317409618670361 90000000000 0 1 0 1 0 1 317409618670361

noncomputable def ep1616 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 317409618670361 125000000 0 1 317409618670361 90000000000 0

noncomputable def ep1617 := @ep1616 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1577) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 41886006069 500000 0 1 Bool.true 317409618670361 125000000 0 1 qz241)

noncomputable def ep1618 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 41886006069 500000 0 1 0 1 0

noncomputable def ep1619 := @ep1618 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1577) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 41886006069 500000 0 1 Bool.true 317409618670361 125000000 0 1 qz241)

noncomputable def ep1620 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.false 13962002023 120000000 0 1 Bool.false 317409618670361 90000000000 0 1 (@ep1575 13962002023 120000000 0 1 (ep1612 rfl) (ep1614 rfl) rfl rfl) (@ep1615 317409618670361 90000000000 0 1 (ep1617 rfl) (ep1619 rfl) rfl rfl)

noncomputable def ep1621 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 13962002023 120000000 0 1 Bool.false 317409618670361 90000000000 0 1 ep1620

noncomputable def ep1622 := @Enclosure.Complex.IsNear.re_isNear qz223 Bool.false 5218400818174083085 ep1572 180087911349146463044233 ep1573 Bool.true 18336218911396972001 ep1572 626178290149089569941733 ep1573

noncomputable abbrev qz710 := (@Nat.cast Real Real.instNatCast 64339296875)

noncomputable abbrev qz242 := (@Inv.inv Real Real.instInv (Real.sqrt qz710))

noncomputable def ep1623 := @Enclosure.Complex.IsNear.of_eq qz223 (Complex.mk (@HMul.hMul Real Real Real qz0 qz242 (Real.cos qz132)) (@HMul.hMul Real Real Real qz0 qz242 qz664)) Bool.false 5218400818174083085 ep1572 180087911349146463044233 ep1573 Bool.true 18336218911396972001 ep1572 626178290149089569941733

noncomputable def ep1624 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz710) 557786472435602635 2199023255552 1 2199023255552 4334726 4334727 1099511627776 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz710) (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz710 qz14)) Bool.false 557786472435602635 2199023255552 1 2199023255552 (BSN.sqrt_natCast_div_one 64339296875) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz710 qz14)) Bool.false 557786472435602635 2199023255552 1 2199023255552 557786472435602635 2199023255552 1 2199023255552 (BSN.sqrt_enclosure 64339296875 1 278893236217801317 278893236217801318 1099511627776 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep1625 := nat_lit 47170766300000000000000000

noncomputable def ep1626 := nat_lit 140841847005213844967262257152

noncomputable def ep1627 := nat_lit 39614081257132168796771975168

noncomputable def ep1628 := nat_lit 294817289375000000000000000

noncomputable def ep1629 := BSN.log_dyadic_bound 3 67 5 4 383733955291025745 1099511627776 294817289375 256758449434344 688905 98529610469 70 64 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 3) (BSN.artanhQ 67) 0 4 256758449434344 383733955291025745 688905 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep1630 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz134 136442 1000 0 1 16011864204894419 4503599627370496 320471707663 94341532600000000000000 1092345387922102158599 2251799813685248000 21862900368477523 ep1625 qz18 (BSN.isNear_log_sfrac 35 1 16011864204894419 4503599627370496 320471707663 94341532600000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' qz440 Bool.false ep1626 ep1627 1001474086446875 ep1628 16011864204894419 4503599627370496 320471707663 94341532600000000000000 (BSN.log_rat_reduce_isNear 35 1 5 70 64 98529610469 1099511627776 24973259072661432 36028797018963968 294817289375 1000000000000000 rfl rfl rfl rfl (ep1629 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1631 := nat_lit 409936512348628799601260888064

noncomputable def ep1632 := nat_lit 316912650057057350374175801344

noncomputable def ep1633 := nat_lit 70015816973452417561666362388504482432259000096172161899992320279118039206033505260561816525426137839325559369109804082491060942955401307124677188769001295939076262241905597785064031243907246740103642693628251094418062041560067035544655214223957663180583606419456

noncomputable def ep1634 := nat_lit 599205769308871494669005633404748773453705986173265619753359186119574540201718521016582654337481038554791270797803930120647421245947038870502085995962344054183037643944802456687515051311778021064186337694386596224481457310393291043136983312363285164951074766848000

noncomputable def ep1635 := nat_lit 1759498179757711521733013466272215048309065434187672718692926056376218315312879884308801686244529339314235351734438182576588376480024731345067629589940934754282003770069800225929243039436623808146274873853122994211719359994666500212499128657565739646976

noncomputable def ep1636 := nat_lit 713368998211694882588744473946406313489663669502632880707607536384813327867765305743571622470625841370476936684334394949346711094880596705756321150850081768753057524880897074027238596030337250132207295355365797268221406107698201407070850234702196094833875983794176

noncomputable def ep1637 := nat_lit 91678482704257338684357861910926562338417015884509639822263955476294904650862933715537146113634598898883064432064001308459055450629896947186819157382238640290004759523554775873189802850702037222820509667241149222345662968490173529599958446791582630237514439327744000

noncomputable def ep1638 := BSN.cos_dyadic_bound_f 5825548219442976 4503599627370496 5 4 2199023255552 590210393769 ep1633 ep1634 ep1635 ep1636 ep1637 ep1635 601929650945 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.cosEvenP 5825548219442976) (BSN.cosEvenQ 4503599627370496) 0 4 ep1633 ep1634 ep1635 rfl rfl rfl rfl) (@BSN.binarySplit_of_base4 (BSN.cosOddP 5825548219442976) (BSN.cosOddQ 4503599627370496) 0 4 ep1636 ep1637 ep1635 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz516 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 1066743542892677) (@Nat.cast Real Real.instNatCast 2199023255552))

noncomputable def ep1639 := @Enclosure.Real.IsNear.cos_image qz132 qz516 Bool.false 1066743542892677 2199023255552 1021 2199023255552 Bool.false 601929650945 2199023255552 1 294817289375 (@Enclosure.Real.IsNear.recentre' qz132 Bool.false 1092345387922102158599 2251799813685248000 21862900368477523 ep1625 1066743542892677 2199023255552 1021 2199023255552 (ep1630 rfl) rfl) (Enclosure.sfrac_false_div 1066743542892677 2199023255552) (BSN.cos_reduce0 qz516 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep1631) (@Nat.cast Real Real.instNatCast ep1632)) 226375608064910080 72057594037927936 Bool.false 601929650945 2199023255552 77 1000000000000000 589634578750 294817289375 (BSN.sin_reduce_arg_pos_rat_q0 1066743542892677 2199023255552 226375608064910080 72057594037927936 77 ep1631 ep1632 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 601929650945 2199023255552 ep1631 ep1632 5825548219442976 4503599627370496 590210393769 589634578750 (ep1638 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1640 := nat_lit 10123400760876265014931766301066732762789687229695221675471085065208382480804328147937453918771905375220422549575669508766773829087397396307616839846953557588782357296149845126187713718173382475776

noncomputable def ep1641 := nat_lit 433508493418857668581224415970842172945704524136195884060107236574755230272398559971038183579402879451701676292035087663075723672867783462894129725544215056950382789287271065333206471540875250892800

noncomputable def ep1642 := nat_lit 1527712444775599443920393112184186911015851376437924733566700053287095648693468917965469505017156725483035296402614886808917083713430078726943832163577504928142337797675261045444951016472576

noncomputable def ep1643 := nat_lit 50588055128056247598248211182588897578308282391661356797354230854912382082956796269537079029437694728190405809956142176889827738453776992473611362575979236571225976234140202891224187501372648718336

noncomputable def ep1644 := nat_lit 15172797269660018400342854558979476053099658344766855942103753280116433059533949598986336425279100780809558670221228068207650328550372421201294540394047526993263397625054487286662226503930633781248000

noncomputable def ep1645 := BSN.sin_dyadic_bound_f 5825548219442976 4503599627370496 4 3 2199023255552 590210393769 ep1640 ep1641 ep1642 ep1643 ep1644 ep1642 2115037582117 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 5825548219442976) (BSN.sinEvenQ 4503599627370496) 0 3 ep1640 ep1641 ep1642 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 5825548219442976) (BSN.sinOddQ 4503599627370496) 0 3 ep1643 ep1644 ep1642 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1646 := @Enclosure.Real.IsNear.sin_image qz132 qz516 Bool.false 1066743542892677 2199023255552 1021 2199023255552 Bool.false 2115037582117 2199023255552 1 294817289375 (@Enclosure.Real.IsNear.recentre' qz132 Bool.false 1092345387922102158599 2251799813685248000 21862900368477523 ep1625 1066743542892677 2199023255552 1021 2199023255552 (ep1630 rfl) rfl) (Enclosure.sfrac_false_div 1066743542892677 2199023255552) (BSN.sin_reduce0 qz516 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep1631) (@Nat.cast Real Real.instNatCast ep1632)) 226375608064910080 72057594037927936 Bool.false 2115037582117 2199023255552 77 1000000000000000 589634578750 294817289375 (BSN.sin_reduce_arg_pos_rat_q0 1066743542892677 2199023255552 226375608064910080 72057594037927936 77 ep1631 ep1632 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 2115037582117 2199023255552 ep1631 ep1632 5825548219442976 4503599627370496 590210393769 589634578750 (ep1645 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz517 := (@Enclosure.Real.IsNear.recentre' qz242 Bool.false 8669453 2199023255552 1 2199023255552 8669453 2199023255552 1 2199023255552 (ep1624 rfl rfl) rfl)

noncomputable def ep1647 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz242 (Real.cos qz132)) (@HMul.hMul Real Real Real qz0 qz242 qz664) Bool.false 5218400818174083085 ep1572 180087911349146463044233 ep1573 Bool.true 18336218911396972001 ep1572 626178290149089569941733 ep1573 (@Enclosure.Real.IsNear.mulLit_ff qz242 (Real.cos qz132) 8669453 2199023255552 1 2199023255552 601929650945 2199023255552 303207475707427 648310075474428559360000 5218400818174083085 ep1572 180087911349146463044233 ep1573 qz517 (@Enclosure.Real.IsNear.recentre' (Real.cos qz132) Bool.false 601929650945 2199023255552 303207475707427 648310075474428559360000 601929650945 2199023255552 303207475707427 648310075474428559360000 (ep1639 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz242 qz664 8669453 2199023255552 1 2199023255552 2115037582117 2199023255552 303207475707427 648310075474428559360000 18336218911396972001 ep1572 626178290149089569941733 ep1573 qz517 (@Enclosure.Real.IsNear.neg qz133 Bool.false 2115037582117 2199023255552 303207475707427 648310075474428559360000 (@Enclosure.Real.IsNear.recentre' qz133 Bool.false 2115037582117 2199023255552 303207475707427 648310075474428559360000 2115037582117 2199023255552 303207475707427 648310075474428559360000 (ep1646 rfl rfl) rfl)) rfl)

noncomputable def ep1648 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz233 317409618670361 90000000000 0 1 18336218911396972001 ep1572 626178290149089569941733 ep1573 ep1567

noncomputable def ep1649 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 13962002023 120000000 0 1 Bool.false 317409618670361 90000000000 0 1 ep1620

noncomputable def ep1650 := @Enclosure.Complex.IsNear.im_isNear qz223 Bool.false 5218400818174083085 ep1572 180087911349146463044233 ep1573 Bool.true 18336218911396972001 ep1572 626178290149089569941733 ep1573

noncomputable def ep1651 := nat_lit 256010325535095380834036358023

noncomputable def ep1652 := nat_lit 580284393415022003858964480000000

noncomputable def ep1653 := nat_lit 8742702553820269547134676138125859

noncomputable def ep1654 := nat_lit 331274122753147112076421608188737

noncomputable def ep1655 := nat_lit 8165947895496336542978040820827011159

noncomputable def ep1656 := @Enclosure.Real.IsNear.addLit_tf_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz233) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz232) ep1651 ep1652 ep1653 ep1566 ep1654 ep1559 ep1655

noncomputable def ep1657 := nat_lit 169949383906736239786119416667673130802480950722915215605760000000

noncomputable def ep1658 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz233 13962002023 120000000 0 1 18336218911396972001 ep1572 626178290149089569941733 ep1573 ep1651

noncomputable def ep1659 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz232 317409618670361 90000000000 0 1 5218400818174083085 ep1572 180087911349146463044233 ep1573 ep1654

noncomputable abbrev qz518 := (@ep1623 ep1573 (BSN.cpow_neg_s_sub_mk qz12 136442 1000 35 3 64339296875 qz13 rfl EMRow47.d21) ep1647)

noncomputable def ep1660 := ep1562 (@ep1569 ep1570 ep1571 ep1553 ep1554 ep1555 ep1556 (@ep1574 ep1564 ep1565 ep1566 ep1621 (ep1622 qz518) rfl) (@ep1648 ep1554 ep1568 ep1570 ep1649 (ep1650 qz518) rfl) rfl rfl) (@ep1656 ep1570 ep1657 ep1558 ep1559 ep1560 ep1556 (@ep1658 ep1652 ep1653 ep1566 ep1621 (ep1650 qz518) rfl) (@ep1659 ep1559 ep1655 ep1570 ep1649 (ep1622 qz518) rfl) rfl rfl)

noncomputable def ep1661 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz76 (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.im (@HMul.hMul Complex Complex Complex qz76 (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) ep1558 ep1559 ep1560 ep1556 ep1558 ep1559 ep1560

noncomputable def ep1662 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz76 (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223) Bool.false ep1553 ep1554 ep1555 ep1556 Bool.false ep1558 ep1559 ep1560

noncomputable def ep1663 := @ep1524 2189103603938838799 4035225266123964416 39007057463 576460752303423488 (@ep1525 1 3670016 (ep1526 (@ep1527 1048576 1 1048576 (ep1528 (@ep1529 18628669364 4657167341 250000 0 1 (ep1533 rfl) (ep1536 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) (Enclosure.Real.IsNear.const Bool.false 2 7) rfl) (@ep1537 1801 1099511627776 (BSN.norm_eq_sqrt_mul_add (@HMul.hMul Complex Complex Complex qz76 (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (@ep1538 3602 2199023255552 15295915769 1099511627776 1801 1099511627776 (@ep1543 15295913968 15295917570 1099511627776 (@ep1549 ep1550 ep1551 ep1547 ep1552 ep1539 ep1540 ep1541 ep1542 (@ep1557 ep1556 ep1544 ep1545 ep1546 ep1547 (@ep1561 ep1556 ep1660) (@ep1561 ep1556 ep1660) rfl) (@ep1661 ep1556 ep1548 ep1550 ep1551 ep1547 (@ep1662 ep1556 ep1660) (@ep1662 ep1556 ep1660) rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl

theorem EMRow47.d22 : Enclosure.Real.IsNear (@HAdd.hAdd Real Real Real qz416 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 35))) (@HMul.hMul Real Real Real qz0 qz220 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz76 (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)))) Bool.false 67329069527750587541 108951082185347039232 1590748764731341 15564440312192434176 := ep1522 (ep1523 ep1663) rfl rfl

noncomputable abbrev qz711 := (@HAdd.hAdd Complex Complex Complex qz713 qz719 (@Nat.cast Complex Complex.instNatCast 3))

noncomputable abbrev qz519 := qz711

noncomputable abbrev qz243 := (@HDiv.hDiv Real Real Real qz270 (@Norm.norm Complex Complex.instNorm qz519) (@HAdd.hAdd Real Real Real qz416 (Complex.re qz444) qz289))

noncomputable abbrev qz520 := (@HPow.hPow Complex Complex Complex qz535 qz655 (@HSub.hSub Complex Complex Complex qz644 qz667 qz542))

noncomputable abbrev qz244 := qz520

noncomputable def ep1664 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz143 1 35))) (@HMul.hMul Real Real Real qz0 qz243 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz76 (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))) 24027903991 1855425871872 192230717 1855425871872 2322683257900564019 4035225266123964416 293856131901

noncomputable def ep1665 := nat_lit 4406524614149135468925575757824

noncomputable def ep1666 := @Enclosure.Real.IsNear.mulLit_ff (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz143 1 35)) 26561 1769472 1 1769472 904631 1048576 7203 1048576 24027903991 1855425871872

noncomputable def ep1667 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (zetaApproximant qz143 1 35)) (Real.sqrt (@HAdd.hAdd Real Real Real qz416 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz143 1 35)) (Complex.re (zetaApproximant qz143 1 35))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz143 1 35)) (Complex.im (zetaApproximant qz143 1 35))))) Bool.false 904631 1048576 7203 1048576

noncomputable def ep1668 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz416 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz143 1 35)) (Complex.re (zetaApproximant qz143 1 35))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz143 1 35)) (Complex.im (zetaApproximant qz143 1 35))))) Bool.false 904631 1048576 7203 1048576

noncomputable def ep1669 := nat_lit 190246368900825590208792896910826633611184021

noncomputable def ep1670 := nat_lit 255590953508411206890179181709728153600000000

noncomputable def ep1671 := nat_lit 560522117534128008306298873691763638898574295358073502738441099

noncomputable def ep1672 := nat_lit 47294894023491772881986150217661719107221007937365763686400000000

noncomputable def ep1673 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz416 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz143 1 35)) (Complex.re (zetaApproximant qz143 1 35))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz143 1 35)) (Complex.im (zetaApproximant qz143 1 35)))) ep1669 ep1670 ep1671 ep1672 448714 455917

noncomputable def ep1674 := nat_lit 36469824969323409928406362782940679577896535416154481

noncomputable def ep1675 := nat_lit 49013160181104392163470975360602451705723879424000000

noncomputable def ep1676 := nat_lit 60917435814619108959385290704156745320695143789325080634992451

noncomputable def ep1677 := nat_lit 5254988224832419209109572246406857678580111993040640409600000000

noncomputable def ep1678 := nat_lit 19675081482918878006042872497679199871063337596001

noncomputable def ep1679 := nat_lit 76583062782975612755423399000941330790193561600000000

noncomputable def ep1680 := nat_lit 5286722070067253306823817825152125436343966057822317682547

noncomputable def ep1681 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz143 1 35)) (Complex.re (zetaApproximant qz143 1 35))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz143 1 35)) (Complex.im (zetaApproximant qz143 1 35))) ep1674 ep1675 ep1676 ep1677 ep1678 ep1679 ep1680

noncomputable def ep1682 := nat_lit 20385730182539557276718168197267982373802158593692139520000000

noncomputable def ep1683 := nat_lit 2793935233230124936945058742940484913102243709956002477884598549172429733420628161998095732938113024000000

noncomputable def ep1684 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (zetaApproximant qz143 1 35)) (Complex.re (zetaApproximant qz143 1 35)) ep1245 ep1246 ep1247 ep1248 ep1245 ep1246 ep1247 ep1248 ep1674

noncomputable def ep1685 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (zetaApproximant qz143 1 35)) (Complex.im (zetaApproximant qz143 1 35)) ep1368 ep1369 ep1370 ep1371 ep1368 ep1369 ep1370 ep1371 ep1678

noncomputable def ep1686 := @ep1664 4035225266123964416 ep1665 64123372636810170209 108951082185347039232 11295771028864879 108951082185347039232 (@ep1666 192230717 1855425871872 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaStirlingErrorBound 1 2) (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 96 162) qz503) Bool.false 26561 1769472 1 1769472 (BSN.theta_err_eq 1 2 96 162 EMRow47.d18 EMRow47.d19 rfl) (ep1503 rfl)) (ep1667 (BSN.norm_eq_sqrt_mul_add (zetaApproximant qz143 1 35)) (@ep1668 904631 1048576 7203 1048576 (@ep1673 524288 (@ep1681 ep1682 ep1683 ep1669 ep1670 ep1671 ep1672 (@ep1684 ep1675 ep1676 ep1677 ep1483 ep1483 rfl) (@ep1685 ep1679 ep1680 ep1682 ep1491 ep1491 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl)

noncomputable abbrev qz245 := (@Norm.norm Complex Complex.instNorm qz519)

noncomputable def ep1687 := @Enclosure.Real.IsNear.of_eq (@HMul.hMul Real Real Real qz0 qz243 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz76 (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))) (@HMul.hMul Real Real Real qz0 (@HMul.hMul Real Real Real qz0 qz245 qz709) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz76 (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))) Bool.false 2322683257900564019 4035225266123964416 293856131901 4035225266123964416 (BSN.zrb_shape_eq qz245 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz76 (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) qz146 3)

noncomputable def ep1688 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz0 qz245 qz709) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz76 (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) 145251079 3670016 1 3670016 15990815861 1099511627776 1913 1099511627776

noncomputable def ep1689 := @Enclosure.Real.IsNear.mulLit_ff qz245 qz709 145251079 1048576 1 1048576 2 7 0 1 145251079 3670016

noncomputable abbrev qz521 := (Complex.re qz711)

noncomputable abbrev qz522 := (Complex.im qz711)

noncomputable abbrev qz246 := (@HAdd.hAdd Real Real Real qz416 (@HMul.hMul Real Real Real qz267 qz521 qz521) (@HMul.hMul Real Real Real qz267 qz522 qz522))

noncomputable abbrev qz247 := qz519

noncomputable def ep1690 := @Enclosure.Real.IsNear.of_eq qz245 (Real.sqrt qz246) Bool.false 145251079 1048576 1 1048576 (BSN.norm_eq_sqrt_mul_add qz247)

noncomputable def ep1691 := @Enclosure.Real.IsNear.recentre' (Real.sqrt qz246) Bool.false 145251079 1048576 1 1048576 145251079

noncomputable def ep1692 := @Enclosure.Real.IsNear.sqrt_image qz246 4797101621 250000 0 1 72625539 72625540 524288

noncomputable abbrev qz248 := (@HMul.hMul Real Real Real qz267 qz521 qz521)

noncomputable abbrev qz249 := (@HMul.hMul Real Real Real qz267 qz522 qz522)

noncomputable def ep1693 := @Enclosure.Real.IsNear.addLit_ff qz248 qz249 49 4 0 1 4794039121 250000 0 1

noncomputable abbrev qz250 := qz521

noncomputable def ep1694 := @Enclosure.Real.IsNear.mulLit_ff qz250 qz250 7 2 0 1 7 2 0 1 49 4

noncomputable def ep1695 := @Enclosure.Complex.IsNear.of_eq qz247 (Complex.mk qz508 qz146) Bool.false 7 2 0 1 Bool.false 138478 1000 0 1 (BSN.s_add_nat_mk qz146 Bool.false 138478 1000 3 qz147)

noncomputable abbrev qz523 := (ep1695 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7 2) qz146 Bool.false 7 2 0 1 Bool.false 138478 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 7 2) qz148))

noncomputable def ep1696 := @ep1694 0 1 (@Enclosure.Complex.IsNear.re_isNear qz247 Bool.false 7 2 0 1 Bool.false 138478 1000 0 1 qz523)

noncomputable def ep1697 := ep1696 (@Enclosure.Complex.IsNear.re_isNear qz247 Bool.false 7 2 0 1 Bool.false 138478 1000 0 1 qz523)

noncomputable abbrev qz251 := qz522

noncomputable def ep1698 := @Enclosure.Real.IsNear.mulLit_ff qz251 qz251 138478 1000 0 1 138478 1000 0 1 4794039121 250000

noncomputable def ep1699 := @ep1698 0 1 (@Enclosure.Complex.IsNear.im_isNear qz247 Bool.false 7 2 0 1 Bool.false 138478 1000 0 1 qz523)

noncomputable def ep1700 := ep1699 (@Enclosure.Complex.IsNear.im_isNear qz247 Bool.false 7 2 0 1 Bool.false 138478 1000 0 1 qz523)

noncomputable def ep1701 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz76 (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Real.sqrt (@HAdd.hAdd Real Real Real qz416 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz76 (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.re (@HMul.hMul Complex Complex Complex qz76 (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz76 (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.im (@HMul.hMul Complex Complex Complex qz76 (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))))) Bool.false 15990815861 1099511627776

noncomputable def ep1702 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz416 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz76 (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.re (@HMul.hMul Complex Complex Complex qz76 (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz76 (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.im (@HMul.hMul Complex Complex Complex qz76 (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))))) Bool.false 31981631722 2199023255552

noncomputable def ep1703 := nat_lit 20031612181733698283232960562668989800766289855217739265549741455729

noncomputable def ep1704 := nat_lit 416476270752596505306305496276026098670130084384482418955732344830179214707740825379

noncomputable def ep1705 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz416 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz76 (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.re (@HMul.hMul Complex Complex Complex qz76 (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz76 (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.im (@HMul.hMul Complex Complex Complex qz76 (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)))) ep1703 ep1540 ep1704 ep1542

noncomputable def ep1706 := nat_lit 2556873513921667420487482755781630283193709167187159842878296351561

noncomputable def ep1707 := nat_lit 21045623577565002022133061591114475483045428618854400000000000000000000

noncomputable def ep1708 := nat_lit 54313821441364326519398641849130080652582572754134116928198015527782439732890863931

noncomputable def ep1709 := nat_lit 1829227391575227039922795927752633064488875917952178700367230402560000000000000000000000000000

noncomputable def ep1710 := nat_lit 17051362738172389782078576323303307052789197205751039945194815747409

noncomputable def ep1711 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz76 (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.re (@HMul.hMul Complex Complex Complex qz76 (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz76 (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.im (@HMul.hMul Complex Complex Complex qz76 (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))) ep1706 ep1707 ep1708 ep1709 ep1710

noncomputable def ep1712 := nat_lit 344128148532914071938023215909881471467017013981757785557682549910316471819463875379

noncomputable def ep1713 := nat_lit 843155539257066061428553655572543649450594806234436384059244300579441931857875344238505017509449993170367551504593715200000000000000000000

noncomputable def ep1714 := nat_lit 1599022674611485120227122152591331

noncomputable def ep1715 := nat_lit 145071098353755500964741120000000000

noncomputable def ep1716 := nat_lit 57606669431184523055255035111155730709

noncomputable def ep1717 := nat_lit 42769467983308221645920174447001600000000000000

noncomputable def ep1718 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz76 (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.re (@HMul.hMul Complex Complex Complex qz76 (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) ep1714 ep1715 ep1716 ep1717 ep1714 ep1715 ep1716

noncomputable def ep1719 := nat_lit 4129329574903460013490114355222903

noncomputable def ep1720 := nat_lit 141337589925787839312935394816499135877

noncomputable def ep1721 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz76 (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz244) Bool.false ep1714 ep1715 ep1716 ep1717 Bool.true ep1719 ep1554 ep1720

noncomputable def ep1722 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz244 Bool.false ep1714 ep1715 ep1716 ep1717 Bool.true ep1719 ep1554 ep1720 ep1556

noncomputable def ep1723 := nat_lit 172026335365549025738041210481

noncomputable def ep1724 := nat_lit 5888360377517548406190240953402579

noncomputable def ep1725 := nat_lit 1642029258452872376661632455211581

noncomputable def ep1726 := nat_lit 18711526445601711984569158290935028653

noncomputable abbrev qz252 := (Complex.re qz520)

noncomputable abbrev qz253 := (Complex.im qz520)

noncomputable def ep1727 := @Enclosure.Real.IsNear.subLit_tt_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3)))) qz252) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3)))) qz253) ep1723 ep1652 ep1724 ep1566 ep1725 ep1715 ep1726

noncomputable def ep1728 := nat_lit 14256489327769407215306724815667200000000000000

noncomputable def ep1729 := nat_lit 927887902793791748452707082060533455414836293753086284922880000000

noncomputable def ep1730 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3)))) qz252 14381804863 120000000 0 1 11961387114083319887 ep1572 409431252447772028026733 ep1573 ep1723

noncomputable def ep1731 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3)))) 14381804863 120000000 0 1 0 1 0 1 14381804863

noncomputable def ep1732 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 43145414589 500000 0 1 14381804863 120000000 0

noncomputable abbrev qz524 := (@HAdd.hAdd Complex Complex Complex qz534 qz666 qz543)

noncomputable abbrev qz254 := qz524

noncomputable def ep1733 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3)) (@HMul.hMul Complex Complex Complex qz76 (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 2)) qz254) Bool.true 43145414589 500000 0 1 Bool.true 331834943636419 125000000 0 1

noncomputable abbrev qz255 := (Complex.re qz524)

noncomputable abbrev qz256 := (Complex.im qz524)

noncomputable def ep1734 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 2))) qz255) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 2))) qz256) 4793851621 100000 0 1 4794039121 125000 0 1

noncomputable def ep1735 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 2))) qz255 4793851621 250000 0 1 5 2 0 1 4793851621 100000

noncomputable abbrev qz525 := (@HAdd.hAdd Complex Complex Complex qz534 qz666 (@Nat.cast Complex Complex.instNatCast 1))

noncomputable abbrev qz257 := qz525

noncomputable def ep1736 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 2)) (@HMul.hMul Complex Complex Complex qz76 (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1)) qz257) Bool.true 4793851621 250000 0 1 Bool.false 69239 250 0 1

noncomputable abbrev qz258 := (Complex.re qz525)

noncomputable abbrev qz259 := (Complex.im qz525)

noncomputable def ep1737 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1))) qz258) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1))) qz259) 3 4 0 1 4794039121 250000 0 1

noncomputable def ep1738 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1))) qz258 1 2 0 1 3 2 0 1 3 4

noncomputable def ep1739 := @ep1738 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 138478 1000 0 1 ep1444)

noncomputable def ep1740 := @Enclosure.Complex.IsNear.of_eq qz257 (Complex.mk qz512 qz146) Bool.false 3 2 0 1 Bool.false 138478 1000 0 1 (BSN.s_add_nat_mk qz146 Bool.false 138478 1000 1 qz147)

noncomputable abbrev qz526 := (ep1740 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 3 2) qz146 Bool.false 3 2 0 1 Bool.false 138478 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 3 2) qz148))

noncomputable def ep1741 := ep1739 (@Enclosure.Complex.IsNear.re_isNear qz257 Bool.false 3 2 0 1 Bool.false 138478 1000 0 1 qz526)

noncomputable def ep1742 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1))) qz259 138478 1000 0 1 138478 1000 0 1 4794039121 250000

noncomputable def ep1743 := @ep1742 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 138478 1000 0 1 ep1444)

noncomputable def ep1744 := ep1743 (@Enclosure.Complex.IsNear.im_isNear qz257 Bool.false 3 2 0 1 Bool.false 138478 1000 0 1 qz526)

noncomputable def ep1745 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1)) qz257 Bool.true 4793851621 250000 0 1 Bool.false 69239 250 0 1 (@ep1737 19175406484 4793851621 250000 0 1 (ep1741 rfl) (ep1744 rfl) rfl rfl)

noncomputable def ep1746 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1))) qz259) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1))) qz258) 69239 1000 0 1 207717 1000 0 1

noncomputable def ep1747 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1))) qz259 1 2 0 1 138478 1000 0 1 69239 1000

noncomputable def ep1748 := @ep1747 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 138478 1000 0 1 ep1444)

noncomputable def ep1749 := ep1748 (@Enclosure.Complex.IsNear.im_isNear qz257 Bool.false 3 2 0 1 Bool.false 138478 1000 0 1 qz526)

noncomputable def ep1750 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1))) qz258 138478 1000 0 1 3 2 0 1 207717 1000

noncomputable def ep1751 := @ep1750 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 138478 1000 0 1 ep1444)

noncomputable def ep1752 := ep1751 (@Enclosure.Complex.IsNear.re_isNear qz257 Bool.false 3 2 0 1 Bool.false 138478 1000 0 1 qz526)

noncomputable abbrev qz260 := (ep1736 (BSN.ascPochhammer_succ_eval_c 1 2 qz444 rfl) (ep1745 (@ep1746 276956000 69239 250 0 1 (ep1749 rfl) (ep1752 rfl) rfl rfl)))

noncomputable def ep1753 := @ep1735 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 4793851621 250000 0 1 Bool.false 69239 250 0 1 qz260)

noncomputable def ep1754 := @Enclosure.Complex.IsNear.of_eq qz254 (Complex.mk qz514 qz146) Bool.false 5 2 0 1 Bool.false 138478 1000 0 1 (BSN.s_add_nat_mk qz146 Bool.false 138478 1000 2 qz147)

noncomputable abbrev qz527 := (ep1754 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 5 2) qz146 Bool.false 5 2 0 1 Bool.false 138478 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 5 2) qz148))

noncomputable def ep1755 := ep1753 (@Enclosure.Complex.IsNear.re_isNear qz254 Bool.false 5 2 0 1 Bool.false 138478 1000 0 1 qz527)

noncomputable def ep1756 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 2))) qz256 69239 250 0 1 138478 1000 0 1 4794039121 125000

noncomputable def ep1757 := @ep1756 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 4793851621 250000 0 1 Bool.false 69239 250 0 1 qz260)

noncomputable def ep1758 := ep1757 (@Enclosure.Complex.IsNear.im_isNear qz254 Bool.false 5 2 0 1 Bool.false 138478 1000 0 1 qz527)

noncomputable def ep1759 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 2)) qz254 Bool.true 43145414589 500000 0 1 Bool.true 331834943636419 125000000 0 1 (@ep1734 1078635364725000 43145414589 500000 0 1 (ep1755 rfl) (ep1758 rfl) rfl rfl)

noncomputable def ep1760 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 2))) qz256) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 2))) qz255) 331921492386419 125000000 0 1 69239 100 0 1

noncomputable def ep1761 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 2))) qz256 4793851621 250000 0 1 138478 1000 0 1 331921492386419 125000000

noncomputable def ep1762 := @ep1761 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 4793851621 250000 0 1 Bool.false 69239 250 0 1 qz260)

noncomputable def ep1763 := ep1762 (@Enclosure.Complex.IsNear.im_isNear qz254 Bool.false 5 2 0 1 Bool.false 138478 1000 0 1 qz527)

noncomputable def ep1764 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 2))) qz255 69239 250 0 1 5 2 0 1 69239 100

noncomputable def ep1765 := @ep1764 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 4793851621 250000 0 1 Bool.false 69239 250 0 1 qz260)

noncomputable def ep1766 := ep1765 (@Enclosure.Complex.IsNear.re_isNear qz254 Bool.false 5 2 0 1 Bool.false 138478 1000 0 1 qz527)

noncomputable abbrev qz261 := (ep1733 (BSN.ascPochhammer_succ_eval_c 2 3 qz444 rfl) (ep1759 (@ep1760 33183494363641900 331834943636419 125000000 0 1 (ep1763 rfl) (ep1766 rfl) rfl rfl)))

noncomputable def ep1767 := @ep1732 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1577) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 43145414589 500000 0 1 Bool.true 331834943636419 125000000 0 1 qz261)

noncomputable def ep1768 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 331834943636419 125000000 0 1 0 1 0

noncomputable def ep1769 := @ep1768 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1577) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 43145414589 500000 0 1 Bool.true 331834943636419 125000000 0 1 qz261)

noncomputable def ep1770 := @Enclosure.Real.IsNear.addLit_ft_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3)))) 331834943636419 90000000000 0 1 0 1 0 1 331834943636419

noncomputable def ep1771 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 331834943636419 125000000 0 1 331834943636419 90000000000 0

noncomputable def ep1772 := @ep1771 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1577) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 43145414589 500000 0 1 Bool.true 331834943636419 125000000 0 1 qz261)

noncomputable def ep1773 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 43145414589 500000 0 1 0 1 0

noncomputable def ep1774 := @ep1773 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1577) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 43145414589 500000 0 1 Bool.true 331834943636419 125000000 0 1 qz261)

noncomputable def ep1775 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.false 14381804863 120000000 0 1 Bool.false 331834943636419 90000000000 0 1 (@ep1731 14381804863 120000000 0 1 (ep1767 rfl) (ep1769 rfl) rfl rfl) (@ep1770 331834943636419 90000000000 0 1 (ep1772 rfl) (ep1774 rfl) rfl rfl)

noncomputable def ep1776 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 14381804863 120000000 0 1 Bool.false 331834943636419 90000000000 0 1 ep1775

noncomputable def ep1777 := @Enclosure.Complex.IsNear.re_isNear qz244 Bool.true 11961387114083319887 ep1572 409431252447772028026733 ep1573 Bool.true 14844994084637375997 ep1572 507492478534539239782983 ep1573

noncomputable def ep1778 := @Enclosure.Complex.IsNear.of_eq qz244 (Complex.mk (@HMul.hMul Real Real Real qz0 qz242 (Real.cos qz217)) (@HMul.hMul Real Real Real qz0 qz242 qz705)) Bool.true 11961387114083319887 ep1572 409431252447772028026733 ep1573 Bool.true 14844994084637375997 ep1572 507492478534539239782983

noncomputable def ep1779 := @Enclosure.Real.IsNear.mulLit_ff qz146 qz134 138478 1000 0 1 16011864204894419 4503599627370496 320471707663 94341532600000000000000 1108645465682684677141 2251799813685248000 22189140566878457 ep1625 qz148 (BSN.isNear_log_sfrac 35 1 16011864204894419 4503599627370496 320471707663 94341532600000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' qz440 Bool.false ep1626 ep1627 1001474086446875 ep1628 16011864204894419 4503599627370496 320471707663 94341532600000000000000 (BSN.log_rat_reduce_isNear 35 1 5 70 64 98529610469 1099511627776 24973259072661432 36028797018963968 294817289375 1000000000000000 rfl rfl rfl rfl (ep1629 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1780 := nat_lit 107471191623630248321499529216

noncomputable def ep1781 := nat_lit 158456325028528675187087900672

noncomputable def ep1782 := nat_lit 764498598601605084404053996011323386058548590052229350790531067981504756809501009972513758868533174645862103302394516923876356649119192535119062193694791851239431111180007471770663645958379667456

noncomputable def ep1783 := nat_lit 659640197372256341157164257844167503953370023838368371919173698743042232652429757043226922519718095803519575534335929030058780207253440629221487441237552463134387145724474483531008966656

noncomputable def ep1784 := nat_lit 3822327649320409121566701721905592379460863183514177305864788365798023610073120487448823993099042242755044658447231647508002678557191876535777087519370781443761849805719750505052683876627294191616

noncomputable def ep1785 := BSN.sin_dyadic_bound_f 3054514980466088 4503599627370496 4 3 2199023255552 590210393769 ep1782 ep1641 ep1783 ep1784 ep1644 ep1783 1379716472779 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 3054514980466088) (BSN.sinEvenQ 4503599627370496) 0 3 ep1782 ep1641 ep1783 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 3054514980466088) (BSN.sinOddQ 4503599627370496) 0 3 ep1784 ep1644 ep1783 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz528 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 541330793790373) (@Nat.cast Real Real.instNatCast 1099511627776))

noncomputable def ep1786 := @Enclosure.Real.IsNear.cos_image qz217 qz528 Bool.false 541330793790373 1099511627776 259 549755813888 Bool.true 1379716472779 2199023255552 1 294817289375 (@Enclosure.Real.IsNear.recentre' qz217 Bool.false 1108645465682684677141 2251799813685248000 22189140566878457 ep1625 541330793790373 1099511627776 259 549755813888 (ep1779 rfl) rfl) (Enclosure.sfrac_false_div 541330793790373 1099511627776) (BSN.cos_reduce1 qz528 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep1780) (@Nat.cast Real Real.instNatCast ep1781)) 226375608064910080 72057594037927936 Bool.false 1379716472779 2199023255552 78 1000000000000000 589634578750 294817289375 (BSN.sin_reduce_arg_pos_rat_q1 541330793790373 1099511627776 226375608064910080 72057594037927936 78 ep1780 ep1781 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1379716472779 2199023255552 ep1780 ep1781 3054514980466088 4503599627370496 590210393769 589634578750 (ep1785 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1787 := nat_lit 294054382234962535104938442153072001401801019061694949408913556836910614008642866009423907100723674191305865414917530229085770188972138961580481233244156635331813978211391533388665795862316711936

noncomputable def ep1788 := nat_lit 33346807186065974506248031997757090226592655702784298773854402813442710020953735382387552583030990727053975099387314435621209513297521804838009978888016542842337137637482389641015882426221173145600

noncomputable def ep1789 := nat_lit 1783780136011372877527745760125801051136346309470792060606950747220197092336659365423174841590725324890739220895008074490319574181399701799991092939342622987491534468893811644304756237955172925440

noncomputable def ep1790 := nat_lit 3034559453932003680068570911795895210619931668953371188420750656023286611906789919797267285055820156161911734044245613641530065710074484240258908078809505398652679525010897457332445300786126756249600

noncomputable def ep1791 := BSN.cos_dyadic_bound_f 3054514980466088 4503599627370496 4 3 2199023255552 590210393769 ep1787 ep1788 ep1783 ep1789 ep1790 ep1783 1712333417649 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 3054514980466088) (BSN.cosEvenQ 4503599627370496) 0 3 ep1787 ep1788 ep1783 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 3054514980466088) (BSN.cosOddQ 4503599627370496) 0 3 ep1789 ep1790 ep1783 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1792 := @Enclosure.Real.IsNear.sin_image qz217 qz528 Bool.false 541330793790373 1099511627776 259 549755813888 Bool.false 1712333417649 2199023255552 1 294817289375 (@Enclosure.Real.IsNear.recentre' qz217 Bool.false 1108645465682684677141 2251799813685248000 22189140566878457 ep1625 541330793790373 1099511627776 259 549755813888 (ep1779 rfl) rfl) (Enclosure.sfrac_false_div 541330793790373 1099511627776) (BSN.sin_reduce1 qz528 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep1780) (@Nat.cast Real Real.instNatCast ep1781)) 226375608064910080 72057594037927936 Bool.false 1712333417649 2199023255552 78 1000000000000000 589634578750 294817289375 (BSN.sin_reduce_arg_pos_rat_q1 541330793790373 1099511627776 226375608064910080 72057594037927936 78 ep1780 ep1781 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1712333417649 2199023255552 ep1780 ep1781 3054514980466088 4503599627370496 590210393769 589634578750 (ep1791 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1793 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz242 (Real.cos qz217)) (@HMul.hMul Real Real Real qz0 qz242 qz705) Bool.true 11961387114083319887 ep1572 409431252447772028026733 ep1573 Bool.true 14844994084637375997 ep1572 507492478534539239782983 ep1573 (@Enclosure.Real.IsNear.mulLit_ft qz242 (Real.cos qz217) 8669453 2199023255552 1 2199023255552 1379716472779 2199023255552 76907433762013 162077518868607139840000 11961387114083319887 ep1572 409431252447772028026733 ep1573 qz517 (@Enclosure.Real.IsNear.recentre' (Real.cos qz217) Bool.true 1379716472779 2199023255552 76907433762013 162077518868607139840000 1379716472779 2199023255552 76907433762013 162077518868607139840000 (ep1786 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz242 qz705 8669453 2199023255552 1 2199023255552 1712333417649 2199023255552 76907433762013 162077518868607139840000 14844994084637375997 ep1572 507492478534539239782983 ep1573 qz517 (@Enclosure.Real.IsNear.neg qz218 Bool.false 1712333417649 2199023255552 76907433762013 162077518868607139840000 (@Enclosure.Real.IsNear.recentre' qz218 Bool.false 1712333417649 2199023255552 76907433762013 162077518868607139840000 1712333417649 2199023255552 76907433762013 162077518868607139840000 (ep1792 rfl rfl) rfl)) rfl)

noncomputable def ep1794 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3)))) qz253 331834943636419 90000000000 0 1 14844994084637375997 ep1572 507492478534539239782983 ep1573 ep1725

noncomputable def ep1795 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 14381804863 120000000 0 1 Bool.false 331834943636419 90000000000 0 1 ep1775

noncomputable def ep1796 := @Enclosure.Complex.IsNear.im_isNear qz244 Bool.true 11961387114083319887 ep1572 409431252447772028026733 ep1573 Bool.true 14844994084637375997 ep1572 507492478534539239782983 ep1573

noncomputable def ep1797 := nat_lit 71165936039214682568404691137

noncomputable def ep1798 := nat_lit 193428131138340667952988160000000

noncomputable def ep1799 := nat_lit 2432885931907986517391742658015443

noncomputable def ep1800 := nat_lit 57025957311077628861226899262668800000000000

noncomputable def ep1801 := nat_lit 3969206218815226977711203800164653

noncomputable def ep1802 := nat_lit 135863596578994869648803973835964389127

noncomputable def ep1803 := @Enclosure.Real.IsNear.addLit_tt (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3)))) qz253) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3)))) qz252) ep1797 ep1798 ep1799 ep1800 ep1801 ep1554 ep1802

noncomputable def ep1804 := nat_lit 798728502527854987432800919201918169381623592269761719828480000000

noncomputable def ep1805 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3)))) qz253 14381804863 120000000 0 1 14844994084637375997 ep1572 507492478534539239782983 ep1573 ep1797

noncomputable def ep1806 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3)))) qz252 331834943636419 90000000000 0 1 11961387114083319887 ep1572 409431252447772028026733 ep1573 ep1801

noncomputable abbrev qz529 := (@ep1778 ep1573 (BSN.cpow_neg_s_sub_mk qz146 138478 1000 35 3 64339296875 qz147 rfl EMRow47.d21) ep1793)

noncomputable def ep1807 := ep1722 (@ep1727 ep1728 ep1729 ep1714 ep1715 ep1716 ep1717 (@ep1730 ep1652 ep1724 ep1566 ep1776 (ep1777 qz529) rfl) (@ep1794 ep1715 ep1726 ep1728 ep1795 (ep1796 qz529) rfl) rfl rfl) (@ep1803 ep1556 ep1804 ep1719 ep1554 ep1720 ep1556 (@ep1805 ep1798 ep1799 ep1800 ep1776 (ep1796 qz529) rfl) (@ep1806 ep1554 ep1802 ep1556 ep1795 (ep1777 qz529) rfl) rfl rfl)

noncomputable def ep1808 := @Enclosure.Real.IsNear.mulLit_tt (Complex.im (@HMul.hMul Complex Complex Complex qz76 (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.im (@HMul.hMul Complex Complex Complex qz76 (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) ep1719 ep1554 ep1720 ep1556 ep1719 ep1554 ep1720

noncomputable def ep1809 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz76 (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz244) Bool.false ep1714 ep1715 ep1716 ep1717 Bool.true ep1719 ep1554 ep1720

noncomputable def ep1810 := @ep1688 2322683257900564019 4035225266123964416 293856131901 4035225266123964416 (@ep1689 1 3670016 (ep1690 (@ep1691 1048576 1 1048576 (ep1692 (@ep1693 19188406484 4797101621 250000 0 1 (ep1697 rfl) (ep1700 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) (Enclosure.Real.IsNear.const Bool.false 2 7) rfl) (@ep1701 1913 1099511627776 (BSN.norm_eq_sqrt_mul_add (@HMul.hMul Complex Complex Complex qz76 (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (@ep1702 3826 2199023255552 15990815861 1099511627776 1913 1099511627776 (@ep1705 15990813948 15990817774 1099511627776 (@ep1711 ep1545 ep1712 ep1547 ep1713 ep1703 ep1540 ep1704 ep1542 (@ep1718 ep1717 ep1706 ep1707 ep1708 ep1709 (@ep1721 ep1556 ep1807) (@ep1721 ep1556 ep1807) rfl) (@ep1808 ep1556 ep1710 ep1545 ep1712 ep1547 (@ep1809 ep1556 ep1807) (@ep1809 ep1556 ep1807) rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl

theorem EMRow47.d23 : Enclosure.Real.IsNear (@HAdd.hAdd Real Real Real qz416 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz143 1 35))) (@HMul.hMul Real Real Real qz0 qz243 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz76 (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)))) Bool.false 64123372636810170209 108951082185347039232 11295771028864879 108951082185347039232 := ep1686 (ep1687 ep1810) rfl rfl

noncomputable def EMRow47.d24 := fun (I J : @NonemptyInterval Real Real.instLE) => @LE.le Real Real.instLE (@Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE I)) (@Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE J))

noncomputable abbrev qz530 := (EMRow47.d3 qz545 qz673 (@Enclosure.dec_le_dec qz545 qz673 136442 1000 138478 1000 (@Eq.refl Real qz545) (@Eq.refl Real qz673) rfl rfl rfl) 35 35 1 1)

noncomputable abbrev qz262 := qz530

noncomputable def ep1811 := @Zeta.Certificates.ZIntervalEM.Certificate.mk qz262 (@Enclosure.dec_nonneg qz12 136442 1000 qz13) (@Enclosure.pos_of_ble 1 rfl) (@Enclosure.pos_of_ble 35 rfl)

noncomputable abbrev qz263 := (Zeta.Certificates.ZIntervalEM.fstVal qz530)

noncomputable def ep1812 := @Enclosure.Real.IsNear.neg_val qz263 ep526 ep527

noncomputable def ep1813 := @Enclosure.Real.IsNear.of_eq qz263 (hardyZApproximantEM 1 35 qz12) Bool.true

noncomputable abbrev qz264 := (Zeta.Certificates.ZIntervalEM.sndVal qz530)

noncomputable def ep1814 := BSN.mul_neg_of_neg_pos_r qz263 qz264 (@ep1812 ep528 ep529 (@ep1813 ep526 ep527 ep528 ep529 (@Eq.refl Real (hardyZApproximantEM 1 35 qz12)) EMRow47.d12) rfl rfl rfl)

noncomputable def ep1815 := @Enclosure.Real.IsNear.pos_val qz264 ep1229 ep1230

noncomputable def ep1816 := @Enclosure.Real.IsNear.of_eq qz264 (hardyZApproximantEM 1 35 qz146) Bool.false

noncomputable def ep1817 := BSN.gt_trans_le (@Norm.norm Real Real.norm qz263) (BSN.hardyZErrorBoundStrong 1 35 qz12)

noncomputable def ep1818 := @Enclosure.norm_gt_of_isNear qz263 (BSN.hardyZErrorBoundStrong 1 35 qz12) Bool.true

noncomputable def ep1819 := @Enclosure.Real.IsNear.of_eq (BSN.hardyZErrorBoundStrong 1 35 qz12) (@HAdd.hAdd Real Real Real qz416 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 35))) (@HMul.hMul Real Real Real qz0 qz220 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz76 (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)))) Bool.false 67329069527750587541 108951082185347039232 1590748764731341 15564440312192434176 (@Eq.refl Real (@HAdd.hAdd Real Real Real qz416 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 35))) (@HMul.hMul Real Real Real qz0 qz220 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz76 (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)))))

noncomputable def ep1820 := BSN.gt_trans_le (@Norm.norm Real Real.norm qz264) (BSN.hardyZErrorBoundStrong 1 35 qz146)

noncomputable def ep1821 := @Enclosure.norm_gt_of_isNear qz264 (BSN.hardyZErrorBoundStrong 1 35 qz146) Bool.false

noncomputable def ep1822 := @Enclosure.Real.IsNear.of_eq (BSN.hardyZErrorBoundStrong 1 35 qz146) (@HAdd.hAdd Real Real Real qz416 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz143 1 35))) (@HMul.hMul Real Real Real qz0 qz243 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz76 (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)))) Bool.false 64123372636810170209 108951082185347039232 11295771028864879 108951082185347039232 (@Eq.refl Real (@HAdd.hAdd Real Real Real qz416 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz143 1 35))) (@HMul.hMul Real Real Real qz0 qz243 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz76 (@HMul.hMul Complex Complex Complex qz76 (@HDiv.hDiv Complex Complex Complex qz83 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)))))

noncomputable def ep1823 := @List.cons EMRow47.d0 (@PSigma.mk Zeta.Certificates.ZIntervalEM Zeta.Certificates.ZIntervalEM.Certificate qz262 (ep1811 (@Enclosure.pos_of_ble 1 rfl) (@Enclosure.pos_of_ble 35 rfl) (ep1814 (@ep1815 ep1231 ep1232 (@ep1816 ep1229 ep1230 ep1231 ep1232 (@Eq.refl Real (hardyZApproximantEM 1 35 qz146)) EMRow47.d17) rfl rfl rfl)) (ep1817 (hardyZErrorBoundEM 1 35 qz12) (BSN.hardyZErrorBoundEM_le_strong 1 35 qz12 rfl) (@ep1818 Bool.false ep526 ep527 ep528 ep529 67329069527750587541 108951082185347039232 1590748764731341 15564440312192434176 (@ep1813 ep526 ep527 ep528 ep529 (@Eq.refl Real (hardyZApproximantEM 1 35 qz12)) EMRow47.d12) (ep1819 EMRow47.d22) rfl rfl rfl rfl rfl)) (ep1820 (hardyZErrorBoundEM 1 35 qz146) (BSN.hardyZErrorBoundEM_le_strong 1 35 qz146 rfl) (@ep1821 Bool.false ep1229 ep1230 ep1231 ep1232 64123372636810170209 108951082185347039232 11295771028864879 108951082185347039232 (@ep1816 ep1229 ep1230 ep1231 ep1232 (@Eq.refl Real (hardyZApproximantEM 1 35 qz146)) EMRow47.d17) (ep1822 EMRow47.d23) rfl rfl rfl rfl rfl)))) (@List.nil EMRow47.d0)

noncomputable abbrev qz531 := (@Enclosure.dec_le_dec qz545 qz673 136442 1000 138478 1000 (@Eq.refl Real qz545) (@Eq.refl Real qz673) rfl rfl rfl)

noncomputable abbrev qz265 := (Zeta.Certificates.CertifiedZeroIntervals.intervals (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedEM ep1823 (@List.IsChain.singleton EMRow47.d1 EMRow47.d24 (EMRow47.d2 qz277 qz446 qz531))))

noncomputable abbrev qz532 := (@NonemptyInterval Real Real.instLE)

noncomputable def ep1824 := And (@Eq (Option Real) (@Option.map qz532 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz532 qz265)) (@Option.some Real qz12))

noncomputable def ep1825 := ep1824 (@Eq (Option Real) (@Option.map qz532 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz532 qz265)) (@Option.some Real qz146))

noncomputable def ep1826 := @And.intro (@Eq Nat (@List.length qz532 qz265) 1) ep1825

noncomputable def ep1827 := @And.intro (@Eq (Option Real) (@Option.map qz532 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz532 qz265)) (@Option.some Real qz12))

noncomputable def ep1828 := @ep1827 (@Eq (Option Real) (@Option.map qz532 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz532 qz265)) (@Option.some Real qz146))

noncomputable abbrev qz266 := (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedEM ep1823 (@List.IsChain.singleton EMRow47.d1 EMRow47.d24 (EMRow47.d2 qz277 qz446 qz531)))

theorem EMRow47.d25 : Zeta.Certificates.BatchSpec 1 136442 1000 138478 1000 := @Exists.intro Zeta.Certificates.CertifiedZeroIntervals (fun (C : Zeta.Certificates.CertifiedZeroIntervals) => And (@Eq Nat (@List.length qz532 (Zeta.Certificates.CertifiedZeroIntervals.intervals C)) 1) (And (@Eq (Option Real) (@Option.map qz532 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz532 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz12)) (@Eq (Option Real) (@Option.map qz532 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz532 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz146)))) qz266 (ep1826 (@Eq.refl Nat 1) (ep1828 (@Eq.refl (Option Real) (@Option.some Real qz12)) (@Eq.refl (Option Real) (@Option.some Real qz146))))

theorem solution : Zeta.Certificates.BatchSpec 1 136442 1000 138478 1000 := EMRow47.d25
#print axioms solution
#check solution
