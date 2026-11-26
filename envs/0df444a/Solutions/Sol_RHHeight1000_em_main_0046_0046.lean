-- Prove2me | solution 1 for RHHeight1000.em_main_0046_0046
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-20T08:32:42.441978+00:00
-- url     : https://prove2.me/submissions/e39300df-36c2-4e8f-b317-921c6107b4aa

import Definitions.Def_RHT1000_Support_20261118_S005
/- Copyright (c) 2026 Salvatore Mercuri, Bhavik Mehta.
Apache 2.0 license; see the source project LICENSE. -/
set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable def EMRow46.d0 := @PSigma Zeta.Certificates.ZIntervalEM fun (I : Zeta.Certificates.ZIntervalEM) => Zeta.Certificates.ZIntervalEM.Certificate I

noncomputable def EMRow46.d1 := @NonemptyInterval Real Real.instLE

noncomputable def EMRow46.d2 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @NonemptyInterval.mk Real Real.instLE (@Prod.mk Real Real a b) h

noncomputable def EMRow46.d3 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) (fc sc fb sb : Nat) => Zeta.Certificates.ZIntervalEM.mk (EMRow46.d2 a b h) fc sc fb sb

noncomputable def ep0 := nat_lit 26986075409044028275299783

noncomputable def ep1 := nat_lit 4294967296000000000000000

noncomputable def ep2 := nat_lit 26986075409044045455168967

noncomputable abbrev qz269 := (@instHMul Real Real.instMul)

noncomputable abbrev qz0 := qz269

noncomputable abbrev qz270 := (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 2 1) Real.pi)

noncomputable def ep3 := @BSN.isNear_log_image_fff qz270 884279719003555 140737488355328 1 500000000000000 ep0 ep1 ep2 ep1 4138529546116343 2251799813685248 250000000195407 97703500000000000000 4138529546116343 2251799813685248 250000000195407 97703500000000000000 963576 524288

noncomputable abbrev qz271 := (@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 2 1) Real.pi 2 1 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 140737488355328 1 500000000000000 (Enclosure.Real.IsNear.const Bool.false 2 1) BSN.pi_near_15 rfl)

noncomputable def ep4 := @ep3 2 524288 qz271 rfl rfl rfl rfl

noncomputable def ep5 := nat_lit 53972150818088056550599566

noncomputable def ep6 := nat_lit 34359738368000000000000000

noncomputable def ep7 := nat_lit 9806206225044028275299783

noncomputable def ep8 := nat_lit 44165944593044028275299783

noncomputable def ep9 := nat_lit 13681445815609410487519367394620474863599256634174726093703677122907123617368241606644861540940610176751640793056574796245399519365549113997355475306157239709119582688278313060810592403844863400465080549957745

noncomputable def ep10 := nat_lit 231714499556395493334623298703961145503103241611736774613091488581016477543539392410113701224645713379230392133956226737605624599560350113120270717249177907454870984269546186598262646369758174842349131395304

noncomputable def ep11 := nat_lit 8978369550011295664474073352761810093897501552430546263638635096022803738134167562509900960712119243631997923545019968443113540909076206607473711060286601587364321108377403290080403445693385008949995305

noncomputable def ep12 := BSN.log_dyadic_bound ep7 ep8 5 4 ep9 1048576 390814 ep10 ep11 473518 ep5 ep6 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP ep7) (BSN.artanhQ ep8) 0 4 ep10 ep9 ep11 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz272 := (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))

noncomputable abbrev qz1 := qz272

noncomputable def ep13 := ep4 rfl rfl rfl rfl (BSN.isNear_log_sfrac ep0 ep1 4138529546116343 2251799813685248 250000000195407 97703500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep0) (@Nat.cast Real Real.instNatCast ep1))) Bool.false 69433004117575847641088 37778931862957161709568 1000000000781628 390814000000000000000 4138529546116343 2251799813685248 250000000195407 97703500000000000000 (BSN.log_rat_reduce_isNear ep0 ep1 2 ep5 ep6 473518 1048576 24973259072661432 36028797018963968 390814 1000000000000000 rfl rfl rfl rfl (ep12 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep14 := nat_lit 53972150818088090910337934

noncomputable def ep15 := nat_lit 9806206225044045455168967

noncomputable def ep16 := nat_lit 44165944593044045455168967

noncomputable def ep17 := nat_lit 13681445815609453062485491347592146866046743284321690683909457683007658987562290830600045658905080811372395010565947827677605470036294121079488508864180301737865471494204890974265645509835068840465080549957745

noncomputable def ep18 := nat_lit 231714499556396865510889920206523150079811393376960301632499817942333196803513131357563499488546302200815366867712007119763002650772307103678175657719139104636874731038771518520299266622696414842349131395304

noncomputable def ep19 := nat_lit 8978369550011421500876706511871067098718760264493934208903156435737864998391937547068187824077011975074541700434630537294838404525415248443919841847024664017658842168336182958576672102333385008949995305

noncomputable def ep20 := BSN.log_dyadic_bound ep15 ep16 5 4 ep17 1048576 390814 ep18 ep19 473518 ep14 ep6 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP ep15) (BSN.artanhQ ep16) 0 4 ep18 ep17 ep19 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep21 := ep13 (BSN.isNear_log_sfrac ep2 ep1 4138529546116343 2251799813685248 250000000195407 97703500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep2) (@Nat.cast Real Real.instNatCast ep1))) Bool.false 69433004117575847641088 37778931862957161709568 1000000000781628 390814000000000000000 4138529546116343 2251799813685248 250000000195407 97703500000000000000 (BSN.log_rat_reduce_isNear ep2 ep1 2 ep14 ep6 473518 1048576 24973259072661432 36028797018963968 390814 1000000000000000 rfl rfl rfl rfl (ep20 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable abbrev qz2 := (Real.log (@HMul.hMul Real Real Real qz269 (2 : Real) Real.pi))

theorem EMRow46.d4 : Enclosure.Real.IsNear qz2 Bool.false 120447 65536 1 262144 := @Enclosure.Real.IsNear.of_eq qz2 (Real.log qz270) Bool.false 120447 65536 1 262144 BSN.log_two_pi_eq (@Enclosure.Real.IsNear.recentre' (Real.log qz270) Bool.false 963576 524288 2 524288 120447 65536 1 262144 (ep21 rfl rfl rfl rfl rfl rfl rfl rfl) rfl)

noncomputable def ep22 := nat_lit 8589934592000000000000000

noncomputable def ep23 := @BSN.isNear_log_image_fff Real.pi 226375608064910080 72057594037927936 1 1000000000000000 ep0 ep22 ep2 ep22 1200336 1048576 1 390814 1200336 1048576 1 390814 600168 524288 2 524288 BSN.pi_near_15 rfl rfl rfl

noncomputable def ep24 := nat_lit 17179869184000000000000000

noncomputable def ep25 := nat_lit 18396140817044028275299783

noncomputable def ep26 := nat_lit 35576010001044028275299783

noncomputable def ep27 := nat_lit 145019262663961446558303139663424756232419223153299357158415217874016130572233056993847515999529612750616182853355499335896178729185698845314776375864537073527142908641610750276034469165612529925303649396973267518946591078603565291376312767403717761600170009932259137778521478520425507632472584532570900560707662248426541531715360699177249902784721815296292248142738824858695953661559845440650653128788875447728828657762006237171740033404723254477174341920697506370253193455781322964835857351124092897592956162654178130575

noncomputable def ep28 := nat_lit 15500762873619990602332184736899274490522931101512051618692838888825382235673431503644115344741331161500627469184702974962114537943617674254904297224139410345221262767191485292268260077615645253784097850065864022184521411511133693085443040736512010941548648374196772723338837137976260321103066698629790037694560548409922339907589559883712609967105556007429010014773911317423638534096849366294542840133852248768895750397896505791271178551667935288585787166713880920071720072716082683081155281219708172458141800988558163320

noncomputable def ep29 := nat_lit 12900190794487083783367107939442176642390171280542213571554777169279725287102813254708993369099729304728646904879886535518616983985412662170766446331701281703998252143668221340329975389245922410714088123244705567402747658401492589451585970559635763980329972215329212888079422466283203384882259392047898400615815810081169907384366653346471604103896809335921621947903075223769953790093549808584241881353287841076643853121427928248525828402335494512605306631304432120211393210317325496757155861061354331245840675149075

noncomputable def ep30 := BSN.log_dyadic_bound ep25 ep26 11 10 ep27 1048576 390814 ep28 ep29 1200336 ep5 ep24 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base10 (BSN.artanhP ep25) (BSN.artanhQ ep26) 0 10 ep28 ep27 ep29 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep31 := nat_lit 18396140817044045455168967

noncomputable def ep32 := nat_lit 35576010001044045455168967

noncomputable def ep33 := nat_lit 145019262663962847171784895425483977818796535899227200426399035286881207006285364467913811844950531107314785650583974625982406238691319033447632878979985852280879486690814033867010958364699188952871572448188560932645032521756218245629809291975913196623825614492380080480004685076434733043183791438169545293975334857826316990371107134320667652578346815517853870648072772035977941843998949310557583393428557296298890786965786350523173236912472938174255438182435383147950274229549088258679583524155427309880956162654178130575

noncomputable def ep34 := nat_lit 15500762873620157189619721156942591192100275120160672416764593300158228469749443299607348495591439275767946573253526107895503597951484257520435868240203420954375895980141891044871083424251900562230440202302413072793440172565998181227591194192658878334739610458454844032013325963992941389843551995646587189684848765634635122388286241104146031552341815777883628509454807838726994150833304950745987647656768534710890974432620160470644835720379148964170536679305861738540146791997074363921127776563807649880221800988558163320

noncomputable def ep35 := nat_lit 12900190794487324729109480814509220959173684627296055849229843377126536688487849343376525559792931631054411655715865486295286288812423905434305314401904993536755333953308594664509631000767632482919425633906965368325056855874260596615770736441041599390097968820060635361729170158825410327022636428624381203910573184452046894301676992229743752846881064485858738985580654099214803581683226335297196686880535448467637789069028262446657986458573827723305156755787640135484017403116612632808333639900906331245840675149075

noncomputable def ep36 := BSN.log_dyadic_bound ep31 ep32 11 10 ep33 1048576 390814 ep34 ep35 1200336 ep14 ep24 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base10 (BSN.artanhP ep31) (BSN.artanhQ ep32) 0 10 ep34 ep33 ep35 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep37 := @Enclosure.Real.IsNear.recentre' (Real.log Real.pi) Bool.false 600168 524288 2 524288 75021 65536 1 262144 (ep23 rfl rfl rfl rfl rfl (BSN.isNear_log_sfrac ep0 ep22 1200336 1048576 1 390814 Bool.false (BSN.logfrac_isNear ep5 ep24 1 ep0 ep22 1200336 1048576 390814 rfl rfl rfl (ep30 rfl))) (BSN.isNear_log_sfrac ep2 ep22 1200336 1048576 1 390814 Bool.false (BSN.logfrac_isNear ep14 ep24 1 ep2 ep22 1200336 1048576 390814 rfl rfl rfl (ep36 rfl))) rfl rfl rfl rfl rfl rfl rfl rfl) rfl

theorem EMRow46.d5 : Enclosure.Real.IsNear (Real.log Real.pi) Bool.false 75021 65536 1 262144 := ep37

noncomputable abbrev qz690 := (@HAdd.hAdd Complex Complex Complex (@instHAdd Complex Complex.instAdd) (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (2 : Complex)) (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul) Complex.I ↑(Enclosure.sfrac Bool.false 134395 1000)))

noncomputable abbrev qz537 := qz690

noncomputable abbrev qz273 := qz537

noncomputable abbrev qz3 := (BSN.headSumC qz273 9)

noncomputable abbrev qz691 := (@instHAdd Complex Complex.instAdd)

noncomputable abbrev qz538 := qz691

noncomputable abbrev qz274 := qz538

noncomputable abbrev qz4 := qz274

noncomputable abbrev qz5 := qz273

noncomputable abbrev qz539 := (@instHPow Complex Complex Complex.instPow)

noncomputable abbrev qz275 := qz539

noncomputable abbrev qz6 := qz275

noncomputable abbrev qz540 := (@Neg.neg Complex Complex.instNeg qz690)

noncomputable abbrev qz276 := qz540

noncomputable abbrev qz7 := qz276

noncomputable abbrev qz541 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 8) qz7)

noncomputable def ep38 := @Enclosure.Complex.IsNear.of_eq qz3 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 8) qz541) Bool.true 410248711963 549755813888 125896030869083 53713067162206208 Bool.false 749100856717 1099511627776 503336798204281 214852268648824832

noncomputable def ep39 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 8) qz541 Bool.true 108827461641 274877906944 225308090037777 107426134324412416 Bool.false 801497927989 1099511627776 450544265805193 214852268648824832 Bool.true

noncomputable abbrev qz542 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 7) qz7)

noncomputable def ep40 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 8) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 7) qz542) Bool.true 108827461641 274877906944 225308090037777 107426134324412416 Bool.false 801497927989 1099511627776 450544265805193 214852268648824832

noncomputable def ep41 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 7) qz542 Bool.true 136439182439 1099511627776 394138045227639 214852268648824832 Bool.false 64092684733 137438953472 197035558871959 107426134324412416 Bool.true

noncomputable abbrev qz543 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 6) qz7)

noncomputable def ep42 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 7) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 6) qz543) Bool.true 136439182439 1099511627776 394138045227639 214852268648824832 Bool.false 64092684733 137438953472 197035558871959 107426134324412416

noncomputable def ep43 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 6) qz543 Bool.false 16867242967 274877906944 83300228947677 53713067162206208 Bool.false 228156798731 274877906944 166522264807269 107426134324412416 Bool.true

noncomputable abbrev qz544 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 5) qz7)

noncomputable def ep44 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 6) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 5) qz544) Bool.false 16867242967 274877906944 83300228947677 53713067162206208 Bool.false 228156798731 274877906944 166522264807269 107426134324412416

noncomputable def ep45 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 5) qz544 Bool.false 505925535805 1099511627776 266366912590961 214852268648824832 Bool.false 283800863151 274877906944 133150242088359 107426134324412416 Bool.true

noncomputable abbrev qz545 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 4) qz7)

noncomputable def ep46 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 5) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 4) qz545) Bool.false 505925535805 1099511627776 266366912590961 214852268648824832 Bool.false 283800863151 274877906944 133150242088359 107426134324412416

noncomputable def ep47 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 4) qz545 Bool.false 822599078101 1099511627776 191730557739865 214852268648824832 Bool.false 685817666285 1099511627776 191614666147119 214852268648824832 Bool.true

noncomputable def ep48 := nat_lit 1248169396029559305928704

noncomputable abbrev qz546 := (@Nat.cast Complex Complex.instNatCast 3)

noncomputable abbrev qz277 := qz546

noncomputable abbrev qz8 := qz277

noncomputable def ep49 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 4) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 3) (@HPow.hPow Complex Complex Complex qz6 qz8 qz7)) Bool.false 822599078101 1099511627776 191730557739865 214852268648824832 Bool.false 685817666285 1099511627776 191614666147119 214852268648824832

noncomputable def ep50 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 3) (@HPow.hPow Complex Complex Complex qz6 qz8 qz7) Bool.false 1457386005351 1099511627776 105479259137735 214852268648824832 Bool.false 172552149055 274877906944 26391711066967 53713067162206208 Bool.true

noncomputable abbrev qz547 := (@Nat.cast Complex Complex.instNatCast 2)

noncomputable abbrev qz278 := qz547

noncomputable abbrev qz9 := qz278

noncomputable def ep51 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 3) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 2) (@HPow.hPow Complex Complex Complex qz6 qz9 qz7)) Bool.false 1457386005351 1099511627776 105479259137735 214852268648824832 Bool.false 172552149055 274877906944 26391711066967 53713067162206208

noncomputable def ep52 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 2) (@HPow.hPow Complex Complex Complex qz6 qz9 qz7) Bool.false 1 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable abbrev qz548 := (Enclosure.sfrac Bool.false 0 1)

noncomputable abbrev qz10 := qz548

noncomputable def ep53 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 2) (Complex.mk (Enclosure.sfrac Bool.false 1 1) qz10) Bool.false 1 1 0 1 Bool.false 0 1 0 1 (BSN.head_sum_c_two qz5)

noncomputable abbrev qz692 := (Enclosure.sfrac Bool.false 134395 1000)

noncomputable abbrev qz549 := qz692

noncomputable abbrev qz279 := qz549

noncomputable abbrev qz280 := (Enclosure.sfrac Bool.false 2 1)

noncomputable abbrev qz11 := (@HMul.hMul Real Real Real qz269 qz279 (Real.log qz280))

noncomputable abbrev qz12 := qz279

noncomputable abbrev qz281 := (@Eq.refl Real qz549)

noncomputable abbrev qz13 := qz281

noncomputable abbrev qz282 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 2)))

noncomputable def ep54 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz9 qz7) (Complex.mk (@HMul.hMul Real Real Real qz0 qz282 (Real.cos qz11)) (@HMul.hMul Real Real Real qz0 qz282 (@Neg.neg Real Real.instNeg (Real.sin qz11)))) Bool.false 357874377575 1099511627776 105479259137735 214852268648824832 Bool.false 172552149055 274877906944 26391711066967 53713067162206208 (BSN.cpow_neg_s_mk qz12 134395 1000 2 qz13 rfl)

noncomputable abbrev qz14 := (@Nat.cast Real Real.instNatCast 1)

noncomputable abbrev qz283 := (Real.sqrt (@Nat.cast Real Real.instNatCast 2))

noncomputable abbrev qz284 := (@Nat.cast Real Real.instNatCast 2)

noncomputable def ep55 := @Enclosure.Real.IsNear.inv_image qz283 1482911 1048576 1 1048576 370727 370728 524288 (@Enclosure.Real.IsNear.of_eq qz283 (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz284 qz14)) Bool.false 1482911 1048576 1 1048576 (BSN.sqrt_natCast_div_one 2) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz284 qz14)) Bool.false 1482911 1048576 1 1048576 1482911 1048576 1 1048576 (BSN.sqrt_enclosure 2 1 741455 741456 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep56 := BSN.log_dyadic_bound 1 3 6 5 613814355 524288 195407 24381081 945 363408 4 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 1) (BSN.artanhQ 3) 0 5 24381081 613814355 945 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep57 := nat_lit 1113436213412395998864496382736921616

noncomputable def ep58 := nat_lit 2552117751907038475975309555738261585920

noncomputable def ep59 := nat_lit 17864824263349269331827166890167831101440

noncomputable abbrev qz15 := (BSN.sinEvenQ 2147483648)

noncomputable abbrev qz16 := (BSN.sinOddQ 2147483648)

noncomputable def ep60 := BSN.sin_dyadic_bound_f 1027226786 2147483648 2 1 1048576 391196 ep57 ep58 ep57 ep57 ep59 ep57 482665 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1027226786) qz15 0 1 ep57 ep58 ep57 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1027226786) qz16 0 1 ep57 ep59 ep57 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz17 := (@Nat.cast Real Real.instNatCast 262144)

noncomputable abbrev qz18 := (Enclosure.Real.IsNear.const Bool.false 134395 1000)

noncomputable abbrev qz285 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 24420109) qz17)

noncomputable abbrev qz286 := (BSN.isNear_log_sfrac 2 1 363408 524288 1 195407 Bool.false (BSN.logfrac_isNear 4 2 1 2 1 363408 524288 195407 rfl rfl rfl (ep56 rfl)))

noncomputable abbrev qz287 := (@Nat.cast Real Real.instNatCast 37778931862957161709568)

noncomputable def ep61 := @Enclosure.Real.IsNear.cos_image qz11 qz285 Bool.false 24420109 262144 361 524288 Bool.false 482665 1048576 1 195407 (@Enclosure.Real.IsNear.recentre' qz11 Bool.false 610502727 6553600 26879 39081400 24420109 262144 361 524288 (@Enclosure.Real.IsNear.mulLit_ff qz12 (Real.log qz280) 134395 1000 0 1 363408 524288 1 195407 610502727 6553600 26879 39081400 qz18 qz286 rfl) rfl) (Enclosure.sfrac_false_div 24420109 262144) (BSN.cos_reduce3 qz285 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 18071164734401169850368) qz287) 226375608064910080 72057594037927936 Bool.false 482665 1048576 14 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q3 24420109 262144 226375608064910080 72057594037927936 14 18071164734401169850368 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 482665 1048576 18071164734401169850368 37778931862957161709568 1027226786 2147483648 391196 390814 (ep60 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep62 := nat_lit 510423550381407695195061911147652317184

noncomputable def ep63 := nat_lit 7656353255721115427925928667214784757760

noncomputable abbrev qz19 := (BSN.cosEvenQ 2147483648)

noncomputable abbrev qz20 := (BSN.cosOddQ 2147483648)

noncomputable def ep64 := BSN.cos_dyadic_bound_f 1027226786 2147483648 2 1 1048576 391196 ep57 ep62 ep57 ep57 ep63 ep57 930884 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1027226786) qz19 0 1 ep57 ep62 ep57 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1027226786) qz20 0 1 ep57 ep63 ep57 rfl rfl rfl rfl) rfl rfl

noncomputable def ep65 := @Enclosure.Real.IsNear.sin_image qz11 qz285 Bool.false 24420109 262144 361 524288 Bool.true 930884 1048576 1 195407 (@Enclosure.Real.IsNear.recentre' qz11 Bool.false 610502727 6553600 26879 39081400 24420109 262144 361 524288 (@Enclosure.Real.IsNear.mulLit_ff qz12 (Real.log qz280) 134395 1000 0 1 363408 524288 1 195407 610502727 6553600 26879 39081400 qz18 qz286 rfl) rfl) (Enclosure.sfrac_false_div 24420109 262144) (BSN.sin_reduce3 qz285 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 18071164734401169850368) qz287) 226375608064910080 72057594037927936 Bool.false 930884 1048576 14 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q3 24420109 262144 226375608064910080 72057594037927936 14 18071164734401169850368 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 930884 1048576 18071164734401169850368 37778931862957161709568 1027226786 2147483648 391196 390814 (ep64 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz288 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 2))) Bool.false 741455 1048576 1 1048576 741455 1048576 1 1048576 (ep55 rfl rfl) rfl)

noncomputable def ep66 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz282 (Real.cos qz11)) (@HMul.hMul Real Real Real qz0 qz282 (@Neg.neg Real Real.instNeg (Real.sin qz11))) Bool.false 357874377575 1099511627776 105479259137735 214852268648824832 Bool.false 172552149055 274877906944 26391711066967 53713067162206208 (@Enclosure.Real.IsNear.mulLit_ff qz282 (Real.cos qz11) 741455 1048576 1 1048576 482665 1048576 71066215 102449545216 357874377575 1099511627776 105479259137735 214852268648824832 qz288 (@Enclosure.Real.IsNear.recentre' (Real.cos qz11) Bool.false 482665 1048576 71066215 102449545216 482665 1048576 71066215 102449545216 (ep61 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz282 (@Neg.neg Real Real.instNeg (Real.sin qz11)) 741455 1048576 1 1048576 232721 262144 71066215 102449545216 172552149055 274877906944 26391711066967 53713067162206208 qz288 (@Enclosure.Real.IsNear.neg (Real.sin qz11) Bool.true 232721 262144 71066215 102449545216 (@Enclosure.Real.IsNear.recentre' (Real.sin qz11) Bool.true 930884 1048576 71066215 102449545216 232721 262144 71066215 102449545216 (ep65 rfl rfl) rfl)) rfl)

noncomputable abbrev qz550 := (Enclosure.Real.IsNear.const Bool.false 0 1)

noncomputable abbrev qz21 := qz550

noncomputable def ep67 := @ep52 357874377575 1099511627776 105479259137735 214852268648824832 Bool.false 172552149055 274877906944 26391711066967 53713067162206208 Bool.false 1457386005351 1457386005351 1099511627776 105479259137735 214852268648824832 Bool.false 172552149055 172552149055 274877906944 26391711066967 53713067162206208 (ep53 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 1) qz10 Bool.false 1 1 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 1) qz21)) (ep54 ep66) rfl rfl

noncomputable abbrev qz551 := (Real.log (Enclosure.sfrac Bool.false 3 1))

noncomputable abbrev qz22 := (@HMul.hMul Real Real Real qz269 qz279 qz551)

noncomputable abbrev qz289 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 3)))

noncomputable def ep68 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz8 qz7) (Complex.mk (@HMul.hMul Real Real Real qz0 qz289 (Real.cos qz22)) (@HMul.hMul Real Real Real qz0 qz289 (@Neg.neg Real Real.instNeg (Real.sin qz22)))) Bool.true 317393463625 549755813888 43125649301065 107426134324412416 Bool.true 4390929935 1099511627776 86047821879251 214852268648824832 (BSN.cpow_neg_s_mk qz12 134395 1000 3 qz13 rfl)

noncomputable abbrev qz290 := (Real.sqrt (@Nat.cast Real Real.instNatCast 3))

noncomputable abbrev qz291 := (@Nat.cast Real Real.instNatCast 3)

noncomputable def ep69 := @Enclosure.Real.IsNear.inv_image qz290 1816187 1048576 1 1048576 302697 302698 524288 (@Enclosure.Real.IsNear.of_eq qz290 (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz291 qz14)) Bool.false 1816187 1048576 1 1048576 (BSN.sqrt_natCast_div_one 3) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz291 qz14)) Bool.false 1816187 1048576 1 1048576 1816187 1048576 1 1048576 (BSN.sqrt_enclosure 3 1 908093 908094 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep70 := BSN.log_dyadic_bound 1 2 10 9 171633298636800 524288 195407 16925142283965 34459425 575989 3 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base9 (BSN.artanhP 1) (BSN.artanhQ 2) 0 9 16925142283965 171633298636800 34459425 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep71 := nat_lit 8197678126503949591954578563341088482167306235736975103644113647344964086499265

noncomputable def ep72 := nat_lit 164135286493895707012911871249815109382010203263545499525931125331216861264609280

noncomputable def ep73 := nat_lit 16183141768389360294410103268527231707405838222482536494480125684246859188161

noncomputable def ep74 := nat_lit 21443908101790094728928184641553806697197621165046153545695901253843268168812481

noncomputable def ep75 := nat_lit 3009146919054754628570050972913277005336853726498334157975403964405642456517836800

noncomputable def ep76 := BSN.sin_dyadic_bound_f 3358403353 2147483648 3 2 1048576 391196 ep71 ep72 ep73 ep74 ep75 ep73 1048550 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3358403353) qz15 0 2 ep71 ep72 ep73 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3358403353) qz16 0 2 ep74 ep75 ep73 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz23 := (@Nat.cast Real Real.instNatCast 1048576)

noncomputable abbrev qz24 := (@Nat.cast Real Real.instNatCast 151115727451828646838272)

noncomputable abbrev qz292 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 154820083) qz23)

noncomputable abbrev qz293 := (BSN.isNear_log_sfrac 3 1 575989 524288 1 195407 Bool.false (BSN.logfrac_isNear 3 1 2 3 1 575989 524288 195407 rfl rfl rfl (ep70 rfl)))

noncomputable def ep77 := @Enclosure.Real.IsNear.cos_image qz22 qz292 Bool.false 154820083 1048576 361 524288 Bool.true 1048550 1048576 1 195407 (@Enclosure.Real.IsNear.recentre' qz22 Bool.false 15482008331 104857600 26879 39081400 154820083 1048576 361 524288 (@Enclosure.Real.IsNear.mulLit_ff qz12 qz551 134395 1000 0 1 575989 524288 1 195407 15482008331 104857600 26879 39081400 qz18 qz293 rfl) rfl) (Enclosure.sfrac_false_div 154820083 1048576) (BSN.cos_reduce1 qz292 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 236326626453399258791936) qz24) 226375608064910080 72057594037927936 Bool.false 1048550 1048576 23 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q1 154820083 1048576 226375608064910080 72057594037927936 23 236326626453399258791936 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1048550 1048576 236326626453399258791936 151115727451828646838272 3358403353 2147483648 391196 390814 (ep76 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep78 := nat_lit 4561458133288145044550059247753283481962906059063867296022054304384645318805441

noncomputable def ep79 := nat_lit 18237254054877300779212430138868345486890022584838388836214569481246317918289920

noncomputable def ep80 := nat_lit 13652008116327656413061357536722795982473906500746636815077202661785442238040001

noncomputable def ep81 := nat_lit 820676432469478535064559356249075546910051016317727497629655626656084306323046400

noncomputable def ep82 := BSN.cos_dyadic_bound_f 3358403353 2147483648 3 2 1048576 391196 ep78 ep79 ep73 ep80 ep81 ep73 7253 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3358403353) qz19 0 2 ep78 ep79 ep73 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3358403353) qz20 0 2 ep80 ep81 ep73 rfl rfl rfl rfl) rfl rfl

noncomputable def ep83 := @Enclosure.Real.IsNear.sin_image qz22 qz292 Bool.false 154820083 1048576 361 524288 Bool.false 7253 1048576 1 195407 (@Enclosure.Real.IsNear.recentre' qz22 Bool.false 15482008331 104857600 26879 39081400 154820083 1048576 361 524288 (@Enclosure.Real.IsNear.mulLit_ff qz12 qz551 134395 1000 0 1 575989 524288 1 195407 15482008331 104857600 26879 39081400 qz18 qz293 rfl) rfl) (Enclosure.sfrac_false_div 154820083 1048576) (BSN.sin_reduce1 qz292 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 236326626453399258791936) qz24) 226375608064910080 72057594037927936 Bool.false 7253 1048576 23 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q1 154820083 1048576 226375608064910080 72057594037927936 23 236326626453399258791936 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 7253 1048576 236326626453399258791936 151115727451828646838272 3358403353 2147483648 391196 390814 (ep82 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz294 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 3))) Bool.false 605395 1048576 1 1048576 605395 1048576 1 1048576 (ep69 rfl rfl) rfl)

noncomputable def ep84 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz289 (Real.cos qz22)) (@HMul.hMul Real Real Real qz0 qz289 (@Neg.neg Real Real.instNeg (Real.sin qz22))) Bool.true 317393463625 549755813888 43125649301065 107426134324412416 Bool.true 4390929935 1099511627776 86047821879251 214852268648824832 (@Enclosure.Real.IsNear.mulLit_ft qz289 (Real.cos qz22) 605395 1048576 1 1048576 524275 524288 71066215 102449545216 317393463625 549755813888 43125649301065 107426134324412416 qz294 (@Enclosure.Real.IsNear.recentre' (Real.cos qz22) Bool.true 1048550 1048576 71066215 102449545216 524275 524288 71066215 102449545216 (ep77 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz289 (@Neg.neg Real Real.instNeg (Real.sin qz22)) 605395 1048576 1 1048576 7253 1048576 71066215 102449545216 4390929935 1099511627776 86047821879251 214852268648824832 qz294 (@Enclosure.Real.IsNear.neg (Real.sin qz22) Bool.false 7253 1048576 71066215 102449545216 (@Enclosure.Real.IsNear.recentre' (Real.sin qz22) Bool.false 7253 1048576 71066215 102449545216 7253 1048576 71066215 102449545216 (ep83 rfl rfl) rfl)) rfl)

noncomputable def ep85 := @ep50 317393463625 549755813888 43125649301065 107426134324412416 Bool.true 4390929935 1099511627776 86047821879251 214852268648824832 Bool.false 452228625684933732466688 822599078101 1099511627776 191730557739865 214852268648824832 Bool.false 188516124653639476183040 685817666285 1099511627776 191614666147119 214852268648824832 (ep51 (BSN.head_sum_c_succ qz5 2 3 rfl rfl) (ep67 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep68 ep84) rfl rfl

noncomputable abbrev qz552 := (Real.log (Enclosure.sfrac Bool.false 4 1))

noncomputable abbrev qz25 := (@HMul.hMul Real Real Real qz269 qz279 qz552)

noncomputable abbrev qz295 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 4)))

noncomputable def ep86 := @Enclosure.Complex.IsNear.of_eq qz545 (Complex.mk (@HMul.hMul Real Real Real qz0 qz295 (Real.cos qz25)) (@HMul.hMul Real Real Real qz0 qz295 (@Neg.neg Real Real.instNeg (Real.sin qz25)))) Bool.true 39584192787 137438953472 9329544356387 26856533581103104 Bool.false 449385786319 1099511627776 74685818029599 214852268648824832 (BSN.cpow_neg_s_mk qz12 134395 1000 4 qz13 rfl)

noncomputable abbrev qz296 := (Real.sqrt (@Nat.cast Real Real.instNatCast 4))

noncomputable abbrev qz297 := (@Nat.cast Real Real.instNatCast 4)

noncomputable def ep87 := @Enclosure.Real.IsNear.inv_image qz296 2097153 1048576 1 1048576 262143 262144 524288 (@Enclosure.Real.IsNear.of_eq qz296 (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz297 qz14)) Bool.false 2097153 1048576 1 1048576 (BSN.sqrt_natCast_div_one 4) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz297 qz14)) Bool.false 2097153 1048576 1 1048576 2097153 1048576 1 1048576 (BSN.sqrt_enclosure 4 1 1048576 1048577 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep88 := nat_lit 318077276165597140789031982421875

noncomputable def ep89 := nat_lit 49379992292270016474244603430625

noncomputable def ep90 := nat_lit 20095619060363156210525625

noncomputable def ep91 := BSN.log_dyadic_bound 3 5 14 13 ep88 524288 195407 ep89 ep90 726817 8 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base13 (BSN.artanhP 3) (BSN.artanhQ 5) 0 13 ep89 ep88 ep90 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep92 := nat_lit 637524029892213394966475671356574641602027380372692735961634281726375561854976

noncomputable def ep93 := nat_lit 318054973196790738414656602600748988513113608422013950970078378557450551296

noncomputable def ep94 := nat_lit 1911935979730246603422597700864522426829055913901234179982962688422011784462336

noncomputable def ep95 := BSN.cos_dyadic_bound_f 2055004484 2147483648 3 2 1048576 391196 ep92 ep79 ep93 ep94 ep81 ep93 604008 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2055004484) qz19 0 2 ep92 ep79 ep93 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2055004484) qz20 0 2 ep94 ep81 ep93 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz298 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 195361141) qz23)

noncomputable abbrev qz299 := (BSN.isNear_log_sfrac 4 1 726817 524288 1 195407 Bool.false (BSN.logfrac_isNear 8 2 1 4 1 726817 524288 195407 rfl rfl rfl (ep91 rfl)))

noncomputable def ep96 := @Enclosure.Real.IsNear.cos_image qz25 qz298 Bool.false 195361141 1048576 361 524288 Bool.true 604008 1048576 1 195407 (@Enclosure.Real.IsNear.recentre' qz25 Bool.false 19536114143 104857600 26879 39081400 195361141 1048576 361 524288 (@Enclosure.Real.IsNear.mulLit_ff qz12 qz552 134395 1000 0 1 726817 524288 1 195407 19536114143 104857600 26879 39081400 qz18 qz299 rfl) rfl) (Enclosure.sfrac_false_div 195361141 1048576) (BSN.cos_reduce2 qz298 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 144608084860801764032512) qz24) 226375608064910080 72057594037927936 Bool.false 604008 1048576 29 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q2 195361141 1048576 226375608064910080 72057594037927936 29 144608084860801764032512 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 604008 1048576 144608084860801764032512 151115727451828646838272 2055004484 2147483648 391196 390814 (ep95 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep97 := nat_lit 1147288809827426678348924483159753755692838793784109313570165644404630050897920

noncomputable def ep98 := nat_lit 3004289079591417924956416583299906242737937514068555417715529894161128546697216

noncomputable def ep99 := BSN.sin_dyadic_bound_f 2055004484 2147483648 3 2 1048576 391196 ep97 ep72 ep93 ep98 ep75 ep93 857137 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2055004484) qz15 0 2 ep97 ep72 ep93 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2055004484) qz16 0 2 ep98 ep75 ep93 rfl rfl rfl rfl) rfl rfl

noncomputable def ep100 := @Enclosure.Real.IsNear.sin_image qz25 qz298 Bool.false 195361141 1048576 361 524288 Bool.true 857137 1048576 1 195407 (@Enclosure.Real.IsNear.recentre' qz25 Bool.false 19536114143 104857600 26879 39081400 195361141 1048576 361 524288 (@Enclosure.Real.IsNear.mulLit_ff qz12 qz552 134395 1000 0 1 726817 524288 1 195407 19536114143 104857600 26879 39081400 qz18 qz299 rfl) rfl) (Enclosure.sfrac_false_div 195361141 1048576) (BSN.sin_reduce2 qz298 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 144608084860801764032512) qz24) 226375608064910080 72057594037927936 Bool.false 857137 1048576 29 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q2 195361141 1048576 226375608064910080 72057594037927936 29 144608084860801764032512 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 857137 1048576 144608084860801764032512 151115727451828646838272 2055004484 2147483648 391196 390814 (ep99 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz300 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 4))) Bool.false 524287 1048576 1 1048576 524287 1048576 1 1048576 (ep87 rfl rfl) rfl)

noncomputable def ep101 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz295 (Real.cos qz25)) (@HMul.hMul Real Real Real qz0 qz295 (@Neg.neg Real Real.instNeg (Real.sin qz25))) Bool.true 39584192787 137438953472 9329544356387 26856533581103104 Bool.false 449385786319 1099511627776 74685818029599 214852268648824832 (@Enclosure.Real.IsNear.mulLit_ft qz295 (Real.cos qz25) 524287 1048576 1 1048576 75501 131072 71066215 102449545216 39584192787 137438953472 9329544356387 26856533581103104 qz300 (@Enclosure.Real.IsNear.recentre' (Real.cos qz25) Bool.true 604008 1048576 71066215 102449545216 75501 131072 71066215 102449545216 (ep96 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz295 (@Neg.neg Real Real.instNeg (Real.sin qz25)) 524287 1048576 1 1048576 857137 1048576 71066215 102449545216 449385786319 1099511627776 74685818029599 214852268648824832 qz300 (@Enclosure.Real.IsNear.neg (Real.sin qz25) Bool.true 857137 1048576 71066215 102449545216 (@Enclosure.Real.IsNear.recentre' (Real.sin qz25) Bool.true 857137 1048576 71066215 102449545216 857137 1048576 71066215 102449545216 (ep100 rfl rfl) rfl)) rfl)

noncomputable def ep102 := @ep47 39584192787 137438953472 9329544356387 26856533581103104 Bool.false 449385786319 1099511627776 74685818029599 214852268648824832 Bool.false 69533876175800065064960 505925535805 1099511627776 266366912590961 214852268648824832 Bool.false ep48 283800863151 274877906944 133150242088359 107426134324412416 (ep49 (BSN.head_sum_c_succ qz5 3 4 rfl rfl) (ep85 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep86 ep101) rfl rfl

noncomputable abbrev qz553 := (Real.log (Enclosure.sfrac Bool.false 5 1))

noncomputable abbrev qz26 := (@HMul.hMul Real Real Real qz269 qz279 qz553)

noncomputable abbrev qz301 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 5)))

noncomputable def ep103 := @Enclosure.Complex.IsNear.of_eq qz544 (Complex.mk (@HMul.hMul Real Real Real qz0 qz301 (Real.cos qz26)) (@HMul.hMul Real Real Real qz0 qz301 (@Neg.neg Real Real.instNeg (Real.sin qz26)))) Bool.true 438456563937 1099511627776 66834003199747 214852268648824832 Bool.true 13911016105 68719476736 16686011359455 53713067162206208 (BSN.cpow_neg_s_mk qz12 134395 1000 5 qz13 rfl)

noncomputable abbrev qz302 := (Real.sqrt (@Nat.cast Real Real.instNatCast 5))

noncomputable abbrev qz303 := (@Nat.cast Real Real.instNatCast 5)

noncomputable def ep104 := @Enclosure.Real.IsNear.inv_image qz302 2344687 1048576 1 1048576 234468 234469 524288 (@Enclosure.Real.IsNear.of_eq qz302 (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz303 qz14)) Bool.false 2344687 1048576 1 1048576 (BSN.sqrt_natCast_div_one 5) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz303 qz14)) Bool.false 2344687 1048576 1 1048576 2344687 1048576 1 1048576 (BSN.sqrt_enclosure 5 1 1172343 1172344 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep105 := nat_lit 3696382175741467532940033205863946875

noncomputable def ep106 := nat_lit 765440954430599474856563326857688500

noncomputable def ep107 := nat_lit 108794268166472120024432640000

noncomputable def ep108 := BSN.log_dyadic_bound 2 3 18 17 ep105 524288 195407 ep106 ep107 843808 5 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_rec (BSN.artanhP 2) (BSN.artanhQ 3) 0 17 8 307084260767580 1483365253795425 132843110400 1663129201793174588340 2491889415829100854875 818968088287641600 ep106 ep105 ep107 rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.artanhP 2) (BSN.artanhQ 3) 0 8 307084260767580 1483365253795425 132843110400 rfl rfl rfl rfl) (@BSN.binarySplit_of_base9 (BSN.artanhP 2) (BSN.artanhQ 3) 8 17 1663129201793174588340 2491889415829100854875 818968088287641600 rfl rfl rfl rfl)) rfl rfl

noncomputable def ep109 := nat_lit 2011286305375635232208859496585203388742801802681441479556562298829931737579520

noncomputable def ep110 := nat_lit 977064512284582678409884866786962692847096750538898131366618594958859370496

noncomputable def ep111 := nat_lit 5266072695344869617162920772700734745204633231331474230435450543019887826108416

noncomputable def ep112 := BSN.sin_dyadic_bound_f 2364505916 2147483648 3 2 1048576 391196 ep109 ep72 ep110 ep111 ep75 ep110 935001 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2364505916) qz15 0 2 ep109 ep72 ep110 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2364505916) qz16 0 2 ep111 ep75 ep110 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz304 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 14175447) (@Nat.cast Real Real.instNatCast 65536))

noncomputable abbrev qz305 := (BSN.isNear_log_sfrac 5 1 843808 524288 1 195407 Bool.false (BSN.logfrac_isNear 5 1 2 5 1 843808 524288 195407 rfl rfl rfl (ep108 rfl rfl)))

noncomputable abbrev qz554 := (@Nat.cast Real Real.instNatCast 9444732965739290427392)

noncomputable def ep113 := @Enclosure.Real.IsNear.cos_image qz26 qz304 Bool.false 14175447 65536 361 524288 Bool.true 935001 1048576 1 195407 (@Enclosure.Real.IsNear.recentre' qz26 Bool.false 708772351 3276800 26879 39081400 14175447 65536 361 524288 (@Enclosure.Real.IsNear.mulLit_ff qz12 qz553 134395 1000 0 1 843808 524288 1 195407 708772351 3276800 26879 39081400 qz18 qz305 rfl) rfl) (Enclosure.sfrac_false_div 14175447 65536) (BSN.cos_reduce1 qz304 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 10399206994880153780224) qz554) 226375608064910080 72057594037927936 Bool.false 935001 1048576 34 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q1 14175447 65536 226375608064910080 72057594037927936 34 10399206994880153780224 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 935001 1048576 10399206994880153780224 9444732965739290427392 2364505916 2147483648 391196 390814 (ep112 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep114 := nat_lit 1117815531658590499084215224710351643831710822267706998923141996503277125042176

noncomputable def ep115 := nat_lit 3351492465951202331895825904397481006109438273302043200506692752319913656385536

noncomputable def ep116 := BSN.cos_dyadic_bound_f 2364505916 2147483648 3 2 1048576 391196 ep114 ep79 ep110 ep115 ep81 ep110 474640 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2364505916) qz19 0 2 ep114 ep79 ep110 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2364505916) qz20 0 2 ep115 ep81 ep110 rfl rfl rfl rfl) rfl rfl

noncomputable def ep117 := @Enclosure.Real.IsNear.sin_image qz26 qz304 Bool.false 14175447 65536 361 524288 Bool.false 474640 1048576 1 195407 (@Enclosure.Real.IsNear.recentre' qz26 Bool.false 708772351 3276800 26879 39081400 14175447 65536 361 524288 (@Enclosure.Real.IsNear.mulLit_ff qz12 qz553 134395 1000 0 1 843808 524288 1 195407 708772351 3276800 26879 39081400 qz18 qz305 rfl) rfl) (Enclosure.sfrac_false_div 14175447 65536) (BSN.sin_reduce1 qz304 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 10399206994880153780224) qz554) 226375608064910080 72057594037927936 Bool.false 474640 1048576 34 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q1 14175447 65536 226375608064910080 72057594037927936 34 10399206994880153780224 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 474640 1048576 10399206994880153780224 9444732965739290427392 2364505916 2147483648 391196 390814 (ep116 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz306 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 5))) Bool.false 468937 1048576 1 1048576 468937 1048576 1 1048576 (ep104 rfl rfl) rfl)

noncomputable def ep118 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz301 (Real.cos qz26)) (@HMul.hMul Real Real Real qz0 qz301 (@Neg.neg Real Real.instNeg (Real.sin qz26))) Bool.true 438456563937 1099511627776 66834003199747 214852268648824832 Bool.true 13911016105 68719476736 16686011359455 53713067162206208 (@Enclosure.Real.IsNear.mulLit_ft qz301 (Real.cos qz26) 468937 1048576 1 1048576 935001 1048576 71066215 102449545216 438456563937 1099511627776 66834003199747 214852268648824832 qz306 (@Enclosure.Real.IsNear.recentre' (Real.cos qz26) Bool.true 935001 1048576 71066215 102449545216 935001 1048576 71066215 102449545216 (ep113 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz301 (@Neg.neg Real Real.instNeg (Real.sin qz26)) 468937 1048576 1 1048576 29665 65536 71066215 102449545216 13911016105 68719476736 16686011359455 53713067162206208 qz306 (@Enclosure.Real.IsNear.neg (Real.sin qz26) Bool.false 29665 65536 71066215 102449545216 (@Enclosure.Real.IsNear.recentre' (Real.sin qz26) Bool.false 474640 1048576 71066215 102449545216 29665 65536 71066215 102449545216 (ep117 rfl rfl) rfl)) rfl)

noncomputable def ep119 := @ep45 438456563937 1099511627776 66834003199747 214852268648824832 Bool.true 13911016105 68719476736 16686011359455 53713067162206208 Bool.false 74182919082957831405568 16867242967 274877906944 83300228947677 53713067162206208 Bool.false 15678815822555188822016 228156798731 274877906944 166522264807269 107426134324412416 (ep46 (BSN.head_sum_c_succ qz5 4 5 rfl rfl) (ep102 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep103 ep118) rfl rfl

noncomputable abbrev qz555 := (Real.log (Enclosure.sfrac Bool.false 6 1))

noncomputable abbrev qz27 := (@HMul.hMul Real Real Real qz269 qz279 qz555)

noncomputable abbrev qz307 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 6)))

noncomputable def ep120 := @Enclosure.Complex.IsNear.of_eq qz543 (Complex.mk (@HMul.hMul Real Real Real qz0 qz307 (Real.cos qz27)) (@HMul.hMul Real Real Real qz0 qz307 (@Neg.neg Real Real.instNeg (Real.sin qz27)))) Bool.true 203908154307 1099511627776 60937129436931 214852268648824832 Bool.true 99971429265 274877906944 15256647032345 53713067162206208 (BSN.cpow_neg_s_mk qz12 134395 1000 6 qz13 rfl)

noncomputable abbrev qz308 := (Real.sqrt (@Nat.cast Real Real.instNatCast 6))

noncomputable abbrev qz309 := (@Nat.cast Real Real.instNatCast 6)

noncomputable abbrev qz556 := (@HDiv.hDiv Real Real Real qz1 qz309 qz14)

noncomputable def ep121 := @Enclosure.Real.IsNear.inv_image qz308 2568477 1048576 1 1048576 214039 214040 524288 (@Enclosure.Real.IsNear.of_eq qz308 (Real.sqrt qz556) Bool.false 2568477 1048576 1 1048576 (BSN.sqrt_natCast_div_one 6) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz556) Bool.false 2568477 1048576 1 1048576 2568477 1048576 1 1048576 (BSN.sqrt_enclosure 6 1 1284238 1284239 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep122 := BSN.log_dyadic_bound 2 10 4 3 105000000 524288 195407 1434560 960 212580 12 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 2) (BSN.artanhQ 10) 0 3 1434560 105000000 960 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep123 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz555 134395 1000 0 1 4034681531866359 2251799813685248 500000000195407 97703500000000000000 108448204895035863561 450359962737049600 13439500005252344753 19540700000000000000000 qz18 (BSN.isNear_log_sfrac 6 1 4034681531866359 2251799813685248 500000000195407 97703500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz556) Bool.false 33845361775666394038272 18889465931478580854784 1000000000390814 195407000000000000000 4034681531866359 2251799813685248 500000000195407 97703500000000000000 (BSN.log_rat_reduce_isNear 6 1 2 12 8 212580 524288 24973259072661432 36028797018963968 195407 1000000000000000 rfl rfl rfl rfl (ep122 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep124 := nat_lit 1051548095693173078531029969693251856

noncomputable def ep125 := BSN.sin_dyadic_bound_f 1012645146 2147483648 2 1 1048576 391196 ep124 ep58 ep124 ep124 ep59 ep124 476333 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1012645146) qz15 0 1 ep124 ep58 ep124 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1012645146) qz16 0 1 ep124 ep59 ep124 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz310 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 252500653) qz23)

noncomputable def ep126 := @Enclosure.Real.IsNear.cos_image qz27 qz310 Bool.false 252500653 1048576 361 524288 Bool.true 476333 1048576 1 195407 (@Enclosure.Real.IsNear.recentre' qz27 Bool.false 108448204895035863561 450359962737049600 13439500005252344753 19540700000000000000000 252500653 1048576 361 524288 (ep123 rfl) rfl) (Enclosure.sfrac_false_div 252500653 1048576) (BSN.cos_reduce1 qz310 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 71258567223934950834176) qz24) 226375608064910080 72057594037927936 Bool.false 476333 1048576 38 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q1 252500653 1048576 226375608064910080 72057594037927936 38 71258567223934950834176 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 476333 1048576 71258567223934950834176 151115727451828646838272 1012645146 2147483648 391196 390814 (ep125 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep127 := BSN.cos_dyadic_bound_f 1012645146 2147483648 2 1 1048576 391196 ep124 ep62 ep124 ep124 ep63 ep124 934140 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1012645146) qz19 0 1 ep124 ep62 ep124 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1012645146) qz20 0 1 ep124 ep63 ep124 rfl rfl rfl rfl) rfl rfl

noncomputable def ep128 := @Enclosure.Real.IsNear.sin_image qz27 qz310 Bool.false 252500653 1048576 361 524288 Bool.false 934140 1048576 1 195407 (@Enclosure.Real.IsNear.recentre' qz27 Bool.false 108448204895035863561 450359962737049600 13439500005252344753 19540700000000000000000 252500653 1048576 361 524288 (ep123 rfl) rfl) (Enclosure.sfrac_false_div 252500653 1048576) (BSN.sin_reduce1 qz310 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 71258567223934950834176) qz24) 226375608064910080 72057594037927936 Bool.false 934140 1048576 38 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q1 252500653 1048576 226375608064910080 72057594037927936 38 71258567223934950834176 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 934140 1048576 71258567223934950834176 151115727451828646838272 1012645146 2147483648 391196 390814 (ep127 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz311 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 6))) Bool.false 428079 1048576 1 1048576 428079 1048576 1 1048576 (ep121 rfl rfl) rfl)

noncomputable def ep129 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz307 (Real.cos qz27)) (@HMul.hMul Real Real Real qz0 qz307 (@Neg.neg Real Real.instNeg (Real.sin qz27))) Bool.true 203908154307 1099511627776 60937129436931 214852268648824832 Bool.true 99971429265 274877906944 15256647032345 53713067162206208 (@Enclosure.Real.IsNear.mulLit_ft qz307 (Real.cos qz27) 428079 1048576 1 1048576 476333 1048576 71066215 102449545216 203908154307 1099511627776 60937129436931 214852268648824832 qz311 (@Enclosure.Real.IsNear.recentre' (Real.cos qz27) Bool.true 476333 1048576 71066215 102449545216 476333 1048576 71066215 102449545216 (ep126 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz307 (@Neg.neg Real Real.instNeg (Real.sin qz27)) 428079 1048576 1 1048576 233535 262144 71066215 102449545216 99971429265 274877906944 15256647032345 53713067162206208 qz311 (@Enclosure.Real.IsNear.neg (Real.sin qz27) Bool.false 233535 262144 71066215 102449545216 (@Enclosure.Real.IsNear.recentre' (Real.sin qz27) Bool.false 934140 1048576 71066215 102449545216 233535 262144 71066215 102449545216 (ep128 rfl rfl) rfl)) rfl)

noncomputable def ep130 := @ep43 203908154307 1099511627776 60937129436931 214852268648824832 Bool.true 99971429265 274877906944 15256647032345 53713067162206208 Bool.true 37504116893982880956416 136439182439 1099511627776 394138045227639 214852268648824832 Bool.false 35235326059657406971904 64092684733 137438953472 197035558871959 107426134324412416 (ep44 (BSN.head_sum_c_succ qz5 5 6 rfl rfl) (ep119 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep120 ep129) rfl rfl

noncomputable abbrev qz557 := (Real.log (Enclosure.sfrac Bool.false 7 1))

noncomputable abbrev qz28 := (@HMul.hMul Real Real Real qz269 qz279 qz557)

noncomputable abbrev qz312 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 7)))

noncomputable def ep131 := @Enclosure.Complex.IsNear.of_eq qz542 (Complex.mk (@HMul.hMul Real Real Real qz0 qz312 (Real.cos qz28)) (@HMul.hMul Real Real Real qz0 qz312 (@Neg.neg Real Real.instNeg (Real.sin qz28)))) Bool.true 298870664125 1099511627776 56478134847915 214852268648824832 Bool.false 288756450125 1099511627776 56473148061275 214852268648824832 (BSN.cpow_neg_s_mk qz12 134395 1000 7 qz13 rfl)

noncomputable abbrev qz313 := (Real.sqrt (@Nat.cast Real Real.instNatCast 7))

noncomputable abbrev qz314 := (@Nat.cast Real Real.instNatCast 7)

noncomputable abbrev qz558 := (@HDiv.hDiv Real Real Real qz1 qz314 qz14)

noncomputable def ep132 := @Enclosure.Real.IsNear.inv_image qz313 2774271 1048576 1 1048576 198162 198163 524288 (@Enclosure.Real.IsNear.of_eq qz313 (Real.sqrt qz558) Bool.false 2774271 1048576 1 1048576 (BSN.sqrt_natCast_div_one 7) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz558) Bool.false 2774271 1048576 1 1048576 2774271 1048576 1 1048576 (BSN.sqrt_enclosure 7 1 1387135 1387136 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep133 := BSN.log_dyadic_bound 3 11 5 4 202569142545 524288 195407 5259111624 688905 293399 14 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 3) (BSN.artanhQ 11) 0 4 5259111624 202569142545 688905 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep134 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz557 134395 1000 0 1 4381796493761783 2251799813685248 500000000195407 97703500000000000000 117778307955822965257 450359962737049600 13439500005252344753 19540700000000000000000 qz18 (BSN.isNear_log_sfrac 7 1 4381796493761783 2251799813685248 500000000195407 97703500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz558) Bool.false 36757173121942042968064 18889465931478580854784 1000000000390814 195407000000000000000 4381796493761783 2251799813685248 500000000195407 97703500000000000000 (BSN.log_rat_reduce_isNear 7 1 2 14 8 293399 524288 24973259072661432 36028797018963968 195407 1000000000000000 rfl rfl rfl rfl (ep133 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep135 := nat_lit 264671992614634370285480994800790465783207192631583351066577359261420137513216

noncomputable def ep136 := nat_lit 54850231159091122433653543031096498951367108393155282278783078892450119936

noncomputable def ep137 := nat_lit 793906277381584928611575677316309204351718843677963742635174511626475512299776

noncomputable def ep138 := BSN.cos_dyadic_bound_f 1649670878 2147483648 3 2 1048576 391196 ep135 ep79 ep136 ep137 ep81 ep136 754105 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1649670878) qz19 0 2 ep135 ep79 ep136 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1649670878) qz20 0 2 ep137 ep81 ep136 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz559 := (@Nat.cast Real Real.instNatCast 131072)

noncomputable abbrev qz315 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 34277999) qz559)

noncomputable abbrev qz316 := (@Nat.cast Real Real.instNatCast 18889465931478580854784)

noncomputable def ep139 := @Enclosure.Real.IsNear.cos_image qz28 qz315 Bool.false 34277999 131072 361 524288 Bool.true 754105 1048576 1 195407 (@Enclosure.Real.IsNear.recentre' qz28 Bool.false 117778307955822965257 450359962737049600 13439500005252344753 19540700000000000000000 34277999 131072 361 524288 (ep134 rfl) rfl) (Enclosure.sfrac_false_div 34277999 131072) (BSN.cos_reduce2 qz315 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 14510658501873099603968) qz316) 226375608064910080 72057594037927936 Bool.false 754105 1048576 41 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q2 34277999 131072 226375608064910080 72057594037927936 41 14510658501873099603968 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 754105 1048576 14510658501873099603968 18889465931478580854784 1649670878 2147483648 391196 390814 (ep138 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep140 := nat_lit 7406094190536002252313121379341501456

noncomputable def ep141 := BSN.sin_dyadic_bound_f 1649670878 2147483648 2 1 1048576 391196 ep140 ep58 ep140 ep140 ep59 ep140 728585 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1649670878) qz15 0 1 ep140 ep58 ep140 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1649670878) qz16 0 1 ep140 ep59 ep140 rfl rfl rfl rfl) rfl rfl

noncomputable def ep142 := @Enclosure.Real.IsNear.sin_image qz28 qz315 Bool.false 34277999 131072 361 524288 Bool.true 728585 1048576 1 195407 (@Enclosure.Real.IsNear.recentre' qz28 Bool.false 117778307955822965257 450359962737049600 13439500005252344753 19540700000000000000000 34277999 131072 361 524288 (ep134 rfl) rfl) (Enclosure.sfrac_false_div 34277999 131072) (BSN.sin_reduce2 qz315 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 14510658501873099603968) qz316) 226375608064910080 72057594037927936 Bool.false 728585 1048576 41 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q2 34277999 131072 226375608064910080 72057594037927936 41 14510658501873099603968 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 728585 1048576 14510658501873099603968 18889465931478580854784 1649670878 2147483648 391196 390814 (ep141 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz317 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 7))) Bool.false 396325 1048576 1 1048576 396325 1048576 1 1048576 (ep132 rfl rfl) rfl)

noncomputable def ep143 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz312 (Real.cos qz28)) (@HMul.hMul Real Real Real qz0 qz312 (@Neg.neg Real Real.instNeg (Real.sin qz28))) Bool.true 298870664125 1099511627776 56478134847915 214852268648824832 Bool.false 288756450125 1099511627776 56473148061275 214852268648824832 (@Enclosure.Real.IsNear.mulLit_ft qz312 (Real.cos qz28) 396325 1048576 1 1048576 754105 1048576 71066215 102449545216 298870664125 1099511627776 56478134847915 214852268648824832 qz317 (@Enclosure.Real.IsNear.recentre' (Real.cos qz28) Bool.true 754105 1048576 71066215 102449545216 754105 1048576 71066215 102449545216 (ep139 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz312 (@Neg.neg Real Real.instNeg (Real.sin qz28)) 396325 1048576 1 1048576 728585 1048576 71066215 102449545216 288756450125 1099511627776 56473148061275 214852268648824832 qz317 (@Enclosure.Real.IsNear.neg (Real.sin qz28) Bool.true 728585 1048576 71066215 102449545216 (@Enclosure.Real.IsNear.recentre' (Real.sin qz28) Bool.true 728585 1048576 71066215 102449545216 728585 1048576 71066215 102449545216 (ep142 rfl rfl) rfl)) rfl)

noncomputable def ep144 := @ep41 298870664125 1099511627776 56478134847915 214852268648824832 Bool.false 288756450125 1099511627776 56473148061275 214852268648824832 Bool.true 478628237982504440561664 108827461641 274877906944 225308090037777 107426134324412416 Bool.false 110157036432784577527808 801497927989 1099511627776 450544265805193 214852268648824832 (ep42 (BSN.head_sum_c_succ qz5 6 7 rfl rfl) (ep130 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep131 ep143) rfl rfl

noncomputable abbrev qz560 := (Real.log (Enclosure.sfrac Bool.false 8 1))

noncomputable abbrev qz29 := (@HMul.hMul Real Real Real qz269 qz279 qz560)

noncomputable abbrev qz318 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 8)))

noncomputable def ep145 := @Enclosure.Complex.IsNear.of_eq qz541 (Complex.mk (@HMul.hMul Real Real Real qz0 qz318 (Real.cos qz29)) (@HMul.hMul Real Real Real qz0 qz318 (@Neg.neg Real Real.instNeg (Real.sin qz29)))) Bool.true 192593788681 549755813888 26483971700389 107426134324412416 Bool.true 6549633909 137438953472 3299533274943 13428266790551552 (BSN.cpow_neg_s_mk qz12 134395 1000 8 qz13 rfl)

noncomputable abbrev qz319 := (Real.sqrt (@Nat.cast Real Real.instNatCast 8))

noncomputable abbrev qz320 := (@Nat.cast Real Real.instNatCast 8)

noncomputable abbrev qz561 := (@HDiv.hDiv Real Real Real qz1 qz320 qz14)

noncomputable def ep146 := @Enclosure.Real.IsNear.inv_image qz319 2965821 1048576 1 1048576 185363 185364 524288 (@Enclosure.Real.IsNear.of_eq qz319 (Real.sqrt qz561) Bool.false 2965821 1048576 1 1048576 (BSN.sqrt_natCast_div_one 8) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz561) Bool.false 2965821 1048576 1 1048576 2965821 1048576 1 1048576 (BSN.sqrt_enclosure 8 1 1482910 1482911 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep147 := BSN.log_dyadic_bound 0 16 1 0 1 524288 195407 0 1 0 16 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 0) (BSN.artanhQ 16) 0 0 rfl) rfl rfl rfl

noncomputable def ep148 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz560 134395 1000 0 1 9364972152248037 4503599627370496 1000000000586221 195407000000000000000 251721086480274986523 900719925474099200 26879000015757034259 39081400000000000000000 qz18 (BSN.isNear_log_sfrac 8 1 9364972152248037 4503599627370496 1000000000586221 195407000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz561) Bool.false 39279540158062550581248 18889465931478580854784 1000000000586221 195407000000000000000 9364972152248037 4503599627370496 1000000000586221 195407000000000000000 (BSN.log_rat_reduce_isNear 8 1 3 16 16 0 524288 24973259072661432 36028797018963968 195407 1000000000000000 rfl rfl rfl rfl (ep147 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep149 := nat_lit 5817794137914917612020055800722139535238775362638754379617560600459116900000000

noncomputable def ep150 := nat_lit 8160091996116706734682390044346446758654278830554537243581443789062500000000

noncomputable def ep151 := nat_lit 15223868307497738125339231798962375964206590450709173172032574473163014500000000

noncomputable def ep152 := BSN.sin_dyadic_bound_f 3082917350 2147483648 3 2 1048576 391196 ep149 ep72 ep150 ep151 ep75 ep150 1039006 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3082917350) qz15 0 2 ep149 ep72 ep150 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3082917350) qz16 0 2 ep151 ep75 ep150 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz321 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 36630239) qz559)

noncomputable def ep153 := @Enclosure.Real.IsNear.cos_image qz29 qz321 Bool.false 36630239 131072 723 1048576 Bool.true 1039006 1048576 1 195407 (@Enclosure.Real.IsNear.recentre' qz29 Bool.false 251721086480274986523 900719925474099200 26879000015757034259 39081400000000000000000 36630239 131072 723 1048576 (ep148 rfl) rfl) (Enclosure.sfrac_false_div 36630239 131072) (BSN.cos_reduce1 qz321 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 27117627798301481893888) qz316) 226375608064910080 72057594037927936 Bool.false 1039006 1048576 44 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q1 36630239 131072 226375608064910080 72057594037927936 44 27117627798301481893888 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1039006 1048576 27117627798301481893888 18889465931478580854784 3082917350 2147483648 391196 390814 (ep152 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep154 := nat_lit 3235734561951006098559889840420898162580943769835110005229125419716870500000000

noncomputable def ep155 := nat_lit 9690883501860784882210304741174001594225522751844220941200213371572486500000000

noncomputable def ep156 := BSN.cos_dyadic_bound_f 3082917350 2147483648 3 2 1048576 391196 ep154 ep79 ep150 ep155 ep81 ep150 141336 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3082917350) qz19 0 2 ep154 ep79 ep150 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3082917350) qz20 0 2 ep155 ep81 ep150 rfl rfl rfl rfl) rfl rfl

noncomputable def ep157 := @Enclosure.Real.IsNear.sin_image qz29 qz321 Bool.false 36630239 131072 723 1048576 Bool.false 141336 1048576 1 195407 (@Enclosure.Real.IsNear.recentre' qz29 Bool.false 251721086480274986523 900719925474099200 26879000015757034259 39081400000000000000000 36630239 131072 723 1048576 (ep148 rfl) rfl) (Enclosure.sfrac_false_div 36630239 131072) (BSN.sin_reduce1 qz321 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 27117627798301481893888) qz316) 226375608064910080 72057594037927936 Bool.false 141336 1048576 44 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q1 36630239 131072 226375608064910080 72057594037927936 44 27117627798301481893888 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 141336 1048576 27117627798301481893888 18889465931478580854784 3082917350 2147483648 391196 390814 (ep156 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz322 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 8))) Bool.false 370727 1048576 1 1048576 370727 1048576 1 1048576 (ep146 rfl rfl) rfl)

noncomputable def ep158 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz318 (Real.cos qz29)) (@HMul.hMul Real Real Real qz0 qz318 (@Neg.neg Real Real.instNeg (Real.sin qz29))) Bool.true 192593788681 549755813888 26483971700389 107426134324412416 Bool.true 6549633909 137438953472 3299533274943 13428266790551552 (@Enclosure.Real.IsNear.mulLit_ft qz318 (Real.cos qz29) 370727 1048576 1 1048576 519503 524288 142327837 204899090432 192593788681 549755813888 26483971700389 107426134324412416 qz322 (@Enclosure.Real.IsNear.recentre' (Real.cos qz29) Bool.true 1039006 1048576 142327837 204899090432 519503 524288 142327837 204899090432 (ep153 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz318 (@Neg.neg Real Real.instNeg (Real.sin qz29)) 370727 1048576 1 1048576 17667 131072 142327837 204899090432 6549633909 137438953472 3299533274943 13428266790551552 qz322 (@Enclosure.Real.IsNear.neg (Real.sin qz29) Bool.false 17667 131072 142327837 204899090432 (@Enclosure.Real.IsNear.recentre' (Real.sin qz29) Bool.false 141336 1048576 142327837 204899090432 17667 131072 142327837 204899090432 (ep157 rfl rfl) rfl)) rfl)

noncomputable def ep159 := @ep39 192593788681 549755813888 26483971700389 107426134324412416 Bool.true 6549633909 137438953472 3299533274943 13428266790551552 Bool.true 112768307270861373571072 410248711963 549755813888 125896030869083 53713067162206208 Bool.false 102955637792163101671424 749100856717 1099511627776 503336798204281 214852268648824832 (ep40 (BSN.head_sum_c_succ qz5 7 8 rfl rfl) (ep144 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep145 ep158) rfl rfl

theorem EMRow46.d6 : Enclosure.Complex.IsNear qz3 Bool.true 410248711963 549755813888 125896030869083 53713067162206208 Bool.false 749100856717 1099511627776 503336798204281 214852268648824832 := ep38 (BSN.head_sum_c_succ qz5 8 9 rfl rfl) (ep159 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable abbrev qz30 := (BSN.headSumC qz273 17)

noncomputable abbrev qz562 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 16) qz7)

noncomputable def ep160 := @Enclosure.Complex.IsNear.of_eq qz30 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 16) qz562) Bool.true 34345821403 137438953472 423140394403129 107426134324412416 Bool.true 41011627499 274877906944 423078803679985 107426134324412416

noncomputable def ep161 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 16) qz562 Bool.true 182236121513 1099511627776 808952650899699 214852268648824832 Bool.false 94787983201 1099511627776 808705502861797 214852268648824832 Bool.true

noncomputable abbrev qz563 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 15) qz7)

noncomputable def ep162 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 16) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 15) qz563) Bool.true 182236121513 1099511627776 808952650899699 214852268648824832 Bool.false 94787983201 1099511627776 808705502861797 214852268648824832

noncomputable def ep163 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 15) qz563 Bool.true 434492550479 1099511627776 770289366754157 214852268648824832 Bool.true 2215528451 68719476736 385065143250839 107426134324412416 Bool.false

noncomputable abbrev qz564 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 14) qz7)

noncomputable def ep164 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 15) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 14) qz564) Bool.true 434492550479 1099511627776 770289366754157 214852268648824832 Bool.true 2215528451 68719476736 385065143250839 107426134324412416

noncomputable def ep165 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 14) qz564 Bool.true 155933250423 1099511627776 730263373046493 214852268648824832 Bool.false 58124962727 1099511627776 730233279196051 214852268648824832 Bool.true

noncomputable abbrev qz565 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 13) qz7)

noncomputable def ep166 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 14) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 13) qz565) Bool.true 155933250423 1099511627776 730263373046493 214852268648824832 Bool.false 58124962727 1099511627776 730233279196051 214852268648824832

noncomputable def ep167 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 13) qz565 Bool.true 177555617097 549755813888 344397010732117 107426134324412416 Bool.true 86395849163 549755813888 344371301033127 107426134324412416 Bool.false

noncomputable abbrev qz566 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 12) qz7)

noncomputable def ep168 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 13) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 12) qz566) Bool.true 177555617097 549755813888 344397010732117 107426134324412416 Bool.true 86395849163 549755813888 344371301033127 107426134324412416

noncomputable def ep169 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 12) qz566 Bool.true 269858224095 549755813888 322825823345909 107426134324412416 Bool.false 21350545835 274877906944 161388180474517 53713067162206208 Bool.false

noncomputable abbrev qz567 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 11) qz7)

noncomputable def ep170 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 12) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 11) qz567) Bool.true 269858224095 549755813888 322825823345909 107426134324412416 Bool.false 21350545835 274877906944 161388180474517 53713067162206208

noncomputable def ep171 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 11) qz567 Bool.true 457130865121 1099511627776 600664298257559 214852268648824832 Bool.false 203232653833 549755813888 300208988884151 107426134324412416 Bool.true

noncomputable abbrev qz568 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 10) qz7)

noncomputable def ep172 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 11) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 10) qz568) Bool.true 457130865121 1099511627776 600664298257559 214852268648824832 Bool.false 203232653833 549755813888 300208988884151 107426134324412416

noncomputable def ep173 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 10) qz568 Bool.true 227014425013 549755813888 138366995688561 53713067162206208 Bool.false 11783557003 17179869184 276509299707067 107426134324412416 Bool.true

noncomputable abbrev qz569 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 9) qz7)

noncomputable def ep174 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 10) (@HAdd.hAdd Complex Complex Complex qz4 qz3 qz569) Bool.true 227014425013 549755813888 138366995688561 53713067162206208 Bool.false 11783557003 17179869184 276509299707067 107426134324412416

noncomputable def ep175 := @Enclosure.Complex.IsNear.addLitP qz3 qz569 Bool.true 410248711963 549755813888 125896030869083 53713067162206208 Bool.false 749100856717 1099511627776 503336798204281 214852268648824832 Bool.false

noncomputable abbrev qz570 := (Real.log (Enclosure.sfrac Bool.false 9 1))

noncomputable abbrev qz31 := (@HMul.hMul Real Real Real qz269 qz279 qz570)

noncomputable abbrev qz323 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 9)))

noncomputable def ep176 := @Enclosure.Complex.IsNear.of_eq qz569 (Complex.mk (@HMul.hMul Real Real Real qz0 qz323 (Real.cos qz31)) (@HMul.hMul Real Real Real qz0 qz323 (@Neg.neg Real Real.instNeg (Real.sin qz31)))) Bool.false 91617143475 274877906944 6235482409739 26856533581103104 Bool.false 5046791475 1099511627776 49681801209853 214852268648824832 (BSN.cpow_neg_s_mk qz12 134395 1000 9 qz13 rfl)

noncomputable abbrev qz324 := (Real.sqrt (@Nat.cast Real Real.instNatCast 9))

noncomputable abbrev qz325 := (@Nat.cast Real Real.instNatCast 9)

noncomputable abbrev qz571 := (@HDiv.hDiv Real Real Real qz1 qz325 qz14)

noncomputable def ep177 := @Enclosure.Real.IsNear.inv_image qz324 3145729 1048576 1 1048576 174762 174763 524288 (@Enclosure.Real.IsNear.of_eq qz324 (Real.sqrt qz571) Bool.false 3145729 1048576 1 1048576 (BSN.sqrt_natCast_div_one 9) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz571) Bool.false 3145729 1048576 1 1048576 3145729 1048576 1 1048576 (BSN.sqrt_enclosure 9 1 1572864 1572865 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep178 := BSN.log_dyadic_bound 1 17 3 2 1252815 524288 195407 1448 3 61752 18 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 1) (BSN.artanhQ 17) 0 2 1448 1252815 3 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep179 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz570 134395 1000 0 1 9895417793173221 4503599627370496 1000000000586221 195407000000000000000 265978934862703007259 900719925474099200 26879000015757034259 39081400000000000000000 qz18 (BSN.isNear_log_sfrac 9 1 9895417793173221 4503599627370496 1000000000586221 195407000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz571) Bool.false 41504390431577613533184 18889465931478580854784 1000000000586221 195407000000000000000 9895417793173221 4503599627370496 1000000000586221 195407000000000000000 (BSN.log_rat_reduce_isNear 9 1 3 18 16 61752 524288 24973259072661432 36028797018963968 195407 1000000000000000 rfl rfl rfl rfl (ep178 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep180 := nat_lit 8054631524502739851166416669453561055986400029398237933272162421153113163790465

noncomputable def ep181 := nat_lit 15624363445776921037924158860490166150483071219428174516475055723612478994561

noncomputable def ep182 := nat_lit 21070166928118775071374452162794723449054075104544882304590894346134209510602881

noncomputable def ep183 := BSN.sin_dyadic_bound_f 3343684497 2147483648 3 2 1048576 391196 ep180 ep72 ep181 ep182 ep75 ep181 1048476 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3343684497) qz15 0 2 ep180 ep72 ep181 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3343684497) qz16 0 2 ep182 ep75 ep181 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz326 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 309640233) qz23)

noncomputable def ep184 := @Enclosure.Real.IsNear.cos_image qz31 qz326 Bool.false 309640233 1048576 361 524288 Bool.false 1048476 1048576 1 195407 (@Enclosure.Real.IsNear.recentre' qz31 Bool.false 265978934862703007259 900719925474099200 26879000015757034259 39081400000000000000000 309640233 1048576 361 524288 (ep179 rfl) rfl) (Enclosure.sfrac_false_div 309640233 1048576) (BSN.cos_reduce3 qz326 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 235290879022128447881216) qz24) 226375608064910080 72057594037927936 Bool.false 1048476 1048576 46 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q3 309640233 1048576 226375608064910080 72057594037927936 46 235290879022128447881216 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1048476 1048576 235290879022128447881216 151115727451828646838272 3343684497 2147483648 391196 390814 (ep183 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep185 := nat_lit 4481739452921867437775975553634418438281548047985433596047412480962223970547841

noncomputable def ep186 := nat_lit 13413969631874048471252078343182274982543678001517444439109287331439446953654401

noncomputable def ep187 := BSN.cos_dyadic_bound_f 3343684497 2147483648 3 2 1048576 391196 ep185 ep79 ep181 ep186 ep81 ep181 14439 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3343684497) qz19 0 2 ep185 ep79 ep181 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3343684497) qz20 0 2 ep186 ep81 ep181 rfl rfl rfl rfl) rfl rfl

noncomputable def ep188 := @Enclosure.Real.IsNear.sin_image qz31 qz326 Bool.false 309640233 1048576 361 524288 Bool.true 14439 1048576 1 195407 (@Enclosure.Real.IsNear.recentre' qz31 Bool.false 265978934862703007259 900719925474099200 26879000015757034259 39081400000000000000000 309640233 1048576 361 524288 (ep179 rfl) rfl) (Enclosure.sfrac_false_div 309640233 1048576) (BSN.sin_reduce3 qz326 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 235290879022128447881216) qz24) 226375608064910080 72057594037927936 Bool.false 14439 1048576 46 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q3 309640233 1048576 226375608064910080 72057594037927936 46 235290879022128447881216 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 14439 1048576 235290879022128447881216 151115727451828646838272 3343684497 2147483648 391196 390814 (ep187 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz327 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 9))) Bool.false 349525 1048576 1 1048576 349525 1048576 1 1048576 (ep177 rfl rfl) rfl)

noncomputable def ep189 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz323 (Real.cos qz31)) (@HMul.hMul Real Real Real qz0 qz323 (@Neg.neg Real Real.instNeg (Real.sin qz31))) Bool.false 91617143475 274877906944 6235482409739 26856533581103104 Bool.false 5046791475 1099511627776 49681801209853 214852268648824832 (@Enclosure.Real.IsNear.mulLit_ff qz323 (Real.cos qz31) 349525 1048576 1 1048576 262119 262144 71066215 102449545216 91617143475 274877906944 6235482409739 26856533581103104 qz327 (@Enclosure.Real.IsNear.recentre' (Real.cos qz31) Bool.false 1048476 1048576 71066215 102449545216 262119 262144 71066215 102449545216 (ep184 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz323 (@Neg.neg Real Real.instNeg (Real.sin qz31)) 349525 1048576 1 1048576 14439 1048576 71066215 102449545216 5046791475 1099511627776 49681801209853 214852268648824832 qz327 (@Enclosure.Real.IsNear.neg (Real.sin qz31) Bool.true 14439 1048576 71066215 102449545216 (@Enclosure.Real.IsNear.recentre' (Real.sin qz31) Bool.true 14439 1048576 71066215 102449545216 14439 1048576 71066215 102449545216 (ep188 rfl rfl) rfl)) rfl)

noncomputable def ep190 := @ep175 91617143475 274877906944 6235482409739 26856533581103104 Bool.false 5046791475 1099511627776 49681801209853 214852268648824832 Bool.true 62401249993669079990272 227014425013 549755813888 138366995688561 53713067162206208 Bool.false 829194108247028103380992 11783557003 17179869184 276509299707067 107426134324412416 EMRow46.d6 (ep176 ep189) rfl rfl

noncomputable abbrev qz32 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 10)))

noncomputable abbrev qz572 := (Real.log (Enclosure.sfrac Bool.false 10 1))

noncomputable abbrev qz33 := (@HMul.hMul Real Real Real qz269 qz279 qz572)

noncomputable def ep191 := @Enclosure.Complex.IsNear.of_eq qz568 (Complex.mk (@HMul.hMul Real Real Real qz0 qz32 (Real.cos qz33)) (@HMul.hMul Real Real Real qz0 qz32 (@Neg.neg Real Real.instNeg (Real.sin qz33)))) Bool.true 3102015095 1099511627776 47196315503315 214852268648824832 Bool.true 173841170263 549755813888 5924922294271 26856533581103104 (BSN.cpow_neg_s_mk qz12 134395 1000 10 qz13 rfl)

noncomputable abbrev qz328 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 10) qz14)

noncomputable def ep192 := @Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 10)) 3315889 1048576 1 1048576 165794 165795 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 10)) (Real.sqrt qz328) Bool.false 3315889 1048576 1 1048576 (BSN.sqrt_natCast_div_one 10) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz328) Bool.false 3315889 1048576 1 1048576 3315889 1048576 1 1048576 (BSN.sqrt_enclosure 10 1 1657944 1657945 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep193 := BSN.log_dyadic_bound 2 18 3 2 1574640 524288 195407 6528 48 116991 20 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 2) (BSN.artanhQ 18) 0 2 6528 1574640 48 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep194 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz572 134395 1000 0 1 10369917190100709 4503599627370496 1000000000586221 195407000000000000000 278733004152716957211 900719925474099200 26879000015757034259 39081400000000000000000 qz18 (BSN.isNear_log_sfrac 10 1 10369917190100709 4503599627370496 1000000000586221 195407000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz328) Bool.false 43494585150108164161536 18889465931478580854784 1000000000586221 195407000000000000000 10369917190100709 4503599627370496 1000000000586221 195407000000000000000 (BSN.log_rat_reduce_isNear 10 1 3 20 16 116991 524288 24973259072661432 36028797018963968 195407 1000000000000000 rfl rfl rfl rfl (ep193 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep195 := BSN.sin_dyadic_bound_f 19159356 2147483648 1 0 1048576 391196 0 1 1 0 1 1 9355 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 19159356) qz15 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 19159356) qz16 0 0 rfl) rfl rfl

noncomputable abbrev qz329 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 324487923) qz23)

noncomputable def ep196 := @Enclosure.Real.IsNear.cos_image qz33 qz329 Bool.false 324487923 1048576 723 1048576 Bool.true 9355 1048576 1 195407 (@Enclosure.Real.IsNear.recentre' qz33 Bool.false 278733004152716957211 900719925474099200 26879000015757034259 39081400000000000000000 324487923 1048576 723 1048576 (ep194 rfl) rfl) (Enclosure.sfrac_false_div 324487923 1048576) (BSN.cos_reduce1 qz329 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 1348219841421399556096) qz24) 226375608064910080 72057594037927936 Bool.false 9355 1048576 49 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q1 324487923 1048576 226375608064910080 72057594037927936 49 1348219841421399556096 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 9355 1048576 1348219841421399556096 151115727451828646838272 19159356 2147483648 391196 390814 (ep195 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep197 := BSN.cos_dyadic_bound_f 19159356 2147483648 1 0 1048576 391196 0 1 1 0 1 1 1048534 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 19159356) qz19 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 19159356) qz20 0 0 rfl) rfl rfl

noncomputable def ep198 := @Enclosure.Real.IsNear.sin_image qz33 qz329 Bool.false 324487923 1048576 723 1048576 Bool.false 1048534 1048576 1 195407 (@Enclosure.Real.IsNear.recentre' qz33 Bool.false 278733004152716957211 900719925474099200 26879000015757034259 39081400000000000000000 324487923 1048576 723 1048576 (ep194 rfl) rfl) (Enclosure.sfrac_false_div 324487923 1048576) (BSN.sin_reduce1 qz329 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 1348219841421399556096) qz24) 226375608064910080 72057594037927936 Bool.false 1048534 1048576 49 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q1 324487923 1048576 226375608064910080 72057594037927936 49 1348219841421399556096 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1048534 1048576 1348219841421399556096 151115727451828646838272 19159356 2147483648 391196 390814 (ep197 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz330 := (@Enclosure.Real.IsNear.recentre' qz32 Bool.false 331589 1048576 1 1048576 331589 1048576 1 1048576 (ep192 rfl rfl) rfl)

noncomputable def ep199 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz32 (Real.cos qz33)) (@HMul.hMul Real Real Real qz0 qz32 (@Neg.neg Real Real.instNeg (Real.sin qz33))) Bool.true 3102015095 1099511627776 47196315503315 214852268648824832 Bool.true 173841170263 549755813888 5924922294271 26856533581103104 (@Enclosure.Real.IsNear.mulLit_ft qz32 (Real.cos qz33) 331589 1048576 1 1048576 9355 1048576 142327837 204899090432 3102015095 1099511627776 47196315503315 214852268648824832 qz330 (@Enclosure.Real.IsNear.recentre' (Real.cos qz33) Bool.true 9355 1048576 142327837 204899090432 9355 1048576 142327837 204899090432 (ep196 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz32 (@Neg.neg Real Real.instNeg (Real.sin qz33)) 331589 1048576 1 1048576 524267 524288 142327837 204899090432 173841170263 549755813888 5924922294271 26856533581103104 qz330 (@Enclosure.Real.IsNear.neg (Real.sin qz33) Bool.false 524267 524288 142327837 204899090432 (@Enclosure.Real.IsNear.recentre' (Real.sin qz33) Bool.false 1048534 1048576 142327837 204899090432 524267 524288 142327837 204899090432 (ep198 rfl rfl) rfl)) rfl)

noncomputable def ep200 := @ep173 3102015095 1099511627776 47196315503315 214852268648824832 Bool.true 173841170263 549755813888 5924922294271 26856533581103104 Bool.true 251310350807920906600448 457130865121 1099511627776 600664298257559 214852268648824832 Bool.false 3491510406768096182272 203232653833 549755813888 300208988884151 107426134324412416 (ep174 (BSN.head_sum_c_succ qz5 9 10 rfl rfl) (ep190 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep191 ep199) rfl rfl

noncomputable abbrev qz34 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 11)))

noncomputable abbrev qz573 := (Real.log (Enclosure.sfrac Bool.false 11 1))

noncomputable abbrev qz35 := (@HMul.hMul Real Real Real qz269 qz279 qz573)

noncomputable def ep201 := @Enclosure.Complex.IsNear.of_eq qz567 (Complex.mk (@HMul.hMul Real Real Real qz0 qz34 (Real.cos qz35)) (@HMul.hMul Real Real Real qz0 qz34 (@Neg.neg Real Real.instNeg (Real.sin qz35)))) Bool.true 82585583069 1099511627776 44987348434259 214852268648824832 Bool.true 160531562163 549755813888 22567372064883 107426134324412416 (BSN.cpow_neg_s_mk qz12 134395 1000 11 qz13 rfl)

noncomputable abbrev qz331 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 11) qz14)

noncomputable def ep202 := @Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 11)) 3477733 1048576 1 1048576 158078 158079 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 11)) (Real.sqrt qz331) Bool.false 3477733 1048576 1 1048576 (BSN.sqrt_natCast_div_one 11) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz331) Bool.false 3477733 1048576 1 1048576 3477733 1048576 1 1048576 (BSN.sqrt_enclosure 11 1 1738866 1738867 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep203 := BSN.log_dyadic_bound 3 19 4 3 4939817505 524288 195407 41676111 10935 166961 22 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 3) (BSN.artanhQ 19) 0 3 41676111 4939817505 10935 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep204 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz573 134395 1000 0 1 10799156221662949 4503599627370496 1000000000586221 195407000000000000000 290270520082078406171 900719925474099200 26879000015757034259 39081400000000000000000 qz18 (BSN.isNear_log_sfrac 11 1 10799156221662949 4503599627370496 1000000000586221 195407000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz331) Bool.false 45294944137145793642496 18889465931478580854784 1000000000586221 195407000000000000000 10799156221662949 4503599627370496 1000000000586221 195407000000000000000 (BSN.log_rat_reduce_isNear 11 1 3 22 16 166961 524288 24973259072661432 36028797018963968 195407 1000000000000000 rfl rfl rfl rfl (ep203 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep205 := nat_lit 85451404292113719309990188011109041

noncomputable def ep206 := BSN.sin_dyadic_bound_f 540666923 2147483648 2 1 1048576 391196 ep205 ep58 ep205 ep205 ep59 ep205 261217 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 540666923) qz15 0 1 ep205 ep58 ep205 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 540666923) qz16 0 1 ep205 ep59 ep205 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz332 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 2639995) (@Nat.cast Real Real.instNatCast 8192))

noncomputable def ep207 := @Enclosure.Real.IsNear.cos_image qz35 qz332 Bool.false 2639995 8192 361 524288 Bool.true 261217 1048576 1 195407 (@Enclosure.Real.IsNear.recentre' qz35 Bool.false 290270520082078406171 900719925474099200 26879000015757034259 39081400000000000000000 2639995 8192 361 524288 (ep204 rfl) rfl) (Enclosure.sfrac_false_div 2639995 8192) (BSN.cos_reduce1 qz332 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 297234784431730851840) (@Nat.cast Real Real.instNatCast 1180591620717411303424)) 226375608064910080 72057594037927936 Bool.false 261217 1048576 51 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q1 2639995 8192 226375608064910080 72057594037927936 51 297234784431730851840 1180591620717411303424 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 261217 1048576 297234784431730851840 1180591620717411303424 540666923 2147483648 391196 390814 (ep206 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep208 := BSN.cos_dyadic_bound_f 540666923 2147483648 2 1 1048576 391196 ep205 ep62 ep205 ep205 ep63 ep205 1015518 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 540666923) qz19 0 1 ep205 ep62 ep205 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 540666923) qz20 0 1 ep205 ep63 ep205 rfl rfl rfl rfl) rfl rfl

noncomputable def ep209 := @Enclosure.Real.IsNear.sin_image qz35 qz332 Bool.false 2639995 8192 361 524288 Bool.false 1015518 1048576 1 195407 (@Enclosure.Real.IsNear.recentre' qz35 Bool.false 290270520082078406171 900719925474099200 26879000015757034259 39081400000000000000000 2639995 8192 361 524288 (ep204 rfl) rfl) (Enclosure.sfrac_false_div 2639995 8192) (BSN.sin_reduce1 qz332 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 297234784431730851840) (@Nat.cast Real Real.instNatCast 1180591620717411303424)) 226375608064910080 72057594037927936 Bool.false 1015518 1048576 51 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q1 2639995 8192 226375608064910080 72057594037927936 51 297234784431730851840 1180591620717411303424 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1015518 1048576 297234784431730851840 1180591620717411303424 540666923 2147483648 391196 390814 (ep208 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz333 := (@Enclosure.Real.IsNear.recentre' qz34 Bool.false 316157 1048576 1 1048576 316157 1048576 1 1048576 (ep202 rfl rfl) rfl)

noncomputable def ep210 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz34 (Real.cos qz35)) (@HMul.hMul Real Real Real qz0 qz34 (@Neg.neg Real Real.instNeg (Real.sin qz35))) Bool.true 82585583069 1099511627776 44987348434259 214852268648824832 Bool.true 160531562163 549755813888 22567372064883 107426134324412416 (@Enclosure.Real.IsNear.mulLit_ft qz34 (Real.cos qz35) 316157 1048576 1 1048576 261217 1048576 71066215 102449545216 82585583069 1099511627776 44987348434259 214852268648824832 qz333 (@Enclosure.Real.IsNear.recentre' (Real.cos qz35) Bool.true 261217 1048576 71066215 102449545216 261217 1048576 71066215 102449545216 (ep207 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz34 (@Neg.neg Real Real.instNeg (Real.sin qz35)) 316157 1048576 1 1048576 507759 524288 71066215 102449545216 160531562163 549755813888 22567372064883 107426134324412416 qz333 (@Enclosure.Real.IsNear.neg (Real.sin qz35) Bool.false 507759 524288 71066215 102449545216 (@Enclosure.Real.IsNear.recentre' (Real.sin qz35) Bool.false 1015518 1048576 71066215 102449545216 507759 524288 71066215 102449545216 (ep209 rfl rfl) rfl)) rfl)

noncomputable def ep211 := @ep171 82585583069 1099511627776 44987348434259 214852268648824832 Bool.true 160531562163 549755813888 22567372064883 107426134324412416 Bool.true 593424510486868068925440 269858224095 549755813888 322825823345909 107426134324412416 Bool.false 23475173404946947112960 21350545835 274877906944 161388180474517 53713067162206208 (ep172 (BSN.head_sum_c_succ qz5 10 11 rfl rfl) (ep200 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep201 ep210) rfl rfl

noncomputable abbrev qz36 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 12)))

noncomputable abbrev qz574 := (Real.log (Enclosure.sfrac Bool.false 12 1))

noncomputable abbrev qz37 := (@HMul.hMul Real Real Real qz269 qz279 qz574)

noncomputable def ep212 := @Enclosure.Complex.IsNear.of_eq qz566 (Complex.mk (@HMul.hMul Real Real Real qz0 qz36 (Real.cos qz37)) (@HMul.hMul Real Real Real qz0 qz36 (@Neg.neg Real Real.instNeg (Real.sin qz37)))) Bool.false 46151303499 274877906944 674099605819 3357066697637888 Bool.true 129096940833 549755813888 21594940084093 107426134324412416 (BSN.cpow_neg_s_mk qz12 134395 1000 12 qz13 rfl)

noncomputable abbrev qz334 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 12) qz14)

noncomputable def ep213 := @Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 12)) 3632373 1048576 1 1048576 151348 151349 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 12)) (Real.sqrt qz334) Bool.false 3632373 1048576 1 1048576 (BSN.sqrt_natCast_div_one 12) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz334) Bool.false 3632373 1048576 1 1048576 3632373 1048576 1 1048576 (BSN.sqrt_enclosure 12 1 1816186 1816187 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep214 := BSN.log_dyadic_bound 4 20 4 3 6720000000 524288 195407 91811840 61440 212580 24 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 4) (BSN.artanhQ 20) 0 3 91811840 6720000000 61440 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep215 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz574 134395 1000 0 1 11191020447815397 4503599627370496 1000000000586221 195407000000000000000 300803438616830055963 900719925474099200 26879000015757034259 39081400000000000000000 qz18 (BSN.isNear_log_sfrac 12 1 11191020447815397 4503599627370496 1000000000586221 195407000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz334) Bool.false 46938541828353910898688 18889465931478580854784 1000000000586221 195407000000000000000 11191020447815397 4503599627370496 1000000000586221 195407000000000000000 (BSN.log_rat_reduce_isNear 12 1 3 24 16 212580 524288 24973259072661432 36028797018963968 195407 1000000000000000 rfl rfl rfl rfl (ep214 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep216 := nat_lit 619445645083969220590895384102374656318851256981578535154078499359972581769216

noncomputable def ep217 := nat_lit 300280937337513849987786142729446128971573061532235208366014397851002535936

noncomputable def ep218 := nat_lit 1857736373377232634072710580021665076698610624821671135045503469284215740235776

noncomputable def ep219 := BSN.cos_dyadic_bound_f 2040285628 2147483648 3 2 1048576 391196 ep216 ep79 ep217 ep218 ep81 ep217 609868 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2040285628) qz19 0 2 ep216 ep79 ep217 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2040285628) qz20 0 2 ep218 ep81 ep217 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz335 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 350181291) qz23)

noncomputable def ep220 := @Enclosure.Real.IsNear.cos_image qz37 qz335 Bool.false 350181291 1048576 361 524288 Bool.false 609868 1048576 1 195407 (@Enclosure.Real.IsNear.recentre' qz37 Bool.false 300803438616830055963 900719925474099200 26879000015757034259 39081400000000000000000 350181291 1048576 361 524288 (ep215 rfl) rfl) (Enclosure.sfrac_false_div 350181291 1048576) (BSN.cos_reduce0 qz335 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 143572337429530953121792) qz24) 226375608064910080 72057594037927936 Bool.false 609868 1048576 53 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q0 350181291 1048576 226375608064910080 72057594037927936 53 143572337429530953121792 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 609868 1048576 143572337429530953121792 151115727451828646838272 2040285628 2147483648 391196 390814 (ep219 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep221 := nat_lit 1114761936401274585983621462470090824470755004117615575110648487329669845155840

noncomputable def ep222 := nat_lit 2919128426200029845628552176523914008452690082970321934952439157790709876064256

noncomputable def ep223 := BSN.sin_dyadic_bound_f 2040285628 2147483648 3 2 1048576 391196 ep221 ep72 ep217 ep222 ep75 ep217 852978 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2040285628) qz15 0 2 ep221 ep72 ep217 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2040285628) qz16 0 2 ep222 ep75 ep217 rfl rfl rfl rfl) rfl rfl

noncomputable def ep224 := @Enclosure.Real.IsNear.sin_image qz37 qz335 Bool.false 350181291 1048576 361 524288 Bool.false 852978 1048576 1 195407 (@Enclosure.Real.IsNear.recentre' qz37 Bool.false 300803438616830055963 900719925474099200 26879000015757034259 39081400000000000000000 350181291 1048576 361 524288 (ep215 rfl) rfl) (Enclosure.sfrac_false_div 350181291 1048576) (BSN.sin_reduce0 qz335 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 143572337429530953121792) qz24) 226375608064910080 72057594037927936 Bool.false 852978 1048576 53 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q0 350181291 1048576 226375608064910080 72057594037927936 53 143572337429530953121792 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 852978 1048576 143572337429530953121792 151115727451828646838272 2040285628 2147483648 391196 390814 (ep223 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz336 := (@Enclosure.Real.IsNear.recentre' qz36 Bool.false 302697 1048576 1 1048576 302697 1048576 1 1048576 (ep213 rfl rfl) rfl)

noncomputable def ep225 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz36 (Real.cos qz37)) (@HMul.hMul Real Real Real qz0 qz36 (@Neg.neg Real Real.instNeg (Real.sin qz37))) Bool.false 46151303499 274877906944 674099605819 3357066697637888 Bool.true 129096940833 549755813888 21594940084093 107426134324412416 (@Enclosure.Real.IsNear.mulLit_ff qz36 (Real.cos qz37) 302697 1048576 1 1048576 152467 262144 71066215 102449545216 46151303499 274877906944 674099605819 3357066697637888 qz336 (@Enclosure.Real.IsNear.recentre' (Real.cos qz37) Bool.false 609868 1048576 71066215 102449545216 152467 262144 71066215 102449545216 (ep220 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz36 (@Neg.neg Real Real.instNeg (Real.sin qz37)) 302697 1048576 1 1048576 426489 524288 71066215 102449545216 129096940833 549755813888 21594940084093 107426134324412416 qz336 (@Enclosure.Real.IsNear.neg (Real.sin qz37) Bool.false 426489 524288 71066215 102449545216 (@Enclosure.Real.IsNear.recentre' (Real.sin qz37) Bool.false 852978 1048576 71066215 102449545216 426489 524288 71066215 102449545216 (ep224 rfl rfl) rfl)) rfl)

noncomputable def ep226 := @ep169 46151303499 274877906944 674099605819 3357066697637888 Bool.true 129096940833 549755813888 21594940084093 107426134324412416 Bool.true 48806116393773661421568 177555617097 549755813888 344397010732117 107426134324412416 Bool.true 23748310186574974287872 86395849163 549755813888 344371301033127 107426134324412416 (ep170 (BSN.head_sum_c_succ qz5 11 12 rfl rfl) (ep211 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep212 ep225) rfl rfl

noncomputable abbrev qz38 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 13)))

noncomputable abbrev qz575 := (Real.log (Enclosure.sfrac Bool.false 13 1))

noncomputable abbrev qz39 := (@HMul.hMul Real Real Real qz269 qz279 qz575)

noncomputable def ep227 := @Enclosure.Complex.IsNear.of_eq qz565 (Complex.mk (@HMul.hMul Real Real Real qz0 qz38 (Real.cos qz39)) (@HMul.hMul Real Real Real qz0 qz38 (@Neg.neg Real Real.instNeg (Real.sin qz39)))) Bool.false 199177983771 1099511627776 41469351582259 214852268648824832 Bool.false 230916661053 1099511627776 41490677129797 214852268648824832 (BSN.cpow_neg_s_mk qz12 134395 1000 13 qz13 rfl)

noncomputable abbrev qz337 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 13) qz14)

noncomputable def ep228 := @Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 13)) 3780695 1048576 1 1048576 145411 145412 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 13)) (Real.sqrt qz337) Bool.false 3780695 1048576 1 1048576 (BSN.sqrt_natCast_div_one 13) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz337) Bool.false 3780695 1048576 1 1048576 3780695 1048576 1 1048576 (BSN.sqrt_enclosure 13 1 1890347 1890348 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep229 := BSN.log_dyadic_bound 5 21 5 4 35742602096145 524288 195407 699352521000 41015625 254545 26 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 5) (BSN.artanhQ 21) 0 4 699352521000 35742602096145 41015625 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep230 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz575 134395 1000 0 1 11551497052968677 4503599627370496 1000000000586221 195407000000000000000 310492689286745069083 900719925474099200 26879000015757034259 39081400000000000000000 qz18 (BSN.isNear_log_sfrac 13 1 11551497052968677 4503599627370496 1000000000586221 195407000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz337) Bool.false 48450490295254733815808 18889465931478580854784 1000000000586221 195407000000000000000 11551497052968677 4503599627370496 1000000000586221 195407000000000000000 (BSN.log_rat_reduce_isNear 13 1 3 26 16 254545 524288 24973259072661432 36028797018963968 195407 1000000000000000 rfl rfl rfl rfl (ep229 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep231 := nat_lit 5457536504395833424821130403245510801

noncomputable def ep232 := BSN.sin_dyadic_bound_f 1528442701 2147483648 2 1 1048576 391196 ep231 ep58 ep231 ep231 ep59 ep231 684877 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1528442701) qz15 0 1 ep231 ep58 ep231 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1528442701) qz16 0 1 ep231 ep59 ep231 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz338 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 361461063) qz23)

noncomputable def ep233 := @Enclosure.Real.IsNear.cos_image qz39 qz338 Bool.false 361461063 1048576 361 524288 Bool.false 684877 1048576 1 195407 (@Enclosure.Real.IsNear.recentre' qz39 Bool.false 310492689286745069083 900719925474099200 26879000015757034259 39081400000000000000000 361461063 1048576 361 524288 (ep230 rfl) rfl) (Enclosure.sfrac_false_div 361461063 1048576) (BSN.cos_reduce3 qz338 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 107554593446405829820416) qz24) 226375608064910080 72057594037927936 Bool.false 684877 1048576 54 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q3 361461063 1048576 226375608064910080 72057594037927936 54 107554593446405829820416 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 684877 1048576 107554593446405829820416 151115727451828646838272 1528442701 2147483648 391196 390814 (ep232 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep234 := nat_lit 195025645828386895597074329323353933935611551790233265674997280878093900968481

noncomputable def ep235 := nat_lit 29784704696813092747086001792718856035976157053111760422992241159407661601

noncomputable def ep236 := nat_lit 585017368075767060605728815966476364094762703056593573504145858151962887582241

noncomputable def ep237 := BSN.cos_dyadic_bound_f 1528442701 2147483648 3 2 1048576 391196 ep234 ep79 ep235 ep236 ep81 ep235 794011 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1528442701) qz19 0 2 ep234 ep79 ep235 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1528442701) qz20 0 2 ep236 ep81 ep235 rfl rfl rfl rfl) rfl rfl

noncomputable def ep238 := @Enclosure.Real.IsNear.sin_image qz39 qz338 Bool.false 361461063 1048576 361 524288 Bool.true 794011 1048576 1 195407 (@Enclosure.Real.IsNear.recentre' qz39 Bool.false 310492689286745069083 900719925474099200 26879000015757034259 39081400000000000000000 361461063 1048576 361 524288 (ep230 rfl) rfl) (Enclosure.sfrac_false_div 361461063 1048576) (BSN.sin_reduce3 qz338 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 107554593446405829820416) qz24) 226375608064910080 72057594037927936 Bool.false 794011 1048576 54 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q3 361461063 1048576 226375608064910080 72057594037927936 54 107554593446405829820416 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 794011 1048576 107554593446405829820416 151115727451828646838272 1528442701 2147483648 391196 390814 (ep237 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz339 := (@Enclosure.Real.IsNear.recentre' qz38 Bool.false 290823 1048576 1 1048576 290823 1048576 1 1048576 (ep228 rfl rfl) rfl)

noncomputable def ep239 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz38 (Real.cos qz39)) (@HMul.hMul Real Real Real qz0 qz38 (@Neg.neg Real Real.instNeg (Real.sin qz39))) Bool.false 199177983771 1099511627776 41469351582259 214852268648824832 Bool.false 230916661053 1099511627776 41490677129797 214852268648824832 (@Enclosure.Real.IsNear.mulLit_ff qz38 (Real.cos qz39) 290823 1048576 1 1048576 684877 1048576 71066215 102449545216 199177983771 1099511627776 41469351582259 214852268648824832 qz339 (@Enclosure.Real.IsNear.recentre' (Real.cos qz39) Bool.false 684877 1048576 71066215 102449545216 684877 1048576 71066215 102449545216 (ep233 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz38 (@Neg.neg Real Real.instNeg (Real.sin qz39)) 290823 1048576 1 1048576 794011 1048576 71066215 102449545216 230916661053 1099511627776 41490677129797 214852268648824832 qz339 (@Enclosure.Real.IsNear.neg (Real.sin qz39) Bool.true 794011 1048576 71066215 102449545216 (@Enclosure.Real.IsNear.recentre' (Real.sin qz39) Bool.true 794011 1048576 71066215 102449545216 794011 1048576 71066215 102449545216 (ep238 rfl rfl) rfl)) rfl)

noncomputable def ep240 := @ep167 199177983771 1099511627776 41469351582259 214852268648824832 Bool.false 230916661053 1099511627776 41490677129797 214852268648824832 Bool.true 85725210998497685274624 155933250423 1099511627776 730263373046493 214852268648824832 Bool.false 31954536191191548952576 58124962727 1099511627776 730233279196051 214852268648824832 (ep168 (BSN.head_sum_c_succ qz5 12 13 rfl rfl) (ep226 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep227 ep239) rfl rfl

noncomputable abbrev qz40 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 14)))

noncomputable abbrev qz576 := (Real.log (Enclosure.sfrac Bool.false 14 1))

noncomputable abbrev qz41 := (@HMul.hMul Real Real Real qz269 qz279 qz576)

noncomputable def ep241 := @Enclosure.Complex.IsNear.of_eq qz564 (Complex.mk (@HMul.hMul Real Real Real qz0 qz40 (Real.cos qz41)) (@HMul.hMul Real Real Real qz0 qz40 (@Neg.neg Real Real.instNeg (Real.sin qz41)))) Bool.true 34819912507 137438953472 2501624606729 13428266790551552 Bool.true 93573417943 1099511627776 39897007305627 214852268648824832 (BSN.cpow_neg_s_mk qz12 134395 1000 14 qz13 rfl)

noncomputable abbrev qz340 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 14) qz14)

noncomputable def ep242 := @Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 14)) 3923413 1048576 1 1048576 140121 140122 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 14)) (Real.sqrt qz340) Bool.false 3923413 1048576 1 1048576 (BSN.sqrt_natCast_div_one 14) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz340) Bool.false 3923413 1048576 1 1048576 3923413 1048576 1 1048576 (BSN.sqrt_enclosure 14 1 1961706 1961707 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep243 := BSN.log_dyadic_bound 6 22 5 4 51857700491520 524288 195407 1346332575744 176359680 293399 28 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 6) (BSN.artanhQ 22) 0 4 1346332575744 51857700491520 176359680 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep244 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz576 134395 1000 0 1 11885250371606245 4503599627370496 1000000000586221 195407000000000000000 63892728947680851871 180143985094819840 26879000015757034259 39081400000000000000000 qz18 (BSN.isNear_log_sfrac 14 1 11885250371606245 4503599627370496 1000000000586221 195407000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz340) Bool.false 49850353174629559828480 18889465931478580854784 1000000000586221 195407000000000000000 11885250371606245 4503599627370496 1000000000586221 195407000000000000000 (BSN.log_rat_reduce_isNear 14 1 3 28 16 293399 524288 24973259072661432 36028797018963968 195407 1000000000000000 rfl rfl rfl rfl (ep243 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep245 := nat_lit 3307071563403300460810667658376601534409029755521323516179601974070020669440000

noncomputable def ep246 := nat_lit 2639921700001442055175629867988123890476042453874980801140705827225600000000

noncomputable def ep247 := nat_lit 8657103745208641729271940466438166103820021481440049716316158313129784115200000

noncomputable def ep248 := BSN.sin_dyadic_bound_f 2677311360 2147483648 3 2 1048576 391196 ep245 ep72 ep246 ep247 ep75 ep246 993992 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2677311360) qz15 0 2 ep245 ep72 ep246 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2677311360) qz16 0 2 ep247 ep75 ep246 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz42 := (@Nat.cast Real Real.instNatCast 524288)

noncomputable abbrev qz43 := (@Nat.cast Real Real.instNatCast 75557863725914323419136)

noncomputable abbrev qz341 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 185952315) qz42)

noncomputable def ep249 := @Enclosure.Real.IsNear.cos_image qz41 qz341 Bool.false 185952315 524288 361 524288 Bool.true 993992 1048576 1 195407 (@Enclosure.Real.IsNear.recentre' qz41 Bool.false 63892728947680851871 180143985094819840 26879000015757034259 39081400000000000000000 185952315 524288 361 524288 (ep244 rfl) rfl) (Enclosure.sfrac_false_div 185952315 524288) (BSN.cos_reduce1 qz341 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 94199519110290399559680) qz43) 226375608064910080 72057594037927936 Bool.false 993992 1048576 56 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q1 185952315 524288 226375608064910080 72057594037927936 56 94199519110290399559680 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 993992 1048576 94199519110290399559680 75557863725914323419136 2677311360 2147483648 391196 390814 (ep248 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep250 := nat_lit 1838435278201834230252671201261662240845228105269124167122508077073222860800000

noncomputable def ep251 := nat_lit 5510025991205499806647662344049010474754732230899622539765242819565217382400000

noncomputable def ep252 := BSN.cos_dyadic_bound_f 2677311360 2147483648 3 2 1048576 391196 ep250 ep79 ep246 ep251 ep81 ep246 333901 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2677311360) qz19 0 2 ep250 ep79 ep246 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2677311360) qz20 0 2 ep251 ep81 ep246 rfl rfl rfl rfl) rfl rfl

noncomputable def ep253 := @Enclosure.Real.IsNear.sin_image qz41 qz341 Bool.false 185952315 524288 361 524288 Bool.false 333901 1048576 1 195407 (@Enclosure.Real.IsNear.recentre' qz41 Bool.false 63892728947680851871 180143985094819840 26879000015757034259 39081400000000000000000 185952315 524288 361 524288 (ep244 rfl) rfl) (Enclosure.sfrac_false_div 185952315 524288) (BSN.sin_reduce1 qz341 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 94199519110290399559680) qz43) 226375608064910080 72057594037927936 Bool.false 333901 1048576 56 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q1 185952315 524288 226375608064910080 72057594037927936 56 94199519110290399559680 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 333901 1048576 94199519110290399559680 75557863725914323419136 2677311360 2147483648 391196 390814 (ep252 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz342 := (@Enclosure.Real.IsNear.recentre' qz40 Bool.false 280243 1048576 1 1048576 280243 1048576 1 1048576 (ep242 rfl rfl) rfl)

noncomputable def ep254 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz40 (Real.cos qz41)) (@HMul.hMul Real Real Real qz0 qz40 (@Neg.neg Real Real.instNeg (Real.sin qz41))) Bool.true 34819912507 137438953472 2501624606729 13428266790551552 Bool.true 93573417943 1099511627776 39897007305627 214852268648824832 (@Enclosure.Real.IsNear.mulLit_ft qz40 (Real.cos qz41) 280243 1048576 1 1048576 124249 131072 71066215 102449545216 34819912507 137438953472 2501624606729 13428266790551552 qz342 (@Enclosure.Real.IsNear.recentre' (Real.cos qz41) Bool.true 993992 1048576 71066215 102449545216 124249 131072 71066215 102449545216 (ep249 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz40 (@Neg.neg Real Real.instNeg (Real.sin qz41)) 280243 1048576 1 1048576 333901 1048576 71066215 102449545216 93573417943 1099511627776 39897007305627 214852268648824832 qz342 (@Enclosure.Real.IsNear.neg (Real.sin qz41) Bool.false 333901 1048576 71066215 102449545216 (@Enclosure.Real.IsNear.recentre' (Real.sin qz41) Bool.false 333901 1048576 71066215 102449545216 333901 1048576 71066215 102449545216 (ep253 rfl rfl) rfl)) rfl)

noncomputable def ep255 := @ep165 34819912507 137438953472 2501624606729 13428266790551552 Bool.true 93573417943 1099511627776 39897007305627 214852268648824832 Bool.true 59716201429213892313088 434492550479 1099511627776 770289366754157 214852268648824832 Bool.true 38975988696688797679616 2215528451 68719476736 385065143250839 107426134324412416 (ep166 (BSN.head_sum_c_succ qz5 13 14 rfl rfl) (ep240 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep241 ep254) rfl rfl

noncomputable abbrev qz44 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 15)))

noncomputable abbrev qz577 := (Real.log (Enclosure.sfrac Bool.false 15 1))

noncomputable abbrev qz45 := (@HMul.hMul Real Real Real qz269 qz279 qz577)

noncomputable def ep256 := @Enclosure.Complex.IsNear.of_eq qz563 (Complex.mk (@HMul.hMul Real Real Real qz0 qz44 (Real.cos qz45)) (@HMul.hMul Real Real Real qz0 qz44 (@Neg.neg Real Real.instNeg (Real.sin qz45)))) Bool.false 126128214483 549755813888 19331642072771 107426134324412416 Bool.false 130236438417 1099511627776 38575216360119 214852268648824832 (BSN.cpow_neg_s_mk qz12 134395 1000 15 qz13 rfl)

noncomputable abbrev qz343 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 15) qz14)

noncomputable def ep257 := @Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 15)) 4061117 1048576 1 1048576 135370 135371 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 15)) (Real.sqrt qz343) Bool.false 4061117 1048576 1 1048576 (BSN.sqrt_natCast_div_one 15) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz343) Bool.false 4061117 1048576 1 1048576 4061117 1048576 1 1048576 (BSN.sqrt_enclosure 15 1 2030558 2030559 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep258 := BSN.log_dyadic_bound 7 23 6 5 430628584065881355 524288 195407 14087658153505881 266939110305 329571 30 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 7) (BSN.artanhQ 23) 0 5 14087658153505881 430628584065881355 266939110305 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep259 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz577 134395 1000 0 1 12195965485668069 4503599627370496 1000000000586221 195407000000000000000 327815356289272026651 900719925474099200 26879000015757034259 39081400000000000000000 qz18 (BSN.isNear_log_sfrac 15 1 12195965485668069 4503599627370496 1000000000586221 195407000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz343) Bool.false 51153586820399524478976 18889465931478580854784 1000000000586221 195407000000000000000 12195965485668069 4503599627370496 1000000000586221 195407000000000000000 (BSN.log_rat_reduce_isNear 15 1 3 30 16 329571 524288 24973259072661432 36028797018963968 195407 1000000000000000 rfl rfl rfl rfl (ep258 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep260 := nat_lit 1961648104766405416953841381671685809571953330552778429852250281653048932915745

noncomputable def ep261 := nat_lit 929454343811907945761126031423307693308460408852403095780641751568318028321

noncomputable def ep262 := nat_lit 5136144967355366336300257033660682241184997406023896758886534460541160404638241

noncomputable def ep263 := BSN.sin_dyadic_bound_f 2349787059 2147483648 3 2 1048576 391196 ep260 ep72 ep261 ep262 ep75 ep261 931726 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2349787059) qz15 0 2 ep260 ep72 ep261 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2349787059) qz16 0 2 ep262 ep75 ep261 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz344 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 190813651) qz42)

noncomputable def ep264 := @Enclosure.Real.IsNear.cos_image qz45 qz344 Bool.false 190813651 524288 361 524288 Bool.false 931726 1048576 1 195407 (@Enclosure.Real.IsNear.recentre' qz45 Bool.false 327815356289272026651 900719925474099200 26879000015757034259 39081400000000000000000 190813651 524288 361 524288 (ep259 rfl) rfl) (Enclosure.sfrac_false_div 190813651 524288) (BSN.cos_reduce3 qz344 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 82675782243405824786432) qz43) 226375608064910080 72057594037927936 Bool.false 931726 1048576 57 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q3 190813651 524288 226375608064910080 72057594037927936 57 82675782243405824786432 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 931726 1048576 82675782243405824786432 75557863725914323419136 2349787059 2147483648 391196 390814 (ep263 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep265 := nat_lit 1090217593467474968505805712498235808737000054933255751293819330585724215188001

noncomputable def ep266 := nat_lit 3268793871714801089625894885431860810824383243982062447689896708254036009507361

noncomputable def ep267 := BSN.cos_dyadic_bound_f 2349787059 2147483648 3 2 1048576 391196 ep265 ep79 ep261 ep266 ep81 ep261 481037 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2349787059) qz19 0 2 ep265 ep79 ep261 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2349787059) qz20 0 2 ep266 ep81 ep261 rfl rfl rfl rfl) rfl rfl

noncomputable def ep268 := @Enclosure.Real.IsNear.sin_image qz45 qz344 Bool.false 190813651 524288 361 524288 Bool.true 481037 1048576 1 195407 (@Enclosure.Real.IsNear.recentre' qz45 Bool.false 327815356289272026651 900719925474099200 26879000015757034259 39081400000000000000000 190813651 524288 361 524288 (ep259 rfl) rfl) (Enclosure.sfrac_false_div 190813651 524288) (BSN.sin_reduce3 qz344 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 82675782243405824786432) qz43) 226375608064910080 72057594037927936 Bool.false 481037 1048576 57 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q3 190813651 524288 226375608064910080 72057594037927936 57 82675782243405824786432 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 481037 1048576 82675782243405824786432 75557863725914323419136 2349787059 2147483648 391196 390814 (ep267 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz345 := (@Enclosure.Real.IsNear.recentre' qz44 Bool.false 270741 1048576 1 1048576 270741 1048576 1 1048576 (ep257 rfl rfl) rfl)

noncomputable def ep269 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz44 (Real.cos qz45)) (@HMul.hMul Real Real Real qz0 qz44 (@Neg.neg Real Real.instNeg (Real.sin qz45))) Bool.false 126128214483 549755813888 19331642072771 107426134324412416 Bool.false 130236438417 1099511627776 38575216360119 214852268648824832 (@Enclosure.Real.IsNear.mulLit_ff qz44 (Real.cos qz45) 270741 1048576 1 1048576 465863 524288 71066215 102449545216 126128214483 549755813888 19331642072771 107426134324412416 qz345 (@Enclosure.Real.IsNear.recentre' (Real.cos qz45) Bool.false 931726 1048576 71066215 102449545216 465863 524288 71066215 102449545216 (ep264 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz44 (@Neg.neg Real Real.instNeg (Real.sin qz45)) 270741 1048576 1 1048576 481037 1048576 71066215 102449545216 130236438417 1099511627776 38575216360119 214852268648824832 qz345 (@Enclosure.Real.IsNear.neg (Real.sin qz45) Bool.true 481037 1048576 71066215 102449545216 (@Enclosure.Real.IsNear.recentre' (Real.sin qz45) Bool.true 481037 1048576 71066215 102449545216 481037 1048576 71066215 102449545216 (ep268 rfl rfl) rfl)) rfl)

noncomputable def ep270 := @ep163 126128214483 549755813888 19331642072771 107426134324412416 Bool.false 130236438417 1099511627776 38575216360119 214852268648824832 Bool.true 100185367302171780972544 182236121513 1099511627776 808952650899699 214852268648824832 Bool.false 6513780606433478311936 94787983201 1099511627776 808705502861797 214852268648824832 (ep164 (BSN.head_sum_c_succ qz5 14 15 rfl rfl) (ep255 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep256 ep269) rfl rfl

noncomputable abbrev qz46 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 16)))

noncomputable abbrev qz578 := (Real.log (Enclosure.sfrac Bool.false 16 1))

noncomputable abbrev qz47 := (@HMul.hMul Real Real Real qz269 qz279 qz578)

noncomputable def ep271 := @Enclosure.Complex.IsNear.of_eq qz562 (Complex.mk (@HMul.hMul Real Real Real qz0 qz46 (Real.cos qz47)) (@HMul.hMul Real Real Real qz0 qz46 (@Neg.neg Real Real.instNeg (Real.sin qz47)))) Bool.true 92530449711 1099511627776 37328137906559 214852268648824832 Bool.true 258834493197 1099511627776 37452104498173 214852268648824832 (BSN.cpow_neg_s_mk qz12 134395 1000 16 qz13 rfl)

noncomputable abbrev qz346 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 16) qz14)

noncomputable def ep272 := @Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 16)) 4194305 1048576 1 1048576 131071 131072 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 16)) (Real.sqrt qz346) Bool.false 4194305 1048576 1 1048576 (BSN.sqrt_natCast_div_one 16) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz346) Bool.false 4194305 1048576 1 1048576 4194305 1048576 1 1048576 (BSN.sqrt_enclosure 16 1 2097152 2097153 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep273 := BSN.log_dyadic_bound 0 32 1 0 1 524288 195407 0 1 0 32 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 0) (BSN.artanhQ 32) 0 0 rfl) rfl rfl rfl

noncomputable def ep274 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz578 134395 1000 0 1 3121657384082679 1125899906842624 250000000195407 48851750000000000000 83907028826758328841 225179981368524800 6719750005252344753 9770350000000000000000 qz18 (BSN.isNear_log_sfrac 16 1 3121657384082679 1125899906842624 250000000195407 48851750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz346) Bool.false 52372720210750067441664 18889465931478580854784 1000000000781628 195407000000000000000 3121657384082679 1125899906842624 250000000195407 48851750000000000000 (BSN.log_rat_reduce_isNear 16 1 4 32 32 0 524288 24973259072661432 36028797018963968 195407 1000000000000000 rfl rfl rfl rfl (ep273 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep275 := nat_lit 295510680696803622432682851398047201

noncomputable def ep276 := BSN.sin_dyadic_bound_f 737298407 2147483648 2 1 1048576 391196 ep275 ep58 ep275 ep275 ep59 ep275 352977 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 737298407) qz15 0 1 ep275 ep58 ep275 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 737298407) qz16 0 1 ep275 ep59 ep275 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz347 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 195361275) qz42)

noncomputable def ep277 := @Enclosure.Real.IsNear.cos_image qz47 qz347 Bool.false 195361275 524288 361 524288 Bool.true 352977 1048576 1 195407 (@Enclosure.Real.IsNear.recentre' qz47 Bool.false 83907028826758328841 225179981368524800 6719750005252344753 9770350000000000000000 195361275 524288 361 524288 (ep274 rfl) rfl) (Enclosure.sfrac_false_div 195361275 524288) (BSN.cos_reduce1 qz347 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 25941381494868352696320) qz43) 226375608064910080 72057594037927936 Bool.false 352977 1048576 59 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q1 195361275 524288 226375608064910080 72057594037927936 59 25941381494868352696320 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 352977 1048576 25941381494868352696320 75557863725914323419136 737298407 2147483648 391196 390814 (ep276 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep278 := BSN.cos_dyadic_bound_f 737298407 2147483648 2 1 1048576 391196 ep275 ep62 ep275 ep275 ep63 ep275 987379 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 737298407) qz19 0 1 ep275 ep62 ep275 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 737298407) qz20 0 1 ep275 ep63 ep275 rfl rfl rfl rfl) rfl rfl

noncomputable def ep279 := @Enclosure.Real.IsNear.sin_image qz47 qz347 Bool.false 195361275 524288 361 524288 Bool.false 987379 1048576 1 195407 (@Enclosure.Real.IsNear.recentre' qz47 Bool.false 83907028826758328841 225179981368524800 6719750005252344753 9770350000000000000000 195361275 524288 361 524288 (ep274 rfl) rfl) (Enclosure.sfrac_false_div 195361275 524288) (BSN.sin_reduce1 qz347 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 25941381494868352696320) qz43) 226375608064910080 72057594037927936 Bool.false 987379 1048576 59 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q1 195361275 524288 226375608064910080 72057594037927936 59 25941381494868352696320 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 987379 1048576 25941381494868352696320 75557863725914323419136 737298407 2147483648 391196 390814 (ep278 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz348 := (@Enclosure.Real.IsNear.recentre' qz46 Bool.false 262143 1048576 1 1048576 262143 1048576 1 1048576 (ep272 rfl rfl) rfl)

noncomputable def ep280 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz46 (Real.cos qz47)) (@HMul.hMul Real Real Real qz0 qz46 (@Neg.neg Real Real.instNeg (Real.sin qz47))) Bool.true 92530449711 1099511627776 37328137906559 214852268648824832 Bool.true 258834493197 1099511627776 37452104498173 214852268648824832 (@Enclosure.Real.IsNear.mulLit_ft qz46 (Real.cos qz47) 262143 1048576 1 1048576 352977 1048576 71066215 102449545216 92530449711 1099511627776 37328137906559 214852268648824832 qz348 (@Enclosure.Real.IsNear.recentre' (Real.cos qz47) Bool.true 352977 1048576 71066215 102449545216 352977 1048576 71066215 102449545216 (ep277 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz46 (@Neg.neg Real Real.instNeg (Real.sin qz47)) 262143 1048576 1 1048576 987379 1048576 71066215 102449545216 258834493197 1099511627776 37452104498173 214852268648824832 qz348 (@Enclosure.Real.IsNear.neg (Real.sin qz47) Bool.false 987379 1048576 71066215 102449545216 (@Enclosure.Real.IsNear.recentre' (Real.sin qz47) Bool.false 987379 1048576 71066215 102449545216 987379 1048576 71066215 102449545216 (ep279 rfl rfl) rfl)) rfl)

noncomputable def ep281 := @ep161 92530449711 1099511627776 37328137906559 214852268648824832 Bool.true 258834493197 1099511627776 37452104498173 214852268648824832 Bool.true 302109039984930480717824 34345821403 137438953472 423140394403129 107426134324412416 Bool.true 180371045236673815248896 41011627499 274877906944 423078803679985 107426134324412416 (ep162 (BSN.head_sum_c_succ qz5 15 16 rfl rfl) (ep270 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep271 ep280) rfl rfl

theorem EMRow46.d7 : Enclosure.Complex.IsNear qz30 Bool.true 34345821403 137438953472 423140394403129 107426134324412416 Bool.true 41011627499 274877906944 423078803679985 107426134324412416 := ep160 (BSN.head_sum_c_succ qz5 16 17 rfl rfl) (ep281 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable abbrev qz48 := (BSN.headSumC qz273 25)

noncomputable abbrev qz579 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 24) qz7)

noncomputable def ep282 := @Enclosure.Complex.IsNear.of_eq qz48 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 24) qz579) Bool.false 437138491985 549755813888 556199449948967 107426134324412416 Bool.true 241886317881 1099511627776 1111753911610533 214852268648824832

noncomputable def ep283 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 24) qz579 Bool.false 163026446551 274877906944 135221755410897 26856533581103104 Bool.true 136844865387 549755813888 67581428209589 13428266790551552 Bool.false

noncomputable abbrev qz580 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 23) qz7)

noncomputable def ep284 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 24) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 23) qz580) Bool.false 163026446551 274877906944 135221755410897 26856533581103104 Bool.true 136844865387 549755813888 67581428209589 13428266790551552

noncomputable def ep285 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 23) qz580 Bool.false 442868152135 1099511627776 1050510639085175 214852268648824832 Bool.true 179980434189 1099511627776 1050142697865339 214852268648824832 Bool.false

noncomputable abbrev qz581 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 22) qz7)

noncomputable def ep286 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 23) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 22) qz581) Bool.false 442868152135 1099511627776 1050510639085175 214852268648824832 Bool.true 179980434189 1099511627776 1050142697865339 214852268648824832

noncomputable def ep287 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 22) qz581 Bool.false 268233918901 1099511627776 1018583152776301 214852268648824832 Bool.true 23603206917 1099511627776 1018231169664527 214852268648824832 Bool.false

noncomputable abbrev qz582 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 21) qz7)

noncomputable def ep288 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 22) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 21) qz582) Bool.false 268233918901 1099511627776 1018583152776301 214852268648824832 Bool.true 23603206917 1099511627776 1018231169664527 214852268648824832

noncomputable def ep289 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 21) qz582 Bool.false 94553048271 1099511627776 985763768639211 214852268648824832 Bool.false 141934488729 1099511627776 985425693816069 214852268648824832 Bool.false

noncomputable abbrev qz583 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 20) qz7)

noncomputable def ep290 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 21) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 20) qz583) Bool.false 94553048271 1099511627776 985763768639211 214852268648824832 Bool.false 141934488729 1099511627776 985425693816069 214852268648824832

noncomputable def ep291 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 20) qz583 Bool.true 122669818903 1099511627776 952256943743589 214852268648824832 Bool.false 257089248699 1099511627776 952003932714059 214852268648824832 Bool.false

noncomputable abbrev qz584 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 19) qz7)

noncomputable def ep292 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 20) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 19) qz584) Bool.true 122669818903 1099511627776 952256943743589 214852268648824832 Bool.false 257089248699 1099511627776 952003932714059 214852268648824832

noncomputable def ep293 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 19) qz584 Bool.true 5828351851 17179869184 229465552605359 53713067162206208 Bool.false 113095083413 549755813888 458893727955165 107426134324412416 Bool.false

noncomputable abbrev qz585 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 18) qz7)

noncomputable def ep294 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 19) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 18) qz585) Bool.true 5828351851 17179869184 229465552605359 53713067162206208 Bool.false 113095083413 549755813888 458893727955165 107426134324412416

noncomputable def ep295 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 18) qz585 Bool.true 489170298293 1099511627776 882642058895623 214852268648824832 Bool.true 2738658663 549755813888 441237988214353 107426134324412416 Bool.false

noncomputable abbrev qz586 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 17) qz7)

noncomputable def ep296 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 18) (@HAdd.hAdd Complex Complex Complex qz4 qz30 qz586) Bool.true 489170298293 1099511627776 882642058895623 214852268648824832 Bool.true 2738658663 549755813888 441237988214353 107426134324412416

noncomputable def ep297 := @Enclosure.Complex.IsNear.addLitP qz30 qz586 Bool.true 34345821403 137438953472 423140394403129 107426134324412416 Bool.true 41011627499 274877906944 423078803679985 107426134324412416 Bool.true

noncomputable abbrev qz49 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 17)))

noncomputable abbrev qz587 := (Real.log (Enclosure.sfrac Bool.false 17 1))

noncomputable abbrev qz50 := (@HMul.hMul Real Real Real qz269 qz279 qz587)

noncomputable def ep298 := @Enclosure.Complex.IsNear.of_eq qz586 (Complex.mk (@HMul.hMul Real Real Real qz0 qz49 (Real.cos qz50)) (@HMul.hMul Real Real Real qz0 qz49 (@Neg.neg Real Real.instNeg (Real.sin qz50)))) Bool.true 214403727069 1099511627776 36361270089365 214852268648824832 Bool.false 79284596335 549755813888 567474516699 3357066697637888 (BSN.cpow_neg_s_mk qz12 134395 1000 17 qz13 rfl)

noncomputable abbrev qz349 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 17) qz14)

noncomputable def ep299 := @Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 17)) 4323389 1048576 1 1048576 127158 127159 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 17)) (Real.sqrt qz349) Bool.false 4323389 1048576 1 1048576 (BSN.sqrt_natCast_div_one 17) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz349) Bool.false 4323389 1048576 1 1048576 4323389 1048576 1 1048576 (BSN.sqrt_enclosure 17 1 2161694 2161695 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep300 := BSN.log_dyadic_bound 1 33 2 1 3267 524288 195407 1 1 31784 34 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 1) (BSN.artanhQ 33) 0 1 1 3267 1 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep301 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz587 134395 1000 0 1 3189913004350711 1125899906842624 250000000195407 48851750000000000000 85741671643942760969 225179981368524800 6719750005252344753 9770350000000000000000 qz18 (BSN.isNear_log_sfrac 17 1 3189913004350711 1125899906842624 250000000195407 48851750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz349) Bool.false 53517859495200818200576 18889465931478580854784 1000000000781628 195407000000000000000 3189913004350711 1125899906842624 250000000195407 48851750000000000000 (BSN.log_rat_reduce_isNear 17 1 4 34 32 31784 524288 24973259072661432 36028797018963968 195407 1000000000000000 rfl rfl rfl rfl (ep300 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep302 := nat_lit 124969292211209134781366812663295919169885848981594983692545663054407522123776

noncomputable def ep303 := nat_lit 12231060572433162483936805600034223306413474901354782213786212190713348096

noncomputable def ep304 := nat_lit 374883414512482538019132564378687689063044719994982241513209416738841139675136

noncomputable def ep305 := BSN.cos_dyadic_bound_f 1367517884 2147483648 3 2 1048576 391196 ep302 ep79 ep303 ep304 ep81 ep303 843057 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1367517884) qz19 0 2 ep302 ep79 ep303 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1367517884) qz20 0 2 ep304 ep81 ep303 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz350 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 399265771) qz23)

noncomputable def ep306 := @Enclosure.Real.IsNear.cos_image qz50 qz350 Bool.false 399265771 1048576 723 1048576 Bool.true 843057 1048576 1 195407 (@Enclosure.Real.IsNear.recentre' qz50 Bool.false 85741671643942760969 225179981368524800 6719750005252344753 9770350000000000000000 399265771 1048576 723 1048576 (ep301 rfl) rfl) (Enclosure.sfrac_false_div 399265771 1048576) (BSN.cos_reduce2 qz350 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 96230516166982423805952) qz24) 226375608064910080 72057594037927936 Bool.false 843057 1048576 60 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q2 399265771 1048576 226375608064910080 72057594037927936 60 96230516166982423805952 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 843057 1048576 96230516166982423805952 151115727451828646838272 1367517884 2147483648 391196 390814 (ep305 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep307 := nat_lit 3497293320903061239816351177140551936

noncomputable def ep308 := BSN.sin_dyadic_bound_f 1367517884 2147483648 2 1 1048576 391196 ep307 ep58 ep307 ep307 ep59 ep307 623510 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1367517884) qz15 0 1 ep307 ep58 ep307 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1367517884) qz16 0 1 ep307 ep59 ep307 rfl rfl rfl rfl) rfl rfl

noncomputable def ep309 := @Enclosure.Real.IsNear.sin_image qz50 qz350 Bool.false 399265771 1048576 723 1048576 Bool.true 623510 1048576 1 195407 (@Enclosure.Real.IsNear.recentre' qz50 Bool.false 85741671643942760969 225179981368524800 6719750005252344753 9770350000000000000000 399265771 1048576 723 1048576 (ep301 rfl) rfl) (Enclosure.sfrac_false_div 399265771 1048576) (BSN.sin_reduce2 qz350 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 96230516166982423805952) qz24) 226375608064910080 72057594037927936 Bool.false 623510 1048576 60 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q2 399265771 1048576 226375608064910080 72057594037927936 60 96230516166982423805952 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 623510 1048576 96230516166982423805952 151115727451828646838272 1367517884 2147483648 391196 390814 (ep308 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz351 := (@Enclosure.Real.IsNear.recentre' qz49 Bool.false 254317 1048576 1 1048576 254317 1048576 1 1048576 (ep299 rfl rfl) rfl)

noncomputable def ep310 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz49 (Real.cos qz50)) (@HMul.hMul Real Real Real qz0 qz49 (@Neg.neg Real Real.instNeg (Real.sin qz50))) Bool.true 214403727069 1099511627776 36361270089365 214852268648824832 Bool.false 79284596335 549755813888 567474516699 3357066697637888 (@Enclosure.Real.IsNear.mulLit_ft qz49 (Real.cos qz50) 254317 1048576 1 1048576 843057 1048576 142327837 204899090432 214403727069 1099511627776 36361270089365 214852268648824832 qz351 (@Enclosure.Real.IsNear.recentre' (Real.cos qz50) Bool.true 843057 1048576 142327837 204899090432 843057 1048576 142327837 204899090432 (ep306 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz49 (@Neg.neg Real Real.instNeg (Real.sin qz50)) 254317 1048576 1 1048576 311755 524288 142327837 204899090432 79284596335 549755813888 567474516699 3357066697637888 qz351 (@Enclosure.Real.IsNear.neg (Real.sin qz50) Bool.true 311755 524288 142327837 204899090432 (@Enclosure.Real.IsNear.recentre' (Real.sin qz50) Bool.true 623510 1048576 142327837 204899090432 311755 524288 142327837 204899090432 (ep309 rfl rfl) rfl)) rfl)

noncomputable def ep311 := @ep297 214403727069 1099511627776 36361270089365 214852268648824832 Bool.false 79284596335 549755813888 567474516699 3357066697637888 Bool.true 67231053866975988023296 489170298293 1099511627776 882642058895623 214852268648824832 Bool.true 752796761119493455872 2738658663 549755813888 441237988214353 107426134324412416 EMRow46.d7 (ep298 ep310) rfl rfl

noncomputable abbrev qz51 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 18)))

noncomputable abbrev qz588 := (Real.log (Enclosure.sfrac Bool.false 18 1))

noncomputable abbrev qz52 := (@HMul.hMul Real Real Real qz269 qz279 qz588)

noncomputable def ep312 := @Enclosure.Complex.IsNear.of_eq qz585 (Complex.mk (@HMul.hMul Real Real Real qz0 qz51 (Real.cos qz52)) (@HMul.hMul Real Real Real qz0 qz51 (@Neg.neg Real Real.instNeg (Real.sin qz52)))) Bool.false 116155779829 1099511627776 35220151525813 214852268648824832 Bool.false 28958435519 137438953472 4413934935203 26856533581103104 (BSN.cpow_neg_s_mk qz12 134395 1000 18 qz13 rfl)

noncomputable abbrev qz352 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 18) qz14)

noncomputable def ep313 := @Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 18)) 4448731 1048576 1 1048576 123575 123576 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 18)) (Real.sqrt qz352) Bool.false 4448731 1048576 1 1048576 (BSN.sqrt_natCast_div_one 18) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz352) Bool.false 4448731 1048576 1 1048576 4448731 1048576 1 1048576 (BSN.sqrt_enclosure 18 1 2224365 2224366 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep314 := BSN.log_dyadic_bound 2 34 3 2 20045040 524288 195407 23168 48 61752 36 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 2) (BSN.artanhQ 34) 0 2 23168 20045040 48 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep315 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz588 134395 1000 0 1 3254268794313975 1125899906842624 250000000195407 48851750000000000000 3498859636894613361 9007199254740992 6719750005252344753 9770350000000000000000 qz18 (BSN.isNear_log_sfrac 18 1 3254268794313975 1125899906842624 250000000195407 48851750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz352) Bool.false 54597570484265130393600 18889465931478580854784 1000000000781628 195407000000000000000 3254268794313975 1125899906842624 250000000195407 48851750000000000000 (BSN.log_rat_reduce_isNear 18 1 4 36 32 61752 524288 24973259072661432 36028797018963968 195407 1000000000000000 rfl rfl rfl rfl (ep314 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep316 := nat_lit 992276491043847939491904023869250625

noncomputable def ep317 := BSN.sin_dyadic_bound_f 998063505 2147483648 2 1 1048576 391196 ep316 ep58 ep316 ep316 ep59 ep316 469979 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 998063505) qz15 0 1 ep316 ep58 ep316 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 998063505) qz16 0 1 ep316 ep59 ep316 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz353 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 203660435) qz42)

noncomputable def ep318 := @Enclosure.Real.IsNear.cos_image qz52 qz353 Bool.false 203660435 524288 361 524288 Bool.false 469979 1048576 1 195407 (@Enclosure.Real.IsNear.recentre' qz52 Bool.false 3498859636894613361 9007199254740992 6719750005252344753 9770350000000000000000 203660435 524288 361 524288 (ep315 rfl) rfl) (Enclosure.sfrac_false_div 203660435 524288) (BSN.cos_reduce3 qz353 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 35116237755132611133440) qz43) 226375608064910080 72057594037927936 Bool.false 469979 1048576 61 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q3 203660435 524288 226375608064910080 72057594037927936 61 35116237755132611133440 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 469979 1048576 35116237755132611133440 75557863725914323419136 998063505 2147483648 391196 390814 (ep317 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep319 := BSN.cos_dyadic_bound_f 998063505 2147483648 2 1 1048576 391196 ep316 ep62 ep316 ep316 ep63 ep316 937352 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 998063505) qz19 0 1 ep316 ep62 ep316 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 998063505) qz20 0 1 ep316 ep63 ep316 rfl rfl rfl rfl) rfl rfl

noncomputable def ep320 := @Enclosure.Real.IsNear.sin_image qz52 qz353 Bool.false 203660435 524288 361 524288 Bool.true 937352 1048576 1 195407 (@Enclosure.Real.IsNear.recentre' qz52 Bool.false 3498859636894613361 9007199254740992 6719750005252344753 9770350000000000000000 203660435 524288 361 524288 (ep315 rfl) rfl) (Enclosure.sfrac_false_div 203660435 524288) (BSN.sin_reduce3 qz353 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 35116237755132611133440) qz43) 226375608064910080 72057594037927936 Bool.false 937352 1048576 61 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q3 203660435 524288 226375608064910080 72057594037927936 61 35116237755132611133440 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 937352 1048576 35116237755132611133440 75557863725914323419136 998063505 2147483648 391196 390814 (ep319 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz354 := (@Enclosure.Real.IsNear.recentre' qz51 Bool.false 247151 1048576 1 1048576 247151 1048576 1 1048576 (ep313 rfl rfl) rfl)

noncomputable def ep321 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz51 (Real.cos qz52)) (@HMul.hMul Real Real Real qz0 qz51 (@Neg.neg Real Real.instNeg (Real.sin qz52))) Bool.false 116155779829 1099511627776 35220151525813 214852268648824832 Bool.false 28958435519 137438953472 4413934935203 26856533581103104 (@Enclosure.Real.IsNear.mulLit_ff qz51 (Real.cos qz52) 247151 1048576 1 1048576 469979 1048576 71066215 102449545216 116155779829 1099511627776 35220151525813 214852268648824832 qz354 (@Enclosure.Real.IsNear.recentre' (Real.cos qz52) Bool.false 469979 1048576 71066215 102449545216 469979 1048576 71066215 102449545216 (ep318 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz51 (@Neg.neg Real Real.instNeg (Real.sin qz52)) 247151 1048576 1 1048576 117169 131072 71066215 102449545216 28958435519 137438953472 4413934935203 26856533581103104 qz354 (@Enclosure.Real.IsNear.neg (Real.sin qz52) Bool.true 117169 131072 71066215 102449545216 (@Enclosure.Real.IsNear.recentre' (Real.sin qz52) Bool.true 937352 1048576 71066215 102449545216 117169 131072 71066215 102449545216 (ep320 rfl rfl) rfl)) rfl)

noncomputable def ep322 := @ep295 116155779829 1099511627776 35220151525813 214852268648824832 Bool.false 28958435519 137438953472 4413934935203 26856533581103104 Bool.true 410133800380433447256064 5828351851 17179869184 229465552605359 53713067162206208 Bool.false 15543669907111265959936 113095083413 549755813888 458893727955165 107426134324412416 (ep296 (BSN.head_sum_c_succ qz5 17 18 rfl rfl) (ep311 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep312 ep321) rfl rfl

noncomputable abbrev qz53 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 19)))

noncomputable abbrev qz589 := (Real.log (Enclosure.sfrac Bool.false 19 1))

noncomputable abbrev qz54 := (@HMul.hMul Real Real Real qz269 qz279 qz589)

noncomputable def ep323 := @Enclosure.Complex.IsNear.of_eq qz584 (Complex.mk (@HMul.hMul Real Real Real qz0 qz53 (Real.cos qz54)) (@HMul.hMul Real Real Real qz0 qz53 (@Neg.neg Real Real.instNeg (Real.sin qz54)))) Bool.false 250344699561 1099511627776 34394733322153 214852268648824832 Bool.false 30899081873 1099511627776 34216476803729 214852268648824832 (BSN.cpow_neg_s_mk qz12 134395 1000 19 qz13 rfl)

noncomputable abbrev qz355 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 19) qz14)

noncomputable def ep324 := @Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 19)) 4570637 1048576 1 1048576 120279 120280 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 19)) (Real.sqrt qz355) Bool.false 4570637 1048576 1 1048576 (BSN.sqrt_natCast_div_one 19) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz355) Bool.false 4570637 1048576 1 1048576 4570637 1048576 1 1048576 (BSN.sqrt_enclosure 19 1 2285318 2285319 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep325 := BSN.log_dyadic_bound 3 35 3 2 22509375 524288 195407 55368 243 90099 38 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 3) (BSN.artanhQ 35) 0 2 55368 22509375 243 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep326 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz589 134395 1000 0 1 3315143513283831 1125899906842624 250000000195407 48851750000000000000 89107742493556093449 225179981368524800 6719750005252344753 9770350000000000000000 qz18 (BSN.isNear_log_sfrac 19 1 3315143513283831 1125899906842624 250000000195407 48851750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz355) Bool.false 55618878793361701994496 18889465931478580854784 1000000000781628 195407000000000000000 3315143513283831 1125899906842624 250000000195407 48851750000000000000 (BSN.log_rat_reduce_isNear 19 1 4 38 32 90099 524288 24973259072661432 36028797018963968 195407 1000000000000000 rfl rfl rfl rfl (ep325 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep327 := nat_lit 6021639914934146433484621404208171283802571063540295553826938143840820490284865

noncomputable def ep328 := nat_lit 8741084029059970388218098197644283887603400180450055902617909453485255831361

noncomputable def ep329 := nat_lit 15756809450685238802307369613939500712236328232789569217132980428086982298447681

noncomputable def ep330 := BSN.sin_dyadic_bound_f 3109536521 2147483648 3 2 1048576 391196 ep327 ep72 ep328 ep329 ep75 ep328 1040679 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3109536521) qz15 0 2 ep327 ep72 ep328 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3109536521) qz16 0 2 ep329 ep75 ep328 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz356 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 103735065) qz17)

noncomputable def ep331 := @Enclosure.Real.IsNear.cos_image qz54 qz356 Bool.false 103735065 262144 361 524288 Bool.false 1040679 1048576 1 195407 (@Enclosure.Real.IsNear.recentre' qz54 Bool.false 89107742493556093449 225179981368524800 6719750005252344753 9770350000000000000000 103735065 262144 361 524288 (ep326 rfl) rfl) (Enclosure.sfrac_false_div 103735065 262144) (BSN.cos_reduce3 qz356 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 54703544993619021660160) qz287) 226375608064910080 72057594037927936 Bool.false 1040679 1048576 62 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q3 103735065 262144 226375608064910080 72057594037927936 62 54703544993619021660160 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1040679 1048576 54703544993619021660160 37778931862957161709568 3109536521 2147483648 391196 390814 (ep330 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep332 := nat_lit 3349240434531885783219553268203492617173696546491475332527240261890893719416641

noncomputable def ep333 := nat_lit 10030239135537537408882223608215189283745882839113525885776484966765710646587201

noncomputable def ep334 := BSN.cos_dyadic_bound_f 3109536521 2147483648 3 2 1048576 391196 ep332 ep79 ep328 ep333 ep81 ep328 128447 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3109536521) qz19 0 2 ep332 ep79 ep328 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3109536521) qz20 0 2 ep333 ep81 ep328 rfl rfl rfl rfl) rfl rfl

noncomputable def ep335 := @Enclosure.Real.IsNear.sin_image qz54 qz356 Bool.false 103735065 262144 361 524288 Bool.true 128447 1048576 1 195407 (@Enclosure.Real.IsNear.recentre' qz54 Bool.false 89107742493556093449 225179981368524800 6719750005252344753 9770350000000000000000 103735065 262144 361 524288 (ep326 rfl) rfl) (Enclosure.sfrac_false_div 103735065 262144) (BSN.sin_reduce3 qz356 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 54703544993619021660160) qz287) 226375608064910080 72057594037927936 Bool.false 128447 1048576 62 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q3 103735065 262144 226375608064910080 72057594037927936 62 54703544993619021660160 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 128447 1048576 54703544993619021660160 37778931862957161709568 3109536521 2147483648 391196 390814 (ep334 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz357 := (@Enclosure.Real.IsNear.recentre' qz53 Bool.false 240559 1048576 1 1048576 240559 1048576 1 1048576 (ep324 rfl rfl) rfl)

noncomputable def ep336 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz53 (Real.cos qz54)) (@HMul.hMul Real Real Real qz0 qz53 (@Neg.neg Real Real.instNeg (Real.sin qz54))) Bool.false 250344699561 1099511627776 34394733322153 214852268648824832 Bool.false 30899081873 1099511627776 34216476803729 214852268648824832 (@Enclosure.Real.IsNear.mulLit_ff qz53 (Real.cos qz54) 240559 1048576 1 1048576 1040679 1048576 71066215 102449545216 250344699561 1099511627776 34394733322153 214852268648824832 qz357 (@Enclosure.Real.IsNear.recentre' (Real.cos qz54) Bool.false 1040679 1048576 71066215 102449545216 1040679 1048576 71066215 102449545216 (ep331 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz53 (@Neg.neg Real Real.instNeg (Real.sin qz54)) 240559 1048576 1 1048576 128447 1048576 71066215 102449545216 30899081873 1099511627776 34216476803729 214852268648824832 qz357 (@Enclosure.Real.IsNear.neg (Real.sin qz54) Bool.true 128447 1048576 71066215 102449545216 (@Enclosure.Real.IsNear.recentre' (Real.sin qz54) Bool.true 128447 1048576 71066215 102449545216 128447 1048576 71066215 102449545216 (ep335 rfl rfl) rfl)) rfl)

noncomputable def ep337 := @ep293 250344699561 1099511627776 34394733322153 214852268648824832 Bool.false 30899081873 1099511627776 34216476803729 214852268648824832 Bool.true 2107451441578510385152 122669818903 1099511627776 952256943743589 214852268648824832 Bool.false 141336309160373190131712 257089248699 1099511627776 952003932714059 214852268648824832 (ep294 (BSN.head_sum_c_succ qz5 18 19 rfl rfl) (ep322 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep323 ep336) rfl rfl

noncomputable abbrev qz55 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 20)))

noncomputable abbrev qz590 := (Real.log (Enclosure.sfrac Bool.false 20 1))

noncomputable abbrev qz56 := (@HMul.hMul Real Real Real qz269 qz279 qz590)

noncomputable def ep338 := @Enclosure.Complex.IsNear.of_eq qz583 (Complex.mk (@HMul.hMul Real Real Real qz0 qz55 (Real.cos qz56)) (@HMul.hMul Real Real Real qz0 qz55 (@Neg.neg Real Real.instNeg (Real.sin qz56)))) Bool.false 108611433587 549755813888 16753412447811 107426134324412416 Bool.true 57577379985 549755813888 16710880551005 107426134324412416 (BSN.cpow_neg_s_mk qz12 134395 1000 20 qz13 rfl)

noncomputable abbrev qz358 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 20) qz14)

noncomputable def ep339 := @Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 20)) 4689375 1048576 1 1048576 117234 117235 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 20)) (Real.sqrt qz358) Bool.false 4689375 1048576 1 1048576 (BSN.sqrt_natCast_div_one 20) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz358) Bool.false 4689375 1048576 1 1048576 4689375 1048576 1 1048576 (BSN.sqrt_enclosure 20 1 2344687 2344688 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep340 := BSN.log_dyadic_bound 4 36 3 2 25194240 524288 195407 104448 768 116991 40 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 4) (BSN.artanhQ 36) 0 2 104448 25194240 768 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep341 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz590 134395 1000 0 1 3372893643545847 1125899906842624 250000000195407 48851750000000000000 90660008244868821513 225179981368524800 6719750005252344753 9770350000000000000000 qz18 (BSN.isNear_log_sfrac 20 1 3372893643545847 1125899906842624 250000000195407 48851750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz358) Bool.false 56587765202795681021952 18889465931478580854784 1000000000781628 195407000000000000000 3372893643545847 1125899906842624 250000000195407 48851750000000000000 (BSN.log_rat_reduce_isNear 20 1 4 40 32 116991 524288 24973259072661432 36028797018963968 195407 1000000000000000 rfl rfl rfl rfl (ep340 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep342 := nat_lit 1200755506775981493160549362647147536

noncomputable def ep343 := BSN.cos_dyadic_bound_f 1046799838 2147483648 2 1 1048576 391196 ep342 ep62 ep342 ep342 ep63 ep342 926446 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1046799838) qz19 0 1 ep342 ep62 ep342 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1046799838) qz20 0 1 ep342 ep63 ep342 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz359 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 422168561) qz23)

noncomputable def ep344 := @Enclosure.Real.IsNear.cos_image qz56 qz359 Bool.false 422168561 1048576 361 524288 Bool.false 926446 1048576 1 195407 (@Enclosure.Real.IsNear.recentre' qz56 Bool.false 90660008244868821513 225179981368524800 6719750005252344753 9770350000000000000000 422168561 1048576 361 524288 (ep341 rfl) rfl) (Enclosure.sfrac_false_div 422168561 1048576) (BSN.cos_reduce0 qz359 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 73661990047017401843712) qz24) 226375608064910080 72057594037927936 Bool.false 926446 1048576 64 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q0 422168561 1048576 226375608064910080 72057594037927936 64 73661990047017401843712 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 926446 1048576 73661990047017401843712 151115727451828646838272 1046799838 2147483648 391196 390814 (ep343 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep345 := BSN.sin_dyadic_bound_f 1046799838 2147483648 2 1 1048576 391196 ep342 ep58 ep342 ep342 ep59 ep342 491130 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1046799838) qz15 0 1 ep342 ep58 ep342 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1046799838) qz16 0 1 ep342 ep59 ep342 rfl rfl rfl rfl) rfl rfl

noncomputable def ep346 := @Enclosure.Real.IsNear.sin_image qz56 qz359 Bool.false 422168561 1048576 361 524288 Bool.false 491130 1048576 1 195407 (@Enclosure.Real.IsNear.recentre' qz56 Bool.false 90660008244868821513 225179981368524800 6719750005252344753 9770350000000000000000 422168561 1048576 361 524288 (ep341 rfl) rfl) (Enclosure.sfrac_false_div 422168561 1048576) (BSN.sin_reduce0 qz359 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 73661990047017401843712) qz24) 226375608064910080 72057594037927936 Bool.false 491130 1048576 64 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q0 422168561 1048576 226375608064910080 72057594037927936 64 73661990047017401843712 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 491130 1048576 73661990047017401843712 151115727451828646838272 1046799838 2147483648 391196 390814 (ep345 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz360 := (@Enclosure.Real.IsNear.recentre' qz55 Bool.false 234469 1048576 1 1048576 234469 1048576 1 1048576 (ep339 rfl rfl) rfl)

noncomputable def ep347 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz55 (Real.cos qz56)) (@HMul.hMul Real Real Real qz0 qz55 (@Neg.neg Real Real.instNeg (Real.sin qz56))) Bool.false 108611433587 549755813888 16753412447811 107426134324412416 Bool.true 57577379985 549755813888 16710880551005 107426134324412416 (@Enclosure.Real.IsNear.mulLit_ff qz55 (Real.cos qz56) 234469 1048576 1 1048576 463223 524288 71066215 102449545216 108611433587 549755813888 16753412447811 107426134324412416 qz360 (@Enclosure.Real.IsNear.recentre' (Real.cos qz56) Bool.false 926446 1048576 71066215 102449545216 463223 524288 71066215 102449545216 (ep344 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz55 (@Neg.neg Real Real.instNeg (Real.sin qz56)) 234469 1048576 1 1048576 245565 524288 71066215 102449545216 57577379985 549755813888 16710880551005 107426134324412416 qz360 (@Enclosure.Real.IsNear.neg (Real.sin qz56) Bool.false 245565 524288 71066215 102449545216 (@Enclosure.Real.IsNear.recentre' (Real.sin qz56) Bool.false 491130 1048576 71066215 102449545216 245565 524288 71066215 102449545216 (ep346 rfl rfl) rfl)) rfl)

noncomputable def ep348 := @ep291 108611433587 549755813888 16753412447811 107426134324412416 Bool.true 57577379985 549755813888 16710880551005 107426134324412416 Bool.false 51981088007814956187648 94553048271 1099511627776 985763768639211 214852268648824832 Bool.false 78029310369988557668352 141934488729 1099511627776 985425693816069 214852268648824832 (ep292 (BSN.head_sum_c_succ qz5 19 20 rfl rfl) (ep337 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep338 ep347) rfl rfl

noncomputable abbrev qz57 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 21)))

noncomputable abbrev qz591 := (Real.log (Enclosure.sfrac Bool.false 21 1))

noncomputable abbrev qz58 := (@HMul.hMul Real Real Real qz269 qz279 qz591)

noncomputable def ep349 := @Enclosure.Complex.IsNear.of_eq qz582 (Complex.mk (@HMul.hMul Real Real Real qz0 qz57 (Real.cos qz58)) (@HMul.hMul Real Real Real qz0 qz57 (@Neg.neg Real Real.instNeg (Real.sin qz58)))) Bool.false 86840435315 549755813888 16409692068545 107426134324412416 Bool.true 82768847823 549755813888 16402737924229 107426134324412416 (BSN.cpow_neg_s_mk qz12 134395 1000 21 qz13 rfl)

noncomputable abbrev qz361 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 21) qz14)

noncomputable def ep350 := @Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 21)) 4805179 1048576 1 1048576 114408 114410 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 21)) (Real.sqrt qz361) Bool.false 4805179 1048576 1 1048576 (BSN.sqrt_natCast_div_one 21) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz361) Bool.false 4805179 1048576 1 1048576 4805179 1048576 1 1048576 (BSN.sqrt_enclosure 21 1 2402589 2402590 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep351 := BSN.log_dyadic_bound 5 37 4 3 269401272945 524288 195407 1658093375 234375 142571 42 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 5) (BSN.artanhQ 37) 0 3 1658093375 269401272945 234375 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep352 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz591 134395 1000 0 1 3427826275261687 1125899906842624 250000000195407 48851750000000000000 92136542452758884873 225179981368524800 6719750005252344753 9770350000000000000000 qz18 (BSN.isNear_log_sfrac 21 1 3427826275261687 1125899906842624 250000000195407 48851750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz361) Bool.false 57509381830540779323392 18889465931478580854784 1000000000781628 195407000000000000000 3427826275261687 1125899906842624 250000000195407 48851750000000000000 (BSN.log_rat_reduce_isNear 21 1 4 42 32 142571 524288 24973259072661432 36028797018963968 195407 1000000000000000 rfl rfl rfl rfl (ep351 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep353 := nat_lit 255435618394014278666051530715268107967336280064583589192463175019773765509376

noncomputable def ep354 := nat_lit 51089503308895508799661231273720339537659261148255510935895010627307069696

noncomputable def ep355 := nat_lit 766204676175425044980555269683256883222933521671454256555517735038066682388736

noncomputable def ep356 := BSN.cos_dyadic_bound_f 1635089238 2147483648 3 2 1048576 391196 ep353 ep79 ep354 ep355 ep81 ep354 759035 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1635089238) qz19 0 2 ep353 ep79 ep354 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1635089238) qz20 0 2 ep355 ep81 ep354 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz362 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 429044209) qz23)

noncomputable def ep357 := @Enclosure.Real.IsNear.cos_image qz58 qz362 Bool.false 429044209 1048576 361 524288 Bool.false 759035 1048576 1 195407 (@Enclosure.Real.IsNear.recentre' qz58 Bool.false 92136542452758884873 225179981368524800 6719750005252344753 9770350000000000000000 429044209 1048576 361 524288 (ep352 rfl) rfl) (Enclosure.sfrac_false_div 429044209 1048576) (BSN.cos_reduce0 qz362 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 115059176301315068264448) qz24) 226375608064910080 72057594037927936 Bool.false 759035 1048576 65 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q0 429044209 1048576 226375608064910080 72057594037927936 65 115059176301315068264448 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 759035 1048576 115059176301315068264448 151115727451828646838272 1635089238 2147483648 391196 390814 (ep356 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep358 := nat_lit 7147692166629415553601015792165374736

noncomputable def ep359 := BSN.sin_dyadic_bound_f 1635089238 2147483648 2 1 1048576 391196 ep358 ep58 ep358 ep358 ep59 ep358 723447 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1635089238) qz15 0 1 ep358 ep58 ep358 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1635089238) qz16 0 1 ep358 ep59 ep358 rfl rfl rfl rfl) rfl rfl

noncomputable def ep360 := @Enclosure.Real.IsNear.sin_image qz58 qz362 Bool.false 429044209 1048576 361 524288 Bool.false 723447 1048576 1 195407 (@Enclosure.Real.IsNear.recentre' qz58 Bool.false 92136542452758884873 225179981368524800 6719750005252344753 9770350000000000000000 429044209 1048576 361 524288 (ep352 rfl) rfl) (Enclosure.sfrac_false_div 429044209 1048576) (BSN.sin_reduce0 qz362 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 115059176301315068264448) qz24) 226375608064910080 72057594037927936 Bool.false 723447 1048576 65 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q0 429044209 1048576 226375608064910080 72057594037927936 65 115059176301315068264448 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 723447 1048576 115059176301315068264448 151115727451828646838272 1635089238 2147483648 391196 390814 (ep359 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz363 := (@Enclosure.Real.IsNear.recentre' qz57 Bool.false 228818 1048576 2 1048576 114409 524288 1 524288 (ep350 rfl rfl) rfl)

noncomputable def ep361 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz57 (Real.cos qz58)) (@HMul.hMul Real Real Real qz0 qz57 (@Neg.neg Real Real.instNeg (Real.sin qz58))) Bool.false 86840435315 549755813888 16409692068545 107426134324412416 Bool.true 82768847823 549755813888 16402737924229 107426134324412416 (@Enclosure.Real.IsNear.mulLit_ff qz57 (Real.cos qz58) 114409 524288 1 524288 759035 1048576 71066215 102449545216 86840435315 549755813888 16409692068545 107426134324412416 qz363 (@Enclosure.Real.IsNear.recentre' (Real.cos qz58) Bool.false 759035 1048576 71066215 102449545216 759035 1048576 71066215 102449545216 (ep357 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz57 (@Neg.neg Real Real.instNeg (Real.sin qz58)) 114409 524288 1 524288 723447 1048576 71066215 102449545216 82768847823 549755813888 16402737924229 107426134324412416 qz363 (@Enclosure.Real.IsNear.neg (Real.sin qz58) Bool.false 723447 1048576 71066215 102449545216 (@Enclosure.Real.IsNear.recentre' (Real.sin qz58) Bool.false 723447 1048576 71066215 102449545216 723447 1048576 71066215 102449545216 (ep360 rfl rfl) rfl)) rfl)

noncomputable def ep362 := @ep289 86840435315 549755813888 16409692068545 107426134324412416 Bool.true 82768847823 549755813888 16402737924229 107426134324412416 Bool.false 147463156397787041497088 268233918901 1099511627776 1018583152776301 214852268648824832 Bool.true 12976000229022206263296 23603206917 1099511627776 1018231169664527 214852268648824832 (ep290 (BSN.head_sum_c_succ qz5 20 21 rfl rfl) (ep348 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep349 ep361) rfl rfl

noncomputable abbrev qz59 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 22)))

noncomputable abbrev qz592 := (Real.log (Enclosure.sfrac Bool.false 22 1))

noncomputable abbrev qz60 := (@HMul.hMul Real Real Real qz269 qz279 qz592)

noncomputable def ep363 := @Enclosure.Complex.IsNear.of_eq qz581 (Complex.mk (@HMul.hMul Real Real Real qz0 qz59 (Real.cos qz60)) (@HMul.hMul Real Real Real qz0 qz59 (@Neg.neg Real Real.instNeg (Real.sin qz60)))) Bool.false 87317116617 549755813888 15963743154437 107426134324412416 Bool.true 19547153409 137438953472 7977882050203 53713067162206208 (BSN.cpow_neg_s_mk qz12 134395 1000 22 qz13 rfl)

noncomputable abbrev qz364 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 22) qz14)

noncomputable def ep364 := @Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 22)) 4918257 1048576 1 1048576 111778 111779 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 22)) (Real.sqrt qz364) Bool.false 4918257 1048576 1 1048576 (BSN.sqrt_natCast_div_one 22) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz364) Bool.false 4918257 1048576 1 1048576 4918257 1048576 1 1048576 (BSN.sqrt_enclosure 22 1 2459128 2459129 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep365 := BSN.log_dyadic_bound 6 38 4 3 316148320320 524288 195407 2667271104 699840 166961 44 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 6) (BSN.artanhQ 38) 0 3 2667271104 316148320320 699840 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep366 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz592 134395 1000 0 1 3480203401436407 1125899906842624 250000000195407 48851750000000000000 93544387227209183753 225179981368524800 6719750005252344753 9770350000000000000000 qz18 (BSN.isNear_log_sfrac 22 1 3480203401436407 1125899906842624 250000000195407 48851750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz364) Bool.false 58388124189833310502912 18889465931478580854784 1000000000781628 195407000000000000000 3480203401436407 1125899906842624 250000000195407 48851750000000000000 (BSN.log_rat_reduce_isNear 22 1 4 44 32 166961 524288 24973259072661432 36028797018963968 195407 1000000000000000 rfl rfl rfl rfl (ep365 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep367 := nat_lit 216184610066318635276675245678308071237068890812895560794148283021054051266081

noncomputable def ep368 := nat_lit 36596959662404116384293716948474525014522046248566625292689842116751175201

noncomputable def ep369 := nat_lit 648480636279631097597257149601027264661177628346189549131859469378928651447841

noncomputable def ep370 := BSN.cos_dyadic_bound_f 1568305357 2147483648 3 2 1048576 391196 ep367 ep79 ep368 ep369 ep81 ep368 781162 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1568305357) qz19 0 2 ep367 ep79 ep368 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1568305357) qz20 0 2 ep369 ep81 ep368 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz365 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 435599997) qz23)

noncomputable def ep371 := @Enclosure.Real.IsNear.cos_image qz60 qz365 Bool.false 435599997 1048576 361 524288 Bool.false 781162 1048576 1 195407 (@Enclosure.Real.IsNear.recentre' qz60 Bool.false 93544387227209183753 225179981368524800 6719750005252344753 9770350000000000000000 435599997 1048576 361 524288 (ep366 rfl) rfl) (Enclosure.sfrac_false_div 435599997 1048576) (BSN.cos_reduce0 qz365 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 110359678497669475467264) qz24) 226375608064910080 72057594037927936 Bool.false 781162 1048576 66 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q0 435599997 1048576 226375608064910080 72057594037927936 66 110359678497669475467264 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 781162 1048576 110359678497669475467264 151115727451828646838272 1568305357 2147483648 391196 390814 (ep370 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep372 := nat_lit 6049542103531813289787669370426707601

noncomputable def ep373 := BSN.sin_dyadic_bound_f 1568305357 2147483648 2 1 1048576 391196 ep372 ep58 ep372 ep372 ep59 ep372 699496 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1568305357) qz15 0 1 ep372 ep58 ep372 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1568305357) qz16 0 1 ep372 ep59 ep372 rfl rfl rfl rfl) rfl rfl

noncomputable def ep374 := @Enclosure.Real.IsNear.sin_image qz60 qz365 Bool.false 435599997 1048576 361 524288 Bool.false 699496 1048576 1 195407 (@Enclosure.Real.IsNear.recentre' qz60 Bool.false 93544387227209183753 225179981368524800 6719750005252344753 9770350000000000000000 435599997 1048576 361 524288 (ep366 rfl) rfl) (Enclosure.sfrac_false_div 435599997 1048576) (BSN.sin_reduce0 qz365 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 110359678497669475467264) qz24) 226375608064910080 72057594037927936 Bool.false 699496 1048576 66 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q0 435599997 1048576 226375608064910080 72057594037927936 66 110359678497669475467264 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 699496 1048576 110359678497669475467264 151115727451828646838272 1568305357 2147483648 391196 390814 (ep373 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz366 := (@Enclosure.Real.IsNear.recentre' qz59 Bool.false 223557 1048576 1 1048576 223557 1048576 1 1048576 (ep364 rfl rfl) rfl)

noncomputable def ep375 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz59 (Real.cos qz60)) (@HMul.hMul Real Real Real qz0 qz59 (@Neg.neg Real Real.instNeg (Real.sin qz60))) Bool.false 87317116617 549755813888 15963743154437 107426134324412416 Bool.true 19547153409 137438953472 7977882050203 53713067162206208 (@Enclosure.Real.IsNear.mulLit_ff qz59 (Real.cos qz60) 223557 1048576 1 1048576 390581 524288 71066215 102449545216 87317116617 549755813888 15963743154437 107426134324412416 qz366 (@Enclosure.Real.IsNear.recentre' (Real.cos qz60) Bool.false 781162 1048576 71066215 102449545216 390581 524288 71066215 102449545216 (ep371 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz59 (@Neg.neg Real Real.instNeg (Real.sin qz60)) 223557 1048576 1 1048576 87437 131072 71066215 102449545216 19547153409 137438953472 7977882050203 53713067162206208 qz366 (@Enclosure.Real.IsNear.neg (Real.sin qz60) Bool.false 87437 131072 71066215 102449545216 (@Enclosure.Real.IsNear.recentre' (Real.sin qz60) Bool.false 699496 1048576 71066215 102449545216 87437 131072 71066215 102449545216 (ep374 rfl rfl) rfl)) rfl)

noncomputable def ep376 := @ep287 87317116617 549755813888 15963743154437 107426134324412416 Bool.true 19547153409 137438953472 7977882050203 53713067162206208 Bool.false 243469341422051529850880 442868152135 1099511627776 1050510639085175 214852268648824832 Bool.true 24736322520372329054208 179980434189 1099511627776 1050142697865339 214852268648824832 (ep288 (BSN.head_sum_c_succ qz5 21 22 rfl rfl) (ep362 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep363 ep375) rfl rfl

noncomputable abbrev qz61 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 23)))

noncomputable abbrev qz593 := (Real.log (Enclosure.sfrac Bool.false 23 1))

noncomputable abbrev qz62 := (@HMul.hMul Real Real Real qz269 qz279 qz593)

noncomputable def ep377 := @Enclosure.Complex.IsNear.of_eq qz580 (Complex.mk (@HMul.hMul Real Real Real qz0 qz61 (Real.cos qz62)) (@HMul.hMul Real Real Real qz0 qz61 (@Neg.neg Real Real.instNeg (Real.sin qz62)))) Bool.false 209237634069 1099511627776 31263404202001 214852268648824832 Bool.true 93709296585 1099511627776 31160153488085 214852268648824832 (BSN.cpow_neg_s_mk qz12 134395 1000 23 qz13 rfl)

noncomputable abbrev qz367 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 23) qz14)

noncomputable def ep378 := @Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 23)) 5028793 1048576 1 1048576 109321 109322 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 23)) (Real.sqrt qz367) Bool.false 5028793 1048576 1 1048576 (BSN.sqrt_natCast_div_one 23) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz367) Bool.false 5028793 1048576 1 1048576 5028793 1048576 1 1048576 (BSN.sqrt_enclosure 23 1 2514396 2514397 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep379 := BSN.log_dyadic_bound 7 39 4 3 369468094905 524288 195407 4046006391 1764735 190266 46 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 7) (BSN.artanhQ 39) 0 3 4046006391 369468094905 1764735 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep380 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz593 134395 1000 0 1 3530250507853047 1125899906842624 250000000195407 48851750000000000000 94889603400582050313 225179981368524800 6719750005252344753 9770350000000000000000 qz18 (BSN.isNear_log_sfrac 23 1 3530250507853047 1125899906842624 250000000195407 48851750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz367) Bool.false 59227775304360265777152 18889465931478580854784 1000000000781628 195407000000000000000 3530250507853047 1125899906842624 250000000195407 48851750000000000000 (BSN.log_rat_reduce_isNear 23 1 4 46 32 190266 524288 24973259072661432 36028797018963968 195407 1000000000000000 rfl rfl rfl rfl (ep379 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep381 := nat_lit 668577810140014496582725611300255601

noncomputable def ep382 := BSN.cos_dyadic_bound_f 904248901 2147483648 2 1 1048576 391196 ep381 ep62 ep381 ep381 ep63 ep381 956983 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 904248901) qz19 0 1 ep381 ep62 ep381 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 904248901) qz20 0 1 ep381 ep63 ep381 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz368 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 110466037) qz17)

noncomputable def ep383 := @Enclosure.Real.IsNear.cos_image qz62 qz368 Bool.false 110466037 262144 361 524288 Bool.false 956983 1048576 1 195407 (@Enclosure.Real.IsNear.recentre' qz62 Bool.false 94889603400582050313 225179981368524800 6719750005252344753 9770350000000000000000 110466037 262144 361 524288 (ep380 rfl) rfl) (Enclosure.sfrac_false_div 110466037 262144) (BSN.cos_reduce0 qz368 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 15907714897286375931904) qz287) 226375608064910080 72057594037927936 Bool.false 956983 1048576 67 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q0 110466037 262144 226375608064910080 72057594037927936 67 15907714897286375931904 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 956983 1048576 15907714897286375931904 37778931862957161709568 904248901 2147483648 391196 390814 (ep382 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep384 := BSN.sin_dyadic_bound_f 904248901 2147483648 2 1 1048576 391196 ep381 ep58 ep381 ep381 ep59 ep381 428595 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 904248901) qz15 0 1 ep381 ep58 ep381 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 904248901) qz16 0 1 ep381 ep59 ep381 rfl rfl rfl rfl) rfl rfl

noncomputable def ep385 := @Enclosure.Real.IsNear.sin_image qz62 qz368 Bool.false 110466037 262144 361 524288 Bool.false 428595 1048576 1 195407 (@Enclosure.Real.IsNear.recentre' qz62 Bool.false 94889603400582050313 225179981368524800 6719750005252344753 9770350000000000000000 110466037 262144 361 524288 (ep380 rfl) rfl) (Enclosure.sfrac_false_div 110466037 262144) (BSN.sin_reduce0 qz368 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 15907714897286375931904) qz287) 226375608064910080 72057594037927936 Bool.false 428595 1048576 67 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q0 110466037 262144 226375608064910080 72057594037927936 67 15907714897286375931904 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 428595 1048576 15907714897286375931904 37778931862957161709568 904248901 2147483648 391196 390814 (ep384 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz369 := (@Enclosure.Real.IsNear.recentre' qz61 Bool.false 218643 1048576 1 1048576 218643 1048576 1 1048576 (ep378 rfl rfl) rfl)

noncomputable def ep386 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz61 (Real.cos qz62)) (@HMul.hMul Real Real Real qz0 qz61 (@Neg.neg Real Real.instNeg (Real.sin qz62))) Bool.false 209237634069 1099511627776 31263404202001 214852268648824832 Bool.true 93709296585 1099511627776 31160153488085 214852268648824832 (@Enclosure.Real.IsNear.mulLit_ff qz61 (Real.cos qz62) 218643 1048576 1 1048576 956983 1048576 71066215 102449545216 209237634069 1099511627776 31263404202001 214852268648824832 qz369 (@Enclosure.Real.IsNear.recentre' (Real.cos qz62) Bool.false 956983 1048576 71066215 102449545216 956983 1048576 71066215 102449545216 (ep383 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz61 (@Neg.neg Real Real.instNeg (Real.sin qz62)) 218643 1048576 1 1048576 428595 1048576 71066215 102449545216 93709296585 1099511627776 31160153488085 214852268648824832 qz369 (@Enclosure.Real.IsNear.neg (Real.sin qz62) Bool.false 428595 1048576 71066215 102449545216 (@Enclosure.Real.IsNear.recentre' (Real.sin qz62) Bool.false 428595 1048576 71066215 102449545216 428595 1048576 71066215 102449545216 (ep385 rfl rfl) rfl)) rfl)

noncomputable def ep387 := @ep285 209237634069 1099511627776 31263404202001 214852268648824832 Bool.true 93709296585 1099511627776 31160153488085 214852268648824832 Bool.false 716997894471308284002304 163026446551 274877906944 135221755410897 26856533581103104 Bool.true 300925041388895940378624 136844865387 549755813888 67581428209589 13428266790551552 (ep286 (BSN.head_sum_c_succ qz5 22 23 rfl rfl) (ep376 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep377 ep386) rfl rfl

noncomputable abbrev qz594 := (@Nat.cast Real Real.instNatCast 24)

noncomputable abbrev qz63 := (@Inv.inv Real Real.instInv (Real.sqrt qz594))

noncomputable abbrev qz595 := (Real.log (Enclosure.sfrac Bool.false 24 1))

noncomputable abbrev qz64 := (@HMul.hMul Real Real Real qz269 qz279 qz595)

noncomputable def ep388 := @Enclosure.Complex.IsNear.of_eq qz579 (Complex.mk (@HMul.hMul Real Real Real qz0 qz63 (Real.cos qz64)) (@HMul.hMul Real Real Real qz0 qz63 (@Neg.neg Real Real.instNeg (Real.sin qz64)))) Bool.false 111085598883 549755813888 15312428305379 107426134324412416 Bool.false 31803412893 1099511627776 30451060257109 214852268648824832 (BSN.cpow_neg_s_mk qz12 134395 1000 24 qz13 rfl)

noncomputable abbrev qz596 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 24) qz14)

noncomputable def ep389 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz594) 5136953 1048576 1 1048576 107019 107020 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz594) (Real.sqrt qz596) Bool.false 5136953 1048576 1 1048576 (BSN.sqrt_natCast_div_one 24) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz596) Bool.false 5136953 1048576 1 1048576 5136953 1048576 1 1048576 (BSN.sqrt_enclosure 24 1 2568476 2568477 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep390 := BSN.log_dyadic_bound 8 40 4 3 430080000000 524288 195407 5875957760 3932160 212580 48 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 8) (BSN.artanhQ 40) 0 3 5875957760 430080000000 3932160 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep391 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz595 134395 1000 0 1 3578169457974519 1125899906842624 250000000195407 48851750000000000000 96177616860897096201 225179981368524800 6719750005252344753 9770350000000000000000 qz18 (BSN.isNear_log_sfrac 24 1 3578169457974519 1125899906842624 250000000195407 48851750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz596) Bool.false 60031721881041427759104 18889465931478580854784 1000000000781628 195407000000000000000 3578169457974519 1125899906842624 250000000195407 48851750000000000000 (BSN.log_rat_reduce_isNear 24 1 4 48 32 212580 524288 24973259072661432 36028797018963968 195407 1000000000000000 rfl rfl rfl rfl (ep390 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep392 := nat_lit 5705286799517066133649474598534690275436642845691568918903109418018900619198720

noncomputable def ep393 := nat_lit 7847961162749165429342195339838843344067510501038183095570031839893835120896

noncomputable def ep394 := nat_lit 14929711585424055510767784203707306879777002912190523443543887471832530650562816

noncomputable def ep395 := BSN.sin_dyadic_bound_f 3067924062 2147483648 3 2 1048576 391196 ep392 ep72 ep393 ep394 ep75 ep393 1037994 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3067924062) qz15 0 2 ep392 ep72 ep393 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3067924062) qz16 0 2 ep394 ep75 ep393 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz370 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 55982741) qz559)

noncomputable def ep396 := @Enclosure.Real.IsNear.cos_image qz64 qz370 Bool.false 55982741 131072 361 524288 Bool.false 1037994 1048576 1 195407 (@Enclosure.Real.IsNear.recentre' qz64 Bool.false 96177616860897096201 225179981368524800 6719750005252344753 9770350000000000000000 55982741 131072 361 524288 (ep391 rfl) rfl) (Enclosure.sfrac_false_div 55982741 131072) (BSN.cos_reduce3 qz370 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 26985745439992359944192) qz316) 226375608064910080 72057594037927936 Bool.false 1037994 1048576 67 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q3 55982741 131072 226375608064910080 72057594037927936 67 26985745439992359944192 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1037994 1048576 26985745439992359944192 18889465931478580854784 3067924062 2147483648 391196 390814 (ep395 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep397 := nat_lit 3173091760248480814440526863781422972284387141162444147433091913050453159608576

noncomputable def ep398 := nat_lit 9503579358419944112462896200664591230165026402485256076108135675471571808583936

noncomputable def ep399 := BSN.cos_dyadic_bound_f 3067924062 2147483648 3 2 1048576 391196 ep397 ep79 ep393 ep398 ep81 ep393 148587 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3067924062) qz19 0 2 ep397 ep79 ep393 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3067924062) qz20 0 2 ep398 ep81 ep393 rfl rfl rfl rfl) rfl rfl

noncomputable def ep400 := @Enclosure.Real.IsNear.sin_image qz64 qz370 Bool.false 55982741 131072 361 524288 Bool.true 148587 1048576 1 195407 (@Enclosure.Real.IsNear.recentre' qz64 Bool.false 96177616860897096201 225179981368524800 6719750005252344753 9770350000000000000000 55982741 131072 361 524288 (ep391 rfl) rfl) (Enclosure.sfrac_false_div 55982741 131072) (BSN.sin_reduce3 qz370 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 26985745439992359944192) qz316) 226375608064910080 72057594037927936 Bool.false 148587 1048576 67 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q3 55982741 131072 226375608064910080 72057594037927936 67 26985745439992359944192 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 148587 1048576 26985745439992359944192 18889465931478580854784 3067924062 2147483648 391196 390814 (ep399 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz371 := (@Enclosure.Real.IsNear.recentre' qz63 Bool.false 214039 1048576 1 1048576 214039 1048576 1 1048576 (ep389 rfl rfl) rfl)

noncomputable def ep401 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz63 (Real.cos qz64)) (@HMul.hMul Real Real Real qz0 qz63 (@Neg.neg Real Real.instNeg (Real.sin qz64))) Bool.false 111085598883 549755813888 15312428305379 107426134324412416 Bool.false 31803412893 1099511627776 30451060257109 214852268648824832 (@Enclosure.Real.IsNear.mulLit_ff qz63 (Real.cos qz64) 214039 1048576 1 1048576 518997 524288 71066215 102449545216 111085598883 549755813888 15312428305379 107426134324412416 qz371 (@Enclosure.Real.IsNear.recentre' (Real.cos qz64) Bool.false 1037994 1048576 71066215 102449545216 518997 524288 71066215 102449545216 (ep396 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz63 (@Neg.neg Real Real.instNeg (Real.sin qz64)) 214039 1048576 1 1048576 148587 1048576 71066215 102449545216 31803412893 1099511627776 30451060257109 214852268648824832 qz371 (@Enclosure.Real.IsNear.neg (Real.sin qz64) Bool.true 148587 1048576 71066215 102449545216 (@Enclosure.Real.IsNear.recentre' (Real.sin qz64) Bool.true 148587 1048576 71066215 102449545216 148587 1048576 71066215 102449545216 (ep400 rfl rfl) rfl)) rfl)

noncomputable def ep402 := @ep283 111085598883 549755813888 15312428305379 107426134324412416 Bool.false 31803412893 1099511627776 30451060257109 214852268648824832 Bool.false 120159713721493319843840 437138491985 549755813888 556199449948967 107426134324412416 Bool.true 132978409555040642531328 241886317881 1099511627776 1111753911610533 214852268648824832 (ep284 (BSN.head_sum_c_succ qz5 23 24 rfl rfl) (ep387 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep388 ep401) rfl rfl

theorem EMRow46.d8 : Enclosure.Complex.IsNear qz48 Bool.false 437138491985 549755813888 556199449948967 107426134324412416 Bool.true 241886317881 1099511627776 1111753911610533 214852268648824832 := ep282 (BSN.head_sum_c_succ qz5 24 25 rfl rfl) (ep402 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable abbrev qz65 := (BSN.headSumC qz273 33)

noncomputable abbrev qz597 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 32) qz7)

noncomputable def ep403 := @Enclosure.Complex.IsNear.of_eq qz65 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 32) qz597) Bool.false 826398132489 1099511627776 1337293444977907 214852268648824832 Bool.true 26673510891 274877906944 668344013694817 107426134324412416

noncomputable def ep404 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 32) qz597 Bool.false 694061925899 1099511627776 1310807702303877 214852268648824832 Bool.false 35663442895 1099511627776 1310191720426963 214852268648824832 Bool.false

noncomputable abbrev qz598 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 31) qz7)

noncomputable def ep405 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 32) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 31) qz598) Bool.false 694061925899 1099511627776 1310807702303877 214852268648824832 Bool.false 35663442895 1099511627776 1310191720426963 214852268648824832

noncomputable def ep406 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 31) qz598 Bool.false 220628664513 274877906944 641922183189789 107426134324412416 Bool.false 47339391661 549755813888 641681343280661 107426134324412416 Bool.true

noncomputable abbrev qz599 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 30) qz7)

noncomputable def ep407 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 31) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 30) qz599) Bool.false 220628664513 274877906944 641922183189789 107426134324412416 Bool.false 47339391661 549755813888 641681343280661 107426134324412416

noncomputable def ep408 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 30) qz599 Bool.false 441062631495 549755813888 314158391998205 53713067162206208 Bool.true 414310035 4294967296 78496711683299 13428266790551552 Bool.false

noncomputable abbrev qz600 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 29) qz7)

noncomputable def ep409 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 30) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 29) qz600) Bool.false 441062631495 549755813888 314158391998205 53713067162206208 Bool.true 414310035 4294967296 78496711683299 13428266790551552

noncomputable def ep410 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 29) qz600 Bool.false 680500801215 1099511627776 1228755768735545 214852268648824832 Bool.true 4618917615 68719476736 153529956713691 26856533581103104 Bool.false

noncomputable abbrev qz601 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 28) qz7)

noncomputable def ep411 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 29) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 28) qz601) Bool.false 680500801215 1099511627776 1228755768735545 214852268648824832 Bool.true 4618917615 68719476736 153529956713691 26856533581103104

noncomputable def ep412 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 28) qz601 Bool.false 712467267397 1099511627776 1200558715992227 214852268648824832 Bool.false 131412615319 1099511627776 1199871663026157 214852268648824832 Bool.true

noncomputable abbrev qz602 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 27) qz7)

noncomputable def ep413 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 28) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 27) qz602) Bool.false 712467267397 1099511627776 1200558715992227 214852268648824832 Bool.false 131412615319 1099511627776 1199871663026157 214852268648824832

noncomputable def ep414 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 27) qz602 Bool.false 924023249047 1099511627776 1171632103557177 214852268648824832 Bool.false 135803761559 1099511627776 1171145653463237 214852268648824832 Bool.true

noncomputable abbrev qz603 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 26) qz7)

noncomputable def ep415 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 27) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 26) qz603) Bool.false 924023249047 1099511627776 1171632103557177 214852268648824832 Bool.false 135803761559 1099511627776 1171145653463237 214852268648824832

noncomputable def ep416 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 26) qz603 Bool.false 62756945065 68719476736 285581830167675 53713067162206208 Bool.true 64404093951 1099511627776 1141726729635327 214852268648824832 Bool.true

noncomputable abbrev qz604 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 25) qz7)

noncomputable def ep417 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 26) (@HAdd.hAdd Complex Complex Complex qz4 qz48 qz604) Bool.false 62756945065 68719476736 285581830167675 53713067162206208 Bool.true 64404093951 1099511627776 1141726729635327 214852268648824832

noncomputable def ep418 := @Enclosure.Complex.IsNear.addLitP qz48 qz604 Bool.false 437138491985 549755813888 556199449948967 107426134324412416 Bool.true 241886317881 1099511627776 1111753911610533 214852268648824832 Bool.false

noncomputable abbrev qz605 := (@Nat.cast Real Real.instNatCast 25)

noncomputable abbrev qz66 := (@Inv.inv Real Real.instInv (Real.sqrt qz605))

noncomputable abbrev qz606 := (Real.log (Enclosure.sfrac Bool.false 25 1))

noncomputable abbrev qz67 := (@HMul.hMul Real Real Real qz269 qz279 qz606)

noncomputable def ep419 := @Enclosure.Complex.IsNear.of_eq qz604 (Complex.mk (@HMul.hMul Real Real Real qz0 qz66 (Real.cos qz67)) (@HMul.hMul Real Real Real qz0 qz66 (@Neg.neg Real Real.instNeg (Real.sin qz67)))) Bool.false 64917068535 549755813888 14964210386383 107426134324412416 Bool.false 88741111965 549755813888 14986409012397 107426134324412416 (BSN.cpow_neg_s_mk qz12 134395 1000 25 qz13 rfl)

noncomputable abbrev qz607 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 25) qz14)

noncomputable def ep420 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz605) 5242881 1048576 1 1048576 104857 104858 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz605) (Real.sqrt qz607) Bool.false 5242881 1048576 1 1048576 (BSN.sqrt_natCast_div_one 25) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz607) Bool.false 5242881 1048576 1 1048576 5242881 1048576 1 1048576 (BSN.sqrt_enclosure 25 1 2621440 2621441 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep421 := BSN.log_dyadic_bound 9 41 5 4 7545754341519345 524288 195407 124828057765224 4519905705 233982 50 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 9) (BSN.artanhQ 41) 0 4 124828057765224 7545754341519345 4519905705 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep422 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz606 134395 1000 0 1 3624129903009015 1125899906842624 250000000195407 48851750000000000000 19482597532595862837 45035996273704960 6719750005252344753 9770350000000000000000 qz18 (BSN.isNear_log_sfrac 25 1 3624129903009015 1125899906842624 250000000195407 48851750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz607) Bool.false 60802810194841294602240 18889465931478580854784 1000000000781628 195407000000000000000 3624129903009015 1125899906842624 250000000195407 48851750000000000000 (BSN.log_rat_reduce_isNear 25 1 4 50 32 233982 524288 24973259072661432 36028797018963968 195407 1000000000000000 rfl rfl rfl rfl (ep421 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep423 := nat_lit 3383955736501620468042896053046410000

noncomputable def ep424 := BSN.sin_dyadic_bound_f 1356301270 2147483648 2 1 1048576 391196 ep423 ep58 ep423 ep423 ep59 ep423 619098 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1356301270) qz15 0 1 ep423 ep58 ep423 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1356301270) qz16 0 1 ep423 ep59 ep423 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz372 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 113403643) qz17)

noncomputable def ep425 := @Enclosure.Real.IsNear.cos_image qz67 qz372 Bool.false 113403643 262144 361 524288 Bool.false 619098 1048576 1 195407 (@Enclosure.Real.IsNear.recentre' qz67 Bool.false 19482597532595862837 45035996273704960 6719750005252344753 9770350000000000000000 113403643 262144 361 524288 (ep422 rfl) rfl) (Enclosure.sfrac_false_div 113403643 262144) (BSN.cos_reduce3 qz372 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 23860304276074524573696) qz287) 226375608064910080 72057594037927936 Bool.false 619098 1048576 68 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q3 113403643 262144 226375608064910080 72057594037927936 68 23860304276074524573696 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 619098 1048576 23860304276074524573696 37778931862957161709568 1356301270 2147483648 391196 390814 (ep424 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep426 := BSN.cos_dyadic_bound_f 1356301270 2147483648 2 1 1048576 391196 ep423 ep62 ep423 ep423 ep63 ep423 846302 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1356301270) qz19 0 1 ep423 ep62 ep423 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1356301270) qz20 0 1 ep423 ep63 ep423 rfl rfl rfl rfl) rfl rfl

noncomputable def ep427 := @Enclosure.Real.IsNear.sin_image qz67 qz372 Bool.false 113403643 262144 361 524288 Bool.true 846302 1048576 1 195407 (@Enclosure.Real.IsNear.recentre' qz67 Bool.false 19482597532595862837 45035996273704960 6719750005252344753 9770350000000000000000 113403643 262144 361 524288 (ep422 rfl) rfl) (Enclosure.sfrac_false_div 113403643 262144) (BSN.sin_reduce3 qz372 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 23860304276074524573696) qz287) 226375608064910080 72057594037927936 Bool.false 846302 1048576 68 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q3 113403643 262144 226375608064910080 72057594037927936 68 23860304276074524573696 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 846302 1048576 23860304276074524573696 37778931862957161709568 1356301270 2147483648 391196 390814 (ep426 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz373 := (@Enclosure.Real.IsNear.recentre' qz66 Bool.false 209715 1048576 1 1048576 209715 1048576 1 1048576 (ep420 rfl rfl) rfl)

noncomputable def ep428 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz66 (Real.cos qz67)) (@HMul.hMul Real Real Real qz0 qz66 (@Neg.neg Real Real.instNeg (Real.sin qz67))) Bool.false 64917068535 549755813888 14964210386383 107426134324412416 Bool.false 88741111965 549755813888 14986409012397 107426134324412416 (@Enclosure.Real.IsNear.mulLit_ff qz66 (Real.cos qz67) 209715 1048576 1 1048576 309549 524288 71066215 102449545216 64917068535 549755813888 14964210386383 107426134324412416 qz373 (@Enclosure.Real.IsNear.recentre' (Real.cos qz67) Bool.false 619098 1048576 71066215 102449545216 309549 524288 71066215 102449545216 (ep425 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz66 (@Neg.neg Real Real.instNeg (Real.sin qz67)) 209715 1048576 1 1048576 423151 524288 71066215 102449545216 88741111965 549755813888 14986409012397 107426134324412416 qz373 (@Enclosure.Real.IsNear.neg (Real.sin qz67) Bool.true 423151 524288 71066215 102449545216 (@Enclosure.Real.IsNear.recentre' (Real.sin qz67) Bool.true 846302 1048576 71066215 102449545216 423151 524288 71066215 102449545216 (ep427 rfl rfl) rfl)) rfl)

noncomputable def ep429 := @ep418 64917068535 549755813888 14964210386383 107426134324412416 Bool.false 88741111965 549755813888 14986409012397 107426134324412416 Bool.false 276007963290668640501760 62756945065 68719476736 285581830167675 53713067162206208 Bool.true 35406525087751222591488 64404093951 1099511627776 1141726729635327 214852268648824832 EMRow46.d8 (ep419 ep428) rfl rfl

noncomputable abbrev qz608 := (@Nat.cast Real Real.instNatCast 26)

noncomputable abbrev qz68 := (@Inv.inv Real Real.instInv (Real.sqrt qz608))

noncomputable abbrev qz609 := (Real.log (Enclosure.sfrac Bool.false 26 1))

noncomputable abbrev qz69 := (@HMul.hMul Real Real Real qz269 qz279 qz609)

noncomputable def ep430 := @Enclosure.Complex.IsNear.of_eq qz603 (Complex.mk (@HMul.hMul Real Real Real qz0 qz68 (Real.cos qz69)) (@HMul.hMul Real Real Real qz0 qz68 (@Neg.neg Real Real.instNeg (Real.sin qz69)))) Bool.true 80087871993 1099511627776 29304782886477 214852268648824832 Bool.false 100103927755 549755813888 14709461913955 107426134324412416 (BSN.cpow_neg_s_mk qz12 134395 1000 26 qz13 rfl)

noncomputable abbrev qz610 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 26) qz14)

noncomputable def ep431 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz608) 5346709 1048576 1 1048576 102821 102822 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz608) (Real.sqrt qz610) Bool.false 5346709 1048576 1 1048576 (BSN.sqrt_natCast_div_one 26) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz610) Bool.false 5346709 1048576 1 1048576 5346709 1048576 1 1048576 (BSN.sqrt_enclosure 26 1 2673354 2673355 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep432 := BSN.log_dyadic_bound 10 42 5 4 9150106136613120 524288 195407 179034245376000 10500000000 254545 52 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 10) (BSN.artanhQ 42) 0 4 179034245376000 9150106136613120 10500000000 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep433 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz609 134395 1000 0 1 3668288609262839 1125899906842624 250000000195407 48851750000000000000 98599929528375849481 225179981368524800 6719750005252344753 9770350000000000000000 qz18 (BSN.isNear_log_sfrac 26 1 3668288609262839 1125899906842624 250000000195407 48851750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz610) Bool.false 61543670347942250676224 18889465931478580854784 1000000000781628 195407000000000000000 3668288609262839 1125899906842624 250000000195407 48851750000000000000 (BSN.log_rat_reduce_isNear 26 1 4 52 32 254545 524288 24973259072661432 36028797018963968 195407 1000000000000000 rfl rfl rfl rfl (ep432 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep434 := nat_lit 1527028816903968246822274067998872182520161529296331263895564764072570496597121

noncomputable def ep435 := nat_lit 1822216035947627337852170596919286750148988827419189082666186730625562688641

noncomputable def ep436 := nat_lit 4577442018640009485791117862802777974060186610234155413521361918756460364414081

noncomputable def ep437 := BSN.cos_dyadic_bound_f 2556083183 2147483648 3 2 1048576 391196 ep434 ep79 ep435 ep436 ep81 ep435 389451 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2556083183) qz19 0 2 ep434 ep79 ep435 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2556083183) qz20 0 2 ep436 ep81 ep435 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz374 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 459141701) qz23)

noncomputable def ep438 := @Enclosure.Real.IsNear.cos_image qz69 qz374 Bool.false 459141701 1048576 361 524288 Bool.true 389451 1048576 1 195407 (@Enclosure.Real.IsNear.recentre' qz69 Bool.false 98599929528375849481 225179981368524800 6719750005252344753 9770350000000000000000 459141701 1048576 361 524288 (ep433 rfl) rfl) (Enclosure.sfrac_false_div 459141701 1048576) (BSN.cos_reduce2 qz374 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 179868363652001832108032) qz24) 226375608064910080 72057594037927936 Bool.false 389451 1048576 69 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q2 459141701 1048576 226375608064910080 72057594037927936 69 179868363652001832108032 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 389451 1048576 179868363652001832108032 151115727451828646838272 2556083183 2147483648 391196 390814 (ep437 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep439 := nat_lit 2747194097598384742409811585920434499136171561671460923745883625946126443723905

noncomputable def ep440 := nat_lit 7192081905842330547764412544063268652523065251038004684629188051342651679685761

noncomputable def ep441 := BSN.sin_dyadic_bound_f 2556083183 2147483648 3 2 1048576 391196 ep439 ep72 ep435 ep440 ep75 ep435 973570 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2556083183) qz15 0 2 ep439 ep72 ep435 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2556083183) qz16 0 2 ep440 ep75 ep435 rfl rfl rfl rfl) rfl rfl

noncomputable def ep442 := @Enclosure.Real.IsNear.sin_image qz69 qz374 Bool.false 459141701 1048576 361 524288 Bool.true 973570 1048576 1 195407 (@Enclosure.Real.IsNear.recentre' qz69 Bool.false 98599929528375849481 225179981368524800 6719750005252344753 9770350000000000000000 459141701 1048576 361 524288 (ep433 rfl) rfl) (Enclosure.sfrac_false_div 459141701 1048576) (BSN.sin_reduce2 qz374 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 179868363652001832108032) qz24) 226375608064910080 72057594037927936 Bool.false 973570 1048576 69 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q2 459141701 1048576 226375608064910080 72057594037927936 69 179868363652001832108032 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 973570 1048576 179868363652001832108032 151115727451828646838272 2556083183 2147483648 391196 390814 (ep441 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz375 := (@Enclosure.Real.IsNear.recentre' qz68 Bool.false 205643 1048576 1 1048576 205643 1048576 1 1048576 (ep431 rfl rfl) rfl)

noncomputable def ep443 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz68 (Real.cos qz69)) (@HMul.hMul Real Real Real qz0 qz68 (@Neg.neg Real Real.instNeg (Real.sin qz69))) Bool.true 80087871993 1099511627776 29304782886477 214852268648824832 Bool.false 100103927755 549755813888 14709461913955 107426134324412416 (@Enclosure.Real.IsNear.mulLit_ft qz68 (Real.cos qz69) 205643 1048576 1 1048576 389451 1048576 71066215 102449545216 80087871993 1099511627776 29304782886477 214852268648824832 qz375 (@Enclosure.Real.IsNear.recentre' (Real.cos qz69) Bool.true 389451 1048576 71066215 102449545216 389451 1048576 71066215 102449545216 (ep438 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz68 (@Neg.neg Real Real.instNeg (Real.sin qz69)) 205643 1048576 1 1048576 486785 524288 71066215 102449545216 100103927755 549755813888 14709461913955 107426134324412416 qz375 (@Enclosure.Real.IsNear.neg (Real.sin qz69) Bool.true 486785 524288 71066215 102449545216 (@Enclosure.Real.IsNear.recentre' (Real.sin qz69) Bool.true 973570 1048576 71066215 102449545216 486785 524288 71066215 102449545216 (ep442 rfl rfl) rfl)) rfl)

noncomputable def ep444 := @ep416 80087871993 1099511627776 29304782886477 214852268648824832 Bool.false 100103927755 549755813888 14709461913955 107426134324412416 Bool.false 63498394166408450670592 924023249047 1099511627776 1171632103557177 214852268648824832 Bool.false 74658907464919932731392 135803761559 1099511627776 1171145653463237 214852268648824832 (ep417 (BSN.head_sum_c_succ qz5 25 26 rfl rfl) (ep429 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep430 ep443) rfl rfl

noncomputable abbrev qz611 := (@Nat.cast Real Real.instNatCast 27)

noncomputable abbrev qz70 := (@Inv.inv Real Real.instInv (Real.sqrt qz611))

noncomputable abbrev qz612 := (Real.log (Enclosure.sfrac Bool.false 27 1))

noncomputable abbrev qz71 := (@HMul.hMul Real Real Real qz269 qz279 qz612)

noncomputable def ep445 := @Enclosure.Complex.IsNear.of_eq qz602 (Complex.mk (@HMul.hMul Real Real Real qz0 qz70 (Real.cos qz71)) (@HMul.hMul Real Real Real qz0 qz70 (@Neg.neg Real Real.instNeg (Real.sin qz71)))) Bool.true 105777990825 549755813888 14463306217525 107426134324412416 Bool.true 17152915 4294967296 3590751195365 26856533581103104 (BSN.cpow_neg_s_mk qz12 134395 1000 27 qz13 rfl)

noncomputable abbrev qz613 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 27) qz14)

noncomputable def ep446 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz611) 5448561 1048576 1 1048576 100899 100900 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz611) (Real.sqrt qz613) Bool.false 5448561 1048576 1 1048576 (BSN.sqrt_natCast_div_one 27) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz613) Bool.false 5448561 1048576 1 1048576 5448561 1048576 1 1048576 (BSN.sqrt_enclosure 27 1 2724280 2724281 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep447 := BSN.log_dyadic_bound 11 43 5 4 11045349262332945 524288 195407 250863800262504 22507682505 274332 54 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 11) (BSN.artanhQ 43) 0 4 250863800262504 11045349262332945 22507682505 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep448 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz612 134395 1000 0 1 3710780868205815 1125899906842624 250000000195407 48851750000000000000 19948415791300820277 45035996273704960 6719750005252344753 9770350000000000000000 qz18 (BSN.isNear_log_sfrac 27 1 3710780868205815 1125899906842624 250000000195407 48851750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz613) Bool.false 62256572154556490711040 18889465931478580854784 1000000000781628 195407000000000000000 3710780868205815 1125899906842624 250000000195407 48851750000000000000 (BSN.log_rat_reduce_isNear 27 1 4 54 32 274332 524288 24973259072661432 36028797018963968 195407 1000000000000000 rfl rfl rfl rfl (ep447 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep449 := nat_lit 7910837568026247170220456865625778160141930703038303624162239288500157584111425

noncomputable def ep450 := nat_lit 15072522289578490140417748951730464920388863601010744536157614739274981046081

noncomputable def ep451 := nat_lit 20694457165885615509397663054526617285738712728793920667366371522208253227169601

noncomputable def ep452 := BSN.sin_dyadic_bound_f 3328689161 2147483648 3 2 1048576 391196 ep449 ep72 ep450 ep451 ep75 ep450 1048350 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3328689161) qz15 0 2 ep449 ep72 ep450 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3328689161) qz16 0 2 ep451 ep75 ep450 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz376 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 58057531) qz559)

noncomputable def ep453 := @Enclosure.Real.IsNear.cos_image qz71 qz376 Bool.false 58057531 131072 723 1048576 Bool.true 1048350 1048576 1 195407 (@Enclosure.Real.IsNear.recentre' qz71 Bool.false 19948415791300820277 45035996273704960 6719750005252344753 9770350000000000000000 58057531 131072 723 1048576 (ep448 rfl) rfl) (Enclosure.sfrac_false_div 58057531 131072) (BSN.cos_reduce1 qz376 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 29279459505058424553472) qz316) 226375608064910080 72057594037927936 Bool.false 1048350 1048576 70 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q1 58057531 131072 226375608064910080 72057594037927936 70 29279459505058424553472 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1048350 1048576 29279459505058424553472 18889465931478580854784 3328689161 2147483648 391196 390814 (ep452 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep454 := nat_lit 4401608658809949979073772813770645851154578774399506788772869655717543093860161

noncomputable def ep455 := nat_lit 13174680931850692956940482943408476623622958595996498877246293737674079319488321

noncomputable def ep456 := BSN.cos_dyadic_bound_f 3328689161 2147483648 3 2 1048576 391196 ep454 ep79 ep450 ep455 ep81 ep450 21760 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3328689161) qz19 0 2 ep454 ep79 ep450 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3328689161) qz20 0 2 ep455 ep81 ep450 rfl rfl rfl rfl) rfl rfl

noncomputable def ep457 := @Enclosure.Real.IsNear.sin_image qz71 qz376 Bool.false 58057531 131072 723 1048576 Bool.false 21760 1048576 1 195407 (@Enclosure.Real.IsNear.recentre' qz71 Bool.false 19948415791300820277 45035996273704960 6719750005252344753 9770350000000000000000 58057531 131072 723 1048576 (ep448 rfl) rfl) (Enclosure.sfrac_false_div 58057531 131072) (BSN.sin_reduce1 qz376 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 29279459505058424553472) qz316) 226375608064910080 72057594037927936 Bool.false 21760 1048576 70 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q1 58057531 131072 226375608064910080 72057594037927936 70 29279459505058424553472 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 21760 1048576 29279459505058424553472 18889465931478580854784 3328689161 2147483648 391196 390814 (ep456 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz377 := (@Enclosure.Real.IsNear.recentre' qz70 Bool.false 201799 1048576 1 1048576 201799 1048576 1 1048576 (ep446 rfl rfl) rfl)

noncomputable def ep458 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz70 (Real.cos qz71)) (@HMul.hMul Real Real Real qz0 qz70 (@Neg.neg Real Real.instNeg (Real.sin qz71))) Bool.true 105777990825 549755813888 14463306217525 107426134324412416 Bool.true 17152915 4294967296 3590751195365 26856533581103104 (@Enclosure.Real.IsNear.mulLit_ft qz70 (Real.cos qz71) 201799 1048576 1 1048576 524175 524288 142327837 204899090432 105777990825 549755813888 14463306217525 107426134324412416 qz377 (@Enclosure.Real.IsNear.recentre' (Real.cos qz71) Bool.true 1048350 1048576 142327837 204899090432 524175 524288 142327837 204899090432 (ep453 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz70 (@Neg.neg Real Real.instNeg (Real.sin qz71)) 201799 1048576 1 1048576 85 4096 142327837 204899090432 17152915 4294967296 3590751195365 26856533581103104 qz377 (@Enclosure.Real.IsNear.neg (Real.sin qz71) Bool.false 85 4096 142327837 204899090432 (@Enclosure.Real.IsNear.recentre' (Real.sin qz71) Bool.false 21760 1048576 142327837 204899090432 85 4096 142327837 204899090432 (ep457 rfl rfl) rfl)) rfl)

noncomputable def ep459 := @ep414 105777990825 549755813888 14463306217525 107426134324412416 Bool.true 17152915 4294967296 3590751195365 26856533581103104 Bool.false 391683022456397062209536 712467267397 1099511627776 1200558715992227 214852268648824832 Bool.false 564412885076933607424 131412615319 1099511627776 1199871663026157 214852268648824832 (ep415 (BSN.head_sum_c_succ qz5 26 27 rfl rfl) (ep444 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep445 ep458) rfl rfl

noncomputable abbrev qz614 := (@Nat.cast Real Real.instNatCast 28)

noncomputable abbrev qz72 := (@Inv.inv Real Real.instInv (Real.sqrt qz614))

noncomputable abbrev qz615 := (Real.log (Enclosure.sfrac Bool.false 28 1))

noncomputable abbrev qz73 := (@HMul.hMul Real Real Real qz269 qz279 qz615)

noncomputable def ep460 := @Enclosure.Complex.IsNear.of_eq qz601 (Complex.mk (@HMul.hMul Real Real Real qz0 qz72 (Real.cos qz73)) (@HMul.hMul Real Real Real qz0 qz72 (@Neg.neg Real Real.instNeg (Real.sin qz73)))) Bool.true 15983233091 549755813888 14098526371659 107426134324412416 Bool.true 205315297159 1099511627776 28367990683371 214852268648824832 (BSN.cpow_neg_s_mk qz12 134395 1000 28 qz13 rfl)

noncomputable abbrev qz616 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 28) qz14)

noncomputable def ep461 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz614) 5548543 1048576 1 1048576 99081 99082 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz614) (Real.sqrt qz616) Bool.false 5548543 1048576 1 1048576 (BSN.sqrt_natCast_div_one 28) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz616) Bool.false 5548543 1048576 1 1048576 5548543 1048576 1 1048576 (BSN.sqrt_enclosure 28 1 2774271 2774272 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep462 := BSN.log_dyadic_bound 12 44 5 4 13275571325829120 524288 195407 344661139390464 45148078080 293399 56 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 12) (BSN.artanhQ 44) 0 4 344661139390464 13275571325829120 45148078080 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep463 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz615 134395 1000 0 1 3751726938922231 1125899906842624 250000000195407 48851750000000000000 100842668391290647049 225179981368524800 6719750005252344753 9770350000000000000000 qz18 (BSN.isNear_log_sfrac 28 1 3751726938922231 1125899906842624 250000000195407 48851750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz616) Bool.false 62943533227317076688896 18889465931478580854784 1000000000781628 195407000000000000000 3751726938922231 1125899906842624 250000000195407 48851750000000000000 (BSN.log_rat_reduce_isNear 28 1 4 56 32 293399 524288 24973259072661432 36028797018963968 195407 1000000000000000 rfl rfl rfl rfl (ep462 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep464 := nat_lit 12104070391532880420852990555979776

noncomputable def ep465 := BSN.sin_dyadic_bound_f 331690368 2147483648 2 1 1048576 391196 ep464 ep58 ep464 ep464 ep59 ep464 161314 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 331690368) qz15 0 1 ep464 ep58 ep464 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 331690368) qz16 0 1 ep464 ep59 ep464 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz378 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 469585267) qz23)

noncomputable def ep466 := @Enclosure.Real.IsNear.cos_image qz73 qz378 Bool.false 469585267 1048576 361 524288 Bool.true 161314 1048576 1 195407 (@Enclosure.Real.IsNear.recentre' qz73 Bool.false 100842668391290647049 225179981368524800 6719750005252344753 9770350000000000000000 469585267 1048576 361 524288 (ep463 rfl) rfl) (Enclosure.sfrac_false_div 469585267 1048576) (BSN.cos_reduce1 qz378 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 23340634708717573505024) qz24) 226375608064910080 72057594037927936 Bool.false 161314 1048576 71 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q1 469585267 1048576 226375608064910080 72057594037927936 71 23340634708717573505024 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 161314 1048576 23340634708717573505024 151115727451828646838272 331690368 2147483648 391196 390814 (ep465 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep467 := BSN.cos_dyadic_bound_f 331690368 2147483648 2 1 1048576 391196 ep464 ep62 ep464 ep464 ep63 ep464 1036093 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 331690368) qz19 0 1 ep464 ep62 ep464 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 331690368) qz20 0 1 ep464 ep63 ep464 rfl rfl rfl rfl) rfl rfl

noncomputable def ep468 := @Enclosure.Real.IsNear.sin_image qz73 qz378 Bool.false 469585267 1048576 361 524288 Bool.false 1036093 1048576 1 195407 (@Enclosure.Real.IsNear.recentre' qz73 Bool.false 100842668391290647049 225179981368524800 6719750005252344753 9770350000000000000000 469585267 1048576 361 524288 (ep463 rfl) rfl) (Enclosure.sfrac_false_div 469585267 1048576) (BSN.sin_reduce1 qz378 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 23340634708717573505024) qz24) 226375608064910080 72057594037927936 Bool.false 1036093 1048576 71 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q1 469585267 1048576 226375608064910080 72057594037927936 71 23340634708717573505024 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1036093 1048576 23340634708717573505024 151115727451828646838272 331690368 2147483648 391196 390814 (ep467 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz379 := (@Enclosure.Real.IsNear.recentre' qz72 Bool.false 198163 1048576 1 1048576 198163 1048576 1 1048576 (ep461 rfl rfl) rfl)

noncomputable def ep469 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz72 (Real.cos qz73)) (@HMul.hMul Real Real Real qz0 qz72 (@Neg.neg Real Real.instNeg (Real.sin qz73))) Bool.true 15983233091 549755813888 14098526371659 107426134324412416 Bool.true 205315297159 1099511627776 28367990683371 214852268648824832 (@Enclosure.Real.IsNear.mulLit_ft qz72 (Real.cos qz73) 198163 1048576 1 1048576 80657 524288 71066215 102449545216 15983233091 549755813888 14098526371659 107426134324412416 qz379 (@Enclosure.Real.IsNear.recentre' (Real.cos qz73) Bool.true 161314 1048576 71066215 102449545216 80657 524288 71066215 102449545216 (ep466 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz72 (@Neg.neg Real Real.instNeg (Real.sin qz73)) 198163 1048576 1 1048576 1036093 1048576 71066215 102449545216 205315297159 1099511627776 28367990683371 214852268648824832 qz379 (@Enclosure.Real.IsNear.neg (Real.sin qz73) Bool.false 1036093 1048576 71066215 102449545216 (@Enclosure.Real.IsNear.recentre' (Real.sin qz73) Bool.false 1036093 1048576 71066215 102449545216 1036093 1048576 71066215 102449545216 (ep468 rfl rfl) rfl)) rfl)

noncomputable def ep470 := @ep412 15983233091 549755813888 14098526371659 107426134324412416 Bool.true 205315297159 1099511627776 28367990683371 214852268648824832 Bool.false 374109271823388424273920 680500801215 1099511627776 1228755768735545 214852268648824832 Bool.true 81256858006910234787840 4618917615 68719476736 153529956713691 26856533581103104 (ep413 (BSN.head_sum_c_succ qz5 27 28 rfl rfl) (ep459 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep460 ep469) rfl rfl

noncomputable abbrev qz617 := (@Nat.cast Real Real.instNatCast 29)

noncomputable abbrev qz74 := (@Inv.inv Real Real.instInv (Real.sqrt qz617))

noncomputable abbrev qz618 := (Real.log (Enclosure.sfrac Bool.false 29 1))

noncomputable abbrev qz75 := (@HMul.hMul Real Real Real qz269 qz279 qz618)

noncomputable def ep471 := @Enclosure.Complex.IsNear.of_eq qz600 (Complex.mk (@HMul.hMul Real Real Real qz0 qz74 (Real.cos qz75)) (@HMul.hMul Real Real Real qz0 qz74 (@Neg.neg Real Real.instNeg (Real.sin qz75)))) Bool.false 201624461775 1099511627776 27877799257275 214852268648824832 Bool.true 2010042945 68719476736 3463466652907 26856533581103104 (BSN.cpow_neg_s_mk qz12 134395 1000 29 qz13 rfl)

noncomputable abbrev qz619 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 29) qz14)

noncomputable def ep472 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz617) 5646755 1048576 1 1048576 97357 97358 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz617) (Real.sqrt qz619) Bool.false 5646755 1048576 1 1048576 (BSN.sqrt_natCast_div_one 29) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz619) Bool.false 5646755 1048576 1 1048576 5646755 1048576 1 1048576 (BSN.sqrt_enclosure 29 1 2823377 2823378 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep473 := BSN.log_dyadic_bound 13 45 6 5 353956287581982421875 524288 195407 10371179520995104305 130276274797305 311797 58 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 13) (BSN.artanhQ 45) 0 5 10371179520995104305 353956287581982421875 130276274797305 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep474 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz618 134395 1000 0 1 3791236343078135 1125899906842624 250000000195407 48851750000000000000 20380928333119438133 45035996273704960 6719750005252344753 9770350000000000000000 qz18 (BSN.isNear_log_sfrac 29 1 3791236343078135 1125899906842624 250000000195407 48851750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz619) Bool.false 63606391034871975772160 18889465931478580854784 1000000000781628 195407000000000000000 3791236343078135 1125899906842624 250000000195407 48851750000000000000 (BSN.log_rat_reduce_isNear 29 1 4 58 32 311797 524288 24973259072661432 36028797018963968 195407 1000000000000000 rfl rfl rfl rfl (ep473 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep475 := nat_lit 13313065735614842383659819577370896

noncomputable def ep476 := BSN.cos_dyadic_bound_f 339679642 2147483648 2 1 1048576 391196 ep475 ep62 ep475 ep475 ep63 ep475 1035485 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 339679642) qz19 0 1 ep475 ep62 ep475 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 339679642) qz20 0 1 ep475 ep63 ep475 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz380 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 237265233) qz42)

noncomputable def ep477 := @Enclosure.Real.IsNear.cos_image qz75 qz380 Bool.false 237265233 524288 361 524288 Bool.false 1035485 1048576 1 195407 (@Enclosure.Real.IsNear.recentre' qz75 Bool.false 20380928333119438133 45035996273704960 6719750005252344753 9770350000000000000000 237265233 524288 361 524288 (ep474 rfl) rfl) (Enclosure.sfrac_false_div 237265233 524288) (BSN.cos_reduce0 qz380 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 11951414929719249862656) qz43) 226375608064910080 72057594037927936 Bool.false 1035485 1048576 72 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q0 237265233 524288 226375608064910080 72057594037927936 72 11951414929719249862656 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1035485 1048576 11951414929719249862656 75557863725914323419136 339679642 2147483648 391196 390814 (ep476 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep478 := BSN.sin_dyadic_bound_f 339679642 2147483648 2 1 1048576 391196 ep475 ep58 ep475 ep475 ep59 ep475 165168 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 339679642) qz15 0 1 ep475 ep58 ep475 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 339679642) qz16 0 1 ep475 ep59 ep475 rfl rfl rfl rfl) rfl rfl

noncomputable def ep479 := @Enclosure.Real.IsNear.sin_image qz75 qz380 Bool.false 237265233 524288 361 524288 Bool.false 165168 1048576 1 195407 (@Enclosure.Real.IsNear.recentre' qz75 Bool.false 20380928333119438133 45035996273704960 6719750005252344753 9770350000000000000000 237265233 524288 361 524288 (ep474 rfl) rfl) (Enclosure.sfrac_false_div 237265233 524288) (BSN.sin_reduce0 qz380 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 11951414929719249862656) qz43) 226375608064910080 72057594037927936 Bool.false 165168 1048576 72 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q0 237265233 524288 226375608064910080 72057594037927936 72 11951414929719249862656 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 165168 1048576 11951414929719249862656 75557863725914323419136 339679642 2147483648 391196 390814 (ep478 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz381 := (@Enclosure.Real.IsNear.recentre' qz74 Bool.false 194715 1048576 1 1048576 194715 1048576 1 1048576 (ep472 rfl rfl) rfl)

noncomputable def ep480 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz74 (Real.cos qz75)) (@HMul.hMul Real Real Real qz0 qz74 (@Neg.neg Real Real.instNeg (Real.sin qz75))) Bool.false 201624461775 1099511627776 27877799257275 214852268648824832 Bool.true 2010042945 68719476736 3463466652907 26856533581103104 (@Enclosure.Real.IsNear.mulLit_ff qz74 (Real.cos qz75) 194715 1048576 1 1048576 1035485 1048576 71066215 102449545216 201624461775 1099511627776 27877799257275 214852268648824832 qz381 (@Enclosure.Real.IsNear.recentre' (Real.cos qz75) Bool.false 1035485 1048576 71066215 102449545216 1035485 1048576 71066215 102449545216 (ep477 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz74 (@Neg.neg Real Real.instNeg (Real.sin qz75)) 194715 1048576 1 1048576 10323 65536 71066215 102449545216 2010042945 68719476736 3463466652907 26856533581103104 qz381 (@Enclosure.Real.IsNear.neg (Real.sin qz75) Bool.false 10323 65536 71066215 102449545216 (@Enclosure.Real.IsNear.recentre' (Real.sin qz75) Bool.false 165168 1048576 71066215 102449545216 10323 65536 71066215 102449545216 (ep479 rfl rfl) rfl)) rfl)

noncomputable def ep481 := @ep410 201624461775 1099511627776 27877799257275 214852268648824832 Bool.true 2010042945 68719476736 3463466652907 26856533581103104 Bool.false 969906983812466988810240 441062631495 549755813888 314158391998205 53713067162206208 Bool.true 455538700986781532160 414310035 4294967296 78496711683299 13428266790551552 (ep411 (BSN.head_sum_c_succ qz5 28 29 rfl rfl) (ep470 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep471 ep480) rfl rfl

noncomputable abbrev qz620 := (@Nat.cast Real Real.instNatCast 30)

noncomputable abbrev qz76 := (@Inv.inv Real Real.instInv (Real.sqrt qz620))

noncomputable abbrev qz621 := (Real.log (Enclosure.sfrac Bool.false 30 1))

noncomputable abbrev qz77 := (@HMul.hMul Real Real Real qz269 qz279 qz621)

noncomputable def ep482 := @Enclosure.Complex.IsNear.of_eq qz599 (Complex.mk (@HMul.hMul Real Real Real qz0 qz76 (Real.cos qz77)) (@HMul.hMul Real Real Real qz0 qz76 (@Neg.neg Real Real.instNeg (Real.sin qz77)))) Bool.false 194697531 549755813888 13605399193379 107426134324412416 Bool.false 100371076141 549755813888 13707649814269 107426134324412416 (BSN.cpow_neg_s_mk qz12 134395 1000 30 qz13 rfl)

noncomputable abbrev qz622 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 30) qz14)

noncomputable def ep483 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz620) 5743287 1048576 1 1048576 95721 95722 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz620) (Real.sqrt qz622) Bool.false 5743287 1048576 1 1048576 (BSN.sqrt_natCast_div_one 30) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz622) Bool.false 5743287 1048576 1 1048576 5743287 1048576 1 1048576 (BSN.sqrt_enclosure 30 1 2871643 2871644 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep484 := BSN.log_dyadic_bound 14 46 6 5 440963670083462507520 524288 195407 14425761949190022144 273345648952320 329571 60 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 14) (BSN.artanhQ 46) 0 5 14425761949190022144 440963670083462507520 273345648952320 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep485 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz621 134395 1000 0 1 3829405717437687 1125899906842624 250000000195407 48851750000000000000 102930596279007588873 225179981368524800 6719750005252344753 9770350000000000000000 qz18 (BSN.isNear_log_sfrac 30 1 3829405717437687 1125899906842624 250000000195407 48851750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz622) Bool.false 64246766873087041339392 18889465931478580854784 1000000000781628 195407000000000000000 3829405717437687 1125899906842624 250000000195407 48851750000000000000 (BSN.log_rat_reduce_isNear 30 1 4 60 32 329571 524288 24973259072661432 36028797018963968 195407 1000000000000000 rfl rfl rfl rfl (ep484 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep486 := BSN.sin_dyadic_bound_f 4166068 2147483648 1 0 1048576 391196 0 1 1 0 1 1 2034 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 4166068) qz15 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 4166068) qz16 0 0 rfl) rfl rfl

noncomputable abbrev qz382 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 479307939) qz23)

noncomputable def ep487 := @Enclosure.Real.IsNear.cos_image qz77 qz382 Bool.false 479307939 1048576 361 524288 Bool.false 2034 1048576 1 195407 (@Enclosure.Real.IsNear.recentre' qz77 Bool.false 102930596279007588873 225179981368524800 6719750005252344753 9770350000000000000000 479307939 1048576 361 524288 (ep485 rfl) rfl) (Enclosure.sfrac_false_div 479307939 1048576) (BSN.cos_reduce3 qz382 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 293160974948423958528) qz24) 226375608064910080 72057594037927936 Bool.false 2034 1048576 72 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q3 479307939 1048576 226375608064910080 72057594037927936 72 293160974948423958528 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 2034 1048576 293160974948423958528 151115727451828646838272 4166068 2147483648 391196 390814 (ep486 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep488 := BSN.cos_dyadic_bound_f 4166068 2147483648 1 0 1048576 391196 0 1 1 0 1 1 1048574 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 4166068) qz19 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 4166068) qz20 0 0 rfl) rfl rfl

noncomputable def ep489 := @Enclosure.Real.IsNear.sin_image qz77 qz382 Bool.false 479307939 1048576 361 524288 Bool.true 1048574 1048576 1 195407 (@Enclosure.Real.IsNear.recentre' qz77 Bool.false 102930596279007588873 225179981368524800 6719750005252344753 9770350000000000000000 479307939 1048576 361 524288 (ep485 rfl) rfl) (Enclosure.sfrac_false_div 479307939 1048576) (BSN.sin_reduce3 qz382 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 293160974948423958528) qz24) 226375608064910080 72057594037927936 Bool.false 1048574 1048576 72 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q3 479307939 1048576 226375608064910080 72057594037927936 72 293160974948423958528 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1048574 1048576 293160974948423958528 151115727451828646838272 4166068 2147483648 391196 390814 (ep488 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz383 := (@Enclosure.Real.IsNear.recentre' qz76 Bool.false 191443 1048576 1 1048576 191443 1048576 1 1048576 (ep483 rfl rfl) rfl)

noncomputable def ep490 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz76 (Real.cos qz77)) (@HMul.hMul Real Real Real qz0 qz76 (@Neg.neg Real Real.instNeg (Real.sin qz77))) Bool.false 194697531 549755813888 13605399193379 107426134324412416 Bool.false 100371076141 549755813888 13707649814269 107426134324412416 (@Enclosure.Real.IsNear.mulLit_ff qz76 (Real.cos qz77) 191443 1048576 1 1048576 1017 524288 71066215 102449545216 194697531 549755813888 13605399193379 107426134324412416 qz383 (@Enclosure.Real.IsNear.recentre' (Real.cos qz77) Bool.false 2034 1048576 71066215 102449545216 1017 524288 71066215 102449545216 (ep487 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz76 (@Neg.neg Real Real.instNeg (Real.sin qz77)) 191443 1048576 1 1048576 524287 524288 71066215 102449545216 100371076141 549755813888 13707649814269 107426134324412416 qz383 (@Enclosure.Real.IsNear.neg (Real.sin qz77) Bool.true 524287 524288 71066215 102449545216 (@Enclosure.Real.IsNear.recentre' (Real.sin qz77) Bool.true 1048574 1048576 71066215 102449545216 524287 524288 71066215 102449545216 (ep489 rfl rfl) rfl)) rfl)

noncomputable def ep491 := @ep408 194697531 549755813888 13605399193379 107426134324412416 Bool.false 100371076141 549755813888 13707649814269 107426134324412416 Bool.false 242583782052733636313088 220628664513 274877906944 641922183189789 107426134324412416 Bool.false 203321138996530118656 47339391661 549755813888 641681343280661 107426134324412416 (ep409 (BSN.head_sum_c_succ qz5 29 30 rfl rfl) (ep481 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep482 ep490) rfl rfl

noncomputable abbrev qz623 := (Real.log (Enclosure.sfrac Bool.false 31 1))

noncomputable abbrev qz78 := (@HMul.hMul Real Real Real qz269 qz279 qz623)

noncomputable abbrev qz384 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 31)))

noncomputable def ep492 := @Enclosure.Complex.IsNear.of_eq qz598 (Complex.mk (@HMul.hMul Real Real Real qz0 qz384 (Real.cos qz78)) (@HMul.hMul Real Real Real qz0 qz384 (@Neg.neg Real Real.instNeg (Real.sin qz78)))) Bool.true 188452732153 1099511627776 26963335924299 214852268648824832 Bool.true 59015340427 1099511627776 26829033865641 214852268648824832 (BSN.cpow_neg_s_mk qz12 134395 1000 31 qz13 rfl)

noncomputable abbrev qz385 := (Real.sqrt (@Nat.cast Real Real.instNatCast 31))

noncomputable abbrev qz386 := (@Nat.cast Real Real.instNatCast 31)

noncomputable abbrev qz624 := (@HDiv.hDiv Real Real Real qz1 qz386 qz14)

noncomputable def ep493 := @Enclosure.Real.IsNear.inv_image qz385 5838225 1048576 1 1048576 94164 94165 524288 (@Enclosure.Real.IsNear.of_eq qz385 (Real.sqrt qz624) Bool.false 5838225 1048576 1 1048576 (BSN.sqrt_natCast_div_one 31) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz624) Bool.false 5838225 1048576 1 1048576 5838225 1048576 1 1048576 (BSN.sqrt_enclosure 31 1 2919112 2919113 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep494 := BSN.log_dyadic_bound 15 47 6 5 546767979591453359355 524288 195407 19788004106328479625 544934619140625 346763 62 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 15) (BSN.artanhQ 47) 0 5 19788004106328479625 546767979591453359355 544934619140625 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep495 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz623 134395 1000 0 1 3866325256314103 1125899906842624 250000000195407 48851750000000000000 103922956564466774537 225179981368524800 6719750005252344753 9770350000000000000000 qz18 (BSN.isNear_log_sfrac 31 1 3866325256314103 1125899906842624 250000000195407 48851750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz624) Bool.false 64866173951437069877248 18889465931478580854784 1000000000781628 195407000000000000000 3866325256314103 1125899906842624 250000000195407 48851750000000000000 (BSN.log_rat_reduce_isNear 31 1 4 62 32 346763 524288 24973259072661432 36028797018963968 195407 1000000000000000 rfl rfl rfl rfl (ep494 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep496 := nat_lit 3531229889242360801629603332998414993536330495945770849651021576194556491626625

noncomputable def ep497 := nat_lit 3009600758332819345884864574784647738966626876434032698517842879093372516481

noncomputable def ep498 := nat_lit 9243586546787929915803242758065245077208252950629459029478884763467211065424001

noncomputable def ep499 := BSN.sin_dyadic_bound_f 2721533039 2147483648 3 2 1048576 391196 ep496 ep72 ep497 ep498 ep75 ep497 1000657 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2721533039) qz15 0 2 ep496 ep72 ep497 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2721533039) qz16 0 2 ep498 ep75 ep497 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz387 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 483928977) qz23)

noncomputable def ep500 := @Enclosure.Real.IsNear.cos_image qz78 qz387 Bool.false 483928977 1048576 361 524288 Bool.true 1000657 1048576 1 195407 (@Enclosure.Real.IsNear.recentre' qz78 Bool.false 103922956564466774537 225179981368524800 6719750005252344753 9770350000000000000000 483928977 1048576 361 524288 (ep495 rfl) rfl) (Enclosure.sfrac_false_div 483928977 1048576) (BSN.cos_reduce1 qz387 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 191510862246082986901504) qz24) 226375608064910080 72057594037927936 Bool.false 1000657 1048576 73 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q1 483928977 1048576 226375608064910080 72057594037927936 73 191510862246082986901504 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1000657 1048576 191510862246082986901504 151115727451828646838272 2721533039 2147483648 391196 390814 (ep499 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep501 := nat_lit 1963131983249459476170172902587912617626390998581621153227686583609906216466561

noncomputable def ep502 := nat_lit 5883376748231712789818748978614168557401239741991995394286024065071531904366721

noncomputable def ep503 := BSN.cos_dyadic_bound_f 2721533039 2147483648 3 2 1048576 391196 ep501 ep79 ep497 ep502 ep81 ep497 313363 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2721533039) qz19 0 2 ep501 ep79 ep497 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2721533039) qz20 0 2 ep502 ep81 ep497 rfl rfl rfl rfl) rfl rfl

noncomputable def ep504 := @Enclosure.Real.IsNear.sin_image qz78 qz387 Bool.false 483928977 1048576 361 524288 Bool.false 313363 1048576 1 195407 (@Enclosure.Real.IsNear.recentre' qz78 Bool.false 103922956564466774537 225179981368524800 6719750005252344753 9770350000000000000000 483928977 1048576 361 524288 (ep495 rfl) rfl) (Enclosure.sfrac_false_div 483928977 1048576) (BSN.sin_reduce1 qz387 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 191510862246082986901504) qz24) 226375608064910080 72057594037927936 Bool.false 313363 1048576 73 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q1 483928977 1048576 226375608064910080 72057594037927936 73 191510862246082986901504 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 313363 1048576 191510862246082986901504 151115727451828646838272 2721533039 2147483648 391196 390814 (ep503 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz388 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 31))) Bool.false 188329 1048576 1 1048576 188329 1048576 1 1048576 (ep493 rfl rfl) rfl)

noncomputable def ep505 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz384 (Real.cos qz78)) (@HMul.hMul Real Real Real qz0 qz384 (@Neg.neg Real Real.instNeg (Real.sin qz78))) Bool.true 188452732153 1099511627776 26963335924299 214852268648824832 Bool.true 59015340427 1099511627776 26829033865641 214852268648824832 (@Enclosure.Real.IsNear.mulLit_ft qz384 (Real.cos qz78) 188329 1048576 1 1048576 1000657 1048576 71066215 102449545216 188452732153 1099511627776 26963335924299 214852268648824832 qz388 (@Enclosure.Real.IsNear.recentre' (Real.cos qz78) Bool.true 1000657 1048576 71066215 102449545216 1000657 1048576 71066215 102449545216 (ep500 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz384 (@Neg.neg Real Real.instNeg (Real.sin qz78)) 188329 1048576 1 1048576 313363 1048576 71066215 102449545216 59015340427 1099511627776 26829033865641 214852268648824832 qz388 (@Enclosure.Real.IsNear.neg (Real.sin qz78) Bool.false 313363 1048576 71066215 102449545216 (@Enclosure.Real.IsNear.recentre' (Real.sin qz78) Bool.false 313363 1048576 71066215 102449545216 313363 1048576 71066215 102449545216 (ep504 rfl rfl) rfl)) rfl)

noncomputable def ep506 := @ep406 188452732153 1099511627776 26963335924299 214852268648824832 Bool.true 59015340427 1099511627776 26829033865641 214852268648824832 Bool.false 190782289480638745542656 694061925899 1099511627776 1310807702303877 214852268648824832 Bool.false 19606185074788935925760 35663442895 1099511627776 1310191720426963 214852268648824832 (ep407 (BSN.head_sum_c_succ qz5 30 31 rfl rfl) (ep491 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep492 ep505) rfl rfl

noncomputable abbrev qz625 := (Real.log (Enclosure.sfrac Bool.false 32 1))

noncomputable abbrev qz79 := (@HMul.hMul Real Real Real qz269 qz279 qz625)

noncomputable abbrev qz389 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 32)))

noncomputable def ep507 := @Enclosure.Complex.IsNear.of_eq qz597 (Complex.mk (@HMul.hMul Real Real Real qz0 qz389 (Real.cos qz79)) (@HMul.hMul Real Real Real qz0 qz389 (@Neg.neg Real Real.instNeg (Real.sin qz79)))) Bool.false 66168103295 549755813888 13242871337015 107426134324412416 Bool.true 142357486459 1099511627776 26496306962671 214852268648824832 (BSN.cpow_neg_s_mk qz12 134395 1000 32 qz13 rfl)

noncomputable abbrev qz390 := (Real.sqrt (@Nat.cast Real Real.instNatCast 32))

noncomputable abbrev qz391 := (@Nat.cast Real Real.instNatCast 32)

noncomputable abbrev qz626 := (@HDiv.hDiv Real Real Real qz1 qz391 qz14)

noncomputable def ep508 := @Enclosure.Real.IsNear.inv_image qz390 5931641 1048576 1 1048576 92681 92682 524288 (@Enclosure.Real.IsNear.of_eq qz390 (Real.sqrt qz626) Bool.false 5931641 1048576 1 1048576 (BSN.sqrt_natCast_div_one 32) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz626) Bool.false 5931641 1048576 1 1048576 5931641 1048576 1 1048576 (BSN.sqrt_enclosure 32 1 2965820 2965821 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep509 := BSN.log_dyadic_bound 0 64 1 0 1 524288 195407 0 1 0 64 64 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 0) (BSN.artanhQ 64) 0 0 rfl) rfl rfl rfl

noncomputable def ep510 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz625 134395 1000 0 1 15608286920413395 4503599627370496 200000000195407 39081400000000000000 83907028826758328841 180143985094819840 5375800005252344753 7816280000000000000000 qz18 (BSN.isNear_log_sfrac 32 1 15608286920413395 4503599627370496 200000000195407 39081400000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz626) Bool.false 65465900263437584302080 18889465931478580854784 1000000000977035 195407000000000000000 15608286920413395 4503599627370496 200000000195407 39081400000000000000 (BSN.log_rat_reduce_isNear 32 1 5 64 64 0 524288 24973259072661432 36028797018963968 195407 1000000000000000 rfl rfl rfl rfl (ep509 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep511 := nat_lit 346789038638298243478378924257900482697056079941561285272135498441947793021761

noncomputable def ep512 := nat_lit 94153697608168481417722555938128513018694193893433986872688532506902223681

noncomputable def ep513 := nat_lit 1040178808519678393472301327661825191065130851436896987842661118260829574617921

noncomputable def ep514 := BSN.cos_dyadic_bound_f 1764938889 2147483648 3 2 1048576 391196 ep511 ep79 ep512 ep513 ep81 ep512 713930 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1764938889) qz19 0 2 ep511 ep79 ep512 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1764938889) qz20 0 2 ep513 ep81 ep512 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz392 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 122100797) qz17)

noncomputable def ep515 := @Enclosure.Real.IsNear.cos_image qz79 qz392 Bool.false 122100797 262144 361 524288 Bool.false 713930 1048576 1 195407 (@Enclosure.Real.IsNear.recentre' qz79 Bool.false 83907028826758328841 180143985094819840 5375800005252344753 7816280000000000000000 122100797 262144 361 524288 (ep510 rfl) rfl) (Enclosure.sfrac_false_div 122100797 262144) (BSN.cos_reduce0 qz392 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 31049133298833176920064) qz287) 226375608064910080 72057594037927936 Bool.false 713930 1048576 74 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q0 122100797 262144 226375608064910080 72057594037927936 74 31049133298833176920064 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 713930 1048576 31049133298833176920064 37778931862957161709568 1764938889 2147483648 391196 390814 (ep514 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep516 := nat_lit 9703282826351527171985524921639771041

noncomputable def ep517 := BSN.sin_dyadic_bound_f 1764938889 2147483648 2 1 1048576 391196 ep516 ep58 ep516 ep516 ep59 ep516 767993 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1764938889) qz15 0 1 ep516 ep58 ep516 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1764938889) qz16 0 1 ep516 ep59 ep516 rfl rfl rfl rfl) rfl rfl

noncomputable def ep518 := @Enclosure.Real.IsNear.sin_image qz79 qz392 Bool.false 122100797 262144 361 524288 Bool.false 767993 1048576 1 195407 (@Enclosure.Real.IsNear.recentre' qz79 Bool.false 83907028826758328841 180143985094819840 5375800005252344753 7816280000000000000000 122100797 262144 361 524288 (ep510 rfl) rfl) (Enclosure.sfrac_false_div 122100797 262144) (BSN.sin_reduce0 qz392 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 31049133298833176920064) qz287) 226375608064910080 72057594037927936 Bool.false 767993 1048576 74 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q0 122100797 262144 226375608064910080 72057594037927936 74 31049133298833176920064 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 767993 1048576 31049133298833176920064 37778931862957161709568 1764938889 2147483648 391196 390814 (ep517 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz393 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 32))) Bool.false 185363 1048576 1 1048576 185363 1048576 1 1048576 (ep508 rfl rfl) rfl)

noncomputable def ep519 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz389 (Real.cos qz79)) (@HMul.hMul Real Real Real qz0 qz389 (@Neg.neg Real Real.instNeg (Real.sin qz79))) Bool.false 66168103295 549755813888 13242871337015 107426134324412416 Bool.true 142357486459 1099511627776 26496306962671 214852268648824832 (@Enclosure.Real.IsNear.mulLit_ff qz389 (Real.cos qz79) 185363 1048576 1 1048576 356965 524288 71066215 102449545216 66168103295 549755813888 13242871337015 107426134324412416 qz393 (@Enclosure.Real.IsNear.recentre' (Real.cos qz79) Bool.false 713930 1048576 71066215 102449545216 356965 524288 71066215 102449545216 (ep515 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz389 (@Neg.neg Real Real.instNeg (Real.sin qz79)) 185363 1048576 1 1048576 767993 1048576 71066215 102449545216 142357486459 1099511627776 26496306962671 214852268648824832 qz393 (@Enclosure.Real.IsNear.neg (Real.sin qz79) Bool.false 767993 1048576 71066215 102449545216 (@Enclosure.Real.IsNear.recentre' (Real.sin qz79) Bool.false 767993 1048576 71066215 102449545216 767993 1048576 71066215 102449545216 (ep518 rfl rfl) rfl)) rfl)

noncomputable def ep520 := @ep404 66168103295 549755813888 13242871337015 107426134324412416 Bool.true 142357486459 1099511627776 26496306962671 214852268648824832 Bool.false 454317177922013450207232 826398132489 1099511627776 1337293444977907 214852268648824832 Bool.true 117311341513057096433664 26673510891 274877906944 668344013694817 107426134324412416 (ep405 (BSN.head_sum_c_succ qz5 31 32 rfl rfl) (ep506 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep507 ep519) rfl rfl

theorem EMRow46.d9 : Enclosure.Complex.IsNear qz65 Bool.false 826398132489 1099511627776 1337293444977907 214852268648824832 Bool.true 26673510891 274877906944 668344013694817 107426134324412416 := ep403 (BSN.head_sum_c_succ qz5 32 33 rfl rfl) (ep520 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

theorem EMRow46.d10 : @Eq Nat (BSN.factNat (Nat.mul 2 1)) 2 := @Eq.refl Nat 2

theorem EMRow46.d11 : @Eq Nat (Nat.pow 34 1) 34 := @Eq.refl Nat 34

noncomputable def ep521 := nat_lit 4092675679815921132770198584431

noncomputable def ep522 := nat_lit 5664229978825380207818230988800

noncomputable def ep523 := nat_lit 1446620697181304488243634606629469930457

noncomputable def ep524 := nat_lit 216282366443405797448081266036117287731200

noncomputable abbrev qz693 := (@instHMul Complex Complex.instMul)

noncomputable abbrev qz627 := qz693

noncomputable abbrev qz394 := qz627

noncomputable abbrev qz80 := qz394

noncomputable abbrev qz628 := (@instHSub Complex Complex.instSub)

noncomputable abbrev qz395 := qz628

noncomputable abbrev qz81 := qz395

noncomputable abbrev qz694 := (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (4 : Complex))

noncomputable abbrev qz695 := (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid))

noncomputable abbrev qz629 := (@HAdd.hAdd Complex Complex Complex qz691 (@HAdd.hAdd Complex Complex Complex qz691 qz694 (@HMul.hMul Complex Complex Complex qz693 Complex.I (@HDiv.hDiv Complex Complex Complex qz695 (↑qz692) (2 : Complex)))) (@Nat.cast Complex Complex.instNatCast 2))

noncomputable abbrev qz396 := qz629

noncomputable abbrev qz82 := (Complex.Stirling.logGammaStirling 1 qz396)

noncomputable abbrev qz630 := (@HAdd.hAdd Complex Complex Complex qz691 qz694 (@HMul.hMul Complex Complex Complex qz693 Complex.I (@HDiv.hDiv Complex Complex Complex qz695 (↑qz692) (2 : Complex))))

noncomputable abbrev qz397 := qz630

noncomputable abbrev qz83 := qz397

noncomputable abbrev qz84 := (@HMul.hMul Real Real Real qz269 (@HDiv.hDiv Real Real Real qz272 qz279 (2 : Real)) (Real.log Real.pi))

noncomputable abbrev qz398 := (@instHSub Real Real.instSub)

noncomputable def ep525 := Complex.re (@HMul.hMul Complex Complex Complex qz80 (Complex.exp (@HMul.hMul Complex Complex Complex qz80 Complex.I ↑(@HSub.hSub Real Real Real qz398 (Complex.im (@HSub.hSub Complex Complex Complex qz81 qz82 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz83 (@Nat.cast Complex Complex.instNatCast j))))) qz84))) (zetaApproximant qz5 1 34))

noncomputable def ep526 := @Enclosure.Real.IsNear.of_eq ep525 (@HSub.hSub Real Real Real qz398 (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz398 (Complex.im (@HSub.hSub Complex Complex Complex qz81 qz82 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz83 (@Nat.cast Complex Complex.instNatCast j))))) qz84)) (Complex.re (zetaApproximant qz5 1 34))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz398 (Complex.im (@HSub.hSub Complex Complex Complex qz81 qz82 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz83 (@Nat.cast Complex Complex.instNatCast j))))) qz84)) (Complex.im (zetaApproximant qz5 1 34))))

noncomputable def ep527 := nat_lit 327409248395177552061775989903

noncomputable def ep528 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz398 (Complex.im (@HSub.hSub Complex Complex Complex qz81 qz82 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz83 (@Nat.cast Complex Complex.instNatCast j))))) qz84)) (Complex.re (zetaApproximant qz5 1 34))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz398 (Complex.im (@HSub.hSub Complex Complex Complex qz81 qz82 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz83 (@Nat.cast Complex Complex.instNatCast j))))) qz84)) (Complex.im (zetaApproximant qz5 1 34))) ep527

noncomputable def ep529 := nat_lit 453138398306030416625458479104

noncomputable def ep530 := nat_lit 577494642657295400471533698237018225813

noncomputable def ep531 := nat_lit 86512946577362318979232506414446915092480

noncomputable def ep532 := nat_lit 120149752403463995997421287

noncomputable def ep533 := nat_lit 11328459957650760415636461977600

noncomputable def ep534 := nat_lit 339304769184233772329454239638160697

noncomputable def ep535 := nat_lit 25444984287459505582127207768954975027200

noncomputable def ep536 := nat_lit 3709097004675661360809561885078762978242582628500533986459648

noncomputable def ep537 := @Enclosure.Real.IsNear.mulLit_ff (Real.cos (@HSub.hSub Real Real Real qz398 (Complex.im (@HSub.hSub Complex Complex Complex qz81 qz82 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz83 (@Nat.cast Complex Complex.instNatCast j))))) qz84)) (Complex.re (zetaApproximant qz5 1 34)) 1048575 1048576 36674583

noncomputable def ep538 := nat_lit 7806052223140394155443721

noncomputable def ep539 := nat_lit 10803661306048164764057600

noncomputable def ep540 := nat_lit 13541294541311943657620139193

noncomputable def ep541 := nat_lit 2111111044830953732050203443200

noncomputable def ep542 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HSub.hSub Real Real Real qz398 (Complex.im (@HSub.hSub Complex Complex Complex qz81 qz82 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz83 (@Nat.cast Complex Complex.instNatCast j))))) qz84)) Bool.false 1048575 1048576 36674583

noncomputable abbrev qz399 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 72472121) qz42)

noncomputable def ep543 := @Enclosure.Real.IsNear.cos_image (@HSub.hSub Real Real Real qz398 (Complex.im (@HSub.hSub Complex Complex Complex qz81 qz82 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz83 (@Nat.cast Complex Complex.instNatCast j))))) qz84) qz399 Bool.false 72472121 524288 185

noncomputable def ep544 := nat_lit 43263129720639194453559677

noncomputable def ep545 := nat_lit 122939454259200000000000000000

noncomputable def ep546 := @Enclosure.Real.IsNear.recentre' (@HSub.hSub Real Real Real qz398 (Complex.im (@HSub.hSub Complex Complex Complex qz81 qz82 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz83 (@Nat.cast Complex Complex.instNatCast j))))) qz84) Bool.false 373518470054623139393 2702159776422297600 ep544 ep545

noncomputable def ep547 := nat_lit 11749061202639194453559677

noncomputable def ep548 := @Enclosure.Real.IsNear.subLit_ff_p (Complex.im (@HSub.hSub Complex Complex Complex qz81 qz82 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz83 (@Nat.cast Complex Complex.instNatCast j))))) qz84 581376620753832728129 2702159776422297600 ep547 ep545 2016489459 26214400

noncomputable def ep549 := nat_lit 9791562581399912825303859200

noncomputable def ep550 := nat_lit 1830235291825858292859233

noncomputable def ep551 := nat_lit 10244954521600000000000000000

noncomputable def ep552 := @Enclosure.Complex.IsNear.im_isNear (@HSub.hSub Complex Complex Complex qz81 qz82 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz83 (@Nat.cast Complex Complex.instNatCast j)))) Bool.true 11899253825930946781 112589990684262400 ep550 ep551 Bool.false 581376620753832728129 2702159776422297600

noncomputable def ep553 := nat_lit 1804020891702918838600033

noncomputable def ep554 := nat_lit 11119915602516254999300477

noncomputable def ep555 := @Enclosure.Complex.IsNear.subLitP qz82 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz83 (@Nat.cast Complex Complex.instNatCast j))) Bool.true 10951758219515819881 112589990684262400 ep553 ep551 Bool.false 589805394407509505729 2702159776422297600 ep554

noncomputable def ep556 := nat_lit 13397368774112390199040140686393344

noncomputable def ep557 := nat_lit 163642970786804952856560551145242624

noncomputable abbrev qz696 := (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (2 : Complex))

noncomputable abbrev qz631 := qz696

noncomputable abbrev qz400 := (@HSub.hSub Complex Complex Complex qz628 qz629 qz631)

noncomputable abbrev qz401 := (Complex.log qz629)

noncomputable abbrev qz85 := (@HSub.hSub Complex Complex Complex qz395 (@HMul.hMul Complex Complex Complex qz394 qz400 qz401) qz396)

noncomputable abbrev qz402 := qz631

noncomputable abbrev qz86 := (@HMul.hMul Complex Complex Complex qz394 qz402 ↑(Real.log (@HMul.hMul Real Real Real qz269 (2 : Real) Real.pi)))

noncomputable abbrev qz632 := qz695

noncomputable abbrev qz403 := qz632

noncomputable abbrev qz87 := qz403

noncomputable abbrev qz88 := (@instHMul Nat instMulNat)

noncomputable abbrev qz633 := (@instHPow Complex Int (@ZPow.toPow Complex (@DivInvMonoid.toZPow Complex Complex.instDivInvMonoid)))

noncomputable abbrev qz404 := qz633

noncomputable abbrev qz89 := qz404

noncomputable abbrev qz90 := qz396

noncomputable abbrev qz91 := (@OfNat.ofNat Int 1 (@instOfNat 1))

noncomputable abbrev qz92 := (@OfNat.ofNat Int 2 (@instOfNat 2))

noncomputable abbrev qz405 := (@instHSub Int Int.instSub)

noncomputable abbrev qz406 := (@instHMul Int Int.instMul)

noncomputable def ep558 := @Enclosure.Complex.IsNear.of_eq qz82 (@HAdd.hAdd Complex Complex Complex qz4 (@HAdd.hAdd Complex Complex Complex qz4 qz85 qz86) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz80 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz89 qz90 (@HSub.hSub Int Int Int qz405 qz91 (@HMul.hMul Int Int Int qz406 qz92 (@Nat.cast Int instNatCastInt k)))))) Bool.true 10951758219515819881

noncomputable def ep559 := @Enclosure.Complex.IsNear.addLitP (@HAdd.hAdd Complex Complex Complex qz4 qz85 qz86) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz80 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz89 qz90 (@HSub.hSub Int Int Int qz405 qz91 (@HMul.hMul Int Int Int qz406 qz92 (@Nat.cast Int instNatCastInt k))))) Bool.true 10951762889422763881 112589990684262400

noncomputable def ep560 := nat_lit 752599094184314165496345788416

noncomputable def ep561 := nat_lit 810622361595083079652857484410880

noncomputable def ep562 := @ep559 27527167426327357303 156325600000000000000000 Bool.false 196602913890758704363 900719925474099200 883718753947807621 9770350000000000000000 Bool.false 2850285 68719476736 3 68719476736 Bool.true 5107520701 4123168604160 26879 20615843020800 Bool.true ep560 10951758219515819881 112589990684262400 ep553 ep551 Bool.false ep561

noncomputable def ep563 := @Enclosure.Complex.IsNear.addLitP qz85 qz86 Bool.true 11055226074603026281 112589990684262400 27229000006893763553 156325600000000000000000

noncomputable def ep564 := nat_lit 1435469465442420507410432

noncomputable def ep565 := @ep563 Bool.false 196602913890758704363 900719925474099200 883718753947807621 9770350000000000000000 Bool.false 120447 131072 1 524288 Bool.false 0 1 0 1 Bool.true ep564 10951762889422763881 112589990684262400 27527167426327357303 156325600000000000000000 Bool.false 196602913890758704363 196602913890758704363 900719925474099200

noncomputable abbrev qz93 := (@HMul.hMul Complex Complex Complex qz394 qz400 qz401)

noncomputable def ep566 := @Enclosure.Complex.IsNear.subLitP qz93 qz90 Bool.true 10801898595563435881 112589990684262400 27229000006893763553 156325600000000000000000 Bool.false 51425808216560897071

noncomputable def ep567 := @ep566 180143985094819840 883718753947807621 9770350000000000000000 Bool.false 9000 4000 0 1 Bool.false 268790 4000 0 1 Bool.true 44220904298412105124000 11055226074603026281 112589990684262400 27229000006893763553 156325600000000000000000 Bool.false 157282331112606963490400 196602913890758704363 900719925474099200 883718753947807621 9770350000000000000000

noncomputable abbrev qz94 := qz400

noncomputable abbrev qz95 := qz401

noncomputable def ep568 := @Enclosure.Complex.IsNear.mul qz94 qz95 Bool.true 10801898595563435881 112589990684262400 27229000006893763553 156325600000000000000000 Bool.false 51425808216560897071 180143985094819840 883718753947807621

noncomputable abbrev qz96 := (Complex.re qz400)

noncomputable abbrev qz97 := (Complex.re qz401)

noncomputable abbrev qz98 := (Complex.im qz400)

noncomputable abbrev qz99 := (Complex.im qz401)

noncomputable def ep569 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 qz96 qz97) (@HMul.hMul Real Real Real qz0 qz98 qz99) 66332107173224515 9007199254740992 875000004103547 390814000000000000000 23262099870457484637 225179981368524800

noncomputable def ep570 := nat_lit 194589705959493495642287548508667904

noncomputable def ep571 := @Enclosure.Real.IsNear.mulLit_ff qz96 qz97 7000 4000 0 1 9476015310460645 2251799813685248 125000000586221 97703500000000000000

noncomputable def ep572 := @Enclosure.Complex.IsNear.re_isNear qz94 Bool.false 7000 4000 0 1 Bool.false 268790 4000 0 1

noncomputable abbrev qz634 := (Enclosure.sfrac Bool.false 268790 4000)

noncomputable abbrev qz407 := qz634

noncomputable def ep573 := @Enclosure.Complex.IsNear.of_eq qz94 (Complex.mk (Enclosure.sfrac Bool.false 7000 4000) qz407) Bool.false 7000 4000 0 1 Bool.false 268790 4000 0

noncomputable abbrev qz635 := (Enclosure.sfrac Bool.false 9000 4000)

noncomputable abbrev qz408 := (Complex.log (Complex.mk qz635 qz634))

noncomputable def ep574 := @Enclosure.Complex.IsNear.of_eq qz95 qz408 Bool.false 9476015310460645 2251799813685248 125000000586221 97703500000000000000 Bool.false 865437697476003 562949953421312 1000000000195407 390814000000000000000

noncomputable def ep575 := BSN.log_dyadic_bound 6793064100 137865064100 2 1 57020327697891326430000 1048576 390814 46145719866708810000 46145719866708810000 103417 144658128200 131072000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 6793064100) (BSN.artanhQ 137865064100) 0 1 46145719866708810000 57020327697891326430000 46145719866708810000 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz100 := (Enclosure.sfrac Bool.false 1 2)

noncomputable abbrev qz409 := (Enclosure.Real.IsNear.const Bool.false 1 2)

noncomputable abbrev qz636 := (Real.log (Enclosure.sfrac Bool.false 72329064100 16000000))

noncomputable abbrev qz637 := (@Nat.cast Real Real.instNatCast 16000000)

noncomputable def ep576 := @Enclosure.Real.IsNear.mulLit_ff qz100 qz636 1 2 0 1 9476015310460645 1125899906842624 125000000586221 48851750000000000000 9476015310460645 2251799813685248 125000000586221 97703500000000000000 qz409 (BSN.isNear_log_sfrac 72329064100 16000000 9476015310460645 1125899906842624 125000000586221 48851750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 72329064100) qz637)) Bool.false 317962311365810601328640 37778931862957161709568 1000000004689768 390814000000000000000 9476015310460645 1125899906842624 125000000586221 48851750000000000000 (BSN.log_rat_reduce_isNear 72329064100 16000000 12 144658128200 131072000000 103417 1048576 24973259072661432 36028797018963968 390814 1000000000000000 rfl rfl rfl rfl (ep575 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep577 := BSN.arctan_dyadic_bound_f 9000 268790 1 0 1048576 390814 0 1 1 0 1 1 35096 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 9000) (BSN.arctanEvenQ 268790) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 9000) (BSN.arctanOddQ 268790) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz101 := (@HMul.hMul Real Real Real qz269 (Enclosure.sfrac Bool.false 1 2) Real.pi)

noncomputable abbrev qz102 := (@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 2) Real.pi 1 2 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 qz409 BSN.pi_near_15 rfl)

noncomputable abbrev qz410 := (Real.arctan (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 9000) (@Nat.cast Real Real.instNatCast 268790)))

noncomputable def ep578 := @Enclosure.Real.IsNear.subLit_ff_p qz101 qz410 884279719003555 562949953421312 1 2000000000000000 35096 1048576 1 390814 907477199068597321728 865437697476003 562949953421312 1000000000195407 390814000000000000000 qz102 (ep577 rfl) rfl rfl

noncomputable abbrev qz411 := (Complex.mk qz635 qz634)

noncomputable abbrev qz412 := (Real.arctan (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 268790) (@Nat.cast Real Real.instNatCast 9000)))

noncomputable def ep579 := @Enclosure.Complex.IsNear.re_isNear qz95 Bool.false 9476015310460645 2251799813685248 125000000586221 97703500000000000000 Bool.false 865437697476003 562949953421312 1000000000195407 390814000000000000000 (ep574 (@congrArg Complex Complex qz90 qz411 Complex.log (BSN.w_shift_mk qz12 Bool.false 134395 1000 2 qz13 rfl)) (@Enclosure.Complex.IsNear.of_parts qz408 Bool.false 9476015310460645 2251799813685248 125000000586221 97703500000000000000 Bool.false 865437697476003 562949953421312 1000000000195407 390814000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz408) (@HMul.hMul Real Real Real qz0 qz100 qz636) Bool.false 9476015310460645 2251799813685248 125000000586221 97703500000000000000 (Enclosure.clog_re_eq 9000 268790 4000 72329064100 16000000 rfl rfl rfl) (ep576 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz408) qz412 Bool.false 865437697476003 562949953421312 1000000000195407 390814000000000000000 (Enclosure.clog_im_eq 9000 268790 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz412 (@HSub.hSub Real Real Real qz398 qz101 qz410) Bool.false 865437697476003 562949953421312 1000000000195407 390814000000000000000 (BSN.arctan_recip 268790 9000 rfl rfl) ep578))))

noncomputable def ep580 := @Enclosure.Real.IsNear.mulLit_ff qz98 qz99 268790 4000 0 1 865437697476003 562949953421312 1000000000195407 390814000000000000000

noncomputable def ep581 := @Enclosure.Complex.IsNear.im_isNear qz94 Bool.false 7000 4000 0 1 Bool.false 268790 4000 0 1

noncomputable def ep582 := @Enclosure.Complex.IsNear.im_isNear qz95 Bool.false 9476015310460645 2251799813685248 125000000586221 97703500000000000000 Bool.false 865437697476003 562949953421312 1000000000195407 390814000000000000000 (ep574 (@congrArg Complex Complex qz90 qz411 Complex.log (BSN.w_shift_mk qz12 Bool.false 134395 1000 2 qz13 rfl)) (@Enclosure.Complex.IsNear.of_parts qz408 Bool.false 9476015310460645 2251799813685248 125000000586221 97703500000000000000 Bool.false 865437697476003 562949953421312 1000000000195407 390814000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz408) (@HMul.hMul Real Real Real qz0 qz100 qz636) Bool.false 9476015310460645 2251799813685248 125000000586221 97703500000000000000 (Enclosure.clog_re_eq 9000 268790 4000 72329064100 16000000 rfl rfl rfl) (ep576 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz408) qz412 Bool.false 865437697476003 562949953421312 1000000000195407 390814000000000000000 (Enclosure.clog_im_eq 9000 268790 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz412 (@HSub.hSub Real Real Real qz398 qz101 qz410) Bool.false 865437697476003 562949953421312 1000000000195407 390814000000000000000 (BSN.arctan_recip 268790 9000 rfl rfl) ep578))))

noncomputable abbrev qz103 := (@ep573 1 (BSN.w_sub_half_mk qz279 Bool.false 134395 1000 2 qz281 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7000 4000) qz407 Bool.false 7000 4000 0 1 Bool.false 268790 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 7000 4000) (Enclosure.Real.IsNear.const Bool.false 268790 4000)))

noncomputable def ep583 := @ep569 26879000005252344753 156325600000000000000000 ep570 10801898595563435881 112589990684262400 27229000006893763553 156325600000000000000000 (@ep571 66332107173224515 9007199254740992 875000004103547 390814000000000000000 (ep572 qz103) ep579 rfl) (@ep580 23262099870457484637 225179981368524800 26879000005252344753 156325600000000000000000 (ep581 qz103) ep582 rfl) rfl

noncomputable def ep584 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz96 qz99) (@HMul.hMul Real Real Real qz0 qz98 qz97) 6058063882332021 2251799813685248 7000000001367849 1563256000000000000000 50941163105974335391 180143985094819840

noncomputable def ep585 := nat_lit 115800625360665123756371969319108608

noncomputable def ep586 := @Enclosure.Real.IsNear.mulLit_ff qz96 qz99 7000 4000 0 1 865437697476003 562949953421312 1000000000195407 390814000000000000000

noncomputable def ep587 := @Enclosure.Real.IsNear.mulLit_ff qz98 qz97 268790 4000 0 1 9476015310460645 2251799813685248 125000000586221 97703500000000000000

noncomputable def ep588 := @ep584 3359875015757034259 39081400000000000000000 ep585 51425808216560897071 180143985094819840 883718753947807621 9770350000000000000000 (@ep586 6058063882332021 2251799813685248 7000000001367849 1563256000000000000000 (ep572 qz103) ep582 rfl) (@ep587 50941163105974335391 180143985094819840 3359875015757034259 39081400000000000000000 (ep581 qz103) ep579 rfl) rfl

noncomputable def ep589 := @Enclosure.Complex.IsNear.of_eq qz90 qz411 Bool.false 9000 4000 0 1 Bool.false 268790 4000 0 1 (BSN.w_shift_mk qz12 Bool.false 134395 1000 2 qz13 rfl)

noncomputable abbrev qz413 := (ep589 (@Enclosure.Complex.IsNear.mk qz635 qz634 Bool.false 9000 4000 0 1 Bool.false 268790 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 9000 4000) (Enclosure.Real.IsNear.const Bool.false 268790 4000)))

noncomputable abbrev qz104 := qz413

noncomputable def ep590 := ep567 (@ep568 9770350000000000000000 (ep583 rfl) (ep588 rfl)) qz104 rfl rfl rfl rfl rfl rfl

noncomputable abbrev qz105 := qz402

noncomputable def ep591 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re qz105) (Complex.re ↑qz2)) (@HMul.hMul Real Real Real qz0 (Complex.im qz105) (Complex.im ↑qz2)) 120447 131072 1 524288 0 1 0 1 120447 120447

noncomputable def ep592 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re qz105) (Complex.re ↑qz2) 1 2 0 1 120447 65536 1 262144 120447 131072 1 524288

noncomputable abbrev qz106 := (@Enclosure.Complex.IsNear.of_eq qz402 (Complex.mk (Enclosure.sfrac Bool.false 1 2) qz548) Bool.false 1 2 0 1 Bool.false 0 1 0 1 BSN.half_c_mk (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 2) qz548 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz409 qz550))

noncomputable def ep593 := ep592 (@Enclosure.Complex.IsNear.re_isNear qz105 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz106) (@Enclosure.Real.IsNear.of_eq (Complex.re ↑qz2) qz2 Bool.false 120447 65536 1 262144 (Complex.ofReal_re qz2) EMRow46.d4)

noncomputable def ep594 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz105) (Complex.im ↑qz2) 0 1 0 1 0 1 0 1 0 1 0 1

noncomputable def ep595 := ep594 (@Enclosure.Complex.IsNear.im_isNear qz105 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz106) (@Enclosure.Real.IsNear.of_eq (Complex.im ↑qz2) qz10 Bool.false 0 1 0 1 (@Eq.trans Real (Complex.im ↑qz2) (0 : Real) qz10 (Complex.ofReal_im qz2) Enclosure.sfrac_zero_eq) qz21)

noncomputable def ep596 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re qz105) (Complex.im ↑qz2)) (@HMul.hMul Real Real Real qz0 (Complex.im qz105) (Complex.re ↑qz2)) 0 1 0 1 0 1 0 1 0 0

noncomputable def ep597 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re qz105) (Complex.im ↑qz2) 1 2 0 1 0 1 0 1 0 1 0 1

noncomputable def ep598 := ep597 (@Enclosure.Complex.IsNear.re_isNear qz105 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz106) (@Enclosure.Real.IsNear.of_eq (Complex.im ↑qz2) qz10 Bool.false 0 1 0 1 (@Eq.trans Real (Complex.im ↑qz2) (0 : Real) qz10 (Complex.ofReal_im qz2) Enclosure.sfrac_zero_eq) qz21)

noncomputable def ep599 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz105) (Complex.re ↑qz2) 0 1 0 1 120447 65536 1 262144 0 1 0 1

noncomputable def ep600 := ep599 (@Enclosure.Complex.IsNear.im_isNear qz105 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz106) (@Enclosure.Real.IsNear.of_eq (Complex.re ↑qz2) qz2 Bool.false 120447 65536 1 262144 (Complex.ofReal_re qz2) EMRow46.d4)

noncomputable def ep601 := @ep565 883718753947807621 9770350000000000000000 (ep590 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@Enclosure.Complex.IsNear.mul qz105 (↑qz2) Bool.false 120447 131072 1 524288 Bool.false 0 1 0 1 (@ep591 131072 1 524288 (ep593 rfl) (ep595 rfl) rfl rfl) (@ep596 1 0 1 (ep598 rfl) (ep600 rfl) rfl rfl))

noncomputable abbrev qz107 := (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 1)

noncomputable abbrev qz414 := (@Nat.cast Complex Complex.instNatCast 1)

noncomputable abbrev qz108 := (@HMul.hMul Complex Complex Complex qz394 (@HMul.hMul Complex Complex Complex qz394 (2 : Complex) qz414) (@HSub.hSub Complex Complex Complex qz395 (@HMul.hMul Complex Complex Complex qz394 (2 : Complex) qz414) (1 : Complex)))

noncomputable abbrev qz415 := (@HPow.hPow Complex Int Complex qz633 qz629 (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) (@OfNat.ofNat Int 1 (@instOfNat 1)) (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (@OfNat.ofNat Int 2 (@instOfNat 2)) (@Nat.cast Int instNatCastInt 1))))

noncomputable abbrev qz109 := qz415

noncomputable def ep602 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz80 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz89 qz90 (@HSub.hSub Int Int Int qz405 qz91 (@HMul.hMul Int Int Int qz406 qz92 (@Nat.cast Int instNatCastInt k))))) (@HAdd.hAdd Complex Complex Complex qz4 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz80 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz89 qz90 (@HSub.hSub Int Int Int qz405 qz91 (@HMul.hMul Int Int Int qz406 qz92 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli qz107)) qz108) qz109)) Bool.false 2850285 68719476736 3 68719476736

noncomputable def ep603 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz80 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz89 qz90 (@HSub.hSub Int Int Int qz405 qz91 (@HMul.hMul Int Int Int qz406 qz92 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli qz107)) qz108) qz109) Bool.false 0 1 0 1 Bool.false

noncomputable def ep604 := @ep603 0 1 0 1 Bool.false 2850285 68719476736 3 68719476736 Bool.true 5107520701 4123168604160 26879 20615843020800 Bool.false 2850285 2850285 68719476736 3 68719476736 Bool.true 5107520701 5107520701 4123168604160 26879

noncomputable def ep605 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz80 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz89 qz90 (@HSub.hSub Int Int Int qz405 qz91 (@HMul.hMul Int Int Int qz406 qz92 (@Nat.cast Int instNatCastInt k))))) (Complex.mk qz10 qz10) Bool.false 0 1 0 1 Bool.false

noncomputable def ep606 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli qz107)) qz108) qz109 Bool.false 2850285 68719476736 3 68719476736 Bool.true 5107520701 4123168604160 26879 20615843020800

noncomputable abbrev qz110 := (Complex.re qz415)

noncomputable abbrev qz111 := (Complex.im qz415)

noncomputable def ep607 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli qz107)) qz108)) qz110) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli qz107)) qz108)) qz111) 2850285 68719476736 3 68719476736 0 1 0

noncomputable def ep608 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli qz107)) qz108)) qz110 1 12 0 1 8550855 17179869184 9 17179869184 2850285

noncomputable def ep609 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli qz107)) qz108) (Complex.mk (Enclosure.sfrac Bool.false 1 12) qz10) Bool.false 1 12 0 1 Bool.false 0 1 0 1

noncomputable abbrev qz416 := (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 12) qz10 Bool.false 1 12 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 12) qz21)

noncomputable def ep610 := @Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli qz107)) qz108) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (ep609 (BSN.stirling_coeff_mk 1 1 6 Bool.false BSN.bern_real_1 rfl rfl) qz416)

noncomputable def ep611 := @Enclosure.Complex.IsNear.re_isNear qz109 Bool.false 8550855 17179869184 9 17179869184 Bool.true 5107520701 343597383680 26879 1717986918400

noncomputable abbrev qz638 := (@instHPow Complex Nat (@NPow.toPow Complex (@Monoid.toNPow Complex (@Semiring.toMonoid Complex Complex.instSemiring))))

noncomputable abbrev qz417 := (@HPow.hPow Complex Nat Complex qz638 qz629 1)

noncomputable abbrev qz112 := (@Inv.inv Complex Complex.instInv qz417)

noncomputable def ep612 := @Enclosure.Complex.IsNear.of_eq qz109 qz112 Bool.false 8550855 17179869184 9 17179869184 Bool.true 5107520701 343597383680 26879

noncomputable def ep613 := @Enclosure.Complex.IsNear.of_parts qz112 Bool.false 8550855 17179869184 9 17179869184 Bool.true 5107520701 343597383680 26879

noncomputable abbrev qz113 := (Complex.re qz417)

noncomputable abbrev qz114 := (@MonoidWithZeroHom Complex Real (@instMulZeroOneClassOfSemiring Complex Complex.instSemiring) (@instMulZeroOneClassOfSemiring Real Real.semiring))

noncomputable abbrev qz115 := (@MonoidWithZeroHom.funLike Complex Real (@instMulZeroOneClassOfSemiring Complex Complex.instSemiring) (@instMulZeroOneClassOfSemiring Real Real.semiring))

noncomputable abbrev qz116 := qz417

noncomputable def ep614 := @Enclosure.Real.IsNear.mulLit_ff qz113 (@Inv.inv Real Real.instInv (@DFunLike.coe qz114 Complex (fun (x : Complex) => Real) qz115 Complex.normSq qz116)) 9000 4000 0 1 950095 4294967296 1 4294967296

noncomputable def ep615 := @Enclosure.Complex.IsNear.re_isNear qz116 Bool.false 9000 4000 0 1 Bool.false 268790 4000 0 1

noncomputable def ep616 := @Enclosure.Complex.IsNear.of_eq qz116 qz90 Bool.false 9000 4000 0 1 Bool.false 268790 4000 0

noncomputable def ep617 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (@DFunLike.coe qz114 Complex (fun (x : Complex) => Real) qz115 Complex.normSq qz116)) Bool.false 950095 4294967296 1 4294967296 950095 4294967296 1

noncomputable abbrev qz117 := (Complex.im qz417)

noncomputable abbrev qz418 := (@instHAdd Real Real.instAdd)

noncomputable def ep618 := @Enclosure.Real.IsNear.of_eq (@DFunLike.coe qz114 Complex (fun (x : Complex) => Real) qz115 Complex.normSq qz116) (@HAdd.hAdd Real Real Real qz418 (@HMul.hMul Real Real Real qz0 qz113 qz113) (@HMul.hMul Real Real Real qz0 qz117 qz117)) Bool.false 723290641 160000 0 1

noncomputable def ep619 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz113 qz113) (@HMul.hMul Real Real Real qz0 qz117 qz117) 81 16 0 1 722480641 160000

noncomputable def ep620 := @Enclosure.Real.IsNear.mulLit_ff qz113 qz113 9000 4000 0 1 9000 4000 0 1

noncomputable def ep621 := @Enclosure.Real.IsNear.mulLit_ff qz117 qz117 268790 4000 0 1 268790 4000 0 1

noncomputable def ep622 := @Enclosure.Complex.IsNear.im_isNear qz116 Bool.false 9000 4000 0 1 Bool.false 268790 4000 0 1

noncomputable abbrev qz118 := (ep615 (@ep616 1 (BSN.pow_one_c qz396) qz413))

noncomputable abbrev qz119 := (ep622 (@ep616 1 (BSN.pow_one_c qz396) qz413))

noncomputable def ep623 := @ep619 0 1 11572650256 723290641 160000 0 1 (@ep620 81 16 0 1 qz118 qz118 rfl) (@ep621 722480641 160000 0 1 qz119 qz119 rfl)

noncomputable def ep624 := @Enclosure.Real.IsNear.inv_image (@DFunLike.coe qz114 Complex (fun (x : Complex) => Real) qz115 Complex.normSq qz116) 723290641 160000 0 1 475047 475048 2147483648 (ep618 (Enclosure.Complex.normSq_eq_mul_add_mul qz116) (ep623 rfl rfl)) rfl

noncomputable def ep625 := @Enclosure.Real.IsNear.of_eq (Complex.re qz112) (@HMul.hMul Real Real Real qz0 qz113 (@Inv.inv Real Real.instInv (@DFunLike.coe qz114 Complex (fun (x : Complex) => Real) qz115 Complex.normSq qz116))) Bool.false 8550855 17179869184 9 17179869184 (Enclosure.Complex.inv_re_eq_mul qz116) (@ep614 8550855 17179869184 9 17179869184 qz118 (@ep617 4294967296 (ep624 rfl rfl rfl rfl rfl) rfl) rfl)

noncomputable def ep626 := @Enclosure.Real.IsNear.of_eq (Complex.im qz112) (@HMul.hMul Real Real Real qz0 (@Neg.neg Real Real.instNeg qz117) (@Inv.inv Real Real.instInv (@DFunLike.coe qz114 Complex (fun (x : Complex) => Real) qz115 Complex.normSq qz116))) Bool.true 5107520701 343597383680 26879 1717986918400 (Enclosure.Complex.inv_im_eq_mul qz116)

noncomputable def ep627 := @Enclosure.Real.IsNear.mulLit_tf (@Neg.neg Real Real.instNeg qz117) (@Inv.inv Real Real.instInv (@DFunLike.coe qz114 Complex (fun (x : Complex) => Real) qz115 Complex.normSq qz116)) 268790 4000 0 1 950095 4294967296 1

noncomputable def ep628 := @ep627 4294967296 5107520701 343597383680 26879 1717986918400 (@Enclosure.Real.IsNear.neg qz117 Bool.false 268790 4000 0 1 qz119) (@ep617 4294967296 (ep624 rfl rfl rfl rfl rfl) rfl) rfl

noncomputable def ep629 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli qz107)) qz108)) qz111 0 1 0 1 5107520701 343597383680 26879 1717986918400 0

noncomputable def ep630 := @Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli qz107)) qz108) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (ep609 (BSN.stirling_coeff_mk 1 1 6 Bool.false BSN.bern_real_1 rfl rfl) qz416)

noncomputable def ep631 := @Enclosure.Complex.IsNear.im_isNear qz109 Bool.false 8550855 17179869184 9 17179869184 Bool.true 5107520701 343597383680 26879 1717986918400

noncomputable abbrev qz120 := (@ep612 1717986918400 (BSN.zpow_one_sub_two_mul qz396 1 1 rfl rfl) (@ep613 1717986918400 ep625 (ep626 ep628)))

noncomputable def ep632 := @ep607 1 2850285 2850285 68719476736 3 68719476736 (@ep608 68719476736 3 68719476736 ep610 (ep611 qz120) rfl) (@ep629 1 0 1 ep630 (ep631 qz120) rfl) rfl

noncomputable def ep633 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli qz107)) qz108)) qz111) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli qz107)) qz108)) qz110) 5107520701 4123168604160 26879 20615843020800 0 1 0

noncomputable def ep634 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli qz107)) qz108)) qz111 1 12 0 1 5107520701 343597383680 26879 1717986918400 5107520701

noncomputable def ep635 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli qz107)) qz108)) qz110 0 1 0 1 8550855 17179869184 9 17179869184 0

noncomputable def ep636 := @ep633 1 5107520701 5107520701 4123168604160 26879 20615843020800 (@ep634 4123168604160 26879 20615843020800 ep610 (ep631 qz120) rfl) (@ep635 1 0 1 ep630 (ep611 qz120) rfl) rfl

noncomputable abbrev qz121 := (@Enclosure.Complex.IsNear.mk qz548 qz548 Bool.false 0 1 0 1 Bool.false 0 1 0 1 qz550 qz550)

noncomputable def ep637 := @ep604 20615843020800 (@ep605 0 1 0 1 (BSN.stirling_sum_base qz90) qz121) (ep606 (ep632 rfl) (ep636 rfl)) rfl rfl rfl rfl rfl

noncomputable def ep638 := @ep562 589805394407509505729 2702159776422297600 ep554 ep545 (ep601 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep602 Bool.true 5107520701 4123168604160 26879 20615843020800 (BSN.stirling_sum_succ qz90 0 1 rfl) (ep637 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl

noncomputable def ep639 := @Enclosure.Complex.IsNear.of_eq (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz83 (@Nat.cast Complex Complex.instNatCast j))) (BSN.logSumC qz12 2) Bool.false 9474956064151269 1125899906842624 125000000586221 48851750000000000000 Bool.false 877997255591331 281474976710656

noncomputable abbrev qz122 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz274 qz397 qz414))

noncomputable def ep640 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz12 2) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.logSumC qz12 1) qz122) Bool.false 9474956064151269 1125899906842624 125000000586221 48851750000000000000 Bool.false 877997255591331 281474976710656 1000000000195407 195407000000000000000

noncomputable def ep641 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz12 1) qz122 Bool.false 9474768696202981 2251799813685248 125000000586221 97703500000000000000 Bool.false 882185385575843 562949953421312 1000000000195407 390814000000000000000 Bool.false

noncomputable def ep642 := nat_lit 42671408599863476461920451559424

noncomputable def ep643 := nat_lit 988537028278359106810275692544

noncomputable abbrev qz123 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz274 qz397 (@Nat.cast Complex Complex.instNatCast 0)))

noncomputable def ep644 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz12 1) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.logSumC qz12 0) qz123) Bool.false 9474768696202981 2251799813685248 125000000586221 97703500000000000000 Bool.false 882185385575843 562949953421312 1000000000195407 390814000000000000000

noncomputable def ep645 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz12 0) qz123 Bool.false 0 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable abbrev qz419 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz634))

noncomputable def ep646 := @Enclosure.Complex.IsNear.of_eq qz123 qz419 Bool.false 9474768696202981 2251799813685248 125000000586221 97703500000000000000 Bool.false 882185385575843 562949953421312 1000000000195407 390814000000000000000

noncomputable def ep647 := BSN.log_dyadic_bound 6713064100 137785064100 2 1 56954171667123326430000 1048576 390814 45065229610708810000 45065229610708810000 102256 144498128200 131072000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 6713064100) (BSN.artanhQ 137785064100) 0 1 45065229610708810000 56954171667123326430000 45065229610708810000 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep648 := @Enclosure.Real.IsNear.mulLit_ff qz100 (Real.log (Enclosure.sfrac Bool.false 72249064100 16000000)) 1 2 0 1 9474768696202981 1125899906842624 125000000586221 48851750000000000000 9474768696202981 2251799813685248 125000000586221 97703500000000000000 qz409 (BSN.isNear_log_sfrac 72249064100 16000000 9474768696202981 1125899906842624 125000000586221 48851750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 72249064100) qz637)) Bool.false 317920481932471584161792 37778931862957161709568 1000000004689768 390814000000000000000 9474768696202981 1125899906842624 125000000586221 48851750000000000000 (BSN.log_rat_reduce_isNear 72249064100 16000000 12 144498128200 131072000000 102256 1048576 24973259072661432 36028797018963968 390814 1000000000000000 rfl rfl rfl rfl (ep647 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep649 := BSN.arctan_dyadic_bound_f 1000 268790 1 0 1048576 390814 0 1 1 0 1 1 3901 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 268790) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 268790) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz420 := (@Nat.cast Real Real.instNatCast 1000)

noncomputable abbrev qz421 := (@Nat.cast Real Real.instNatCast 268790)

noncomputable def ep650 := @Enclosure.Real.IsNear.subLit_ff_p qz101 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz420 qz421)) 884279719003555 562949953421312 1 2000000000000000 3901 1048576 1 390814 925038422865575149568 882185385575843 562949953421312 1000000000195407 390814000000000000000 qz102 (ep649 rfl) rfl rfl

noncomputable abbrev qz124 := (@HAdd.hAdd Complex Complex Complex qz274 qz397 (@Nat.cast Complex Complex.instNatCast 0))

noncomputable abbrev qz422 := (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz634)

noncomputable def ep651 := @ep645 9474768696202981 2251799813685248 125000000586221 97703500000000000000 Bool.false 882185385575843 562949953421312 1000000000195407 390814000000000000000 Bool.false 9474768696202981 9474768696202981 2251799813685248 125000000586221 97703500000000000000 Bool.false 882185385575843 882185385575843 562949953421312 1000000000195407 390814000000000000000 (@Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz12 0) (Complex.mk qz10 qz10) Bool.false 0 1 0 1 Bool.false 0 1 0 1 (BSN.log_sum_c_base qz12) qz121) (ep646 (@congrArg Complex Complex qz124 qz422 Complex.log (BSN.w_shift_mk qz12 Bool.false 134395 1000 0 qz13 rfl)) (@Enclosure.Complex.IsNear.of_parts qz419 Bool.false 9474768696202981 2251799813685248 125000000586221 97703500000000000000 Bool.false 882185385575843 562949953421312 1000000000195407 390814000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz419) (@HMul.hMul Real Real Real qz0 qz100 (Real.log (Enclosure.sfrac Bool.false 72249064100 16000000))) Bool.false 9474768696202981 2251799813685248 125000000586221 97703500000000000000 (Enclosure.clog_re_eq 1000 268790 4000 72249064100 16000000 rfl rfl rfl) (ep648 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz419) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz421 qz420)) Bool.false 882185385575843 562949953421312 1000000000195407 390814000000000000000 (Enclosure.clog_im_eq 1000 268790 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz421 qz420)) (@HSub.hSub Real Real Real qz398 qz101 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz420 qz421))) Bool.false 882185385575843 562949953421312 1000000000195407 390814000000000000000 (BSN.arctan_recip 268790 1000 rfl rfl) ep650)))) rfl rfl

noncomputable abbrev qz423 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz634))

noncomputable def ep652 := @Enclosure.Complex.IsNear.of_eq qz122 qz423 Bool.false 9475143432099557 2251799813685248 125000000586221 97703500000000000000 Bool.false 873809125606819 562949953421312 1000000000195407 390814000000000000000

noncomputable def ep653 := BSN.log_dyadic_bound 6737064100 137809064100 2 1 56974014444353726430000 1048576 390814 45388032687508810000 45388032687508810000 102605 144546128200 131072000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 6737064100) (BSN.artanhQ 137809064100) 0 1 45388032687508810000 56974014444353726430000 45388032687508810000 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep654 := @Enclosure.Real.IsNear.mulLit_ff qz100 (Real.log (Enclosure.sfrac Bool.false 72273064100 16000000)) 1 2 0 1 9475143432099557 1125899906842624 125000000586221 48851750000000000000 9475143432099557 2251799813685248 125000000586221 97703500000000000000 qz409 (BSN.isNear_log_sfrac 72273064100 16000000 9475143432099557 1125899906842624 125000000586221 48851750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 72273064100) qz637)) Bool.false 317933055982631202586624 37778931862957161709568 1000000004689768 390814000000000000000 9475143432099557 1125899906842624 125000000586221 48851750000000000000 (BSN.log_rat_reduce_isNear 72273064100 16000000 12 144546128200 131072000000 102605 1048576 24973259072661432 36028797018963968 390814 1000000000000000 rfl rfl rfl rfl (ep653 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep655 := BSN.arctan_dyadic_bound_f 5000 268790 1 0 1048576 390814 0 1 1 0 1 1 19503 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 5000) (BSN.arctanEvenQ 268790) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 5000) (BSN.arctanOddQ 268790) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz424 := (@Nat.cast Real Real.instNatCast 5000)

noncomputable def ep656 := @Enclosure.Real.IsNear.subLit_ff_p qz101 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz424 qz421)) 884279719003555 562949953421312 1 2000000000000000 19503 1048576 1 390814 916255277692295839744 873809125606819 562949953421312 1000000000195407 390814000000000000000 qz102 (ep655 rfl) rfl rfl

noncomputable abbrev qz125 := (@HAdd.hAdd Complex Complex Complex qz274 qz397 qz414)

noncomputable abbrev qz425 := (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz634)

noncomputable def ep657 := @ep641 9475143432099557 2251799813685248 125000000586221 97703500000000000000 Bool.false 873809125606819 562949953421312 1000000000195407 390814000000000000000 Bool.false ep642 9474956064151269 1125899906842624 125000000586221 48851750000000000000 Bool.false ep643 877997255591331 281474976710656 1000000000195407 195407000000000000000 (ep644 (BSN.log_sum_c_succ qz12 0 1 rfl) (ep651 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep652 (@congrArg Complex Complex qz125 qz425 Complex.log (BSN.w_shift_mk qz12 Bool.false 134395 1000 1 qz13 rfl)) (@Enclosure.Complex.IsNear.of_parts qz423 Bool.false 9475143432099557 2251799813685248 125000000586221 97703500000000000000 Bool.false 873809125606819 562949953421312 1000000000195407 390814000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz423) (@HMul.hMul Real Real Real qz0 qz100 (Real.log (Enclosure.sfrac Bool.false 72273064100 16000000))) Bool.false 9475143432099557 2251799813685248 125000000586221 97703500000000000000 (Enclosure.clog_re_eq 5000 268790 4000 72273064100 16000000 rfl rfl rfl) (ep654 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz423) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz421 qz424)) Bool.false 873809125606819 562949953421312 1000000000195407 390814000000000000000 (Enclosure.clog_im_eq 5000 268790 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz421 qz424)) (@HSub.hSub Real Real Real qz398 qz101 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz424 qz421))) Bool.false 873809125606819 562949953421312 1000000000195407 390814000000000000000 (BSN.arctan_recip 268790 5000 rfl rfl) ep656)))) rfl rfl

noncomputable def ep658 := @ep555 ep545 Bool.false 9474956064151269 1125899906842624 125000000586221 48851750000000000000 Bool.false 877997255591331 281474976710656 1000000000195407 195407000000000000000 Bool.true ep556 11899253825930946781 112589990684262400 ep550 ep551 Bool.false ep557 581376620753832728129 2702159776422297600 ep547 ep545 (@ep558 112589990684262400 ep553 ep551 Bool.false 589805394407509505729 2702159776422297600 ep554 ep545 (BSN.logGammaStirling_unfold 1 qz90) (ep638 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (@ep639 1000000000195407 195407000000000000000 (BSN.log_sum_c_eq qz12 2) (ep640 (BSN.log_sum_c_succ qz12 1 2 rfl) (ep657 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)))

noncomputable abbrev qz126 := (@HDiv.hDiv Real Real Real qz272 qz279 (2 : Real))

noncomputable def ep659 := @Enclosure.Real.IsNear.mulLit_ff qz126 (Real.log Real.pi) 134395 2000 0 1 75021 65536 1 262144 2016489459 26214400 26879 104857600 (@Enclosure.Real.IsNear.of_eq qz126 (Enclosure.sfrac Bool.false 134395 2000) Bool.false 134395 2000 0 1 (BSN.t_half_eq qz12 Bool.false 134395 1000 qz13) (Enclosure.Real.IsNear.const Bool.false 134395 2000)) EMRow46.d5 rfl

noncomputable def ep660 := @ep548 26879 104857600 ep549 373518470054623139393 2702159776422297600 ep544 ep545 (@ep552 ep547 ep545 (ep658 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) ep659 rfl rfl

noncomputable def ep661 := nat_lit 8333861765039413646945467217050976014855209411807293884791919175550245444788480

noncomputable def ep662 := nat_lit 16724196880350348788331395272153705671371194477876794629532630551193871196416

noncomputable def ep663 := nat_lit 21799703542058849463009401404692878801152852239864445364102449772215376563937536

noncomputable def ep664 := BSN.sin_dyadic_bound_f 3372237542 2147483648 3 2 1048576 391196 ep661 ep72 ep662 ep663 ep75 ep662 1048575 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3372237542) qz15 0 2 ep661 ep72 ep662 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3372237542) qz16 0 2 ep663 ep75 ep662 rfl rfl rfl rfl) rfl rfl

noncomputable def ep665 := @ep543 524288 Bool.false 1048575 1048576 1 195407 (@ep546 72472121 524288 185 524288 ep660 rfl) (Enclosure.sfrac_false_div 72472121 524288) (BSN.cos_reduce3 qz399 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 118650060472388820140032) qz43) 226375608064910080 72057594037927936 Bool.false 1048575 1048576 21 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q3 72472121 524288 226375608064910080 72057594037927936 21 118650060472388820140032 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1048575 1048576 118650060472388820140032 75557863725914323419136 3372237542 2147483648 391196 390814 (ep664 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep666 := nat_lit 21607322612096329528115200

noncomputable def ep667 := nat_lit 27072839379900433632131872071

noncomputable def ep668 := nat_lit 4222222089661907464100406886400

noncomputable abbrev qz426 := (@HPow.hPow Complex Complex Complex qz539 (@Nat.cast Complex Complex.instNatCast 34) qz540)

noncomputable abbrev qz127 := qz426

noncomputable abbrev qz427 := (@Nat.cast Complex Complex.instNatCast 34)

noncomputable abbrev qz128 := (@HAdd.hAdd Complex Complex Complex qz274 (@HDiv.hDiv Complex Complex Complex qz403 qz427 (@HSub.hSub Complex Complex Complex qz395 qz273 (1 : Complex))) qz402)

noncomputable abbrev qz129 := (@instHSub Nat instSubNat)

noncomputable abbrev qz428 := qz638

noncomputable abbrev qz130 := qz428

noncomputable abbrev qz131 := qz427

noncomputable def ep669 := @Enclosure.Complex.IsNear.of_eq (zetaApproximant qz5 1 34) (@HAdd.hAdd Complex Complex Complex qz4 (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 34, @HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast n) qz7) (@HMul.hMul Complex Complex Complex qz80 qz127 (@HAdd.hAdd Complex Complex Complex qz4 qz128 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz131 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1))))))) Bool.false ep538 ep539 ep540

noncomputable def ep670 := @Enclosure.Complex.IsNear.addLitP (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 34, @HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast n) qz7) (@HMul.hMul Complex Complex Complex qz80 qz127 (@HAdd.hAdd Complex Complex Complex qz4 qz128 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz131 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))))) Bool.false 27275594137 34359738368 340821785221683 53713067162206208

noncomputable def ep671 := nat_lit 145808617418096226997255993

noncomputable def ep672 := nat_lit 290835237306382219282256071

noncomputable def ep673 := nat_lit 268213912074048698513442576508387328

noncomputable def ep674 := nat_lit 66318298113461880793240074281025536

noncomputable def ep675 := @ep670 Bool.false 9873867035 137438953472 681415404827665 107426134324412416 Bool.true 770156298046127979314679 ep539 ep671 ep541 Bool.true 1069780645344334767861537 ep666 ep672 ep668 Bool.false ep673 ep538 ep539 ep540 ep541 Bool.false ep674 482529126118329301194463 ep666

noncomputable def ep676 := @Enclosure.Complex.IsNear.of_eq (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 34, @HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast n) qz7) (BSN.headSumC qz5 34) Bool.false 27275594137 34359738368 340821785221683 53713067162206208 Bool.false 9873867035 137438953472 681415404827665

noncomputable abbrev qz639 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 33) qz7)

noncomputable def ep677 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 34) (@HAdd.hAdd Complex Complex Complex qz4 qz65 qz639) Bool.false 27275594137 34359738368 340821785221683 53713067162206208 Bool.false 9873867035 137438953472 681415404827665 107426134324412416

noncomputable def ep678 := @Enclosure.Complex.IsNear.addLitP qz65 qz639 Bool.false 826398132489 1099511627776 1337293444977907 214852268648824832 Bool.true 26673510891 274877906944 668344013694817 107426134324412416 Bool.false

noncomputable abbrev qz640 := (Real.log (Enclosure.sfrac Bool.false 33 1))

noncomputable abbrev qz132 := (@HMul.hMul Real Real Real qz269 qz279 qz640)

noncomputable abbrev qz429 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 33)))

noncomputable def ep679 := @Enclosure.Complex.IsNear.of_eq qz639 (Complex.mk (@HMul.hMul Real Real Real qz0 qz429 (Real.cos qz132)) (@HMul.hMul Real Real Real qz0 qz429 (@Neg.neg Real Real.instNeg (Real.sin qz132)))) Bool.false 46420879895 1099511627776 25993695908825 214852268648824832 Bool.false 46421244961 274877906944 816961945803 6714133395275776 (BSN.cpow_neg_s_mk qz12 134395 1000 33 qz13 rfl)

noncomputable abbrev qz430 := (Real.sqrt (@Nat.cast Real Real.instNatCast 33))

noncomputable abbrev qz431 := (@Nat.cast Real Real.instNatCast 33)

noncomputable abbrev qz641 := (@HDiv.hDiv Real Real Real qz1 qz431 qz14)

noncomputable def ep680 := @Enclosure.Real.IsNear.inv_image qz430 6023611 1048576 1 1048576 91266 91267 524288 (@Enclosure.Real.IsNear.of_eq qz430 (Real.sqrt qz641) Bool.false 6023611 1048576 1 1048576 (BSN.sqrt_natCast_div_one 33) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz641) Bool.false 6023611 1048576 1 1048576 6023611 1048576 1 1048576 (BSN.sqrt_enclosure 33 1 3011805 3011806 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep681 := BSN.log_dyadic_bound 1 65 2 1 12675 524288 195407 1 1 16133 66 64 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 1) (BSN.artanhQ 65) 0 1 1 12675 1 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep682 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz640 134395 1000 0 1 15746868335186131 4503599627370496 200000000195407 39081400000000000000 423260073981468015149 900719925474099200 5375800005252344753 7816280000000000000000 qz18 (BSN.isNear_log_sfrac 33 1 15746868335186131 4503599627370496 200000000195407 39081400000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz641) Bool.false 66047152845744529997824 18889465931478580854784 1000000000977035 195407000000000000000 15746868335186131 4503599627370496 200000000195407 39081400000000000000 (BSN.log_rat_reduce_isNear 33 1 5 66 64 16133 524288 24973259072661432 36028797018963968 195407 1000000000000000 rfl rfl rfl rfl (ep681 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep683 := nat_lit 76599265946382501927957292357186576

noncomputable def ep684 := BSN.sin_dyadic_bound_f 526085282 2147483648 2 1 1048576 391196 ep683 ep58 ep683 ep683 ep59 ep683 254315 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 526085282) qz15 0 1 ep683 ep58 ep683 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 526085282) qz16 0 1 ep683 ep59 ep683 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz432 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 492739577) qz23)

noncomputable def ep685 := @Enclosure.Real.IsNear.cos_image qz132 qz432 Bool.false 492739577 1048576 361 524288 Bool.false 254315 1048576 1 195407 (@Enclosure.Real.IsNear.recentre' qz132 Bool.false 423260073981468015149 900719925474099200 5375800005252344753 7816280000000000000000 492739577 1048576 361 524288 (ep682 rfl) rfl) (Enclosure.sfrac_false_div 492739577 1048576) (BSN.cos_reduce3 qz432 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 37019960693591820468224) qz24) 226375608064910080 72057594037927936 Bool.false 254315 1048576 74 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q3 492739577 1048576 226375608064910080 72057594037927936 74 37019960693591820468224 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 254315 1048576 37019960693591820468224 151115727451828646838272 526085282 2147483648 391196 390814 (ep684 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep686 := BSN.cos_dyadic_bound_f 526085282 2147483648 2 1 1048576 391196 ep683 ep62 ep683 ep683 ep63 ep683 1017268 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 526085282) qz19 0 1 ep683 ep62 ep683 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 526085282) qz20 0 1 ep683 ep63 ep683 rfl rfl rfl rfl) rfl rfl

noncomputable def ep687 := @Enclosure.Real.IsNear.sin_image qz132 qz432 Bool.false 492739577 1048576 361 524288 Bool.true 1017268 1048576 1 195407 (@Enclosure.Real.IsNear.recentre' qz132 Bool.false 423260073981468015149 900719925474099200 5375800005252344753 7816280000000000000000 492739577 1048576 361 524288 (ep682 rfl) rfl) (Enclosure.sfrac_false_div 492739577 1048576) (BSN.sin_reduce3 qz432 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 37019960693591820468224) qz24) 226375608064910080 72057594037927936 Bool.false 1017268 1048576 74 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q3 492739577 1048576 226375608064910080 72057594037927936 74 37019960693591820468224 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1017268 1048576 37019960693591820468224 151115727451828646838272 526085282 2147483648 391196 390814 (ep686 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz433 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 33))) Bool.false 182533 1048576 1 1048576 182533 1048576 1 1048576 (ep680 rfl rfl) rfl)

noncomputable def ep688 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz429 (Real.cos qz132)) (@HMul.hMul Real Real Real qz0 qz429 (@Neg.neg Real Real.instNeg (Real.sin qz132))) Bool.false 46420879895 1099511627776 25993695908825 214852268648824832 Bool.false 46421244961 274877906944 816961945803 6714133395275776 (@Enclosure.Real.IsNear.mulLit_ff qz429 (Real.cos qz132) 182533 1048576 1 1048576 254315 1048576 71066215 102449545216 46420879895 1099511627776 25993695908825 214852268648824832 qz433 (@Enclosure.Real.IsNear.recentre' (Real.cos qz132) Bool.false 254315 1048576 71066215 102449545216 254315 1048576 71066215 102449545216 (ep685 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz429 (@Neg.neg Real Real.instNeg (Real.sin qz132)) 182533 1048576 1 1048576 254317 262144 71066215 102449545216 46421244961 274877906944 816961945803 6714133395275776 qz433 (@Enclosure.Real.IsNear.neg (Real.sin qz132) Bool.true 254317 262144 71066215 102449545216 (@Enclosure.Real.IsNear.recentre' (Real.sin qz132) Bool.true 1017268 1048576 71066215 102449545216 254317 262144 71066215 102449545216 (ep687 rfl rfl) rfl)) rfl)

noncomputable def ep689 := @ep678 46420879895 1099511627776 25993695908825 214852268648824832 Bool.false 46421244961 274877906944 816961945803 6714133395275776 Bool.false 959674653060172542377984 27275594137 34359738368 340821785221683 53713067162206208 Bool.false 5428215808048318382080 9873867035 137438953472 681415404827665 107426134324412416 EMRow46.d9 (ep679 ep688) rfl rfl

noncomputable def ep690 := @Enclosure.Complex.IsNear.mul qz127 (@HAdd.hAdd Complex Complex Complex qz4 qz128 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz131 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1))))) Bool.true 770156298046127979314679 ep539 ep671 ep541 Bool.true

noncomputable def ep691 := nat_lit 2530980119113597130316441

noncomputable abbrev qz133 := (Complex.re qz426)

noncomputable abbrev qz134 := (Complex.im qz426)

noncomputable def ep692 := @Enclosure.Real.IsNear.subLit_tt_n (@HMul.hMul Real Real Real qz0 qz133 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz128 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz131 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz134 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz128 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz131 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1))))))) 979338032952706827231 12710189771821370310656 ep691

noncomputable def ep693 := nat_lit 42222220896619074641004068864

noncomputable def ep694 := nat_lit 19259611462416370481433943

noncomputable def ep695 := nat_lit 9788832702129706646622155680136140432210919424

noncomputable def ep696 := @Enclosure.Real.IsNear.mulLit_tf qz133 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz128 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz131 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))))) 169341552549 1099511627776 25743685946067 214852268648824832 294943792169

noncomputable abbrev qz642 := (Real.log (Enclosure.sfrac Bool.false 34 1))

noncomputable abbrev qz135 := (@HMul.hMul Real Real Real qz269 qz279 qz642)

noncomputable abbrev qz136 := (Real.sin (@HMul.hMul Real Real Real qz269 qz279 qz642))

noncomputable abbrev qz434 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 34)))

noncomputable abbrev qz643 := (@Neg.neg Real Real.instNeg qz136)

noncomputable def ep697 := @Enclosure.Complex.IsNear.of_eq qz127 (Complex.mk (@HMul.hMul Real Real Real qz0 qz434 (Real.cos qz135)) (@HMul.hMul Real Real Real qz0 qz434 qz643)) Bool.true 169341552549 1099511627776 25743685946067 214852268648824832 Bool.true 41472703467 549755813888 12824902792011 107426134324412416 (BSN.cpow_neg_s_mk qz12 134395 1000 34 qz13 rfl)

noncomputable abbrev qz435 := (Real.sqrt (@Nat.cast Real Real.instNatCast 34))

noncomputable abbrev qz436 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 34) qz14)

noncomputable def ep698 := @Enclosure.Real.IsNear.inv_image qz435 6114197 1048576 1 1048576 89914 89915 524288 (@Enclosure.Real.IsNear.of_eq qz435 (Real.sqrt qz436) Bool.false 6114197 1048576 1 1048576 (BSN.sqrt_natCast_div_one 34) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz436) Bool.false 6114197 1048576 1 1048576 6114197 1048576 1 1048576 (BSN.sqrt_enclosure 34 1 3057098 3057099 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep699 := BSN.log_dyadic_bound 2 66 2 1 13068 524288 195407 4 4 31784 68 64 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 2) (BSN.artanhQ 66) 0 1 4 13068 4 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz137 := qz642

noncomputable def ep700 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz137 134395 1000 0 1 15881309401485523 4503599627370496 200000000195407 39081400000000000000 426873715402529372717 900719925474099200 5375800005252344753 7816280000000000000000 qz18 (BSN.isNear_log_sfrac 34 1 15881309401485523 4503599627370496 200000000195407 39081400000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz436) Bool.false 66611039547888335060992 18889465931478580854784 1000000000977035 195407000000000000000 15881309401485523 4503599627370496 200000000195407 39081400000000000000 (BSN.log_rat_reduce_isNear 34 1 5 68 64 31784 524288 24973259072661432 36028797018963968 195407 1000000000000000 rfl rfl rfl rfl (ep699 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep701 := nat_lit 2117680155047012354104671279970965088577712406772779689992944890226315643224320

noncomputable def ep702 := nat_lit 1083113256466201429842567568483147864399771236245199578368514846847238308096

noncomputable def ep703 := nat_lit 5544551556041229934625822528622602516399266197641454579235592355126407346422016

noncomputable def ep704 := BSN.sin_dyadic_bound_f 2395158366 2147483648 3 2 1048576 391196 ep701 ep72 ep702 ep703 ep75 ep702 941681 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2395158366) qz15 0 2 ep701 ep72 ep702 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2395158366) qz16 0 2 ep703 ep75 ep702 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz437 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 496946409) qz23)

noncomputable def ep705 := @Enclosure.Real.IsNear.cos_image qz135 qz437 Bool.false 496946409 1048576 361 524288 Bool.true 941681 1048576 1 195407 (@Enclosure.Real.IsNear.recentre' qz135 Bool.false 426873715402529372717 900719925474099200 5375800005252344753 7816280000000000000000 496946409 1048576 361 524288 (ep700 rfl) rfl) (Enclosure.sfrac_false_div 496946409 1048576) (BSN.cos_reduce1 qz437 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 168544286372578426093568) qz24) 226375608064910080 72057594037927936 Bool.false 941681 1048576 75 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q1 496946409 1048576 226375608064910080 72057594037927936 75 168544286372578426093568 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 941681 1048576 168544286372578426093568 151115727451828646838272 2395158366 2147483648 391196 390814 (ep704 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep706 := nat_lit 1176970358695658508471414074458750892705129013200986583142022056724329685483776

noncomputable def ep707 := nat_lit 3528744849574043122554557088239286382386587497130469350269329140479294579835136

noncomputable def ep708 := BSN.cos_dyadic_bound_f 2395158366 2147483648 3 2 1048576 391196 ep706 ep79 ep702 ep707 ep81 ep702 461246 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2395158366) qz19 0 2 ep706 ep79 ep702 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2395158366) qz20 0 2 ep707 ep81 ep702 rfl rfl rfl rfl) rfl rfl

noncomputable def ep709 := @Enclosure.Real.IsNear.sin_image qz135 qz437 Bool.false 496946409 1048576 361 524288 Bool.false 461246 1048576 1 195407 (@Enclosure.Real.IsNear.recentre' qz135 Bool.false 426873715402529372717 900719925474099200 5375800005252344753 7816280000000000000000 496946409 1048576 361 524288 (ep700 rfl) rfl) (Enclosure.sfrac_false_div 496946409 1048576) (BSN.sin_reduce1 qz437 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 168544286372578426093568) qz24) 226375608064910080 72057594037927936 Bool.false 461246 1048576 75 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q1 496946409 1048576 226375608064910080 72057594037927936 75 168544286372578426093568 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 461246 1048576 168544286372578426093568 151115727451828646838272 2395158366 2147483648 391196 390814 (ep708 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz438 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 34))) Bool.false 179829 1048576 1 1048576 179829 1048576 1 1048576 (ep698 rfl rfl) rfl)

noncomputable def ep710 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz434 (Real.cos qz135)) (@HMul.hMul Real Real Real qz0 qz434 qz643) Bool.true 169341552549 1099511627776 25743685946067 214852268648824832 Bool.true 41472703467 549755813888 12824902792011 107426134324412416 (@Enclosure.Real.IsNear.mulLit_ft qz434 (Real.cos qz135) 179829 1048576 1 1048576 941681 1048576 71066215 102449545216 169341552549 1099511627776 25743685946067 214852268648824832 qz438 (@Enclosure.Real.IsNear.recentre' (Real.cos qz135) Bool.true 941681 1048576 71066215 102449545216 941681 1048576 71066215 102449545216 (ep705 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz434 qz643 179829 1048576 1 1048576 230623 524288 71066215 102449545216 41472703467 549755813888 12824902792011 107426134324412416 qz438 (@Enclosure.Real.IsNear.neg qz136 Bool.false 230623 524288 71066215 102449545216 (@Enclosure.Real.IsNear.recentre' qz136 Bool.false 461246 1048576 71066215 102449545216 230623 524288 71066215 102449545216 (ep709 rfl rfl) rfl)) rfl)

noncomputable def ep711 := @ep696 589552363056 0 1 979338032952706827231 12710189771821370310656 ep691 ep693 (@Enclosure.Complex.IsNear.re_isNear qz127 Bool.true 169341552549 1099511627776 25743685946067 214852268648824832 Bool.true 41472703467 549755813888 12824902792011 107426134324412416 (ep697 ep710))

noncomputable def ep712 := @Enclosure.Complex.IsNear.re_isNear (@HAdd.hAdd Complex Complex Complex qz4 qz128 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz131 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1))))) Bool.false 294943792169 589552363056 0 1 Bool.false

noncomputable def ep713 := @Enclosure.Complex.IsNear.addLitP qz128 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz131 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) Bool.false 721130641 1444981282 0 1 Bool.true 182777200

noncomputable def ep714 := @ep713 722490641 0 1 Bool.false 1 816 0 1 Bool.false 26879 81600 0 1 Bool.false 589887584338 294943792169 589552363056 0 1 Bool.false 4505206419439 4505206419439 58955236305600 0 1

noncomputable abbrev qz138 := (@HDiv.hDiv Complex Complex Complex qz403 qz427 (@HSub.hSub Complex Complex Complex qz395 qz273 (1 : Complex)))

noncomputable def ep715 := @Enclosure.Complex.IsNear.addLitP qz138 qz105 Bool.true 68000000 72249064100 0 1 Bool.true 18277720000 72249064100 0 1

noncomputable def ep716 := @Enclosure.Complex.IsNear.of_eq qz138 (Complex.mk (Enclosure.sfrac Bool.true 68000000 72249064100) (Enclosure.sfrac Bool.true 18277720000 72249064100)) Bool.true 68000000 72249064100 0 1 Bool.true 18277720000 72249064100 0 1

noncomputable def ep717 := @ep715 Bool.false 1 2 0 1 Bool.false 0 1 0 1 Bool.false 72113064100 721130641 1444981282 0 1 Bool.true 18277720000 182777200 722490641 0 1 (ep716 (BSN.N_div_s_sub_one_mk qz12 134395 1000 34 qz13 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 68000000 72249064100) (Enclosure.sfrac Bool.true 18277720000 72249064100) Bool.true 68000000 72249064100 0 1 Bool.true 18277720000 72249064100 0 1 (Enclosure.Real.IsNear.const Bool.true 68000000 72249064100) (Enclosure.Real.IsNear.const Bool.true 18277720000 72249064100))) qz106 rfl

noncomputable abbrev qz139 := (@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 1)))

noncomputable abbrev qz140 := (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz428 qz427 1))

noncomputable def ep718 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz131 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@HAdd.hAdd Complex Complex Complex qz4 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz131 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz140)) Bool.false 1 816 0 1

noncomputable def ep719 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz131 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz140) Bool.false 0 1 0 1 Bool.false

noncomputable def ep720 := @ep719 0 1 0 1 Bool.false 1 816 0 1 Bool.false 26879 81600 0 1 Bool.false 1 1 816 0 1 Bool.false 26879 26879 81600 0

noncomputable def ep721 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz131 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (Complex.mk qz10 qz10) Bool.false 0 1 0 1 Bool.false

noncomputable def ep722 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz140 Bool.false 1 816 0 1 Bool.false 26879 81600 0 1

noncomputable def ep723 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz140)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz140)) 1 816 0 1 0 1 0

noncomputable def ep724 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz140) 1 24 0 1 1 34 0 1 1

noncomputable def ep725 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) 1 24 0 1 0 1 0 1 1

noncomputable def ep726 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 1 2 0 1 1 24 0

noncomputable def ep727 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139) (Complex.mk (Enclosure.sfrac Bool.false 1 12) qz10) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (BSN.bern_coeff_mk 1 1 6 2 Bool.false BSN.bern_real_1 EMRow46.d10 rfl) qz416

noncomputable def ep728 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) qz5 Bool.false 1 2 0 1 Bool.false 134395 1000 0 1 (BSN.ascPochhammer_one_eval qz5)

noncomputable def ep729 := ep728 (@Enclosure.Complex.IsNear.of_eq qz5 (Complex.mk qz100 qz12) Bool.false 1 2 0 1 Bool.false 134395 1000 0 1 (BSN.s_crit_mk qz12 Bool.false 134395 1000 qz13) (@Enclosure.Complex.IsNear.mk qz100 qz12 Bool.false 1 2 0 1 Bool.false 134395 1000 0 1 qz409 qz18))

noncomputable def ep730 := @ep726 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep727) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 134395 1000 0 1 ep729)

noncomputable def ep731 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 134395 1000 0 1 0 1 0

noncomputable def ep732 := @ep731 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep727) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 134395 1000 0 1 ep729)

noncomputable def ep733 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) 26879 2400 0 1 0 1 0 1 26879

noncomputable def ep734 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 134395 1000 0 1 26879 2400 0

noncomputable def ep735 := @ep734 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep727) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 134395 1000 0 1 ep729)

noncomputable def ep736 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 1 2 0 1 0 1 0

noncomputable def ep737 := @ep736 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep727) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 134395 1000 0 1 ep729)

noncomputable def ep738 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 24 0 1 Bool.false 26879 2400 0 1 (@ep725 1 24 0 1 (ep730 rfl) (ep732 rfl) rfl rfl) (@ep733 26879 2400 0 1 (ep735 rfl) (ep737 rfl) rfl rfl)

noncomputable def ep739 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 26879 2400 0 1 ep738

noncomputable abbrev qz141 := (@Enclosure.Complex.IsNear.of_eq (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz428 qz427 1)) (Complex.mk (Enclosure.sfrac Bool.false 1 34) qz548) Bool.false 1 34 0 1 Bool.false 0 1 0 1 (BSN.natCast_pow_inv_mk 34 1 34 EMRow46.d11 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 34) qz548 Bool.false 1 34 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 34) qz550))

noncomputable def ep740 := @ep724 816 0 1 ep739 (@Enclosure.Complex.IsNear.re_isNear qz140 Bool.false 1 34 0 1 Bool.false 0 1 0 1 qz141)

noncomputable def ep741 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz140) 26879 2400 0 1 0 1 0 1 0

noncomputable def ep742 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 26879 2400 0 1 ep738

noncomputable def ep743 := @ep741 1 0 1 ep742 (@Enclosure.Complex.IsNear.im_isNear qz140 Bool.false 1 34 0 1 Bool.false 0 1 0 1 qz141)

noncomputable def ep744 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz140)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz140)) 0 1 0 1 26879 81600 0

noncomputable def ep745 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz140) 1 24 0 1 0 1 0 1 0

noncomputable def ep746 := @ep745 1 0 1 ep739 (@Enclosure.Complex.IsNear.im_isNear qz140 Bool.false 1 34 0 1 Bool.false 0 1 0 1 qz141)

noncomputable def ep747 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz140) 26879 2400 0 1 1 34 0 1 26879

noncomputable def ep748 := @ep747 81600 0 1 ep742 (@Enclosure.Complex.IsNear.re_isNear qz140 Bool.false 1 34 0 1 Bool.false 0 1 0 1 qz141)

noncomputable def ep749 := @ep720 1 (@ep721 0 1 0 1 (BSN.bern_sum_base qz5 34) qz121) (ep722 (@ep723 1 1 1 816 0 1 (ep740 rfl) (ep743 rfl) rfl rfl) (@ep744 1 26879 26879 81600 0 1 (ep746 rfl) (ep748 rfl) rfl rfl)) rfl rfl rfl rfl rfl

noncomputable def ep750 := ep714 (ep717 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep718 Bool.false 26879 81600 0 1 (BSN.bern_sum_succ qz5 34 0 1 1 rfl rfl) (ep749 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl rfl

noncomputable def ep751 := @Enclosure.Real.IsNear.mulLit_tf qz134 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz128 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz131 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))))) 41472703467 549755813888 12824902792011 107426134324412416 4505206419439

noncomputable def ep752 := @ep751 58955236305600 0 1 62281029963672823831671 ep539 ep694 ep541 (@Enclosure.Complex.IsNear.im_isNear qz127 Bool.true 169341552549 1099511627776 25743685946067 214852268648824832 Bool.true 41472703467 549755813888 12824902792011 107426134324412416 (ep697 ep710))

noncomputable def ep753 := @Enclosure.Complex.IsNear.im_isNear (@HAdd.hAdd Complex Complex Complex qz4 qz128 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz131 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1))))) Bool.false 294943792169 589552363056 0 1 Bool.false

noncomputable def ep754 := nat_lit 1271018977182137031065600

noncomputable def ep755 := nat_lit 38660206394747538111465471

noncomputable def ep756 := @Enclosure.Real.IsNear.addLit_tt (@HMul.hMul Real Real Real qz0 qz133 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz128 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz131 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz134 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz128 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz131 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1))))))) 14959189208265128501961 ep754 ep755

noncomputable def ep757 := nat_lit 1260875154558173405853953

noncomputable def ep758 := nat_lit 21111110448309537320502034432

noncomputable def ep759 := nat_lit 6798557508274014300136809765053059645241819136

noncomputable def ep760 := @Enclosure.Real.IsNear.mulLit_tf qz133 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz128 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz131 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))))) 169341552549 1099511627776 25743685946067 214852268648824832 4505206419439

noncomputable def ep761 := @ep760 58955236305600 0 1 14959189208265128501961 ep754 ep755 ep668 (@Enclosure.Complex.IsNear.re_isNear qz127 Bool.true 169341552549 1099511627776 25743685946067 214852268648824832 Bool.true 41472703467 549755813888 12824902792011 107426134324412416 (ep697 ep710))

noncomputable def ep762 := @Enclosure.Real.IsNear.mulLit_tf qz134 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz128 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz131 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))))) 41472703467 549755813888 12824902792011 107426134324412416 294943792169

noncomputable def ep763 := @ep762 589552363056 0 1 4077372144019137916641 108036613060481647640576 ep757 ep758 (@Enclosure.Complex.IsNear.im_isNear qz127 Bool.true 169341552549 1099511627776 25743685946067 214852268648824832 Bool.true 41472703467 549755813888 12824902792011 107426134324412416 (ep697 ep710))

noncomputable abbrev qz644 := (ep750 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable def ep764 := @ep690 1069780645344334767861537 ep666 ep672 ep668 (@ep692 ep693 62281029963672823831671 ep539 ep694 ep541 ep695 770156298046127979314679 ep539 ep671 ep541 (ep711 (@ep712 4505206419439 58955236305600 0 1 qz644) rfl) (ep752 (@ep753 4505206419439 58955236305600 0 1 qz644) rfl) rfl rfl) (@ep756 ep668 4077372144019137916641 108036613060481647640576 ep757 ep758 ep759 1069780645344334767861537 ep666 ep672 ep668 (ep761 (@ep753 4505206419439 58955236305600 0 1 qz644) rfl) (ep763 (@ep712 4505206419439 58955236305600 0 1 qz644) rfl) rfl rfl)

noncomputable def ep765 := @ep675 ep667 ep668 (@ep676 107426134324412416 (BSN.head_sum_c_eq qz5 34) (ep677 (BSN.head_sum_c_succ qz5 33 34 rfl rfl) (ep689 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))) ep764 rfl rfl rfl

noncomputable def ep766 := @Enclosure.Complex.IsNear.re_isNear (zetaApproximant qz5 1 34) Bool.false ep538 ep539 ep540 ep541 Bool.false 482529126118329301194463 ep666 ep667 ep668 (@ep669 ep541 Bool.false 482529126118329301194463 ep666 ep667 ep668 (BSN.zetaApproximant_eq_folded' qz5 1 34 rfl) (ep765 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

noncomputable def ep767 := @Enclosure.Real.IsNear.mulLit_tf (Real.sin (@HSub.hSub Real Real Real qz398 (Complex.im (@HSub.hSub Complex Complex Complex qz81 qz82 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz83 (@Nat.cast Complex Complex.instNatCast j))))) qz84)) (Complex.im (zetaApproximant qz5 1 34)) 249 524288 36674583

noncomputable def ep768 := @Enclosure.Real.IsNear.recentre' (Real.sin (@HSub.hSub Real Real Real qz398 (Complex.im (@HSub.hSub Complex Complex Complex qz81 qz82 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz83 (@Nat.cast Complex Complex.instNatCast j))))) qz84)) Bool.true 498 1048576 36674583

noncomputable def ep769 := @Enclosure.Real.IsNear.sin_image (@HSub.hSub Real Real Real qz398 (Complex.im (@HSub.hSub Complex Complex Complex qz81 qz82 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz83 (@Nat.cast Complex Complex.instNatCast j))))) qz84) qz399 Bool.false 72472121 524288 185

noncomputable def ep770 := nat_lit 4637356179190941069986740185149277210773503537438664066941969599995111412080896

noncomputable def ep771 := nat_lit 13878620143812122512383557764903524220977768223360238611566843538882946493849856

noncomputable def ep772 := BSN.cos_dyadic_bound_f 3372237542 2147483648 3 2 1048576 391196 ep770 ep79 ep662 ep771 ep81 ep662 498 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3372237542) qz19 0 2 ep770 ep79 ep662 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3372237542) qz20 0 2 ep771 ep81 ep662 rfl rfl rfl rfl) rfl rfl

noncomputable def ep773 := @ep769 524288 Bool.true 498 1048576 1 195407 (@ep546 72472121 524288 185 524288 ep660 rfl) (Enclosure.sfrac_false_div 72472121 524288) (BSN.sin_reduce3 qz399 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 118650060472388820140032) qz43) 226375608064910080 72057594037927936 Bool.false 498 1048576 21 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q3 72472121 524288 226375608064910080 72057594037927936 21 118650060472388820140032 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 498 1048576 118650060472388820140032 75557863725914323419136 3372237542 2147483648 391196 390814 (ep772 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep774 := @Enclosure.Complex.IsNear.im_isNear (zetaApproximant qz5 1 34) Bool.false ep538 ep539 ep540 ep541 Bool.false 482529126118329301194463 ep666 ep667 ep668 (@ep669 ep541 Bool.false 482529126118329301194463 ep666 ep667 ep668 (BSN.zetaApproximant_eq_folded' qz5 1 34 rfl) (ep765 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

theorem EMRow46.d12 : Enclosure.Real.IsNear (hardyZApproximantEM 1 34 qz12) Bool.false ep521 ep522 ep523 ep524 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantEM 1 34 qz12) ep525 Bool.false ep521 ep522 ep523 ep524 (@Eq.refl Real ep525) (@ep526 Bool.false ep521 ep522 ep523 ep524 (BSN.re_exp_mul (@HSub.hSub Real Real Real qz398 (Complex.im (@HSub.hSub Complex Complex Complex qz81 qz82 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz83 (@Nat.cast Complex Complex.instNatCast j))))) qz84) (zetaApproximant qz5 1 34)) (@ep528 ep529 ep530 ep531 ep532 ep533 ep534 ep535 ep536 ep521 ep522 ep523 ep524 (@ep537 102449545216 ep538 ep539 ep540 ep541 ep527 ep529 ep530 ep531 (@ep542 102449545216 1048575 1048576 36674583 102449545216 (ep665 rfl rfl) rfl) ep766 rfl) (@ep767 102449545216 482529126118329301194463 ep666 ep667 ep668 ep532 ep533 ep534 ep535 (@ep768 102449545216 249 524288 36674583 102449545216 (ep773 rfl rfl) rfl) ep774 rfl) rfl rfl))

noncomputable abbrev qz697 := (@HAdd.hAdd Complex Complex Complex (@instHAdd Complex Complex.instAdd) (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (2 : Complex)) (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul) Complex.I ↑(Enclosure.sfrac Bool.false 136442 1000)))

noncomputable abbrev qz645 := qz697

noncomputable abbrev qz439 := qz645

noncomputable abbrev qz142 := (BSN.headSumC qz439 9)

noncomputable abbrev qz143 := qz439

noncomputable abbrev qz646 := (@Neg.neg Complex Complex.instNeg qz697)

noncomputable abbrev qz440 := qz646

noncomputable abbrev qz144 := qz440

noncomputable abbrev qz647 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 8) qz144)

noncomputable def ep775 := @Enclosure.Complex.IsNear.of_eq qz142 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz143 8) qz647) Bool.false 3712078734803 1099511627776 511201488725275 214852268648824832 Bool.true 427701602855 1099511627776 511128717986033 214852268648824832

noncomputable def ep776 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz143 8) qz647 Bool.false 873871946853 274877906944 114399495672287 53713067162206208 Bool.true 104896257783 1099511627776 457469227258185 214852268648824832 Bool.false

noncomputable abbrev qz648 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 7) qz144)

noncomputable def ep777 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz143 8) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz143 7) qz648) Bool.false 873871946853 274877906944 114399495672287 53713067162206208 Bool.true 104896257783 1099511627776 457469227258185 214852268648824832

noncomputable def ep778 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz143 7) qz648 Bool.false 877930314853 274877906944 25020616429379 13428266790551552 Bool.false 77590792273 274877906944 100001092185099 53713067162206208 Bool.true

noncomputable abbrev qz649 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 6) qz144)

noncomputable def ep779 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz143 7) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz143 6) qz649) Bool.false 877930314853 274877906944 25020616429379 13428266790551552 Bool.false 77590792273 274877906944 100001092185099 53713067162206208

noncomputable def ep780 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz143 6) qz649 Bool.false 3134569533805 1099511627776 338309854277513 214852268648824832 Bool.false 66963014719 1099511627776 338045414283367 214852268648824832 Bool.false

noncomputable def ep781 := nat_lit 3861178358231672880627712

noncomputable abbrev qz650 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 5) qz144)

noncomputable def ep782 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz143 6) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz143 5) qz650) Bool.false 3134569533805 1099511627776 338309854277513 214852268648824832 Bool.false 66963014719 1099511627776 338045414283367 214852268648824832

noncomputable def ep783 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz143 5) qz650 Bool.false 1333662463719 549755813888 135227941798305 107426134324412416 Bool.true 86226510819 1099511627776 270322310992283 214852268648824832 Bool.false

noncomputable def ep784 := nat_lit 1723247825245496504483840

noncomputable abbrev qz651 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 4) qz144)

noncomputable def ep785 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz143 5) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz143 4) qz651) Bool.false 1333662463719 549755813888 135227941798305 107426134324412416 Bool.true 86226510819 1099511627776 270322310992283 214852268648824832

noncomputable def ep786 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz143 4) qz651 Bool.false 2230703432421 1099511627776 194647877948457 214852268648824832 Bool.false 30978327655 137438953472 12159533349823 13428266790551552 Bool.false

noncomputable def ep787 := nat_lit 2932754772774856465317888

noncomputable def ep788 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz143 4) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz143 3) (@HPow.hPow Complex Complex Complex qz6 qz8 qz144)) Bool.false 2230703432421 1099511627776 194647877948457 214852268648824832 Bool.false 30978327655 137438953472 12159533349823 13428266790551552

noncomputable def ep789 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz143 3) (@HPow.hPow Complex Complex Complex qz6 qz8 qz144) Bool.false 1835931406871 1099511627776 107172765627655 214852268648824832 Bool.true 124646741505 549755813888 53522192884473 107426134324412416 Bool.false

noncomputable def ep790 := nat_lit 1226342181033362061262848

noncomputable def ep791 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz143 3) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz143 2) (@HPow.hPow Complex Complex Complex qz6 qz9 qz144)) Bool.false 1835931406871 1099511627776 107172765627655 214852268648824832 Bool.true 124646741505 549755813888 53522192884473 107426134324412416

noncomputable def ep792 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz143 2) (@HPow.hPow Complex Complex Complex qz6 qz9 qz144) Bool.false 1 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable def ep793 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz143 2) (Complex.mk (Enclosure.sfrac Bool.false 1 1) qz10) Bool.false 1 1 0 1 Bool.false 0 1 0 1 (BSN.head_sum_c_two qz143)

noncomputable abbrev qz698 := (Enclosure.sfrac Bool.false 136442 1000)

noncomputable abbrev qz652 := qz698

noncomputable abbrev qz441 := qz652

noncomputable abbrev qz145 := (@HMul.hMul Real Real Real qz269 qz441 (Real.log qz280))

noncomputable abbrev qz146 := qz441

noncomputable abbrev qz442 := (@Eq.refl Real qz652)

noncomputable abbrev qz147 := qz442

noncomputable def ep794 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz9 qz144) (Complex.mk (@HMul.hMul Real Real Real qz0 qz282 (Real.cos qz145)) (@HMul.hMul Real Real Real qz0 qz282 (@Neg.neg Real Real.instNeg (Real.sin qz145)))) Bool.false 736419779095 1099511627776 107172765627655 214852268648824832 Bool.true 124646741505 549755813888 53522192884473 107426134324412416 (BSN.cpow_neg_s_mk qz146 136442 1000 2 qz147 rfl)

noncomputable def ep795 := nat_lit 241427238327395654956160053858533376

noncomputable def ep796 := BSN.cos_dyadic_bound_f 700965376 2147483648 2 1 1048576 391196 ep795 ep62 ep795 ep795 ep63 ep795 993209 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 700965376) qz19 0 1 ep795 ep62 ep795 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 700965376) qz20 0 1 ep795 ep63 ep795 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz148 := (Enclosure.Real.IsNear.const Bool.false 136442 1000)

noncomputable abbrev qz443 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 24792057) qz17)

noncomputable def ep797 := @Enclosure.Real.IsNear.cos_image qz145 qz443 Bool.false 24792057 262144 733 1048576 Bool.false 993209 1048576 1 195407 (@Enclosure.Real.IsNear.recentre' qz145 Bool.false 1549503573 16384000 68221 97703500 24792057 262144 733 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz146 (Real.log qz280) 136442 1000 0 1 363408 524288 1 195407 1549503573 16384000 68221 97703500 qz148 qz286 rfl) rfl) (Enclosure.sfrac_false_div 24792057 262144) (BSN.cos_reduce0 qz443 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 12331513308271821717504) qz287) 226375608064910080 72057594037927936 Bool.false 993209 1048576 15 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q0 24792057 262144 226375608064910080 72057594037927936 15 12331513308271821717504 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 993209 1048576 12331513308271821717504 37778931862957161709568 700965376 2147483648 391196 390814 (ep796 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep798 := BSN.sin_dyadic_bound_f 700965376 2147483648 2 1 1048576 391196 ep795 ep58 ep795 ep795 ep59 ep795 336222 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 700965376) qz15 0 1 ep795 ep58 ep795 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 700965376) qz16 0 1 ep795 ep59 ep795 rfl rfl rfl rfl) rfl rfl

noncomputable def ep799 := @Enclosure.Real.IsNear.sin_image qz145 qz443 Bool.false 24792057 262144 733 1048576 Bool.false 336222 1048576 1 195407 (@Enclosure.Real.IsNear.recentre' qz145 Bool.false 1549503573 16384000 68221 97703500 24792057 262144 733 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz146 (Real.log qz280) 136442 1000 0 1 363408 524288 1 195407 1549503573 16384000 68221 97703500 qz148 qz286 rfl) rfl) (Enclosure.sfrac_false_div 24792057 262144) (BSN.sin_reduce0 qz443 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 12331513308271821717504) qz287) 226375608064910080 72057594037927936 Bool.false 336222 1048576 15 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q0 24792057 262144 226375608064910080 72057594037927936 15 12331513308271821717504 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 336222 1048576 12331513308271821717504 37778931862957161709568 700965376 2147483648 391196 390814 (ep798 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep800 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz282 (Real.cos qz145)) (@HMul.hMul Real Real Real qz0 qz282 (@Neg.neg Real Real.instNeg (Real.sin qz145))) Bool.false 736419779095 1099511627776 107172765627655 214852268648824832 Bool.true 124646741505 549755813888 53522192884473 107426134324412416 (@Enclosure.Real.IsNear.mulLit_ff qz282 (Real.cos qz145) 741455 1048576 1 1048576 993209 1048576 144281907 204899090432 736419779095 1099511627776 107172765627655 214852268648824832 qz288 (@Enclosure.Real.IsNear.recentre' (Real.cos qz145) Bool.false 993209 1048576 144281907 204899090432 993209 1048576 144281907 204899090432 (ep797 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz282 (@Neg.neg Real Real.instNeg (Real.sin qz145)) 741455 1048576 1 1048576 168111 524288 144281907 204899090432 124646741505 549755813888 53522192884473 107426134324412416 qz288 (@Enclosure.Real.IsNear.neg (Real.sin qz145) Bool.false 168111 524288 144281907 204899090432 (@Enclosure.Real.IsNear.recentre' (Real.sin qz145) Bool.false 336222 1048576 144281907 204899090432 168111 524288 144281907 204899090432 (ep799 rfl rfl) rfl)) rfl)

noncomputable def ep801 := @ep792 736419779095 1099511627776 107172765627655 214852268648824832 Bool.true 124646741505 549755813888 53522192884473 107426134324412416 Bool.false 1835931406871 1835931406871 1099511627776 107172765627655 214852268648824832 Bool.true 124646741505 124646741505 549755813888 53522192884473 107426134324412416 (ep793 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 1) qz10 Bool.false 1 1 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 1) qz21)) (ep794 ep800) rfl rfl

noncomputable abbrev qz149 := (@HMul.hMul Real Real Real qz269 qz441 qz551)

noncomputable def ep802 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz8 qz144) (Complex.mk (@HMul.hMul Real Real Real qz0 qz289 (Real.cos qz149)) (@HMul.hMul Real Real Real qz0 qz289 (@Neg.neg Real Real.instNeg (Real.sin qz149)))) Bool.false 197386012775 549755813888 43737556160401 107426134324412416 Bool.false 248560052125 549755813888 43754073914111 107426134324412416 (BSN.cpow_neg_s_mk qz146 136442 1000 3 qz147 rfl)

noncomputable def ep803 := nat_lit 4315020842981120942940302001135420081

noncomputable def ep804 := BSN.sin_dyadic_bound_f 1441271253 2147483648 2 1 1048576 391196 ep803 ep58 ep803 ep803 ep59 ep803 652090 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1441271253) qz15 0 1 ep803 ep58 ep803 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1441271253) qz16 0 1 ep803 ep59 ep803 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz444 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 78589091) qz42)

noncomputable def ep805 := @Enclosure.Real.IsNear.cos_image qz149 qz444 Bool.false 78589091 524288 733 1048576 Bool.false 652090 1048576 1 195407 (@Enclosure.Real.IsNear.recentre' qz149 Bool.false 39294545569 262144000 68221 97703500 78589091 524288 733 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz146 qz551 136442 1000 0 1 575989 524288 1 195407 39294545569 262144000 68221 97703500 qz148 qz293 rfl) rfl) (Enclosure.sfrac_false_div 78589091 524288) (BSN.cos_reduce3 qz444 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 50710224067672305303552) qz43) 226375608064910080 72057594037927936 Bool.false 652090 1048576 23 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q3 78589091 524288 226375608064910080 72057594037927936 23 50710224067672305303552 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 652090 1048576 50710224067672305303552 75557863725914323419136 1441271253 2147483648 391196 390814 (ep804 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep806 := nat_lit 154192797509969255741650903349098866367004262957124852118673521648342986079841

noncomputable def ep807 := nat_lit 18619404875361503599582790098023357963001761096212148151298102760338046561

noncomputable def ep808 := nat_lit 462541153720157044217753544467100552385086785349182132059717968739508282146401

noncomputable def ep809 := BSN.cos_dyadic_bound_f 1441271253 2147483648 3 2 1048576 391196 ep806 ep79 ep807 ep808 ep81 ep807 821150 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1441271253) qz19 0 2 ep806 ep79 ep807 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1441271253) qz20 0 2 ep808 ep81 ep807 rfl rfl rfl rfl) rfl rfl

noncomputable def ep810 := @Enclosure.Real.IsNear.sin_image qz149 qz444 Bool.false 78589091 524288 733 1048576 Bool.true 821150 1048576 1 195407 (@Enclosure.Real.IsNear.recentre' qz149 Bool.false 39294545569 262144000 68221 97703500 78589091 524288 733 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz146 qz551 136442 1000 0 1 575989 524288 1 195407 39294545569 262144000 68221 97703500 qz148 qz293 rfl) rfl) (Enclosure.sfrac_false_div 78589091 524288) (BSN.sin_reduce3 qz444 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 50710224067672305303552) qz43) 226375608064910080 72057594037927936 Bool.false 821150 1048576 23 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q3 78589091 524288 226375608064910080 72057594037927936 23 50710224067672305303552 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 821150 1048576 50710224067672305303552 75557863725914323419136 1441271253 2147483648 391196 390814 (ep809 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep811 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz289 (Real.cos qz149)) (@HMul.hMul Real Real Real qz0 qz289 (@Neg.neg Real Real.instNeg (Real.sin qz149))) Bool.false 197386012775 549755813888 43737556160401 107426134324412416 Bool.false 248560052125 549755813888 43754073914111 107426134324412416 (@Enclosure.Real.IsNear.mulLit_ff qz289 (Real.cos qz149) 605395 1048576 1 1048576 326045 524288 144281907 204899090432 197386012775 549755813888 43737556160401 107426134324412416 qz294 (@Enclosure.Real.IsNear.recentre' (Real.cos qz149) Bool.false 652090 1048576 144281907 204899090432 326045 524288 144281907 204899090432 (ep805 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz289 (@Neg.neg Real Real.instNeg (Real.sin qz149)) 605395 1048576 1 1048576 410575 524288 144281907 204899090432 248560052125 549755813888 43754073914111 107426134324412416 qz294 (@Enclosure.Real.IsNear.neg (Real.sin qz149) Bool.true 410575 524288 144281907 204899090432 (@Enclosure.Real.IsNear.recentre' (Real.sin qz149) Bool.true 821150 1048576 144281907 204899090432 410575 524288 144281907 204899090432 (ep810 rfl rfl) rfl)) rfl)

noncomputable def ep812 := @ep789 197386012775 549755813888 43737556160401 107426134324412416 Bool.false 248560052125 549755813888 43754073914111 107426134324412416 Bool.false ep790 2230703432421 1099511627776 194647877948457 214852268648824832 Bool.false 68122062931454653890560 30978327655 137438953472 12159533349823 13428266790551552 (ep791 (BSN.head_sum_c_succ qz143 2 3 rfl rfl) (ep801 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep802 ep811) rfl rfl

noncomputable abbrev qz150 := (@HMul.hMul Real Real Real qz269 qz441 qz552)

noncomputable def ep813 := @Enclosure.Complex.IsNear.of_eq qz651 (Complex.mk (@HMul.hMul Real Real Real qz0 qz295 (Real.cos qz150)) (@HMul.hMul Real Real Real qz0 qz295 (@Neg.neg Real Real.instNeg (Real.sin qz150)))) Bool.false 436621495017 1099511627776 75808005648153 214852268648824832 Bool.true 334053132059 1099511627776 75769777395115 214852268648824832 (BSN.cpow_neg_s_mk qz146 136442 1000 4 qz147 rfl)

noncomputable def ep814 := nat_lit 138253845932458374874815337210966712694435648564332196224362550603886798831616

noncomputable def ep815 := nat_lit 14969348644931008899452658144144147519195055637041654323787504687394062336

noncomputable def ep816 := nat_lit 414731599100085262606647106316611849788268555581722505364440076802285608370176

noncomputable def ep817 := BSN.cos_dyadic_bound_f 1402491904 2147483648 3 2 1048576 391196 ep814 ep79 ep815 ep816 ep81 ep815 832791 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1402491904) qz19 0 2 ep814 ep79 ep815 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1402491904) qz20 0 2 ep816 ep81 ep815 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz445 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 99168365) qz42)

noncomputable def ep818 := @Enclosure.Real.IsNear.cos_image qz150 qz445 Bool.false 99168365 524288 733 1048576 Bool.false 832791 1048576 1 195407 (@Enclosure.Real.IsNear.recentre' qz150 Bool.false 49584182557 262144000 68221 97703500 99168365 524288 733 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz146 qz552 136442 1000 0 1 726817 524288 1 195407 49584182557 262144000 68221 97703500 qz148 qz299 rfl) rfl) (Enclosure.sfrac_false_div 99168365 524288) (BSN.cos_reduce0 qz445 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 49345797013853679124480) qz43) 226375608064910080 72057594037927936 Bool.false 832791 1048576 30 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q0 99168365 524288 226375608064910080 72057594037927936 30 49345797013853679124480 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 832791 1048576 49345797013853679124480 75557863725914323419136 1402491904 2147483648 391196 390814 (ep817 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep819 := nat_lit 3869024249721240620212570566380486656

noncomputable def ep820 := BSN.sin_dyadic_bound_f 1402491904 2147483648 2 1 1048576 391196 ep819 ep58 ep819 ep819 ep59 ep819 637157 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1402491904) qz15 0 1 ep819 ep58 ep819 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1402491904) qz16 0 1 ep819 ep59 ep819 rfl rfl rfl rfl) rfl rfl

noncomputable def ep821 := @Enclosure.Real.IsNear.sin_image qz150 qz445 Bool.false 99168365 524288 733 1048576 Bool.false 637157 1048576 1 195407 (@Enclosure.Real.IsNear.recentre' qz150 Bool.false 49584182557 262144000 68221 97703500 99168365 524288 733 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz146 qz552 136442 1000 0 1 726817 524288 1 195407 49584182557 262144000 68221 97703500 qz148 qz299 rfl) rfl) (Enclosure.sfrac_false_div 99168365 524288) (BSN.sin_reduce0 qz445 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 49345797013853679124480) qz43) 226375608064910080 72057594037927936 Bool.false 637157 1048576 30 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q0 99168365 524288 226375608064910080 72057594037927936 30 49345797013853679124480 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 637157 1048576 49345797013853679124480 75557863725914323419136 1402491904 2147483648 391196 390814 (ep820 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep822 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz295 (Real.cos qz150)) (@HMul.hMul Real Real Real qz0 qz295 (@Neg.neg Real Real.instNeg (Real.sin qz150))) Bool.false 436621495017 1099511627776 75808005648153 214852268648824832 Bool.true 334053132059 1099511627776 75769777395115 214852268648824832 (@Enclosure.Real.IsNear.mulLit_ff qz295 (Real.cos qz150) 524287 1048576 1 1048576 832791 1048576 144281907 204899090432 436621495017 1099511627776 75808005648153 214852268648824832 qz300 (@Enclosure.Real.IsNear.recentre' (Real.cos qz150) Bool.false 832791 1048576 144281907 204899090432 832791 1048576 144281907 204899090432 (ep818 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz295 (@Neg.neg Real Real.instNeg (Real.sin qz150)) 524287 1048576 1 1048576 637157 1048576 144281907 204899090432 334053132059 1099511627776 75769777395115 214852268648824832 qz300 (@Enclosure.Real.IsNear.neg (Real.sin qz150) Bool.false 637157 1048576 144281907 204899090432 (@Enclosure.Real.IsNear.recentre' (Real.sin qz150) Bool.false 637157 1048576 144281907 204899090432 637157 1048576 144281907 204899090432 (ep821 rfl rfl) rfl)) rfl)

noncomputable def ep823 := @ep786 436621495017 1099511627776 75808005648153 214852268648824832 Bool.true 334053132059 1099511627776 75769777395115 214852268648824832 Bool.false ep787 1333662463719 549755813888 135227941798305 107426134324412416 Bool.true 11850881408505445613568 86226510819 1099511627776 270322310992283 214852268648824832 (ep788 (BSN.head_sum_c_succ qz143 3 4 rfl rfl) (ep812 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep813 ep822) rfl rfl

noncomputable abbrev qz151 := (@HMul.hMul Real Real Real qz269 qz441 qz553)

noncomputable def ep824 := @Enclosure.Complex.IsNear.of_eq qz650 (Complex.mk (@HMul.hMul Real Real Real qz0 qz301 (Real.cos qz151)) (@HMul.hMul Real Real Real qz0 qz301 (@Neg.neg Real Real.instNeg (Real.sin qz151)))) Bool.false 467244606367 1099511627776 67853970680903 214852268648824832 Bool.false 76594762769 549755813888 16930775822771 53713067162206208 (BSN.cpow_neg_s_mk qz146 136442 1000 5 qz147 rfl)

noncomputable def ep825 := nat_lit 3384859505521550207687678558621497185584373502503074039535490538403380631668545

noncomputable def ep826 := nat_lit 2765469409712732092303958860175275117076961588090998341476971082251463001921

noncomputable def ep827 := nat_lit 8860630802083572787223046958235065993007615521127332296706750599780446904747841

noncomputable def ep828 := BSN.sin_dyadic_bound_f 2692905463 2147483648 3 2 1048576 391196 ep825 ep72 ep826 ep827 ep75 ep826 996391 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2692905463) qz15 0 2 ep825 ep72 ep826 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2692905463) qz16 0 2 ep827 ep75 ep826 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz446 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 115130851) qz42)

noncomputable def ep829 := @Enclosure.Real.IsNear.cos_image qz151 qz446 Bool.false 115130851 524288 733 1048576 Bool.false 996391 1048576 1 195407 (@Enclosure.Real.IsNear.recentre' qz151 Bool.false 1798919549 8192000 68221 97703500 115130851 524288 733 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz146 qz553 136442 1000 0 1 843808 524288 1 195407 1798919549 8192000 68221 97703500 qz148 qz305 rfl) rfl) (Enclosure.sfrac_false_div 115130851 524288) (BSN.cos_reduce3 qz446 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 94748187840494029504512) qz43) 226375608064910080 72057594037927936 Bool.false 996391 1048576 34 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q3 115130851 524288 226375608064910080 72057594037927936 34 94748187840494029504512 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 996391 1048576 94748187840494029504512 75557863725914323419136 2692905463 2147483648 391196 390814 (ep828 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep830 := nat_lit 1881706600582955774089734292060909669821130595429748243449262286260656556705601

noncomputable def ep831 := nat_lit 5639588862929441858084594958462378459229237863113062733664832916617466744112961

noncomputable def ep832 := BSN.cos_dyadic_bound_f 2692905463 2147483648 3 2 1048576 391196 ep830 ep79 ep826 ep831 ep81 ep826 326674 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2692905463) qz19 0 2 ep830 ep79 ep826 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2692905463) qz20 0 2 ep831 ep81 ep826 rfl rfl rfl rfl) rfl rfl

noncomputable def ep833 := @Enclosure.Real.IsNear.sin_image qz151 qz446 Bool.false 115130851 524288 733 1048576 Bool.true 326674 1048576 1 195407 (@Enclosure.Real.IsNear.recentre' qz151 Bool.false 1798919549 8192000 68221 97703500 115130851 524288 733 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz146 qz553 136442 1000 0 1 843808 524288 1 195407 1798919549 8192000 68221 97703500 qz148 qz305 rfl) rfl) (Enclosure.sfrac_false_div 115130851 524288) (BSN.sin_reduce3 qz446 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 94748187840494029504512) qz43) 226375608064910080 72057594037927936 Bool.false 326674 1048576 34 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q3 115130851 524288 226375608064910080 72057594037927936 34 94748187840494029504512 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 326674 1048576 94748187840494029504512 75557863725914323419136 2692905463 2147483648 391196 390814 (ep832 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep834 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz301 (Real.cos qz151)) (@HMul.hMul Real Real Real qz0 qz301 (@Neg.neg Real Real.instNeg (Real.sin qz151))) Bool.false 467244606367 1099511627776 67853970680903 214852268648824832 Bool.false 76594762769 549755813888 16930775822771 53713067162206208 (@Enclosure.Real.IsNear.mulLit_ff qz301 (Real.cos qz151) 468937 1048576 1 1048576 996391 1048576 144281907 204899090432 467244606367 1099511627776 67853970680903 214852268648824832 qz306 (@Enclosure.Real.IsNear.recentre' (Real.cos qz151) Bool.false 996391 1048576 144281907 204899090432 996391 1048576 144281907 204899090432 (ep829 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz301 (@Neg.neg Real Real.instNeg (Real.sin qz151)) 468937 1048576 1 1048576 163337 524288 144281907 204899090432 76594762769 549755813888 16930775822771 53713067162206208 qz306 (@Enclosure.Real.IsNear.neg (Real.sin qz151) Bool.true 163337 524288 144281907 204899090432 (@Enclosure.Real.IsNear.recentre' (Real.sin qz151) Bool.true 326674 1048576 144281907 204899090432 163337 524288 144281907 204899090432 (ep833 rfl rfl) rfl)) rfl)

noncomputable def ep835 := @ep783 467244606367 1099511627776 67853970680903 214852268648824832 Bool.false 76594762769 549755813888 16930775822771 53713067162206208 Bool.false ep784 3134569533805 1099511627776 338309854277513 214852268648824832 Bool.false 36813306657237968617472 66963014719 1099511627776 338045414283367 214852268648824832 (ep785 (BSN.head_sum_c_succ qz143 4 5 rfl rfl) (ep823 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep824 ep834) rfl rfl

noncomputable abbrev qz152 := (@HMul.hMul Real Real Real qz269 qz441 qz555)

noncomputable def ep836 := @Enclosure.Complex.IsNear.of_eq qz649 (Complex.mk (@HMul.hMul Real Real Real qz0 qz307 (Real.cos qz152)) (@HMul.hMul Real Real Real qz0 qz307 (@Neg.neg Real Real.instNeg (Real.sin qz152)))) Bool.false 377151725607 1099511627776 62020008592551 214852268648824832 Bool.false 243400154373 1099511627776 61958954457029 214852268648824832 (BSN.cpow_neg_s_mk qz146 136442 1000 6 qz147 rfl)

noncomputable def ep837 := @Enclosure.Real.IsNear.mulLit_ff qz146 qz555 136442 1000 0 1 4034681531866359 2251799813685248 500000000195407 97703500000000000000 275250008785454877339 1125899906842624000 34110500013330860947 48851750000000000000000 qz148 (BSN.isNear_log_sfrac 6 1 4034681531866359 2251799813685248 500000000195407 97703500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz556) Bool.false 33845361775666394038272 18889465931478580854784 1000000000390814 195407000000000000000 4034681531866359 2251799813685248 500000000195407 97703500000000000000 (BSN.log_rat_reduce_isNear 6 1 2 12 8 212580 524288 24973259072661432 36028797018963968 195407 1000000000000000 rfl rfl rfl rfl (ep122 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep838 := nat_lit 1355623625989327179279200175746651030373767045559460747695503410633656874700385

noncomputable def ep839 := nat_lit 444008438234424883379085756939605081033210607996477823917129332557792546401

noncomputable def ep840 := nat_lit 3549723959167286876872434321444279052276288492623736232249500247025912531521121

noncomputable def ep841 := BSN.sin_dyadic_bound_f 2142515157 2147483648 3 2 1048576 391196 ep838 ep72 ep839 ep840 ep75 ep839 881033 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2142515157) qz15 0 2 ep838 ep72 ep839 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2142515157) qz16 0 2 ep840 ep75 ep839 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz447 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 128173273) qz42)

noncomputable def ep842 := @Enclosure.Real.IsNear.cos_image qz152 qz447 Bool.false 128173273 524288 367 524288 Bool.false 881033 1048576 1 195407 (@Enclosure.Real.IsNear.recentre' qz152 Bool.false 275250008785454877339 1125899906842624000 34110500013330860947 48851750000000000000000 128173273 524288 367 524288 (ep837 rfl) rfl) (Enclosure.sfrac_false_div 128173273 524288) (BSN.cos_reduce3 qz447 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 75383050517005106937856) qz43) 226375608064910080 72057594037927936 Bool.false 881033 1048576 38 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q3 128173273 524288 226375608064910080 72057594037927936 38 75383050517005106937856 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 881033 1048576 75383050517005106937856 75557863725914323419136 2142515157 2147483648 391196 390814 (ep841 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep843 := nat_lit 753321573744397066214390802417890396910329785581032183308131730055390615965281

noncomputable def ep844 := nat_lit 2259076704356722348876414235739791980568922935527103594276560931501056262803041

noncomputable def ep845 := BSN.cos_dyadic_bound_f 2142515157 2147483648 3 2 1048576 391196 ep843 ep79 ep839 ep844 ep81 ep839 568587 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2142515157) qz19 0 2 ep843 ep79 ep839 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2142515157) qz20 0 2 ep844 ep81 ep839 rfl rfl rfl rfl) rfl rfl

noncomputable def ep846 := @Enclosure.Real.IsNear.sin_image qz152 qz447 Bool.false 128173273 524288 367 524288 Bool.true 568587 1048576 1 195407 (@Enclosure.Real.IsNear.recentre' qz152 Bool.false 275250008785454877339 1125899906842624000 34110500013330860947 48851750000000000000000 128173273 524288 367 524288 (ep837 rfl) rfl) (Enclosure.sfrac_false_div 128173273 524288) (BSN.sin_reduce3 qz447 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 75383050517005106937856) qz43) 226375608064910080 72057594037927936 Bool.false 568587 1048576 38 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q3 128173273 524288 226375608064910080 72057594037927936 38 75383050517005106937856 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 568587 1048576 75383050517005106937856 75557863725914323419136 2142515157 2147483648 391196 390814 (ep845 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep847 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz307 (Real.cos qz152)) (@HMul.hMul Real Real Real qz0 qz307 (@Neg.neg Real Real.instNeg (Real.sin qz152))) Bool.false 377151725607 1099511627776 62020008592551 214852268648824832 Bool.false 243400154373 1099511627776 61958954457029 214852268648824832 (@Enclosure.Real.IsNear.mulLit_ff qz307 (Real.cos qz152) 428079 1048576 1 1048576 881033 1048576 72238657 102449545216 377151725607 1099511627776 62020008592551 214852268648824832 qz311 (@Enclosure.Real.IsNear.recentre' (Real.cos qz152) Bool.false 881033 1048576 72238657 102449545216 881033 1048576 72238657 102449545216 (ep842 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz307 (@Neg.neg Real Real.instNeg (Real.sin qz152)) 428079 1048576 1 1048576 568587 1048576 72238657 102449545216 243400154373 1099511627776 61958954457029 214852268648824832 qz311 (@Enclosure.Real.IsNear.neg (Real.sin qz152) Bool.true 568587 1048576 72238657 102449545216 (@Enclosure.Real.IsNear.recentre' (Real.sin qz152) Bool.true 568587 1048576 72238657 102449545216 568587 1048576 72238657 102449545216 (ep846 rfl rfl) rfl)) rfl)

noncomputable def ep848 := @ep780 377151725607 1099511627776 62020008592551 214852268648824832 Bool.false 243400154373 1099511627776 61958954457029 214852268648824832 Bool.false ep781 877930314853 274877906944 25020616429379 13428266790551552 Bool.false 341247913250062851899392 77590792273 274877906944 100001092185099 53713067162206208 (ep782 (BSN.head_sum_c_succ qz143 5 6 rfl rfl) (ep835 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep836 ep847) rfl rfl

noncomputable abbrev qz153 := (@HMul.hMul Real Real Real qz269 qz441 qz557)

noncomputable def ep849 := @Enclosure.Complex.IsNear.of_eq qz648 (Complex.mk (@HMul.hMul Real Real Real qz0 qz312 (Real.cos qz153)) (@HMul.hMul Real Real Real qz0 qz312 (@Neg.neg Real Real.instNeg (Real.sin qz153)))) Bool.true 1981625 134217728 14317029954771 53713067162206208 Bool.true 415259426875 1099511627776 57464858517789 214852268648824832 (BSN.cpow_neg_s_mk qz146 136442 1000 7 qz147 rfl)

noncomputable def ep850 := @Enclosure.Real.IsNear.mulLit_ff qz146 qz557 136442 1000 0 1 4381796493761783 2251799813685248 500000000195407 97703500000000000000 298930538600922598043 1125899906842624000 34110500013330860947 48851750000000000000000 qz148 (BSN.isNear_log_sfrac 7 1 4381796493761783 2251799813685248 500000000195407 97703500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz558) Bool.false 36757173121942042968064 18889465931478580854784 1000000000390814 195407000000000000000 4381796493761783 2251799813685248 500000000195407 97703500000000000000 (BSN.log_rat_reduce_isNear 7 1 2 14 8 293399 524288 24973259072661432 36028797018963968 195407 1000000000000000 rfl rfl rfl rfl (ep133 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep851 := BSN.sin_dyadic_bound_f 83909367 2147483648 1 0 1048576 391196 0 1 1 0 1 1 40960 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 83909367) qz15 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 83909367) qz16 0 0 rfl) rfl rfl

noncomputable abbrev qz448 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 139200379) qz42)

noncomputable def ep852 := @Enclosure.Real.IsNear.cos_image qz153 qz448 Bool.false 139200379 524288 367 524288 Bool.true 40960 1048576 1 195407 (@Enclosure.Real.IsNear.recentre' qz153 Bool.false 298930538600922598043 1125899906842624000 34110500013330860947 48851750000000000000000 139200379 524288 367 524288 (ep850 rfl) rfl) (Enclosure.sfrac_false_div 139200379 524288) (BSN.cos_reduce1 qz448 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 2952298423505783881728) qz43) 226375608064910080 72057594037927936 Bool.false 40960 1048576 42 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q1 139200379 524288 226375608064910080 72057594037927936 42 2952298423505783881728 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 40960 1048576 2952298423505783881728 75557863725914323419136 83909367 2147483648 391196 390814 (ep851 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep853 := BSN.cos_dyadic_bound_f 83909367 2147483648 1 0 1048576 391196 0 1 1 0 1 1 1047775 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 83909367) qz19 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 83909367) qz20 0 0 rfl) rfl rfl

noncomputable def ep854 := @Enclosure.Real.IsNear.sin_image qz153 qz448 Bool.false 139200379 524288 367 524288 Bool.false 1047775 1048576 1 195407 (@Enclosure.Real.IsNear.recentre' qz153 Bool.false 298930538600922598043 1125899906842624000 34110500013330860947 48851750000000000000000 139200379 524288 367 524288 (ep850 rfl) rfl) (Enclosure.sfrac_false_div 139200379 524288) (BSN.sin_reduce1 qz448 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 2952298423505783881728) qz43) 226375608064910080 72057594037927936 Bool.false 1047775 1048576 42 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q1 139200379 524288 226375608064910080 72057594037927936 42 2952298423505783881728 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1047775 1048576 2952298423505783881728 75557863725914323419136 83909367 2147483648 391196 390814 (ep853 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep855 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz312 (Real.cos qz153)) (@HMul.hMul Real Real Real qz0 qz312 (@Neg.neg Real Real.instNeg (Real.sin qz153))) Bool.true 1981625 134217728 14317029954771 53713067162206208 Bool.true 415259426875 1099511627776 57464858517789 214852268648824832 (@Enclosure.Real.IsNear.mulLit_ft qz312 (Real.cos qz153) 396325 1048576 1 1048576 5 128 72238657 102449545216 1981625 134217728 14317029954771 53713067162206208 qz317 (@Enclosure.Real.IsNear.recentre' (Real.cos qz153) Bool.true 40960 1048576 72238657 102449545216 5 128 72238657 102449545216 (ep852 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz312 (@Neg.neg Real Real.instNeg (Real.sin qz153)) 396325 1048576 1 1048576 1047775 1048576 72238657 102449545216 415259426875 1099511627776 57464858517789 214852268648824832 qz317 (@Enclosure.Real.IsNear.neg (Real.sin qz153) Bool.false 1047775 1048576 72238657 102449545216 (@Enclosure.Real.IsNear.recentre' (Real.sin qz153) Bool.false 1047775 1048576 72238657 102449545216 1047775 1048576 72238657 102449545216 (ep854 rfl rfl) rfl)) rfl)

noncomputable def ep856 := @ep778 1981625 134217728 14317029954771 53713067162206208 Bool.true 415259426875 1099511627776 57464858517789 214852268648824832 Bool.false 117289107269546409984 873871946853 274877906944 114399495672287 53713067162206208 Bool.true 28833663785649309745152 104896257783 1099511627776 457469227258185 214852268648824832 (ep779 (BSN.head_sum_c_succ qz143 6 7 rfl rfl) (ep848 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep849 ep855) rfl rfl

noncomputable abbrev qz154 := (@HMul.hMul Real Real Real qz269 qz441 qz560)

noncomputable def ep857 := @Enclosure.Complex.IsNear.of_eq qz647 (Complex.mk (@HMul.hMul Real Real Real qz0 qz318 (Real.cos qz154)) (@HMul.hMul Real Real Real qz0 qz318 (@Neg.neg Real Real.instNeg (Real.sin qz154)))) Bool.false 216590947391 1099511627776 53603506036127 214852268648824832 Bool.true 20175334067 68719476736 6707436340981 26856533581103104 (BSN.cpow_neg_s_mk qz146 136442 1000 8 qz147 rfl)

noncomputable def ep858 := @Enclosure.Real.IsNear.mulLit_ff qz146 qz560 136442 1000 0 1 9364972152248037 4503599627370496 1000000000586221 195407000000000000000 638887765198513332177 2251799813685248000 68221000039992582841 97703500000000000000000 qz148 (BSN.isNear_log_sfrac 8 1 9364972152248037 4503599627370496 1000000000586221 195407000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz561) Bool.false 39279540158062550581248 18889465931478580854784 1000000000586221 195407000000000000000 9364972152248037 4503599627370496 1000000000586221 195407000000000000000 (BSN.log_rat_reduce_isNear 8 1 3 16 16 0 524288 24973259072661432 36028797018963968 195407 1000000000000000 rfl rfl rfl rfl (ep147 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep859 := nat_lit 700774670939596730895245583234290372436542405016541704899985509099572335476736

noncomputable def ep860 := nat_lit 384257981795400481341978565148420520194773571676314631940521142684961734656

noncomputable def ep861 := nat_lit 2101555496855199391723052792572574276269237667906272485436075485013347082960896

noncomputable def ep862 := BSN.cos_dyadic_bound_f 2104155648 2147483648 3 2 1048576 391196 ep859 ep79 ep860 ep861 ep81 ep860 584233 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2104155648) qz19 0 2 ep859 ep79 ep860 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2104155648) qz20 0 2 ep861 ep81 ep860 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz449 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 297505299) qz23)

noncomputable def ep863 := @Enclosure.Real.IsNear.cos_image qz154 qz449 Bool.false 297505299 1048576 733 1048576 Bool.false 584233 1048576 1 195407 (@Enclosure.Real.IsNear.recentre' qz154 Bool.false 638887765198513332177 2251799813685248000 68221000039992582841 97703500000000000000000 297505299 1048576 733 1048576 (ep858 rfl) rfl) (Enclosure.sfrac_false_div 297505299 1048576) (BSN.cos_reduce0 qz449 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 148066790539928511971328) qz24) 226375608064910080 72057594037927936 Bool.false 584233 1048576 45 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q0 297505299 1048576 226375608064910080 72057594037927936 45 148066790539928511971328 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 584233 1048576 148066790539928511971328 151115727451828646838272 2104155648 2147483648 391196 390814 (ep862 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep864 := nat_lit 1261087001305837795226368466969603933969620510172434017114421499465082234470400

noncomputable def ep865 := nat_lit 3302224776211430243861173257719674765268690750383184583038438321510868295090176

noncomputable def ep866 := BSN.sin_dyadic_bound_f 2104155648 2147483648 3 2 1048576 391196 ep864 ep72 ep860 ep865 ep75 ep860 870736 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2104155648) qz15 0 2 ep864 ep72 ep860 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2104155648) qz16 0 2 ep865 ep75 ep860 rfl rfl rfl rfl) rfl rfl

noncomputable def ep867 := @Enclosure.Real.IsNear.sin_image qz154 qz449 Bool.false 297505299 1048576 733 1048576 Bool.false 870736 1048576 1 195407 (@Enclosure.Real.IsNear.recentre' qz154 Bool.false 638887765198513332177 2251799813685248000 68221000039992582841 97703500000000000000000 297505299 1048576 733 1048576 (ep858 rfl) rfl) (Enclosure.sfrac_false_div 297505299 1048576) (BSN.sin_reduce0 qz449 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 148066790539928511971328) qz24) 226375608064910080 72057594037927936 Bool.false 870736 1048576 45 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q0 297505299 1048576 226375608064910080 72057594037927936 45 148066790539928511971328 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 870736 1048576 148066790539928511971328 151115727451828646838272 2104155648 2147483648 391196 390814 (ep866 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep868 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz318 (Real.cos qz154)) (@HMul.hMul Real Real Real qz0 qz318 (@Neg.neg Real Real.instNeg (Real.sin qz154))) Bool.false 216590947391 1099511627776 53603506036127 214852268648824832 Bool.true 20175334067 68719476736 6707436340981 26856533581103104 (@Enclosure.Real.IsNear.mulLit_ff qz318 (Real.cos qz154) 370727 1048576 1 1048576 584233 1048576 144281907 204899090432 216590947391 1099511627776 53603506036127 214852268648824832 qz322 (@Enclosure.Real.IsNear.recentre' (Real.cos qz154) Bool.false 584233 1048576 144281907 204899090432 584233 1048576 144281907 204899090432 (ep863 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz318 (@Neg.neg Real Real.instNeg (Real.sin qz154)) 370727 1048576 1 1048576 54421 65536 144281907 204899090432 20175334067 68719476736 6707436340981 26856533581103104 qz322 (@Enclosure.Real.IsNear.neg (Real.sin qz154) Bool.false 54421 65536 144281907 204899090432 (@Enclosure.Real.IsNear.recentre' (Real.sin qz154) Bool.false 870736 1048576 144281907 204899090432 54421 65536 144281907 204899090432 (ep867 rfl rfl) rfl)) rfl)

noncomputable def ep869 := @ep776 216590947391 1099511627776 53603506036127 214852268648824832 Bool.true 20175334067 68719476736 6707436340981 26856533581103104 Bool.false 1020368433033980288172032 3712078734803 1099511627776 511201488725275 214852268648824832 Bool.true 29391430347344083681280 427701602855 1099511627776 511128717986033 214852268648824832 (ep777 (BSN.head_sum_c_succ qz143 7 8 rfl rfl) (ep856 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep857 ep868) rfl rfl

theorem EMRow46.d13 : Enclosure.Complex.IsNear qz142 Bool.false 3712078734803 1099511627776 511201488725275 214852268648824832 Bool.true 427701602855 1099511627776 511128717986033 214852268648824832 := ep775 (BSN.head_sum_c_succ qz143 8 9 rfl rfl) (ep869 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable abbrev qz155 := (BSN.headSumC qz439 17)

noncomputable abbrev qz653 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 16) qz144)

noncomputable def ep870 := @Enclosure.Complex.IsNear.of_eq qz155 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz143 16) qz653) Bool.false 4552428540229 1099511627776 859233708580197 214852268648824832 Bool.true 124410818961 1099511627776 859379757726067 214852268648824832

noncomputable def ep871 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz143 16) qz653 Bool.false 4480604503945 1099511627776 821357533178473 214852268648824832 Bool.false 35229108015 274877906944 410679670444315 107426134324412416 Bool.false

noncomputable def ep872 := nat_lit 1251362028650276822450176

noncomputable abbrev qz654 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 15) qz144)

noncomputable def ep873 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz143 16) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz143 15) qz654) Bool.false 4480604503945 1099511627776 821357533178473 214852268648824832 Bool.false 35229108015 274877906944 410679670444315 107426134324412416

noncomputable def ep874 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz143 15) qz654 Bool.false 4382087810347 1099511627776 782170351923139 214852268648824832 Bool.true 62667028857 549755813888 24439096811317 6714133395275776 Bool.false

noncomputable def ep875 := nat_lit 2463238375776521981788160

noncomputable abbrev qz655 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 14) qz144)

noncomputable def ep876 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz143 15) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz143 14) qz655) Bool.false 4382087810347 1099511627776 782170351923139 214852268648824832 Bool.true 62667028857 549755813888 24439096811317 6714133395275776

noncomputable def ep877 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz143 14) qz655 Bool.false 1121791581103 274877906944 370804091353419 107426134324412416 Bool.false 74546109289 549755813888 185342711611305 53713067162206208 Bool.true

noncomputable abbrev qz656 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 13) qz144)

noncomputable def ep878 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz143 14) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz143 13) qz656) Bool.false 1121791581103 274877906944 370804091353419 107426134324412416 Bool.false 74546109289 549755813888 185342711611305 53713067162206208

noncomputable def ep879 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz143 13) qz656 Bool.false 4583383078201 1099511627776 699526063302001 214852268648824832 Bool.true 17535092243 137438953472 349579471688893 107426134324412416 Bool.true

noncomputable def ep880 := nat_lit 4933691549455889006067712

noncomputable abbrev qz657 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 12) qz144)

noncomputable def ep881 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz143 13) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz143 12) qz657) Bool.false 4583383078201 1099511627776 699526063302001 214852268648824832 Bool.true 17535092243 137438953472 349579471688893 107426134324412416

noncomputable def ep882 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz143 12) qz657 Bool.false 2137788427769 549755813888 163898591008519 53713067162206208 Bool.true 108865304273 549755813888 2560062310067 839266674409472 Bool.false

noncomputable def ep883 := nat_lit 2519741494516877505855488

noncomputable abbrev qz658 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 11) qz144)

noncomputable def ep884 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz143 12) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz143 11) qz658) Bool.false 2137788427769 549755813888 163898591008519 53713067162206208 Bool.true 108865304273 549755813888 2560062310067 839266674409472

noncomputable def ep885 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz143 11) qz658 Bool.false 3976758853889 1099511627776 609793794586871 214852268648824832 Bool.true 37085018993 549755813888 304835670906643 107426134324412416 Bool.false

noncomputable def ep886 := nat_lit 4701046468113977980223488

noncomputable abbrev qz659 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 10) qz144)

noncomputable def ep887 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz143 11) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz143 10) qz659) Bool.false 3976758853889 1099511627776 609793794586871 214852268648824832 Bool.true 37085018993 549755813888 304835670906643 107426134324412416

noncomputable def ep888 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz143 10) qz659 Bool.false 3629079829253 1099511627776 561746468115473 214852268648824832 Bool.true 35360093015 549755813888 70228358907091 26856533581103104 Bool.false

noncomputable abbrev qz660 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 9) qz144)

noncomputable def ep889 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz143 10) (@HAdd.hAdd Complex Complex Complex qz4 qz142 qz660) Bool.false 3629079829253 1099511627776 561746468115473 214852268648824832 Bool.true 35360093015 549755813888 70228358907091 26856533581103104

noncomputable def ep890 := @Enclosure.Complex.IsNear.addLitP qz142 qz660 Bool.false 3712078734803 1099511627776 511201488725275 214852268648824832 Bool.true 427701602855 1099511627776 511128717986033 214852268648824832 Bool.true

noncomputable def ep891 := nat_lit 1995107735195507086065664

noncomputable abbrev qz156 := (@HMul.hMul Real Real Real qz269 qz441 qz570)

noncomputable def ep892 := @Enclosure.Complex.IsNear.of_eq qz660 (Complex.mk (@HMul.hMul Real Real Real qz0 qz323 (Real.cos qz156)) (@HMul.hMul Real Real Real qz0 qz323 (@Neg.neg Real Real.instNeg (Real.sin qz156)))) Bool.true 41499452775 549755813888 25272489695099 107426134324412416 Bool.false 356981416825 1099511627776 50698153270695 214852268648824832 (BSN.cpow_neg_s_mk qz146 136442 1000 9 qz147 rfl)

noncomputable def ep893 := @Enclosure.Real.IsNear.mulLit_ff qz146 qz570 136442 1000 0 1 9895417793173221 4503599627370496 1000000000586221 195407000000000000000 675075297268070309841 2251799813685248000 68221000039992582841 97703500000000000000000 qz148 (BSN.isNear_log_sfrac 9 1 9895417793173221 4503599627370496 1000000000586221 195407000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz571) Bool.false 41504390431577613533184 18889465931478580854784 1000000000586221 195407000000000000000 9895417793173221 4503599627370496 1000000000586221 195407000000000000000 (BSN.log_rat_reduce_isNear 9 1 3 18 16 61752 524288 24973259072661432 36028797018963968 195407 1000000000000000 rfl rfl rfl rfl (ep178 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep894 := nat_lit 2472024969907422443113057700826012873762457234917599819123581858405494980862561

noncomputable def ep895 := nat_lit 4768383165036304083800207840500505590937922320768589152794164159337281872481

noncomputable def ep896 := nat_lit 7406538143392194721171572686797037610105495860111262279065157246897810378842721

noncomputable def ep897 := BSN.cos_dyadic_bound_f 2882679723 2147483648 3 2 1048576 391196 ep894 ep79 ep895 ep896 ep81 ep895 237462 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2882679723) qz19 0 2 ep894 ep79 ep895 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2882679723) qz20 0 2 ep896 ep81 ep895 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz450 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 314356431) qz23)

noncomputable def ep898 := @Enclosure.Real.IsNear.cos_image qz156 qz450 Bool.false 314356431 1048576 367 524288 Bool.true 237462 1048576 1 195407 (@Enclosure.Real.IsNear.recentre' qz156 Bool.false 675075297268070309841 2251799813685248000 68221000039992582841 97703500000000000000000 314356431 1048576 367 524288 (ep893 rfl) rfl) (Enclosure.sfrac_false_div 314356431 1048576) (BSN.cos_reduce2 qz450 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 202850551988290303557632) qz24) 226375608064910080 72057594037927936 Bool.false 237462 1048576 47 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q2 314356431 1048576 226375608064910080 72057594037927936 47 202850551988290303557632 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 237462 1048576 202850551988290303557632 151115727451828646838272 2882679723 2147483648 391196 390814 (ep897 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep899 := nat_lit 4445830239301331354336463695214422768299672684995064803100212013802421140054625

noncomputable def ep900 := nat_lit 11636120863521999530936014103343630241256671824562972959015079008462652148540001

noncomputable def ep901 := BSN.sin_dyadic_bound_f 2882679723 2147483648 3 2 1048576 391196 ep899 ep72 ep895 ep900 ep75 ep895 1021333 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2882679723) qz15 0 2 ep899 ep72 ep895 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2882679723) qz16 0 2 ep900 ep75 ep895 rfl rfl rfl rfl) rfl rfl

noncomputable def ep902 := @Enclosure.Real.IsNear.sin_image qz156 qz450 Bool.false 314356431 1048576 367 524288 Bool.true 1021333 1048576 1 195407 (@Enclosure.Real.IsNear.recentre' qz156 Bool.false 675075297268070309841 2251799813685248000 68221000039992582841 97703500000000000000000 314356431 1048576 367 524288 (ep893 rfl) rfl) (Enclosure.sfrac_false_div 314356431 1048576) (BSN.sin_reduce2 qz450 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 202850551988290303557632) qz24) 226375608064910080 72057594037927936 Bool.false 1021333 1048576 47 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q2 314356431 1048576 226375608064910080 72057594037927936 47 202850551988290303557632 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1021333 1048576 202850551988290303557632 151115727451828646838272 2882679723 2147483648 391196 390814 (ep901 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep903 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz323 (Real.cos qz156)) (@HMul.hMul Real Real Real qz0 qz323 (@Neg.neg Real Real.instNeg (Real.sin qz156))) Bool.true 41499452775 549755813888 25272489695099 107426134324412416 Bool.false 356981416825 1099511627776 50698153270695 214852268648824832 (@Enclosure.Real.IsNear.mulLit_ft qz323 (Real.cos qz156) 349525 1048576 1 1048576 118731 524288 72238657 102449545216 41499452775 549755813888 25272489695099 107426134324412416 qz327 (@Enclosure.Real.IsNear.recentre' (Real.cos qz156) Bool.true 237462 1048576 72238657 102449545216 118731 524288 72238657 102449545216 (ep898 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz323 (@Neg.neg Real Real.instNeg (Real.sin qz156)) 349525 1048576 1 1048576 1021333 1048576 72238657 102449545216 356981416825 1099511627776 50698153270695 214852268648824832 qz327 (@Enclosure.Real.IsNear.neg (Real.sin qz156) Bool.true 1021333 1048576 72238657 102449545216 (@Enclosure.Real.IsNear.recentre' (Real.sin qz156) Bool.true 1021333 1048576 72238657 102449545216 1021333 1048576 72238657 102449545216 (ep902 rfl rfl) rfl)) rfl)

noncomputable def ep904 := @ep890 41499452775 549755813888 25272489695099 107426134324412416 Bool.false 356981416825 1099511627776 50698153270695 214852268648824832 Bool.false ep891 3629079829253 1099511627776 561746468115473 214852268648824832 Bool.true 77757666858466835169280 35360093015 549755813888 70228358907091 26856533581103104 EMRow46.d13 (ep892 ep903) rfl rfl

noncomputable abbrev qz157 := (@HMul.hMul Real Real Real qz269 qz441 qz572)

noncomputable def ep905 := @Enclosure.Complex.IsNear.of_eq qz659 (Complex.mk (@HMul.hMul Real Real Real qz0 qz32 (Real.cos qz157)) (@HMul.hMul Real Real Real qz0 qz32 (@Neg.neg Real Real.instNeg (Real.sin qz157)))) Bool.false 86919756159 274877906944 24023663235699 107426134324412416 Bool.true 862462989 274877906944 23922235278279 107426134324412416 (BSN.cpow_neg_s_mk qz146 136442 1000 10 qz147 rfl)

noncomputable def ep906 := @Enclosure.Real.IsNear.mulLit_ff qz146 qz572 136442 1000 0 1 10369917190100709 4503599627370496 1000000000586221 195407000000000000000 707446120625860468689 2251799813685248000 68221000039992582841 97703500000000000000000 qz148 (BSN.isNear_log_sfrac 10 1 10369917190100709 4503599627370496 1000000000586221 195407000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz328) Bool.false 43494585150108164161536 18889465931478580854784 1000000000586221 195407000000000000000 10369917190100709 4503599627370496 1000000000586221 195407000000000000000 (BSN.log_rat_reduce_isNear 10 1 3 20 16 116991 524288 24973259072661432 36028797018963968 195407 1000000000000000 rfl rfl rfl rfl (ep193 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep907 := BSN.cos_dyadic_bound_f 21309781 2147483648 1 0 1048576 391196 0 1 1 0 1 1 1048524 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 21309781) qz19 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 21309781) qz20 0 0 rfl) rfl rfl

noncomputable abbrev qz451 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 329430271) qz23)

noncomputable def ep908 := @Enclosure.Real.IsNear.cos_image qz157 qz451 Bool.false 329430271 1048576 733 1048576 Bool.false 1048524 1048576 1 195407 (@Enclosure.Real.IsNear.recentre' qz157 Bool.false 707446120625860468689 2251799813685248000 68221000039992582841 97703500000000000000000 329430271 1048576 733 1048576 (ep906 rfl) rfl) (Enclosure.sfrac_false_div 329430271 1048576) (BSN.cos_reduce0 qz451 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 1499542590938060685312) qz24) 226375608064910080 72057594037927936 Bool.false 1048524 1048576 50 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q0 329430271 1048576 226375608064910080 72057594037927936 50 1499542590938060685312 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1048524 1048576 1499542590938060685312 151115727451828646838272 21309781 2147483648 391196 390814 (ep907 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep909 := BSN.sin_dyadic_bound_f 21309781 2147483648 1 0 1048576 391196 0 1 1 0 1 1 10404 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 21309781) qz15 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 21309781) qz16 0 0 rfl) rfl rfl

noncomputable def ep910 := @Enclosure.Real.IsNear.sin_image qz157 qz451 Bool.false 329430271 1048576 733 1048576 Bool.false 10404 1048576 1 195407 (@Enclosure.Real.IsNear.recentre' qz157 Bool.false 707446120625860468689 2251799813685248000 68221000039992582841 97703500000000000000000 329430271 1048576 733 1048576 (ep906 rfl) rfl) (Enclosure.sfrac_false_div 329430271 1048576) (BSN.sin_reduce0 qz451 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 1499542590938060685312) qz24) 226375608064910080 72057594037927936 Bool.false 10404 1048576 50 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q0 329430271 1048576 226375608064910080 72057594037927936 50 1499542590938060685312 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 10404 1048576 1499542590938060685312 151115727451828646838272 21309781 2147483648 391196 390814 (ep909 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep911 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz32 (Real.cos qz157)) (@HMul.hMul Real Real Real qz0 qz32 (@Neg.neg Real Real.instNeg (Real.sin qz157))) Bool.false 86919756159 274877906944 24023663235699 107426134324412416 Bool.true 862462989 274877906944 23922235278279 107426134324412416 (@Enclosure.Real.IsNear.mulLit_ff qz32 (Real.cos qz157) 331589 1048576 1 1048576 262131 262144 144281907 204899090432 86919756159 274877906944 24023663235699 107426134324412416 qz330 (@Enclosure.Real.IsNear.recentre' (Real.cos qz157) Bool.false 1048524 1048576 144281907 204899090432 262131 262144 144281907 204899090432 (ep908 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz32 (@Neg.neg Real Real.instNeg (Real.sin qz157)) 331589 1048576 1 1048576 2601 262144 144281907 204899090432 862462989 274877906944 23922235278279 107426134324412416 qz330 (@Enclosure.Real.IsNear.neg (Real.sin qz157) Bool.false 2601 262144 144281907 204899090432 (@Enclosure.Real.IsNear.recentre' (Real.sin qz157) Bool.false 10404 1048576 144281907 204899090432 2601 262144 144281907 204899090432 (ep910 rfl rfl) rfl)) rfl)

noncomputable def ep912 := @ep888 86919756159 274877906944 24023663235699 107426134324412416 Bool.true 862462989 274877906944 23922235278279 107426134324412416 Bool.false 1093123150178028634505216 3976758853889 1099511627776 609793794586871 214852268648824832 Bool.true 10193852399774326587392 37085018993 549755813888 304835670906643 107426134324412416 (ep889 (BSN.head_sum_c_succ qz143 9 10 rfl rfl) (ep904 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep905 ep911) rfl rfl

noncomputable abbrev qz158 := (@HMul.hMul Real Real Real qz269 qz441 qz573)

noncomputable def ep913 := @Enclosure.Complex.IsNear.of_eq qz658 (Complex.mk (@HMul.hMul Real Real Real qz0 qz34 (Real.cos qz158)) (@HMul.hMul Real Real Real qz0 qz34 (@Neg.neg Real Real.instNeg (Real.sin qz158)))) Bool.false 298818001649 1099511627776 45800569447205 214852268648824832 Bool.true 2243133915 17179869184 22852304781933 107426134324412416 (BSN.cpow_neg_s_mk qz146 136442 1000 11 qz147 rfl)

noncomputable def ep914 := @Enclosure.Real.IsNear.mulLit_ff qz146 qz573 136442 1000 0 1 10799156221662949 4503599627370496 1000000000586221 195407000000000000000 736729236598068043729 2251799813685248000 68221000039992582841 97703500000000000000000 qz148 (BSN.isNear_log_sfrac 11 1 10799156221662949 4503599627370496 1000000000586221 195407000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz331) Bool.false 45294944137145793642496 18889465931478580854784 1000000000586221 195407000000000000000 10799156221662949 4503599627370496 1000000000586221 195407000000000000000 (BSN.log_rat_reduce_isNear 11 1 3 22 16 166961 524288 24973259072661432 36028797018963968 195407 1000000000000000 rfl rfl rfl rfl (ep203 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep915 := nat_lit 855695436178912961615703379798016256

noncomputable def ep916 := BSN.cos_dyadic_bound_f 961788996 2147483648 2 1 1048576 391196 ep915 ep62 ep915 ep915 ep63 ep915 945157 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 961788996) qz19 0 1 ep915 ep62 ep915 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 961788996) qz20 0 1 ep915 ep63 ep915 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz452 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 85766571) qz17)

noncomputable def ep917 := @Enclosure.Real.IsNear.cos_image qz158 qz452 Bool.false 85766571 262144 733 1048576 Bool.false 945157 1048576 1 195407 (@Enclosure.Real.IsNear.recentre' qz158 Bool.false 736729236598068043729 2251799813685248000 68221000039992582841 97703500000000000000000 85766571 262144 733 1048576 (ep914 rfl) rfl) (Enclosure.sfrac_false_div 85766571 262144) (BSN.cos_reduce0 qz452 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 16919970968146125258752) qz287) 226375608064910080 72057594037927936 Bool.false 945157 1048576 52 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q0 85766571 262144 226375608064910080 72057594037927936 52 16919970968146125258752 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 945157 1048576 16919970968146125258752 37778931862957161709568 961788996 2147483648 391196 390814 (ep916 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep918 := BSN.sin_dyadic_bound_f 961788996 2147483648 2 1 1048576 391196 ep915 ep58 ep915 ep915 ep59 ep915 454080 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 961788996) qz15 0 1 ep915 ep58 ep915 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 961788996) qz16 0 1 ep915 ep59 ep915 rfl rfl rfl rfl) rfl rfl

noncomputable def ep919 := @Enclosure.Real.IsNear.sin_image qz158 qz452 Bool.false 85766571 262144 733 1048576 Bool.false 454080 1048576 1 195407 (@Enclosure.Real.IsNear.recentre' qz158 Bool.false 736729236598068043729 2251799813685248000 68221000039992582841 97703500000000000000000 85766571 262144 733 1048576 (ep914 rfl) rfl) (Enclosure.sfrac_false_div 85766571 262144) (BSN.sin_reduce0 qz452 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 16919970968146125258752) qz287) 226375608064910080 72057594037927936 Bool.false 454080 1048576 52 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q0 85766571 262144 226375608064910080 72057594037927936 52 16919970968146125258752 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 454080 1048576 16919970968146125258752 37778931862957161709568 961788996 2147483648 391196 390814 (ep918 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep920 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz34 (Real.cos qz158)) (@HMul.hMul Real Real Real qz0 qz34 (@Neg.neg Real Real.instNeg (Real.sin qz158))) Bool.false 298818001649 1099511627776 45800569447205 214852268648824832 Bool.true 2243133915 17179869184 22852304781933 107426134324412416 (@Enclosure.Real.IsNear.mulLit_ff qz34 (Real.cos qz158) 316157 1048576 1 1048576 945157 1048576 144281907 204899090432 298818001649 1099511627776 45800569447205 214852268648824832 qz333 (@Enclosure.Real.IsNear.recentre' (Real.cos qz158) Bool.false 945157 1048576 144281907 204899090432 945157 1048576 144281907 204899090432 (ep917 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz34 (@Neg.neg Real Real.instNeg (Real.sin qz158)) 316157 1048576 1 1048576 7095 16384 144281907 204899090432 2243133915 17179869184 22852304781933 107426134324412416 qz333 (@Enclosure.Real.IsNear.neg (Real.sin qz158) Bool.false 7095 16384 144281907 204899090432 (@Enclosure.Real.IsNear.recentre' (Real.sin qz158) Bool.false 454080 1048576 144281907 204899090432 7095 16384 144281907 204899090432 (ep919 rfl rfl) rfl)) rfl)

noncomputable def ep921 := @ep885 298818001649 1099511627776 45800569447205 214852268648824832 Bool.true 2243133915 17179869184 22852304781933 107426134324412416 Bool.false ep886 2137788427769 549755813888 163898591008519 53713067162206208 Bool.true 1870291686086496223232 108865304273 549755813888 2560062310067 839266674409472 (ep887 (BSN.head_sum_c_succ qz143 10 11 rfl rfl) (ep912 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep913 ep920) rfl rfl

noncomputable abbrev qz159 := (@HMul.hMul Real Real Real qz269 qz441 qz574)

noncomputable def ep922 := @Enclosure.Complex.IsNear.of_eq qz657 (Complex.mk (@HMul.hMul Real Real Real qz0 qz36 (Real.cos qz159)) (@HMul.hMul Real Real Real qz0 qz36 (@Neg.neg Real Real.instNeg (Real.sin qz159)))) Bool.false 307806222663 1099511627776 43931699267925 214852268648824832 Bool.false 38724935301 549755813888 21891496000317 107426134324412416 (BSN.cpow_neg_s_mk qz146 136442 1000 12 qz147 rfl)

noncomputable def ep923 := @Enclosure.Real.IsNear.mulLit_ff qz146 qz574 136442 1000 0 1 11191020447815397 4503599627370496 1000000000586221 195407000000000000000 763462605970414198737 2251799813685248000 68221000039992582841 97703500000000000000000 qz148 (BSN.isNear_log_sfrac 12 1 11191020447815397 4503599627370496 1000000000586221 195407000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz334) Bool.false 46938541828353910898688 18889465931478580854784 1000000000586221 195407000000000000000 11191020447815397 4503599627370496 1000000000586221 195407000000000000000 (BSN.log_rat_reduce_isNear 12 1 3 24 16 212580 524288 24973259072661432 36028797018963968 195407 1000000000000000 rfl rfl rfl rfl (ep214 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep924 := nat_lit 4211145537045777202707707397688831714284135860617803045025450116819083250441825

noncomputable def ep925 := nat_lit 4278731413360620197036541421151222099455568163685599793867757835369348406881

noncomputable def ep926 := nat_lit 11022263222355404050582126879265076320678380143638755099209916793268905758498401

noncomputable def ep927 := BSN.sin_dyadic_bound_f 2843900373 2147483648 3 2 1048576 391196 ep924 ep72 ep925 ep926 ep75 ep925 1016879 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2843900373) qz15 0 2 ep924 ep72 ep925 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2843900373) qz16 0 2 ep926 ep75 ep925 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz453 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 355514979) qz23)

noncomputable def ep928 := @Enclosure.Real.IsNear.cos_image qz159 qz453 Bool.false 355514979 1048576 367 524288 Bool.false 1016879 1048576 1 195407 (@Enclosure.Real.IsNear.recentre' qz159 Bool.false 763462605970414198737 2251799813685248000 68221000039992582841 97703500000000000000000 355514979 1048576 367 524288 (ep923 rfl) rfl) (Enclosure.sfrac_false_div 355514979 1048576) (BSN.cos_reduce3 qz453 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 200121697880653051199488) qz24) 226375608064910080 72057594037927936 Bool.false 1016879 1048576 53 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q3 355514979 1048576 226375608064910080 72057594037927936 53 200121697880653051199488 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1016879 1048576 200121697880653051199488 151115727451828646838272 2843900373 2147483648 391196 390814 (ep927 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep929 := nat_lit 2341426956764703166036298128236529273313166841749306402700302401715210405092961

noncomputable def ep930 := nat_lit 7015723407467388257714821301867285375740589388920548008513171689474892518465121

noncomputable def ep931 := BSN.cos_dyadic_bound_f 2843900373 2147483648 3 2 1048576 391196 ep929 ep79 ep925 ep930 ep81 ep925 255866 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2843900373) qz19 0 2 ep929 ep79 ep925 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2843900373) qz20 0 2 ep930 ep81 ep925 rfl rfl rfl rfl) rfl rfl

noncomputable def ep932 := @Enclosure.Real.IsNear.sin_image qz159 qz453 Bool.false 355514979 1048576 367 524288 Bool.true 255866 1048576 1 195407 (@Enclosure.Real.IsNear.recentre' qz159 Bool.false 763462605970414198737 2251799813685248000 68221000039992582841 97703500000000000000000 355514979 1048576 367 524288 (ep923 rfl) rfl) (Enclosure.sfrac_false_div 355514979 1048576) (BSN.sin_reduce3 qz453 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 200121697880653051199488) qz24) 226375608064910080 72057594037927936 Bool.false 255866 1048576 53 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q3 355514979 1048576 226375608064910080 72057594037927936 53 200121697880653051199488 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 255866 1048576 200121697880653051199488 151115727451828646838272 2843900373 2147483648 391196 390814 (ep931 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep933 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz36 (Real.cos qz159)) (@HMul.hMul Real Real Real qz0 qz36 (@Neg.neg Real Real.instNeg (Real.sin qz159))) Bool.false 307806222663 1099511627776 43931699267925 214852268648824832 Bool.false 38724935301 549755813888 21891496000317 107426134324412416 (@Enclosure.Real.IsNear.mulLit_ff qz36 (Real.cos qz159) 302697 1048576 1 1048576 1016879 1048576 72238657 102449545216 307806222663 1099511627776 43931699267925 214852268648824832 qz336 (@Enclosure.Real.IsNear.recentre' (Real.cos qz159) Bool.false 1016879 1048576 72238657 102449545216 1016879 1048576 72238657 102449545216 (ep928 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz36 (@Neg.neg Real Real.instNeg (Real.sin qz159)) 302697 1048576 1 1048576 127933 524288 72238657 102449545216 38724935301 549755813888 21891496000317 107426134324412416 qz336 (@Enclosure.Real.IsNear.neg (Real.sin qz159) Bool.true 127933 524288 72238657 102449545216 (@Enclosure.Real.IsNear.recentre' (Real.sin qz159) Bool.true 255866 1048576 72238657 102449545216 127933 524288 72238657 102449545216 (ep932 rfl rfl) rfl)) rfl)

noncomputable def ep934 := @ep882 307806222663 1099511627776 43931699267925 214852268648824832 Bool.false 38724935301 549755813888 21891496000317 107426134324412416 Bool.false ep883 4583383078201 1099511627776 699526063302001 214852268648824832 Bool.true 38560075630606481883136 17535092243 137438953472 349579471688893 107426134324412416 (ep884 (BSN.head_sum_c_succ qz143 11 12 rfl rfl) (ep921 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep922 ep933) rfl rfl

noncomputable abbrev qz160 := (@HMul.hMul Real Real Real qz269 qz441 qz575)

noncomputable def ep935 := @Enclosure.Complex.IsNear.of_eq qz656 (Complex.mk (@HMul.hMul Real Real Real qz0 qz38 (Real.cos qz160)) (@HMul.hMul Real Real Real qz0 qz38 (@Neg.neg Real Real.instNeg (Real.sin qz160)))) Bool.true 96216753789 1099511627776 42082119404837 214852268648824832 Bool.false 144686478261 549755813888 21105951533717 107426134324412416 (BSN.cpow_neg_s_mk qz146 136442 1000 13 qz147 rfl)

noncomputable def ep936 := @Enclosure.Real.IsNear.mulLit_ff qz146 qz575 136442 1000 0 1 11551497052968677 4503599627370496 1000000000586221 195407000000000000000 788054680450576113617 2251799813685248000 68221000039992582841 97703500000000000000000 qz148 (BSN.isNear_log_sfrac 13 1 11551497052968677 4503599627370496 1000000000586221 195407000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz337) Bool.false 48450490295254733815808 18889465931478580854784 1000000000586221 195407000000000000000 11551497052968677 4503599627370496 1000000000586221 195407000000000000000 (BSN.log_rat_reduce_isNear 13 1 3 26 16 254545 524288 24973259072661432 36028797018963968 195407 1000000000000000 rfl rfl rfl rfl (ep229 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep937 := nat_lit 1856664510774473501968463985899086396049335811328749978057023897466444485284801

noncomputable def ep938 := nat_lit 2692457634467286037726465649089352356112363173774719950443913060009488733121

noncomputable def ep939 := nat_lit 5564608617054485933829939026399080483435782707638700494270183866279314478388161

noncomputable def ep940 := BSN.cos_dyadic_bound_f 2683914087 2147483648 3 2 1048576 391196 ep937 ep79 ep938 ep939 ep81 ep938 330843 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2683914087) qz19 0 2 ep937 ep79 ep938 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2683914087) qz20 0 2 ep939 ep81 ep938 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz454 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 91741639) qz17)

noncomputable def ep941 := @Enclosure.Real.IsNear.cos_image qz160 qz454 Bool.false 91741639 262144 367 524288 Bool.true 330843 1048576 1 195407 (@Enclosure.Real.IsNear.recentre' qz160 Bool.false 788054680450576113617 2251799813685248000 68221000039992582841 97703500000000000000000 91741639 262144 367 524288 (ep936 rfl) rfl) (Enclosure.sfrac_false_div 91741639 262144) (BSN.cos_reduce2 qz454 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 47215915946225086496768) qz287) 226375608064910080 72057594037927936 Bool.false 330843 1048576 55 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q2 91741639 262144 226375608064910080 72057594037927936 55 47215915946225086496768 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 330843 1048576 47215915946225086496768 37778931862957161709568 2683914087 2147483648 391196 390814 (ep940 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep942 := nat_lit 3339842153286478474713054002099084031003914569852730184542287884991592482526145

noncomputable def ep943 := nat_lit 8742846422437353732568346203970503986909880047332943793881463839547488758191041

noncomputable def ep944 := BSN.sin_dyadic_bound_f 2683914087 2147483648 3 2 1048576 391196 ep942 ep72 ep938 ep943 ep75 ep938 995014 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2683914087) qz15 0 2 ep942 ep72 ep938 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2683914087) qz16 0 2 ep943 ep75 ep938 rfl rfl rfl rfl) rfl rfl

noncomputable def ep945 := @Enclosure.Real.IsNear.sin_image qz160 qz454 Bool.false 91741639 262144 367 524288 Bool.true 995014 1048576 1 195407 (@Enclosure.Real.IsNear.recentre' qz160 Bool.false 788054680450576113617 2251799813685248000 68221000039992582841 97703500000000000000000 91741639 262144 367 524288 (ep936 rfl) rfl) (Enclosure.sfrac_false_div 91741639 262144) (BSN.sin_reduce2 qz454 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 47215915946225086496768) qz287) 226375608064910080 72057594037927936 Bool.false 995014 1048576 55 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q2 91741639 262144 226375608064910080 72057594037927936 55 47215915946225086496768 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 995014 1048576 47215915946225086496768 37778931862957161709568 2683914087 2147483648 391196 390814 (ep944 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep946 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz38 (Real.cos qz160)) (@HMul.hMul Real Real Real qz0 qz38 (@Neg.neg Real Real.instNeg (Real.sin qz160))) Bool.true 96216753789 1099511627776 42082119404837 214852268648824832 Bool.false 144686478261 549755813888 21105951533717 107426134324412416 (@Enclosure.Real.IsNear.mulLit_ft qz38 (Real.cos qz160) 290823 1048576 1 1048576 330843 1048576 72238657 102449545216 96216753789 1099511627776 42082119404837 214852268648824832 qz339 (@Enclosure.Real.IsNear.recentre' (Real.cos qz160) Bool.true 330843 1048576 72238657 102449545216 330843 1048576 72238657 102449545216 (ep941 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz38 (@Neg.neg Real Real.instNeg (Real.sin qz160)) 290823 1048576 1 1048576 497507 524288 72238657 102449545216 144686478261 549755813888 21105951533717 107426134324412416 qz339 (@Enclosure.Real.IsNear.neg (Real.sin qz160) Bool.true 497507 524288 72238657 102449545216 (@Enclosure.Real.IsNear.recentre' (Real.sin qz160) Bool.true 995014 1048576 72238657 102449545216 497507 524288 72238657 102449545216 (ep945 rfl rfl) rfl)) rfl)

noncomputable def ep947 := @ep879 96216753789 1099511627776 42082119404837 214852268648824832 Bool.false 144686478261 549755813888 21105951533717 107426134324412416 Bool.false ep880 1121791581103 274877906944 370804091353419 107426134324412416 Bool.false 10245539246089498001408 74546109289 549755813888 185342711611305 53713067162206208 (ep881 (BSN.head_sum_c_succ qz143 12 13 rfl rfl) (ep934 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep935 ep946) rfl rfl

noncomputable abbrev qz161 := (@HMul.hMul Real Real Real qz269 qz441 qz576)

noncomputable def ep948 := @Enclosure.Complex.IsNear.of_eq qz655 (Complex.mk (@HMul.hMul Real Real Real qz0 qz40 (Real.cos qz161)) (@HMul.hMul Real Real Real qz0 qz40 (@Neg.neg Real Real.instNeg (Real.sin qz161)))) Bool.true 105078514065 1099511627776 40562169216301 214852268648824832 Bool.true 68606569073 274877906944 10170062879231 53713067162206208 (BSN.cpow_neg_s_mk qz146 136442 1000 14 qz147 rfl)

noncomputable def ep949 := @Enclosure.Real.IsNear.mulLit_ff qz146 qz576 136442 1000 0 1 11885250371606245 4503599627370496 1000000000586221 195407000000000000000 162164733120269928029 450359962737049600 68221000039992582841 97703500000000000000000 qz148 (BSN.isNear_log_sfrac 14 1 11885250371606245 4503599627370496 1000000000586221 195407000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz340) Bool.false 49850353174629559828480 18889465931478580854784 1000000000586221 195407000000000000000 11885250371606245 4503599627370496 1000000000586221 195407000000000000000 (BSN.log_rat_reduce_isNear 14 1 3 28 16 293399 524288 24973259072661432 36028797018963968 195407 1000000000000000 rfl rfl rfl rfl (ep243 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep950 := nat_lit 380303575840080256894935001179099136

noncomputable def ep951 := BSN.sin_dyadic_bound_f 785294584 2147483648 2 1 1048576 391196 ep950 ep58 ep950 ep950 ep59 ep950 374955 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 785294584) qz15 0 1 ep950 ep58 ep950 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 785294584) qz16 0 1 ep950 ep59 ep950 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz455 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 377569191) qz23)

noncomputable def ep952 := @Enclosure.Real.IsNear.cos_image qz161 qz455 Bool.false 377569191 1048576 367 524288 Bool.true 374955 1048576 1 195407 (@Enclosure.Real.IsNear.recentre' qz161 Bool.false 162164733120269928029 450359962737049600 68221000039992582841 97703500000000000000000 377569191 1048576 367 524288 (ep949 rfl) rfl) (Enclosure.sfrac_false_div 377569191 1048576) (BSN.cos_reduce1 qz455 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 55260193693654405087232) qz24) 226375608064910080 72057594037927936 Bool.false 374955 1048576 57 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q1 377569191 1048576 226375608064910080 72057594037927936 57 55260193693654405087232 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 374955 1048576 55260193693654405087232 151115727451828646838272 785294584 2147483648 391196 390814 (ep951 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep953 := BSN.cos_dyadic_bound_f 785294584 2147483648 2 1 1048576 391196 ep950 ep62 ep950 ep950 ep63 ep950 979244 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 785294584) qz19 0 1 ep950 ep62 ep950 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 785294584) qz20 0 1 ep950 ep63 ep950 rfl rfl rfl rfl) rfl rfl

noncomputable def ep954 := @Enclosure.Real.IsNear.sin_image qz161 qz455 Bool.false 377569191 1048576 367 524288 Bool.false 979244 1048576 1 195407 (@Enclosure.Real.IsNear.recentre' qz161 Bool.false 162164733120269928029 450359962737049600 68221000039992582841 97703500000000000000000 377569191 1048576 367 524288 (ep949 rfl) rfl) (Enclosure.sfrac_false_div 377569191 1048576) (BSN.sin_reduce1 qz455 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 55260193693654405087232) qz24) 226375608064910080 72057594037927936 Bool.false 979244 1048576 57 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q1 377569191 1048576 226375608064910080 72057594037927936 57 55260193693654405087232 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 979244 1048576 55260193693654405087232 151115727451828646838272 785294584 2147483648 391196 390814 (ep953 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep955 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz40 (Real.cos qz161)) (@HMul.hMul Real Real Real qz0 qz40 (@Neg.neg Real Real.instNeg (Real.sin qz161))) Bool.true 105078514065 1099511627776 40562169216301 214852268648824832 Bool.true 68606569073 274877906944 10170062879231 53713067162206208 (@Enclosure.Real.IsNear.mulLit_ft qz40 (Real.cos qz161) 280243 1048576 1 1048576 374955 1048576 72238657 102449545216 105078514065 1099511627776 40562169216301 214852268648824832 qz342 (@Enclosure.Real.IsNear.recentre' (Real.cos qz161) Bool.true 374955 1048576 72238657 102449545216 374955 1048576 72238657 102449545216 (ep952 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz40 (@Neg.neg Real Real.instNeg (Real.sin qz161)) 280243 1048576 1 1048576 244811 262144 72238657 102449545216 68606569073 274877906944 10170062879231 53713067162206208 qz342 (@Enclosure.Real.IsNear.neg (Real.sin qz161) Bool.false 244811 262144 72238657 102449545216 (@Enclosure.Real.IsNear.recentre' (Real.sin qz161) Bool.false 979244 1048576 72238657 102449545216 244811 262144 72238657 102449545216 (ep954 rfl rfl) rfl)) rfl)

noncomputable def ep956 := @ep877 105078514065 1099511627776 40562169216301 214852268648824832 Bool.true 68606569073 274877906944 10170062879231 53713067162206208 Bool.false 1204539125352999386349568 4382087810347 1099511627776 782170351923139 214852268648824832 Bool.true 17225781726611408683008 62667028857 549755813888 24439096811317 6714133395275776 (ep878 (BSN.head_sum_c_succ qz143 13 14 rfl rfl) (ep947 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep948 ep955) rfl rfl

noncomputable abbrev qz162 := (@HMul.hMul Real Real Real qz269 qz441 qz577)

noncomputable def ep957 := @Enclosure.Complex.IsNear.of_eq qz654 (Complex.mk (@HMul.hMul Real Real Real qz0 qz44 (Real.cos qz162)) (@HMul.hMul Real Real Real qz0 qz44 (@Neg.neg Real Real.instNeg (Real.sin qz162)))) Bool.false 49258346799 549755813888 19593590627667 107426134324412416 Bool.false 133125244887 549755813888 19654121463243 107426134324412416 (BSN.cpow_neg_s_mk qz146 136442 1000 15 qz147 rfl)

noncomputable def ep958 := @Enclosure.Real.IsNear.mulLit_ff qz146 qz577 136442 1000 0 1 12195965485668069 4503599627370496 1000000000586221 195407000000000000000 832020961397761335249 2251799813685248000 68221000039992582841 97703500000000000000000 qz148 (BSN.isNear_log_sfrac 15 1 12195965485668069 4503599627370496 1000000000586221 195407000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz343) Bool.false 51153586820399524478976 18889465931478580854784 1000000000586221 195407000000000000000 12195965485668069 4503599627370496 1000000000586221 195407000000000000000 (BSN.log_rat_reduce_isNear 15 1 3 30 16 329571 524288 24973259072661432 36028797018963968 195407 1000000000000000 rfl rfl rfl rfl (ep258 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep959 := nat_lit 335477230320517512955641587420276401

noncomputable def ep960 := BSN.sin_dyadic_bound_f 761054507 2147483648 2 1 1048576 391196 ep959 ep58 ep959 ep959 ep59 ep959 363878 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 761054507) qz15 0 1 ep959 ep58 ep959 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 761054507) qz16 0 1 ep959 ep59 ep959 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz456 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 387439951) qz23)

noncomputable def ep961 := @Enclosure.Real.IsNear.cos_image qz162 qz456 Bool.false 387439951 1048576 367 524288 Bool.false 363878 1048576 1 195407 (@Enclosure.Real.IsNear.recentre' qz162 Bool.false 832020961397761335249 2251799813685248000 68221000039992582841 97703500000000000000000 387439951 1048576 367 524288 (ep958 rfl) rfl) (Enclosure.sfrac_false_div 387439951 1048576) (BSN.cos_reduce3 qz456 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 53554449931662599913472) qz24) 226375608064910080 72057594037927936 Bool.false 363878 1048576 58 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q3 387439951 1048576 226375608064910080 72057594037927936 58 53554449931662599913472 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 363878 1048576 53554449931662599913472 151115727451828646838272 761054507 2147483648 391196 390814 (ep960 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep962 := BSN.cos_dyadic_bound_f 761054507 2147483648 2 1 1048576 391196 ep959 ep62 ep959 ep959 ep63 ep959 983414 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 761054507) qz19 0 1 ep959 ep62 ep959 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 761054507) qz20 0 1 ep959 ep63 ep959 rfl rfl rfl rfl) rfl rfl

noncomputable def ep963 := @Enclosure.Real.IsNear.sin_image qz162 qz456 Bool.false 387439951 1048576 367 524288 Bool.true 983414 1048576 1 195407 (@Enclosure.Real.IsNear.recentre' qz162 Bool.false 832020961397761335249 2251799813685248000 68221000039992582841 97703500000000000000000 387439951 1048576 367 524288 (ep958 rfl) rfl) (Enclosure.sfrac_false_div 387439951 1048576) (BSN.sin_reduce3 qz456 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 53554449931662599913472) qz24) 226375608064910080 72057594037927936 Bool.false 983414 1048576 58 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q3 387439951 1048576 226375608064910080 72057594037927936 58 53554449931662599913472 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 983414 1048576 53554449931662599913472 151115727451828646838272 761054507 2147483648 391196 390814 (ep962 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep964 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz44 (Real.cos qz162)) (@HMul.hMul Real Real Real qz0 qz44 (@Neg.neg Real Real.instNeg (Real.sin qz162))) Bool.false 49258346799 549755813888 19593590627667 107426134324412416 Bool.false 133125244887 549755813888 19654121463243 107426134324412416 (@Enclosure.Real.IsNear.mulLit_ff qz44 (Real.cos qz162) 270741 1048576 1 1048576 181939 524288 72238657 102449545216 49258346799 549755813888 19593590627667 107426134324412416 qz345 (@Enclosure.Real.IsNear.recentre' (Real.cos qz162) Bool.false 363878 1048576 72238657 102449545216 181939 524288 72238657 102449545216 (ep961 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz44 (@Neg.neg Real Real.instNeg (Real.sin qz162)) 270741 1048576 1 1048576 491707 524288 72238657 102449545216 133125244887 549755813888 19654121463243 107426134324412416 qz345 (@Enclosure.Real.IsNear.neg (Real.sin qz162) Bool.true 491707 524288 72238657 102449545216 (@Enclosure.Real.IsNear.recentre' (Real.sin qz162) Bool.true 983414 1048576 72238657 102449545216 491707 524288 72238657 102449545216 (ep963 rfl rfl) rfl)) rfl)

noncomputable def ep965 := @ep874 49258346799 549755813888 19593590627667 107426134324412416 Bool.false 133125244887 549755813888 19654121463243 107426134324412416 Bool.false ep875 4480604503945 1099511627776 821357533178473 214852268648824832 Bool.false 38734813898669178224640 35229108015 274877906944 410679670444315 107426134324412416 (ep876 (BSN.head_sum_c_succ qz143 14 15 rfl rfl) (ep956 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep957 ep964) rfl rfl

noncomputable abbrev qz163 := (@HMul.hMul Real Real Real qz269 qz441 qz578)

noncomputable def ep966 := @Enclosure.Complex.IsNear.of_eq qz653 (Complex.mk (@HMul.hMul Real Real Real qz0 qz46 (Real.cos qz163)) (@HMul.hMul Real Real Real qz0 qz46 (@Neg.neg Real Real.instNeg (Real.sin qz163)))) Bool.false 17956009071 274877906944 9469043850431 53713067162206208 Bool.true 265327251021 1099511627776 38020416837437 214852268648824832 (BSN.cpow_neg_s_mk qz146 136442 1000 16 qz147 rfl)

noncomputable def ep967 := @Enclosure.Real.IsNear.mulLit_ff qz146 qz578 136442 1000 0 1 3121657384082679 1125899906842624 250000000195407 48851750000000000000 212962588399504444059 562949953421312000 17055250013330860947 24425875000000000000000 qz148 (BSN.isNear_log_sfrac 16 1 3121657384082679 1125899906842624 250000000195407 48851750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz346) Bool.false 52372720210750067441664 18889465931478580854784 1000000000781628 195407000000000000000 3121657384082679 1125899906842624 250000000195407 48851750000000000000 (BSN.log_rat_reduce_isNear 16 1 4 32 32 0 524288 24973259072661432 36028797018963968 195407 1000000000000000 rfl rfl rfl rfl (ep273 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep968 := nat_lit 2217417822616660837282111424122068953231042396956882744751872407236856917262336

noncomputable def ep969 := nat_lit 3838245861140583134465463686262290384314080291629165633112939126200526176256

noncomputable def ep970 := nat_lit 6644576976127701345577403344993682278924499030287389902989391343458169699434496

noncomputable def ep971 := BSN.cos_dyadic_bound_f 2805540864 2147483648 3 2 1048576 391196 ep968 ep79 ep969 ep970 ep81 ep969 273988 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2805540864) qz19 0 2 ep968 ep79 ep969 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2805540864) qz20 0 2 ep970 ep81 ep969 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz457 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 99168433) qz17)

noncomputable def ep972 := @Enclosure.Real.IsNear.cos_image qz163 qz457 Bool.false 99168433 262144 733 1048576 Bool.false 273988 1048576 1 195407 (@Enclosure.Real.IsNear.recentre' qz163 Bool.false 212962588399504444059 562949953421312000 17055250013330860947 24425875000000000000000 99168433 262144 733 1048576 (ep967 rfl) rfl) (Enclosure.sfrac_false_div 99168433 262144) (BSN.cos_reduce0 qz457 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 49355596846642837323776) qz287) 226375608064910080 72057594037927936 Bool.false 273988 1048576 60 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q0 99168433 262144 226375608064910080 72057594037927936 60 49355596846642837323776 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 273988 1048576 49355596846642837323776 37778931862957161709568 2805540864 2147483648 391196 390814 (ep971 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep973 := nat_lit 3988281484021077040600228192470714283508425050289085608046879981725382030131200

noncomputable def ep974 := nat_lit 10439284821994307495544796420026493700947461858856396038621550431647866369867776

noncomputable def ep975 := BSN.sin_dyadic_bound_f 2805540864 2147483648 3 2 1048576 391196 ep973 ep72 ep969 ep974 ep75 ep969 1012147 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2805540864) qz15 0 2 ep973 ep72 ep969 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2805540864) qz16 0 2 ep974 ep75 ep969 rfl rfl rfl rfl) rfl rfl

noncomputable def ep976 := @Enclosure.Real.IsNear.sin_image qz163 qz457 Bool.false 99168433 262144 733 1048576 Bool.false 1012147 1048576 1 195407 (@Enclosure.Real.IsNear.recentre' qz163 Bool.false 212962588399504444059 562949953421312000 17055250013330860947 24425875000000000000000 99168433 262144 733 1048576 (ep967 rfl) rfl) (Enclosure.sfrac_false_div 99168433 262144) (BSN.sin_reduce0 qz457 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 49355596846642837323776) qz287) 226375608064910080 72057594037927936 Bool.false 1012147 1048576 60 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q0 99168433 262144 226375608064910080 72057594037927936 60 49355596846642837323776 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1012147 1048576 49355596846642837323776 37778931862957161709568 2805540864 2147483648 391196 390814 (ep975 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep977 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz46 (Real.cos qz163)) (@HMul.hMul Real Real Real qz0 qz46 (@Neg.neg Real Real.instNeg (Real.sin qz163))) Bool.false 17956009071 274877906944 9469043850431 53713067162206208 Bool.true 265327251021 1099511627776 38020416837437 214852268648824832 (@Enclosure.Real.IsNear.mulLit_ff qz46 (Real.cos qz163) 262143 1048576 1 1048576 68497 262144 144281907 204899090432 17956009071 274877906944 9469043850431 53713067162206208 qz348 (@Enclosure.Real.IsNear.recentre' (Real.cos qz163) Bool.false 273988 1048576 144281907 204899090432 68497 262144 144281907 204899090432 (ep972 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz46 (@Neg.neg Real Real.instNeg (Real.sin qz163)) 262143 1048576 1 1048576 1012147 1048576 144281907 204899090432 265327251021 1099511627776 38020416837437 214852268648824832 qz348 (@Enclosure.Real.IsNear.neg (Real.sin qz163) Bool.false 1012147 1048576 144281907 204899090432 (@Enclosure.Real.IsNear.recentre' (Real.sin qz163) Bool.false 1012147 1048576 144281907 204899090432 1012147 1048576 144281907 204899090432 (ep976 rfl rfl) rfl)) rfl)

noncomputable def ep978 := @ep871 17956009071 274877906944 9469043850431 53713067162206208 Bool.true 265327251021 1099511627776 38020416837437 214852268648824832 Bool.false ep872 4552428540229 1099511627776 859233708580197 214852268648824832 Bool.true 34197785517188588765184 124410818961 1099511627776 859379757726067 214852268648824832 (ep873 (BSN.head_sum_c_succ qz143 15 16 rfl rfl) (ep965 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep966 ep977) rfl rfl

theorem EMRow46.d14 : Enclosure.Complex.IsNear qz155 Bool.false 4552428540229 1099511627776 859233708580197 214852268648824832 Bool.true 124410818961 1099511627776 859379757726067 214852268648824832 := ep870 (BSN.head_sum_c_succ qz143 16 17 rfl rfl) (ep978 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable abbrev qz164 := (BSN.headSumC qz439 25)

noncomputable abbrev qz661 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 24) qz144)

noncomputable def ep979 := @Enclosure.Complex.IsNear.of_eq qz164 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz143 24) qz661) Bool.false 5548594187443 1099511627776 1129307007033635 214852268648824832 Bool.true 273137132885 1099511627776 1128925001981195 214852268648824832

noncomputable def ep980 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz143 24) qz661 Bool.false 665609730267 137438953472 17159044387631 3357066697637888 Bool.true 15948610157 68719476736 548992340838743 107426134324412416 Bool.false

noncomputable abbrev qz662 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 23) qz144)

noncomputable def ep981 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz143 24) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz143 23) qz662) Bool.false 665609730267 137438953472 17159044387631 3357066697637888 Bool.true 15948610157 68719476736 548992340838743 107426134324412416

noncomputable def ep982 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz143 23) qz662 Bool.false 2565088343961 549755813888 533229228995795 107426134324412416 Bool.true 67063470067 549755813888 4165352039451 839266674409472 Bool.false

noncomputable def ep983 := nat_lit 1463691275978826930192384

noncomputable abbrev qz663 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 22) qz144)

noncomputable def ep984 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz143 23) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz143 22) qz663) Bool.false 2565088343961 549755813888 533229228995795 107426134324412416 Bool.true 67063470067 549755813888 4165352039451 839266674409472

noncomputable def ep985 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz143 22) qz663 Bool.false 4962618704409 1099511627776 1034056624121321 214852268648824832 Bool.false 14905045325 549755813888 516965726618183 107426134324412416 Bool.false

noncomputable def ep986 := nat_lit 5640688920915606578921472

noncomputable abbrev qz664 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 21) qz144)

noncomputable def ep987 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz143 22) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz143 21) qz664) Bool.false 4962618704409 1099511627776 1034056624121321 214852268648824832 Bool.false 14905045325 549755813888 516965726618183 107426134324412416

noncomputable def ep988 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz143 21) qz664 Bool.false 4780717089493 1099511627776 1000731355882513 214852268648824832 Bool.false 46567415241 274877906944 250162409803851 53713067162206208 Bool.false

noncomputable def ep989 := nat_lit 1364114242429090944516096

noncomputable abbrev qz665 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 20) qz144)

noncomputable def ep990 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz143 21) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz143 20) qz665) Bool.false 4780717089493 1099511627776 1000731355882513 214852268648824832 Bool.false 46567415241 274877906944 250162409803851 53713067162206208

noncomputable def ep991 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz143 20) qz665 Bool.false 4548649989929 1099511627776 966708171897531 214852268648824832 Bool.false 267455724559 1099511627776 966752199830329 214852268648824832 Bool.false

noncomputable def ep992 := nat_lit 1314113507251247374139392

noncomputable abbrev qz666 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 19) qz144)

noncomputable def ep993 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz143 20) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz143 19) qz666) Bool.false 4548649989929 1099511627776 966708171897531 214852268648824832 Bool.false 267455724559 1099511627776 966752199830329 214852268648824832

noncomputable def ep994 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz143 19) qz666 Bool.false 4314280572999 1099511627776 931809337171721 214852268648824832 Bool.false 87096101527 549755813888 116495998245693 26856533581103104 Bool.false

noncomputable def ep995 := nat_lit 2500646777305060398333952

noncomputable abbrev qz667 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 18) qz144)

noncomputable def ep996 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz143 19) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz143 18) qz667) Bool.false 4314280572999 1099511627776 931809337171721 214852268648824832 Bool.false 87096101527 549755813888 116495998245693 26856533581103104

noncomputable def ep997 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz143 18) qz667 Bool.false 4288881359031 1099511627776 896129693706281 214852268648824832 Bool.true 83716538523 1099511627776 896104511606191 214852268648824832 Bool.false

noncomputable abbrev qz668 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 17) qz144)

noncomputable def ep998 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz143 18) (@HAdd.hAdd Complex Complex Complex qz4 qz155 qz668) Bool.false 4288881359031 1099511627776 896129693706281 214852268648824832 Bool.true 83716538523 1099511627776 896104511606191 214852268648824832

noncomputable def ep999 := @Enclosure.Complex.IsNear.addLitP qz155 qz668 Bool.false 4552428540229 1099511627776 859233708580197 214852268648824832 Bool.true 124410818961 1099511627776 859379757726067 214852268648824832 Bool.true

noncomputable def ep1000 := nat_lit 2357837462203158944022528

noncomputable abbrev qz165 := (@HMul.hMul Real Real Real qz269 qz441 qz587)

noncomputable def ep1001 := @Enclosure.Complex.IsNear.of_eq qz668 (Complex.mk (@HMul.hMul Real Real Real qz0 qz49 (Real.cos qz165)) (@HMul.hMul Real Real Real qz0 qz49 (@Neg.neg Real Real.instNeg (Real.sin qz165)))) Bool.true 131773590599 549755813888 9223996281521 53713067162206208 Bool.false 20347140219 549755813888 9181188470031 53713067162206208 (BSN.cpow_neg_s_mk qz146 136442 1000 17 qz147 rfl)

noncomputable def ep1002 := @Enclosure.Real.IsNear.mulLit_ff qz146 qz587 136442 1000 0 1 3189913004350711 1125899906842624 250000000195407 48851750000000000000 217619055069809855131 562949953421312000 17055250013330860947 24425875000000000000000 qz148 (BSN.isNear_log_sfrac 17 1 3189913004350711 1125899906842624 250000000195407 48851750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz349) Bool.false 53517859495200818200576 18889465931478580854784 1000000000781628 195407000000000000000 3189913004350711 1125899906842624 250000000195407 48851750000000000000 (BSN.log_rat_reduce_isNear 17 1 4 34 32 31784 524288 24973259072661432 36028797018963968 195407 1000000000000000 rfl rfl rfl rfl (ep300 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1003 := nat_lit 11715382927125475251611270423640721

noncomputable def ep1004 := BSN.cos_dyadic_bound_f 328994867 2147483648 2 1 1048576 391196 ep1003 ep62 ep1003 ep1003 ep63 ep1003 1036294 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 328994867) qz19 0 1 ep1003 ep62 ep1003 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 328994867) qz20 0 1 ep1003 ep63 ep1003 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz458 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 405347077) qz23)

noncomputable def ep1005 := @Enclosure.Real.IsNear.cos_image qz165 qz458 Bool.false 405347077 1048576 733 1048576 Bool.true 1036294 1048576 1 195407 (@Enclosure.Real.IsNear.recentre' qz165 Bool.false 217619055069809855131 562949953421312000 17055250013330860947 24425875000000000000000 405347077 1048576 733 1048576 (ep1002 rfl) rfl) (Enclosure.sfrac_false_div 405347077 1048576) (BSN.cos_reduce2 qz458 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 23150955694728585150464) qz24) 226375608064910080 72057594037927936 Bool.false 1036294 1048576 61 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q2 405347077 1048576 226375608064910080 72057594037927936 61 23150955694728585150464 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1036294 1048576 23150955694728585150464 151115727451828646838272 328994867 2147483648 391196 390814 (ep1004 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1006 := BSN.sin_dyadic_bound_f 328994867 2147483648 2 1 1048576 391196 ep1003 ep58 ep1003 ep1003 ep59 ep1003 160014 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 328994867) qz15 0 1 ep1003 ep58 ep1003 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 328994867) qz16 0 1 ep1003 ep59 ep1003 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1007 := @Enclosure.Real.IsNear.sin_image qz165 qz458 Bool.false 405347077 1048576 733 1048576 Bool.true 160014 1048576 1 195407 (@Enclosure.Real.IsNear.recentre' qz165 Bool.false 217619055069809855131 562949953421312000 17055250013330860947 24425875000000000000000 405347077 1048576 733 1048576 (ep1002 rfl) rfl) (Enclosure.sfrac_false_div 405347077 1048576) (BSN.sin_reduce2 qz458 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 23150955694728585150464) qz24) 226375608064910080 72057594037927936 Bool.false 160014 1048576 61 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q2 405347077 1048576 226375608064910080 72057594037927936 61 23150955694728585150464 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 160014 1048576 23150955694728585150464 151115727451828646838272 328994867 2147483648 391196 390814 (ep1006 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1008 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz49 (Real.cos qz165)) (@HMul.hMul Real Real Real qz0 qz49 (@Neg.neg Real Real.instNeg (Real.sin qz165))) Bool.true 131773590599 549755813888 9223996281521 53713067162206208 Bool.false 20347140219 549755813888 9181188470031 53713067162206208 (@Enclosure.Real.IsNear.mulLit_ft qz49 (Real.cos qz165) 254317 1048576 1 1048576 518147 524288 144281907 204899090432 131773590599 549755813888 9223996281521 53713067162206208 qz351 (@Enclosure.Real.IsNear.recentre' (Real.cos qz165) Bool.true 1036294 1048576 144281907 204899090432 518147 524288 144281907 204899090432 (ep1005 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz49 (@Neg.neg Real Real.instNeg (Real.sin qz165)) 254317 1048576 1 1048576 80007 524288 144281907 204899090432 20347140219 549755813888 9181188470031 53713067162206208 qz351 (@Enclosure.Real.IsNear.neg (Real.sin qz165) Bool.true 80007 524288 144281907 204899090432 (@Enclosure.Real.IsNear.recentre' (Real.sin qz165) Bool.true 160014 1048576 144281907 204899090432 80007 524288 144281907 204899090432 (ep1007 rfl rfl) rfl)) rfl)

noncomputable def ep1009 := @ep999 131773590599 549755813888 9223996281521 53713067162206208 Bool.false 20347140219 549755813888 9181188470031 53713067162206208 Bool.false ep1000 4288881359031 1099511627776 896129693706281 214852268648824832 Bool.true 46023653771597970407424 83716538523 1099511627776 896104511606191 214852268648824832 EMRow46.d14 (ep1001 ep1008) rfl rfl

noncomputable abbrev qz166 := (@HMul.hMul Real Real Real qz269 qz441 qz588)

noncomputable def ep1010 := @Enclosure.Complex.IsNear.of_eq qz667 (Complex.mk (@HMul.hMul Real Real Real qz0 qz51 (Real.cos qz166)) (@HMul.hMul Real Real Real qz0 qz51 (@Neg.neg Real Real.instNeg (Real.sin qz166)))) Bool.false 1587450873 68719476736 1114988858295 6714133395275776 Bool.false 257908741577 1099511627776 35863474359353 214852268648824832 (BSN.cpow_neg_s_mk qz146 136442 1000 18 qz147 rfl)

noncomputable def ep1011 := @Enclosure.Real.IsNear.mulLit_ff qz146 qz588 136442 1000 0 1 3254268794313975 1125899906842624 250000000195407 48851750000000000000 8880378856675747539 22517998136852480 17055250013330860947 24425875000000000000000 qz148 (BSN.isNear_log_sfrac 18 1 3254268794313975 1125899906842624 250000000195407 48851750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz352) Bool.false 54597570484265130393600 18889465931478580854784 1000000000781628 195407000000000000000 3254268794313975 1125899906842624 250000000195407 48851750000000000000 (BSN.log_rat_reduce_isNear 18 1 4 36 32 61752 524288 24973259072661432 36028797018963968 195407 1000000000000000 rfl rfl rfl rfl (ep314 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1012 := BSN.sin_dyadic_bound_f 210807561 2147483648 1 0 1048576 391196 0 1 1 0 1 1 102768 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 210807561) qz15 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 210807561) qz16 0 0 rfl) rfl rfl

noncomputable abbrev qz459 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 413524865) qz23)

noncomputable def ep1013 := @Enclosure.Real.IsNear.cos_image qz166 qz459 Bool.false 413524865 1048576 733 1048576 Bool.false 102768 1048576 1 195407 (@Enclosure.Real.IsNear.recentre' qz166 Bool.false 8880378856675747539 22517998136852480 17055250013330860947 24425875000000000000000 413524865 1048576 733 1048576 (ep1011 rfl) rfl) (Enclosure.sfrac_false_div 413524865 1048576) (BSN.cos_reduce3 qz459 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 14834263347850064691200) qz24) 226375608064910080 72057594037927936 Bool.false 102768 1048576 62 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q3 413524865 1048576 226375608064910080 72057594037927936 62 14834263347850064691200 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 102768 1048576 14834263347850064691200 151115727451828646838272 210807561 2147483648 391196 390814 (ep1012 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1014 := nat_lit 1974898292651105452769105039975841

noncomputable def ep1015 := BSN.cos_dyadic_bound_f 210807561 2147483648 2 1 1048576 391196 ep1014 ep62 ep1014 ep1014 ep63 ep1014 1043527 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 210807561) qz19 0 1 ep1014 ep62 ep1014 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 210807561) qz20 0 1 ep1014 ep63 ep1014 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1016 := @Enclosure.Real.IsNear.sin_image qz166 qz459 Bool.false 413524865 1048576 733 1048576 Bool.true 1043527 1048576 1 195407 (@Enclosure.Real.IsNear.recentre' qz166 Bool.false 8880378856675747539 22517998136852480 17055250013330860947 24425875000000000000000 413524865 1048576 733 1048576 (ep1011 rfl) rfl) (Enclosure.sfrac_false_div 413524865 1048576) (BSN.sin_reduce3 qz459 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 14834263347850064691200) qz24) 226375608064910080 72057594037927936 Bool.false 1043527 1048576 62 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q3 413524865 1048576 226375608064910080 72057594037927936 62 14834263347850064691200 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1043527 1048576 14834263347850064691200 151115727451828646838272 210807561 2147483648 391196 390814 (ep1015 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1017 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz51 (Real.cos qz166)) (@HMul.hMul Real Real Real qz0 qz51 (@Neg.neg Real Real.instNeg (Real.sin qz166))) Bool.false 1587450873 68719476736 1114988858295 6714133395275776 Bool.false 257908741577 1099511627776 35863474359353 214852268648824832 (@Enclosure.Real.IsNear.mulLit_ff qz51 (Real.cos qz166) 247151 1048576 1 1048576 6423 65536 144281907 204899090432 1587450873 68719476736 1114988858295 6714133395275776 qz354 (@Enclosure.Real.IsNear.recentre' (Real.cos qz166) Bool.false 102768 1048576 144281907 204899090432 6423 65536 144281907 204899090432 (ep1013 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz51 (@Neg.neg Real Real.instNeg (Real.sin qz166)) 247151 1048576 1 1048576 1043527 1048576 144281907 204899090432 257908741577 1099511627776 35863474359353 214852268648824832 qz354 (@Enclosure.Real.IsNear.neg (Real.sin qz166) Bool.true 1043527 1048576 144281907 204899090432 (@Enclosure.Real.IsNear.recentre' (Real.sin qz166) Bool.true 1043527 1048576 144281907 204899090432 1043527 1048576 144281907 204899090432 (ep1016 rfl rfl) rfl)) rfl)

noncomputable def ep1018 := @ep997 1587450873 68719476736 1114988858295 6714133395275776 Bool.false 257908741577 1099511627776 35863474359353 214852268648824832 Bool.false 296475103468781530251264 4314280572999 1099511627776 931809337171721 214852268648824832 Bool.false 191526352725791058427904 87096101527 549755813888 116495998245693 26856533581103104 (ep998 (BSN.head_sum_c_succ qz143 17 18 rfl rfl) (ep1009 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1010 ep1017) rfl rfl

noncomputable abbrev qz167 := (@HMul.hMul Real Real Real qz269 qz441 qz589)

noncomputable def ep1019 := @Enclosure.Complex.IsNear.of_eq qz666 (Complex.mk (@HMul.hMul Real Real Real qz0 qz53 (Real.cos qz167)) (@HMul.hMul Real Real Real qz0 qz53 (@Neg.neg Real Real.instNeg (Real.sin qz167)))) Bool.false 117184708465 549755813888 17449417362905 107426134324412416 Bool.false 93263521505 1099511627776 34784213864785 214852268648824832 (BSN.cpow_neg_s_mk qz146 136442 1000 19 qz147 rfl)

noncomputable def ep1020 := @Enclosure.Real.IsNear.mulLit_ff qz146 qz589 136442 1000 0 1 3315143513283831 1125899906842624 250000000195407 48851750000000000000 226162405619736234651 562949953421312000 17055250013330860947 24425875000000000000000 qz148 (BSN.isNear_log_sfrac 19 1 3315143513283831 1125899906842624 250000000195407 48851750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz355) Bool.false 55618878793361701994496 18889465931478580854784 1000000000781628 195407000000000000000 3315143513283831 1125899906842624 250000000195407 48851750000000000000 (BSN.log_rat_reduce_isNear 19 1 4 38 32 90099 524288 24973259072661432 36028797018963968 195407 1000000000000000 rfl rfl rfl rfl (ep325 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1021 := nat_lit 2763888605976758637063693460834036870366094621263294845556061167668208850698240

noncomputable def ep1022 := nat_lit 1844415430992203116217800236545567161070599824513428630363778669417632628736

noncomputable def ep1023 := nat_lit 7235769676384190006311987387515689456507562084545131425340523606999585108525056

noncomputable def ep1024 := BSN.sin_dyadic_bound_f 2559955072 2147483648 3 2 1048576 391196 ep1021 ep72 ep1022 ep1023 ep75 ep1022 974270 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2559955072) qz15 0 2 ep1021 ep72 ep1022 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2559955072) qz16 0 2 ep1023 ep75 ep1022 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz460 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 421260307) qz23)

noncomputable def ep1025 := @Enclosure.Real.IsNear.cos_image qz167 qz460 Bool.false 421260307 1048576 733 1048576 Bool.false 974270 1048576 1 195407 (@Enclosure.Real.IsNear.recentre' qz167 Bool.false 226162405619736234651 562949953421312000 17055250013330860947 24425875000000000000000 421260307 1048576 733 1048576 (ep1020 rfl) rfl) (Enclosure.sfrac_false_div 421260307 1048576) (BSN.cos_reduce3 qz460 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 180140823618640154722304) qz24) 226375608064910080 72057594037927936 Bool.false 974270 1048576 63 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q3 421260307 1048576 226375608064910080 72057594037927936 63 180140823618640154722304 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 974270 1048576 180140823618640154722304 151115727451828646838272 2559955072 2147483648 391196 390814 (ep1024 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1026 := nat_lit 1536313410178640221975926500568485180052750611734947549144640105890968309334016

noncomputable def ep1027 := nat_lit 4605251399673936259695343901232364405836110635555815790173192760334069662744576

noncomputable def ep1028 := BSN.cos_dyadic_bound_f 2559955072 2147483648 3 2 1048576 391196 ep1026 ep79 ep1022 ep1027 ep81 ep1022 387695 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2559955072) qz19 0 2 ep1026 ep79 ep1022 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2559955072) qz20 0 2 ep1027 ep81 ep1022 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1029 := @Enclosure.Real.IsNear.sin_image qz167 qz460 Bool.false 421260307 1048576 733 1048576 Bool.true 387695 1048576 1 195407 (@Enclosure.Real.IsNear.recentre' qz167 Bool.false 226162405619736234651 562949953421312000 17055250013330860947 24425875000000000000000 421260307 1048576 733 1048576 (ep1020 rfl) rfl) (Enclosure.sfrac_false_div 421260307 1048576) (BSN.sin_reduce3 qz460 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 180140823618640154722304) qz24) 226375608064910080 72057594037927936 Bool.false 387695 1048576 63 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q3 421260307 1048576 226375608064910080 72057594037927936 63 180140823618640154722304 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 387695 1048576 180140823618640154722304 151115727451828646838272 2559955072 2147483648 391196 390814 (ep1028 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1030 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz53 (Real.cos qz167)) (@HMul.hMul Real Real Real qz0 qz53 (@Neg.neg Real Real.instNeg (Real.sin qz167))) Bool.false 117184708465 549755813888 17449417362905 107426134324412416 Bool.false 93263521505 1099511627776 34784213864785 214852268648824832 (@Enclosure.Real.IsNear.mulLit_ff qz53 (Real.cos qz167) 240559 1048576 1 1048576 487135 524288 144281907 204899090432 117184708465 549755813888 17449417362905 107426134324412416 qz357 (@Enclosure.Real.IsNear.recentre' (Real.cos qz167) Bool.false 974270 1048576 144281907 204899090432 487135 524288 144281907 204899090432 (ep1025 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz53 (@Neg.neg Real Real.instNeg (Real.sin qz167)) 240559 1048576 1 1048576 387695 1048576 144281907 204899090432 93263521505 1099511627776 34784213864785 214852268648824832 qz357 (@Enclosure.Real.IsNear.neg (Real.sin qz167) Bool.true 387695 1048576 144281907 204899090432 (@Enclosure.Real.IsNear.recentre' (Real.sin qz167) Bool.true 387695 1048576 144281907 204899090432 387695 1048576 144281907 204899090432 (ep1029 rfl rfl) rfl)) rfl)

noncomputable def ep1031 := @ep994 117184708465 549755813888 17449417362905 107426134324412416 Bool.false 93263521505 1099511627776 34784213864785 214852268648824832 Bool.false ep995 4548649989929 1099511627776 966708171897531 214852268648824832 Bool.false 147035339533937794875392 267455724559 1099511627776 966752199830329 214852268648824832 (ep996 (BSN.head_sum_c_succ qz143 18 19 rfl rfl) (ep1018 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1019 ep1030) rfl rfl

noncomputable abbrev qz168 := (@HMul.hMul Real Real Real qz269 qz441 qz590)

noncomputable def ep1032 := @Enclosure.Complex.IsNear.of_eq qz665 (Complex.mk (@HMul.hMul Real Real Real qz0 qz55 (Real.cos qz168)) (@HMul.hMul Real Real Real qz0 qz55 (@Neg.neg Real Real.instNeg (Real.sin qz168)))) Bool.false 58016774891 274877906944 17011591992491 107426134324412416 Bool.true 81186063595 1099511627776 33897439385075 214852268648824832 (BSN.cpow_neg_s_mk qz146 136442 1000 20 qz147 rfl)

noncomputable def ep1033 := @Enclosure.Real.IsNear.mulLit_ff qz146 qz590 136442 1000 0 1 3372893643545847 1125899906842624 250000000195407 48851750000000000000 230102177256341228187 562949953421312000 17055250013330860947 24425875000000000000000 qz148 (BSN.isNear_log_sfrac 20 1 3372893643545847 1125899906842624 250000000195407 48851750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz358) Bool.false 56587765202795681021952 18889465931478580854784 1000000000781628 195407000000000000000 3372893643545847 1125899906842624 250000000195407 48851750000000000000 (BSN.log_rat_reduce_isNear 20 1 4 40 32 116991 524288 24973259072661432 36028797018963968 195407 1000000000000000 rfl rfl rfl rfl (ep340 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1034 := nat_lit 272784817758766611022719489473760016

noncomputable def ep1035 := BSN.cos_dyadic_bound_f 722694998 2147483648 2 1 1048576 391196 ep1034 ep62 ep1034 ep1034 ep63 ep1034 989756 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 722694998) qz19 0 1 ep1034 ep62 ep1034 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 722694998) qz20 0 1 ep1034 ep63 ep1034 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz461 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 26787419) (@Nat.cast Real Real.instNatCast 65536))

noncomputable def ep1036 := @Enclosure.Real.IsNear.cos_image qz168 qz461 Bool.false 26787419 65536 733 1048576 Bool.false 989756 1048576 1 195407 (@Enclosure.Real.IsNear.recentre' qz168 Bool.false 230102177256341228187 562949953421312000 17055250013330860947 24425875000000000000000 26787419 65536 733 1048576 (ep1033 rfl) rfl) (Enclosure.sfrac_false_div 26787419 65536) (BSN.cos_reduce0 qz461 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 3178446214848806125568) qz554) 226375608064910080 72057594037927936 Bool.false 989756 1048576 65 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q0 26787419 65536 226375608064910080 72057594037927936 65 3178446214848806125568 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 989756 1048576 3178446214848806125568 9444732965739290427392 722694998 2147483648 391196 390814 (ep1035 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1037 := BSN.sin_dyadic_bound_f 722694998 2147483648 2 1 1048576 391196 ep1034 ep58 ep1034 ep1034 ep59 ep1034 346255 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 722694998) qz15 0 1 ep1034 ep58 ep1034 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 722694998) qz16 0 1 ep1034 ep59 ep1034 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1038 := @Enclosure.Real.IsNear.sin_image qz168 qz461 Bool.false 26787419 65536 733 1048576 Bool.false 346255 1048576 1 195407 (@Enclosure.Real.IsNear.recentre' qz168 Bool.false 230102177256341228187 562949953421312000 17055250013330860947 24425875000000000000000 26787419 65536 733 1048576 (ep1033 rfl) rfl) (Enclosure.sfrac_false_div 26787419 65536) (BSN.sin_reduce0 qz461 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 3178446214848806125568) qz554) 226375608064910080 72057594037927936 Bool.false 346255 1048576 65 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q0 26787419 65536 226375608064910080 72057594037927936 65 3178446214848806125568 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 346255 1048576 3178446214848806125568 9444732965739290427392 722694998 2147483648 391196 390814 (ep1037 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1039 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz55 (Real.cos qz168)) (@HMul.hMul Real Real Real qz0 qz55 (@Neg.neg Real Real.instNeg (Real.sin qz168))) Bool.false 58016774891 274877906944 17011591992491 107426134324412416 Bool.true 81186063595 1099511627776 33897439385075 214852268648824832 (@Enclosure.Real.IsNear.mulLit_ff qz55 (Real.cos qz168) 234469 1048576 1 1048576 247439 262144 144281907 204899090432 58016774891 274877906944 17011591992491 107426134324412416 qz360 (@Enclosure.Real.IsNear.recentre' (Real.cos qz168) Bool.false 989756 1048576 144281907 204899090432 247439 262144 144281907 204899090432 (ep1036 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz55 (@Neg.neg Real Real.instNeg (Real.sin qz168)) 234469 1048576 1 1048576 346255 1048576 144281907 204899090432 81186063595 1099511627776 33897439385075 214852268648824832 qz360 (@Enclosure.Real.IsNear.neg (Real.sin qz168) Bool.false 346255 1048576 144281907 204899090432 (@Enclosure.Real.IsNear.recentre' (Real.sin qz168) Bool.false 346255 1048576 144281907 204899090432 346255 1048576 144281907 204899090432 (ep1038 rfl rfl) rfl)) rfl)

noncomputable def ep1040 := @ep991 58016774891 274877906944 17011591992491 107426134324412416 Bool.true 81186063595 1099511627776 33897439385075 214852268648824832 Bool.false ep992 4780717089493 1099511627776 1000731355882513 214852268648824832 Bool.false 204805658131811285336064 46567415241 274877906944 250162409803851 53713067162206208 (ep993 (BSN.head_sum_c_succ qz143 19 20 rfl rfl) (ep1031 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1032 ep1039) rfl rfl

noncomputable abbrev qz169 := (@HMul.hMul Real Real Real qz269 qz441 qz591)

noncomputable def ep1041 := @Enclosure.Complex.IsNear.of_eq qz664 (Complex.mk (@HMul.hMul Real Real Real qz0 qz57 (Real.cos qz169)) (@HMul.hMul Real Real Real qz0 qz57 (@Neg.neg Real Real.instNeg (Real.sin qz169)))) Bool.false 45475403729 274877906944 4165658529851 26856533581103104 Bool.true 78229785157 549755813888 16640907010481 107426134324412416 (BSN.cpow_neg_s_mk qz146 136442 1000 21 qz147 rfl)

noncomputable def ep1042 := @Enclosure.Real.IsNear.mulLit_ff qz146 qz591 136442 1000 0 1 3427826275261687 1125899906842624 250000000195407 48851750000000000000 233849736324627548827 562949953421312000 17055250013330860947 24425875000000000000000 qz148 (BSN.isNear_log_sfrac 21 1 3427826275261687 1125899906842624 250000000195407 48851750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz361) Bool.false 57509381830540779323392 18889465931478580854784 1000000000781628 195407000000000000000 3427826275261687 1125899906842624 250000000195407 48851750000000000000 (BSN.log_rat_reduce_isNear 21 1 4 42 32 142571 524288 24973259072661432 36028797018963968 195407 1000000000000000 rfl rfl rfl rfl (ep351 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1043 := nat_lit 193508131521247856950787472103272416552670685790600878379700894346664163716641

noncomputable def ep1044 := nat_lit 29323062099879836172333825778493563401854981705936684108724455433748131361

noncomputable def ep1045 := nat_lit 580465748439543811180017748658260262531208347408390761770885234129124994887201

noncomputable def ep1046 := BSN.cos_dyadic_bound_f 1525461197 2147483648 3 2 1048576 391196 ep1043 ep79 ep1044 ep1045 ep81 ep1044 794962 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1525461197) qz19 0 2 ep1043 ep79 ep1044 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1525461197) qz20 0 2 ep1045 ep81 ep1044 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz462 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 435579077) qz23)

noncomputable def ep1047 := @Enclosure.Real.IsNear.cos_image qz169 qz462 Bool.false 435579077 1048576 733 1048576 Bool.false 794962 1048576 1 195407 (@Enclosure.Real.IsNear.recentre' qz169 Bool.false 233849736324627548827 562949953421312000 17055250013330860947 24425875000000000000000 435579077 1048576 733 1048576 (ep1042 rfl) rfl) (Enclosure.sfrac_false_div 435579077 1048576) (BSN.cos_reduce0 qz462 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 107344788763122570625024) qz24) 226375608064910080 72057594037927936 Bool.false 794962 1048576 66 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q0 435579077 1048576 226375608064910080 72057594037927936 66 107344788763122570625024 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 794962 1048576 107344788763122570625024 151115727451828646838272 1525461197 2147483648 391196 390814 (ep1046 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1048 := nat_lit 5415077293989425242018873567807950481

noncomputable def ep1049 := BSN.sin_dyadic_bound_f 1525461197 2147483648 2 1 1048576 391196 ep1048 ep58 ep1048 ep1048 ep59 ep1048 683773 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1525461197) qz15 0 1 ep1048 ep58 ep1048 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1525461197) qz16 0 1 ep1048 ep59 ep1048 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1050 := @Enclosure.Real.IsNear.sin_image qz169 qz462 Bool.false 435579077 1048576 733 1048576 Bool.false 683773 1048576 1 195407 (@Enclosure.Real.IsNear.recentre' qz169 Bool.false 233849736324627548827 562949953421312000 17055250013330860947 24425875000000000000000 435579077 1048576 733 1048576 (ep1042 rfl) rfl) (Enclosure.sfrac_false_div 435579077 1048576) (BSN.sin_reduce0 qz462 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 107344788763122570625024) qz24) 226375608064910080 72057594037927936 Bool.false 683773 1048576 66 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q0 435579077 1048576 226375608064910080 72057594037927936 66 107344788763122570625024 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 683773 1048576 107344788763122570625024 151115727451828646838272 1525461197 2147483648 391196 390814 (ep1049 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1051 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz57 (Real.cos qz169)) (@HMul.hMul Real Real Real qz0 qz57 (@Neg.neg Real Real.instNeg (Real.sin qz169))) Bool.false 45475403729 274877906944 4165658529851 26856533581103104 Bool.true 78229785157 549755813888 16640907010481 107426134324412416 (@Enclosure.Real.IsNear.mulLit_ff qz57 (Real.cos qz169) 114409 524288 1 524288 397481 524288 144281907 204899090432 45475403729 274877906944 4165658529851 26856533581103104 qz363 (@Enclosure.Real.IsNear.recentre' (Real.cos qz169) Bool.false 794962 1048576 144281907 204899090432 397481 524288 144281907 204899090432 (ep1047 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz57 (@Neg.neg Real Real.instNeg (Real.sin qz169)) 114409 524288 1 524288 683773 1048576 144281907 204899090432 78229785157 549755813888 16640907010481 107426134324412416 qz363 (@Enclosure.Real.IsNear.neg (Real.sin qz169) Bool.false 683773 1048576 144281907 204899090432 (@Enclosure.Real.IsNear.recentre' (Real.sin qz169) Bool.false 683773 1048576 144281907 204899090432 683773 1048576 144281907 204899090432 (ep1050 rfl rfl) rfl)) rfl)

noncomputable def ep1052 := @ep988 45475403729 274877906944 4165658529851 26856533581103104 Bool.true 78229785157 549755813888 16640907010481 107426134324412416 Bool.false ep989 4962618704409 1099511627776 1034056624121321 214852268648824832 Bool.false 4097067661841452236800 14905045325 549755813888 516965726618183 107426134324412416 (ep990 (BSN.head_sum_c_succ qz143 20 21 rfl rfl) (ep1040 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1041 ep1051) rfl rfl

noncomputable abbrev qz170 := (@HMul.hMul Real Real Real qz269 qz441 qz592)

noncomputable def ep1053 := @Enclosure.Complex.IsNear.of_eq qz663 (Complex.mk (@HMul.hMul Real Real Real qz0 qz59 (Real.cos qz170)) (@HMul.hMul Real Real Real qz0 qz59 (@Neg.neg Real Real.instNeg (Real.sin qz170)))) Bool.false 167557983513 1099511627776 32401833870269 214852268648824832 Bool.true 1280758053 8589934592 16199334431545 107426134324412416 (BSN.cpow_neg_s_mk qz146 136442 1000 22 qz147 rfl)

noncomputable def ep1054 := @Enclosure.Real.IsNear.mulLit_ff qz146 qz592 136442 1000 0 1 3480203401436407 1125899906842624 250000000195407 48851750000000000000 237422956249393121947 562949953421312000 17055250013330860947 24425875000000000000000 qz148 (BSN.isNear_log_sfrac 22 1 3480203401436407 1125899906842624 250000000195407 48851750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz364) Bool.false 58388124189833310502912 18889465931478580854784 1000000000781628 195407000000000000000 3480203401436407 1125899906842624 250000000195407 48851750000000000000 (BSN.log_rat_reduce_isNear 22 1 4 44 32 166961 524288 24973259072661432 36028797018963968 195407 1000000000000000 rfl rfl rfl rfl (ep365 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1055 := nat_lit 273446714889077401244435136413407185769637819188023327388082569647265384005601

noncomputable def ep1056 := nat_lit 58546635456168549874515476835956924203071754258004582140550469794178301921

noncomputable def ep1057 := nat_lit 820223051396319866633556378286549643460507314055553972999966608002207795412961

noncomputable def ep1058 := BSN.cos_dyadic_bound_f 1663174213 2147483648 3 2 1048576 391196 ep1055 ep79 ep1056 ep1057 ep81 ep1056 749509 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1663174213) qz19 0 2 ep1055 ep79 ep1056 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1663174213) qz20 0 2 ep1057 ep81 ep1056 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz463 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 442234717) qz23)

noncomputable def ep1059 := @Enclosure.Real.IsNear.cos_image qz170 qz463 Bool.false 442234717 1048576 733 1048576 Bool.false 749509 1048576 1 195407 (@Enclosure.Real.IsNear.recentre' qz170 Bool.false 237422956249393121947 562949953421312000 17055250013330860947 24425875000000000000000 442234717 1048576 733 1048576 (ep1054 rfl) rfl) (Enclosure.sfrac_false_div 442234717 1048576) (BSN.cos_reduce0 qz463 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 117035480719227338358784) qz24) 226375608064910080 72057594037927936 Bool.false 749509 1048576 67 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q0 442234717 1048576 226375608064910080 72057594037927936 67 117035480719227338358784 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 749509 1048576 117035480719227338358784 151115727451828646838272 1663174213 2147483648 391196 390814 (ep1058 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1060 := nat_lit 7651577318185352420330931910229858161

noncomputable def ep1061 := BSN.sin_dyadic_bound_f 1663174213 2147483648 2 1 1048576 391196 ep1060 ep58 ep1060 ep1060 ep59 ep1060 733312 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1663174213) qz15 0 1 ep1060 ep58 ep1060 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1663174213) qz16 0 1 ep1060 ep59 ep1060 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1062 := @Enclosure.Real.IsNear.sin_image qz170 qz463 Bool.false 442234717 1048576 733 1048576 Bool.false 733312 1048576 1 195407 (@Enclosure.Real.IsNear.recentre' qz170 Bool.false 237422956249393121947 562949953421312000 17055250013330860947 24425875000000000000000 442234717 1048576 733 1048576 (ep1054 rfl) rfl) (Enclosure.sfrac_false_div 442234717 1048576) (BSN.sin_reduce0 qz463 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 117035480719227338358784) qz24) 226375608064910080 72057594037927936 Bool.false 733312 1048576 67 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q0 442234717 1048576 226375608064910080 72057594037927936 67 117035480719227338358784 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 733312 1048576 117035480719227338358784 151115727451828646838272 1663174213 2147483648 391196 390814 (ep1061 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1063 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz59 (Real.cos qz170)) (@HMul.hMul Real Real Real qz0 qz59 (@Neg.neg Real Real.instNeg (Real.sin qz170))) Bool.false 167557983513 1099511627776 32401833870269 214852268648824832 Bool.true 1280758053 8589934592 16199334431545 107426134324412416 (@Enclosure.Real.IsNear.mulLit_ff qz59 (Real.cos qz170) 223557 1048576 1 1048576 749509 1048576 144281907 204899090432 167557983513 1099511627776 32401833870269 214852268648824832 qz366 (@Enclosure.Real.IsNear.recentre' (Real.cos qz170) Bool.false 749509 1048576 144281907 204899090432 749509 1048576 144281907 204899090432 (ep1059 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz59 (@Neg.neg Real Real.instNeg (Real.sin qz170)) 223557 1048576 1 1048576 5729 8192 144281907 204899090432 1280758053 8589934592 16199334431545 107426134324412416 qz366 (@Enclosure.Real.IsNear.neg (Real.sin qz170) Bool.false 5729 8192 144281907 204899090432 (@Enclosure.Real.IsNear.recentre' (Real.sin qz170) Bool.false 733312 1048576 144281907 204899090432 5729 8192 144281907 204899090432 (ep1062 rfl rfl) rfl)) rfl)

noncomputable def ep1064 := @ep985 167557983513 1099511627776 32401833870269 214852268648824832 Bool.true 1280758053 8589934592 16199334431545 107426134324412416 Bool.false ep986 2565088343961 549755813888 533229228995795 107426134324412416 Bool.true 576070821388079857664 67063470067 549755813888 4165352039451 839266674409472 (ep987 (BSN.head_sum_c_succ qz143 21 22 rfl rfl) (ep1052 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1053 ep1063) rfl rfl

noncomputable abbrev qz171 := (@HMul.hMul Real Real Real qz269 qz441 qz593)

noncomputable def ep1065 := @Enclosure.Complex.IsNear.of_eq qz662 (Complex.mk (@HMul.hMul Real Real Real qz0 qz61 (Real.cos qz171)) (@HMul.hMul Real Real Real qz0 qz61 (@Neg.neg Real Real.instNeg (Real.sin qz171)))) Bool.false 97350577107 549755813888 15860191408397 107426134324412416 Bool.true 60525411189 549755813888 15827279789015 107426134324412416 (BSN.cpow_neg_s_mk qz146 136442 1000 23 qz147 rfl)

noncomputable def ep1066 := @Enclosure.Real.IsNear.mulLit_ff qz146 qz593 136442 1000 0 1 3530250507853047 1125899906842624 250000000195407 48851750000000000000 240837219896242719387 562949953421312000 17055250013330860947 24425875000000000000000 qz148 (BSN.isNear_log_sfrac 23 1 3530250507853047 1125899906842624 250000000195407 48851750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz367) Bool.false 59227775304360265777152 18889465931478580854784 1000000000781628 195407000000000000000 3530250507853047 1125899906842624 250000000195407 48851750000000000000 (BSN.log_rat_reduce_isNear 23 1 4 46 32 190266 524288 24973259072661432 36028797018963968 195407 1000000000000000 rfl rfl rfl rfl (ep379 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1067 := nat_lit 2035977395687974993810609851556577536

noncomputable def ep1068 := BSN.cos_dyadic_bound_f 1194519484 2147483648 2 1 1048576 391196 ep1067 ep62 ep1067 ep1067 ep63 ep1067 890498 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1194519484) qz19 0 1 ep1067 ep62 ep1067 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1194519484) qz20 0 1 ep1067 ep63 ep1067 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz464 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 448594279) qz23)

noncomputable def ep1069 := @Enclosure.Real.IsNear.cos_image qz171 qz464 Bool.false 448594279 1048576 733 1048576 Bool.false 890498 1048576 1 195407 (@Enclosure.Real.IsNear.recentre' qz171 Bool.false 240837219896242719387 562949953421312000 17055250013330860947 24425875000000000000000 448594279 1048576 733 1048576 (ep1066 rfl) rfl) (Enclosure.sfrac_false_div 448594279 1048576) (BSN.cos_reduce0 qz464 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 84056836020208851222528) qz24) 226375608064910080 72057594037927936 Bool.false 890498 1048576 68 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q0 448594279 1048576 226375608064910080 72057594037927936 68 84056836020208851222528 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 890498 1048576 84056836020208851222528 151115727451828646838272 1194519484 2147483648 391196 390814 (ep1068 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1070 := BSN.sin_dyadic_bound_f 1194519484 2147483648 2 1 1048576 391196 ep1067 ep58 ep1067 ep1067 ep59 ep1067 553646 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1194519484) qz15 0 1 ep1067 ep58 ep1067 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1194519484) qz16 0 1 ep1067 ep59 ep1067 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1071 := @Enclosure.Real.IsNear.sin_image qz171 qz464 Bool.false 448594279 1048576 733 1048576 Bool.false 553646 1048576 1 195407 (@Enclosure.Real.IsNear.recentre' qz171 Bool.false 240837219896242719387 562949953421312000 17055250013330860947 24425875000000000000000 448594279 1048576 733 1048576 (ep1066 rfl) rfl) (Enclosure.sfrac_false_div 448594279 1048576) (BSN.sin_reduce0 qz464 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 84056836020208851222528) qz24) 226375608064910080 72057594037927936 Bool.false 553646 1048576 68 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q0 448594279 1048576 226375608064910080 72057594037927936 68 84056836020208851222528 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 553646 1048576 84056836020208851222528 151115727451828646838272 1194519484 2147483648 391196 390814 (ep1070 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1072 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz61 (Real.cos qz171)) (@HMul.hMul Real Real Real qz0 qz61 (@Neg.neg Real Real.instNeg (Real.sin qz171))) Bool.false 97350577107 549755813888 15860191408397 107426134324412416 Bool.true 60525411189 549755813888 15827279789015 107426134324412416 (@Enclosure.Real.IsNear.mulLit_ff qz61 (Real.cos qz171) 218643 1048576 1 1048576 445249 524288 144281907 204899090432 97350577107 549755813888 15860191408397 107426134324412416 qz369 (@Enclosure.Real.IsNear.recentre' (Real.cos qz171) Bool.false 890498 1048576 144281907 204899090432 445249 524288 144281907 204899090432 (ep1069 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz61 (@Neg.neg Real Real.instNeg (Real.sin qz171)) 218643 1048576 1 1048576 276823 524288 144281907 204899090432 60525411189 549755813888 15827279789015 107426134324412416 qz369 (@Enclosure.Real.IsNear.neg (Real.sin qz171) Bool.false 276823 524288 144281907 204899090432 (@Enclosure.Real.IsNear.recentre' (Real.sin qz171) Bool.false 553646 1048576 144281907 204899090432 276823 524288 144281907 204899090432 (ep1071 rfl rfl) rfl)) rfl)

noncomputable def ep1073 := @ep982 97350577107 549755813888 15860191408397 107426134324412416 Bool.true 60525411189 549755813888 15827279789015 107426134324412416 Bool.false ep983 665609730267 137438953472 17159044387631 3357066697637888 Bool.true 70142729257951667683328 15948610157 68719476736 548992340838743 107426134324412416 (ep984 (BSN.head_sum_c_succ qz143 22 23 rfl rfl) (ep1064 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1065 ep1072) rfl rfl

noncomputable abbrev qz172 := (@HMul.hMul Real Real Real qz269 qz441 qz595)

noncomputable def ep1074 := @Enclosure.Complex.IsNear.of_eq qz661 (Complex.mk (@HMul.hMul Real Real Real qz0 qz63 (Real.cos qz172)) (@HMul.hMul Real Real Real qz0 qz63 (@Neg.neg Real Real.instNeg (Real.sin qz172)))) Bool.false 223716345307 1099511627776 31128166225251 214852268648824832 Bool.true 17959370373 1099511627776 30940320303709 214852268648824832 (BSN.cpow_neg_s_mk qz146 136442 1000 24 qz147 rfl)

noncomputable def ep1075 := @Enclosure.Real.IsNear.mulLit_ff qz146 qz595 136442 1000 0 1 3578169457974519 1125899906842624 250000000195407 48851750000000000000 244106298592479660699 562949953421312000 17055250013330860947 24425875000000000000000 qz148 (BSN.isNear_log_sfrac 24 1 3578169457974519 1125899906842624 250000000195407 48851750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz596) Bool.false 60031721881041427759104 18889465931478580854784 1000000000781628 195407000000000000000 3578169457974519 1125899906842624 250000000195407 48851750000000000000 (BSN.log_rat_reduce_isNear 24 1 4 48 32 212580 524288 24973259072661432 36028797018963968 195407 1000000000000000 rfl rfl rfl rfl (ep390 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1076 := nat_lit 875745693774361621130136903599761

noncomputable def ep1077 := BSN.cos_dyadic_bound_f 172026163 2147483648 2 1 1048576 391196 ep1076 ep62 ep1076 ep1076 ep63 ep1076 1045213 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 172026163) qz19 0 1 ep1076 ep62 ep1076 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 172026163) qz20 0 1 ep1076 ep63 ep1076 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz465 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 113670853) qz17)

noncomputable def ep1078 := @Enclosure.Real.IsNear.cos_image qz172 qz465 Bool.false 113670853 262144 367 524288 Bool.false 1045213 1048576 1 195407 (@Enclosure.Real.IsNear.recentre' qz172 Bool.false 244106298592479660699 562949953421312000 17055250013330860947 24425875000000000000000 113670853 262144 367 524288 (ep1075 rfl) rfl) (Enclosure.sfrac_false_div 113670853 262144) (BSN.cos_reduce0 qz465 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 3026316281256184119296) qz287) 226375608064910080 72057594037927936 Bool.false 1045213 1048576 69 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q0 113670853 262144 226375608064910080 72057594037927936 69 3026316281256184119296 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1045213 1048576 3026316281256184119296 37778931862957161709568 172026163 2147483648 391196 390814 (ep1077 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1079 := BSN.sin_dyadic_bound_f 172026163 2147483648 1 0 1048576 391196 0 1 1 0 1 1 83907 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 172026163) qz15 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 172026163) qz16 0 0 rfl) rfl rfl

noncomputable def ep1080 := @Enclosure.Real.IsNear.sin_image qz172 qz465 Bool.false 113670853 262144 367 524288 Bool.false 83907 1048576 1 195407 (@Enclosure.Real.IsNear.recentre' qz172 Bool.false 244106298592479660699 562949953421312000 17055250013330860947 24425875000000000000000 113670853 262144 367 524288 (ep1075 rfl) rfl) (Enclosure.sfrac_false_div 113670853 262144) (BSN.sin_reduce0 qz465 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 3026316281256184119296) qz287) 226375608064910080 72057594037927936 Bool.false 83907 1048576 69 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q0 113670853 262144 226375608064910080 72057594037927936 69 3026316281256184119296 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 83907 1048576 3026316281256184119296 37778931862957161709568 172026163 2147483648 391196 390814 (ep1079 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1081 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz63 (Real.cos qz172)) (@HMul.hMul Real Real Real qz0 qz63 (@Neg.neg Real Real.instNeg (Real.sin qz172))) Bool.false 223716345307 1099511627776 31128166225251 214852268648824832 Bool.true 17959370373 1099511627776 30940320303709 214852268648824832 (@Enclosure.Real.IsNear.mulLit_ff qz63 (Real.cos qz172) 214039 1048576 1 1048576 1045213 1048576 72238657 102449545216 223716345307 1099511627776 31128166225251 214852268648824832 qz371 (@Enclosure.Real.IsNear.recentre' (Real.cos qz172) Bool.false 1045213 1048576 72238657 102449545216 1045213 1048576 72238657 102449545216 (ep1078 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz63 (@Neg.neg Real Real.instNeg (Real.sin qz172)) 214039 1048576 1 1048576 83907 1048576 72238657 102449545216 17959370373 1099511627776 30940320303709 214852268648824832 qz371 (@Enclosure.Real.IsNear.neg (Real.sin qz172) Bool.false 83907 1048576 72238657 102449545216 (@Enclosure.Real.IsNear.recentre' (Real.sin qz172) Bool.false 83907 1048576 72238657 102449545216 83907 1048576 72238657 102449545216 (ep1080 rfl rfl) rfl)) rfl)

noncomputable def ep1082 := @ep980 223716345307 1099511627776 31128166225251 214852268648824832 Bool.true 17959370373 1099511627776 30940320303709 214852268648824832 Bool.false 762592978362988123652096 5548594187443 1099511627776 1129307007033635 214852268648824832 Bool.true 18769840849028498063360 273137132885 1099511627776 1128925001981195 214852268648824832 (ep981 (BSN.head_sum_c_succ qz143 23 24 rfl rfl) (ep1073 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1074 ep1081) rfl rfl

theorem EMRow46.d15 : Enclosure.Complex.IsNear qz164 Bool.false 5548594187443 1099511627776 1129307007033635 214852268648824832 Bool.true 273137132885 1099511627776 1128925001981195 214852268648824832 := ep979 (BSN.head_sum_c_succ qz143 24 25 rfl rfl) (ep1082 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable abbrev qz173 := (BSN.headSumC qz439 33)

noncomputable abbrev qz669 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 32) qz144)

noncomputable def ep1083 := @Enclosure.Complex.IsNear.of_eq qz173 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz143 32) qz669) Bool.false 5485948446639 1099511627776 1357571956475483 214852268648824832 Bool.true 22980239781 274877906944 678699430230261 107426134324412416

noncomputable def ep1084 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz143 32) qz669 Bool.false 5498038562951 1099511627776 1330814539840167 214852268648824832 Bool.false 25517394087 274877906944 665224843513983 107426134324412416 Bool.true

noncomputable abbrev qz670 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 31) qz144)

noncomputable def ep1085 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz143 32) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz143 31) qz670) Bool.false 5498038562951 1099511627776 1330814539840167 214852268648824832 Bool.false 25517394087 274877906944 665224843513983 107426134324412416

noncomputable def ep1086 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz143 31) qz670 Bool.false 5676478407161 1099511627776 1303456782116427 214852268648824832 Bool.false 8737036419 549755813888 651594650306163 107426134324412416 Bool.true

noncomputable def ep1087 := nat_lit 3022578664962736928063488

noncomputable abbrev qz671 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 30) qz144)

noncomputable def ep1088 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz143 31) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz143 30) qz671) Bool.false 5676478407161 1099511627776 1303456782116427 214852268648824832 Bool.false 8737036419 549755813888 651594650306163 107426134324412416

noncomputable def ep1089 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz143 30) qz671 Bool.false 5550096544939 1099511627776 1275705878000041 214852268648824832 Bool.true 17311386661 137438953472 318852050160761 53713067162206208 Bool.false

noncomputable def ep1090 := nat_lit 3120677006746453402451968

noncomputable abbrev qz672 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 29) qz144)

noncomputable def ep1091 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz143 30) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz143 29) qz672) Bool.false 5550096544939 1099511627776 1275705878000041 214852268648824832 Bool.true 17311386661 137438953472 318852050160761 53713067162206208

noncomputable def ep1092 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz143 29) qz672 Bool.false 1350802980421 274877906944 623732237779165 107426134324412416 Bool.false 3324319657 1099511627776 1247171885427171 214852268648824832 Bool.false

noncomputable def ep1093 := nat_lit 1525598921609958356156416

noncomputable abbrev qz673 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 28) qz144)

noncomputable def ep1094 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz143 29) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz143 28) qz673) Bool.false 1350802980421 274877906944 623732237779165 107426134324412416 Bool.false 3324319657 1099511627776 1247171885427171 214852268648824832

noncomputable def ep1095 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz143 28) qz673 Bool.false 5535843804725 1099511627776 1218703485833885 214852268648824832 Bool.false 81638665917 549755813888 609191977274411 107426134324412416 Bool.true

noncomputable def ep1096 := nat_lit 5940894335229463871094784

noncomputable abbrev qz674 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 27) qz144)

noncomputable def ep1097 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz143 28) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz143 27) qz674) Bool.false 5535843804725 1099511627776 1218703485833885 214852268648824832 Bool.false 81638665917 549755813888 609191977274411 107426134324412416

noncomputable def ep1098 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz143 27) qz674 Bool.false 5727052393205 1099511627776 1189402244960645 214852268648824832 Bool.false 36321875281 549755813888 594590051480563 107426134324412416 Bool.true

noncomputable abbrev qz675 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 26) qz144)

noncomputable def ep1099 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz143 27) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz143 26) qz675) Bool.false 5727052393205 1099511627776 1189402244960645 214852268648824832 Bool.false 36321875281 549755813888 594590051480563 107426134324412416

noncomputable def ep1100 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz143 26) qz675 Bool.false 715730427251 137438953472 144966298459973 26856533581103104 Bool.true 142985067875 1099511627776 1159304498709505 214852268648824832 Bool.false

noncomputable abbrev qz676 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 25) qz144)

noncomputable def ep1101 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz143 26) (@HAdd.hAdd Complex Complex Complex qz4 qz164 qz676) Bool.false 715730427251 137438953472 144966298459973 26856533581103104 Bool.true 142985067875 1099511627776 1159304498709505 214852268648824832

noncomputable def ep1102 := @Enclosure.Complex.IsNear.addLitP qz164 qz676 Bool.false 5548594187443 1099511627776 1129307007033635 214852268648824832 Bool.true 273137132885 1099511627776 1128925001981195 214852268648824832 Bool.false

noncomputable def ep1103 := nat_lit 6295631416924471671390208

noncomputable abbrev qz174 := (@HMul.hMul Real Real Real qz269 qz441 qz606)

noncomputable def ep1104 := @Enclosure.Complex.IsNear.of_eq qz676 (Complex.mk (@HMul.hMul Real Real Real qz0 qz66 (Real.cos qz174)) (@HMul.hMul Real Real Real qz0 qz66 (@Neg.neg Real Real.instNeg (Real.sin qz174)))) Bool.false 177249230565 1099511627776 30423380646149 214852268648824832 Bool.false 65076032505 549755813888 15189748364155 107426134324412416 (BSN.cpow_neg_s_mk qz146 136442 1000 25 qz147 rfl)

noncomputable def ep1105 := @Enclosure.Real.IsNear.mulLit_ff qz146 qz606 136442 1000 0 1 3624129903009015 1125899906842624 250000000195407 48851750000000000000 49448353222635602463 112589990684262400 17055250013330860947 24425875000000000000000 qz148 (BSN.isNear_log_sfrac 25 1 3624129903009015 1125899906842624 250000000195407 48851750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz607) Bool.false 60802810194841294602240 18889465931478580854784 1000000000781628 195407000000000000000 3624129903009015 1125899906842624 250000000195407 48851750000000000000 (BSN.log_rat_reduce_isNear 25 1 4 50 32 233982 524288 24973259072661432 36028797018963968 195407 1000000000000000 rfl rfl rfl rfl (ep421 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1106 := nat_lit 1056527777456805462910739536237746499482175205399979519366684465004298784113185

noncomputable def ep1107 := nat_lit 269735159096721942184679021579506744015100935411788251643217235664447636001

noncomputable def ep1108 := nat_lit 2766659845938810091145542638397254963915386803104517750695798866153516281266721

noncomputable def ep1109 := BSN.sin_dyadic_bound_f 2013108557 2147483648 3 2 1048576 391196 ep1106 ep72 ep1107 ep1108 ep75 ep1107 845191 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2013108557) qz15 0 2 ep1106 ep72 ep1107 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2013108557) qz16 0 2 ep1108 ep75 ep1107 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz466 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 115130919) qz17)

noncomputable def ep1110 := @Enclosure.Real.IsNear.cos_image qz174 qz466 Bool.false 115130919 262144 733 1048576 Bool.false 845191 1048576 1 195407 (@Enclosure.Real.IsNear.recentre' qz174 Bool.false 49448353222635602463 112589990684262400 17055250013330860947 24425875000000000000000 115130919 262144 733 1048576 (ep1105 rfl) rfl) (Enclosure.sfrac_false_div 115130919 262144) (BSN.cos_reduce3 qz466 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 35414980272715399692288) qz287) 226375608064910080 72057594037927936 Bool.false 845191 1048576 69 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q3 115130919 262144 226375608064910080 72057594037927936 69 35414980272715399692288 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 845191 1048576 35414980272715399692288 37778931862957161709568 2013108557 2147483648 391196 390814 (ep1109 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1111 := nat_lit 587079758657823800258048488586116724931881825637949416648888354884905745678881

noncomputable def ep1112 := nat_lit 1760699805655277956889776107715191161307615275043024673443378630183388341764641

noncomputable def ep1113 := BSN.cos_dyadic_bound_f 2013108557 2147483648 3 2 1048576 391196 ep1111 ep79 ep1107 ep1112 ep81 ep1107 620614 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2013108557) qz19 0 2 ep1111 ep79 ep1107 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2013108557) qz20 0 2 ep1112 ep81 ep1107 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1114 := @Enclosure.Real.IsNear.sin_image qz174 qz466 Bool.false 115130919 262144 733 1048576 Bool.true 620614 1048576 1 195407 (@Enclosure.Real.IsNear.recentre' qz174 Bool.false 49448353222635602463 112589990684262400 17055250013330860947 24425875000000000000000 115130919 262144 733 1048576 (ep1105 rfl) rfl) (Enclosure.sfrac_false_div 115130919 262144) (BSN.sin_reduce3 qz466 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 35414980272715399692288) qz287) 226375608064910080 72057594037927936 Bool.false 620614 1048576 69 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q3 115130919 262144 226375608064910080 72057594037927936 69 35414980272715399692288 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 620614 1048576 35414980272715399692288 37778931862957161709568 2013108557 2147483648 391196 390814 (ep1113 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1115 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz66 (Real.cos qz174)) (@HMul.hMul Real Real Real qz0 qz66 (@Neg.neg Real Real.instNeg (Real.sin qz174))) Bool.false 177249230565 1099511627776 30423380646149 214852268648824832 Bool.false 65076032505 549755813888 15189748364155 107426134324412416 (@Enclosure.Real.IsNear.mulLit_ff qz66 (Real.cos qz174) 209715 1048576 1 1048576 845191 1048576 144281907 204899090432 177249230565 1099511627776 30423380646149 214852268648824832 qz373 (@Enclosure.Real.IsNear.recentre' (Real.cos qz174) Bool.false 845191 1048576 144281907 204899090432 845191 1048576 144281907 204899090432 (ep1110 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz66 (@Neg.neg Real Real.instNeg (Real.sin qz174)) 209715 1048576 1 1048576 310307 524288 144281907 204899090432 65076032505 549755813888 15189748364155 107426134324412416 qz373 (@Enclosure.Real.IsNear.neg (Real.sin qz174) Bool.true 310307 524288 144281907 204899090432 (@Enclosure.Real.IsNear.recentre' (Real.sin qz174) Bool.true 620614 1048576 144281907 204899090432 310307 524288 144281907 204899090432 (ep1114 rfl rfl) rfl)) rfl)

noncomputable def ep1116 := @ep1102 177249230565 1099511627776 30423380646149 214852268648824832 Bool.false 65076032505 549755813888 15189748364155 107426134324412416 Bool.false ep1103 715730427251 137438953472 144966298459973 26856533581103104 Bool.true 78606872363451547648000 142985067875 1099511627776 1159304498709505 214852268648824832 EMRow46.d15 (ep1104 ep1115) rfl rfl

noncomputable abbrev qz175 := (@HMul.hMul Real Real Real qz269 qz441 qz609)

noncomputable def ep1117 := @Enclosure.Complex.IsNear.of_eq qz675 (Complex.mk (@HMul.hMul Real Real Real qz0 qz68 (Real.cos qz175)) (@HMul.hMul Real Real Real qz0 qz68 (@Neg.neg Real Real.instNeg (Real.sin qz175)))) Bool.false 1208975197 1099511627776 29671857280861 214852268648824832 Bool.false 215628818437 1099511627776 29875604251621 214852268648824832 (BSN.cpow_neg_s_mk qz146 136442 1000 26 qz147 rfl)

noncomputable def ep1118 := @Enclosure.Real.IsNear.mulLit_ff qz146 qz609 136442 1000 0 1 3668288609262839 1125899906842624 250000000195407 48851750000000000000 250254317212520139419 562949953421312000 17055250013330860947 24425875000000000000000 qz148 (BSN.isNear_log_sfrac 26 1 3668288609262839 1125899906842624 250000000195407 48851750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz610) Bool.false 61543670347942250676224 18889465931478580854784 1000000000781628 195407000000000000000 3668288609262839 1125899906842624 250000000195407 48851750000000000000 (BSN.log_rat_reduce_isNear 26 1 4 52 32 254545 524288 24973259072661432 36028797018963968 195407 1000000000000000 rfl rfl rfl rfl (ep432 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1119 := BSN.sin_dyadic_bound_f 12041925 2147483648 1 0 1048576 391196 0 1 1 0 1 1 5879 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 12041925) qz15 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 12041925) qz16 0 0 rfl) rfl rfl

noncomputable abbrev qz467 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 233067495) qz42)

noncomputable def ep1120 := @Enclosure.Real.IsNear.cos_image qz175 qz467 Bool.false 233067495 524288 733 1048576 Bool.false 5879 1048576 1 195407 (@Enclosure.Real.IsNear.recentre' qz175 Bool.false 250254317212520139419 562949953421312000 17055250013330860947 24425875000000000000000 233067495 524288 733 1048576 (ep1118 rfl) rfl) (Enclosure.sfrac_false_div 233067495 524288) (BSN.cos_reduce3 qz467 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 423687572230053560320) qz43) 226375608064910080 72057594037927936 Bool.false 5879 1048576 70 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q3 233067495 524288 226375608064910080 72057594037927936 70 423687572230053560320 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 5879 1048576 423687572230053560320 75557863725914323419136 12041925 2147483648 391196 390814 (ep1119 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1121 := BSN.cos_dyadic_bound_f 12041925 2147483648 1 0 1048576 391196 0 1 1 0 1 1 1048559 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 12041925) qz19 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 12041925) qz20 0 0 rfl) rfl rfl

noncomputable def ep1122 := @Enclosure.Real.IsNear.sin_image qz175 qz467 Bool.false 233067495 524288 733 1048576 Bool.true 1048559 1048576 1 195407 (@Enclosure.Real.IsNear.recentre' qz175 Bool.false 250254317212520139419 562949953421312000 17055250013330860947 24425875000000000000000 233067495 524288 733 1048576 (ep1118 rfl) rfl) (Enclosure.sfrac_false_div 233067495 524288) (BSN.sin_reduce3 qz467 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 423687572230053560320) qz43) 226375608064910080 72057594037927936 Bool.false 1048559 1048576 70 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q3 233067495 524288 226375608064910080 72057594037927936 70 423687572230053560320 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1048559 1048576 423687572230053560320 75557863725914323419136 12041925 2147483648 391196 390814 (ep1121 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1123 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz68 (Real.cos qz175)) (@HMul.hMul Real Real Real qz0 qz68 (@Neg.neg Real Real.instNeg (Real.sin qz175))) Bool.false 1208975197 1099511627776 29671857280861 214852268648824832 Bool.false 215628818437 1099511627776 29875604251621 214852268648824832 (@Enclosure.Real.IsNear.mulLit_ff qz68 (Real.cos qz175) 205643 1048576 1 1048576 5879 1048576 144281907 204899090432 1208975197 1099511627776 29671857280861 214852268648824832 qz375 (@Enclosure.Real.IsNear.recentre' (Real.cos qz175) Bool.false 5879 1048576 144281907 204899090432 5879 1048576 144281907 204899090432 (ep1120 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz68 (@Neg.neg Real Real.instNeg (Real.sin qz175)) 205643 1048576 1 1048576 1048559 1048576 144281907 204899090432 215628818437 1099511627776 29875604251621 214852268648824832 qz375 (@Enclosure.Real.IsNear.neg (Real.sin qz175) Bool.true 1048559 1048576 144281907 204899090432 (@Enclosure.Real.IsNear.recentre' (Real.sin qz175) Bool.true 1048559 1048576 144281907 204899090432 1048559 1048576 144281907 204899090432 (ep1122 rfl rfl) rfl)) rfl)

noncomputable def ep1124 := @ep1100 1208975197 1099511627776 29671857280861 214852268648824832 Bool.false 215628818437 1099511627776 29875604251621 214852268648824832 Bool.false 787120087401408243957760 5727052393205 1099511627776 1189402244960645 214852268648824832 Bool.false 79872648428178334810112 36321875281 549755813888 594590051480563 107426134324412416 (ep1101 (BSN.head_sum_c_succ qz143 25 26 rfl rfl) (ep1116 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1117 ep1123) rfl rfl

noncomputable abbrev qz176 := (@HMul.hMul Real Real Real qz269 qz441 qz612)

noncomputable def ep1125 := @Enclosure.Complex.IsNear.of_eq qz674 (Complex.mk (@HMul.hMul Real Real Real qz0 qz70 (Real.cos qz176)) (@HMul.hMul Real Real Real qz0 qz70 (@Neg.neg Real Real.instNeg (Real.sin qz176)))) Bool.true 2987634195 17179869184 3662655109155 26856533581103104 Bool.false 11329197659 137438953472 1825240724231 13428266790551552 (BSN.cpow_neg_s_mk qz146 136442 1000 27 qz147 rfl)

noncomputable def ep1126 := @Enclosure.Real.IsNear.mulLit_ff qz146 qz612 136442 1000 0 1 3710780868205815 1125899906842624 250000000195407 48851750000000000000 50630636321973781023 112589990684262400 17055250013330860947 24425875000000000000000 qz148 (BSN.isNear_log_sfrac 27 1 3710780868205815 1125899906842624 250000000195407 48851750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz613) Bool.false 62256572154556490711040 18889465931478580854784 1000000000781628 195407000000000000000 3710780868205815 1125899906842624 250000000195407 48851750000000000000 (BSN.log_rat_reduce_isNear 27 1 4 54 32 274332 524288 24973259072661432 36028797018963968 195407 1000000000000000 rfl rfl rfl rfl (ep447 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1127 := nat_lit 816401967159590804570493314987033616

noncomputable def ep1128 := BSN.cos_dyadic_bound_f 950552286 2147483648 2 1 1048576 391196 ep1127 ep62 ep1127 ep1127 ep63 ep1127 947520 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 950552286) qz19 0 1 ep1127 ep62 ep1127 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 950552286) qz20 0 1 ep1127 ep63 ep1127 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz468 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 471534545) qz23)

noncomputable def ep1129 := @Enclosure.Real.IsNear.cos_image qz176 qz468 Bool.false 471534545 1048576 733 1048576 Bool.true 947520 1048576 1 195407 (@Enclosure.Real.IsNear.recentre' qz176 Bool.false 50630636321973781023 112589990684262400 17055250013330860947 24425875000000000000000 471534545 1048576 733 1048576 (ep1126 rfl) rfl) (Enclosure.sfrac_false_div 471534545 1048576) (BSN.cos_reduce2 qz468 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 66889170688574603919360) qz24) 226375608064910080 72057594037927936 Bool.false 947520 1048576 71 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q2 471534545 1048576 226375608064910080 72057594037927936 71 66889170688574603919360 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 947520 1048576 66889170688574603919360 151115727451828646838272 950552286 2147483648 391196 390814 (ep1128 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1130 := BSN.sin_dyadic_bound_f 950552286 2147483648 2 1 1048576 391196 ep1127 ep58 ep1127 ep1127 ep59 ep1127 449128 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 950552286) qz15 0 1 ep1127 ep58 ep1127 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 950552286) qz16 0 1 ep1127 ep59 ep1127 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1131 := @Enclosure.Real.IsNear.sin_image qz176 qz468 Bool.false 471534545 1048576 733 1048576 Bool.true 449128 1048576 1 195407 (@Enclosure.Real.IsNear.recentre' qz176 Bool.false 50630636321973781023 112589990684262400 17055250013330860947 24425875000000000000000 471534545 1048576 733 1048576 (ep1126 rfl) rfl) (Enclosure.sfrac_false_div 471534545 1048576) (BSN.sin_reduce2 qz468 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 66889170688574603919360) qz24) 226375608064910080 72057594037927936 Bool.false 449128 1048576 71 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q2 471534545 1048576 226375608064910080 72057594037927936 71 66889170688574603919360 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 449128 1048576 66889170688574603919360 151115727451828646838272 950552286 2147483648 391196 390814 (ep1130 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1132 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz70 (Real.cos qz176)) (@HMul.hMul Real Real Real qz0 qz70 (@Neg.neg Real Real.instNeg (Real.sin qz176))) Bool.true 2987634195 17179869184 3662655109155 26856533581103104 Bool.false 11329197659 137438953472 1825240724231 13428266790551552 (@Enclosure.Real.IsNear.mulLit_ft qz70 (Real.cos qz176) 201799 1048576 1 1048576 14805 16384 144281907 204899090432 2987634195 17179869184 3662655109155 26856533581103104 qz377 (@Enclosure.Real.IsNear.recentre' (Real.cos qz176) Bool.true 947520 1048576 144281907 204899090432 14805 16384 144281907 204899090432 (ep1129 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz70 (@Neg.neg Real Real.instNeg (Real.sin qz176)) 201799 1048576 1 1048576 56141 131072 144281907 204899090432 11329197659 137438953472 1825240724231 13428266790551552 qz377 (@Enclosure.Real.IsNear.neg (Real.sin qz176) Bool.true 56141 131072 144281907 204899090432 (@Enclosure.Real.IsNear.recentre' (Real.sin qz176) Bool.true 449128 1048576 144281907 204899090432 56141 131072 144281907 204899090432 (ep1131 rfl rfl) rfl)) rfl)

noncomputable def ep1133 := @ep1098 2987634195 17179869184 3662655109155 26856533581103104 Bool.false 11329197659 137438953472 1825240724231 13428266790551552 Bool.false 95105072388232341094400 5535843804725 1099511627776 1218703485833885 214852268648824832 Bool.false 11220332806482715213824 81638665917 549755813888 609191977274411 107426134324412416 (ep1099 (BSN.head_sum_c_succ qz143 26 27 rfl rfl) (ep1124 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1125 ep1132) rfl rfl

noncomputable abbrev qz177 := (@HMul.hMul Real Real Real qz269 qz441 qz615)

noncomputable def ep1134 := @Enclosure.Complex.IsNear.of_eq qz673 (Complex.mk (@HMul.hMul Real Real Real qz0 qz72 (Real.cos qz177)) (@HMul.hMul Real Real Real qz0 qz72 (@Neg.neg Real Real.instNeg (Real.sin qz177)))) Bool.true 132631883041 1099511627776 28760989724445 214852268648824832 Bool.true 159953012177 1099511627776 28787930878349 214852268648824832 (BSN.cpow_neg_s_mk qz146 136442 1000 28 qz147 rfl)

noncomputable def ep1135 := @Enclosure.Real.IsNear.mulLit_ff qz146 qz615 136442 1000 0 1 3751726938922231 1125899906842624 250000000195407 48851750000000000000 255946563500213521051 562949953421312000 17055250013330860947 24425875000000000000000 qz148 (BSN.isNear_log_sfrac 28 1 3751726938922231 1125899906842624 250000000195407 48851750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz616) Bool.false 62943533227317076688896 18889465931478580854784 1000000000781628 195407000000000000000 3751726938922231 1125899906842624 250000000195407 48851750000000000000 (BSN.log_rat_reduce_isNear 28 1 4 56 32 293399 524288 24973259072661432 36028797018963968 195407 1000000000000000 rfl rfl rfl rfl (ep462 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1136 := nat_lit 4885058425572200446988202241600000000

noncomputable def ep1137 := BSN.sin_dyadic_bound_f 1486679800 2147483648 2 1 1048576 391196 ep1136 ep58 ep1136 ep1136 ep59 ep1136 669307 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1486679800) qz15 0 1 ep1136 ep58 ep1136 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1486679800) qz16 0 1 ep1136 ep59 ep1136 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz469 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 59592203) qz559)

noncomputable def ep1138 := @Enclosure.Real.IsNear.cos_image qz177 qz469 Bool.false 59592203 131072 367 524288 Bool.true 669307 1048576 1 195407 (@Enclosure.Real.IsNear.recentre' qz177 Bool.false 255946563500213521051 562949953421312000 17055250013330860947 24425875000000000000000 59592203 131072 367 524288 (ep1135 rfl) rfl) (Enclosure.sfrac_false_div 59592203 131072) (BSN.cos_reduce1 qz469 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 13076973817537155301376) qz316) 226375608064910080 72057594037927936 Bool.false 669307 1048576 72 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q1 59592203 131072 226375608064910080 72057594037927936 72 13076973817537155301376 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 669307 1048576 13076973817537155301376 18889465931478580854784 1486679800 2147483648 391196 390814 (ep1137 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1139 := nat_lit 174565284373903308537635134397769110535345156278653085138556969975808000000000

noncomputable def ep1140 := nat_lit 23863795821253945854024379823397429403739983177503264770560000000000000000

noncomputable def ep1141 := nat_lit 523648125530067417721197354433660536747227988869604248886129789927424000000000

noncomputable def ep1142 := BSN.cos_dyadic_bound_f 1486679800 2147483648 3 2 1048576 391196 ep1139 ep79 ep1140 ep1141 ep81 ep1140 807179 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1486679800) qz19 0 2 ep1139 ep79 ep1140 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1486679800) qz20 0 2 ep1141 ep81 ep1140 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1143 := @Enclosure.Real.IsNear.sin_image qz177 qz469 Bool.false 59592203 131072 367 524288 Bool.false 807179 1048576 1 195407 (@Enclosure.Real.IsNear.recentre' qz177 Bool.false 255946563500213521051 562949953421312000 17055250013330860947 24425875000000000000000 59592203 131072 367 524288 (ep1135 rfl) rfl) (Enclosure.sfrac_false_div 59592203 131072) (BSN.sin_reduce1 qz469 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 13076973817537155301376) qz316) 226375608064910080 72057594037927936 Bool.false 807179 1048576 72 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q1 59592203 131072 226375608064910080 72057594037927936 72 13076973817537155301376 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 807179 1048576 13076973817537155301376 18889465931478580854784 1486679800 2147483648 391196 390814 (ep1142 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1144 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz72 (Real.cos qz177)) (@HMul.hMul Real Real Real qz0 qz72 (@Neg.neg Real Real.instNeg (Real.sin qz177))) Bool.true 132631883041 1099511627776 28760989724445 214852268648824832 Bool.true 159953012177 1099511627776 28787930878349 214852268648824832 (@Enclosure.Real.IsNear.mulLit_ft qz72 (Real.cos qz177) 198163 1048576 1 1048576 669307 1048576 72238657 102449545216 132631883041 1099511627776 28760989724445 214852268648824832 qz379 (@Enclosure.Real.IsNear.recentre' (Real.cos qz177) Bool.true 669307 1048576 72238657 102449545216 669307 1048576 72238657 102449545216 (ep1138 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz72 (@Neg.neg Real Real.instNeg (Real.sin qz177)) 198163 1048576 1 1048576 807179 1048576 72238657 102449545216 159953012177 1099511627776 28787930878349 214852268648824832 qz379 (@Enclosure.Real.IsNear.neg (Real.sin qz177) Bool.false 807179 1048576 72238657 102449545216 (@Enclosure.Real.IsNear.recentre' (Real.sin qz177) Bool.false 807179 1048576 72238657 102449545216 807179 1048576 72238657 102449545216 (ep1143 rfl rfl) rfl)) rfl)

noncomputable def ep1145 := @ep1095 132631883041 1099511627776 28760989724445 214852268648824832 Bool.true 159953012177 1099511627776 28787930878349 214852268648824832 Bool.false ep1096 1350802980421 274877906944 623732237779165 107426134324412416 Bool.false 1827564058657911996416 3324319657 1099511627776 1247171885427171 214852268648824832 (ep1097 (BSN.head_sum_c_succ qz143 27 28 rfl rfl) (ep1133 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1134 ep1144) rfl rfl

noncomputable abbrev qz178 := (@HMul.hMul Real Real Real qz269 qz441 qz618)

noncomputable def ep1146 := @Enclosure.Complex.IsNear.of_eq qz672 (Complex.mk (@HMul.hMul Real Real Real qz0 qz74 (Real.cos qz178)) (@HMul.hMul Real Real Real qz0 qz74 (@Neg.neg Real Real.instNeg (Real.sin qz178)))) Bool.false 146884623255 1099511627776 28241402441711 214852268648824832 Bool.true 141815412945 1099511627776 28236315215873 214852268648824832 (BSN.cpow_neg_s_mk qz146 136442 1000 29 qz147 rfl)

noncomputable def ep1147 := @Enclosure.Real.IsNear.mulLit_ff qz146 qz618 136442 1000 0 1 3791236343078135 1125899906842624 250000000195407 48851750000000000000 51728386912226689567 112589990684262400 17055250013330860947 24425875000000000000000 qz148 (BSN.isNear_log_sfrac 29 1 3791236343078135 1125899906842624 250000000195407 48851750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz619) Bool.false 63606391034871975772160 18889465931478580854784 1000000000781628 195407000000000000000 3791236343078135 1125899906842624 250000000195407 48851750000000000000 (BSN.log_rat_reduce_isNear 29 1 4 58 32 311797 524288 24973259072661432 36028797018963968 195407 1000000000000000 rfl rfl rfl rfl (ep473 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1148 := nat_lit 264194495063880631931641993079636646236390764659435752395169014517494535099521

noncomputable def ep1149 := nat_lit 54652538776822879751393596944183351055504973935460566117185404340381095041

noncomputable def ep1150 := nat_lit 792474180114088250035423192045021572007061284030436336053272672743802843108481

noncomputable def ep1151 := BSN.cos_dyadic_bound_f 1648926481 2147483648 3 2 1048576 391196 ep1148 ep79 ep1149 ep1150 ep81 ep1149 754357 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1648926481) qz19 0 2 ep1148 ep79 ep1149 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1648926481) qz20 0 2 ep1150 ep81 ep1149 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz470 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 7527471) (@Nat.cast Real Real.instNatCast 16384))

noncomputable def ep1152 := @Enclosure.Real.IsNear.cos_image qz178 qz470 Bool.false 7527471 16384 733 1048576 Bool.false 754357 1048576 1 195407 (@Enclosure.Real.IsNear.recentre' qz178 Bool.false 51728386912226689567 112589990684262400 17055250013330860947 24425875000000000000000 7527471 16384 733 1048576 (ep1147 rfl) rfl) (Enclosure.sfrac_false_div 7527471 16384) (BSN.cos_reduce0 qz470 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 1813013840188745449472) (@Nat.cast Real Real.instNatCast 2361183241434822606848)) 226375608064910080 72057594037927936 Bool.false 754357 1048576 73 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q0 7527471 16384 226375608064910080 72057594037927936 73 1813013840188745449472 2361183241434822606848 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 754357 1048576 1813013840188745449472 2361183241434822606848 1648926481 2147483648 391196 390814 (ep1151 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1153 := nat_lit 7392735540841622704028532594326176321

noncomputable def ep1154 := BSN.sin_dyadic_bound_f 1648926481 2147483648 2 1 1048576 391196 ep1153 ep58 ep1153 ep1153 ep59 ep1153 728323 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1648926481) qz15 0 1 ep1153 ep58 ep1153 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1648926481) qz16 0 1 ep1153 ep59 ep1153 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1155 := @Enclosure.Real.IsNear.sin_image qz178 qz470 Bool.false 7527471 16384 733 1048576 Bool.false 728323 1048576 1 195407 (@Enclosure.Real.IsNear.recentre' qz178 Bool.false 51728386912226689567 112589990684262400 17055250013330860947 24425875000000000000000 7527471 16384 733 1048576 (ep1147 rfl) rfl) (Enclosure.sfrac_false_div 7527471 16384) (BSN.sin_reduce0 qz470 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 1813013840188745449472) (@Nat.cast Real Real.instNatCast 2361183241434822606848)) 226375608064910080 72057594037927936 Bool.false 728323 1048576 73 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q0 7527471 16384 226375608064910080 72057594037927936 73 1813013840188745449472 2361183241434822606848 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 728323 1048576 1813013840188745449472 2361183241434822606848 1648926481 2147483648 391196 390814 (ep1154 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1156 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz74 (Real.cos qz178)) (@HMul.hMul Real Real Real qz0 qz74 (@Neg.neg Real Real.instNeg (Real.sin qz178))) Bool.false 146884623255 1099511627776 28241402441711 214852268648824832 Bool.true 141815412945 1099511627776 28236315215873 214852268648824832 (@Enclosure.Real.IsNear.mulLit_ff qz74 (Real.cos qz178) 194715 1048576 1 1048576 754357 1048576 144281907 204899090432 146884623255 1099511627776 28241402441711 214852268648824832 qz381 (@Enclosure.Real.IsNear.recentre' (Real.cos qz178) Bool.false 754357 1048576 144281907 204899090432 754357 1048576 144281907 204899090432 (ep1152 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz74 (@Neg.neg Real Real.instNeg (Real.sin qz178)) 194715 1048576 1 1048576 728323 1048576 144281907 204899090432 141815412945 1099511627776 28236315215873 214852268648824832 qz381 (@Enclosure.Real.IsNear.neg (Real.sin qz178) Bool.false 728323 1048576 144281907 204899090432 (@Enclosure.Real.IsNear.recentre' (Real.sin qz178) Bool.false 728323 1048576 144281907 204899090432 728323 1048576 144281907 204899090432 (ep1155 rfl rfl) rfl)) rfl)

noncomputable def ep1157 := @ep1092 146884623255 1099511627776 28241402441711 214852268648824832 Bool.true 141815412945 1099511627776 28236315215873 214852268648824832 Bool.false ep1093 5550096544939 1099511627776 1275705878000041 214852268648824832 Bool.true 152272567413566747967488 17311386661 137438953472 318852050160761 53713067162206208 (ep1094 (BSN.head_sum_c_succ qz143 28 29 rfl rfl) (ep1145 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1146 ep1156) rfl rfl

noncomputable abbrev qz179 := (@HMul.hMul Real Real Real qz269 qz441 qz621)

noncomputable def ep1158 := @Enclosure.Complex.IsNear.of_eq qz671 (Complex.mk (@HMul.hMul Real Real Real qz0 qz76 (Real.cos qz179)) (@HMul.hMul Real Real Real qz0 qz76 (@Neg.neg Real Real.instNeg (Real.sin qz179)))) Bool.false 63190931111 549755813888 13875452058193 107426134324412416 Bool.false 77982583063 549755813888 13890549984641 107426134324412416 (BSN.cpow_neg_s_mk qz146 136442 1000 30 qz147 rfl)

noncomputable def ep1159 := @Enclosure.Real.IsNear.mulLit_ff qz146 qz621 136442 1000 0 1 3829405717437687 1125899906842624 250000000195407 48851750000000000000 261245887449316444827 562949953421312000 17055250013330860947 24425875000000000000000 qz148 (BSN.isNear_log_sfrac 30 1 3829405717437687 1125899906842624 250000000195407 48851750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz622) Bool.false 64246766873087041339392 18889465931478580854784 1000000000781628 195407000000000000000 3829405717437687 1125899906842624 250000000195407 48851750000000000000 (BSN.log_rat_reduce_isNear 30 1 4 60 32 329571 524288 24973259072661432 36028797018963968 195407 1000000000000000 rfl rfl rfl rfl (ep484 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1160 := nat_lit 4574191393524788902644470864329506481

noncomputable def ep1161 := BSN.sin_dyadic_bound_f 1462441771 2147483648 2 1 1048576 391196 ep1160 ep58 ep1160 ep1160 ep59 ep1160 660154 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1462441771) qz15 0 1 ep1160 ep58 ep1160 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1462441771) qz16 0 1 ep1160 ep59 ep1160 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz471 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 486608385) qz23)

noncomputable def ep1162 := @Enclosure.Real.IsNear.cos_image qz179 qz471 Bool.false 486608385 1048576 733 1048576 Bool.false 660154 1048576 1 195407 (@Enclosure.Real.IsNear.recentre' qz179 Bool.false 261245887449316444827 562949953421312000 17055250013330860947 24425875000000000000000 486608385 1048576 733 1048576 (ep1159 rfl) rfl) (Enclosure.sfrac_false_div 486608385 1048576) (BSN.cos_reduce3 qz471 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 102910190893493513093120) qz24) 226375608064910080 72057594037927936 Bool.false 660154 1048576 73 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q3 486608385 1048576 226375608064910080 72057594037927936 73 102910190893493513093120 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 660154 1048576 102910190893493513093120 151115727451828646838272 1462441771 2147483648 391196 390814 (ep1161 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1163 := nat_lit 163455174011394705553376648674180778251436557206498490360893163853284717868641

noncomputable def ep1164 := nat_lit 20923226904596250212511910525649386441596124105701368873115913689021003361

noncomputable def ep1165 := nat_lit 490323675580374924159704922201491035981426479371284068344933259732476111599201

noncomputable def ep1166 := BSN.cos_dyadic_bound_f 1462441771 2147483648 3 2 1048576 391196 ep1163 ep79 ep1164 ep1165 ep81 ep1164 814682 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1462441771) qz19 0 2 ep1163 ep79 ep1164 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1462441771) qz20 0 2 ep1165 ep81 ep1164 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1167 := @Enclosure.Real.IsNear.sin_image qz179 qz471 Bool.false 486608385 1048576 733 1048576 Bool.true 814682 1048576 1 195407 (@Enclosure.Real.IsNear.recentre' qz179 Bool.false 261245887449316444827 562949953421312000 17055250013330860947 24425875000000000000000 486608385 1048576 733 1048576 (ep1159 rfl) rfl) (Enclosure.sfrac_false_div 486608385 1048576) (BSN.sin_reduce3 qz471 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 102910190893493513093120) qz24) 226375608064910080 72057594037927936 Bool.false 814682 1048576 73 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q3 486608385 1048576 226375608064910080 72057594037927936 73 102910190893493513093120 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 814682 1048576 102910190893493513093120 151115727451828646838272 1462441771 2147483648 391196 390814 (ep1166 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1168 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz76 (Real.cos qz179)) (@HMul.hMul Real Real Real qz0 qz76 (@Neg.neg Real Real.instNeg (Real.sin qz179))) Bool.false 63190931111 549755813888 13875452058193 107426134324412416 Bool.false 77982583063 549755813888 13890549984641 107426134324412416 (@Enclosure.Real.IsNear.mulLit_ff qz76 (Real.cos qz179) 191443 1048576 1 1048576 330077 524288 144281907 204899090432 63190931111 549755813888 13875452058193 107426134324412416 qz383 (@Enclosure.Real.IsNear.recentre' (Real.cos qz179) Bool.false 660154 1048576 144281907 204899090432 330077 524288 144281907 204899090432 (ep1162 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz76 (@Neg.neg Real Real.instNeg (Real.sin qz179)) 191443 1048576 1 1048576 407341 524288 144281907 204899090432 77982583063 549755813888 13890549984641 107426134324412416 qz383 (@Enclosure.Real.IsNear.neg (Real.sin qz179) Bool.true 407341 524288 144281907 204899090432 (@Enclosure.Real.IsNear.recentre' (Real.sin qz179) Bool.true 814682 1048576 144281907 204899090432 407341 524288 144281907 204899090432 (ep1167 rfl rfl) rfl)) rfl)

noncomputable def ep1169 := @ep1089 63190931111 549755813888 13875452058193 107426134324412416 Bool.false 77982583063 549755813888 13890549984641 107426134324412416 Bool.false ep1090 5676478407161 1099511627776 1303456782116427 214852268648824832 Bool.false 1200809141874110496768 8737036419 549755813888 651594650306163 107426134324412416 (ep1091 (BSN.head_sum_c_succ qz143 29 30 rfl rfl) (ep1157 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1158 ep1168) rfl rfl

noncomputable abbrev qz180 := (@HMul.hMul Real Real Real qz269 qz441 qz623)

noncomputable def ep1170 := @Enclosure.Complex.IsNear.of_eq qz670 (Complex.mk (@HMul.hMul Real Real Real qz0 qz384 (Real.cos qz180)) (@HMul.hMul Real Real Real qz0 qz384 (@Neg.neg Real Real.instNeg (Real.sin qz180)))) Bool.true 89219922105 549755813888 6839439430935 53713067162206208 Bool.false 42297751755 549755813888 3407548301955 26856533581103104 (BSN.cpow_neg_s_mk qz146 136442 1000 31 qz147 rfl)

noncomputable def ep1171 := @Enclosure.Real.IsNear.mulLit_ff qz146 qz623 136442 1000 0 1 3866325256314103 1125899906842624 250000000195407 48851750000000000000 263764575311004420763 562949953421312000 17055250013330860947 24425875000000000000000 qz148 (BSN.isNear_log_sfrac 31 1 3866325256314103 1125899906842624 250000000195407 48851750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz624) Bool.false 64866173951437069877248 18889465931478580854784 1000000000781628 195407000000000000000 3866325256314103 1125899906842624 250000000195407 48851750000000000000 (BSN.log_rat_reduce_isNear 31 1 4 62 32 346763 524288 24973259072661432 36028797018963968 195407 1000000000000000 rfl rfl rfl rfl (ep494 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1172 := nat_lit 816887904660395162074109163032914801

noncomputable def ep1173 := BSN.cos_dyadic_bound_f 950693701 2147483648 2 1 1048576 391196 ep1172 ep62 ep1172 ep1172 ep63 ep1172 947490 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 950693701) qz19 0 1 ep1172 ep62 ep1172 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 950693701) qz20 0 1 ep1172 ep63 ep1172 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz472 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 245649903) qz42)

noncomputable def ep1174 := @Enclosure.Real.IsNear.cos_image qz180 qz472 Bool.false 245649903 524288 733 1048576 Bool.true 947490 1048576 1 195407 (@Enclosure.Real.IsNear.recentre' qz180 Bool.false 263764575311004420763 562949953421312000 17055250013330860947 24425875000000000000000 245649903 524288 733 1048576 (ep1171 rfl) rfl) (Enclosure.sfrac_false_div 245649903 524288) (BSN.cos_reduce2 qz472 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 33449560922349943914496) qz43) 226375608064910080 72057594037927936 Bool.false 947490 1048576 74 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q2 245649903 524288 226375608064910080 72057594037927936 74 33449560922349943914496 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 947490 1048576 33449560922349943914496 75557863725914323419136 950693701 2147483648 391196 390814 (ep1173 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1175 := BSN.sin_dyadic_bound_f 950693701 2147483648 2 1 1048576 391196 ep1172 ep58 ep1172 ep1172 ep59 ep1172 449190 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 950693701) qz15 0 1 ep1172 ep58 ep1172 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 950693701) qz16 0 1 ep1172 ep59 ep1172 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1176 := @Enclosure.Real.IsNear.sin_image qz180 qz472 Bool.false 245649903 524288 733 1048576 Bool.true 449190 1048576 1 195407 (@Enclosure.Real.IsNear.recentre' qz180 Bool.false 263764575311004420763 562949953421312000 17055250013330860947 24425875000000000000000 245649903 524288 733 1048576 (ep1171 rfl) rfl) (Enclosure.sfrac_false_div 245649903 524288) (BSN.sin_reduce2 qz472 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 33449560922349943914496) qz43) 226375608064910080 72057594037927936 Bool.false 449190 1048576 74 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q2 245649903 524288 226375608064910080 72057594037927936 74 33449560922349943914496 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 449190 1048576 33449560922349943914496 75557863725914323419136 950693701 2147483648 391196 390814 (ep1175 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1177 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz384 (Real.cos qz180)) (@HMul.hMul Real Real Real qz0 qz384 (@Neg.neg Real Real.instNeg (Real.sin qz180))) Bool.true 89219922105 549755813888 6839439430935 53713067162206208 Bool.false 42297751755 549755813888 3407548301955 26856533581103104 (@Enclosure.Real.IsNear.mulLit_ft qz384 (Real.cos qz180) 188329 1048576 1 1048576 473745 524288 144281907 204899090432 89219922105 549755813888 6839439430935 53713067162206208 qz388 (@Enclosure.Real.IsNear.recentre' (Real.cos qz180) Bool.true 947490 1048576 144281907 204899090432 473745 524288 144281907 204899090432 (ep1174 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz384 (@Neg.neg Real Real.instNeg (Real.sin qz180)) 188329 1048576 1 1048576 224595 524288 144281907 204899090432 42297751755 549755813888 3407548301955 26856533581103104 qz388 (@Enclosure.Real.IsNear.neg (Real.sin qz180) Bool.true 224595 524288 144281907 204899090432 (@Enclosure.Real.IsNear.recentre' (Real.sin qz180) Bool.true 449190 1048576 144281907 204899090432 224595 524288 144281907 204899090432 (ep1176 rfl rfl) rfl)) rfl)

noncomputable def ep1178 := @ep1086 89219922105 549755813888 6839439430935 53713067162206208 Bool.false 42297751755 549755813888 3407548301955 26856533581103104 Bool.false ep1087 5498038562951 1099511627776 1330814539840167 214852268648824832 Bool.false 28056671509199047360512 25517394087 274877906944 665224843513983 107426134324412416 (ep1088 (BSN.head_sum_c_succ qz143 30 31 rfl rfl) (ep1169 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1170 ep1177) rfl rfl

noncomputable abbrev qz181 := (@HMul.hMul Real Real Real qz269 qz441 qz625)

noncomputable def ep1179 := @Enclosure.Complex.IsNear.of_eq qz669 (Complex.mk (@HMul.hMul Real Real Real qz0 qz389 (Real.cos qz181)) (@HMul.hMul Real Real Real qz0 qz389 (@Neg.neg Real Real.instNeg (Real.sin qz181)))) Bool.true 1511264539 137438953472 6689354158829 53713067162206208 Bool.true 12124408467 68719476736 6737293358139 53713067162206208 (BSN.cpow_neg_s_mk qz146 136442 1000 32 qz147 rfl)

noncomputable def ep1180 := @Enclosure.Real.IsNear.mulLit_ff qz146 qz625 136442 1000 0 1 15608286920413395 4503599627370496 200000000195407 39081400000000000000 212962588399504444059 450359962737049600 13644200013330860947 19540700000000000000000 qz148 (BSN.isNear_log_sfrac 32 1 15608286920413395 4503599627370496 200000000195407 39081400000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz626) Bool.false 65465900263437584302080 18889465931478580854784 1000000000977035 195407000000000000000 15608286920413395 4503599627370496 200000000195407 39081400000000000000 (BSN.log_rat_reduce_isNear 32 1 5 64 64 0 524288 24973259072661432 36028797018963968 195407 1000000000000000 rfl rfl rfl rfl (ep509 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1181 := BSN.sin_dyadic_bound_f 133666654 2147483648 1 0 1048576 391196 0 1 1 0 1 1 65224 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 133666654) qz15 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 133666654) qz16 0 0 rfl) rfl rfl

noncomputable abbrev qz473 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 495842165) qz23)

noncomputable def ep1182 := @Enclosure.Real.IsNear.cos_image qz181 qz473 Bool.false 495842165 1048576 733 1048576 Bool.true 65224 1048576 1 195407 (@Enclosure.Real.IsNear.recentre' qz181 Bool.false 212962588399504444059 450359962737049600 13644200013330860947 19540700000000000000000 495842165 1048576 733 1048576 (ep1180 rfl) rfl) (Enclosure.sfrac_false_div 495842165 1048576) (BSN.cos_reduce1 qz473 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 9405954630943034572800) qz24) 226375608064910080 72057594037927936 Bool.false 65224 1048576 75 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q1 495842165 1048576 226375608064910080 72057594037927936 75 9405954630943034572800 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 65224 1048576 9405954630943034572800 151115727451828646838272 133666654 2147483648 391196 390814 (ep1181 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1183 := BSN.cos_dyadic_bound_f 133666654 2147483648 1 0 1048576 391196 0 1 1 0 1 1 1046544 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 133666654) qz19 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 133666654) qz20 0 0 rfl) rfl rfl

noncomputable def ep1184 := @Enclosure.Real.IsNear.sin_image qz181 qz473 Bool.false 495842165 1048576 733 1048576 Bool.false 1046544 1048576 1 195407 (@Enclosure.Real.IsNear.recentre' qz181 Bool.false 212962588399504444059 450359962737049600 13644200013330860947 19540700000000000000000 495842165 1048576 733 1048576 (ep1180 rfl) rfl) (Enclosure.sfrac_false_div 495842165 1048576) (BSN.sin_reduce1 qz473 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 9405954630943034572800) qz24) 226375608064910080 72057594037927936 Bool.false 1046544 1048576 75 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q1 495842165 1048576 226375608064910080 72057594037927936 75 9405954630943034572800 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1046544 1048576 9405954630943034572800 151115727451828646838272 133666654 2147483648 391196 390814 (ep1183 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1185 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz389 (Real.cos qz181)) (@HMul.hMul Real Real Real qz0 qz389 (@Neg.neg Real Real.instNeg (Real.sin qz181))) Bool.true 1511264539 137438953472 6689354158829 53713067162206208 Bool.true 12124408467 68719476736 6737293358139 53713067162206208 (@Enclosure.Real.IsNear.mulLit_ft qz389 (Real.cos qz181) 185363 1048576 1 1048576 8153 131072 144281907 204899090432 1511264539 137438953472 6689354158829 53713067162206208 qz393 (@Enclosure.Real.IsNear.recentre' (Real.cos qz181) Bool.true 65224 1048576 144281907 204899090432 8153 131072 144281907 204899090432 (ep1182 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz389 (@Neg.neg Real Real.instNeg (Real.sin qz181)) 185363 1048576 1 1048576 65409 65536 144281907 204899090432 12124408467 68719476736 6737293358139 53713067162206208 qz393 (@Enclosure.Real.IsNear.neg (Real.sin qz181) Bool.false 65409 65536 144281907 204899090432 (@Enclosure.Real.IsNear.recentre' (Real.sin qz181) Bool.false 1046544 1048576 144281907 204899090432 65409 65536 144281907 204899090432 (ep1184 rfl rfl) rfl)) rfl)

noncomputable def ep1186 := @ep1084 1511264539 137438953472 6689354158829 53713067162206208 Bool.true 12124408467 68719476736 6737293358139 53713067162206208 Bool.false 753983013307408195780608 5485948446639 1099511627776 1357571956475483 214852268648824832 Bool.true 1579190053018131234816 22980239781 274877906944 678699430230261 107426134324412416 (ep1085 (BSN.head_sum_c_succ qz143 31 32 rfl rfl) (ep1178 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1179 ep1185) rfl rfl

theorem EMRow46.d16 : Enclosure.Complex.IsNear qz173 Bool.false 5485948446639 1099511627776 1357571956475483 214852268648824832 Bool.true 22980239781 274877906944 678699430230261 107426134324412416 := ep1083 (BSN.head_sum_c_succ qz143 32 33 rfl rfl) (ep1186 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

theorem EMRow46.d17 : @Eq Nat (Nat.pow 35 1) 35 := @Eq.refl Nat 35

noncomputable def ep1187 := nat_lit 1888652484726300530870449734183869

noncomputable def ep1188 := nat_lit 375612272943443776847866757120000

noncomputable def ep1189 := nat_lit 121430197497201734138986373808205214744777

noncomputable def ep1190 := nat_lit 14342339834556163253857386402126107770880000

noncomputable abbrev qz677 := (@HAdd.hAdd Complex Complex Complex qz691 (@HAdd.hAdd Complex Complex Complex qz691 qz694 (@HMul.hMul Complex Complex Complex qz693 Complex.I (@HDiv.hDiv Complex Complex Complex qz695 (↑qz698) (2 : Complex)))) (@Nat.cast Complex Complex.instNatCast 2))

noncomputable abbrev qz474 := qz677

noncomputable abbrev qz182 := (Complex.Stirling.logGammaStirling 1 qz474)

noncomputable abbrev qz678 := (@HAdd.hAdd Complex Complex Complex qz691 qz694 (@HMul.hMul Complex Complex Complex qz693 Complex.I (@HDiv.hDiv Complex Complex Complex qz695 (↑qz698) (2 : Complex))))

noncomputable abbrev qz475 := qz678

noncomputable abbrev qz183 := qz475

noncomputable abbrev qz184 := (@HMul.hMul Real Real Real qz269 (@HDiv.hDiv Real Real Real qz272 qz441 (2 : Real)) (Real.log Real.pi))

noncomputable def ep1191 := Complex.re (@HMul.hMul Complex Complex Complex qz80 (Complex.exp (@HMul.hMul Complex Complex Complex qz80 Complex.I ↑(@HSub.hSub Real Real Real qz398 (Complex.im (@HSub.hSub Complex Complex Complex qz81 qz182 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz183 (@Nat.cast Complex Complex.instNatCast j))))) qz184))) (zetaApproximant qz143 1 35))

noncomputable def ep1192 := @Enclosure.Real.IsNear.of_eq ep1191 (@HSub.hSub Real Real Real qz398 (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz398 (Complex.im (@HSub.hSub Complex Complex Complex qz81 qz182 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz183 (@Nat.cast Complex Complex.instNatCast j))))) qz184)) (Complex.re (zetaApproximant qz143 1 35))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz398 (Complex.im (@HSub.hSub Complex Complex Complex qz81 qz182 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz183 (@Nat.cast Complex Complex.instNatCast j))))) qz184)) (Complex.im (zetaApproximant qz143 1 35))))

noncomputable def ep1193 := nat_lit 2158458405135842099941999534351

noncomputable def ep1194 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz398 (Complex.im (@HSub.hSub Complex Complex Complex qz81 qz182 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz183 (@Nat.cast Complex Complex.instNatCast j))))) qz184)) (Complex.re (zetaApproximant qz143 1 35))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz398 (Complex.im (@HSub.hSub Complex Complex Complex qz81 qz182 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz183 (@Nat.cast Complex Complex.instNatCast j))))) qz184)) (Complex.im (zetaApproximant qz143 1 35))) ep1193

noncomputable def ep1195 := nat_lit 429271169078221459254704865280

noncomputable def ep1196 := nat_lit 51989347442806507709979095348816279802407

noncomputable def ep1197 := nat_lit 6146717071952641394510308458054046187520000

noncomputable def ep1198 := nat_lit 172529054836677650017703343

noncomputable def ep1199 := nat_lit 46951534117930472105983344640000

noncomputable def ep1200 := nat_lit 182580195979824223552726991450842808741

noncomputable def ep1201 := nat_lit 21513509751834244880786079603189161656320000

noncomputable def ep1202 := nat_lit 101343007512618353414049245603619932394379473515398145549271040

noncomputable def ep1203 := @Enclosure.Real.IsNear.mulLit_tf (Real.cos (@HSub.hSub Real Real Real qz398 (Complex.im (@HSub.hSub Complex Complex Complex qz81 qz182 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz183 (@Nat.cast Complex Complex.instNatCast j))))) qz184)) (Complex.re (zetaApproximant qz143 1 35)) 1048575 1048576 74326201

noncomputable def ep1204 := nat_lit 154385123033820334735855771

noncomputable def ep1205 := nat_lit 30703866654268845981696000

noncomputable def ep1206 := nat_lit 6860106873300291545913909443

noncomputable def ep1207 := nat_lit 1034439736432881445990563840000

noncomputable def ep1208 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HSub.hSub Real Real Real qz398 (Complex.im (@HSub.hSub Complex Complex Complex qz81 qz182 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz183 (@Nat.cast Complex Complex.instNatCast j))))) qz184)) Bool.true 1048575 1048576 74326201

noncomputable abbrev qz476 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 74119761) qz42)

noncomputable def ep1209 := @Enclosure.Real.IsNear.cos_image (@HSub.hSub Real Real Real qz398 (Complex.im (@HSub.hSub Complex Complex Complex qz81 qz182 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz183 (@Nat.cast Complex Complex.instNatCast j))))) qz184) qz476 Bool.false 74119761 524288 375

noncomputable def ep1210 := nat_lit 109760281369972489911077623

noncomputable def ep1211 := nat_lit 307348635648000000000000000000

noncomputable def ep1212 := @Enclosure.Real.IsNear.recentre' (@HSub.hSub Real Real Real qz398 (Complex.im (@HSub.hSub Complex Complex Complex qz81 qz182 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz183 (@Nat.cast Complex Complex.instNatCast j))))) qz184) Bool.false 318341950578292382489 2251799813685248000 ep1210 ep1211

noncomputable def ep1213 := nat_lit 29775115687972489911077623

noncomputable def ep1214 := @Enclosure.Real.IsNear.subLit_ff_p (Complex.im (@HSub.hSub Complex Complex Complex qz81 qz182 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz183 (@Nat.cast Complex Complex.instNatCast j))))) qz184 494195354088477252377 2251799813685248000 ep1213 ep1211 5118007641 65536000

noncomputable def ep1215 := nat_lit 20862858073098969578799104000

noncomputable def ep1216 := nat_lit 9285328651155505741678309

noncomputable def ep1217 := nat_lit 51224772608000000000000000000

noncomputable def ep1218 := @Enclosure.Complex.IsNear.im_isNear (@HSub.hSub Complex Complex Complex qz81 qz182 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz183 (@Nat.cast Complex Complex.instNatCast j)))) Bool.true 24161380568997306931 225179981368524800 ep1216 ep1217 Bool.false 494195354088477252377 2251799813685248000

noncomputable def ep1219 := nat_lit 9154256650540808470382309

noncomputable def ep1220 := nat_lit 28202251687665141275429623

noncomputable def ep1221 := @Enclosure.Complex.IsNear.subLitP qz182 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz183 (@Nat.cast Complex Complex.instNatCast j))) Bool.true 22259582799370534731 225179981368524800 ep1219 ep1217 Bool.false 501220088047451996377 2251799813685248000 ep1220

noncomputable def ep1222 := nat_lit 27203296131823253528436835241426944

noncomputable def ep1223 := nat_lit 139103625782568530044462908217229312

noncomputable abbrev qz477 := (@HSub.hSub Complex Complex Complex qz628 qz677 qz631)

noncomputable abbrev qz478 := (Complex.log qz677)

noncomputable abbrev qz185 := (@HSub.hSub Complex Complex Complex qz395 (@HMul.hMul Complex Complex Complex qz394 qz477 qz478) qz474)

noncomputable abbrev qz186 := qz474

noncomputable def ep1224 := @Enclosure.Complex.IsNear.of_eq qz182 (@HAdd.hAdd Complex Complex Complex qz4 (@HAdd.hAdd Complex Complex Complex qz4 qz185 qz86) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz80 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz89 qz186 (@HSub.hSub Int Int Int qz405 qz91 (@HMul.hMul Int Int Int qz406 qz92 (@Nat.cast Int instNatCastInt k)))))) Bool.true 22259582799370534731

noncomputable def ep1225 := @Enclosure.Complex.IsNear.addLitP (@HAdd.hAdd Complex Complex Complex qz4 qz185 qz86) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz80 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz89 qz186 (@HSub.hSub Int Int Int qz405 qz91 (@HMul.hMul Int Int Int qz406 qz92 (@Nat.cast Int instNatCastInt k))))) Bool.true 22259591861337997131 225179981368524800

noncomputable def ep1226 := nat_lit 1529666882334409216890834518016

noncomputable def ep1227 := nat_lit 8610895545048187282276501946368000

noncomputable def ep1228 := @ep1225 34920709283009196161 195407000000000000000000 Bool.false 501222835676262007001 2251799813685248000 17930250080156146807 195407000000000000000000 Bool.false 2765493 68719476736 3 68719476736 Bool.true 20962744217 17179869184000 68221 51539607552000 Bool.true ep1226 22259582799370534731 225179981368524800 ep1219 ep1217 Bool.false ep1227

noncomputable def ep1229 := @Enclosure.Complex.IsNear.addLitP qz185 qz86 Bool.true 22466518231698521931 225179981368524800 69096000017434407947 390814000000000000000000

noncomputable def ep1230 := nat_lit 2917609224449293959954432

noncomputable def ep1231 := @ep1229 Bool.false 501222835676262007001 2251799813685248000 17930250080156146807 195407000000000000000000 Bool.false 120447 131072 1 524288 Bool.false 0 1 0 1 Bool.true ep1230 22259591861337997131 225179981368524800 34920709283009196161 195407000000000000000000 Bool.false 501222835676262007001 501222835676262007001 2251799813685248000

noncomputable abbrev qz187 := (@HMul.hMul Complex Complex Complex qz394 qz477 qz478)

noncomputable def ep1232 := @Enclosure.Complex.IsNear.subLitP qz187 qz186 Bool.true 21959863273619341131 225179981368524800 69096000017434407947 390814000000000000000000 Bool.false 654842870765683310809

noncomputable def ep1233 := nat_lit 2004891342705048028004000

noncomputable def ep1234 := @ep1232 2251799813685248000 17930250080156146807 195407000000000000000000 Bool.false 9000 4000 0 1 Bool.false 272884 4000 0 1 Bool.true 89866072926794087724000 22466518231698521931 225179981368524800 69096000017434407947 390814000000000000000000 Bool.false ep1233 501222835676262007001 2251799813685248000 17930250080156146807 195407000000000000000000

noncomputable abbrev qz188 := qz477

noncomputable abbrev qz189 := qz478

noncomputable def ep1235 := @Enclosure.Complex.IsNear.mul qz188 qz189 Bool.true 21959863273619341131 225179981368524800 69096000017434407947 390814000000000000000000 Bool.false 654842870765683310809 2251799813685248000 17930250080156146807

noncomputable abbrev qz190 := (Complex.re qz477)

noncomputable abbrev qz191 := (Complex.re qz478)

noncomputable abbrev qz192 := (Complex.im qz477)

noncomputable abbrev qz193 := (Complex.im qz478)

noncomputable def ep1236 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 qz190 qz191) (@HMul.hMul Real Real Real qz0 qz192 qz193) 66570114933416003 9007199254740992 875000004103547 390814000000000000000 11812058073477370603 112589990684262400

noncomputable def ep1237 := nat_lit 98898432056179105160980229548670976

noncomputable def ep1238 := @Enclosure.Real.IsNear.mulLit_ff qz190 qz191 7000 4000 0 1 9510016419059429 2251799813685248 125000000586221 97703500000000000000

noncomputable def ep1239 := @Enclosure.Complex.IsNear.re_isNear qz188 Bool.false 7000 4000 0 1 Bool.false 272884 4000 0 1

noncomputable abbrev qz679 := (Enclosure.sfrac Bool.false 272884 4000)

noncomputable abbrev qz479 := qz679

noncomputable def ep1240 := @Enclosure.Complex.IsNear.of_eq qz188 (Complex.mk (Enclosure.sfrac Bool.false 7000 4000) qz479) Bool.false 7000 4000 0 1 Bool.false 272884 4000 0

noncomputable abbrev qz480 := (Complex.log (Complex.mk qz635 qz679))

noncomputable def ep1241 := @Enclosure.Complex.IsNear.of_eq qz189 qz480 Bool.false 9510016419059429 2251799813685248 125000000586221 97703500000000000000 Bool.false 865720091575715 562949953421312 1000000000195407 390814000000000000000

noncomputable def ep1242 := nat_lit 5776024079034667283742391421032082668546621440

noncomputable def ep1243 := nat_lit 7986023435776163732566930409507362680864768

noncomputable def ep1244 := nat_lit 19776572740358283312076458036500685324288

noncomputable def ep1245 := BSN.log_dyadic_bound 9010677456 140082677456 3 2 ep1242 1048576 390814 ep1243 ep1244 135083 149093354912 131072000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 9010677456) (BSN.artanhQ 140082677456) 0 2 ep1243 ep1242 ep1244 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz680 := (Real.log (Enclosure.sfrac Bool.false 74546677456 16000000))

noncomputable def ep1246 := @Enclosure.Real.IsNear.mulLit_ff qz100 qz680 1 2 0 1 9510016419059429 1125899906842624 125000000586221 48851750000000000000 9510016419059429 2251799813685248 125000000586221 97703500000000000000 qz409 (BSN.isNear_log_sfrac 74546677456 16000000 9510016419059429 1125899906842624 125000000586221 48851750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 74546677456) qz637)) Bool.false 319103199252213114339328 37778931862957161709568 1000000004689768 390814000000000000000 9510016419059429 1125899906842624 125000000586221 48851750000000000000 (BSN.log_rat_reduce_isNear 74546677456 16000000 12 149093354912 131072000000 135083 1048576 24973259072661432 36028797018963968 390814 1000000000000000 rfl rfl rfl rfl (ep1245 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1247 := BSN.arctan_dyadic_bound_f 9000 272884 1 0 1048576 390814 0 1 1 0 1 1 34570 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 9000) (BSN.arctanEvenQ 272884) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 9000) (BSN.arctanOddQ 272884) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz481 := (Real.arctan (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 9000) (@Nat.cast Real Real.instNatCast 272884)))

noncomputable def ep1248 := @Enclosure.Real.IsNear.subLit_ff_p qz101 qz481 884279719003555 562949953421312 1 2000000000000000 34570 1048576 1 390814 907773310744096931840 865720091575715 562949953421312 1000000000195407 390814000000000000000 qz102 (ep1247 rfl) rfl rfl

noncomputable abbrev qz482 := (Complex.mk qz635 qz679)

noncomputable abbrev qz483 := (Real.arctan (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 272884) (@Nat.cast Real Real.instNatCast 9000)))

noncomputable def ep1249 := @Enclosure.Complex.IsNear.re_isNear qz189 Bool.false 9510016419059429 2251799813685248 125000000586221 97703500000000000000 Bool.false 865720091575715 562949953421312 1000000000195407 390814000000000000000 (ep1241 (@congrArg Complex Complex qz186 qz482 Complex.log (BSN.w_shift_mk qz146 Bool.false 136442 1000 2 qz147 rfl)) (@Enclosure.Complex.IsNear.of_parts qz480 Bool.false 9510016419059429 2251799813685248 125000000586221 97703500000000000000 Bool.false 865720091575715 562949953421312 1000000000195407 390814000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz480) (@HMul.hMul Real Real Real qz0 qz100 qz680) Bool.false 9510016419059429 2251799813685248 125000000586221 97703500000000000000 (Enclosure.clog_re_eq 9000 272884 4000 74546677456 16000000 rfl rfl rfl) (ep1246 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz480) qz483 Bool.false 865720091575715 562949953421312 1000000000195407 390814000000000000000 (Enclosure.clog_im_eq 9000 272884 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz483 (@HSub.hSub Real Real Real qz398 qz101 qz481) Bool.false 865720091575715 562949953421312 1000000000195407 390814000000000000000 (BSN.arctan_recip 272884 9000 rfl rfl) ep1248))))

noncomputable def ep1250 := @Enclosure.Real.IsNear.mulLit_ff qz192 qz193 272884 4000 0 1 865720091575715 562949953421312 1000000000195407 390814000000000000000

noncomputable def ep1251 := @Enclosure.Complex.IsNear.im_isNear qz188 Bool.false 7000 4000 0 1 Bool.false 272884 4000 0 1

noncomputable def ep1252 := @Enclosure.Complex.IsNear.im_isNear qz189 Bool.false 9510016419059429 2251799813685248 125000000586221 97703500000000000000 Bool.false 865720091575715 562949953421312 1000000000195407 390814000000000000000 (ep1241 (@congrArg Complex Complex qz186 qz482 Complex.log (BSN.w_shift_mk qz146 Bool.false 136442 1000 2 qz147 rfl)) (@Enclosure.Complex.IsNear.of_parts qz480 Bool.false 9510016419059429 2251799813685248 125000000586221 97703500000000000000 Bool.false 865720091575715 562949953421312 1000000000195407 390814000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz480) (@HMul.hMul Real Real Real qz0 qz100 qz680) Bool.false 9510016419059429 2251799813685248 125000000586221 97703500000000000000 (Enclosure.clog_re_eq 9000 272884 4000 74546677456 16000000 rfl rfl rfl) (ep1246 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz480) qz483 Bool.false 865720091575715 562949953421312 1000000000195407 390814000000000000000 (Enclosure.clog_im_eq 9000 272884 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz483 (@HSub.hSub Real Real Real qz398 qz101 qz481) Bool.false 865720091575715 562949953421312 1000000000195407 390814000000000000000 (BSN.arctan_recip 272884 9000 rfl rfl) ep1248))))

noncomputable abbrev qz194 := (@ep1240 1 (BSN.w_sub_half_mk qz441 Bool.false 136442 1000 2 qz442 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7000 4000) qz479 Bool.false 7000 4000 0 1 Bool.false 272884 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 7000 4000) (Enclosure.Real.IsNear.const Bool.false 272884 4000)))

noncomputable def ep1253 := @ep1236 68221000013330860947 390814000000000000000000 ep1237 21959863273619341131 225179981368524800 69096000017434407947 390814000000000000000000 (@ep1238 66570114933416003 9007199254740992 875000004103547 390814000000000000000 (ep1239 qz194) ep1249 rfl) (@ep1250 11812058073477370603 112589990684262400 68221000013330860947 390814000000000000000000 (ep1251 qz194) ep1252 rfl) rfl

noncomputable def ep1254 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz190 qz193) (@HMul.hMul Real Real Real qz0 qz192 qz191) 6060040641030005 2251799813685248 7000000001367849 1563256000000000000000 648782830124653305809 2251799813685248000

noncomputable def ep1255 := nat_lit 1474575054383278613603370036082245632

noncomputable def ep1256 := @Enclosure.Real.IsNear.mulLit_ff qz190 qz193 7000 4000 0 1 865720091575715 562949953421312 1000000000195407 390814000000000000000

noncomputable def ep1257 := @Enclosure.Real.IsNear.mulLit_ff qz192 qz191 272884 4000 0 1 9510016419059429 2251799813685248 125000000586221 97703500000000000000

noncomputable def ep1258 := @ep1254 8527625039992582841 97703500000000000000000 ep1255 654842870765683310809 2251799813685248000 17930250080156146807 195407000000000000000000 (@ep1256 6060040641030005 2251799813685248 7000000001367849 1563256000000000000000 (ep1239 qz194) ep1252 rfl) (@ep1257 648782830124653305809 2251799813685248000 8527625039992582841 97703500000000000000000 (ep1251 qz194) ep1249 rfl) rfl

noncomputable def ep1259 := @Enclosure.Complex.IsNear.of_eq qz186 qz482 Bool.false 9000 4000 0 1 Bool.false 272884 4000 0 1 (BSN.w_shift_mk qz146 Bool.false 136442 1000 2 qz147 rfl)

noncomputable abbrev qz484 := (ep1259 (@Enclosure.Complex.IsNear.mk qz635 qz679 Bool.false 9000 4000 0 1 Bool.false 272884 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 9000 4000) (Enclosure.Real.IsNear.const Bool.false 272884 4000)))

noncomputable abbrev qz195 := qz484

noncomputable def ep1260 := ep1234 (@ep1235 195407000000000000000000 (ep1253 rfl) (ep1258 rfl)) qz195 rfl rfl rfl rfl rfl rfl

noncomputable def ep1261 := @ep1231 17930250080156146807 195407000000000000000000 (ep1260 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@Enclosure.Complex.IsNear.mul qz105 (↑qz2) Bool.false 120447 131072 1 524288 Bool.false 0 1 0 1 (@ep591 131072 1 524288 (ep593 rfl) (ep595 rfl) rfl rfl) (@ep596 1 0 1 (ep598 rfl) (ep600 rfl) rfl rfl))

noncomputable abbrev qz485 := (@HPow.hPow Complex Int Complex qz633 qz677 (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) (@OfNat.ofNat Int 1 (@instOfNat 1)) (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (@OfNat.ofNat Int 2 (@instOfNat 2)) (@Nat.cast Int instNatCastInt 1))))

noncomputable abbrev qz196 := qz485

noncomputable def ep1262 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz80 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz89 qz186 (@HSub.hSub Int Int Int qz405 qz91 (@HMul.hMul Int Int Int qz406 qz92 (@Nat.cast Int instNatCastInt k))))) (@HAdd.hAdd Complex Complex Complex qz4 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz80 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz89 qz186 (@HSub.hSub Int Int Int qz405 qz91 (@HMul.hMul Int Int Int qz406 qz92 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli qz107)) qz108) qz196)) Bool.false 2765493 68719476736 3 68719476736

noncomputable def ep1263 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz80 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz89 qz186 (@HSub.hSub Int Int Int qz405 qz91 (@HMul.hMul Int Int Int qz406 qz92 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli qz107)) qz108) qz196) Bool.false 0 1 0 1 Bool.false

noncomputable def ep1264 := @ep1263 0 1 0 1 Bool.false 2765493 68719476736 3 68719476736 Bool.true 20962744217 17179869184000 68221 51539607552000 Bool.false 2765493 2765493 68719476736 3 68719476736 Bool.true 20962744217 20962744217 17179869184000 68221

noncomputable def ep1265 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz80 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz89 qz186 (@HSub.hSub Int Int Int qz405 qz91 (@HMul.hMul Int Int Int qz406 qz92 (@Nat.cast Int instNatCastInt k))))) (Complex.mk qz10 qz10) Bool.false 0 1 0 1 Bool.false

noncomputable def ep1266 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli qz107)) qz108) qz196 Bool.false 2765493 68719476736 3 68719476736 Bool.true 20962744217 17179869184000 68221 51539607552000

noncomputable abbrev qz197 := (Complex.re qz485)

noncomputable abbrev qz198 := (Complex.im qz485)

noncomputable def ep1267 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli qz107)) qz108)) qz197) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli qz107)) qz108)) qz198) 2765493 68719476736 3 68719476736 0 1 0

noncomputable def ep1268 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli qz107)) qz108)) qz197 1 12 0 1 8296479 17179869184 9 17179869184 2765493

noncomputable def ep1269 := @Enclosure.Complex.IsNear.re_isNear qz196 Bool.false 8296479 17179869184 9 17179869184 Bool.true 62888232651 4294967296000 68221 4294967296000

noncomputable abbrev qz486 := (@HPow.hPow Complex Nat Complex qz638 qz677 1)

noncomputable abbrev qz199 := (@Inv.inv Complex Complex.instInv qz486)

noncomputable def ep1270 := @Enclosure.Complex.IsNear.of_eq qz196 qz199 Bool.false 8296479 17179869184 9 17179869184 Bool.true 62888232651 4294967296000 68221

noncomputable def ep1271 := @Enclosure.Complex.IsNear.of_parts qz199 Bool.false 8296479 17179869184 9 17179869184 Bool.true 62888232651 4294967296000 68221

noncomputable abbrev qz200 := (Complex.re qz486)

noncomputable abbrev qz201 := qz486

noncomputable def ep1272 := @Enclosure.Real.IsNear.mulLit_ff qz200 (@Inv.inv Real Real.instInv (@DFunLike.coe qz114 Complex (fun (x : Complex) => Real) qz115 Complex.normSq qz201)) 9000 4000 0 1 921831 4294967296 1 4294967296

noncomputable def ep1273 := @Enclosure.Complex.IsNear.re_isNear qz201 Bool.false 9000 4000 0 1 Bool.false 272884 4000 0 1

noncomputable def ep1274 := @Enclosure.Complex.IsNear.of_eq qz201 qz186 Bool.false 9000 4000 0 1 Bool.false 272884 4000 0

noncomputable def ep1275 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (@DFunLike.coe qz114 Complex (fun (x : Complex) => Real) qz115 Complex.normSq qz201)) Bool.false 921831 4294967296 1 4294967296 921831 4294967296 1

noncomputable abbrev qz202 := (Complex.im qz486)

noncomputable def ep1276 := @Enclosure.Real.IsNear.of_eq (@DFunLike.coe qz114 Complex (fun (x : Complex) => Real) qz115 Complex.normSq qz201) (@HAdd.hAdd Real Real Real qz418 (@HMul.hMul Real Real Real qz0 qz200 qz200) (@HMul.hMul Real Real Real qz0 qz202 qz202)) Bool.false 4659167341 1000000 0 1

noncomputable def ep1277 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz200 qz200) (@HMul.hMul Real Real Real qz0 qz202 qz202) 81 16 0 1 4654104841 1000000

noncomputable def ep1278 := @Enclosure.Real.IsNear.mulLit_ff qz200 qz200 9000 4000 0 1 9000 4000 0 1

noncomputable def ep1279 := @Enclosure.Real.IsNear.mulLit_ff qz202 qz202 272884 4000 0 1 272884 4000 0 1

noncomputable def ep1280 := @Enclosure.Complex.IsNear.im_isNear qz201 Bool.false 9000 4000 0 1 Bool.false 272884 4000 0 1

noncomputable abbrev qz203 := (ep1273 (@ep1274 1 (BSN.pow_one_c qz474) qz484))

noncomputable abbrev qz204 := (ep1280 (@ep1274 1 (BSN.pow_one_c qz474) qz484))

noncomputable def ep1281 := @ep1277 0 1 74546677456 4659167341 1000000 0 1 (@ep1278 81 16 0 1 qz203 qz203 rfl) (@ep1279 4654104841 1000000 0 1 qz204 qz204 rfl)

noncomputable def ep1282 := @Enclosure.Real.IsNear.inv_image (@DFunLike.coe qz114 Complex (fun (x : Complex) => Real) qz115 Complex.normSq qz201) 4659167341 1000000 0 1 460915 460916 2147483648 (ep1276 (Enclosure.Complex.normSq_eq_mul_add_mul qz201) (ep1281 rfl rfl)) rfl

noncomputable def ep1283 := @Enclosure.Real.IsNear.of_eq (Complex.re qz199) (@HMul.hMul Real Real Real qz0 qz200 (@Inv.inv Real Real.instInv (@DFunLike.coe qz114 Complex (fun (x : Complex) => Real) qz115 Complex.normSq qz201))) Bool.false 8296479 17179869184 9 17179869184 (Enclosure.Complex.inv_re_eq_mul qz201) (@ep1272 8296479 17179869184 9 17179869184 qz203 (@ep1275 4294967296 (ep1282 rfl rfl rfl rfl rfl) rfl) rfl)

noncomputable def ep1284 := @Enclosure.Real.IsNear.of_eq (Complex.im qz199) (@HMul.hMul Real Real Real qz0 (@Neg.neg Real Real.instNeg qz202) (@Inv.inv Real Real.instInv (@DFunLike.coe qz114 Complex (fun (x : Complex) => Real) qz115 Complex.normSq qz201))) Bool.true 62888232651 4294967296000 68221 4294967296000 (Enclosure.Complex.inv_im_eq_mul qz201)

noncomputable def ep1285 := @Enclosure.Real.IsNear.mulLit_tf (@Neg.neg Real Real.instNeg qz202) (@Inv.inv Real Real.instInv (@DFunLike.coe qz114 Complex (fun (x : Complex) => Real) qz115 Complex.normSq qz201)) 272884 4000 0 1 921831 4294967296 1

noncomputable def ep1286 := @ep1285 4294967296 62888232651 4294967296000 68221 4294967296000 (@Enclosure.Real.IsNear.neg qz202 Bool.false 272884 4000 0 1 qz204) (@ep1275 4294967296 (ep1282 rfl rfl rfl rfl rfl) rfl) rfl

noncomputable def ep1287 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli qz107)) qz108)) qz198 0 1 0 1 62888232651 4294967296000 68221 4294967296000 0

noncomputable def ep1288 := @Enclosure.Complex.IsNear.im_isNear qz196 Bool.false 8296479 17179869184 9 17179869184 Bool.true 62888232651 4294967296000 68221 4294967296000

noncomputable abbrev qz205 := (@ep1270 4294967296000 (BSN.zpow_one_sub_two_mul qz474 1 1 rfl rfl) (@ep1271 4294967296000 ep1283 (ep1284 ep1286)))

noncomputable def ep1289 := @ep1267 1 2765493 2765493 68719476736 3 68719476736 (@ep1268 68719476736 3 68719476736 ep610 (ep1269 qz205) rfl) (@ep1287 1 0 1 ep630 (ep1288 qz205) rfl) rfl

noncomputable def ep1290 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli qz107)) qz108)) qz198) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli qz107)) qz108)) qz197) 20962744217 17179869184000 68221 51539607552000 0 1 0

noncomputable def ep1291 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli qz107)) qz108)) qz198 1 12 0 1 62888232651 4294967296000 68221 4294967296000 20962744217

noncomputable def ep1292 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli qz107)) qz108)) qz197 0 1 0 1 8296479 17179869184 9 17179869184 0

noncomputable def ep1293 := @ep1290 1 20962744217 20962744217 17179869184000 68221 51539607552000 (@ep1291 17179869184000 68221 51539607552000 ep610 (ep1288 qz205) rfl) (@ep1292 1 0 1 ep630 (ep1269 qz205) rfl) rfl

noncomputable def ep1294 := @ep1264 51539607552000 (@ep1265 0 1 0 1 (BSN.stirling_sum_base qz186) qz121) (ep1266 (ep1289 rfl) (ep1293 rfl)) rfl rfl rfl rfl rfl

noncomputable def ep1295 := @ep1228 501220088047451996377 2251799813685248000 ep1220 ep1211 (ep1261 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep1262 Bool.true 20962744217 17179869184000 68221 51539607552000 (BSN.stirling_sum_succ qz186 0 1 rfl) (ep1294 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl

noncomputable def ep1296 := @Enclosure.Complex.IsNear.of_eq (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz183 (@Nat.cast Complex Complex.instNatCast j))) (BSN.logSumC qz146 2) Bool.false 9508988848133861 1125899906842624 125000000586221 48851750000000000000 Bool.false 878091744871843 281474976710656

noncomputable abbrev qz206 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz274 qz475 qz414))

noncomputable def ep1297 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz146 2) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.logSumC qz146 1) qz206) Bool.false 9508988848133861 1125899906842624 125000000586221 48851750000000000000 Bool.false 878091744871843 281474976710656 1000000000195407 195407000000000000000

noncomputable def ep1298 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz146 1) qz206 Bool.false 9508807385765605 2251799813685248 125000000586221 97703500000000000000 Bool.false 882217060959651 562949953421312 1000000000195407 390814000000000000000 Bool.false

noncomputable def ep1299 := nat_lit 42824678633125858377948049965056

noncomputable def ep1300 := nat_lit 988643413750485194177649836032

noncomputable abbrev qz207 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz274 qz475 (@Nat.cast Complex Complex.instNatCast 0)))

noncomputable def ep1301 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz146 1) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.logSumC qz146 0) qz207) Bool.false 9508807385765605 2251799813685248 125000000586221 97703500000000000000 Bool.false 882217060959651 562949953421312 1000000000195407 390814000000000000000

noncomputable def ep1302 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz146 0) qz207 Bool.false 0 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable abbrev qz487 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz679))

noncomputable def ep1303 := @Enclosure.Complex.IsNear.of_eq qz207 qz487 Bool.false 9508807385765605 2251799813685248 125000000586221 97703500000000000000 Bool.false 882217060959651 562949953421312 1000000000195407 390814000000000000000

noncomputable def ep1304 := nat_lit 5762840829001712625676678332612075551746621440

noncomputable def ep1305 := nat_lit 7835568486786402939904292521930233720864768

noncomputable def ep1306 := nat_lit 19083537062349093953791102995077325324288

noncomputable def ep1307 := BSN.log_dyadic_bound 8930677456 140002677456 3 2 ep1304 1048576 390814 ep1305 ep1306 133957 148933354912 131072000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 8930677456) (BSN.artanhQ 140002677456) 0 2 ep1305 ep1304 ep1306 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep1308 := @Enclosure.Real.IsNear.mulLit_ff qz100 (Real.log (Enclosure.sfrac Bool.false 74466677456 16000000)) 1 2 0 1 9508807385765605 1125899906842624 125000000586221 48851750000000000000 9508807385765605 2251799813685248 125000000586221 97703500000000000000 qz409 (BSN.isNear_log_sfrac 74466677456 16000000 9508807385765605 1125899906842624 125000000586221 48851750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 74466677456) qz637)) Bool.false 319062630826769760911360 37778931862957161709568 1000000004689768 390814000000000000000 9508807385765605 1125899906842624 125000000586221 48851750000000000000 (BSN.log_rat_reduce_isNear 74466677456 16000000 12 148933354912 131072000000 133957 1048576 24973259072661432 36028797018963968 390814 1000000000000000 rfl rfl rfl rfl (ep1307 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1309 := BSN.arctan_dyadic_bound_f 1000 272884 1 0 1048576 390814 0 1 1 0 1 1 3842 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 272884) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 272884) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz488 := (@Nat.cast Real Real.instNatCast 272884)

noncomputable def ep1310 := @Enclosure.Real.IsNear.subLit_ff_p qz101 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz420 qz488)) 884279719003555 562949953421312 1 2000000000000000 3842 1048576 1 390814 925071636912827006976 882217060959651 562949953421312 1000000000195407 390814000000000000000 qz102 (ep1309 rfl) rfl rfl

noncomputable abbrev qz208 := (@HAdd.hAdd Complex Complex Complex qz274 qz475 (@Nat.cast Complex Complex.instNatCast 0))

noncomputable abbrev qz489 := (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz679)

noncomputable def ep1311 := @ep1302 9508807385765605 2251799813685248 125000000586221 97703500000000000000 Bool.false 882217060959651 562949953421312 1000000000195407 390814000000000000000 Bool.false 9508807385765605 9508807385765605 2251799813685248 125000000586221 97703500000000000000 Bool.false 882217060959651 882217060959651 562949953421312 1000000000195407 390814000000000000000 (@Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz146 0) (Complex.mk qz10 qz10) Bool.false 0 1 0 1 Bool.false 0 1 0 1 (BSN.log_sum_c_base qz146) qz121) (ep1303 (@congrArg Complex Complex qz208 qz489 Complex.log (BSN.w_shift_mk qz146 Bool.false 136442 1000 0 qz147 rfl)) (@Enclosure.Complex.IsNear.of_parts qz487 Bool.false 9508807385765605 2251799813685248 125000000586221 97703500000000000000 Bool.false 882217060959651 562949953421312 1000000000195407 390814000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz487) (@HMul.hMul Real Real Real qz0 qz100 (Real.log (Enclosure.sfrac Bool.false 74466677456 16000000))) Bool.false 9508807385765605 2251799813685248 125000000586221 97703500000000000000 (Enclosure.clog_re_eq 1000 272884 4000 74466677456 16000000 rfl rfl rfl) (ep1308 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz487) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz488 qz420)) Bool.false 882217060959651 562949953421312 1000000000195407 390814000000000000000 (Enclosure.clog_im_eq 1000 272884 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz488 qz420)) (@HSub.hSub Real Real Real qz398 qz101 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz420 qz488))) Bool.false 882217060959651 562949953421312 1000000000195407 390814000000000000000 (BSN.arctan_recip 272884 1000 rfl rfl) ep1310)))) rfl rfl

noncomputable abbrev qz490 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz679))

noncomputable def ep1312 := @Enclosure.Complex.IsNear.of_eq qz206 qz490 Bool.false 9509170310502117 2251799813685248 125000000586221 97703500000000000000 Bool.false 873966428784035 562949953421312 1000000000195407 390814000000000000000

noncomputable def ep1313 := nat_lit 5766793431930595736183705260159517686786621440

noncomputable def ep1314 := nat_lit 7880536957180591413186412432971372408864768

noncomputable def ep1315 := nat_lit 19289503269010993087364913795504333324288

noncomputable def ep1316 := BSN.log_dyadic_bound 8954677456 140026677456 3 2 ep1313 1048576 390814 ep1314 ep1315 134295 148981354912 131072000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 8954677456) (BSN.artanhQ 140026677456) 0 2 ep1314 ep1313 ep1315 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep1317 := @Enclosure.Real.IsNear.mulLit_ff qz100 (Real.log (Enclosure.sfrac Bool.false 74490677456 16000000)) 1 2 0 1 9509170310502117 1125899906842624 125000000586221 48851750000000000000 9509170310502117 2251799813685248 125000000586221 97703500000000000000 qz409 (BSN.isNear_log_sfrac 74490677456 16000000 9509170310502117 1125899906842624 125000000586221 48851750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 74490677456) qz637)) Bool.false 319074808560162170732544 37778931862957161709568 1000000004689768 390814000000000000000 9509170310502117 1125899906842624 125000000586221 48851750000000000000 (BSN.log_rat_reduce_isNear 74490677456 16000000 12 148981354912 131072000000 134295 1048576 24973259072661432 36028797018963968 390814 1000000000000000 rfl rfl rfl rfl (ep1316 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1318 := BSN.arctan_dyadic_bound_f 5000 272884 1 0 1048576 390814 0 1 1 0 1 1 19210 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 5000) (BSN.arctanEvenQ 272884) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 5000) (BSN.arctanOddQ 272884) 0 0 rfl) rfl rfl rfl

noncomputable def ep1319 := @Enclosure.Real.IsNear.subLit_ff_p qz101 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz424 qz488)) 884279719003555 562949953421312 1 2000000000000000 19210 1048576 1 390814 916420222028648284160 873966428784035 562949953421312 1000000000195407 390814000000000000000 qz102 (ep1318 rfl) rfl rfl

noncomputable abbrev qz209 := (@HAdd.hAdd Complex Complex Complex qz274 qz475 qz414)

noncomputable abbrev qz491 := (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz679)

noncomputable def ep1320 := @ep1298 9509170310502117 2251799813685248 125000000586221 97703500000000000000 Bool.false 873966428784035 562949953421312 1000000000195407 390814000000000000000 Bool.false ep1299 9508988848133861 1125899906842624 125000000586221 48851750000000000000 Bool.false ep1300 878091744871843 281474976710656 1000000000195407 195407000000000000000 (ep1301 (BSN.log_sum_c_succ qz146 0 1 rfl) (ep1311 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1312 (@congrArg Complex Complex qz209 qz491 Complex.log (BSN.w_shift_mk qz146 Bool.false 136442 1000 1 qz147 rfl)) (@Enclosure.Complex.IsNear.of_parts qz490 Bool.false 9509170310502117 2251799813685248 125000000586221 97703500000000000000 Bool.false 873966428784035 562949953421312 1000000000195407 390814000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz490) (@HMul.hMul Real Real Real qz0 qz100 (Real.log (Enclosure.sfrac Bool.false 74490677456 16000000))) Bool.false 9509170310502117 2251799813685248 125000000586221 97703500000000000000 (Enclosure.clog_re_eq 5000 272884 4000 74490677456 16000000 rfl rfl rfl) (ep1317 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz490) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz488 qz424)) Bool.false 873966428784035 562949953421312 1000000000195407 390814000000000000000 (Enclosure.clog_im_eq 5000 272884 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz488 qz424)) (@HSub.hSub Real Real Real qz398 qz101 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz424 qz488))) Bool.false 873966428784035 562949953421312 1000000000195407 390814000000000000000 (BSN.arctan_recip 272884 5000 rfl rfl) ep1319)))) rfl rfl

noncomputable def ep1321 := @ep1221 ep1211 Bool.false 9508988848133861 1125899906842624 125000000586221 48851750000000000000 Bool.false 878091744871843 281474976710656 1000000000195407 195407000000000000000 Bool.true ep1222 24161380568997306931 225179981368524800 ep1216 ep1217 Bool.false ep1223 494195354088477252377 2251799813685248000 ep1213 ep1211 (@ep1224 225179981368524800 ep1219 ep1217 Bool.false 501220088047451996377 2251799813685248000 ep1220 ep1211 (BSN.logGammaStirling_unfold 1 qz186) (ep1295 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (@ep1296 1000000000195407 195407000000000000000 (BSN.log_sum_c_eq qz146 2) (ep1297 (BSN.log_sum_c_succ qz146 1 2 rfl) (ep1320 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)))

noncomputable abbrev qz210 := (@HDiv.hDiv Real Real Real qz272 qz441 (2 : Real))

noncomputable def ep1322 := @Enclosure.Real.IsNear.mulLit_ff qz210 (Real.log Real.pi) 136442 2000 0 1 75021 65536 1 262144 5118007641 65536000 68221 262144000 (@Enclosure.Real.IsNear.of_eq qz210 (Enclosure.sfrac Bool.false 136442 2000) Bool.false 136442 2000 0 1 (BSN.t_half_eq qz146 Bool.false 136442 1000 qz147) (Enclosure.Real.IsNear.const Bool.false 136442 2000)) EMRow46.d5 rfl

noncomputable def ep1323 := @ep1214 68221 262144000 ep1215 318341950578292382489 2251799813685248000 ep1210 ep1211 (@ep1218 ep1213 ep1211 (ep1321 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) ep1322 rfl rfl

noncomputable def ep1324 := BSN.cos_dyadic_bound_f 1192704 2147483648 1 0 1048576 391196 0 1 1 0 1 1 1048575 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 1192704) qz19 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 1192704) qz20 0 0 rfl) rfl rfl

noncomputable def ep1325 := @ep1209 1048576 Bool.true 1048575 1048576 1 195407 (@ep1212 74119761 524288 375 1048576 ep1323 rfl) (Enclosure.sfrac_false_div 74119761 524288) (BSN.cos_reduce2 qz476 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 41964550285261012992) qz43) 226375608064910080 72057594037927936 Bool.false 1048575 1048576 22 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q2 74119761 524288 226375608064910080 72057594037927936 22 41964550285261012992 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1048575 1048576 41964550285261012992 75557863725914323419136 1192704 2147483648 391196 390814 (ep1324 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1326 := nat_lit 89552944408284134113280000

noncomputable def ep1327 := nat_lit 696157015778463666285657737441

noncomputable def ep1328 := nat_lit 104995633247937466768042229760000

noncomputable abbrev qz492 := (@HPow.hPow Complex Complex Complex qz539 (@Nat.cast Complex Complex.instNatCast 35) qz646)

noncomputable abbrev qz211 := qz492

noncomputable abbrev qz493 := (@Nat.cast Complex Complex.instNatCast 35)

noncomputable abbrev qz212 := (@HAdd.hAdd Complex Complex Complex qz274 (@HDiv.hDiv Complex Complex Complex qz403 qz493 (@HSub.hSub Complex Complex Complex qz395 qz439 (1 : Complex))) qz402)

noncomputable abbrev qz213 := qz493

noncomputable def ep1329 := @Enclosure.Complex.IsNear.of_eq (zetaApproximant qz143 1 35) (@HAdd.hAdd Complex Complex Complex qz4 (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 35, @HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast n) qz144) (@HMul.hMul Complex Complex Complex qz80 qz211 (@HAdd.hAdd Complex Complex Complex qz4 qz212 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz213 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1))))))) Bool.false ep1204 ep1205 ep1206

noncomputable def ep1330 := @Enclosure.Complex.IsNear.addLitP (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 35, @HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast n) qz144) (@HMul.hMul Complex Complex Complex qz80 qz211 (@HAdd.hAdd Complex Complex Complex qz4 qz212 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz213 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))))) Bool.false 1372720869279 274877906944 352564077344301 53713067162206208

noncomputable def ep1331 := nat_lit 70208055152800263126429443

noncomputable def ep1332 := nat_lit 6999509925146544045715673

noncomputable def ep1333 := nat_lit 7155867227179110685366052441

noncomputable def ep1334 := nat_lit 42437059482828456936337493441143373824

noncomputable def ep1335 := nat_lit 651882137189450889342829683433013248

noncomputable def ep1336 := @ep1330 Bool.false 78659171519 1099511627776 1409901110061617 214852268648824832 Bool.false 1052179719241486324519771 ep1205 ep1331 ep1207 Bool.true ep1332 ep1326 ep1333 ep1328 Bool.false ep1334 ep1204 ep1205 ep1206 ep1207 Bool.true ep1335 592883349954218728583173 ep1326

noncomputable def ep1337 := @Enclosure.Complex.IsNear.of_eq (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 35, @HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast n) qz144) (BSN.headSumC qz143 35) Bool.false 1372720869279 274877906944 352564077344301 53713067162206208 Bool.false 78659171519 1099511627776 1409901110061617

noncomputable def ep1338 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz143 35) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz143 34) (@HPow.hPow Complex Complex Complex qz6 qz131 qz144)) Bool.false 1372720869279 274877906944 352564077344301 53713067162206208 Bool.false 78659171519 1099511627776 1409901110061617 214852268648824832

noncomputable def ep1339 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz143 34) (@HPow.hPow Complex Complex Complex qz6 qz131 qz144) Bool.false 2829077868681 549755813888 86508020720661 13428266790551552 Bool.true 8383819009 1099511627776 1383860311484783 214852268648824832 Bool.true

noncomputable def ep1340 := nat_lit 1509322557463039001493504

noncomputable abbrev qz681 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 33) qz144)

noncomputable def ep1341 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz143 34) (@HAdd.hAdd Complex Complex Complex qz4 qz173 qz681) Bool.false 2829077868681 549755813888 86508020720661 13428266790551552 Bool.true 8383819009 1099511627776 1383860311484783 214852268648824832

noncomputable def ep1342 := @Enclosure.Complex.IsNear.addLitP qz173 qz681 Bool.false 5485948446639 1099511627776 1357571956475483 214852268648824832 Bool.true 22980239781 274877906944 678699430230261 107426134324412416 Bool.false

noncomputable def ep1343 := nat_lit 6221208024997006160166912

noncomputable abbrev qz214 := (@HMul.hMul Real Real Real qz269 qz441 qz640)

noncomputable def ep1344 := @Enclosure.Complex.IsNear.of_eq qz681 (Complex.mk (@HMul.hMul Real Real Real qz0 qz429 (Real.cos qz214)) (@HMul.hMul Real Real Real qz0 qz429 (@Neg.neg Real Real.instNeg (Real.sin qz214)))) Bool.false 172207290723 1099511627776 26556375055093 214852268648824832 Bool.false 83537140115 1099511627776 26461451024261 214852268648824832 (BSN.cpow_neg_s_mk qz146 136442 1000 33 qz147 rfl)

noncomputable def ep1345 := @Enclosure.Real.IsNear.mulLit_ff qz146 qz640 136442 1000 0 1 15746868335186131 4503599627370496 200000000195407 39081400000000000000 1074267104694733042951 2251799813685248000 13644200013330860947 19540700000000000000000 qz148 (BSN.isNear_log_sfrac 33 1 15746868335186131 4503599627370496 200000000195407 39081400000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz641) Bool.false 66047152845744529997824 18889465931478580854784 1000000000977035 195407000000000000000 15746868335186131 4503599627370496 200000000195407 39081400000000000000 (BSN.log_rat_reduce_isNear 33 1 5 66 64 16133 524288 24973259072661432 36028797018963968 195407 1000000000000000 rfl rfl rfl rfl (ep681 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1346 := nat_lit 2146774642700603876655858174267028354812940234418626726816825514368941298295040

noncomputable def ep1347 := nat_lit 1113063524563695013961360234653503277833843991645425859942983187084057518336

noncomputable def ep1348 := nat_lit 5620702913747526075504643492224206685869779152252786928366063898187186354790656

noncomputable def ep1349 := BSN.sin_dyadic_bound_f 2403338778 2147483648 3 2 1048576 391196 ep1346 ep72 ep1347 ep1348 ep75 ep1347 943431 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2403338778) qz15 0 2 ep1346 ep72 ep1347 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2403338778) qz16 0 2 ep1348 ep75 ep1347 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz494 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 250122301) qz42)

noncomputable def ep1350 := @Enclosure.Real.IsNear.cos_image qz214 qz494 Bool.false 250122301 524288 367 524288 Bool.false 943431 1048576 1 195407 (@Enclosure.Real.IsNear.recentre' qz214 Bool.false 1074267104694733042951 2251799813685248000 13644200013330860947 19540700000000000000000 250122301 524288 367 524288 (ep1345 rfl) rfl) (Enclosure.sfrac_false_div 250122301 524288) (BSN.cos_reduce3 qz494 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 84559965836753714020352) qz43) 226375608064910080 72057594037927936 Bool.false 943431 1048576 75 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q3 250122301 524288 226375608064910080 72057594037927936 75 84559965836753714020352 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 943431 1048576 84559965836753714020352 75557863725914323419136 2403338778 2147483648 391196 390814 (ep1349 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1351 := nat_lit 1193147274177919351481681812474861754130670727562190593058211056065893635727616

noncomputable def ep1352 := nat_lit 3577215695484630664417122716955278255836344494703280927454747201823512792146176

noncomputable def ep1353 := BSN.cos_dyadic_bound_f 2403338778 2147483648 3 2 1048576 391196 ep1351 ep79 ep1347 ep1352 ep81 ep1347 457655 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2403338778) qz19 0 2 ep1351 ep79 ep1347 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2403338778) qz20 0 2 ep1352 ep81 ep1347 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1354 := @Enclosure.Real.IsNear.sin_image qz214 qz494 Bool.false 250122301 524288 367 524288 Bool.true 457655 1048576 1 195407 (@Enclosure.Real.IsNear.recentre' qz214 Bool.false 1074267104694733042951 2251799813685248000 13644200013330860947 19540700000000000000000 250122301 524288 367 524288 (ep1345 rfl) rfl) (Enclosure.sfrac_false_div 250122301 524288) (BSN.sin_reduce3 qz494 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 84559965836753714020352) qz43) 226375608064910080 72057594037927936 Bool.false 457655 1048576 75 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q3 250122301 524288 226375608064910080 72057594037927936 75 84559965836753714020352 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 457655 1048576 84559965836753714020352 75557863725914323419136 2403338778 2147483648 391196 390814 (ep1353 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1355 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz429 (Real.cos qz214)) (@HMul.hMul Real Real Real qz0 qz429 (@Neg.neg Real Real.instNeg (Real.sin qz214))) Bool.false 172207290723 1099511627776 26556375055093 214852268648824832 Bool.false 83537140115 1099511627776 26461451024261 214852268648824832 (@Enclosure.Real.IsNear.mulLit_ff qz429 (Real.cos qz214) 182533 1048576 1 1048576 943431 1048576 72238657 102449545216 172207290723 1099511627776 26556375055093 214852268648824832 qz433 (@Enclosure.Real.IsNear.recentre' (Real.cos qz214) Bool.false 943431 1048576 72238657 102449545216 943431 1048576 72238657 102449545216 (ep1350 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz429 (@Neg.neg Real Real.instNeg (Real.sin qz214)) 182533 1048576 1 1048576 457655 1048576 72238657 102449545216 83537140115 1099511627776 26461451024261 214852268648824832 qz433 (@Enclosure.Real.IsNear.neg (Real.sin qz214) Bool.true 457655 1048576 72238657 102449545216 (@Enclosure.Real.IsNear.recentre' (Real.sin qz214) Bool.true 457655 1048576 72238657 102449545216 457655 1048576 72238657 102449545216 (ep1354 rfl rfl) rfl)) rfl)

noncomputable def ep1356 := @ep1342 172207290723 1099511627776 26556375055093 214852268648824832 Bool.false 83537140115 1099511627776 26461451024261 214852268648824832 Bool.false ep1343 2829077868681 549755813888 86508020720661 13428266790551552 Bool.true 2304526621391240298496 8383819009 1099511627776 1383860311484783 214852268648824832 EMRow46.d16 (ep1344 ep1355) rfl rfl

noncomputable abbrev qz215 := (@HMul.hMul Real Real Real qz269 qz441 qz642)

noncomputable def ep1357 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz131 qz144) (Complex.mk (@HMul.hMul Real Real Real qz0 qz434 (Real.cos qz215)) (@HMul.hMul Real Real Real qz0 qz434 (@Neg.neg Real Real.instNeg (Real.sin qz215)))) Bool.true 83636130123 549755813888 6531994461657 53713067162206208 Bool.false 1360046727 17179869184 13020399288417 107426134324412416 (BSN.cpow_neg_s_mk qz146 136442 1000 34 qz147 rfl)

noncomputable def ep1358 := @Enclosure.Real.IsNear.mulLit_ff qz146 qz137 136442 1000 0 1 15881309401485523 4503599627370496 200000000195407 39081400000000000000 1083438808678743864583 2251799813685248000 13644200013330860947 19540700000000000000000 qz148 (BSN.isNear_log_sfrac 34 1 15881309401485523 4503599627370496 200000000195407 39081400000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz436) Bool.false 66611039547888335060992 18889465931478580854784 1000000000977035 195407000000000000000 15881309401485523 4503599627370496 200000000195407 39081400000000000000 (BSN.log_rat_reduce_isNear 34 1 5 68 64 31784 524288 24973259072661432 36028797018963968 195407 1000000000000000 rfl rfl rfl rfl (ep699 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1359 := nat_lit 1127171041992687515064568959839867136

noncomputable def ep1360 := BSN.cos_dyadic_bound_f 1030380084 2147483648 2 1 1048576 391196 ep1359 ep62 ep1359 ep1359 ep63 ep1359 930174 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1030380084) qz19 0 1 ep1359 ep62 ep1359 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1030380084) qz20 0 1 ep1359 ep63 ep1359 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz495 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 252257755) qz42)

noncomputable def ep1361 := @Enclosure.Real.IsNear.cos_image qz215 qz495 Bool.false 252257755 524288 733 1048576 Bool.true 930174 1048576 1 195407 (@Enclosure.Real.IsNear.recentre' qz215 Bool.false 1083438808678743864583 2251799813685248000 13644200013330860947 19540700000000000000000 252257755 524288 733 1048576 (ep1358 rfl) rfl) (Enclosure.sfrac_false_div 252257755 524288) (BSN.cos_reduce2 qz495 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 36253276270685711237120) qz43) 226375608064910080 72057594037927936 Bool.false 930174 1048576 76 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q2 252257755 524288 226375608064910080 72057594037927936 76 36253276270685711237120 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 930174 1048576 36253276270685711237120 75557863725914323419136 1030380084 2147483648 391196 390814 (ep1360 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1362 := BSN.sin_dyadic_bound_f 1030380084 2147483648 2 1 1048576 391196 ep1359 ep58 ep1359 ep1359 ep59 ep1359 484032 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1030380084) qz15 0 1 ep1359 ep58 ep1359 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1030380084) qz16 0 1 ep1359 ep59 ep1359 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1363 := @Enclosure.Real.IsNear.sin_image qz215 qz495 Bool.false 252257755 524288 733 1048576 Bool.true 484032 1048576 1 195407 (@Enclosure.Real.IsNear.recentre' qz215 Bool.false 1083438808678743864583 2251799813685248000 13644200013330860947 19540700000000000000000 252257755 524288 733 1048576 (ep1358 rfl) rfl) (Enclosure.sfrac_false_div 252257755 524288) (BSN.sin_reduce2 qz495 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 36253276270685711237120) qz43) 226375608064910080 72057594037927936 Bool.false 484032 1048576 76 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q2 252257755 524288 226375608064910080 72057594037927936 76 36253276270685711237120 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 484032 1048576 36253276270685711237120 75557863725914323419136 1030380084 2147483648 391196 390814 (ep1362 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1364 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz434 (Real.cos qz215)) (@HMul.hMul Real Real Real qz0 qz434 (@Neg.neg Real Real.instNeg (Real.sin qz215))) Bool.true 83636130123 549755813888 6531994461657 53713067162206208 Bool.false 1360046727 17179869184 13020399288417 107426134324412416 (@Enclosure.Real.IsNear.mulLit_ft qz434 (Real.cos qz215) 179829 1048576 1 1048576 465087 524288 144281907 204899090432 83636130123 549755813888 6531994461657 53713067162206208 qz438 (@Enclosure.Real.IsNear.recentre' (Real.cos qz215) Bool.true 930174 1048576 144281907 204899090432 465087 524288 144281907 204899090432 (ep1361 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz434 (@Neg.neg Real Real.instNeg (Real.sin qz215)) 179829 1048576 1 1048576 7563 16384 144281907 204899090432 1360046727 17179869184 13020399288417 107426134324412416 qz438 (@Enclosure.Real.IsNear.neg (Real.sin qz215) Bool.true 7563 16384 144281907 204899090432 (@Enclosure.Real.IsNear.recentre' (Real.sin qz215) Bool.true 484032 1048576 144281907 204899090432 7563 16384 144281907 204899090432 (ep1363 rfl rfl) rfl)) rfl)

noncomputable def ep1365 := @ep1339 83636130123 549755813888 6531994461657 53713067162206208 Bool.false 1360046727 17179869184 13020399288417 107426134324412416 Bool.false ep1340 1372720869279 274877906944 352564077344301 53713067162206208 Bool.false 1351354276818238570496 78659171519 1099511627776 1409901110061617 214852268648824832 (ep1341 (BSN.head_sum_c_succ qz143 33 34 rfl rfl) (ep1356 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1357 ep1364) rfl rfl

noncomputable def ep1366 := @Enclosure.Complex.IsNear.mul qz211 (@HAdd.hAdd Complex Complex Complex qz4 qz212 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz213 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1))))) Bool.false 1052179719241486324519771 ep1205 ep1331 ep1207 Bool.true

noncomputable def ep1367 := nat_lit 2149270665798819218718720

noncomputable def ep1368 := nat_lit 6265406543376606697168129

noncomputable abbrev qz216 := (Complex.re qz492)

noncomputable abbrev qz217 := (Complex.im qz492)

noncomputable def ep1369 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 qz216 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz212 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz213 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz217 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz212 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz213 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1))))))) 49772343432566174594987 ep1367 ep1368

noncomputable def ep1370 := nat_lit 104995633247937466768042229760

noncomputable def ep1371 := nat_lit 2388023691433786812139697

noncomputable def ep1372 := nat_lit 214927066579881921871872000

noncomputable def ep1373 := nat_lit 1721422109265240020328918929

noncomputable def ep1374 := nat_lit 209991266495874933536084459520000

noncomputable def ep1375 := nat_lit 15829933039999147926956262026790736228425494691840

noncomputable def ep1376 := @Enclosure.Real.IsNear.mulLit_ff qz216 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz212 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz213 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))))) 25449503467 549755813888 3203616196289 26856533581103104 1955729450561

noncomputable abbrev qz682 := (Real.log (Enclosure.sfrac Bool.false 35 1))

noncomputable abbrev qz218 := (@HMul.hMul Real Real Real qz269 qz441 qz682)

noncomputable abbrev qz219 := (Real.sin (@HMul.hMul Real Real Real qz269 qz441 qz682))

noncomputable abbrev qz496 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 35)))

noncomputable abbrev qz683 := (@Neg.neg Real Real.instNeg qz219)

noncomputable def ep1377 := @Enclosure.Complex.IsNear.of_eq qz211 (Complex.mk (@HMul.hMul Real Real Real qz0 qz496 (Real.cos qz218)) (@HMul.hMul Real Real Real qz0 qz496 qz683)) Bool.false 25449503467 549755813888 3203616196289 26856533581103104 Bool.true 178744889885 1099511627776 25769878788889 214852268648824832 (BSN.cpow_neg_s_mk qz146 136442 1000 35 qz147 rfl)

noncomputable abbrev qz497 := (Real.sqrt (@Nat.cast Real Real.instNatCast 35))

noncomputable abbrev qz498 := (@Nat.cast Real Real.instNatCast 35)

noncomputable abbrev qz684 := (@HDiv.hDiv Real Real Real qz1 qz498 qz14)

noncomputable def ep1378 := @Enclosure.Real.IsNear.inv_image qz497 6203459 1048576 1 1048576 88620 88621 524288 (@Enclosure.Real.IsNear.of_eq qz497 (Real.sqrt qz684) Bool.false 6203459 1048576 1 1048576 (BSN.sqrt_natCast_div_one 35) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz684) Bool.false 6203459 1048576 1 1048576 6203459 1048576 1 1048576 (BSN.sqrt_enclosure 35 1 3101729 3101730 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep1379 := BSN.log_dyadic_bound 3 67 2 1 13467 524288 195407 9 9 46982 70 64 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 3) (BSN.artanhQ 67) 0 1 9 13467 9 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep1380 := @Enclosure.Real.IsNear.mulLit_ff qz146 qz682 136442 1000 0 1 16011859227414739 4503599627370496 200000000195407 39081400000000000000 1092345048353460909319 2251799813685248000 13644200013330860947 19540700000000000000000 qz148 (BSN.isNear_log_sfrac 35 1 16011859227414739 4503599627370496 200000000195407 39081400000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz684) Bool.false 67158605204982549446656 18889465931478580854784 1000000000977035 195407000000000000000 16011859227414739 4503599627370496 200000000195407 39081400000000000000 (BSN.log_rat_reduce_isNear 35 1 5 70 64 46982 524288 24973259072661432 36028797018963968 195407 1000000000000000 rfl rfl rfl rfl (ep1379 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1381 := nat_lit 2129982673196061990148485469218895038626374771039628696619375671134514507953281

noncomputable def ep1382 := nat_lit 3542004033425636201562179705755463590624414721352461478797017511024450614401

noncomputable def ep1383 := nat_lit 6382864011521334698042332048245174188697875483676181166900532978381494622631041

noncomputable def ep1384 := BSN.cos_dyadic_bound_f 2777513199 2147483648 3 2 1048576 391196 ep1381 ep79 ep1382 ep1383 ep81 ep1382 287174 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2777513199) qz19 0 2 ep1381 ep79 ep1382 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2777513199) qz20 0 2 ep1383 ep81 ep1382 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz499 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 508662801) qz23)

noncomputable def ep1385 := @Enclosure.Real.IsNear.cos_image qz218 qz499 Bool.false 508662801 1048576 733 1048576 Bool.false 287174 1048576 1 195407 (@Enclosure.Real.IsNear.recentre' qz218 Bool.false 1092345048353460909319 2251799813685248000 13644200013330860947 19540700000000000000000 508662801 1048576 733 1048576 (ep1380 rfl) rfl) (Enclosure.sfrac_false_div 508662801 1048576) (BSN.cos_reduce0 qz499 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 195450115807133493624832) qz24) 226375608064910080 72057594037927936 Bool.false 287174 1048576 77 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q0 508662801 1048576 226375608064910080 72057594037927936 77 195450115807133493624832 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 287174 1048576 195450115807133493624832 151115727451828646838272 2777513199 2147483648 391196 390814 (ep1384 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1386 := nat_lit 3831135208526171073306024100829406698654975056094249684731838594033306553824385

noncomputable def ep1387 := nat_lit 10028190872942997019094200544553413460187733237364654712855810670307477578069121

noncomputable def ep1388 := BSN.sin_dyadic_bound_f 2777513199 2147483648 3 2 1048576 391196 ep1386 ep72 ep1382 ep1387 ep75 ep1382 1008485 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2777513199) qz15 0 2 ep1386 ep72 ep1382 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2777513199) qz16 0 2 ep1387 ep75 ep1382 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1389 := @Enclosure.Real.IsNear.sin_image qz218 qz499 Bool.false 508662801 1048576 733 1048576 Bool.false 1008485 1048576 1 195407 (@Enclosure.Real.IsNear.recentre' qz218 Bool.false 1092345048353460909319 2251799813685248000 13644200013330860947 19540700000000000000000 508662801 1048576 733 1048576 (ep1380 rfl) rfl) (Enclosure.sfrac_false_div 508662801 1048576) (BSN.sin_reduce0 qz499 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 195450115807133493624832) qz24) 226375608064910080 72057594037927936 Bool.false 1008485 1048576 77 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q0 508662801 1048576 226375608064910080 72057594037927936 77 195450115807133493624832 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1008485 1048576 195450115807133493624832 151115727451828646838272 2777513199 2147483648 391196 390814 (ep1388 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1390 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz496 (Real.cos qz218)) (@HMul.hMul Real Real Real qz0 qz496 qz683) Bool.false 25449503467 549755813888 3203616196289 26856533581103104 Bool.true 178744889885 1099511627776 25769878788889 214852268648824832 (@Enclosure.Real.IsNear.mulLit_ff qz496 (Real.cos qz218) 177241 1048576 1 1048576 143587 524288 144281907 204899090432 25449503467 549755813888 3203616196289 26856533581103104 (@Enclosure.Real.IsNear.recentre' qz496 Bool.false 177241 1048576 1 1048576 177241 1048576 1 1048576 (ep1378 rfl rfl) rfl) (@Enclosure.Real.IsNear.recentre' (Real.cos qz218) Bool.false 287174 1048576 144281907 204899090432 143587 524288 144281907 204899090432 (ep1385 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz496 qz683 177241 1048576 1 1048576 1008485 1048576 144281907 204899090432 178744889885 1099511627776 25769878788889 214852268648824832 (@Enclosure.Real.IsNear.recentre' qz496 Bool.false 177241 1048576 1 1048576 177241 1048576 1 1048576 (ep1378 rfl rfl) rfl) (@Enclosure.Real.IsNear.neg qz219 Bool.false 1008485 1048576 144281907 204899090432 (@Enclosure.Real.IsNear.recentre' qz219 Bool.false 1008485 1048576 144281907 204899090432 1008485 1048576 144281907 204899090432 (ep1389 rfl rfl) rfl)) rfl)

noncomputable def ep1391 := @ep1376 3909500566440 0 1 49772343432566174594987 ep1367 ep1368 ep1370 (@Enclosure.Complex.IsNear.re_isNear qz211 Bool.false 25449503467 549755813888 3203616196289 26856533581103104 Bool.true 178744889885 1099511627776 25769878788889 214852268648824832 (ep1377 ep1390))

noncomputable def ep1392 := @Enclosure.Complex.IsNear.re_isNear (@HAdd.hAdd Complex Complex Complex qz4 qz212 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz213 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1))))) Bool.false 1955729450561 3909500566440 0 1 Bool.false

noncomputable def ep1393 := @Enclosure.Complex.IsNear.addLitP qz212 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz213 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) Bool.false 4645417341 9308334682 0 1 Bool.true 1193867500

noncomputable def ep1394 := @ep1393 4654167341 0 1 Bool.false 1 840 0 1 Bool.false 68221 210000 0 1 Bool.false 3911458901122 1955729450561 3909500566440 0 1 Bool.false 66799775170361 66799775170361 977375141610000 0 1

noncomputable abbrev qz220 := (@HDiv.hDiv Complex Complex Complex qz403 qz493 (@HSub.hSub Complex Complex Complex qz395 qz439 (1 : Complex)))

noncomputable def ep1395 := @Enclosure.Complex.IsNear.addLitP qz220 qz105 Bool.true 70000000 74466677456 0 1 Bool.true 19101880000 74466677456 0 1

noncomputable def ep1396 := @Enclosure.Complex.IsNear.of_eq qz220 (Complex.mk (Enclosure.sfrac Bool.true 70000000 74466677456) (Enclosure.sfrac Bool.true 19101880000 74466677456)) Bool.true 70000000 74466677456 0 1 Bool.true 19101880000 74466677456 0 1

noncomputable def ep1397 := @ep1395 Bool.false 1 2 0 1 Bool.false 0 1 0 1 Bool.false 74326677456 4645417341 9308334682 0 1 Bool.true 19101880000 1193867500 4654167341 0 1 (ep1396 (BSN.N_div_s_sub_one_mk qz146 136442 1000 35 qz147 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 70000000 74466677456) (Enclosure.sfrac Bool.true 19101880000 74466677456) Bool.true 70000000 74466677456 0 1 Bool.true 19101880000 74466677456 0 1 (Enclosure.Real.IsNear.const Bool.true 70000000 74466677456) (Enclosure.Real.IsNear.const Bool.true 19101880000 74466677456))) qz106 rfl

noncomputable abbrev qz221 := (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz428 qz493 1))

noncomputable def ep1398 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz213 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@HAdd.hAdd Complex Complex Complex qz4 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz213 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1))) qz221)) Bool.false 1 840 0 1

noncomputable def ep1399 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz213 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1))) qz221) Bool.false 0 1 0 1 Bool.false

noncomputable def ep1400 := @ep1399 0 1 0 1 Bool.false 1 840 0 1 Bool.false 68221 210000 0 1 Bool.false 1 1 840 0 1 Bool.false 68221 68221 210000 0

noncomputable def ep1401 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz213 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (Complex.mk qz10 qz10) Bool.false 0 1 0 1 Bool.false

noncomputable def ep1402 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1))) qz221 Bool.false 1 840 0 1 Bool.false 68221 210000 0 1

noncomputable def ep1403 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz221)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz221)) 1 840 0 1 0 1 0

noncomputable def ep1404 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz221) 1 24 0 1 1 35 0 1 1

noncomputable def ep1405 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1)))) 1 24 0 1 0 1 0 1 1

noncomputable def ep1406 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 1 2 0 1 1 24 0

noncomputable def ep1407 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1)) qz143 Bool.false 1 2 0 1 Bool.false 136442 1000 0 1 (BSN.ascPochhammer_one_eval qz143)

noncomputable def ep1408 := ep1407 (@Enclosure.Complex.IsNear.of_eq qz143 (Complex.mk qz100 qz146) Bool.false 1 2 0 1 Bool.false 136442 1000 0 1 (BSN.s_crit_mk qz146 Bool.false 136442 1000 qz147) (@Enclosure.Complex.IsNear.mk qz100 qz146 Bool.false 1 2 0 1 Bool.false 136442 1000 0 1 qz409 qz148))

noncomputable def ep1409 := @ep1406 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep727) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 136442 1000 0 1 ep1408)

noncomputable def ep1410 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 136442 1000 0 1 0 1 0

noncomputable def ep1411 := @ep1410 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep727) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 136442 1000 0 1 ep1408)

noncomputable def ep1412 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1)))) 68221 6000 0 1 0 1 0 1 68221

noncomputable def ep1413 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 136442 1000 0 1 68221 6000 0

noncomputable def ep1414 := @ep1413 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep727) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 136442 1000 0 1 ep1408)

noncomputable def ep1415 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 1 2 0 1 0 1 0

noncomputable def ep1416 := @ep1415 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep727) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 136442 1000 0 1 ep1408)

noncomputable def ep1417 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 24 0 1 Bool.false 68221 6000 0 1 (@ep1405 1 24 0 1 (ep1409 rfl) (ep1411 rfl) rfl rfl) (@ep1412 68221 6000 0 1 (ep1414 rfl) (ep1416 rfl) rfl rfl)

noncomputable def ep1418 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 68221 6000 0 1 ep1417

noncomputable abbrev qz222 := (@Enclosure.Complex.IsNear.of_eq (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz428 qz493 1)) (Complex.mk (Enclosure.sfrac Bool.false 1 35) qz548) Bool.false 1 35 0 1 Bool.false 0 1 0 1 (BSN.natCast_pow_inv_mk 35 1 35 EMRow46.d17 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 35) qz548 Bool.false 1 35 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 35) qz550))

noncomputable def ep1419 := @ep1404 840 0 1 ep1418 (@Enclosure.Complex.IsNear.re_isNear qz221 Bool.false 1 35 0 1 Bool.false 0 1 0 1 qz222)

noncomputable def ep1420 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz221) 68221 6000 0 1 0 1 0 1 0

noncomputable def ep1421 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 68221 6000 0 1 ep1417

noncomputable def ep1422 := @ep1420 1 0 1 ep1421 (@Enclosure.Complex.IsNear.im_isNear qz221 Bool.false 1 35 0 1 Bool.false 0 1 0 1 qz222)

noncomputable def ep1423 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz221)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz221)) 0 1 0 1 68221 210000 0

noncomputable def ep1424 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz221) 1 24 0 1 0 1 0 1 0

noncomputable def ep1425 := @ep1424 1 0 1 ep1418 (@Enclosure.Complex.IsNear.im_isNear qz221 Bool.false 1 35 0 1 Bool.false 0 1 0 1 qz222)

noncomputable def ep1426 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz221) 68221 6000 0 1 1 35 0 1 68221

noncomputable def ep1427 := @ep1426 210000 0 1 ep1421 (@Enclosure.Complex.IsNear.re_isNear qz221 Bool.false 1 35 0 1 Bool.false 0 1 0 1 qz222)

noncomputable def ep1428 := @ep1400 1 (@ep1401 0 1 0 1 (BSN.bern_sum_base qz143 35) qz121) (ep1402 (@ep1403 1 1 1 840 0 1 (ep1419 rfl) (ep1422 rfl) rfl rfl) (@ep1423 1 68221 68221 210000 0 1 (ep1425 rfl) (ep1427 rfl) rfl rfl)) rfl rfl rfl rfl rfl

noncomputable def ep1429 := ep1394 (ep1397 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep1398 Bool.false 68221 210000 0 1 (BSN.bern_sum_succ qz143 35 0 1 1 rfl rfl) (ep1428 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl rfl

noncomputable def ep1430 := @Enclosure.Real.IsNear.mulLit_tf qz217 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz212 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz213 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))))) 178744889885 1099511627776 25769878788889 214852268648824832 66799775170361

noncomputable def ep1431 := @ep1430 977375141610000 0 1 ep1371 ep1372 ep1373 ep1374 (@Enclosure.Complex.IsNear.im_isNear qz211 Bool.false 25449503467 549755813888 3203616196289 26856533581103104 Bool.true 178744889885 1099511627776 25769878788889 214852268648824832 (ep1377 ep1390))

noncomputable def ep1432 := @Enclosure.Complex.IsNear.im_isNear (@HAdd.hAdd Complex Complex Complex qz4 qz212 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz213 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1))))) Bool.false 1955729450561 3909500566440 0 1 Bool.false

noncomputable def ep1433 := nat_lit 1700021109792922785141587

noncomputable def ep1434 := nat_lit 537317666449704804679680000

noncomputable def ep1435 := nat_lit 214000841644232293790990329

noncomputable def ep1436 := @Enclosure.Real.IsNear.addLit_ft_n (@HMul.hMul Real Real Real qz0 qz216 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz212 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz213 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz217 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz212 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz213 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1))))))) ep1433 ep1434 ep1435

noncomputable def ep1437 := nat_lit 26248908311984366692010557440000

noncomputable def ep1438 := nat_lit 50398910884817452081616729

noncomputable def ep1439 := nat_lit 839965065983499734144337838080

noncomputable def ep1440 := nat_lit 36105219257004374384175848479284046302577157996544

noncomputable def ep1441 := @Enclosure.Real.IsNear.mulLit_ff qz216 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz212 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz213 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))))) 25449503467 549755813888 3203616196289 26856533581103104 66799775170361

noncomputable def ep1442 := @ep1441 977375141610000 0 1 ep1433 ep1434 ep1435 ep1437 (@Enclosure.Complex.IsNear.re_isNear qz211 Bool.false 25449503467 549755813888 3203616196289 26856533581103104 Bool.true 178744889885 1099511627776 25769878788889 214852268648824832 (ep1377 ep1390))

noncomputable def ep1443 := @Enclosure.Real.IsNear.mulLit_tf qz217 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz212 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz213 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))))) 178744889885 1099511627776 25769878788889 214852268648824832 1955729450561

noncomputable def ep1444 := @ep1443 3909500566440 0 1 69915329057075499295097 859708266319527687487488 ep1438 ep1439 (@Enclosure.Complex.IsNear.im_isNear qz211 Bool.false 25449503467 549755813888 3203616196289 26856533581103104 Bool.true 178744889885 1099511627776 25769878788889 214852268648824832 (ep1377 ep1390))

noncomputable abbrev qz685 := (ep1429 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable def ep1445 := @ep1366 ep1332 ep1326 ep1333 ep1328 (@ep1369 ep1370 ep1371 ep1372 ep1373 ep1374 ep1375 1052179719241486324519771 ep1205 ep1331 ep1207 (ep1391 (@ep1392 66799775170361 977375141610000 0 1 qz685) rfl) (ep1431 (@ep1432 66799775170361 977375141610000 0 1 qz685) rfl) rfl rfl) (@ep1436 ep1437 69915329057075499295097 859708266319527687487488 ep1438 ep1439 ep1440 ep1332 ep1326 ep1333 ep1328 (ep1442 (@ep1432 66799775170361 977375141610000 0 1 qz685) rfl) (ep1444 (@ep1392 66799775170361 977375141610000 0 1 qz685) rfl) rfl rfl)

noncomputable def ep1446 := @ep1336 ep1327 ep1328 (@ep1337 214852268648824832 (BSN.head_sum_c_eq qz143 35) (ep1338 (BSN.head_sum_c_succ qz143 34 35 rfl rfl) (ep1365 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))) ep1445 rfl rfl rfl

noncomputable def ep1447 := @Enclosure.Complex.IsNear.re_isNear (zetaApproximant qz143 1 35) Bool.false ep1204 ep1205 ep1206 ep1207 Bool.true 592883349954218728583173 ep1326 ep1327 ep1328 (@ep1329 ep1207 Bool.true 592883349954218728583173 ep1326 ep1327 ep1328 (BSN.zetaApproximant_eq_folded' qz143 1 35 rfl) (ep1446 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

noncomputable def ep1448 := @Enclosure.Real.IsNear.mulLit_tt (Real.sin (@HSub.hSub Real Real Real qz398 (Complex.im (@HSub.hSub Complex Complex Complex qz81 qz182 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz183 (@Nat.cast Complex Complex.instNatCast j))))) qz184)) (Complex.im (zetaApproximant qz143 1 35)) 291 524288 74326201

noncomputable def ep1449 := @Enclosure.Real.IsNear.recentre' (Real.sin (@HSub.hSub Real Real Real qz398 (Complex.im (@HSub.hSub Complex Complex Complex qz81 qz182 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz183 (@Nat.cast Complex Complex.instNatCast j))))) qz184)) Bool.true 582 1048576 74326201

noncomputable def ep1450 := @Enclosure.Real.IsNear.sin_image (@HSub.hSub Real Real Real qz398 (Complex.im (@HSub.hSub Complex Complex Complex qz81 qz182 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz183 (@Nat.cast Complex Complex.instNatCast j))))) qz184) qz476 Bool.false 74119761 524288 375

noncomputable def ep1451 := BSN.sin_dyadic_bound_f 1192704 2147483648 1 0 1048576 391196 0 1 1 0 1 1 582 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 1192704) qz15 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 1192704) qz16 0 0 rfl) rfl rfl

noncomputable def ep1452 := @ep1450 1048576 Bool.true 582 1048576 1 195407 (@ep1212 74119761 524288 375 1048576 ep1323 rfl) (Enclosure.sfrac_false_div 74119761 524288) (BSN.sin_reduce2 qz476 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 41964550285261012992) qz43) 226375608064910080 72057594037927936 Bool.false 582 1048576 22 1000000000000000 390814 195407 (BSN.sin_reduce_arg_pos_rat_q2 74119761 524288 226375608064910080 72057594037927936 22 41964550285261012992 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 582 1048576 41964550285261012992 75557863725914323419136 1192704 2147483648 391196 390814 (ep1451 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1453 := @Enclosure.Complex.IsNear.im_isNear (zetaApproximant qz143 1 35) Bool.false ep1204 ep1205 ep1206 ep1207 Bool.true 592883349954218728583173 ep1326 ep1327 ep1328 (@ep1329 ep1207 Bool.true 592883349954218728583173 ep1326 ep1327 ep1328 (BSN.zetaApproximant_eq_folded' qz143 1 35 rfl) (ep1446 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

theorem EMRow46.d18 : Enclosure.Real.IsNear (hardyZApproximantEM 1 35 qz146) Bool.true ep1187 ep1188 ep1189 ep1190 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantEM 1 35 qz146) ep1191 Bool.true ep1187 ep1188 ep1189 ep1190 (@Eq.refl Real ep1191) (@ep1192 Bool.true ep1187 ep1188 ep1189 ep1190 (BSN.re_exp_mul (@HSub.hSub Real Real Real qz398 (Complex.im (@HSub.hSub Complex Complex Complex qz81 qz182 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz183 (@Nat.cast Complex Complex.instNatCast j))))) qz184) (zetaApproximant qz143 1 35)) (@ep1194 ep1195 ep1196 ep1197 ep1198 ep1199 ep1200 ep1201 ep1202 ep1187 ep1188 ep1189 ep1190 (@ep1203 204899090432 ep1204 ep1205 ep1206 ep1207 ep1193 ep1195 ep1196 ep1197 (@ep1208 204899090432 1048575 1048576 74326201 204899090432 (ep1325 rfl rfl) rfl) ep1447 rfl) (@ep1448 204899090432 592883349954218728583173 ep1326 ep1327 ep1328 ep1198 ep1199 ep1200 ep1201 (@ep1449 204899090432 291 524288 74326201 204899090432 (ep1452 rfl rfl) rfl) ep1453 rfl) rfl rfl))

theorem EMRow46.d19 : @Eq Nat (Nat.mul (BSN.factNat (Nat.succ (Nat.mul 2 1))) (Nat.pow 4 (Nat.mul 2 1))) 96 := @Eq.refl Nat 96

theorem EMRow46.d20 : @Eq Nat (Nat.mul (Nat.mul 2 1) (Nat.pow (Nat.succ (Nat.mul 4 2)) (Nat.mul 2 1))) 162 := @Eq.refl Nat 162

theorem EMRow46.d21 : @Eq Nat (BSN.factNat (Nat.mul 2 2)) 24 := @Eq.refl Nat 24

theorem EMRow46.d22 : @Eq Nat (Nat.pow 34 (Nat.succ (Nat.mul 2 3))) 52523350144 := @Eq.refl Nat 52523350144

noncomputable abbrev qz686 := (@HAdd.hAdd Complex Complex Complex qz691 qz690 (@Nat.cast Complex Complex.instNatCast 3))

noncomputable abbrev qz500 := qz686

noncomputable abbrev qz223 := (@HDiv.hDiv Real Real Real qz272 (@Norm.norm Complex Complex.instNorm qz500) (@HAdd.hAdd Real Real Real qz418 (Complex.re qz273) qz291))

noncomputable abbrev qz224 := (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 2)

noncomputable abbrev qz225 := (@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 2)))

noncomputable abbrev qz501 := (@HPow.hPow Complex Complex Complex qz539 (@Nat.cast Complex Complex.instNatCast 34) (@HSub.hSub Complex Complex Complex qz628 qz540 qz546))

noncomputable abbrev qz226 := qz501

noncomputable def ep1454 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 34))) (@HMul.hMul Real Real Real qz0 qz223 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz226))) 6710769455 618475290624 62150969 618475290624 285092544980445871 504403158265495552 63133341113

noncomputable def ep1455 := nat_lit 179707627919010670794625777664

noncomputable def ep1456 := @Enclosure.Real.IsNear.mulLit_ff (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 34)) 26561 1769472 1 1769472 757965 1048576 6991 1048576 6710769455 618475290624

noncomputable abbrev qz227 := (@HMul.hMul Real Real Real qz269 (2 : Real) Real.pi)

noncomputable abbrev qz687 := (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid)))

noncomputable abbrev qz502 := (@Inv.inv Real Real.instInv (@HPow.hPow Real Nat Real qz687 qz227 2))

noncomputable def ep1457 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 96 162) qz502 96 162 0 1 26561 1048576 1 1048576 26561 1769472 1 1769472

noncomputable def ep1458 := nat_lit 781950621441006189802102638025

noncomputable def ep1459 := nat_lit 19807040628566084398385987584

noncomputable def ep1460 := nat_lit 26986075409044041160201671

noncomputable def ep1461 := nat_lit 1073741824000000000000000000000000000000

noncomputable abbrev qz503 := (@HPow.hPow Real Nat Real qz687 qz227 1)

noncomputable def ep1462 := @Enclosure.Real.IsNear.mulLit_ff qz503 qz227 884279719003555 140737488355328 1 500000000000000 884279719003555 140737488355328 1 500000000000000 ep1458 ep1459 ep1460 ep1461

noncomputable def ep1463 := ep1462 (@Enclosure.Real.IsNear.of_eq qz503 qz227 Bool.false 884279719003555 140737488355328 1 500000000000000 (BSN.pow_one_r qz227) (@Enclosure.Real.IsNear.of_eq qz227 qz270 Bool.false 884279719003555 140737488355328 1 500000000000000 BSN.two_pi_eq qz271)) (@Enclosure.Real.IsNear.of_eq qz227 qz270 Bool.false 884279719003555 140737488355328 1 500000000000000 BSN.two_pi_eq qz271) rfl

noncomputable abbrev qz504 := (@HPow.hPow Real Nat Real qz687 qz227 2)

noncomputable def ep1464 := @Enclosure.Real.IsNear.inv_image qz504 ep1458 ep1459 ep1460 ep1461 13280 13281 524288 (@Enclosure.Real.IsNear.of_eq qz504 (@HMul.hMul Real Real Real qz0 qz503 qz227) Bool.false ep1458 ep1459 ep1460 ep1461 (BSN.pow_succ_r qz227 1 2 rfl) ep1463) rfl rfl rfl

noncomputable def ep1465 := ep1457 (Enclosure.Real.IsNear.const Bool.false 96 162) (@Enclosure.Real.IsNear.recentre' qz502 Bool.false 26561 1048576 1 1048576 26561 1048576 1 1048576 (ep1464 rfl rfl rfl) rfl)

noncomputable def ep1466 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 34)) (Real.sqrt (@HAdd.hAdd Real Real Real qz418 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz5 1 34)) (Complex.re (zetaApproximant qz5 1 34))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz5 1 34)) (Complex.im (zetaApproximant qz5 1 34))))) Bool.false 757965 1048576 6991 1048576

noncomputable def ep1467 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz418 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz5 1 34)) (Complex.re (zetaApproximant qz5 1 34))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz5 1 34)) (Complex.im (zetaApproximant qz5 1 34))))) Bool.false 757965 1048576 6991 1048576

noncomputable def ep1468 := nat_lit 337679999925608556546333561131133230447413

noncomputable def ep1469 := nat_lit 646204066833316044195101180251540029440000

noncomputable def ep1470 := nat_lit 171814272047728263323984977974292574474286861092577158532827

noncomputable def ep1471 := nat_lit 17827159374428964553035546430323418810300401722036542504960000

noncomputable def ep1472 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz418 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz5 1 34)) (Complex.re (zetaApproximant qz5 1 34))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz5 1 34)) (Complex.im (zetaApproximant qz5 1 34)))) ep1468 ep1469 ep1470 ep1471 375487 382478

noncomputable def ep1473 := nat_lit 60934451310395089947415042245766321694898398325841

noncomputable def ep1474 := nat_lit 116719097615802337231525745194947924276816117760000

noncomputable def ep1475 := nat_lit 41493990176253030802655920399775536799267900519301040083791

noncomputable def ep1476 := nat_lit 4456789843607241138258886607580854702575100430509135626240000

noncomputable def ep1477 := nat_lit 232834357552518544585111798379845942758541858369

noncomputable def ep1478 := nat_lit 466876390463209348926102980779791697107264471040000

noncomputable def ep1479 := nat_lit 5838311342716140113361296375190427277215259015372998197663

noncomputable def ep1480 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz5 1 34)) (Complex.re (zetaApproximant qz5 1 34))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz5 1 34)) (Complex.im (zetaApproximant qz5 1 34))) ep1473 ep1474 ep1475 ep1476 ep1477 ep1478 ep1479

noncomputable def ep1481 := nat_lit 28476032898760921623200227139963952067501841678119089852802531245329726145481710623409718773678080000

noncomputable def ep1482 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (zetaApproximant qz5 1 34)) (Complex.re (zetaApproximant qz5 1 34)) ep538 ep539 ep540 ep541 ep538 ep539 ep540 ep541 ep1473

noncomputable def ep1483 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (zetaApproximant qz5 1 34)) (Complex.im (zetaApproximant qz5 1 34)) 482529126118329301194463 ep666 ep667 ep668 482529126118329301194463 ep666 ep667 ep668 ep1477

noncomputable def ep1484 := @ep1454 504403158265495552 ep1455 2615090167368335399 4539628424389459968 456758301361025 4539628424389459968 (@ep1456 62150969 618475290624 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaStirlingErrorBound 1 2) (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 96 162) qz502) Bool.false 26561 1769472 1 1769472 (BSN.theta_err_eq 1 2 96 162 EMRow46.d19 EMRow46.d20 rfl) (ep1465 rfl)) (ep1466 (BSN.norm_eq_sqrt_mul_add (zetaApproximant qz5 1 34)) (@ep1467 757965 1048576 6991 1048576 (@ep1472 524288 (@ep1480 ep1471 ep1481 ep1468 ep1469 ep1470 ep1471 (@ep1482 ep1474 ep1475 ep1476 ep766 ep766 rfl) (@ep1483 ep1478 ep1479 ep1471 ep774 ep774 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl)

noncomputable abbrev qz228 := (@Norm.norm Complex Complex.instNorm qz500)

noncomputable abbrev qz688 := (Enclosure.sfrac Bool.false 2 7)

noncomputable def ep1485 := @Enclosure.Real.IsNear.of_eq (@HMul.hMul Real Real Real qz0 qz223 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz226))) (@HMul.hMul Real Real Real qz0 (@HMul.hMul Real Real Real qz0 qz228 qz688) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz226))) Bool.false 285092544980445871 504403158265495552 63133341113 504403158265495552 (BSN.zrb_shape_eq qz228 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz226)) qz12 3)

noncomputable def ep1486 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz0 qz228 qz688) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz226)) 140971151 3670016 1 3670016 2022346721 137438953472 867 274877906944

noncomputable def ep1487 := @Enclosure.Real.IsNear.mulLit_ff qz228 qz688 140971151 1048576 1 1048576 2 7 0 1 140971151 3670016

noncomputable abbrev qz505 := (Complex.re qz686)

noncomputable abbrev qz506 := (Complex.im qz686)

noncomputable abbrev qz229 := (@HAdd.hAdd Real Real Real qz418 (@HMul.hMul Real Real Real qz269 qz505 qz505) (@HMul.hMul Real Real Real qz269 qz506 qz506))

noncomputable abbrev qz230 := qz500

noncomputable def ep1488 := @Enclosure.Real.IsNear.of_eq qz228 (Real.sqrt qz229) Bool.false 140971151 1048576 1 1048576 (BSN.norm_eq_sqrt_mul_add qz230)

noncomputable def ep1489 := @Enclosure.Real.IsNear.recentre' (Real.sqrt qz229) Bool.false 140971151 1048576 1 1048576 140971151

noncomputable def ep1490 := @Enclosure.Real.IsNear.sqrt_image qz229 722970641 40000 0 1 70485575 70485576 524288

noncomputable abbrev qz231 := (@HMul.hMul Real Real Real qz269 qz505 qz505)

noncomputable abbrev qz232 := (@HMul.hMul Real Real Real qz269 qz506 qz506)

noncomputable def ep1491 := @Enclosure.Real.IsNear.addLit_ff qz231 qz232 49 4 0 1 722480641 40000 0 1

noncomputable abbrev qz233 := qz505

noncomputable def ep1492 := @Enclosure.Real.IsNear.mulLit_ff qz233 qz233 7 2 0 1 7 2 0 1 49 4

noncomputable abbrev qz507 := (Enclosure.sfrac Bool.false 7 2)

noncomputable def ep1493 := @Enclosure.Complex.IsNear.of_eq qz230 (Complex.mk qz507 qz12) Bool.false 7 2 0 1 Bool.false 134395 1000 0 1 (BSN.s_add_nat_mk qz12 Bool.false 134395 1000 3 qz13)

noncomputable abbrev qz508 := (ep1493 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7 2) qz12 Bool.false 7 2 0 1 Bool.false 134395 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 7 2) qz18))

noncomputable def ep1494 := @ep1492 0 1 (@Enclosure.Complex.IsNear.re_isNear qz230 Bool.false 7 2 0 1 Bool.false 134395 1000 0 1 qz508)

noncomputable def ep1495 := ep1494 (@Enclosure.Complex.IsNear.re_isNear qz230 Bool.false 7 2 0 1 Bool.false 134395 1000 0 1 qz508)

noncomputable abbrev qz234 := qz506

noncomputable def ep1496 := @Enclosure.Real.IsNear.mulLit_ff qz234 qz234 134395 1000 0 1 134395 1000 0 1 722480641 40000

noncomputable def ep1497 := @ep1496 0 1 (@Enclosure.Complex.IsNear.im_isNear qz230 Bool.false 7 2 0 1 Bool.false 134395 1000 0 1 qz508)

noncomputable def ep1498 := ep1497 (@Enclosure.Complex.IsNear.im_isNear qz230 Bool.false 7 2 0 1 Bool.false 134395 1000 0 1 qz508)

noncomputable def ep1499 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz226)) (Real.sqrt (@HAdd.hAdd Real Real Real qz418 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz226)) (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz226))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz226)) (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz226))))) Bool.false 2022346721 137438953472

noncomputable def ep1500 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz418 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz226)) (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz226))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz226)) (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz226))))) Bool.false 16178773768 1099511627776

noncomputable def ep1501 := nat_lit 671917261749927789706375953476909059879463891907219762852341

noncomputable def ep1502 := nat_lit 3103303470253424938175652729979376096827946722421794406400000000

noncomputable def ep1503 := nat_lit 79895799996836929476523730826206203149228810878615149514838012404671076120189

noncomputable def ep1504 := nat_lit 861042562106999891433691574048717050520518106774956246306642139911091650560000000000000

noncomputable def ep1505 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz418 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz226)) (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz226))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz226)) (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz226)))) ep1501 ep1502 ep1503 ep1504

noncomputable def ep1506 := nat_lit 70383988274947993004159486473084039439465272201450070625982081

noncomputable def ep1507 := nat_lit 1939564668908390586359782956237110060517466701513621504000000000000

noncomputable def ep1508 := nat_lit 75103805338101853941167230448449018292616292589908111634039257983110481772013

noncomputable def ep1509 := nat_lit 4305212810534999457168457870243585252602590533874781231533210699555458252800000000000000

noncomputable def ep1510 := nat_lit 87391075079689218890581371112496030746299915060140570289182761

noncomputable def ep1511 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz226)) (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz226))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz226)) (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz226))) ep1506 ep1507 ep1508 ep1509 ep1510

noncomputable def ep1512 := nat_lit 484891167227097646589945739059277515129366675378405376000000000000

noncomputable def ep1513 := nat_lit 81093798661520698360362855920645499363381940450791908985037701010061224707233

noncomputable def ep1514 := nat_lit 1076303202633749864292114467560896313150647633468695307883302674888864563200000000000000

noncomputable def ep1515 := nat_lit 203629215831223610601890244190127700354666385441815102994437635590003827994921301141166602701678576633091205365760000000000000000

noncomputable def ep1516 := nat_lit 8389516569799954391419687500991

noncomputable def ep1517 := nat_lit 1392682544196052809261514752000000

noncomputable def ep1518 := nat_lit 54851581165338439837759096116619441

noncomputable def ep1519 := nat_lit 37882330140119414505690414264342282240000000

noncomputable def ep1520 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz226)) (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz226)) ep1516 ep1517 ep1518 ep1519 ep1516 ep1517 ep1518

noncomputable def ep1521 := nat_lit 9348319371934680478660111424819

noncomputable def ep1522 := nat_lit 696341272098026404630757376000000

noncomputable def ep1523 := nat_lit 53151834107748429319735177136108639

noncomputable def ep1524 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz226) Bool.false ep1516 ep1517 ep1518 ep1519 Bool.true ep1521 ep1522 ep1523

noncomputable def ep1525 := nat_lit 18941165070059707252845207132171141120000000

noncomputable def ep1526 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz226 Bool.false ep1516 ep1517 ep1518 ep1519 Bool.true ep1521 ep1522 ep1523 ep1525

noncomputable def ep1527 := nat_lit 1026848703425425793688112733

noncomputable def ep1528 := nat_lit 2321137573660088015435857920000

noncomputable def ep1529 := nat_lit 5838092317951691505574125424973

noncomputable def ep1530 := nat_lit 63137216900199024176150690440570470400000

noncomputable def ep1531 := nat_lit 9005625791855209867632555140791

noncomputable def ep1532 := nat_lit 51348725774567424934414620861635641

noncomputable abbrev qz235 := (Complex.re qz501)

noncomputable abbrev qz236 := (Complex.im qz501)

noncomputable def ep1533 := @Enclosure.Real.IsNear.subLit_tt_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz235) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz236) ep1527 ep1528 ep1529 ep1530 ep1531 ep1517 ep1532

noncomputable def ep1534 := nat_lit 19473222135006570574636083553709982326431510564096935198720000

noncomputable def ep1535 := nat_lit 9865190140656097527523545381339136

noncomputable def ep1536 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz235 2167391923 19200000 0 1 2368857917501397355 604462909807314587353088 8080807521702236461053 ep1535 ep1527

noncomputable def ep1537 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) 2167391923 19200000 0 1 0 1 0 1 2167391923

noncomputable def ep1538 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 6502175769 80000 0 1 2167391923 19200000 0

noncomputable def ep1539 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (Complex.mk (Enclosure.sfrac Bool.true 1 720) qz10) Bool.true 1 720 0 1 Bool.false 0 1 0 1 (BSN.bern_coeff_mk 2 1 30 24 Bool.true BSN.bern_real_2 EMRow46.d21 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 1 720) qz10 Bool.true 1 720 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.true 1 720) qz21)

noncomputable abbrev qz509 := (@HAdd.hAdd Complex Complex Complex qz538 qz537 qz547)

noncomputable abbrev qz237 := qz509

noncomputable def ep1540 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) (@HMul.hMul Complex Complex Complex qz80 (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) qz237) Bool.true 6502175769 80000 0 1 Bool.true 19413374979439 8000000 0 1

noncomputable abbrev qz238 := (Complex.re qz509)

noncomputable abbrev qz239 := (Complex.im qz509)

noncomputable def ep1541 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz238) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz239) 722450641 16000 0 1 722480641 20000 0 1

noncomputable def ep1542 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz238 722450641 40000 0 1 5 2 0 1 722450641 16000

noncomputable abbrev qz510 := (@HAdd.hAdd Complex Complex Complex qz538 qz537 (@Nat.cast Complex Complex.instNatCast 1))

noncomputable abbrev qz240 := qz510

noncomputable def ep1543 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) (@HMul.hMul Complex Complex Complex qz80 (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) qz240) Bool.true 722450641 40000 0 1 Bool.false 26879 100 0 1

noncomputable abbrev qz241 := (Complex.re qz510)

noncomputable abbrev qz242 := (Complex.im qz510)

noncomputable def ep1544 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz241) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz242) 3 4 0 1 722480641 40000 0 1

noncomputable def ep1545 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz241 1 2 0 1 3 2 0 1 3 4

noncomputable def ep1546 := @ep1545 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 134395 1000 0 1 ep729)

noncomputable abbrev qz511 := (Enclosure.sfrac Bool.false 3 2)

noncomputable def ep1547 := @Enclosure.Complex.IsNear.of_eq qz240 (Complex.mk qz511 qz12) Bool.false 3 2 0 1 Bool.false 134395 1000 0 1 (BSN.s_add_nat_mk qz12 Bool.false 134395 1000 1 qz13)

noncomputable abbrev qz512 := (ep1547 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 3 2) qz12 Bool.false 3 2 0 1 Bool.false 134395 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 3 2) qz18))

noncomputable def ep1548 := ep1546 (@Enclosure.Complex.IsNear.re_isNear qz240 Bool.false 3 2 0 1 Bool.false 134395 1000 0 1 qz512)

noncomputable def ep1549 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz242 134395 1000 0 1 134395 1000 0 1 722480641 40000

noncomputable def ep1550 := @ep1549 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 134395 1000 0 1 ep729)

noncomputable def ep1551 := ep1550 (@Enclosure.Complex.IsNear.im_isNear qz240 Bool.false 3 2 0 1 Bool.false 134395 1000 0 1 qz512)

noncomputable def ep1552 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) qz240 Bool.true 722450641 40000 0 1 Bool.false 26879 100 0 1 (@ep1544 2889802564 722450641 40000 0 1 (ep1548 rfl) (ep1551 rfl) rfl rfl)

noncomputable def ep1553 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz242) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz241) 26879 400 0 1 80637 400 0 1

noncomputable def ep1554 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz242 1 2 0 1 134395 1000 0 1 26879 400

noncomputable def ep1555 := @ep1554 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 134395 1000 0 1 ep729)

noncomputable def ep1556 := ep1555 (@Enclosure.Complex.IsNear.im_isNear qz240 Bool.false 3 2 0 1 Bool.false 134395 1000 0 1 qz512)

noncomputable def ep1557 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz241 134395 1000 0 1 3 2 0 1 80637 400

noncomputable def ep1558 := @ep1557 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 134395 1000 0 1 ep729)

noncomputable def ep1559 := ep1558 (@Enclosure.Complex.IsNear.re_isNear qz240 Bool.false 3 2 0 1 Bool.false 134395 1000 0 1 qz512)

noncomputable abbrev qz243 := (ep1543 (BSN.ascPochhammer_succ_eval_c 1 2 qz273 rfl) (ep1552 (@ep1553 43006400 26879 100 0 1 (ep1556 rfl) (ep1559 rfl) rfl rfl)))

noncomputable def ep1560 := @ep1542 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 722450641 40000 0 1 Bool.false 26879 100 0 1 qz243)

noncomputable abbrev qz513 := (Enclosure.sfrac Bool.false 5 2)

noncomputable def ep1561 := @Enclosure.Complex.IsNear.of_eq qz237 (Complex.mk qz513 qz12) Bool.false 5 2 0 1 Bool.false 134395 1000 0 1 (BSN.s_add_nat_mk qz12 Bool.false 134395 1000 2 qz13)

noncomputable abbrev qz514 := (ep1561 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 5 2) qz12 Bool.false 5 2 0 1 Bool.false 134395 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 5 2) qz18))

noncomputable def ep1562 := ep1560 (@Enclosure.Complex.IsNear.re_isNear qz237 Bool.false 5 2 0 1 Bool.false 134395 1000 0 1 qz514)

noncomputable def ep1563 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz239 26879 100 0 1 134395 1000 0 1 722480641 20000

noncomputable def ep1564 := @ep1563 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 722450641 40000 0 1 Bool.false 26879 100 0 1 qz243)

noncomputable def ep1565 := ep1564 (@Enclosure.Complex.IsNear.im_isNear qz237 Bool.false 5 2 0 1 Bool.false 134395 1000 0 1 qz514)

noncomputable def ep1566 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) qz237 Bool.true 6502175769 80000 0 1 Bool.true 19413374979439 8000000 0 1 (@ep1541 26008703076000 6502175769 80000 0 1 (ep1562 rfl) (ep1565 rfl) rfl rfl)

noncomputable def ep1567 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz239) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz238) 19418750779439 8000000 0 1 26879 40 0 1

noncomputable def ep1568 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz239 722450641 40000 0 1 134395 1000 0 1 19418750779439 8000000

noncomputable def ep1569 := @ep1568 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 722450641 40000 0 1 Bool.false 26879 100 0 1 qz243)

noncomputable def ep1570 := ep1569 (@Enclosure.Complex.IsNear.im_isNear qz237 Bool.false 5 2 0 1 Bool.false 134395 1000 0 1 qz514)

noncomputable def ep1571 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz238 26879 100 0 1 5 2 0 1 26879 40

noncomputable def ep1572 := @ep1571 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 722450641 40000 0 1 Bool.false 26879 100 0 1 qz243)

noncomputable def ep1573 := ep1572 (@Enclosure.Complex.IsNear.re_isNear qz237 Bool.false 5 2 0 1 Bool.false 134395 1000 0 1 qz514)

noncomputable abbrev qz244 := (ep1540 (BSN.ascPochhammer_succ_eval_c 2 3 qz273 rfl) (ep1566 (@ep1567 776534999177560 19413374979439 8000000 0 1 (ep1570 rfl) (ep1573 rfl) rfl rfl)))

noncomputable def ep1574 := @ep1538 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1539) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 6502175769 80000 0 1 Bool.true 19413374979439 8000000 0 1 qz244)

noncomputable def ep1575 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 19413374979439 8000000 0 1 0 1 0

noncomputable def ep1576 := @ep1575 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1539) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 6502175769 80000 0 1 Bool.true 19413374979439 8000000 0 1 qz244)

noncomputable def ep1577 := @Enclosure.Real.IsNear.addLit_ft_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) 19413374979439 5760000000 0 1 0 1 0 1 19413374979439

noncomputable def ep1578 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 19413374979439 8000000 0 1 19413374979439 5760000000 0

noncomputable def ep1579 := @ep1578 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1539) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 6502175769 80000 0 1 Bool.true 19413374979439 8000000 0 1 qz244)

noncomputable def ep1580 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 6502175769 80000 0 1 0 1 0

noncomputable def ep1581 := @ep1580 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1539) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 6502175769 80000 0 1 Bool.true 19413374979439 8000000 0 1 qz244)

noncomputable def ep1582 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.false 2167391923 19200000 0 1 Bool.false 19413374979439 5760000000 0 1 (@ep1537 2167391923 19200000 0 1 (ep1574 rfl) (ep1576 rfl) rfl rfl) (@ep1577 19413374979439 5760000000 0 1 (ep1579 rfl) (ep1581 rfl) rfl rfl)

noncomputable def ep1583 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 2167391923 19200000 0 1 Bool.false 19413374979439 5760000000 0 1 ep1582

noncomputable def ep1584 := nat_lit 1208925819614629174706176

noncomputable def ep1585 := nat_lit 19730380281312195055047090762678272

noncomputable def ep1586 := @Enclosure.Complex.IsNear.re_isNear qz226 Bool.true 2368857917501397355 604462909807314587353088 8080807521702236461053 ep1535 Bool.true 2319438480272802845 ep1584 7935053924773766465157 ep1585

noncomputable abbrev qz515 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 52523350144)))

noncomputable def ep1587 := @Enclosure.Complex.IsNear.of_eq qz226 (Complex.mk (@HMul.hMul Real Real Real qz0 qz515 (Real.cos qz135)) (@HMul.hMul Real Real Real qz0 qz515 qz643)) Bool.true 2368857917501397355 604462909807314587353088 8080807521702236461053 ep1535 Bool.true 2319438480272802845 ep1584 7935053924773766465157

noncomputable abbrev qz516 := (Real.sqrt (@Nat.cast Real Real.instNatCast 52523350144))

noncomputable abbrev qz517 := (@Nat.cast Real Real.instNatCast 52523350144)

noncomputable def ep1588 := @Enclosure.Real.IsNear.inv_image qz516 251985781586464421 1099511627776 1 1099511627776 2398797 2398798 549755813888 (@Enclosure.Real.IsNear.of_eq qz516 (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz517 qz14)) Bool.false 251985781586464421 1099511627776 1 1099511627776 (BSN.sqrt_natCast_div_one 52523350144) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz517 qz14)) Bool.false 251985781586464421 1099511627776 1 1099511627776 251985781586464421 1099511627776 1 1099511627776 (BSN.sqrt_enclosure 52523350144 1 125992890793232210 125992890793232211 549755813888 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep1589 := nat_lit 652823521880000000000000000

noncomputable def ep1590 := nat_lit 3264117609400000000000000

noncomputable def ep1591 := nat_lit 69846766182031428999891124224

noncomputable def ep1592 := nat_lit 261129408752000000000000000

noncomputable def ep1593 := BSN.log_dyadic_bound 2 66 4 3 8678664751680 549755813888 261129408752 2657927616 960 33328738308 68 64 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 2) (BSN.artanhQ 66) 0 3 2657927616 8678664751680 960 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep1594 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz137 134395 1000 0 1 15881315944632531 4503599627370496 12516320588047 ep1590 426873891275777800749 900719925474099200 336426181086115313 ep1589 qz18 (BSN.isNear_log_sfrac 34 1 15881315944632531 4503599627370496 12516320588047 ep1590 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz436) Bool.false ep1591 ep1459 1001305647043760 ep1592 15881315944632531 4503599627370496 12516320588047 ep1590 (BSN.log_rat_reduce_isNear 34 1 5 68 64 33328738308 549755813888 24973259072661432 36028797018963968 261129408752 1000000000000000 rfl rfl rfl rfl (ep1593 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1595 := nat_lit 44190630322832227223958716416

noncomputable def ep1596 := nat_lit 39614081257132168796771975168

noncomputable def ep1597 := nat_lit 1366473480156877520560434627386473959222572799332134238565904305797750428409878187854105230261546261041095926551122289080188432762396285577244490032287305433115737907273410260468678776351358976

noncomputable def ep1598 := nat_lit 105837034526088297993462992180381389879322393587938448256862118304383601140722304680429244037940156116138104563485128823993096599821236196995637140025443129138277048165837662434864861216033996800

noncomputable def ep1599 := nat_lit 63113845819722983328389535891318938613418131660410640366809424432228232728800249662742968415898767924313233759375367624938968758726914871671754225218288725500983263835391242969207013376

noncomputable def ep1600 := nat_lit 6830205397036939842468492625056669534183545357137008820057620913733027412302781336044324852140166003365060461220463070377320837047874452416088942399607671094427147463759057574500442425561972736

noncomputable def ep1601 := nat_lit 3704296208413090429771204726313348645776283775577845688990174140653426039925280663815023541327905464064833659721979508839758380993743266894847299900890509519839696685804318185220270142561189888000

noncomputable def ep1602 := BSN.sin_dyadic_bound_f 2511946509163876 2251799813685248 4 3 1099511627776 522768835881 ep1597 ep1598 ep1599 ep1600 ep1601 ep1599 987518920418 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 2511946509163876) (BSN.sinEvenQ 2251799813685248) 0 3 ep1597 ep1598 ep1599 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 2511946509163876) (BSN.sinOddQ 2251799813685248) 0 3 ep1600 ep1601 ep1599 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz518 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 130271573265313) (@Nat.cast Real Real.instNatCast 274877906944))

noncomputable def ep1603 := @Enclosure.Real.IsNear.cos_image qz135 qz518 Bool.false 130271573265313 274877906944 567 1099511627776 Bool.true 987518920418 1099511627776 1 261129408752 (@Enclosure.Real.IsNear.recentre' qz135 Bool.false 426873891275777800749 900719925474099200 336426181086115313 ep1589 130271573265313 274877906944 567 1099511627776 (ep1594 rfl) rfl) (Enclosure.sfrac_false_div 130271573265313 274877906944) (BSN.cos_reduce1 qz518 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep1595) (@Nat.cast Real Real.instNatCast ep1596)) 226375608064910080 72057594037927936 Bool.false 987518920418 1099511627776 75 1000000000000000 522258817504 261129408752 (BSN.sin_reduce_arg_pos_rat_q1 130271573265313 274877906944 226375608064910080 72057594037927936 75 ep1595 ep1596 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 987518920418 1099511627776 ep1595 ep1596 2511946509163876 2251799813685248 522768835881 522258817504 (ep1602 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1604 := nat_lit 525781958937751309147878345483318620270012450030870145605404602422113589213666191045191660477739152905535004061782259150920054165993385309052636487551396406597422949152997277154580500217593856

noncomputable def ep1605 := nat_lit 8141310348160638307189460936952414606101722583687572942835547561875661626209408052340711079841550470472161889498856063384084353832402784384279780001957163779867465243525974033451143170464153600

noncomputable def ep1606 := nat_lit 3187785272098610121398547989694344851163400959725167278863279305243408309341510333345753422595852971643055790241913164023064750332323735403917315992368586698980219996883918216480144450146795520

noncomputable def ep1607 := nat_lit 740859241682618085954240945262669729155256755115569137798034828130685207985056132763004708265581092812966731944395901767951676198748653378969459980178101903967939337160863637044054028512237977600

noncomputable def ep1608 := BSN.cos_dyadic_bound_f 2511946509163876 2251799813685248 4 3 1099511627776 522768835881 ep1604 ep1605 ep1599 ep1606 ep1607 ep1599 483458582951 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 2511946509163876) (BSN.cosEvenQ 2251799813685248) 0 3 ep1604 ep1605 ep1599 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 2511946509163876) (BSN.cosOddQ 2251799813685248) 0 3 ep1606 ep1607 ep1599 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1609 := @Enclosure.Real.IsNear.sin_image qz135 qz518 Bool.false 130271573265313 274877906944 567 1099511627776 Bool.false 483458582951 1099511627776 1 261129408752 (@Enclosure.Real.IsNear.recentre' qz135 Bool.false 426873891275777800749 900719925474099200 336426181086115313 ep1589 130271573265313 274877906944 567 1099511627776 (ep1594 rfl) rfl) (Enclosure.sfrac_false_div 130271573265313 274877906944) (BSN.sin_reduce1 qz518 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep1595) (@Nat.cast Real Real.instNatCast ep1596)) 226375608064910080 72057594037927936 Bool.false 483458582951 1099511627776 75 1000000000000000 522258817504 261129408752 (BSN.sin_reduce_arg_pos_rat_q1 130271573265313 274877906944 226375608064910080 72057594037927936 75 ep1595 ep1596 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 483458582951 1099511627776 ep1595 ep1596 2511946509163876 2251799813685248 522768835881 522258817504 (ep1608 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1610 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz515 (Real.cos qz135)) (@HMul.hMul Real Real Real qz0 qz515 qz643) Bool.true 2368857917501397355 604462909807314587353088 8080807521702236461053 ep1535 Bool.true 2319438480272802845 ep1584 7935053924773766465157 ep1585 (@Enclosure.Real.IsNear.mulLit_ft qz515 (Real.cos qz135) 4797595 1099511627776 1 1099511627776 493759460209 549755813888 9322492899385 17944676329818498793472 2368857917501397355 604462909807314587353088 8080807521702236461053 ep1535 (@Enclosure.Real.IsNear.recentre' qz515 Bool.false 4797595 1099511627776 1 1099511627776 4797595 1099511627776 1 1099511627776 (ep1588 rfl rfl) rfl) (@Enclosure.Real.IsNear.recentre' (Real.cos qz135) Bool.true 987518920418 1099511627776 149159886390160 287114821277095980695552 493759460209 549755813888 9322492899385 17944676329818498793472 (ep1603 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz515 qz643 4797595 1099511627776 1 1099511627776 483458582951 1099511627776 9322492899385 17944676329818498793472 2319438480272802845 ep1584 7935053924773766465157 ep1585 (@Enclosure.Real.IsNear.recentre' qz515 Bool.false 4797595 1099511627776 1 1099511627776 4797595 1099511627776 1 1099511627776 (ep1588 rfl rfl) rfl) (@Enclosure.Real.IsNear.neg qz136 Bool.false 483458582951 1099511627776 9322492899385 17944676329818498793472 (@Enclosure.Real.IsNear.recentre' qz136 Bool.false 483458582951 1099511627776 149159886390160 287114821277095980695552 483458582951 1099511627776 9322492899385 17944676329818498793472 (ep1609 rfl rfl) rfl)) rfl)

noncomputable def ep1611 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz236 19413374979439 5760000000 0 1 2319438480272802845 ep1584 7935053924773766465157 ep1585 ep1531

noncomputable def ep1612 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 2167391923 19200000 0 1 Bool.false 19413374979439 5760000000 0 1 ep1582

noncomputable def ep1613 := @Enclosure.Complex.IsNear.im_isNear qz226 Bool.true 2368857917501397355 604462909807314587353088 8080807521702236461053 ep1535 Bool.true 2319438480272802845 ep1584 7935053924773766465157 ep1585

noncomputable def ep1614 := nat_lit 1005426445607733544564884187

noncomputable def ep1615 := nat_lit 4642275147320176030871715840000

noncomputable def ep1616 := nat_lit 5732790595041370346289847575637

noncomputable def ep1617 := nat_lit 126274433800398048352301380881140940800000

noncomputable def ep1618 := nat_lit 9197505405093520446975378796769

noncomputable def ep1619 := nat_lit 52291915518492223767791699999763089

noncomputable def ep1620 := @Enclosure.Real.IsNear.addLit_tt (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz236) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz235) ep1614 ep1615 ep1616 ep1617 ep1618 ep1522 ep1619

noncomputable def ep1621 := nat_lit 43397470689544124285297116616558209287335991993749691432960000

noncomputable def ep1622 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz236 2167391923 19200000 0 1 2319438480272802845 ep1584 7935053924773766465157 ep1585 ep1614

noncomputable def ep1623 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz235 19413374979439 5760000000 0 1 2368857917501397355 604462909807314587353088 8080807521702236461053 ep1535 ep1618

noncomputable abbrev qz519 := (@ep1587 ep1585 (BSN.cpow_neg_s_sub_mk qz12 134395 1000 34 3 52523350144 qz13 rfl EMRow46.d22) ep1610)

noncomputable def ep1624 := ep1526 (@ep1533 ep1519 ep1534 ep1516 ep1517 ep1518 ep1519 (@ep1536 ep1528 ep1529 ep1530 ep1583 (ep1586 qz519) rfl) (@ep1611 ep1517 ep1532 ep1519 ep1612 (ep1613 qz519) rfl) rfl rfl) (@ep1620 ep1525 ep1621 ep1521 ep1522 ep1523 ep1525 (@ep1622 ep1615 ep1616 ep1617 ep1583 (ep1613 qz519) rfl) (@ep1623 ep1522 ep1619 ep1525 ep1612 (ep1586 qz519) rfl) rfl rfl)

noncomputable def ep1625 := @Enclosure.Real.IsNear.mulLit_tt (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz226)) (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz226)) ep1521 ep1522 ep1523 ep1525 ep1521 ep1522 ep1523

noncomputable def ep1626 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz226) Bool.false ep1516 ep1517 ep1518 ep1519 Bool.true ep1521 ep1522 ep1523

noncomputable def ep1627 := @ep1486 285092544980445871 504403158265495552 63133341113 504403158265495552 (@ep1487 1 3670016 (ep1488 (@ep1489 1048576 1 1048576 (ep1490 (@ep1491 2891882564 722970641 40000 0 1 (ep1495 rfl) (ep1498 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) (Enclosure.Real.IsNear.const Bool.false 2 7) rfl) (@ep1499 867 274877906944 (BSN.norm_eq_sqrt_mul_add (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz226)) (@ep1500 3468 1099511627776 2022346721 137438953472 867 274877906944 (@ep1505 8089385150 8089388618 549755813888 (@ep1511 ep1512 ep1513 ep1514 ep1515 ep1501 ep1502 ep1503 ep1504 (@ep1520 ep1519 ep1506 ep1507 ep1508 ep1509 (@ep1524 ep1525 ep1624) (@ep1524 ep1525 ep1624) rfl) (@ep1625 ep1525 ep1510 ep1512 ep1513 ep1514 (@ep1626 ep1525 ep1624) (@ep1626 ep1525 ep1624) rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl

theorem EMRow46.d23 : Enclosure.Real.IsNear (@HAdd.hAdd Real Real Real qz418 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 34))) (@HMul.hMul Real Real Real qz0 qz223 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz226)))) Bool.false 2615090167368335399 4539628424389459968 456758301361025 4539628424389459968 := ep1484 (ep1485 ep1627) rfl rfl

theorem EMRow46.d24 : @Eq Nat (Nat.pow 35 (Nat.succ (Nat.mul 2 3))) 64339296875 := @Eq.refl Nat 64339296875

noncomputable abbrev qz689 := (@HAdd.hAdd Complex Complex Complex qz691 qz697 (@Nat.cast Complex Complex.instNatCast 3))

noncomputable abbrev qz520 := qz689

noncomputable abbrev qz245 := (@HDiv.hDiv Real Real Real qz272 (@Norm.norm Complex Complex.instNorm qz520) (@HAdd.hAdd Real Real Real qz418 (Complex.re qz439) qz291))

noncomputable abbrev qz521 := (@HPow.hPow Complex Complex Complex qz539 (@Nat.cast Complex Complex.instNatCast 35) (@HSub.hSub Complex Complex Complex qz628 qz646 qz546))

noncomputable abbrev qz246 := qz521

noncomputable def ep1628 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz143 1 35))) (@HMul.hMul Real Real Real qz0 qz245 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz246))) 140041464767 1855425871872 190489273 1855425871872 2189103603938838799 4035225266123964416 39007057463

noncomputable def ep1629 := nat_lit 4626818319889164713415462092800

noncomputable def ep1630 := @Enclosure.Real.IsNear.mulLit_ff (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz143 1 35)) 26561 1769472 1 1769472 5272447 1048576 6973 1048576 140041464767 1855425871872

noncomputable def ep1631 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (zetaApproximant qz143 1 35)) (Real.sqrt (@HAdd.hAdd Real Real Real qz418 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz143 1 35)) (Complex.re (zetaApproximant qz143 1 35))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz143 1 35)) (Complex.im (zetaApproximant qz143 1 35))))) Bool.false 5272447 1048576 6973 1048576

noncomputable def ep1632 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz418 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz143 1 35)) (Complex.re (zetaApproximant qz143 1 35))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz143 1 35)) (Complex.im (zetaApproximant qz143 1 35))))) Bool.false 5272447 1048576 6973 1048576

noncomputable def ep1633 := nat_lit 6273439928272575742696398687651154769622626261

noncomputable def ep1634 := nat_lit 248130549269785036103778101609732505600000000

noncomputable def ep1635 := nat_lit 2948583283163284620606431957027261797651357065526274675447747923

noncomputable def ep1636 := nat_lit 44096332004541566387708414384477284821028972058850518630400000000

noncomputable def ep1637 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz418 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz143 1 35)) (Complex.re (zetaApproximant qz143 1 35))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz143 1 35)) (Complex.im (zetaApproximant qz143 1 35)))) ep1633 ep1634 ep1635 ep1636 2632737 2639710

noncomputable def ep1638 := nat_lit 23834766214167842077336346473834998443578743714004441

noncomputable def ep1639 := nat_lit 942727427523122378060987695692242085967036416000000

noncomputable def ep1640 := nat_lit 230101918525004176563077355155894477450086663897161327698659

noncomputable def ep1641 := nat_lit 3447989053447616419400141870707427071782701701372313600000000

noncomputable def ep1642 := nat_lit 351510666652936592872360648551641180867978747929

noncomputable def ep1643 := nat_lit 8019729852193228563366041161270809411872358400000000

noncomputable def ep1644 := nat_lit 1452461786751551635308915484631831385549680236369613877399493

noncomputable def ep1645 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz143 1 35)) (Complex.re (zetaApproximant qz143 1 35))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz143 1 35)) (Complex.im (zetaApproximant qz143 1 35))) ep1638 ep1639 ep1640 ep1641 ep1642 ep1643 ep1644

noncomputable def ep1646 := nat_lit 11024083001135391596927103596119321205257243014712629657600000000

noncomputable def ep1647 := nat_lit 191148717506554946740477144324306703774142957061210447237877156941782295868478660897282749171236864000000

noncomputable def ep1648 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (zetaApproximant qz143 1 35)) (Complex.re (zetaApproximant qz143 1 35)) ep1204 ep1205 ep1206 ep1207 ep1204 ep1205 ep1206 ep1207 ep1638

noncomputable def ep1649 := @Enclosure.Real.IsNear.mulLit_tt (Complex.im (zetaApproximant qz143 1 35)) (Complex.im (zetaApproximant qz143 1 35)) 592883349954218728583173 ep1326 ep1327 ep1328 592883349954218728583173 ep1326 ep1327 ep1328 ep1642

noncomputable def ep1650 := @ep1628 576460752303423488 ep1629 67329067968081867925 108951082185347039232 1598993029953485 15564440312192434176 (@ep1630 190489273 1855425871872 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaStirlingErrorBound 1 2) (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 96 162) qz502) Bool.false 26561 1769472 1 1769472 (BSN.theta_err_eq 1 2 96 162 EMRow46.d19 EMRow46.d20 rfl) (ep1465 rfl)) (ep1631 (BSN.norm_eq_sqrt_mul_add (zetaApproximant qz143 1 35)) (@ep1632 5272447 1048576 6973 1048576 (@ep1637 524288 (@ep1645 ep1646 ep1647 ep1633 ep1634 ep1635 ep1636 (@ep1648 ep1639 ep1640 ep1641 ep1447 ep1447 rfl) (@ep1649 ep1643 ep1644 ep1646 ep1453 ep1453 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl)

noncomputable abbrev qz247 := (@Norm.norm Complex Complex.instNorm qz520)

noncomputable def ep1651 := @Enclosure.Real.IsNear.of_eq (@HMul.hMul Real Real Real qz0 qz245 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz246))) (@HMul.hMul Real Real Real qz0 (@HMul.hMul Real Real Real qz0 qz247 qz688) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz246))) Bool.false 2189103603938838799 4035225266123964416 39007057463 576460752303423488 (BSN.zrb_shape_eq qz247 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz246)) qz146 3)

noncomputable def ep1652 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz0 qz247 qz688) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz246)) 143116871 3670016 1 3670016 15295915769 1099511627776 1801 1099511627776

noncomputable def ep1653 := @Enclosure.Real.IsNear.mulLit_ff qz247 qz688 143116871 1048576 1 1048576 2 7 0 1 143116871 3670016

noncomputable abbrev qz522 := (Complex.re qz689)

noncomputable abbrev qz523 := (Complex.im qz689)

noncomputable abbrev qz248 := (@HAdd.hAdd Real Real Real qz418 (@HMul.hMul Real Real Real qz269 qz522 qz522) (@HMul.hMul Real Real Real qz269 qz523 qz523))

noncomputable abbrev qz249 := qz520

noncomputable def ep1654 := @Enclosure.Real.IsNear.of_eq qz247 (Real.sqrt qz248) Bool.false 143116871 1048576 1 1048576 (BSN.norm_eq_sqrt_mul_add qz249)

noncomputable def ep1655 := @Enclosure.Real.IsNear.recentre' (Real.sqrt qz248) Bool.false 143116871 1048576 1 1048576 143116871

noncomputable def ep1656 := @Enclosure.Real.IsNear.sqrt_image qz248 4657167341 250000 0 1 71558435 71558436 524288

noncomputable abbrev qz250 := (@HMul.hMul Real Real Real qz269 qz522 qz522)

noncomputable abbrev qz251 := (@HMul.hMul Real Real Real qz269 qz523 qz523)

noncomputable def ep1657 := @Enclosure.Real.IsNear.addLit_ff qz250 qz251 49 4 0 1 4654104841 250000 0 1

noncomputable abbrev qz252 := qz522

noncomputable def ep1658 := @Enclosure.Real.IsNear.mulLit_ff qz252 qz252 7 2 0 1 7 2 0 1 49 4

noncomputable def ep1659 := @Enclosure.Complex.IsNear.of_eq qz249 (Complex.mk qz507 qz146) Bool.false 7 2 0 1 Bool.false 136442 1000 0 1 (BSN.s_add_nat_mk qz146 Bool.false 136442 1000 3 qz147)

noncomputable abbrev qz524 := (ep1659 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7 2) qz146 Bool.false 7 2 0 1 Bool.false 136442 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 7 2) qz148))

noncomputable def ep1660 := @ep1658 0 1 (@Enclosure.Complex.IsNear.re_isNear qz249 Bool.false 7 2 0 1 Bool.false 136442 1000 0 1 qz524)

noncomputable def ep1661 := ep1660 (@Enclosure.Complex.IsNear.re_isNear qz249 Bool.false 7 2 0 1 Bool.false 136442 1000 0 1 qz524)

noncomputable abbrev qz253 := qz523

noncomputable def ep1662 := @Enclosure.Real.IsNear.mulLit_ff qz253 qz253 136442 1000 0 1 136442 1000 0 1 4654104841 250000

noncomputable def ep1663 := @ep1662 0 1 (@Enclosure.Complex.IsNear.im_isNear qz249 Bool.false 7 2 0 1 Bool.false 136442 1000 0 1 qz524)

noncomputable def ep1664 := ep1663 (@Enclosure.Complex.IsNear.im_isNear qz249 Bool.false 7 2 0 1 Bool.false 136442 1000 0 1 qz524)

noncomputable def ep1665 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz246)) (Real.sqrt (@HAdd.hAdd Real Real Real qz418 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz246)) (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz246))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz246)) (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz246))))) Bool.false 15295915769 1099511627776

noncomputable def ep1666 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz418 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz246)) (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz246))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz246)) (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz246))))) Bool.false 30591831538 2199023255552

noncomputable def ep1667 := nat_lit 18328445216175813446352329316961532789363516738568255999459641449273

noncomputable def ep1668 := nat_lit 94705306099042509099598777160015139673704428784844800000000000000000000

noncomputable def ep1669 := nat_lit 371001697523699191420894653176904174029161477207156807697051806127192649432413575019

noncomputable def ep1670 := nat_lit 8143271252803264684151565385495705595993158665483063636116027473920000000000000000000000000000

noncomputable def ep1671 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz418 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz246)) (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz246))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz246)) (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz246)))) ep1667 ep1668 ep1669 ep1670

noncomputable def ep1672 := nat_lit 34512531818446265563234386747024264432335480667282250971721796089321

noncomputable def ep1673 := nat_lit 189410612198085018199197554320030279347408857569689600000000000000000000

noncomputable def ep1674 := nat_lit 687572457598327082123307869096783407807273592100327115809401545795792804323312505019

noncomputable def ep1675 := nat_lit 16286542505606529368303130770991411191986317330966127272232054947840000000000000000000000000000

noncomputable def ep1676 := nat_lit 85774344556214453178810875475952045855662112394170441087899472369

noncomputable def ep1677 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz246)) (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz246))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz246)) (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz246))) ep1672 ep1673 ep1674 ep1675 ep1676

noncomputable def ep1678 := nat_lit 7576424487923400727967902172801211173896354302787584000000000000000000

noncomputable def ep1679 := nat_lit 54430937449071300718481437257024940251049362313986499584702066458592494541514645019

noncomputable def ep1680 := nat_lit 277728162322793882294448417822995984655502643985817376475168912105417781616082652494595305530937881897481581147260452864000000000000000000

noncomputable def ep1681 := nat_lit 5874736744607903327256296226278611

noncomputable def ep1682 := nat_lit 435213295061266502894223360000000000

noncomputable def ep1683 := nat_lit 199566548440155374559660522930441453613

noncomputable def ep1684 := nat_lit 127618738849772878361284163351347200000000000000

noncomputable def ep1685 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz246)) (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz246)) ep1681 ep1682 ep1683 ep1684 ep1681 ep1682 ep1683

noncomputable def ep1686 := nat_lit 292872573922882804951316154485287

noncomputable def ep1687 := nat_lit 87042659012253300578844672000000000

noncomputable def ep1688 := nat_lit 63380371926430708697482813438707051113

noncomputable def ep1689 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz246) Bool.false ep1681 ep1682 ep1683 ep1684 Bool.false ep1686 ep1687 ep1688

noncomputable def ep1690 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz246 Bool.false ep1681 ep1682 ep1683 ep1684 Bool.false ep1686 ep1687 ep1688 ep1684

noncomputable def ep1691 := nat_lit 14571864556034280639788016191

noncomputable def ep1692 := nat_lit 116056878683004400771792896000000

noncomputable def ep1693 := nat_lit 2501051702064968419784063223057109

noncomputable def ep1694 := nat_lit 170158318466363837815045551135129600000000000

noncomputable def ep1695 := nat_lit 5820092252522774774857091165562361

noncomputable def ep1696 := nat_lit 28241537094800949749260353644735517409

noncomputable abbrev qz254 := (Complex.re qz521)

noncomputable abbrev qz255 := (Complex.im qz521)

noncomputable def ep1697 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3)))) qz254) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3)))) qz255) ep1691 ep1692 ep1693 ep1694 ep1695 ep1682 ep1696

noncomputable def ep1698 := nat_lit 18231248407110411194469166193049600000000000000

noncomputable def ep1699 := nat_lit 681803609663547644230132378514313494519317537601840486547456000000

noncomputable def ep1700 := nat_lit 4835703278458516698824704

noncomputable def ep1701 := nat_lit 1417985987219698648458712926126080000

noncomputable def ep1702 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3)))) qz254 13962002023 120000000 0 1 5218400818174083085 ep1700 179132741704586158960483 ep1701 ep1691

noncomputable def ep1703 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3)))) 13962002023 120000000 0 1 0 1 0 1 13962002023

noncomputable def ep1704 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 41886006069 500000 0 1 13962002023 120000000 0

noncomputable abbrev qz525 := (@HAdd.hAdd Complex Complex Complex qz538 qz645 qz547)

noncomputable abbrev qz256 := qz525

noncomputable def ep1705 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3)) (@HMul.hMul Complex Complex Complex qz80 (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 2)) qz256) Bool.true 41886006069 500000 0 1 Bool.true 317409618670361 125000000 0 1

noncomputable abbrev qz257 := (Complex.re qz525)

noncomputable abbrev qz258 := (Complex.im qz525)

noncomputable def ep1706 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 2))) qz257) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 2))) qz258) 4653917341 100000 0 1 4654104841 125000 0 1

noncomputable def ep1707 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 2))) qz257 4653917341 250000 0 1 5 2 0 1 4653917341 100000

noncomputable abbrev qz526 := (@HAdd.hAdd Complex Complex Complex qz538 qz645 (@Nat.cast Complex Complex.instNatCast 1))

noncomputable abbrev qz259 := qz526

noncomputable def ep1708 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 2)) (@HMul.hMul Complex Complex Complex qz80 (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1)) qz259) Bool.true 4653917341 250000 0 1 Bool.false 68221 250 0 1

noncomputable abbrev qz260 := (Complex.re qz526)

noncomputable abbrev qz261 := (Complex.im qz526)

noncomputable def ep1709 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1))) qz260) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1))) qz261) 3 4 0 1 4654104841 250000 0 1

noncomputable def ep1710 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1))) qz260 1 2 0 1 3 2 0 1 3 4

noncomputable def ep1711 := @ep1710 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 136442 1000 0 1 ep1408)

noncomputable def ep1712 := @Enclosure.Complex.IsNear.of_eq qz259 (Complex.mk qz511 qz146) Bool.false 3 2 0 1 Bool.false 136442 1000 0 1 (BSN.s_add_nat_mk qz146 Bool.false 136442 1000 1 qz147)

noncomputable abbrev qz527 := (ep1712 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 3 2) qz146 Bool.false 3 2 0 1 Bool.false 136442 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 3 2) qz148))

noncomputable def ep1713 := ep1711 (@Enclosure.Complex.IsNear.re_isNear qz259 Bool.false 3 2 0 1 Bool.false 136442 1000 0 1 qz527)

noncomputable def ep1714 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1))) qz261 136442 1000 0 1 136442 1000 0 1 4654104841 250000

noncomputable def ep1715 := @ep1714 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 136442 1000 0 1 ep1408)

noncomputable def ep1716 := ep1715 (@Enclosure.Complex.IsNear.im_isNear qz259 Bool.false 3 2 0 1 Bool.false 136442 1000 0 1 qz527)

noncomputable def ep1717 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1)) qz259 Bool.true 4653917341 250000 0 1 Bool.false 68221 250 0 1 (@ep1709 18615669364 4653917341 250000 0 1 (ep1713 rfl) (ep1716 rfl) rfl rfl)

noncomputable def ep1718 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1))) qz261) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1))) qz260) 68221 1000 0 1 204663 1000 0 1

noncomputable def ep1719 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1))) qz261 1 2 0 1 136442 1000 0 1 68221 1000

noncomputable def ep1720 := @ep1719 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 136442 1000 0 1 ep1408)

noncomputable def ep1721 := ep1720 (@Enclosure.Complex.IsNear.im_isNear qz259 Bool.false 3 2 0 1 Bool.false 136442 1000 0 1 qz527)

noncomputable def ep1722 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1))) qz260 136442 1000 0 1 3 2 0 1 204663 1000

noncomputable def ep1723 := @ep1722 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 136442 1000 0 1 ep1408)

noncomputable def ep1724 := ep1723 (@Enclosure.Complex.IsNear.re_isNear qz259 Bool.false 3 2 0 1 Bool.false 136442 1000 0 1 qz527)

noncomputable abbrev qz262 := (ep1708 (BSN.ascPochhammer_succ_eval_c 1 2 qz439 rfl) (ep1717 (@ep1718 272884000 68221 250 0 1 (ep1721 rfl) (ep1724 rfl) rfl rfl)))

noncomputable def ep1725 := @ep1707 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 4653917341 250000 0 1 Bool.false 68221 250 0 1 qz262)

noncomputable def ep1726 := @Enclosure.Complex.IsNear.of_eq qz256 (Complex.mk qz513 qz146) Bool.false 5 2 0 1 Bool.false 136442 1000 0 1 (BSN.s_add_nat_mk qz146 Bool.false 136442 1000 2 qz147)

noncomputable abbrev qz528 := (ep1726 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 5 2) qz146 Bool.false 5 2 0 1 Bool.false 136442 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 5 2) qz148))

noncomputable def ep1727 := ep1725 (@Enclosure.Complex.IsNear.re_isNear qz256 Bool.false 5 2 0 1 Bool.false 136442 1000 0 1 qz528)

noncomputable def ep1728 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 2))) qz258 68221 250 0 1 136442 1000 0 1 4654104841 125000

noncomputable def ep1729 := @ep1728 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 4653917341 250000 0 1 Bool.false 68221 250 0 1 qz262)

noncomputable def ep1730 := ep1729 (@Enclosure.Complex.IsNear.im_isNear qz256 Bool.false 5 2 0 1 Bool.false 136442 1000 0 1 qz528)

noncomputable def ep1731 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 2)) qz256 Bool.true 41886006069 500000 0 1 Bool.true 317409618670361 125000000 0 1 (@ep1706 1047150151725000 41886006069 500000 0 1 (ep1727 rfl) (ep1730 rfl) rfl rfl)

noncomputable def ep1732 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 2))) qz258) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 2))) qz257) 317494894920361 125000000 0 1 68221 100 0 1

noncomputable def ep1733 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 2))) qz258 4653917341 250000 0 1 136442 1000 0 1 317494894920361 125000000

noncomputable def ep1734 := @ep1733 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 4653917341 250000 0 1 Bool.false 68221 250 0 1 qz262)

noncomputable def ep1735 := ep1734 (@Enclosure.Complex.IsNear.im_isNear qz256 Bool.false 5 2 0 1 Bool.false 136442 1000 0 1 qz528)

noncomputable def ep1736 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 2))) qz257 68221 250 0 1 5 2 0 1 68221 100

noncomputable def ep1737 := @ep1736 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 4653917341 250000 0 1 Bool.false 68221 250 0 1 qz262)

noncomputable def ep1738 := ep1737 (@Enclosure.Complex.IsNear.re_isNear qz256 Bool.false 5 2 0 1 Bool.false 136442 1000 0 1 qz528)

noncomputable abbrev qz263 := (ep1705 (BSN.ascPochhammer_succ_eval_c 2 3 qz439 rfl) (ep1731 (@ep1732 31740961867036100 317409618670361 125000000 0 1 (ep1735 rfl) (ep1738 rfl) rfl rfl)))

noncomputable def ep1739 := @ep1704 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1539) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 41886006069 500000 0 1 Bool.true 317409618670361 125000000 0 1 qz263)

noncomputable def ep1740 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 317409618670361 125000000 0 1 0 1 0

noncomputable def ep1741 := @ep1740 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1539) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 41886006069 500000 0 1 Bool.true 317409618670361 125000000 0 1 qz263)

noncomputable def ep1742 := @Enclosure.Real.IsNear.addLit_ft_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3)))) 317409618670361 90000000000 0 1 0 1 0 1 317409618670361

noncomputable def ep1743 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 317409618670361 125000000 0 1 317409618670361 90000000000 0

noncomputable def ep1744 := @ep1743 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1539) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 41886006069 500000 0 1 Bool.true 317409618670361 125000000 0 1 qz263)

noncomputable def ep1745 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 41886006069 500000 0 1 0 1 0

noncomputable def ep1746 := @ep1745 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1539) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 41886006069 500000 0 1 Bool.true 317409618670361 125000000 0 1 qz263)

noncomputable def ep1747 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.false 13962002023 120000000 0 1 Bool.false 317409618670361 90000000000 0 1 (@ep1703 13962002023 120000000 0 1 (ep1739 rfl) (ep1741 rfl) rfl rfl) (@ep1742 317409618670361 90000000000 0 1 (ep1744 rfl) (ep1746 rfl) rfl rfl)

noncomputable def ep1748 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 13962002023 120000000 0 1 Bool.false 317409618670361 90000000000 0 1 ep1747

noncomputable def ep1749 := @Enclosure.Complex.IsNear.re_isNear qz246 Bool.false 5218400818174083085 ep1700 179132741704586158960483 ep1701 Bool.true 18336218911396972001 ep1700 622825358890318244337983 ep1701

noncomputable abbrev qz529 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 64339296875)))

noncomputable def ep1750 := @Enclosure.Complex.IsNear.of_eq qz246 (Complex.mk (@HMul.hMul Real Real Real qz0 qz529 (Real.cos qz218)) (@HMul.hMul Real Real Real qz0 qz529 qz683)) Bool.false 5218400818174083085 ep1700 179132741704586158960483 ep1701 Bool.true 18336218911396972001 ep1700 622825358890318244337983

noncomputable abbrev qz530 := (Real.sqrt (@Nat.cast Real Real.instNatCast 64339296875))

noncomputable abbrev qz531 := (@Nat.cast Real Real.instNatCast 64339296875)

noncomputable def ep1751 := @Enclosure.Real.IsNear.inv_image qz530 557786472435602635 2199023255552 1 2199023255552 4334726 4334727 1099511627776 (@Enclosure.Real.IsNear.of_eq qz530 (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz531 qz14)) Bool.false 557786472435602635 2199023255552 1 2199023255552 (BSN.sqrt_natCast_div_one 64339296875) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz531 qz14)) Bool.false 557786472435602635 2199023255552 1 2199023255552 557786472435602635 2199023255552 1 2199023255552 (BSN.sqrt_enclosure 64339296875 1 278893236217801317 278893236217801318 1099511627776 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep1752 := nat_lit 46917220700000000000000000

noncomputable def ep1753 := nat_lit 140841847005213844967262257152

noncomputable def ep1754 := nat_lit 293232629375000000000000000

noncomputable def ep1755 := BSN.log_dyadic_bound 3 67 5 4 383733955291025745 1099511627776 293232629375 256758449434344 688905 98529610469 70 64 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 3) (BSN.artanhQ 67) 0 4 256758449434344 383733955291025745 688905 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep1756 := @Enclosure.Real.IsNear.mulLit_ff qz146 qz682 136442 1000 0 1 16011864204894419 4503599627370496 320469172207 93834441400000000000000 1092345387922102158599 2251799813685248000 21862727397133747 ep1752 qz148 (BSN.isNear_log_sfrac 35 1 16011864204894419 4503599627370496 320469172207 93834441400000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz684) Bool.false ep1753 ep1596 1001466163146875 ep1754 16011864204894419 4503599627370496 320469172207 93834441400000000000000 (BSN.log_rat_reduce_isNear 35 1 5 70 64 98529610469 1099511627776 24973259072661432 36028797018963968 293232629375 1000000000000000 rfl rfl rfl rfl (ep1755 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1757 := nat_lit 409936512348628799601260888064

noncomputable def ep1758 := nat_lit 316912650057057350374175801344

noncomputable def ep1759 := nat_lit 70015816973452417561666362388504482432259000096172161899992320279118039206033505260561816525426137839325559369109804082491060942955401307124677188769001295939076262241905597785064031243907246740103642693628251094418062041560067035544655214223957663180583606419456

noncomputable def ep1760 := nat_lit 599205769308871494669005633404748773453705986173265619753359186119574540201718521016582654337481038554791270797803930120647421245947038870502085995962344054183037643944802456687515051311778021064186337694386596224481457310393291043136983312363285164951074766848000

noncomputable def ep1761 := nat_lit 1759498179757711521733013466272215048309065434187672718692926056376218315312879884308801686244529339314235351734438182576588376480024731345067629589940934754282003770069800225929243039436623808146274873853122994211719359994666500212499128657565739646976

noncomputable def ep1762 := nat_lit 713368998211694882588744473946406313489663669502632880707607536384813327867765305743571622470625841370476936684334394949346711094880596705756321150850081768753057524880897074027238596030337250132207295355365797268221406107698201407070850234702196094833875983794176

noncomputable def ep1763 := nat_lit 91678482704257338684357861910926562338417015884509639822263955476294904650862933715537146113634598898883064432064001308459055450629896947186819157382238640290004759523554775873189802850702037222820509667241149222345662968490173529599958446791582630237514439327744000

noncomputable def ep1764 := BSN.cos_dyadic_bound_f 5825548219442976 4503599627370496 5 4 2199023255552 587037978730 ep1759 ep1760 ep1761 ep1762 ep1763 ep1761 601929650945 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.cosEvenP 5825548219442976) (BSN.cosEvenQ 4503599627370496) 0 4 ep1759 ep1760 ep1761 rfl rfl rfl rfl) (@BSN.binarySplit_of_base4 (BSN.cosOddP 5825548219442976) (BSN.cosOddQ 4503599627370496) 0 4 ep1762 ep1763 ep1761 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz532 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 1066743542892677) (@Nat.cast Real Real.instNatCast 2199023255552))

noncomputable def ep1765 := @Enclosure.Real.IsNear.cos_image qz218 qz532 Bool.false 1066743542892677 2199023255552 513 1099511627776 Bool.false 601929650945 2199023255552 1 293232629375 (@Enclosure.Real.IsNear.recentre' qz218 Bool.false 1092345387922102158599 2251799813685248000 21862727397133747 ep1752 1066743542892677 2199023255552 513 1099511627776 (ep1756 rfl) rfl) (Enclosure.sfrac_false_div 1066743542892677 2199023255552) (BSN.cos_reduce0 qz532 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep1757) (@Nat.cast Real Real.instNatCast ep1758)) 226375608064910080 72057594037927936 Bool.false 601929650945 2199023255552 77 1000000000000000 586465258750 293232629375 (BSN.sin_reduce_arg_pos_rat_q0 1066743542892677 2199023255552 226375608064910080 72057594037927936 77 ep1757 ep1758 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 601929650945 2199023255552 ep1757 ep1758 5825548219442976 4503599627370496 587037978730 586465258750 (ep1764 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1766 := nat_lit 10123400760876265014931766301066732762789687229695221675471085065208382480804328147937453918771905375220422549575669508766773829087397396307616839846953557588782357296149845126187713718173382475776

noncomputable def ep1767 := nat_lit 433508493418857668581224415970842172945704524136195884060107236574755230272398559971038183579402879451701676292035087663075723672867783462894129725544215056950382789287271065333206471540875250892800

noncomputable def ep1768 := nat_lit 1527712444775599443920393112184186911015851376437924733566700053287095648693468917965469505017156725483035296402614886808917083713430078726943832163577504928142337797675261045444951016472576

noncomputable def ep1769 := nat_lit 50588055128056247598248211182588897578308282391661356797354230854912382082956796269537079029437694728190405809956142176889827738453776992473611362575979236571225976234140202891224187501372648718336

noncomputable def ep1770 := nat_lit 15172797269660018400342854558979476053099658344766855942103753280116433059533949598986336425279100780809558670221228068207650328550372421201294540394047526993263397625054487286662226503930633781248000

noncomputable def ep1771 := BSN.sin_dyadic_bound_f 5825548219442976 4503599627370496 4 3 2199023255552 587037978730 ep1766 ep1767 ep1768 ep1769 ep1770 ep1768 2115037582117 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 5825548219442976) (BSN.sinEvenQ 4503599627370496) 0 3 ep1766 ep1767 ep1768 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 5825548219442976) (BSN.sinOddQ 4503599627370496) 0 3 ep1769 ep1770 ep1768 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1772 := @Enclosure.Real.IsNear.sin_image qz218 qz532 Bool.false 1066743542892677 2199023255552 513 1099511627776 Bool.false 2115037582117 2199023255552 1 293232629375 (@Enclosure.Real.IsNear.recentre' qz218 Bool.false 1092345387922102158599 2251799813685248000 21862727397133747 ep1752 1066743542892677 2199023255552 513 1099511627776 (ep1756 rfl) rfl) (Enclosure.sfrac_false_div 1066743542892677 2199023255552) (BSN.sin_reduce0 qz532 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep1757) (@Nat.cast Real Real.instNatCast ep1758)) 226375608064910080 72057594037927936 Bool.false 2115037582117 2199023255552 77 1000000000000000 586465258750 293232629375 (BSN.sin_reduce_arg_pos_rat_q0 1066743542892677 2199023255552 226375608064910080 72057594037927936 77 ep1757 ep1758 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 2115037582117 2199023255552 ep1757 ep1758 5825548219442976 4503599627370496 587037978730 586465258750 (ep1771 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1773 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz529 (Real.cos qz218)) (@HMul.hMul Real Real Real qz0 qz529 qz683) Bool.false 5218400818174083085 ep1700 179132741704586158960483 ep1701 Bool.true 18336218911396972001 ep1700 622825358890318244337983 ep1701 (@Enclosure.Real.IsNear.mulLit_ff qz529 (Real.cos qz218) 8669453 2199023255552 1 2199023255552 601929650945 2199023255552 151527850497151 322412685641142763520000 5218400818174083085 ep1700 179132741704586158960483 ep1701 (@Enclosure.Real.IsNear.recentre' qz529 Bool.false 8669453 2199023255552 1 2199023255552 8669453 2199023255552 1 2199023255552 (ep1751 rfl rfl) rfl) (@Enclosure.Real.IsNear.recentre' (Real.cos qz218) Bool.false 601929650945 2199023255552 151527850497151 322412685641142763520000 601929650945 2199023255552 151527850497151 322412685641142763520000 (ep1765 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz529 qz683 8669453 2199023255552 1 2199023255552 2115037582117 2199023255552 151527850497151 322412685641142763520000 18336218911396972001 ep1700 622825358890318244337983 ep1701 (@Enclosure.Real.IsNear.recentre' qz529 Bool.false 8669453 2199023255552 1 2199023255552 8669453 2199023255552 1 2199023255552 (ep1751 rfl rfl) rfl) (@Enclosure.Real.IsNear.neg qz219 Bool.false 2115037582117 2199023255552 151527850497151 322412685641142763520000 (@Enclosure.Real.IsNear.recentre' qz219 Bool.false 2115037582117 2199023255552 151527850497151 322412685641142763520000 2115037582117 2199023255552 151527850497151 322412685641142763520000 (ep1772 rfl rfl) rfl)) rfl)

noncomputable def ep1774 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3)))) qz255 317409618670361 90000000000 0 1 18336218911396972001 ep1700 622825358890318244337983 ep1701 ep1695

noncomputable def ep1775 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 13962002023 120000000 0 1 Bool.false 317409618670361 90000000000 0 1 ep1747

noncomputable def ep1776 := @Enclosure.Complex.IsNear.im_isNear qz246 Bool.false 5218400818174083085 ep1700 179132741704586158960483 ep1701 Bool.true 18336218911396972001 ep1700 622825358890318244337983 ep1701

noncomputable def ep1777 := nat_lit 256010325535095380834036358023

noncomputable def ep1778 := nat_lit 580284393415022003858964480000000

noncomputable def ep1779 := nat_lit 8695888920802324362560726941739609

noncomputable def ep1780 := nat_lit 331274122753147112076421608188737

noncomputable def ep1781 := nat_lit 8122636462261280775080324033200334909

noncomputable def ep1782 := @Enclosure.Real.IsNear.addLit_tf_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3)))) qz255) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3)))) qz254) ep1777 ep1778 ep1779 ep1694 ep1780 ep1687 ep1781

noncomputable def ep1783 := nat_lit 169949383906736239786119416667673130802480950722915215605760000000

noncomputable def ep1784 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3)))) qz255 13962002023 120000000 0 1 18336218911396972001 ep1700 622825358890318244337983 ep1701 ep1777

noncomputable def ep1785 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3)))) qz254 317409618670361 90000000000 0 1 5218400818174083085 ep1700 179132741704586158960483 ep1701 ep1780

noncomputable abbrev qz533 := (@ep1750 ep1701 (BSN.cpow_neg_s_sub_mk qz146 136442 1000 35 3 64339296875 qz147 rfl EMRow46.d24) ep1773)

noncomputable def ep1786 := ep1690 (@ep1697 ep1698 ep1699 ep1681 ep1682 ep1683 ep1684 (@ep1702 ep1692 ep1693 ep1694 ep1748 (ep1749 qz533) rfl) (@ep1774 ep1682 ep1696 ep1698 ep1775 (ep1776 qz533) rfl) rfl rfl) (@ep1782 ep1698 ep1783 ep1686 ep1687 ep1688 ep1684 (@ep1784 ep1778 ep1779 ep1694 ep1748 (ep1776 qz533) rfl) (@ep1785 ep1687 ep1781 ep1698 ep1775 (ep1749 qz533) rfl) rfl rfl)

noncomputable def ep1787 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz246)) (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz246)) ep1686 ep1687 ep1688 ep1684 ep1686 ep1687 ep1688

noncomputable def ep1788 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz246) Bool.false ep1681 ep1682 ep1683 ep1684 Bool.false ep1686 ep1687 ep1688

noncomputable def ep1789 := @ep1652 2189103603938838799 4035225266123964416 39007057463 576460752303423488 (@ep1653 1 3670016 (ep1654 (@ep1655 1048576 1 1048576 (ep1656 (@ep1657 18628669364 4657167341 250000 0 1 (ep1661 rfl) (ep1664 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) (Enclosure.Real.IsNear.const Bool.false 2 7) rfl) (@ep1665 1801 1099511627776 (BSN.norm_eq_sqrt_mul_add (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz246)) (@ep1666 3602 2199023255552 15295915769 1099511627776 1801 1099511627776 (@ep1671 15295913968 15295917570 1099511627776 (@ep1677 ep1678 ep1679 ep1675 ep1680 ep1667 ep1668 ep1669 ep1670 (@ep1685 ep1684 ep1672 ep1673 ep1674 ep1675 (@ep1689 ep1684 ep1786) (@ep1689 ep1684 ep1786) rfl) (@ep1787 ep1684 ep1676 ep1678 ep1679 ep1675 (@ep1788 ep1684 ep1786) (@ep1788 ep1684 ep1786) rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl

theorem EMRow46.d25 : Enclosure.Real.IsNear (@HAdd.hAdd Real Real Real qz418 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz143 1 35))) (@HMul.hMul Real Real Real qz0 qz245 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz246)))) Bool.false 67329067968081867925 108951082185347039232 1598993029953485 15564440312192434176 := ep1650 (ep1651 ep1789) rfl rfl

noncomputable def EMRow46.d26 := fun (I J : @NonemptyInterval Real Real.instLE) => @LE.le Real Real.instLE (@Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE I)) (@Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE J))

noncomputable abbrev qz534 := (EMRow46.d3 qz549 qz652 (@Enclosure.dec_le_dec qz549 qz652 134395 1000 136442 1000 (@Eq.refl Real qz549) (@Eq.refl Real qz652) rfl rfl rfl) 34 35 1 1)

noncomputable abbrev qz264 := qz534

noncomputable def ep1790 := @Zeta.Certificates.ZIntervalEM.Certificate.mk qz264 (@Enclosure.dec_nonneg qz12 134395 1000 qz13) (@Enclosure.pos_of_ble 1 rfl) (@Enclosure.pos_of_ble 34 rfl)

noncomputable abbrev qz265 := (Zeta.Certificates.ZIntervalEM.fstVal qz534)

noncomputable def ep1791 := @Enclosure.Real.IsNear.pos_val qz265 ep521 ep522

noncomputable def ep1792 := @Enclosure.Real.IsNear.of_eq qz265 (hardyZApproximantEM 1 34 qz12) Bool.false

noncomputable abbrev qz266 := (Zeta.Certificates.ZIntervalEM.sndVal qz534)

noncomputable def ep1793 := BSN.mul_neg_of_pos_neg_r qz265 qz266 (@ep1791 ep523 ep524 (@ep1792 ep521 ep522 ep523 ep524 (@Eq.refl Real (hardyZApproximantEM 1 34 qz12)) EMRow46.d12) rfl rfl rfl)

noncomputable def ep1794 := @Enclosure.Real.IsNear.neg_val qz266 ep1187 ep1188

noncomputable def ep1795 := @Enclosure.Real.IsNear.of_eq qz266 (hardyZApproximantEM 1 35 qz146) Bool.true

noncomputable def ep1796 := BSN.gt_trans_le (@Norm.norm Real Real.norm qz265) (BSN.hardyZErrorBoundStrong 1 34 qz12)

noncomputable def ep1797 := @Enclosure.norm_gt_of_isNear qz265 (BSN.hardyZErrorBoundStrong 1 34 qz12) Bool.false

noncomputable def ep1798 := @Enclosure.Real.IsNear.of_eq (BSN.hardyZErrorBoundStrong 1 34 qz12) (@HAdd.hAdd Real Real Real qz418 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 34))) (@HMul.hMul Real Real Real qz0 qz223 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz226)))) Bool.false 2615090167368335399 4539628424389459968 456758301361025 4539628424389459968 (@Eq.refl Real (@HAdd.hAdd Real Real Real qz418 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 34))) (@HMul.hMul Real Real Real qz0 qz223 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz226)))))

noncomputable def ep1799 := BSN.gt_trans_le (@Norm.norm Real Real.norm qz266) (BSN.hardyZErrorBoundStrong 1 35 qz146)

noncomputable def ep1800 := @Enclosure.norm_gt_of_isNear qz266 (BSN.hardyZErrorBoundStrong 1 35 qz146) Bool.true

noncomputable def ep1801 := @Enclosure.Real.IsNear.of_eq (BSN.hardyZErrorBoundStrong 1 35 qz146) (@HAdd.hAdd Real Real Real qz418 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz143 1 35))) (@HMul.hMul Real Real Real qz0 qz245 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz246)))) Bool.false 67329067968081867925 108951082185347039232 1598993029953485 15564440312192434176 (@Eq.refl Real (@HAdd.hAdd Real Real Real qz418 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz143 1 35))) (@HMul.hMul Real Real Real qz0 qz245 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz246)))))

noncomputable def ep1802 := @List.cons EMRow46.d0 (@PSigma.mk Zeta.Certificates.ZIntervalEM Zeta.Certificates.ZIntervalEM.Certificate qz264 (ep1790 (@Enclosure.pos_of_ble 1 rfl) (@Enclosure.pos_of_ble 35 rfl) (ep1793 (@ep1794 ep1189 ep1190 (@ep1795 ep1187 ep1188 ep1189 ep1190 (@Eq.refl Real (hardyZApproximantEM 1 35 qz146)) EMRow46.d18) rfl rfl rfl)) (ep1796 (hardyZErrorBoundEM 1 34 qz12) (BSN.hardyZErrorBoundEM_le_strong 1 34 qz12 rfl) (@ep1797 Bool.false ep521 ep522 ep523 ep524 2615090167368335399 4539628424389459968 456758301361025 4539628424389459968 (@ep1792 ep521 ep522 ep523 ep524 (@Eq.refl Real (hardyZApproximantEM 1 34 qz12)) EMRow46.d12) (ep1798 EMRow46.d23) rfl rfl rfl rfl rfl)) (ep1799 (hardyZErrorBoundEM 1 35 qz146) (BSN.hardyZErrorBoundEM_le_strong 1 35 qz146 rfl) (@ep1800 Bool.false ep1187 ep1188 ep1189 ep1190 67329067968081867925 108951082185347039232 1598993029953485 15564440312192434176 (@ep1795 ep1187 ep1188 ep1189 ep1190 (@Eq.refl Real (hardyZApproximantEM 1 35 qz146)) EMRow46.d18) (ep1801 EMRow46.d25) rfl rfl rfl rfl rfl)))) (@List.nil EMRow46.d0)

noncomputable abbrev qz535 := (@Enclosure.dec_le_dec qz549 qz652 134395 1000 136442 1000 (@Eq.refl Real qz549) (@Eq.refl Real qz652) rfl rfl rfl)

noncomputable abbrev qz267 := (Zeta.Certificates.CertifiedZeroIntervals.intervals (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedEM ep1802 (@List.IsChain.singleton EMRow46.d1 EMRow46.d26 (EMRow46.d2 qz279 qz441 qz535))))

noncomputable abbrev qz536 := (@NonemptyInterval Real Real.instLE)

noncomputable def ep1803 := And (@Eq (Option Real) (@Option.map qz536 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz536 qz267)) (@Option.some Real qz12))

noncomputable def ep1804 := ep1803 (@Eq (Option Real) (@Option.map qz536 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz536 qz267)) (@Option.some Real qz146))

noncomputable def ep1805 := @And.intro (@Eq Nat (@List.length qz536 qz267) 1) ep1804

noncomputable def ep1806 := @And.intro (@Eq (Option Real) (@Option.map qz536 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz536 qz267)) (@Option.some Real qz12))

noncomputable def ep1807 := @ep1806 (@Eq (Option Real) (@Option.map qz536 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz536 qz267)) (@Option.some Real qz146))

noncomputable abbrev qz268 := (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedEM ep1802 (@List.IsChain.singleton EMRow46.d1 EMRow46.d26 (EMRow46.d2 qz279 qz441 qz535)))

theorem EMRow46.d27 : Zeta.Certificates.BatchSpec 1 134395 1000 136442 1000 := @Exists.intro Zeta.Certificates.CertifiedZeroIntervals (fun (C : Zeta.Certificates.CertifiedZeroIntervals) => And (@Eq Nat (@List.length qz536 (Zeta.Certificates.CertifiedZeroIntervals.intervals C)) 1) (And (@Eq (Option Real) (@Option.map qz536 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz536 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz12)) (@Eq (Option Real) (@Option.map qz536 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz536 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz146)))) qz268 (ep1805 (@Eq.refl Nat 1) (ep1807 (@Eq.refl (Option Real) (@Option.some Real qz12)) (@Eq.refl (Option Real) (@Option.some Real qz146))))

theorem solution : Zeta.Certificates.BatchSpec 1 134395 1000 136442 1000 := EMRow46.d27
#print axioms solution
#check solution
