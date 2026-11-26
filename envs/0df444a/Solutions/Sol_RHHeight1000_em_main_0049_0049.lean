-- Prove2me | solution 1 for RHHeight1000.em_main_0049_0049
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-19T22:01:29.996203+00:00
-- url     : https://prove2.me/submissions/3ac7d7c2-07ec-4bd5-becd-e21c9f2c92c2

import Definitions.Def_RHT1000_Support_20261118_S005
/- Copyright (c) 2026 Salvatore Mercuri, Bhavik Mehta.
Apache 2.0 license; see the source project LICENSE. -/
set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable def EMRow49.d0 := @PSigma Zeta.Certificates.ZIntervalEM fun (I : Zeta.Certificates.ZIntervalEM) => Zeta.Certificates.ZIntervalEM.Certificate I

noncomputable def EMRow49.d1 := @NonemptyInterval Real Real.instLE

noncomputable def EMRow49.d2 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @NonemptyInterval.mk Real Real.instLE (@Prod.mk Real Real a b) h

noncomputable def EMRow49.d3 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) (fc sc fb sb : Nat) => Zeta.Certificates.ZIntervalEM.mk (EMRow49.d2 a b h) fc sc fb sb

noncomputable def ep0 := nat_lit 26986075409044028275299783

noncomputable def ep1 := nat_lit 4294967296000000000000000

noncomputable def ep2 := nat_lit 26986075409044045455168967

noncomputable abbrev qz267 := (@instHMul Real Real.instMul)

noncomputable abbrev qz0 := qz267

noncomputable abbrev qz268 := (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 2 1) Real.pi)

noncomputable def ep3 := @BSN.isNear_log_image_fff qz268 884279719003555 140737488355328 1 500000000000000 ep0 ep1 ep2 ep1 4138529546116343 2251799813685248 125000000099157 49578500000000000000 4138529546116343 2251799813685248 125000000099157 49578500000000000000 963576 524288

noncomputable abbrev qz269 := (@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 2 1) Real.pi 2 1 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 140737488355328 1 500000000000000 (Enclosure.Real.IsNear.const Bool.false 2 1) BSN.pi_near_15 rfl)

noncomputable def ep4 := @ep3 2 524288 qz269 rfl rfl rfl rfl

noncomputable def ep5 := nat_lit 53972150818088056550599566

noncomputable def ep6 := nat_lit 34359738368000000000000000

noncomputable def ep7 := nat_lit 9806206225044028275299783

noncomputable def ep8 := nat_lit 44165944593044028275299783

noncomputable def ep9 := nat_lit 13681445815609410487519367394620474863599256634174726093703677122907123617368241606644861540940610176751640793056574796245399519365549113997355475306157239709119582688278313060810592403844863400465080549957745

noncomputable def ep10 := nat_lit 231714499556395493334623298703961145503103241611736774613091488581016477543539392410113701224645713379230392133956226737605624599560350113120270717249177907454870984269546186598262646369758174842349131395304

noncomputable def ep11 := nat_lit 8978369550011295664474073352761810093897501552430546263638635096022803738134167562509900960712119243631997923545019968443113540909076206607473711060286601587364321108377403290080403445693385008949995305

noncomputable def ep12 := BSN.log_dyadic_bound ep7 ep8 5 4 ep9 1048576 396628 ep10 ep11 473518 ep5 ep6 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP ep7) (BSN.artanhQ ep8) 0 4 ep10 ep9 ep11 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz270 := (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))

noncomputable abbrev qz1 := qz270

noncomputable def ep13 := ep4 rfl rfl rfl rfl (BSN.isNear_log_sfrac ep0 ep1 4138529546116343 2251799813685248 125000000099157 49578500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep0) (@Nat.cast Real Real.instNatCast ep1))) Bool.false 69433004117575847641088 37778931862957161709568 1000000000793256 396628000000000000000 4138529546116343 2251799813685248 125000000099157 49578500000000000000 (BSN.log_rat_reduce_isNear ep0 ep1 2 ep5 ep6 473518 1048576 24973259072661432 36028797018963968 396628 1000000000000000 rfl rfl rfl rfl (ep12 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep14 := nat_lit 53972150818088090910337934

noncomputable def ep15 := nat_lit 9806206225044045455168967

noncomputable def ep16 := nat_lit 44165944593044045455168967

noncomputable def ep17 := nat_lit 13681445815609453062485491347592146866046743284321690683909457683007658987562290830600045658905080811372395010565947827677605470036294121079488508864180301737865471494204890974265645509835068840465080549957745

noncomputable def ep18 := nat_lit 231714499556396865510889920206523150079811393376960301632499817942333196803513131357563499488546302200815366867712007119763002650772307103678175657719139104636874731038771518520299266622696414842349131395304

noncomputable def ep19 := nat_lit 8978369550011421500876706511871067098718760264493934208903156435737864998391937547068187824077011975074541700434630537294838404525415248443919841847024664017658842168336182958576672102333385008949995305

noncomputable def ep20 := BSN.log_dyadic_bound ep15 ep16 5 4 ep17 1048576 396628 ep18 ep19 473518 ep14 ep6 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP ep15) (BSN.artanhQ ep16) 0 4 ep18 ep17 ep19 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep21 := ep13 (BSN.isNear_log_sfrac ep2 ep1 4138529546116343 2251799813685248 125000000099157 49578500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep2) (@Nat.cast Real Real.instNatCast ep1))) Bool.false 69433004117575847641088 37778931862957161709568 1000000000793256 396628000000000000000 4138529546116343 2251799813685248 125000000099157 49578500000000000000 (BSN.log_rat_reduce_isNear ep2 ep1 2 ep14 ep6 473518 1048576 24973259072661432 36028797018963968 396628 1000000000000000 rfl rfl rfl rfl (ep20 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable abbrev qz2 := (Real.log (@HMul.hMul Real Real Real qz267 (2 : Real) Real.pi))

theorem EMRow49.d4 : Enclosure.Real.IsNear qz2 Bool.false 120447 65536 1 262144 := @Enclosure.Real.IsNear.of_eq qz2 (Real.log qz268) Bool.false 120447 65536 1 262144 BSN.log_two_pi_eq (@Enclosure.Real.IsNear.recentre' (Real.log qz268) Bool.false 963576 524288 2 524288 120447 65536 1 262144 (ep21 rfl rfl rfl rfl rfl rfl rfl rfl) rfl)

noncomputable def ep22 := nat_lit 8589934592000000000000000

noncomputable def ep23 := @BSN.isNear_log_image_fff Real.pi 226375608064910080 72057594037927936 1 1000000000000000 ep0 ep22 ep2 ep22 1200336 1048576 1 396628 1200336 1048576 1 396628 600168 524288 2 524288 BSN.pi_near_15 rfl rfl rfl

noncomputable def ep24 := nat_lit 17179869184000000000000000

noncomputable def ep25 := nat_lit 18396140817044028275299783

noncomputable def ep26 := nat_lit 35576010001044028275299783

noncomputable def ep27 := nat_lit 145019262663961446558303139663424756232419223153299357158415217874016130572233056993847515999529612750616182853355499335896178729185698845314776375864537073527142908641610750276034469165612529925303649396973267518946591078603565291376312767403717761600170009932259137778521478520425507632472584532570900560707662248426541531715360699177249902784721815296292248142738824858695953661559845440650653128788875447728828657762006237171740033404723254477174341920697506370253193455781322964835857351124092897592956162654178130575

noncomputable def ep28 := nat_lit 15500762873619990602332184736899274490522931101512051618692838888825382235673431503644115344741331161500627469184702974962114537943617674254904297224139410345221262767191485292268260077615645253784097850065864022184521411511133693085443040736512010941548648374196772723338837137976260321103066698629790037694560548409922339907589559883712609967105556007429010014773911317423638534096849366294542840133852248768895750397896505791271178551667935288585787166713880920071720072716082683081155281219708172458141800988558163320

noncomputable def ep29 := nat_lit 12900190794487083783367107939442176642390171280542213571554777169279725287102813254708993369099729304728646904879886535518616983985412662170766446331701281703998252143668221340329975389245922410714088123244705567402747658401492589451585970559635763980329972215329212888079422466283203384882259392047898400615815810081169907384366653346471604103896809335921621947903075223769953790093549808584241881353287841076643853121427928248525828402335494512605306631304432120211393210317325496757155861061354331245840675149075

noncomputable def ep30 := BSN.log_dyadic_bound ep25 ep26 11 10 ep27 1048576 396628 ep28 ep29 1200336 ep5 ep24 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base10 (BSN.artanhP ep25) (BSN.artanhQ ep26) 0 10 ep28 ep27 ep29 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep31 := nat_lit 18396140817044045455168967

noncomputable def ep32 := nat_lit 35576010001044045455168967

noncomputable def ep33 := nat_lit 145019262663962847171784895425483977818796535899227200426399035286881207006285364467913811844950531107314785650583974625982406238691319033447632878979985852280879486690814033867010958364699188952871572448188560932645032521756218245629809291975913196623825614492380080480004685076434733043183791438169545293975334857826316990371107134320667652578346815517853870648072772035977941843998949310557583393428557296298890786965786350523173236912472938174255438182435383147950274229549088258679583524155427309880956162654178130575

noncomputable def ep34 := nat_lit 15500762873620157189619721156942591192100275120160672416764593300158228469749443299607348495591439275767946573253526107895503597951484257520435868240203420954375895980141891044871083424251900562230440202302413072793440172565998181227591194192658878334739610458454844032013325963992941389843551995646587189684848765634635122388286241104146031552341815777883628509454807838726994150833304950745987647656768534710890974432620160470644835720379148964170536679305861738540146791997074363921127776563807649880221800988558163320

noncomputable def ep35 := nat_lit 12900190794487324729109480814509220959173684627296055849229843377126536688487849343376525559792931631054411655715865486295286288812423905434305314401904993536755333953308594664509631000767632482919425633906965368325056855874260596615770736441041599390097968820060635361729170158825410327022636428624381203910573184452046894301676992229743752846881064485858738985580654099214803581683226335297196686880535448467637789069028262446657986458573827723305156755787640135484017403116612632808333639900906331245840675149075

noncomputable def ep36 := BSN.log_dyadic_bound ep31 ep32 11 10 ep33 1048576 396628 ep34 ep35 1200336 ep14 ep24 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base10 (BSN.artanhP ep31) (BSN.artanhQ ep32) 0 10 ep34 ep33 ep35 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep37 := @Enclosure.Real.IsNear.recentre' (Real.log Real.pi) Bool.false 600168 524288 2 524288 75021 65536 1 262144 (ep23 rfl rfl rfl rfl rfl (BSN.isNear_log_sfrac ep0 ep22 1200336 1048576 1 396628 Bool.false (BSN.logfrac_isNear ep5 ep24 1 ep0 ep22 1200336 1048576 396628 rfl rfl rfl (ep30 rfl))) (BSN.isNear_log_sfrac ep2 ep22 1200336 1048576 1 396628 Bool.false (BSN.logfrac_isNear ep14 ep24 1 ep2 ep22 1200336 1048576 396628 rfl rfl rfl (ep36 rfl))) rfl rfl rfl rfl rfl rfl rfl rfl) rfl

theorem EMRow49.d5 : Enclosure.Real.IsNear (Real.log Real.pi) Bool.false 75021 65536 1 262144 := ep37

noncomputable abbrev qz729 := (@HAdd.hAdd Complex Complex Complex (@instHAdd Complex Complex.instAdd) (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (2 : Complex)) (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul) Complex.I ↑(Enclosure.sfrac Bool.false 140505 1000)))

noncomputable abbrev qz540 := qz729

noncomputable abbrev qz271 := qz540

noncomputable abbrev qz3 := (BSN.headSumC qz271 9)

noncomputable abbrev qz730 := (@instHAdd Complex Complex.instAdd)

noncomputable abbrev qz541 := qz730

noncomputable abbrev qz272 := qz541

noncomputable abbrev qz4 := qz272

noncomputable abbrev qz5 := qz271

noncomputable abbrev qz542 := (@instHPow Complex Complex Complex.instPow)

noncomputable abbrev qz273 := qz542

noncomputable abbrev qz6 := qz273

noncomputable abbrev qz543 := (@Neg.neg Complex Complex.instNeg qz729)

noncomputable abbrev qz274 := qz543

noncomputable abbrev qz7 := qz274

noncomputable abbrev qz544 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 8) qz7)

noncomputable def ep38 := @Enclosure.Complex.IsNear.of_eq qz3 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 8) qz544) Bool.false 390213106953 1099511627776 263244824925101 109024274475384832 Bool.false 72263011735 549755813888 65659473884475 27256068618846208

noncomputable def ep39 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 8) qz544 Bool.false 778945575889 1099511627776 235596838262037 109024274475384832 Bool.false 143042744743 1099511627776 235093485004855 109024274475384832 Bool.true

noncomputable abbrev qz545 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 7) qz7)

noncomputable def ep40 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 8) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 7) qz545) Bool.false 778945575889 1099511627776 235596838262037 109024274475384832 Bool.false 143042744743 1099511627776 235093485004855 109024274475384832

noncomputable def ep41 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 7) qz545 Bool.false 1192790518839 1099511627776 206047427058399 109024274475384832 Bool.false 52572875959 549755813888 102819066322031 54512137237692416 Bool.true

noncomputable abbrev qz546 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 6) qz7)

noncomputable def ep42 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 7) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 6) qz546) Bool.false 1192790518839 1099511627776 206047427058399 109024274475384832 Bool.false 52572875959 549755813888 102819066322031 54512137237692416

noncomputable def ep43 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 6) qz546 Bool.false 97949313951 137438953472 87073771558573 54512137237692416 Bool.false 36207580411 137438953472 10861893259167 6814017154711552 Bool.false

noncomputable abbrev qz547 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 5) qz7)

noncomputable def ep44 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 6) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 5) qz547) Bool.false 97949313951 137438953472 87073771558573 54512137237692416 Bool.false 36207580411 137438953472 10861893259167 6814017154711552

noncomputable def ep45 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 5) qz547 Bool.false 146394551775 549755813888 69624764455413 54512137237692416 Bool.false 259753248239 1099511627776 138989735091901 109024274475384832 Bool.false

noncomputable abbrev qz548 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 4) qz7)

noncomputable def ep46 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 5) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 4) qz548) Bool.false 146394551775 549755813888 69624764455413 54512137237692416 Bool.false 259753248239 1099511627776 138989735091901 109024274475384832

noncomputable def ep47 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 4) qz548 Bool.true 128481782307 549755813888 50096239894687 54512137237692416 Bool.false 261078645775 1099511627776 100036408555357 109024274475384832 Bool.false

noncomputable abbrev qz549 := (@Nat.cast Complex Complex.instNatCast 3)

noncomputable abbrev qz275 := qz549

noncomputable abbrev qz8 := qz275

noncomputable def ep48 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 4) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 3) (@HPow.hPow Complex Complex Complex qz6 qz8 qz7)) Bool.true 128481782307 549755813888 50096239894687 54512137237692416 Bool.false 261078645775 1099511627776 100036408555357 109024274475384832

noncomputable def ep49 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 3) (@HPow.hPow Complex Complex Complex qz6 qz8 qz7) Bool.false 322040451151 1099511627776 55118480610459 109024274475384832 Bool.false 832653965 1099511627776 55014618412495 109024274475384832 Bool.true

noncomputable abbrev qz550 := (@Nat.cast Complex Complex.instNatCast 2)

noncomputable abbrev qz276 := qz550

noncomputable abbrev qz9 := qz276

noncomputable def ep50 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 3) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 2) (@HPow.hPow Complex Complex Complex qz6 qz9 qz7)) Bool.false 322040451151 1099511627776 55118480610459 109024274475384832 Bool.false 832653965 1099511627776 55014618412495 109024274475384832

noncomputable def ep51 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 2) (@HPow.hPow Complex Complex Complex qz6 qz9 qz7) Bool.false 1 1 0 1 Bool.false 0 1 0 1 Bool.true

noncomputable abbrev qz551 := (Enclosure.sfrac Bool.false 0 1)

noncomputable abbrev qz10 := qz551

noncomputable def ep52 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 2) (Complex.mk (Enclosure.sfrac Bool.false 1 1) qz10) Bool.false 1 1 0 1 Bool.false 0 1 0 1 (BSN.head_sum_c_two qz5)

noncomputable abbrev qz731 := (Enclosure.sfrac Bool.false 140505 1000)

noncomputable abbrev qz552 := qz731

noncomputable abbrev qz277 := qz552

noncomputable abbrev qz278 := (Enclosure.sfrac Bool.false 2 1)

noncomputable abbrev qz11 := (@HMul.hMul Real Real Real qz267 qz277 (Real.log qz278))

noncomputable abbrev qz12 := qz277

noncomputable abbrev qz279 := (@Eq.refl Real qz552)

noncomputable abbrev qz13 := qz279

noncomputable abbrev qz280 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 2)))

noncomputable def ep53 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz9 qz7) (Complex.mk (@HMul.hMul Real Real Real qz0 qz280 (Real.cos qz11)) (@HMul.hMul Real Real Real qz0 qz280 (@Neg.neg Real Real.instNeg (Real.sin qz11)))) Bool.true 777471176625 1099511627776 55118480610459 109024274475384832 Bool.false 832653965 1099511627776 55014618412495 109024274475384832 (BSN.cpow_neg_s_mk qz12 140505 1000 2 qz13 rfl)

noncomputable abbrev qz14 := (@Nat.cast Real Real.instNatCast 1)

noncomputable abbrev qz281 := (Real.sqrt (@Nat.cast Real Real.instNatCast 2))

noncomputable abbrev qz282 := (@Nat.cast Real Real.instNatCast 2)

noncomputable def ep54 := @Enclosure.Real.IsNear.inv_image qz281 1482911 1048576 1 1048576 370727 370728 524288 (@Enclosure.Real.IsNear.of_eq qz281 (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz282 qz14)) Bool.false 1482911 1048576 1 1048576 (BSN.sqrt_natCast_div_one 2) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz282 qz14)) Bool.false 1482911 1048576 1 1048576 1482911 1048576 1 1048576 (BSN.sqrt_enclosure 2 1 741455 741456 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep55 := BSN.log_dyadic_bound 1 3 6 5 613814355 524288 198314 24381081 945 363408 4 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 1) (BSN.artanhQ 3) 0 5 24381081 613814355 945 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz15 := (BSN.cosEvenQ 2147483648)

noncomputable abbrev qz16 := (BSN.cosOddQ 2147483648)

noncomputable def ep56 := BSN.cos_dyadic_bound_f 2301115 2147483648 1 0 1048576 397016 0 1 1 0 1 1 1048575 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 2301115) qz15 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 2301115) qz16 0 0 rfl) rfl rfl

noncomputable abbrev qz17 := (@Nat.cast Real Real.instNatCast 524288)

noncomputable abbrev qz18 := (Enclosure.Real.IsNear.const Bool.false 140505 1000)

noncomputable abbrev qz19 := (@Nat.cast Real Real.instNatCast 75557863725914323419136)

noncomputable abbrev qz283 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 51060641) qz17)

noncomputable abbrev qz284 := (BSN.isNear_log_sfrac 2 1 363408 524288 1 198314 Bool.false (BSN.logfrac_isNear 4 2 1 2 1 363408 524288 198314 rfl rfl rfl (ep55 rfl)))

noncomputable def ep57 := @Enclosure.Real.IsNear.cos_image qz11 qz283 Bool.false 51060641 524288 743 1048576 Bool.true 1048575 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz11 Bool.false 638258013 6553600 28101 39662800 51060641 524288 743 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz12 (Real.log qz278) 140505 1000 0 1 363408 524288 1 198314 638258013 6553600 28101 39662800 qz18 qz284 rfl) rfl) (Enclosure.sfrac_false_div 51060641 524288) (BSN.cos_reduce2 qz283 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 80963318351734505472) qz19) 226375608064910080 72057594037927936 Bool.false 1048575 1048576 15 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q2 51060641 524288 226375608064910080 72057594037927936 15 80963318351734505472 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1048575 1048576 80963318351734505472 75557863725914323419136 2301115 2147483648 397016 396628 (ep56 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz20 := (BSN.sinEvenQ 2147483648)

noncomputable abbrev qz21 := (BSN.sinOddQ 2147483648)

noncomputable def ep58 := BSN.sin_dyadic_bound_f 2301115 2147483648 1 0 1048576 397016 0 1 1 0 1 1 1123 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 2301115) qz20 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 2301115) qz21 0 0 rfl) rfl rfl

noncomputable def ep59 := @Enclosure.Real.IsNear.sin_image qz11 qz283 Bool.false 51060641 524288 743 1048576 Bool.true 1123 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz11 Bool.false 638258013 6553600 28101 39662800 51060641 524288 743 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz12 (Real.log qz278) 140505 1000 0 1 363408 524288 1 198314 638258013 6553600 28101 39662800 qz18 qz284 rfl) rfl) (Enclosure.sfrac_false_div 51060641 524288) (BSN.sin_reduce2 qz283 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 80963318351734505472) qz19) 226375608064910080 72057594037927936 Bool.false 1123 1048576 15 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q2 51060641 524288 226375608064910080 72057594037927936 15 80963318351734505472 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1123 1048576 80963318351734505472 75557863725914323419136 2301115 2147483648 397016 396628 (ep58 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz285 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 2))) Bool.false 741455 1048576 1 1048576 741455 1048576 1 1048576 (ep54 rfl rfl) rfl)

noncomputable def ep60 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz280 (Real.cos qz11)) (@HMul.hMul Real Real Real qz0 qz280 (@Neg.neg Real Real.instNeg (Real.sin qz11))) Bool.true 777471176625 1099511627776 55118480610459 109024274475384832 Bool.false 832653965 1099511627776 55014618412495 109024274475384832 (@Enclosure.Real.IsNear.mulLit_ft qz280 (Real.cos qz11) 741455 1048576 1 1048576 1048575 1048576 74197939 103973650432 777471176625 1099511627776 55118480610459 109024274475384832 qz285 (@Enclosure.Real.IsNear.recentre' (Real.cos qz11) Bool.true 1048575 1048576 148395878 207947300864 1048575 1048576 74197939 103973650432 (ep57 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz280 (@Neg.neg Real Real.instNeg (Real.sin qz11)) 741455 1048576 1 1048576 1123 1048576 74197939 103973650432 832653965 1099511627776 55014618412495 109024274475384832 qz285 (@Enclosure.Real.IsNear.neg (Real.sin qz11) Bool.true 1123 1048576 74197939 103973650432 (@Enclosure.Real.IsNear.recentre' (Real.sin qz11) Bool.true 1123 1048576 148395878 207947300864 1123 1048576 74197939 103973650432 (ep59 rfl rfl) rfl)) rfl)

noncomputable abbrev qz553 := (Enclosure.Real.IsNear.const Bool.false 0 1)

noncomputable abbrev qz22 := qz553

noncomputable def ep61 := @ep51 777471176625 1099511627776 55118480610459 109024274475384832 Bool.false 832653965 1099511627776 55014618412495 109024274475384832 Bool.false 322040451151 322040451151 1099511627776 55118480610459 109024274475384832 Bool.false 832653965 832653965 1099511627776 55014618412495 109024274475384832 (ep52 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 1) qz10 Bool.false 1 1 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 1) qz22)) (ep53 ep60) rfl rfl

noncomputable abbrev qz554 := (Real.log (Enclosure.sfrac Bool.false 3 1))

noncomputable abbrev qz23 := (@HMul.hMul Real Real Real qz267 qz277 qz554)

noncomputable abbrev qz286 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 3)))

noncomputable def ep62 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz8 qz7) (Complex.mk (@HMul.hMul Real Real Real qz0 qz286 (Real.cos qz23)) (@HMul.hMul Real Real Real qz0 qz286 (@Neg.neg Real Real.instNeg (Real.sin qz23)))) Bool.true 579004015765 1099511627776 45073999178915 109024274475384832 Bool.false 130122995905 549755813888 22510895071431 54512137237692416 (BSN.cpow_neg_s_mk qz12 140505 1000 3 qz13 rfl)

noncomputable abbrev qz287 := (Real.sqrt (@Nat.cast Real Real.instNatCast 3))

noncomputable abbrev qz288 := (@Nat.cast Real Real.instNatCast 3)

noncomputable def ep63 := @Enclosure.Real.IsNear.inv_image qz287 1816187 1048576 1 1048576 302697 302698 524288 (@Enclosure.Real.IsNear.of_eq qz287 (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz288 qz14)) Bool.false 1816187 1048576 1 1048576 (BSN.sqrt_natCast_div_one 3) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz288 qz14)) Bool.false 1816187 1048576 1 1048576 1816187 1048576 1 1048576 (BSN.sqrt_enclosure 3 1 908093 908094 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep64 := BSN.log_dyadic_bound 1 2 10 9 171633298636800 524288 198314 16925142283965 34459425 575989 3 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base9 (BSN.artanhP 1) (BSN.artanhQ 2) 0 9 16925142283965 171633298636800 34459425 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep65 := nat_lit 677134387819770095738473800001916481

noncomputable def ep66 := nat_lit 510423550381407695195061911147652317184

noncomputable def ep67 := nat_lit 7656353255721115427925928667214784757760

noncomputable def ep68 := BSN.cos_dyadic_bound_f 907128303 2147483648 2 1 1048576 397016 ep65 ep66 ep65 ep65 ep67 ep65 956407 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 907128303) qz15 0 1 ep65 ep66 ep65 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 907128303) qz16 0 1 ep65 ep67 ep65 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz24 := (@Nat.cast Real Real.instNatCast 262144)

noncomputable abbrev qz289 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 40464667) qz24)

noncomputable abbrev qz290 := (BSN.isNear_log_sfrac 3 1 575989 524288 1 198314 Bool.false (BSN.logfrac_isNear 3 1 2 3 1 575989 524288 198314 rfl rfl rfl (ep64 rfl)))

noncomputable abbrev qz291 := (@Nat.cast Real Real.instNatCast 37778931862957161709568)

noncomputable def ep69 := @Enclosure.Real.IsNear.cos_image qz23 qz289 Bool.false 40464667 262144 93 131072 Bool.true 956407 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz23 Bool.false 16185866889 104857600 28101 39662800 40464667 262144 93 131072 (@Enclosure.Real.IsNear.mulLit_ff qz12 qz554 140505 1000 0 1 575989 524288 1 198314 16185866889 104857600 28101 39662800 qz18 qz290 rfl) rfl) (Enclosure.sfrac_false_div 40464667 262144) (BSN.cos_reduce2 qz289 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 15958369876235375345664) qz291) 226375608064910080 72057594037927936 Bool.false 956407 1048576 24 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q2 40464667 262144 226375608064910080 72057594037927936 24 15958369876235375345664 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 956407 1048576 15958369876235375345664 37778931862957161709568 907128303 2147483648 397016 396628 (ep68 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep70 := nat_lit 2552117751907038475975309555738261585920

noncomputable def ep71 := nat_lit 17864824263349269331827166890167831101440

noncomputable def ep72 := BSN.sin_dyadic_bound_f 907128303 2147483648 2 1 1048576 397016 ep65 ep70 ep65 ep65 ep71 ep65 429878 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 907128303) qz20 0 1 ep65 ep70 ep65 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 907128303) qz21 0 1 ep65 ep71 ep65 rfl rfl rfl rfl) rfl rfl

noncomputable def ep73 := @Enclosure.Real.IsNear.sin_image qz23 qz289 Bool.false 40464667 262144 93 131072 Bool.true 429878 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz23 Bool.false 16185866889 104857600 28101 39662800 40464667 262144 93 131072 (@Enclosure.Real.IsNear.mulLit_ff qz12 qz554 140505 1000 0 1 575989 524288 1 198314 16185866889 104857600 28101 39662800 qz18 qz290 rfl) rfl) (Enclosure.sfrac_false_div 40464667 262144) (BSN.sin_reduce2 qz289 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 15958369876235375345664) qz291) 226375608064910080 72057594037927936 Bool.false 429878 1048576 24 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q2 40464667 262144 226375608064910080 72057594037927936 24 15958369876235375345664 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 429878 1048576 15958369876235375345664 37778931862957161709568 907128303 2147483648 397016 396628 (ep72 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz292 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 3))) Bool.false 605395 1048576 1 1048576 605395 1048576 1 1048576 (ep63 rfl rfl) rfl)

noncomputable def ep74 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz286 (Real.cos qz23)) (@HMul.hMul Real Real Real qz0 qz286 (@Neg.neg Real Real.instNeg (Real.sin qz23))) Bool.true 579004015765 1099511627776 45073999178915 109024274475384832 Bool.false 130122995905 549755813888 22510895071431 54512137237692416 (@Enclosure.Real.IsNear.mulLit_ft qz286 (Real.cos qz23) 605395 1048576 1 1048576 956407 1048576 9287137 12996706304 579004015765 1099511627776 45073999178915 109024274475384832 qz292 (@Enclosure.Real.IsNear.recentre' (Real.cos qz23) Bool.true 956407 1048576 18574274 25993412608 956407 1048576 9287137 12996706304 (ep69 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz286 (@Neg.neg Real Real.instNeg (Real.sin qz23)) 605395 1048576 1 1048576 214939 524288 9287137 12996706304 130122995905 549755813888 22510895071431 54512137237692416 qz292 (@Enclosure.Real.IsNear.neg (Real.sin qz23) Bool.true 214939 524288 9287137 12996706304 (@Enclosure.Real.IsNear.recentre' (Real.sin qz23) Bool.true 429878 1048576 18574274 25993412608 214939 524288 9287137 12996706304 (ep73 rfl rfl) rfl)) rfl)

noncomputable def ep75 := @ep49 579004015765 1099511627776 45073999178915 109024274475384832 Bool.false 130122995905 549755813888 22510895071431 54512137237692416 Bool.true 282534427207862493118464 128481782307 549755813888 50096239894687 54512137237692416 Bool.false 143529503396811977523200 261078645775 1099511627776 100036408555357 109024274475384832 (ep50 (BSN.head_sum_c_succ qz5 2 3 rfl rfl) (ep61 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep62 ep74) rfl rfl

noncomputable abbrev qz555 := (Real.log (Enclosure.sfrac Bool.false 4 1))

noncomputable abbrev qz25 := (@HMul.hMul Real Real Real qz267 qz277 qz555)

noncomputable abbrev qz293 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 4)))

noncomputable def ep76 := @Enclosure.Complex.IsNear.of_eq qz548 (Complex.mk (@HMul.hMul Real Real Real qz0 qz293 (Real.cos qz25)) (@HMul.hMul Real Real Real qz0 qz293 (@Neg.neg Real Real.instNeg (Real.sin qz25)))) Bool.false 137438167041 274877906944 9764262280363 27256068618846208 Bool.true 41418673 34359738368 1217291454267 3407008577355776 (BSN.cpow_neg_s_mk qz12 140505 1000 4 qz13 rfl)

noncomputable abbrev qz294 := (Real.sqrt (@Nat.cast Real Real.instNatCast 4))

noncomputable abbrev qz295 := (@Nat.cast Real Real.instNatCast 4)

noncomputable def ep77 := @Enclosure.Real.IsNear.inv_image qz294 2097153 1048576 1 1048576 262143 262144 524288 (@Enclosure.Real.IsNear.of_eq qz294 (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz295 qz14)) Bool.false 2097153 1048576 1 1048576 (BSN.sqrt_natCast_div_one 4) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz295 qz14)) Bool.false 2097153 1048576 1 1048576 2097153 1048576 1 1048576 (BSN.sqrt_enclosure 4 1 1048576 1048577 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep78 := nat_lit 318077276165597140789031982421875

noncomputable def ep79 := nat_lit 49379992292270016474244603430625

noncomputable def ep80 := nat_lit 20095619060363156210525625

noncomputable def ep81 := BSN.log_dyadic_bound 3 5 14 13 ep78 524288 198314 ep79 ep80 726817 8 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base13 (BSN.artanhP 3) (BSN.artanhQ 5) 0 13 ep79 ep78 ep80 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep82 := BSN.cos_dyadic_bound_f 5177719 2147483648 1 0 1048576 397016 0 1 1 0 1 1 1048572 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 5177719) qz15 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 5177719) qz16 0 0 rfl) rfl rfl

noncomputable abbrev qz26 := (@Nat.cast Real Real.instNatCast 1048576)

noncomputable abbrev qz27 := (@Nat.cast Real Real.instNatCast 151115727451828646838272)

noncomputable abbrev qz296 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 204242845) qz26)

noncomputable abbrev qz297 := (BSN.isNear_log_sfrac 4 1 726817 524288 1 198314 Bool.false (BSN.logfrac_isNear 8 2 1 4 1 726817 524288 198314 rfl rfl rfl (ep81 rfl)))

noncomputable def ep83 := @Enclosure.Real.IsNear.cos_image qz25 qz296 Bool.false 204242845 1048576 93 131072 Bool.false 1048572 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz25 Bool.false 20424284517 104857600 28101 39662800 204242845 1048576 93 131072 (@Enclosure.Real.IsNear.mulLit_ff qz12 qz555 140505 1000 0 1 726817 524288 1 198314 20424284517 104857600 28101 39662800 qz18 qz297 rfl) rfl) (Enclosure.sfrac_false_div 204242845 1048576) (BSN.cos_reduce0 qz296 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 364349641256253521920) qz27) 226375608064910080 72057594037927936 Bool.false 1048572 1048576 31 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q0 204242845 1048576 226375608064910080 72057594037927936 31 364349641256253521920 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1048572 1048576 364349641256253521920 151115727451828646838272 5177719 2147483648 397016 396628 (ep82 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep84 := BSN.sin_dyadic_bound_f 5177719 2147483648 1 0 1048576 397016 0 1 1 0 1 1 2528 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 5177719) qz20 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 5177719) qz21 0 0 rfl) rfl rfl

noncomputable def ep85 := @Enclosure.Real.IsNear.sin_image qz25 qz296 Bool.false 204242845 1048576 93 131072 Bool.false 2528 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz25 Bool.false 20424284517 104857600 28101 39662800 204242845 1048576 93 131072 (@Enclosure.Real.IsNear.mulLit_ff qz12 qz555 140505 1000 0 1 726817 524288 1 198314 20424284517 104857600 28101 39662800 qz18 qz297 rfl) rfl) (Enclosure.sfrac_false_div 204242845 1048576) (BSN.sin_reduce0 qz296 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 364349641256253521920) qz27) 226375608064910080 72057594037927936 Bool.false 2528 1048576 31 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q0 204242845 1048576 226375608064910080 72057594037927936 31 364349641256253521920 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 2528 1048576 364349641256253521920 151115727451828646838272 5177719 2147483648 397016 396628 (ep84 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz298 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 4))) Bool.false 524287 1048576 1 1048576 524287 1048576 1 1048576 (ep77 rfl rfl) rfl)

noncomputable def ep86 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz293 (Real.cos qz25)) (@HMul.hMul Real Real Real qz0 qz293 (@Neg.neg Real Real.instNeg (Real.sin qz25))) Bool.false 137438167041 274877906944 9764262280363 27256068618846208 Bool.true 41418673 34359738368 1217291454267 3407008577355776 (@Enclosure.Real.IsNear.mulLit_ff qz293 (Real.cos qz25) 524287 1048576 1 1048576 262143 262144 9287137 12996706304 137438167041 274877906944 9764262280363 27256068618846208 qz298 (@Enclosure.Real.IsNear.recentre' (Real.cos qz25) Bool.false 1048572 1048576 18574274 25993412608 262143 262144 9287137 12996706304 (ep83 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz293 (@Neg.neg Real Real.instNeg (Real.sin qz25)) 524287 1048576 1 1048576 79 32768 9287137 12996706304 41418673 34359738368 1217291454267 3407008577355776 qz298 (@Enclosure.Real.IsNear.neg (Real.sin qz25) Bool.false 79 32768 9287137 12996706304 (@Enclosure.Real.IsNear.recentre' (Real.sin qz25) Bool.false 2528 1048576 18574274 25993412608 79 32768 9287137 12996706304 (ep85 rfl rfl) rfl)) rfl)

noncomputable def ep87 := @ep47 137438167041 274877906944 9764262280363 27256068618846208 Bool.true 41418673 34359738368 1217291454267 3407008577355776 Bool.false 40240627979917040025600 146394551775 549755813888 69624764455413 54512137237692416 Bool.false 8925053649730196733952 259753248239 1099511627776 138989735091901 109024274475384832 (ep48 (BSN.head_sum_c_succ qz5 3 4 rfl rfl) (ep75 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep76 ep86) rfl rfl

noncomputable abbrev qz556 := (Real.log (Enclosure.sfrac Bool.false 5 1))

noncomputable abbrev qz28 := (@HMul.hMul Real Real Real qz267 qz277 qz556)

noncomputable abbrev qz299 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 5)))

noncomputable def ep88 := @Enclosure.Complex.IsNear.of_eq qz547 (Complex.mk (@HMul.hMul Real Real Real qz0 qz299 (Real.cos qz28)) (@HMul.hMul Real Real Real qz0 qz299 (@Neg.neg Real Real.instNeg (Real.sin qz28)))) Bool.false 245402704029 549755813888 2181125887895 6814017154711552 Bool.false 29907395049 1099511627776 34800557054771 109024274475384832 (BSN.cpow_neg_s_mk qz12 140505 1000 5 qz13 rfl)

noncomputable abbrev qz300 := (Real.sqrt (@Nat.cast Real Real.instNatCast 5))

noncomputable abbrev qz301 := (@Nat.cast Real Real.instNatCast 5)

noncomputable def ep89 := @Enclosure.Real.IsNear.inv_image qz300 2344687 1048576 1 1048576 234468 234469 524288 (@Enclosure.Real.IsNear.of_eq qz300 (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz301 qz14)) Bool.false 2344687 1048576 1 1048576 (BSN.sqrt_natCast_div_one 5) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz301 qz14)) Bool.false 2344687 1048576 1 1048576 2344687 1048576 1 1048576 (BSN.sqrt_enclosure 5 1 1172343 1172344 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep90 := nat_lit 3696382175741467532940033205863946875

noncomputable def ep91 := nat_lit 765440954430599474856563326857688500

noncomputable def ep92 := nat_lit 108794268166472120024432640000

noncomputable def ep93 := BSN.log_dyadic_bound 2 3 18 17 ep90 524288 198314 ep91 ep92 843808 5 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_rec (BSN.artanhP 2) (BSN.artanhQ 3) 0 17 8 307084260767580 1483365253795425 132843110400 1663129201793174588340 2491889415829100854875 818968088287641600 ep91 ep90 ep92 rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.artanhP 2) (BSN.artanhQ 3) 0 8 307084260767580 1483365253795425 132843110400 rfl rfl rfl rfl) (@BSN.binarySplit_of_base9 (BSN.artanhP 2) (BSN.artanhQ 3) 8 17 1663129201793174588340 2491889415829100854875 818968088287641600 rfl rfl rfl rfl)) rfl rfl

noncomputable def ep94 := nat_lit 7121966849833608328090002514318347255273988292278607329757487837488901349564545

noncomputable def ep95 := nat_lit 164135286493895707012911871249815109382010203263545499525931125331216861264609280

noncomputable def ep96 := nat_lit 12220969443139861517700977113707149712840908528037961776475926972246798753921

noncomputable def ep97 := nat_lit 18632983989513414416826109765030621711896798342160481544583888073563484908019841

noncomputable def ep98 := nat_lit 3009146919054754628570050972913277005336853726498334157975403964405642456517836800

noncomputable def ep99 := BSN.sin_dyadic_bound_f 3242561391 2147483648 3 2 1048576 397016 ep94 ep95 ep96 ep97 ep98 ep96 1046634 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3242561391) qz20 0 2 ep94 ep95 ep96 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3242561391) qz21 0 2 ep97 ep98 ep96 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz302 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 118559243) qz17)

noncomputable abbrev qz303 := (BSN.isNear_log_sfrac 5 1 843808 524288 1 198314 Bool.false (BSN.logfrac_isNear 5 1 2 5 1 843808 524288 198314 rfl rfl rfl (ep93 rfl rfl)))

noncomputable def ep100 := @Enclosure.Real.IsNear.cos_image qz28 qz302 Bool.false 118559243 524288 743 1048576 Bool.false 1046634 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz28 Bool.false 740995269 3276800 28101 39662800 118559243 524288 743 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz12 qz556 140505 1000 0 1 843808 524288 1 198314 740995269 3276800 28101 39662800 qz18 qz303 rfl) rfl) (Enclosure.sfrac_false_div 118559243 524288) (BSN.cos_reduce3 qz302 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 114087486513711390130176) qz19) 226375608064910080 72057594037927936 Bool.false 1046634 1048576 35 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q3 118559243 524288 226375608064910080 72057594037927936 35 114087486513711390130176 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1046634 1048576 114087486513711390130176 75557863725914323419136 3242561391 2147483648 397016 396628 (ep99 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep101 := nat_lit 3962079791882289009613424053338507208357922788389465388432593655037054882537601

noncomputable def ep102 := nat_lit 18237254054877300779212430138868345486890022584838388836214569481246317918289920

noncomputable def ep103 := nat_lit 11861797436760587305804870205788107325648086548112320241744829111166671050104961

noncomputable def ep104 := nat_lit 820676432469478535064559356249075546910051016317727497629655626656084306323046400

noncomputable def ep105 := BSN.cos_dyadic_bound_f 3242561391 2147483648 3 2 1048576 397016 ep101 ep102 ep96 ep103 ep104 ep96 63777 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3242561391) qz15 0 2 ep101 ep102 ep96 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3242561391) qz16 0 2 ep103 ep104 ep96 rfl rfl rfl rfl) rfl rfl

noncomputable def ep106 := @Enclosure.Real.IsNear.sin_image qz28 qz302 Bool.false 118559243 524288 743 1048576 Bool.true 63777 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz28 Bool.false 740995269 3276800 28101 39662800 118559243 524288 743 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz12 qz556 140505 1000 0 1 843808 524288 1 198314 740995269 3276800 28101 39662800 qz18 qz303 rfl) rfl) (Enclosure.sfrac_false_div 118559243 524288) (BSN.sin_reduce3 qz302 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 114087486513711390130176) qz19) 226375608064910080 72057594037927936 Bool.false 63777 1048576 35 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q3 118559243 524288 226375608064910080 72057594037927936 35 114087486513711390130176 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 63777 1048576 114087486513711390130176 75557863725914323419136 3242561391 2147483648 397016 396628 (ep105 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz304 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 5))) Bool.false 468937 1048576 1 1048576 468937 1048576 1 1048576 (ep89 rfl rfl) rfl)

noncomputable def ep107 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz299 (Real.cos qz28)) (@HMul.hMul Real Real Real qz0 qz299 (@Neg.neg Real Real.instNeg (Real.sin qz28))) Bool.false 245402704029 549755813888 2181125887895 6814017154711552 Bool.false 29907395049 1099511627776 34800557054771 109024274475384832 (@Enclosure.Real.IsNear.mulLit_ff qz299 (Real.cos qz28) 468937 1048576 1 1048576 523317 524288 74197939 103973650432 245402704029 549755813888 2181125887895 6814017154711552 qz304 (@Enclosure.Real.IsNear.recentre' (Real.cos qz28) Bool.false 1046634 1048576 148395878 207947300864 523317 524288 74197939 103973650432 (ep100 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz299 (@Neg.neg Real Real.instNeg (Real.sin qz28)) 468937 1048576 1 1048576 63777 1048576 74197939 103973650432 29907395049 1099511627776 34800557054771 109024274475384832 qz304 (@Enclosure.Real.IsNear.neg (Real.sin qz28) Bool.true 63777 1048576 74197939 103973650432 (@Enclosure.Real.IsNear.recentre' (Real.sin qz28) Bool.true 63777 1048576 148395878 207947300864 63777 1048576 74197939 103973650432 (ep106 rfl rfl) rfl)) rfl)

noncomputable def ep108 := @ep45 245402704029 549755813888 2181125887895 6814017154711552 Bool.false 29907395049 1099511627776 34800557054771 109024274475384832 Bool.false 215392819243612951805952 97949313951 137438953472 87073771558573 54512137237692416 Bool.false 318485245404232168767488 36207580411 137438953472 10861893259167 6814017154711552 (ep46 (BSN.head_sum_c_succ qz5 4 5 rfl rfl) (ep87 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep88 ep107) rfl rfl

noncomputable abbrev qz557 := (Real.log (Enclosure.sfrac Bool.false 6 1))

noncomputable abbrev qz29 := (@HMul.hMul Real Real Real qz267 qz277 qz557)

noncomputable abbrev qz305 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 6)))

noncomputable def ep109 := @Enclosure.Complex.IsNear.of_eq qz546 (Complex.mk (@HMul.hMul Real Real Real qz0 qz305 (Real.cos qz29)) (@HMul.hMul Real Real Real qz0 qz305 (@Neg.neg Real Real.instNeg (Real.sin qz29)))) Bool.false 409196007231 1099511627776 31899883941253 109024274475384832 Bool.true 92257445685 549755813888 15923920248695 54512137237692416 (BSN.cpow_neg_s_mk qz12 140505 1000 6 qz13 rfl)

noncomputable abbrev qz306 := (Real.sqrt (@Nat.cast Real Real.instNatCast 6))

noncomputable abbrev qz307 := (@Nat.cast Real Real.instNatCast 6)

noncomputable abbrev qz558 := (@HDiv.hDiv Real Real Real qz1 qz307 qz14)

noncomputable def ep110 := @Enclosure.Real.IsNear.inv_image qz306 2568477 1048576 1 1048576 214039 214040 524288 (@Enclosure.Real.IsNear.of_eq qz306 (Real.sqrt qz558) Bool.false 2568477 1048576 1 1048576 (BSN.sqrt_natCast_div_one 6) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz558) Bool.false 2568477 1048576 1 1048576 2568477 1048576 1 1048576 (BSN.sqrt_enclosure 6 1 1284238 1284239 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep111 := BSN.log_dyadic_bound 2 10 4 3 105000000 524288 198314 1434560 960 212580 12 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 2) (BSN.artanhQ 10) 0 3 1434560 105000000 960 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep112 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz557 140505 1000 0 1 4034681531866359 2251799813685248 250000000099157 49578500000000000000 113378585726976554259 450359962737049600 7025250002786410857 9915700000000000000000 qz18 (BSN.isNear_log_sfrac 6 1 4034681531866359 2251799813685248 250000000099157 49578500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz558) Bool.false 33845361775666394038272 18889465931478580854784 1000000000396628 198314000000000000000 4034681531866359 2251799813685248 250000000099157 49578500000000000000 (BSN.log_rat_reduce_isNear 6 1 2 12 8 212580 524288 24973259072661432 36028797018963968 198314 1000000000000000 rfl rfl rfl rfl (ep111 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep113 := nat_lit 684894372601442603443602826126117041

noncomputable def ep114 := BSN.cos_dyadic_bound_f 909716139 2147483648 2 1 1048576 397016 ep113 ep66 ep113 ep113 ep67 ep113 955889 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 909716139) qz15 0 1 ep113 ep66 ep113 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 909716139) qz16 0 1 ep113 ep67 ep113 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz308 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 131990045) qz17)

noncomputable def ep115 := @Enclosure.Real.IsNear.cos_image qz29 qz308 Bool.false 131990045 524288 93 131072 Bool.false 955889 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz29 Bool.false 113378585726976554259 450359962737049600 7025250002786410857 9915700000000000000000 131990045 524288 93 131072 (ep112 rfl) rfl) (Enclosure.sfrac_false_div 131990045 524288) (BSN.cos_reduce0 qz308 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 32007791133987795107840) qz19) 226375608064910080 72057594037927936 Bool.false 955889 1048576 40 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q0 131990045 524288 226375608064910080 72057594037927936 40 32007791133987795107840 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 955889 1048576 32007791133987795107840 75557863725914323419136 909716139 2147483648 397016 396628 (ep114 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep116 := BSN.sin_dyadic_bound_f 909716139 2147483648 2 1 1048576 397016 ep113 ep70 ep113 ep113 ep71 ep113 431030 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 909716139) qz20 0 1 ep113 ep70 ep113 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 909716139) qz21 0 1 ep113 ep71 ep113 rfl rfl rfl rfl) rfl rfl

noncomputable def ep117 := @Enclosure.Real.IsNear.sin_image qz29 qz308 Bool.false 131990045 524288 93 131072 Bool.false 431030 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz29 Bool.false 113378585726976554259 450359962737049600 7025250002786410857 9915700000000000000000 131990045 524288 93 131072 (ep112 rfl) rfl) (Enclosure.sfrac_false_div 131990045 524288) (BSN.sin_reduce0 qz308 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 32007791133987795107840) qz19) 226375608064910080 72057594037927936 Bool.false 431030 1048576 40 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q0 131990045 524288 226375608064910080 72057594037927936 40 32007791133987795107840 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 431030 1048576 32007791133987795107840 75557863725914323419136 909716139 2147483648 397016 396628 (ep116 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz309 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 6))) Bool.false 428079 1048576 1 1048576 428079 1048576 1 1048576 (ep110 rfl rfl) rfl)

noncomputable def ep118 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz305 (Real.cos qz29)) (@HMul.hMul Real Real Real qz0 qz305 (@Neg.neg Real Real.instNeg (Real.sin qz29))) Bool.false 409196007231 1099511627776 31899883941253 109024274475384832 Bool.true 92257445685 549755813888 15923920248695 54512137237692416 (@Enclosure.Real.IsNear.mulLit_ff qz305 (Real.cos qz29) 428079 1048576 1 1048576 955889 1048576 9287137 12996706304 409196007231 1099511627776 31899883941253 109024274475384832 qz309 (@Enclosure.Real.IsNear.recentre' (Real.cos qz29) Bool.false 955889 1048576 18574274 25993412608 955889 1048576 9287137 12996706304 (ep115 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz305 (@Neg.neg Real Real.instNeg (Real.sin qz29)) 428079 1048576 1 1048576 215515 524288 9287137 12996706304 92257445685 549755813888 15923920248695 54512137237692416 qz309 (@Enclosure.Real.IsNear.neg (Real.sin qz29) Bool.false 215515 524288 9287137 12996706304 (@Enclosure.Real.IsNear.recentre' (Real.sin qz29) Bool.false 431030 1048576 18574274 25993412608 215515 524288 9287137 12996706304 (ep117 rfl rfl) rfl)) rfl)

noncomputable def ep119 := @ep43 409196007231 1099511627776 31899883941253 109024274475384832 Bool.true 92257445685 549755813888 15923920248695 54512137237692416 Bool.false 163935880620556060459008 1192790518839 1099511627776 206047427058399 109024274475384832 Bool.false 7225561052818228379648 52572875959 549755813888 102819066322031 54512137237692416 (ep44 (BSN.head_sum_c_succ qz5 5 6 rfl rfl) (ep108 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep109 ep118) rfl rfl

noncomputable abbrev qz559 := (Real.log (Enclosure.sfrac Bool.false 7 1))

noncomputable abbrev qz30 := (@HMul.hMul Real Real Real qz267 qz277 qz559)

noncomputable abbrev qz310 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 7)))

noncomputable def ep120 := @Enclosure.Complex.IsNear.of_eq qz545 (Complex.mk (@HMul.hMul Real Real Real qz0 qz310 (Real.cos qz30)) (@HMul.hMul Real Real Real qz0 qz310 (@Neg.neg Real Real.instNeg (Real.sin qz30)))) Bool.true 206922471475 549755813888 14774705601819 54512137237692416 Bool.false 37896992825 1099511627776 29455352360793 109024274475384832 (BSN.cpow_neg_s_mk qz12 140505 1000 7 qz13 rfl)

noncomputable abbrev qz311 := (Real.sqrt (@Nat.cast Real Real.instNatCast 7))

noncomputable abbrev qz312 := (@Nat.cast Real Real.instNatCast 7)

noncomputable abbrev qz560 := (@HDiv.hDiv Real Real Real qz1 qz312 qz14)

noncomputable def ep121 := @Enclosure.Real.IsNear.inv_image qz311 2774271 1048576 1 1048576 198162 198163 524288 (@Enclosure.Real.IsNear.of_eq qz311 (Real.sqrt qz560) Bool.false 2774271 1048576 1 1048576 (BSN.sqrt_natCast_div_one 7) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz560) Bool.false 2774271 1048576 1 1048576 2774271 1048576 1 1048576 (BSN.sqrt_enclosure 7 1 1387135 1387136 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep122 := BSN.log_dyadic_bound 3 11 5 4 202569142545 524288 198314 5259111624 688905 293399 14 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 3) (BSN.artanhQ 11) 0 4 5259111624 202569142545 688905 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep123 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz559 140505 1000 0 1 4381796493761783 2251799813685248 250000000099157 49578500000000000000 123132863271199864083 450359962737049600 7025250002786410857 9915700000000000000000 qz18 (BSN.isNear_log_sfrac 7 1 4381796493761783 2251799813685248 250000000099157 49578500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz560) Bool.false 36757173121942042968064 18889465931478580854784 1000000000396628 198314000000000000000 4381796493761783 2251799813685248 250000000099157 49578500000000000000 (BSN.log_rat_reduce_isNear 7 1 2 14 8 293399 524288 24973259072661432 36028797018963968 198314 1000000000000000 rfl rfl rfl rfl (ep122 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep124 := nat_lit 1478974426122518620902701355332241

noncomputable def ep125 := BSN.cos_dyadic_bound_f 196105677 2147483648 2 1 1048576 397016 ep124 ep66 ep124 ep124 ep67 ep124 1044206 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 196105677) qz15 0 1 ep124 ep66 ep124 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 196105677) qz16 0 1 ep124 ep67 ep124 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz313 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 143345519) qz17)

noncomputable def ep126 := @Enclosure.Real.IsNear.cos_image qz30 qz313 Bool.false 143345519 524288 93 131072 Bool.true 1044206 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz30 Bool.false 123132863271199864083 450359962737049600 7025250002786410857 9915700000000000000000 143345519 524288 93 131072 (ep123 rfl) rfl) (Enclosure.sfrac_false_div 143345519 524288) (BSN.cos_reduce2 qz313 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 6899855118581113028608) qz19) 226375608064910080 72057594037927936 Bool.false 1044206 1048576 43 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q2 143345519 524288 226375608064910080 72057594037927936 43 6899855118581113028608 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1044206 1048576 6899855118581113028608 75557863725914323419136 196105677 2147483648 397016 396628 (ep125 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep127 := BSN.sin_dyadic_bound_f 196105677 2147483648 1 0 1048576 397016 0 1 1 0 1 1 95621 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 196105677) qz20 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 196105677) qz21 0 0 rfl) rfl rfl

noncomputable def ep128 := @Enclosure.Real.IsNear.sin_image qz30 qz313 Bool.false 143345519 524288 93 131072 Bool.true 95621 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz30 Bool.false 123132863271199864083 450359962737049600 7025250002786410857 9915700000000000000000 143345519 524288 93 131072 (ep123 rfl) rfl) (Enclosure.sfrac_false_div 143345519 524288) (BSN.sin_reduce2 qz313 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 6899855118581113028608) qz19) 226375608064910080 72057594037927936 Bool.false 95621 1048576 43 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q2 143345519 524288 226375608064910080 72057594037927936 43 6899855118581113028608 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 95621 1048576 6899855118581113028608 75557863725914323419136 196105677 2147483648 397016 396628 (ep127 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz314 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 7))) Bool.false 396325 1048576 1 1048576 396325 1048576 1 1048576 (ep121 rfl rfl) rfl)

noncomputable def ep129 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz310 (Real.cos qz30)) (@HMul.hMul Real Real Real qz0 qz310 (@Neg.neg Real Real.instNeg (Real.sin qz30))) Bool.true 206922471475 549755813888 14774705601819 54512137237692416 Bool.false 37896992825 1099511627776 29455352360793 109024274475384832 (@Enclosure.Real.IsNear.mulLit_ft qz310 (Real.cos qz30) 396325 1048576 1 1048576 522103 524288 9287137 12996706304 206922471475 549755813888 14774705601819 54512137237692416 qz314 (@Enclosure.Real.IsNear.recentre' (Real.cos qz30) Bool.true 1044206 1048576 18574274 25993412608 522103 524288 9287137 12996706304 (ep126 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz310 (@Neg.neg Real Real.instNeg (Real.sin qz30)) 396325 1048576 1 1048576 95621 1048576 9287137 12996706304 37896992825 1099511627776 29455352360793 109024274475384832 qz314 (@Enclosure.Real.IsNear.neg (Real.sin qz30) Bool.true 95621 1048576 9287137 12996706304 (@Enclosure.Real.IsNear.recentre' (Real.sin qz30) Bool.true 95621 1048576 18574274 25993412608 95621 1048576 9287137 12996706304 (ep128 rfl rfl) rfl)) rfl)

noncomputable def ep130 := @ep41 206922471475 549755813888 14774705601819 54512137237692416 Bool.false 37896992825 1099511627776 29455352360793 109024274475384832 Bool.false 428229859047314064146432 778945575889 1099511627776 235596838262037 109024274475384832 Bool.false 78638580556961398390784 143042744743 1099511627776 235093485004855 109024274475384832 (ep42 (BSN.head_sum_c_succ qz5 6 7 rfl rfl) (ep119 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep120 ep129) rfl rfl

noncomputable abbrev qz561 := (Real.log (Enclosure.sfrac Bool.false 8 1))

noncomputable abbrev qz31 := (@HMul.hMul Real Real Real qz267 qz277 qz561)

noncomputable abbrev qz315 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 8)))

noncomputable def ep131 := @Enclosure.Complex.IsNear.of_eq qz544 (Complex.mk (@HMul.hMul Real Real Real qz0 qz315 (Real.cos qz31)) (@HMul.hMul Real Real Real qz0 qz315 (@Neg.neg Real Real.instNeg (Real.sin qz31)))) Bool.true 48591558617 137438953472 3455998332883 13628034309423104 Bool.false 1483278727 1099511627776 27544410533045 109024274475384832 (BSN.cpow_neg_s_mk qz12 140505 1000 8 qz13 rfl)

noncomputable abbrev qz316 := (Real.sqrt (@Nat.cast Real Real.instNatCast 8))

noncomputable abbrev qz317 := (@Nat.cast Real Real.instNatCast 8)

noncomputable abbrev qz562 := (@HDiv.hDiv Real Real Real qz1 qz317 qz14)

noncomputable def ep132 := @Enclosure.Real.IsNear.inv_image qz316 2965821 1048576 1 1048576 185363 185364 524288 (@Enclosure.Real.IsNear.of_eq qz316 (Real.sqrt qz562) Bool.false 2965821 1048576 1 1048576 (BSN.sqrt_natCast_div_one 8) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz562) Bool.false 2965821 1048576 1 1048576 2965821 1048576 1 1048576 (BSN.sqrt_enclosure 8 1 1482910 1482911 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep133 := BSN.log_dyadic_bound 0 16 1 0 1 524288 198314 0 1 0 16 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 0) (BSN.artanhQ 16) 0 0 rfl) rfl rfl rfl

noncomputable def ep134 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz561 140505 1000 0 1 9364972152248037 4503599627370496 500000000297471 99157000000000000000 263165082450322087737 900719925474099200 14050500008359232571 19831400000000000000000 qz18 (BSN.isNear_log_sfrac 8 1 9364972152248037 4503599627370496 500000000297471 99157000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz562) Bool.false 39279540158062550581248 18889465931478580854784 1000000000594942 198314000000000000000 9364972152248037 4503599627370496 500000000297471 99157000000000000000 (BSN.log_rat_reduce_isNear 8 1 3 16 16 0 524288 24973259072661432 36028797018963968 198314 1000000000000000 rfl rfl rfl rfl (ep133 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep135 := BSN.cos_dyadic_bound_f 8195635 2147483648 1 0 1048576 397016 0 1 1 0 1 1 1048568 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 8195635) qz15 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 8195635) qz16 0 0 rfl) rfl rfl

noncomputable abbrev qz318 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 306364477) qz26)

noncomputable def ep136 := @Enclosure.Real.IsNear.cos_image qz31 qz318 Bool.false 306364477 1048576 93 131072 Bool.true 1048568 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz31 Bool.false 263165082450322087737 900719925474099200 14050500008359232571 19831400000000000000000 306364477 1048576 93 131072 (ep134 rfl) rfl) (Enclosure.sfrac_false_div 306364477 1048576) (BSN.cos_reduce2 qz318 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 576716593786272088064) qz27) 226375608064910080 72057594037927936 Bool.false 1048568 1048576 46 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q2 306364477 1048576 226375608064910080 72057594037927936 46 576716593786272088064 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1048568 1048576 576716593786272088064 151115727451828646838272 8195635 2147483648 397016 396628 (ep135 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep137 := BSN.sin_dyadic_bound_f 8195635 2147483648 1 0 1048576 397016 0 1 1 0 1 1 4001 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 8195635) qz20 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 8195635) qz21 0 0 rfl) rfl rfl

noncomputable def ep138 := @Enclosure.Real.IsNear.sin_image qz31 qz318 Bool.false 306364477 1048576 93 131072 Bool.true 4001 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz31 Bool.false 263165082450322087737 900719925474099200 14050500008359232571 19831400000000000000000 306364477 1048576 93 131072 (ep134 rfl) rfl) (Enclosure.sfrac_false_div 306364477 1048576) (BSN.sin_reduce2 qz318 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 576716593786272088064) qz27) 226375608064910080 72057594037927936 Bool.false 4001 1048576 46 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q2 306364477 1048576 226375608064910080 72057594037927936 46 576716593786272088064 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 4001 1048576 576716593786272088064 151115727451828646838272 8195635 2147483648 397016 396628 (ep137 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz319 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 8))) Bool.false 370727 1048576 1 1048576 370727 1048576 1 1048576 (ep132 rfl rfl) rfl)

noncomputable def ep139 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz315 (Real.cos qz31)) (@HMul.hMul Real Real Real qz0 qz315 (@Neg.neg Real Real.instNeg (Real.sin qz31))) Bool.true 48591558617 137438953472 3455998332883 13628034309423104 Bool.false 1483278727 1099511627776 27544410533045 109024274475384832 (@Enclosure.Real.IsNear.mulLit_ft qz315 (Real.cos qz31) 370727 1048576 1 1048576 131071 131072 9287137 12996706304 48591558617 137438953472 3455998332883 13628034309423104 qz319 (@Enclosure.Real.IsNear.recentre' (Real.cos qz31) Bool.true 1048568 1048576 18574274 25993412608 131071 131072 9287137 12996706304 (ep136 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz315 (@Neg.neg Real Real.instNeg (Real.sin qz31)) 370727 1048576 1 1048576 4001 1048576 9287137 12996706304 1483278727 1099511627776 27544410533045 109024274475384832 qz319 (@Enclosure.Real.IsNear.neg (Real.sin qz31) Bool.true 4001 1048576 9287137 12996706304 (@Enclosure.Real.IsNear.recentre' (Real.sin qz31) Bool.true 4001 1048576 18574274 25993412608 4001 1048576 9287137 12996706304 (ep138 rfl rfl) rfl)) rfl)

noncomputable def ep140 := @ep39 48591558617 137438953472 3455998332883 13628034309423104 Bool.false 1483278727 1099511627776 27544410533045 109024274475384832 Bool.false 53630481050677926690816 390213106953 1099511627776 263244824925101 109024274475384832 Bool.false 158908043321492079902720 72263011735 549755813888 65659473884475 27256068618846208 (ep40 (BSN.head_sum_c_succ qz5 7 8 rfl rfl) (ep130 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep131 ep139) rfl rfl

theorem EMRow49.d6 : Enclosure.Complex.IsNear qz3 Bool.false 390213106953 1099511627776 263244824925101 109024274475384832 Bool.false 72263011735 549755813888 65659473884475 27256068618846208 := ep38 (BSN.head_sum_c_succ qz5 8 9 rfl rfl) (ep140 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable abbrev qz32 := (BSN.headSumC qz271 17)

noncomputable abbrev qz563 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 16) qz7)

noncomputable def ep141 := @Enclosure.Complex.IsNear.of_eq qz32 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 16) qz563) Bool.true 130506235681 1099511627776 442561805923489 109024274475384832 Bool.false 44267444217 1099511627776 441569538056523 109024274475384832

noncomputable def ep142 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 16) qz563 Bool.true 405379424047 1099511627776 422981295727431 109024274475384832 Bool.false 45666239265 1099511627776 422092471020947 109024274475384832 Bool.false

noncomputable abbrev qz564 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 15) qz7)

noncomputable def ep143 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 16) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 15) qz564) Bool.true 405379424047 1099511627776 422981295727431 109024274475384832 Bool.false 45666239265 1099511627776 422092471020947 109024274475384832

noncomputable def ep144 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 15) qz564 Bool.true 34961937907 274877906944 100692175560509 27256068618846208 Bool.true 27385951605 549755813888 50242542735955 13628034309423104 Bool.true

noncomputable abbrev qz565 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 14) qz7)

noncomputable def ep145 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 15) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 14) qz565) Bool.true 34961937907 274877906944 100692175560509 27256068618846208 Bool.true 27385951605 549755813888 50242542735955 13628034309423104

noncomputable def ep146 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 14) qz565 Bool.true 54055623005 137438953472 23865241164589 6814017154711552 Bool.true 27602624603 1099511627776 381109413344223 109024274475384832 Bool.false

noncomputable abbrev qz566 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 13) qz7)

noncomputable def ep147 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 14) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 13) qz566) Bool.true 54055623005 137438953472 23865241164589 6814017154711552 Bool.true 27602624603 1099511627776 381109413344223 109024274475384832

noncomputable def ep148 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 13) qz566 Bool.true 120869482541 549755813888 180085729090099 54512137237692416 Bool.false 210358641979 1099511627776 359420901068381 109024274475384832 Bool.true

noncomputable abbrev qz567 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 12) qz7)

noncomputable def ep149 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 13) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 12) qz567) Bool.true 120869482541 549755813888 180085729090099 54512137237692416 Bool.false 210358641979 1099511627776 359420901068381 109024274475384832

noncomputable def ep150 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 12) qz567 Bool.false 47439284201 1099511627776 337587147265967 109024274475384832 Bool.false 79519074517 1099511627776 336888458486751 109024274475384832 Bool.true

noncomputable abbrev qz568 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 11) qz7)

noncomputable def ep151 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 12) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 11) qz568) Bool.false 47439284201 1099511627776 337587147265967 109024274475384832 Bool.false 79519074517 1099511627776 336888458486751 109024274475384832

noncomputable def ep152 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 11) qz568 Bool.false 286419198931 1099511627776 314022574204069 109024274475384832 Bool.true 37560662641 274877906944 156663388272751 54512137237692416 Bool.true

noncomputable abbrev qz569 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 10) qz7)

noncomputable def ep153 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 11) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 10) qz569) Bool.false 286419198931 1099511627776 314022574204069 109024274475384832 Bool.true 37560662641 274877906944 156663388272751 54512137237692416

noncomputable def ep154 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 10) qz569 Bool.false 316750515889 549755813888 144641305114459 54512137237692416 Bool.true 64791333165 549755813888 72171106101705 27256068618846208 Bool.true

noncomputable abbrev qz570 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 9) qz7)

noncomputable def ep155 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 10) (@HAdd.hAdd Complex Complex Complex qz4 qz3 qz570) Bool.false 316750515889 549755813888 144641305114459 54512137237692416 Bool.true 64791333165 549755813888 72171106101705 27256068618846208

noncomputable def ep156 := @Enclosure.Complex.IsNear.addLitP qz3 qz570 Bool.false 390213106953 1099511627776 263244824925101 109024274475384832 Bool.false 72263011735 549755813888 65659473884475 27256068618846208 Bool.false

noncomputable abbrev qz571 := (Real.log (Enclosure.sfrac Bool.false 9 1))

noncomputable abbrev qz33 := (@HMul.hMul Real Real Real qz267 qz277 qz571)

noncomputable abbrev qz320 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 9)))

noncomputable def ep157 := @Enclosure.Complex.IsNear.of_eq qz570 (Complex.mk (@HMul.hMul Real Real Real qz0 qz320 (Real.cos qz33)) (@HMul.hMul Real Real Real qz0 qz320 (@Neg.neg Real Real.instNeg (Real.sin qz33)))) Bool.false 243287924825 1099511627776 26037785303817 109024274475384832 Bool.true 34263586225 137438953472 3255816108615 13628034309423104 (BSN.cpow_neg_s_mk qz12 140505 1000 9 qz13 rfl)

noncomputable abbrev qz321 := (Real.sqrt (@Nat.cast Real Real.instNatCast 9))

noncomputable abbrev qz322 := (@Nat.cast Real Real.instNatCast 9)

noncomputable abbrev qz572 := (@HDiv.hDiv Real Real Real qz1 qz322 qz14)

noncomputable def ep158 := @Enclosure.Real.IsNear.inv_image qz321 3145729 1048576 1 1048576 174762 174763 524288 (@Enclosure.Real.IsNear.of_eq qz321 (Real.sqrt qz572) Bool.false 3145729 1048576 1 1048576 (BSN.sqrt_natCast_div_one 9) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz572) Bool.false 3145729 1048576 1 1048576 3145729 1048576 1 1048576 (BSN.sqrt_enclosure 9 1 1572864 1572865 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep159 := BSN.log_dyadic_bound 1 17 3 2 1252815 524288 198314 1448 3 61752 18 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 1) (BSN.artanhQ 17) 0 2 1448 1252815 3 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep160 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz571 140505 1000 0 1 9895417793173221 4503599627370496 500000000297471 99157000000000000000 278071135405960683321 900719925474099200 14050500008359232571 19831400000000000000000 qz18 (BSN.isNear_log_sfrac 9 1 9895417793173221 4503599627370496 500000000297471 99157000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz572) Bool.false 41504390431577613533184 18889465931478580854784 1000000000594942 198314000000000000000 9895417793173221 4503599627370496 500000000297471 99157000000000000000 (BSN.log_rat_reduce_isNear 9 1 3 18 16 61752 524288 24973259072661432 36028797018963968 198314 1000000000000000 rfl rfl rfl rfl (ep159 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep161 := nat_lit 387341948325605225621175613405735590398455435318103163575628203427195184251136

noncomputable def ep162 := nat_lit 117454092660136126482648732417711564496262112698360724848363723582184653056

noncomputable def ep163 := nat_lit 1161790936791495404610561542752371348066373781728912769277187882834421183447296

noncomputable def ep164 := BSN.cos_dyadic_bound_f 1814402014 2147483648 3 2 1048576 397016 ep161 ep102 ep162 ep163 ep104 ep162 696053 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1814402014) qz15 0 2 ep161 ep102 ep162 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1814402014) qz16 0 2 ep163 ep104 ep162 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz323 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 323717407) qz26)

noncomputable def ep165 := @Enclosure.Real.IsNear.cos_image qz33 qz323 Bool.false 323717407 1048576 93 131072 Bool.false 696053 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz33 Bool.false 278071135405960683321 900719925474099200 14050500008359232571 19831400000000000000000 323717407 1048576 93 131072 (ep160 rfl) rfl) (Enclosure.sfrac_false_div 323717407 1048576) (BSN.cos_reduce0 qz323 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 127677191188236388532224) qz27) 226375608064910080 72057594037927936 Bool.false 696053 1048576 49 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q0 323717407 1048576 226375608064910080 72057594037927936 49 127677191188236388532224 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 696053 1048576 127677191188236388532224 151115727451828646838272 1814402014 2147483648 397016 396628 (ep164 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep166 := nat_lit 10837623939782009546393303465180390416

noncomputable def ep167 := BSN.sin_dyadic_bound_f 1814402014 2147483648 2 1 1048576 397016 ep166 ep70 ep166 ep166 ep71 ep166 784232 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1814402014) qz20 0 1 ep166 ep70 ep166 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1814402014) qz21 0 1 ep166 ep71 ep166 rfl rfl rfl rfl) rfl rfl

noncomputable def ep168 := @Enclosure.Real.IsNear.sin_image qz33 qz323 Bool.false 323717407 1048576 93 131072 Bool.false 784232 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz33 Bool.false 278071135405960683321 900719925474099200 14050500008359232571 19831400000000000000000 323717407 1048576 93 131072 (ep160 rfl) rfl) (Enclosure.sfrac_false_div 323717407 1048576) (BSN.sin_reduce0 qz323 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 127677191188236388532224) qz27) 226375608064910080 72057594037927936 Bool.false 784232 1048576 49 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q0 323717407 1048576 226375608064910080 72057594037927936 49 127677191188236388532224 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 784232 1048576 127677191188236388532224 151115727451828646838272 1814402014 2147483648 397016 396628 (ep167 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz324 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 9))) Bool.false 349525 1048576 1 1048576 349525 1048576 1 1048576 (ep158 rfl rfl) rfl)

noncomputable def ep169 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz320 (Real.cos qz33)) (@HMul.hMul Real Real Real qz0 qz320 (@Neg.neg Real Real.instNeg (Real.sin qz33))) Bool.false 243287924825 1099511627776 26037785303817 109024274475384832 Bool.true 34263586225 137438953472 3255816108615 13628034309423104 (@Enclosure.Real.IsNear.mulLit_ff qz320 (Real.cos qz33) 349525 1048576 1 1048576 696053 1048576 9287137 12996706304 243287924825 1099511627776 26037785303817 109024274475384832 qz324 (@Enclosure.Real.IsNear.recentre' (Real.cos qz33) Bool.false 696053 1048576 18574274 25993412608 696053 1048576 9287137 12996706304 (ep165 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz320 (@Neg.neg Real Real.instNeg (Real.sin qz33)) 349525 1048576 1 1048576 98029 131072 9287137 12996706304 34263586225 137438953472 3255816108615 13628034309423104 qz324 (@Enclosure.Real.IsNear.neg (Real.sin qz33) Bool.false 98029 131072 9287137 12996706304 (@Enclosure.Real.IsNear.recentre' (Real.sin qz33) Bool.false 784232 1048576 18574274 25993412608 98029 131072 9287137 12996706304 (ep168 rfl rfl) rfl)) rfl)

noncomputable def ep170 := @ep156 243287924825 1099511627776 26037785303817 109024274475384832 Bool.true 34263586225 137438953472 3255816108615 13628034309423104 Bool.false 696541750648004283465728 316750515889 549755813888 144641305114459 54512137237692416 Bool.true 8904853024253285498880 64791333165 549755813888 72171106101705 27256068618846208 EMRow49.d6 (ep157 ep169) rfl rfl

noncomputable abbrev qz573 := (@Nat.cast Real Real.instNatCast 10)

noncomputable abbrev qz34 := (@Inv.inv Real Real.instInv (Real.sqrt qz573))

noncomputable abbrev qz574 := (Real.log (Enclosure.sfrac Bool.false 10 1))

noncomputable abbrev qz35 := (@HMul.hMul Real Real Real qz267 qz277 qz574)

noncomputable def ep171 := @Enclosure.Complex.IsNear.of_eq qz569 (Complex.mk (@HMul.hMul Real Real Real qz0 qz34 (Real.cos qz35)) (@HMul.hMul Real Real Real qz0 qz34 (@Neg.neg Real Real.instNeg (Real.sin qz35)))) Bool.true 347081832847 1099511627776 24739963975151 109024274475384832 Bool.true 10329992117 549755813888 12321176069341 54512137237692416 (BSN.cpow_neg_s_mk qz12 140505 1000 10 qz13 rfl)

noncomputable abbrev qz575 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 10) qz14)

noncomputable def ep172 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz573) 3315889 1048576 1 1048576 165794 165795 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz573) (Real.sqrt qz575) Bool.false 3315889 1048576 1 1048576 (BSN.sqrt_natCast_div_one 10) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz575) Bool.false 3315889 1048576 1 1048576 3315889 1048576 1 1048576 (BSN.sqrt_enclosure 10 1 1657944 1657945 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep173 := BSN.log_dyadic_bound 2 18 3 2 1574640 524288 198314 6528 48 116991 20 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 2) (BSN.artanhQ 18) 0 2 6528 1574640 48 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep174 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz574 140505 1000 0 1 10369917190100709 4503599627370496 500000000297471 99157000000000000000 291405042959020023609 900719925474099200 14050500008359232571 19831400000000000000000 qz18 (BSN.isNear_log_sfrac 10 1 10369917190100709 4503599627370496 500000000297471 99157000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz575) Bool.false 43494585150108164161536 18889465931478580854784 1000000000594942 198314000000000000000 10369917190100709 4503599627370496 500000000297471 99157000000000000000 (BSN.log_rat_reduce_isNear 10 1 3 20 16 116991 524288 24973259072661432 36028797018963968 198314 1000000000000000 rfl rfl rfl rfl (ep173 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep175 := nat_lit 7148563840838301694513845912881194253049568766532277998265476822923802982297185

noncomputable def ep176 := nat_lit 12312260794687606127261522421001444671012359566905336521983480281841537724001

noncomputable def ep177 := nat_lit 18702494970432724504282601592673887371376755330190500402993037472915550083034721

noncomputable def ep178 := BSN.sin_dyadic_bound_f 3245579307 2147483648 3 2 1048576 397016 ep175 ep95 ep176 ep177 ep98 ep176 1046723 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3245579307) qz20 0 2 ep175 ep95 ep176 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3245579307) qz21 0 2 ep177 ep98 ep176 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz325 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 169620059) qz17)

noncomputable def ep179 := @Enclosure.Real.IsNear.cos_image qz35 qz325 Bool.false 169620059 524288 93 131072 Bool.true 1046723 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz35 Bool.false 291405042959020023609 900719925474099200 14050500008359232571 19831400000000000000000 169620059 524288 93 131072 (ep174 rfl) rfl) (Enclosure.sfrac_false_div 169620059 524288) (BSN.cos_reduce1 qz325 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 114193669989976399413248) qz19) 226375608064910080 72057594037927936 Bool.false 1046723 1048576 51 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q1 169620059 524288 226375608064910080 72057594037927936 51 114193669989976399413248 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1046723 1048576 114193669989976399413248 75557863725914323419136 3245579307 2147483648 397016 396628 (ep178 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep180 := nat_lit 3976896471930028766342030628232219671547988141214334593046146448416264562486881

noncomputable def ep181 := nat_lit 11906064894200711086771568839854656125301939704509193106094472384685110612012641

noncomputable def ep182 := BSN.cos_dyadic_bound_f 3245579307 2147483648 3 2 1048576 397016 ep180 ep102 ep176 ep181 ep104 ep176 62306 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3245579307) qz15 0 2 ep180 ep102 ep176 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3245579307) qz16 0 2 ep181 ep104 ep176 rfl rfl rfl rfl) rfl rfl

noncomputable def ep183 := @Enclosure.Real.IsNear.sin_image qz35 qz325 Bool.false 169620059 524288 93 131072 Bool.false 62306 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz35 Bool.false 291405042959020023609 900719925474099200 14050500008359232571 19831400000000000000000 169620059 524288 93 131072 (ep174 rfl) rfl) (Enclosure.sfrac_false_div 169620059 524288) (BSN.sin_reduce1 qz325 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 114193669989976399413248) qz19) 226375608064910080 72057594037927936 Bool.false 62306 1048576 51 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q1 169620059 524288 226375608064910080 72057594037927936 51 114193669989976399413248 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 62306 1048576 114193669989976399413248 75557863725914323419136 3245579307 2147483648 397016 396628 (ep182 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz326 := (@Enclosure.Real.IsNear.recentre' qz34 Bool.false 331589 1048576 1 1048576 331589 1048576 1 1048576 (ep172 rfl rfl) rfl)

noncomputable def ep184 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz34 (Real.cos qz35)) (@HMul.hMul Real Real Real qz0 qz34 (@Neg.neg Real Real.instNeg (Real.sin qz35))) Bool.true 347081832847 1099511627776 24739963975151 109024274475384832 Bool.true 10329992117 549755813888 12321176069341 54512137237692416 (@Enclosure.Real.IsNear.mulLit_ft qz34 (Real.cos qz35) 331589 1048576 1 1048576 1046723 1048576 9287137 12996706304 347081832847 1099511627776 24739963975151 109024274475384832 qz326 (@Enclosure.Real.IsNear.recentre' (Real.cos qz35) Bool.true 1046723 1048576 18574274 25993412608 1046723 1048576 9287137 12996706304 (ep179 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz34 (@Neg.neg Real Real.instNeg (Real.sin qz35)) 331589 1048576 1 1048576 31153 524288 9287137 12996706304 10329992117 549755813888 12321176069341 54512137237692416 qz326 (@Enclosure.Real.IsNear.neg (Real.sin qz35) Bool.false 31153 524288 9287137 12996706304 (@Enclosure.Real.IsNear.recentre' (Real.sin qz35) Bool.false 62306 1048576 18574274 25993412608 31153 524288 9287137 12996706304 (ep183 rfl rfl) rfl)) rfl)

noncomputable def ep185 := @ep154 347081832847 1099511627776 24739963975151 109024274475384832 Bool.true 10329992117 549755813888 12321176069341 54512137237692416 Bool.false 157460619821460884553728 286419198931 1099511627776 314022574204069 109024274475384832 Bool.true 41298385320751101116416 37560662641 274877906944 156663388272751 54512137237692416 (ep155 (BSN.head_sum_c_succ qz5 9 10 rfl rfl) (ep170 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep171 ep184) rfl rfl

noncomputable abbrev qz576 := (@Nat.cast Real Real.instNatCast 11)

noncomputable abbrev qz36 := (@Inv.inv Real Real.instInv (Real.sqrt qz576))

noncomputable abbrev qz577 := (Real.log (Enclosure.sfrac Bool.false 11 1))

noncomputable abbrev qz37 := (@HMul.hMul Real Real Real qz267 qz277 qz577)

noncomputable def ep186 := @Enclosure.Complex.IsNear.of_eq qz568 (Complex.mk (@HMul.hMul Real Real Real qz0 qz36 (Real.cos qz37)) (@HMul.hMul Real Real Real qz0 qz36 (@Neg.neg Real Real.instNeg (Real.sin qz37)))) Bool.true 119489957365 549755813888 11782286530949 54512137237692416 Bool.false 229761725081 1099511627776 23561681941249 109024274475384832 (BSN.cpow_neg_s_mk qz12 140505 1000 11 qz13 rfl)

noncomputable abbrev qz578 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 11) qz14)

noncomputable def ep187 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz576) 3477733 1048576 1 1048576 158078 158079 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz576) (Real.sqrt qz578) Bool.false 3477733 1048576 1 1048576 (BSN.sqrt_natCast_div_one 11) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz578) Bool.false 3477733 1048576 1 1048576 3477733 1048576 1 1048576 (BSN.sqrt_enclosure 11 1 1738866 1738867 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep188 := BSN.log_dyadic_bound 3 19 4 3 4939817505 524288 198314 41676111 10935 166961 22 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 3) (BSN.artanhQ 19) 0 3 41676111 4939817505 10935 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep189 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz577 140505 1000 0 1 10799156221662949 4503599627370496 500000000297471 99157000000000000000 303467088984950529849 900719925474099200 14050500008359232571 19831400000000000000000 qz18 (BSN.isNear_log_sfrac 11 1 10799156221662949 4503599627370496 500000000297471 99157000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz578) Bool.false 45294944137145793642496 18889465931478580854784 1000000000594942 198314000000000000000 10799156221662949 4503599627370496 500000000297471 99157000000000000000 (BSN.log_rat_reduce_isNear 11 1 3 22 16 166961 524288 24973259072661432 36028797018963968 198314 1000000000000000 rfl rfl rfl rfl (ep188 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep190 := nat_lit 261307294027465847800207803165383731147215867971873991569471830589803495161856

noncomputable def ep191 := nat_lit 53464787036944863436599479218579017325875759598243520424500867603655294976

noncomputable def ep192 := nat_lit 783814952508323653673750210537714035406995852396425487667566490034203174895616

noncomputable def ep193 := BSN.cos_dyadic_bound_f 1644403832 2147483648 3 2 1048576 397016 ep190 ep102 ep191 ep192 ep104 ep191 755890 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1644403832) qz15 0 2 ep190 ep102 ep191 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1644403832) qz16 0 2 ep192 ep104 ep191 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz327 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 88320547) qz24)

noncomputable def ep194 := @Enclosure.Real.IsNear.cos_image qz37 qz327 Bool.false 88320547 262144 93 131072 Bool.true 755890 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz37 Bool.false 303467088984950529849 900719925474099200 14050500008359232571 19831400000000000000000 88320547 262144 93 131072 (ep189 rfl) rfl) (Enclosure.sfrac_false_div 88320547 262144) (BSN.cos_reduce2 qz327 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 28928658145961473736704) qz291) 226375608064910080 72057594037927936 Bool.false 755890 1048576 53 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q2 88320547 262144 226375608064910080 72057594037927936 53 28928658145961473736704 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 755890 1048576 28928658145961473736704 37778931862957161709568 1644403832 2147483648 397016 396628 (ep193 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep195 := nat_lit 7311961914352731599339882696591282176

noncomputable def ep196 := BSN.sin_dyadic_bound_f 1644403832 2147483648 2 1 1048576 397016 ep195 ep70 ep195 ep195 ep71 ep195 726733 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1644403832) qz20 0 1 ep195 ep70 ep195 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1644403832) qz21 0 1 ep195 ep71 ep195 rfl rfl rfl rfl) rfl rfl

noncomputable def ep197 := @Enclosure.Real.IsNear.sin_image qz37 qz327 Bool.false 88320547 262144 93 131072 Bool.true 726733 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz37 Bool.false 303467088984950529849 900719925474099200 14050500008359232571 19831400000000000000000 88320547 262144 93 131072 (ep189 rfl) rfl) (Enclosure.sfrac_false_div 88320547 262144) (BSN.sin_reduce2 qz327 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 28928658145961473736704) qz291) 226375608064910080 72057594037927936 Bool.false 726733 1048576 53 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q2 88320547 262144 226375608064910080 72057594037927936 53 28928658145961473736704 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 726733 1048576 28928658145961473736704 37778931862957161709568 1644403832 2147483648 397016 396628 (ep196 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz328 := (@Enclosure.Real.IsNear.recentre' qz36 Bool.false 316157 1048576 1 1048576 316157 1048576 1 1048576 (ep187 rfl rfl) rfl)

noncomputable def ep198 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz36 (Real.cos qz37)) (@HMul.hMul Real Real Real qz0 qz36 (@Neg.neg Real Real.instNeg (Real.sin qz37))) Bool.true 119489957365 549755813888 11782286530949 54512137237692416 Bool.false 229761725081 1099511627776 23561681941249 109024274475384832 (@Enclosure.Real.IsNear.mulLit_ft qz36 (Real.cos qz37) 316157 1048576 1 1048576 377945 524288 9287137 12996706304 119489957365 549755813888 11782286530949 54512137237692416 qz328 (@Enclosure.Real.IsNear.recentre' (Real.cos qz37) Bool.true 755890 1048576 18574274 25993412608 377945 524288 9287137 12996706304 (ep194 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz36 (@Neg.neg Real Real.instNeg (Real.sin qz37)) 316157 1048576 1 1048576 726733 1048576 9287137 12996706304 229761725081 1099511627776 23561681941249 109024274475384832 qz328 (@Enclosure.Real.IsNear.neg (Real.sin qz37) Bool.true 726733 1048576 9287137 12996706304 (@Enclosure.Real.IsNear.recentre' (Real.sin qz37) Bool.true 726733 1048576 18574274 25993412608 726733 1048576 9287137 12996706304 (ep197 rfl rfl) rfl)) rfl)

noncomputable def ep199 := @ep152 119489957365 549755813888 11782286530949 54512137237692416 Bool.false 229761725081 1099511627776 23561681941249 109024274475384832 Bool.false 26080022296184894783488 47439284201 1099511627776 337587147265967 109024274475384832 Bool.false 21858036765356927746048 79519074517 1099511627776 336888458486751 109024274475384832 (ep153 (BSN.head_sum_c_succ qz5 10 11 rfl rfl) (ep185 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep186 ep198) rfl rfl

noncomputable abbrev qz579 := (@Nat.cast Real Real.instNatCast 12)

noncomputable abbrev qz38 := (@Inv.inv Real Real.instInv (Real.sqrt qz579))

noncomputable abbrev qz580 := (Real.log (Enclosure.sfrac Bool.false 12 1))

noncomputable abbrev qz39 := (@HMul.hMul Real Real Real qz267 qz277 qz580)

noncomputable def ep200 := @Enclosure.Complex.IsNear.of_eq qz567 (Complex.mk (@HMul.hMul Real Real Real qz0 qz38 (Real.cos qz39)) (@HMul.hMul Real Real Real qz0 qz38 (@Neg.neg Real Real.instNeg (Real.sin qz39)))) Bool.true 289178249283 1099511627776 22584310914231 109024274475384832 Bool.false 65419783731 549755813888 11266221290815 54512137237692416 (BSN.cpow_neg_s_mk qz12 140505 1000 12 qz13 rfl)

noncomputable abbrev qz581 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 12) qz14)

noncomputable def ep201 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz579) 3632373 1048576 1 1048576 151348 151349 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz579) (Real.sqrt qz581) Bool.false 3632373 1048576 1 1048576 (BSN.sqrt_natCast_div_one 12) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz581) Bool.false 3632373 1048576 1 1048576 3632373 1048576 1 1048576 (BSN.sqrt_enclosure 12 1 1816186 1816187 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep202 := BSN.log_dyadic_bound 4 20 4 3 6720000000 524288 198314 91811840 61440 212580 24 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 4) (BSN.artanhQ 20) 0 3 91811840 6720000000 61440 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep203 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz580 140505 1000 0 1 11191020447815397 4503599627370496 500000000297471 99157000000000000000 314478865604060471097 900719925474099200 14050500008359232571 19831400000000000000000 qz18 (BSN.isNear_log_sfrac 12 1 11191020447815397 4503599627370496 500000000297471 99157000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz581) Bool.false 46938541828353910898688 18889465931478580854784 1000000000594942 198314000000000000000 11191020447815397 4503599627370496 500000000297471 99157000000000000000 (BSN.log_rat_reduce_isNear 12 1 3 24 16 212580 524288 24973259072661432 36028797018963968 198314 1000000000000000 rfl rfl rfl rfl (ep202 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep204 := nat_lit 693162608514451336605636794496714721

noncomputable def ep205 := BSN.cos_dyadic_bound_f 912449383 2147483648 2 1 1048576 397016 ep204 ep66 ep204 ep204 ep67 ep204 955339 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 912449383) qz15 0 1 ep204 ep66 ep204 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 912449383) qz16 0 1 ep204 ep67 ep204 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz329 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 366101583) qz26)

noncomputable def ep206 := @Enclosure.Real.IsNear.cos_image qz39 qz329 Bool.false 366101583 1048576 93 131072 Bool.true 955339 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz39 Bool.false 314478865604060471097 900719925474099200 14050500008359232571 19831400000000000000000 366101583 1048576 93 131072 (ep203 rfl) rfl) (Enclosure.sfrac_false_div 366101583 1048576) (BSN.cos_reduce2 qz329 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 64207917209363064815616) qz27) 226375608064910080 72057594037927936 Bool.false 955339 1048576 55 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q2 366101583 1048576 226375608064910080 72057594037927936 55 64207917209363064815616 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 955339 1048576 64207917209363064815616 151115727451828646838272 912449383 2147483648 397016 396628 (ep205 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep207 := BSN.sin_dyadic_bound_f 912449383 2147483648 2 1 1048576 397016 ep204 ep70 ep204 ep204 ep71 ep204 432246 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 912449383) qz20 0 1 ep204 ep70 ep204 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 912449383) qz21 0 1 ep204 ep71 ep204 rfl rfl rfl rfl) rfl rfl

noncomputable def ep208 := @Enclosure.Real.IsNear.sin_image qz39 qz329 Bool.false 366101583 1048576 93 131072 Bool.true 432246 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz39 Bool.false 314478865604060471097 900719925474099200 14050500008359232571 19831400000000000000000 366101583 1048576 93 131072 (ep203 rfl) rfl) (Enclosure.sfrac_false_div 366101583 1048576) (BSN.sin_reduce2 qz329 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 64207917209363064815616) qz27) 226375608064910080 72057594037927936 Bool.false 432246 1048576 55 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q2 366101583 1048576 226375608064910080 72057594037927936 55 64207917209363064815616 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 432246 1048576 64207917209363064815616 151115727451828646838272 912449383 2147483648 397016 396628 (ep207 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz330 := (@Enclosure.Real.IsNear.recentre' qz38 Bool.false 302697 1048576 1 1048576 302697 1048576 1 1048576 (ep201 rfl rfl) rfl)

noncomputable def ep209 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz38 (Real.cos qz39)) (@HMul.hMul Real Real Real qz0 qz38 (@Neg.neg Real Real.instNeg (Real.sin qz39))) Bool.true 289178249283 1099511627776 22584310914231 109024274475384832 Bool.false 65419783731 549755813888 11266221290815 54512137237692416 (@Enclosure.Real.IsNear.mulLit_ft qz38 (Real.cos qz39) 302697 1048576 1 1048576 955339 1048576 9287137 12996706304 289178249283 1099511627776 22584310914231 109024274475384832 qz330 (@Enclosure.Real.IsNear.recentre' (Real.cos qz39) Bool.true 955339 1048576 18574274 25993412608 955339 1048576 9287137 12996706304 (ep206 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz38 (@Neg.neg Real Real.instNeg (Real.sin qz39)) 302697 1048576 1 1048576 216123 524288 9287137 12996706304 65419783731 549755813888 11266221290815 54512137237692416 qz330 (@Enclosure.Real.IsNear.neg (Real.sin qz39) Bool.true 216123 524288 9287137 12996706304 (@Enclosure.Real.IsNear.recentre' (Real.sin qz39) Bool.true 432246 1048576 18574274 25993412608 216123 524288 9287137 12996706304 (ep208 rfl rfl) rfl)) rfl)

noncomputable def ep210 := @ep150 289178249283 1099511627776 22584310914231 109024274475384832 Bool.false 65419783731 549755813888 11266221290815 54512137237692416 Bool.true 265794802994195445317632 120869482541 549755813888 180085729090099 54512137237692416 Bool.false 115645886429539548004352 210358641979 1099511627776 359420901068381 109024274475384832 (ep151 (BSN.head_sum_c_succ qz5 11 12 rfl rfl) (ep199 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep200 ep209) rfl rfl

noncomputable abbrev qz582 := (@Nat.cast Real Real.instNatCast 13)

noncomputable abbrev qz40 := (@Inv.inv Real Real.instInv (Real.sqrt qz582))

noncomputable abbrev qz583 := (Real.log (Enclosure.sfrac Bool.false 13 1))

noncomputable abbrev qz41 := (@HMul.hMul Real Real Real qz267 qz277 qz583)

noncomputable def ep211 := @Enclosure.Complex.IsNear.of_eq qz566 (Complex.mk (@HMul.hMul Real Real Real qz0 qz40 (Real.cos qz41)) (@HMul.hMul Real Real Real qz0 qz40 (@Neg.neg Real Real.instNeg (Real.sin qz41)))) Bool.true 95353009479 549755813888 10836200226613 54512137237692416 Bool.true 118980633291 549755813888 10844256137921 54512137237692416 (BSN.cpow_neg_s_mk qz12 140505 1000 13 qz13 rfl)

noncomputable abbrev qz584 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 13) qz14)

noncomputable def ep212 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz582) 3780695 1048576 1 1048576 145411 145412 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz582) (Real.sqrt qz584) Bool.false 3780695 1048576 1 1048576 (BSN.sqrt_natCast_div_one 13) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz584) Bool.false 3780695 1048576 1 1048576 3780695 1048576 1 1048576 (BSN.sqrt_enclosure 13 1 1890347 1890348 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep213 := BSN.log_dyadic_bound 5 21 5 4 35742602096145 524288 198314 699352521000 41015625 254545 26 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 5) (BSN.artanhQ 21) 0 4 699352521000 35742602096145 41015625 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep214 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz583 140505 1000 0 1 11551497052968677 4503599627370496 500000000297471 99157000000000000000 324608618685472792377 900719925474099200 14050500008359232571 19831400000000000000000 qz18 (BSN.isNear_log_sfrac 13 1 11551497052968677 4503599627370496 500000000297471 99157000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz584) Bool.false 48450490295254733815808 18889465931478580854784 1000000000594942 198314000000000000000 11551497052968677 4503599627370496 500000000297471 99157000000000000000 (BSN.log_rat_reduce_isNear 13 1 3 26 16 254545 524288 24973259072661432 36028797018963968 198314 1000000000000000 rfl rfl rfl rfl (ep213 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep215 := nat_lit 4430849908765804788943167700380160000

noncomputable def ep216 := BSN.sin_dyadic_bound_f 1450847480 2147483648 2 1 1048576 397016 ep215 ep70 ep215 ep215 ep71 ep215 655746 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1450847480) qz20 0 1 ep215 ep70 ep215 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1450847480) qz21 0 1 ep215 ep71 ep215 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz585 := (@Nat.cast Real Real.instNatCast 131072)

noncomputable abbrev qz331 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 47236771) qz585)

noncomputable abbrev qz332 := (@Nat.cast Real Real.instNatCast 18889465931478580854784)

noncomputable def ep217 := @Enclosure.Real.IsNear.cos_image qz41 qz331 Bool.false 47236771 131072 93 131072 Bool.true 655746 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz41 Bool.false 324608618685472792377 900719925474099200 14050500008359232571 19831400000000000000000 47236771 131072 93 131072 (ep214 rfl) rfl) (Enclosure.sfrac_false_div 47236771 131072) (BSN.cos_reduce1 qz331 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 12761789396122727350272) qz332) 226375608064910080 72057594037927936 Bool.false 655746 1048576 57 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q1 47236771 131072 226375608064910080 72057594037927936 57 12761789396122727350272 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 655746 1048576 12761789396122727350272 18889465931478580854784 1450847480 2147483648 397016 396628 (ep216 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep218 := nat_lit 158332342345670501471211040996968488251979380019369907226505476840672460800000

noncomputable def ep219 := nat_lit 19632430914009940621856045019684296628616277207452559265808521625600000000

noncomputable def ep220 := nat_lit 474957762175183484532389410900866096162680907503694816560984813478766182400000

noncomputable def ep221 := BSN.cos_dyadic_bound_f 1450847480 2147483648 3 2 1048576 397016 ep218 ep102 ep219 ep220 ep104 ep219 818234 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1450847480) qz15 0 2 ep218 ep102 ep219 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1450847480) qz16 0 2 ep220 ep104 ep219 rfl rfl rfl rfl) rfl rfl

noncomputable def ep222 := @Enclosure.Real.IsNear.sin_image qz41 qz331 Bool.false 47236771 131072 93 131072 Bool.false 818234 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz41 Bool.false 324608618685472792377 900719925474099200 14050500008359232571 19831400000000000000000 47236771 131072 93 131072 (ep214 rfl) rfl) (Enclosure.sfrac_false_div 47236771 131072) (BSN.sin_reduce1 qz331 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 12761789396122727350272) qz332) 226375608064910080 72057594037927936 Bool.false 818234 1048576 57 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q1 47236771 131072 226375608064910080 72057594037927936 57 12761789396122727350272 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 818234 1048576 12761789396122727350272 18889465931478580854784 1450847480 2147483648 397016 396628 (ep221 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz333 := (@Enclosure.Real.IsNear.recentre' qz40 Bool.false 290823 1048576 1 1048576 290823 1048576 1 1048576 (ep212 rfl rfl) rfl)

noncomputable def ep223 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz40 (Real.cos qz41)) (@HMul.hMul Real Real Real qz0 qz40 (@Neg.neg Real Real.instNeg (Real.sin qz41))) Bool.true 95353009479 549755813888 10836200226613 54512137237692416 Bool.true 118980633291 549755813888 10844256137921 54512137237692416 (@Enclosure.Real.IsNear.mulLit_ft qz40 (Real.cos qz41) 290823 1048576 1 1048576 327873 524288 9287137 12996706304 95353009479 549755813888 10836200226613 54512137237692416 qz333 (@Enclosure.Real.IsNear.recentre' (Real.cos qz41) Bool.true 655746 1048576 18574274 25993412608 327873 524288 9287137 12996706304 (ep217 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz40 (@Neg.neg Real Real.instNeg (Real.sin qz41)) 290823 1048576 1 1048576 409117 524288 9287137 12996706304 118980633291 549755813888 10844256137921 54512137237692416 qz333 (@Enclosure.Real.IsNear.neg (Real.sin qz41) Bool.false 409117 524288 9287137 12996706304 (@Enclosure.Real.IsNear.recentre' (Real.sin qz41) Bool.false 818234 1048576 18574274 25993412608 409117 524288 9287137 12996706304 (ep222 rfl rfl) rfl)) rfl)

noncomputable def ep224 := @ep148 95353009479 549755813888 10836200226613 54512137237692416 Bool.true 118980633291 549755813888 10844256137921 54512137237692416 Bool.true 118869572081346685173760 54055623005 137438953472 23865241164589 6814017154711552 Bool.true 15174703354067197886464 27602624603 1099511627776 381109413344223 109024274475384832 (ep149 (BSN.head_sum_c_succ qz5 12 13 rfl rfl) (ep210 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep211 ep223) rfl rfl

noncomputable abbrev qz586 := (@Nat.cast Real Real.instNatCast 14)

noncomputable abbrev qz42 := (@Inv.inv Real Real.instInv (Real.sqrt qz586))

noncomputable abbrev qz587 := (Real.log (Enclosure.sfrac Bool.false 14 1))

noncomputable abbrev qz43 := (@HMul.hMul Real Real Real qz267 qz277 qz587)

noncomputable def ep225 := @Enclosure.Complex.IsNear.of_eq qz565 (Complex.mk (@HMul.hMul Real Real Real qz0 qz42 (Real.cos qz43)) (@HMul.hMul Real Real Real qz0 qz42 (@Neg.neg Real Real.instNeg (Real.sin qz43)))) Bool.false 73149308103 274877906944 5231210902153 27256068618846208 Bool.true 27169278607 1099511627776 20830928543417 109024274475384832 (BSN.cpow_neg_s_mk qz12 140505 1000 14 qz13 rfl)

noncomputable abbrev qz588 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 14) qz14)

noncomputable def ep226 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz586) 3923413 1048576 1 1048576 140121 140122 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz586) (Real.sqrt qz588) Bool.false 3923413 1048576 1 1048576 (BSN.sqrt_natCast_div_one 14) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz588) Bool.false 3923413 1048576 1 1048576 3923413 1048576 1 1048576 (BSN.sqrt_enclosure 14 1 1961706 1961707 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep227 := BSN.log_dyadic_bound 6 22 5 4 51857700491520 524288 198314 1346332575744 176359680 293399 28 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 6) (BSN.artanhQ 22) 0 4 1346332575744 51857700491520 176359680 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep228 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz587 140505 1000 0 1 11885250371606245 4503599627370496 500000000297471 99157000000000000000 66797484138501418149 180143985094819840 14050500008359232571 19831400000000000000000 qz18 (BSN.isNear_log_sfrac 14 1 11885250371606245 4503599627370496 500000000297471 99157000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz588) Bool.false 49850353174629559828480 18889465931478580854784 1000000000594942 198314000000000000000 11885250371606245 4503599627370496 500000000297471 99157000000000000000 (BSN.log_rat_reduce_isNear 14 1 3 28 16 293399 524288 24973259072661432 36028797018963968 198314 1000000000000000 rfl rfl rfl rfl (ep227 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep229 := nat_lit 1563103366448087441736011343860641

noncomputable def ep230 := BSN.cos_dyadic_bound_f 198836873 2147483648 2 1 1048576 397016 ep229 ep66 ep229 ep229 ep67 ep229 1044084 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 198836873) qz15 0 1 ep229 ep66 ep229 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 198836873) qz16 0 1 ep229 ep67 ep229 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz334 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 194406265) qz17)

noncomputable def ep231 := @Enclosure.Real.IsNear.cos_image qz43 qz334 Bool.false 194406265 524288 93 131072 Bool.false 1044084 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz43 Bool.false 66797484138501418149 180143985094819840 14050500008359232571 19831400000000000000000 194406265 524288 93 131072 (ep228 rfl) rfl) (Enclosure.sfrac_false_div 194406265 524288) (BSN.cos_reduce0 qz334 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 6995950531680812400640) qz19) 226375608064910080 72057594037927936 Bool.false 1044084 1048576 59 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q0 194406265 524288 226375608064910080 72057594037927936 59 6995950531680812400640 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1044084 1048576 6995950531680812400640 75557863725914323419136 198836873 2147483648 397016 396628 (ep230 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep232 := BSN.sin_dyadic_bound_f 198836873 2147483648 1 0 1048576 397016 0 1 1 0 1 1 96949 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 198836873) qz20 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 198836873) qz21 0 0 rfl) rfl rfl

noncomputable def ep233 := @Enclosure.Real.IsNear.sin_image qz43 qz334 Bool.false 194406265 524288 93 131072 Bool.false 96949 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz43 Bool.false 66797484138501418149 180143985094819840 14050500008359232571 19831400000000000000000 194406265 524288 93 131072 (ep228 rfl) rfl) (Enclosure.sfrac_false_div 194406265 524288) (BSN.sin_reduce0 qz334 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 6995950531680812400640) qz19) 226375608064910080 72057594037927936 Bool.false 96949 1048576 59 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q0 194406265 524288 226375608064910080 72057594037927936 59 6995950531680812400640 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 96949 1048576 6995950531680812400640 75557863725914323419136 198836873 2147483648 397016 396628 (ep232 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz335 := (@Enclosure.Real.IsNear.recentre' qz42 Bool.false 280243 1048576 1 1048576 280243 1048576 1 1048576 (ep226 rfl rfl) rfl)

noncomputable def ep234 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz42 (Real.cos qz43)) (@HMul.hMul Real Real Real qz0 qz42 (@Neg.neg Real Real.instNeg (Real.sin qz43))) Bool.false 73149308103 274877906944 5231210902153 27256068618846208 Bool.true 27169278607 1099511627776 20830928543417 109024274475384832 (@Enclosure.Real.IsNear.mulLit_ff qz42 (Real.cos qz43) 280243 1048576 1 1048576 261021 262144 9287137 12996706304 73149308103 274877906944 5231210902153 27256068618846208 qz335 (@Enclosure.Real.IsNear.recentre' (Real.cos qz43) Bool.false 1044084 1048576 18574274 25993412608 261021 262144 9287137 12996706304 (ep231 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz42 (@Neg.neg Real Real.instNeg (Real.sin qz43)) 280243 1048576 1 1048576 96949 1048576 9287137 12996706304 27169278607 1099511627776 20830928543417 109024274475384832 qz335 (@Enclosure.Real.IsNear.neg (Real.sin qz43) Bool.false 96949 1048576 9287137 12996706304 (@Enclosure.Real.IsNear.recentre' (Real.sin qz43) Bool.false 96949 1048576 18574274 25993412608 96949 1048576 9287137 12996706304 (ep233 rfl rfl) rfl)) rfl)

noncomputable def ep235 := @ep146 73149308103 274877906944 5231210902153 27256068618846208 Bool.true 27169278607 1099511627776 20830928543417 109024274475384832 Bool.true 4805132157291126063104 34961937907 274877906944 100692175560509 27256068618846208 Bool.true 60222344454816619560960 27385951605 549755813888 50242542735955 13628034309423104 (ep147 (BSN.head_sum_c_succ qz5 13 14 rfl rfl) (ep224 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep225 ep234) rfl rfl

noncomputable abbrev qz589 := (@Nat.cast Real Real.instNatCast 15)

noncomputable abbrev qz44 := (@Inv.inv Real Real.instInv (Real.sqrt qz589))

noncomputable abbrev qz590 := (Real.log (Enclosure.sfrac Bool.false 15 1))

noncomputable abbrev qz45 := (@HMul.hMul Real Real Real qz267 qz277 qz590)

noncomputable def ep236 := @Enclosure.Complex.IsNear.of_eq qz564 (Complex.mk (@HMul.hMul Real Real Real qz0 qz44 (Real.cos qz45)) (@HMul.hMul Real Real Real qz0 qz44 (@Neg.neg Real Real.instNeg (Real.sin qz45)))) Bool.true 265531672419 1099511627776 20212593485395 109024274475384832 Bool.false 100438142475 1099511627776 20152129133307 109024274475384832 (BSN.cpow_neg_s_mk qz12 140505 1000 15 qz13 rfl)

noncomputable abbrev qz591 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 15) qz14)

noncomputable def ep237 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz589) 4061117 1048576 1 1048576 135370 135371 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz589) (Real.sqrt qz591) Bool.false 4061117 1048576 1 1048576 (BSN.sqrt_natCast_div_one 15) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz591) Bool.false 4061117 1048576 1 1048576 4061117 1048576 1 1048576 (BSN.sqrt_enclosure 15 1 2030558 2030559 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep238 := BSN.log_dyadic_bound 7 23 6 5 430628584065881355 524288 198314 14087658153505881 266939110305 329571 30 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 7) (BSN.artanhQ 23) 0 5 14087658153505881 430628584065881355 266939110305 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep239 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz590 140505 1000 0 1 12195965485668069 4503599627370496 500000000297471 99157000000000000000 342718826112758406969 900719925474099200 14050500008359232571 19831400000000000000000 qz18 (BSN.isNear_log_sfrac 15 1 12195965485668069 4503599627370496 500000000297471 99157000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz591) Bool.false 51153586820399524478976 18889465931478580854784 1000000000594942 198314000000000000000 12195965485668069 4503599627370496 500000000297471 99157000000000000000 (BSN.log_rat_reduce_isNear 15 1 3 30 16 329571 524288 24973259072661432 36028797018963968 198314 1000000000000000 rfl rfl rfl rfl (ep238 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep240 := nat_lit 363689323679850072164525200227123456

noncomputable def ep241 := BSN.cos_dyadic_bound_f 776573628 2147483648 2 1 1048576 397016 ep240 ep66 ep240 ep240 ep67 ep240 980759 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 776573628) qz15 0 1 ep240 ep66 ep240 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 776573628) qz16 0 1 ep240 ep67 ep240 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz336 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 49872153) qz585)

noncomputable def ep242 := @Enclosure.Real.IsNear.cos_image qz45 qz336 Bool.false 49872153 131072 93 131072 Bool.true 980759 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz45 Bool.false 342718826112758406969 900719925474099200 14050500008359232571 19831400000000000000000 49872153 131072 93 131072 (ep239 rfl) rfl) (Enclosure.sfrac_false_div 49872153 131072) (BSN.cos_reduce2 qz336 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 6830813874157304938496) qz332) 226375608064910080 72057594037927936 Bool.false 980759 1048576 60 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q2 49872153 131072 226375608064910080 72057594037927936 60 6830813874157304938496 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 980759 1048576 6830813874157304938496 18889465931478580854784 776573628 2147483648 397016 396628 (ep241 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep243 := BSN.sin_dyadic_bound_f 776573628 2147483648 2 1 1048576 397016 ep240 ep70 ep240 ep240 ep71 ep240 370975 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 776573628) qz20 0 1 ep240 ep70 ep240 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 776573628) qz21 0 1 ep240 ep71 ep240 rfl rfl rfl rfl) rfl rfl

noncomputable def ep244 := @Enclosure.Real.IsNear.sin_image qz45 qz336 Bool.false 49872153 131072 93 131072 Bool.true 370975 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz45 Bool.false 342718826112758406969 900719925474099200 14050500008359232571 19831400000000000000000 49872153 131072 93 131072 (ep239 rfl) rfl) (Enclosure.sfrac_false_div 49872153 131072) (BSN.sin_reduce2 qz336 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 6830813874157304938496) qz332) 226375608064910080 72057594037927936 Bool.false 370975 1048576 60 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q2 49872153 131072 226375608064910080 72057594037927936 60 6830813874157304938496 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 370975 1048576 6830813874157304938496 18889465931478580854784 776573628 2147483648 397016 396628 (ep243 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz337 := (@Enclosure.Real.IsNear.recentre' qz44 Bool.false 270741 1048576 1 1048576 270741 1048576 1 1048576 (ep237 rfl rfl) rfl)

noncomputable def ep245 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz44 (Real.cos qz45)) (@HMul.hMul Real Real Real qz0 qz44 (@Neg.neg Real Real.instNeg (Real.sin qz45))) Bool.true 265531672419 1099511627776 20212593485395 109024274475384832 Bool.false 100438142475 1099511627776 20152129133307 109024274475384832 (@Enclosure.Real.IsNear.mulLit_ft qz44 (Real.cos qz45) 270741 1048576 1 1048576 980759 1048576 9287137 12996706304 265531672419 1099511627776 20212593485395 109024274475384832 qz337 (@Enclosure.Real.IsNear.recentre' (Real.cos qz45) Bool.true 980759 1048576 18574274 25993412608 980759 1048576 9287137 12996706304 (ep242 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz44 (@Neg.neg Real Real.instNeg (Real.sin qz45)) 270741 1048576 1 1048576 370975 1048576 9287137 12996706304 100438142475 1099511627776 20152129133307 109024274475384832 qz337 (@Enclosure.Real.IsNear.neg (Real.sin qz45) Bool.true 370975 1048576 9287137 12996706304 (@Enclosure.Real.IsNear.recentre' (Real.sin qz45) Bool.true 370975 1048576 18574274 25993412608 370975 1048576 9287137 12996706304 (ep244 rfl rfl) rfl)) rfl)

noncomputable def ep246 := @ep144 265531672419 1099511627776 20212593485395 109024274475384832 Bool.false 100438142475 1099511627776 20152129133307 109024274475384832 Bool.true 111429847600203581882368 405379424047 1099511627776 422981295727431 109024274475384832 Bool.false 25105280534334217912320 45666239265 1099511627776 422092471020947 109024274475384832 (ep145 (BSN.head_sum_c_succ qz5 14 15 rfl rfl) (ep235 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep236 ep245) rfl rfl

noncomputable abbrev qz592 := (@Nat.cast Real Real.instNatCast 16)

noncomputable abbrev qz46 := (@Inv.inv Real Real.instInv (Real.sqrt qz592))

noncomputable abbrev qz593 := (Real.log (Enclosure.sfrac Bool.false 16 1))

noncomputable abbrev qz47 := (@HMul.hMul Real Real Real qz267 qz277 qz593)

noncomputable def ep247 := @Enclosure.Complex.IsNear.of_eq qz563 (Complex.mk (@HMul.hMul Real Real Real qz0 qz46 (Real.cos qz47)) (@HMul.hMul Real Real Real qz0 qz46 (@Neg.neg Real Real.instNeg (Real.sin qz47)))) Bool.false 137436594183 549755813888 9790255098029 54512137237692416 Bool.true 174849381 137438953472 2434633379447 13628034309423104 (BSN.cpow_neg_s_mk qz12 140505 1000 16 qz13 rfl)

noncomputable abbrev qz594 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 16) qz14)

noncomputable def ep248 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz592) 4194305 1048576 1 1048576 131071 131072 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz592) (Real.sqrt qz594) Bool.false 4194305 1048576 1 1048576 (BSN.sqrt_natCast_div_one 16) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz594) Bool.false 4194305 1048576 1 1048576 4194305 1048576 1 1048576 (BSN.sqrt_enclosure 16 1 2097152 2097153 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep249 := BSN.log_dyadic_bound 0 32 1 0 1 524288 198314 0 1 0 32 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 0) (BSN.artanhQ 32) 0 0 rfl) rfl rfl rfl

noncomputable def ep250 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz593 140505 1000 0 1 3121657384082679 1125899906842624 125000000099157 24789250000000000000 87721694150107362579 225179981368524800 3512625002786410857 4957850000000000000000 qz18 (BSN.isNear_log_sfrac 16 1 3121657384082679 1125899906842624 125000000099157 24789250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz594) Bool.false 52372720210750067441664 18889465931478580854784 1000000000793256 198314000000000000000 3121657384082679 1125899906842624 125000000099157 24789250000000000000 (BSN.log_rat_reduce_isNear 16 1 4 32 32 0 524288 24973259072661432 36028797018963968 198314 1000000000000000 rfl rfl rfl rfl (ep249 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep251 := BSN.cos_dyadic_bound_f 10928879 2147483648 1 0 1048576 397016 0 1 1 0 1 1 1048562 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 10928879) qz15 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 10928879) qz16 0 0 rfl) rfl rfl

noncomputable abbrev qz338 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 204242985) qz17)

noncomputable def ep252 := @Enclosure.Real.IsNear.cos_image qz47 qz338 Bool.false 204242985 524288 93 131072 Bool.false 1048562 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz47 Bool.false 87721694150107362579 225179981368524800 3512625002786410857 4957850000000000000000 204242985 524288 93 131072 (ep250 rfl) rfl) (Enclosure.sfrac_false_div 204242985 524288) (BSN.cos_reduce0 qz338 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 384525767586873344000) qz19) 226375608064910080 72057594037927936 Bool.false 1048562 1048576 62 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q0 204242985 524288 226375608064910080 72057594037927936 62 384525767586873344000 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1048562 1048576 384525767586873344000 75557863725914323419136 10928879 2147483648 397016 396628 (ep251 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep253 := BSN.sin_dyadic_bound_f 10928879 2147483648 1 0 1048576 397016 0 1 1 0 1 1 5336 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 10928879) qz20 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 10928879) qz21 0 0 rfl) rfl rfl

noncomputable def ep254 := @Enclosure.Real.IsNear.sin_image qz47 qz338 Bool.false 204242985 524288 93 131072 Bool.false 5336 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz47 Bool.false 87721694150107362579 225179981368524800 3512625002786410857 4957850000000000000000 204242985 524288 93 131072 (ep250 rfl) rfl) (Enclosure.sfrac_false_div 204242985 524288) (BSN.sin_reduce0 qz338 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 384525767586873344000) qz19) 226375608064910080 72057594037927936 Bool.false 5336 1048576 62 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q0 204242985 524288 226375608064910080 72057594037927936 62 384525767586873344000 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 5336 1048576 384525767586873344000 75557863725914323419136 10928879 2147483648 397016 396628 (ep253 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz339 := (@Enclosure.Real.IsNear.recentre' qz46 Bool.false 262143 1048576 1 1048576 262143 1048576 1 1048576 (ep248 rfl rfl) rfl)

noncomputable def ep255 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz46 (Real.cos qz47)) (@HMul.hMul Real Real Real qz0 qz46 (@Neg.neg Real Real.instNeg (Real.sin qz47))) Bool.false 137436594183 549755813888 9790255098029 54512137237692416 Bool.true 174849381 137438953472 2434633379447 13628034309423104 (@Enclosure.Real.IsNear.mulLit_ff qz46 (Real.cos qz47) 262143 1048576 1 1048576 524281 524288 9287137 12996706304 137436594183 549755813888 9790255098029 54512137237692416 qz339 (@Enclosure.Real.IsNear.recentre' (Real.cos qz47) Bool.false 1048562 1048576 18574274 25993412608 524281 524288 9287137 12996706304 (ep252 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz46 (@Neg.neg Real Real.instNeg (Real.sin qz47)) 262143 1048576 1 1048576 667 131072 9287137 12996706304 174849381 137438953472 2434633379447 13628034309423104 qz339 (@Enclosure.Real.IsNear.neg (Real.sin qz47) Bool.false 667 131072 9287137 12996706304 (@Enclosure.Real.IsNear.recentre' (Real.sin qz47) Bool.false 5336 1048576 18574274 25993412608 667 131072 9287137 12996706304 (ep254 rfl rfl) rfl)) rfl)

noncomputable def ep256 := @ep142 137436594183 549755813888 9790255098029 54512137237692416 Bool.true 174849381 137438953472 2434633379447 13628034309423104 Bool.true 71746561814267300937728 130506235681 1099511627776 442561805923489 109024274475384832 Bool.false 6084071206064618471424 44267444217 1099511627776 441569538056523 109024274475384832 (ep143 (BSN.head_sum_c_succ qz5 15 16 rfl rfl) (ep246 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep247 ep255) rfl rfl

theorem EMRow49.d7 : Enclosure.Complex.IsNear qz32 Bool.true 130506235681 1099511627776 442561805923489 109024274475384832 Bool.false 44267444217 1099511627776 441569538056523 109024274475384832 := ep141 (BSN.head_sum_c_succ qz5 16 17 rfl rfl) (ep256 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable abbrev qz48 := (BSN.headSumC qz271 25)

noncomputable abbrev qz595 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 24) qz7)

noncomputable def ep257 := @Enclosure.Complex.IsNear.of_eq qz48 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 24) qz595) Bool.false 670912389343 1099511627776 581547117797421 109024274475384832 Bool.true 17063795071 68719476736 18136572005543 3407008577355776

noncomputable def ep258 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 24) qz595 Bool.false 466550520611 1099511627776 565571117020145 109024274475384832 Bool.true 90121474059 549755813888 282222998261141 54512137237692416 Bool.false

noncomputable abbrev qz596 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 23) qz7)

noncomputable def ep259 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 24) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 23) qz596) Bool.false 466550520611 1099511627776 565571117020145 109024274475384832 Bool.true 90121474059 549755813888 282222998261141 54512137237692416

noncomputable def ep260 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 23) qz596 Bool.false 295613674067 1099511627776 549248981026465 109024274475384832 Bool.true 27460685793 1099511627776 548132093831783 109024274475384832 Bool.false

noncomputable abbrev qz597 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 22) qz7)

noncomputable def ep261 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 23) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 22) qz597) Bool.false 295613674067 1099511627776 549248981026465 109024274475384832 Bool.true 27460685793 1099511627776 548132093831783 109024274475384832

noncomputable def ep262 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 22) qz597 Bool.false 63417981781 549755813888 66570551346799 13628034309423104 Bool.false 135220401765 1099511627776 531450227690257 109024274475384832 Bool.false

noncomputable abbrev qz598 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 21) qz7)

noncomputable def ep263 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 22) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 21) qz598) Bool.false 63417981781 549755813888 66570551346799 13628034309423104 Bool.false 135220401765 1099511627776 531450227690257 109024274475384832

noncomputable def ep264 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 21) qz598 Bool.true 41054825387 549755813888 64422832305243 13628034309423104 Bool.false 253158919415 1099511627776 514347350190087 109024274475384832 Bool.false

noncomputable abbrev qz599 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 20) qz7)

noncomputable def ep265 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 21) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 20) qz599) Bool.true 41054825387 549755813888 64422832305243 13628034309423104 Bool.false 253158919415 1099511627776 514347350190087 109024274475384832

noncomputable def ep266 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 20) qz599 Bool.true 327552034443 1099511627776 497858420696067 109024274475384832 Bool.false 238862406609 1099511627776 496920864092049 109024274475384832 Bool.false

noncomputable abbrev qz600 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 19) qz7)

noncomputable def ep267 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 20) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 19) qz600) Bool.true 327552034443 1099511627776 497858420696067 109024274475384832 Bool.false 238862406609 1099511627776 496920864092049 109024274475384832

noncomputable def ep268 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 19) qz600 Bool.true 233836059543 549755813888 239963877305209 54512137237692416 Bool.false 3639546045 137438953472 239480749299631 54512137237692416 Bool.false

noncomputable abbrev qz601 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 18) qz7)

noncomputable def ep269 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 19) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 18) qz601) Bool.true 233836059543 549755813888 239963877305209 54512137237692416 Bool.false 3639546045 137438953472 239480749299631 54512137237692416

noncomputable def ep270 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 18) qz601 Bool.true 295888580781 1099511627776 461496159171191 109024274475384832 Bool.true 41231459039 274877906944 230260486490729 54512137237692416 Bool.true

noncomputable abbrev qz602 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 17) qz7)

noncomputable def ep271 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 18) (@HAdd.hAdd Complex Complex Complex qz4 qz32 qz602) Bool.true 295888580781 1099511627776 461496159171191 109024274475384832 Bool.true 41231459039 274877906944 230260486490729 54512137237692416

noncomputable def ep272 := @Enclosure.Complex.IsNear.addLitP qz32 qz602 Bool.true 130506235681 1099511627776 442561805923489 109024274475384832 Bool.false 44267444217 1099511627776 441569538056523 109024274475384832 Bool.true

noncomputable abbrev qz603 := (@Nat.cast Real Real.instNatCast 17)

noncomputable abbrev qz49 := (@Inv.inv Real Real.instInv (Real.sqrt qz603))

noncomputable abbrev qz604 := (Real.log (Enclosure.sfrac Bool.false 17 1))

noncomputable abbrev qz50 := (@HMul.hMul Real Real Real qz267 qz277 qz604)

noncomputable def ep273 := @Enclosure.Complex.IsNear.of_eq qz602 (Complex.mk (@HMul.hMul Real Real Real qz0 qz49 (Real.cos qz50)) (@HMul.hMul Real Real Real qz0 qz49 (@Neg.neg Real Real.instNeg (Real.sin qz50)))) Bool.true 41345586275 274877906944 9467176623851 54512137237692416 Bool.true 209193280373 1099511627776 18951434924935 109024274475384832 (BSN.cpow_neg_s_mk qz12 140505 1000 17 qz13 rfl)

noncomputable abbrev qz605 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 17) qz14)

noncomputable def ep274 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz603) 4323389 1048576 1 1048576 127158 127159 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz603) (Real.sqrt qz605) Bool.false 4323389 1048576 1 1048576 (BSN.sqrt_natCast_div_one 17) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz605) Bool.false 4323389 1048576 1 1048576 4323389 1048576 1 1048576 (BSN.sqrt_enclosure 17 1 2161694 2161695 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep275 := BSN.log_dyadic_bound 1 33 2 1 3267 524288 198314 1 1 31784 34 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 1) (BSN.artanhQ 33) 0 1 1 3267 1 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep276 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz604 140505 1000 0 1 3189913004350711 1125899906842624 125000000099157 24789250000000000000 89639745335259329811 225179981368524800 3512625002786410857 4957850000000000000000 qz18 (BSN.isNear_log_sfrac 17 1 3189913004350711 1125899906842624 125000000099157 24789250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz605) Bool.false 53517859495200818200576 18889465931478580854784 1000000000793256 198314000000000000000 3189913004350711 1125899906842624 125000000099157 24789250000000000000 (BSN.log_rat_reduce_isNear 17 1 4 34 32 31784 524288 24973259072661432 36028797018963968 198314 1000000000000000 rfl rfl rfl rfl (ep275 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep277 := nat_lit 4259275323173888124999543292916121856

noncomputable def ep278 := BSN.sin_dyadic_bound_f 1436593604 2147483648 2 1 1048576 397016 ep277 ep70 ep277 ep277 ep71 ep277 650300 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1436593604) qz20 0 1 ep277 ep70 ep277 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1436593604) qz21 0 1 ep277 ep71 ep277 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz340 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 52177199) qz585)

noncomputable def ep279 := @Enclosure.Real.IsNear.cos_image qz50 qz340 Bool.false 52177199 131072 743 1048576 Bool.true 650300 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz50 Bool.false 89639745335259329811 225179981368524800 3512625002786410857 4957850000000000000000 52177199 131072 743 1048576 (ep276 rfl) rfl) (Enclosure.sfrac_false_div 52177199 131072) (BSN.cos_reduce1 qz340 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 12636410984533745205248) qz332) 226375608064910080 72057594037927936 Bool.false 650300 1048576 63 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q1 52177199 131072 226375608064910080 72057594037927936 63 12636410984533745205248 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 650300 1048576 12636410984533745205248 18889465931478580854784 1436593604 2147483648 397016 396628 (ep278 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep280 := nat_lit 152200551701721952008593181042812818366941430790502995346135728300410515030016

noncomputable def ep281 := nat_lit 18141426278598029128576825347591453853366539608204080464478059159040884736

noncomputable def ep282 := nat_lit 456565372252608659967522389477743272193117559292292577877478228782913463320576

noncomputable def ep283 := BSN.cos_dyadic_bound_f 1436593604 2147483648 3 2 1048576 397016 ep280 ep102 ep281 ep282 ep104 ep281 822569 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1436593604) qz15 0 2 ep280 ep102 ep281 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1436593604) qz16 0 2 ep282 ep104 ep281 rfl rfl rfl rfl) rfl rfl

noncomputable def ep284 := @Enclosure.Real.IsNear.sin_image qz50 qz340 Bool.false 52177199 131072 743 1048576 Bool.false 822569 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz50 Bool.false 89639745335259329811 225179981368524800 3512625002786410857 4957850000000000000000 52177199 131072 743 1048576 (ep276 rfl) rfl) (Enclosure.sfrac_false_div 52177199 131072) (BSN.sin_reduce1 qz340 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 12636410984533745205248) qz332) 226375608064910080 72057594037927936 Bool.false 822569 1048576 63 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q1 52177199 131072 226375608064910080 72057594037927936 63 12636410984533745205248 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 822569 1048576 12636410984533745205248 18889465931478580854784 1436593604 2147483648 397016 396628 (ep283 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz341 := (@Enclosure.Real.IsNear.recentre' qz49 Bool.false 254317 1048576 1 1048576 254317 1048576 1 1048576 (ep274 rfl rfl) rfl)

noncomputable def ep285 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz49 (Real.cos qz50)) (@HMul.hMul Real Real Real qz0 qz49 (@Neg.neg Real Real.instNeg (Real.sin qz50))) Bool.true 41345586275 274877906944 9467176623851 54512137237692416 Bool.true 209193280373 1099511627776 18951434924935 109024274475384832 (@Enclosure.Real.IsNear.mulLit_ft qz49 (Real.cos qz50) 254317 1048576 1 1048576 162575 262144 74197939 103973650432 41345586275 274877906944 9467176623851 54512137237692416 qz341 (@Enclosure.Real.IsNear.recentre' (Real.cos qz50) Bool.true 650300 1048576 148395878 207947300864 162575 262144 74197939 103973650432 (ep279 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz49 (@Neg.neg Real Real.instNeg (Real.sin qz50)) 254317 1048576 1 1048576 822569 1048576 74197939 103973650432 209193280373 1099511627776 18951434924935 109024274475384832 qz341 (@Enclosure.Real.IsNear.neg (Real.sin qz50) Bool.false 822569 1048576 74197939 103973650432 (@Enclosure.Real.IsNear.recentre' (Real.sin qz50) Bool.false 822569 1048576 148395878 207947300864 822569 1048576 74197939 103973650432 (ep284 rfl rfl) rfl)) rfl)

noncomputable def ep286 := @ep272 41345586275 274877906944 9467176623851 54512137237692416 Bool.true 209193280373 1099511627776 18951434924935 109024274475384832 Bool.true 81333233773711944843264 295888580781 1099511627776 461496159171191 109024274475384832 Bool.true 181337874574201434669056 41231459039 274877906944 230260486490729 54512137237692416 EMRow49.d7 (ep273 ep285) rfl rfl

noncomputable abbrev qz606 := (@Nat.cast Real Real.instNatCast 18)

noncomputable abbrev qz51 := (@Inv.inv Real Real.instInv (Real.sqrt qz606))

noncomputable abbrev qz607 := (Real.log (Enclosure.sfrac Bool.false 18 1))

noncomputable abbrev qz52 := (@HMul.hMul Real Real Real qz267 qz277 qz607)

noncomputable def ep287 := @Enclosure.Complex.IsNear.of_eq qz601 (Complex.mk (@HMul.hMul Real Real Real qz0 qz51 (Real.cos qz52)) (@HMul.hMul Real Real Real qz0 qz51 (@Neg.neg Real Real.instNeg (Real.sin qz52)))) Bool.true 171783538305 1099511627776 18431595439227 109024274475384832 Bool.false 48510551129 274877906944 4610131404451 27256068618846208 (BSN.cpow_neg_s_mk qz12 140505 1000 18 qz13 rfl)

noncomputable abbrev qz608 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 18) qz14)

noncomputable def ep288 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz606) 4448731 1048576 1 1048576 123575 123576 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz606) (Real.sqrt qz608) Bool.false 4448731 1048576 1 1048576 (BSN.sqrt_natCast_div_one 18) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz608) Bool.false 4448731 1048576 1 1048576 4448731 1048576 1 1048576 (BSN.sqrt_enclosure 18 1 2224365 2224366 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep289 := BSN.log_dyadic_bound 2 34 3 2 20045040 524288 198314 23168 48 61752 36 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 2) (BSN.artanhQ 34) 0 2 23168 20045040 48 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep290 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz607 140505 1000 0 1 3254268794313975 1125899906842624 125000000099157 24789250000000000000 3657928295560680459 9007199254740992 3512625002786410857 4957850000000000000000 qz18 (BSN.isNear_log_sfrac 18 1 3254268794313975 1125899906842624 125000000099157 24789250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz608) Bool.false 54597570484265130393600 18889465931478580854784 1000000000793256 198314000000000000000 3254268794313975 1125899906842624 125000000099157 24789250000000000000 (BSN.log_rat_reduce_isNear 18 1 4 36 32 61752 524288 24973259072661432 36028797018963968 198314 1000000000000000 rfl rfl rfl rfl (ep289 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep291 := nat_lit 389680176139223068501802932826923287860842808047028376978417120530404912800000

noncomputable def ep292 := nat_lit 118875984072351423998187379189704749114427869523756984477609654176100000000

noncomputable def ep293 := nat_lit 1168802776449524502657412423722390454084299568402037616966296142282862538400000

noncomputable def ep294 := BSN.cos_dyadic_bound_f 1817133210 2147483648 3 2 1048576 397016 ep291 ep102 ep292 ep293 ep104 ep292 695055 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1817133210) qz15 0 2 ep291 ep102 ep292 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1817133210) qz16 0 2 ep293 ep104 ep292 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz342 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 425838899) qz26)

noncomputable def ep295 := @Enclosure.Real.IsNear.cos_image qz52 qz342 Bool.false 425838899 1048576 93 131072 Bool.true 695055 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz52 Bool.false 3657928295560680459 9007199254740992 3512625002786410857 4957850000000000000000 425838899 1048576 93 131072 (ep290 rfl) rfl) (Enclosure.sfrac_false_div 425838899 1048576) (BSN.cos_reduce2 qz342 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 127869382014435787276288) qz27) 226375608064910080 72057594037927936 Bool.false 695055 1048576 64 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q2 425838899 1048576 226375608064910080 72057594037927936 64 127869382014435787276288 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 695055 1048576 127869382014435787276288 151115727451828646838272 1817133210 2147483648 397016 396628 (ep294 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep296 := nat_lit 10903026372175361476882091666196810000

noncomputable def ep297 := BSN.sin_dyadic_bound_f 1817133210 2147483648 2 1 1048576 397016 ep296 ep70 ep296 ep296 ep71 ep296 785116 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1817133210) qz20 0 1 ep296 ep70 ep296 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1817133210) qz21 0 1 ep296 ep71 ep296 rfl rfl rfl rfl) rfl rfl

noncomputable def ep298 := @Enclosure.Real.IsNear.sin_image qz52 qz342 Bool.false 425838899 1048576 93 131072 Bool.true 785116 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz52 Bool.false 3657928295560680459 9007199254740992 3512625002786410857 4957850000000000000000 425838899 1048576 93 131072 (ep290 rfl) rfl) (Enclosure.sfrac_false_div 425838899 1048576) (BSN.sin_reduce2 qz342 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 127869382014435787276288) qz27) 226375608064910080 72057594037927936 Bool.false 785116 1048576 64 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q2 425838899 1048576 226375608064910080 72057594037927936 64 127869382014435787276288 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 785116 1048576 127869382014435787276288 151115727451828646838272 1817133210 2147483648 397016 396628 (ep297 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz343 := (@Enclosure.Real.IsNear.recentre' qz51 Bool.false 247151 1048576 1 1048576 247151 1048576 1 1048576 (ep288 rfl rfl) rfl)

noncomputable def ep299 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz51 (Real.cos qz52)) (@HMul.hMul Real Real Real qz0 qz51 (@Neg.neg Real Real.instNeg (Real.sin qz52))) Bool.true 171783538305 1099511627776 18431595439227 109024274475384832 Bool.false 48510551129 274877906944 4610131404451 27256068618846208 (@Enclosure.Real.IsNear.mulLit_ft qz51 (Real.cos qz52) 247151 1048576 1 1048576 695055 1048576 9287137 12996706304 171783538305 1099511627776 18431595439227 109024274475384832 qz343 (@Enclosure.Real.IsNear.recentre' (Real.cos qz52) Bool.true 695055 1048576 18574274 25993412608 695055 1048576 9287137 12996706304 (ep295 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz51 (@Neg.neg Real Real.instNeg (Real.sin qz52)) 247151 1048576 1 1048576 196279 262144 9287137 12996706304 48510551129 274877906944 4610131404451 27256068618846208 qz343 (@Enclosure.Real.IsNear.neg (Real.sin qz52) Bool.true 196279 262144 9287137 12996706304 (@Enclosure.Real.IsNear.recentre' (Real.sin qz52) Bool.true 785116 1048576 18574274 25993412608 196279 262144 9287137 12996706304 (ep298 rfl rfl) rfl)) rfl)

noncomputable def ep300 := @ep270 171783538305 1099511627776 18431595439227 109024274475384832 Bool.false 48510551129 274877906944 4610131404451 27256068618846208 Bool.true 514210932921699177332736 233836059543 549755813888 239963877305209 54512137237692416 Bool.false 2000861598151826472960 3639546045 137438953472 239480749299631 54512137237692416 (ep271 (BSN.head_sum_c_succ qz5 17 18 rfl rfl) (ep286 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep287 ep299) rfl rfl

noncomputable abbrev qz609 := (@Nat.cast Real Real.instNatCast 19)

noncomputable abbrev qz53 := (@Inv.inv Real Real.instInv (Real.sqrt qz609))

noncomputable abbrev qz610 := (Real.log (Enclosure.sfrac Bool.false 19 1))

noncomputable abbrev qz54 := (@HMul.hMul Real Real Real qz267 qz277 qz610)

noncomputable def ep301 := @Enclosure.Complex.IsNear.of_eq qz600 (Complex.mk (@HMul.hMul Real Real Real qz0 qz53 (Real.cos qz54)) (@HMul.hMul Real Real Real qz0 qz53 (@Neg.neg Real Real.instNeg (Real.sin qz54)))) Bool.false 140120084643 1099511627776 17930666085649 109024274475384832 Bool.false 209746038249 1099511627776 17959365492787 109024274475384832 (BSN.cpow_neg_s_mk qz12 140505 1000 19 qz13 rfl)

noncomputable abbrev qz611 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 19) qz14)

noncomputable def ep302 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz609) 4570637 1048576 1 1048576 120279 120280 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz609) (Real.sqrt qz611) Bool.false 4570637 1048576 1 1048576 (BSN.sqrt_natCast_div_one 19) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz611) Bool.false 4570637 1048576 1 1048576 4570637 1048576 1 1048576 (BSN.sqrt_enclosure 19 1 2285318 2285319 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep303 := BSN.log_dyadic_bound 3 35 3 2 22509375 524288 198314 55368 243 90099 38 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 3) (BSN.artanhQ 35) 0 2 55368 22509375 243 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep304 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz610 140505 1000 0 1 3315143513283831 1125899906842624 125000000099157 24789250000000000000 93158847866788934931 225179981368524800 3512625002786410857 4957850000000000000000 qz18 (BSN.isNear_log_sfrac 19 1 3315143513283831 1125899906842624 125000000099157 24789250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz611) Bool.false 55618878793361701994496 18889465931478580854784 1000000000793256 198314000000000000000 3315143513283831 1125899906842624 125000000099157 24789250000000000000 (BSN.log_rat_reduce_isNear 19 1 4 38 32 90099 524288 24973259072661432 36028797018963968 198314 1000000000000000 rfl rfl rfl rfl (ep303 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep305 := nat_lit 2558907153664869104918957692063471681

noncomputable def ep306 := BSN.sin_dyadic_bound_f 1264776047 2147483648 2 1 1048576 397016 ep305 ep70 ep305 ep305 ep71 ep305 582477 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1264776047) qz20 0 1 ep305 ep70 ep305 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1264776047) qz21 0 1 ep305 ep71 ep305 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz344 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 216902345) qz17)

noncomputable def ep307 := @Enclosure.Real.IsNear.cos_image qz54 qz344 Bool.false 216902345 524288 93 131072 Bool.false 582477 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz54 Bool.false 93158847866788934931 225179981368524800 3512625002786410857 4957850000000000000000 216902345 524288 93 131072 (ep304 rfl) rfl) (Enclosure.sfrac_false_div 216902345 524288) (BSN.cos_reduce3 qz344 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 44500351070520024760320) qz19) 226375608064910080 72057594037927936 Bool.false 582477 1048576 65 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q3 216902345 524288 226375608064910080 72057594037927936 65 44500351070520024760320 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 582477 1048576 44500351070520024760320 75557863725914323419136 1264776047 2147483648 397016 396628 (ep306 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep308 := BSN.cos_dyadic_bound_f 1264776047 2147483648 2 1 1048576 397016 ep305 ep66 ep305 ep305 ep67 ep305 871911 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1264776047) qz15 0 1 ep305 ep66 ep305 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1264776047) qz16 0 1 ep305 ep67 ep305 rfl rfl rfl rfl) rfl rfl

noncomputable def ep309 := @Enclosure.Real.IsNear.sin_image qz54 qz344 Bool.false 216902345 524288 93 131072 Bool.true 871911 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz54 Bool.false 93158847866788934931 225179981368524800 3512625002786410857 4957850000000000000000 216902345 524288 93 131072 (ep304 rfl) rfl) (Enclosure.sfrac_false_div 216902345 524288) (BSN.sin_reduce3 qz344 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 44500351070520024760320) qz19) 226375608064910080 72057594037927936 Bool.false 871911 1048576 65 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q3 216902345 524288 226375608064910080 72057594037927936 65 44500351070520024760320 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 871911 1048576 44500351070520024760320 75557863725914323419136 1264776047 2147483648 397016 396628 (ep308 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz345 := (@Enclosure.Real.IsNear.recentre' qz53 Bool.false 240559 1048576 1 1048576 240559 1048576 1 1048576 (ep302 rfl rfl) rfl)

noncomputable def ep310 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz53 (Real.cos qz54)) (@HMul.hMul Real Real Real qz0 qz53 (@Neg.neg Real Real.instNeg (Real.sin qz54))) Bool.false 140120084643 1099511627776 17930666085649 109024274475384832 Bool.false 209746038249 1099511627776 17959365492787 109024274475384832 (@Enclosure.Real.IsNear.mulLit_ff qz53 (Real.cos qz54) 240559 1048576 1 1048576 582477 1048576 9287137 12996706304 140120084643 1099511627776 17930666085649 109024274475384832 qz345 (@Enclosure.Real.IsNear.recentre' (Real.cos qz54) Bool.false 582477 1048576 18574274 25993412608 582477 1048576 9287137 12996706304 (ep307 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz53 (@Neg.neg Real Real.instNeg (Real.sin qz54)) 240559 1048576 1 1048576 871911 1048576 9287137 12996706304 209746038249 1099511627776 17959365492787 109024274475384832 qz345 (@Enclosure.Real.IsNear.neg (Real.sin qz54) Bool.true 871911 1048576 9287137 12996706304 (@Enclosure.Real.IsNear.recentre' (Real.sin qz54) Bool.true 871911 1048576 18574274 25993412608 871911 1048576 9287137 12996706304 (ep309 rfl rfl) rfl)) rfl)

noncomputable def ep311 := @ep268 140120084643 1099511627776 17930666085649 109024274475384832 Bool.false 209746038249 1099511627776 17959365492787 109024274475384832 Bool.true 180073635285881673744384 327552034443 1099511627776 497858420696067 109024274475384832 Bool.false 32828999188144296296448 238862406609 1099511627776 496920864092049 109024274475384832 (ep269 (BSN.head_sum_c_succ qz5 18 19 rfl rfl) (ep300 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep301 ep310) rfl rfl

noncomputable abbrev qz612 := (@Nat.cast Real Real.instNatCast 20)

noncomputable abbrev qz55 := (@Inv.inv Real Real.instInv (Real.sqrt qz612))

noncomputable abbrev qz613 := (Real.log (Enclosure.sfrac Bool.false 20 1))

noncomputable abbrev qz56 := (@HMul.hMul Real Real Real qz267 qz277 qz613)

noncomputable def ep312 := @Enclosure.Complex.IsNear.of_eq qz599 (Complex.mk (@HMul.hMul Real Real Real qz0 qz55 (Real.cos qz56)) (@HMul.hMul Real Real Real qz0 qz55 (@Neg.neg Real Real.instNeg (Real.sin qz56)))) Bool.false 245442383669 1099511627776 17524237745877 109024274475384832 Bool.false 7148256403 549755813888 8713243049019 54512137237692416 (BSN.cpow_neg_s_mk qz12 140505 1000 20 qz13 rfl)

noncomputable abbrev qz614 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 20) qz14)

noncomputable def ep313 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz612) 4689375 1048576 1 1048576 117234 117235 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz612) (Real.sqrt qz614) Bool.false 4689375 1048576 1 1048576 (BSN.sqrt_natCast_div_one 20) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz614) Bool.false 4689375 1048576 1 1048576 4689375 1048576 1 1048576 (BSN.sqrt_enclosure 20 1 2344687 2344688 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep314 := BSN.log_dyadic_bound 4 36 3 2 25194240 524288 198314 104448 768 116991 40 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 4) (BSN.artanhQ 36) 0 2 104448 25194240 768 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep315 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz613 140505 1000 0 1 3372893643545847 1125899906842624 125000000099157 24789250000000000000 94781684277281846547 225179981368524800 3512625002786410857 4957850000000000000000 qz18 (BSN.isNear_log_sfrac 20 1 3372893643545847 1125899906842624 125000000099157 24789250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz614) Bool.false 56587765202795681021952 18889465931478580854784 1000000000793256 198314000000000000000 3372893643545847 1125899906842624 125000000099157 24789250000000000000 (BSN.log_rat_reduce_isNear 20 1 4 40 32 116991 524288 24973259072661432 36028797018963968 198314 1000000000000000 rfl rfl rfl rfl (ep314 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep316 := nat_lit 7172716414542885200532000075562619334760889055225125007932691305465427593832385

noncomputable def ep317 := nat_lit 12395455238755035770433249842068875244140714959142035934496714071102331070401

noncomputable def ep318 := nat_lit 18765617015321000705384060650538748650168957796608145057834530167722906590685121

noncomputable def ep319 := BSN.sin_dyadic_bound_f 3248312551 2147483648 3 2 1048576 397016 ep316 ep95 ep317 ep318 ep98 ep317 1046801 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3248312551) qz20 0 2 ep316 ep95 ep317 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3248312551) qz21 0 2 ep318 ep98 ep317 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz346 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 441361611) qz26)

noncomputable def ep320 := @Enclosure.Real.IsNear.cos_image qz56 qz346 Bool.false 441361611 1048576 93 131072 Bool.false 1046801 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz56 Bool.false 94781684277281846547 225179981368524800 3512625002786410857 4957850000000000000000 441361611 1048576 93 131072 (ep315 rfl) rfl) (Enclosure.sfrac_false_div 441361611 1048576) (BSN.cos_reduce3 qz346 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 228579674921340273426432) qz27) 226375608064910080 72057594037927936 Bool.false 1046801 1048576 66 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q3 441361611 1048576 226375608064910080 72057594037927936 66 228579674921340273426432 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1046801 1048576 228579674921340273426432 151115727451828646838272 3248312551 2147483648 397016 396628 (ep319 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep321 := nat_lit 3990351543741049571749081486353485797197889792884688131489049264845727477049281

noncomputable def ep322 := nat_lit 11946263720745638643706377959376319641105387948735780322598154366394977769007041

noncomputable def ep323 := BSN.cos_dyadic_bound_f 3248312551 2147483648 3 2 1048576 397016 ep321 ep102 ep317 ep322 ep104 ep317 60974 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3248312551) qz15 0 2 ep321 ep102 ep317 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3248312551) qz16 0 2 ep322 ep104 ep317 rfl rfl rfl rfl) rfl rfl

noncomputable def ep324 := @Enclosure.Real.IsNear.sin_image qz56 qz346 Bool.false 441361611 1048576 93 131072 Bool.true 60974 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz56 Bool.false 94781684277281846547 225179981368524800 3512625002786410857 4957850000000000000000 441361611 1048576 93 131072 (ep315 rfl) rfl) (Enclosure.sfrac_false_div 441361611 1048576) (BSN.sin_reduce3 qz346 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 228579674921340273426432) qz27) 226375608064910080 72057594037927936 Bool.false 60974 1048576 66 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q3 441361611 1048576 226375608064910080 72057594037927936 66 228579674921340273426432 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 60974 1048576 228579674921340273426432 151115727451828646838272 3248312551 2147483648 397016 396628 (ep323 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz347 := (@Enclosure.Real.IsNear.recentre' qz55 Bool.false 234469 1048576 1 1048576 234469 1048576 1 1048576 (ep313 rfl rfl) rfl)

noncomputable def ep325 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz55 (Real.cos qz56)) (@HMul.hMul Real Real Real qz0 qz55 (@Neg.neg Real Real.instNeg (Real.sin qz56))) Bool.false 245442383669 1099511627776 17524237745877 109024274475384832 Bool.false 7148256403 549755813888 8713243049019 54512137237692416 (@Enclosure.Real.IsNear.mulLit_ff qz55 (Real.cos qz56) 234469 1048576 1 1048576 1046801 1048576 9287137 12996706304 245442383669 1099511627776 17524237745877 109024274475384832 qz347 (@Enclosure.Real.IsNear.recentre' (Real.cos qz56) Bool.false 1046801 1048576 18574274 25993412608 1046801 1048576 9287137 12996706304 (ep320 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz55 (@Neg.neg Real Real.instNeg (Real.sin qz56)) 234469 1048576 1 1048576 30487 524288 9287137 12996706304 7148256403 549755813888 8713243049019 54512137237692416 qz347 (@Enclosure.Real.IsNear.neg (Real.sin qz56) Bool.true 30487 524288 9287137 12996706304 (@Enclosure.Real.IsNear.recentre' (Real.sin qz56) Bool.true 60974 1048576 18574274 25993412608 30487 524288 9287137 12996706304 (ep324 rfl rfl) rfl)) rfl)

noncomputable def ep326 := @ep266 245442383669 1099511627776 17524237745877 109024274475384832 Bool.false 7148256403 549755813888 8713243049019 54512137237692416 Bool.true 90280515778639638298624 41054825387 549755813888 64422832305243 13628034309423104 Bool.false 139175587785999929835520 253158919415 1099511627776 514347350190087 109024274475384832 (ep267 (BSN.head_sum_c_succ qz5 19 20 rfl rfl) (ep311 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep312 ep325) rfl rfl

noncomputable abbrev qz615 := (@Nat.cast Real Real.instNatCast 21)

noncomputable abbrev qz57 := (@Inv.inv Real Real.instInv (Real.sqrt qz615))

noncomputable abbrev qz616 := (Real.log (Enclosure.sfrac Bool.false 21 1))

noncomputable abbrev qz58 := (@HMul.hMul Real Real Real qz267 qz277 qz616)

noncomputable def ep327 := @Enclosure.Complex.IsNear.of_eq qz598 (Complex.mk (@HMul.hMul Real Real Real qz0 qz57 (Real.cos qz58)) (@HMul.hMul Real Real Real qz0 qz57 (@Neg.neg Real Real.instNeg (Real.sin qz58)))) Bool.false 408096903 2147483648 536929760389 3407008577355776 Bool.true 58969258825 549755813888 8551438750085 54512137237692416 (BSN.cpow_neg_s_mk qz12 140505 1000 21 qz13 rfl)

noncomputable abbrev qz617 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 21) qz14)

noncomputable def ep328 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz615) 4805179 1048576 1 1048576 114408 114410 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz615) (Real.sqrt qz617) Bool.false 4805179 1048576 1 1048576 (BSN.sqrt_natCast_div_one 21) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz617) Bool.false 4805179 1048576 1 1048576 4805179 1048576 1 1048576 (BSN.sqrt_enclosure 21 1 2402589 2402590 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep329 := BSN.log_dyadic_bound 5 37 4 3 269401272945 524288 198314 1658093375 234375 142571 42 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 5) (BSN.artanhQ 37) 0 3 1658093375 269401272945 234375 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep330 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz616 140505 1000 0 1 3427826275261687 1125899906842624 125000000099157 24789250000000000000 96325346161128666387 225179981368524800 3512625002786410857 4957850000000000000000 qz18 (BSN.isNear_log_sfrac 21 1 3427826275261687 1125899906842624 125000000099157 24789250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz617) Bool.false 57509381830540779323392 18889465931478580854784 1000000000793256 198314000000000000000 3427826275261687 1125899906842624 125000000099157 24789250000000000000 (BSN.log_rat_reduce_isNear 21 1 4 42 32 142571 524288 24973259072661432 36028797018963968 198314 1000000000000000 rfl rfl rfl rfl (ep329 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep331 := nat_lit 1482934389055506833244205680100000000

noncomputable def ep332 := BSN.cos_dyadic_bound_f 1103520700 2147483648 2 1 1048576 397016 ep331 ep66 ep331 ep331 ep67 ep331 913152 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1103520700) qz15 0 1 ep331 ep66 ep331 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1103520700) qz16 0 1 ep331 ep67 ep331 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz348 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 224274923) qz17)

noncomputable def ep333 := @Enclosure.Real.IsNear.cos_image qz58 qz348 Bool.false 224274923 524288 93 131072 Bool.false 913152 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz58 Bool.false 96325346161128666387 225179981368524800 3512625002786410857 4957850000000000000000 224274923 524288 93 131072 (ep330 rfl) rfl) (Enclosure.sfrac_false_div 224274923 524288) (BSN.cos_reduce0 qz348 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 38826682934217173630976) qz19) 226375608064910080 72057594037927936 Bool.false 913152 1048576 68 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q0 224274923 524288 226375608064910080 72057594037927936 68 38826682934217173630976 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 913152 1048576 38826682934217173630976 75557863725914323419136 1103520700 2147483648 397016 396628 (ep332 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep334 := BSN.sin_dyadic_bound_f 1103520700 2147483648 2 1 1048576 397016 ep331 ep70 ep331 ep331 ep71 ep331 515425 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1103520700) qz20 0 1 ep331 ep70 ep331 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1103520700) qz21 0 1 ep331 ep71 ep331 rfl rfl rfl rfl) rfl rfl

noncomputable def ep335 := @Enclosure.Real.IsNear.sin_image qz58 qz348 Bool.false 224274923 524288 93 131072 Bool.false 515425 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz58 Bool.false 96325346161128666387 225179981368524800 3512625002786410857 4957850000000000000000 224274923 524288 93 131072 (ep330 rfl) rfl) (Enclosure.sfrac_false_div 224274923 524288) (BSN.sin_reduce0 qz348 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 38826682934217173630976) qz19) 226375608064910080 72057594037927936 Bool.false 515425 1048576 68 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q0 224274923 524288 226375608064910080 72057594037927936 68 38826682934217173630976 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 515425 1048576 38826682934217173630976 75557863725914323419136 1103520700 2147483648 397016 396628 (ep334 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz349 := (@Enclosure.Real.IsNear.recentre' qz57 Bool.false 228818 1048576 2 1048576 114409 524288 1 524288 (ep328 rfl rfl) rfl)

noncomputable def ep336 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz57 (Real.cos qz58)) (@HMul.hMul Real Real Real qz0 qz57 (@Neg.neg Real Real.instNeg (Real.sin qz58))) Bool.false 408096903 2147483648 536929760389 3407008577355776 Bool.true 58969258825 549755813888 8551438750085 54512137237692416 (@Enclosure.Real.IsNear.mulLit_ff qz57 (Real.cos qz58) 114409 524288 1 524288 3567 4096 9287137 12996706304 408096903 2147483648 536929760389 3407008577355776 qz349 (@Enclosure.Real.IsNear.recentre' (Real.cos qz58) Bool.false 913152 1048576 18574274 25993412608 3567 4096 9287137 12996706304 (ep333 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz57 (@Neg.neg Real Real.instNeg (Real.sin qz58)) 114409 524288 1 524288 515425 1048576 9287137 12996706304 58969258825 549755813888 8551438750085 54512137237692416 qz349 (@Enclosure.Real.IsNear.neg (Real.sin qz58) Bool.false 515425 1048576 9287137 12996706304 (@Enclosure.Real.IsNear.recentre' (Real.sin qz58) Bool.false 515425 1048576 18574274 25993412608 515425 1048576 9287137 12996706304 (ep335 rfl rfl) rfl)) rfl)

noncomputable def ep337 := @ep264 408096903 2147483648 536929760389 3407008577355776 Bool.true 58969258825 549755813888 8551438750085 54512137237692416 Bool.false 136189078863859417088 63417981781 549755813888 66570551346799 13628034309423104 Bool.false 74338202026579926712320 135220401765 1099511627776 531450227690257 109024274475384832 (ep265 (BSN.head_sum_c_succ qz5 20 21 rfl rfl) (ep326 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep327 ep336) rfl rfl

noncomputable abbrev qz618 := (@Nat.cast Real Real.instNatCast 22)

noncomputable abbrev qz59 := (@Inv.inv Real Real.instInv (Real.sqrt qz618))

noncomputable abbrev qz619 := (Real.log (Enclosure.sfrac Bool.false 22 1))

noncomputable abbrev qz60 := (@HMul.hMul Real Real Real qz267 qz277 qz619)

noncomputable def ep338 := @Enclosure.Complex.IsNear.of_eq qz597 (Complex.mk (@HMul.hMul Real Real Real qz0 qz59 (Real.cos qz60)) (@HMul.hMul Real Real Real qz0 qz59 (@Neg.neg Real Real.instNeg (Real.sin qz60)))) Bool.false 168777710505 1099511627776 16684570252073 109024274475384832 Bool.true 81340543779 549755813888 8340933070763 54512137237692416 (BSN.cpow_neg_s_mk qz12 140505 1000 22 qz13 rfl)

noncomputable abbrev qz620 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 22) qz14)

noncomputable def ep339 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz618) 4918257 1048576 1 1048576 111778 111779 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz618) (Real.sqrt qz620) Bool.false 4918257 1048576 1 1048576 (BSN.sqrt_natCast_div_one 22) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz620) Bool.false 4918257 1048576 1 1048576 4918257 1048576 1 1048576 (BSN.sqrt_enclosure 22 1 2459128 2459129 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep340 := BSN.log_dyadic_bound 6 38 4 3 316148320320 524288 198314 2667271104 699840 166961 44 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 6) (BSN.artanhQ 38) 0 3 2667271104 316148320320 699840 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep341 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz619 140505 1000 0 1 3480203401436407 1125899906842624 125000000099157 24789250000000000000 97797195783764473107 225179981368524800 3512625002786410857 4957850000000000000000 qz18 (BSN.isNear_log_sfrac 22 1 3480203401436407 1125899906842624 125000000099157 24789250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz620) Bool.false 58388124189833310502912 18889465931478580854784 1000000000793256 198314000000000000000 3480203401436407 1125899906842624 125000000099157 24789250000000000000 (BSN.log_rat_reduce_isNear 22 1 4 44 32 166961 524288 24973259072661432 36028797018963968 198314 1000000000000000 rfl rfl rfl rfl (ep340 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep342 := nat_lit 263048006436721388238920449185204815924248074223745880309679657075486599126561

noncomputable def ep343 := nat_lit 54179328978123948583171358581473117541198499062099066051974427283316776481

noncomputable def ep344 := nat_lit 789035660652207916819595004838451501537661825673113442796935022371893163826721

noncomputable def ep345 := BSN.cos_dyadic_bound_f 1647135027 2147483648 3 2 1048576 397016 ep342 ep102 ep343 ep344 ep104 ep343 754965 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1647135027) qz15 0 2 ep342 ep102 ep343 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1647135027) qz16 0 2 ep344 ep104 ep343 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz350 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 14231365) (@Nat.cast Real Real.instNatCast 32768))

noncomputable abbrev qz621 := (@Nat.cast Real Real.instNatCast 4722366482869645213696)

noncomputable def ep346 := @Enclosure.Real.IsNear.cos_image qz60 qz350 Bool.false 14231365 32768 93 131072 Bool.false 754965 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz60 Bool.false 97797195783764473107 225179981368524800 3512625002786410857 4957850000000000000000 14231365 32768 93 131072 (ep341 rfl) rfl) (Enclosure.sfrac_false_div 14231365 32768) (BSN.cos_reduce0 qz350 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 3622088231563915427840) qz621) 226375608064910080 72057594037927936 Bool.false 754965 1048576 69 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q0 14231365 32768 226375608064910080 72057594037927936 69 3622088231563915427840 4722366482869645213696 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 754965 1048576 3622088231563915427840 4722366482869645213696 1647135027 2147483648 397016 396628 (ep345 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep347 := nat_lit 7360660906340133026843694958383351441

noncomputable def ep348 := BSN.sin_dyadic_bound_f 1647135027 2147483648 2 1 1048576 397016 ep347 ep70 ep347 ep347 ep71 ep347 727694 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1647135027) qz20 0 1 ep347 ep70 ep347 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1647135027) qz21 0 1 ep347 ep71 ep347 rfl rfl rfl rfl) rfl rfl

noncomputable def ep349 := @Enclosure.Real.IsNear.sin_image qz60 qz350 Bool.false 14231365 32768 93 131072 Bool.false 727694 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz60 Bool.false 97797195783764473107 225179981368524800 3512625002786410857 4957850000000000000000 14231365 32768 93 131072 (ep341 rfl) rfl) (Enclosure.sfrac_false_div 14231365 32768) (BSN.sin_reduce0 qz350 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 3622088231563915427840) qz621) 226375608064910080 72057594037927936 Bool.false 727694 1048576 69 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q0 14231365 32768 226375608064910080 72057594037927936 69 3622088231563915427840 4722366482869645213696 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 727694 1048576 3622088231563915427840 4722366482869645213696 1647135027 2147483648 397016 396628 (ep348 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz351 := (@Enclosure.Real.IsNear.recentre' qz59 Bool.false 223557 1048576 1 1048576 223557 1048576 1 1048576 (ep339 rfl rfl) rfl)

noncomputable def ep350 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz59 (Real.cos qz60)) (@HMul.hMul Real Real Real qz0 qz59 (@Neg.neg Real Real.instNeg (Real.sin qz60))) Bool.false 168777710505 1099511627776 16684570252073 109024274475384832 Bool.true 81340543779 549755813888 8340933070763 54512137237692416 (@Enclosure.Real.IsNear.mulLit_ff qz59 (Real.cos qz60) 223557 1048576 1 1048576 754965 1048576 9287137 12996706304 168777710505 1099511627776 16684570252073 109024274475384832 qz351 (@Enclosure.Real.IsNear.recentre' (Real.cos qz60) Bool.false 754965 1048576 18574274 25993412608 754965 1048576 9287137 12996706304 (ep346 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz59 (@Neg.neg Real Real.instNeg (Real.sin qz60)) 223557 1048576 1 1048576 363847 524288 9287137 12996706304 81340543779 549755813888 8340933070763 54512137237692416 qz351 (@Enclosure.Real.IsNear.neg (Real.sin qz60) Bool.false 363847 524288 9287137 12996706304 (@Enclosure.Real.IsNear.recentre' (Real.sin qz60) Bool.false 727694 1048576 18574274 25993412608 363847 524288 9287137 12996706304 (ep349 rfl rfl) rfl)) rfl)

noncomputable def ep351 := @ep262 168777710505 1099511627776 16684570252073 109024274475384832 Bool.true 81340543779 549755813888 8340933070763 54512137237692416 Bool.false 162515335983125544042496 295613674067 1099511627776 549248981026465 109024274475384832 Bool.true 15096671668053353693184 27460685793 1099511627776 548132093831783 109024274475384832 (ep263 (BSN.head_sum_c_succ qz5 21 22 rfl rfl) (ep337 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep338 ep350) rfl rfl

noncomputable abbrev qz622 := (@Nat.cast Real Real.instNatCast 23)

noncomputable abbrev qz61 := (@Inv.inv Real Real.instInv (Real.sqrt qz622))

noncomputable abbrev qz623 := (Real.log (Enclosure.sfrac Bool.false 23 1))

noncomputable abbrev qz62 := (@HMul.hMul Real Real Real qz267 qz277 qz623)

noncomputable def ep352 := @Enclosure.Complex.IsNear.of_eq qz596 (Complex.mk (@HMul.hMul Real Real Real qz0 qz61 (Real.cos qz62)) (@HMul.hMul Real Real Real qz0 qz61 (@Neg.neg Real Real.instNeg (Real.sin qz62)))) Bool.false 10683552909 68719476736 1020133499605 6814017154711552 Bool.true 152782262325 1099511627776 16313902690499 109024274475384832 (BSN.cpow_neg_s_mk qz12 140505 1000 23 qz13 rfl)

noncomputable abbrev qz624 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 23) qz14)

noncomputable def ep353 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz622) 5028793 1048576 1 1048576 109321 109322 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz622) (Real.sqrt qz624) Bool.false 5028793 1048576 1 1048576 (BSN.sqrt_natCast_div_one 23) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz624) Bool.false 5028793 1048576 1 1048576 5028793 1048576 1 1048576 (BSN.sqrt_enclosure 23 1 2514396 2514397 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep354 := BSN.log_dyadic_bound 7 39 4 3 369468094905 524288 198314 4046006391 1764735 190266 46 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 7) (BSN.artanhQ 39) 0 3 4046006391 369468094905 1764735 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep355 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz623 140505 1000 0 1 3530250507853047 1125899906842624 125000000099157 24789250000000000000 99203569521178473747 225179981368524800 3512625002786410857 4957850000000000000000 qz18 (BSN.isNear_log_sfrac 23 1 3530250507853047 1125899906842624 125000000099157 24789250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz624) Bool.false 59227775304360265777152 18889465931478580854784 1000000000793256 198314000000000000000 3530250507853047 1125899906842624 125000000099157 24789250000000000000 (BSN.log_rat_reduce_isNear 23 1 4 46 32 190266 524288 24973259072661432 36028797018963968 198314 1000000000000000 rfl rfl rfl rfl (ep354 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep356 := nat_lit 215093098359888846170665982022919493632974564510473086813909535577025365830241

noncomputable def ep357 := nat_lit 36228399906678075206828632676150818062382420096379700597019130341411940961

noncomputable def ep358 := nat_lit 645206838279853182361584288803406179262798928691226501040534568470393273608801

noncomputable def ep359 := BSN.cos_dyadic_bound_f 1566322347 2147483648 3 2 1048576 397016 ep356 ep102 ep357 ep358 ep104 ep357 781808 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1566322347) qz15 0 2 ep356 ep102 ep357 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1566322347) qz16 0 2 ep358 ep104 ep357 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz352 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 230976309) qz17)

noncomputable def ep360 := @Enclosure.Real.IsNear.cos_image qz62 qz352 Bool.false 230976309 524288 93 131072 Bool.false 781808 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz62 Bool.false 99203569521178473747 225179981368524800 3512625002786410857 4957850000000000000000 230976309 524288 93 131072 (ep355 rfl) rfl) (Enclosure.sfrac_false_div 230976309 524288) (BSN.cos_reduce0 qz352 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 55110068284040044085248) qz19) 226375608064910080 72057594037927936 Bool.false 781808 1048576 70 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q0 230976309 524288 226375608064910080 72057594037927936 70 55110068284040044085248 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 781808 1048576 55110068284040044085248 75557863725914323419136 1566322347 2147483648 397016 396628 (ep359 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep361 := nat_lit 6019003231987674818283639755823151281

noncomputable def ep362 := BSN.sin_dyadic_bound_f 1566322347 2147483648 2 1 1048576 397016 ep361 ep70 ep361 ep361 ep71 ep361 698775 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1566322347) qz20 0 1 ep361 ep70 ep361 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1566322347) qz21 0 1 ep361 ep71 ep361 rfl rfl rfl rfl) rfl rfl

noncomputable def ep363 := @Enclosure.Real.IsNear.sin_image qz62 qz352 Bool.false 230976309 524288 93 131072 Bool.false 698775 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz62 Bool.false 99203569521178473747 225179981368524800 3512625002786410857 4957850000000000000000 230976309 524288 93 131072 (ep355 rfl) rfl) (Enclosure.sfrac_false_div 230976309 524288) (BSN.sin_reduce0 qz352 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 55110068284040044085248) qz19) 226375608064910080 72057594037927936 Bool.false 698775 1048576 70 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q0 230976309 524288 226375608064910080 72057594037927936 70 55110068284040044085248 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 698775 1048576 55110068284040044085248 75557863725914323419136 1566322347 2147483648 397016 396628 (ep362 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz353 := (@Enclosure.Real.IsNear.recentre' qz61 Bool.false 218643 1048576 1 1048576 218643 1048576 1 1048576 (ep353 rfl rfl) rfl)

noncomputable def ep364 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz61 (Real.cos qz62)) (@HMul.hMul Real Real Real qz0 qz61 (@Neg.neg Real Real.instNeg (Real.sin qz62))) Bool.false 10683552909 68719476736 1020133499605 6814017154711552 Bool.true 152782262325 1099511627776 16313902690499 109024274475384832 (@Enclosure.Real.IsNear.mulLit_ff qz61 (Real.cos qz62) 218643 1048576 1 1048576 48863 65536 9287137 12996706304 10683552909 68719476736 1020133499605 6814017154711552 qz353 (@Enclosure.Real.IsNear.recentre' (Real.cos qz62) Bool.false 781808 1048576 18574274 25993412608 48863 65536 9287137 12996706304 (ep360 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz61 (@Neg.neg Real Real.instNeg (Real.sin qz62)) 218643 1048576 1 1048576 698775 1048576 9287137 12996706304 152782262325 1099511627776 16313902690499 109024274475384832 qz353 (@Enclosure.Real.IsNear.neg (Real.sin qz62) Bool.false 698775 1048576 9287137 12996706304 (@Enclosure.Real.IsNear.recentre' (Real.sin qz62) Bool.false 698775 1048576 18574274 25993412608 698775 1048576 9287137 12996706304 (ep363 rfl rfl) rfl)) rfl)

noncomputable def ep365 := @ep260 10683552909 68719476736 1020133499605 6814017154711552 Bool.true 152782262325 1099511627776 16313902690499 109024274475384832 Bool.false 32061107647296303005696 466550520611 1099511627776 565571117020145 109024274475384832 Bool.true 198179217280367295725568 90121474059 549755813888 282222998261141 54512137237692416 (ep261 (BSN.head_sum_c_succ qz5 22 23 rfl rfl) (ep351 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep352 ep364) rfl rfl

noncomputable abbrev qz625 := (@Nat.cast Real Real.instNatCast 24)

noncomputable abbrev qz63 := (@Inv.inv Real Real.instInv (Real.sqrt qz625))

noncomputable abbrev qz626 := (Real.log (Enclosure.sfrac Bool.false 24 1))

noncomputable abbrev qz64 := (@HMul.hMul Real Real Real qz267 qz277 qz626)

noncomputable def ep366 := @Enclosure.Complex.IsNear.of_eq qz595 (Complex.mk (@HMul.hMul Real Real Real qz0 qz63 (Real.cos qz64)) (@HMul.hMul Real Real Real qz0 qz63 (@Neg.neg Real Real.instNeg (Real.sin qz64)))) Bool.false 51090467183 274877906944 3994000194319 27256068618846208 Bool.true 46388886509 549755813888 7962153827547 54512137237692416 (BSN.cpow_neg_s_mk qz12 140505 1000 24 qz13 rfl)

noncomputable abbrev qz627 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 24) qz14)

noncomputable def ep367 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz625) 5136953 1048576 1 1048576 107019 107020 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz625) (Real.sqrt qz627) Bool.false 5136953 1048576 1 1048576 (BSN.sqrt_natCast_div_one 24) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz627) Bool.false 5136953 1048576 1 1048576 5136953 1048576 1 1048576 (BSN.sqrt_enclosure 24 1 2568476 2568477 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep368 := BSN.log_dyadic_bound 8 40 4 3 430080000000 524288 198314 5875957760 3932160 212580 48 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 8) (BSN.artanhQ 40) 0 3 5875957760 430080000000 3932160 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep369 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz626 140505 1000 0 1 3578169457974519 1125899906842624 125000000099157 24789250000000000000 100550139938541958419 225179981368524800 3512625002786410857 4957850000000000000000 qz18 (BSN.isNear_log_sfrac 24 1 3578169457974519 1125899906842624 125000000099157 24789250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz627) Bool.false 60031721881041427759104 18889465931478580854784 1000000000793256 198314000000000000000 3578169457974519 1125899906842624 125000000099157 24789250000000000000 (BSN.log_rat_reduce_isNear 24 1 4 48 32 212580 524288 24973259072661432 36028797018963968 198314 1000000000000000 rfl rfl rfl rfl (ep368 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep370 := nat_lit 701505478720779687116265994336527376

noncomputable def ep371 := BSN.cos_dyadic_bound_f 915182626 2147483648 2 1 1048576 397016 ep370 ep66 ep370 ep370 ep67 ep370 954788 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 915182626) qz15 0 1 ep370 ep66 ep370 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 915182626) qz16 0 1 ep370 ep67 ep370 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz354 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 117055769) qz24)

noncomputable def ep372 := @Enclosure.Real.IsNear.cos_image qz64 qz354 Bool.false 117055769 262144 743 1048576 Bool.false 954788 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz64 Bool.false 100550139938541958419 225179981368524800 3512625002786410857 4957850000000000000000 117055769 262144 743 1048576 (ep369 rfl) rfl) (Enclosure.sfrac_false_div 117055769 262144) (BSN.cos_reduce0 qz354 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 16100063037687634853888) qz291) 226375608064910080 72057594037927936 Bool.false 954788 1048576 71 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q0 117055769 262144 226375608064910080 72057594037927936 71 16100063037687634853888 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 954788 1048576 16100063037687634853888 37778931862957161709568 915182626 2147483648 397016 396628 (ep371 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep373 := BSN.sin_dyadic_bound_f 915182626 2147483648 2 1 1048576 397016 ep370 ep70 ep370 ep370 ep71 ep370 433462 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 915182626) qz20 0 1 ep370 ep70 ep370 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 915182626) qz21 0 1 ep370 ep71 ep370 rfl rfl rfl rfl) rfl rfl

noncomputable def ep374 := @Enclosure.Real.IsNear.sin_image qz64 qz354 Bool.false 117055769 262144 743 1048576 Bool.false 433462 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz64 Bool.false 100550139938541958419 225179981368524800 3512625002786410857 4957850000000000000000 117055769 262144 743 1048576 (ep369 rfl) rfl) (Enclosure.sfrac_false_div 117055769 262144) (BSN.sin_reduce0 qz354 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 16100063037687634853888) qz291) 226375608064910080 72057594037927936 Bool.false 433462 1048576 71 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q0 117055769 262144 226375608064910080 72057594037927936 71 16100063037687634853888 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 433462 1048576 16100063037687634853888 37778931862957161709568 915182626 2147483648 397016 396628 (ep373 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz355 := (@Enclosure.Real.IsNear.recentre' qz63 Bool.false 214039 1048576 1 1048576 214039 1048576 1 1048576 (ep367 rfl rfl) rfl)

noncomputable def ep375 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz63 (Real.cos qz64)) (@HMul.hMul Real Real Real qz0 qz63 (@Neg.neg Real Real.instNeg (Real.sin qz64))) Bool.false 51090467183 274877906944 3994000194319 27256068618846208 Bool.true 46388886509 549755813888 7962153827547 54512137237692416 (@Enclosure.Real.IsNear.mulLit_ff qz63 (Real.cos qz64) 214039 1048576 1 1048576 238697 262144 74197939 103973650432 51090467183 274877906944 3994000194319 27256068618846208 qz355 (@Enclosure.Real.IsNear.recentre' (Real.cos qz64) Bool.false 954788 1048576 148395878 207947300864 238697 262144 74197939 103973650432 (ep372 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz63 (@Neg.neg Real Real.instNeg (Real.sin qz64)) 214039 1048576 1 1048576 216731 524288 74197939 103973650432 46388886509 549755813888 7962153827547 54512137237692416 qz355 (@Enclosure.Real.IsNear.neg (Real.sin qz64) Bool.false 216731 524288 74197939 103973650432 (@Enclosure.Real.IsNear.recentre' (Real.sin qz64) Bool.false 433462 1048576 148395878 207947300864 216731 524288 74197939 103973650432 (ep374 rfl rfl) rfl)) rfl)

noncomputable def ep376 := @ep258 51090467183 274877906944 3994000194319 27256068618846208 Bool.true 46388886509 549755813888 7962153827547 54512137237692416 Bool.false 184418993325401851297792 670912389343 1099511627776 581547117797421 109024274475384832 Bool.true 75047364378205181968384 17063795071 68719476736 18136572005543 3407008577355776 (ep259 (BSN.head_sum_c_succ qz5 23 24 rfl rfl) (ep365 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep366 ep375) rfl rfl

theorem EMRow49.d8 : Enclosure.Complex.IsNear qz48 Bool.false 670912389343 1099511627776 581547117797421 109024274475384832 Bool.true 17063795071 68719476736 18136572005543 3407008577355776 := ep257 (BSN.head_sum_c_succ qz5 24 25 rfl rfl) (ep376 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable abbrev qz65 := (BSN.headSumC qz271 33)

noncomputable abbrev qz628 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 32) qz7)

noncomputable def ep377 := @Enclosure.Complex.IsNear.of_eq qz65 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 32) qz628) Bool.false 367559533959 549755813888 349560000476849 54512137237692416 Bool.false 17431680189 274877906944 348910167144789 54512137237692416

noncomputable def ep378 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 32) qz628 Bool.false 232370545755 274877906944 42827751411361 6814017154711552 Bool.false 68490534909 1099511627776 684047666108601 109024274475384832 Bool.true

noncomputable abbrev qz629 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 31) qz7)

noncomputable def ep379 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 32) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 31) qz629) Bool.false 232370545755 274877906944 42827751411361 6814017154711552 Bool.false 68490534909 1099511627776 684047666108601 109024274475384832

noncomputable def ep380 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 31) qz629 Bool.false 219782635395 274877906944 20975785621143 3407008577355776 Bool.true 122459628113 1099511627776 669954756951795 109024274475384832 Bool.false

noncomputable abbrev qz630 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 30) qz7)

noncomputable def ep381 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 31) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 30) qz630) Bool.false 219782635395 274877906944 20975785621143 3407008577355776 Bool.true 122459628113 1099511627776 669954756951795 109024274475384832

noncomputable def ep382 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 30) qz630 Bool.false 345730824441 549755813888 328452102205525 54512137237692416 Bool.true 51200331767 1099511627776 655694115288317 109024274475384832 Bool.false

noncomputable abbrev qz631 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 29) qz7)

noncomputable def ep383 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 30) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 29) qz631) Bool.false 345730824441 549755813888 328452102205525 54512137237692416 Bool.true 51200331767 1099511627776 655694115288317 109024274475384832

noncomputable def ep384 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 29) qz631 Bool.false 754133592357 1099511627776 642405455898509 109024274475384832 Bool.false 71558238029 549755813888 320564163859823 54512137237692416 Bool.true

noncomputable abbrev qz632 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 28) qz7)

noncomputable def ep385 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 29) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 28) qz632) Bool.false 754133592357 1099511627776 642405455898509 109024274475384832 Bool.false 71558238029 549755813888 320564163859823 54512137237692416

noncomputable def ep386 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 28) qz632 Bool.false 961007837837 1099511627776 627578930225045 109024274475384832 Bool.false 15455176593 137438953472 19574861657383 3407008577355776 Bool.true

noncomputable abbrev qz633 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 27) qz7)

noncomputable def ep387 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 28) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 27) qz633) Bool.false 961007837837 1099511627776 627578930225045 109024274475384832 Bool.false 15455176593 137438953472 19574861657383 3407008577355776

noncomputable def ep388 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 27) qz633 Bool.false 512128950103 549755813888 306277348687289 54512137237692416 Bool.true 78285729621 1099511627776 611303199098761 109024274475384832 Bool.true

noncomputable abbrev qz634 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 26) qz7)

noncomputable def ep389 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 27) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 26) qz634) Bool.false 512128950103 549755813888 306277348687289 54512137237692416 Bool.true 78285729621 1099511627776 611303199098761 109024274475384832

noncomputable def ep390 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 26) qz634 Bool.false 111149307101 137438953472 74651352554419 13628034309423104 Bool.true 246378317821 1099511627776 595943396157137 109024274475384832 Bool.false

noncomputable abbrev qz635 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 25) qz7)

noncomputable def ep391 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 26) (@HAdd.hAdd Complex Complex Complex qz4 qz48 qz635) Bool.false 111149307101 137438953472 74651352554419 13628034309423104 Bool.true 246378317821 1099511627776 595943396157137 109024274475384832

noncomputable def ep392 := @Enclosure.Complex.IsNear.addLitP qz48 qz635 Bool.false 670912389343 1099511627776 581547117797421 109024274475384832 Bool.true 17063795071 68719476736 18136572005543 3407008577355776 Bool.false

noncomputable abbrev qz636 := (Real.log (Enclosure.sfrac Bool.false 25 1))

noncomputable abbrev qz66 := (@HMul.hMul Real Real Real qz267 qz277 qz636)

noncomputable abbrev qz356 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 25)))

noncomputable def ep393 := @Enclosure.Complex.IsNear.of_eq qz635 (Complex.mk (@HMul.hMul Real Real Real qz0 qz356 (Real.cos qz66)) (@HMul.hMul Real Real Real qz0 qz356 (@Neg.neg Real Real.instNeg (Real.sin qz66)))) Bool.false 218282067465 1099511627776 15663702637931 109024274475384832 Bool.false 26642403315 1099511627776 15573091979761 109024274475384832 (BSN.cpow_neg_s_mk qz12 140505 1000 25 qz13 rfl)

noncomputable abbrev qz357 := (Real.sqrt (@Nat.cast Real Real.instNatCast 25))

noncomputable abbrev qz358 := (@Nat.cast Real Real.instNatCast 25)

noncomputable abbrev qz637 := (@HDiv.hDiv Real Real Real qz1 qz358 qz14)

noncomputable def ep394 := @Enclosure.Real.IsNear.inv_image qz357 5242881 1048576 1 1048576 104857 104858 524288 (@Enclosure.Real.IsNear.of_eq qz357 (Real.sqrt qz637) Bool.false 5242881 1048576 1 1048576 (BSN.sqrt_natCast_div_one 25) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz637) Bool.false 5242881 1048576 1 1048576 5242881 1048576 1 1048576 (BSN.sqrt_enclosure 25 1 2621440 2621441 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep395 := BSN.log_dyadic_bound 9 41 5 4 7545754341519345 524288 198314 124828057765224 4519905705 233982 50 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 9) (BSN.artanhQ 41) 0 4 124828057765224 7545754341519345 4519905705 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep396 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz636 140505 1000 0 1 3624129903009015 1125899906842624 125000000099157 24789250000000000000 20368334880891266103 45035996273704960 3512625002786410857 4957850000000000000000 qz18 (BSN.isNear_log_sfrac 25 1 3624129903009015 1125899906842624 125000000099157 24789250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz637) Bool.false 60802810194841294602240 18889465931478580854784 1000000000793256 198314000000000000000 3624129903009015 1125899906842624 125000000099157 24789250000000000000 (BSN.log_rat_reduce_isNear 25 1 4 50 32 233982 524288 24973259072661432 36028797018963968 198314 1000000000000000 rfl rfl rfl rfl (ep395 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep397 := nat_lit 6044169758001053161852265203409059492914460437164013623744757951062300168355840

noncomputable def ep398 := nat_lit 8806520047638094490213897043884464743768799987245993766669712538799072935936

noncomputable def ep399 := nat_lit 15815710238497058509009872080381247633762246897354970738947377003909873370464256

noncomputable def ep400 := BSN.sin_dyadic_bound_f 3112436796 2147483648 3 2 1048576 397016 ep397 ep95 ep398 ep399 ep98 ep398 1040851 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3112436796) qz20 0 2 ep397 ep95 ep398 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3112436796) qz21 0 2 ep399 ep98 ep398 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz359 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 118559313) qz24)

noncomputable def ep401 := @Enclosure.Real.IsNear.cos_image qz66 qz359 Bool.false 118559313 262144 743 1048576 Bool.false 1040851 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz66 Bool.false 20368334880891266103 45035996273704960 3512625002786410857 4957850000000000000000 118559313 262144 743 1048576 (ep396 rfl) rfl) (Enclosure.sfrac_false_div 118559313 262144) (BSN.cos_reduce3 qz359 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 54754567176308912029696) qz291) 226375608064910080 72057594037927936 Bool.false 1040851 1048576 71 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q3 118559313 262144 226375608064910080 72057594037927936 71 54754567176308912029696 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1040851 1048576 54754567176308912029696 37778931862957161709568 3112436796 2147483648 397016 396628 (ep400 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep402 := nat_lit 3361786096688424243024686845024537258171930820641005788198940956162966348169216

noncomputable def ep403 := nat_lit 10067745249969996540093632740985842845028254861948525377063483443411300898635776

noncomputable def ep404 := BSN.cos_dyadic_bound_f 3112436796 2147483648 3 2 1048576 397016 ep402 ep102 ep398 ep403 ep104 ep398 127041 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3112436796) qz15 0 2 ep402 ep102 ep398 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3112436796) qz16 0 2 ep403 ep104 ep398 rfl rfl rfl rfl) rfl rfl

noncomputable def ep405 := @Enclosure.Real.IsNear.sin_image qz66 qz359 Bool.false 118559313 262144 743 1048576 Bool.true 127041 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz66 Bool.false 20368334880891266103 45035996273704960 3512625002786410857 4957850000000000000000 118559313 262144 743 1048576 (ep396 rfl) rfl) (Enclosure.sfrac_false_div 118559313 262144) (BSN.sin_reduce3 qz359 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 54754567176308912029696) qz291) 226375608064910080 72057594037927936 Bool.false 127041 1048576 71 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q3 118559313 262144 226375608064910080 72057594037927936 71 54754567176308912029696 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 127041 1048576 54754567176308912029696 37778931862957161709568 3112436796 2147483648 397016 396628 (ep404 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz360 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 25))) Bool.false 209715 1048576 1 1048576 209715 1048576 1 1048576 (ep394 rfl rfl) rfl)

noncomputable def ep406 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz356 (Real.cos qz66)) (@HMul.hMul Real Real Real qz0 qz356 (@Neg.neg Real Real.instNeg (Real.sin qz66))) Bool.false 218282067465 1099511627776 15663702637931 109024274475384832 Bool.false 26642403315 1099511627776 15573091979761 109024274475384832 (@Enclosure.Real.IsNear.mulLit_ff qz356 (Real.cos qz66) 209715 1048576 1 1048576 1040851 1048576 74197939 103973650432 218282067465 1099511627776 15663702637931 109024274475384832 qz360 (@Enclosure.Real.IsNear.recentre' (Real.cos qz66) Bool.false 1040851 1048576 148395878 207947300864 1040851 1048576 74197939 103973650432 (ep401 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz356 (@Neg.neg Real Real.instNeg (Real.sin qz66)) 209715 1048576 1 1048576 127041 1048576 74197939 103973650432 26642403315 1099511627776 15573091979761 109024274475384832 qz360 (@Enclosure.Real.IsNear.neg (Real.sin qz66) Bool.true 127041 1048576 74197939 103973650432 (@Enclosure.Real.IsNear.recentre' (Real.sin qz66) Bool.true 127041 1048576 148395878 207947300864 127041 1048576 74197939 103973650432 (ep405 rfl rfl) rfl)) rfl)

noncomputable def ep407 := @ep392 218282067465 1099511627776 15663702637931 109024274475384832 Bool.false 26642403315 1099511627776 15573091979761 109024274475384832 Bool.false 977679644614360205099008 111149307101 137438953472 74651352554419 13628034309423104 Bool.true 16930989079755023712256 246378317821 1099511627776 595943396157137 109024274475384832 EMRow49.d8 (ep393 ep406) rfl rfl

noncomputable abbrev qz638 := (Real.log (Enclosure.sfrac Bool.false 26 1))

noncomputable abbrev qz67 := (@HMul.hMul Real Real Real qz267 qz277 qz638)

noncomputable abbrev qz361 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 26)))

noncomputable def ep408 := @Enclosure.Complex.IsNear.of_eq qz634 (Complex.mk (@HMul.hMul Real Real Real qz0 qz361 (Real.cos qz67)) (@HMul.hMul Real Real Real qz0 qz361 (@Neg.neg Real Real.instNeg (Real.sin qz67)))) Bool.false 67531721699 549755813888 7671938469613 54512137237692416 Bool.false 21011573525 137438953472 1919975367703 13628034309423104 (BSN.cpow_neg_s_mk qz12 140505 1000 26 qz13 rfl)

noncomputable abbrev qz362 := (Real.sqrt (@Nat.cast Real Real.instNatCast 26))

noncomputable abbrev qz363 := (@Nat.cast Real Real.instNatCast 26)

noncomputable abbrev qz639 := (@HDiv.hDiv Real Real Real qz1 qz363 qz14)

noncomputable def ep409 := @Enclosure.Real.IsNear.inv_image qz362 5346709 1048576 1 1048576 102821 102822 524288 (@Enclosure.Real.IsNear.of_eq qz362 (Real.sqrt qz639) Bool.false 5346709 1048576 1 1048576 (BSN.sqrt_natCast_div_one 26) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz639) Bool.false 5346709 1048576 1 1048576 5346709 1048576 1 1048576 (BSN.sqrt_enclosure 26 1 2673354 2673355 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep410 := BSN.log_dyadic_bound 10 42 5 4 9150106136613120 524288 198314 179034245376000 10500000000 254545 52 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 10) (BSN.artanhQ 42) 0 4 179034245376000 9150106136613120 10500000000 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep411 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz638 140505 1000 0 1 3668288609262839 1125899906842624 125000000099157 24789250000000000000 103082578208895038739 225179981368524800 3512625002786410857 4957850000000000000000 qz18 (BSN.isNear_log_sfrac 26 1 3668288609262839 1125899906842624 125000000099157 24789250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz639) Bool.false 61543670347942250676224 18889465931478580854784 1000000000793256 198314000000000000000 3668288609262839 1125899906842624 125000000099157 24789250000000000000 (BSN.log_rat_reduce_isNear 26 1 4 52 32 254545 524288 24973259072661432 36028797018963968 198314 1000000000000000 rfl rfl rfl rfl (ep410 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep412 := nat_lit 4464308239790529127404603548117176576

noncomputable def ep413 := BSN.sin_dyadic_bound_f 1453578676 2147483648 2 1 1048576 397016 ep412 ep70 ep412 ep412 ep71 ep412 656786 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1453578676) qz20 0 1 ep412 ep70 ep412 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1453578676) qz21 0 1 ep412 ep71 ep412 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz364 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 120003915) qz24)

noncomputable def ep414 := @Enclosure.Real.IsNear.cos_image qz67 qz364 Bool.false 120003915 262144 93 131072 Bool.false 656786 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz67 Bool.false 103082578208895038739 225179981368524800 3512625002786410857 4957850000000000000000 120003915 262144 93 131072 (ep411 rfl) rfl) (Enclosure.sfrac_false_div 120003915 262144) (BSN.cos_reduce3 qz364 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 25571626498795304386560) qz291) 226375608064910080 72057594037927936 Bool.false 656786 1048576 72 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q3 120003915 262144 226375608064910080 72057594037927936 72 25571626498795304386560 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 656786 1048576 25571626498795304386560 37778931862957161709568 1453578676 2147483648 397016 396628 (ep413 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep415 := nat_lit 159528094370619687110211175313358850789304957045984124590640410759512058822656

noncomputable def ep416 := nat_lit 19930048059861612514908640914051372559821271543809266724797913645963083776

noncomputable def ep417 := nat_lit 478544423015739338105603708658248449622795228594864755238471636451244250300416

noncomputable def ep418 := BSN.cos_dyadic_bound_f 1453578676 2147483648 3 2 1048576 397016 ep415 ep102 ep416 ep417 ep104 ep416 817400 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1453578676) qz15 0 2 ep415 ep102 ep416 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1453578676) qz16 0 2 ep417 ep104 ep416 rfl rfl rfl rfl) rfl rfl

noncomputable def ep419 := @Enclosure.Real.IsNear.sin_image qz67 qz364 Bool.false 120003915 262144 93 131072 Bool.true 817400 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz67 Bool.false 103082578208895038739 225179981368524800 3512625002786410857 4957850000000000000000 120003915 262144 93 131072 (ep411 rfl) rfl) (Enclosure.sfrac_false_div 120003915 262144) (BSN.sin_reduce3 qz364 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 25571626498795304386560) qz291) 226375608064910080 72057594037927936 Bool.false 817400 1048576 72 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q3 120003915 262144 226375608064910080 72057594037927936 72 25571626498795304386560 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 817400 1048576 25571626498795304386560 37778931862957161709568 1453578676 2147483648 397016 396628 (ep418 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz365 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 26))) Bool.false 205643 1048576 1 1048576 205643 1048576 1 1048576 (ep409 rfl rfl) rfl)

noncomputable def ep420 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz361 (Real.cos qz67)) (@HMul.hMul Real Real Real qz0 qz361 (@Neg.neg Real Real.instNeg (Real.sin qz67))) Bool.false 67531721699 549755813888 7671938469613 54512137237692416 Bool.false 21011573525 137438953472 1919975367703 13628034309423104 (@Enclosure.Real.IsNear.mulLit_ff qz361 (Real.cos qz67) 205643 1048576 1 1048576 328393 524288 9287137 12996706304 67531721699 549755813888 7671938469613 54512137237692416 qz365 (@Enclosure.Real.IsNear.recentre' (Real.cos qz67) Bool.false 656786 1048576 18574274 25993412608 328393 524288 9287137 12996706304 (ep414 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz361 (@Neg.neg Real Real.instNeg (Real.sin qz67)) 205643 1048576 1 1048576 102175 131072 9287137 12996706304 21011573525 137438953472 1919975367703 13628034309423104 qz365 (@Enclosure.Real.IsNear.neg (Real.sin qz67) Bool.true 102175 131072 9287137 12996706304 (@Enclosure.Real.IsNear.recentre' (Real.sin qz67) Bool.true 817400 1048576 18574274 25993412608 102175 131072 9287137 12996706304 (ep419 rfl rfl) rfl)) rfl)

noncomputable def ep421 := @ep390 67531721699 549755813888 7671938469613 54512137237692416 Bool.false 21011573525 137438953472 1919975367703 13628034309423104 Bool.false 70386466944870426607616 512128950103 549755813888 306277348687289 54512137237692416 Bool.true 10759508750902191194112 78285729621 1099511627776 611303199098761 109024274475384832 (ep391 (BSN.head_sum_c_succ qz5 25 26 rfl rfl) (ep407 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep408 ep420) rfl rfl

noncomputable abbrev qz640 := (Real.log (Enclosure.sfrac Bool.false 27 1))

noncomputable abbrev qz68 := (@HMul.hMul Real Real Real qz267 qz277 qz640)

noncomputable abbrev qz366 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 27)))

noncomputable def ep422 := @Enclosure.Complex.IsNear.of_eq qz633 (Complex.mk (@HMul.hMul Real Real Real qz0 qz366 (Real.cos qz68)) (@HMul.hMul Real Real Real qz0 qz366 (@Neg.neg Real Real.instNeg (Real.sin qz68)))) Bool.true 63250062369 1099511627776 15024232850467 109024274475384832 Bool.false 201927142365 1099511627776 15092373937495 109024274475384832 (BSN.cpow_neg_s_mk qz12 140505 1000 27 qz13 rfl)

noncomputable abbrev qz367 := (Real.sqrt (@Nat.cast Real Real.instNatCast 27))

noncomputable abbrev qz368 := (@Nat.cast Real Real.instNatCast 27)

noncomputable abbrev qz641 := (@HDiv.hDiv Real Real Real qz1 qz368 qz14)

noncomputable def ep423 := @Enclosure.Real.IsNear.inv_image qz367 5448561 1048576 1 1048576 100899 100900 524288 (@Enclosure.Real.IsNear.of_eq qz367 (Real.sqrt qz641) Bool.false 5448561 1048576 1 1048576 (BSN.sqrt_natCast_div_one 27) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz641) Bool.false 5448561 1048576 1 1048576 5448561 1048576 1 1048576 (BSN.sqrt_enclosure 27 1 2724280 2724281 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep424 := BSN.log_dyadic_bound 11 43 5 4 11045349262332945 524288 198314 250863800262504 22507682505 274332 54 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 11) (BSN.artanhQ 43) 0 4 250863800262504 11045349262332945 22507682505 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep425 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz640 140505 1000 0 1 3710780868205815 1125899906842624 125000000099157 24789250000000000000 20855330635490321463 45035996273704960 3512625002786410857 4957850000000000000000 qz18 (BSN.isNear_log_sfrac 27 1 3710780868205815 1125899906842624 125000000099157 24789250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz641) Bool.false 62256572154556490711040 18889465931478580854784 1000000000793256 198314000000000000000 3710780868205815 1125899906842624 125000000099157 24789250000000000000 (BSN.log_rat_reduce_isNear 27 1 4 54 32 274332 524288 24973259072661432 36028797018963968 198314 1000000000000000 rfl rfl rfl rfl (ep424 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep426 := nat_lit 1962709876044456214007412570768098239930428587868629641661055236075890725672481

noncomputable def ep427 := nat_lit 3008308645674313869031611515833893006933474806399987504105607489154105005601

noncomputable def ep428 := nat_lit 5882113010842020014284174489272626933777418813993088949974954493249363967006241

noncomputable def ep429 := BSN.cos_dyadic_bound_f 2721386957 2147483648 3 2 1048576 397016 ep426 ep102 ep427 ep428 ep104 ep427 313431 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2721386957) qz15 0 2 ep426 ep102 ep427 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2721386957) qz16 0 2 ep428 ep104 ep427 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz369 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 485576005) qz26)

noncomputable def ep430 := @Enclosure.Real.IsNear.cos_image qz68 qz369 Bool.false 485576005 1048576 93 131072 Bool.true 313431 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz68 Bool.false 20855330635490321463 45035996273704960 3512625002786410857 4957850000000000000000 485576005 1048576 93 131072 (ep425 rfl) rfl) (Enclosure.sfrac_false_div 485576005 1048576) (BSN.cos_reduce2 qz369 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 191500582630012580003840) qz27) 226375608064910080 72057594037927936 Bool.false 313431 1048576 73 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q2 485576005 1048576 226375608064910080 72057594037927936 73 191500582630012580003840 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 313431 1048576 191500582630012580003840 151115727451828646838272 2721386957 2147483648 397016 396628 (ep429 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep431 := nat_lit 3530471129963481734118117338169909717469224678318413364986614938945280022205985

noncomputable def ep432 := nat_lit 9241601412097074700235684705133651528503410436385482642815439570826626745292321

noncomputable def ep433 := BSN.sin_dyadic_bound_f 2721386957 2147483648 3 2 1048576 397016 ep431 ep95 ep427 ep432 ep98 ep427 1000635 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2721386957) qz20 0 2 ep431 ep95 ep427 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2721386957) qz21 0 2 ep432 ep98 ep427 rfl rfl rfl rfl) rfl rfl

noncomputable def ep434 := @Enclosure.Real.IsNear.sin_image qz68 qz369 Bool.false 485576005 1048576 93 131072 Bool.true 1000635 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz68 Bool.false 20855330635490321463 45035996273704960 3512625002786410857 4957850000000000000000 485576005 1048576 93 131072 (ep425 rfl) rfl) (Enclosure.sfrac_false_div 485576005 1048576) (BSN.sin_reduce2 qz369 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 191500582630012580003840) qz27) 226375608064910080 72057594037927936 Bool.false 1000635 1048576 73 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q2 485576005 1048576 226375608064910080 72057594037927936 73 191500582630012580003840 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1000635 1048576 191500582630012580003840 151115727451828646838272 2721386957 2147483648 397016 396628 (ep433 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz370 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 27))) Bool.false 201799 1048576 1 1048576 201799 1048576 1 1048576 (ep423 rfl rfl) rfl)

noncomputable def ep435 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz366 (Real.cos qz68)) (@HMul.hMul Real Real Real qz0 qz366 (@Neg.neg Real Real.instNeg (Real.sin qz68))) Bool.true 63250062369 1099511627776 15024232850467 109024274475384832 Bool.false 201927142365 1099511627776 15092373937495 109024274475384832 (@Enclosure.Real.IsNear.mulLit_ft qz366 (Real.cos qz68) 201799 1048576 1 1048576 313431 1048576 9287137 12996706304 63250062369 1099511627776 15024232850467 109024274475384832 qz370 (@Enclosure.Real.IsNear.recentre' (Real.cos qz68) Bool.true 313431 1048576 18574274 25993412608 313431 1048576 9287137 12996706304 (ep430 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz366 (@Neg.neg Real Real.instNeg (Real.sin qz68)) 201799 1048576 1 1048576 1000635 1048576 9287137 12996706304 201927142365 1099511627776 15092373937495 109024274475384832 qz370 (@Enclosure.Real.IsNear.neg (Real.sin qz68) Bool.true 1000635 1048576 9287137 12996706304 (@Enclosure.Real.IsNear.recentre' (Real.sin qz68) Bool.true 1000635 1048576 18574274 25993412608 1000635 1048576 9287137 12996706304 (ep434 rfl rfl) rfl)) rfl)

noncomputable def ep436 := @ep388 63250062369 1099511627776 15024232850467 109024274475384832 Bool.false 201927142365 1099511627776 15092373937495 109024274475384832 Bool.false 528319646042827056480256 961007837837 1099511627776 627578930225045 109024274475384832 Bool.false 135945170986679710777344 15455176593 137438953472 19574861657383 3407008577355776 (ep389 (BSN.head_sum_c_succ qz5 26 27 rfl rfl) (ep421 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep422 ep435) rfl rfl

noncomputable abbrev qz642 := (Real.log (Enclosure.sfrac Bool.false 28 1))

noncomputable abbrev qz69 := (@HMul.hMul Real Real Real qz267 qz277 qz642)

noncomputable abbrev qz371 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 28)))

noncomputable def ep437 := @Enclosure.Complex.IsNear.of_eq qz632 (Complex.mk (@HMul.hMul Real Real Real qz0 qz371 (Real.cos qz69)) (@HMul.hMul Real Real Real qz0 qz371 (@Neg.neg Real Real.instNeg (Real.sin qz69)))) Bool.true 25859280685 137438953472 1853315709183 13628034309423104 Bool.false 9737531657 549755813888 7366377341695 54512137237692416 (BSN.cpow_neg_s_mk qz12 140505 1000 28 qz13 rfl)

noncomputable abbrev qz372 := (Real.sqrt (@Nat.cast Real Real.instNatCast 28))

noncomputable abbrev qz373 := (@Nat.cast Real Real.instNatCast 28)

noncomputable abbrev qz643 := (@HDiv.hDiv Real Real Real qz1 qz373 qz14)

noncomputable def ep438 := @Enclosure.Real.IsNear.inv_image qz372 5548543 1048576 1 1048576 99081 99082 524288 (@Enclosure.Real.IsNear.of_eq qz372 (Real.sqrt qz643) Bool.false 5548543 1048576 1 1048576 (BSN.sqrt_natCast_div_one 28) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz643) Bool.false 5548543 1048576 1 1048576 5548543 1048576 1 1048576 (BSN.sqrt_enclosure 28 1 2774271 2774272 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep439 := BSN.log_dyadic_bound 12 44 5 4 13275571325829120 524288 198314 344661139390464 45148078080 293399 56 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 12) (BSN.artanhQ 44) 0 4 344661139390464 13275571325829120 45148078080 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep440 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz642 140505 1000 0 1 3751726938922231 1125899906842624 125000000099157 24789250000000000000 105427278710653613331 225179981368524800 3512625002786410857 4957850000000000000000 qz18 (BSN.isNear_log_sfrac 28 1 3751726938922231 1125899906842624 125000000099157 24789250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz643) Bool.false 62943533227317076688896 18889465931478580854784 1000000000793256 198314000000000000000 3751726938922231 1125899906842624 125000000099157 24789250000000000000 (BSN.log_rat_reduce_isNear 28 1 4 56 32 293399 524288 24973259072661432 36028797018963968 198314 1000000000000000 rfl rfl rfl rfl (ep439 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep441 := nat_lit 1650838510858624183819445317028721

noncomputable def ep442 := BSN.cos_dyadic_bound_f 201570117 2147483648 2 1 1048576 397016 ep441 ep66 ep441 ep441 ep67 ep441 1043960 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 201570117) qz15 0 1 ep441 ep66 ep441 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 201570117) qz16 0 1 ep441 ep67 ep441 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz374 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 490934023) qz26)

noncomputable def ep443 := @Enclosure.Real.IsNear.cos_image qz69 qz374 Bool.false 490934023 1048576 93 131072 Bool.true 1043960 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz69 Bool.false 105427278710653613331 225179981368524800 3512625002786410857 4957850000000000000000 490934023 1048576 93 131072 (ep440 rfl) rfl) (Enclosure.sfrac_false_div 490934023 1048576) (BSN.cos_reduce2 qz374 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 14184236004749099401216) qz27) 226375608064910080 72057594037927936 Bool.false 1043960 1048576 74 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q2 490934023 1048576 226375608064910080 72057594037927936 74 14184236004749099401216 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1043960 1048576 14184236004749099401216 151115727451828646838272 201570117 2147483648 397016 396628 (ep442 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep444 := BSN.sin_dyadic_bound_f 201570117 2147483648 1 0 1048576 397016 0 1 1 0 1 1 98278 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 201570117) qz20 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 201570117) qz21 0 0 rfl) rfl rfl

noncomputable def ep445 := @Enclosure.Real.IsNear.sin_image qz69 qz374 Bool.false 490934023 1048576 93 131072 Bool.true 98278 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz69 Bool.false 105427278710653613331 225179981368524800 3512625002786410857 4957850000000000000000 490934023 1048576 93 131072 (ep440 rfl) rfl) (Enclosure.sfrac_false_div 490934023 1048576) (BSN.sin_reduce2 qz374 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 14184236004749099401216) qz27) 226375608064910080 72057594037927936 Bool.false 98278 1048576 74 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q2 490934023 1048576 226375608064910080 72057594037927936 74 14184236004749099401216 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 98278 1048576 14184236004749099401216 151115727451828646838272 201570117 2147483648 397016 396628 (ep444 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz375 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 28))) Bool.false 198163 1048576 1 1048576 198163 1048576 1 1048576 (ep438 rfl rfl) rfl)

noncomputable def ep446 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz371 (Real.cos qz69)) (@HMul.hMul Real Real Real qz0 qz371 (@Neg.neg Real Real.instNeg (Real.sin qz69))) Bool.true 25859280685 137438953472 1853315709183 13628034309423104 Bool.false 9737531657 549755813888 7366377341695 54512137237692416 (@Enclosure.Real.IsNear.mulLit_ft qz371 (Real.cos qz69) 198163 1048576 1 1048576 130495 131072 9287137 12996706304 25859280685 137438953472 1853315709183 13628034309423104 qz375 (@Enclosure.Real.IsNear.recentre' (Real.cos qz69) Bool.true 1043960 1048576 18574274 25993412608 130495 131072 9287137 12996706304 (ep443 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz371 (@Neg.neg Real Real.instNeg (Real.sin qz69)) 198163 1048576 1 1048576 49139 524288 9287137 12996706304 9737531657 549755813888 7366377341695 54512137237692416 qz375 (@Enclosure.Real.IsNear.neg (Real.sin qz69) Bool.true 49139 524288 9287137 12996706304 (@Enclosure.Real.IsNear.recentre' (Real.sin qz69) Bool.true 98278 1048576 18574274 25993412608 49139 524288 9287137 12996706304 (ep445 rfl rfl) rfl)) rfl)

noncomputable def ep447 := @ep386 25859280685 137438953472 1853315709183 13628034309423104 Bool.false 9737531657 549755813888 7366377341695 54512137237692416 Bool.false 103647331711625937813504 754133592357 1099511627776 642405455898509 109024274475384832 Bool.false 9834889347006031986688 71558238029 549755813888 320564163859823 54512137237692416 (ep387 (BSN.head_sum_c_succ qz5 27 28 rfl rfl) (ep436 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep437 ep446) rfl rfl

noncomputable abbrev qz644 := (Real.log (Enclosure.sfrac Bool.false 29 1))

noncomputable abbrev qz70 := (@HMul.hMul Real Real Real qz267 qz277 qz644)

noncomputable abbrev qz376 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 29)))

noncomputable def ep448 := @Enclosure.Complex.IsNear.of_eq qz631 (Complex.mk (@HMul.hMul Real Real Real qz0 qz376 (Real.cos qz70)) (@HMul.hMul Real Real Real qz0 qz376 (@Neg.neg Real Real.instNeg (Real.sin qz70)))) Bool.true 62671943475 1099511627776 14498748512541 109024274475384832 Bool.true 194316807825 1099511627776 14565787568671 109024274475384832 (BSN.cpow_neg_s_mk qz12 140505 1000 29 qz13 rfl)

noncomputable abbrev qz377 := (Real.sqrt (@Nat.cast Real Real.instNatCast 29))

noncomputable abbrev qz378 := (@Nat.cast Real Real.instNatCast 29)

noncomputable abbrev qz645 := (@HDiv.hDiv Real Real Real qz1 qz378 qz14)

noncomputable def ep449 := @Enclosure.Real.IsNear.inv_image qz377 5646755 1048576 1 1048576 97357 97358 524288 (@Enclosure.Real.IsNear.of_eq qz377 (Real.sqrt qz645) Bool.false 5646755 1048576 1 1048576 (BSN.sqrt_natCast_div_one 29) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz645) Bool.false 5646755 1048576 1 1048576 5646755 1048576 1 1048576 (BSN.sqrt_enclosure 29 1 2823377 2823378 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep450 := BSN.log_dyadic_bound 13 45 6 5 353956287581982421875 524288 198314 10371179520995104305 130276274797305 311797 58 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 13) (BSN.artanhQ 45) 0 5 10371179520995104305 353956287581982421875 130276274797305 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep451 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz644 140505 1000 0 1 3791236343078135 1125899906842624 125000000099157 24789250000000000000 21307506495367734327 45035996273704960 3512625002786410857 4957850000000000000000 qz18 (BSN.isNear_log_sfrac 29 1 3791236343078135 1125899906842624 125000000099157 24789250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz645) Bool.false 63606391034871975772160 18889465931478580854784 1000000000793256 198314000000000000000 3791236343078135 1125899906842624 125000000099157 24789250000000000000 (BSN.log_rat_reduce_isNear 29 1 4 58 32 311797 524288 24973259072661432 36028797018963968 198314 1000000000000000 rfl rfl rfl rfl (ep450 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep452 := nat_lit 201507473346471785138128826282439696

noncomputable def ep453 := BSN.sin_dyadic_bound_f 669996894 2147483648 2 1 1048576 397016 ep452 ep70 ep452 ep452 ep71 ep452 321865 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 669996894) qz20 0 1 ep452 ep70 ep452 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 669996894) qz21 0 1 ep452 ep71 ep452 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz379 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 496104045) qz26)

noncomputable def ep454 := @Enclosure.Real.IsNear.cos_image qz70 qz379 Bool.false 496104045 1048576 93 131072 Bool.true 321865 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz70 Bool.false 21307506495367734327 45035996273704960 3512625002786410857 4957850000000000000000 496104045 1048576 93 131072 (ep451 rfl) rfl) (Enclosure.sfrac_false_div 496104045 1048576) (BSN.cos_reduce1 qz379 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 47146840084248170332160) qz27) 226375608064910080 72057594037927936 Bool.false 321865 1048576 75 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q1 496104045 1048576 226375608064910080 72057594037927936 75 47146840084248170332160 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 321865 1048576 47146840084248170332160 151115727451828646838272 669996894 2147483648 397016 396628 (ep453 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep455 := BSN.cos_dyadic_bound_f 669996894 2147483648 2 1 1048576 397016 ep452 ep66 ep452 ep452 ep67 ep452 997955 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 669996894) qz15 0 1 ep452 ep66 ep452 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 669996894) qz16 0 1 ep452 ep67 ep452 rfl rfl rfl rfl) rfl rfl

noncomputable def ep456 := @Enclosure.Real.IsNear.sin_image qz70 qz379 Bool.false 496104045 1048576 93 131072 Bool.false 997955 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz70 Bool.false 21307506495367734327 45035996273704960 3512625002786410857 4957850000000000000000 496104045 1048576 93 131072 (ep451 rfl) rfl) (Enclosure.sfrac_false_div 496104045 1048576) (BSN.sin_reduce1 qz379 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 47146840084248170332160) qz27) 226375608064910080 72057594037927936 Bool.false 997955 1048576 75 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q1 496104045 1048576 226375608064910080 72057594037927936 75 47146840084248170332160 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 997955 1048576 47146840084248170332160 151115727451828646838272 669996894 2147483648 397016 396628 (ep455 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz380 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 29))) Bool.false 194715 1048576 1 1048576 194715 1048576 1 1048576 (ep449 rfl rfl) rfl)

noncomputable def ep457 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz376 (Real.cos qz70)) (@HMul.hMul Real Real Real qz0 qz376 (@Neg.neg Real Real.instNeg (Real.sin qz70))) Bool.true 62671943475 1099511627776 14498748512541 109024274475384832 Bool.true 194316807825 1099511627776 14565787568671 109024274475384832 (@Enclosure.Real.IsNear.mulLit_ft qz376 (Real.cos qz70) 194715 1048576 1 1048576 321865 1048576 9287137 12996706304 62671943475 1099511627776 14498748512541 109024274475384832 qz380 (@Enclosure.Real.IsNear.recentre' (Real.cos qz70) Bool.true 321865 1048576 18574274 25993412608 321865 1048576 9287137 12996706304 (ep454 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz376 (@Neg.neg Real Real.instNeg (Real.sin qz70)) 194715 1048576 1 1048576 997955 1048576 9287137 12996706304 194316807825 1099511627776 14565787568671 109024274475384832 qz380 (@Enclosure.Real.IsNear.neg (Real.sin qz70) Bool.false 997955 1048576 9287137 12996706304 (@Enclosure.Real.IsNear.recentre' (Real.sin qz70) Bool.false 997955 1048576 18574274 25993412608 997955 1048576 9287137 12996706304 (ep456 rfl rfl) rfl)) rfl)

noncomputable def ep458 := @ep384 62671943475 1099511627776 14498748512541 109024274475384832 Bool.true 194316807825 1099511627776 14565787568671 109024274475384832 Bool.false 760270123106924790546432 345730824441 549755813888 328452102205525 54512137237692416 Bool.true 28147680061902706180096 51200331767 1099511627776 655694115288317 109024274475384832 (ep385 (BSN.head_sum_c_succ qz5 28 29 rfl rfl) (ep447 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep448 ep457) rfl rfl

noncomputable abbrev qz646 := (Real.log (Enclosure.sfrac Bool.false 30 1))

noncomputable abbrev qz71 := (@HMul.hMul Real Real Real qz267 qz277 qz646)

noncomputable abbrev qz381 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 30)))

noncomputable def ep459 := @Enclosure.Complex.IsNear.of_eq qz630 (Complex.mk (@HMul.hMul Real Real Real qz0 qz381 (Real.cos qz71)) (@HMul.hMul Real Real Real qz0 qz381 (@Neg.neg Real Real.instNeg (Real.sin qz71)))) Bool.false 93834446349 549755813888 31268418047 238044267413504 Bool.true 35629648173 549755813888 31136772191 238044267413504 (BSN.cpow_neg_s_mk qz12 140505 1000 30 qz13 rfl)

noncomputable abbrev qz382 := (Real.sqrt (@Nat.cast Real Real.instNatCast 30))

noncomputable abbrev qz383 := (@Nat.cast Real Real.instNatCast 30)

noncomputable abbrev qz647 := (@HDiv.hDiv Real Real Real qz1 qz383 qz14)

noncomputable def ep460 := @Enclosure.Real.IsNear.inv_image qz382 5743287 1048576 1 1048576 95721 95722 524288 (@Enclosure.Real.IsNear.of_eq qz382 (Real.sqrt qz647) Bool.false 5743287 1048576 1 1048576 (BSN.sqrt_natCast_div_one 30) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz647) Bool.false 5743287 1048576 1 1048576 5743287 1048576 1 1048576 (BSN.sqrt_enclosure 30 1 2871643 2871644 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep461 := BSN.log_dyadic_bound 14 46 6 5 440963670083462507520 524288 198314 14425761949190022144 273345648952320 329571 60 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 14) (BSN.artanhQ 46) 0 5 14425761949190022144 440963670083462507520 273345648952320 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep462 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz646 140505 1000 0 1 3829405717437687 1125899906842624 125000000099157 24789250000000000000 107610130065716442387 225179981368524800 3512625002786410857 4957850000000000000000 qz18 (BSN.isNear_log_sfrac 30 1 3829405717437687 1125899906842624 125000000099157 24789250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz647) Bool.false 64246766873087041339392 18889465931478580854784 1000000000793256 198314000000000000000 3829405717437687 1125899906842624 125000000099157 24789250000000000000 (BSN.log_rat_reduce_isNear 30 1 4 60 32 329571 524288 24973259072661432 36028797018963968 198314 1000000000000000 rfl rfl rfl rfl (ep461 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep463 := nat_lit 368832734435045152779200510176792576

noncomputable def ep464 := BSN.cos_dyadic_bound_f 779304824 2147483648 2 1 1048576 397016 ep463 ep66 ep463 ep463 ep67 ep463 980286 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 779304824) qz15 0 1 ep463 ep66 ep463 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 779304824) qz16 0 1 ep463 ep67 ep463 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz384 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 125274679) qz24)

noncomputable def ep465 := @Enclosure.Real.IsNear.cos_image qz71 qz384 Bool.false 125274679 262144 93 131072 Bool.false 980286 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz71 Bool.false 107610130065716442387 225179981368524800 3512625002786410857 4957850000000000000000 125274679 262144 93 131072 (ep462 rfl) rfl) (Enclosure.sfrac_false_div 125274679 262144) (BSN.cos_reduce0 qz384 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 13709675454864459563008) qz291) 226375608064910080 72057594037927936 Bool.false 980286 1048576 76 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q0 125274679 262144 226375608064910080 72057594037927936 76 13709675454864459563008 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 980286 1048576 13709675454864459563008 37778931862957161709568 779304824 2147483648 397016 396628 (ep464 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep466 := BSN.sin_dyadic_bound_f 779304824 2147483648 2 1 1048576 397016 ep463 ep70 ep463 ep463 ep71 ep463 372222 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 779304824) qz20 0 1 ep463 ep70 ep463 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 779304824) qz21 0 1 ep463 ep71 ep463 rfl rfl rfl rfl) rfl rfl

noncomputable def ep467 := @Enclosure.Real.IsNear.sin_image qz71 qz384 Bool.false 125274679 262144 93 131072 Bool.false 372222 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz71 Bool.false 107610130065716442387 225179981368524800 3512625002786410857 4957850000000000000000 125274679 262144 93 131072 (ep462 rfl) rfl) (Enclosure.sfrac_false_div 125274679 262144) (BSN.sin_reduce0 qz384 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 13709675454864459563008) qz291) 226375608064910080 72057594037927936 Bool.false 372222 1048576 76 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q0 125274679 262144 226375608064910080 72057594037927936 76 13709675454864459563008 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 372222 1048576 13709675454864459563008 37778931862957161709568 779304824 2147483648 397016 396628 (ep466 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz385 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 30))) Bool.false 191443 1048576 1 1048576 191443 1048576 1 1048576 (ep460 rfl rfl) rfl)

noncomputable def ep468 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz381 (Real.cos qz71)) (@HMul.hMul Real Real Real qz0 qz381 (@Neg.neg Real Real.instNeg (Real.sin qz71))) Bool.false 93834446349 549755813888 31268418047 238044267413504 Bool.true 35629648173 549755813888 31136772191 238044267413504 (@Enclosure.Real.IsNear.mulLit_ff qz381 (Real.cos qz71) 191443 1048576 1 1048576 490143 524288 9287137 12996706304 93834446349 549755813888 31268418047 238044267413504 qz385 (@Enclosure.Real.IsNear.recentre' (Real.cos qz71) Bool.false 980286 1048576 18574274 25993412608 490143 524288 9287137 12996706304 (ep465 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz381 (@Neg.neg Real Real.instNeg (Real.sin qz71)) 191443 1048576 1 1048576 186111 524288 9287137 12996706304 35629648173 549755813888 31136772191 238044267413504 qz385 (@Enclosure.Real.IsNear.neg (Real.sin qz71) Bool.false 186111 524288 9287137 12996706304 (@Enclosure.Real.IsNear.recentre' (Real.sin qz71) Bool.false 372222 1048576 18574274 25993412608 186111 524288 9287137 12996706304 (ep467 rfl rfl) rfl)) rfl)

noncomputable def ep469 := @ep382 93834446349 549755813888 31268418047 238044267413504 Bool.true 35629648173 549755813888 31136772191 238044267413504 Bool.false 241653563200055562731520 219782635395 274877906944 20975785621143 3407008577355776 Bool.true 67322892521684120633344 122459628113 1099511627776 669954756951795 109024274475384832 (ep383 (BSN.head_sum_c_succ qz5 29 30 rfl rfl) (ep458 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep459 ep468) rfl rfl

noncomputable abbrev qz648 := (Real.log (Enclosure.sfrac Bool.false 31 1))

noncomputable abbrev qz72 := (@HMul.hMul Real Real Real qz267 qz277 qz648)

noncomputable abbrev qz386 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 31)))

noncomputable def ep470 := @Enclosure.Complex.IsNear.of_eq qz629 (Complex.mk (@HMul.hMul Real Real Real qz0 qz386 (Real.cos qz72)) (@HMul.hMul Real Real Real qz0 qz386 (@Neg.neg Real Real.instNeg (Real.sin qz72)))) Bool.false 1573488795 34359738368 876180169075 6814017154711552 Bool.false 95475081511 549755813888 7046454578403 54512137237692416 (BSN.cpow_neg_s_mk qz12 140505 1000 31 qz13 rfl)

noncomputable abbrev qz387 := (Real.sqrt (@Nat.cast Real Real.instNatCast 31))

noncomputable abbrev qz388 := (@Nat.cast Real Real.instNatCast 31)

noncomputable abbrev qz649 := (@HDiv.hDiv Real Real Real qz1 qz388 qz14)

noncomputable def ep471 := @Enclosure.Real.IsNear.inv_image qz387 5838225 1048576 1 1048576 94164 94165 524288 (@Enclosure.Real.IsNear.of_eq qz387 (Real.sqrt qz649) Bool.false 5838225 1048576 1 1048576 (BSN.sqrt_natCast_div_one 31) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz649) Bool.false 5838225 1048576 1 1048576 5838225 1048576 1 1048576 (BSN.sqrt_enclosure 31 1 2919112 2919113 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep472 := BSN.log_dyadic_bound 15 47 6 5 546767979591453359355 524288 198314 19788004106328479625 544934619140625 346763 62 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 15) (BSN.artanhQ 47) 0 5 19788004106328479625 546767979591453359355 544934619140625 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep473 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz648 140505 1000 0 1 3866325256314103 1125899906842624 125000000099157 24789250000000000000 108647606027682608403 225179981368524800 3512625002786410857 4957850000000000000000 qz18 (BSN.isNear_log_sfrac 31 1 3866325256314103 1125899906842624 125000000099157 24789250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz649) Bool.false 64866173951437069877248 18889465931478580854784 1000000000793256 198314000000000000000 3866325256314103 1125899906842624 125000000099157 24789250000000000000 (BSN.log_rat_reduce_isNear 31 1 4 62 32 346763 524288 24973259072661432 36028797018963968 198314 1000000000000000 rfl rfl rfl rfl (ep472 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep474 := nat_lit 93972169583442588731362999385302081

noncomputable def ep475 := BSN.sin_dyadic_bound_f 553668497 2147483648 2 1 1048576 397016 ep474 ep70 ep474 ep474 ep71 ep474 267360 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 553668497) qz20 0 1 ep474 ep70 ep474 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 553668497) qz21 0 1 ep474 ep71 ep474 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz389 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 31620615) (@Nat.cast Real Real.instNatCast 65536))

noncomputable abbrev qz650 := (@Nat.cast Real Real.instNatCast 9444732965739290427392)

noncomputable def ep476 := @Enclosure.Real.IsNear.cos_image qz72 qz389 Bool.false 31620615 65536 93 131072 Bool.false 267360 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz72 Bool.false 108647606027682608403 225179981368524800 3512625002786410857 4957850000000000000000 31620615 65536 93 131072 (ep473 rfl) rfl) (Enclosure.sfrac_false_div 31620615 65536) (BSN.cos_reduce3 qz389 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 2435059805651594117120) qz650) 226375608064910080 72057594037927936 Bool.false 267360 1048576 76 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q3 31620615 65536 226375608064910080 72057594037927936 76 2435059805651594117120 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 267360 1048576 2435059805651594117120 9444732965739290427392 553668497 2147483648 397016 396628 (ep475 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep477 := BSN.cos_dyadic_bound_f 553668497 2147483648 2 1 1048576 397016 ep474 ep66 ep474 ep474 ep67 ep474 1013918 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 553668497) qz15 0 1 ep474 ep66 ep474 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 553668497) qz16 0 1 ep474 ep67 ep474 rfl rfl rfl rfl) rfl rfl

noncomputable def ep478 := @Enclosure.Real.IsNear.sin_image qz72 qz389 Bool.false 31620615 65536 93 131072 Bool.true 1013918 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz72 Bool.false 108647606027682608403 225179981368524800 3512625002786410857 4957850000000000000000 31620615 65536 93 131072 (ep473 rfl) rfl) (Enclosure.sfrac_false_div 31620615 65536) (BSN.sin_reduce3 qz389 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 2435059805651594117120) qz650) 226375608064910080 72057594037927936 Bool.false 1013918 1048576 76 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q3 31620615 65536 226375608064910080 72057594037927936 76 2435059805651594117120 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1013918 1048576 2435059805651594117120 9444732965739290427392 553668497 2147483648 397016 396628 (ep477 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz390 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 31))) Bool.false 188329 1048576 1 1048576 188329 1048576 1 1048576 (ep471 rfl rfl) rfl)

noncomputable def ep479 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz386 (Real.cos qz72)) (@HMul.hMul Real Real Real qz0 qz386 (@Neg.neg Real Real.instNeg (Real.sin qz72))) Bool.false 1573488795 34359738368 876180169075 6814017154711552 Bool.false 95475081511 549755813888 7046454578403 54512137237692416 (@Enclosure.Real.IsNear.mulLit_ff qz386 (Real.cos qz72) 188329 1048576 1 1048576 8355 32768 9287137 12996706304 1573488795 34359738368 876180169075 6814017154711552 qz390 (@Enclosure.Real.IsNear.recentre' (Real.cos qz72) Bool.false 267360 1048576 18574274 25993412608 8355 32768 9287137 12996706304 (ep476 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz386 (@Neg.neg Real Real.instNeg (Real.sin qz72)) 188329 1048576 1 1048576 506959 524288 9287137 12996706304 95475081511 549755813888 7046454578403 54512137237692416 qz390 (@Enclosure.Real.IsNear.neg (Real.sin qz72) Bool.true 506959 524288 9287137 12996706304 (@Enclosure.Real.IsNear.recentre' (Real.sin qz72) Bool.true 1013918 1048576 18574274 25993412608 506959 524288 9287137 12996706304 (ep478 rfl rfl) rfl)) rfl)

noncomputable def ep480 := @ep380 1573488795 34359738368 876180169075 6814017154711552 Bool.false 95475081511 549755813888 7046454578403 54512137237692416 Bool.false 7984191156571173027840 232370545755 274877906944 42827751411361 6814017154711552 Bool.false 37653069762521771016192 68490534909 1099511627776 684047666108601 109024274475384832 (ep381 (BSN.head_sum_c_succ qz5 30 31 rfl rfl) (ep469 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep470 ep479) rfl rfl

noncomputable abbrev qz651 := (Real.log (Enclosure.sfrac Bool.false 32 1))

noncomputable abbrev qz73 := (@HMul.hMul Real Real Real qz267 qz277 qz651)

noncomputable abbrev qz391 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 32)))

noncomputable def ep481 := @Enclosure.Complex.IsNear.of_eq qz628 (Complex.mk (@HMul.hMul Real Real Real qz0 qz391 (Real.cos qz73)) (@HMul.hMul Real Real Real qz0 qz391 (@Neg.neg Real Real.instNeg (Real.sin qz73)))) Bool.true 97181557551 549755813888 6937989185961 54512137237692416 Bool.false 1236185847 1099511627776 13772668180977 109024274475384832 (BSN.cpow_neg_s_mk qz12 140505 1000 32 qz13 rfl)

noncomputable abbrev qz392 := (Real.sqrt (@Nat.cast Real Real.instNatCast 32))

noncomputable abbrev qz393 := (@Nat.cast Real Real.instNatCast 32)

noncomputable abbrev qz652 := (@HDiv.hDiv Real Real Real qz1 qz393 qz14)

noncomputable def ep482 := @Enclosure.Real.IsNear.inv_image qz392 5931641 1048576 1 1048576 92681 92682 524288 (@Enclosure.Real.IsNear.of_eq qz392 (Real.sqrt qz652) Bool.false 5931641 1048576 1 1048576 (BSN.sqrt_natCast_div_one 32) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz652) Bool.false 5931641 1048576 1 1048576 5931641 1048576 1 1048576 (BSN.sqrt_enclosure 32 1 2965820 2965821 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep483 := BSN.log_dyadic_bound 0 64 1 0 1 524288 198314 0 1 0 64 64 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 0) (BSN.artanhQ 64) 0 0 rfl) rfl rfl rfl

noncomputable def ep484 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz651 140505 1000 0 1 15608286920413395 4503599627370496 100000000099157 19831400000000000000 87721694150107362579 180143985094819840 2810100002786410857 3966280000000000000000 qz18 (BSN.isNear_log_sfrac 32 1 15608286920413395 4503599627370496 100000000099157 19831400000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz652) Bool.false 65465900263437584302080 18889465931478580854784 1000000000991570 198314000000000000000 15608286920413395 4503599627370496 100000000099157 19831400000000000000 (BSN.log_rat_reduce_isNear 32 1 5 64 64 0 524288 24973259072661432 36028797018963968 198314 1000000000000000 rfl rfl rfl rfl (ep483 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep485 := BSN.cos_dyadic_bound_f 13660075 2147483648 1 0 1048576 397016 0 1 1 0 1 1 1048554 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 13660075) qz15 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 13660075) qz16 0 0 rfl) rfl rfl

noncomputable abbrev qz394 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 255303731) qz17)

noncomputable def ep486 := @Enclosure.Real.IsNear.cos_image qz73 qz394 Bool.false 255303731 524288 93 131072 Bool.true 1048554 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz73 Bool.false 87721694150107362579 180143985094819840 2810100002786410857 3966280000000000000000 255303731 524288 93 131072 (ep484 rfl) rfl) (Enclosure.sfrac_false_div 255303731 524288) (BSN.cos_reduce2 qz394 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 480621180686572716032) qz19) 226375608064910080 72057594037927936 Bool.false 1048554 1048576 77 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q2 255303731 524288 226375608064910080 72057594037927936 77 480621180686572716032 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1048554 1048576 480621180686572716032 75557863725914323419136 13660075 2147483648 397016 396628 (ep485 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep487 := BSN.sin_dyadic_bound_f 13660075 2147483648 1 0 1048576 397016 0 1 1 0 1 1 6669 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 13660075) qz20 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 13660075) qz21 0 0 rfl) rfl rfl

noncomputable def ep488 := @Enclosure.Real.IsNear.sin_image qz73 qz394 Bool.false 255303731 524288 93 131072 Bool.true 6669 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz73 Bool.false 87721694150107362579 180143985094819840 2810100002786410857 3966280000000000000000 255303731 524288 93 131072 (ep484 rfl) rfl) (Enclosure.sfrac_false_div 255303731 524288) (BSN.sin_reduce2 qz394 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 480621180686572716032) qz19) 226375608064910080 72057594037927936 Bool.false 6669 1048576 77 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q2 255303731 524288 226375608064910080 72057594037927936 77 480621180686572716032 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 6669 1048576 480621180686572716032 75557863725914323419136 13660075 2147483648 397016 396628 (ep487 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz395 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 32))) Bool.false 185363 1048576 1 1048576 185363 1048576 1 1048576 (ep482 rfl rfl) rfl)

noncomputable def ep489 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz391 (Real.cos qz73)) (@HMul.hMul Real Real Real qz0 qz391 (@Neg.neg Real Real.instNeg (Real.sin qz73))) Bool.true 97181557551 549755813888 6937989185961 54512137237692416 Bool.false 1236185847 1099511627776 13772668180977 109024274475384832 (@Enclosure.Real.IsNear.mulLit_ft qz391 (Real.cos qz73) 185363 1048576 1 1048576 524277 524288 9287137 12996706304 97181557551 549755813888 6937989185961 54512137237692416 qz395 (@Enclosure.Real.IsNear.recentre' (Real.cos qz73) Bool.true 1048554 1048576 18574274 25993412608 524277 524288 9287137 12996706304 (ep486 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz391 (@Neg.neg Real Real.instNeg (Real.sin qz73)) 185363 1048576 1 1048576 6669 1048576 9287137 12996706304 1236185847 1099511627776 13772668180977 109024274475384832 qz395 (@Enclosure.Real.IsNear.neg (Real.sin qz73) Bool.true 6669 1048576 9287137 12996706304 (@Enclosure.Real.IsNear.recentre' (Real.sin qz73) Bool.true 6669 1048576 18574274 25993412608 6669 1048576 9287137 12996706304 (ep488 rfl rfl) rfl)) rfl)

noncomputable def ep490 := @ep378 97181557551 549755813888 6937989185961 54512137237692416 Bool.false 1236185847 1099511627776 13772668180977 109024274475384832 Bool.false 101033995371962009911296 367559533959 549755813888 349560000476849 54512137237692416 Bool.false 76665340237912165318656 17431680189 274877906944 348910167144789 54512137237692416 (ep379 (BSN.head_sum_c_succ qz5 31 32 rfl rfl) (ep480 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep481 ep489) rfl rfl

theorem EMRow49.d9 : Enclosure.Complex.IsNear qz65 Bool.false 367559533959 549755813888 349560000476849 54512137237692416 Bool.false 17431680189 274877906944 348910167144789 54512137237692416 := ep377 (BSN.head_sum_c_succ qz5 32 33 rfl rfl) (ep490 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

theorem EMRow49.d10 : @Eq Nat (BSN.factNat (Nat.mul 2 1)) 2 := @Eq.refl Nat 2

theorem EMRow49.d11 : @Eq Nat (Nat.pow 36 1) 36 := @Eq.refl Nat 36

noncomputable def ep491 := nat_lit 321181538900509585412618878613

noncomputable def ep492 := nat_lit 437008643428386680926088724480

noncomputable def ep493 := nat_lit 2759588485375032043689501388859322199063

noncomputable def ep494 := nat_lit 386704560308155609898084591689077148876800

noncomputable abbrev qz732 := (@instHMul Complex Complex.instMul)

noncomputable abbrev qz653 := qz732

noncomputable abbrev qz396 := qz653

noncomputable abbrev qz74 := qz396

noncomputable abbrev qz654 := (@instHSub Complex Complex.instSub)

noncomputable abbrev qz397 := qz654

noncomputable abbrev qz75 := qz397

noncomputable abbrev qz733 := (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (4 : Complex))

noncomputable abbrev qz734 := (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid))

noncomputable abbrev qz655 := (@HAdd.hAdd Complex Complex Complex qz730 (@HAdd.hAdd Complex Complex Complex qz730 qz733 (@HMul.hMul Complex Complex Complex qz732 Complex.I (@HDiv.hDiv Complex Complex Complex qz734 (↑qz731) (2 : Complex)))) (@Nat.cast Complex Complex.instNatCast 2))

noncomputable abbrev qz398 := qz655

noncomputable abbrev qz76 := (Complex.Stirling.logGammaStirling 1 qz398)

noncomputable abbrev qz656 := (@HAdd.hAdd Complex Complex Complex qz730 qz733 (@HMul.hMul Complex Complex Complex qz732 Complex.I (@HDiv.hDiv Complex Complex Complex qz734 (↑qz731) (2 : Complex))))

noncomputable abbrev qz399 := qz656

noncomputable abbrev qz77 := qz399

noncomputable abbrev qz78 := (@HMul.hMul Real Real Real qz267 (@HDiv.hDiv Real Real Real qz270 qz277 (2 : Real)) (Real.log Real.pi))

noncomputable abbrev qz400 := (@instHSub Real Real.instSub)

noncomputable def ep495 := Complex.re (@HMul.hMul Complex Complex Complex qz74 (Complex.exp (@HMul.hMul Complex Complex Complex qz74 Complex.I ↑(@HSub.hSub Real Real Real qz400 (Complex.im (@HSub.hSub Complex Complex Complex qz75 qz76 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz77 (@Nat.cast Complex Complex.instNatCast j))))) qz78))) (zetaApproximant qz5 1 36))

noncomputable def ep496 := @Enclosure.Real.IsNear.of_eq ep495 (@HSub.hSub Real Real Real qz400 (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz400 (Complex.im (@HSub.hSub Complex Complex Complex qz75 qz76 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz77 (@Nat.cast Complex Complex.instNatCast j))))) qz78)) (Complex.re (zetaApproximant qz5 1 36))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz400 (Complex.im (@HSub.hSub Complex Complex Complex qz75 qz76 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz77 (@Nat.cast Complex Complex.instNatCast j))))) qz78)) (Complex.im (zetaApproximant qz5 1 36))))

noncomputable def ep497 := nat_lit 192707774165386888721197105925

noncomputable def ep498 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz400 (Complex.im (@HSub.hSub Complex Complex Complex qz75 qz76 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz77 (@Nat.cast Complex Complex.instNatCast j))))) qz78)) (Complex.re (zetaApproximant qz5 1 36))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz400 (Complex.im (@HSub.hSub Complex Complex Complex qz75 qz76 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz77 (@Nat.cast Complex Complex.instNatCast j))))) qz78)) (Complex.im (zetaApproximant qz5 1 36))) ep497

noncomputable def ep499 := nat_lit 262205186057032008555653234688

noncomputable def ep500 := nat_lit 459302307820647117873503797281109097771

noncomputable def ep501 := nat_lit 64450760051359268316347431948179524812800

noncomputable def ep502 := nat_lit 2872937297156315935553107

noncomputable def ep503 := nat_lit 655512965142580021389133086720

noncomputable def ep504 := nat_lit 3774638451149336448478605172667612437

noncomputable def ep505 := nat_lit 126323197748237969418585532057950156525118715967973009391616

noncomputable def ep506 := @Enclosure.Real.IsNear.mulLit_tf (Real.cos (@HSub.hSub Real Real Real qz400 (Complex.im (@HSub.hSub Complex Complex Complex qz75 qz76 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz77 (@Nat.cast Complex Complex.instNatCast j))))) qz78)) (Complex.re (zetaApproximant qz5 1 36)) 1048575 1048576 38699733

noncomputable def ep507 := nat_lit 1415447190636264297282030679

noncomputable def ep508 := nat_lit 206625299722807589152279756800

noncomputable def ep509 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HSub.hSub Real Real Real qz400 (Complex.im (@HSub.hSub Complex Complex Complex qz75 qz76 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz77 (@Nat.cast Complex Complex.instNatCast j))))) qz78)) Bool.true 1048575 1048576 77399466

noncomputable abbrev qz401 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 154827681) qz26)

noncomputable def ep510 := @Enclosure.Real.IsNear.cos_image (@HSub.hSub Real Real Real qz400 (Complex.im (@HSub.hSub Complex Complex Complex qz75 qz76 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz77 (@Nat.cast Complex Complex.instNatCast j))))) qz78) qz401 Bool.false 154827681 1048576 385

noncomputable def ep511 := nat_lit 7611085203641286386515271

noncomputable def ep512 := nat_lit 20794730086400000000000000000

noncomputable def ep513 := @Enclosure.Real.IsNear.recentre' (@HSub.hSub Real Real Real qz400 (Complex.im (@HSub.hSub Complex Complex Complex qz75 qz76 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz77 (@Nat.cast Complex Complex.instNatCast j))))) qz78) Bool.false 132995966106258804873 900719925474099200 ep511 ep512

noncomputable def ep514 := nat_lit 2038263489641286386515271

noncomputable def ep515 := @Enclosure.Real.IsNear.subLit_ff_p (Complex.im (@HSub.hSub Complex Complex Complex qz75 qz76 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz77 (@Nat.cast Complex Complex.instNatCast j))))) qz78 205431968100361867401 900719925474099200 ep514 ep512 2108165121 26214400

noncomputable def ep516 := nat_lit 3486409453895910814462771200

noncomputable def ep517 := nat_lit 5198682521600000000000000000

noncomputable def ep518 := @Enclosure.Complex.IsNear.im_isNear (@HSub.hSub Complex Complex Complex qz75 qz76 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz77 (@Nat.cast Complex Complex.instNatCast j)))) Bool.true 6220399652835733107 56294995342131200 955305495251942639207227 ep517 Bool.false 205431968100361867401 900719925474099200

noncomputable def ep519 := nat_lit 1933405889620491656428871

noncomputable def ep520 := @Enclosure.Complex.IsNear.subLitP qz76 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz77 (@Nat.cast Complex Complex.instNatCast j))) Bool.true 5741646977925232057 56294995342131200 942198295189558448948027 ep517 Bool.false 208242433773595592201 900719925474099200 ep519

noncomputable def ep521 := nat_lit 7003547389651642575683444715552768

noncomputable def ep522 := nat_lit 57823958436673582940342420615725056

noncomputable abbrev qz735 := (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (2 : Complex))

noncomputable abbrev qz657 := qz735

noncomputable abbrev qz402 := (@HSub.hSub Complex Complex Complex qz654 qz655 qz657)

noncomputable abbrev qz403 := (Complex.log qz655)

noncomputable abbrev qz79 := (@HSub.hSub Complex Complex Complex qz397 (@HMul.hMul Complex Complex Complex qz396 qz402 qz403) qz398)

noncomputable abbrev qz404 := qz657

noncomputable abbrev qz80 := (@HMul.hMul Complex Complex Complex qz396 qz404 ↑(Real.log (@HMul.hMul Real Real Real qz267 (2 : Real) Real.pi)))

noncomputable abbrev qz658 := qz734

noncomputable abbrev qz405 := qz658

noncomputable abbrev qz81 := qz405

noncomputable abbrev qz82 := (@instHMul Nat instMulNat)

noncomputable abbrev qz659 := (@instHPow Complex Int (@ZPow.toPow Complex (@DivInvMonoid.toZPow Complex Complex.instDivInvMonoid)))

noncomputable abbrev qz406 := qz659

noncomputable abbrev qz83 := qz406

noncomputable abbrev qz84 := qz398

noncomputable abbrev qz85 := (@OfNat.ofNat Int 1 (@instOfNat 1))

noncomputable abbrev qz86 := (@OfNat.ofNat Int 2 (@instOfNat 2))

noncomputable abbrev qz407 := (@instHSub Int Int.instSub)

noncomputable abbrev qz408 := (@instHMul Int Int.instMul)

noncomputable def ep523 := @Enclosure.Complex.IsNear.of_eq qz76 (@HAdd.hAdd Complex Complex Complex qz4 (@HAdd.hAdd Complex Complex Complex qz4 qz79 qz80) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz75 (@HMul.hMul Complex Complex Complex qz74 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz83 qz84 (@HSub.hSub Int Int Int qz407 qz85 (@HMul.hMul Int Int Int qz408 qz86 (@Nat.cast Int instNatCastInt k)))))) Bool.true 5741646977925232057

noncomputable def ep524 := @Enclosure.Complex.IsNear.addLitP (@HAdd.hAdd Complex Complex Complex qz4 qz79 qz80) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz75 (@HMul.hMul Complex Complex Complex qz74 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz83 qz84 (@HSub.hSub Int Int Int qz407 qz85 (@HMul.hMul Int Int Int qz408 qz86 (@Nat.cast Int instNatCastInt k))))) Bool.true 5741649114422588857 56294995342131200

noncomputable def ep525 := nat_lit 394562975925857689888412925952

noncomputable def ep526 := nat_lit 1431031108315262298932876253593600

noncomputable def ep527 := @ep524 14376801578326360907 79325600000000000000000 Bool.false 208243501110701786633 900719925474099200 921906254188292523 9915700000000000000000 Bool.false 2608029 68719476736 3 68719476736 Bool.true 8143135881 6871947673600 9367 6871947673600 Bool.true ep525 5741646977925232057 56294995342131200 942198295189558448948027 ep517 Bool.false ep526

noncomputable def ep528 := @Enclosure.Complex.IsNear.addLitP qz79 qz80 Bool.true 5793380707012720057 56294995342131200 14225500003619329657 79325600000000000000000

noncomputable def ep529 := @ep528 Bool.false 208243501110701786633 900719925474099200 921906254188292523 9915700000000000000000 Bool.false 120447 131072 1 524288 Bool.false 0 1 0 1 Bool.true 752569432725597566664704 5741649114422588857 56294995342131200 14376801578326360907 79325600000000000000000 Bool.false 208243501110701786633 208243501110701786633 900719925474099200

noncomputable abbrev qz87 := (@HMul.hMul Complex Complex Complex qz396 qz402 qz403)

noncomputable def ep530 := @Enclosure.Complex.IsNear.subLitP qz87 qz84 Bool.true 5666716967492924857 56294995342131200 14225500003619329657 79325600000000000000000 Bool.false 271521327675070940681

noncomputable def ep531 := @ep530 900719925474099200 921906254188292523 9915700000000000000000 Bool.false 9000 4000 0 1 Bool.false 281010 4000 0 1 Bool.true 23173522828050880228000 5793380707012720057 56294995342131200 14225500003619329657 79325600000000000000000 Bool.false 832974004442807146532000 208243501110701786633 900719925474099200 921906254188292523 9915700000000000000000

noncomputable abbrev qz88 := qz402

noncomputable abbrev qz89 := qz403

noncomputable def ep532 := @Enclosure.Complex.IsNear.mul qz88 qz89 Bool.true 5666716967492924857 56294995342131200 14225500003619329657 79325600000000000000000 Bool.false 271521327675070940681 900719925474099200 921906254188292523

noncomputable abbrev qz90 := (Complex.re qz402)

noncomputable abbrev qz91 := (Complex.re qz403)

noncomputable abbrev qz92 := (Complex.im qz402)

noncomputable abbrev qz93 := (Complex.im qz403)

noncomputable def ep533 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 qz90 qz91) (@HMul.hMul Real Real Real qz0 qz92 qz93) 67032157851443267 9007199254740992 437500002082297 198314000000000000000 24342671816257781103 225179981368524800

noncomputable def ep534 := nat_lit 204164995385721627845699896214552576

noncomputable def ep535 := @Enclosure.Real.IsNear.mulLit_ff qz90 qz91 7000 4000 0 1 9576022550206181 2251799813685248 62500000297471 49578500000000000000

noncomputable def ep536 := @Enclosure.Complex.IsNear.re_isNear qz88 Bool.false 7000 4000 0 1 Bool.false 281010 4000 0 1

noncomputable abbrev qz660 := (Enclosure.sfrac Bool.false 281010 4000)

noncomputable abbrev qz409 := qz660

noncomputable def ep537 := @Enclosure.Complex.IsNear.of_eq qz88 (Complex.mk (Enclosure.sfrac Bool.false 7000 4000) qz409) Bool.false 7000 4000 0 1 Bool.false 281010 4000 0

noncomputable abbrev qz661 := (Enclosure.sfrac Bool.false 9000 4000)

noncomputable abbrev qz410 := (Complex.log (Complex.mk qz661 qz660))

noncomputable def ep538 := @Enclosure.Complex.IsNear.of_eq qz89 qz410 Bool.false 9576022550206181 2251799813685248 62500000297471 49578500000000000000 Bool.false 866256425616803 562949953421312 500000000099157 198314000000000000000

noncomputable def ep539 := nat_lit 6554923640636280392563998117716977201500000000

noncomputable def ep540 := nat_lit 19181951514628983650691098516403840800000000

noncomputable def ep541 := nat_lit 99988708351854705231903980131440300000000

noncomputable def ep542 := BSN.log_dyadic_bound 13511620100 144583620100 3 2 ep539 1048576 396628 ep540 ep541 196556 158095240200 131072000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 13511620100) (BSN.artanhQ 144583620100) 0 2 ep540 ep539 ep541 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz94 := (Enclosure.sfrac Bool.false 1 2)

noncomputable abbrev qz411 := (Enclosure.Real.IsNear.const Bool.false 1 2)

noncomputable abbrev qz662 := (Real.log (Enclosure.sfrac Bool.false 79047620100 16000000))

noncomputable abbrev qz663 := (@Nat.cast Real Real.instNatCast 16000000)

noncomputable def ep543 := @Enclosure.Real.IsNear.mulLit_ff qz94 qz662 1 2 0 1 9576022550206181 1125899906842624 62500000297471 24789250000000000000 9576022550206181 2251799813685248 62500000297471 49578500000000000000 qz411 (BSN.isNear_log_sfrac 79047620100 16000000 9576022550206181 1125899906842624 62500000297471 24789250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 79047620100) qz663)) Bool.false 321317997491359886344192 37778931862957161709568 1000000004759536 396628000000000000000 9576022550206181 1125899906842624 62500000297471 24789250000000000000 (BSN.log_rat_reduce_isNear 79047620100 16000000 12 158095240200 131072000000 196556 1048576 24973259072661432 36028797018963968 396628 1000000000000000 rfl rfl rfl rfl (ep542 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep544 := BSN.arctan_dyadic_bound_f 9000 281010 1 0 1048576 396628 0 1 1 0 1 1 33571 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 9000) (BSN.arctanEvenQ 281010) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 9000) (BSN.arctanOddQ 281010) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz95 := (@HMul.hMul Real Real Real qz267 (Enclosure.sfrac Bool.false 1 2) Real.pi)

noncomputable abbrev qz96 := (@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 2) Real.pi 1 2 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 qz411 BSN.pi_near_15 rfl)

noncomputable abbrev qz412 := (Real.arctan (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 9000) (@Nat.cast Real Real.instNatCast 281010)))

noncomputable def ep545 := @Enclosure.Real.IsNear.subLit_ff_p qz95 qz412 884279719003555 562949953421312 1 2000000000000000 33571 1048576 1 396628 908335697747564822528 866256425616803 562949953421312 500000000099157 198314000000000000000 qz96 (ep544 rfl) rfl rfl

noncomputable abbrev qz413 := (Complex.mk qz661 qz660)

noncomputable abbrev qz414 := (Real.arctan (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 281010) (@Nat.cast Real Real.instNatCast 9000)))

noncomputable def ep546 := @Enclosure.Complex.IsNear.re_isNear qz89 Bool.false 9576022550206181 2251799813685248 62500000297471 49578500000000000000 Bool.false 866256425616803 562949953421312 500000000099157 198314000000000000000 (ep538 (@congrArg Complex Complex qz84 qz413 Complex.log (BSN.w_shift_mk qz12 Bool.false 140505 1000 2 qz13 rfl)) (@Enclosure.Complex.IsNear.of_parts qz410 Bool.false 9576022550206181 2251799813685248 62500000297471 49578500000000000000 Bool.false 866256425616803 562949953421312 500000000099157 198314000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz410) (@HMul.hMul Real Real Real qz0 qz94 qz662) Bool.false 9576022550206181 2251799813685248 62500000297471 49578500000000000000 (Enclosure.clog_re_eq 9000 281010 4000 79047620100 16000000 rfl rfl rfl) (ep543 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz410) qz414 Bool.false 866256425616803 562949953421312 500000000099157 198314000000000000000 (Enclosure.clog_im_eq 9000 281010 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz414 (@HSub.hSub Real Real Real qz400 qz95 qz412) Bool.false 866256425616803 562949953421312 500000000099157 198314000000000000000 (BSN.arctan_recip 281010 9000 rfl rfl) ep545))))

noncomputable def ep547 := @Enclosure.Real.IsNear.mulLit_ff qz92 qz93 281010 4000 0 1 866256425616803 562949953421312 500000000099157 198314000000000000000

noncomputable def ep548 := @Enclosure.Complex.IsNear.im_isNear qz88 Bool.false 7000 4000 0 1 Bool.false 281010 4000 0 1

noncomputable def ep549 := @Enclosure.Complex.IsNear.im_isNear qz89 Bool.false 9576022550206181 2251799813685248 62500000297471 49578500000000000000 Bool.false 866256425616803 562949953421312 500000000099157 198314000000000000000 (ep538 (@congrArg Complex Complex qz84 qz413 Complex.log (BSN.w_shift_mk qz12 Bool.false 140505 1000 2 qz13 rfl)) (@Enclosure.Complex.IsNear.of_parts qz410 Bool.false 9576022550206181 2251799813685248 62500000297471 49578500000000000000 Bool.false 866256425616803 562949953421312 500000000099157 198314000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz410) (@HMul.hMul Real Real Real qz0 qz94 qz662) Bool.false 9576022550206181 2251799813685248 62500000297471 49578500000000000000 (Enclosure.clog_re_eq 9000 281010 4000 79047620100 16000000 rfl rfl rfl) (ep543 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz410) qz414 Bool.false 866256425616803 562949953421312 500000000099157 198314000000000000000 (Enclosure.clog_im_eq 9000 281010 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz414 (@HSub.hSub Real Real Real qz400 qz95 qz412) Bool.false 866256425616803 562949953421312 500000000099157 198314000000000000000 (BSN.arctan_recip 281010 9000 rfl rfl) ep545))))

noncomputable abbrev qz97 := (@ep537 1 (BSN.w_sub_half_mk qz277 Bool.false 140505 1000 2 qz279 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7000 4000) qz409 Bool.false 7000 4000 0 1 Bool.false 281010 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 7000 4000) (Enclosure.Real.IsNear.const Bool.false 281010 4000)))

noncomputable def ep550 := @ep533 14050500002786410857 79325600000000000000000 ep534 5666716967492924857 56294995342131200 14225500003619329657 79325600000000000000000 (@ep535 67032157851443267 9007199254740992 437500002082297 198314000000000000000 (ep536 qz97) ep546 rfl) (@ep547 24342671816257781103 225179981368524800 14050500002786410857 79325600000000000000000 (ep548 qz97) ep549 rfl) rfl

noncomputable def ep551 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz90 qz93) (@HMul.hMul Real Real Real qz0 qz92 qz91) 6063794979317621 2251799813685248 3500000000694099 793256000000000000000 269095809683343892281 900719925474099200

noncomputable def ep552 := nat_lit 611411675070295915733896904612773888

noncomputable def ep553 := @Enclosure.Real.IsNear.mulLit_ff qz90 qz93 7000 4000 0 1 866256425616803 562949953421312 500000000099157 198314000000000000000

noncomputable def ep554 := @Enclosure.Real.IsNear.mulLit_ff qz92 qz91 281010 4000 0 1 9576022550206181 2251799813685248 62500000297471 49578500000000000000

noncomputable def ep555 := @ep551 1756312508359232571 19831400000000000000000 ep552 271521327675070940681 900719925474099200 921906254188292523 9915700000000000000000 (@ep553 6063794979317621 2251799813685248 3500000000694099 793256000000000000000 (ep536 qz97) ep549 rfl) (@ep554 269095809683343892281 900719925474099200 1756312508359232571 19831400000000000000000 (ep548 qz97) ep546 rfl) rfl

noncomputable def ep556 := @Enclosure.Complex.IsNear.of_eq qz84 qz413 Bool.false 9000 4000 0 1 Bool.false 281010 4000 0 1 (BSN.w_shift_mk qz12 Bool.false 140505 1000 2 qz13 rfl)

noncomputable abbrev qz415 := (ep556 (@Enclosure.Complex.IsNear.mk qz661 qz660 Bool.false 9000 4000 0 1 Bool.false 281010 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 9000 4000) (Enclosure.Real.IsNear.const Bool.false 281010 4000)))

noncomputable abbrev qz98 := qz415

noncomputable def ep557 := ep531 (@ep532 9915700000000000000000 (ep550 rfl) (ep555 rfl)) qz98 rfl rfl rfl rfl rfl rfl

noncomputable abbrev qz99 := qz404

noncomputable def ep558 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re qz99) (Complex.re ↑qz2)) (@HMul.hMul Real Real Real qz0 (Complex.im qz99) (Complex.im ↑qz2)) 120447 131072 1 524288 0 1 0 1 120447 120447

noncomputable def ep559 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re qz99) (Complex.re ↑qz2) 1 2 0 1 120447 65536 1 262144 120447 131072 1 524288

noncomputable abbrev qz100 := (@Enclosure.Complex.IsNear.of_eq qz404 (Complex.mk (Enclosure.sfrac Bool.false 1 2) qz551) Bool.false 1 2 0 1 Bool.false 0 1 0 1 BSN.half_c_mk (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 2) qz551 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz411 qz553))

noncomputable def ep560 := ep559 (@Enclosure.Complex.IsNear.re_isNear qz99 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz100) (@Enclosure.Real.IsNear.of_eq (Complex.re ↑qz2) qz2 Bool.false 120447 65536 1 262144 (Complex.ofReal_re qz2) EMRow49.d4)

noncomputable def ep561 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz99) (Complex.im ↑qz2) 0 1 0 1 0 1 0 1 0 1 0 1

noncomputable def ep562 := ep561 (@Enclosure.Complex.IsNear.im_isNear qz99 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz100) (@Enclosure.Real.IsNear.of_eq (Complex.im ↑qz2) qz10 Bool.false 0 1 0 1 (@Eq.trans Real (Complex.im ↑qz2) (0 : Real) qz10 (Complex.ofReal_im qz2) Enclosure.sfrac_zero_eq) qz22)

noncomputable def ep563 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re qz99) (Complex.im ↑qz2)) (@HMul.hMul Real Real Real qz0 (Complex.im qz99) (Complex.re ↑qz2)) 0 1 0 1 0 1 0 1 0 0

noncomputable def ep564 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re qz99) (Complex.im ↑qz2) 1 2 0 1 0 1 0 1 0 1 0 1

noncomputable def ep565 := ep564 (@Enclosure.Complex.IsNear.re_isNear qz99 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz100) (@Enclosure.Real.IsNear.of_eq (Complex.im ↑qz2) qz10 Bool.false 0 1 0 1 (@Eq.trans Real (Complex.im ↑qz2) (0 : Real) qz10 (Complex.ofReal_im qz2) Enclosure.sfrac_zero_eq) qz22)

noncomputable def ep566 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz99) (Complex.re ↑qz2) 0 1 0 1 120447 65536 1 262144 0 1 0 1

noncomputable def ep567 := ep566 (@Enclosure.Complex.IsNear.im_isNear qz99 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz100) (@Enclosure.Real.IsNear.of_eq (Complex.re ↑qz2) qz2 Bool.false 120447 65536 1 262144 (Complex.ofReal_re qz2) EMRow49.d4)

noncomputable def ep568 := @ep529 921906254188292523 9915700000000000000000 (ep557 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@Enclosure.Complex.IsNear.mul qz99 (↑qz2) Bool.false 120447 131072 1 524288 Bool.false 0 1 0 1 (@ep558 131072 1 524288 (ep560 rfl) (ep562 rfl) rfl rfl) (@ep563 1 0 1 (ep565 rfl) (ep567 rfl) rfl rfl))

noncomputable abbrev qz101 := (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 1)

noncomputable abbrev qz416 := (@Nat.cast Complex Complex.instNatCast 1)

noncomputable abbrev qz102 := (@HMul.hMul Complex Complex Complex qz396 (@HMul.hMul Complex Complex Complex qz396 (2 : Complex) qz416) (@HSub.hSub Complex Complex Complex qz397 (@HMul.hMul Complex Complex Complex qz396 (2 : Complex) qz416) (1 : Complex)))

noncomputable abbrev qz417 := (@HPow.hPow Complex Int Complex qz659 qz655 (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) (@OfNat.ofNat Int 1 (@instOfNat 1)) (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (@OfNat.ofNat Int 2 (@instOfNat 2)) (@Nat.cast Int instNatCastInt 1))))

noncomputable abbrev qz103 := qz417

noncomputable def ep569 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz75 (@HMul.hMul Complex Complex Complex qz74 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz83 qz84 (@HSub.hSub Int Int Int qz407 qz85 (@HMul.hMul Int Int Int qz408 qz86 (@Nat.cast Int instNatCastInt k))))) (@HAdd.hAdd Complex Complex Complex qz4 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz75 (@HMul.hMul Complex Complex Complex qz74 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz83 qz84 (@HSub.hSub Int Int Int qz407 qz85 (@HMul.hMul Int Int Int qz408 qz86 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 (@Rat.cast Complex Complex.instRatCast (bernoulli qz101)) qz102) qz103)) Bool.false 2608029 68719476736 3 68719476736

noncomputable def ep570 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz75 (@HMul.hMul Complex Complex Complex qz74 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz83 qz84 (@HSub.hSub Int Int Int qz407 qz85 (@HMul.hMul Int Int Int qz408 qz86 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 (@Rat.cast Complex Complex.instRatCast (bernoulli qz101)) qz102) qz103) Bool.false 0 1 0 1 Bool.false

noncomputable def ep571 := @ep570 0 1 0 1 Bool.false 2608029 68719476736 3 68719476736 Bool.true 8143135881 6871947673600 9367 6871947673600 Bool.false 2608029 2608029 68719476736 3 68719476736 Bool.true 8143135881 8143135881 6871947673600 9367

noncomputable def ep572 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz75 (@HMul.hMul Complex Complex Complex qz74 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz83 qz84 (@HSub.hSub Int Int Int qz407 qz85 (@HMul.hMul Int Int Int qz408 qz86 (@Nat.cast Int instNatCastInt k))))) (Complex.mk qz10 qz10) Bool.false 0 1 0 1 Bool.false

noncomputable def ep573 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz81 (@Rat.cast Complex Complex.instRatCast (bernoulli qz101)) qz102) qz103 Bool.false 2608029 68719476736 3 68719476736 Bool.true 8143135881 6871947673600 9367 6871947673600

noncomputable abbrev qz104 := (Complex.re qz417)

noncomputable abbrev qz105 := (Complex.im qz417)

noncomputable def ep574 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz81 (@Rat.cast Complex Complex.instRatCast (bernoulli qz101)) qz102)) qz104) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz81 (@Rat.cast Complex Complex.instRatCast (bernoulli qz101)) qz102)) qz105) 2608029 68719476736 3 68719476736 0 1 0

noncomputable def ep575 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz81 (@Rat.cast Complex Complex.instRatCast (bernoulli qz101)) qz102)) qz104 1 12 0 1 7824087 17179869184 9 17179869184 2608029

noncomputable def ep576 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz81 (@Rat.cast Complex Complex.instRatCast (bernoulli qz101)) qz102) (Complex.mk (Enclosure.sfrac Bool.false 1 12) qz10) Bool.false 1 12 0 1 Bool.false 0 1 0 1

noncomputable abbrev qz418 := (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 12) qz10 Bool.false 1 12 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 12) qz22)

noncomputable def ep577 := @Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz81 (@Rat.cast Complex Complex.instRatCast (bernoulli qz101)) qz102) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (ep576 (BSN.stirling_coeff_mk 1 1 6 Bool.false BSN.bern_real_1 rfl rfl) qz418)

noncomputable def ep578 := @Enclosure.Complex.IsNear.re_isNear qz103 Bool.false 7824087 17179869184 9 17179869184 Bool.true 24429407643 1717986918400 28101 1717986918400

noncomputable abbrev qz664 := (@instHPow Complex Nat (@NPow.toPow Complex (@Monoid.toNPow Complex (@Semiring.toMonoid Complex Complex.instSemiring))))

noncomputable abbrev qz419 := (@HPow.hPow Complex Nat Complex qz664 qz655 1)

noncomputable abbrev qz106 := (@Inv.inv Complex Complex.instInv qz419)

noncomputable def ep579 := @Enclosure.Complex.IsNear.of_eq qz103 qz106 Bool.false 7824087 17179869184 9 17179869184 Bool.true 24429407643 1717986918400 28101

noncomputable def ep580 := @Enclosure.Complex.IsNear.of_parts qz106 Bool.false 7824087 17179869184 9 17179869184 Bool.true 24429407643 1717986918400 28101

noncomputable abbrev qz107 := (Complex.re qz419)

noncomputable abbrev qz108 := (@MonoidWithZeroHom Complex Real (@instMulZeroOneClassOfSemiring Complex Complex.instSemiring) (@instMulZeroOneClassOfSemiring Real Real.semiring))

noncomputable abbrev qz109 := (@MonoidWithZeroHom.funLike Complex Real (@instMulZeroOneClassOfSemiring Complex Complex.instSemiring) (@instMulZeroOneClassOfSemiring Real Real.semiring))

noncomputable abbrev qz110 := qz419

noncomputable def ep581 := @Enclosure.Real.IsNear.mulLit_ff qz107 (@Inv.inv Real Real.instInv (@DFunLike.coe qz108 Complex (fun (x : Complex) => Real) qz109 Complex.normSq qz110)) 9000 4000 0 1 869343 4294967296 1 4294967296

noncomputable def ep582 := @Enclosure.Complex.IsNear.re_isNear qz110 Bool.false 9000 4000 0 1 Bool.false 281010 4000 0 1

noncomputable def ep583 := @Enclosure.Complex.IsNear.of_eq qz110 qz84 Bool.false 9000 4000 0 1 Bool.false 281010 4000 0

noncomputable def ep584 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (@DFunLike.coe qz108 Complex (fun (x : Complex) => Real) qz109 Complex.normSq qz110)) Bool.false 869343 4294967296 1 4294967296 869343 4294967296 1

noncomputable abbrev qz111 := (Complex.im qz419)

noncomputable abbrev qz420 := (@instHAdd Real Real.instAdd)

noncomputable def ep585 := @Enclosure.Real.IsNear.of_eq (@DFunLike.coe qz108 Complex (fun (x : Complex) => Real) qz109 Complex.normSq qz110) (@HAdd.hAdd Real Real Real qz420 (@HMul.hMul Real Real Real qz0 qz107 qz107) (@HMul.hMul Real Real Real qz0 qz111 qz111)) Bool.false 790476201 160000 0 1

noncomputable def ep586 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz107 qz107) (@HMul.hMul Real Real Real qz0 qz111 qz111) 81 16 0 1 789666201 160000

noncomputable def ep587 := @Enclosure.Real.IsNear.mulLit_ff qz107 qz107 9000 4000 0 1 9000 4000 0 1

noncomputable def ep588 := @Enclosure.Real.IsNear.mulLit_ff qz111 qz111 281010 4000 0 1 281010 4000 0 1

noncomputable def ep589 := @Enclosure.Complex.IsNear.im_isNear qz110 Bool.false 9000 4000 0 1 Bool.false 281010 4000 0 1

noncomputable abbrev qz112 := (ep582 (@ep583 1 (BSN.pow_one_c qz398) qz415))

noncomputable abbrev qz113 := (ep589 (@ep583 1 (BSN.pow_one_c qz398) qz415))

noncomputable def ep590 := @ep586 0 1 12647619216 790476201 160000 0 1 (@ep587 81 16 0 1 qz112 qz112 rfl) (@ep588 789666201 160000 0 1 qz113 qz113 rfl)

noncomputable def ep591 := @Enclosure.Real.IsNear.inv_image (@DFunLike.coe qz108 Complex (fun (x : Complex) => Real) qz109 Complex.normSq qz110) 790476201 160000 0 1 434671 434672 2147483648 (ep585 (Enclosure.Complex.normSq_eq_mul_add_mul qz110) (ep590 rfl rfl)) rfl

noncomputable def ep592 := @Enclosure.Real.IsNear.of_eq (Complex.re qz106) (@HMul.hMul Real Real Real qz0 qz107 (@Inv.inv Real Real.instInv (@DFunLike.coe qz108 Complex (fun (x : Complex) => Real) qz109 Complex.normSq qz110))) Bool.false 7824087 17179869184 9 17179869184 (Enclosure.Complex.inv_re_eq_mul qz110) (@ep581 7824087 17179869184 9 17179869184 qz112 (@ep584 4294967296 (ep591 rfl rfl rfl rfl rfl) rfl) rfl)

noncomputable def ep593 := @Enclosure.Real.IsNear.of_eq (Complex.im qz106) (@HMul.hMul Real Real Real qz0 (@Neg.neg Real Real.instNeg qz111) (@Inv.inv Real Real.instInv (@DFunLike.coe qz108 Complex (fun (x : Complex) => Real) qz109 Complex.normSq qz110))) Bool.true 24429407643 1717986918400 28101 1717986918400 (Enclosure.Complex.inv_im_eq_mul qz110)

noncomputable def ep594 := @Enclosure.Real.IsNear.mulLit_tf (@Neg.neg Real Real.instNeg qz111) (@Inv.inv Real Real.instInv (@DFunLike.coe qz108 Complex (fun (x : Complex) => Real) qz109 Complex.normSq qz110)) 281010 4000 0 1 869343 4294967296 1

noncomputable def ep595 := @ep594 4294967296 24429407643 1717986918400 28101 1717986918400 (@Enclosure.Real.IsNear.neg qz111 Bool.false 281010 4000 0 1 qz113) (@ep584 4294967296 (ep591 rfl rfl rfl rfl rfl) rfl) rfl

noncomputable def ep596 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz81 (@Rat.cast Complex Complex.instRatCast (bernoulli qz101)) qz102)) qz105 0 1 0 1 24429407643 1717986918400 28101 1717986918400 0

noncomputable def ep597 := @Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz81 (@Rat.cast Complex Complex.instRatCast (bernoulli qz101)) qz102) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (ep576 (BSN.stirling_coeff_mk 1 1 6 Bool.false BSN.bern_real_1 rfl rfl) qz418)

noncomputable def ep598 := @Enclosure.Complex.IsNear.im_isNear qz103 Bool.false 7824087 17179869184 9 17179869184 Bool.true 24429407643 1717986918400 28101 1717986918400

noncomputable abbrev qz114 := (@ep579 1717986918400 (BSN.zpow_one_sub_two_mul qz398 1 1 rfl rfl) (@ep580 1717986918400 ep592 (ep593 ep595)))

noncomputable def ep599 := @ep574 1 2608029 2608029 68719476736 3 68719476736 (@ep575 68719476736 3 68719476736 ep577 (ep578 qz114) rfl) (@ep596 1 0 1 ep597 (ep598 qz114) rfl) rfl

noncomputable def ep600 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz81 (@Rat.cast Complex Complex.instRatCast (bernoulli qz101)) qz102)) qz105) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz81 (@Rat.cast Complex Complex.instRatCast (bernoulli qz101)) qz102)) qz104) 8143135881 6871947673600 9367 6871947673600 0 1 0

noncomputable def ep601 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HDiv.hDiv Complex Complex Complex qz81 (@Rat.cast Complex Complex.instRatCast (bernoulli qz101)) qz102)) qz105 1 12 0 1 24429407643 1717986918400 28101 1717986918400 8143135881

noncomputable def ep602 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz81 (@Rat.cast Complex Complex.instRatCast (bernoulli qz101)) qz102)) qz104 0 1 0 1 7824087 17179869184 9 17179869184 0

noncomputable def ep603 := @ep600 1 8143135881 8143135881 6871947673600 9367 6871947673600 (@ep601 6871947673600 9367 6871947673600 ep577 (ep598 qz114) rfl) (@ep602 1 0 1 ep597 (ep578 qz114) rfl) rfl

noncomputable abbrev qz115 := (@Enclosure.Complex.IsNear.mk qz551 qz551 Bool.false 0 1 0 1 Bool.false 0 1 0 1 qz553 qz553)

noncomputable def ep604 := @ep571 6871947673600 (@ep572 0 1 0 1 (BSN.stirling_sum_base qz84) qz115) (ep573 (ep599 rfl) (ep603 rfl)) rfl rfl rfl rfl rfl

noncomputable def ep605 := @ep527 208242433773595592201 900719925474099200 ep519 ep512 (ep568 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep569 Bool.true 8143135881 6871947673600 9367 6871947673600 (BSN.stirling_sum_succ qz84 0 1 rfl) (ep604 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl

noncomputable def ep606 := @Enclosure.Complex.IsNear.of_eq (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz77 (@Nat.cast Complex Complex.instNatCast j))) (BSN.logSumC qz12 2) Bool.false 9575053498210021 1125899906842624 62500000297471 24789250000000000000 Bool.false 878270522885539 281474976710656

noncomputable abbrev qz116 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz272 qz399 qz416))

noncomputable def ep607 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz12 2) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.logSumC qz12 1) qz116) Bool.false 9575053498210021 1125899906842624 62500000297471 24789250000000000000 Bool.false 878270522885539 281474976710656 500000000099157 99157000000000000000

noncomputable def ep608 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz12 1) qz116 Bool.false 9574882236389093 2251799813685248 62500000297471 49578500000000000000 Bool.false 882276653630883 562949953421312 500000000099157 198314000000000000000 Bool.false

noncomputable def ep609 := nat_lit 43122207366591214764134986940416

noncomputable def ep610 := nat_lit 988844699899451029935238414336

noncomputable abbrev qz117 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz272 qz399 (@Nat.cast Complex Complex.instNatCast 0)))

noncomputable def ep611 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz12 1) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.logSumC qz12 0) qz117) Bool.false 9574882236389093 2251799813685248 62500000297471 49578500000000000000 Bool.false 882276653630883 562949953421312 500000000099157 198314000000000000000

noncomputable def ep612 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz12 0) qz117 Bool.false 0 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable abbrev qz421 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz660))

noncomputable def ep613 := @Enclosure.Complex.IsNear.of_eq qz117 qz421 Bool.false 9574882236389093 2251799813685248 62500000297471 49578500000000000000 Bool.false 882276653630883 562949953421312 500000000099157 198314000000000000000

noncomputable def ep614 := nat_lit 6540427978666881978379635100432177201500000000

noncomputable def ep615 := nat_lit 18933449731738124392045930897843840800000000

noncomputable def ep616 := nat_lit 97641592408621636854814123171440300000000

noncomputable def ep617 := BSN.log_dyadic_bound 13431620100 144503620100 3 2 ep614 1048576 396628 ep615 ep616 195494 157935240200 131072000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 13431620100) (BSN.artanhQ 144503620100) 0 2 ep615 ep614 ep616 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep618 := @Enclosure.Real.IsNear.mulLit_ff qz94 (Real.log (Enclosure.sfrac Bool.false 78967620100 16000000)) 1 2 0 1 9574882236389093 1125899906842624 62500000297471 24789250000000000000 9574882236389093 2251799813685248 62500000297471 49578500000000000000 qz411 (BSN.isNear_log_sfrac 78967620100 16000000 9574882236389093 1125899906842624 62500000297471 24789250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 78967620100) qz663)) Bool.false 321279734908925746610176 37778931862957161709568 1000000004759536 396628000000000000000 9574882236389093 1125899906842624 62500000297471 24789250000000000000 (BSN.log_rat_reduce_isNear 78967620100 16000000 12 157935240200 131072000000 195494 1048576 24973259072661432 36028797018963968 396628 1000000000000000 rfl rfl rfl rfl (ep617 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep619 := BSN.arctan_dyadic_bound_f 1000 281010 1 0 1048576 396628 0 1 1 0 1 1 3731 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 281010) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 281010) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz422 := (@Nat.cast Real Real.instNatCast 281010)

noncomputable abbrev qz665 := (@Nat.cast Real Real.instNatCast 1000)

noncomputable def ep620 := @Enclosure.Real.IsNear.subLit_ff_p qz95 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz665 qz422)) 884279719003555 562949953421312 1 2000000000000000 3731 1048576 1 396628 925134124357656772608 882276653630883 562949953421312 500000000099157 198314000000000000000 qz96 (ep619 rfl) rfl rfl

noncomputable abbrev qz118 := (@HAdd.hAdd Complex Complex Complex qz272 qz399 (@Nat.cast Complex Complex.instNatCast 0))

noncomputable abbrev qz423 := (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz660)

noncomputable def ep621 := @ep612 9574882236389093 2251799813685248 62500000297471 49578500000000000000 Bool.false 882276653630883 562949953421312 500000000099157 198314000000000000000 Bool.false 9574882236389093 9574882236389093 2251799813685248 62500000297471 49578500000000000000 Bool.false 882276653630883 882276653630883 562949953421312 500000000099157 198314000000000000000 (@Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz12 0) (Complex.mk qz10 qz10) Bool.false 0 1 0 1 Bool.false 0 1 0 1 (BSN.log_sum_c_base qz12) qz115) (ep613 (@congrArg Complex Complex qz118 qz423 Complex.log (BSN.w_shift_mk qz12 Bool.false 140505 1000 0 qz13 rfl)) (@Enclosure.Complex.IsNear.of_parts qz421 Bool.false 9574882236389093 2251799813685248 62500000297471 49578500000000000000 Bool.false 882276653630883 562949953421312 500000000099157 198314000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz421) (@HMul.hMul Real Real Real qz0 qz94 (Real.log (Enclosure.sfrac Bool.false 78967620100 16000000))) Bool.false 9574882236389093 2251799813685248 62500000297471 49578500000000000000 (Enclosure.clog_re_eq 1000 281010 4000 78967620100 16000000 rfl rfl rfl) (ep618 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz421) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz422 qz665)) Bool.false 882276653630883 562949953421312 500000000099157 198314000000000000000 (Enclosure.clog_im_eq 1000 281010 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz422 qz665)) (@HSub.hSub Real Real Real qz400 qz95 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz665 qz422))) Bool.false 882276653630883 562949953421312 500000000099157 198314000000000000000 (BSN.arctan_recip 281010 1000 rfl rfl) ep620)))) rfl rfl

noncomputable abbrev qz424 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz660))

noncomputable def ep622 := @Enclosure.Complex.IsNear.of_eq qz116 qz424 Bool.false 9575224760030949 2251799813685248 62500000297471 49578500000000000000 Bool.false 874264392140195 562949953421312 500000000099157 198314000000000000000

noncomputable def ep623 := nat_lit 6544774150244042865349287756017617201500000000

noncomputable def ep624 := nat_lit 19007801952260973011584948063411840800000000

noncomputable def ep625 := nat_lit 98341340186244700761491160259440300000000

noncomputable def ep626 := BSN.log_dyadic_bound 13455620100 144527620100 3 2 ep623 1048576 396628 ep624 ep625 195813 157983240200 131072000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 13455620100) (BSN.artanhQ 144527620100) 0 2 ep624 ep623 ep625 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep627 := @Enclosure.Real.IsNear.mulLit_ff qz94 (Real.log (Enclosure.sfrac Bool.false 78991620100 16000000)) 1 2 0 1 9575224760030949 1125899906842624 62500000297471 24789250000000000000 9575224760030949 2251799813685248 62500000297471 49578500000000000000 qz411 (BSN.isNear_log_sfrac 78991620100 16000000 9575224760030949 1125899906842624 62500000297471 24789250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 78991620100) qz663)) Bool.false 321291228095174796115968 37778931862957161709568 1000000004759536 396628000000000000000 9575224760030949 1125899906842624 62500000297471 24789250000000000000 (BSN.log_rat_reduce_isNear 78991620100 16000000 12 157983240200 131072000000 195813 1048576 24973259072661432 36028797018963968 396628 1000000000000000 rfl rfl rfl rfl (ep626 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep628 := BSN.arctan_dyadic_bound_f 5000 281010 1 0 1048576 396628 0 1 1 0 1 1 18655 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 5000) (BSN.arctanEvenQ 281010) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 5000) (BSN.arctanOddQ 281010) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz666 := (@Nat.cast Real Real.instNatCast 5000)

noncomputable def ep629 := @Enclosure.Real.IsNear.subLit_ff_p qz95 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz666 qz422)) 884279719003555 562949953421312 1 2000000000000000 18655 1048576 1 396628 916732659252797112320 874264392140195 562949953421312 500000000099157 198314000000000000000 qz96 (ep628 rfl) rfl rfl

noncomputable abbrev qz119 := (@HAdd.hAdd Complex Complex Complex qz272 qz399 qz416)

noncomputable abbrev qz425 := (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz660)

noncomputable def ep630 := @ep608 9575224760030949 2251799813685248 62500000297471 49578500000000000000 Bool.false 874264392140195 562949953421312 500000000099157 198314000000000000000 Bool.false ep609 9575053498210021 1125899906842624 62500000297471 24789250000000000000 Bool.false ep610 878270522885539 281474976710656 500000000099157 99157000000000000000 (ep611 (BSN.log_sum_c_succ qz12 0 1 rfl) (ep621 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep622 (@congrArg Complex Complex qz119 qz425 Complex.log (BSN.w_shift_mk qz12 Bool.false 140505 1000 1 qz13 rfl)) (@Enclosure.Complex.IsNear.of_parts qz424 Bool.false 9575224760030949 2251799813685248 62500000297471 49578500000000000000 Bool.false 874264392140195 562949953421312 500000000099157 198314000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz424) (@HMul.hMul Real Real Real qz0 qz94 (Real.log (Enclosure.sfrac Bool.false 78991620100 16000000))) Bool.false 9575224760030949 2251799813685248 62500000297471 49578500000000000000 (Enclosure.clog_re_eq 5000 281010 4000 78991620100 16000000 rfl rfl rfl) (ep627 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz424) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz422 qz666)) Bool.false 874264392140195 562949953421312 500000000099157 198314000000000000000 (Enclosure.clog_im_eq 5000 281010 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz422 qz666)) (@HSub.hSub Real Real Real qz400 qz95 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz666 qz422))) Bool.false 874264392140195 562949953421312 500000000099157 198314000000000000000 (BSN.arctan_recip 281010 5000 rfl rfl) ep629)))) rfl rfl

noncomputable def ep631 := @ep520 ep512 Bool.false 9575053498210021 1125899906842624 62500000297471 24789250000000000000 Bool.false 878270522885539 281474976710656 500000000099157 99157000000000000000 Bool.true ep521 6220399652835733107 56294995342131200 955305495251942639207227 ep517 Bool.false ep522 205431968100361867401 900719925474099200 ep514 ep512 (@ep523 56294995342131200 942198295189558448948027 ep517 Bool.false 208242433773595592201 900719925474099200 ep519 ep512 (BSN.logGammaStirling_unfold 1 qz84) (ep605 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (@ep606 500000000099157 99157000000000000000 (BSN.log_sum_c_eq qz12 2) (ep607 (BSN.log_sum_c_succ qz12 1 2 rfl) (ep630 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)))

noncomputable abbrev qz120 := (@HDiv.hDiv Real Real Real qz270 qz277 (2 : Real))

noncomputable def ep632 := @Enclosure.Real.IsNear.mulLit_ff qz120 (Real.log Real.pi) 140505 2000 0 1 75021 65536 1 262144 2108165121 26214400 28101 104857600 (@Enclosure.Real.IsNear.of_eq qz120 (Enclosure.sfrac Bool.false 140505 2000) Bool.false 140505 2000 0 1 (BSN.t_half_eq qz12 Bool.false 140505 1000 qz13) (Enclosure.Real.IsNear.const Bool.false 140505 2000)) EMRow49.d5 rfl

noncomputable def ep633 := @ep515 28101 104857600 ep516 132995966106258804873 900719925474099200 ep511 ep512 (@ep518 ep514 ep512 (ep631 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) ep632 rfl rfl

noncomputable def ep634 := BSN.cos_dyadic_bound_f 704631 2147483648 1 0 1048576 397016 0 1 1 0 1 1 1048575 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 704631) qz15 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 704631) qz16 0 0 rfl) rfl rfl

noncomputable def ep635 := @ep510 1048576 Bool.true 1048575 1048576 1 198314 (@ep513 154827681 1048576 385 1048576 ep633 rfl) (Enclosure.sfrac_false_div 154827681 1048576) (BSN.cos_reduce2 qz401 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 49584050128459661312) qz27) 226375608064910080 72057594037927936 Bool.false 1048575 1048576 23 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q2 154827681 1048576 226375608064910080 72057594037927936 23 49584050128459661312 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1048575 1048576 49584050128459661312 151115727451828646838272 704631 2147483648 397016 396628 (ep634 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep636 := nat_lit 5001167031422271891701760

noncomputable def ep637 := nat_lit 50865907446078482821802053879

noncomputable def ep638 := nat_lit 7438510790021073209482071244800

noncomputable abbrev qz667 := (@Nat.cast Complex Complex.instNatCast 36)

noncomputable abbrev qz426 := (@HPow.hPow Complex Complex Complex qz542 qz667 qz543)

noncomputable abbrev qz121 := qz426

noncomputable abbrev qz427 := qz667

noncomputable abbrev qz122 := (@HAdd.hAdd Complex Complex Complex qz272 (@HDiv.hDiv Complex Complex Complex qz405 qz427 (@HSub.hSub Complex Complex Complex qz397 qz271 (1 : Complex))) qz404)

noncomputable abbrev qz123 := (@instHSub Nat instSubNat)

noncomputable abbrev qz428 := qz664

noncomputable abbrev qz124 := qz428

noncomputable abbrev qz125 := qz427

noncomputable def ep639 := @Enclosure.Complex.IsNear.of_eq (zetaApproximant qz5 1 36) (@HAdd.hAdd Complex Complex Complex qz4 (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 36, @HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast n) qz7) (@HMul.hMul Complex Complex Complex qz74 qz121 (@HAdd.hAdd Complex Complex Complex qz4 qz122 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz82 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz124 qz125 (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1))))))) Bool.false 551341890180636259841777 750175054713340783755264 ep507

noncomputable def ep640 := @Enclosure.Complex.IsNear.addLitP (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 36, @HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast n) qz7) (@HMul.hMul Complex Complex Complex qz74 qz121 (@HAdd.hAdd Complex Complex Complex qz4 qz122 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz82 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz124 qz125 (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))))) Bool.false 737927888093 1099511627776 739418477887573 109024274475384832

noncomputable def ep641 := nat_lit 14084371674357533081615479

noncomputable def ep642 := nat_lit 507305612623956498221701879

noncomputable def ep643 := nat_lit 606206819133608004734000729478397952

noncomputable def ep644 := nat_lit 9182639430507914971567805199024128

noncomputable def ep645 := @ep640 Bool.false 5706760909 137438953472 184523158716545 27256068618846208 Bool.false 47868275313650624107025 750175054713340783755264 ep641 ep508 Bool.true 274471705377859404507769 ep636 ep642 ep638 Bool.false ep643 551341890180636259841777 750175054713340783755264 ep507 ep508 Bool.true ep644 66812495282705021757049 ep636

noncomputable def ep646 := @Enclosure.Complex.IsNear.of_eq (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 36, @HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast n) qz7) (BSN.headSumC qz5 36) Bool.false 737927888093 1099511627776 739418477887573 109024274475384832 Bool.false 5706760909 137438953472 184523158716545

noncomputable abbrev qz668 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 35) qz7)

noncomputable def ep647 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 36) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 35) qz668) Bool.false 737927888093 1099511627776 739418477887573 109024274475384832 Bool.false 5706760909 137438953472 184523158716545 27256068618846208

noncomputable def ep648 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 35) qz668 Bool.false 923690280891 1099511627776 726145987728095 109024274475384832 Bool.false 19966196655 549755813888 362460433995337 54512137237692416 Bool.true

noncomputable abbrev qz669 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 34) qz7)

noncomputable def ep649 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 35) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 34) qz669) Bool.false 923690280891 1099511627776 726145987728095 109024274475384832 Bool.false 19966196655 549755813888 362460433995337 54512137237692416

noncomputable def ep650 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 34) qz669 Bool.false 806559381057 1099511627776 712720555439093 109024274475384832 Bool.true 107840468979 1099511627776 711478539844657 109024274475384832 Bool.false

noncomputable abbrev qz670 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 33) qz7)

noncomputable def ep651 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 34) (@HAdd.hAdd Complex Complex Complex qz4 qz65 qz670) Bool.false 806559381057 1099511627776 712720555439093 109024274475384832 Bool.true 107840468979 1099511627776 711478539844657 109024274475384832

noncomputable def ep652 := @Enclosure.Complex.IsNear.addLitP qz65 qz670 Bool.false 367559533959 549755813888 349560000476849 54512137237692416 Bool.false 17431680189 274877906944 348910167144789 54512137237692416 Bool.false

noncomputable abbrev qz671 := (Real.log (Enclosure.sfrac Bool.false 33 1))

noncomputable abbrev qz126 := (@HMul.hMul Real Real Real qz267 qz277 qz671)

noncomputable abbrev qz429 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 33)))

noncomputable def ep653 := @Enclosure.Complex.IsNear.of_eq qz670 (Complex.mk (@HMul.hMul Real Real Real qz0 qz429 (Real.cos qz126)) (@HMul.hMul Real Real Real qz0 qz429 (@Neg.neg Real Real.instNeg (Real.sin qz126)))) Bool.false 71440313139 1099511627776 13600554485395 109024274475384832 Bool.true 177567189735 1099511627776 13658205555079 109024274475384832 (BSN.cpow_neg_s_mk qz12 140505 1000 33 qz13 rfl)

noncomputable abbrev qz430 := (Real.sqrt (@Nat.cast Real Real.instNatCast 33))

noncomputable abbrev qz431 := (@Nat.cast Real Real.instNatCast 33)

noncomputable abbrev qz672 := (@HDiv.hDiv Real Real Real qz1 qz431 qz14)

noncomputable def ep654 := @Enclosure.Real.IsNear.inv_image qz430 6023611 1048576 1 1048576 91266 91267 524288 (@Enclosure.Real.IsNear.of_eq qz430 (Real.sqrt qz672) Bool.false 6023611 1048576 1 1048576 (BSN.sqrt_natCast_div_one 33) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz672) Bool.false 6023611 1048576 1 1048576 6023611 1048576 1 1048576 (BSN.sqrt_enclosure 33 1 3011805 3011806 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep655 := BSN.log_dyadic_bound 1 65 2 1 12675 524288 198314 1 1 16133 66 64 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 1) (BSN.artanhQ 65) 0 1 1 12675 1 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep656 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz671 140505 1000 0 1 15746868335186131 4503599627370496 100000000099157 19831400000000000000 442502747087065467231 900719925474099200 2810100002786410857 3966280000000000000000 qz18 (BSN.isNear_log_sfrac 33 1 15746868335186131 4503599627370496 100000000099157 19831400000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz672) Bool.false 66047152845744529997824 18889465931478580854784 1000000000991570 198314000000000000000 15746868335186131 4503599627370496 100000000099157 19831400000000000000 (BSN.log_rat_reduce_isNear 33 1 5 66 64 16133 524288 24973259072661432 36028797018963968 198314 1000000000000000 rfl rfl rfl rfl (ep655 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep657 := nat_lit 1516856912291624201584145122605511406166873643938293137321260970000598318562241

noncomputable def ep658 := nat_lit 1798049007900862512773313412195601810516593417819831269573835427189736192961

noncomputable def ep659 := nat_lit 4546974638859070879726888740992143014879587744979239749424635239147415483300801

noncomputable def ep660 := BSN.cos_dyadic_bound_f 2551820903 2147483648 3 2 1048576 397016 ep657 ep102 ep658 ep659 ep104 ep658 391383 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2551820903) qz15 0 2 ep657 ep102 ep658 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2551820903) qz16 0 2 ep659 ep104 ep658 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz432 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 515140997) qz26)

noncomputable def ep661 := @Enclosure.Real.IsNear.cos_image qz126 qz432 Bool.false 515140997 1048576 93 131072 Bool.false 391383 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz126 Bool.false 442502747087065467231 900719925474099200 2810100002786410857 3966280000000000000000 515140997 1048576 93 131072 (ep656 rfl) rfl) (Enclosure.sfrac_false_div 515140997 1048576) (BSN.cos_reduce0 qz432 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 179568432330306092007424) qz27) 226375608064910080 72057594037927936 Bool.false 391383 1048576 78 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q0 515140997 1048576 226375608064910080 72057594037927936 78 179568432330306092007424 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 391383 1048576 179568432330306092007424 151115727451828646838272 2551820903 2147483648 397016 396628 (ep660 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep662 := nat_lit 2728904002918602872841242569960164049651959284354671782162610677659325184457665

noncomputable def ep663 := nat_lit 7144218404488310889563526128180684393776199831585765416941813184130401624505281

noncomputable def ep664 := BSN.sin_dyadic_bound_f 2551820903 2147483648 3 2 1048576 397016 ep662 ep95 ep658 ep663 ep98 ep658 972795 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2551820903) qz20 0 2 ep662 ep95 ep658 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2551820903) qz21 0 2 ep663 ep98 ep658 rfl rfl rfl rfl) rfl rfl

noncomputable def ep665 := @Enclosure.Real.IsNear.sin_image qz126 qz432 Bool.false 515140997 1048576 93 131072 Bool.false 972795 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz126 Bool.false 442502747087065467231 900719925474099200 2810100002786410857 3966280000000000000000 515140997 1048576 93 131072 (ep656 rfl) rfl) (Enclosure.sfrac_false_div 515140997 1048576) (BSN.sin_reduce0 qz432 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 179568432330306092007424) qz27) 226375608064910080 72057594037927936 Bool.false 972795 1048576 78 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q0 515140997 1048576 226375608064910080 72057594037927936 78 179568432330306092007424 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 972795 1048576 179568432330306092007424 151115727451828646838272 2551820903 2147483648 397016 396628 (ep664 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz433 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 33))) Bool.false 182533 1048576 1 1048576 182533 1048576 1 1048576 (ep654 rfl rfl) rfl)

noncomputable def ep666 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz429 (Real.cos qz126)) (@HMul.hMul Real Real Real qz0 qz429 (@Neg.neg Real Real.instNeg (Real.sin qz126))) Bool.false 71440313139 1099511627776 13600554485395 109024274475384832 Bool.true 177567189735 1099511627776 13658205555079 109024274475384832 (@Enclosure.Real.IsNear.mulLit_ff qz429 (Real.cos qz126) 182533 1048576 1 1048576 391383 1048576 9287137 12996706304 71440313139 1099511627776 13600554485395 109024274475384832 qz433 (@Enclosure.Real.IsNear.recentre' (Real.cos qz126) Bool.false 391383 1048576 18574274 25993412608 391383 1048576 9287137 12996706304 (ep661 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz429 (@Neg.neg Real Real.instNeg (Real.sin qz126)) 182533 1048576 1 1048576 972795 1048576 9287137 12996706304 177567189735 1099511627776 13658205555079 109024274475384832 qz433 (@Enclosure.Real.IsNear.neg (Real.sin qz126) Bool.false 972795 1048576 9287137 12996706304 (@Enclosure.Real.IsNear.recentre' (Real.sin qz126) Bool.false 972795 1048576 18574274 25993412608 972795 1048576 9287137 12996706304 (ep665 rfl rfl) rfl)) rfl)

noncomputable def ep667 := @ep652 71440313139 1099511627776 13600554485395 109024274475384832 Bool.true 177567189735 1099511627776 13658205555079 109024274475384832 Bool.false 443410708981992564719616 806559381057 1099511627776 712720555439093 109024274475384832 Bool.true 29642962396806880690176 107840468979 1099511627776 711478539844657 109024274475384832 EMRow49.d9 (ep653 ep666) rfl rfl

noncomputable abbrev qz673 := (Real.log (Enclosure.sfrac Bool.false 34 1))

noncomputable abbrev qz127 := (@HMul.hMul Real Real Real qz267 qz277 qz673)

noncomputable abbrev qz434 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 34)))

noncomputable def ep668 := @Enclosure.Complex.IsNear.of_eq qz669 (Complex.mk (@HMul.hMul Real Real Real qz0 qz434 (Real.cos qz127)) (@HMul.hMul Real Real Real qz0 qz434 (@Neg.neg Real Real.instNeg (Real.sin qz127)))) Bool.false 58565449917 549755813888 6712716144501 54512137237692416 Bool.false 147772862289 1099511627776 13442328146017 109024274475384832 (BSN.cpow_neg_s_mk qz12 140505 1000 34 qz13 rfl)

noncomputable abbrev qz435 := (Real.sqrt (@Nat.cast Real Real.instNatCast 34))

noncomputable abbrev qz436 := (@Nat.cast Real Real.instNatCast 34)

noncomputable abbrev qz674 := (@HDiv.hDiv Real Real Real qz1 qz436 qz14)

noncomputable def ep669 := @Enclosure.Real.IsNear.inv_image qz435 6114197 1048576 1 1048576 89914 89915 524288 (@Enclosure.Real.IsNear.of_eq qz435 (Real.sqrt qz674) Bool.false 6114197 1048576 1 1048576 (BSN.sqrt_natCast_div_one 34) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz674) Bool.false 6114197 1048576 1 1048576 6114197 1048576 1 1048576 (BSN.sqrt_enclosure 34 1 3057098 3057099 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep670 := BSN.log_dyadic_bound 2 66 2 1 13068 524288 198314 4 4 31784 68 64 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 2) (BSN.artanhQ 66) 0 1 4 13068 4 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep671 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz673 140505 1000 0 1 15881309401485523 4503599627370496 100000000099157 19831400000000000000 446280675491144681823 900719925474099200 2810100002786410857 3966280000000000000000 qz18 (BSN.isNear_log_sfrac 34 1 15881309401485523 4503599627370496 100000000099157 19831400000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz674) Bool.false 66611039547888335060992 18889465931478580854784 1000000000991570 198314000000000000000 15881309401485523 4503599627370496 100000000099157 19831400000000000000 (BSN.log_rat_reduce_isNear 34 1 5 68 64 31784 524288 24973259072661432 36028797018963968 198314 1000000000000000 rfl rfl rfl rfl (ep670 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep672 := nat_lit 4291758084703692397681416601600000000

noncomputable def ep673 := BSN.sin_dyadic_bound_f 1439324800 2147483648 2 1 1048576 397016 ep672 ep70 ep672 ep672 ep71 ep672 651346 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1439324800) qz20 0 1 ep672 ep70 ep672 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1439324800) qz21 0 1 ep672 ep71 ep672 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz437 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 129884771) qz24)

noncomputable def ep674 := @Enclosure.Real.IsNear.cos_image qz127 qz437 Bool.false 129884771 262144 93 131072 Bool.false 651346 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz127 Bool.false 446280675491144681823 900719925474099200 2810100002786410857 3966280000000000000000 129884771 262144 93 131072 (ep671 rfl) rfl) (Enclosure.sfrac_false_div 129884771 262144) (BSN.cos_reduce3 qz437 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 25320869675617340096512) qz291) 226375608064910080 72057594037927936 Bool.false 651346 1048576 78 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q3 129884771 262144 226375608064910080 72057594037927936 78 25320869675617340096512 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 651346 1048576 25320869675617340096512 37778931862957161709568 1439324800 2147483648 397016 396628 (ep673 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep675 := nat_lit 153361427115537444686921125135542850329541238568410671442054619332608000000000

noncomputable def ep676 := nat_lit 18419187457619506129292308103531835641735324655336093122560000000000000000

noncomputable def ep677 := nat_lit 460047442971697095048504790790421487317340245055921342139918737997824000000000

noncomputable def ep678 := BSN.cos_dyadic_bound_f 1439324800 2147483648 3 2 1048576 397016 ep675 ep102 ep676 ep677 ep104 ep676 821741 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1439324800) qz15 0 2 ep675 ep102 ep676 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1439324800) qz16 0 2 ep677 ep104 ep676 rfl rfl rfl rfl) rfl rfl

noncomputable def ep679 := @Enclosure.Real.IsNear.sin_image qz127 qz437 Bool.false 129884771 262144 93 131072 Bool.true 821741 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz127 Bool.false 446280675491144681823 900719925474099200 2810100002786410857 3966280000000000000000 129884771 262144 93 131072 (ep671 rfl) rfl) (Enclosure.sfrac_false_div 129884771 262144) (BSN.sin_reduce3 qz437 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 25320869675617340096512) qz291) 226375608064910080 72057594037927936 Bool.false 821741 1048576 78 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q3 129884771 262144 226375608064910080 72057594037927936 78 25320869675617340096512 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 821741 1048576 25320869675617340096512 37778931862957161709568 1439324800 2147483648 397016 396628 (ep678 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz438 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 34))) Bool.false 179829 1048576 1 1048576 179829 1048576 1 1048576 (ep669 rfl rfl) rfl)

noncomputable def ep680 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz434 (Real.cos qz127)) (@HMul.hMul Real Real Real qz0 qz434 (@Neg.neg Real Real.instNeg (Real.sin qz127))) Bool.false 58565449917 549755813888 6712716144501 54512137237692416 Bool.false 147772862289 1099511627776 13442328146017 109024274475384832 (@Enclosure.Real.IsNear.mulLit_ff qz434 (Real.cos qz127) 179829 1048576 1 1048576 325673 524288 9287137 12996706304 58565449917 549755813888 6712716144501 54512137237692416 qz438 (@Enclosure.Real.IsNear.recentre' (Real.cos qz127) Bool.false 651346 1048576 18574274 25993412608 325673 524288 9287137 12996706304 (ep674 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz434 (@Neg.neg Real Real.instNeg (Real.sin qz127)) 179829 1048576 1 1048576 821741 1048576 9287137 12996706304 147772862289 1099511627776 13442328146017 109024274475384832 qz438 (@Enclosure.Real.IsNear.neg (Real.sin qz127) Bool.true 821741 1048576 9287137 12996706304 (@Enclosure.Real.IsNear.recentre' (Real.sin qz127) Bool.true 821741 1048576 18574274 25993412608 821741 1048576 9287137 12996706304 (ep679 rfl rfl) rfl)) rfl)

noncomputable def ep681 := @ep650 58565449917 549755813888 6712716144501 54512137237692416 Bool.false 147772862289 1099511627776 13442328146017 109024274475384832 Bool.false 507804102151667038814208 923690280891 1099511627776 726145987728095 109024274475384832 Bool.false 43906130769269552578560 19966196655 549755813888 362460433995337 54512137237692416 (ep651 (BSN.head_sum_c_succ qz5 33 34 rfl rfl) (ep667 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep668 ep680) rfl rfl

noncomputable abbrev qz675 := (Real.log (Enclosure.sfrac Bool.false 35 1))

noncomputable abbrev qz128 := (@HMul.hMul Real Real Real qz267 qz277 qz675)

noncomputable abbrev qz439 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 35)))

noncomputable def ep682 := @Enclosure.Complex.IsNear.of_eq qz668 (Complex.mk (@HMul.hMul Real Real Real qz0 qz439 (Real.cos qz128)) (@HMul.hMul Real Real Real qz0 qz439 (@Neg.neg Real Real.instNeg (Real.sin qz128)))) Bool.true 92881196399 549755813888 6636245079739 54512137237692416 Bool.false 2860846981 549755813888 6585883437753 54512137237692416 (BSN.cpow_neg_s_mk qz12 140505 1000 35 qz13 rfl)

noncomputable abbrev qz440 := (Real.sqrt (@Nat.cast Real Real.instNatCast 35))

noncomputable abbrev qz441 := (@Nat.cast Real Real.instNatCast 35)

noncomputable abbrev qz676 := (@HDiv.hDiv Real Real Real qz1 qz441 qz14)

noncomputable def ep683 := @Enclosure.Real.IsNear.inv_image qz440 6203459 1048576 1 1048576 88620 88621 524288 (@Enclosure.Real.IsNear.of_eq qz440 (Real.sqrt qz676) Bool.false 6203459 1048576 1 1048576 (BSN.sqrt_natCast_div_one 35) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz676) Bool.false 6203459 1048576 1 1048576 6203459 1048576 1 1048576 (BSN.sqrt_enclosure 35 1 3101729 3101730 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep684 := BSN.log_dyadic_bound 3 67 2 1 13467 524288 198314 9 9 46982 70 64 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 3) (BSN.artanhQ 67) 0 1 9 13467 9 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep685 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz675 140505 1000 0 1 16011859227414739 4503599627370496 100000000099157 19831400000000000000 449949256149581580639 900719925474099200 2810100002786410857 3966280000000000000000 qz18 (BSN.isNear_log_sfrac 35 1 16011859227414739 4503599627370496 100000000099157 19831400000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz676) Bool.false 67158605204982549446656 18889465931478580854784 1000000000991570 198314000000000000000 16011859227414739 4503599627370496 100000000099157 19831400000000000000 (BSN.log_rat_reduce_isNear 35 1 5 70 64 46982 524288 24973259072661432 36028797018963968 198314 1000000000000000 rfl rfl rfl rfl (ep684 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep686 := BSN.cos_dyadic_bound_f 66124442 2147483648 1 0 1048576 397016 0 1 1 0 1 1 1048078 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 66124442) qz15 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 66124442) qz16 0 0 rfl) rfl rfl

noncomputable abbrev qz442 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 261904937) qz17)

noncomputable def ep687 := @Enclosure.Real.IsNear.cos_image qz128 qz442 Bool.false 261904937 524288 93 131072 Bool.true 1048078 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz128 Bool.false 449949256149581580639 900719925474099200 2810100002786410857 3966280000000000000000 261904937 524288 93 131072 (ep685 rfl) rfl) (Enclosure.sfrac_false_div 261904937 524288) (BSN.cos_reduce2 qz442 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 2326546989070201913344) qz19) 226375608064910080 72057594037927936 Bool.false 1048078 1048576 79 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q2 261904937 524288 226375608064910080 72057594037927936 79 2326546989070201913344 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1048078 1048576 2326546989070201913344 75557863725914323419136 66124442 2147483648 397016 396628 (ep686 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep688 := BSN.sin_dyadic_bound_f 66124442 2147483648 1 0 1048576 397016 0 1 1 0 1 1 32282 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 66124442) qz20 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 66124442) qz21 0 0 rfl) rfl rfl

noncomputable def ep689 := @Enclosure.Real.IsNear.sin_image qz128 qz442 Bool.false 261904937 524288 93 131072 Bool.true 32282 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz128 Bool.false 449949256149581580639 900719925474099200 2810100002786410857 3966280000000000000000 261904937 524288 93 131072 (ep685 rfl) rfl) (Enclosure.sfrac_false_div 261904937 524288) (BSN.sin_reduce2 qz442 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 2326546989070201913344) qz19) 226375608064910080 72057594037927936 Bool.false 32282 1048576 79 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q2 261904937 524288 226375608064910080 72057594037927936 79 2326546989070201913344 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 32282 1048576 2326546989070201913344 75557863725914323419136 66124442 2147483648 397016 396628 (ep688 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz443 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 35))) Bool.false 177241 1048576 1 1048576 177241 1048576 1 1048576 (ep683 rfl rfl) rfl)

noncomputable def ep690 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz439 (Real.cos qz128)) (@HMul.hMul Real Real Real qz0 qz439 (@Neg.neg Real Real.instNeg (Real.sin qz128))) Bool.true 92881196399 549755813888 6636245079739 54512137237692416 Bool.false 2860846981 549755813888 6585883437753 54512137237692416 (@Enclosure.Real.IsNear.mulLit_ft qz439 (Real.cos qz128) 177241 1048576 1 1048576 524039 524288 9287137 12996706304 92881196399 549755813888 6636245079739 54512137237692416 qz443 (@Enclosure.Real.IsNear.recentre' (Real.cos qz128) Bool.true 1048078 1048576 18574274 25993412608 524039 524288 9287137 12996706304 (ep687 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz439 (@Neg.neg Real Real.instNeg (Real.sin qz128)) 177241 1048576 1 1048576 16141 524288 9287137 12996706304 2860846981 549755813888 6585883437753 54512137237692416 qz443 (@Enclosure.Real.IsNear.neg (Real.sin qz128) Bool.true 16141 524288 9287137 12996706304 (@Enclosure.Real.IsNear.recentre' (Real.sin qz128) Bool.true 32282 1048576 18574274 25993412608 16141 524288 9287137 12996706304 (ep689 rfl rfl) rfl)) rfl)

noncomputable def ep691 := @ep648 92881196399 549755813888 6636245079739 54512137237692416 Bool.false 2860846981 549755813888 6585883437753 54512137237692416 Bool.false 405680146709220199235584 737927888093 1099511627776 739418477887573 109024274475384832 Bool.false 12549299952766070816768 5706760909 137438953472 184523158716545 27256068618846208 (ep649 (BSN.head_sum_c_succ qz5 34 35 rfl rfl) (ep681 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep682 ep690) rfl rfl

noncomputable def ep692 := @Enclosure.Complex.IsNear.mul qz121 (@HAdd.hAdd Complex Complex Complex qz4 qz122 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz82 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz124 qz125 (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1))))) Bool.false 47868275313650624107025 750175054713340783755264 ep641 ep508 Bool.true

noncomputable def ep693 := nat_lit 1485061506990069690061769

noncomputable abbrev qz129 := (Complex.re qz426)

noncomputable abbrev qz130 := (Complex.im qz426)

noncomputable def ep694 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 qz129 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz122 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz82 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz124 qz125 (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz130 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz122 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz82 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz124 qz125 (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1))))))) 41398965018215779395845 750175054713340783755264 ep693

noncomputable def ep695 := nat_lit 24795035966736910698273570816

noncomputable def ep696 := nat_lit 1281644337080214248325553

noncomputable def ep697 := nat_lit 154968974792105691864209817600

noncomputable def ep698 := nat_lit 997488501456975469607596473049525396281753600

noncomputable def ep699 := @Enclosure.Real.IsNear.mulLit_ff qz129 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz122 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz82 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz124 qz125 (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))))) 121295133965 1099511627776 13053278096979 109024274475384832 341307715033

noncomputable abbrev qz677 := (Real.log (Enclosure.sfrac Bool.false 36 1))

noncomputable abbrev qz131 := (@HMul.hMul Real Real Real qz267 qz277 qz677)

noncomputable abbrev qz132 := (Real.sin (@HMul.hMul Real Real Real qz267 qz277 qz677))

noncomputable abbrev qz678 := (@Nat.cast Real Real.instNatCast 36)

noncomputable abbrev qz444 := (@Inv.inv Real Real.instInv (Real.sqrt qz678))

noncomputable abbrev qz679 := (@Neg.neg Real Real.instNeg qz132)

noncomputable def ep700 := @Enclosure.Complex.IsNear.of_eq qz121 (Complex.mk (@HMul.hMul Real Real Real qz0 qz444 (Real.cos qz131)) (@HMul.hMul Real Real Real qz0 qz444 qz679)) Bool.false 121295133965 1099511627776 13053278096979 109024274475384832 Bool.true 8585232375 68719476736 816399692959 6814017154711552 (BSN.cpow_neg_s_mk qz12 140505 1000 36 qz13 rfl)

noncomputable abbrev qz445 := (Real.sqrt qz678)

noncomputable abbrev qz446 := (@HDiv.hDiv Real Real Real qz1 qz678 qz14)

noncomputable def ep701 := @Enclosure.Real.IsNear.inv_image qz445 6291457 1048576 1 1048576 87381 87382 524288 (@Enclosure.Real.IsNear.of_eq qz445 (Real.sqrt qz446) Bool.false 6291457 1048576 1 1048576 (BSN.sqrt_natCast_div_one 36) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz446) Bool.false 6291457 1048576 1 1048576 6291457 1048576 1 1048576 (BSN.sqrt_enclosure 36 1 3145728 3145729 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep702 := BSN.log_dyadic_bound 4 68 3 2 320720640 524288 198314 370688 768 61752 72 64 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 4) (BSN.artanhQ 68) 0 2 370688 320720640 768 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz133 := qz677

noncomputable abbrev qz447 := (Real.log (@HDiv.hDiv Real Real Real qz1 qz678 qz14))

noncomputable def ep703 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz133 140505 1000 0 1 16138732561338579 4503599627370496 100000000099157 19831400000000000000 453514523706175408479 900719925474099200 2810100002786410857 3966280000000000000000 qz18 (BSN.isNear_log_sfrac 36 1 16138732561338579 4503599627370496 100000000099157 19831400000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' qz447 Bool.false 67690750536952647254016 18889465931478580854784 1000000000991570 198314000000000000000 16138732561338579 4503599627370496 100000000099157 19831400000000000000 (BSN.log_rat_reduce_isNear 36 1 5 72 64 61752 524288 24973259072661432 36028797018963968 198314 1000000000000000 rfl rfl rfl rfl (ep702 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep704 := nat_lit 392030744849122685698155282517485018678313624855000627729619331762594486313216

noncomputable def ep705 := nat_lit 120313997575723416574509515435446412248490471582639087736906815069166919936

noncomputable def ep706 := nat_lit 1175851606552216610261316828521584163210443893621836605013384181657645125099776

noncomputable def ep707 := BSN.cos_dyadic_bound_f 1819866454 2147483648 3 2 1048576 397016 ep704 ep102 ep705 ep706 ep104 ep705 694055 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1819866454) qz15 0 2 ep704 ep102 ep705 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1819866454) qz16 0 2 ep706 ep104 ep705 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz448 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 65995049) qz585)

noncomputable def ep708 := @Enclosure.Real.IsNear.cos_image qz131 qz448 Bool.false 65995049 131072 93 131072 Bool.false 694055 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz131 Bool.false 453514523706175408479 900719925474099200 2810100002786410857 3966280000000000000000 65995049 131072 93 131072 (ep703 rfl) rfl) (Enclosure.sfrac_false_div 65995049 131072) (BSN.cos_reduce0 qz448 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 16007714619477907734528) qz332) 226375608064910080 72057594037927936 Bool.false 694055 1048576 80 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q0 65995049 131072 226375608064910080 72057594037927936 80 16007714619477907734528 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 694055 1048576 16007714619477907734528 18889465931478580854784 1819866454 2147483648 397016 396628 (ep707 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep709 := nat_lit 10968773749864814153655564288687901456

noncomputable def ep710 := BSN.sin_dyadic_bound_f 1819866454 2147483648 2 1 1048576 397016 ep709 ep70 ep709 ep709 ep71 ep709 786000 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1819866454) qz20 0 1 ep709 ep70 ep709 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1819866454) qz21 0 1 ep709 ep71 ep709 rfl rfl rfl rfl) rfl rfl

noncomputable def ep711 := @Enclosure.Real.IsNear.sin_image qz131 qz448 Bool.false 65995049 131072 93 131072 Bool.false 786000 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz131 Bool.false 453514523706175408479 900719925474099200 2810100002786410857 3966280000000000000000 65995049 131072 93 131072 (ep703 rfl) rfl) (Enclosure.sfrac_false_div 65995049 131072) (BSN.sin_reduce0 qz448 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 16007714619477907734528) qz332) 226375608064910080 72057594037927936 Bool.false 786000 1048576 80 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q0 65995049 131072 226375608064910080 72057594037927936 80 16007714619477907734528 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 786000 1048576 16007714619477907734528 18889465931478580854784 1819866454 2147483648 397016 396628 (ep710 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz449 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz678)) Bool.false 174763 1048576 1 1048576 174763 1048576 1 1048576 (ep701 rfl rfl) rfl)

noncomputable def ep712 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz444 (Real.cos qz131)) (@HMul.hMul Real Real Real qz0 qz444 qz679) Bool.false 121295133965 1099511627776 13053278096979 109024274475384832 Bool.true 8585232375 68719476736 816399692959 6814017154711552 (@Enclosure.Real.IsNear.mulLit_ff qz444 (Real.cos qz131) 174763 1048576 1 1048576 694055 1048576 9287137 12996706304 121295133965 1099511627776 13053278096979 109024274475384832 qz449 (@Enclosure.Real.IsNear.recentre' (Real.cos qz131) Bool.false 694055 1048576 18574274 25993412608 694055 1048576 9287137 12996706304 (ep708 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz444 qz679 174763 1048576 1 1048576 49125 65536 9287137 12996706304 8585232375 68719476736 816399692959 6814017154711552 qz449 (@Enclosure.Real.IsNear.neg qz132 Bool.false 49125 65536 9287137 12996706304 (@Enclosure.Real.IsNear.recentre' qz132 Bool.false 786000 1048576 18574274 25993412608 49125 65536 9287137 12996706304 (ep711 rfl rfl) rfl)) rfl)

noncomputable def ep713 := @ep699 682280237664 0 1 41398965018215779395845 750175054713340783755264 ep693 ep695 (@Enclosure.Complex.IsNear.re_isNear qz121 Bool.false 121295133965 1099511627776 13053278096979 109024274475384832 Bool.true 8585232375 68719476736 816399692959 6814017154711552 (ep700 ep712))

noncomputable def ep714 := @Enclosure.Complex.IsNear.re_isNear (@HAdd.hAdd Complex Complex Complex qz4 qz122 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz82 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz124 qz125 (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1))))) Bool.false 341307715033 682280237664 0 1 Bool.false

noncomputable def ep715 := @Enclosure.Complex.IsNear.addLitP qz122 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz82 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz124 qz125 (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) Bool.false 788236201 1579352402 0 1 Bool.true 202327200

noncomputable def ep716 := @ep715 789676201 0 1 Bool.false 1 864 0 1 Bool.false 9367 28800 0 1 Bool.false 682615430066 341307715033 682280237664 0 1 Bool.false 1569873614767 1569873614767 22742674588800 0 1

noncomputable abbrev qz134 := (@HDiv.hDiv Complex Complex Complex qz405 qz427 (@HSub.hSub Complex Complex Complex qz397 qz271 (1 : Complex)))

noncomputable def ep717 := @Enclosure.Complex.IsNear.addLitP qz134 qz99 Bool.true 72000000 78967620100 0 1 Bool.true 20232720000 78967620100 0 1

noncomputable def ep718 := @Enclosure.Complex.IsNear.of_eq qz134 (Complex.mk (Enclosure.sfrac Bool.true 72000000 78967620100) (Enclosure.sfrac Bool.true 20232720000 78967620100)) Bool.true 72000000 78967620100 0 1 Bool.true 20232720000 78967620100 0 1

noncomputable def ep719 := @ep717 Bool.false 1 2 0 1 Bool.false 0 1 0 1 Bool.false 78823620100 788236201 1579352402 0 1 Bool.true 20232720000 202327200 789676201 0 1 (ep718 (BSN.N_div_s_sub_one_mk qz12 140505 1000 36 qz13 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 72000000 78967620100) (Enclosure.sfrac Bool.true 20232720000 78967620100) Bool.true 72000000 78967620100 0 1 Bool.true 20232720000 78967620100 0 1 (Enclosure.Real.IsNear.const Bool.true 72000000 78967620100) (Enclosure.Real.IsNear.const Bool.true 20232720000 78967620100))) qz100 rfl

noncomputable abbrev qz135 := (@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 1)))

noncomputable abbrev qz450 := (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz664 qz667 1))

noncomputable abbrev qz136 := qz450

noncomputable def ep720 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz82 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz124 qz125 (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) (@HAdd.hAdd Complex Complex Complex qz4 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz82 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz124 qz125 (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz135) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz136)) Bool.false 1 864 0 1

noncomputable def ep721 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz82 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz124 qz125 (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz135) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz136) Bool.false 0 1 0 1 Bool.false

noncomputable def ep722 := @ep721 0 1 0 1 Bool.false 1 864 0 1 Bool.false 9367 28800 0 1 Bool.false 1 1 864 0 1 Bool.false 9367 9367 28800 0

noncomputable def ep723 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz82 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz124 qz125 (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) (Complex.mk qz10 qz10) Bool.false 0 1 0 1 Bool.false

noncomputable def ep724 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz135) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz136 Bool.false 1 864 0 1 Bool.false 9367 28800 0 1

noncomputable abbrev qz137 := (Complex.re qz450)

noncomputable abbrev qz138 := (Complex.im qz450)

noncomputable def ep725 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz135) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) qz137) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz135) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) qz138) 1 864 0 1 0 1 0

noncomputable def ep726 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz135) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) qz137 1 24 0 1 1 36 0 1 1

noncomputable def ep727 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz135)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz135)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) 1 24 0 1 0 1 0 1 1

noncomputable def ep728 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz135)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 1 2 0 1 1 24 0

noncomputable def ep729 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz135) (Complex.mk (Enclosure.sfrac Bool.false 1 12) qz10) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (BSN.bern_coeff_mk 1 1 6 2 Bool.false BSN.bern_real_1 EMRow49.d10 rfl) qz418

noncomputable def ep730 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) qz5 Bool.false 1 2 0 1 Bool.false 140505 1000 0 1 (BSN.ascPochhammer_one_eval qz5)

noncomputable def ep731 := ep730 (@Enclosure.Complex.IsNear.of_eq qz5 (Complex.mk qz94 qz12) Bool.false 1 2 0 1 Bool.false 140505 1000 0 1 (BSN.s_crit_mk qz12 Bool.false 140505 1000 qz13) (@Enclosure.Complex.IsNear.mk qz94 qz12 Bool.false 1 2 0 1 Bool.false 140505 1000 0 1 qz411 qz18))

noncomputable def ep732 := @ep728 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz135) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep729) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 140505 1000 0 1 ep731)

noncomputable def ep733 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz135)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 140505 1000 0 1 0 1 0

noncomputable def ep734 := @ep733 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz135) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep729) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 140505 1000 0 1 ep731)

noncomputable def ep735 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz135)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz135)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) 9367 800 0 1 0 1 0 1 9367

noncomputable def ep736 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz135)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 140505 1000 0 1 9367 800 0

noncomputable def ep737 := @ep736 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz135) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep729) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 140505 1000 0 1 ep731)

noncomputable def ep738 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz135)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 1 2 0 1 0 1 0

noncomputable def ep739 := @ep738 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz135) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep729) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 140505 1000 0 1 ep731)

noncomputable def ep740 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz135) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 24 0 1 Bool.false 9367 800 0 1 (@ep727 1 24 0 1 (ep732 rfl) (ep734 rfl) rfl rfl) (@ep735 9367 800 0 1 (ep737 rfl) (ep739 rfl) rfl rfl)

noncomputable def ep741 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz135) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 9367 800 0 1 ep740

noncomputable abbrev qz139 := (@Enclosure.Complex.IsNear.re_isNear qz450 Bool.false 1 36 0 1 Bool.false 0 1 0 1 (@Enclosure.Complex.IsNear.of_eq qz450 (Complex.mk (Enclosure.sfrac Bool.false 1 36) qz551) Bool.false 1 36 0 1 Bool.false 0 1 0 1 (BSN.natCast_pow_inv_mk 36 1 36 EMRow49.d11 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 36) qz551 Bool.false 1 36 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 36) qz553)))

noncomputable def ep742 := @ep726 864 0 1 ep741 qz139

noncomputable def ep743 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz135) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) qz138 9367 800 0 1 0 1 0 1 0

noncomputable def ep744 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz135) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 9367 800 0 1 ep740

noncomputable abbrev qz140 := (@Enclosure.Complex.IsNear.im_isNear qz450 Bool.false 1 36 0 1 Bool.false 0 1 0 1 (@Enclosure.Complex.IsNear.of_eq qz450 (Complex.mk (Enclosure.sfrac Bool.false 1 36) qz551) Bool.false 1 36 0 1 Bool.false 0 1 0 1 (BSN.natCast_pow_inv_mk 36 1 36 EMRow49.d11 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 36) qz551 Bool.false 1 36 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 36) qz553)))

noncomputable def ep745 := @ep743 1 0 1 ep744 qz140

noncomputable def ep746 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz135) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) qz138) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz135) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) qz137) 0 1 0 1 9367 28800 0

noncomputable def ep747 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz135) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) qz138 1 24 0 1 0 1 0 1 0

noncomputable def ep748 := @ep747 1 0 1 ep741 qz140

noncomputable def ep749 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz135) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) qz137 9367 800 0 1 1 36 0 1 9367

noncomputable def ep750 := @ep749 28800 0 1 ep744 qz139

noncomputable def ep751 := @ep722 1 (@ep723 0 1 0 1 (BSN.bern_sum_base qz5 36) qz115) (ep724 (@ep725 1 1 1 864 0 1 (ep742 rfl) (ep745 rfl) rfl rfl) (@ep746 1 9367 9367 28800 0 1 (ep748 rfl) (ep750 rfl) rfl rfl)) rfl rfl rfl rfl rfl

noncomputable def ep752 := ep716 (ep719 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep720 Bool.false 9367 28800 0 1 (BSN.bern_sum_succ qz5 36 0 1 1 rfl rfl) (ep751 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl rfl

noncomputable def ep753 := @Enclosure.Real.IsNear.mulLit_tf qz130 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz122 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz82 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz124 qz125 (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))))) 8585232375 68719476736 816399692959 6814017154711552 1569873614767

noncomputable def ep754 := @ep753 22742674588800 0 1 179703063762079019755 20838195964259466215424 ep696 ep697 (@Enclosure.Complex.IsNear.im_isNear qz121 Bool.false 121295133965 1099511627776 13053278096979 109024274475384832 Bool.true 8585232375 68719476736 816399692959 6814017154711552 (ep700 ep712))

noncomputable def ep755 := @Enclosure.Complex.IsNear.im_isNear (@HAdd.hAdd Complex Complex Complex qz4 qz122 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz82 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz124 qz125 (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1))))) Bool.false 341307715033 682280237664 0 1 Bool.false

noncomputable def ep756 := nat_lit 6830665623554443170829631

noncomputable def ep757 := @Enclosure.Real.IsNear.addLit_ft_n (@HMul.hMul Real Real Real qz0 qz129 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz122 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz82 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz124 qz125 (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz130 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz122 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz82 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz124 qz125 (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1))))))) 38083606082256413452231 ep636 ep756

noncomputable def ep758 := nat_lit 826501198891230356609119027200

noncomputable def ep759 := nat_lit 4649069243763170755926294528

noncomputable def ep760 := nat_lit 4289621387481242304456449782510734861026721792

noncomputable def ep761 := @Enclosure.Real.IsNear.mulLit_ff qz129 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz122 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz82 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz124 qz125 (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))))) 121295133965 1099511627776 13053278096979 109024274475384832 1569873614767

noncomputable def ep762 := @ep761 22742674588800 0 1 38083606082256413452231 ep636 ep756 ep758 (@Enclosure.Complex.IsNear.re_isNear qz121 Bool.false 121295133965 1099511627776 13053278096979 109024274475384832 Bool.true 8585232375 68719476736 816399692959 6814017154711552 (ep700 ep712))

noncomputable def ep763 := @Enclosure.Real.IsNear.mulLit_tf qz130 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz122 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz82 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz124 qz125 (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))))) 8585232375 68719476736 816399692959 6814017154711552 341307715033

noncomputable def ep764 := @ep763 682280237664 0 1 976735348312861931125 15628646973194599661568 278643513757479068552647 ep759 (@Enclosure.Complex.IsNear.im_isNear qz121 Bool.false 121295133965 1099511627776 13053278096979 109024274475384832 Bool.true 8585232375 68719476736 816399692959 6814017154711552 (ep700 ep712))

noncomputable abbrev qz680 := (ep752 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable def ep765 := @ep692 274471705377859404507769 ep636 ep642 ep638 (@ep694 ep695 179703063762079019755 20838195964259466215424 ep696 ep697 ep698 47868275313650624107025 750175054713340783755264 ep641 ep508 (ep713 (@ep714 1569873614767 22742674588800 0 1 qz680) rfl) (ep754 (@ep755 1569873614767 22742674588800 0 1 qz680) rfl) rfl rfl) (@ep757 ep758 976735348312861931125 15628646973194599661568 278643513757479068552647 ep759 ep760 274471705377859404507769 ep636 ep642 ep638 (ep762 (@ep755 1569873614767 22742674588800 0 1 qz680) rfl) (ep764 (@ep714 1569873614767 22742674588800 0 1 qz680) rfl) rfl rfl)

noncomputable def ep766 := @ep645 ep637 ep638 (@ep646 27256068618846208 (BSN.head_sum_c_eq qz5 36) (ep647 (BSN.head_sum_c_succ qz5 35 36 rfl rfl) (ep691 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))) ep765 rfl rfl rfl

noncomputable def ep767 := @Enclosure.Complex.IsNear.re_isNear (zetaApproximant qz5 1 36) Bool.false 551341890180636259841777 750175054713340783755264 ep507 ep508 Bool.true 66812495282705021757049 ep636 ep637 ep638 (@ep639 ep508 Bool.true 66812495282705021757049 ep636 ep637 ep638 (BSN.zetaApproximant_eq_folded' qz5 1 36 rfl) (ep766 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

noncomputable def ep768 := @Enclosure.Real.IsNear.mulLit_tt (Real.sin (@HSub.hSub Real Real Real qz400 (Complex.im (@HSub.hSub Complex Complex Complex qz75 qz76 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz77 (@Nat.cast Complex Complex.instNatCast j))))) qz78)) (Complex.im (zetaApproximant qz5 1 36)) 43 131072 38699733

noncomputable def ep769 := @Enclosure.Real.IsNear.recentre' (Real.sin (@HSub.hSub Real Real Real qz400 (Complex.im (@HSub.hSub Complex Complex Complex qz75 qz76 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz77 (@Nat.cast Complex Complex.instNatCast j))))) qz78)) Bool.true 344 1048576 77399466

noncomputable def ep770 := @Enclosure.Real.IsNear.sin_image (@HSub.hSub Real Real Real qz400 (Complex.im (@HSub.hSub Complex Complex Complex qz75 qz76 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz77 (@Nat.cast Complex Complex.instNatCast j))))) qz78) qz401 Bool.false 154827681 1048576 385

noncomputable def ep771 := BSN.sin_dyadic_bound_f 704631 2147483648 1 0 1048576 397016 0 1 1 0 1 1 344 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 704631) qz20 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 704631) qz21 0 0 rfl) rfl rfl

noncomputable def ep772 := @ep770 1048576 Bool.true 344 1048576 1 198314 (@ep513 154827681 1048576 385 1048576 ep633 rfl) (Enclosure.sfrac_false_div 154827681 1048576) (BSN.sin_reduce2 qz401 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 49584050128459661312) qz27) 226375608064910080 72057594037927936 Bool.false 344 1048576 23 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q2 154827681 1048576 226375608064910080 72057594037927936 23 49584050128459661312 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 344 1048576 49584050128459661312 151115727451828646838272 704631 2147483648 397016 396628 (ep771 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep773 := @Enclosure.Complex.IsNear.im_isNear (zetaApproximant qz5 1 36) Bool.false 551341890180636259841777 750175054713340783755264 ep507 ep508 Bool.true 66812495282705021757049 ep636 ep637 ep638 (@ep639 ep508 Bool.true 66812495282705021757049 ep636 ep637 ep638 (BSN.zetaApproximant_eq_folded' qz5 1 36 rfl) (ep766 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

theorem EMRow49.d12 : Enclosure.Real.IsNear (hardyZApproximantEM 1 36 qz12) Bool.true ep491 ep492 ep493 ep494 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantEM 1 36 qz12) ep495 Bool.true ep491 ep492 ep493 ep494 (@Eq.refl Real ep495) (@ep496 Bool.true ep491 ep492 ep493 ep494 (BSN.re_exp_mul (@HSub.hSub Real Real Real qz400 (Complex.im (@HSub.hSub Complex Complex Complex qz75 qz76 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz77 (@Nat.cast Complex Complex.instNatCast j))))) qz78) (zetaApproximant qz5 1 36)) (@ep498 ep499 ep500 ep501 ep502 ep503 ep504 ep494 ep505 ep491 ep492 ep493 ep494 (@ep506 103973650432 551341890180636259841777 750175054713340783755264 ep507 ep508 ep497 ep499 ep500 ep501 (@ep509 207947300864 1048575 1048576 38699733 103973650432 (ep635 rfl rfl) rfl) ep767 rfl) (@ep768 103973650432 66812495282705021757049 ep636 ep637 ep638 ep502 ep503 ep504 ep494 (@ep769 207947300864 43 131072 38699733 103973650432 (ep772 rfl rfl) rfl) ep773 rfl) rfl rfl))

noncomputable abbrev qz736 := (@HAdd.hAdd Complex Complex Complex (@instHAdd Complex Complex.instAdd) (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (2 : Complex)) (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul) Complex.I ↑(Enclosure.sfrac Bool.false 142522 1000)))

noncomputable abbrev qz681 := qz736

noncomputable abbrev qz451 := qz681

noncomputable abbrev qz141 := (BSN.headSumC qz451 9)

noncomputable abbrev qz142 := qz451

noncomputable abbrev qz682 := (@Neg.neg Complex Complex.instNeg qz736)

noncomputable abbrev qz452 := qz682

noncomputable abbrev qz143 := qz452

noncomputable abbrev qz683 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 8) qz143)

noncomputable def ep774 := @Enclosure.Complex.IsNear.of_eq qz141 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz142 8) qz683) Bool.false 691151233701 1099511627776 266926143968849 109024274475384832 Bool.false 75251180895 137438953472 133438164390545 54512137237692416

noncomputable def ep775 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz142 8) qz683 Bool.false 499909486389 1099511627776 238963376666609 109024274475384832 Bool.false 940449462003 1099511627776 238874190894529 109024274475384832 Bool.false

noncomputable abbrev qz684 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 7) qz143)

noncomputable def ep776 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz142 8) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz142 7) qz684) Bool.false 499909486389 1099511627776 238963376666609 109024274475384832 Bool.false 940449462003 1099511627776 238874190894529 109024274475384832

noncomputable def ep777 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz142 7) qz684 Bool.false 58351473091 274877906944 104509272746351 54512137237692416 Bool.false 1259322252553 1099511627776 208916257412113 109024274475384832 Bool.false

noncomputable abbrev qz685 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 6) qz143)

noncomputable def ep778 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz142 7) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz142 6) qz685) Bool.false 58351473091 274877906944 104509272746351 54512137237692416 Bool.false 1259322252553 1099511627776 208916257412113 109024274475384832

noncomputable def ep779 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz142 6) qz685 Bool.false 256916369921 549755813888 44181004346387 27256068618846208 Bool.false 908825722039 1099511627776 176605498890571 109024274475384832 Bool.true

noncomputable abbrev qz686 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 5) qz143)

noncomputable def ep780 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz142 6) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz142 5) qz686) Bool.false 256916369921 549755813888 44181004346387 27256068618846208 Bool.false 908825722039 1099511627776 176605498890571 109024274475384832

noncomputable def ep781 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz142 5) qz686 Bool.false 1005077541869 1099511627776 141267928445927 109024274475384832 Bool.false 887306203109 1099511627776 141248733633867 109024274475384832 Bool.true

noncomputable abbrev qz687 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 4) qz143)

noncomputable def ep782 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz142 5) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz142 4) qz687) Bool.false 1005077541869 1099511627776 141267928445927 109024274475384832 Bool.false 887306203109 1099511627776 141248733633867 109024274475384832

noncomputable def ep783 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz142 4) qz687 Bool.false 1522803614351 1099511627776 101645081351601 109024274475384832 Bool.false 1072210693695 1099511627776 101688832196397 109024274475384832 Bool.true

noncomputable def ep784 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz142 4) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz142 3) (@HPow.hPow Complex Complex Complex qz6 qz8 qz143)) Bool.false 1522803614351 1099511627776 101645081351601 109024274475384832 Bool.false 1072210693695 1099511627776 101688832196397 109024274475384832

noncomputable def ep785 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz142 3) (@HPow.hPow Complex Complex Complex qz6 qz8 qz143) Bool.false 483356294273 549755813888 27957256651965 54512137237692416 Bool.false 383023048265 549755813888 27999599665675 54512137237692416 Bool.false

noncomputable def ep786 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz142 3) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz142 2) (@HPow.hPow Complex Complex Complex qz6 qz9 qz143)) Bool.false 483356294273 549755813888 27957256651965 54512137237692416 Bool.false 383023048265 549755813888 27999599665675 54512137237692416

noncomputable def ep787 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz142 2) (@HPow.hPow Complex Complex Complex qz6 qz9 qz143) Bool.false 1 1 0 1 Bool.false 0 1 0 1 Bool.true

noncomputable def ep788 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz142 2) (Complex.mk (Enclosure.sfrac Bool.false 1 1) qz10) Bool.false 1 1 0 1 Bool.false 0 1 0 1 (BSN.head_sum_c_two qz142)

noncomputable abbrev qz737 := (Enclosure.sfrac Bool.false 142522 1000)

noncomputable abbrev qz688 := qz737

noncomputable abbrev qz453 := qz688

noncomputable abbrev qz144 := (@HMul.hMul Real Real Real qz267 qz453 (Real.log qz278))

noncomputable abbrev qz145 := qz453

noncomputable abbrev qz454 := (@Eq.refl Real qz688)

noncomputable abbrev qz146 := qz454

noncomputable def ep789 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz9 qz143) (Complex.mk (@HMul.hMul Real Real Real qz0 qz280 (Real.cos qz144)) (@HMul.hMul Real Real Real qz0 qz280 (@Neg.neg Real Real.instNeg (Real.sin qz144)))) Bool.true 66399519615 549755813888 27957256651965 54512137237692416 Bool.false 383023048265 549755813888 27999599665675 54512137237692416 (BSN.cpow_neg_s_mk qz145 142522 1000 2 qz146 rfl)

noncomputable def ep790 := nat_lit 2918700277491429577059148755906639021656608253938817348602000659124018776082401

noncomputable def ep791 := nat_lit 6642666320942172054408356921846787878017842908613917309832757312981149386721

noncomputable def ep792 := nat_lit 8742815499832404387068629553876223489213789075999224211186336462746094029473761

noncomputable def ep793 := BSN.cos_dyadic_bound_f 3004642491 2147483648 3 2 1048576 397016 ep790 ep102 ep791 ep792 ep104 ep791 179106 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3004642491) qz15 0 2 ep790 ep102 ep791 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3004642491) qz16 0 2 ep792 ep104 ep791 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz147 := (Enclosure.Real.IsNear.const Bool.false 142522 1000)

noncomputable abbrev qz455 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 103587269) qz26)

noncomputable def ep794 := @Enclosure.Real.IsNear.cos_image qz144 qz455 Bool.false 103587269 1048576 755 1048576 Bool.true 179106 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz144 Bool.false 1618551093 16384000 71261 99157000 103587269 1048576 755 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz145 (Real.log qz278) 142522 1000 0 1 363408 524288 1 198314 1618551093 16384000 71261 99157000 qz147 qz284 rfl) rfl) (Enclosure.sfrac_false_div 103587269 1048576) (BSN.cos_reduce2 qz455 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 211432918858463191236608) qz27) 226375608064910080 72057594037927936 Bool.false 179106 1048576 15 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q2 103587269 1048576 226375608064910080 72057594037927936 15 211432918858463191236608 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 179106 1048576 211432918858463191236608 151115727451828646838272 3004642491 2147483648 397016 396628 (ep793 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep795 := nat_lit 5248346366427819501062941075094472808679480582762980093635734980572848877438945

noncomputable def ep796 := nat_lit 13734914261838954224219613094993010175691372637765287236258624294422158532380641

noncomputable def ep797 := BSN.sin_dyadic_bound_f 3004642491 2147483648 3 2 1048576 397016 ep795 ep95 ep791 ep796 ep98 ep791 1033166 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3004642491) qz20 0 2 ep795 ep95 ep791 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3004642491) qz21 0 2 ep796 ep98 ep791 rfl rfl rfl rfl) rfl rfl

noncomputable def ep798 := @Enclosure.Real.IsNear.sin_image qz144 qz455 Bool.false 103587269 1048576 755 1048576 Bool.true 1033166 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz144 Bool.false 1618551093 16384000 71261 99157000 103587269 1048576 755 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz145 (Real.log qz278) 142522 1000 0 1 363408 524288 1 198314 1618551093 16384000 71261 99157000 qz147 qz284 rfl) rfl) (Enclosure.sfrac_false_div 103587269 1048576) (BSN.sin_reduce2 qz455 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 211432918858463191236608) qz27) 226375608064910080 72057594037927936 Bool.false 1033166 1048576 15 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q2 103587269 1048576 226375608064910080 72057594037927936 15 211432918858463191236608 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1033166 1048576 211432918858463191236608 151115727451828646838272 3004642491 2147483648 397016 396628 (ep797 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep799 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz280 (Real.cos qz144)) (@HMul.hMul Real Real Real qz0 qz280 (@Neg.neg Real Real.instNeg (Real.sin qz144))) Bool.true 66399519615 549755813888 27957256651965 54512137237692416 Bool.false 383023048265 549755813888 27999599665675 54512137237692416 (@Enclosure.Real.IsNear.mulLit_ft qz280 (Real.cos qz144) 741455 1048576 1 1048576 89553 524288 75387823 103973650432 66399519615 549755813888 27957256651965 54512137237692416 qz285 (@Enclosure.Real.IsNear.recentre' (Real.cos qz144) Bool.true 179106 1048576 150775646 207947300864 89553 524288 75387823 103973650432 (ep794 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz280 (@Neg.neg Real Real.instNeg (Real.sin qz144)) 741455 1048576 1 1048576 516583 524288 75387823 103973650432 383023048265 549755813888 27999599665675 54512137237692416 qz285 (@Enclosure.Real.IsNear.neg (Real.sin qz144) Bool.true 516583 524288 75387823 103973650432 (@Enclosure.Real.IsNear.recentre' (Real.sin qz144) Bool.true 1033166 1048576 150775646 207947300864 516583 524288 75387823 103973650432 (ep798 rfl rfl) rfl)) rfl)

noncomputable def ep800 := @ep787 66399519615 549755813888 27957256651965 54512137237692416 Bool.false 383023048265 549755813888 27999599665675 54512137237692416 Bool.false 483356294273 483356294273 549755813888 27957256651965 54512137237692416 Bool.false 383023048265 383023048265 549755813888 27999599665675 54512137237692416 (ep788 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 1) qz10 Bool.false 1 1 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 1) qz22)) (ep789 ep799) rfl rfl

noncomputable abbrev qz148 := (@HMul.hMul Real Real Real qz267 qz453 qz554)

noncomputable def ep801 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz8 qz143) (Complex.mk (@HMul.hMul Real Real Real qz0 qz286 (Real.cos qz148)) (@HMul.hMul Real Real Real qz0 qz286 (@Neg.neg Real Real.instNeg (Real.sin qz148)))) Bool.false 556091025805 1099511627776 45730568047671 109024274475384832 Bool.false 306164597165 1099511627776 45689632865047 109024274475384832 (BSN.cpow_neg_s_mk qz145 142522 1000 3 qz146 rfl)

noncomputable def ep802 := nat_lit 1777088393721487645262496148804272984446408548933317958797736043466836118508065

noncomputable def ep803 := nat_lit 762856095536686536752092846722041588959060557837977968212589092758584201761

noncomputable def ep804 := nat_lit 4653044026068265387961319858449831653834660101541237927759821636262961650242081

noncomputable def ep805 := BSN.sin_dyadic_bound_f 2292478797 2147483648 3 2 1048576 397016 ep802 ep95 ep803 ep804 ep98 ep803 918559 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2292478797) qz20 0 2 ep802 ep95 ep803 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2292478797) qz21 0 2 ep804 ep98 ep803 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz456 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 2565347) (@Nat.cast Real Real.instNatCast 16384))

noncomputable abbrev qz689 := (@Nat.cast Real Real.instNatCast 2361183241434822606848)

noncomputable def ep806 := @Enclosure.Real.IsNear.cos_image qz148 qz456 Bool.false 2565347 16384 755 1048576 Bool.false 918559 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz148 Bool.false 41045552129 262144000 71261 99157000 2565347 16384 755 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz145 qz554 142522 1000 0 1 575989 524288 1 198314 41045552129 262144000 71261 99157000 qz147 qz290 rfl) rfl) (Enclosure.sfrac_false_div 2565347 16384) (BSN.cos_reduce3 qz456 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 2520607093819445346304) qz689) 226375608064910080 72057594037927936 Bool.false 918559 1048576 24 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q3 2565347 16384 226375608064910080 72057594037927936 24 2520607093819445346304 2361183241434822606848 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 918559 1048576 2520607093819445346304 2361183241434822606848 2292478797 2147483648 397016 396628 (ep805 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep807 := nat_lit 987610376998842774717721012823139232065319887433104633984614508189468325483041

noncomputable def ep808 := nat_lit 2961305418805454951079658852775973613018041541183637946017418346382887808045601

noncomputable def ep809 := BSN.cos_dyadic_bound_f 2292478797 2147483648 3 2 1048576 397016 ep807 ep102 ep803 ep808 ep104 ep803 505727 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2292478797) qz15 0 2 ep807 ep102 ep803 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2292478797) qz16 0 2 ep808 ep104 ep803 rfl rfl rfl rfl) rfl rfl

noncomputable def ep810 := @Enclosure.Real.IsNear.sin_image qz148 qz456 Bool.false 2565347 16384 755 1048576 Bool.true 505727 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz148 Bool.false 41045552129 262144000 71261 99157000 2565347 16384 755 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz145 qz554 142522 1000 0 1 575989 524288 1 198314 41045552129 262144000 71261 99157000 qz147 qz290 rfl) rfl) (Enclosure.sfrac_false_div 2565347 16384) (BSN.sin_reduce3 qz456 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 2520607093819445346304) qz689) 226375608064910080 72057594037927936 Bool.false 505727 1048576 24 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q3 2565347 16384 226375608064910080 72057594037927936 24 2520607093819445346304 2361183241434822606848 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 505727 1048576 2520607093819445346304 2361183241434822606848 2292478797 2147483648 397016 396628 (ep809 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep811 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz286 (Real.cos qz148)) (@HMul.hMul Real Real Real qz0 qz286 (@Neg.neg Real Real.instNeg (Real.sin qz148))) Bool.false 556091025805 1099511627776 45730568047671 109024274475384832 Bool.false 306164597165 1099511627776 45689632865047 109024274475384832 (@Enclosure.Real.IsNear.mulLit_ff qz286 (Real.cos qz148) 605395 1048576 1 1048576 918559 1048576 75387823 103973650432 556091025805 1099511627776 45730568047671 109024274475384832 qz292 (@Enclosure.Real.IsNear.recentre' (Real.cos qz148) Bool.false 918559 1048576 150775646 207947300864 918559 1048576 75387823 103973650432 (ep806 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz286 (@Neg.neg Real Real.instNeg (Real.sin qz148)) 605395 1048576 1 1048576 505727 1048576 75387823 103973650432 306164597165 1099511627776 45689632865047 109024274475384832 qz292 (@Enclosure.Real.IsNear.neg (Real.sin qz148) Bool.true 505727 1048576 75387823 103973650432 (@Enclosure.Real.IsNear.recentre' (Real.sin qz148) Bool.true 505727 1048576 150775646 207947300864 505727 1048576 75387823 103973650432 (ep810 rfl rfl) rfl)) rfl)

noncomputable def ep812 := @ep785 556091025805 1099511627776 45730568047671 109024274475384832 Bool.false 306164597165 1099511627776 45689632865047 109024274475384832 Bool.false 837170140399122081906688 1522803614351 1099511627776 101645081351601 109024274475384832 Bool.false 589454062571711795036160 1072210693695 1099511627776 101688832196397 109024274475384832 (ep786 (BSN.head_sum_c_succ qz142 2 3 rfl rfl) (ep800 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep801 ep811) rfl rfl

noncomputable abbrev qz149 := (@HMul.hMul Real Real Real qz267 qz453 qz555)

noncomputable def ep813 := @Enclosure.Complex.IsNear.of_eq qz687 (Complex.mk (@HMul.hMul Real Real Real qz0 qz293 (Real.cos qz149)) (@HMul.hMul Real Real Real qz0 qz293 (@Neg.neg Real Real.instNeg (Real.sin qz149)))) Bool.true 258863036241 549755813888 19811423547163 54512137237692416 Bool.true 92452245293 549755813888 19779950718735 54512137237692416 (BSN.cpow_neg_s_mk qz145 142522 1000 4 qz146 rfl)

noncomputable def ep814 := nat_lit 3110368828121075664403764917915705345289984912183211611828358688139815484630625

noncomputable def ep815 := nat_lit 2335440743947012768776285479940714977619400907525412281152678389011250390625

noncomputable def ep816 := nat_lit 8142422883874522052765175084716467127700481454248608315857168418212546149590625

noncomputable def ep817 := BSN.sin_dyadic_bound_f 2636611285 2147483648 3 2 1048576 397016 ep814 ep95 ep815 ep816 ep98 ep815 987486 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2636611285) qz20 0 2 ep814 ep95 ep815 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2636611285) qz21 0 2 ep816 ep98 ep815 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz457 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 25896853) qz585)

noncomputable def ep818 := @Enclosure.Real.IsNear.cos_image qz149 qz457 Bool.false 25896853 131072 755 1048576 Bool.true 987486 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz149 Bool.false 51793706237 262144000 71261 99157000 25896853 131072 755 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz145 qz555 142522 1000 0 1 726817 524288 1 198314 51793706237 262144000 71261 99157000 qz147 qz297 rfl) rfl) (Enclosure.sfrac_false_div 25896853 131072) (BSN.cos_reduce1 qz457 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 23191878132305615650816) qz332) 226375608064910080 72057594037927936 Bool.false 987486 1048576 31 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q1 25896853 131072 226375608064910080 72057594037927936 31 23191878132305615650816 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 987486 1048576 23191878132305615650816 18889465931478580854784 2636611285 2147483648 397016 396628 (ep817 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep819 := nat_lit 1729020655953462930343769970166476620706711351616239967585156017139458047190625

noncomputable def ep820 := nat_lit 5182391086372494765493757339539548432164895253033669078193162694640351640790625

noncomputable def ep821 := BSN.cos_dyadic_bound_f 2636611285 2147483648 3 2 1048576 397016 ep819 ep102 ep815 ep820 ep104 ep815 352678 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2636611285) qz15 0 2 ep819 ep102 ep815 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2636611285) qz16 0 2 ep820 ep104 ep815 rfl rfl rfl rfl) rfl rfl

noncomputable def ep822 := @Enclosure.Real.IsNear.sin_image qz149 qz457 Bool.false 25896853 131072 755 1048576 Bool.false 352678 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz149 Bool.false 51793706237 262144000 71261 99157000 25896853 131072 755 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz145 qz555 142522 1000 0 1 726817 524288 1 198314 51793706237 262144000 71261 99157000 qz147 qz297 rfl) rfl) (Enclosure.sfrac_false_div 25896853 131072) (BSN.sin_reduce1 qz457 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 23191878132305615650816) qz332) 226375608064910080 72057594037927936 Bool.false 352678 1048576 31 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q1 25896853 131072 226375608064910080 72057594037927936 31 23191878132305615650816 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 352678 1048576 23191878132305615650816 18889465931478580854784 2636611285 2147483648 397016 396628 (ep821 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep823 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz293 (Real.cos qz149)) (@HMul.hMul Real Real Real qz0 qz293 (@Neg.neg Real Real.instNeg (Real.sin qz149))) Bool.true 258863036241 549755813888 19811423547163 54512137237692416 Bool.true 92452245293 549755813888 19779950718735 54512137237692416 (@Enclosure.Real.IsNear.mulLit_ft qz293 (Real.cos qz149) 524287 1048576 1 1048576 493743 524288 75387823 103973650432 258863036241 549755813888 19811423547163 54512137237692416 qz298 (@Enclosure.Real.IsNear.recentre' (Real.cos qz149) Bool.true 987486 1048576 150775646 207947300864 493743 524288 75387823 103973650432 (ep818 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz293 (@Neg.neg Real Real.instNeg (Real.sin qz149)) 524287 1048576 1 1048576 176339 524288 75387823 103973650432 92452245293 549755813888 19779950718735 54512137237692416 qz298 (@Enclosure.Real.IsNear.neg (Real.sin qz149) Bool.false 176339 524288 75387823 103973650432 (@Enclosure.Real.IsNear.recentre' (Real.sin qz149) Bool.false 352678 1048576 150775646 207947300864 176339 524288 75387823 103973650432 (ep822 rfl rfl) rfl)) rfl)

noncomputable def ep824 := @ep783 258863036241 549755813888 19811423547163 54512137237692416 Bool.true 92452245293 549755813888 19779950718735 54512137237692416 Bool.false 552547222050742491676672 1005077541869 1099511627776 141267928445927 109024274475384832 Bool.false 487801743858059330977792 887306203109 1099511627776 141248733633867 109024274475384832 (ep784 (BSN.head_sum_c_succ qz142 3 4 rfl rfl) (ep812 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep813 ep823) rfl rfl

noncomputable abbrev qz150 := (@HMul.hMul Real Real Real qz267 qz453 qz556)

noncomputable def ep825 := @Enclosure.Complex.IsNear.of_eq qz686 (Complex.mk (@HMul.hMul Real Real Real qz0 qz299 (Real.cos qz150)) (@HMul.hMul Real Real Real qz0 qz299 (@Neg.neg Real Real.instNeg (Real.sin qz150)))) Bool.true 491244802027 1099511627776 35456088939621 109024274475384832 Bool.false 10759759465 549755813888 34528091071 106469018042368 (BSN.cpow_neg_s_mk qz145 142522 1000 5 qz146 rfl)

noncomputable def ep826 := BSN.cos_dyadic_bound_f 94013320 2147483648 1 0 1048576 397016 0 1 1 0 1 1 1047571 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 94013320) qz15 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 94013320) qz16 0 0 rfl) rfl rfl

noncomputable abbrev qz458 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 240522407) qz26)

noncomputable def ep827 := @Enclosure.Real.IsNear.cos_image qz150 qz458 Bool.false 240522407 1048576 755 1048576 Bool.true 1047571 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz150 Bool.false 1879081309 8192000 71261 99157000 240522407 1048576 755 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz145 qz556 142522 1000 0 1 843808 524288 1 198314 1879081309 8192000 71261 99157000 qz147 qz303 rfl) rfl) (Enclosure.sfrac_false_div 240522407 1048576) (BSN.cos_reduce2 qz458 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 6615599330964719796224) qz27) 226375608064910080 72057594037927936 Bool.false 1047571 1048576 36 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q2 240522407 1048576 226375608064910080 72057594037927936 36 6615599330964719796224 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1047571 1048576 6615599330964719796224 151115727451828646838272 94013320 2147483648 397016 396628 (ep826 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep828 := BSN.sin_dyadic_bound_f 94013320 2147483648 1 0 1048576 397016 0 1 1 0 1 1 45890 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 94013320) qz20 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 94013320) qz21 0 0 rfl) rfl rfl

noncomputable def ep829 := @Enclosure.Real.IsNear.sin_image qz150 qz458 Bool.false 240522407 1048576 755 1048576 Bool.true 45890 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz150 Bool.false 1879081309 8192000 71261 99157000 240522407 1048576 755 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz145 qz556 142522 1000 0 1 843808 524288 1 198314 1879081309 8192000 71261 99157000 qz147 qz303 rfl) rfl) (Enclosure.sfrac_false_div 240522407 1048576) (BSN.sin_reduce2 qz458 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 6615599330964719796224) qz27) 226375608064910080 72057594037927936 Bool.false 45890 1048576 36 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q2 240522407 1048576 226375608064910080 72057594037927936 36 6615599330964719796224 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 45890 1048576 6615599330964719796224 151115727451828646838272 94013320 2147483648 397016 396628 (ep828 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep830 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz299 (Real.cos qz150)) (@HMul.hMul Real Real Real qz0 qz299 (@Neg.neg Real Real.instNeg (Real.sin qz150))) Bool.true 491244802027 1099511627776 35456088939621 109024274475384832 Bool.false 10759759465 549755813888 34528091071 106469018042368 (@Enclosure.Real.IsNear.mulLit_ft qz299 (Real.cos qz150) 468937 1048576 1 1048576 1047571 1048576 75387823 103973650432 491244802027 1099511627776 35456088939621 109024274475384832 qz304 (@Enclosure.Real.IsNear.recentre' (Real.cos qz150) Bool.true 1047571 1048576 150775646 207947300864 1047571 1048576 75387823 103973650432 (ep827 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz299 (@Neg.neg Real Real.instNeg (Real.sin qz150)) 468937 1048576 1 1048576 22945 524288 75387823 103973650432 10759759465 549755813888 34528091071 106469018042368 qz304 (@Enclosure.Real.IsNear.neg (Real.sin qz150) Bool.true 22945 524288 75387823 103973650432 (@Enclosure.Real.IsNear.recentre' (Real.sin qz150) Bool.true 45890 1048576 150775646 207947300864 22945 524288 75387823 103973650432 (ep829 rfl rfl) rfl)) rfl)

noncomputable def ep831 := @ep781 491244802027 1099511627776 35456088939621 109024274475384832 Bool.false 10759759465 549755813888 34528091071 106469018042368 Bool.false 564965072188279349051392 256916369921 549755813888 44181004346387 27256068618846208 Bool.false 499632224501899703877632 908825722039 1099511627776 176605498890571 109024274475384832 (ep782 (BSN.head_sum_c_succ qz142 4 5 rfl rfl) (ep824 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep825 ep830) rfl rfl

noncomputable abbrev qz151 := (@HMul.hMul Real Real Real qz267 qz453 qz557)

noncomputable def ep832 := @Enclosure.Complex.IsNear.of_eq qz685 (Complex.mk (@HMul.hMul Real Real Real qz0 qz305 (Real.cos qz151)) (@HMul.hMul Real Real Real qz0 qz305 (@Neg.neg Real Real.instNeg (Real.sin qz151)))) Bool.true 140213423739 549755813888 16147264053577 54512137237692416 Bool.false 175248265257 549755813888 16155379260771 54512137237692416 (BSN.cpow_neg_s_mk qz145 142522 1000 6 qz146 rfl)

noncomputable def ep833 := @Enclosure.Real.IsNear.mulLit_ff qz145 qz557 142522 1000 0 1 4034681531866359 2251799813685248 250000000099157 49578500000000000000 287515440642328608699 1125899906842624000 17815250007066026977 24789250000000000000000 qz147 (BSN.isNear_log_sfrac 6 1 4034681531866359 2251799813685248 250000000099157 49578500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz558) Bool.false 33845361775666394038272 18889465931478580854784 1000000000396628 198314000000000000000 4034681531866359 2251799813685248 250000000099157 49578500000000000000 (BSN.log_rat_reduce_isNear 6 1 2 12 8 212580 524288 24973259072661432 36028797018963968 198314 1000000000000000 rfl rfl rfl rfl (ep111 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep834 := nat_lit 489953985567437721098584822212125798765154274987913250584930284174529093837056

noncomputable def ep835 := nat_lit 187897038158016306098115758916563204721713108103225421696704522610232402176

noncomputable def ep836 := nat_lit 1469486162625997130683558235118544269886019398747533300911397443478366816706816

noncomputable def ep837 := BSN.cos_dyadic_bound_f 1924154726 2147483648 3 2 1048576 397016 ep834 ep102 ep835 ep836 ep104 ep835 655082 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1924154726) qz15 0 2 ep834 ep102 ep835 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1924154726) qz16 0 2 ep836 ep104 ep835 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz459 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 66942405) qz24)

noncomputable def ep838 := @Enclosure.Real.IsNear.cos_image qz151 qz459 Bool.false 66942405 262144 377 524288 Bool.true 655082 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz151 Bool.false 287515440642328608699 1125899906842624000 17815250007066026977 24789250000000000000000 66942405 262144 377 524288 (ep833 rfl) rfl) (Enclosure.sfrac_false_div 66942405 262144) (BSN.cos_reduce2 qz459 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 33850087933132847185920) qz291) 226375608064910080 72057594037927936 Bool.false 655082 1048576 40 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q2 66942405 262144 226375608064910080 72057594037927936 40 33850087933132847185920 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 655082 1048576 33850087933132847185920 37778931862957161709568 1924154726 2147483648 397016 396628 (ep837 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep839 := nat_lit 881766856390861484932574187374693187213500324491761270715517147896064182984960

noncomputable def ep840 := nat_lit 2309085171533333767470678303324045816561046647684350486905512151453084864880896

noncomputable def ep841 := BSN.sin_dyadic_bound_f 1924154726 2147483648 3 2 1048576 397016 ep839 ep95 ep835 ep840 ep98 ep835 818766 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1924154726) qz20 0 2 ep839 ep95 ep835 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1924154726) qz21 0 2 ep840 ep98 ep835 rfl rfl rfl rfl) rfl rfl

noncomputable def ep842 := @Enclosure.Real.IsNear.sin_image qz151 qz459 Bool.false 66942405 262144 377 524288 Bool.true 818766 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz151 Bool.false 287515440642328608699 1125899906842624000 17815250007066026977 24789250000000000000000 66942405 262144 377 524288 (ep833 rfl) rfl) (Enclosure.sfrac_false_div 66942405 262144) (BSN.sin_reduce2 qz459 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 33850087933132847185920) qz291) 226375608064910080 72057594037927936 Bool.false 818766 1048576 40 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q2 66942405 262144 226375608064910080 72057594037927936 40 33850087933132847185920 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 818766 1048576 33850087933132847185920 37778931862957161709568 1924154726 2147483648 397016 396628 (ep841 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep843 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz305 (Real.cos qz151)) (@HMul.hMul Real Real Real qz0 qz305 (@Neg.neg Real Real.instNeg (Real.sin qz151))) Bool.true 140213423739 549755813888 16147264053577 54512137237692416 Bool.false 175248265257 549755813888 16155379260771 54512137237692416 (@Enclosure.Real.IsNear.mulLit_ft qz305 (Real.cos qz151) 428079 1048576 1 1048576 327541 524288 37644333 51986825216 140213423739 549755813888 16147264053577 54512137237692416 qz309 (@Enclosure.Real.IsNear.recentre' (Real.cos qz151) Bool.true 655082 1048576 75288666 103973650432 327541 524288 37644333 51986825216 (ep838 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz305 (@Neg.neg Real Real.instNeg (Real.sin qz151)) 428079 1048576 1 1048576 409383 524288 37644333 51986825216 175248265257 549755813888 16155379260771 54512137237692416 qz309 (@Enclosure.Real.IsNear.neg (Real.sin qz151) Bool.true 409383 524288 37644333 51986825216 (@Enclosure.Real.IsNear.recentre' (Real.sin qz151) Bool.true 818766 1048576 75288666 103973650432 409383 524288 37644333 51986825216 (ep842 rfl rfl) rfl)) rfl)

noncomputable def ep844 := @ep779 140213423739 549755813888 16147264053577 54512137237692416 Bool.false 175248265257 549755813888 16155379260771 54512137237692416 Bool.false 64158123161412872175616 58351473091 274877906944 104509272746351 54512137237692416 Bool.false 692319729899544000856064 1259322252553 1099511627776 208916257412113 109024274475384832 (ep780 (BSN.head_sum_c_succ qz142 5 6 rfl rfl) (ep831 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep832 ep843) rfl rfl

noncomputable abbrev qz152 := (@HMul.hMul Real Real Real qz267 qz453 qz559)

noncomputable def ep845 := @Enclosure.Complex.IsNear.of_eq qz684 (Complex.mk (@HMul.hMul Real Real Real qz0 qz310 (Real.cos qz152)) (@HMul.hMul Real Real Real qz0 qz310 (@Neg.neg Real Real.instNeg (Real.sin qz152)))) Bool.false 266503594025 1099511627776 29944831173907 109024274475384832 Bool.true 159436395275 549755813888 1872370842651 6814017154711552 (BSN.cpow_neg_s_mk qz145 142522 1000 7 qz146 rfl)

noncomputable def ep846 := @Enclosure.Real.IsNear.mulLit_ff qz145 qz559 142522 1000 0 1 4381796493761783 2251799813685248 250000000099157 49578500000000000000 312251199941958418363 1125899906842624000 17815250007066026977 24789250000000000000000 qz147 (BSN.isNear_log_sfrac 7 1 4381796493761783 2251799813685248 250000000099157 49578500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz560) Bool.false 36757173121942042968064 18889465931478580854784 1000000000396628 198314000000000000000 4381796493761783 2251799813685248 250000000099157 49578500000000000000 (BSN.log_rat_reduce_isNear 7 1 2 14 8 293399 524288 24973259072661432 36028797018963968 198314 1000000000000000 rfl rfl rfl rfl (ep122 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep847 := nat_lit 444819428191104272417398918262865290956714820738385999853998690914469111462721

noncomputable def ep848 := nat_lit 154884341971958287072811758743061808933357993146706674994902705763498130241

noncomputable def ep849 := nat_lit 1334148515889368900678051131271109749252277746228864586212006267331880338127681

noncomputable def ep850 := BSN.cos_dyadic_bound_f 1878239369 2147483648 3 2 1048576 397016 ep847 ep102 ep848 ep849 ep104 ep848 672437 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1878239369) qz15 0 2 ep847 ep102 ep848 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1878239369) qz16 0 2 ep849 ep104 ep848 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz460 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 290806591) qz26)

noncomputable def ep851 := @Enclosure.Real.IsNear.cos_image qz152 qz460 Bool.false 290806591 1048576 755 1048576 Bool.false 672437 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz152 Bool.false 312251199941958418363 1125899906842624000 17815250007066026977 24789250000000000000000 290806591 1048576 755 1048576 (ep846 rfl) rfl) (Enclosure.sfrac_false_div 290806591 1048576) (BSN.cos_reduce0 qz460 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 132169345663772783542272) qz27) 226375608064910080 72057594037927936 Bool.false 672437 1048576 44 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q0 290806591 1048576 226375608064910080 72057594037927936 44 132169345663772783542272 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 672437 1048576 132169345663772783542272 151115727451828646838272 1878239369 2147483648 397016 396628 (ep850 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep852 := nat_lit 800551063270410123721659803466163074274939990934577434397201721481433602128705

noncomputable def ep853 := nat_lit 2096430591059310010615753028135319284934188825220703374518869904261089960983361

noncomputable def ep854 := BSN.sin_dyadic_bound_f 1878239369 2147483648 3 2 1048576 397016 ep852 ep95 ep848 ep853 ep98 ep848 804574 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1878239369) qz20 0 2 ep852 ep95 ep848 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1878239369) qz21 0 2 ep853 ep98 ep848 rfl rfl rfl rfl) rfl rfl

noncomputable def ep855 := @Enclosure.Real.IsNear.sin_image qz152 qz460 Bool.false 290806591 1048576 755 1048576 Bool.false 804574 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz152 Bool.false 312251199941958418363 1125899906842624000 17815250007066026977 24789250000000000000000 290806591 1048576 755 1048576 (ep846 rfl) rfl) (Enclosure.sfrac_false_div 290806591 1048576) (BSN.sin_reduce0 qz460 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 132169345663772783542272) qz27) 226375608064910080 72057594037927936 Bool.false 804574 1048576 44 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q0 290806591 1048576 226375608064910080 72057594037927936 44 132169345663772783542272 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 804574 1048576 132169345663772783542272 151115727451828646838272 1878239369 2147483648 397016 396628 (ep854 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep856 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz310 (Real.cos qz152)) (@HMul.hMul Real Real Real qz0 qz310 (@Neg.neg Real Real.instNeg (Real.sin qz152))) Bool.false 266503594025 1099511627776 29944831173907 109024274475384832 Bool.true 159436395275 549755813888 1872370842651 6814017154711552 (@Enclosure.Real.IsNear.mulLit_ff qz310 (Real.cos qz152) 396325 1048576 1 1048576 672437 1048576 75387823 103973650432 266503594025 1099511627776 29944831173907 109024274475384832 qz314 (@Enclosure.Real.IsNear.recentre' (Real.cos qz152) Bool.false 672437 1048576 150775646 207947300864 672437 1048576 75387823 103973650432 (ep851 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz310 (@Neg.neg Real Real.instNeg (Real.sin qz152)) 396325 1048576 1 1048576 402287 524288 75387823 103973650432 159436395275 549755813888 1872370842651 6814017154711552 qz314 (@Enclosure.Real.IsNear.neg (Real.sin qz152) Bool.false 402287 524288 75387823 103973650432 (@Enclosure.Real.IsNear.recentre' (Real.sin qz152) Bool.false 804574 1048576 150775646 207947300864 402287 524288 75387823 103973650432 (ep855 rfl rfl) rfl)) rfl)

noncomputable def ep857 := @ep777 266503594025 1099511627776 29944831173907 109024274475384832 Bool.true 159436395275 549755813888 1872370842651 6814017154711552 Bool.false 137414073280058376585216 499909486389 1099511627776 238963376666609 109024274475384832 Bool.false 517017559403990995697664 940449462003 1099511627776 238874190894529 109024274475384832 (ep778 (BSN.head_sum_c_succ qz142 6 7 rfl rfl) (ep844 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep845 ep856) rfl rfl

noncomputable abbrev qz153 := (@HMul.hMul Real Real Real qz267 qz453 qz561)

noncomputable def ep858 := @Enclosure.Complex.IsNear.of_eq qz683 (Complex.mk (@HMul.hMul Real Real Real qz0 qz315 (Real.cos qz153)) (@HMul.hMul Real Real Real qz0 qz315 (@Neg.neg Real Real.instNeg (Real.sin qz153)))) Bool.false 11952609207 68719476736 873836478195 3407008577355776 Bool.true 338440014843 1099511627776 28002137886561 109024274475384832 (BSN.cpow_neg_s_mk qz145 142522 1000 8 qz146 rfl)

noncomputable def ep859 := @Enclosure.Real.IsNear.mulLit_ff qz145 qz561 142522 1000 0 1 9364972152248037 4503599627370496 500000000297471 99157000000000000000 667357280541347364657 2251799813685248000 35630500021198080931 49578500000000000000000 qz147 (BSN.isNear_log_sfrac 8 1 9364972152248037 4503599627370496 500000000297471 99157000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz562) Bool.false 39279540158062550581248 18889465931478580854784 1000000000594942 198314000000000000000 9364972152248037 4503599627370496 500000000297471 99157000000000000000 (BSN.log_rat_reduce_isNear 8 1 3 16 16 0 524288 24973259072661432 36028797018963968 198314 1000000000000000 rfl rfl rfl rfl (ep133 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep860 := nat_lit 947280167668717419463008979183900240096777120366783498938419120291305375798401

noncomputable def ep861 := nat_lit 701868254496892736086264278312777968095264104835446720219549518093838062721

noncomputable def ep862 := nat_lit 2840436766497158472916854408995075164354140832890679603374818261837728451269761

noncomputable def ep863 := BSN.cos_dyadic_bound_f 2268725487 2147483648 3 2 1048576 397016 ep860 ep102 ep861 ep862 ep104 ep861 515856 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2268725487) qz15 0 2 ep860 ep102 ep861 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2268725487) qz16 0 2 ep862 ep104 ep861 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz461 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 155381225) qz17)

noncomputable def ep864 := @Enclosure.Real.IsNear.cos_image qz153 qz461 Bool.false 155381225 524288 377 524288 Bool.false 515856 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz153 Bool.false 667357280541347364657 2251799813685248000 35630500021198080931 49578500000000000000000 155381225 524288 377 524288 (ep859 rfl) rfl) (Enclosure.sfrac_false_div 155381225 524288) (BSN.cos_reduce0 qz461 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 79823681718390022471680) qz19) 226375608064910080 72057594037927936 Bool.false 515856 1048576 47 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q0 155381225 524288 226375608064910080 72057594037927936 47 79823681718390022471680 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 515856 1048576 79823681718390022471680 75557863725914323419136 2268725487 2147483648 397016 396628 (ep863 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep865 := nat_lit 1704542807200093840844547151108370209799722605376341940712978776909874605986945

noncomputable def ep866 := nat_lit 4463142422635822233020150491690367956574738300768304835748874668877519658816641

noncomputable def ep867 := BSN.sin_dyadic_bound_f 2268725487 2147483648 3 2 1048576 397016 ep865 ep95 ep861 ep866 ep98 ep861 912909 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2268725487) qz20 0 2 ep865 ep95 ep861 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2268725487) qz21 0 2 ep866 ep98 ep861 rfl rfl rfl rfl) rfl rfl

noncomputable def ep868 := @Enclosure.Real.IsNear.sin_image qz153 qz461 Bool.false 155381225 524288 377 524288 Bool.false 912909 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz153 Bool.false 667357280541347364657 2251799813685248000 35630500021198080931 49578500000000000000000 155381225 524288 377 524288 (ep859 rfl) rfl) (Enclosure.sfrac_false_div 155381225 524288) (BSN.sin_reduce0 qz461 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 79823681718390022471680) qz19) 226375608064910080 72057594037927936 Bool.false 912909 1048576 47 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q0 155381225 524288 226375608064910080 72057594037927936 47 79823681718390022471680 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 912909 1048576 79823681718390022471680 75557863725914323419136 2268725487 2147483648 397016 396628 (ep867 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep869 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz315 (Real.cos qz153)) (@HMul.hMul Real Real Real qz0 qz315 (@Neg.neg Real Real.instNeg (Real.sin qz153))) Bool.false 11952609207 68719476736 873836478195 3407008577355776 Bool.true 338440014843 1099511627776 28002137886561 109024274475384832 (@Enclosure.Real.IsNear.mulLit_ff qz315 (Real.cos qz153) 370727 1048576 1 1048576 32241 65536 37644333 51986825216 11952609207 68719476736 873836478195 3407008577355776 qz319 (@Enclosure.Real.IsNear.recentre' (Real.cos qz153) Bool.false 515856 1048576 75288666 103973650432 32241 65536 37644333 51986825216 (ep864 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz315 (@Neg.neg Real Real.instNeg (Real.sin qz153)) 370727 1048576 1 1048576 912909 1048576 37644333 51986825216 338440014843 1099511627776 28002137886561 109024274475384832 qz319 (@Enclosure.Real.IsNear.neg (Real.sin qz153) Bool.false 912909 1048576 37644333 51986825216 (@Enclosure.Real.IsNear.recentre' (Real.sin qz153) Bool.false 912909 1048576 75288666 103973650432 912909 1048576 37644333 51986825216 (ep868 rfl rfl) rfl)) rfl)

noncomputable def ep870 := @ep775 11952609207 68719476736 873836478195 3407008577355776 Bool.true 338440014843 1099511627776 28002137886561 109024274475384832 Bool.false 47495551125373568679936 691151233701 1099511627776 266926143968849 109024274475384832 Bool.false 661916387183421460316160 75251180895 137438953472 133438164390545 54512137237692416 (ep776 (BSN.head_sum_c_succ qz142 7 8 rfl rfl) (ep857 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep858 ep869) rfl rfl

theorem EMRow49.d13 : Enclosure.Complex.IsNear qz141 Bool.false 691151233701 1099511627776 266926143968849 109024274475384832 Bool.false 75251180895 137438953472 133438164390545 54512137237692416 := ep774 (BSN.head_sum_c_succ qz142 8 9 rfl rfl) (ep870 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable abbrev qz154 := (BSN.headSumC qz451 17)

noncomputable abbrev qz690 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 16) qz143)

noncomputable def ep871 := @Enclosure.Complex.IsNear.of_eq qz154 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz142 16) qz690) Bool.false 739981744471 1099511627776 448627211849529 109024274475384832 Bool.false 58066758319 549755813888 224347059166375 54512137237692416

noncomputable def ep872 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz142 16) qz690 Bool.false 527248505683 1099511627776 428784278885005 109024274475384832 Bool.true 57940707511 1099511627776 428865808348487 109024274475384832 Bool.false

noncomputable abbrev qz691 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 15) qz143)

noncomputable def ep873 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz142 16) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz142 15) qz691) Bool.false 527248505683 1099511627776 428784278885005 109024274475384832 Bool.true 57940707511 1099511627776 428865808348487 109024274475384832

noncomputable def ep874 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz142 15) qz691 Bool.false 390851269673 549755813888 102070109224497 27256068618846208 Bool.false 8493521491 137438953472 204204526225559 54512137237692416 Bool.true

noncomputable abbrev qz692 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 14) qz143)

noncomputable def ep875 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz142 15) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz142 14) qz692) Bool.false 390851269673 549755813888 102070109224497 27256068618846208 Bool.false 8493521491 137438953472 204204526225559 54512137237692416

noncomputable def ep876 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz142 14) qz692 Bool.false 591682371981 1099511627776 387086217929541 109024274475384832 Bool.true 156202790407 1099511627776 387202757151641 109024274475384832 Bool.false

noncomputable abbrev qz693 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 13) qz143)

noncomputable def ep877 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz142 14) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz142 13) qz693) Bool.false 591682371981 1099511627776 387086217929541 109024274475384832 Bool.true 156202790407 1099511627776 387202757151641 109024274475384832

noncomputable def ep878 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz142 13) qz693 Bool.false 463427102397 1099511627776 365146737898501 109024274475384832 Bool.false 60232490857 549755813888 182606337709759 54512137237692416 Bool.false

noncomputable abbrev qz694 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 12) qz143)

noncomputable def ep879 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz142 13) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz142 12) qz694) Bool.false 463427102397 1099511627776 365146737898501 109024274475384832 Bool.false 60232490857 549755813888 182606337709759 54512137237692416

noncomputable def ep880 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz142 12) qz694 Bool.false 673801517397 1099511627776 342258080537047 109024274475384832 Bool.false 358132071719 1099511627776 342315077567159 109024274475384832 Bool.true

noncomputable abbrev qz695 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 11) qz143)

noncomputable def ep881 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz142 12) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz142 11) qz695) Bool.false 673801517397 1099511627776 342258080537047 109024274475384832 Bool.false 358132071719 1099511627776 342315077567159 109024274475384832

noncomputable def ep882 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz142 11) qz695 Bool.false 931391065461 1099511627776 318342828828949 109024274475384832 Bool.false 566817190395 1099511627776 318415163860449 109024274475384832 Bool.true

noncomputable abbrev qz696 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 10) qz143)

noncomputable def ep883 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz142 11) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz142 10) qz696) Bool.false 931391065461 1099511627776 318342828828949 109024274475384832 Bool.false 566817190395 1099511627776 318415163860449 109024274475384832

noncomputable def ep884 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz142 10) qz696 Bool.false 221792174619 274877906944 146665878263537 54512137237692416 Bool.false 911689645735 1099511627776 293314186402459 109024274475384832 Bool.false

noncomputable abbrev qz697 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 9) qz143)

noncomputable def ep885 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz142 10) (@HAdd.hAdd Complex Complex Complex qz4 qz141 qz697) Bool.false 221792174619 274877906944 146665878263537 54512137237692416 Bool.false 911689645735 1099511627776 293314186402459 109024274475384832

noncomputable def ep886 := @Enclosure.Complex.IsNear.addLitP qz141 qz697 Bool.false 691151233701 1099511627776 266926143968849 109024274475384832 Bool.false 75251180895 137438953472 133438164390545 54512137237692416 Bool.false

noncomputable abbrev qz155 := (@HMul.hMul Real Real Real qz267 qz453 qz571)

noncomputable def ep887 := @Enclosure.Complex.IsNear.of_eq qz697 (Complex.mk (@HMul.hMul Real Real Real qz0 qz320 (Real.cos qz155)) (@HMul.hMul Real Real Real qz0 qz320 (@Neg.neg Real Real.instNeg (Real.sin qz155)))) Bool.false 196017464775 1099511627776 26405612558225 109024274475384832 Bool.false 309680198575 1099511627776 26437857621369 109024274475384832 (BSN.cpow_neg_s_mk qz145 142522 1000 9 qz146 rfl)

noncomputable def ep888 := @Enclosure.Real.IsNear.mulLit_ff qz145 qz571 142522 1000 0 1 9895417793173221 4503599627370496 500000000297471 99157000000000000000 705157367359316901681 2251799813685248000 35630500021198080931 49578500000000000000000 qz147 (BSN.isNear_log_sfrac 9 1 9895417793173221 4503599627370496 500000000297471 99157000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz572) Bool.false 41504390431577613533184 18889465931478580854784 1000000000594942 198314000000000000000 9895417793173221 4503599627370496 500000000297471 99157000000000000000 (BSN.log_rat_reduce_isNear 9 1 3 18 16 61752 524288 24973259072661432 36028797018963968 198314 1000000000000000 rfl rfl rfl rfl (ep159 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep889 := nat_lit 2156682726563649578431929924798386176

noncomputable def ep890 := BSN.sin_dyadic_bound_f 1211843576 2147483648 2 1 1048576 397016 ep889 ep70 ep889 ep889 ep71 ep889 560811 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1211843576) qz20 0 1 ep889 ep70 ep889 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1211843576) qz21 0 1 ep889 ep71 ep889 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz462 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 328364487) qz26)

noncomputable def ep891 := @Enclosure.Real.IsNear.cos_image qz155 qz462 Bool.false 328364487 1048576 755 1048576 Bool.false 560811 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz155 Bool.false 705157367359316901681 2251799813685248000 35630500021198080931 49578500000000000000000 328364487 1048576 755 1048576 (ep888 rfl) rfl) (Enclosure.sfrac_false_div 328364487 1048576) (BSN.cos_reduce3 qz462 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 85275910584971238047744) qz27) 226375608064910080 72057594037927936 Bool.false 560811 1048576 49 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q3 328364487 1048576 226375608064910080 72057594037927936 49 85275910584971238047744 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 560811 1048576 85275910584971238047744 151115727451828646838272 1211843576 2147483648 397016 396628 (ep890 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep892 := BSN.cos_dyadic_bound_f 1211843576 2147483648 2 1 1048576 397016 ep889 ep66 ep889 ep889 ep67 ep889 886003 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1211843576) qz15 0 1 ep889 ep66 ep889 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1211843576) qz16 0 1 ep889 ep67 ep889 rfl rfl rfl rfl) rfl rfl

noncomputable def ep893 := @Enclosure.Real.IsNear.sin_image qz155 qz462 Bool.false 328364487 1048576 755 1048576 Bool.true 886003 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz155 Bool.false 705157367359316901681 2251799813685248000 35630500021198080931 49578500000000000000000 328364487 1048576 755 1048576 (ep888 rfl) rfl) (Enclosure.sfrac_false_div 328364487 1048576) (BSN.sin_reduce3 qz462 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 85275910584971238047744) qz27) 226375608064910080 72057594037927936 Bool.false 886003 1048576 49 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q3 328364487 1048576 226375608064910080 72057594037927936 49 85275910584971238047744 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 886003 1048576 85275910584971238047744 151115727451828646838272 1211843576 2147483648 397016 396628 (ep892 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep894 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz320 (Real.cos qz155)) (@HMul.hMul Real Real Real qz0 qz320 (@Neg.neg Real Real.instNeg (Real.sin qz155))) Bool.false 196017464775 1099511627776 26405612558225 109024274475384832 Bool.false 309680198575 1099511627776 26437857621369 109024274475384832 (@Enclosure.Real.IsNear.mulLit_ff qz320 (Real.cos qz155) 349525 1048576 1 1048576 560811 1048576 75387823 103973650432 196017464775 1099511627776 26405612558225 109024274475384832 qz324 (@Enclosure.Real.IsNear.recentre' (Real.cos qz155) Bool.false 560811 1048576 150775646 207947300864 560811 1048576 75387823 103973650432 (ep891 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz320 (@Neg.neg Real Real.instNeg (Real.sin qz155)) 349525 1048576 1 1048576 886003 1048576 75387823 103973650432 309680198575 1099511627776 26437857621369 109024274475384832 qz324 (@Enclosure.Real.IsNear.neg (Real.sin qz155) Bool.true 886003 1048576 75387823 103973650432 (@Enclosure.Real.IsNear.recentre' (Real.sin qz155) Bool.true 886003 1048576 150775646 207947300864 886003 1048576 75387823 103973650432 (ep893 rfl rfl) rfl)) rfl)

noncomputable def ep895 := @ep886 196017464775 1099511627776 26405612558225 109024274475384832 Bool.false 309680198575 1099511627776 26437857621369 109024274475384832 Bool.false 975452299773262090469376 221792174619 274877906944 146665878263537 54512137237692416 Bool.false 125301670801076828241920 911689645735 1099511627776 293314186402459 109024274475384832 EMRow49.d13 (ep887 ep894) rfl rfl

noncomputable abbrev qz156 := (@HMul.hMul Real Real Real qz267 qz453 qz574)

noncomputable def ep896 := @Enclosure.Complex.IsNear.of_eq qz696 (Complex.mk (@HMul.hMul Real Real Real qz0 qz34 (Real.cos qz156)) (@HMul.hMul Real Real Real qz0 qz34 (@Neg.neg Real Real.instNeg (Real.sin qz156)))) Bool.false 44222366985 1099511627776 25011072301875 109024274475384832 Bool.true 86218113835 274877906944 12550488728995 54512137237692416 (BSN.cpow_neg_s_mk qz145 142522 1000 10 qz146 rfl)

noncomputable def ep897 := @Enclosure.Real.IsNear.mulLit_ff qz145 qz574 142522 1000 0 1 10369917190100709 4503599627370496 500000000297471 99157000000000000000 738970668883766624049 2251799813685248000 35630500021198080931 49578500000000000000000 qz147 (BSN.isNear_log_sfrac 10 1 10369917190100709 4503599627370496 500000000297471 99157000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz575) Bool.false 43494585150108164161536 18889465931478580854784 1000000000594942 198314000000000000000 10369917190100709 4503599627370496 500000000297471 99157000000000000000 (BSN.log_rat_reduce_isNear 10 1 3 20 16 116991 524288 24973259072661432 36028797018963968 198314 1000000000000000 rfl rfl rfl rfl (ep173 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep898 := nat_lit 3305605330638169138815708212949770027611922311802176262451357188585088000000000

noncomputable def ep899 := nat_lit 8515381365515156035067222900583220591492167923901784175792010000000000000000

noncomputable def ep900 := nat_lit 9899785229183477104376990193048143641652782599558725219002487545755264000000000

noncomputable def ep901 := BSN.cos_dyadic_bound_f 3099384900 2147483648 3 2 1048576 397016 ep898 ep102 ep899 ep900 ep104 ep899 133365 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3099384900) qz15 0 2 ep898 ep102 ep899 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3099384900) qz16 0 2 ep900 ep104 ep899 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz463 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 21506877) (@Nat.cast Real Real.instNatCast 65536))

noncomputable def ep902 := @Enclosure.Real.IsNear.cos_image qz156 qz463 Bool.false 21506877 65536 755 1048576 Bool.false 133365 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz156 Bool.false 738970668883766624049 2251799813685248000 35630500021198080931 49578500000000000000000 21506877 65536 755 1048576 (ep897 rfl) rfl) (Enclosure.sfrac_false_div 21506877 65536) (BSN.cos_reduce0 qz463 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 13631238949773932232704) qz650) 226375608064910080 72057594037927936 Bool.false 133365 1048576 52 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q0 21506877 65536 226375608064910080 72057594037927936 52 13631238949773932232704 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 133365 1048576 13631238949773932232704 9444732965739290427392 3099384900 2147483648 397016 396628 (ep901 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep903 := nat_lit 5943277290056292325040221004989119473228266426904795845071809331453158400000000

noncomputable def ep904 := nat_lit 15551939427936598217715231890275321025116377131921481467474884994758272000000000

noncomputable def ep905 := BSN.sin_dyadic_bound_f 3099384900 2147483648 3 2 1048576 397016 ep903 ep95 ep899 ep904 ep98 ep899 1040060 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3099384900) qz20 0 2 ep903 ep95 ep899 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3099384900) qz21 0 2 ep904 ep98 ep899 rfl rfl rfl rfl) rfl rfl

noncomputable def ep906 := @Enclosure.Real.IsNear.sin_image qz156 qz463 Bool.false 21506877 65536 755 1048576 Bool.false 1040060 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz156 Bool.false 738970668883766624049 2251799813685248000 35630500021198080931 49578500000000000000000 21506877 65536 755 1048576 (ep897 rfl) rfl) (Enclosure.sfrac_false_div 21506877 65536) (BSN.sin_reduce0 qz463 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 13631238949773932232704) qz650) 226375608064910080 72057594037927936 Bool.false 1040060 1048576 52 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q0 21506877 65536 226375608064910080 72057594037927936 52 13631238949773932232704 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1040060 1048576 13631238949773932232704 9444732965739290427392 3099384900 2147483648 397016 396628 (ep905 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep907 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz34 (Real.cos qz156)) (@HMul.hMul Real Real Real qz0 qz34 (@Neg.neg Real Real.instNeg (Real.sin qz156))) Bool.false 44222366985 1099511627776 25011072301875 109024274475384832 Bool.true 86218113835 274877906944 12550488728995 54512137237692416 (@Enclosure.Real.IsNear.mulLit_ff qz34 (Real.cos qz156) 331589 1048576 1 1048576 133365 1048576 75387823 103973650432 44222366985 1099511627776 25011072301875 109024274475384832 qz326 (@Enclosure.Real.IsNear.recentre' (Real.cos qz156) Bool.false 133365 1048576 150775646 207947300864 133365 1048576 75387823 103973650432 (ep902 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz34 (@Neg.neg Real Real.instNeg (Real.sin qz156)) 331589 1048576 1 1048576 260015 262144 75387823 103973650432 86218113835 274877906944 12550488728995 54512137237692416 qz326 (@Enclosure.Real.IsNear.neg (Real.sin qz156) Bool.false 260015 262144 75387823 103973650432 (@Enclosure.Real.IsNear.recentre' (Real.sin qz156) Bool.false 1040060 1048576 150775646 207947300864 260015 262144 75387823 103973650432 (ep906 rfl rfl) rfl)) rfl)

noncomputable def ep908 := @ep884 44222366985 1099511627776 25011072301875 109024274475384832 Bool.true 86218113835 274877906944 12550488728995 54512137237692416 Bool.false 256018826620261770461184 931391065461 1099511627776 318342828828949 109024274475384832 Bool.false 155805522915656340602880 566817190395 1099511627776 318415163860449 109024274475384832 (ep885 (BSN.head_sum_c_succ qz142 9 10 rfl rfl) (ep895 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep896 ep907) rfl rfl

noncomputable abbrev qz157 := (@HMul.hMul Real Real Real qz267 qz453 qz577)

noncomputable def ep909 := @Enclosure.Complex.IsNear.of_eq qz695 (Complex.mk (@HMul.hMul Real Real Real qz0 qz36 (Real.cos qz157)) (@HMul.hMul Real Real Real qz0 qz36 (@Neg.neg Real Real.instNeg (Real.sin qz157)))) Bool.true 8049673377 34359738368 11957625854049 54512137237692416 Bool.true 52171279669 274877906944 11949956853355 54512137237692416 (BSN.cpow_neg_s_mk qz145 142522 1000 11 qz146 rfl)

noncomputable def ep910 := @Enclosure.Real.IsNear.mulLit_ff qz145 qz577 142522 1000 0 1 10799156221662949 4503599627370496 500000000297471 99157000000000000000 769558671511923408689 2251799813685248000 35630500021198080931 49578500000000000000000 qz147 (BSN.isNear_log_sfrac 11 1 10799156221662949 4503599627370496 500000000297471 99157000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz578) Bool.false 45294944137145793642496 18889465931478580854784 1000000000594942 198314000000000000000 10799156221662949 4503599627370496 500000000297471 99157000000000000000 (BSN.log_rat_reduce_isNear 11 1 3 22 16 166961 524288 24973259072661432 36028797018963968 198314 1000000000000000 rfl rfl rfl rfl (ep188 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep911 := nat_lit 857972445836543086238109130515993249283319811690156664410405129206582920216705

noncomputable def ep912 := nat_lit 177895133476545972556001183269240456767731963939286884674924392370676826241

noncomputable def ep913 := nat_lit 2246782670784365103810909435149927358812023178865937180404444508429593219039361

noncomputable def ep914 := BSN.sin_dyadic_bound_f 1911043217 2147483648 3 2 1048576 397016 ep911 ep95 ep912 ep913 ep98 ep912 814752 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1911043217) qz20 0 2 ep911 ep95 ep912 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1911043217) qz21 0 2 ep913 ep98 ep912 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz464 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 358353681) qz26)

noncomputable def ep915 := @Enclosure.Real.IsNear.cos_image qz157 qz464 Bool.false 358353681 1048576 755 1048576 Bool.true 814752 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz157 Bool.false 769558671511923408689 2251799813685248000 35630500021198080931 49578500000000000000000 358353681 1048576 755 1048576 (ep910 rfl) rfl) (Enclosure.sfrac_false_div 358353681 1048576) (BSN.cos_reduce1 qz464 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 134477711297418962665472) qz27) 226375608064910080 72057594037927936 Bool.false 814752 1048576 54 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q1 358353681 1048576 226375608064910080 72057594037927936 54 134477711297418962665472 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 814752 1048576 134477711297418962665472 151115727451828646838272 1911043217 2147483648 397016 396628 (ep914 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep916 := nat_lit 476730423301846846120085517479227023138185554034060052176747260400266367598721

noncomputable def ep917 := nat_lit 1429835479638587446415144550071142588501021198174301582760891932416057749143681

noncomputable def ep918 := BSN.cos_dyadic_bound_f 1911043217 2147483648 3 2 1048576 397016 ep916 ep102 ep912 ep917 ep104 ep912 660068 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1911043217) qz15 0 2 ep916 ep102 ep912 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1911043217) qz16 0 2 ep917 ep104 ep912 rfl rfl rfl rfl) rfl rfl

noncomputable def ep919 := @Enclosure.Real.IsNear.sin_image qz157 qz464 Bool.false 358353681 1048576 755 1048576 Bool.false 660068 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz157 Bool.false 769558671511923408689 2251799813685248000 35630500021198080931 49578500000000000000000 358353681 1048576 755 1048576 (ep910 rfl) rfl) (Enclosure.sfrac_false_div 358353681 1048576) (BSN.sin_reduce1 qz464 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 134477711297418962665472) qz27) 226375608064910080 72057594037927936 Bool.false 660068 1048576 54 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q1 358353681 1048576 226375608064910080 72057594037927936 54 134477711297418962665472 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 660068 1048576 134477711297418962665472 151115727451828646838272 1911043217 2147483648 397016 396628 (ep918 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep920 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz36 (Real.cos qz157)) (@HMul.hMul Real Real Real qz0 qz36 (@Neg.neg Real Real.instNeg (Real.sin qz157))) Bool.true 8049673377 34359738368 11957625854049 54512137237692416 Bool.true 52171279669 274877906944 11949956853355 54512137237692416 (@Enclosure.Real.IsNear.mulLit_ft qz36 (Real.cos qz157) 316157 1048576 1 1048576 25461 32768 75387823 103973650432 8049673377 34359738368 11957625854049 54512137237692416 qz328 (@Enclosure.Real.IsNear.recentre' (Real.cos qz157) Bool.true 814752 1048576 150775646 207947300864 25461 32768 75387823 103973650432 (ep915 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz36 (@Neg.neg Real Real.instNeg (Real.sin qz157)) 316157 1048576 1 1048576 165017 262144 75387823 103973650432 52171279669 274877906944 11949956853355 54512137237692416 qz328 (@Enclosure.Real.IsNear.neg (Real.sin qz157) Bool.false 165017 262144 75387823 103973650432 (@Enclosure.Real.IsNear.recentre' (Real.sin qz157) Bool.false 660068 1048576 150775646 207947300864 165017 262144 75387823 103973650432 (ep919 rfl rfl) rfl)) rfl)

noncomputable def ep921 := @ep882 8049673377 34359738368 11957625854049 54512137237692416 Bool.true 52171279669 274877906944 11949956853355 54512137237692416 Bool.false 23151643849722320388096 673801517397 1099511627776 342258080537047 109024274475384832 Bool.false 98442594283637216116736 358132071719 1099511627776 342315077567159 109024274475384832 (ep883 (BSN.head_sum_c_succ qz142 10 11 rfl rfl) (ep908 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep909 ep920) rfl rfl

noncomputable abbrev qz158 := (@HMul.hMul Real Real Real qz267 qz453 qz580)

noncomputable def ep922 := @Enclosure.Complex.IsNear.of_eq qz694 (Complex.mk (@HMul.hMul Real Real Real qz0 qz38 (Real.cos qz158)) (@HMul.hMul Real Real Real qz0 qz38 (@Neg.neg Real Real.instNeg (Real.sin qz158)))) Bool.true 26296801875 137438953472 11444328680727 54512137237692416 Bool.true 237667090005 1099511627776 22897597852359 109024274475384832 (BSN.cpow_neg_s_mk qz145 142522 1000 12 qz146 rfl)

noncomputable def ep923 := @Enclosure.Real.IsNear.mulLit_ff qz145 qz580 142522 1000 0 1 11191020447815397 4503599627370496 500000000297471 99157000000000000000 797483308131773005617 2251799813685248000 35630500021198080931 49578500000000000000000 qz147 (BSN.isNear_log_sfrac 12 1 11191020447815397 4503599627370496 500000000297471 99157000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz581) Bool.false 46938541828353910898688 18889465931478580854784 1000000000594942 198314000000000000000 11191020447815397 4503599627370496 500000000297471 99157000000000000000 (BSN.log_rat_reduce_isNear 12 1 3 24 16 212580 524288 24973259072661432 36028797018963968 198314 1000000000000000 rfl rfl rfl rfl (ep202 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep924 := nat_lit 5861538843633287481329294482882953216

noncomputable def ep925 := BSN.sin_dyadic_bound_f 1555976064 2147483648 2 1 1048576 397016 ep924 ep70 ep924 ep924 ep71 ep924 695000 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1555976064) qz20 0 1 ep924 ep70 ep924 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1555976064) qz21 0 1 ep924 ep71 ep924 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz465 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 371357103) qz26)

noncomputable def ep926 := @Enclosure.Real.IsNear.cos_image qz158 qz465 Bool.false 371357103 1048576 755 1048576 Bool.true 695000 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz158 Bool.false 797483308131773005617 2251799813685248000 35630500021198080931 49578500000000000000000 371357103 1048576 755 1048576 (ep923 rfl) rfl) (Enclosure.sfrac_false_div 371357103 1048576) (BSN.cos_reduce1 qz465 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 109492081638971661090816) qz27) 226375608064910080 72057594037927936 Bool.false 695000 1048576 56 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q1 371357103 1048576 226375608064910080 72057594037927936 56 109492081638971661090816 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 695000 1048576 109492081638971661090816 151115727451828646838272 1555976064 2147483648 397016 396628 (ep925 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep927 := nat_lit 209465080346223767909591640357404555866697732222745916269549724524288185204736

noncomputable def ep928 := nat_lit 34357637615421856990595646804416459304524259152460129360565514605644742656

noncomputable def ep929 := nat_lit 628326525763440460014793729778604834681484148149932828549928042543653266128896

noncomputable def ep930 := BSN.cos_dyadic_bound_f 1555976064 2147483648 3 2 1048576 397016 ep927 ep102 ep928 ep929 ep104 ep928 785165 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1555976064) qz15 0 2 ep927 ep102 ep928 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1555976064) qz16 0 2 ep929 ep104 ep928 rfl rfl rfl rfl) rfl rfl

noncomputable def ep931 := @Enclosure.Real.IsNear.sin_image qz158 qz465 Bool.false 371357103 1048576 755 1048576 Bool.false 785165 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz158 Bool.false 797483308131773005617 2251799813685248000 35630500021198080931 49578500000000000000000 371357103 1048576 755 1048576 (ep923 rfl) rfl) (Enclosure.sfrac_false_div 371357103 1048576) (BSN.sin_reduce1 qz465 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 109492081638971661090816) qz27) 226375608064910080 72057594037927936 Bool.false 785165 1048576 56 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q1 371357103 1048576 226375608064910080 72057594037927936 56 109492081638971661090816 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 785165 1048576 109492081638971661090816 151115727451828646838272 1555976064 2147483648 397016 396628 (ep930 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep932 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz38 (Real.cos qz158)) (@HMul.hMul Real Real Real qz0 qz38 (@Neg.neg Real Real.instNeg (Real.sin qz158))) Bool.true 26296801875 137438953472 11444328680727 54512137237692416 Bool.true 237667090005 1099511627776 22897597852359 109024274475384832 (@Enclosure.Real.IsNear.mulLit_ft qz38 (Real.cos qz158) 302697 1048576 1 1048576 86875 131072 75387823 103973650432 26296801875 137438953472 11444328680727 54512137237692416 qz330 (@Enclosure.Real.IsNear.recentre' (Real.cos qz158) Bool.true 695000 1048576 150775646 207947300864 86875 131072 75387823 103973650432 (ep926 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz38 (@Neg.neg Real Real.instNeg (Real.sin qz158)) 302697 1048576 1 1048576 785165 1048576 75387823 103973650432 237667090005 1099511627776 22897597852359 109024274475384832 qz330 (@Enclosure.Real.IsNear.neg (Real.sin qz158) Bool.false 785165 1048576 75387823 103973650432 (@Enclosure.Real.IsNear.recentre' (Real.sin qz158) Bool.false 785165 1048576 150775646 207947300864 785165 1048576 75387823 103973650432 (ep931 rfl rfl) rfl)) rfl)

noncomputable def ep933 := @ep880 26296801875 137438953472 11444328680727 54512137237692416 Bool.true 237667090005 1099511627776 22897597852359 109024274475384832 Bool.false 63692935964005062672384 463427102397 1099511627776 365146737898501 109024274475384832 Bool.false 132452648134366214488064 60232490857 549755813888 182606337709759 54512137237692416 (ep881 (BSN.head_sum_c_succ qz142 11 12 rfl rfl) (ep921 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep922 ep932) rfl rfl

noncomputable abbrev qz159 := (@HMul.hMul Real Real Real qz267 qz453 qz583)

noncomputable def ep934 := @Enclosure.Complex.IsNear.of_eq qz693 (Complex.mk (@HMul.hMul Real Real Real qz0 qz40 (Real.cos qz159)) (@HMul.hMul Real Real Real qz0 qz40 (@Neg.neg Real Real.instNeg (Real.sin qz159)))) Bool.false 8015954349 68719476736 342804375485 1703504288677888 Bool.true 276667772121 1099511627776 21990081732123 109024274475384832 (BSN.cpow_neg_s_mk qz145 142522 1000 13 qz146 rfl)

noncomputable def ep935 := @Enclosure.Real.IsNear.mulLit_ff qz145 qz583 142522 1000 0 1 11551497052968677 4503599627370496 500000000297471 99157000000000000000 823171231491600891697 2251799813685248000 35630500021198080931 49578500000000000000000 qz147 (BSN.isNear_log_sfrac 13 1 11551497052968677 4503599627370496 500000000297471 99157000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz584) Bool.false 48450490295254733815808 18889465931478580854784 1000000000594942 198314000000000000000 11551497052968677 4503599627370496 500000000297471 99157000000000000000 (BSN.log_rat_reduce_isNear 13 1 3 26 16 254545 524288 24973259072661432 36028797018963968 198314 1000000000000000 rfl rfl rfl rfl (ep213 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep936 := nat_lit 1269941930985466669236071804269738278250014786168634635784989837982315725571201

noncomputable def ep937 := nat_lit 1260803688597284026030079739410146013190816353137923072268785057609769403521

noncomputable def ep938 := nat_lit 3807304185579205439656155253330394542723662725799628061210431943831727637906561

noncomputable def ep939 := BSN.cos_dyadic_bound_f 2441073937 2147483648 3 2 1048576 397016 ep936 ep102 ep937 ep938 ep104 ep937 441008 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2441073937) qz15 0 2 ep936 ep102 ep937 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2441073937) qz16 0 2 ep938 ep104 ep937 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz466 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 383318975) qz26)

noncomputable def ep940 := @Enclosure.Real.IsNear.cos_image qz159 qz466 Bool.false 383318975 1048576 377 524288 Bool.false 441008 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz159 Bool.false 823171231491600891697 2251799813685248000 35630500021198080931 49578500000000000000000 383318975 1048576 377 524288 (ep935 rfl) rfl) (Enclosure.sfrac_false_div 383318975 1048576) (BSN.cos_reduce0 qz466 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 171775307442387828080640) qz27) 226375608064910080 72057594037927936 Bool.false 441008 1048576 58 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q0 383318975 1048576 226375608064910080 72057594037927936 58 171775307442387828080640 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 441008 1048576 171775307442387828080640 151115727451828646838272 2441073937 2147483648 397016 396628 (ep939 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep941 := nat_lit 2284886832822962177404105183894000784039473962021032005955166680322080490505345

noncomputable def ep942 := nat_lit 5982186118088124385730512495382385626558218102626193854432239463131223562765441

noncomputable def ep943 := BSN.sin_dyadic_bound_f 2441073937 2147483648 3 2 1048576 397016 ep941 ep95 ep937 ep942 ep98 ep937 951327 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2441073937) qz20 0 2 ep941 ep95 ep937 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2441073937) qz21 0 2 ep942 ep98 ep937 rfl rfl rfl rfl) rfl rfl

noncomputable def ep944 := @Enclosure.Real.IsNear.sin_image qz159 qz466 Bool.false 383318975 1048576 377 524288 Bool.false 951327 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz159 Bool.false 823171231491600891697 2251799813685248000 35630500021198080931 49578500000000000000000 383318975 1048576 377 524288 (ep935 rfl) rfl) (Enclosure.sfrac_false_div 383318975 1048576) (BSN.sin_reduce0 qz466 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 171775307442387828080640) qz27) 226375608064910080 72057594037927936 Bool.false 951327 1048576 58 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q0 383318975 1048576 226375608064910080 72057594037927936 58 171775307442387828080640 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 951327 1048576 171775307442387828080640 151115727451828646838272 2441073937 2147483648 397016 396628 (ep943 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep945 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz40 (Real.cos qz159)) (@HMul.hMul Real Real Real qz0 qz40 (@Neg.neg Real Real.instNeg (Real.sin qz159))) Bool.false 8015954349 68719476736 342804375485 1703504288677888 Bool.true 276667772121 1099511627776 21990081732123 109024274475384832 (@Enclosure.Real.IsNear.mulLit_ff qz40 (Real.cos qz159) 290823 1048576 1 1048576 27563 65536 37644333 51986825216 8015954349 68719476736 342804375485 1703504288677888 qz333 (@Enclosure.Real.IsNear.recentre' (Real.cos qz159) Bool.false 441008 1048576 75288666 103973650432 27563 65536 37644333 51986825216 (ep940 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz40 (@Neg.neg Real Real.instNeg (Real.sin qz159)) 290823 1048576 1 1048576 951327 1048576 37644333 51986825216 276667772121 1099511627776 21990081732123 109024274475384832 qz333 (@Enclosure.Real.IsNear.neg (Real.sin qz159) Bool.false 951327 1048576 37644333 51986825216 (@Enclosure.Real.IsNear.recentre' (Real.sin qz159) Bool.false 951327 1048576 75288666 103973650432 951327 1048576 37644333 51986825216 (ep944 rfl rfl) rfl)) rfl)

noncomputable def ep946 := @ep878 8015954349 68719476736 342804375485 1703504288677888 Bool.true 276667772121 1099511627776 21990081732123 109024274475384832 Bool.false 40660102996449627734016 591682371981 1099511627776 387086217929541 109024274475384832 Bool.true 85873392171776963772416 156202790407 1099511627776 387202757151641 109024274475384832 (ep879 (BSN.head_sum_c_succ qz142 12 13 rfl rfl) (ep933 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep934 ep945) rfl rfl

noncomputable abbrev qz160 := (@HMul.hMul Real Real Real qz267 qz453 qz587)

noncomputable def ep947 := @Enclosure.Complex.IsNear.of_eq qz692 (Complex.mk (@HMul.hMul Real Real Real qz0 qz42 (Real.cos qz160)) (@HMul.hMul Real Real Real qz0 qz42 (@Neg.neg Real Real.instNeg (Real.sin qz160)))) Bool.false 190020167365 1099511627776 21194218968447 109024274475384832 Bool.false 224150962335 1099511627776 21206295299477 109024274475384832 (BSN.cpow_neg_s_mk qz145 142522 1000 14 qz146 rfl)

noncomputable def ep948 := @Enclosure.Real.IsNear.mulLit_ff qz145 qz587 142522 1000 0 1 11885250371606245 4503599627370496 500000000297471 99157000000000000000 169390965346206524989 450359962737049600 35630500021198080931 49578500000000000000000 qz147 (BSN.isNear_log_sfrac 14 1 11885250371606245 4503599627370496 500000000297471 99157000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz588) Bool.false 49850353174629559828480 18889465931478580854784 1000000000594942 198314000000000000000 11885250371606245 4503599627370496 500000000297471 99157000000000000000 (BSN.log_rat_reduce_isNear 14 1 3 28 16 293399 524288 24973259072661432 36028797018963968 198314 1000000000000000 rfl rfl rfl rfl (ep227 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep949 := nat_lit 5199692091550974586939504849674286096

noncomputable def ep950 := BSN.sin_dyadic_bound_f 1510060706 2147483648 2 1 1048576 397016 ep949 ep70 ep949 ep949 ep71 ep949 678055 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1510060706) qz20 0 1 ep949 ep70 ep949 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1510060706) qz21 0 1 ep949 ep71 ep949 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz467 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 197197037) qz17)

noncomputable def ep951 := @Enclosure.Real.IsNear.cos_image qz160 qz467 Bool.false 197197037 524288 755 1048576 Bool.false 678055 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz160 Bool.false 169390965346206524989 450359962737049600 35630500021198080931 49578500000000000000000 197197037 524288 755 1048576 (ep948 rfl) rfl) (Enclosure.sfrac_false_div 197197037 524288) (BSN.cos_reduce3 qz467 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 53130537785106527944704) qz19) 226375608064910080 72057594037927936 Bool.false 678055 1048576 59 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q3 197197037 524288 226375608064910080 72057594037927936 59 53130537785106527944704 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 678055 1048576 53130537785106527944704 75557863725914323419136 1510060706 2147483648 397016 396628 (ep950 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep952 := nat_lit 185810207676017259917837970114008470352192922063125789128562302222221974077696

noncomputable def ep953 := nat_lit 27036797846937748685406243520068216666956166867739815427065220747258921216

noncomputable def ep954 := nat_lit 557376549432357904256143097854985274623244853855641887754832776225171404390656

noncomputable def ep955 := BSN.cos_dyadic_bound_f 1510060706 2147483648 3 2 1048576 397016 ep952 ep102 ep953 ep954 ep104 ep953 799845 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1510060706) qz15 0 2 ep952 ep102 ep953 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1510060706) qz16 0 2 ep954 ep104 ep953 rfl rfl rfl rfl) rfl rfl

noncomputable def ep956 := @Enclosure.Real.IsNear.sin_image qz160 qz467 Bool.false 197197037 524288 755 1048576 Bool.true 799845 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz160 Bool.false 169390965346206524989 450359962737049600 35630500021198080931 49578500000000000000000 197197037 524288 755 1048576 (ep948 rfl) rfl) (Enclosure.sfrac_false_div 197197037 524288) (BSN.sin_reduce3 qz467 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 53130537785106527944704) qz19) 226375608064910080 72057594037927936 Bool.false 799845 1048576 59 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q3 197197037 524288 226375608064910080 72057594037927936 59 53130537785106527944704 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 799845 1048576 53130537785106527944704 75557863725914323419136 1510060706 2147483648 397016 396628 (ep955 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep957 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz42 (Real.cos qz160)) (@HMul.hMul Real Real Real qz0 qz42 (@Neg.neg Real Real.instNeg (Real.sin qz160))) Bool.false 190020167365 1099511627776 21194218968447 109024274475384832 Bool.false 224150962335 1099511627776 21206295299477 109024274475384832 (@Enclosure.Real.IsNear.mulLit_ff qz42 (Real.cos qz160) 280243 1048576 1 1048576 678055 1048576 75387823 103973650432 190020167365 1099511627776 21194218968447 109024274475384832 qz335 (@Enclosure.Real.IsNear.recentre' (Real.cos qz160) Bool.false 678055 1048576 150775646 207947300864 678055 1048576 75387823 103973650432 (ep951 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz42 (@Neg.neg Real Real.instNeg (Real.sin qz160)) 280243 1048576 1 1048576 799845 1048576 75387823 103973650432 224150962335 1099511627776 21206295299477 109024274475384832 qz335 (@Enclosure.Real.IsNear.neg (Real.sin qz160) Bool.true 799845 1048576 75387823 103973650432 (@Enclosure.Real.IsNear.recentre' (Real.sin qz160) Bool.true 799845 1048576 150775646 207947300864 799845 1048576 75387823 103973650432 (ep956 rfl rfl) rfl)) rfl)

noncomputable def ep958 := @ep876 190020167365 1099511627776 21194218968447 109024274475384832 Bool.false 224150962335 1099511627776 21206295299477 109024274475384832 Bool.false 859491031472953146474496 390851269673 549755813888 102070109224497 27256068618846208 Bool.false 74709805120958788272128 8493521491 137438953472 204204526225559 54512137237692416 (ep877 (BSN.head_sum_c_succ qz142 13 14 rfl rfl) (ep946 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep947 ep957) rfl rfl

noncomputable abbrev qz161 := (@HMul.hMul Real Real Real qz267 qz453 qz590)

noncomputable def ep959 := @Enclosure.Complex.IsNear.of_eq qz691 (Complex.mk (@HMul.hMul Real Real Real qz0 qz44 (Real.cos qz161)) (@HMul.hMul Real Real Real qz0 qz44 (@Neg.neg Real Real.instNeg (Real.sin qz161)))) Bool.true 254454033663 1099511627776 20503841987017 109024274475384832 Bool.true 125888879439 1099511627776 20456755897369 109024274475384832 (BSN.cpow_neg_s_mk qz145 142522 1000 15 qz146 rfl)

noncomputable def ep960 := @Enclosure.Real.IsNear.mulLit_ff qz145 qz590 142522 1000 0 1 12195965485668069 4503599627370496 500000000297471 99157000000000000000 869096696474192265009 2251799813685248000 35630500021198080931 49578500000000000000000 qz147 (BSN.isNear_log_sfrac 15 1 12195965485668069 4503599627370496 500000000297471 99157000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz591) Bool.false 51153586820399524478976 18889465931478580854784 1000000000594942 198314000000000000000 12195965485668069 4503599627370496 500000000297471 99157000000000000000 (BSN.log_rat_reduce_isNear 15 1 3 30 16 329571 524288 24973259072661432 36028797018963968 198314 1000000000000000 rfl rfl rfl rfl (ep238 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep961 := nat_lit 2087690653001958191120956019712504158975276422691350619315388659636279649788160

noncomputable def ep962 := nat_lit 1052668723031396029991538117829589200956331689615214772022754786800212664576

noncomputable def ep963 := nat_lit 5466056913263077764125374704199120129086080379551303179052266791297341595607296

noncomputable def ep964 := BSN.sin_dyadic_bound_f 2386637526 2147483648 3 2 1048576 397016 ep961 ep95 ep962 ep963 ep98 ep962 939843 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2386637526) qz20 0 2 ep961 ep95 ep962 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2386637526) qz21 0 2 ep963 ep98 ep962 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz468 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 202352343) qz17)

noncomputable def ep965 := @Enclosure.Real.IsNear.cos_image qz161 qz468 Bool.false 202352343 524288 755 1048576 Bool.true 939843 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz161 Bool.false 869096696474192265009 2251799813685248000 35630500021198080931 49578500000000000000000 202352343 524288 755 1048576 (ep960 rfl) rfl) (Enclosure.sfrac_false_div 202352343 524288) (BSN.cos_reduce1 qz468 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 83972342756881303863296) qz19) 226375608064910080 72057594037927936 Bool.false 939843 1048576 61 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q1 202352343 524288 226375608064910080 72057594037927936 61 83972342756881303863296 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 939843 1048576 83972342756881303863296 75557863725914323419136 2386637526 2147483648 397016 396628 (ep964 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep966 := nat_lit 1160295993322435171080527361225982127964467493357245995073892701925399899955456

noncomputable def ep967 := nat_lit 3478782642521242721181599007442287205491489816692507555677632596202599274537216

noncomputable def ep968 := BSN.cos_dyadic_bound_f 2386637526 2147483648 3 2 1048576 397016 ep966 ep102 ep962 ep967 ep104 ep962 464979 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2386637526) qz15 0 2 ep966 ep102 ep962 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2386637526) qz16 0 2 ep967 ep104 ep962 rfl rfl rfl rfl) rfl rfl

noncomputable def ep969 := @Enclosure.Real.IsNear.sin_image qz161 qz468 Bool.false 202352343 524288 755 1048576 Bool.false 464979 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz161 Bool.false 869096696474192265009 2251799813685248000 35630500021198080931 49578500000000000000000 202352343 524288 755 1048576 (ep960 rfl) rfl) (Enclosure.sfrac_false_div 202352343 524288) (BSN.sin_reduce1 qz468 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 83972342756881303863296) qz19) 226375608064910080 72057594037927936 Bool.false 464979 1048576 61 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q1 202352343 524288 226375608064910080 72057594037927936 61 83972342756881303863296 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 464979 1048576 83972342756881303863296 75557863725914323419136 2386637526 2147483648 397016 396628 (ep968 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep970 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz44 (Real.cos qz161)) (@HMul.hMul Real Real Real qz0 qz44 (@Neg.neg Real Real.instNeg (Real.sin qz161))) Bool.true 254454033663 1099511627776 20503841987017 109024274475384832 Bool.true 125888879439 1099511627776 20456755897369 109024274475384832 (@Enclosure.Real.IsNear.mulLit_ft qz44 (Real.cos qz161) 270741 1048576 1 1048576 939843 1048576 75387823 103973650432 254454033663 1099511627776 20503841987017 109024274475384832 qz337 (@Enclosure.Real.IsNear.recentre' (Real.cos qz161) Bool.true 939843 1048576 150775646 207947300864 939843 1048576 75387823 103973650432 (ep965 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz44 (@Neg.neg Real Real.instNeg (Real.sin qz161)) 270741 1048576 1 1048576 464979 1048576 75387823 103973650432 125888879439 1099511627776 20456755897369 109024274475384832 qz337 (@Enclosure.Real.IsNear.neg (Real.sin qz161) Bool.false 464979 1048576 75387823 103973650432 (@Enclosure.Real.IsNear.recentre' (Real.sin qz161) Bool.false 464979 1048576 150775646 207947300864 464979 1048576 75387823 103973650432 (ep969 rfl rfl) rfl)) rfl)

noncomputable def ep971 := @ep874 254454033663 1099511627776 20503841987017 109024274475384832 Bool.true 125888879439 1099511627776 20456755897369 109024274475384832 Bool.false 289857931362989458325504 527248505683 1099511627776 428784278885005 109024274475384832 Bool.true 7963310203739089928192 57940707511 1099511627776 428865808348487 109024274475384832 (ep875 (BSN.head_sum_c_succ qz142 14 15 rfl rfl) (ep958 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep959 ep970) rfl rfl

noncomputable abbrev qz162 := (@HMul.hMul Real Real Real qz267 qz453 qz593)

noncomputable def ep972 := @Enclosure.Complex.IsNear.of_eq qz690 (Complex.mk (@HMul.hMul Real Real Real qz0 qz46 (Real.cos qz162)) (@HMul.hMul Real Real Real qz0 qz46 (@Neg.neg Real Real.instNeg (Real.sin qz162)))) Bool.false 53183309697 274877906944 4960733241131 27256068618846208 Bool.false 174074224149 1099511627776 19828309984263 109024274475384832 (BSN.cpow_neg_s_mk qz145 142522 1000 16 qz146 rfl)

noncomputable def ep973 := @Enclosure.Real.IsNear.mulLit_ff qz145 qz593 142522 1000 0 1 3121657384082679 1125899906842624 125000000099157 24789250000000000000 222452426847115788219 562949953421312000 8907625007066026977 12394625000000000000000 qz147 (BSN.isNear_log_sfrac 16 1 3121657384082679 1125899906842624 125000000099157 24789250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz594) Bool.false 52372720210750067441664 18889465931478580854784 1000000000793256 198314000000000000000 3121657384082679 1125899906842624 125000000099157 24789250000000000000 (BSN.log_rat_reduce_isNear 16 1 4 32 32 0 524288 24973259072661432 36028797018963968 198314 1000000000000000 rfl rfl rfl rfl (ep249 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep974 := nat_lit 839273751852126210210247037190596909242895960850720687968206109650403737890625

noncomputable def ep975 := nat_lit 170227057659024834601810917105718007308458666395570421846998730621337890625

noncomputable def ep976 := nat_lit 2197822315805073081770815498776249314100513821530104211614692289234813337890625

noncomputable def ep977 := BSN.sin_dyadic_bound_f 1900546825 2147483648 3 2 1048576 397016 ep974 ep95 ep975 ep976 ep98 ep975 811516 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1900546825) qz20 0 2 ep974 ep95 ep975 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1900546825) qz21 0 2 ep976 ep98 ep975 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz469 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 414349933) qz26)

noncomputable def ep978 := @Enclosure.Real.IsNear.cos_image qz162 qz469 Bool.false 414349933 1048576 755 1048576 Bool.false 811516 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz162 Bool.false 222452426847115788219 562949953421312000 8907625007066026977 12394625000000000000000 414349933 1048576 755 1048576 (ep973 rfl) rfl) (Enclosure.sfrac_false_div 414349933 1048576) (BSN.cos_reduce3 qz469 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 133739093343220317290496) qz27) 226375608064910080 72057594037927936 Bool.false 811516 1048576 62 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q3 414349933 1048576 226375608064910080 72057594037927936 62 133739093343220317290496 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 811516 1048576 133739093343220317290496 151115727451828646838272 1900546825 2147483648 397016 396628 (ep977 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep979 := nat_lit 466338851943474127821071381069045268693745959879909524614268727019389337890625

noncomputable def ep980 := nat_lit 1398676101715104333794010521372924370066620962306937432999112183596925337890625

noncomputable def ep981 := BSN.cos_dyadic_bound_f 1900546825 2147483648 3 2 1048576 397016 ep979 ep102 ep975 ep980 ep104 ep975 664043 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1900546825) qz15 0 2 ep979 ep102 ep975 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1900546825) qz16 0 2 ep980 ep104 ep975 rfl rfl rfl rfl) rfl rfl

noncomputable def ep982 := @Enclosure.Real.IsNear.sin_image qz162 qz469 Bool.false 414349933 1048576 755 1048576 Bool.true 664043 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz162 Bool.false 222452426847115788219 562949953421312000 8907625007066026977 12394625000000000000000 414349933 1048576 755 1048576 (ep973 rfl) rfl) (Enclosure.sfrac_false_div 414349933 1048576) (BSN.sin_reduce3 qz469 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 133739093343220317290496) qz27) 226375608064910080 72057594037927936 Bool.false 664043 1048576 62 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q3 414349933 1048576 226375608064910080 72057594037927936 62 133739093343220317290496 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 664043 1048576 133739093343220317290496 151115727451828646838272 1900546825 2147483648 397016 396628 (ep981 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep983 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz46 (Real.cos qz162)) (@HMul.hMul Real Real Real qz0 qz46 (@Neg.neg Real Real.instNeg (Real.sin qz162))) Bool.false 53183309697 274877906944 4960733241131 27256068618846208 Bool.false 174074224149 1099511627776 19828309984263 109024274475384832 (@Enclosure.Real.IsNear.mulLit_ff qz46 (Real.cos qz162) 262143 1048576 1 1048576 202879 262144 75387823 103973650432 53183309697 274877906944 4960733241131 27256068618846208 qz339 (@Enclosure.Real.IsNear.recentre' (Real.cos qz162) Bool.false 811516 1048576 150775646 207947300864 202879 262144 75387823 103973650432 (ep978 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz46 (@Neg.neg Real Real.instNeg (Real.sin qz162)) 262143 1048576 1 1048576 664043 1048576 75387823 103973650432 174074224149 1099511627776 19828309984263 109024274475384832 qz339 (@Enclosure.Real.IsNear.neg (Real.sin qz162) Bool.true 664043 1048576 75387823 103973650432 (@Enclosure.Real.IsNear.recentre' (Real.sin qz162) Bool.true 664043 1048576 150775646 207947300864 664043 1048576 75387823 103973650432 (ep982 rfl rfl) rfl)) rfl)

noncomputable def ep984 := @ep872 53183309697 274877906944 4960733241131 27256068618846208 Bool.false 174074224149 1099511627776 19828309984263 109024274475384832 Bool.false 203404633096958324506624 739981744471 1099511627776 448627211849529 109024274475384832 Bool.false 127690151917998558937088 58066758319 549755813888 224347059166375 54512137237692416 (ep873 (BSN.head_sum_c_succ qz142 15 16 rfl rfl) (ep971 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep972 ep983) rfl rfl

theorem EMRow49.d14 : Enclosure.Complex.IsNear qz154 Bool.false 739981744471 1099511627776 448627211849529 109024274475384832 Bool.false 58066758319 549755813888 224347059166375 54512137237692416 := ep871 (BSN.head_sum_c_succ qz142 16 17 rfl rfl) (ep984 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable abbrev qz163 := (BSN.headSumC qz451 25)

noncomputable abbrev qz698 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 24) qz143)

noncomputable def ep985 := @Enclosure.Complex.IsNear.of_eq qz163 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz142 24) qz698) Bool.false 1525438120315 1099511627776 589516745658731 109024274475384832 Bool.true 31476199109 137438953472 294731613875139 54512137237692416

noncomputable def ep986 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz142 24) qz698 Bool.false 1334466959501 1099511627776 573313489134609 109024274475384832 Bool.true 8369057843 68719476736 286646910225623 54512137237692416 Bool.false

noncomputable abbrev qz699 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 23) qz143)

noncomputable def ep987 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz142 24) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz142 23) qz699) Bool.false 1334466959501 1099511627776 573313489134609 109024274475384832 Bool.true 8369057843 68719476736 286646910225623 54512137237692416

noncomputable def ep988 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz142 23) qz699 Bool.false 1169952532439 1099511627776 556755784864459 109024274475384832 Bool.false 12886121921 549755813888 139184577482641 27256068618846208 Bool.false

noncomputable abbrev qz700 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 22) qz143)

noncomputable def ep989 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz142 23) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz142 22) qz700) Bool.false 1169952532439 1099511627776 556755784864459 109024274475384832 Bool.false 12886121921 549755813888 139184577482641 27256068618846208

noncomputable def ep990 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz142 22) qz700 Bool.false 496739100769 549755813888 269923063714565 54512137237692416 Bool.false 45017485975 274877906944 269919244385239 54512137237692416 Bool.false

noncomputable abbrev qz701 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 21) qz143)

noncomputable def ep991 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz142 22) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz142 21) qz701) Bool.false 496739100769 549755813888 269923063714565 54512137237692416 Bool.false 45017485975 274877906944 269919244385239 54512137237692416

noncomputable def ep992 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz142 21) qz701 Bool.false 96238861023 137438953472 130600530620407 27256068618846208 Bool.false 66791120401 274877906944 261256381625213 54512137237692416 Bool.false

noncomputable abbrev qz702 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 20) qz143)

noncomputable def ep993 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz142 21) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz142 20) qz702) Bool.false 96238861023 137438953472 130600530620407 27256068618846208 Bool.false 66791120401 274877906944 261256381625213 54512137237692416

noncomputable def ep994 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz142 20) qz702 Bool.false 267479675491 549755813888 252324913949751 54512137237692416 Bool.false 194748496485 1099511627776 504829204994799 109024274475384832 Bool.false

noncomputable abbrev qz703 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 19) qz143)

noncomputable def ep995 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz142 20) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz142 19) qz703) Bool.false 267479675491 549755813888 252324913949751 54512137237692416 Bool.false 194748496485 1099511627776 504829204994799 109024274475384832

noncomputable def ep996 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz142 19) qz703 Bool.false 118462055935 274877906944 950221087423 212938036084736 Bool.true 24990537449 549755813888 243308443708465 54512137237692416 Bool.false

noncomputable abbrev qz704 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 18) qz143)

noncomputable def ep997 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz142 19) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz142 18) qz704) Bool.false 118462055935 274877906944 950221087423 212938036084736 Bool.true 24990537449 549755813888 243308443708465 54512137237692416

noncomputable def ep998 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz142 18) qz704 Bool.false 89157677529 137438953472 116946223234459 27256068618846208 Bool.true 37298725207 274877906944 116986207898081 27256068618846208 Bool.true

noncomputable abbrev qz705 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 17) qz143)

noncomputable def ep999 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz142 18) (@HAdd.hAdd Complex Complex Complex qz4 qz154 qz705) Bool.false 89157677529 137438953472 116946223234459 27256068618846208 Bool.true 37298725207 274877906944 116986207898081 27256068618846208

noncomputable def ep1000 := @Enclosure.Complex.IsNear.addLitP qz154 qz705 Bool.false 739981744471 1099511627776 448627211849529 109024274475384832 Bool.false 58066758319 549755813888 224347059166375 54512137237692416 Bool.true

noncomputable abbrev qz164 := (@HMul.hMul Real Real Real qz267 qz453 qz604)

noncomputable def ep1001 := @Enclosure.Complex.IsNear.of_eq qz705 (Complex.mk (@HMul.hMul Real Real Real qz0 qz49 (Real.cos qz164)) (@HMul.hMul Real Real Real qz0 qz49 (@Neg.neg Real Real.instNeg (Real.sin qz164)))) Bool.true 26720324239 1099511627776 19157681088307 109024274475384832 Bool.true 132664208733 549755813888 9625356629787 54512137237692416 (BSN.cpow_neg_s_mk qz145 142522 1000 17 qz146 rfl)

noncomputable def ep1002 := @Enclosure.Real.IsNear.mulLit_ff qz145 qz604 142522 1000 0 1 3189913004350711 1125899906842624 125000000099157 24789250000000000000 227316390603036016571 562949953421312000 8907625007066026977 12394625000000000000000 qz147 (BSN.isNear_log_sfrac 17 1 3189913004350711 1125899906842624 125000000099157 24789250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz605) Bool.false 53517859495200818200576 18889465931478580854784 1000000000793256 198314000000000000000 3189913004350711 1125899906842624 125000000099157 24789250000000000000 (BSN.log_rat_reduce_isNear 17 1 4 34 32 31784 524288 24973259072661432 36028797018963968 198314 1000000000000000 rfl rfl rfl rfl (ep275 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1003 := BSN.sin_dyadic_bound_f 215540540 2147483648 1 0 1048576 397016 0 1 1 0 1 1 105067 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 215540540) qz20 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 215540540) qz21 0 0 rfl) rfl rfl

noncomputable abbrev qz470 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 105852443) qz24)

noncomputable def ep1004 := @Enclosure.Real.IsNear.cos_image qz164 qz470 Bool.false 105852443 262144 377 524288 Bool.true 105067 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz164 Bool.false 227316390603036016571 562949953421312000 8907625007066026977 12394625000000000000000 105852443 262144 377 524288 (ep1002 rfl) rfl) (Enclosure.sfrac_false_div 105852443 262144) (BSN.cos_reduce1 qz470 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 3791829287891848134656) qz291) 226375608064910080 72057594037927936 Bool.false 105067 1048576 64 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q1 105852443 262144 226375608064910080 72057594037927936 64 3791829287891848134656 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 105067 1048576 3791829287891848134656 37778931862957161709568 215540540 2147483648 397016 396628 (ep1003 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1005 := nat_lit 2158320154892469965302607270560000

noncomputable def ep1006 := BSN.cos_dyadic_bound_f 215540540 2147483648 2 1 1048576 397016 ep1005 ep66 ep1005 ep1005 ep67 ep1005 1043298 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 215540540) qz15 0 1 ep1005 ep66 ep1005 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 215540540) qz16 0 1 ep1005 ep67 ep1005 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1007 := @Enclosure.Real.IsNear.sin_image qz164 qz470 Bool.false 105852443 262144 377 524288 Bool.false 1043298 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz164 Bool.false 227316390603036016571 562949953421312000 8907625007066026977 12394625000000000000000 105852443 262144 377 524288 (ep1002 rfl) rfl) (Enclosure.sfrac_false_div 105852443 262144) (BSN.sin_reduce1 qz470 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 3791829287891848134656) qz291) 226375608064910080 72057594037927936 Bool.false 1043298 1048576 64 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q1 105852443 262144 226375608064910080 72057594037927936 64 3791829287891848134656 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1043298 1048576 3791829287891848134656 37778931862957161709568 215540540 2147483648 397016 396628 (ep1006 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1008 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz49 (Real.cos qz164)) (@HMul.hMul Real Real Real qz0 qz49 (@Neg.neg Real Real.instNeg (Real.sin qz164))) Bool.true 26720324239 1099511627776 19157681088307 109024274475384832 Bool.true 132664208733 549755813888 9625356629787 54512137237692416 (@Enclosure.Real.IsNear.mulLit_ft qz49 (Real.cos qz164) 254317 1048576 1 1048576 105067 1048576 37644333 51986825216 26720324239 1099511627776 19157681088307 109024274475384832 qz341 (@Enclosure.Real.IsNear.recentre' (Real.cos qz164) Bool.true 105067 1048576 75288666 103973650432 105067 1048576 37644333 51986825216 (ep1004 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz49 (@Neg.neg Real Real.instNeg (Real.sin qz164)) 254317 1048576 1 1048576 521649 524288 37644333 51986825216 132664208733 549755813888 9625356629787 54512137237692416 qz341 (@Enclosure.Real.IsNear.neg (Real.sin qz164) Bool.false 521649 524288 37644333 51986825216 (@Enclosure.Real.IsNear.recentre' (Real.sin qz164) Bool.false 1043298 1048576 75288666 103973650432 521649 524288 37644333 51986825216 (ep1007 rfl rfl) rfl)) rfl)

noncomputable def ep1009 := @ep1000 26720324239 1099511627776 19157681088307 109024274475384832 Bool.true 132664208733 549755813888 9625356629787 54512137237692416 Bool.false 784239225189107899564032 89157677529 137438953472 116946223234459 27256068618846208 Bool.true 41010382066318292549632 37298725207 274877906944 116986207898081 27256068618846208 EMRow49.d14 (ep1001 ep1008) rfl rfl

noncomputable abbrev qz165 := (@HMul.hMul Real Real Real qz267 qz453 qz607)

noncomputable def ep1010 := @Enclosure.Complex.IsNear.of_eq qz704 (Complex.mk (@HMul.hMul Real Real Real qz0 qz51 (Real.cos qz165)) (@HMul.hMul Real Real Real qz0 qz51 (@Neg.neg Real Real.instNeg (Real.sin qz165)))) Bool.true 59853299123 274877906944 4682075955685 27256068618846208 Bool.false 49606912965 549755813888 9336027912303 54512137237692416 (BSN.cpow_neg_s_mk qz145 142522 1000 18 qz146 rfl)

noncomputable def ep1011 := @Enclosure.Real.IsNear.mulLit_ff qz145 qz607 142522 1000 0 1 3254268794313975 1125899906842624 125000000099157 24789250000000000000 9276097942064326899 22517998136852480 8907625007066026977 12394625000000000000000 qz147 (BSN.isNear_log_sfrac 18 1 3254268794313975 1125899906842624 125000000099157 24789250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz608) Bool.false 54597570484265130393600 18889465931478580854784 1000000000793256 198314000000000000000 3254268794313975 1125899906842624 125000000099157 24789250000000000000 (BSN.log_rat_reduce_isNear 18 1 4 36 32 61752 524288 24973259072661432 36028797018963968 198314 1000000000000000 rfl rfl rfl rfl (ep289 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1012 := nat_lit 506617223925410821035485142473309761

noncomputable def ep1013 := BSN.cos_dyadic_bound_f 843664913 2147483648 2 1 1048576 397016 ep1012 ep66 ep1012 ep1012 ep67 ep1012 968692 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 843664913) qz15 0 1 ep1012 ep66 ep1012 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 843664913) qz16 0 1 ep1012 ep67 ep1012 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz471 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 215975985) qz17)

noncomputable def ep1014 := @Enclosure.Real.IsNear.cos_image qz165 qz471 Bool.false 215975985 524288 755 1048576 Bool.true 968692 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz165 Bool.false 9276097942064326899 22517998136852480 8907625007066026977 12394625000000000000000 215975985 524288 755 1048576 (ep1011 rfl) rfl) (Enclosure.sfrac_false_div 215975985 524288) (BSN.cos_reduce2 qz471 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 29683820245705755197440) qz19) 226375608064910080 72057594037927936 Bool.false 968692 1048576 65 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q2 215975985 524288 226375608064910080 72057594037927936 65 29683820245705755197440 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 968692 1048576 29683820245705755197440 75557863725914323419136 843664913 2147483648 397016 396628 (ep1013 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1015 := BSN.sin_dyadic_bound_f 843664913 2147483648 2 1 1048576 397016 ep1012 ep70 ep1012 ep1012 ep71 ep1012 401430 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 843664913) qz20 0 1 ep1012 ep70 ep1012 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 843664913) qz21 0 1 ep1012 ep71 ep1012 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1016 := @Enclosure.Real.IsNear.sin_image qz165 qz471 Bool.false 215975985 524288 755 1048576 Bool.true 401430 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz165 Bool.false 9276097942064326899 22517998136852480 8907625007066026977 12394625000000000000000 215975985 524288 755 1048576 (ep1011 rfl) rfl) (Enclosure.sfrac_false_div 215975985 524288) (BSN.sin_reduce2 qz471 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 29683820245705755197440) qz19) 226375608064910080 72057594037927936 Bool.false 401430 1048576 65 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q2 215975985 524288 226375608064910080 72057594037927936 65 29683820245705755197440 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 401430 1048576 29683820245705755197440 75557863725914323419136 843664913 2147483648 397016 396628 (ep1015 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1017 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz51 (Real.cos qz165)) (@HMul.hMul Real Real Real qz0 qz51 (@Neg.neg Real Real.instNeg (Real.sin qz165))) Bool.true 59853299123 274877906944 4682075955685 27256068618846208 Bool.false 49606912965 549755813888 9336027912303 54512137237692416 (@Enclosure.Real.IsNear.mulLit_ft qz51 (Real.cos qz165) 247151 1048576 1 1048576 242173 262144 75387823 103973650432 59853299123 274877906944 4682075955685 27256068618846208 qz343 (@Enclosure.Real.IsNear.recentre' (Real.cos qz165) Bool.true 968692 1048576 150775646 207947300864 242173 262144 75387823 103973650432 (ep1014 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz51 (@Neg.neg Real Real.instNeg (Real.sin qz165)) 247151 1048576 1 1048576 200715 524288 75387823 103973650432 49606912965 549755813888 9336027912303 54512137237692416 qz343 (@Enclosure.Real.IsNear.neg (Real.sin qz165) Bool.true 200715 524288 75387823 103973650432 (@Enclosure.Real.IsNear.recentre' (Real.sin qz165) Bool.true 401430 1048576 150775646 207947300864 200715 524288 75387823 103973650432 (ep1016 rfl rfl) rfl)) rfl)

noncomputable def ep1018 := @ep998 59853299123 274877906944 4682075955685 27256068618846208 Bool.false 49606912965 549755813888 9336027912303 54512137237692416 Bool.false 16281300993847926456320 118462055935 274877906944 950221087423 212938036084736 Bool.true 6869346627386769145856 24990537449 549755813888 243308443708465 54512137237692416 (ep999 (BSN.head_sum_c_succ qz142 17 18 rfl rfl) (ep1009 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1010 ep1017) rfl rfl

noncomputable abbrev qz166 := (@HMul.hMul Real Real Real qz267 qz453 qz610)

noncomputable def ep1019 := @Enclosure.Complex.IsNear.of_eq qz703 (Complex.mk (@HMul.hMul Real Real Real qz0 qz53 (Real.cos qz166)) (@HMul.hMul Real Real Real qz0 qz53 (@Neg.neg Real Real.instNeg (Real.sin qz166)))) Bool.false 30555563621 549755813888 9068315569463 54512137237692416 Bool.false 244729571383 1099511627776 18212317577869 109024274475384832 (BSN.cpow_neg_s_mk qz145 142522 1000 19 qz146 rfl)

noncomputable def ep1020 := @Enclosure.Real.IsNear.mulLit_ff qz145 qz610 142522 1000 0 1 3315143513283831 1125899906842624 125000000099157 24789250000000000000 236240441900119080891 562949953421312000 8907625007066026977 12394625000000000000000 qz147 (BSN.isNear_log_sfrac 19 1 3315143513283831 1125899906842624 125000000099157 24789250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz611) Bool.false 55618878793361701994496 18889465931478580854784 1000000000793256 198314000000000000000 3315143513283831 1125899906842624 125000000099157 24789250000000000000 (BSN.log_rat_reduce_isNear 19 1 4 38 32 90099 524288 24973259072661432 36028797018963968 198314 1000000000000000 rfl rfl rfl rfl (ep303 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1021 := nat_lit 76259336138439192949319403579494881

noncomputable def ep1022 := BSN.sin_dyadic_bound_f 525500647 2147483648 2 1 1048576 397016 ep1021 ep70 ep1021 ep1021 ep71 ep1021 254038 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 525500647) qz20 0 1 ep1021 ep70 ep1021 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 525500647) qz21 0 1 ep1021 ep71 ep1021 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz472 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 440032113) qz26)

noncomputable def ep1023 := @Enclosure.Real.IsNear.cos_image qz166 qz472 Bool.false 440032113 1048576 377 524288 Bool.false 254038 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz166 Bool.false 236240441900119080891 562949953421312000 8907625007066026977 12394625000000000000000 440032113 1048576 377 524288 (ep1020 rfl) rfl) (Enclosure.sfrac_false_div 440032113 1048576) (BSN.cos_reduce3 qz472 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 36978820604866043314176) qz27) 226375608064910080 72057594037927936 Bool.false 254038 1048576 66 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q3 440032113 1048576 226375608064910080 72057594037927936 66 36978820604866043314176 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 254038 1048576 36978820604866043314176 151115727451828646838272 525500647 2147483648 397016 396628 (ep1022 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1024 := BSN.cos_dyadic_bound_f 525500647 2147483648 2 1 1048576 397016 ep1021 ep66 ep1021 ep1021 ep67 ep1021 1017337 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 525500647) qz15 0 1 ep1021 ep66 ep1021 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 525500647) qz16 0 1 ep1021 ep67 ep1021 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1025 := @Enclosure.Real.IsNear.sin_image qz166 qz472 Bool.false 440032113 1048576 377 524288 Bool.true 1017337 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz166 Bool.false 236240441900119080891 562949953421312000 8907625007066026977 12394625000000000000000 440032113 1048576 377 524288 (ep1020 rfl) rfl) (Enclosure.sfrac_false_div 440032113 1048576) (BSN.sin_reduce3 qz472 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 36978820604866043314176) qz27) 226375608064910080 72057594037927936 Bool.false 1017337 1048576 66 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q3 440032113 1048576 226375608064910080 72057594037927936 66 36978820604866043314176 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1017337 1048576 36978820604866043314176 151115727451828646838272 525500647 2147483648 397016 396628 (ep1024 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1026 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz53 (Real.cos qz166)) (@HMul.hMul Real Real Real qz0 qz53 (@Neg.neg Real Real.instNeg (Real.sin qz166))) Bool.false 30555563621 549755813888 9068315569463 54512137237692416 Bool.false 244729571383 1099511627776 18212317577869 109024274475384832 (@Enclosure.Real.IsNear.mulLit_ff qz53 (Real.cos qz166) 240559 1048576 1 1048576 127019 524288 37644333 51986825216 30555563621 549755813888 9068315569463 54512137237692416 qz345 (@Enclosure.Real.IsNear.recentre' (Real.cos qz166) Bool.false 254038 1048576 75288666 103973650432 127019 524288 37644333 51986825216 (ep1023 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz53 (@Neg.neg Real Real.instNeg (Real.sin qz166)) 240559 1048576 1 1048576 1017337 1048576 37644333 51986825216 244729571383 1099511627776 18212317577869 109024274475384832 qz345 (@Enclosure.Real.IsNear.neg (Real.sin qz166) Bool.true 1017337 1048576 37644333 51986825216 (@Enclosure.Real.IsNear.recentre' (Real.sin qz166) Bool.true 1017337 1048576 75288666 103973650432 1017337 1048576 37644333 51986825216 (ep1025 rfl rfl) rfl)) rfl)

noncomputable def ep1027 := @ep996 30555563621 549755813888 9068315569463 54512137237692416 Bool.false 244729571383 1099511627776 18212317577869 109024274475384832 Bool.false 73524253349026415509504 267479675491 549755813888 252324913949751 54512137237692416 Bool.false 107064118188575482183680 194748496485 1099511627776 504829204994799 109024274475384832 (ep997 (BSN.head_sum_c_succ qz142 18 19 rfl rfl) (ep1018 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1019 ep1026) rfl rfl

noncomputable abbrev qz167 := (@HMul.hMul Real Real Real qz267 qz453 qz613)

noncomputable def ep1028 := @Enclosure.Complex.IsNear.of_eq qz702 (Complex.mk (@HMul.hMul Real Real Real qz0 qz55 (Real.cos qz167)) (@HMul.hMul Real Real Real qz0 qz55 (@Neg.neg Real Real.instNeg (Real.sin qz167)))) Bool.false 117475768601 549755813888 8876147291063 54512137237692416 Bool.false 72415985119 1099511627776 17683558255627 109024274475384832 (BSN.cpow_neg_s_mk qz145 142522 1000 20 qz146 rfl)

noncomputable def ep1029 := @Enclosure.Real.IsNear.mulLit_ff qz145 qz613 142522 1000 0 1 3372893643545847 1125899906842624 125000000099157 24789250000000000000 240355773932720603067 562949953421312000 8907625007066026977 12394625000000000000000 qz147 (BSN.isNear_log_sfrac 20 1 3372893643545847 1125899906842624 125000000099157 24789250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz614) Bool.false 56587765202795681021952 18889465931478580854784 1000000000793256 198314000000000000000 3372893643545847 1125899906842624 125000000099157 24789250000000000000 (BSN.log_rat_reduce_isNear 20 1 4 40 32 116991 524288 24973259072661432 36028797018963968 198314 1000000000000000 rfl rfl rfl rfl (ep314 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1030 := nat_lit 3581757054968676967215200189421336192137041822172155223134646738513587238764800

noncomputable def ep1031 := nat_lit 3096268188274884558578807768029709170488661171194100383876833223093633843456

noncomputable def ep1032 := nat_lit 9375779281184566053421158616860022878844794559030854183778750394698195932446976

noncomputable def ep1033 := BSN.sin_dyadic_bound_f 2731208286 2147483648 3 2 1048576 397016 ep1030 ep95 ep1031 ep1032 ep98 ep1031 1002058 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2731208286) qz20 0 2 ep1030 ep95 ep1031 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2731208286) qz21 0 2 ep1032 ep98 ep1031 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz473 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 111924379) qz24)

noncomputable def ep1034 := @Enclosure.Real.IsNear.cos_image qz167 qz473 Bool.false 111924379 262144 377 524288 Bool.false 1002058 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz167 Bool.false 240355773932720603067 562949953421312000 8907625007066026977 12394625000000000000000 111924379 262144 377 524288 (ep1029 rfl) rfl) (Enclosure.sfrac_false_div 111924379 262144) (BSN.cos_reduce3 qz473 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 48047924304502815981568) qz291) 226375608064910080 72057594037927936 Bool.false 1002058 1048576 67 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q3 111924379 262144 226375608064910080 72057594037927936 67 48047924304502815981568 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1002058 1048576 48047924304502815981568 37778931862957161709568 2731208286 2147483648 397016 396628 (ep1033 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1035 := nat_lit 1991241149732942708256701797575422199707462639505061390800971225051145636577536

noncomputable def ep1036 := nat_lit 5967530912822278355652947777190207180781410596172795971635160008707249642045696

noncomputable def ep1037 := BSN.cos_dyadic_bound_f 2731208286 2147483648 3 2 1048576 397016 ep1035 ep102 ep1031 ep1036 ep104 ep1031 308851 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2731208286) qz15 0 2 ep1035 ep102 ep1031 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2731208286) qz16 0 2 ep1036 ep104 ep1031 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1038 := @Enclosure.Real.IsNear.sin_image qz167 qz473 Bool.false 111924379 262144 377 524288 Bool.true 308851 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz167 Bool.false 240355773932720603067 562949953421312000 8907625007066026977 12394625000000000000000 111924379 262144 377 524288 (ep1029 rfl) rfl) (Enclosure.sfrac_false_div 111924379 262144) (BSN.sin_reduce3 qz473 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 48047924304502815981568) qz291) 226375608064910080 72057594037927936 Bool.false 308851 1048576 67 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q3 111924379 262144 226375608064910080 72057594037927936 67 48047924304502815981568 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 308851 1048576 48047924304502815981568 37778931862957161709568 2731208286 2147483648 397016 396628 (ep1037 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1039 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz55 (Real.cos qz167)) (@HMul.hMul Real Real Real qz0 qz55 (@Neg.neg Real Real.instNeg (Real.sin qz167))) Bool.false 117475768601 549755813888 8876147291063 54512137237692416 Bool.false 72415985119 1099511627776 17683558255627 109024274475384832 (@Enclosure.Real.IsNear.mulLit_ff qz55 (Real.cos qz167) 234469 1048576 1 1048576 501029 524288 37644333 51986825216 117475768601 549755813888 8876147291063 54512137237692416 qz347 (@Enclosure.Real.IsNear.recentre' (Real.cos qz167) Bool.false 1002058 1048576 75288666 103973650432 501029 524288 37644333 51986825216 (ep1034 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz55 (@Neg.neg Real Real.instNeg (Real.sin qz167)) 234469 1048576 1 1048576 308851 1048576 37644333 51986825216 72415985119 1099511627776 17683558255627 109024274475384832 qz347 (@Enclosure.Real.IsNear.neg (Real.sin qz167) Bool.true 308851 1048576 37644333 51986825216 (@Enclosure.Real.IsNear.recentre' (Real.sin qz167) Bool.true 308851 1048576 75288666 103973650432 308851 1048576 37644333 51986825216 (ep1038 rfl rfl) rfl)) rfl)

noncomputable def ep1040 := @ep994 117475768601 549755813888 8876147291063 54512137237692416 Bool.false 72415985119 1099511627776 17683558255627 109024274475384832 Bool.false 211631493477413941149696 96238861023 137438953472 130600530620407 27256068618846208 Bool.false 293750454052345247432704 66791120401 274877906944 261256381625213 54512137237692416 (ep995 (BSN.head_sum_c_succ qz142 19 20 rfl rfl) (ep1027 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1028 ep1039) rfl rfl

noncomputable abbrev qz168 := (@HMul.hMul Real Real Real qz267 qz453 qz616)

noncomputable def ep1041 := @Enclosure.Complex.IsNear.of_eq qz701 (Complex.mk (@HMul.hMul Real Real Real qz0 qz57 (Real.cos qz168)) (@HMul.hMul Real Real Real qz0 qz57 (@Neg.neg Real Real.instNeg (Real.sin qz168)))) Bool.false 111783656677 549755813888 8722002473751 54512137237692416 Bool.true 10886817213 137438953472 4331431380013 27256068618846208 (BSN.cpow_neg_s_mk qz145 142522 1000 21 qz146 rfl)

noncomputable def ep1042 := @Enclosure.Real.IsNear.mulLit_ff qz145 qz616 142522 1000 0 1 3427826275261687 1125899906842624 125000000099157 24789250000000000000 244270328201423077307 562949953421312000 8907625007066026977 12394625000000000000000 qz147 (BSN.isNear_log_sfrac 21 1 3427826275261687 1125899906842624 125000000099157 24789250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz617) Bool.false 57509381830540779323392 18889465931478580854784 1000000000793256 198314000000000000000 3427826275261687 1125899906842624 125000000099157 24789250000000000000 (BSN.log_rat_reduce_isNear 21 1 4 42 32 142571 524288 24973259072661432 36028797018963968 198314 1000000000000000 rfl rfl rfl rfl (ep329 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1043 := nat_lit 405010499884378325956314904338900625

noncomputable def ep1044 := BSN.cos_dyadic_bound_f 797749555 2147483648 2 1 1048576 397016 ep1043 ep66 ep1043 ep1043 ep67 ep1043 977053 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 797749555) qz15 0 1 ep1043 ep66 ep1043 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 797749555) qz16 0 1 ep1043 ep67 ep1043 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz474 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 454988941) qz26)

noncomputable def ep1045 := @Enclosure.Real.IsNear.cos_image qz168 qz474 Bool.false 454988941 1048576 755 1048576 Bool.false 977053 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz168 Bool.false 244270328201423077307 562949953421312000 8907625007066026977 12394625000000000000000 454988941 1048576 755 1048576 (ep1042 rfl) rfl) (Enclosure.sfrac_false_div 454988941 1048576) (BSN.cos_reduce0 qz474 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 56136634422652905193472) qz27) 226375608064910080 72057594037927936 Bool.false 977053 1048576 69 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q0 454988941 1048576 226375608064910080 72057594037927936 69 56136634422652905193472 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 977053 1048576 56136634422652905193472 151115727451828646838272 797749555 2147483648 397016 396628 (ep1044 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1046 := BSN.sin_dyadic_bound_f 797749555 2147483648 2 1 1048576 397016 ep1043 ep70 ep1043 ep1043 ep71 ep1043 380628 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 797749555) qz20 0 1 ep1043 ep70 ep1043 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 797749555) qz21 0 1 ep1043 ep71 ep1043 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1047 := @Enclosure.Real.IsNear.sin_image qz168 qz474 Bool.false 454988941 1048576 755 1048576 Bool.false 380628 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz168 Bool.false 244270328201423077307 562949953421312000 8907625007066026977 12394625000000000000000 454988941 1048576 755 1048576 (ep1042 rfl) rfl) (Enclosure.sfrac_false_div 454988941 1048576) (BSN.sin_reduce0 qz474 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 56136634422652905193472) qz27) 226375608064910080 72057594037927936 Bool.false 380628 1048576 69 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q0 454988941 1048576 226375608064910080 72057594037927936 69 56136634422652905193472 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 380628 1048576 56136634422652905193472 151115727451828646838272 797749555 2147483648 397016 396628 (ep1046 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1048 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz57 (Real.cos qz168)) (@HMul.hMul Real Real Real qz0 qz57 (@Neg.neg Real Real.instNeg (Real.sin qz168))) Bool.false 111783656677 549755813888 8722002473751 54512137237692416 Bool.true 10886817213 137438953472 4331431380013 27256068618846208 (@Enclosure.Real.IsNear.mulLit_ff qz57 (Real.cos qz168) 114409 524288 1 524288 977053 1048576 75387823 103973650432 111783656677 549755813888 8722002473751 54512137237692416 qz349 (@Enclosure.Real.IsNear.recentre' (Real.cos qz168) Bool.false 977053 1048576 150775646 207947300864 977053 1048576 75387823 103973650432 (ep1045 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz57 (@Neg.neg Real Real.instNeg (Real.sin qz168)) 114409 524288 1 524288 95157 262144 75387823 103973650432 10886817213 137438953472 4331431380013 27256068618846208 qz349 (@Enclosure.Real.IsNear.neg (Real.sin qz168) Bool.false 95157 262144 75387823 103973650432 (@Enclosure.Real.IsNear.recentre' (Real.sin qz168) Bool.false 380628 1048576 150775646 207947300864 95157 262144 75387823 103973650432 (ep1047 rfl rfl) rfl)) rfl)

noncomputable def ep1049 := @ep992 111783656677 549755813888 8722002473751 54512137237692416 Bool.true 10886817213 137438953472 4331431380013 27256068618846208 Bool.false 68271302158313710419968 496739100769 549755813888 269923063714565 54512137237692416 Bool.false 6187156160344437555200 45017485975 274877906944 269919244385239 54512137237692416 (ep993 (BSN.head_sum_c_succ qz142 20 21 rfl rfl) (ep1040 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1041 ep1048) rfl rfl

noncomputable abbrev qz169 := (@HMul.hMul Real Real Real qz267 qz453 qz619)

noncomputable def ep1050 := @Enclosure.Complex.IsNear.of_eq qz700 (Complex.mk (@HMul.hMul Real Real Real qz0 qz59 (Real.cos qz169)) (@HMul.hMul Real Real Real qz0 qz59 (@Neg.neg Real Real.instNeg (Real.sin qz169)))) Bool.false 176474330901 1099511627776 16909657435329 109024274475384832 Bool.true 77148850029 549755813888 8449910580043 54512137237692416 (BSN.cpow_neg_s_mk qz145 142522 1000 22 qz146 rfl)

noncomputable def ep1051 := @Enclosure.Real.IsNear.mulLit_ff qz145 qz619 142522 1000 0 1 3480203401436407 1125899906842624 125000000099157 24789250000000000000 248002774589759799227 562949953421312000 8907625007066026977 12394625000000000000000 qz147 (BSN.isNear_log_sfrac 22 1 3480203401436407 1125899906842624 125000000099157 24789250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz620) Bool.false 58388124189833310502912 18889465931478580854784 1000000000793256 198314000000000000000 3480203401436407 1125899906842624 125000000099157 24789250000000000000 (BSN.log_rat_reduce_isNear 22 1 4 44 32 166961 524288 24973259072661432 36028797018963968 198314 1000000000000000 rfl rfl rfl rfl (ep340 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1052 := nat_lit 202493519240612939379880550718483362927083458491092318899739158872961409657441

noncomputable def ep1053 := nat_lit 32109018249821462912382914595940460284400505227153885251663832164132760161

noncomputable def ep1054 := nat_lit 607416339685339175213816886326258207860681574462822648928714148954555963452001

noncomputable def ep1055 := BSN.cos_dyadic_bound_f 1542866603 2147483648 3 2 1048576 397016 ep1052 ep102 ep1053 ep1054 ep104 ep1053 789393 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1542866603) qz15 0 2 ep1052 ep102 ep1053 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1542866603) qz16 0 2 ep1054 ep104 ep1053 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz475 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 461941165) qz26)

noncomputable def ep1056 := @Enclosure.Real.IsNear.cos_image qz169 qz475 Bool.false 461941165 1048576 377 524288 Bool.false 789393 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz169 Bool.false 248002774589759799227 562949953421312000 8907625007066026977 12394625000000000000000 461941165 1048576 377 524288 (ep1051 rfl) rfl) (Enclosure.sfrac_false_div 461941165 1048576) (BSN.cos_reduce0 qz475 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 108569585319047310868480) qz27) 226375608064910080 72057594037927936 Bool.false 789393 1048576 70 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q0 461941165 1048576 226375608064910080 72057594037927936 70 108569585319047310868480 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 789393 1048576 108569585319047310868480 151115727451828646838272 1542866603 2147483648 397016 396628 (ep1055 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1057 := nat_lit 5666481999426228029318164279141832881

noncomputable def ep1058 := BSN.sin_dyadic_bound_f 1542866603 2147483648 2 1 1048576 397016 ep1057 ep70 ep1057 ep1057 ep71 ep1057 690194 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1542866603) qz20 0 1 ep1057 ep70 ep1057 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1542866603) qz21 0 1 ep1057 ep71 ep1057 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1059 := @Enclosure.Real.IsNear.sin_image qz169 qz475 Bool.false 461941165 1048576 377 524288 Bool.false 690194 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz169 Bool.false 248002774589759799227 562949953421312000 8907625007066026977 12394625000000000000000 461941165 1048576 377 524288 (ep1051 rfl) rfl) (Enclosure.sfrac_false_div 461941165 1048576) (BSN.sin_reduce0 qz475 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 108569585319047310868480) qz27) 226375608064910080 72057594037927936 Bool.false 690194 1048576 70 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q0 461941165 1048576 226375608064910080 72057594037927936 70 108569585319047310868480 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 690194 1048576 108569585319047310868480 151115727451828646838272 1542866603 2147483648 397016 396628 (ep1058 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1060 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz59 (Real.cos qz169)) (@HMul.hMul Real Real Real qz0 qz59 (@Neg.neg Real Real.instNeg (Real.sin qz169))) Bool.false 176474330901 1099511627776 16909657435329 109024274475384832 Bool.true 77148850029 549755813888 8449910580043 54512137237692416 (@Enclosure.Real.IsNear.mulLit_ff qz59 (Real.cos qz169) 223557 1048576 1 1048576 789393 1048576 37644333 51986825216 176474330901 1099511627776 16909657435329 109024274475384832 qz351 (@Enclosure.Real.IsNear.recentre' (Real.cos qz169) Bool.false 789393 1048576 75288666 103973650432 789393 1048576 37644333 51986825216 (ep1056 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz59 (@Neg.neg Real Real.instNeg (Real.sin qz169)) 223557 1048576 1 1048576 345097 524288 37644333 51986825216 77148850029 549755813888 8449910580043 54512137237692416 qz351 (@Enclosure.Real.IsNear.neg (Real.sin qz169) Bool.false 345097 524288 37644333 51986825216 (@Enclosure.Real.IsNear.recentre' (Real.sin qz169) Bool.false 690194 1048576 75288666 103973650432 345097 524288 37644333 51986825216 (ep1059 rfl rfl) rfl)) rfl)

noncomputable def ep1061 := @ep990 176474330901 1099511627776 16909657435329 109024274475384832 Bool.true 77148850029 549755813888 8449910580043 54512137237692416 Bool.false 643188206681329166712832 1169952532439 1099511627776 556755784864459 109024274475384832 Bool.false 3542110222269676519424 12886121921 549755813888 139184577482641 27256068618846208 (ep991 (BSN.head_sum_c_succ qz142 21 22 rfl rfl) (ep1049 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1050 ep1060) rfl rfl

noncomputable abbrev qz170 := (@HMul.hMul Real Real Real qz267 qz453 qz623)

noncomputable def ep1062 := @Enclosure.Complex.IsNear.of_eq qz699 (Complex.mk (@HMul.hMul Real Real Real qz0 qz61 (Real.cos qz170)) (@HMul.hMul Real Real Real qz0 qz61 (@Neg.neg Real Real.instNeg (Real.sin qz170)))) Bool.false 82257213531 549755813888 8278852135075 54512137237692416 Bool.true 79838584665 549755813888 8277755260341 54512137237692416 (BSN.cpow_neg_s_mk qz145 142522 1000 23 qz146 rfl)

noncomputable def ep1063 := @Enclosure.Real.IsNear.mulLit_ff qz145 qz623 142522 1000 0 1 3530250507853047 1125899906842624 125000000099157 24789250000000000000 251569181440115982267 562949953421312000 8907625007066026977 12394625000000000000000 qz147 (BSN.isNear_log_sfrac 23 1 3530250507853047 1125899906842624 125000000099157 24789250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz624) Bool.false 59227775304360265777152 18889465931478580854784 1000000000793256 198314000000000000000 3530250507853047 1125899906842624 125000000099157 24789250000000000000 (BSN.log_rat_reduce_isNear 23 1 4 46 32 190266 524288 24973259072661432 36028797018963968 198314 1000000000000000 rfl rfl rfl rfl (ep354 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1064 := nat_lit 267844009820855243996625627069548054544388868483173976599858871863205042094336

noncomputable def ep1065 := nat_lit 56172558786782713770371423353883878346421702342837898382176221382627328256

noncomputable def ep1066 := nat_lit 803419684344992166562336138361936395876473762044836254002812263146849871626496

noncomputable def ep1067 := BSN.cos_dyadic_bound_f 1654590498 2147483648 3 2 1048576 397016 ep1064 ep102 ep1065 ep1066 ep104 ep1065 752434 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1654590498) qz15 0 2 ep1064 ep102 ep1065 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1654590498) qz16 0 2 ep1066 ep104 ep1065 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz476 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 468584115) qz26)

noncomputable def ep1068 := @Enclosure.Real.IsNear.cos_image qz170 qz476 Bool.false 468584115 1048576 755 1048576 Bool.false 752434 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz170 Bool.false 251569181440115982267 562949953421312000 8907625007066026977 12394625000000000000000 468584115 1048576 755 1048576 (ep1063 rfl) rfl) (Enclosure.sfrac_false_div 468584115 1048576) (BSN.cos_reduce0 qz476 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 116431455538469467586560) qz27) 226375608064910080 72057594037927936 Bool.false 752434 1048576 71 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q0 468584115 1048576 226375608064910080 72057594037927936 71 116431455538469467586560 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 752434 1048576 116431455538469467586560 151115727451828646838272 1654590498 2147483648 397016 396628 (ep1067 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1069 := nat_lit 7494835474297131878994141613119104016

noncomputable def ep1070 := BSN.sin_dyadic_bound_f 1654590498 2147483648 2 1 1048576 397016 ep1069 ep70 ep1069 ep1069 ep71 ep1069 730310 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1654590498) qz20 0 1 ep1069 ep70 ep1069 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1654590498) qz21 0 1 ep1069 ep71 ep1069 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1071 := @Enclosure.Real.IsNear.sin_image qz170 qz476 Bool.false 468584115 1048576 755 1048576 Bool.false 730310 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz170 Bool.false 251569181440115982267 562949953421312000 8907625007066026977 12394625000000000000000 468584115 1048576 755 1048576 (ep1063 rfl) rfl) (Enclosure.sfrac_false_div 468584115 1048576) (BSN.sin_reduce0 qz476 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 116431455538469467586560) qz27) 226375608064910080 72057594037927936 Bool.false 730310 1048576 71 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q0 468584115 1048576 226375608064910080 72057594037927936 71 116431455538469467586560 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 730310 1048576 116431455538469467586560 151115727451828646838272 1654590498 2147483648 397016 396628 (ep1070 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1072 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz61 (Real.cos qz170)) (@HMul.hMul Real Real Real qz0 qz61 (@Neg.neg Real Real.instNeg (Real.sin qz170))) Bool.false 82257213531 549755813888 8278852135075 54512137237692416 Bool.true 79838584665 549755813888 8277755260341 54512137237692416 (@Enclosure.Real.IsNear.mulLit_ff qz61 (Real.cos qz170) 218643 1048576 1 1048576 376217 524288 75387823 103973650432 82257213531 549755813888 8278852135075 54512137237692416 qz353 (@Enclosure.Real.IsNear.recentre' (Real.cos qz170) Bool.false 752434 1048576 150775646 207947300864 376217 524288 75387823 103973650432 (ep1068 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz61 (@Neg.neg Real Real.instNeg (Real.sin qz170)) 218643 1048576 1 1048576 365155 524288 75387823 103973650432 79838584665 549755813888 8277755260341 54512137237692416 qz353 (@Enclosure.Real.IsNear.neg (Real.sin qz170) Bool.false 365155 524288 75387823 103973650432 (@Enclosure.Real.IsNear.recentre' (Real.sin qz170) Bool.false 730310 1048576 150775646 207947300864 365155 524288 75387823 103973650432 (ep1071 rfl rfl) rfl)) rfl)

noncomputable def ep1073 := @ep988 82257213531 549755813888 8278852135075 54512137237692416 Bool.true 79838584665 549755813888 8277755260341 54512137237692416 Bool.false 733630969427116989349888 1334466959501 1099511627776 573313489134609 109024274475384832 Bool.true 36807505647633717788672 8369057843 68719476736 286646910225623 54512137237692416 (ep989 (BSN.head_sum_c_succ qz142 22 23 rfl rfl) (ep1061 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1062 ep1072) rfl rfl

noncomputable abbrev qz171 := (@HMul.hMul Real Real Real qz267 qz453 qz626)

noncomputable def ep1074 := @Enclosure.Complex.IsNear.of_eq qz698 (Complex.mk (@HMul.hMul Real Real Real qz0 qz63 (Real.cos qz171)) (@HMul.hMul Real Real Real qz0 qz63 (@Neg.neg Real Real.instNeg (Real.sin qz171)))) Bool.false 95485580407 549755813888 8101628262061 54512137237692416 Bool.true 14738083423 137438953472 2021175912379 13628034309423104 (BSN.cpow_neg_s_mk qz145 142522 1000 24 qz146 rfl)

noncomputable def ep1075 := @Enclosure.Real.IsNear.mulLit_ff qz145 qz626 142522 1000 0 1 3578169457974519 1125899906842624 125000000099157 24789250000000000000 254983933744722198459 562949953421312000 8907625007066026977 12394625000000000000000 qz147 (BSN.isNear_log_sfrac 24 1 3578169457974519 1125899906842624 125000000099157 24789250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz627) Bool.false 60031721881041427759104 18889465931478580854784 1000000000793256 198314000000000000000 3578169457974519 1125899906842624 125000000099157 24789250000000000000 (BSN.log_rat_reduce_isNear 24 1 4 48 32 212580 524288 24973259072661432 36028797018963968 198314 1000000000000000 rfl rfl rfl rfl (ep368 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1076 := nat_lit 1990547196859488391754119191506250000

noncomputable def ep1077 := BSN.cos_dyadic_bound_f 1187799450 2147483648 2 1 1048576 397016 ep1076 ep66 ep1076 ep1076 ep67 ep1076 892226 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1187799450) qz15 0 1 ep1076 ep66 ep1076 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1187799450) qz16 0 1 ep1076 ep67 ep1076 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz477 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 474944587) qz26)

noncomputable def ep1078 := @Enclosure.Real.IsNear.cos_image qz171 qz477 Bool.false 474944587 1048576 377 524288 Bool.false 892226 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz171 Bool.false 254983933744722198459 562949953421312000 8907625007066026977 12394625000000000000000 474944587 1048576 377 524288 (ep1075 rfl) rfl) (Enclosure.sfrac_false_div 474944587 1048576) (BSN.cos_reduce0 qz477 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 83583955660600009293824) qz27) 226375608064910080 72057594037927936 Bool.false 892226 1048576 72 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q0 474944587 1048576 226375608064910080 72057594037927936 72 83583955660600009293824 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 892226 1048576 83583955660600009293824 151115727451828646838272 1187799450 2147483648 397016 396628 (ep1077 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1079 := BSN.sin_dyadic_bound_f 1187799450 2147483648 2 1 1048576 397016 ep1076 ep70 ep1076 ep1076 ep71 ep1076 550856 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1187799450) qz20 0 1 ep1076 ep70 ep1076 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1187799450) qz21 0 1 ep1076 ep71 ep1076 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1080 := @Enclosure.Real.IsNear.sin_image qz171 qz477 Bool.false 474944587 1048576 377 524288 Bool.false 550856 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz171 Bool.false 254983933744722198459 562949953421312000 8907625007066026977 12394625000000000000000 474944587 1048576 377 524288 (ep1075 rfl) rfl) (Enclosure.sfrac_false_div 474944587 1048576) (BSN.sin_reduce0 qz477 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 83583955660600009293824) qz27) 226375608064910080 72057594037927936 Bool.false 550856 1048576 72 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q0 474944587 1048576 226375608064910080 72057594037927936 72 83583955660600009293824 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 550856 1048576 83583955660600009293824 151115727451828646838272 1187799450 2147483648 397016 396628 (ep1079 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1081 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz63 (Real.cos qz171)) (@HMul.hMul Real Real Real qz0 qz63 (@Neg.neg Real Real.instNeg (Real.sin qz171))) Bool.false 95485580407 549755813888 8101628262061 54512137237692416 Bool.true 14738083423 137438953472 2021175912379 13628034309423104 (@Enclosure.Real.IsNear.mulLit_ff qz63 (Real.cos qz171) 214039 1048576 1 1048576 446113 524288 37644333 51986825216 95485580407 549755813888 8101628262061 54512137237692416 qz355 (@Enclosure.Real.IsNear.recentre' (Real.cos qz171) Bool.false 892226 1048576 75288666 103973650432 446113 524288 37644333 51986825216 (ep1078 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz63 (@Neg.neg Real Real.instNeg (Real.sin qz171)) 214039 1048576 1 1048576 68857 131072 37644333 51986825216 14738083423 137438953472 2021175912379 13628034309423104 qz355 (@Enclosure.Real.IsNear.neg (Real.sin qz171) Bool.false 68857 131072 37644333 51986825216 (@Enclosure.Real.IsNear.recentre' (Real.sin qz171) Bool.false 550856 1048576 75288666 103973650432 68857 131072 37644333 51986825216 (ep1080 rfl rfl) rfl)) rfl)

noncomputable def ep1082 := @ep986 95485580407 549755813888 8101628262061 54512137237692416 Bool.true 14738083423 137438953472 2021175912379 13628034309423104 Bool.false 838618475369553691934720 1525438120315 1099511627776 589516745658731 109024274475384832 Bool.true 2163027932408629428224 31476199109 137438953472 294731613875139 54512137237692416 (ep987 (BSN.head_sum_c_succ qz142 23 24 rfl rfl) (ep1073 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1074 ep1081) rfl rfl

theorem EMRow49.d15 : Enclosure.Complex.IsNear qz163 Bool.false 1525438120315 1099511627776 589516745658731 109024274475384832 Bool.true 31476199109 137438953472 294731613875139 54512137237692416 := ep985 (BSN.head_sum_c_succ qz142 24 25 rfl rfl) (ep1082 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable abbrev qz172 := (BSN.headSumC qz451 33)

noncomputable abbrev qz706 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 32) qz143)

noncomputable def ep1083 := @Enclosure.Complex.IsNear.of_eq qz172 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz142 32) qz706) Bool.false 866239839741 549755813888 354375500489335 54512137237692416 Bool.false 116724576395 1099511627776 708627207727921 109024274475384832

noncomputable def ep1084 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz142 32) qz706 Bool.false 469856920159 274877906944 86839573148655 13628034309423104 Bool.true 10495240669 1099511627776 694603345218001 109024274475384832 Bool.true

noncomputable abbrev qz707 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 31) qz143)

noncomputable def ep1085 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz142 32) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz142 31) qz707) Bool.false 469856920159 274877906944 86839573148655 13628034309423104 Bool.true 10495240669 1099511627776 694603345218001 109024274475384832

noncomputable def ep1086 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz142 31) qz707 Bool.false 1724617287727 1099511627776 680455961585163 109024274475384832 Bool.true 66548050683 549755813888 85044960029665 13628034309423104 Bool.false

noncomputable def ep1087 := nat_lit 2066452588423360634945536

noncomputable abbrev qz708 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 30) qz143)

noncomputable def ep1088 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz142 31) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz142 30) qz708) Bool.false 1724617287727 1099511627776 680455961585163 109024274475384832 Bool.true 66548050683 549755813888 85044960029665 13628034309423104

noncomputable def ep1089 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz142 30) qz708 Bool.false 1606208643569 1099511627776 665962085999309 109024274475384832 Bool.false 29005387239 1099511627776 665843174148513 109024274475384832 Bool.false

noncomputable abbrev qz709 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 29) qz143)

noncomputable def ep1090 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz142 30) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz142 29) qz709) Bool.false 1606208643569 1099511627776 665962085999309 109024274475384832 Bool.false 29005387239 1099511627776 665843174148513 109024274475384832

noncomputable def ep1091 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz142 29) qz709 Bool.false 109723614389 68719476736 81400850704459 13628034309423104 Bool.false 42050373501 274877906944 325546537170749 54512137237692416 Bool.true

noncomputable abbrev qz710 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 28) qz143)

noncomputable def ep1092 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz142 29) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz142 28) qz710) Bool.false 109723614389 68719476736 81400850704459 13628034309423104 Bool.false 42050373501 274877906944 325546537170749 54512137237692416

noncomputable def ep1093 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz142 28) qz710 Bool.false 1934677351461 1099511627776 636197684429005 109024274475384832 Bool.false 62847144239 1099511627776 636120853817439 109024274475384832 Bool.true

noncomputable def ep1094 := nat_lit 1930278237797048410701824

noncomputable abbrev qz711 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 27) qz143)

noncomputable def ep1095 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz142 28) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz142 27) qz711) Bool.false 1934677351461 1099511627776 636197684429005 109024274475384832 Bool.false 62847144239 1099511627776 636120853817439 109024274475384832

noncomputable def ep1096 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz142 27) qz711 Bool.false 1921785624145 1099511627776 620998097084417 109024274475384832 Bool.true 74180568867 549755813888 38801488789075 6814017154711552 Bool.false

noncomputable abbrev qz712 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 26) qz143)

noncomputable def ep1097 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz142 27) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz142 26) qz712) Bool.false 1921785624145 1099511627776 620998097084417 109024274475384832 Bool.true 74180568867 549755813888 38801488789075 6814017154711552

noncomputable def ep1098 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz142 26) qz712 Bool.false 1744492568125 1099511627776 605409556395425 109024274475384832 Bool.true 2117955779 8589934592 302630792846683 54512137237692416 Bool.false

noncomputable abbrev qz713 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 25) qz143)

noncomputable def ep1099 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz142 26) (@HAdd.hAdd Complex Complex Complex qz4 qz163 qz713) Bool.false 1744492568125 1099511627776 605409556395425 109024274475384832 Bool.true 2117955779 8589934592 302630792846683 54512137237692416

noncomputable def ep1100 := @Enclosure.Complex.IsNear.addLitP qz163 qz713 Bool.false 1525438120315 1099511627776 589516745658731 109024274475384832 Bool.true 31476199109 137438953472 294731613875139 54512137237692416 Bool.false

noncomputable abbrev qz173 := (@HMul.hMul Real Real Real qz267 qz453 qz636)

noncomputable def ep1101 := @Enclosure.Complex.IsNear.of_eq qz713 (Complex.mk (@HMul.hMul Real Real Real qz0 qz356 (Real.cos qz173)) (@HMul.hMul Real Real Real qz0 qz356 (@Neg.neg Real Real.instNeg (Real.sin qz173)))) Bool.false 109527223905 549755813888 7946405368347 54512137237692416 Bool.true 2411093355 137438953472 987397371443 6814017154711552 (BSN.cpow_neg_s_mk qz145 142522 1000 25 qz146 rfl)

noncomputable def ep1102 := @Enclosure.Real.IsNear.mulLit_ff qz145 qz636 142522 1000 0 1 3624129903009015 1125899906842624 125000000099157 24789250000000000000 51651824203665083583 112589990684262400 8907625007066026977 12394625000000000000000 qz147 (BSN.isNear_log_sfrac 25 1 3624129903009015 1125899906842624 125000000099157 24789250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz637) Bool.false 60802810194841294602240 18889465931478580854784 1000000000793256 198314000000000000000 3624129903009015 1125899906842624 125000000099157 24789250000000000000 (BSN.log_rat_reduce_isNear 25 1 4 50 32 233982 524288 24973259072661432 36028797018963968 198314 1000000000000000 rfl rfl rfl rfl (ep395 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1103 := nat_lit 1265499030621672765733886122287681

noncomputable def ep1104 := BSN.cos_dyadic_bound_f 188610321 2147483648 2 1 1048576 397016 ep1103 ep66 ep1103 ep1103 ep67 ep1103 1044534 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 188610321) qz15 0 1 ep1103 ep66 ep1103 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 188610321) qz16 0 1 ep1103 ep67 ep1103 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz478 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 481045099) qz26)

noncomputable def ep1105 := @Enclosure.Real.IsNear.cos_image qz173 qz478 Bool.false 481045099 1048576 377 524288 Bool.false 1044534 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz173 Bool.false 51651824203665083583 112589990684262400 8907625007066026977 12394625000000000000000 481045099 1048576 377 524288 (ep1102 rfl) rfl) (Enclosure.sfrac_false_div 481045099 1048576) (BSN.cos_reduce0 qz478 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 13272271490531058515968) qz27) 226375608064910080 72057594037927936 Bool.false 1044534 1048576 73 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q0 481045099 1048576 226375608064910080 72057594037927936 73 13272271490531058515968 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1044534 1048576 13272271490531058515968 151115727451828646838272 188610321 2147483648 397016 396628 (ep1104 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1106 := BSN.sin_dyadic_bound_f 188610321 2147483648 1 0 1048576 397016 0 1 1 0 1 1 91976 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 188610321) qz20 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 188610321) qz21 0 0 rfl) rfl rfl

noncomputable def ep1107 := @Enclosure.Real.IsNear.sin_image qz173 qz478 Bool.false 481045099 1048576 377 524288 Bool.false 91976 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz173 Bool.false 51651824203665083583 112589990684262400 8907625007066026977 12394625000000000000000 481045099 1048576 377 524288 (ep1102 rfl) rfl) (Enclosure.sfrac_false_div 481045099 1048576) (BSN.sin_reduce0 qz478 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 13272271490531058515968) qz27) 226375608064910080 72057594037927936 Bool.false 91976 1048576 73 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q0 481045099 1048576 226375608064910080 72057594037927936 73 13272271490531058515968 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 91976 1048576 13272271490531058515968 151115727451828646838272 188610321 2147483648 397016 396628 (ep1106 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1108 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz356 (Real.cos qz173)) (@HMul.hMul Real Real Real qz0 qz356 (@Neg.neg Real Real.instNeg (Real.sin qz173))) Bool.false 109527223905 549755813888 7946405368347 54512137237692416 Bool.true 2411093355 137438953472 987397371443 6814017154711552 (@Enclosure.Real.IsNear.mulLit_ff qz356 (Real.cos qz173) 209715 1048576 1 1048576 522267 524288 37644333 51986825216 109527223905 549755813888 7946405368347 54512137237692416 qz360 (@Enclosure.Real.IsNear.recentre' (Real.cos qz173) Bool.false 1044534 1048576 75288666 103973650432 522267 524288 37644333 51986825216 (ep1105 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz356 (@Neg.neg Real Real.instNeg (Real.sin qz173)) 209715 1048576 1 1048576 11497 131072 37644333 51986825216 2411093355 137438953472 987397371443 6814017154711552 qz360 (@Enclosure.Real.IsNear.neg (Real.sin qz173) Bool.false 11497 131072 37644333 51986825216 (@Enclosure.Real.IsNear.recentre' (Real.sin qz173) Bool.false 91976 1048576 75288666 103973650432 11497 131072 37644333 51986825216 (ep1107 rfl rfl) rfl)) rfl)

noncomputable def ep1109 := @ep1100 109527223905 549755813888 7946405368347 54512137237692416 Bool.true 2411093355 137438953472 987397371443 6814017154711552 Bool.false 959044931611126661120000 1744492568125 1099511627776 605409556395425 109024274475384832 Bool.true 4657434012251752235008 2117955779 8589934592 302630792846683 54512137237692416 EMRow49.d15 (ep1101 ep1108) rfl rfl

noncomputable abbrev qz174 := (@HMul.hMul Real Real Real qz267 qz453 qz638)

noncomputable def ep1110 := @Enclosure.Complex.IsNear.of_eq qz712 (Complex.mk (@HMul.hMul Real Real Real qz0 qz361 (Real.cos qz174)) (@HMul.hMul Real Real Real qz0 qz361 (@Neg.neg Real Real.instNeg (Real.sin qz174)))) Bool.false 44323264005 274877906944 487141896531 3407008577355776 Bool.false 61368600989 549755813888 7781117465917 54512137237692416 (BSN.cpow_neg_s_mk qz145 142522 1000 26 qz146 rfl)

noncomputable def ep1111 := @Enclosure.Real.IsNear.mulLit_ff qz145 qz638 142522 1000 0 1 3668288609262839 1125899906842624 125000000099157 24789250000000000000 261405914584679169979 562949953421312000 8907625007066026977 12394625000000000000000 qz147 (BSN.isNear_log_sfrac 26 1 3668288609262839 1125899906842624 125000000099157 24789250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz639) Bool.false 61543670347942250676224 18889465931478580854784 1000000000793256 198314000000000000000 3668288609262839 1125899906842624 125000000099157 24789250000000000000 (BSN.log_rat_reduce_isNear 26 1 4 52 32 254545 524288 24973259072661432 36028797018963968 198314 1000000000000000 rfl rfl rfl rfl (ep410 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1112 := nat_lit 1187778217231761808844591660719432011623062874905380390703519583249704050390625

noncomputable def ep1113 := nat_lit 340893635353972242937908654337450115231199676809510729531416821441650390625

noncomputable def ep1114 := nat_lit 3110295788768803068104412021205775587397647491942114196375690900324033650390625

noncomputable def ep1115 := BSN.sin_dyadic_bound_f 2072895275 2147483648 3 2 1048576 397016 ep1112 ep95 ep1113 ep1114 ep98 ep1113 862140 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2072895275) qz20 0 2 ep1112 ep95 ep1113 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2072895275) qz21 0 2 ep1114 ep98 ep1113 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz479 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 243453229) qz17)

noncomputable def ep1116 := @Enclosure.Real.IsNear.cos_image qz174 qz479 Bool.false 243453229 524288 755 1048576 Bool.false 862140 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz174 Bool.false 261405914584679169979 562949953421312000 8907625007066026977 12394625000000000000000 243453229 524288 755 1048576 (ep1111 rfl) rfl) (Enclosure.sfrac_false_div 243453229 524288) (BSN.cos_reduce3 qz479 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 72933518674414050213888) qz19) 226375608064910080 72057594037927936 Bool.false 862140 1048576 73 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q3 243453229 524288 226375608064910080 72057594037927936 73 72933518674414050213888 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 862140 1048576 72933518674414050213888 75557863725914323419136 2072895275 2147483648 397016 396628 (ep1115 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1117 := nat_lit 660028295633358325910523326468278873175137685914904444048413731503809650390625

noncomputable def ep1118 := nat_lit 1979403099629367033245694162096161719294950658391094310686178360868545650390625

noncomputable def ep1119 := BSN.cos_dyadic_bound_f 2072895275 2147483648 3 2 1048576 397016 ep1117 ep102 ep1113 ep1118 ep104 ep1113 596846 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2072895275) qz15 0 2 ep1117 ep102 ep1113 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2072895275) qz16 0 2 ep1118 ep104 ep1113 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1120 := @Enclosure.Real.IsNear.sin_image qz174 qz479 Bool.false 243453229 524288 755 1048576 Bool.true 596846 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz174 Bool.false 261405914584679169979 562949953421312000 8907625007066026977 12394625000000000000000 243453229 524288 755 1048576 (ep1111 rfl) rfl) (Enclosure.sfrac_false_div 243453229 524288) (BSN.sin_reduce3 qz479 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 72933518674414050213888) qz19) 226375608064910080 72057594037927936 Bool.false 596846 1048576 73 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q3 243453229 524288 226375608064910080 72057594037927936 73 72933518674414050213888 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 596846 1048576 72933518674414050213888 75557863725914323419136 2072895275 2147483648 397016 396628 (ep1119 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1121 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz361 (Real.cos qz174)) (@HMul.hMul Real Real Real qz0 qz361 (@Neg.neg Real Real.instNeg (Real.sin qz174))) Bool.false 44323264005 274877906944 487141896531 3407008577355776 Bool.false 61368600989 549755813888 7781117465917 54512137237692416 (@Enclosure.Real.IsNear.mulLit_ff qz361 (Real.cos qz174) 205643 1048576 1 1048576 215535 262144 75387823 103973650432 44323264005 274877906944 487141896531 3407008577355776 qz365 (@Enclosure.Real.IsNear.recentre' (Real.cos qz174) Bool.false 862140 1048576 150775646 207947300864 215535 262144 75387823 103973650432 (ep1116 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz361 (@Neg.neg Real Real.instNeg (Real.sin qz174)) 205643 1048576 1 1048576 298423 524288 75387823 103973650432 61368600989 549755813888 7781117465917 54512137237692416 qz365 (@Enclosure.Real.IsNear.neg (Real.sin qz174) Bool.true 298423 524288 75387823 103973650432 (@Enclosure.Real.IsNear.recentre' (Real.sin qz174) Bool.true 596846 1048576 150775646 207947300864 298423 524288 75387823 103973650432 (ep1120 rfl rfl) rfl)) rfl)

noncomputable def ep1122 := @ep1098 44323264005 274877906944 487141896531 3407008577355776 Bool.false 61368600989 549755813888 7781117465917 54512137237692416 Bool.false 528256409960046269562880 1921785624145 1099511627776 620998097084417 109024274475384832 Bool.true 637206234564881547264 74180568867 549755813888 38801488789075 6814017154711552 (ep1099 (BSN.head_sum_c_succ qz142 25 26 rfl rfl) (ep1109 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1110 ep1121) rfl rfl

noncomputable abbrev qz175 := (@HMul.hMul Real Real Real qz267 qz453 qz640)

noncomputable def ep1123 := @Enclosure.Complex.IsNear.of_eq qz711 (Complex.mk (@HMul.hMul Real Real Real qz0 qz366 (Real.cos qz175)) (@HMul.hMul Real Real Real qz0 qz366 (@Neg.neg Real Real.instNeg (Real.sin qz175)))) Bool.false 3222931829 274877906944 3799896836147 27256068618846208 Bool.false 211208281973 1099511627776 15297033192239 109024274475384832 (BSN.cpow_neg_s_mk qz145 142522 1000 27 qz146 rfl)

noncomputable def ep1124 := @Enclosure.Real.IsNear.mulLit_ff qz145 qz640 142522 1000 0 1 3710780868205815 1125899906842624 125000000099157 24789250000000000000 52886791089842916543 112589990684262400 8907625007066026977 12394625000000000000000 qz147 (BSN.isNear_log_sfrac 27 1 3710780868205815 1125899906842624 125000000099157 24789250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz641) Bool.false 62256572154556490711040 18889465931478580854784 1000000000793256 198314000000000000000 3710780868205815 1125899906842624 125000000099157 24789250000000000000 (BSN.log_rat_reduce_isNear 27 1 4 54 32 274332 524288 24973259072661432 36028797018963968 198314 1000000000000000 rfl rfl rfl rfl (ep424 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1125 := BSN.sin_dyadic_bound_f 130917538 2147483648 1 0 1048576 397016 0 1 1 0 1 1 63884 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 130917538) qz20 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 130917538) qz21 0 0 rfl) rfl rfl

noncomputable abbrev qz480 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 7696041) (@Nat.cast Real Real.instNatCast 16384))

noncomputable def ep1126 := @Enclosure.Real.IsNear.cos_image qz175 qz480 Bool.false 7696041 16384 377 524288 Bool.false 63884 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz175 Bool.false 52886791089842916543 112589990684262400 8907625007066026977 12394625000000000000000 7696041 16384 377 524288 (ep1124 rfl) rfl) (Enclosure.sfrac_false_div 7696041 16384) (BSN.cos_reduce3 qz480 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 143945356387362537472) qz689) 226375608064910080 72057594037927936 Bool.false 63884 1048576 74 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q3 7696041 16384 226375608064910080 72057594037927936 74 143945356387362537472 2361183241434822606848 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 63884 1048576 143945356387362537472 2361183241434822606848 130917538 2147483648 397016 396628 (ep1125 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1127 := BSN.cos_dyadic_bound_f 130917538 2147483648 1 0 1048576 397016 0 1 1 0 1 1 1046627 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 130917538) qz15 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 130917538) qz16 0 0 rfl) rfl rfl

noncomputable def ep1128 := @Enclosure.Real.IsNear.sin_image qz175 qz480 Bool.false 7696041 16384 377 524288 Bool.true 1046627 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz175 Bool.false 52886791089842916543 112589990684262400 8907625007066026977 12394625000000000000000 7696041 16384 377 524288 (ep1124 rfl) rfl) (Enclosure.sfrac_false_div 7696041 16384) (BSN.sin_reduce3 qz480 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 143945356387362537472) qz689) 226375608064910080 72057594037927936 Bool.false 1046627 1048576 74 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q3 7696041 16384 226375608064910080 72057594037927936 74 143945356387362537472 2361183241434822606848 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1046627 1048576 143945356387362537472 2361183241434822606848 130917538 2147483648 397016 396628 (ep1127 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1129 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz366 (Real.cos qz175)) (@HMul.hMul Real Real Real qz0 qz366 (@Neg.neg Real Real.instNeg (Real.sin qz175))) Bool.false 3222931829 274877906944 3799896836147 27256068618846208 Bool.false 211208281973 1099511627776 15297033192239 109024274475384832 (@Enclosure.Real.IsNear.mulLit_ff qz366 (Real.cos qz175) 201799 1048576 1 1048576 15971 262144 37644333 51986825216 3222931829 274877906944 3799896836147 27256068618846208 qz370 (@Enclosure.Real.IsNear.recentre' (Real.cos qz175) Bool.false 63884 1048576 75288666 103973650432 15971 262144 37644333 51986825216 (ep1126 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz366 (@Neg.neg Real Real.instNeg (Real.sin qz175)) 201799 1048576 1 1048576 1046627 1048576 37644333 51986825216 211208281973 1099511627776 15297033192239 109024274475384832 qz370 (@Enclosure.Real.IsNear.neg (Real.sin qz175) Bool.true 1046627 1048576 37644333 51986825216 (@Enclosure.Real.IsNear.recentre' (Real.sin qz175) Bool.true 1046627 1048576 75288666 103973650432 1046627 1048576 37644333 51986825216 (ep1128 rfl rfl) rfl)) rfl)

noncomputable def ep1130 := @ep1096 3222931829 274877906944 3799896836147 27256068618846208 Bool.false 211208281973 1099511627776 15297033192239 109024274475384832 Bool.false 531800060981561140445184 1934677351461 1099511627776 636197684429005 109024274475384832 Bool.false 34550582931647975391232 62847144239 1099511627776 636120853817439 109024274475384832 (ep1097 (BSN.head_sum_c_succ qz142 26 27 rfl rfl) (ep1122 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1123 ep1129) rfl rfl

noncomputable abbrev qz176 := (@HMul.hMul Real Real Real qz267 qz453 qz642)

noncomputable def ep1131 := @Enclosure.Complex.IsNear.of_eq qz710 (Complex.mk (@HMul.hMul Real Real Real qz0 qz371 (Real.cos qz176)) (@HMul.hMul Real Real Real qz0 qz371 (@Neg.neg Real Real.instNeg (Real.sin qz176)))) Bool.true 179099521237 1099511627776 15009121206667 109024274475384832 Bool.false 105354349765 1099511627776 14972220524059 109024274475384832 (BSN.cpow_neg_s_mk qz145 142522 1000 28 qz146 rfl)

noncomputable def ep1132 := @Enclosure.Real.IsNear.mulLit_ff qz145 qz642 142522 1000 0 1 3751726938922231 1125899906842624 125000000099157 24789250000000000000 267351813394537103291 562949953421312000 8907625007066026977 12394625000000000000000 qz147 (BSN.isNear_log_sfrac 28 1 3751726938922231 1125899906842624 125000000099157 24789250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz643) Bool.false 62943533227317076688896 18889465931478580854784 1000000000793256 198314000000000000000 3751726938922231 1125899906842624 125000000099157 24789250000000000000 (BSN.log_rat_reduce_isNear 28 1 4 56 32 293399 524288 24973259072661432 36028797018963968 198314 1000000000000000 rfl rfl rfl rfl (ep439 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1133 := nat_lit 1700153331244035419173634211048407296

noncomputable def ep1134 := BSN.cos_dyadic_bound_f 1141884092 2147483648 2 1 1048576 397016 ep1133 ep66 ep1133 ep1133 ep67 ep1133 903799 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1141884092) qz15 0 1 ep1133 ep66 ep1133 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1141884092) qz16 0 1 ep1133 ep67 ep1133 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz481 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 248990779) qz17)

noncomputable def ep1135 := @Enclosure.Real.IsNear.cos_image qz176 qz481 Bool.false 248990779 524288 377 524288 Bool.true 903799 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz176 Bool.false 267351813394537103291 562949953421312000 8907625007066026977 12394625000000000000000 248990779 524288 377 524288 (ep1132 rfl) rfl) (Enclosure.sfrac_false_div 248990779 524288) (BSN.cos_reduce2 qz481 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 40176474795920702046208) qz19) 226375608064910080 72057594037927936 Bool.false 903799 1048576 75 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q2 248990779 524288 226375608064910080 72057594037927936 75 40176474795920702046208 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 903799 1048576 40176474795920702046208 75557863725914323419136 1141884092 2147483648 397016 396628 (ep1134 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1136 := BSN.sin_dyadic_bound_f 1141884092 2147483648 2 1 1048576 397016 ep1133 ep70 ep1133 ep1133 ep71 ep1133 531655 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1141884092) qz20 0 1 ep1133 ep70 ep1133 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1141884092) qz21 0 1 ep1133 ep71 ep1133 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1137 := @Enclosure.Real.IsNear.sin_image qz176 qz481 Bool.false 248990779 524288 377 524288 Bool.true 531655 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz176 Bool.false 267351813394537103291 562949953421312000 8907625007066026977 12394625000000000000000 248990779 524288 377 524288 (ep1132 rfl) rfl) (Enclosure.sfrac_false_div 248990779 524288) (BSN.sin_reduce2 qz481 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 40176474795920702046208) qz19) 226375608064910080 72057594037927936 Bool.false 531655 1048576 75 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q2 248990779 524288 226375608064910080 72057594037927936 75 40176474795920702046208 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 531655 1048576 40176474795920702046208 75557863725914323419136 1141884092 2147483648 397016 396628 (ep1136 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1138 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz371 (Real.cos qz176)) (@HMul.hMul Real Real Real qz0 qz371 (@Neg.neg Real Real.instNeg (Real.sin qz176))) Bool.true 179099521237 1099511627776 15009121206667 109024274475384832 Bool.false 105354349765 1099511627776 14972220524059 109024274475384832 (@Enclosure.Real.IsNear.mulLit_ft qz371 (Real.cos qz176) 198163 1048576 1 1048576 903799 1048576 37644333 51986825216 179099521237 1099511627776 15009121206667 109024274475384832 qz375 (@Enclosure.Real.IsNear.recentre' (Real.cos qz176) Bool.true 903799 1048576 75288666 103973650432 903799 1048576 37644333 51986825216 (ep1135 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz371 (@Neg.neg Real Real.instNeg (Real.sin qz176)) 198163 1048576 1 1048576 531655 1048576 37644333 51986825216 105354349765 1099511627776 14972220524059 109024274475384832 qz375 (@Enclosure.Real.IsNear.neg (Real.sin qz176) Bool.true 531655 1048576 37644333 51986825216 (@Enclosure.Real.IsNear.recentre' (Real.sin qz176) Bool.true 531655 1048576 75288666 103973650432 531655 1048576 37644333 51986825216 (ep1137 rfl rfl) rfl)) rfl)

noncomputable def ep1139 := @ep1093 179099521237 1099511627776 15009121206667 109024274475384832 Bool.false 105354349765 1099511627776 14972220524059 109024274475384832 Bool.false ep1094 109723614389 68719476736 81400850704459 13628034309423104 Bool.false 184939498466693143855104 42050373501 274877906944 325546537170749 54512137237692416 (ep1095 (BSN.head_sum_c_succ qz142 27 28 rfl rfl) (ep1130 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1131 ep1138) rfl rfl

noncomputable abbrev qz177 := (@HMul.hMul Real Real Real qz267 qz453 qz644)

noncomputable def ep1140 := @Enclosure.Complex.IsNear.of_eq qz709 (Complex.mk (@HMul.hMul Real Real Real qz0 qz376 (Real.cos qz177)) (@HMul.hMul Real Real Real qz0 qz376 (@Neg.neg Real Real.instNeg (Real.sin qz177)))) Bool.true 149369186655 1099511627776 14755280363637 109024274475384832 Bool.true 139196106765 1099511627776 14750099807015 109024274475384832 (BSN.cpow_neg_s_mk qz145 142522 1000 29 qz146 rfl)

noncomputable def ep1141 := @Enclosure.Real.IsNear.mulLit_ff qz145 qz644 142522 1000 0 1 3791236343078135 1125899906842624 125000000099157 24789250000000000000 54033458608818195647 112589990684262400 8907625007066026977 12394625000000000000000 qz147 (BSN.isNear_log_sfrac 29 1 3791236343078135 1125899906842624 125000000099157 24789250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz645) Bool.false 63606391034871975772160 18889465931478580854784 1000000000793256 198314000000000000000 3791236343078135 1125899906842624 125000000099157 24789250000000000000 (BSN.log_rat_reduce_isNear 29 1 4 58 32 311797 524288 24973259072661432 36028797018963968 198314 1000000000000000 rfl rfl rfl rfl (ep450 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1142 := nat_lit 9645540013978539425069575728812153616

noncomputable def ep1143 := BSN.sin_dyadic_bound_f 1762307286 2147483648 2 1 1048576 397016 ep1142 ep70 ep1142 ep1142 ep71 ep1142 767117 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1762307286) qz20 0 1 ep1142 ep70 ep1142 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1762307286) qz21 0 1 ep1142 ep71 ep1142 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz482 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 503225797) qz26)

noncomputable def ep1144 := @Enclosure.Real.IsNear.cos_image qz177 qz482 Bool.false 503225797 1048576 755 1048576 Bool.true 767117 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz177 Bool.false 54033458608818195647 112589990684262400 8907625007066026977 12394625000000000000000 503225797 1048576 755 1048576 (ep1141 rfl) rfl) (Enclosure.sfrac_false_div 503225797 1048576) (BSN.cos_reduce1 qz482 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 124011350584766270275584) qz27) 226375608064910080 72057594037927936 Bool.false 767117 1048576 76 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q1 503225797 1048576 226375608064910080 72057594037927936 76 124011350584766270275584 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 767117 1048576 124011350584766270275584 151115727451828646838272 1762307286 2147483648 397016 396628 (ep1143 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1145 := nat_lit 344724790991821384318686597543213702063465684883427813643840839106855499489536

noncomputable def ep1146 := nat_lit 93036442161261122527570755408798025139997716262864363942821658391981875456

noncomputable def ep1147 := nat_lit 1033988300091141630711004651118823510140117059217757712203636874003782534717696

noncomputable def ep1148 := BSN.cos_dyadic_bound_f 1762307286 2147483648 3 2 1048576 397016 ep1145 ep102 ep1146 ep1147 ep104 ep1146 714871 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1762307286) qz15 0 2 ep1145 ep102 ep1146 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1762307286) qz16 0 2 ep1147 ep104 ep1146 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1149 := @Enclosure.Real.IsNear.sin_image qz177 qz482 Bool.false 503225797 1048576 755 1048576 Bool.false 714871 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz177 Bool.false 54033458608818195647 112589990684262400 8907625007066026977 12394625000000000000000 503225797 1048576 755 1048576 (ep1141 rfl) rfl) (Enclosure.sfrac_false_div 503225797 1048576) (BSN.sin_reduce1 qz482 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 124011350584766270275584) qz27) 226375608064910080 72057594037927936 Bool.false 714871 1048576 76 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q1 503225797 1048576 226375608064910080 72057594037927936 76 124011350584766270275584 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 714871 1048576 124011350584766270275584 151115727451828646838272 1762307286 2147483648 397016 396628 (ep1148 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1150 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz376 (Real.cos qz177)) (@HMul.hMul Real Real Real qz0 qz376 (@Neg.neg Real Real.instNeg (Real.sin qz177))) Bool.true 149369186655 1099511627776 14755280363637 109024274475384832 Bool.true 139196106765 1099511627776 14750099807015 109024274475384832 (@Enclosure.Real.IsNear.mulLit_ft qz376 (Real.cos qz177) 194715 1048576 1 1048576 767117 1048576 75387823 103973650432 149369186655 1099511627776 14755280363637 109024274475384832 qz380 (@Enclosure.Real.IsNear.recentre' (Real.cos qz177) Bool.true 767117 1048576 150775646 207947300864 767117 1048576 75387823 103973650432 (ep1144 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz376 (@Neg.neg Real Real.instNeg (Real.sin qz177)) 194715 1048576 1 1048576 714871 1048576 75387823 103973650432 139196106765 1099511627776 14750099807015 109024274475384832 qz380 (@Enclosure.Real.IsNear.neg (Real.sin qz177) Bool.false 714871 1048576 75387823 103973650432 (@Enclosure.Real.IsNear.recentre' (Real.sin qz177) Bool.false 714871 1048576 150775646 207947300864 714871 1048576 75387823 103973650432 (ep1149 rfl rfl) rfl)) rfl)

noncomputable def ep1151 := @ep1091 149369186655 1099511627776 14755280363637 109024274475384832 Bool.true 139196106765 1099511627776 14750099807015 109024274475384832 Bool.false 110377817514902011510784 1606208643569 1099511627776 665962085999309 109024274475384832 Bool.false 7972940134356527087616 29005387239 1099511627776 665843174148513 109024274475384832 (ep1092 (BSN.head_sum_c_succ qz142 28 29 rfl rfl) (ep1139 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1140 ep1150) rfl rfl

noncomputable abbrev qz178 := (@HMul.hMul Real Real Real qz267 qz453 qz646)

noncomputable def ep1152 := @Enclosure.Complex.IsNear.of_eq qz708 (Complex.mk (@HMul.hMul Real Real Real qz0 qz381 (Real.cos qz178)) (@HMul.hMul Real Real Real qz0 qz381 (@Neg.neg Real Real.instNeg (Real.sin qz178)))) Bool.false 59204322079 549755813888 31646016563 238044267413504 Bool.true 162101488605 1099511627776 63390856283 476088534827008 (BSN.cpow_neg_s_mk qz145 142522 1000 30 qz146 rfl)

noncomputable def ep1153 := @Enclosure.Real.IsNear.mulLit_ff qz145 qz646 142522 1000 0 1 3829405717437687 1125899906842624 125000000099157 24789250000000000000 272887280830327013307 562949953421312000 8907625007066026977 12394625000000000000000 qz147 (BSN.isNear_log_sfrac 30 1 3829405717437687 1125899906842624 125000000099157 24789250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz647) Bool.false 64246766873087041339392 18889465931478580854784 1000000000793256 198314000000000000000 3829405717437687 1125899906842624 125000000099157 24789250000000000000 (BSN.log_rat_reduce_isNear 30 1 4 60 32 329571 524288 24973259072661432 36028797018963968 198314 1000000000000000 rfl rfl rfl rfl (ep461 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1154 := nat_lit 593348799790413641347342503033824490985799214246463130387937051248255677904001

noncomputable def ep1155 := nat_lit 275523864940390782013647284639456885161652455049068292341917337143661704321

noncomputable def ep1156 := nat_lit 1779495351641360142478000214532194559187074337829291254579127319070479710303361

noncomputable def ep1157 := BSN.cos_dyadic_bound_f 2018458863 2147483648 3 2 1048576 397016 ep1154 ep102 ep1155 ep1156 ep104 ep1155 618506 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2018458863) qz15 0 2 ep1154 ep102 ep1155 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2018458863) qz16 0 2 ep1156 ep104 ep1155 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz483 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 508292169) qz26)

noncomputable def ep1158 := @Enclosure.Real.IsNear.cos_image qz178 qz483 Bool.false 508292169 1048576 755 1048576 Bool.false 618506 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz178 Bool.false 272887280830327013307 562949953421312000 8907625007066026977 12394625000000000000000 508292169 1048576 755 1048576 (ep1153 rfl) rfl) (Enclosure.sfrac_false_div 508292169 1048576) (BSN.cos_reduce0 qz483 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 142036415420202880073728) qz27) 226375608064910080 72057594037927936 Bool.false 618506 1048576 77 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q0 508292169 1048576 226375608064910080 72057594037927936 77 142036415420202880073728 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 618506 1048576 142036415420202880073728 151115727451828646838272 2018458863 2147483648 397016 396628 (ep1157 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1159 := nat_lit 1067807420530792241799605587633172518266309263679594380064413158377145290863745

noncomputable def ep1160 := nat_lit 2796192396085028572018563967245083189073881586614572503885861834346671738074241

noncomputable def ep1161 := BSN.sin_dyadic_bound_f 2018458863 2147483648 3 2 1048576 397016 ep1159 ep95 ep1155 ep1160 ep98 ep1155 846735 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2018458863) qz20 0 2 ep1159 ep95 ep1155 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2018458863) qz21 0 2 ep1160 ep98 ep1155 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1162 := @Enclosure.Real.IsNear.sin_image qz178 qz483 Bool.false 508292169 1048576 755 1048576 Bool.false 846735 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz178 Bool.false 272887280830327013307 562949953421312000 8907625007066026977 12394625000000000000000 508292169 1048576 755 1048576 (ep1153 rfl) rfl) (Enclosure.sfrac_false_div 508292169 1048576) (BSN.sin_reduce0 qz483 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 142036415420202880073728) qz27) 226375608064910080 72057594037927936 Bool.false 846735 1048576 77 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q0 508292169 1048576 226375608064910080 72057594037927936 77 142036415420202880073728 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 846735 1048576 142036415420202880073728 151115727451828646838272 2018458863 2147483648 397016 396628 (ep1161 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1163 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz381 (Real.cos qz178)) (@HMul.hMul Real Real Real qz0 qz381 (@Neg.neg Real Real.instNeg (Real.sin qz178))) Bool.false 59204322079 549755813888 31646016563 238044267413504 Bool.true 162101488605 1099511627776 63390856283 476088534827008 (@Enclosure.Real.IsNear.mulLit_ff qz381 (Real.cos qz178) 191443 1048576 1 1048576 309253 524288 75387823 103973650432 59204322079 549755813888 31646016563 238044267413504 qz385 (@Enclosure.Real.IsNear.recentre' (Real.cos qz178) Bool.false 618506 1048576 150775646 207947300864 309253 524288 75387823 103973650432 (ep1158 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz381 (@Neg.neg Real Real.instNeg (Real.sin qz178)) 191443 1048576 1 1048576 846735 1048576 75387823 103973650432 162101488605 1099511627776 63390856283 476088534827008 qz385 (@Enclosure.Real.IsNear.neg (Real.sin qz178) Bool.false 846735 1048576 75387823 103973650432 (@Enclosure.Real.IsNear.recentre' (Real.sin qz178) Bool.false 846735 1048576 150775646 207947300864 846735 1048576 75387823 103973650432 (ep1162 rfl rfl) rfl)) rfl)

noncomputable def ep1164 := @ep1089 59204322079 549755813888 31646016563 238044267413504 Bool.true 162101488605 1099511627776 63390856283 476088534827008 Bool.false 948118380659671958552576 1724617287727 1099511627776 680455961585163 109024274475384832 Bool.true 146340711063570157142016 66548050683 549755813888 85044960029665 13628034309423104 (ep1090 (BSN.head_sum_c_succ qz142 29 30 rfl rfl) (ep1151 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1152 ep1163) rfl rfl

noncomputable abbrev qz179 := (@HMul.hMul Real Real Real qz267 qz453 qz648)

noncomputable def ep1165 := @Enclosure.Complex.IsNear.of_eq qz707 (Complex.mk (@HMul.hMul Real Real Real qz0 qz386 (Real.cos qz179)) (@HMul.hMul Real Real Real qz0 qz386 (@Neg.neg Real Real.instNeg (Real.sin qz179)))) Bool.false 154810392909 1099511627776 14260623604077 109024274475384832 Bool.false 122600860697 1099511627776 14243664980681 109024274475384832 (BSN.cpow_neg_s_mk qz145 142522 1000 31 qz146 rfl)

noncomputable def ep1166 := @Enclosure.Real.IsNear.mulLit_ff qz145 qz648 142522 1000 0 1 3866325256314103 1125899906842624 125000000099157 24789250000000000000 275518204090199293883 562949953421312000 8907625007066026977 12394625000000000000000 qz147 (BSN.isNear_log_sfrac 31 1 3866325256314103 1125899906842624 125000000099157 24789250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz649) Bool.false 64866173951437069877248 18889465931478580854784 1000000000793256 198314000000000000000 3866325256314103 1125899906842624 125000000099157 24789250000000000000 (BSN.log_rat_reduce_isNear 31 1 4 62 32 346763 524288 24973259072661432 36028797018963968 198314 1000000000000000 rfl rfl rfl rfl (ep472 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1167 := nat_lit 901554122749403296860911058345615598732908961443866007373661920991252197687105

noncomputable def ep1168 := nat_lit 196422777513202234777676321531090020903604018114909995476528339000621023041

noncomputable def ep1169 := nat_lit 2360895160799130116731793676860800041409489063942701117414533509094897607524161

noncomputable def ep1170 := BSN.sin_dyadic_bound_f 1934857481 2147483648 3 2 1048576 397016 ep1167 ep95 ep1168 ep1169 ep98 ep1168 822021 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1934857481) qz20 0 2 ep1167 ep95 ep1168 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1934857481) qz21 0 2 ep1169 ep98 ep1168 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz484 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 256596323) qz17)

noncomputable def ep1171 := @Enclosure.Real.IsNear.cos_image qz179 qz484 Bool.false 256596323 524288 377 524288 Bool.false 822021 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz179 Bool.false 275518204090199293883 562949953421312000 8907625007066026977 12394625000000000000000 256596323 524288 377 524288 (ep1166 rfl) rfl) (Enclosure.sfrac_false_div 256596323 524288) (BSN.cos_reduce3 qz484 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 68076745564897689993216) qz19) 226375608064910080 72057594037927936 Bool.false 822021 1048576 77 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q3 256596323 524288 226375608064910080 72057594037927936 77 68076745564897689993216 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 822021 1048576 68076745564897689993216 75557863725914323419136 1934857481 2147483648 397016 396628 (ep1170 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1172 := nat_lit 500950700539674365915962888557133594860906580365754408538912857590251496947521

noncomputable def ep1173 := nat_lit 1502459256063996693278333313028338604540912533061033405625785516092753248796481

noncomputable def ep1174 := BSN.cos_dyadic_bound_f 1934857481 2147483648 3 2 1048576 397016 ep1172 ep102 ep1168 ep1173 ep104 ep1168 650993 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1934857481) qz15 0 2 ep1172 ep102 ep1168 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1934857481) qz16 0 2 ep1173 ep104 ep1168 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1175 := @Enclosure.Real.IsNear.sin_image qz179 qz484 Bool.false 256596323 524288 377 524288 Bool.true 650993 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz179 Bool.false 275518204090199293883 562949953421312000 8907625007066026977 12394625000000000000000 256596323 524288 377 524288 (ep1166 rfl) rfl) (Enclosure.sfrac_false_div 256596323 524288) (BSN.sin_reduce3 qz484 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 68076745564897689993216) qz19) 226375608064910080 72057594037927936 Bool.false 650993 1048576 77 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q3 256596323 524288 226375608064910080 72057594037927936 77 68076745564897689993216 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 650993 1048576 68076745564897689993216 75557863725914323419136 1934857481 2147483648 397016 396628 (ep1174 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1176 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz386 (Real.cos qz179)) (@HMul.hMul Real Real Real qz0 qz386 (@Neg.neg Real Real.instNeg (Real.sin qz179))) Bool.false 154810392909 1099511627776 14260623604077 109024274475384832 Bool.false 122600860697 1099511627776 14243664980681 109024274475384832 (@Enclosure.Real.IsNear.mulLit_ff qz386 (Real.cos qz179) 188329 1048576 1 1048576 822021 1048576 37644333 51986825216 154810392909 1099511627776 14260623604077 109024274475384832 qz390 (@Enclosure.Real.IsNear.recentre' (Real.cos qz179) Bool.false 822021 1048576 75288666 103973650432 822021 1048576 37644333 51986825216 (ep1171 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz386 (@Neg.neg Real Real.instNeg (Real.sin qz179)) 188329 1048576 1 1048576 650993 1048576 37644333 51986825216 122600860697 1099511627776 14243664980681 109024274475384832 qz390 (@Enclosure.Real.IsNear.neg (Real.sin qz179) Bool.true 650993 1048576 37644333 51986825216 (@Enclosure.Real.IsNear.recentre' (Real.sin qz179) Bool.true 650993 1048576 75288666 103973650432 650993 1048576 37644333 51986825216 (ep1175 rfl rfl) rfl)) rfl)

noncomputable def ep1177 := @ep1086 154810392909 1099511627776 14260623604077 109024274475384832 Bool.false 122600860697 1099511627776 14243664980681 109024274475384832 Bool.false ep1087 469856920159 274877906944 86839573148655 13628034309423104 Bool.true 5769819575936532611072 10495240669 1099511627776 694603345218001 109024274475384832 (ep1088 (BSN.head_sum_c_succ qz142 30 31 rfl rfl) (ep1164 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1165 ep1176) rfl rfl

noncomputable abbrev qz180 := (@HMul.hMul Real Real Real qz267 qz453 qz651)

noncomputable def ep1178 := @Enclosure.Complex.IsNear.of_eq qz706 (Complex.mk (@HMul.hMul Real Real Real qz0 qz391 (Real.cos qz180)) (@HMul.hMul Real Real Real qz0 qz391 (@Neg.neg Real Real.instNeg (Real.sin qz180)))) Bool.true 73474000577 549755813888 7017207894715 54512137237692416 Bool.false 15902477133 137438953472 438245703435 3407008577355776 (BSN.cpow_neg_s_mk qz145 142522 1000 32 qz146 rfl)

noncomputable def ep1179 := @Enclosure.Real.IsNear.mulLit_ff qz145 qz651 142522 1000 0 1 15608286920413395 4503599627370496 100000000099157 19831400000000000000 222452426847115788219 450359962737049600 7126100007066026977 9915700000000000000000 qz147 (BSN.isNear_log_sfrac 32 1 15608286920413395 4503599627370496 100000000099157 19831400000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz652) Bool.false 65465900263437584302080 18889465931478580854784 1000000000991570 198314000000000000000 15608286920413395 4503599627370496 100000000099157 19831400000000000000 (BSN.log_rat_reduce_isNear 32 1 5 64 64 0 524288 24973259072661432 36028797018963968 198314 1000000000000000 rfl rfl rfl rfl (ep483 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1180 := nat_lit 197038259664940264825925053623829232341258443176159908460213260856931644902561

noncomputable def ep1181 := nat_lit 30402521641694643867477878260228075028445623952313595464083001490976312481

noncomputable def ep1182 := nat_lit 591053973951537405190040205114967240873718438280575098189711616567812982082721

noncomputable def ep1183 := BSN.cos_dyadic_bound_f 1532370211 2147483648 3 2 1048576 397016 ep1180 ep102 ep1181 ep1182 ep104 ep1181 792758 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1532370211) qz15 0 2 ep1180 ep102 ep1181 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1532370211) qz16 0 2 ep1182 ep104 ep1181 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz485 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 517937417) qz26)

noncomputable def ep1184 := @Enclosure.Real.IsNear.cos_image qz180 qz485 Bool.false 517937417 1048576 377 524288 Bool.true 792758 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz180 Bool.false 222452426847115788219 450359962737049600 7126100007066026977 9915700000000000000000 517937417 1048576 377 524288 (ep1179 rfl) rfl) (Enclosure.sfrac_false_div 517937417 1048576) (BSN.cos_reduce2 qz485 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 107830967364848665493504) qz27) 226375608064910080 72057594037927936 Bool.false 792758 1048576 78 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q2 517937417 1048576 226375608064910080 72057594037927936 78 107830967364848665493504 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 792758 1048576 107830967364848665493504 151115727451828646838272 1532370211 2147483648 397016 396628 (ep1183 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1185 := nat_lit 5513848169989326416969309143567999441

noncomputable def ep1186 := BSN.sin_dyadic_bound_f 1532370211 2147483648 2 1 1048576 397016 ep1185 ep70 ep1185 ep1185 ep71 ep1185 686328 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1532370211) qz20 0 1 ep1185 ep70 ep1185 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1532370211) qz21 0 1 ep1185 ep71 ep1185 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1187 := @Enclosure.Real.IsNear.sin_image qz180 qz485 Bool.false 517937417 1048576 377 524288 Bool.true 686328 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz180 Bool.false 222452426847115788219 450359962737049600 7126100007066026977 9915700000000000000000 517937417 1048576 377 524288 (ep1179 rfl) rfl) (Enclosure.sfrac_false_div 517937417 1048576) (BSN.sin_reduce2 qz485 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 107830967364848665493504) qz27) 226375608064910080 72057594037927936 Bool.false 686328 1048576 78 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q2 517937417 1048576 226375608064910080 72057594037927936 78 107830967364848665493504 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 686328 1048576 107830967364848665493504 151115727451828646838272 1532370211 2147483648 397016 396628 (ep1186 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1188 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz391 (Real.cos qz180)) (@HMul.hMul Real Real Real qz0 qz391 (@Neg.neg Real Real.instNeg (Real.sin qz180))) Bool.true 73474000577 549755813888 7017207894715 54512137237692416 Bool.false 15902477133 137438953472 438245703435 3407008577355776 (@Enclosure.Real.IsNear.mulLit_ft qz391 (Real.cos qz180) 185363 1048576 1 1048576 396379 524288 37644333 51986825216 73474000577 549755813888 7017207894715 54512137237692416 qz395 (@Enclosure.Real.IsNear.recentre' (Real.cos qz180) Bool.true 792758 1048576 75288666 103973650432 396379 524288 37644333 51986825216 (ep1184 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz391 (@Neg.neg Real Real.instNeg (Real.sin qz180)) 185363 1048576 1 1048576 85791 131072 37644333 51986825216 15902477133 137438953472 438245703435 3407008577355776 qz395 (@Enclosure.Real.IsNear.neg (Real.sin qz180) Bool.true 85791 131072 37644333 51986825216 (@Enclosure.Real.IsNear.recentre' (Real.sin qz180) Bool.true 686328 1048576 75288666 103973650432 85791 131072 37644333 51986825216 (ep1187 rfl rfl) rfl)) rfl)

noncomputable def ep1189 := @ep1084 73474000577 549755813888 7017207894715 54512137237692416 Bool.false 15902477133 137438953472 438245703435 3407008577355776 Bool.false 238110194059512071061504 866239839741 549755813888 354375500489335 54512137237692416 Bool.false 16042503624191314493440 116724576395 1099511627776 708627207727921 109024274475384832 (ep1085 (BSN.head_sum_c_succ qz142 31 32 rfl rfl) (ep1177 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1178 ep1188) rfl rfl

theorem EMRow49.d16 : Enclosure.Complex.IsNear qz172 Bool.false 866239839741 549755813888 354375500489335 54512137237692416 Bool.false 116724576395 1099511627776 708627207727921 109024274475384832 := ep1083 (BSN.head_sum_c_succ qz142 32 33 rfl rfl) (ep1189 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable def ep1190 := nat_lit 248622290730309850927024660508461

noncomputable def ep1191 := nat_lit 158078451886741111129182830592000

noncomputable def ep1192 := nat_lit 46928629841602317169055082429121701208549

noncomputable def ep1193 := nat_lit 6216979320692245682557323693326264696832000

noncomputable abbrev qz714 := (@HAdd.hAdd Complex Complex Complex qz730 (@HAdd.hAdd Complex Complex Complex qz730 qz733 (@HMul.hMul Complex Complex Complex qz732 Complex.I (@HDiv.hDiv Complex Complex Complex qz734 (↑qz737) (2 : Complex)))) (@Nat.cast Complex Complex.instNatCast 2))

noncomputable abbrev qz486 := qz714

noncomputable abbrev qz181 := (Complex.Stirling.logGammaStirling 1 qz486)

noncomputable abbrev qz715 := (@HAdd.hAdd Complex Complex Complex qz730 qz733 (@HMul.hMul Complex Complex Complex qz732 Complex.I (@HDiv.hDiv Complex Complex Complex qz734 (↑qz737) (2 : Complex))))

noncomputable abbrev qz487 := qz715

noncomputable abbrev qz182 := qz487

noncomputable abbrev qz183 := (@HMul.hMul Real Real Real qz267 (@HDiv.hDiv Real Real Real qz270 qz453 (2 : Real)) (Real.log Real.pi))

noncomputable def ep1194 := Complex.re (@HMul.hMul Complex Complex Complex qz74 (Complex.exp (@HMul.hMul Complex Complex Complex qz74 Complex.I ↑(@HSub.hSub Real Real Real qz400 (Complex.im (@HSub.hSub Complex Complex Complex qz75 qz181 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz182 (@Nat.cast Complex Complex.instNatCast j))))) qz183))) (zetaApproximant qz142 1 36))

noncomputable def ep1195 := @Enclosure.Real.IsNear.of_eq ep1194 (@HSub.hSub Real Real Real qz400 (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz400 (Complex.im (@HSub.hSub Complex Complex Complex qz75 qz181 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz182 (@Nat.cast Complex Complex.instNatCast j))))) qz183)) (Complex.re (zetaApproximant qz142 1 36))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz400 (Complex.im (@HSub.hSub Complex Complex Complex qz75 qz181 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz182 (@Nat.cast Complex Complex.instNatCast j))))) qz183)) (Complex.im (zetaApproximant qz142 1 36))))

noncomputable def ep1196 := nat_lit 2946630631360509357154079433629

noncomputable def ep1197 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz400 (Complex.im (@HSub.hSub Complex Complex Complex qz75 qz181 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz182 (@Nat.cast Complex Complex.instNatCast j))))) qz183)) (Complex.re (zetaApproximant qz142 1 36))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz400 (Complex.im (@HSub.hSub Complex Complex Complex qz75 qz181 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz182 (@Nat.cast Complex Complex.instNatCast j))))) qz183)) (Complex.im (zetaApproximant qz142 1 36))) ep1196

noncomputable def ep1198 := nat_lit 1873522392731746502271796510720

noncomputable def ep1199 := nat_lit 18753141786152545843343304733249372911797

noncomputable def ep1200 := nat_lit 2486791728276898273022929477330505878732800

noncomputable def ep1201 := nat_lit 2649674134991337193666368113

noncomputable def ep1202 := nat_lit 1264627615093928889033462644736000

noncomputable def ep1203 := nat_lit 91550752441905121393641191996537858113

noncomputable def ep1204 := nat_lit 12433958641384491365114647386652529393664000

noncomputable def ep1205 := nat_lit 3726395432123984243509348714388025276639396305848114246697615360

noncomputable def ep1206 := @Enclosure.Real.IsNear.mulLit_ff (Real.cos (@HSub.hSub Real Real Real qz400 (Complex.im (@HSub.hSub Complex Complex Complex qz75 qz181 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz182 (@Nat.cast Complex Complex.instNatCast j))))) qz183)) (Complex.re (zetaApproximant qz142 1 36)) 1048575 1048576 19597759

noncomputable def ep1207 := nat_lit 210759647475896527941783809

noncomputable def ep1208 := nat_lit 134004764037018764181504000

noncomputable def ep1209 := nat_lit 48859188975573823083205052059

noncomputable def ep1210 := nat_lit 7034564322856942729382854656000

noncomputable def ep1211 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HSub.hSub Real Real Real qz400 (Complex.im (@HSub.hSub Complex Complex Complex qz75 qz181 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz182 (@Nat.cast Complex Complex.instNatCast j))))) qz183)) Bool.false 1048575 1048576 39195518

noncomputable abbrev qz716 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 79060617) qz17)

noncomputable def ep1212 := @Enclosure.Real.IsNear.cos_image (@HSub.hSub Real Real Real qz400 (Complex.im (@HSub.hSub Complex Complex Complex qz75 qz181 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz182 (@Nat.cast Complex Complex.instNatCast j))))) qz183) qz716 Bool.false 79060617 524288 195

noncomputable def ep1213 := nat_lit 57881420255006126577830893

noncomputable def ep1214 := nat_lit 155960475648000000000000000000

noncomputable def ep1215 := @Enclosure.Real.IsNear.recentre' (@HSub.hSub Real Real Real qz400 (Complex.im (@HSub.hSub Complex Complex Complex qz75 qz181 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz182 (@Nat.cast Complex Complex.instNatCast j))))) qz183) Bool.false 339562765299461339769 2251799813685248000 ep1213 ep1214

noncomputable def ep1216 := nat_lit 15485258393006126577830893

noncomputable def ep1217 := @Enclosure.Real.IsNear.subLit_ff_p (Complex.im (@HSub.hSub Complex Complex Complex qz75 qz181 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz182 (@Nat.cast Complex Complex.instNatCast j))))) qz183 523252382683247622777 2251799813685248000 ep1216 ep1214 5346071481 65536000

noncomputable def ep1218 := nat_lit 22253585386665498363101184000

noncomputable def ep1219 := nat_lit 4842620532272820374343719

noncomputable def ep1220 := nat_lit 25993412608000000000000000000

noncomputable def ep1221 := @Enclosure.Complex.IsNear.im_isNear (@HSub.hSub Complex Complex Complex qz75 qz181 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz182 (@Nat.cast Complex Complex.instNatCast j)))) Bool.true 126195613783035120191 1125899906842624000 ep1219 ep1220 Bool.false 523252382683247622777 2251799813685248000

noncomputable def ep1222 := nat_lit 4777084531960899423047719

noncomputable def ep1223 := nat_lit 14698826392850166102182893

noncomputable def ep1224 := @Enclosure.Complex.IsNear.subLitP qz181 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz182 (@Nat.cast Complex Complex.instNatCast j))) Bool.true 116588469899802123191 1125899906842624000 ep1222 ep1220 Bool.false 530279227618648350777 2251799813685248000 ep1223

noncomputable def ep1225 := nat_lit 142083629802266999086061787161821184

noncomputable def ep1226 := nat_lit 147282452229562385491359150964211712

noncomputable abbrev qz488 := (@HSub.hSub Complex Complex Complex qz654 qz714 qz657)

noncomputable abbrev qz489 := (Complex.log qz714)

noncomputable abbrev qz184 := (@HSub.hSub Complex Complex Complex qz397 (@HMul.hMul Complex Complex Complex qz396 qz488 qz489) qz486)

noncomputable abbrev qz185 := qz486

noncomputable def ep1227 := @Enclosure.Complex.IsNear.of_eq qz181 (@HAdd.hAdd Complex Complex Complex qz4 (@HAdd.hAdd Complex Complex Complex qz4 qz184 qz80) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz75 (@HMul.hMul Complex Complex Complex qz74 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz83 qz185 (@HSub.hSub Int Int Int qz407 qz85 (@HMul.hMul Int Int Int qz408 qz86 (@Nat.cast Int instNatCastInt k)))))) Bool.true 116588469899802123191

noncomputable def ep1228 := @Enclosure.Complex.IsNear.addLitP (@HAdd.hAdd Complex Complex Complex qz4 qz184 qz80) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz75 (@HMul.hMul Complex Complex Complex qz74 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz83 qz185 (@HSub.hSub Int Int Int qz407 qz85 (@HMul.hMul Int Int Int qz408 qz86 (@Nat.cast Int instNatCastInt k))))) Bool.true 116588511430047243191 1125899906842624000

noncomputable def ep1229 := nat_lit 8011898644965288255627330584576

noncomputable def ep1230 := nat_lit 1822025552296187701049240951193600

noncomputable def ep1231 := @ep1228 18223126972957951051 99157000000000000000000 Bool.false 530281858273579458617 2251799813685248000 9345125042482924237 99157000000000000000000 Bool.false 2534805 68719476736 3 68719476736 Bool.true 4014060869 3435973836800 71261 51539607552000 Bool.true ep1229 116588469899802123191 1125899906842624000 ep1222 ep1220 Bool.false ep1230

noncomputable def ep1232 := @Enclosure.Complex.IsNear.addLitP qz184 qz80 Bool.true 117623143281849867191 1125899906842624000 36068000009148323977 198314000000000000000000

noncomputable def ep1233 := nat_lit 15281489370159152259530752

noncomputable def ep1234 := @ep1232 Bool.false 530281858273579458617 2251799813685248000 9345125042482924237 99157000000000000000000 Bool.false 120447 131072 1 524288 Bool.false 0 1 0 1 Bool.true ep1233 116588511430047243191 1125899906842624000 18223126972957951051 99157000000000000000000 Bool.false 530281858273579458617 530281858273579458617 2251799813685248000

noncomputable abbrev qz186 := (@HMul.hMul Complex Complex Complex qz396 qz488 qz489)

noncomputable def ep1235 := @Enclosure.Complex.IsNear.subLitP qz186 qz185 Bool.true 115089868491453963191 1125899906842624000 36068000009148323977 198314000000000000000000 Bool.false 138149472959320783269

noncomputable def ep1236 := @ep1235 450359962737049600 9345125042482924237 99157000000000000000000 Bool.false 9000 4000 0 1 Bool.false 285044 4000 0 1 Bool.true 470492573127399468764000 117623143281849867191 1125899906842624000 36068000009148323977 198314000000000000000000 Bool.false 424225486618863566893600 530281858273579458617 2251799813685248000 9345125042482924237 99157000000000000000000

noncomputable abbrev qz187 := qz488

noncomputable abbrev qz188 := qz489

noncomputable def ep1237 := @Enclosure.Complex.IsNear.mul qz187 qz188 Bool.true 115089868491453963191 1125899906842624000 36068000009148323977 198314000000000000000000 Bool.false 138149472959320783269 450359962737049600 9345125042482924237

noncomputable abbrev qz189 := (Complex.re qz488)

noncomputable abbrev qz190 := (Complex.re qz489)

noncomputable abbrev qz191 := (Complex.im qz488)

noncomputable abbrev qz192 := (Complex.im qz489)

noncomputable def ep1238 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 qz189 qz190) (@HMul.hMul Real Real Real qz0 qz191 qz192) 67256598883688515 9007199254740992 437500002082297 198314000000000000000 61748471675957513783 562949953421312000

noncomputable def ep1239 := nat_lit 518318688852231457231269057303412736

noncomputable def ep1240 := @Enclosure.Real.IsNear.mulLit_ff qz189 qz190 7000 4000 0 1 9608085554812645 2251799813685248 62500000297471 49578500000000000000

noncomputable def ep1241 := @Enclosure.Complex.IsNear.re_isNear qz187 Bool.false 7000 4000 0 1 Bool.false 285044 4000 0 1

noncomputable abbrev qz717 := (Enclosure.sfrac Bool.false 285044 4000)

noncomputable abbrev qz490 := qz717

noncomputable def ep1242 := @Enclosure.Complex.IsNear.of_eq qz187 (Complex.mk (Enclosure.sfrac Bool.false 7000 4000) qz490) Bool.false 7000 4000 0 1 Bool.false 285044 4000 0

noncomputable abbrev qz491 := (Complex.log (Complex.mk qz661 qz717))

noncomputable def ep1243 := @Enclosure.Complex.IsNear.of_eq qz188 qz491 Bool.false 9608085554812645 2251799813685248 62500000297471 49578500000000000000 Bool.false 866511439300003 562949953421312 500000000099157 198314000000000000000

noncomputable def ep1244 := nat_lit 6978934516418121119306957590566990474983178240

noncomputable def ep1245 := nat_lit 27093568119066231168646105666746753420361728

noncomputable def ep1246 := nat_lit 186727716917581015781510750302731412635648

noncomputable def ep1247 := BSN.log_dyadic_bound 15795081936 146867081936 3 2 ep1244 1048576 396628 ep1245 ep1246 226417 162662163872 131072000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 15795081936) (BSN.artanhQ 146867081936) 0 2 ep1245 ep1244 ep1246 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz718 := (Real.log (Enclosure.sfrac Bool.false 81331081936 16000000))

noncomputable def ep1248 := @Enclosure.Real.IsNear.mulLit_ff qz94 qz718 1 2 0 1 9608085554812645 1125899906842624 62500000297471 24789250000000000000 9608085554812645 2251799813685248 62500000297471 49578500000000000000 qz411 (BSN.isNear_log_sfrac 81331081936 16000000 9608085554812645 1125899906842624 62500000297471 24789250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 81331081936) qz663)) Bool.false 322393853399143169392640 37778931862957161709568 1000000004759536 396628000000000000000 9608085554812645 1125899906842624 62500000297471 24789250000000000000 (BSN.log_rat_reduce_isNear 81331081936 16000000 12 162662163872 131072000000 226417 1048576 24973259072661432 36028797018963968 396628 1000000000000000 rfl rfl rfl rfl (ep1247 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1249 := BSN.arctan_dyadic_bound_f 9000 285044 1 0 1048576 396628 0 1 1 0 1 1 33096 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 9000) (BSN.arctanEvenQ 285044) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 9000) (BSN.arctanOddQ 285044) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz492 := (Real.arctan (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 9000) (@Nat.cast Real Real.instNatCast 285044)))

noncomputable def ep1250 := @Enclosure.Real.IsNear.subLit_ff_p qz95 qz492 884279719003555 562949953421312 1 2000000000000000 33096 1048576 1 396628 908603098975439945728 866511439300003 562949953421312 500000000099157 198314000000000000000 qz96 (ep1249 rfl) rfl rfl

noncomputable abbrev qz493 := (Complex.mk qz661 qz717)

noncomputable abbrev qz494 := (Real.arctan (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 285044) (@Nat.cast Real Real.instNatCast 9000)))

noncomputable def ep1251 := @Enclosure.Complex.IsNear.re_isNear qz188 Bool.false 9608085554812645 2251799813685248 62500000297471 49578500000000000000 Bool.false 866511439300003 562949953421312 500000000099157 198314000000000000000 (ep1243 (@congrArg Complex Complex qz185 qz493 Complex.log (BSN.w_shift_mk qz145 Bool.false 142522 1000 2 qz146 rfl)) (@Enclosure.Complex.IsNear.of_parts qz491 Bool.false 9608085554812645 2251799813685248 62500000297471 49578500000000000000 Bool.false 866511439300003 562949953421312 500000000099157 198314000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz491) (@HMul.hMul Real Real Real qz0 qz94 qz718) Bool.false 9608085554812645 2251799813685248 62500000297471 49578500000000000000 (Enclosure.clog_re_eq 9000 285044 4000 81331081936 16000000 rfl rfl rfl) (ep1248 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz491) qz494 Bool.false 866511439300003 562949953421312 500000000099157 198314000000000000000 (Enclosure.clog_im_eq 9000 285044 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz494 (@HSub.hSub Real Real Real qz400 qz95 qz492) Bool.false 866511439300003 562949953421312 500000000099157 198314000000000000000 (BSN.arctan_recip 285044 9000 rfl rfl) ep1250))))

noncomputable def ep1252 := @Enclosure.Real.IsNear.mulLit_ff qz191 qz192 285044 4000 0 1 866511439300003 562949953421312 500000000099157 198314000000000000000

noncomputable def ep1253 := @Enclosure.Complex.IsNear.im_isNear qz187 Bool.false 7000 4000 0 1 Bool.false 285044 4000 0 1

noncomputable def ep1254 := @Enclosure.Complex.IsNear.im_isNear qz188 Bool.false 9608085554812645 2251799813685248 62500000297471 49578500000000000000 Bool.false 866511439300003 562949953421312 500000000099157 198314000000000000000 (ep1243 (@congrArg Complex Complex qz185 qz493 Complex.log (BSN.w_shift_mk qz145 Bool.false 142522 1000 2 qz146 rfl)) (@Enclosure.Complex.IsNear.of_parts qz491 Bool.false 9608085554812645 2251799813685248 62500000297471 49578500000000000000 Bool.false 866511439300003 562949953421312 500000000099157 198314000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz491) (@HMul.hMul Real Real Real qz0 qz94 qz718) Bool.false 9608085554812645 2251799813685248 62500000297471 49578500000000000000 (Enclosure.clog_re_eq 9000 285044 4000 81331081936 16000000 rfl rfl rfl) (ep1248 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz491) qz494 Bool.false 866511439300003 562949953421312 500000000099157 198314000000000000000 (Enclosure.clog_im_eq 9000 285044 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz494 (@HSub.hSub Real Real Real qz400 qz95 qz492) Bool.false 866511439300003 562949953421312 500000000099157 198314000000000000000 (BSN.arctan_recip 285044 9000 rfl rfl) ep1250))))

noncomputable abbrev qz193 := (@ep1242 1 (BSN.w_sub_half_mk qz453 Bool.false 142522 1000 2 qz454 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7000 4000) qz490 Bool.false 7000 4000 0 1 Bool.false 285044 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 7000 4000) (Enclosure.Real.IsNear.const Bool.false 285044 4000)))

noncomputable def ep1255 := @ep1238 35630500007066026977 198314000000000000000000 ep1239 115089868491453963191 1125899906842624000 36068000009148323977 198314000000000000000000 (@ep1240 67256598883688515 9007199254740992 437500002082297 198314000000000000000 (ep1241 qz193) ep1251 rfl) (@ep1252 61748471675957513783 562949953421312000 35630500007066026977 198314000000000000000000 (ep1253 qz193) ep1254 rfl) rfl

noncomputable def ep1256 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz189 qz192) (@HMul.hMul Real Real Real qz0 qz191 qz190) 6065580075100021 2251799813685248 3500000000694099 793256000000000000000 136936356944300779069 450359962737049600

noncomputable def ep1257 := nat_lit 311084957470513746418576376790515712

noncomputable def ep1258 := @Enclosure.Real.IsNear.mulLit_ff qz189 qz192 7000 4000 0 1 866511439300003 562949953421312 500000000099157 198314000000000000000

noncomputable def ep1259 := @Enclosure.Real.IsNear.mulLit_ff qz191 qz190 285044 4000 0 1 9608085554812645 2251799813685248 62500000297471 49578500000000000000

noncomputable def ep1260 := @ep1256 4453812521198080931 49578500000000000000000 ep1257 138149472959320783269 450359962737049600 9345125042482924237 99157000000000000000000 (@ep1258 6065580075100021 2251799813685248 3500000000694099 793256000000000000000 (ep1241 qz193) ep1254 rfl) (@ep1259 136936356944300779069 450359962737049600 4453812521198080931 49578500000000000000000 (ep1253 qz193) ep1251 rfl) rfl

noncomputable def ep1261 := @Enclosure.Complex.IsNear.of_eq qz185 qz493 Bool.false 9000 4000 0 1 Bool.false 285044 4000 0 1 (BSN.w_shift_mk qz145 Bool.false 142522 1000 2 qz146 rfl)

noncomputable abbrev qz495 := (ep1261 (@Enclosure.Complex.IsNear.mk qz661 qz717 Bool.false 9000 4000 0 1 Bool.false 285044 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 9000 4000) (Enclosure.Real.IsNear.const Bool.false 285044 4000)))

noncomputable abbrev qz194 := qz495

noncomputable def ep1262 := ep1236 (@ep1237 99157000000000000000000 (ep1255 rfl) (ep1260 rfl)) qz194 rfl rfl rfl rfl rfl rfl

noncomputable def ep1263 := @ep1234 9345125042482924237 99157000000000000000000 (ep1262 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@Enclosure.Complex.IsNear.mul qz99 (↑qz2) Bool.false 120447 131072 1 524288 Bool.false 0 1 0 1 (@ep558 131072 1 524288 (ep560 rfl) (ep562 rfl) rfl rfl) (@ep563 1 0 1 (ep565 rfl) (ep567 rfl) rfl rfl))

noncomputable abbrev qz496 := (@HPow.hPow Complex Int Complex qz659 qz714 (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) (@OfNat.ofNat Int 1 (@instOfNat 1)) (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (@OfNat.ofNat Int 2 (@instOfNat 2)) (@Nat.cast Int instNatCastInt 1))))

noncomputable abbrev qz195 := qz496

noncomputable def ep1264 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz75 (@HMul.hMul Complex Complex Complex qz74 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz83 qz185 (@HSub.hSub Int Int Int qz407 qz85 (@HMul.hMul Int Int Int qz408 qz86 (@Nat.cast Int instNatCastInt k))))) (@HAdd.hAdd Complex Complex Complex qz4 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz75 (@HMul.hMul Complex Complex Complex qz74 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz83 qz185 (@HSub.hSub Int Int Int qz407 qz85 (@HMul.hMul Int Int Int qz408 qz86 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 (@Rat.cast Complex Complex.instRatCast (bernoulli qz101)) qz102) qz195)) Bool.false 2534805 68719476736 3 68719476736

noncomputable def ep1265 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz75 (@HMul.hMul Complex Complex Complex qz74 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz83 qz185 (@HSub.hSub Int Int Int qz407 qz85 (@HMul.hMul Int Int Int qz408 qz86 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 (@Rat.cast Complex Complex.instRatCast (bernoulli qz101)) qz102) qz195) Bool.false 0 1 0 1 Bool.false

noncomputable def ep1266 := @ep1265 0 1 0 1 Bool.false 2534805 68719476736 3 68719476736 Bool.true 4014060869 3435973836800 71261 51539607552000 Bool.false 2534805 2534805 68719476736 3 68719476736 Bool.true 4014060869 4014060869 3435973836800 71261

noncomputable def ep1267 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz75 (@HMul.hMul Complex Complex Complex qz74 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz83 qz185 (@HSub.hSub Int Int Int qz407 qz85 (@HMul.hMul Int Int Int qz408 qz86 (@Nat.cast Int instNatCastInt k))))) (Complex.mk qz10 qz10) Bool.false 0 1 0 1 Bool.false

noncomputable def ep1268 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz81 (@Rat.cast Complex Complex.instRatCast (bernoulli qz101)) qz102) qz195 Bool.false 2534805 68719476736 3 68719476736 Bool.true 4014060869 3435973836800 71261 51539607552000

noncomputable abbrev qz196 := (Complex.re qz496)

noncomputable abbrev qz197 := (Complex.im qz496)

noncomputable def ep1269 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz81 (@Rat.cast Complex Complex.instRatCast (bernoulli qz101)) qz102)) qz196) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz81 (@Rat.cast Complex Complex.instRatCast (bernoulli qz101)) qz102)) qz197) 2534805 68719476736 3 68719476736 0 1 0

noncomputable def ep1270 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz81 (@Rat.cast Complex Complex.instRatCast (bernoulli qz101)) qz102)) qz196 1 12 0 1 7604415 17179869184 9 17179869184 2534805

noncomputable def ep1271 := @Enclosure.Complex.IsNear.re_isNear qz195 Bool.false 7604415 17179869184 9 17179869184 Bool.true 12042182607 858993459200 71261 4294967296000

noncomputable abbrev qz497 := (@HPow.hPow Complex Nat Complex qz664 qz714 1)

noncomputable abbrev qz198 := (@Inv.inv Complex Complex.instInv qz497)

noncomputable def ep1272 := @Enclosure.Complex.IsNear.of_eq qz195 qz198 Bool.false 7604415 17179869184 9 17179869184 Bool.true 12042182607 858993459200 71261

noncomputable def ep1273 := @Enclosure.Complex.IsNear.of_parts qz198 Bool.false 7604415 17179869184 9 17179869184 Bool.true 12042182607 858993459200 71261

noncomputable abbrev qz199 := (Complex.re qz497)

noncomputable abbrev qz200 := qz497

noncomputable def ep1274 := @Enclosure.Real.IsNear.mulLit_ff qz199 (@Inv.inv Real Real.instInv (@DFunLike.coe qz108 Complex (fun (x : Complex) => Real) qz109 Complex.normSq qz200)) 9000 4000 0 1 844935 4294967296 1 4294967296

noncomputable def ep1275 := @Enclosure.Complex.IsNear.re_isNear qz200 Bool.false 9000 4000 0 1 Bool.false 285044 4000 0 1

noncomputable def ep1276 := @Enclosure.Complex.IsNear.of_eq qz200 qz185 Bool.false 9000 4000 0 1 Bool.false 285044 4000 0

noncomputable def ep1277 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (@DFunLike.coe qz108 Complex (fun (x : Complex) => Real) qz109 Complex.normSq qz200)) Bool.false 844935 4294967296 1 4294967296 844935 4294967296 1

noncomputable abbrev qz201 := (Complex.im qz497)

noncomputable def ep1278 := @Enclosure.Real.IsNear.of_eq (@DFunLike.coe qz108 Complex (fun (x : Complex) => Real) qz109 Complex.normSq qz200) (@HAdd.hAdd Real Real Real qz420 (@HMul.hMul Real Real Real qz0 qz199 qz199) (@HMul.hMul Real Real Real qz0 qz201 qz201)) Bool.false 5083192621 1000000 0 1

noncomputable def ep1279 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz199 qz199) (@HMul.hMul Real Real Real qz0 qz201 qz201) 81 16 0 1 5078130121 1000000

noncomputable def ep1280 := @Enclosure.Real.IsNear.mulLit_ff qz199 qz199 9000 4000 0 1 9000 4000 0 1

noncomputable def ep1281 := @Enclosure.Real.IsNear.mulLit_ff qz201 qz201 285044 4000 0 1 285044 4000 0 1

noncomputable def ep1282 := @Enclosure.Complex.IsNear.im_isNear qz200 Bool.false 9000 4000 0 1 Bool.false 285044 4000 0 1

noncomputable abbrev qz202 := (ep1275 (@ep1276 1 (BSN.pow_one_c qz486) qz495))

noncomputable abbrev qz203 := (ep1282 (@ep1276 1 (BSN.pow_one_c qz486) qz495))

noncomputable def ep1283 := @ep1279 0 1 81331081936 5083192621 1000000 0 1 (@ep1280 81 16 0 1 qz202 qz202 rfl) (@ep1281 5078130121 1000000 0 1 qz203 qz203 rfl)

noncomputable def ep1284 := @Enclosure.Real.IsNear.inv_image (@DFunLike.coe qz108 Complex (fun (x : Complex) => Real) qz109 Complex.normSq qz200) 5083192621 1000000 0 1 422467 422468 2147483648 (ep1278 (Enclosure.Complex.normSq_eq_mul_add_mul qz200) (ep1283 rfl rfl)) rfl

noncomputable def ep1285 := @Enclosure.Real.IsNear.of_eq (Complex.re qz198) (@HMul.hMul Real Real Real qz0 qz199 (@Inv.inv Real Real.instInv (@DFunLike.coe qz108 Complex (fun (x : Complex) => Real) qz109 Complex.normSq qz200))) Bool.false 7604415 17179869184 9 17179869184 (Enclosure.Complex.inv_re_eq_mul qz200) (@ep1274 7604415 17179869184 9 17179869184 qz202 (@ep1277 4294967296 (ep1284 rfl rfl rfl rfl rfl) rfl) rfl)

noncomputable def ep1286 := @Enclosure.Real.IsNear.of_eq (Complex.im qz198) (@HMul.hMul Real Real Real qz0 (@Neg.neg Real Real.instNeg qz201) (@Inv.inv Real Real.instInv (@DFunLike.coe qz108 Complex (fun (x : Complex) => Real) qz109 Complex.normSq qz200))) Bool.true 12042182607 858993459200 71261 4294967296000 (Enclosure.Complex.inv_im_eq_mul qz200)

noncomputable def ep1287 := @Enclosure.Real.IsNear.mulLit_tf (@Neg.neg Real Real.instNeg qz201) (@Inv.inv Real Real.instInv (@DFunLike.coe qz108 Complex (fun (x : Complex) => Real) qz109 Complex.normSq qz200)) 285044 4000 0 1 844935 4294967296 1

noncomputable def ep1288 := @ep1287 4294967296 12042182607 858993459200 71261 4294967296000 (@Enclosure.Real.IsNear.neg qz201 Bool.false 285044 4000 0 1 qz203) (@ep1277 4294967296 (ep1284 rfl rfl rfl rfl rfl) rfl) rfl

noncomputable def ep1289 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz81 (@Rat.cast Complex Complex.instRatCast (bernoulli qz101)) qz102)) qz197 0 1 0 1 12042182607 858993459200 71261 4294967296000 0

noncomputable def ep1290 := @Enclosure.Complex.IsNear.im_isNear qz195 Bool.false 7604415 17179869184 9 17179869184 Bool.true 12042182607 858993459200 71261 4294967296000

noncomputable abbrev qz204 := (@ep1272 4294967296000 (BSN.zpow_one_sub_two_mul qz486 1 1 rfl rfl) (@ep1273 4294967296000 ep1285 (ep1286 ep1288)))

noncomputable def ep1291 := @ep1269 1 2534805 2534805 68719476736 3 68719476736 (@ep1270 68719476736 3 68719476736 ep577 (ep1271 qz204) rfl) (@ep1289 1 0 1 ep597 (ep1290 qz204) rfl) rfl

noncomputable def ep1292 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz81 (@Rat.cast Complex Complex.instRatCast (bernoulli qz101)) qz102)) qz197) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz81 (@Rat.cast Complex Complex.instRatCast (bernoulli qz101)) qz102)) qz196) 4014060869 3435973836800 71261 51539607552000 0 1 0

noncomputable def ep1293 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HDiv.hDiv Complex Complex Complex qz81 (@Rat.cast Complex Complex.instRatCast (bernoulli qz101)) qz102)) qz197 1 12 0 1 12042182607 858993459200 71261 4294967296000 4014060869

noncomputable def ep1294 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz81 (@Rat.cast Complex Complex.instRatCast (bernoulli qz101)) qz102)) qz196 0 1 0 1 7604415 17179869184 9 17179869184 0

noncomputable def ep1295 := @ep1292 1 4014060869 4014060869 3435973836800 71261 51539607552000 (@ep1293 3435973836800 71261 51539607552000 ep577 (ep1290 qz204) rfl) (@ep1294 1 0 1 ep597 (ep1271 qz204) rfl) rfl

noncomputable def ep1296 := @ep1266 51539607552000 (@ep1267 0 1 0 1 (BSN.stirling_sum_base qz185) qz115) (ep1268 (ep1291 rfl) (ep1295 rfl)) rfl rfl rfl rfl rfl

noncomputable def ep1297 := @ep1231 530279227618648350777 2251799813685248000 ep1223 ep1214 (ep1263 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep1264 Bool.true 4014060869 3435973836800 71261 51539607552000 (BSN.stirling_sum_succ qz185 0 1 rfl) (ep1296 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl

noncomputable def ep1298 := @Enclosure.Complex.IsNear.of_eq (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz182 (@Nat.cast Complex Complex.instNatCast j))) (BSN.logSumC qz145 2) Bool.false 9607143883232997 1125899906842624 62500000297471 24789250000000000000 Bool.false 878355616925091 281474976710656

noncomputable abbrev qz205 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz272 qz487 qz416))

noncomputable def ep1299 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz145 2) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.logSumC qz145 1) qz205) Bool.false 9607143883232997 1125899906842624 62500000297471 24789250000000000000 Bool.false 878355616925091 281474976710656 500000000099157 99157000000000000000

noncomputable def ep1300 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz145 1) qz205 Bool.false 9606977453250277 2251799813685248 62500000297471 49578500000000000000 Bool.false 882305107789219 562949953421312 500000000099157 198314000000000000000 Bool.false

noncomputable def ep1301 := nat_lit 43266729612622865223454411456512

noncomputable def ep1302 := nat_lit 988940507270655489297333878784

noncomputable abbrev qz206 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz272 qz487 (@Nat.cast Complex Complex.instNatCast 0)))

noncomputable def ep1303 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz145 1) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.logSumC qz145 0) qz206) Bool.false 9606977453250277 2251799813685248 62500000297471 49578500000000000000 Bool.false 882305107789219 562949953421312 500000000099157 198314000000000000000

noncomputable def ep1304 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz145 0) qz206 Bool.false 0 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable abbrev qz498 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz717))

noncomputable def ep1305 := @Enclosure.Complex.IsNear.of_eq qz206 qz498 Bool.false 9606977453250277 2251799813685248 62500000297471 49578500000000000000 Bool.false 882305107789219 562949953421312 500000000099157 198314000000000000000

noncomputable def ep1306 := nat_lit 6963740948466404094206757372125291966183178240

noncomputable def ep1307 := nat_lit 26788936044176596336505121553200882060361728

noncomputable def ep1308 := nat_lit 182973355909461351163684728523029652635648

noncomputable def ep1309 := BSN.log_dyadic_bound 15715081936 146787081936 3 2 ep1306 1048576 396628 ep1307 ep1308 225385 162502163872 131072000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 15715081936) (BSN.artanhQ 146787081936) 0 2 ep1307 ep1306 ep1308 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep1310 := @Enclosure.Real.IsNear.mulLit_ff qz94 (Real.log (Enclosure.sfrac Bool.false 81251081936 16000000)) 1 2 0 1 9606977453250277 1125899906842624 62500000297471 24789250000000000000 9606977453250277 2251799813685248 62500000297471 49578500000000000000 qz411 (BSN.isNear_log_sfrac 81251081936 16000000 9606977453250277 1125899906842624 62500000297471 24789250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 81251081936) qz663)) Bool.false 322356671680619598577664 37778931862957161709568 1000000004759536 396628000000000000000 9606977453250277 1125899906842624 62500000297471 24789250000000000000 (BSN.log_rat_reduce_isNear 81251081936 16000000 12 162502163872 131072000000 225385 1048576 24973259072661432 36028797018963968 396628 1000000000000000 rfl rfl rfl rfl (ep1309 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1311 := BSN.arctan_dyadic_bound_f 1000 285044 1 0 1048576 396628 0 1 1 0 1 1 3678 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 285044) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 285044) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz499 := (@Nat.cast Real Real.instNatCast 285044)

noncomputable def ep1312 := @Enclosure.Real.IsNear.subLit_ff_p qz95 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz665 qz499)) 884279719003555 562949953421312 1 2000000000000000 3678 1048576 1 396628 925163960705188102144 882305107789219 562949953421312 500000000099157 198314000000000000000 qz96 (ep1311 rfl) rfl rfl

noncomputable abbrev qz207 := (@HAdd.hAdd Complex Complex Complex qz272 qz487 (@Nat.cast Complex Complex.instNatCast 0))

noncomputable abbrev qz500 := (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz717)

noncomputable def ep1313 := @ep1304 9606977453250277 2251799813685248 62500000297471 49578500000000000000 Bool.false 882305107789219 562949953421312 500000000099157 198314000000000000000 Bool.false 9606977453250277 9606977453250277 2251799813685248 62500000297471 49578500000000000000 Bool.false 882305107789219 882305107789219 562949953421312 500000000099157 198314000000000000000 (@Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz145 0) (Complex.mk qz10 qz10) Bool.false 0 1 0 1 Bool.false 0 1 0 1 (BSN.log_sum_c_base qz145) qz115) (ep1305 (@congrArg Complex Complex qz207 qz500 Complex.log (BSN.w_shift_mk qz145 Bool.false 142522 1000 0 qz146 rfl)) (@Enclosure.Complex.IsNear.of_parts qz498 Bool.false 9606977453250277 2251799813685248 62500000297471 49578500000000000000 Bool.false 882305107789219 562949953421312 500000000099157 198314000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz498) (@HMul.hMul Real Real Real qz0 qz94 (Real.log (Enclosure.sfrac Bool.false 81251081936 16000000))) Bool.false 9606977453250277 2251799813685248 62500000297471 49578500000000000000 (Enclosure.clog_re_eq 1000 285044 4000 81251081936 16000000 rfl rfl rfl) (ep1310 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz498) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz499 qz665)) Bool.false 882305107789219 562949953421312 500000000099157 198314000000000000000 (Enclosure.clog_im_eq 1000 285044 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz499 qz665)) (@HSub.hSub Real Real Real qz400 qz95 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz665 qz499))) Bool.false 882305107789219 562949953421312 500000000099157 198314000000000000000 (BSN.arctan_recip 285044 1000 rfl rfl) ep1312)))) rfl rfl

noncomputable abbrev qz501 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz717))

noncomputable def ep1314 := @Enclosure.Complex.IsNear.of_eq qz205 qz501 Bool.false 9607310313215717 2251799813685248 62500000297471 49578500000000000000 Bool.false 874406126060963 562949953421312 500000000099157 198314000000000000000

noncomputable def ep1315 := nat_lit 6968296411362420867823797898365641518823178240

noncomputable def ep1316 := nat_lit 26880110980773027504535630498112643468361728

noncomputable def ep1317 := nat_lit 184093663268677292671652676624940180635648

noncomputable def ep1318 := BSN.log_dyadic_bound 15739081936 146811081936 3 2 ep1315 1048576 396628 ep1316 ep1317 225695 162550163872 131072000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 15739081936) (BSN.artanhQ 146811081936) 0 2 ep1316 ep1315 ep1317 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep1319 := @Enclosure.Real.IsNear.mulLit_ff qz94 (Real.log (Enclosure.sfrac Bool.false 81275081936 16000000)) 1 2 0 1 9607310313215717 1125899906842624 62500000297471 24789250000000000000 9607310313215717 2251799813685248 62500000297471 49578500000000000000 qz411 (BSN.isNear_log_sfrac 81275081936 16000000 9607310313215717 1125899906842624 62500000297471 24789250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 81275081936) qz663)) Bool.false 322367840607695477407744 37778931862957161709568 1000000004759536 396628000000000000000 9607310313215717 1125899906842624 62500000297471 24789250000000000000 (BSN.log_rat_reduce_isNear 81275081936 16000000 12 162550163872 131072000000 225695 1048576 24973259072661432 36028797018963968 396628 1000000000000000 rfl rfl rfl rfl (ep1318 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1320 := BSN.arctan_dyadic_bound_f 5000 285044 1 0 1048576 396628 0 1 1 0 1 1 18391 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 5000) (BSN.arctanEvenQ 285044) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 5000) (BSN.arctanOddQ 285044) 0 0 rfl) rfl rfl rfl

noncomputable def ep1321 := @Enclosure.Real.IsNear.subLit_ff_p qz95 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz666 qz499)) 884279719003555 562949953421312 1 2000000000000000 18391 1048576 1 396628 916881278040500338688 874406126060963 562949953421312 500000000099157 198314000000000000000 qz96 (ep1320 rfl) rfl rfl

noncomputable abbrev qz208 := (@HAdd.hAdd Complex Complex Complex qz272 qz487 qz416)

noncomputable abbrev qz502 := (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz717)

noncomputable def ep1322 := @ep1300 9607310313215717 2251799813685248 62500000297471 49578500000000000000 Bool.false 874406126060963 562949953421312 500000000099157 198314000000000000000 Bool.false ep1301 9607143883232997 1125899906842624 62500000297471 24789250000000000000 Bool.false ep1302 878355616925091 281474976710656 500000000099157 99157000000000000000 (ep1303 (BSN.log_sum_c_succ qz145 0 1 rfl) (ep1313 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1314 (@congrArg Complex Complex qz208 qz502 Complex.log (BSN.w_shift_mk qz145 Bool.false 142522 1000 1 qz146 rfl)) (@Enclosure.Complex.IsNear.of_parts qz501 Bool.false 9607310313215717 2251799813685248 62500000297471 49578500000000000000 Bool.false 874406126060963 562949953421312 500000000099157 198314000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz501) (@HMul.hMul Real Real Real qz0 qz94 (Real.log (Enclosure.sfrac Bool.false 81275081936 16000000))) Bool.false 9607310313215717 2251799813685248 62500000297471 49578500000000000000 (Enclosure.clog_re_eq 5000 285044 4000 81275081936 16000000 rfl rfl rfl) (ep1319 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz501) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz499 qz666)) Bool.false 874406126060963 562949953421312 500000000099157 198314000000000000000 (Enclosure.clog_im_eq 5000 285044 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz499 qz666)) (@HSub.hSub Real Real Real qz400 qz95 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz666 qz499))) Bool.false 874406126060963 562949953421312 500000000099157 198314000000000000000 (BSN.arctan_recip 285044 5000 rfl rfl) ep1321)))) rfl rfl

noncomputable def ep1323 := @ep1224 ep1214 Bool.false 9607143883232997 1125899906842624 62500000297471 24789250000000000000 Bool.false 878355616925091 281474976710656 500000000099157 99157000000000000000 Bool.true ep1225 126195613783035120191 1125899906842624000 ep1219 ep1220 Bool.false ep1226 523252382683247622777 2251799813685248000 ep1216 ep1214 (@ep1227 1125899906842624000 ep1222 ep1220 Bool.false 530279227618648350777 2251799813685248000 ep1223 ep1214 (BSN.logGammaStirling_unfold 1 qz185) (ep1297 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (@ep1298 500000000099157 99157000000000000000 (BSN.log_sum_c_eq qz145 2) (ep1299 (BSN.log_sum_c_succ qz145 1 2 rfl) (ep1322 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)))

noncomputable abbrev qz209 := (@HDiv.hDiv Real Real Real qz270 qz453 (2 : Real))

noncomputable def ep1324 := @Enclosure.Real.IsNear.mulLit_ff qz209 (Real.log Real.pi) 142522 2000 0 1 75021 65536 1 262144 5346071481 65536000 71261 262144000 (@Enclosure.Real.IsNear.of_eq qz209 (Enclosure.sfrac Bool.false 142522 2000) Bool.false 142522 2000 0 1 (BSN.t_half_eq qz145 Bool.false 142522 1000 qz146) (Enclosure.Real.IsNear.const Bool.false 142522 2000)) EMRow49.d5 rfl

noncomputable def ep1325 := @ep1217 71261 262144000 ep1218 339562765299461339769 2251799813685248000 ep1213 ep1214 (@ep1221 ep1216 ep1214 (ep1323 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) ep1324 rfl rfl

noncomputable def ep1326 := nat_lit 8337866198797707953301835803494637833778361481594573029426380173510816825753185

noncomputable def ep1327 := nat_lit 16740240528573549575895808618059294550247188042465638545505232051421437116001

noncomputable def ep1328 := nat_lit 21810165369328687464096214842818622135385784623536080233709701507302218883546721

noncomputable def ep1329 := BSN.sin_dyadic_bound_f 3372641749 2147483648 3 2 1048576 397016 ep1326 ep95 ep1327 ep1328 ep98 ep1327 1048575 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3372641749) qz20 0 2 ep1326 ep95 ep1327 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3372641749) qz21 0 2 ep1328 ep98 ep1327 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1330 := @ep1212 524288 Bool.false 1048575 1048576 1 198314 (@ep1215 79060617 524288 195 524288 ep1325 rfl) (Enclosure.sfrac_false_div 79060617 524288) (BSN.cos_reduce3 qz716 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 118664282240328321204224) qz19) 226375608064910080 72057594037927936 Bool.false 1048575 1048576 23 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q3 79060617 524288 226375608064910080 72057594037927936 23 118664282240328321204224 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1048575 1048576 118664282240328321204224 75557863725914323419136 3372641749 2147483648 397016 396628 (ep1329 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1331 := nat_lit 8802904102961253135104213

noncomputable def ep1332 := nat_lit 1206042876333168877633536000

noncomputable def ep1333 := nat_lit 830485279492007918381436711037

noncomputable def ep1334 := nat_lit 119587593488568026399508529152000

noncomputable abbrev qz503 := (@HPow.hPow Complex Complex Complex qz542 qz667 qz682)

noncomputable abbrev qz210 := qz503

noncomputable abbrev qz211 := (@HAdd.hAdd Complex Complex Complex qz272 (@HDiv.hDiv Complex Complex Complex qz405 qz427 (@HSub.hSub Complex Complex Complex qz397 qz451 (1 : Complex))) qz404)

noncomputable def ep1335 := @Enclosure.Complex.IsNear.of_eq (zetaApproximant qz142 1 36) (@HAdd.hAdd Complex Complex Complex qz4 (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 36, @HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast n) qz143) (@HMul.hMul Complex Complex Complex qz74 qz210 (@HAdd.hAdd Complex Complex Complex qz4 qz211 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz82 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz124 qz125 (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1))))))) Bool.false ep1207 ep1208 ep1209

noncomputable def ep1336 := @Enclosure.Complex.IsNear.addLitP (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 36, @HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast n) qz143) (@HMul.hMul Complex Complex Complex qz74 qz210 (@HAdd.hAdd Complex Complex Complex qz4 qz211 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz82 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz124 qz125 (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))))) Bool.false 1735596327679 1099511627776 749618645041965 109024274475384832

noncomputable def ep1337 := nat_lit 491606604263059668999332059

noncomputable def ep1338 := nat_lit 101516639055305719757199787

noncomputable def ep1339 := nat_lit 8393777737691822489268327037

noncomputable def ep1340 := nat_lit 231732683065718921162217382798671478784

noncomputable def ep1341 := nat_lit 4839447709701478268217608241512710144

noncomputable def ep1342 := @ep1336 Bool.false 50287441207 549755813888 93684393711493 13628034309423104 Bool.true 768971666204172618032191 ep1208 ep1337 ep1210 Bool.true ep1338 ep1332 ep1339 ep1334 Bool.false ep1340 ep1207 ep1208 ep1209 ep1210 Bool.false ep1341 ep1331 ep1332

noncomputable def ep1343 := @Enclosure.Complex.IsNear.of_eq (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 36, @HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast n) qz143) (BSN.headSumC qz142 36) Bool.false 1735596327679 1099511627776 749618645041965 109024274475384832 Bool.false 50287441207 549755813888 93684393711493

noncomputable abbrev qz719 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 35) qz143)

noncomputable def ep1344 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz142 36) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz142 35) qz719) Bool.false 1735596327679 1099511627776 749618645041965 109024274475384832 Bool.false 50287441207 549755813888 93684393711493 13628034309423104

noncomputable def ep1345 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz142 35) qz719 Bool.false 1848374421497 1099511627776 736193663117013 109024274475384832 Bool.true 23573137277 549755813888 368015309482221 54512137237692416 Bool.true

noncomputable abbrev qz720 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 34) qz143)

noncomputable def ep1346 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz142 35) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz142 34) qz720) Bool.false 1848374421497 1099511627776 736193663117013 109024274475384832 Bool.true 23573137277 549755813888 368015309482221 54512137237692416

noncomputable def ep1347 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz142 34) qz720 Bool.false 1660286235185 1099511627776 722532959824227 109024274475384832 Bool.true 60537600697 1099511627776 722466242830033 109024274475384832 Bool.false

noncomputable abbrev qz721 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 33) qz143)

noncomputable def ep1348 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz142 34) (@HAdd.hAdd Complex Complex Complex qz4 qz172 qz721) Bool.false 1660286235185 1099511627776 722532959824227 109024274475384832 Bool.true 60537600697 1099511627776 722466242830033 109024274475384832

noncomputable def ep1349 := @Enclosure.Complex.IsNear.addLitP qz172 qz721 Bool.false 866239839741 549755813888 354375500489335 54512137237692416 Bool.false 116724576395 1099511627776 708627207727921 109024274475384832 Bool.true

noncomputable abbrev qz212 := (@HMul.hMul Real Real Real qz267 qz453 qz671)

noncomputable def ep1350 := @Enclosure.Complex.IsNear.of_eq qz721 (Complex.mk (@HMul.hMul Real Real Real qz0 qz429 (Real.cos qz212)) (@HMul.hMul Real Real Real qz0 qz429 (@Neg.neg Real Real.instNeg (Real.sin qz212)))) Bool.true 72193444297 1099511627776 13781958845557 109024274475384832 Bool.true 44315544273 274877906944 432469846941 3407008577355776 (BSN.cpow_neg_s_mk qz145 142522 1000 33 qz146 rfl)

noncomputable def ep1351 := @Enclosure.Real.IsNear.mulLit_ff qz145 qz671 142522 1000 0 1 15746868335186131 4503599627370496 100000000099157 19831400000000000000 1122137584433698881191 2251799813685248000 7126100007066026977 9915700000000000000000 qz147 (BSN.isNear_log_sfrac 33 1 15746868335186131 4503599627370496 100000000099157 19831400000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz672) Bool.false 66047152845744529997824 18889465931478580854784 1000000000991570 198314000000000000000 15746868335186131 4503599627370496 100000000099157 19831400000000000000 (BSN.log_rat_reduce_isNear 33 1 5 66 64 16133 524288 24973259072661432 36028797018963968 198314 1000000000000000 rfl rfl rfl rfl (ep655 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1352 := nat_lit 475854886765134805582858440705884416

noncomputable def ep1353 := BSN.sin_dyadic_bound_f 830555452 2147483648 2 1 1048576 397016 ep1352 ep70 ep1352 ep1352 ep71 ep1352 395509 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 830555452) qz20 0 1 ep1352 ep70 ep1352 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 830555452) qz21 0 1 ep1352 ep71 ep1352 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz504 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 16329251) (@Nat.cast Real Real.instNatCast 32768))

noncomputable def ep1354 := @Enclosure.Real.IsNear.cos_image qz212 qz504 Bool.false 16329251 32768 377 524288 Bool.true 395509 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz212 Bool.false 1122137584433698881191 2251799813685248000 7126100007066026977 9915700000000000000000 16329251 32768 377 524288 (ep1351 rfl) rfl) (Enclosure.sfrac_false_div 16329251 32768) (BSN.cos_reduce1 qz504 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 1826410755358973755392) qz621) 226375608064910080 72057594037927936 Bool.false 395509 1048576 79 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q1 16329251 32768 226375608064910080 72057594037927936 79 1826410755358973755392 4722366482869645213696 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 395509 1048576 1826410755358973755392 4722366482869645213696 830555452 2147483648 397016 396628 (ep1353 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1355 := BSN.cos_dyadic_bound_f 830555452 2147483648 2 1 1048576 397016 ep1352 ep66 ep1352 ep1352 ep67 ep1352 971124 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 830555452) qz15 0 1 ep1352 ep66 ep1352 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 830555452) qz16 0 1 ep1352 ep67 ep1352 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1356 := @Enclosure.Real.IsNear.sin_image qz212 qz504 Bool.false 16329251 32768 377 524288 Bool.false 971124 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz212 Bool.false 1122137584433698881191 2251799813685248000 7126100007066026977 9915700000000000000000 16329251 32768 377 524288 (ep1351 rfl) rfl) (Enclosure.sfrac_false_div 16329251 32768) (BSN.sin_reduce1 qz504 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 1826410755358973755392) qz621) 226375608064910080 72057594037927936 Bool.false 971124 1048576 79 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q1 16329251 32768 226375608064910080 72057594037927936 79 1826410755358973755392 4722366482869645213696 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 971124 1048576 1826410755358973755392 4722366482869645213696 830555452 2147483648 397016 396628 (ep1355 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1357 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz429 (Real.cos qz212)) (@HMul.hMul Real Real Real qz0 qz429 (@Neg.neg Real Real.instNeg (Real.sin qz212))) Bool.true 72193444297 1099511627776 13781958845557 109024274475384832 Bool.true 44315544273 274877906944 432469846941 3407008577355776 (@Enclosure.Real.IsNear.mulLit_ft qz429 (Real.cos qz212) 182533 1048576 1 1048576 395509 1048576 37644333 51986825216 72193444297 1099511627776 13781958845557 109024274475384832 qz433 (@Enclosure.Real.IsNear.recentre' (Real.cos qz212) Bool.true 395509 1048576 75288666 103973650432 395509 1048576 37644333 51986825216 (ep1354 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz429 (@Neg.neg Real Real.instNeg (Real.sin qz212)) 182533 1048576 1 1048576 242781 262144 37644333 51986825216 44315544273 274877906944 432469846941 3407008577355776 qz433 (@Enclosure.Real.IsNear.neg (Real.sin qz212) Bool.false 242781 262144 37644333 51986825216 (@Enclosure.Real.IsNear.recentre' (Real.sin qz212) Bool.false 971124 1048576 75288666 103973650432 242781 262144 37644333 51986825216 (ep1356 rfl rfl) rfl)) rfl)

noncomputable def ep1358 := @ep1349 72193444297 1099511627776 13781958845557 109024274475384832 Bool.true 44315544273 274877906944 432469846941 3407008577355776 Bool.false 912752010511173057249280 1660286235185 1099511627776 722532959824227 109024274475384832 Bool.true 16640448971002995539968 60537600697 1099511627776 722466242830033 109024274475384832 EMRow49.d16 (ep1350 ep1357) rfl rfl

noncomputable abbrev qz213 := (@HMul.hMul Real Real Real qz267 qz453 qz673)

noncomputable def ep1359 := @Enclosure.Complex.IsNear.of_eq qz720 (Complex.mk (@HMul.hMul Real Real Real qz0 qz434 (Real.cos qz213)) (@HMul.hMul Real Real Real qz0 qz434 (@Neg.neg Real Real.instNeg (Real.sin qz213)))) Bool.false 23511023289 137438953472 6830351646393 54512137237692416 Bool.false 13391326143 1099511627776 13564376134409 109024274475384832 (BSN.cpow_neg_s_mk qz145 142522 1000 34 qz146 rfl)

noncomputable def ep1360 := @Enclosure.Real.IsNear.mulLit_ff qz145 qz673 142522 1000 0 1 15881309401485523 4503599627370496 100000000099157 19831400000000000000 1131717989259259854503 2251799813685248000 7126100007066026977 9915700000000000000000 qz147 (BSN.isNear_log_sfrac 34 1 15881309401485523 4503599627370496 100000000099157 19831400000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz674) Bool.false 66611039547888335060992 18889465931478580854784 1000000000991570 198314000000000000000 15881309401485523 4503599627370496 100000000099157 19831400000000000000 (BSN.log_rat_reduce_isNear 34 1 5 68 64 31784 524288 24973259072661432 36028797018963968 198314 1000000000000000 rfl rfl rfl rfl (ep670 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1361 := nat_lit 6930838799977989080157599912394348414540845650309974553267613638118797150781440

noncomputable def ep1362 := nat_lit 11574901161686908320655513118096619570018054074555427124445303078993721819136

noncomputable def ep1363 := nat_lit 18133456540918668786941224177889232273065042710881605519404171894849907464339456

noncomputable def ep1364 := BSN.sin_dyadic_bound_f 3220621304 2147483648 3 2 1048576 397016 ep1361 ep95 ep1362 ep1363 ep98 ep1362 1045928 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3220621304) qz20 0 2 ep1361 ep95 ep1362 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3220621304) qz21 0 2 ep1363 ep98 ep1362 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz505 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 526997255) qz26)

noncomputable def ep1365 := @Enclosure.Real.IsNear.cos_image qz213 qz505 Bool.false 526997255 1048576 755 1048576 Bool.false 1045928 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz213 Bool.false 1131717989259259854503 2251799813685248000 7126100007066026977 9915700000000000000000 526997255 1048576 755 1048576 (ep1360 rfl) rfl) (Enclosure.sfrac_false_div 526997255 1048576) (BSN.cos_reduce3 qz505 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 226631076660278816931840) qz27) 226375608064910080 72057594037927936 Bool.false 1045928 1048576 79 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q3 526997255 1048576 226375608064910080 72057594037927936 79 226631076660278816931840 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1045928 1048576 226631076660278816931840 151115727451828646838272 3220621304 2147483648 397016 396628 (ep1364 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1366 := nat_lit 3855610400504077003785624623827125394553811163094232719426205489212217849020416

noncomputable def ep1367 := nat_lit 11543681399188857194715562845245182944521397381133587304029725861478666103422976

noncomputable def ep1368 := BSN.cos_dyadic_bound_f 3220621304 2147483648 3 2 1048576 397016 ep1366 ep102 ep1362 ep1367 ep104 ep1362 74467 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3220621304) qz15 0 2 ep1366 ep102 ep1362 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3220621304) qz16 0 2 ep1367 ep104 ep1362 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1369 := @Enclosure.Real.IsNear.sin_image qz213 qz505 Bool.false 526997255 1048576 755 1048576 Bool.true 74467 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz213 Bool.false 1131717989259259854503 2251799813685248000 7126100007066026977 9915700000000000000000 526997255 1048576 755 1048576 (ep1360 rfl) rfl) (Enclosure.sfrac_false_div 526997255 1048576) (BSN.sin_reduce3 qz505 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 226631076660278816931840) qz27) 226375608064910080 72057594037927936 Bool.false 74467 1048576 79 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q3 526997255 1048576 226375608064910080 72057594037927936 79 226631076660278816931840 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 74467 1048576 226631076660278816931840 151115727451828646838272 3220621304 2147483648 397016 396628 (ep1368 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1370 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz434 (Real.cos qz213)) (@HMul.hMul Real Real Real qz0 qz434 (@Neg.neg Real Real.instNeg (Real.sin qz213))) Bool.false 23511023289 137438953472 6830351646393 54512137237692416 Bool.false 13391326143 1099511627776 13564376134409 109024274475384832 (@Enclosure.Real.IsNear.mulLit_ff qz434 (Real.cos qz213) 179829 1048576 1 1048576 130741 131072 75387823 103973650432 23511023289 137438953472 6830351646393 54512137237692416 qz438 (@Enclosure.Real.IsNear.recentre' (Real.cos qz213) Bool.false 1045928 1048576 150775646 207947300864 130741 131072 75387823 103973650432 (ep1365 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz434 (@Neg.neg Real Real.instNeg (Real.sin qz213)) 179829 1048576 1 1048576 74467 1048576 75387823 103973650432 13391326143 1099511627776 13564376134409 109024274475384832 qz438 (@Enclosure.Real.IsNear.neg (Real.sin qz213) Bool.true 74467 1048576 75387823 103973650432 (@Enclosure.Real.IsNear.recentre' (Real.sin qz213) Bool.true 74467 1048576 150775646 207947300864 74467 1048576 75387823 103973650432 (ep1369 rfl rfl) rfl)) rfl)

noncomputable def ep1371 := @ep1347 23511023289 137438953472 6830351646393 54512137237692416 Bool.false 13391326143 1099511627776 13564376134409 109024274475384832 Bool.false 254038646114961099587584 1848374421497 1099511627776 736193663117013 109024274475384832 Bool.true 51837877078442748411904 23573137277 549755813888 368015309482221 54512137237692416 (ep1348 (BSN.head_sum_c_succ qz142 33 34 rfl rfl) (ep1358 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1359 ep1370) rfl rfl

noncomputable abbrev qz214 := (@HMul.hMul Real Real Real qz267 qz453 qz675)

noncomputable def ep1372 := @Enclosure.Complex.IsNear.of_eq qz719 (Complex.mk (@HMul.hMul Real Real Real qz0 qz439 (Real.cos qz214)) (@HMul.hMul Real Real Real qz0 qz439 (@Neg.neg Real Real.instNeg (Real.sin qz214)))) Bool.true 56389046909 549755813888 1678122740619 13628034309423104 Bool.false 18465144621 137438953472 6722265363751 54512137237692416 (BSN.cpow_neg_s_mk qz145 142522 1000 35 qz146 rfl)

noncomputable def ep1373 := @Enclosure.Real.IsNear.mulLit_ff qz145 qz675 142522 1000 0 1 16011859227414739 4503599627370496 100000000099157 19831400000000000000 1141021100404801715879 2251799813685248000 7126100007066026977 9915700000000000000000 qz147 (BSN.isNear_log_sfrac 35 1 16011859227414739 4503599627370496 100000000099157 19831400000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz676) Bool.false 67158605204982549446656 18889465931478580854784 1000000000991570 198314000000000000000 16011859227414739 4503599627370496 100000000099157 19831400000000000000 (BSN.log_rat_reduce_isNear 35 1 5 70 64 46982 524288 24973259072661432 36028797018963968 198314 1000000000000000 rfl rfl rfl rfl (ep684 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1374 := nat_lit 541633083124003509911439278543229422670241633270062403505806830555739384978561

noncomputable def ep1375 := nat_lit 229606718660117700315926511113313344404376348043233702656758016337618148481

noncomputable def ep1376 := nat_lit 1624440035934690294333685982607461641321916147114100743112106975634542918638721

noncomputable def ep1377 := BSN.cos_dyadic_bound_f 1972981777 2147483648 3 2 1048576 397016 ep1374 ep102 ep1375 ep1376 ep104 ep1375 636298 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1972981777) qz15 0 2 ep1374 ep102 ep1375 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1972981777) qz16 0 2 ep1376 ep104 ep1375 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz506 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 265664677) qz17)

noncomputable def ep1378 := @Enclosure.Real.IsNear.cos_image qz214 qz506 Bool.false 265664677 524288 755 1048576 Bool.true 636298 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz214 Bool.false 1141021100404801715879 2251799813685248000 7126100007066026977 9915700000000000000000 265664677 524288 755 1048576 (ep1373 rfl) rfl) (Enclosure.sfrac_false_div 265664677 524288) (BSN.cos_reduce2 qz506 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 69418125000846254014464) qz19) 226375608064910080 72057594037927936 Bool.false 636298 1048576 80 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q2 265664677 524288 226375608064910080 72057594037927936 80 69418125000846254014464 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 636298 1048576 69418125000846254014464 75557863725914323419136 1972981777 2147483648 397016 396628 (ep1377 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1379 := nat_lit 974755864248278223680337960168922310130911438807677739348326888587260798442625

noncomputable def ep1380 := nat_lit 2552560281200993252409897443233946400166208587551847891346078528559231661776001

noncomputable def ep1381 := BSN.sin_dyadic_bound_f 1972981777 2147483648 3 2 1048576 397016 ep1379 ep95 ep1375 ep1380 ep98 ep1375 833448 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1972981777) qz20 0 2 ep1379 ep95 ep1375 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1972981777) qz21 0 2 ep1380 ep98 ep1375 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1382 := @Enclosure.Real.IsNear.sin_image qz214 qz506 Bool.false 265664677 524288 755 1048576 Bool.true 833448 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz214 Bool.false 1141021100404801715879 2251799813685248000 7126100007066026977 9915700000000000000000 265664677 524288 755 1048576 (ep1373 rfl) rfl) (Enclosure.sfrac_false_div 265664677 524288) (BSN.sin_reduce2 qz506 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 69418125000846254014464) qz19) 226375608064910080 72057594037927936 Bool.false 833448 1048576 80 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q2 265664677 524288 226375608064910080 72057594037927936 80 69418125000846254014464 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 833448 1048576 69418125000846254014464 75557863725914323419136 1972981777 2147483648 397016 396628 (ep1381 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1383 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz439 (Real.cos qz214)) (@HMul.hMul Real Real Real qz0 qz439 (@Neg.neg Real Real.instNeg (Real.sin qz214))) Bool.true 56389046909 549755813888 1678122740619 13628034309423104 Bool.false 18465144621 137438953472 6722265363751 54512137237692416 (@Enclosure.Real.IsNear.mulLit_ft qz439 (Real.cos qz214) 177241 1048576 1 1048576 318149 524288 75387823 103973650432 56389046909 549755813888 1678122740619 13628034309423104 qz443 (@Enclosure.Real.IsNear.recentre' (Real.cos qz214) Bool.true 636298 1048576 150775646 207947300864 318149 524288 75387823 103973650432 (ep1378 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz439 (@Neg.neg Real Real.instNeg (Real.sin qz214)) 177241 1048576 1 1048576 104181 131072 75387823 103973650432 18465144621 137438953472 6722265363751 54512137237692416 qz443 (@Enclosure.Real.IsNear.neg (Real.sin qz214) Bool.true 104181 131072 75387823 103973650432 (@Enclosure.Real.IsNear.recentre' (Real.sin qz214) Bool.true 833448 1048576 150775646 207947300864 104181 131072 75387823 103973650432 (ep1382 rfl rfl) rfl)) rfl)

noncomputable def ep1384 := @ep1345 56389046909 549755813888 1678122740619 13628034309423104 Bool.false 18465144621 137438953472 6722265363751 54512137237692416 Bool.false 954154171704192587005952 1735596327679 1099511627776 749618645041965 109024274475384832 Bool.false 6911453292274808520704 50287441207 549755813888 93684393711493 13628034309423104 (ep1346 (BSN.head_sum_c_succ qz142 34 35 rfl rfl) (ep1371 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1372 ep1383) rfl rfl

noncomputable def ep1385 := @Enclosure.Complex.IsNear.mul qz210 (@HAdd.hAdd Complex Complex Complex qz4 qz211 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz82 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz124 qz125 (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1))))) Bool.true 768971666204172618032191 ep1208 ep1337 ep1210 Bool.true

noncomputable def ep1386 := nat_lit 4824171505332675510534144

noncomputable def ep1387 := nat_lit 28930974666858545116574911

noncomputable abbrev qz215 := (Complex.re qz503)

noncomputable abbrev qz216 := (Complex.im qz503)

noncomputable def ep1388 := @Enclosure.Real.IsNear.subLit_tt_n (@HMul.hMul Real Real Real qz0 qz215 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz211 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz82 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz124 qz125 (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz216 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz211 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz82 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz124 qz125 (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1))))))) 88334895007914473555161 ep1386 ep1387

noncomputable def ep1389 := nat_lit 478350373954272105598034116608

noncomputable def ep1390 := nat_lit 15162978756141064826500531

noncomputable def ep1391 := nat_lit 1124568605757378093844917253

noncomputable def ep1392 := nat_lit 33386860804593231878876185377800798246057369665536

noncomputable def ep1393 := @Enclosure.Real.IsNear.mulLit_tf qz215 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz211 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz82 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz124 qz125 (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))))) 40244248877 1099511627776 13180582199627 109024274475384832 2194969404893

noncomputable abbrev qz217 := (@HMul.hMul Real Real Real qz267 qz453 qz677)

noncomputable abbrev qz218 := (Real.sin (@HMul.hMul Real Real Real qz267 qz453 qz677))

noncomputable abbrev qz722 := (@Neg.neg Real Real.instNeg qz218)

noncomputable def ep1394 := @Enclosure.Complex.IsNear.of_eq qz210 (Complex.mk (@HMul.hMul Real Real Real qz0 qz444 (Real.cos qz217)) (@HMul.hMul Real Real Real qz0 qz444 qz722)) Bool.true 40244248877 1099511627776 13180582199627 109024274475384832 Bool.true 178778529451 1099511627776 13259183755213 109024274475384832 (BSN.cpow_neg_s_mk qz145 142522 1000 36 qz146 rfl)

noncomputable def ep1395 := @Enclosure.Real.IsNear.mulLit_ff qz145 qz133 142522 1000 0 1 16138732561338579 4503599627370496 100000000099157 19831400000000000000 1150062221053548478119 2251799813685248000 7126100007066026977 9915700000000000000000 qz147 (BSN.isNear_log_sfrac 36 1 16138732561338579 4503599627370496 100000000099157 19831400000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' qz447 Bool.false 67690750536952647254016 18889465931478580854784 1000000000991570 198314000000000000000 16138732561338579 4503599627370496 100000000099157 19831400000000000000 (BSN.log_rat_reduce_isNear 36 1 5 72 64 61752 524288 24973259072661432 36028797018963968 198314 1000000000000000 rfl rfl rfl rfl (ep702 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1396 := nat_lit 51116291306450352636359677271386801

noncomputable def ep1397 := BSN.sin_dyadic_bound_f 475488299 2147483648 2 1 1048576 397016 ep1396 ep70 ep1396 ep1396 ep71 ep1396 230279 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 475488299) qz20 0 1 ep1396 ep70 ep1396 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 475488299) qz21 0 1 ep1396 ep71 ep1396 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz507 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 267769727) qz17)

noncomputable def ep1398 := @Enclosure.Real.IsNear.cos_image qz217 qz507 Bool.false 267769727 524288 377 524288 Bool.true 230279 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz217 Bool.false 1150062221053548478119 2251799813685248000 7126100007066026977 9915700000000000000000 267769727 524288 377 524288 (ep1395 rfl) rfl) (Enclosure.sfrac_false_div 267769727 524288) (BSN.cos_reduce1 qz507 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 16729757256519929298944) qz19) 226375608064910080 72057594037927936 Bool.false 230279 1048576 81 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q1 267769727 524288 226375608064910080 72057594037927936 81 16729757256519929298944 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 230279 1048576 16729757256519929298944 75557863725914323419136 475488299 2147483648 397016 396628 (ep1397 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1399 := BSN.cos_dyadic_bound_f 475488299 2147483648 2 1 1048576 397016 ep1396 ep66 ep1396 ep1396 ep67 ep1396 1022977 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 475488299) qz15 0 1 ep1396 ep66 ep1396 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 475488299) qz16 0 1 ep1396 ep67 ep1396 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1400 := @Enclosure.Real.IsNear.sin_image qz217 qz507 Bool.false 267769727 524288 377 524288 Bool.false 1022977 1048576 1 198314 (@Enclosure.Real.IsNear.recentre' qz217 Bool.false 1150062221053548478119 2251799813685248000 7126100007066026977 9915700000000000000000 267769727 524288 377 524288 (ep1395 rfl) rfl) (Enclosure.sfrac_false_div 267769727 524288) (BSN.sin_reduce1 qz507 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 16729757256519929298944) qz19) 226375608064910080 72057594037927936 Bool.false 1022977 1048576 81 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q1 267769727 524288 226375608064910080 72057594037927936 81 16729757256519929298944 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1022977 1048576 16729757256519929298944 75557863725914323419136 475488299 2147483648 397016 396628 (ep1399 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1401 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz444 (Real.cos qz217)) (@HMul.hMul Real Real Real qz0 qz444 qz722) Bool.true 40244248877 1099511627776 13180582199627 109024274475384832 Bool.true 178778529451 1099511627776 13259183755213 109024274475384832 (@Enclosure.Real.IsNear.mulLit_ft qz444 (Real.cos qz217) 174763 1048576 1 1048576 230279 1048576 37644333 51986825216 40244248877 1099511627776 13180582199627 109024274475384832 qz449 (@Enclosure.Real.IsNear.recentre' (Real.cos qz217) Bool.true 230279 1048576 75288666 103973650432 230279 1048576 37644333 51986825216 (ep1398 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz444 qz722 174763 1048576 1 1048576 1022977 1048576 37644333 51986825216 178778529451 1099511627776 13259183755213 109024274475384832 qz449 (@Enclosure.Real.IsNear.neg qz218 Bool.false 1022977 1048576 37644333 51986825216 (@Enclosure.Real.IsNear.recentre' qz218 Bool.false 1022977 1048576 75288666 103973650432 1022977 1048576 37644333 51986825216 (ep1400 rfl rfl) rfl)) rfl)

noncomputable def ep1402 := @ep1393 4387558424544 0 1 88334895007914473555161 ep1386 ep1387 ep1389 (@Enclosure.Complex.IsNear.re_isNear qz210 Bool.true 40244248877 1099511627776 13180582199627 109024274475384832 Bool.true 178778529451 1099511627776 13259183755213 109024274475384832 (ep1394 ep1401))

noncomputable def ep1403 := @Enclosure.Complex.IsNear.re_isNear (@HAdd.hAdd Complex Complex Complex qz4 qz211 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz82 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz124 qz125 (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1))))) Bool.false 2194969404893 4387558424544 0 1 Bool.false

noncomputable def ep1404 := @Enclosure.Complex.IsNear.addLitP qz211 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz82 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz124 qz125 (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) Bool.false 5069192621 10156385242 0 1 Bool.true 1282698000

noncomputable def ep1405 := @ep1404 5078192621 0 1 Bool.false 1 864 0 1 Bool.false 71261 216000 0 1 Bool.false 4389938809786 2194969404893 4387558424544 0 1 Bool.false 84814316365081 84814316365081 1096889606136000 0 1

noncomputable abbrev qz219 := (@HDiv.hDiv Complex Complex Complex qz405 qz427 (@HSub.hSub Complex Complex Complex qz397 qz451 (1 : Complex)))

noncomputable def ep1406 := @Enclosure.Complex.IsNear.addLitP qz219 qz99 Bool.true 72000000 81251081936 0 1 Bool.true 20523168000 81251081936 0 1

noncomputable def ep1407 := @Enclosure.Complex.IsNear.of_eq qz219 (Complex.mk (Enclosure.sfrac Bool.true 72000000 81251081936) (Enclosure.sfrac Bool.true 20523168000 81251081936)) Bool.true 72000000 81251081936 0 1 Bool.true 20523168000 81251081936 0 1

noncomputable def ep1408 := @ep1406 Bool.false 1 2 0 1 Bool.false 0 1 0 1 Bool.false 81107081936 5069192621 10156385242 0 1 Bool.true 20523168000 1282698000 5078192621 0 1 (ep1407 (BSN.N_div_s_sub_one_mk qz145 142522 1000 36 qz146 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 72000000 81251081936) (Enclosure.sfrac Bool.true 20523168000 81251081936) Bool.true 72000000 81251081936 0 1 Bool.true 20523168000 81251081936 0 1 (Enclosure.Real.IsNear.const Bool.true 72000000 81251081936) (Enclosure.Real.IsNear.const Bool.true 20523168000 81251081936))) qz100 rfl

noncomputable def ep1409 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz82 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz124 qz125 (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) (@HAdd.hAdd Complex Complex Complex qz4 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz82 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz124 qz125 (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz135) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1))) qz136)) Bool.false 1 864 0 1

noncomputable def ep1410 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz82 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz124 qz125 (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz135) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1))) qz136) Bool.false 0 1 0 1 Bool.false

noncomputable def ep1411 := @ep1410 0 1 0 1 Bool.false 1 864 0 1 Bool.false 71261 216000 0 1 Bool.false 1 1 864 0 1 Bool.false 71261 71261 216000 0

noncomputable def ep1412 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz82 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz124 qz125 (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) (Complex.mk qz10 qz10) Bool.false 0 1 0 1 Bool.false

noncomputable def ep1413 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz135) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1))) qz136 Bool.false 1 864 0 1 Bool.false 71261 216000 0 1

noncomputable def ep1414 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz135) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1)))) qz137) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz135) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1)))) qz138) 1 864 0 1 0 1 0

noncomputable def ep1415 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz135) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1)))) qz137 1 24 0 1 1 36 0 1 1

noncomputable def ep1416 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz135)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz135)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1)))) 1 24 0 1 0 1 0 1 1

noncomputable def ep1417 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz135)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 1 2 0 1 1 24 0

noncomputable def ep1418 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1)) qz142 Bool.false 1 2 0 1 Bool.false 142522 1000 0 1 (BSN.ascPochhammer_one_eval qz142)

noncomputable def ep1419 := ep1418 (@Enclosure.Complex.IsNear.of_eq qz142 (Complex.mk qz94 qz145) Bool.false 1 2 0 1 Bool.false 142522 1000 0 1 (BSN.s_crit_mk qz145 Bool.false 142522 1000 qz146) (@Enclosure.Complex.IsNear.mk qz94 qz145 Bool.false 1 2 0 1 Bool.false 142522 1000 0 1 qz411 qz147))

noncomputable def ep1420 := @ep1417 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz135) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep729) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 142522 1000 0 1 ep1419)

noncomputable def ep1421 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz135)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 142522 1000 0 1 0 1 0

noncomputable def ep1422 := @ep1421 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz135) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep729) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 142522 1000 0 1 ep1419)

noncomputable def ep1423 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz135)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz135)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1)))) 71261 6000 0 1 0 1 0 1 71261

noncomputable def ep1424 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz135)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 142522 1000 0 1 71261 6000 0

noncomputable def ep1425 := @ep1424 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz135) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep729) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 142522 1000 0 1 ep1419)

noncomputable def ep1426 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz135)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 1 2 0 1 0 1 0

noncomputable def ep1427 := @ep1426 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz135) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep729) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 142522 1000 0 1 ep1419)

noncomputable def ep1428 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz135) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 24 0 1 Bool.false 71261 6000 0 1 (@ep1416 1 24 0 1 (ep1420 rfl) (ep1422 rfl) rfl rfl) (@ep1423 71261 6000 0 1 (ep1425 rfl) (ep1427 rfl) rfl rfl)

noncomputable def ep1429 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz135) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 71261 6000 0 1 ep1428

noncomputable def ep1430 := @ep1415 864 0 1 ep1429 qz139

noncomputable def ep1431 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz135) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1)))) qz138 71261 6000 0 1 0 1 0 1 0

noncomputable def ep1432 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz135) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 71261 6000 0 1 ep1428

noncomputable def ep1433 := @ep1431 1 0 1 ep1432 qz140

noncomputable def ep1434 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz135) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1)))) qz138) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz135) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1)))) qz137) 0 1 0 1 71261 216000 0

noncomputable def ep1435 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz135) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1)))) qz138 1 24 0 1 0 1 0 1 0

noncomputable def ep1436 := @ep1435 1 0 1 ep1429 qz140

noncomputable def ep1437 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz135) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1)))) qz137 71261 6000 0 1 1 36 0 1 71261

noncomputable def ep1438 := @ep1437 216000 0 1 ep1432 qz139

noncomputable def ep1439 := @ep1411 1 (@ep1412 0 1 0 1 (BSN.bern_sum_base qz142 36) qz115) (ep1413 (@ep1414 1 1 1 864 0 1 (ep1430 rfl) (ep1433 rfl) rfl rfl) (@ep1434 1 71261 71261 216000 0 1 (ep1436 rfl) (ep1438 rfl) rfl rfl)) rfl rfl rfl rfl rfl

noncomputable def ep1440 := ep1405 (ep1408 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep1409 Bool.false 71261 216000 0 1 (BSN.bern_sum_succ qz142 36 0 1 1 rfl rfl) (ep1439 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl rfl

noncomputable def ep1441 := @Enclosure.Real.IsNear.mulLit_tf qz216 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz211 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz82 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz124 qz125 (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))))) 178778529451 1099511627776 13259183755213 109024274475384832 84814316365081

noncomputable def ep1442 := @ep1441 1096889606136000 0 1 ep1390 ep1332 ep1391 ep1334 (@Enclosure.Complex.IsNear.im_isNear qz210 Bool.true 40244248877 1099511627776 13180582199627 109024274475384832 Bool.true 178778529451 1099511627776 13259183755213 109024274475384832 (ep1394 ep1401))

noncomputable def ep1443 := @Enclosure.Complex.IsNear.im_isNear (@HAdd.hAdd Complex Complex Complex qz4 qz211 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz82 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz124 qz125 (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1))))) Bool.false 2194969404893 4387558424544 0 1 Bool.false

noncomputable def ep1444 := nat_lit 3413288456128933756264037

noncomputable def ep1445 := nat_lit 1117902068555119590154024787

noncomputable def ep1446 := @Enclosure.Real.IsNear.addLit_tt (@HMul.hMul Real Real Real qz0 qz215 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz211 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz82 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz124 qz125 (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz216 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz211 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz82 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz124 qz125 (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1))))))) ep1444 ep1332 ep1445

noncomputable def ep1447 := nat_lit 29103502676546811596457209

noncomputable def ep1448 := nat_lit 489733677447748072041632983215170168686106093027328

noncomputable def ep1449 := @Enclosure.Real.IsNear.mulLit_tf qz215 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz211 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz82 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz124 qz125 (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))))) 40244248877 1099511627776 13180582199627 109024274475384832 84814316365081

noncomputable def ep1450 := @ep1449 1096889606136000 0 1 ep1444 ep1332 ep1445 ep1334 (@Enclosure.Complex.IsNear.re_isNear qz210 Bool.true 40244248877 1099511627776 13180582199627 109024274475384832 Bool.true 178778529451 1099511627776 13259183755213 109024274475384832 (ep1394 ep1401))

noncomputable def ep1451 := @Enclosure.Real.IsNear.mulLit_tf qz216 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz211 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz82 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz124 qz125 (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))))) 178778529451 1099511627776 13259183755213 109024274475384832 2194969404893

noncomputable def ep1452 := @ep1451 4387558424544 0 1 392413402396707144003743 ep1386 ep1447 ep1389 (@Enclosure.Complex.IsNear.im_isNear qz210 Bool.true 40244248877 1099511627776 13180582199627 109024274475384832 Bool.true 178778529451 1099511627776 13259183755213 109024274475384832 (ep1394 ep1401))

noncomputable abbrev qz723 := (ep1440 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable def ep1453 := @ep1385 ep1338 ep1332 ep1339 ep1334 (@ep1388 ep1389 ep1390 ep1332 ep1391 ep1334 ep1392 768971666204172618032191 ep1208 ep1337 ep1210 (ep1402 (@ep1403 84814316365081 1096889606136000 0 1 qz723) rfl) (ep1442 (@ep1443 84814316365081 1096889606136000 0 1 qz723) rfl) rfl rfl) (@ep1446 ep1334 392413402396707144003743 ep1386 ep1447 ep1389 ep1448 ep1338 ep1332 ep1339 ep1334 (ep1450 (@ep1443 84814316365081 1096889606136000 0 1 qz723) rfl) (ep1452 (@ep1403 84814316365081 1096889606136000 0 1 qz723) rfl) rfl rfl)

noncomputable def ep1454 := @ep1342 ep1333 ep1334 (@ep1343 13628034309423104 (BSN.head_sum_c_eq qz142 36) (ep1344 (BSN.head_sum_c_succ qz142 35 36 rfl rfl) (ep1384 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))) ep1453 rfl rfl rfl

noncomputable def ep1455 := @Enclosure.Complex.IsNear.re_isNear (zetaApproximant qz142 1 36) Bool.false ep1207 ep1208 ep1209 ep1210 Bool.false ep1331 ep1332 ep1333 ep1334 (@ep1335 ep1210 Bool.false ep1331 ep1332 ep1333 ep1334 (BSN.zetaApproximant_eq_folded' qz142 1 36 rfl) (ep1454 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

noncomputable def ep1456 := @Enclosure.Real.IsNear.mulLit_tf (Real.sin (@HSub.hSub Real Real Real qz400 (Complex.im (@HSub.hSub Complex Complex Complex qz75 qz181 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz182 (@Nat.cast Complex Complex.instNatCast j))))) qz183)) (Complex.im (zetaApproximant qz142 1 36)) 301 1048576 19597759

noncomputable def ep1457 := @Enclosure.Real.IsNear.recentre' (Real.sin (@HSub.hSub Real Real Real qz400 (Complex.im (@HSub.hSub Complex Complex Complex qz75 qz181 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz182 (@Nat.cast Complex Complex.instNatCast j))))) qz183)) Bool.true 301 1048576 39195518

noncomputable def ep1458 := @Enclosure.Real.IsNear.sin_image (@HSub.hSub Real Real Real qz400 (Complex.im (@HSub.hSub Complex Complex Complex qz75 qz181 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz182 (@Nat.cast Complex Complex.instNatCast j))))) qz183) qz716 Bool.false 79060617 524288 195

noncomputable def ep1459 := nat_lit 4639587995122537107201418027993936260788088462238080855701546866195529986358881

noncomputable def ep1460 := nat_lit 13885283504310464222452462466745690193263771010629311290013630134483747084844641

noncomputable def ep1461 := BSN.cos_dyadic_bound_f 3372641749 2147483648 3 2 1048576 397016 ep1459 ep102 ep1327 ep1460 ep104 ep1327 301 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3372641749) qz15 0 2 ep1459 ep102 ep1327 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3372641749) qz16 0 2 ep1460 ep104 ep1327 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1462 := @ep1458 524288 Bool.true 301 1048576 1 198314 (@ep1215 79060617 524288 195 524288 ep1325 rfl) (Enclosure.sfrac_false_div 79060617 524288) (BSN.sin_reduce3 qz716 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 118664282240328321204224) qz19) 226375608064910080 72057594037927936 Bool.false 301 1048576 23 1000000000000000 396628 198314 (BSN.sin_reduce_arg_pos_rat_q3 79060617 524288 226375608064910080 72057594037927936 23 118664282240328321204224 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 301 1048576 118664282240328321204224 75557863725914323419136 3372641749 2147483648 397016 396628 (ep1461 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1463 := @Enclosure.Complex.IsNear.im_isNear (zetaApproximant qz142 1 36) Bool.false ep1207 ep1208 ep1209 ep1210 Bool.false ep1331 ep1332 ep1333 ep1334 (@ep1335 ep1210 Bool.false ep1331 ep1332 ep1333 ep1334 (BSN.zetaApproximant_eq_folded' qz142 1 36 rfl) (ep1454 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

theorem EMRow49.d17 : Enclosure.Real.IsNear (hardyZApproximantEM 1 36 qz145) Bool.false ep1190 ep1191 ep1192 ep1193 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantEM 1 36 qz145) ep1194 Bool.false ep1190 ep1191 ep1192 ep1193 (@Eq.refl Real ep1194) (@ep1195 Bool.false ep1190 ep1191 ep1192 ep1193 (BSN.re_exp_mul (@HSub.hSub Real Real Real qz400 (Complex.im (@HSub.hSub Complex Complex Complex qz75 qz181 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz182 (@Nat.cast Complex Complex.instNatCast j))))) qz183) (zetaApproximant qz142 1 36)) (@ep1197 ep1198 ep1199 ep1200 ep1201 ep1202 ep1203 ep1204 ep1205 ep1190 ep1191 ep1192 ep1193 (@ep1206 51986825216 ep1207 ep1208 ep1209 ep1210 ep1196 ep1198 ep1199 ep1200 (@ep1211 103973650432 1048575 1048576 19597759 51986825216 (ep1330 rfl rfl) rfl) ep1455 rfl) (@ep1456 51986825216 ep1331 ep1332 ep1333 ep1334 ep1201 ep1202 ep1203 ep1204 (@ep1457 103973650432 301 1048576 19597759 51986825216 (ep1462 rfl rfl) rfl) ep1463 rfl) rfl rfl))

theorem EMRow49.d18 : @Eq Nat (Nat.mul (BSN.factNat (Nat.succ (Nat.mul 2 1))) (Nat.pow 4 (Nat.mul 2 1))) 96 := @Eq.refl Nat 96

theorem EMRow49.d19 : @Eq Nat (Nat.mul (Nat.mul 2 1) (Nat.pow (Nat.succ (Nat.mul 4 2)) (Nat.mul 2 1))) 162 := @Eq.refl Nat 162

theorem EMRow49.d20 : @Eq Nat (BSN.factNat (Nat.mul 2 2)) 24 := @Eq.refl Nat 24

theorem EMRow49.d21 : @Eq Nat (Nat.pow 36 (Nat.succ (Nat.mul 2 3))) 78364164096 := @Eq.refl Nat 78364164096

noncomputable abbrev qz724 := (@HAdd.hAdd Complex Complex Complex qz730 qz729 (@Nat.cast Complex Complex.instNatCast 3))

noncomputable abbrev qz508 := qz724

noncomputable abbrev qz220 := (@HDiv.hDiv Real Real Real qz270 (@Norm.norm Complex Complex.instNorm qz508) (@HAdd.hAdd Real Real Real qz420 (Complex.re qz271) qz288))

noncomputable abbrev qz221 := (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 2)

noncomputable abbrev qz222 := (@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 2)))

noncomputable abbrev qz509 := (@HPow.hPow Complex Complex Complex qz542 qz667 (@HSub.hSub Complex Complex Complex qz654 qz543 qz549))

noncomputable abbrev qz223 := qz509

noncomputable def ep1464 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 36))) (@HMul.hMul Real Real Real qz0 qz220 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))) 2558966423 231928233984 6149947 57982058496 4461044904337317375 8070450532247928832 88349566599

noncomputable def ep1465 := nat_lit 1055294278316781169204250279936

noncomputable def ep1466 := @Enclosure.Real.IsNear.mulLit_ff (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 36)) 26561 1769472 1 1769472 96343 131072 1845 262144 2558966423 231928233984

noncomputable abbrev qz224 := (@HMul.hMul Real Real Real qz267 (2 : Real) Real.pi)

noncomputable abbrev qz725 := (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid)))

noncomputable abbrev qz510 := (@Inv.inv Real Real.instInv (@HPow.hPow Real Nat Real qz725 qz224 2))

noncomputable def ep1467 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 96 162) qz510 96 162 0 1 26561 1048576 1 1048576 26561 1769472 1 1769472

noncomputable def ep1468 := nat_lit 781950621441006189802102638025

noncomputable def ep1469 := nat_lit 19807040628566084398385987584

noncomputable def ep1470 := nat_lit 26986075409044041160201671

noncomputable def ep1471 := nat_lit 1073741824000000000000000000000000000000

noncomputable abbrev qz511 := qz725

noncomputable def ep1472 := @Enclosure.Real.IsNear.mulLit_ff (@HPow.hPow Real Nat Real qz511 qz224 1) qz224 884279719003555 140737488355328 1 500000000000000 884279719003555 140737488355328 1 500000000000000 ep1468 ep1469 ep1470 ep1471

noncomputable def ep1473 := ep1472 (@Enclosure.Real.IsNear.of_eq (@HPow.hPow Real Nat Real qz511 qz224 1) qz224 Bool.false 884279719003555 140737488355328 1 500000000000000 (BSN.pow_one_r qz224) (@Enclosure.Real.IsNear.of_eq qz224 qz268 Bool.false 884279719003555 140737488355328 1 500000000000000 BSN.two_pi_eq qz269)) (@Enclosure.Real.IsNear.of_eq qz224 qz268 Bool.false 884279719003555 140737488355328 1 500000000000000 BSN.two_pi_eq qz269) rfl

noncomputable abbrev qz512 := (@HPow.hPow Real Nat Real qz725 qz224 2)

noncomputable def ep1474 := @Enclosure.Real.IsNear.inv_image qz512 ep1468 ep1469 ep1470 ep1471 13280 13281 524288 (@Enclosure.Real.IsNear.of_eq qz512 (@HMul.hMul Real Real Real qz0 (@HPow.hPow Real Nat Real qz511 qz224 1) qz224) Bool.false ep1468 ep1469 ep1470 ep1471 (BSN.pow_succ_r qz224 1 2 rfl) ep1473) rfl rfl rfl

noncomputable def ep1475 := ep1467 (Enclosure.Real.IsNear.const Bool.false 96 162) (@Enclosure.Real.IsNear.recentre' qz510 Bool.false 26561 1048576 1 1048576 26561 1048576 1 1048576 (ep1474 rfl rfl rfl) rfl)

noncomputable def ep1476 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 36)) (Real.sqrt (@HAdd.hAdd Real Real Real qz420 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz5 1 36)) (Complex.re (zetaApproximant qz5 1 36))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz5 1 36)) (Complex.im (zetaApproximant qz5 1 36))))) Bool.false 96343 131072 1845 262144

noncomputable def ep1477 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz420 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz5 1 36)) (Complex.re (zetaApproximant qz5 1 36))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz5 1 36)) (Complex.im (zetaApproximant qz5 1 36))))) Bool.false 770744 1048576 7380 1048576

noncomputable def ep1478 := nat_lit 154026836542482838308400973727844260021409

noncomputable def ep1479 := nat_lit 285059933173376128354092343596960605798400

noncomputable def ep1480 := nat_lit 572441301415764033673868886643299233486073710127408227053387

noncomputable def ep1481 := nat_lit 55331442773259930692225078612144938041421513811463021527040000

noncomputable def ep1482 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz420 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz5 1 36)) (Complex.re (zetaApproximant qz5 1 36))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz5 1 36)) (Complex.im (zetaApproximant qz5 1 36)))) ep1478 ep1479 ep1480 ep1481 381682 389062

noncomputable def ep1483 := nat_lit 303977879867956773840022322646685978093074517729

noncomputable def ep1484 := nat_lit 562762612714163838456870061737086315833847709696

noncomputable def ep1485 := nat_lit 3887114401286713818765009525518264679621246280587191835919

noncomputable def ep1486 := nat_lit 384246130369860629807118601473228736398760512579604316160000

noncomputable def ep1487 := nat_lit 4463909525901480785157584381163548459181188401

noncomputable def ep1488 := nat_lit 25011671676185059486972002743870502925948787097600

noncomputable def ep1489 := nat_lit 12696827630477243771707514968669119620614245722852602681051

noncomputable def ep1490 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz5 1 36)) (Complex.re (zetaApproximant qz5 1 36))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz5 1 36)) (Complex.im (zetaApproximant qz5 1 36))) ep1483 ep1484 ep1485 ep1486 ep1487 ep1488 ep1489

noncomputable def ep1491 := nat_lit 7605507049467875012488890325860546679880633499488125399805535047045253598889706587668278983786496

noncomputable def ep1492 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (zetaApproximant qz5 1 36)) (Complex.re (zetaApproximant qz5 1 36)) 551341890180636259841777 750175054713340783755264 ep507 ep508 551341890180636259841777 750175054713340783755264 ep507 ep508 ep1483

noncomputable def ep1493 := @Enclosure.Real.IsNear.mulLit_tt (Complex.im (zetaApproximant qz5 1 36)) (Complex.im (zetaApproximant qz5 1 36)) 66812495282705021757049 ep636 ep637 ep638 66812495282705021757049 ep636 ep637 ep638 ep1487

noncomputable def ep1494 := @ep1464 1152921504606846976 ep1465 122852423032370997733 217902164370694078464 3304113092939837 31128880624384868352 (@ep1466 6149947 57982058496 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaStirlingErrorBound 1 2) (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 96 162) qz510) Bool.false 26561 1769472 1 1769472 (BSN.theta_err_eq 1 2 96 162 EMRow49.d18 EMRow49.d19 rfl) (ep1475 rfl)) (ep1476 (BSN.norm_eq_sqrt_mul_add (zetaApproximant qz5 1 36)) (@ep1477 96343 131072 1845 262144 (@ep1482 524288 (@ep1490 ep1481 ep1491 ep1478 ep1479 ep1480 ep1481 (@ep1492 ep1484 ep1485 ep1486 ep767 ep767 rfl) (@ep1493 ep1488 ep1489 ep1481 ep773 ep773 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl)

noncomputable abbrev qz225 := (@Norm.norm Complex Complex.instNorm qz508)

noncomputable abbrev qz726 := (Enclosure.sfrac Bool.false 2 7)

noncomputable def ep1495 := @Enclosure.Real.IsNear.of_eq (@HMul.hMul Real Real Real qz0 qz220 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))) (@HMul.hMul Real Real Real qz0 (@HMul.hMul Real Real Real qz0 qz225 qz726) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))) Bool.false 4461044904337317375 8070450532247928832 88349566599 1152921504606846976 (BSN.zrb_shape_eq qz225 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) qz12 3)

noncomputable def ep1496 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz0 qz225 qz726) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) 147375875 3670016 1 3670016 30269845077 2199023255552 3991 2199023255552

noncomputable def ep1497 := @Enclosure.Real.IsNear.mulLit_ff qz225 qz726 147375875 1048576 1 1048576 2 7 0 1 147375875 3670016

noncomputable abbrev qz513 := (Complex.re qz724)

noncomputable abbrev qz514 := (Complex.im qz724)

noncomputable abbrev qz226 := (@HAdd.hAdd Real Real Real qz420 (@HMul.hMul Real Real Real qz267 qz513 qz513) (@HMul.hMul Real Real Real qz267 qz514 qz514))

noncomputable abbrev qz227 := qz508

noncomputable def ep1498 := @Enclosure.Real.IsNear.of_eq qz225 (Real.sqrt qz226) Bool.false 147375875 1048576 1 1048576 (BSN.norm_eq_sqrt_mul_add qz227)

noncomputable def ep1499 := @Enclosure.Real.IsNear.recentre' (Real.sqrt qz226) Bool.false 147375875 1048576 1 1048576 147375875

noncomputable def ep1500 := @Enclosure.Real.IsNear.sqrt_image qz226 790156201 40000 0 1 73687937 73687938 524288

noncomputable abbrev qz228 := (@HMul.hMul Real Real Real qz267 qz513 qz513)

noncomputable abbrev qz229 := (@HMul.hMul Real Real Real qz267 qz514 qz514)

noncomputable def ep1501 := @Enclosure.Real.IsNear.addLit_ff qz228 qz229 49 4 0 1 789666201 40000 0 1

noncomputable abbrev qz230 := qz513

noncomputable def ep1502 := @Enclosure.Real.IsNear.mulLit_ff qz230 qz230 7 2 0 1 7 2 0 1 49 4

noncomputable abbrev qz515 := (Enclosure.sfrac Bool.false 7 2)

noncomputable def ep1503 := @Enclosure.Complex.IsNear.of_eq qz227 (Complex.mk qz515 qz12) Bool.false 7 2 0 1 Bool.false 140505 1000 0 1 (BSN.s_add_nat_mk qz12 Bool.false 140505 1000 3 qz13)

noncomputable abbrev qz516 := (ep1503 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7 2) qz12 Bool.false 7 2 0 1 Bool.false 140505 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 7 2) qz18))

noncomputable def ep1504 := @ep1502 0 1 (@Enclosure.Complex.IsNear.re_isNear qz227 Bool.false 7 2 0 1 Bool.false 140505 1000 0 1 qz516)

noncomputable def ep1505 := ep1504 (@Enclosure.Complex.IsNear.re_isNear qz227 Bool.false 7 2 0 1 Bool.false 140505 1000 0 1 qz516)

noncomputable abbrev qz231 := qz514

noncomputable def ep1506 := @Enclosure.Real.IsNear.mulLit_ff qz231 qz231 140505 1000 0 1 140505 1000 0 1 789666201 40000

noncomputable def ep1507 := @ep1506 0 1 (@Enclosure.Complex.IsNear.im_isNear qz227 Bool.false 7 2 0 1 Bool.false 140505 1000 0 1 qz516)

noncomputable def ep1508 := ep1507 (@Enclosure.Complex.IsNear.im_isNear qz227 Bool.false 7 2 0 1 Bool.false 140505 1000 0 1 qz516)

noncomputable def ep1509 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Real.sqrt (@HAdd.hAdd Real Real Real qz420 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.re (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.im (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))))) Bool.false 30269845077 2199023255552

noncomputable def ep1510 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz420 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.re (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.im (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))))) Bool.false 30269845077 2199023255552

noncomputable def ep1511 := nat_lit 8166810954254299960527315344544242637870364468452736067866458229

noncomputable def ep1512 := nat_lit 43101437086853124141328510138602445789277037811413811200000000000000

noncomputable def ep1513 := nat_lit 11249882203227284112017801655463169405913934854571598892054769127507269459

noncomputable def ep1514 := nat_lit 225213056481529350010910712448565177770777050340472051242397525134540800000000000000

noncomputable def ep1515 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz420 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.re (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.im (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)))) ep1511 ep1512 ep1513 ep1514

noncomputable def ep1516 := nat_lit 9695240896997172234913109363680113127409025982832216545191665809

noncomputable def ep1517 := nat_lit 86202874173706248282657020277204891578554075622827622400000000000000

noncomputable def ep1518 := nat_lit 12955685581326564904170121831119985637826756941611454917695685807237739863

noncomputable def ep1519 := nat_lit 450426112963058700021821424897130355541554100680944102484795050269081600000000000000

noncomputable def ep1520 := nat_lit 6638381011511427686141521325408372148331702954073255590541250649

noncomputable def ep1521 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.re (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.im (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))) ep1516 ep1517 ep1518 ep1519 ep1520

noncomputable def ep1522 := nat_lit 1908815765025600663973096295961270634800222553506348573282770489555359811

noncomputable def ep1523 := nat_lit 90085222592611740004364284979426071108310820136188820496959010053816320000000000000

noncomputable def ep1524 := nat_lit 1408005154180058549505523343421037359393507736775197633738551476173978949263710824040700868394942830258448788953969459200000000000000

noncomputable def ep1525 := nat_lit 98464414368832622610619537439447

noncomputable def ep1526 := nat_lit 9284550294640352061743431680000000

noncomputable def ep1527 := nat_lit 910123162021201143136235654194297

noncomputable def ep1528 := nat_lit 671137923949361320862607928763351040000000

noncomputable def ep1529 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.re (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) ep1525 ep1526 ep1527 ep1528 ep1525 ep1526 ep1527

noncomputable def ep1530 := nat_lit 81476260416832016543178290890843

noncomputable def ep1531 := nat_lit 162051103612551697435865356181177

noncomputable def ep1532 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223) Bool.false ep1525 ep1526 ep1527 ep1528 Bool.false ep1530 ep1526 ep1531

noncomputable def ep1533 := nat_lit 134227584789872264172521585752670208000000

noncomputable def ep1534 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223 Bool.false ep1525 ep1526 ep1527 ep1528 Bool.false ep1530 ep1526 ep1531 ep1533

noncomputable def ep1535 := nat_lit 9028156706013277335952054529

noncomputable def ep1536 := nat_lit 30948500982134506872478105600000

noncomputable def ep1537 := nat_lit 50097956144677437774106174153

noncomputable def ep1538 := nat_lit 1342275847898722641725215857526702080000

noncomputable def ep1539 := nat_lit 95755967357028639409833921080747

noncomputable def ep1540 := nat_lit 885074183948862424249182567117797

noncomputable abbrev qz232 := (Complex.re qz509)

noncomputable abbrev qz233 := (Complex.im qz509)

noncomputable def ep1541 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz232) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz233) ep1535 ep1536 ep1537 ep1538 ep1539 ep1526 ep1540

noncomputable def ep1542 := nat_lit 3047326024799115471485534076342481495332844725698993271603200000

noncomputable def ep1543 := nat_lit 4835703278458516698824704

noncomputable def ep1544 := nat_lit 349551002056959021282608296230912

noncomputable def ep1545 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz232 2368948603 19200000 0 1 11433118508244744729 ep1543 105738799231933859255 ep1544 ep1535

noncomputable def ep1546 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) 2368948603 19200000 0 1 0 1 0 1 2368948603

noncomputable def ep1547 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 7106845809 80000 0 1 2368948603 19200000 0

noncomputable def ep1548 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (Complex.mk (Enclosure.sfrac Bool.true 1 720) qz10) Bool.true 1 720 0 1 Bool.false 0 1 0 1 (BSN.bern_coeff_mk 2 1 30 24 Bool.true BSN.bern_real_2 EMRow49.d20 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 1 720) qz10 Bool.true 1 720 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.true 1 720) qz22)

noncomputable abbrev qz517 := (@HAdd.hAdd Complex Complex Complex qz541 qz540 qz550)

noncomputable abbrev qz234 := qz517

noncomputable def ep1549 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) (@HMul.hMul Complex Complex Complex qz74 (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) qz234) Bool.true 7106845809 80000 0 1 Bool.true 22183946684301 8000000 0 1

noncomputable abbrev qz235 := (Complex.re qz517)

noncomputable abbrev qz236 := (Complex.im qz517)

noncomputable def ep1550 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz235) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz236) 789636201 16000 0 1 789666201 20000 0 1

noncomputable def ep1551 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz235 789636201 40000 0 1 5 2 0 1 789636201 16000

noncomputable abbrev qz518 := (@HAdd.hAdd Complex Complex Complex qz541 qz540 (@Nat.cast Complex Complex.instNatCast 1))

noncomputable abbrev qz237 := qz518

noncomputable def ep1552 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) (@HMul.hMul Complex Complex Complex qz74 (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) qz237) Bool.true 789636201 40000 0 1 Bool.false 28101 100 0 1

noncomputable abbrev qz238 := (Complex.re qz518)

noncomputable abbrev qz239 := (Complex.im qz518)

noncomputable def ep1553 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz238) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz239) 3 4 0 1 789666201 40000 0 1

noncomputable def ep1554 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz238 1 2 0 1 3 2 0 1 3 4

noncomputable def ep1555 := @ep1554 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 140505 1000 0 1 ep731)

noncomputable abbrev qz519 := (Enclosure.sfrac Bool.false 3 2)

noncomputable def ep1556 := @Enclosure.Complex.IsNear.of_eq qz237 (Complex.mk qz519 qz12) Bool.false 3 2 0 1 Bool.false 140505 1000 0 1 (BSN.s_add_nat_mk qz12 Bool.false 140505 1000 1 qz13)

noncomputable abbrev qz520 := (ep1556 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 3 2) qz12 Bool.false 3 2 0 1 Bool.false 140505 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 3 2) qz18))

noncomputable def ep1557 := ep1555 (@Enclosure.Complex.IsNear.re_isNear qz237 Bool.false 3 2 0 1 Bool.false 140505 1000 0 1 qz520)

noncomputable def ep1558 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz239 140505 1000 0 1 140505 1000 0 1 789666201 40000

noncomputable def ep1559 := @ep1558 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 140505 1000 0 1 ep731)

noncomputable def ep1560 := ep1559 (@Enclosure.Complex.IsNear.im_isNear qz237 Bool.false 3 2 0 1 Bool.false 140505 1000 0 1 qz520)

noncomputable def ep1561 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) qz237 Bool.true 789636201 40000 0 1 Bool.false 28101 100 0 1 (@ep1553 3158544804 789636201 40000 0 1 (ep1557 rfl) (ep1560 rfl) rfl rfl)

noncomputable def ep1562 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz239) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz238) 28101 400 0 1 84303 400 0 1

noncomputable def ep1563 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz239 1 2 0 1 140505 1000 0 1 28101 400

noncomputable def ep1564 := @ep1563 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 140505 1000 0 1 ep731)

noncomputable def ep1565 := ep1564 (@Enclosure.Complex.IsNear.im_isNear qz237 Bool.false 3 2 0 1 Bool.false 140505 1000 0 1 qz520)

noncomputable def ep1566 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz238 140505 1000 0 1 3 2 0 1 84303 400

noncomputable def ep1567 := @ep1566 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 140505 1000 0 1 ep731)

noncomputable def ep1568 := ep1567 (@Enclosure.Complex.IsNear.re_isNear qz237 Bool.false 3 2 0 1 Bool.false 140505 1000 0 1 qz520)

noncomputable abbrev qz240 := (ep1552 (BSN.ascPochhammer_succ_eval_c 1 2 qz271 rfl) (ep1561 (@ep1562 44961600 28101 100 0 1 (ep1565 rfl) (ep1568 rfl) rfl rfl)))

noncomputable def ep1569 := @ep1551 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 789636201 40000 0 1 Bool.false 28101 100 0 1 qz240)

noncomputable abbrev qz521 := (Enclosure.sfrac Bool.false 5 2)

noncomputable def ep1570 := @Enclosure.Complex.IsNear.of_eq qz234 (Complex.mk qz521 qz12) Bool.false 5 2 0 1 Bool.false 140505 1000 0 1 (BSN.s_add_nat_mk qz12 Bool.false 140505 1000 2 qz13)

noncomputable abbrev qz522 := (ep1570 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 5 2) qz12 Bool.false 5 2 0 1 Bool.false 140505 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 5 2) qz18))

noncomputable def ep1571 := ep1569 (@Enclosure.Complex.IsNear.re_isNear qz234 Bool.false 5 2 0 1 Bool.false 140505 1000 0 1 qz522)

noncomputable def ep1572 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz236 28101 100 0 1 140505 1000 0 1 789666201 20000

noncomputable def ep1573 := @ep1572 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 789636201 40000 0 1 Bool.false 28101 100 0 1 qz240)

noncomputable def ep1574 := ep1573 (@Enclosure.Complex.IsNear.im_isNear qz234 Bool.false 5 2 0 1 Bool.false 140505 1000 0 1 qz522)

noncomputable def ep1575 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) qz234 Bool.true 7106845809 80000 0 1 Bool.true 22183946684301 8000000 0 1 (@ep1550 28427383236000 7106845809 80000 0 1 (ep1571 rfl) (ep1574 rfl) rfl rfl)

noncomputable def ep1576 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz236) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz235) 22189566884301 8000000 0 1 28101 40 0 1

noncomputable def ep1577 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz236 789636201 40000 0 1 140505 1000 0 1 22189566884301 8000000

noncomputable def ep1578 := @ep1577 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 789636201 40000 0 1 Bool.false 28101 100 0 1 qz240)

noncomputable def ep1579 := ep1578 (@Enclosure.Complex.IsNear.im_isNear qz234 Bool.false 5 2 0 1 Bool.false 140505 1000 0 1 qz522)

noncomputable def ep1580 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz235 28101 100 0 1 5 2 0 1 28101 40

noncomputable def ep1581 := @ep1580 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 789636201 40000 0 1 Bool.false 28101 100 0 1 qz240)

noncomputable def ep1582 := ep1581 (@Enclosure.Complex.IsNear.re_isNear qz234 Bool.false 5 2 0 1 Bool.false 140505 1000 0 1 qz522)

noncomputable abbrev qz241 := (ep1549 (BSN.ascPochhammer_succ_eval_c 2 3 qz271 rfl) (ep1575 (@ep1576 887357867372040 22183946684301 8000000 0 1 (ep1579 rfl) (ep1582 rfl) rfl rfl)))

noncomputable def ep1583 := @ep1547 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1548) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 7106845809 80000 0 1 Bool.true 22183946684301 8000000 0 1 qz241)

noncomputable def ep1584 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 22183946684301 8000000 0 1 0 1 0

noncomputable def ep1585 := @ep1584 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1548) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 7106845809 80000 0 1 Bool.true 22183946684301 8000000 0 1 qz241)

noncomputable def ep1586 := @Enclosure.Real.IsNear.addLit_ft_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) 7394648894767 1920000000 0 1 0 1 0 1 7394648894767

noncomputable def ep1587 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 22183946684301 8000000 0 1 7394648894767 1920000000 0

noncomputable def ep1588 := @ep1587 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1548) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 7106845809 80000 0 1 Bool.true 22183946684301 8000000 0 1 qz241)

noncomputable def ep1589 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 7106845809 80000 0 1 0 1 0

noncomputable def ep1590 := @ep1589 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1548) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 7106845809 80000 0 1 Bool.true 22183946684301 8000000 0 1 qz241)

noncomputable def ep1591 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.false 2368948603 19200000 0 1 Bool.false 7394648894767 1920000000 0 1 (@ep1546 2368948603 19200000 0 1 (ep1583 rfl) (ep1585 rfl) rfl rfl) (@ep1586 7394648894767 1920000000 0 1 (ep1588 rfl) (ep1590 rfl) rfl rfl)

noncomputable def ep1592 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 2368948603 19200000 0 1 Bool.false 7394648894767 1920000000 0 1 ep1591

noncomputable def ep1593 := @Enclosure.Complex.IsNear.re_isNear qz223 Bool.false 11433118508244744729 ep1543 105738799231933859255 ep1544 Bool.true 12949359559828815941 ep1543 119691170810720482091 ep1544

noncomputable abbrev qz727 := (@Nat.cast Real Real.instNatCast 78364164096)

noncomputable abbrev qz242 := (@Inv.inv Real Real.instInv (Real.sqrt qz727))

noncomputable def ep1594 := @Enclosure.Complex.IsNear.of_eq qz223 (Complex.mk (@HMul.hMul Real Real Real qz0 qz242 (Real.cos qz131)) (@HMul.hMul Real Real Real qz0 qz242 qz679)) Bool.false 11433118508244744729 ep1543 105738799231933859255 ep1544 Bool.true 12949359559828815941 ep1543 119691170810720482091

noncomputable def ep1595 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz727) 615585774066204673 2199023255552 1 2199023255552 3927725 3927726 1099511627776 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz727) (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz727 qz14)) Bool.false 615585774066204673 2199023255552 1 2199023255552 (BSN.sqrt_natCast_div_one 78364164096) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz727 qz14)) Bool.false 615585774066204673 2199023255552 1 2199023255552 615585774066204673 2199023255552 1 2199023255552 (BSN.sqrt_enclosure 78364164096 1 307792887033102336 307792887033102337 1099511627776 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep1596 := nat_lit 8674254360000000000000000

noncomputable def ep1597 := nat_lit 141957810414438141666634235904

noncomputable def ep1598 := nat_lit 39614081257132168796771975168

noncomputable def ep1599 := nat_lit 333091367424000000000000000

noncomputable def ep1600 := BSN.log_dyadic_bound 4 68 5 4 432019261472440320 1099511627776 333091367424 499329192689664 6881280 129503817258 72 64 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 4) (BSN.artanhQ 68) 0 4 499329192689664 432019261472440320 6881280 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep1601 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz133 140505 1000 0 1 16138734555902163 4503599627370496 391275569077 130113815400000000000000 453514579755406682463 900719925474099200 3665078255544259 ep1596 qz18 (BSN.isNear_log_sfrac 36 1 16138734555902163 4503599627370496 391275569077 130113815400000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' qz447 Bool.false ep1597 ep1598 1001665456837120 ep1599 16138734555902163 4503599627370496 391275569077 130113815400000000000000 (BSN.log_rat_reduce_isNear 36 1 5 72 64 129503817258 1099511627776 24973259072661432 36028797018963968 333091367424 1000000000000000 rfl rfl rfl rfl (ep1600 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1602 := nat_lit 268584698417110577889469792256

noncomputable def ep1603 := nat_lit 316912650057057350374175801344

noncomputable def ep1604 := nat_lit 717039587891594629224071083345321745057757200357293845827293534639705037969327212609740237233282523657384339621091801466042895254656067427053426962742398427158746563601173780026970031615845072896

noncomputable def ep1605 := nat_lit 33346807186065974506248031997757090226592655702784298773854402813442710020953735382387552583030990727053975099387314435621209513297521804838009978888016542842337137637482389641015882426221173145600

noncomputable def ep1606 := nat_lit 9559112984057704585878493939646108882384214877033650832914426730025147707463710836373126009772951672982181559767365955986962808842243755275413289191145561300829720690823962977098757308416

noncomputable def ep1607 := nat_lit 4349149839081806624155039572068570683566194719165567387759621440580507111494296547591449227410229294047459114263306712958062312160970108579159249759714659458330871855809744471896200041927446364160

noncomputable def ep1608 := nat_lit 3034559453932003680068570911795895210619931668953371188420750656023286611906789919797267285055820156161911734044245613641530065710074484240258908078809505398652679525010897457332445300786126756249600

noncomputable def ep1609 := BSN.cos_dyadic_bound_f 3816818127931904 4503599627370496 4 3 2199023255552 666833303926 ep1604 ep1605 ep1606 ep1607 ep1608 ep1606 1455437569179 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 3816818127931904) (BSN.cosEvenQ 4503599627370496) 0 3 ep1604 ep1605 ep1606 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 3816818127931904) (BSN.cosOddQ 4503599627370496) 0 3 ep1607 ep1608 ep1606 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz523 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 1107213329480973) (@Nat.cast Real Real.instNatCast 2199023255552))

noncomputable def ep1610 := @Enclosure.Real.IsNear.cos_image qz131 qz523 Bool.false 1107213329480973 2199023255552 465 1099511627776 Bool.false 1455437569179 2199023255552 1 333091367424 (@Enclosure.Real.IsNear.recentre' qz131 Bool.false 453514579755406682463 900719925474099200 3665078255544259 ep1596 1107213329480973 2199023255552 465 1099511627776 (ep1601 rfl) rfl) (Enclosure.sfrac_false_div 1107213329480973 2199023255552) (BSN.cos_reduce0 qz523 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep1602) (@Nat.cast Real Real.instNatCast ep1603)) 226375608064910080 72057594037927936 Bool.false 1455437569179 2199023255552 80 1000000000000000 666182734848 333091367424 (BSN.sin_reduce_arg_pos_rat_q0 1107213329480973 2199023255552 226375608064910080 72057594037927936 80 ep1602 ep1603 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1455437569179 2199023255552 ep1602 ep1603 3816818127931904 4503599627370496 666833303926 666182734848 (ep1609 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1611 := nat_lit 1864048547787080973705889355927861869265752425612698319719370871838071848758431518626766333605386403027414491101939527294037309878203813826292754876137003938695648687130701115106255871440811196416

noncomputable def ep1612 := nat_lit 433508493418857668581224415970842172945704524136195884060107236574755230272398559971038183579402879451701676292035087663075723672867783462894129725544215056950382789287271065333206471540875250892800

noncomputable def ep1613 := nat_lit 9319259925148900002222660686762939452366845821361661205230031310588258188994541913805680125927498151416616682352801571235243702833862164507999095240931072582661611176111541146332260947481671499776

noncomputable def ep1614 := nat_lit 15172797269660018400342854558979476053099658344766855942103753280116433059533949598986336425279100780809558670221228068207650328550372421201294540394047526993263397625054487286662226503930633781248000

noncomputable def ep1615 := BSN.sin_dyadic_bound_f 3816818127931904 4503599627370496 4 3 2199023255552 666833303926 ep1611 ep1612 ep1606 ep1613 ep1614 ep1606 1648455264991 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 3816818127931904) (BSN.sinEvenQ 4503599627370496) 0 3 ep1611 ep1612 ep1606 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 3816818127931904) (BSN.sinOddQ 4503599627370496) 0 3 ep1613 ep1614 ep1606 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1616 := @Enclosure.Real.IsNear.sin_image qz131 qz523 Bool.false 1107213329480973 2199023255552 465 1099511627776 Bool.false 1648455264991 2199023255552 1 333091367424 (@Enclosure.Real.IsNear.recentre' qz131 Bool.false 453514579755406682463 900719925474099200 3665078255544259 ep1596 1107213329480973 2199023255552 465 1099511627776 (ep1601 rfl) rfl) (Enclosure.sfrac_false_div 1107213329480973 2199023255552) (BSN.sin_reduce0 qz523 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep1602) (@Nat.cast Real Real.instNatCast ep1603)) 226375608064910080 72057594037927936 Bool.false 1648455264991 2199023255552 80 1000000000000000 666182734848 333091367424 (BSN.sin_reduce_arg_pos_rat_q0 1107213329480973 2199023255552 226375608064910080 72057594037927936 80 ep1602 ep1603 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1648455264991 2199023255552 ep1602 ep1603 3816818127931904 4503599627370496 666833303926 666182734848 (ep1615 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz524 := (@Enclosure.Real.IsNear.recentre' qz242 Bool.false 7855451 2199023255552 1 2199023255552 7855451 2199023255552 1 2199023255552 (ep1595 rfl rfl) rfl)

noncomputable def ep1617 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz242 (Real.cos qz131)) (@HMul.hMul Real Real Real qz0 qz242 qz679) Bool.false 11433118508244744729 ep1543 105738799231933859255 ep1544 Bool.true 12949359559828815941 ep1543 119691170810720482091 ep1544 (@Enclosure.Real.IsNear.mulLit_ff qz242 (Real.cos qz131) 7855451 2199023255552 1 2199023255552 1455437569179 2199023255552 304662104453 715308264832999882752 11433118508244744729 ep1543 105738799231933859255 ep1544 qz524 (@Enclosure.Real.IsNear.recentre' (Real.cos qz131) Bool.false 1455437569179 2199023255552 155986997479936 366237831594495939969024 1455437569179 2199023255552 304662104453 715308264832999882752 (ep1610 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz242 qz679 7855451 2199023255552 1 2199023255552 1648455264991 2199023255552 304662104453 715308264832999882752 12949359559828815941 ep1543 119691170810720482091 ep1544 qz524 (@Enclosure.Real.IsNear.neg qz132 Bool.false 1648455264991 2199023255552 304662104453 715308264832999882752 (@Enclosure.Real.IsNear.recentre' qz132 Bool.false 1648455264991 2199023255552 155986997479936 366237831594495939969024 1648455264991 2199023255552 304662104453 715308264832999882752 (ep1616 rfl rfl) rfl)) rfl)

noncomputable def ep1618 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz233 7394648894767 1920000000 0 1 12949359559828815941 ep1543 119691170810720482091 ep1544 ep1539

noncomputable def ep1619 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 2368948603 19200000 0 1 Bool.false 7394648894767 1920000000 0 1 ep1591

noncomputable def ep1620 := @Enclosure.Complex.IsNear.im_isNear qz223 Bool.false 11433118508244744729 ep1543 105738799231933859255 ep1544 Bool.true 12949359559828815941 ep1543 119691170810720482091 ep1544

noncomputable def ep1621 := nat_lit 30676367239001168442576080423

noncomputable def ep1622 := nat_lit 92845502946403520617434316800000

noncomputable def ep1623 := nat_lit 283542231883490663472960968873

noncomputable def ep1624 := nat_lit 6711379239493613208626079287633510400000

noncomputable def ep1625 := nat_lit 28181299046910711129145299644381

noncomputable def ep1626 := nat_lit 3094850098213450687247810560000000

noncomputable def ep1627 := nat_lit 156380258974881884166406136803717

noncomputable def ep1628 := @Enclosure.Real.IsNear.addLit_tf_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz233) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz232) ep1621 ep1622 ep1623 ep1624 ep1625 ep1626 ep1627

noncomputable def ep1629 := nat_lit 2521568125530972510285473328103357126522445568046437027020800000

noncomputable def ep1630 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz233 2368948603 19200000 0 1 12949359559828815941 ep1543 119691170810720482091 ep1544 ep1621

noncomputable def ep1631 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz232 7394648894767 1920000000 0 1 11433118508244744729 ep1543 105738799231933859255 ep1544 ep1625

noncomputable abbrev qz525 := (@ep1594 ep1544 (BSN.cpow_neg_s_sub_mk qz12 140505 1000 36 3 78364164096 qz13 rfl EMRow49.d21) ep1617)

noncomputable def ep1632 := ep1534 (@ep1541 ep1528 ep1542 ep1525 ep1526 ep1527 ep1528 (@ep1545 ep1536 ep1537 ep1538 ep1592 (ep1593 qz525) rfl) (@ep1618 ep1526 ep1540 ep1528 ep1619 (ep1620 qz525) rfl) rfl rfl) (@ep1628 ep1533 ep1629 ep1530 ep1526 ep1531 ep1533 (@ep1630 ep1622 ep1623 ep1624 ep1592 (ep1620 qz525) rfl) (@ep1631 ep1626 ep1627 ep1533 ep1619 (ep1593 qz525) rfl) rfl rfl)

noncomputable def ep1633 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.im (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) ep1530 ep1526 ep1531 ep1533 ep1530 ep1526 ep1531

noncomputable def ep1634 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223) Bool.false ep1525 ep1526 ep1527 ep1528 Bool.false ep1530 ep1526 ep1531

noncomputable def ep1635 := @ep1496 4461044904337317375 8070450532247928832 88349566599 1152921504606846976 (@ep1497 1 3670016 (ep1498 (@ep1499 1048576 1 1048576 (ep1500 (@ep1501 3160624804 790156201 40000 0 1 (ep1505 rfl) (ep1508 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) (Enclosure.Real.IsNear.const Bool.false 2 7) rfl) (@ep1509 3991 2199023255552 (BSN.norm_eq_sqrt_mul_add (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (@ep1510 3991 2199023255552 30269845077 2199023255552 3991 2199023255552 (@ep1515 15134920543 15134924534 1099511627776 (@ep1521 ep1517 ep1522 ep1523 ep1524 ep1511 ep1512 ep1513 ep1514 (@ep1529 ep1528 ep1516 ep1517 ep1518 ep1519 (@ep1532 ep1533 ep1632) (@ep1532 ep1533 ep1632) rfl) (@ep1633 ep1533 ep1520 ep1517 ep1522 ep1523 (@ep1634 ep1533 ep1632) (@ep1634 ep1533 ep1632) rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl

theorem EMRow49.d22 : Enclosure.Real.IsNear (@HAdd.hAdd Real Real Real qz420 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 36))) (@HMul.hMul Real Real Real qz0 qz220 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)))) Bool.false 122852423032370997733 217902164370694078464 3304113092939837 31128880624384868352 := ep1494 (ep1495 ep1635) rfl rfl

noncomputable abbrev qz728 := (@HAdd.hAdd Complex Complex Complex qz730 qz736 (@Nat.cast Complex Complex.instNatCast 3))

noncomputable abbrev qz526 := qz728

noncomputable abbrev qz243 := (@HDiv.hDiv Real Real Real qz270 (@Norm.norm Complex Complex.instNorm qz526) (@HAdd.hAdd Real Real Real qz420 (Complex.re qz451) qz288))

noncomputable abbrev qz527 := (@HPow.hPow Complex Complex Complex qz542 qz667 (@HSub.hSub Complex Complex Complex qz654 qz682 qz549))

noncomputable abbrev qz244 := qz527

noncomputable def ep1636 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz142 1 36))) (@HMul.hMul Real Real Real qz0 qz243 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))) 2433545381 103079215104 10937771 103079215104 2361351409640795585 4035225266123964416 321802479319

noncomputable def ep1637 := nat_lit 253226153698167656857873678336

noncomputable def ep1638 := @Enclosure.Real.IsNear.mulLit_ff (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz142 1 36)) 26561 1769472 1 1769472 824589 524288 3675 524288 2433545381 103079215104

noncomputable def ep1639 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (zetaApproximant qz142 1 36)) (Real.sqrt (@HAdd.hAdd Real Real Real qz420 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz142 1 36)) (Complex.re (zetaApproximant qz142 1 36))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz142 1 36)) (Complex.im (zetaApproximant qz142 1 36))))) Bool.false 824589 524288 3675 524288

noncomputable def ep1640 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz420 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz142 1 36)) (Complex.re (zetaApproximant qz142 1 36))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz142 1 36)) (Complex.im (zetaApproximant qz142 1 36))))) Bool.false 1649178 1048576 7350 1048576

noncomputable def ep1641 := nat_lit 70853307642934805601385353953611777890430373

noncomputable def ep1642 := nat_lit 28642856388294202100938485925200632217600000

noncomputable def ep1643 := nat_lit 17515443305377542723862039970965538451471923833233415959519373

noncomputable def ep1644 := nat_lit 794510695354833212580782177134826963751069598288579657728000000

noncomputable def ep1645 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz420 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz142 1 36)) (Complex.re (zetaApproximant qz142 1 36))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz142 1 36)) (Complex.im (zetaApproximant qz142 1 36)))) ep1641 ep1642 ep1643 ep1644 820914 828264

noncomputable def ep1646 := nat_lit 44419629004164177701549489577355863662819428894548481

noncomputable def ep1647 := nat_lit 17957276784617077516798582271637803515055702016000000

noncomputable def ep1648 := nat_lit 18419909591341145768542137478008921013222055680712678240790983

noncomputable def ep1649 := nat_lit 841246618610999872144357599319228549854073692305554931712000000

noncomputable def ep1650 := nat_lit 77491120645932064737062481220111130370926370349369

noncomputable def ep1651 := nat_lit 1454539419553983278860685164002662084719511863296000000

noncomputable def ep1652 := nat_lit 2139516443996290964300382351228034901719682426085957177902003

noncomputable def ep1653 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz142 1 36)) (Complex.re (zetaApproximant qz142 1 36))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz142 1 36)) (Complex.im (zetaApproximant qz142 1 36))) ep1646 ep1647 ep1648 ep1649 ep1650 ep1651 ep1652

noncomputable def ep1654 := nat_lit 14301192516386997826454079188426885347519252769194433839104000000

noncomputable def ep1655 := nat_lit 64611492918022032493105058625526637410081317803748165665860226411301195977473703676954411118394081280000000

noncomputable def ep1656 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (zetaApproximant qz142 1 36)) (Complex.re (zetaApproximant qz142 1 36)) ep1207 ep1208 ep1209 ep1210 ep1207 ep1208 ep1209 ep1210 ep1646

noncomputable def ep1657 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (zetaApproximant qz142 1 36)) (Complex.im (zetaApproximant qz142 1 36)) ep1331 ep1332 ep1333 ep1334 ep1331 ep1332 ep1333 ep1334 ep1650

noncomputable def ep1658 := @ep1636 4035225266123964416 ep1637 7369851044442261827 12105675798371893248 1285502833816709 12105675798371893248 (@ep1638 10937771 103079215104 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaStirlingErrorBound 1 2) (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 96 162) qz510) Bool.false 26561 1769472 1 1769472 (BSN.theta_err_eq 1 2 96 162 EMRow49.d18 EMRow49.d19 rfl) (ep1475 rfl)) (ep1639 (BSN.norm_eq_sqrt_mul_add (zetaApproximant qz142 1 36)) (@ep1640 824589 524288 3675 524288 (@ep1645 524288 (@ep1653 ep1654 ep1655 ep1641 ep1642 ep1643 ep1644 (@ep1656 ep1647 ep1648 ep1649 ep1455 ep1455 rfl) (@ep1657 ep1651 ep1652 ep1654 ep1463 ep1463 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl)

noncomputable abbrev qz245 := (@Norm.norm Complex Complex.instNorm qz526)

noncomputable def ep1659 := @Enclosure.Real.IsNear.of_eq (@HMul.hMul Real Real Real qz0 qz243 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))) (@HMul.hMul Real Real Real qz0 (@HMul.hMul Real Real Real qz0 qz245 qz726) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))) Bool.false 2361351409640795585 4035225266123964416 321802479319 4035225266123964416 (BSN.zrb_shape_eq qz245 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) qz145 3)

noncomputable def ep1660 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz0 qz245 qz726) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) 149490205 3670016 1 3670016 15796027637 1099511627776 2047 1099511627776

noncomputable def ep1661 := @Enclosure.Real.IsNear.mulLit_ff qz245 qz726 149490205 1048576 1 1048576 2 7 0 1 149490205 3670016

noncomputable abbrev qz528 := (Complex.re qz728)

noncomputable abbrev qz529 := (Complex.im qz728)

noncomputable abbrev qz246 := (@HAdd.hAdd Real Real Real qz420 (@HMul.hMul Real Real Real qz267 qz528 qz528) (@HMul.hMul Real Real Real qz267 qz529 qz529))

noncomputable abbrev qz247 := qz526

noncomputable def ep1662 := @Enclosure.Real.IsNear.of_eq qz245 (Real.sqrt qz246) Bool.false 149490205 1048576 1 1048576 (BSN.norm_eq_sqrt_mul_add qz247)

noncomputable def ep1663 := @Enclosure.Real.IsNear.recentre' (Real.sqrt qz246) Bool.false 149490205 1048576 1 1048576 149490205

noncomputable def ep1664 := @Enclosure.Real.IsNear.sqrt_image qz246 5081192621 250000 0 1 74745102 74745103 524288

noncomputable abbrev qz248 := (@HMul.hMul Real Real Real qz267 qz528 qz528)

noncomputable abbrev qz249 := (@HMul.hMul Real Real Real qz267 qz529 qz529)

noncomputable def ep1665 := @Enclosure.Real.IsNear.addLit_ff qz248 qz249 49 4 0 1 5078130121 250000 0 1

noncomputable abbrev qz250 := qz528

noncomputable def ep1666 := @Enclosure.Real.IsNear.mulLit_ff qz250 qz250 7 2 0 1 7 2 0 1 49 4

noncomputable def ep1667 := @Enclosure.Complex.IsNear.of_eq qz247 (Complex.mk qz515 qz145) Bool.false 7 2 0 1 Bool.false 142522 1000 0 1 (BSN.s_add_nat_mk qz145 Bool.false 142522 1000 3 qz146)

noncomputable abbrev qz530 := (ep1667 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7 2) qz145 Bool.false 7 2 0 1 Bool.false 142522 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 7 2) qz147))

noncomputable def ep1668 := @ep1666 0 1 (@Enclosure.Complex.IsNear.re_isNear qz247 Bool.false 7 2 0 1 Bool.false 142522 1000 0 1 qz530)

noncomputable def ep1669 := ep1668 (@Enclosure.Complex.IsNear.re_isNear qz247 Bool.false 7 2 0 1 Bool.false 142522 1000 0 1 qz530)

noncomputable abbrev qz251 := qz529

noncomputable def ep1670 := @Enclosure.Real.IsNear.mulLit_ff qz251 qz251 142522 1000 0 1 142522 1000 0 1 5078130121 250000

noncomputable def ep1671 := @ep1670 0 1 (@Enclosure.Complex.IsNear.im_isNear qz247 Bool.false 7 2 0 1 Bool.false 142522 1000 0 1 qz530)

noncomputable def ep1672 := ep1671 (@Enclosure.Complex.IsNear.im_isNear qz247 Bool.false 7 2 0 1 Bool.false 142522 1000 0 1 qz530)

noncomputable def ep1673 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Real.sqrt (@HAdd.hAdd Real Real Real qz420 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.re (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.im (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))))) Bool.false 15796027637 1099511627776

noncomputable def ep1674 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz420 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.re (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.im (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))))) Bool.false 31592055274 2199023255552

noncomputable def ep1675 := nat_lit 3909312827127742544538636826989986097576011333175638935207433418409

noncomputable def ep1676 := nat_lit 18941061219808501819919755432003027934740885756968960000000000000000000

noncomputable def ep1677 := nat_lit 141147212312750331053282648368015718838206936609267995871941127081516467

noncomputable def ep1678 := nat_lit 2639370348703379335361367778416290266030233999072019075615948800000000000000000000

noncomputable def ep1679 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz420 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.re (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.im (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)))) ep1675 ep1676 ep1677 ep1678

noncomputable def ep1680 := nat_lit 4071419004998651911455405418879236388251759258959355392773034957089

noncomputable def ep1681 := nat_lit 21045623577565002022133061591114475483045428618854400000000000000000000

noncomputable def ep1682 := nat_lit 264664686513450054801854052154735703709903479904317672360145041611270543

noncomputable def ep1683 := nat_lit 5278740697406758670722735556832580532060467998144038151231897600000000000000000000

noncomputable def ep1684 := nat_lit 2450357226289558242287719499986733481494280001122190817117019570289

noncomputable def ep1685 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.re (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.im (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))) ep1680 ep1681 ep1682 ep1683 ep1684

noncomputable def ep1686 := nat_lit 189410612198085018199197554320030279347408857569689600000000000000000000

noncomputable def ep1687 := nat_lit 17629738112050607304711244581295733966510393314218319383737212551762391

noncomputable def ep1688 := nat_lit 822739262066769133386061981684425220798967708720451566456786361704778351987957946862069977856404425163135677414506496000000000000000000000

noncomputable def ep1689 := nat_lit 2017775756866617701274526359884783

noncomputable def ep1690 := nat_lit 145071098353755500964741120000000000

noncomputable def ep1691 := nat_lit 130950997058123281103513226091823

noncomputable def ep1692 := nat_lit 72654942690822891259664541941760000000000

noncomputable def ep1693 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.re (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) ep1689 ep1690 ep1691 ep1692 ep1689 ep1690 ep1691

noncomputable def ep1694 := nat_lit 1565361691842993276170919732926233

noncomputable def ep1695 := nat_lit 435213295061266502894223360000000000

noncomputable def ep1696 := nat_lit 33731691924462794620793666860367

noncomputable def ep1697 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) qz244) Bool.false ep1689 ep1690 ep1691 ep1692 Bool.true ep1694 ep1695 ep1696

noncomputable def ep1698 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) qz244 Bool.false ep1689 ep1690 ep1691 ep1692 Bool.true ep1694 ep1695 ep1696 ep1692

noncomputable def ep1699 := nat_lit 57808950660291023826794058109

noncomputable def ep1700 := nat_lit 580284393415022003858964480000000

noncomputable def ep1701 := nat_lit 540178093566675462738811410203

noncomputable def ep1702 := nat_lit 41946120246835082553912995547709440000000

noncomputable def ep1703 := nat_lit 677409331510563485743741624804011

noncomputable def ep1704 := nat_lit 48357032784585166988247040000000000

noncomputable def ep1705 := nat_lit 56296648155992374120767118340107109

noncomputable abbrev qz252 := (Complex.re qz527)

noncomputable abbrev qz253 := (Complex.im qz527)

noncomputable def ep1706 := @Enclosure.Real.IsNear.subLit_tt_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3)))) qz252) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3)))) qz253) ep1699 ep1700 ep1701 ep1702 ep1703 ep1704 ep1705

noncomputable def ep1707 := nat_lit 31459590185126311915434746660782080000000000

noncomputable def ep1708 := nat_lit 390294593706960724233322080359997046327156453948358163169280000000

noncomputable def ep1709 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3)))) qz252 15234077863 120000000 0 1 3794712826084170043 ep1543 35458535687193859181 ep1544 ep1699

noncomputable def ep1710 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3)))) 15234077863 120000000 0 1 0 1 0 1 15234077863

noncomputable def ep1711 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 45702233589 500000 0 1 15234077863 120000000 0

noncomputable abbrev qz531 := (@HAdd.hAdd Complex Complex Complex qz541 qz681 qz550)

noncomputable abbrev qz254 := qz531

noncomputable def ep1712 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3)) (@HMul.hMul Complex Complex Complex qz74 (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 2)) qz254) Bool.true 45702233589 500000 0 1 Bool.true 361770192865081 125000000 0 1

noncomputable abbrev qz255 := (Complex.re qz531)

noncomputable abbrev qz256 := (Complex.im qz531)

noncomputable def ep1713 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 2))) qz255) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 2))) qz256) 5077942621 100000 0 1 5078130121 125000 0 1

noncomputable def ep1714 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 2))) qz255 5077942621 250000 0 1 5 2 0 1 5077942621 100000

noncomputable abbrev qz532 := (@HAdd.hAdd Complex Complex Complex qz541 qz681 (@Nat.cast Complex Complex.instNatCast 1))

noncomputable abbrev qz257 := qz532

noncomputable def ep1715 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 2)) (@HMul.hMul Complex Complex Complex qz74 (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1)) qz257) Bool.true 5077942621 250000 0 1 Bool.false 71261 250 0 1

noncomputable abbrev qz258 := (Complex.re qz532)

noncomputable abbrev qz259 := (Complex.im qz532)

noncomputable def ep1716 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1))) qz258) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1))) qz259) 3 4 0 1 5078130121 250000 0 1

noncomputable def ep1717 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1))) qz258 1 2 0 1 3 2 0 1 3 4

noncomputable def ep1718 := @ep1717 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 142522 1000 0 1 ep1419)

noncomputable def ep1719 := @Enclosure.Complex.IsNear.of_eq qz257 (Complex.mk qz519 qz145) Bool.false 3 2 0 1 Bool.false 142522 1000 0 1 (BSN.s_add_nat_mk qz145 Bool.false 142522 1000 1 qz146)

noncomputable abbrev qz533 := (ep1719 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 3 2) qz145 Bool.false 3 2 0 1 Bool.false 142522 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 3 2) qz147))

noncomputable def ep1720 := ep1718 (@Enclosure.Complex.IsNear.re_isNear qz257 Bool.false 3 2 0 1 Bool.false 142522 1000 0 1 qz533)

noncomputable def ep1721 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1))) qz259 142522 1000 0 1 142522 1000 0 1 5078130121 250000

noncomputable def ep1722 := @ep1721 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 142522 1000 0 1 ep1419)

noncomputable def ep1723 := ep1722 (@Enclosure.Complex.IsNear.im_isNear qz257 Bool.false 3 2 0 1 Bool.false 142522 1000 0 1 qz533)

noncomputable def ep1724 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1)) qz257 Bool.true 5077942621 250000 0 1 Bool.false 71261 250 0 1 (@ep1716 20311770484 5077942621 250000 0 1 (ep1720 rfl) (ep1723 rfl) rfl rfl)

noncomputable def ep1725 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1))) qz259) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1))) qz258) 71261 1000 0 1 213783 1000 0 1

noncomputable def ep1726 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1))) qz259 1 2 0 1 142522 1000 0 1 71261 1000

noncomputable def ep1727 := @ep1726 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 142522 1000 0 1 ep1419)

noncomputable def ep1728 := ep1727 (@Enclosure.Complex.IsNear.im_isNear qz257 Bool.false 3 2 0 1 Bool.false 142522 1000 0 1 qz533)

noncomputable def ep1729 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1))) qz258 142522 1000 0 1 3 2 0 1 213783 1000

noncomputable def ep1730 := @ep1729 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 142522 1000 0 1 ep1419)

noncomputable def ep1731 := ep1730 (@Enclosure.Complex.IsNear.re_isNear qz257 Bool.false 3 2 0 1 Bool.false 142522 1000 0 1 qz533)

noncomputable abbrev qz260 := (ep1715 (BSN.ascPochhammer_succ_eval_c 1 2 qz451 rfl) (ep1724 (@ep1725 285044000 71261 250 0 1 (ep1728 rfl) (ep1731 rfl) rfl rfl)))

noncomputable def ep1732 := @ep1714 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 5077942621 250000 0 1 Bool.false 71261 250 0 1 qz260)

noncomputable def ep1733 := @Enclosure.Complex.IsNear.of_eq qz254 (Complex.mk qz521 qz145) Bool.false 5 2 0 1 Bool.false 142522 1000 0 1 (BSN.s_add_nat_mk qz145 Bool.false 142522 1000 2 qz146)

noncomputable abbrev qz534 := (ep1733 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 5 2) qz145 Bool.false 5 2 0 1 Bool.false 142522 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 5 2) qz147))

noncomputable def ep1734 := ep1732 (@Enclosure.Complex.IsNear.re_isNear qz254 Bool.false 5 2 0 1 Bool.false 142522 1000 0 1 qz534)

noncomputable def ep1735 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 2))) qz256 71261 250 0 1 142522 1000 0 1 5078130121 125000

noncomputable def ep1736 := @ep1735 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 5077942621 250000 0 1 Bool.false 71261 250 0 1 qz260)

noncomputable def ep1737 := ep1736 (@Enclosure.Complex.IsNear.im_isNear qz254 Bool.false 5 2 0 1 Bool.false 142522 1000 0 1 qz534)

noncomputable def ep1738 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 2)) qz254 Bool.true 45702233589 500000 0 1 Bool.true 361770192865081 125000000 0 1 (@ep1713 1142555839725000 45702233589 500000 0 1 (ep1734 rfl) (ep1737 rfl) rfl rfl)

noncomputable def ep1739 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 2))) qz256) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 2))) qz255) 361859269115081 125000000 0 1 71261 100 0 1

noncomputable def ep1740 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 2))) qz256 5077942621 250000 0 1 142522 1000 0 1 361859269115081 125000000

noncomputable def ep1741 := @ep1740 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 5077942621 250000 0 1 Bool.false 71261 250 0 1 qz260)

noncomputable def ep1742 := ep1741 (@Enclosure.Complex.IsNear.im_isNear qz254 Bool.false 5 2 0 1 Bool.false 142522 1000 0 1 qz534)

noncomputable def ep1743 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 2))) qz255 71261 250 0 1 5 2 0 1 71261 100

noncomputable def ep1744 := @ep1743 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 5077942621 250000 0 1 Bool.false 71261 250 0 1 qz260)

noncomputable def ep1745 := ep1744 (@Enclosure.Complex.IsNear.re_isNear qz254 Bool.false 5 2 0 1 Bool.false 142522 1000 0 1 qz534)

noncomputable abbrev qz261 := (ep1712 (BSN.ascPochhammer_succ_eval_c 2 3 qz451 rfl) (ep1738 (@ep1739 36177019286508100 361770192865081 125000000 0 1 (ep1742 rfl) (ep1745 rfl) rfl rfl)))

noncomputable def ep1746 := @ep1711 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1548) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 45702233589 500000 0 1 Bool.true 361770192865081 125000000 0 1 qz261)

noncomputable def ep1747 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 361770192865081 125000000 0 1 0 1 0

noncomputable def ep1748 := @ep1747 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1548) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 45702233589 500000 0 1 Bool.true 361770192865081 125000000 0 1 qz261)

noncomputable def ep1749 := @Enclosure.Real.IsNear.addLit_ft_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3)))) 361770192865081 90000000000 0 1 0 1 0 1 361770192865081

noncomputable def ep1750 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 361770192865081 125000000 0 1 361770192865081 90000000000 0

noncomputable def ep1751 := @ep1750 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1548) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 45702233589 500000 0 1 Bool.true 361770192865081 125000000 0 1 qz261)

noncomputable def ep1752 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 45702233589 500000 0 1 0 1 0

noncomputable def ep1753 := @ep1752 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1548) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 45702233589 500000 0 1 Bool.true 361770192865081 125000000 0 1 qz261)

noncomputable def ep1754 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.false 15234077863 120000000 0 1 Bool.false 361770192865081 90000000000 0 1 (@ep1710 15234077863 120000000 0 1 (ep1746 rfl) (ep1748 rfl) rfl rfl) (@ep1749 361770192865081 90000000000 0 1 (ep1751 rfl) (ep1753 rfl) rfl rfl)

noncomputable def ep1755 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 15234077863 120000000 0 1 Bool.false 361770192865081 90000000000 0 1 ep1754

noncomputable def ep1756 := @Enclosure.Complex.IsNear.re_isNear qz244 Bool.true 3794712826084170043 ep1543 35458535687193859181 ep1544 Bool.true 16852366789291498779 ep1543 155614390754927982989 ep1544

noncomputable def ep1757 := @Enclosure.Complex.IsNear.of_eq qz244 (Complex.mk (@HMul.hMul Real Real Real qz0 qz242 (Real.cos qz217)) (@HMul.hMul Real Real Real qz0 qz242 qz722)) Bool.true 3794712826084170043 ep1543 35458535687193859181 ep1544 Bool.true 16852366789291498779 ep1543 155614390754927982989

noncomputable def ep1758 := nat_lit 65056907700000000000000000

noncomputable def ep1759 := @Enclosure.Real.IsNear.mulLit_ff qz145 qz133 142522 1000 0 1 16138734555902163 4503599627370496 391275569077 130113815400000000000000 1150062363188144037543 2251799813685248000 27882688327996097 ep1758 qz147 (BSN.isNear_log_sfrac 36 1 16138734555902163 4503599627370496 391275569077 130113815400000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' qz447 Bool.false ep1597 ep1598 1001665456837120 ep1599 16138734555902163 4503599627370496 391275569077 130113815400000000000000 (BSN.log_rat_reduce_isNear 36 1 5 72 64 129503817258 1099511627776 24973259072661432 36028797018963968 333091367424 1000000000000000 rfl rfl rfl rfl (ep1600 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1760 := nat_lit 70189794142092135283516506112

noncomputable def ep1761 := nat_lit 1231396466561171831546445404323013688752332408942700412969522431193787779626569904964454088461297885229155248654607335439728640

noncomputable def ep1762 := nat_lit 61410301428378985366443782906606580462830461786644062426627418836269151622101161260299433135197153936766438149027961922930794823680

noncomputable def ep1763 := nat_lit 979835894765780059462089893971870893640927703995599285072659981564904040842657266727302732145971884391174903296128188416

noncomputable def ep1764 := nat_lit 3225084397449715652311070263176636087512757080966980326807049583105664508224950291557043149384690034502831875050318637182222336

noncomputable def ep1765 := nat_lit 1125855526186948065051469353287787308485225132755141144488169345331601113071854623105489607478614488840718032732179301920397905100800

noncomputable def ep1766 := BSN.sin_dyadic_bound_f 997456967043208 4503599627370496 3 2 2199023255552 666833303926 ep1761 ep1762 ep1763 ep1764 ep1765 ep1763 483067468193 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 997456967043208) (BSN.sinEvenQ 4503599627370496) 0 2 ep1761 ep1762 ep1763 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 997456967043208) (BSN.sinOddQ 4503599627370496) 0 2 ep1764 ep1765 ep1763 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz535 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 1123107776550921) (@Nat.cast Real Real.instNatCast 2199023255552))

noncomputable def ep1767 := @Enclosure.Real.IsNear.cos_image qz217 qz535 Bool.false 1123107776550921 2199023255552 59 137438953472 Bool.true 483067468193 2199023255552 1 333091367424 (@Enclosure.Real.IsNear.recentre' qz217 Bool.false 1150062363188144037543 2251799813685248000 27882688327996097 ep1758 1123107776550921 2199023255552 59 137438953472 (ep1759 rfl) rfl) (Enclosure.sfrac_false_div 1123107776550921 2199023255552) (BSN.cos_reduce1 qz535 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep1760) (@Nat.cast Real Real.instNatCast ep1603)) 226375608064910080 72057594037927936 Bool.false 483067468193 2199023255552 81 1000000000000000 666182734848 333091367424 (BSN.sin_reduce_arg_pos_rat_q1 1123107776550921 2199023255552 226375608064910080 72057594037927936 81 ep1760 ep1603 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 483067468193 2199023255552 ep1760 ep1603 997456967043208 4503599627370496 666833303926 666182734848 (ep1766 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1768 := nat_lit 684109583572159802316940541108293814582804067602702005249416938512096128638779210605704150168602001114812645330294429079044096

noncomputable def ep1769 := nat_lit 6823366825375442818493753656289620051425606865182673602958602092918794624677906806699937015021905992974048683225329102547866091520

noncomputable def ep1770 := nat_lit 2052326791044689875390702699145093500006624920952698024549680670216325256108255946502578995900341711400669153641076694980755456

noncomputable def ep1771 := nat_lit 307051507141894926832218914533032902314152308933220312133137094181345758110505806301497165675985769683832190745139809614653974118400

noncomputable def ep1772 := BSN.cos_dyadic_bound_f 997456967043208 4503599627370496 3 2 2199023255552 666833303926 ep1768 ep1769 ep1763 ep1770 ep1771 ep1763 2145308625729 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 997456967043208) (BSN.cosEvenQ 4503599627370496) 0 2 ep1768 ep1769 ep1763 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 997456967043208) (BSN.cosOddQ 4503599627370496) 0 2 ep1770 ep1771 ep1763 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1773 := @Enclosure.Real.IsNear.sin_image qz217 qz535 Bool.false 1123107776550921 2199023255552 59 137438953472 Bool.false 2145308625729 2199023255552 1 333091367424 (@Enclosure.Real.IsNear.recentre' qz217 Bool.false 1150062363188144037543 2251799813685248000 27882688327996097 ep1758 1123107776550921 2199023255552 59 137438953472 (ep1759 rfl) rfl) (Enclosure.sfrac_false_div 1123107776550921 2199023255552) (BSN.sin_reduce1 qz535 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep1760) (@Nat.cast Real Real.instNatCast ep1603)) 226375608064910080 72057594037927936 Bool.false 2145308625729 2199023255552 81 1000000000000000 666182734848 333091367424 (BSN.sin_reduce_arg_pos_rat_q1 1123107776550921 2199023255552 226375608064910080 72057594037927936 81 ep1760 ep1603 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 2145308625729 2199023255552 ep1760 ep1603 997456967043208 4503599627370496 666833303926 666182734848 (ep1772 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1774 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz242 (Real.cos qz217)) (@HMul.hMul Real Real Real qz0 qz242 qz722) Bool.true 3794712826084170043 ep1543 35458535687193859181 ep1544 Bool.true 16852366789291498779 ep1543 155614390754927982989 ep1544 (@Enclosure.Real.IsNear.mulLit_ft qz242 (Real.cos qz217) 7855451 2199023255552 1 2199023255552 483067468193 2199023255552 38652010999 89413533104124985344 3794712826084170043 ep1543 35458535687193859181 ep1544 qz524 (@Enclosure.Real.IsNear.recentre' (Real.cos qz217) Bool.true 483067468193 2199023255552 19789829631488 45779728949311992496128 483067468193 2199023255552 38652010999 89413533104124985344 (ep1767 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz242 qz722 7855451 2199023255552 1 2199023255552 2145308625729 2199023255552 38652010999 89413533104124985344 16852366789291498779 ep1543 155614390754927982989 ep1544 qz524 (@Enclosure.Real.IsNear.neg qz218 Bool.false 2145308625729 2199023255552 38652010999 89413533104124985344 (@Enclosure.Real.IsNear.recentre' qz218 Bool.false 2145308625729 2199023255552 19789829631488 45779728949311992496128 2145308625729 2199023255552 38652010999 89413533104124985344 (ep1773 rfl rfl) rfl)) rfl)

noncomputable def ep1775 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3)))) qz253 361770192865081 90000000000 0 1 16852366789291498779 ep1543 155614390754927982989 ep1544 ep1703

noncomputable def ep1776 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 15234077863 120000000 0 1 Bool.false 361770192865081 90000000000 0 1 ep1754

noncomputable def ep1777 := @Enclosure.Complex.IsNear.im_isNear qz244 Bool.true 3794712826084170043 ep1543 35458535687193859181 ep1544 Bool.true 16852366789291498779 ep1543 155614390754927982989 ep1544

noncomputable def ep1778 := nat_lit 85576755947967335667751809759

noncomputable def ep1779 := nat_lit 193428131138340667952988160000000

noncomputable def ep1780 := nat_lit 2370641745363880243811965472507

noncomputable def ep1781 := nat_lit 1372813990960066770918478160968483

noncomputable def ep1782 := nat_lit 12827841294269479887944683646158661

noncomputable def ep1783 := @Enclosure.Real.IsNear.addLit_tt (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3)))) qz253) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3)))) qz252) ep1778 ep1779 ep1780 ep1702 ep1781 ep1695 ep1782

noncomputable def ep1784 := nat_lit 302784986608741316892887148036881823067496576806473202401280000000

noncomputable def ep1785 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3)))) qz253 15234077863 120000000 0 1 16852366789291498779 ep1543 155614390754927982989 ep1544 ep1778

noncomputable def ep1786 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3)))) qz252 361770192865081 90000000000 0 1 3794712826084170043 ep1543 35458535687193859181 ep1544 ep1781

noncomputable abbrev qz536 := (@ep1757 ep1544 (BSN.cpow_neg_s_sub_mk qz145 142522 1000 36 3 78364164096 qz146 rfl EMRow49.d21) ep1774)

noncomputable def ep1787 := ep1698 (@ep1706 ep1707 ep1708 ep1689 ep1690 ep1691 ep1692 (@ep1709 ep1700 ep1701 ep1702 ep1755 (ep1756 qz536) rfl) (@ep1775 ep1704 ep1705 ep1707 ep1776 (ep1777 qz536) rfl) rfl rfl) (@ep1783 ep1707 ep1784 ep1694 ep1695 ep1696 ep1692 (@ep1785 ep1779 ep1780 ep1702 ep1755 (ep1777 qz536) rfl) (@ep1786 ep1695 ep1782 ep1707 ep1776 (ep1756 qz536) rfl) rfl rfl)

noncomputable def ep1788 := @Enclosure.Real.IsNear.mulLit_tt (Complex.im (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.im (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) ep1694 ep1695 ep1696 ep1692 ep1694 ep1695 ep1696

noncomputable def ep1789 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) qz244) Bool.false ep1689 ep1690 ep1691 ep1692 Bool.true ep1694 ep1695 ep1696

noncomputable def ep1790 := @ep1660 2361351409640795585 4035225266123964416 321802479319 4035225266123964416 (@ep1661 1 3670016 (ep1662 (@ep1663 1048576 1 1048576 (ep1664 (@ep1665 20324770484 5081192621 250000 0 1 (ep1669 rfl) (ep1672 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) (Enclosure.Real.IsNear.const Bool.false 2 7) rfl) (@ep1673 2047 1099511627776 (BSN.norm_eq_sqrt_mul_add (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (@ep1674 4094 2199023255552 15796027637 1099511627776 2047 1099511627776 (@ep1679 15796025590 15796029684 1099511627776 (@ep1685 ep1686 ep1687 ep1683 ep1688 ep1675 ep1676 ep1677 ep1678 (@ep1693 ep1692 ep1680 ep1681 ep1682 ep1683 (@ep1697 ep1692 ep1787) (@ep1697 ep1692 ep1787) rfl) (@ep1788 ep1692 ep1684 ep1686 ep1687 ep1683 (@ep1789 ep1692 ep1787) (@ep1789 ep1692 ep1787) rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl

theorem EMRow49.d23 : Enclosure.Real.IsNear (@HAdd.hAdd Real Real Real qz420 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz142 1 36))) (@HMul.hMul Real Real Real qz0 qz243 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)))) Bool.false 7369851044442261827 12105675798371893248 1285502833816709 12105675798371893248 := ep1658 (ep1659 ep1790) rfl rfl

noncomputable def EMRow49.d24 := fun (I J : @NonemptyInterval Real Real.instLE) => @LE.le Real Real.instLE (@Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE I)) (@Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE J))

noncomputable abbrev qz537 := (EMRow49.d3 qz552 qz688 (@Enclosure.dec_le_dec qz552 qz688 140505 1000 142522 1000 (@Eq.refl Real qz552) (@Eq.refl Real qz688) rfl rfl rfl) 36 36 1 1)

noncomputable abbrev qz262 := qz537

noncomputable def ep1791 := @Zeta.Certificates.ZIntervalEM.Certificate.mk qz262 (@Enclosure.dec_nonneg qz12 140505 1000 qz13) (@Enclosure.pos_of_ble 1 rfl) (@Enclosure.pos_of_ble 36 rfl)

noncomputable abbrev qz263 := (Zeta.Certificates.ZIntervalEM.fstVal qz537)

noncomputable def ep1792 := @Enclosure.Real.IsNear.neg_val qz263 ep491 ep492

noncomputable def ep1793 := @Enclosure.Real.IsNear.of_eq qz263 (hardyZApproximantEM 1 36 qz12) Bool.true

noncomputable abbrev qz264 := (Zeta.Certificates.ZIntervalEM.sndVal qz537)

noncomputable def ep1794 := BSN.mul_neg_of_neg_pos_r qz263 qz264 (@ep1792 ep493 ep494 (@ep1793 ep491 ep492 ep493 ep494 (@Eq.refl Real (hardyZApproximantEM 1 36 qz12)) EMRow49.d12) rfl rfl rfl)

noncomputable def ep1795 := @Enclosure.Real.IsNear.pos_val qz264 ep1190 ep1191

noncomputable def ep1796 := @Enclosure.Real.IsNear.of_eq qz264 (hardyZApproximantEM 1 36 qz145) Bool.false

noncomputable def ep1797 := BSN.gt_trans_le (@Norm.norm Real Real.norm qz263) (BSN.hardyZErrorBoundStrong 1 36 qz12)

noncomputable def ep1798 := @Enclosure.norm_gt_of_isNear qz263 (BSN.hardyZErrorBoundStrong 1 36 qz12) Bool.true

noncomputable def ep1799 := @Enclosure.Real.IsNear.of_eq (BSN.hardyZErrorBoundStrong 1 36 qz12) (@HAdd.hAdd Real Real Real qz420 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 36))) (@HMul.hMul Real Real Real qz0 qz220 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)))) Bool.false 122852423032370997733 217902164370694078464 3304113092939837 31128880624384868352 (@Eq.refl Real (@HAdd.hAdd Real Real Real qz420 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 36))) (@HMul.hMul Real Real Real qz0 qz220 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)))))

noncomputable def ep1800 := BSN.gt_trans_le (@Norm.norm Real Real.norm qz264) (BSN.hardyZErrorBoundStrong 1 36 qz145)

noncomputable def ep1801 := @Enclosure.norm_gt_of_isNear qz264 (BSN.hardyZErrorBoundStrong 1 36 qz145) Bool.false

noncomputable def ep1802 := @Enclosure.Real.IsNear.of_eq (BSN.hardyZErrorBoundStrong 1 36 qz145) (@HAdd.hAdd Real Real Real qz420 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz142 1 36))) (@HMul.hMul Real Real Real qz0 qz243 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)))) Bool.false 7369851044442261827 12105675798371893248 1285502833816709 12105675798371893248 (@Eq.refl Real (@HAdd.hAdd Real Real Real qz420 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz142 1 36))) (@HMul.hMul Real Real Real qz0 qz243 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)))))

noncomputable def ep1803 := @List.cons EMRow49.d0 (@PSigma.mk Zeta.Certificates.ZIntervalEM Zeta.Certificates.ZIntervalEM.Certificate qz262 (ep1791 (@Enclosure.pos_of_ble 1 rfl) (@Enclosure.pos_of_ble 36 rfl) (ep1794 (@ep1795 ep1192 ep1193 (@ep1796 ep1190 ep1191 ep1192 ep1193 (@Eq.refl Real (hardyZApproximantEM 1 36 qz145)) EMRow49.d17) rfl rfl rfl)) (ep1797 (hardyZErrorBoundEM 1 36 qz12) (BSN.hardyZErrorBoundEM_le_strong 1 36 qz12 rfl) (@ep1798 Bool.false ep491 ep492 ep493 ep494 122852423032370997733 217902164370694078464 3304113092939837 31128880624384868352 (@ep1793 ep491 ep492 ep493 ep494 (@Eq.refl Real (hardyZApproximantEM 1 36 qz12)) EMRow49.d12) (ep1799 EMRow49.d22) rfl rfl rfl rfl rfl)) (ep1800 (hardyZErrorBoundEM 1 36 qz145) (BSN.hardyZErrorBoundEM_le_strong 1 36 qz145 rfl) (@ep1801 Bool.false ep1190 ep1191 ep1192 ep1193 7369851044442261827 12105675798371893248 1285502833816709 12105675798371893248 (@ep1796 ep1190 ep1191 ep1192 ep1193 (@Eq.refl Real (hardyZApproximantEM 1 36 qz145)) EMRow49.d17) (ep1802 EMRow49.d23) rfl rfl rfl rfl rfl)))) (@List.nil EMRow49.d0)

noncomputable abbrev qz538 := (@Enclosure.dec_le_dec qz552 qz688 140505 1000 142522 1000 (@Eq.refl Real qz552) (@Eq.refl Real qz688) rfl rfl rfl)

noncomputable abbrev qz265 := (Zeta.Certificates.CertifiedZeroIntervals.intervals (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedEM ep1803 (@List.IsChain.singleton EMRow49.d1 EMRow49.d24 (EMRow49.d2 qz277 qz453 qz538))))

noncomputable abbrev qz539 := (@NonemptyInterval Real Real.instLE)

noncomputable def ep1804 := And (@Eq (Option Real) (@Option.map qz539 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz539 qz265)) (@Option.some Real qz12))

noncomputable def ep1805 := ep1804 (@Eq (Option Real) (@Option.map qz539 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz539 qz265)) (@Option.some Real qz145))

noncomputable def ep1806 := @And.intro (@Eq Nat (@List.length qz539 qz265) 1) ep1805

noncomputable def ep1807 := @And.intro (@Eq (Option Real) (@Option.map qz539 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz539 qz265)) (@Option.some Real qz12))

noncomputable def ep1808 := @ep1807 (@Eq (Option Real) (@Option.map qz539 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz539 qz265)) (@Option.some Real qz145))

noncomputable abbrev qz266 := (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedEM ep1803 (@List.IsChain.singleton EMRow49.d1 EMRow49.d24 (EMRow49.d2 qz277 qz453 qz538)))

theorem EMRow49.d25 : Zeta.Certificates.BatchSpec 1 140505 1000 142522 1000 := @Exists.intro Zeta.Certificates.CertifiedZeroIntervals (fun (C : Zeta.Certificates.CertifiedZeroIntervals) => And (@Eq Nat (@List.length qz539 (Zeta.Certificates.CertifiedZeroIntervals.intervals C)) 1) (And (@Eq (Option Real) (@Option.map qz539 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz539 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz12)) (@Eq (Option Real) (@Option.map qz539 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz539 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz145)))) qz266 (ep1806 (@Eq.refl Nat 1) (ep1808 (@Eq.refl (Option Real) (@Option.some Real qz12)) (@Eq.refl (Option Real) (@Option.some Real qz145))))

theorem solution : Zeta.Certificates.BatchSpec 1 140505 1000 142522 1000 := EMRow49.d25
#print axioms solution
#check solution
