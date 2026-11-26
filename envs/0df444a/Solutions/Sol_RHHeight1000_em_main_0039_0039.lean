-- Prove2me | solution 1 for RHHeight1000.em_main_0039_0039
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-20T09:43:21.70018+00:00
-- url     : https://prove2.me/submissions/6f30c324-3a7f-4326-a99d-52c61bef6fcb

import Definitions.Def_RHT1000_Support_20261118_S005
/- Copyright (c) 2026 Salvatore Mercuri, Bhavik Mehta.
Apache 2.0 license; see the source project LICENSE. -/
set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable def EMRow39.d0 := @PSigma Zeta.Certificates.ZIntervalEM fun (I : Zeta.Certificates.ZIntervalEM) => Zeta.Certificates.ZIntervalEM.Certificate I

noncomputable def EMRow39.d1 := @NonemptyInterval Real Real.instLE

noncomputable def EMRow39.d2 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @NonemptyInterval.mk Real Real.instLE (@Prod.mk Real Real a b) h

noncomputable def EMRow39.d3 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) (fc sc fb sb : Nat) => Zeta.Certificates.ZIntervalEM.mk (EMRow39.d2 a b h) fc sc fb sb

noncomputable def ep0 := nat_lit 26986075409044028275299783

noncomputable def ep1 := nat_lit 4294967296000000000000000

noncomputable def ep2 := nat_lit 26986075409044045455168967

noncomputable abbrev qz268 := (@instHMul Real Real.instMul)

noncomputable abbrev qz0 := qz268

noncomputable abbrev qz269 := (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 2 1) Real.pi)

noncomputable def ep3 := @BSN.isNear_log_image_fff qz269 884279719003555 140737488355328 1 500000000000000 ep0 ep1 ep2 ep1 4138529546116343 2251799813685248 31250000017647 8823500000000000000 4138529546116343 2251799813685248 31250000017647 8823500000000000000 963576 524288

noncomputable abbrev qz270 := (@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 2 1) Real.pi 2 1 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 140737488355328 1 500000000000000 (Enclosure.Real.IsNear.const Bool.false 2 1) BSN.pi_near_15 rfl)

noncomputable def ep4 := @ep3 3 524288 qz270 rfl rfl rfl rfl

noncomputable def ep5 := nat_lit 53972150818088056550599566

noncomputable def ep6 := nat_lit 34359738368000000000000000

noncomputable def ep7 := nat_lit 9806206225044028275299783

noncomputable def ep8 := nat_lit 44165944593044028275299783

noncomputable def ep9 := nat_lit 13681445815609410487519367394620474863599256634174726093703677122907123617368241606644861540940610176751640793056574796245399519365549113997355475306157239709119582688278313060810592403844863400465080549957745

noncomputable def ep10 := nat_lit 231714499556395493334623298703961145503103241611736774613091488581016477543539392410113701224645713379230392133956226737605624599560350113120270717249177907454870984269546186598262646369758174842349131395304

noncomputable def ep11 := nat_lit 8978369550011295664474073352761810093897501552430546263638635096022803738134167562509900960712119243631997923545019968443113540909076206607473711060286601587364321108377403290080403445693385008949995305

noncomputable def ep12 := BSN.log_dyadic_bound ep7 ep8 5 4 ep9 1048576 282352 ep10 ep11 473518 ep5 ep6 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP ep7) (BSN.artanhQ ep8) 0 4 ep10 ep9 ep11 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz271 := (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))

noncomputable abbrev qz1 := qz271

noncomputable def ep13 := ep4 rfl rfl rfl rfl (BSN.isNear_log_sfrac ep0 ep1 4138529546116343 2251799813685248 31250000017647 8823500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep0) (@Nat.cast Real Real.instNatCast ep1))) Bool.false 69433004117575847641088 37778931862957161709568 1000000000564704 282352000000000000000 4138529546116343 2251799813685248 31250000017647 8823500000000000000 (BSN.log_rat_reduce_isNear ep0 ep1 2 ep5 ep6 473518 1048576 24973259072661432 36028797018963968 282352 1000000000000000 rfl rfl rfl rfl (ep12 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep14 := nat_lit 53972150818088090910337934

noncomputable def ep15 := nat_lit 9806206225044045455168967

noncomputable def ep16 := nat_lit 44165944593044045455168967

noncomputable def ep17 := nat_lit 13681445815609453062485491347592146866046743284321690683909457683007658987562290830600045658905080811372395010565947827677605470036294121079488508864180301737865471494204890974265645509835068840465080549957745

noncomputable def ep18 := nat_lit 231714499556396865510889920206523150079811393376960301632499817942333196803513131357563499488546302200815366867712007119763002650772307103678175657719139104636874731038771518520299266622696414842349131395304

noncomputable def ep19 := nat_lit 8978369550011421500876706511871067098718760264493934208903156435737864998391937547068187824077011975074541700434630537294838404525415248443919841847024664017658842168336182958576672102333385008949995305

noncomputable def ep20 := BSN.log_dyadic_bound ep15 ep16 5 4 ep17 1048576 282352 ep18 ep19 473518 ep14 ep6 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP ep15) (BSN.artanhQ ep16) 0 4 ep18 ep17 ep19 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep21 := ep13 (BSN.isNear_log_sfrac ep2 ep1 4138529546116343 2251799813685248 31250000017647 8823500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep2) (@Nat.cast Real Real.instNatCast ep1))) Bool.false 69433004117575847641088 37778931862957161709568 1000000000564704 282352000000000000000 4138529546116343 2251799813685248 31250000017647 8823500000000000000 (BSN.log_rat_reduce_isNear ep2 ep1 2 ep14 ep6 473518 1048576 24973259072661432 36028797018963968 282352 1000000000000000 rfl rfl rfl rfl (ep20 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable abbrev qz2 := (Real.log (@HMul.hMul Real Real Real qz268 (2 : Real) Real.pi))

theorem EMRow39.d4 : Enclosure.Real.IsNear qz2 Bool.false 120447 65536 3 524288 := @Enclosure.Real.IsNear.of_eq qz2 (Real.log qz269) Bool.false 120447 65536 3 524288 BSN.log_two_pi_eq (@Enclosure.Real.IsNear.recentre' (Real.log qz269) Bool.false 963576 524288 3 524288 120447 65536 3 524288 (ep21 rfl rfl rfl rfl rfl rfl rfl rfl) rfl)

noncomputable def ep22 := nat_lit 8589934592000000000000000

noncomputable def ep23 := @BSN.isNear_log_image_fff Real.pi 226375608064910080 72057594037927936 1 1000000000000000 ep0 ep22 ep2 ep22 1200336 1048576 1 282352 1200336 1048576 1 282352 600168 524288 2 524288 BSN.pi_near_15 rfl rfl rfl

noncomputable def ep24 := nat_lit 17179869184000000000000000

noncomputable def ep25 := nat_lit 18396140817044028275299783

noncomputable def ep26 := nat_lit 35576010001044028275299783

noncomputable def ep27 := nat_lit 145019262663961446558303139663424756232419223153299357158415217874016130572233056993847515999529612750616182853355499335896178729185698845314776375864537073527142908641610750276034469165612529925303649396973267518946591078603565291376312767403717761600170009932259137778521478520425507632472584532570900560707662248426541531715360699177249902784721815296292248142738824858695953661559845440650653128788875447728828657762006237171740033404723254477174341920697506370253193455781322964835857351124092897592956162654178130575

noncomputable def ep28 := nat_lit 15500762873619990602332184736899274490522931101512051618692838888825382235673431503644115344741331161500627469184702974962114537943617674254904297224139410345221262767191485292268260077615645253784097850065864022184521411511133693085443040736512010941548648374196772723338837137976260321103066698629790037694560548409922339907589559883712609967105556007429010014773911317423638534096849366294542840133852248768895750397896505791271178551667935288585787166713880920071720072716082683081155281219708172458141800988558163320

noncomputable def ep29 := nat_lit 12900190794487083783367107939442176642390171280542213571554777169279725287102813254708993369099729304728646904879886535518616983985412662170766446331701281703998252143668221340329975389245922410714088123244705567402747658401492589451585970559635763980329972215329212888079422466283203384882259392047898400615815810081169907384366653346471604103896809335921621947903075223769953790093549808584241881353287841076643853121427928248525828402335494512605306631304432120211393210317325496757155861061354331245840675149075

noncomputable def ep30 := BSN.log_dyadic_bound ep25 ep26 11 10 ep27 1048576 282352 ep28 ep29 1200336 ep5 ep24 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base10 (BSN.artanhP ep25) (BSN.artanhQ ep26) 0 10 ep28 ep27 ep29 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep31 := nat_lit 18396140817044045455168967

noncomputable def ep32 := nat_lit 35576010001044045455168967

noncomputable def ep33 := nat_lit 145019262663962847171784895425483977818796535899227200426399035286881207006285364467913811844950531107314785650583974625982406238691319033447632878979985852280879486690814033867010958364699188952871572448188560932645032521756218245629809291975913196623825614492380080480004685076434733043183791438169545293975334857826316990371107134320667652578346815517853870648072772035977941843998949310557583393428557296298890786965786350523173236912472938174255438182435383147950274229549088258679583524155427309880956162654178130575

noncomputable def ep34 := nat_lit 15500762873620157189619721156942591192100275120160672416764593300158228469749443299607348495591439275767946573253526107895503597951484257520435868240203420954375895980141891044871083424251900562230440202302413072793440172565998181227591194192658878334739610458454844032013325963992941389843551995646587189684848765634635122388286241104146031552341815777883628509454807838726994150833304950745987647656768534710890974432620160470644835720379148964170536679305861738540146791997074363921127776563807649880221800988558163320

noncomputable def ep35 := nat_lit 12900190794487324729109480814509220959173684627296055849229843377126536688487849343376525559792931631054411655715865486295286288812423905434305314401904993536755333953308594664509631000767632482919425633906965368325056855874260596615770736441041599390097968820060635361729170158825410327022636428624381203910573184452046894301676992229743752846881064485858738985580654099214803581683226335297196686880535448467637789069028262446657986458573827723305156755787640135484017403116612632808333639900906331245840675149075

noncomputable def ep36 := BSN.log_dyadic_bound ep31 ep32 11 10 ep33 1048576 282352 ep34 ep35 1200336 ep14 ep24 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base10 (BSN.artanhP ep31) (BSN.artanhQ ep32) 0 10 ep34 ep33 ep35 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep37 := @Enclosure.Real.IsNear.recentre' (Real.log Real.pi) Bool.false 600168 524288 2 524288 75021 65536 1 262144 (ep23 rfl rfl rfl rfl rfl (BSN.isNear_log_sfrac ep0 ep22 1200336 1048576 1 282352 Bool.false (BSN.logfrac_isNear ep5 ep24 1 ep0 ep22 1200336 1048576 282352 rfl rfl rfl (ep30 rfl))) (BSN.isNear_log_sfrac ep2 ep22 1200336 1048576 1 282352 Bool.false (BSN.logfrac_isNear ep14 ep24 1 ep2 ep22 1200336 1048576 282352 rfl rfl rfl (ep36 rfl))) rfl rfl rfl rfl rfl rfl rfl rfl) rfl

theorem EMRow39.d5 : Enclosure.Real.IsNear (Real.log Real.pi) Bool.false 75021 65536 1 262144 := ep37

noncomputable abbrev qz609 := (@HAdd.hAdd Complex Complex Complex (@instHAdd Complex Complex.instAdd) (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (2 : Complex)) (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul) Complex.I ↑(Enclosure.sfrac Bool.false 119766 1000)))

noncomputable abbrev qz534 := qz609

noncomputable abbrev qz272 := qz534

noncomputable abbrev qz3 := (BSN.headSumC qz272 9)

noncomputable abbrev qz610 := (@instHAdd Complex Complex.instAdd)

noncomputable abbrev qz535 := qz610

noncomputable abbrev qz273 := qz535

noncomputable abbrev qz4 := qz273

noncomputable abbrev qz5 := qz272

noncomputable abbrev qz536 := (@instHPow Complex Complex Complex.instPow)

noncomputable abbrev qz274 := qz536

noncomputable abbrev qz6 := qz274

noncomputable abbrev qz537 := (@Neg.neg Complex Complex.instNeg qz609)

noncomputable abbrev qz275 := qz537

noncomputable abbrev qz7 := qz275

noncomputable abbrev qz538 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 8) qz7)

noncomputable def ep38 := @Enclosure.Complex.IsNear.of_eq qz3 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 8) qz538) Bool.false 380215730853 274877906944 14024044413045 4850770423840768 Bool.true 634474951203 1099511627776 56100960853883 19403081695363072

noncomputable def ep39 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 8) qz538 Bool.false 443579648239 274877906944 12553232471935 4850770423840768 Bool.true 929220711099 1099511627776 50215747637171 19403081695363072 Bool.true

noncomputable abbrev qz539 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 7) qz7)

noncomputable def ep40 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 8) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 7) qz539) Bool.false 443579648239 274877906944 12553232471935 4850770423840768 Bool.true 929220711099 1099511627776 50215747637171 19403081695363072

noncomputable def ep41 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 7) qz539 Bool.false 1425756700331 1099511627776 43920833593893 19403081695363072 Bool.true 702927855249 1099511627776 43929095566353 19403081695363072 Bool.false

noncomputable def ep42 := nat_lit 1950883924334273527545856

noncomputable abbrev qz540 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 6) qz7)

noncomputable def ep43 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 7) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 6) qz540) Bool.false 1425756700331 1099511627776 43920833593893 19403081695363072 Bool.true 702927855249 1099511627776 43929095566353 19403081695363072

noncomputable def ep44 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 6) qz540 Bool.false 1169589945941 1099511627776 37123258116703 19403081695363072 Bool.true 5223879561 17179869184 2320430324553 1212692605960192 Bool.false

noncomputable abbrev qz541 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 5) qz7)

noncomputable def ep45 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 6) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 5) qz541) Bool.false 1169589945941 1099511627776 37123258116703 19403081695363072 Bool.true 5223879561 17179869184 2320430324553 1212692605960192

noncomputable def ep46 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 5) qz541 Bool.false 692228674139 549755813888 14840185872347 9701540847681536 Bool.true 388306863223 549755813888 7418860160871 4850770423840768 Bool.true

noncomputable abbrev qz542 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 4) qz7)

noncomputable def ep47 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 5) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 4) qz542) Bool.false 692228674139 549755813888 14840185872347 9701540847681536 Bool.true 388306863223 549755813888 7418860160871 4850770423840768

noncomputable def ep48 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 4) qz542 Bool.false 936851551173 549755813888 10675777206737 9701540847681536 Bool.true 525877138705 1099511627776 21354651303151 19403081695363072 Bool.true

noncomputable abbrev qz543 := (@Nat.cast Complex Complex.instNatCast 3)

noncomputable abbrev qz276 := qz543

noncomputable abbrev qz8 := qz276

noncomputable def ep49 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 4) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 3) (@HPow.hPow Complex Complex Complex qz6 qz8 qz7)) Bool.false 936851551173 549755813888 10675777206737 9701540847681536 Bool.true 525877138705 1099511627776 21354651303151 19403081695363072

noncomputable def ep50 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 3) (@HPow.hPow Complex Complex Complex qz6 qz8 qz7) Bool.false 640992593093 549755813888 5873354485653 9701540847681536 Bool.true 377877350565 549755813888 5880176674677 9701540847681536 Bool.false

noncomputable abbrev qz544 := (@Nat.cast Complex Complex.instNatCast 2)

noncomputable abbrev qz277 := qz544

noncomputable abbrev qz9 := qz277

noncomputable def ep51 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 3) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 2) (@HPow.hPow Complex Complex Complex qz6 qz9 qz7)) Bool.false 640992593093 549755813888 5873354485653 9701540847681536 Bool.true 377877350565 549755813888 5880176674677 9701540847681536

noncomputable def ep52 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 2) (@HPow.hPow Complex Complex Complex qz6 qz9 qz7) Bool.false 1 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable abbrev qz278 := (Enclosure.sfrac Bool.false 0 1)

noncomputable abbrev qz10 := qz278

noncomputable def ep53 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 2) (Complex.mk (Enclosure.sfrac Bool.false 1 1) qz10) Bool.false 1 1 0 1 Bool.false 0 1 0 1 (BSN.head_sum_c_two qz5)

noncomputable abbrev qz545 := (@Nat.cast Real Real.instNatCast 2)

noncomputable abbrev qz11 := (@Inv.inv Real Real.instInv (Real.sqrt qz545))

noncomputable abbrev qz611 := (Enclosure.sfrac Bool.false 119766 1000)

noncomputable abbrev qz546 := qz611

noncomputable abbrev qz279 := qz546

noncomputable abbrev qz280 := (Enclosure.sfrac Bool.false 2 1)

noncomputable abbrev qz12 := (@HMul.hMul Real Real Real qz268 qz279 (Real.log qz280))

noncomputable abbrev qz13 := qz279

noncomputable abbrev qz281 := (@Eq.refl Real qz546)

noncomputable abbrev qz14 := qz281

noncomputable def ep54 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz9 qz7) (Complex.mk (@HMul.hMul Real Real Real qz0 qz11 (Real.cos qz12)) (@HMul.hMul Real Real Real qz0 qz11 (@Neg.neg Real Real.instNeg (Real.sin qz12)))) Bool.false 91236779205 549755813888 5873354485653 9701540847681536 Bool.true 377877350565 549755813888 5880176674677 9701540847681536 (BSN.cpow_neg_s_mk qz13 119766 1000 2 qz14 rfl)

noncomputable abbrev qz15 := (@Nat.cast Real Real.instNatCast 1)

noncomputable def ep55 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz545) 1482911 1048576 1 1048576 370727 370728 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz545) (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz545 qz15)) Bool.false 1482911 1048576 1 1048576 (BSN.sqrt_natCast_div_one 2) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz545 qz15)) Bool.false 1482911 1048576 1 1048576 1482911 1048576 1 1048576 (BSN.sqrt_enclosure 2 1 741455 741456 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep56 := BSN.log_dyadic_bound 1 3 6 5 613814355 524288 141176 24381081 945 363408 4 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 1) (BSN.artanhQ 3) 0 5 24381081 613814355 945 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep57 := nat_lit 2410124434840263456239342546413950980796525091760448981081467838017233152382081

noncomputable def ep58 := nat_lit 18237254054877300779212430138868345486890022584838388836214569481246317918289920

noncomputable def ep59 := nat_lit 4533005515154609706593226751364091784788032119413216079145871072239342851201

noncomputable def ep60 := nat_lit 7221307293490481149304841185739124758819999211042520511086111771907220771443841

noncomputable def ep61 := nat_lit 820676432469478535064559356249075546910051016317727497629655626656084306323046400

noncomputable abbrev qz16 := (BSN.cosEvenQ 2147483648)

noncomputable abbrev qz282 := (BSN.cosOddQ 2147483648)

noncomputable def ep62 := BSN.cos_dyadic_bound_f 2864496401 2147483648 3 2 1048576 282628 ep57 ep58 ep59 ep60 ep61 ep59 246102 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2864496401) qz16 0 2 ep57 ep58 ep59 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2864496401) qz282 0 2 ep60 ep61 ep59 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz17 := (@Nat.cast Real Real.instNatCast 1048576)

noncomputable abbrev qz18 := (Real.log qz280)

noncomputable abbrev qz19 := (Enclosure.Real.IsNear.const Bool.false 119766 1000)

noncomputable abbrev qz20 := (@Nat.cast Real Real.instNatCast 151115727451828646838272)

noncomputable abbrev qz283 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 87047845) qz17)

noncomputable abbrev qz284 := (BSN.isNear_log_sfrac 2 1 363408 524288 1 141176 Bool.false (BSN.logfrac_isNear 4 2 1 2 1 363408 524288 141176 rfl rfl rfl (ep56 rfl)))

noncomputable def ep63 := @Enclosure.Real.IsNear.cos_image qz12 qz283 Bool.false 87047845 1048576 445 524288 Bool.false 246102 1048576 1 141176 (@Enclosure.Real.IsNear.recentre' qz12 Bool.false 1360122579 16384000 59883 70588000 87047845 1048576 445 524288 (@Enclosure.Real.IsNear.mulLit_ff qz13 qz18 119766 1000 0 1 363408 524288 1 141176 1360122579 16384000 59883 70588000 qz19 qz284 rfl) rfl) (Enclosure.sfrac_false_div 87047845 1048576) (BSN.cos_reduce0 qz283 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 201571014454850281799680) qz20) 226375608064910080 72057594037927936 Bool.false 246102 1048576 13 1000000000000000 282352 141176 (BSN.sin_reduce_arg_pos_rat_q0 87047845 1048576 226375608064910080 72057594037927936 13 201571014454850281799680 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 246102 1048576 201571014454850281799680 151115727451828646838272 2864496401 2147483648 282628 282352 (ep62 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep64 := nat_lit 4334597578300350533465542002144020492005914739473277593083325411573228200006785

noncomputable def ep65 := nat_lit 164135286493895707012911871249815109382010203263545499525931125331216861264609280

noncomputable def ep66 := nat_lit 11345178315190667743360982876589273711411548456141438965375806572384353016353921

noncomputable def ep67 := nat_lit 3009146919054754628570050972913277005336853726498334157975403964405642456517836800

noncomputable abbrev qz21 := (BSN.sinEvenQ 2147483648)

noncomputable abbrev qz285 := (BSN.sinOddQ 2147483648)

noncomputable def ep68 := BSN.sin_dyadic_bound_f 2864496401 2147483648 3 2 1048576 282628 ep64 ep65 ep59 ep66 ep67 ep59 1019286 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2864496401) qz21 0 2 ep64 ep65 ep59 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2864496401) qz285 0 2 ep66 ep67 ep59 rfl rfl rfl rfl) rfl rfl

noncomputable def ep69 := @Enclosure.Real.IsNear.sin_image qz12 qz283 Bool.false 87047845 1048576 445 524288 Bool.false 1019286 1048576 1 141176 (@Enclosure.Real.IsNear.recentre' qz12 Bool.false 1360122579 16384000 59883 70588000 87047845 1048576 445 524288 (@Enclosure.Real.IsNear.mulLit_ff qz13 qz18 119766 1000 0 1 363408 524288 1 141176 1360122579 16384000 59883 70588000 qz19 qz284 rfl) rfl) (Enclosure.sfrac_false_div 87047845 1048576) (BSN.sin_reduce0 qz283 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 201571014454850281799680) qz20) 226375608064910080 72057594037927936 Bool.false 1019286 1048576 13 1000000000000000 282352 141176 (BSN.sin_reduce_arg_pos_rat_q0 87047845 1048576 226375608064910080 72057594037927936 13 201571014454850281799680 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1019286 1048576 201571014454850281799680 151115727451828646838272 2864496401 2147483648 282628 282352 (ep68 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz286 := (@Enclosure.Real.IsNear.recentre' qz11 Bool.false 741455 1048576 1 1048576 741455 1048576 1 1048576 (ep55 rfl rfl) rfl)

noncomputable def ep70 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz11 (Real.cos qz12)) (@HMul.hMul Real Real Real qz0 qz11 (@Neg.neg Real Real.instNeg (Real.sin qz12))) Bool.false 91236779205 549755813888 5873354485653 9701540847681536 Bool.true 377877350565 549755813888 5880176674677 9701540847681536 (@Enclosure.Real.IsNear.mulLit_ff qz11 (Real.cos qz12) 741455 1048576 1 1048576 123051 524288 7918451 9252110336 91236779205 549755813888 5873354485653 9701540847681536 qz286 (@Enclosure.Real.IsNear.recentre' (Real.cos qz12) Bool.false 246102 1048576 63347608 74016882688 123051 524288 7918451 9252110336 (ep63 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz11 (@Neg.neg Real Real.instNeg (Real.sin qz12)) 741455 1048576 1 1048576 509643 524288 7918451 9252110336 377877350565 549755813888 5880176674677 9701540847681536 qz286 (@Enclosure.Real.IsNear.neg (Real.sin qz12) Bool.false 509643 524288 7918451 9252110336 (@Enclosure.Real.IsNear.recentre' (Real.sin qz12) Bool.false 1019286 1048576 63347608 74016882688 509643 524288 7918451 9252110336 (ep69 rfl rfl) rfl)) rfl)

noncomputable abbrev qz287 := (Enclosure.Real.IsNear.const Bool.false 0 1)

noncomputable abbrev qz22 := qz287

noncomputable def ep71 := @ep52 91236779205 549755813888 5873354485653 9701540847681536 Bool.true 377877350565 549755813888 5880176674677 9701540847681536 Bool.false 640992593093 640992593093 549755813888 5873354485653 9701540847681536 Bool.true 377877350565 377877350565 549755813888 5880176674677 9701540847681536 (ep53 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 1) qz10 Bool.false 1 1 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 1) qz22)) (ep54 ep70) rfl rfl

noncomputable abbrev qz547 := (@Nat.cast Real Real.instNatCast 3)

noncomputable abbrev qz23 := (@Inv.inv Real Real.instInv (Real.sqrt qz547))

noncomputable abbrev qz24 := (@HMul.hMul Real Real Real qz268 qz279 (Real.log (Enclosure.sfrac Bool.false 3 1)))

noncomputable def ep72 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz8 qz7) (Complex.mk (@HMul.hMul Real Real Real qz0 qz23 (Real.cos qz24)) (@HMul.hMul Real Real Real qz0 qz23 (@Neg.neg Real Real.instNeg (Real.sin qz24)))) Bool.false 1155699055 2147483648 1200605680271 2425385211920384 Bool.false 229877562425 1099511627776 9594297953797 19403081695363072 (BSN.cpow_neg_s_mk qz13 119766 1000 3 qz14 rfl)

noncomputable def ep73 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz547) 1816187 1048576 1 1048576 302697 302698 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz547) (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz547 qz15)) Bool.false 1816187 1048576 1 1048576 (BSN.sqrt_natCast_div_one 3) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz547 qz15)) Bool.false 1816187 1048576 1 1048576 1816187 1048576 1 1048576 (BSN.sqrt_enclosure 3 1 908093 908094 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep74 := BSN.log_dyadic_bound 1 2 10 9 171633298636800 524288 141176 16925142283965 34459425 575989 3 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base9 (BSN.artanhP 1) (BSN.artanhQ 2) 0 9 16925142283965 171633298636800 34459425 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep75 := nat_lit 2840564137745873457131751192636695164592912460328512651790442496412744320495745

noncomputable def ep76 := nat_lit 1948098027216651042601214476250424076336746311516265517721998305658964488321

noncomputable def ep77 := nat_lit 7436418678242746381276089252515510458762606473498887753374847112395644420698241

noncomputable def ep78 := BSN.sin_dyadic_bound_f 2577515887 2147483648 3 2 1048576 282628 ep75 ep65 ep76 ep77 ep67 ep76 977408 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2577515887) qz21 0 2 ep75 ep65 ep76 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2577515887) qz285 0 2 ep77 ep67 ep76 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz25 := (Real.log (Enclosure.sfrac Bool.false 3 1))

noncomputable abbrev qz288 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 137967797) qz17)

noncomputable abbrev qz289 := (BSN.isNear_log_sfrac 3 1 575989 524288 1 141176 Bool.false (BSN.logfrac_isNear 3 1 2 3 1 575989 524288 141176 rfl rfl rfl (ep74 rfl)))

noncomputable def ep79 := @Enclosure.Real.IsNear.cos_image qz24 qz288 Bool.false 137967797 1048576 445 524288 Bool.false 977408 1048576 1 141176 (@Enclosure.Real.IsNear.recentre' qz24 Bool.false 34491949287 262144000 59883 70588000 137967797 1048576 445 524288 (@Enclosure.Real.IsNear.mulLit_ff qz13 qz25 119766 1000 0 1 575989 524288 1 141176 34491949287 262144000 59883 70588000 qz19 qz289 rfl) rfl) (Enclosure.sfrac_false_div 137967797 1048576) (BSN.cos_reduce3 qz288 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 181376556077997929529344) qz20) 226375608064910080 72057594037927936 Bool.false 977408 1048576 20 1000000000000000 282352 141176 (BSN.sin_reduce_arg_pos_rat_q3 137967797 1048576 226375608064910080 72057594037927936 20 181376556077997929529344 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 977408 1048576 181376556077997929529344 151115727451828646838272 2577515887 2147483648 282628 282352 (ep78 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep80 := nat_lit 1578957008982025987758795646787608613252212142987625369002566719476261940048001

noncomputable def ep81 := nat_lit 4732974830891644661191184511410324991603962936339843575972256161817467891167361

noncomputable def ep82 := BSN.cos_dyadic_bound_f 2577515887 2147483648 3 2 1048576 282628 ep80 ep58 ep76 ep81 ep61 ep76 379715 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2577515887) qz16 0 2 ep80 ep58 ep76 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2577515887) qz282 0 2 ep81 ep61 ep76 rfl rfl rfl rfl) rfl rfl

noncomputable def ep83 := @Enclosure.Real.IsNear.sin_image qz24 qz288 Bool.false 137967797 1048576 445 524288 Bool.true 379715 1048576 1 141176 (@Enclosure.Real.IsNear.recentre' qz24 Bool.false 34491949287 262144000 59883 70588000 137967797 1048576 445 524288 (@Enclosure.Real.IsNear.mulLit_ff qz13 qz25 119766 1000 0 1 575989 524288 1 141176 34491949287 262144000 59883 70588000 qz19 qz289 rfl) rfl) (Enclosure.sfrac_false_div 137967797 1048576) (BSN.sin_reduce3 qz288 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 181376556077997929529344) qz20) 226375608064910080 72057594037927936 Bool.false 379715 1048576 20 1000000000000000 282352 141176 (BSN.sin_reduce_arg_pos_rat_q3 137967797 1048576 226375608064910080 72057594037927936 20 181376556077997929529344 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 379715 1048576 181376556077997929529344 151115727451828646838272 2577515887 2147483648 282628 282352 (ep82 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz290 := (@Enclosure.Real.IsNear.recentre' qz23 Bool.false 605395 1048576 1 1048576 605395 1048576 1 1048576 (ep73 rfl rfl) rfl)

noncomputable def ep84 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz23 (Real.cos qz24)) (@HMul.hMul Real Real Real qz0 qz23 (@Neg.neg Real Real.instNeg (Real.sin qz24))) Bool.false 1155699055 2147483648 1200605680271 2425385211920384 Bool.false 229877562425 1099511627776 9594297953797 19403081695363072 (@Enclosure.Real.IsNear.mulLit_ff qz23 (Real.cos qz24) 605395 1048576 1 1048576 1909 2048 7918451 9252110336 1155699055 2147483648 1200605680271 2425385211920384 qz290 (@Enclosure.Real.IsNear.recentre' (Real.cos qz24) Bool.false 977408 1048576 63347608 74016882688 1909 2048 7918451 9252110336 (ep79 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz23 (@Neg.neg Real Real.instNeg (Real.sin qz24)) 605395 1048576 1 1048576 379715 1048576 7918451 9252110336 229877562425 1099511627776 9594297953797 19403081695363072 qz290 (@Enclosure.Real.IsNear.neg (Real.sin qz24) Bool.true 379715 1048576 7918451 9252110336 (@Enclosure.Real.IsNear.recentre' (Real.sin qz24) Bool.true 379715 1048576 63347608 74016882688 379715 1048576 7918451 9252110336 (ep83 rfl rfl) rfl)) rfl)

noncomputable def ep85 := @ep50 1155699055 2147483648 1200605680271 2425385211920384 Bool.false 229877562425 1099511627776 9594297953797 19403081695363072 Bool.false 2011873386747452719104 936851551173 549755813888 10675777206737 9701540847681536 Bool.true 289104014393859941335040 525877138705 1099511627776 21354651303151 19403081695363072 (ep51 (BSN.head_sum_c_succ qz5 2 3 rfl rfl) (ep71 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep72 ep84) rfl rfl

noncomputable abbrev qz548 := (@Nat.cast Real Real.instNatCast 4)

noncomputable abbrev qz26 := (@Inv.inv Real Real.instInv (Real.sqrt qz548))

noncomputable abbrev qz291 := (Real.log (Enclosure.sfrac Bool.false 4 1))

noncomputable abbrev qz27 := (@HMul.hMul Real Real Real qz268 qz279 qz291)

noncomputable def ep86 := @Enclosure.Complex.IsNear.of_eq qz542 (Complex.mk (@HMul.hMul Real Real Real qz0 qz26 (Real.cos qz27)) (@HMul.hMul Real Real Real qz0 qz26 (@Neg.neg Real Real.instNeg (Real.sin qz27)))) Bool.true 122311438517 274877906944 2082204332805 4850770423840768 Bool.true 250736587741 1099511627776 8320789340333 19403081695363072 (BSN.cpow_neg_s_mk qz13 119766 1000 4 qz14 rfl)

noncomputable def ep87 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz548) 2097153 1048576 1 1048576 262143 262144 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz548) (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz548 qz15)) Bool.false 2097153 1048576 1 1048576 (BSN.sqrt_natCast_div_one 4) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz548 qz15)) Bool.false 2097153 1048576 1 1048576 2097153 1048576 1 1048576 (BSN.sqrt_enclosure 4 1 1048576 1048577 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep88 := nat_lit 318077276165597140789031982421875

noncomputable def ep89 := nat_lit 49379992292270016474244603430625

noncomputable def ep90 := nat_lit 20095619060363156210525625

noncomputable def ep91 := BSN.log_dyadic_bound 3 5 14 13 ep88 524288 141176 ep89 ep90 726817 8 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base13 (BSN.artanhP 3) (BSN.artanhQ 5) 0 13 ep89 ep88 ep90 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep92 := nat_lit 1983237783782690596269827462876102175535663977908998593578484579833776963584000

noncomputable def ep93 := nat_lit 950015965288777139353683010162812132865481105249727203314616227601219321856

noncomputable def ep94 := nat_lit 5192656074534674493909642154087623049616385353686496758185902616148537692389376

noncomputable def ep95 := BSN.sin_dyadic_bound_f 2356222848 2147483648 3 2 1048576 282628 ep92 ep65 ep93 ep94 ep67 ep93 933164 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2356222848) qz21 0 2 ep92 ep65 ep93 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2356222848) qz285 0 2 ep94 ep67 ep93 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz292 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 174095929) qz17)

noncomputable abbrev qz293 := (BSN.isNear_log_sfrac 4 1 726817 524288 1 141176 Bool.false (BSN.logfrac_isNear 8 2 1 4 1 726817 524288 141176 rfl rfl rfl (ep91 rfl)))

noncomputable def ep96 := @Enclosure.Real.IsNear.cos_image qz27 qz292 Bool.false 174095929 1048576 891 1048576 Bool.true 933164 1048576 1 141176 (@Enclosure.Real.IsNear.recentre' qz27 Bool.false 43523982411 262144000 59883 70588000 174095929 1048576 891 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz13 qz291 119766 1000 0 1 726817 524288 1 141176 43523982411 262144000 59883 70588000 qz19 qz293 rfl) rfl) (Enclosure.sfrac_false_div 174095929 1048576) (BSN.cos_reduce1 qz292 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 165804442837379541106688) qz20) 226375608064910080 72057594037927936 Bool.false 933164 1048576 26 1000000000000000 282352 141176 (BSN.sin_reduce_arg_pos_rat_q1 174095929 1048576 226375608064910080 72057594037927936 26 165804442837379541106688 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 933164 1048576 165804442837379541106688 151115727451828646838272 2356222848 2147483648 282628 282352 (ep95 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep97 := nat_lit 1102220998086067565545172449602351347356642423773999097411742373786587743911936

noncomputable def ep98 := nat_lit 3304762962327625142356809982786728417804196309111497837828597888904560793092096

noncomputable def ep99 := BSN.cos_dyadic_bound_f 2356222848 2147483648 3 2 1048576 282628 ep97 ep58 ep93 ep98 ep61 ep93 478243 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2356222848) qz16 0 2 ep97 ep58 ep93 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2356222848) qz282 0 2 ep98 ep61 ep93 rfl rfl rfl rfl) rfl rfl

noncomputable def ep100 := @Enclosure.Real.IsNear.sin_image qz27 qz292 Bool.false 174095929 1048576 891 1048576 Bool.false 478243 1048576 1 141176 (@Enclosure.Real.IsNear.recentre' qz27 Bool.false 43523982411 262144000 59883 70588000 174095929 1048576 891 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz13 qz291 119766 1000 0 1 726817 524288 1 141176 43523982411 262144000 59883 70588000 qz19 qz293 rfl) rfl) (Enclosure.sfrac_false_div 174095929 1048576) (BSN.sin_reduce1 qz292 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 165804442837379541106688) qz20) 226375608064910080 72057594037927936 Bool.false 478243 1048576 26 1000000000000000 282352 141176 (BSN.sin_reduce_arg_pos_rat_q1 174095929 1048576 226375608064910080 72057594037927936 26 165804442837379541106688 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 478243 1048576 165804442837379541106688 151115727451828646838272 2356222848 2147483648 282628 282352 (ep99 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz294 := (@Enclosure.Real.IsNear.recentre' qz26 Bool.false 524287 1048576 1 1048576 524287 1048576 1 1048576 (ep87 rfl rfl) rfl)

noncomputable def ep101 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz26 (Real.cos qz27)) (@HMul.hMul Real Real Real qz0 qz26 (@Neg.neg Real Real.instNeg (Real.sin qz27))) Bool.true 122311438517 274877906944 2082204332805 4850770423840768 Bool.true 250736587741 1099511627776 8320789340333 19403081695363072 (@Enclosure.Real.IsNear.mulLit_ft qz26 (Real.cos qz27) 524287 1048576 1 1048576 233291 262144 15854549 18504220672 122311438517 274877906944 2082204332805 4850770423840768 qz294 (@Enclosure.Real.IsNear.recentre' (Real.cos qz27) Bool.true 933164 1048576 126836392 148033765376 233291 262144 15854549 18504220672 (ep96 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz26 (@Neg.neg Real Real.instNeg (Real.sin qz27)) 524287 1048576 1 1048576 478243 1048576 15854549 18504220672 250736587741 1099511627776 8320789340333 19403081695363072 qz294 (@Enclosure.Real.IsNear.neg (Real.sin qz27) Bool.false 478243 1048576 15854549 18504220672 (@Enclosure.Real.IsNear.recentre' (Real.sin qz27) Bool.false 478243 1048576 126836392 148033765376 478243 1048576 15854549 18504220672 (ep100 rfl rfl) rfl)) rfl)

noncomputable def ep102 := @ep48 122311438517 274877906944 2082204332805 4850770423840768 Bool.true 250736587741 1099511627776 8320789340333 19403081695363072 Bool.false 190278369073948541321216 692228674139 549755813888 14840185872347 9701540847681536 Bool.true 853895822517826639364096 388306863223 549755813888 7418860160871 4850770423840768 (ep49 (BSN.head_sum_c_succ qz5 3 4 rfl rfl) (ep85 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep86 ep101) rfl rfl

noncomputable abbrev qz549 := (@Nat.cast Real Real.instNatCast 5)

noncomputable abbrev qz28 := (@Inv.inv Real Real.instInv (Real.sqrt qz549))

noncomputable abbrev qz295 := (Real.log (Enclosure.sfrac Bool.false 5 1))

noncomputable abbrev qz29 := (@HMul.hMul Real Real Real qz268 qz279 qz295)

noncomputable def ep103 := @Enclosure.Complex.IsNear.of_eq qz541 (Complex.mk (@HMul.hMul Real Real Real qz0 qz28 (Real.cos qz29)) (@HMul.hMul Real Real Real qz0 qz28 (@Neg.neg Real Real.instNeg (Real.sin qz29)))) Bool.true 214867402337 1099511627776 7442886372009 19403081695363072 Bool.false 221142717271 549755813888 1862861137341 4850770423840768 (BSN.cpow_neg_s_mk qz13 119766 1000 5 qz14 rfl)

noncomputable def ep104 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz549) 2344687 1048576 1 1048576 234468 234469 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz549) (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz549 qz15)) Bool.false 2344687 1048576 1 1048576 (BSN.sqrt_natCast_div_one 5) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz549 qz15)) Bool.false 2344687 1048576 1 1048576 2344687 1048576 1 1048576 (BSN.sqrt_enclosure 5 1 1172343 1172344 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep105 := nat_lit 11734546589655452485523914939250625

noncomputable def ep106 := nat_lit 2429970938528035899633153341031900

noncomputable def ep107 := nat_lit 824199001261152424427520000

noncomputable def ep108 := BSN.log_dyadic_bound 2 3 17 16 ep105 524288 141176 ep106 ep107 843808 5 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base16 (BSN.artanhP 2) (BSN.artanhQ 3) 0 16 ep106 ep105 ep107 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep109 := nat_lit 1190680606580739054926145945791735995372462403350106455055575618968423896252416

noncomputable def ep110 := nat_lit 1108470342438664503413390912507253051179981813953153517961948627059972571136

noncomputable def ep111 := nat_lit 3569824879057339835771611055550193480015027246422413058130802959651151743614976

noncomputable def ep112 := BSN.cos_dyadic_bound_f 2402096828 2147483648 3 2 1048576 282628 ep109 ep58 ep110 ep111 ep61 ep110 458201 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2402096828) qz16 0 2 ep109 ep58 ep110 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2402096828) qz282 0 2 ep111 ep61 ep110 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz296 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 202119017) qz17)

noncomputable abbrev qz297 := (BSN.isNear_log_sfrac 5 1 843808 524288 1 141176 Bool.false (BSN.logfrac_isNear 5 1 2 5 1 843808 524288 141176 rfl rfl rfl (ep108 rfl)))

noncomputable def ep113 := @Enclosure.Real.IsNear.cos_image qz29 qz296 Bool.false 202119017 1048576 891 1048576 Bool.true 458201 1048576 1 141176 (@Enclosure.Real.IsNear.recentre' qz29 Bool.false 1579054827 8192000 59883 70588000 202119017 1048576 891 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz13 qz295 119766 1000 0 1 843808 524288 1 141176 1579054827 8192000 59883 70588000 qz19 qz297 rfl) rfl) (Enclosure.sfrac_false_div 202119017 1048576) (BSN.cos_reduce2 qz296 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 169032537185029732696064) qz20) 226375608064910080 72057594037927936 Bool.false 458201 1048576 30 1000000000000000 282352 141176 (BSN.sin_reduce_arg_pos_rat_q2 202119017 1048576 226375608064910080 72057594037927936 30 169032537185029732696064 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 458201 1048576 169032537185029732696064 151115727451828646838272 2402096828 2147483648 282628 282352 (ep112 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep114 := nat_lit 2142338315571379367264331989695118989229488340579029096285666555241515035197440

noncomputable def ep115 := nat_lit 5609091398322997647924866863914585609708654254770104432195283537379204184211456

noncomputable def ep116 := BSN.sin_dyadic_bound_f 2402096828 2147483648 3 2 1048576 282628 ep114 ep65 ep110 ep115 ep67 ep110 943166 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2402096828) qz21 0 2 ep114 ep65 ep110 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2402096828) qz285 0 2 ep115 ep67 ep110 rfl rfl rfl rfl) rfl rfl

noncomputable def ep117 := @Enclosure.Real.IsNear.sin_image qz29 qz296 Bool.false 202119017 1048576 891 1048576 Bool.true 943166 1048576 1 141176 (@Enclosure.Real.IsNear.recentre' qz29 Bool.false 1579054827 8192000 59883 70588000 202119017 1048576 891 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz13 qz295 119766 1000 0 1 843808 524288 1 141176 1579054827 8192000 59883 70588000 qz19 qz297 rfl) rfl) (Enclosure.sfrac_false_div 202119017 1048576) (BSN.sin_reduce2 qz296 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 169032537185029732696064) qz20) 226375608064910080 72057594037927936 Bool.false 943166 1048576 30 1000000000000000 282352 141176 (BSN.sin_reduce_arg_pos_rat_q2 202119017 1048576 226375608064910080 72057594037927936 30 169032537185029732696064 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 943166 1048576 169032537185029732696064 151115727451828646838272 2402096828 2147483648 282628 282352 (ep116 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz298 := (@Enclosure.Real.IsNear.recentre' qz28 Bool.false 468937 1048576 1 1048576 468937 1048576 1 1048576 (ep104 rfl rfl) rfl)

noncomputable def ep118 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz28 (Real.cos qz29)) (@HMul.hMul Real Real Real qz0 qz28 (@Neg.neg Real Real.instNeg (Real.sin qz29))) Bool.true 214867402337 1099511627776 7442886372009 19403081695363072 Bool.false 221142717271 549755813888 1862861137341 4850770423840768 (@Enclosure.Real.IsNear.mulLit_ft qz28 (Real.cos qz29) 468937 1048576 1 1048576 458201 1048576 15854549 18504220672 214867402337 1099511627776 7442886372009 19403081695363072 qz298 (@Enclosure.Real.IsNear.recentre' (Real.cos qz29) Bool.true 458201 1048576 126836392 148033765376 458201 1048576 15854549 18504220672 (ep113 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz28 (@Neg.neg Real Real.instNeg (Real.sin qz29)) 468937 1048576 1 1048576 471583 524288 15854549 18504220672 221142717271 549755813888 1862861137341 4850770423840768 qz298 (@Enclosure.Real.IsNear.neg (Real.sin qz29) Bool.true 471583 524288 15854549 18504220672 (@Enclosure.Real.IsNear.recentre' (Real.sin qz29) Bool.true 943166 1048576 126836392 148033765376 471583 524288 15854549 18504220672 (ep117 rfl rfl) rfl)) rfl)

noncomputable def ep119 := @ep46 214867402337 1099511627776 7442886372009 19403081695363072 Bool.false 221142717271 549755813888 1862861137341 4850770423840768 Bool.false 642988872646016377028608 1169589945941 1099511627776 37123258116703 19403081695363072 Bool.true 91899461110734180581376 5223879561 17179869184 2320430324553 1212692605960192 (ep47 (BSN.head_sum_c_succ qz5 4 5 rfl rfl) (ep102 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep103 ep118) rfl rfl

noncomputable abbrev qz30 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 6)))

noncomputable abbrev qz550 := (Real.log (Enclosure.sfrac Bool.false 6 1))

noncomputable abbrev qz31 := (@HMul.hMul Real Real Real qz268 qz279 qz550)

noncomputable def ep120 := @Enclosure.Complex.IsNear.of_eq qz540 (Complex.mk (@HMul.hMul Real Real Real qz0 qz30 (Real.cos qz31)) (@HMul.hMul Real Real Real qz0 qz30 (@Neg.neg Real Real.instNeg (Real.sin qz31)))) Bool.false 128083377195 549755813888 3398787738595 9701540847681536 Bool.true 368599563345 1099511627776 6802210373505 19403081695363072 (BSN.cpow_neg_s_mk qz13 119766 1000 6 qz14 rfl)

noncomputable abbrev qz299 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 6) qz15)

noncomputable def ep121 := @Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 6)) 2568477 1048576 1 1048576 214039 214040 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 6)) (Real.sqrt qz299) Bool.false 2568477 1048576 1 1048576 (BSN.sqrt_natCast_div_one 6) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz299) Bool.false 2568477 1048576 1 1048576 2568477 1048576 1 1048576 (BSN.sqrt_enclosure 6 1 1284238 1284239 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep122 := BSN.log_dyadic_bound 2 10 4 3 105000000 524288 141176 1434560 960 212580 12 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 2) (BSN.artanhQ 10) 0 3 1434560 105000000 960 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep123 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz550 119766 1000 0 1 4034681531866359 2251799813685248 62500000017647 8823500000000000000 241608834172753175997 1125899906842624000 3742687501056755301 4411750000000000000000 qz19 (BSN.isNear_log_sfrac 6 1 4034681531866359 2251799813685248 62500000017647 8823500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz299) Bool.false 33845361775666394038272 18889465931478580854784 1000000000282352 141176000000000000000 4034681531866359 2251799813685248 62500000017647 8823500000000000000 (BSN.log_rat_reduce_isNear 6 1 2 12 8 212580 524288 24973259072661432 36028797018963968 141176 1000000000000000 rfl rfl rfl rfl (ep122 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep124 := nat_lit 655074224291249160528785473383563131295065394508426576625294699317534668390656

noncomputable def ep125 := nat_lit 335798051853093622575080103834042912055716171073515135725826258122711531776

noncomputable def ep126 := nat_lit 1964551076770041294341206259943021308061084751183132699604432445436358582108416

noncomputable def ep127 := BSN.cos_dyadic_bound_f 2068996574 2147483648 3 2 1048576 282628 ep124 ep58 ep125 ep126 ep61 ep125 598410 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2068996574) qz16 0 2 ep124 ep58 ep125 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2068996574) qz282 0 2 ep126 ep61 ep125 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz300 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 225015761) qz17)

noncomputable def ep128 := @Enclosure.Real.IsNear.cos_image qz31 qz300 Bool.false 225015761 1048576 891 1048576 Bool.false 598410 1048576 1 141176 (@Enclosure.Real.IsNear.recentre' qz31 Bool.false 241608834172753175997 1125899906842624000 3742687501056755301 4411750000000000000000 225015761 1048576 891 1048576 (ep123 rfl) rfl) (Enclosure.sfrac_false_div 225015761 1048576) (BSN.cos_reduce0 qz300 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 145592690637958086131712) qz20) 226375608064910080 72057594037927936 Bool.false 598410 1048576 34 1000000000000000 282352 141176 (BSN.sin_reduce_arg_pos_rat_q0 225015761 1048576 226375608064910080 72057594037927936 34 145592690637958086131712 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 598410 1048576 145592690637958086131712 151115727451828646838272 2068996574 2147483648 282628 282352 (ep127 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep129 := nat_lit 1178864965282766014053753788007346402001473137178309025816949797765064233877760

noncomputable def ep130 := nat_lit 3086959807466148837608995505565414031003387056904309376443693370681064793866496

noncomputable def ep131 := BSN.sin_dyadic_bound_f 2068996574 2147483648 3 2 1048576 282628 ep129 ep65 ep125 ep130 ep67 ep125 861055 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2068996574) qz21 0 2 ep129 ep65 ep125 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2068996574) qz285 0 2 ep130 ep67 ep125 rfl rfl rfl rfl) rfl rfl

noncomputable def ep132 := @Enclosure.Real.IsNear.sin_image qz31 qz300 Bool.false 225015761 1048576 891 1048576 Bool.false 861055 1048576 1 141176 (@Enclosure.Real.IsNear.recentre' qz31 Bool.false 241608834172753175997 1125899906842624000 3742687501056755301 4411750000000000000000 225015761 1048576 891 1048576 (ep123 rfl) rfl) (Enclosure.sfrac_false_div 225015761 1048576) (BSN.sin_reduce0 qz300 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 145592690637958086131712) qz20) 226375608064910080 72057594037927936 Bool.false 861055 1048576 34 1000000000000000 282352 141176 (BSN.sin_reduce_arg_pos_rat_q0 225015761 1048576 226375608064910080 72057594037927936 34 145592690637958086131712 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 861055 1048576 145592690637958086131712 151115727451828646838272 2068996574 2147483648 282628 282352 (ep131 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz301 := (@Enclosure.Real.IsNear.recentre' qz30 Bool.false 428079 1048576 1 1048576 428079 1048576 1 1048576 (ep121 rfl rfl) rfl)

noncomputable def ep133 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz30 (Real.cos qz31)) (@HMul.hMul Real Real Real qz0 qz30 (@Neg.neg Real Real.instNeg (Real.sin qz31))) Bool.false 128083377195 549755813888 3398787738595 9701540847681536 Bool.true 368599563345 1099511627776 6802210373505 19403081695363072 (@Enclosure.Real.IsNear.mulLit_ff qz30 (Real.cos qz31) 428079 1048576 1 1048576 299205 524288 15854549 18504220672 128083377195 549755813888 3398787738595 9701540847681536 qz301 (@Enclosure.Real.IsNear.recentre' (Real.cos qz31) Bool.false 598410 1048576 126836392 148033765376 299205 524288 15854549 18504220672 (ep128 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz30 (@Neg.neg Real Real.instNeg (Real.sin qz31)) 428079 1048576 1 1048576 861055 1048576 15854549 18504220672 368599563345 1099511627776 6802210373505 19403081695363072 qz301 (@Enclosure.Real.IsNear.neg (Real.sin qz31) Bool.false 861055 1048576 15854549 18504220672 (@Enclosure.Real.IsNear.recentre' (Real.sin qz31) Bool.false 861055 1048576 126836392 148033765376 861055 1048576 15854549 18504220672 (ep132 rfl rfl) rfl)) rfl)

noncomputable def ep134 := @ep44 128083377195 549755813888 3398787738595 9701540847681536 Bool.true 368599563345 1099511627776 6802210373505 19403081695363072 Bool.false 783818035196738223996928 1425756700331 1099511627776 43920833593893 19403081695363072 Bool.true 12076208598967507746816 702927855249 1099511627776 43929095566353 19403081695363072 (ep45 (BSN.head_sum_c_succ qz5 5 6 rfl rfl) (ep119 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep120 ep133) rfl rfl

noncomputable abbrev qz32 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 7)))

noncomputable abbrev qz551 := (Real.log (Enclosure.sfrac Bool.false 7 1))

noncomputable abbrev qz33 := (@HMul.hMul Real Real Real qz268 qz279 qz551)

noncomputable def ep135 := @Enclosure.Complex.IsNear.of_eq qz539 (Complex.mk (@HMul.hMul Real Real Real qz0 qz32 (Real.cos qz33)) (@HMul.hMul Real Real Real qz0 qz32 (@Neg.neg Real Real.instNeg (Real.sin qz33)))) Bool.false 348561892625 1099511627776 898870899121 2771868813623296 Bool.true 113146427925 549755813888 449046576487 1385934406811648 (BSN.cpow_neg_s_mk qz13 119766 1000 7 qz14 rfl)

noncomputable abbrev qz302 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 7) qz15)

noncomputable def ep136 := @Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 7)) 2774271 1048576 1 1048576 198162 198163 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 7)) (Real.sqrt qz302) Bool.false 2774271 1048576 1 1048576 (BSN.sqrt_natCast_div_one 7) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz302) Bool.false 2774271 1048576 1 1048576 2774271 1048576 1 1048576 (BSN.sqrt_enclosure 7 1 1387135 1387136 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep137 := BSN.log_dyadic_bound 3 11 5 4 202569142545 524288 141176 5259111624 688905 293399 14 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 3) (BSN.artanhQ 11) 0 4 5259111624 202569142545 688905 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep138 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz551 119766 1000 0 1 4381796493761783 2251799813685248 62500000017647 8823500000000000000 262395119435936851389 1125899906842624000 3742687501056755301 4411750000000000000000 qz19 (BSN.isNear_log_sfrac 7 1 4381796493761783 2251799813685248 62500000017647 8823500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz302) Bool.false 36757173121942042968064 18889465931478580854784 1000000000282352 141176000000000000000 4381796493761783 2251799813685248 62500000017647 8823500000000000000 (BSN.log_rat_reduce_isNear 7 1 2 14 8 293399 524288 24973259072661432 36028797018963968 141176 1000000000000000 rfl rfl rfl rfl (ep137 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep139 := nat_lit 2338214920682833972996521559432642816

noncomputable def ep140 := nat_lit 510423550381407695195061911147652317184

noncomputable def ep141 := nat_lit 7656353255721115427925928667214784757760

noncomputable def ep142 := BSN.cos_dyadic_bound_f 1236576836 2147483648 2 1 1048576 282628 ep139 ep140 ep139 ep139 ep141 ep139 879485 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1236576836) qz16 0 1 ep139 ep140 ep139 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1236576836) qz282 0 1 ep139 ep141 ep139 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz34 := (@Nat.cast Real Real.instNatCast 524288)

noncomputable abbrev qz35 := (@Nat.cast Real Real.instNatCast 75557863725914323419136)

noncomputable abbrev qz303 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 122187249) qz34)

noncomputable def ep143 := @Enclosure.Real.IsNear.cos_image qz33 qz303 Bool.false 122187249 524288 445 524288 Bool.false 879485 1048576 1 141176 (@Enclosure.Real.IsNear.recentre' qz33 Bool.false 262395119435936851389 1125899906842624000 3742687501056755301 4411750000000000000000 122187249 524288 445 524288 (ep138 rfl) rfl) (Enclosure.sfrac_false_div 122187249 524288) (BSN.cos_reduce0 qz303 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 43508179538367068766208) qz35) 226375608064910080 72057594037927936 Bool.false 879485 1048576 37 1000000000000000 282352 141176 (BSN.sin_reduce_arg_pos_rat_q0 122187249 524288 226375608064910080 72057594037927936 37 43508179538367068766208 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 879485 1048576 43508179538367068766208 75557863725914323419136 1236576836 2147483648 282628 282352 (ep142 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep144 := nat_lit 2552117751907038475975309555738261585920

noncomputable def ep145 := nat_lit 17864824263349269331827166890167831101440

noncomputable def ep146 := BSN.sin_dyadic_bound_f 1236576836 2147483648 2 1 1048576 282628 ep139 ep144 ep139 ep139 ep145 ep139 570978 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1236576836) qz21 0 1 ep139 ep144 ep139 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1236576836) qz285 0 1 ep139 ep145 ep139 rfl rfl rfl rfl) rfl rfl

noncomputable def ep147 := @Enclosure.Real.IsNear.sin_image qz33 qz303 Bool.false 122187249 524288 445 524288 Bool.false 570978 1048576 1 141176 (@Enclosure.Real.IsNear.recentre' qz33 Bool.false 262395119435936851389 1125899906842624000 3742687501056755301 4411750000000000000000 122187249 524288 445 524288 (ep138 rfl) rfl) (Enclosure.sfrac_false_div 122187249 524288) (BSN.sin_reduce0 qz303 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 43508179538367068766208) qz35) 226375608064910080 72057594037927936 Bool.false 570978 1048576 37 1000000000000000 282352 141176 (BSN.sin_reduce_arg_pos_rat_q0 122187249 524288 226375608064910080 72057594037927936 37 43508179538367068766208 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 570978 1048576 43508179538367068766208 75557863725914323419136 1236576836 2147483648 282628 282352 (ep146 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz304 := (@Enclosure.Real.IsNear.recentre' qz32 Bool.false 396325 1048576 1 1048576 396325 1048576 1 1048576 (ep136 rfl rfl) rfl)

noncomputable def ep148 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz32 (Real.cos qz33)) (@HMul.hMul Real Real Real qz0 qz32 (@Neg.neg Real Real.instNeg (Real.sin qz33))) Bool.false 348561892625 1099511627776 898870899121 2771868813623296 Bool.true 113146427925 549755813888 449046576487 1385934406811648 (@Enclosure.Real.IsNear.mulLit_ff qz32 (Real.cos qz33) 396325 1048576 1 1048576 879485 1048576 7918451 9252110336 348561892625 1099511627776 898870899121 2771868813623296 qz304 (@Enclosure.Real.IsNear.recentre' (Real.cos qz33) Bool.false 879485 1048576 63347608 74016882688 879485 1048576 7918451 9252110336 (ep143 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz32 (@Neg.neg Real Real.instNeg (Real.sin qz33)) 396325 1048576 1 1048576 285489 524288 7918451 9252110336 113146427925 549755813888 449046576487 1385934406811648 qz304 (@Enclosure.Real.IsNear.neg (Real.sin qz33) Bool.false 285489 524288 7918451 9252110336 (@Enclosure.Real.IsNear.recentre' (Real.sin qz33) Bool.false 570978 1048576 63347608 74016882688 285489 524288 7918451 9252110336 (ep147 rfl rfl) rfl)) rfl)

noncomputable def ep149 := @ep41 348561892625 1099511627776 898870899121 2771868813623296 Bool.true 113146427925 549755813888 449046576487 1385934406811648 Bool.false ep42 443579648239 274877906944 12553232471935 4850770423840768 Bool.true 510844488311816859942912 929220711099 1099511627776 50215747637171 19403081695363072 (ep43 (BSN.head_sum_c_succ qz5 6 7 rfl rfl) (ep134 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep135 ep148) rfl rfl

noncomputable abbrev qz36 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 8)))

noncomputable abbrev qz552 := (Real.log (Enclosure.sfrac Bool.false 8 1))

noncomputable abbrev qz37 := (@HMul.hMul Real Real Real qz268 qz279 qz552)

noncomputable def ep150 := @Enclosure.Complex.IsNear.of_eq qz538 (Complex.mk (@HMul.hMul Real Real Real qz0 qz36 (Real.cos qz37)) (@HMul.hMul Real Real Real qz0 qz36 (@Neg.neg Real Real.instNeg (Real.sin qz37)))) Bool.true 31681958693 137438953472 735405970555 2425385211920384 Bool.false 36843219987 137438953472 735651652089 2425385211920384 (BSN.cpow_neg_s_mk qz13 119766 1000 8 qz14 rfl)

noncomputable abbrev qz305 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 8) qz15)

noncomputable def ep151 := @Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 8)) 2965821 1048576 1 1048576 185363 185364 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 8)) (Real.sqrt qz305) Bool.false 2965821 1048576 1 1048576 (BSN.sqrt_natCast_div_one 8) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz305) Bool.false 2965821 1048576 1 1048576 2965821 1048576 1 1048576 (BSN.sqrt_enclosure 8 1 1482910 1482911 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep152 := BSN.log_dyadic_bound 0 16 1 0 1 524288 141176 0 1 0 16 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 0) (BSN.artanhQ 16) 0 0 rfl) rfl rfl rfl

noncomputable def ep153 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz552 119766 1000 0 1 9364972152248037 4503599627370496 125000000052941 17647000000000000000 560802627393069199671 2251799813685248000 7485375003170265903 8823500000000000000000 qz19 (BSN.isNear_log_sfrac 8 1 9364972152248037 4503599627370496 125000000052941 17647000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz305) Bool.false 39279540158062550581248 18889465931478580854784 1000000000423528 141176000000000000000 9364972152248037 4503599627370496 125000000052941 17647000000000000000 (BSN.log_rat_reduce_isNear 8 1 3 16 16 0 524288 24973259072661432 36028797018963968 141176 1000000000000000 rfl rfl rfl rfl (ep152 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep154 := nat_lit 416913750606024052842951795650346173121376843219825943578505263742527462890625

noncomputable def ep155 := nat_lit 136066566499118832107123614008580066054790254827053299435476123199462890625

noncomputable def ep156 := nat_lit 1250469118685073920864641139723021359232020949149823724136644838981183462890625

noncomputable def ep157 := BSN.cos_dyadic_bound_f 1848072175 2147483648 3 2 1048576 282628 ep154 ep58 ep155 ep156 ep61 ep155 683672 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1848072175) qz16 0 2 ep154 ep58 ep155 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1848072175) qz282 0 2 ep156 ep61 ep155 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz306 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 261144073) qz17)

noncomputable def ep158 := @Enclosure.Real.IsNear.cos_image qz37 qz306 Bool.false 261144073 1048576 445 524288 Bool.true 683672 1048576 1 141176 (@Enclosure.Real.IsNear.recentre' qz37 Bool.false 560802627393069199671 2251799813685248000 7485375003170265903 8823500000000000000000 261144073 1048576 445 524288 (ep153 rfl) rfl) (Enclosure.sfrac_false_div 261144073 1048576) (BSN.cos_reduce2 qz306 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 130046518131193351766016) qz20) 226375608064910080 72057594037927936 Bool.false 683672 1048576 39 1000000000000000 282352 141176 (BSN.sin_reduce_arg_pos_rat_q2 261144073 1048576 226375608064910080 72057594037927936 39 130046518131193351766016 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 683672 1048576 130046518131193351766016 151115727451828646838272 1848072175 2147483648 282628 282352 (ep157 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep159 := nat_lit 11664757455648995709516980204437890625

noncomputable def ep160 := BSN.sin_dyadic_bound_f 1848072175 2147483648 2 1 1048576 282628 ep159 ep144 ep159 ep159 ep145 ep159 795048 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1848072175) qz21 0 1 ep159 ep144 ep159 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1848072175) qz285 0 1 ep159 ep145 ep159 rfl rfl rfl rfl) rfl rfl

noncomputable def ep161 := @Enclosure.Real.IsNear.sin_image qz37 qz306 Bool.false 261144073 1048576 445 524288 Bool.true 795048 1048576 1 141176 (@Enclosure.Real.IsNear.recentre' qz37 Bool.false 560802627393069199671 2251799813685248000 7485375003170265903 8823500000000000000000 261144073 1048576 445 524288 (ep153 rfl) rfl) (Enclosure.sfrac_false_div 261144073 1048576) (BSN.sin_reduce2 qz306 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 130046518131193351766016) qz20) 226375608064910080 72057594037927936 Bool.false 795048 1048576 39 1000000000000000 282352 141176 (BSN.sin_reduce_arg_pos_rat_q2 261144073 1048576 226375608064910080 72057594037927936 39 130046518131193351766016 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 795048 1048576 130046518131193351766016 151115727451828646838272 1848072175 2147483648 282628 282352 (ep160 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz307 := (@Enclosure.Real.IsNear.recentre' qz36 Bool.false 370727 1048576 1 1048576 370727 1048576 1 1048576 (ep151 rfl rfl) rfl)

noncomputable def ep162 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz36 (Real.cos qz37)) (@HMul.hMul Real Real Real qz0 qz36 (@Neg.neg Real Real.instNeg (Real.sin qz37))) Bool.true 31681958693 137438953472 735405970555 2425385211920384 Bool.false 36843219987 137438953472 735651652089 2425385211920384 (@Enclosure.Real.IsNear.mulLit_ft qz36 (Real.cos qz37) 370727 1048576 1 1048576 85459 131072 7918451 9252110336 31681958693 137438953472 735405970555 2425385211920384 qz307 (@Enclosure.Real.IsNear.recentre' (Real.cos qz37) Bool.true 683672 1048576 63347608 74016882688 85459 131072 7918451 9252110336 (ep158 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz36 (@Neg.neg Real Real.instNeg (Real.sin qz37)) 370727 1048576 1 1048576 99381 131072 7918451 9252110336 36843219987 137438953472 735651652089 2425385211920384 qz307 (@Enclosure.Real.IsNear.neg (Real.sin qz37) Bool.true 99381 131072 7918451 9252110336 (@Enclosure.Real.IsNear.recentre' (Real.sin qz37) Bool.true 795048 1048576 63347608 74016882688 99381 131072 7918451 9252110336 (ep161 rfl rfl) rfl)) rfl)

noncomputable def ep163 := @ep39 31681958693 137438953472 735405970555 2425385211920384 Bool.false 36843219987 137438953472 735651652089 2425385211920384 Bool.false 52256452142027941871616 380215730853 274877906944 14024044413045 4850770423840768 Bool.true 87201573297538587426816 634474951203 1099511627776 56100960853883 19403081695363072 (ep40 (BSN.head_sum_c_succ qz5 7 8 rfl rfl) (ep149 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep150 ep162) rfl rfl

theorem EMRow39.d6 : Enclosure.Complex.IsNear qz3 Bool.false 380215730853 274877906944 14024044413045 4850770423840768 Bool.true 634474951203 1099511627776 56100960853883 19403081695363072 := ep38 (BSN.head_sum_c_succ qz5 8 9 rfl rfl) (ep163 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable abbrev qz38 := (BSN.headSumC qz272 17)

noncomputable abbrev qz308 := (@Nat.cast Complex Complex.instNatCast 16)

noncomputable def ep164 := @Enclosure.Complex.IsNear.of_eq qz38 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 16) (@HPow.hPow Complex Complex Complex qz6 qz308 qz7)) Bool.false 925937518169 549755813888 47144737231043 9701540847681536 Bool.false 247731199751 1099511627776 94316861388443 19403081695363072

noncomputable def ep165 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 16) (@HPow.hPow Complex Complex Complex qz6 qz308 qz7) Bool.false 1691305370977 1099511627776 90122490305061 19403081695363072 Bool.false 6157354721 274877906944 11268208460093 2425385211920384 Bool.false

noncomputable def ep166 := nat_lit 2036158135641733530124288

noncomputable abbrev qz309 := (@Nat.cast Complex Complex.instNatCast 15)

noncomputable def ep167 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 16) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 15) (@HPow.hPow Complex Complex Complex qz6 qz309 qz7)) Bool.false 1691305370977 1099511627776 90122490305061 19403081695363072 Bool.false 6157354721 274877906944 11268208460093 2425385211920384

noncomputable def ep168 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 15) (@HPow.hPow Complex Complex Complex qz6 qz309 qz7) Bool.false 1899398528023 1099511627776 85821212193695 19403081695363072 Bool.true 84241007093 549755813888 42922683041885 9701540847681536 Bool.true

noncomputable abbrev qz310 := (@Nat.cast Complex Complex.instNatCast 14)

noncomputable def ep169 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 15) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 14) (@HPow.hPow Complex Complex Complex qz6 qz310 qz7)) Bool.false 1899398528023 1099511627776 85821212193695 19403081695363072 Bool.true 84241007093 549755813888 42922683041885 9701540847681536

noncomputable def ep170 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 14) (@HPow.hPow Complex Complex Complex qz6 qz310 qz7) Bool.false 1997142242049 1099511627776 81371915007785 19403081695363072 Bool.false 108641600981 1099511627776 81384773282571 19403081695363072 Bool.true

noncomputable abbrev qz311 := (@Nat.cast Complex Complex.instNatCast 13)

noncomputable def ep171 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 14) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 13) (@HPow.hPow Complex Complex Complex qz6 qz311 qz7)) Bool.false 1997142242049 1099511627776 81371915007785 19403081695363072 Bool.false 108641600981 1099511627776 81384773282571 19403081695363072

noncomputable def ep172 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 13) (@HPow.hPow Complex Complex Complex qz6 qz311 qz7) Bool.false 880257199461 549755813888 38375902678317 9701540847681536 Bool.true 5232286465 68719476736 38383674946527 9701540847681536 Bool.false

noncomputable abbrev qz312 := (@Nat.cast Complex Complex.instNatCast 12)

noncomputable def ep173 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 13) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 12) (@HPow.hPow Complex Complex Complex qz6 qz312 qz7)) Bool.false 880257199461 549755813888 38375902678317 9701540847681536 Bool.true 5232286465 68719476736 38383674946527 9701540847681536

noncomputable def ep174 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 12) (@HPow.hPow Complex Complex Complex qz6 qz312 qz7) Bool.false 1971400069155 1099511627776 10277195801807 2771868813623296 Bool.false 153497066459 1099511627776 10279197178329 2771868813623296 Bool.true

noncomputable def ep175 := nat_lit 1935706052481814439657472

noncomputable abbrev qz313 := (@Nat.cast Complex Complex.instNatCast 11)

noncomputable def ep176 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 12) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 11) (@HPow.hPow Complex Complex Complex qz6 qz313 qz7)) Bool.false 1971400069155 1099511627776 10277195801807 2771868813623296 Bool.false 153497066459 1099511627776 10279197178329 2771868813623296

noncomputable def ep177 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 11) (@HPow.hPow Complex Complex Complex qz6 qz313 qz7) Bool.false 257458611307 137438953472 16730725297759 4850770423840768 Bool.true 41512521263 274877906944 16731000379195 4850770423840768 Bool.true

noncomputable abbrev qz314 := (@Nat.cast Complex Complex.instNatCast 10)

noncomputable def ep178 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 11) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 10) (@HPow.hPow Complex Complex Complex qz6 qz314 qz7)) Bool.false 257458611307 137438953472 16730725297759 4850770423840768 Bool.true 41512521263 274877906944 16731000379195 4850770423840768

noncomputable def ep179 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 10) (@HPow.hPow Complex Complex Complex qz6 qz314 qz7) Bool.false 1791257211037 1099511627776 61651406553389 19403081695363072 Bool.true 193532713789 549755813888 15413757322093 4850770423840768 Bool.false

noncomputable def ep180 := nat_lit 2264629894424864390905856

noncomputable abbrev qz553 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 9) qz7)

noncomputable def ep181 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 10) (@HAdd.hAdd Complex Complex Complex qz4 qz3 qz553) Bool.false 1791257211037 1099511627776 61651406553389 19403081695363072 Bool.true 193532713789 549755813888 15413757322093 4850770423840768

noncomputable def ep182 := @Enclosure.Complex.IsNear.addLitP qz3 qz553 Bool.false 380215730853 274877906944 14024044413045 4850770423840768 Bool.true 634474951203 1099511627776 56100960853883 19403081695363072 Bool.false

noncomputable abbrev qz39 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 9)))

noncomputable abbrev qz554 := (Real.log (Enclosure.sfrac Bool.false 9 1))

noncomputable abbrev qz40 := (@HMul.hMul Real Real Real qz268 qz279 qz554)

noncomputable def ep183 := @Enclosure.Complex.IsNear.of_eq qz553 (Complex.mk (@HMul.hMul Real Real Real qz0 qz39 (Real.cos qz40)) (@HMul.hMul Real Real Real qz0 qz39 (@Neg.neg Real Real.instNeg (Real.sin qz40)))) Bool.false 270394287625 1099511627776 5555228901209 19403081695363072 Bool.false 247409523625 1099511627776 5554068434489 19403081695363072 (BSN.cpow_neg_s_mk qz13 119766 1000 9 qz14 rfl)

noncomputable abbrev qz315 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 9) qz15)

noncomputable def ep184 := @Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 9)) 3145729 1048576 1 1048576 174762 174763 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 9)) (Real.sqrt qz315) Bool.false 3145729 1048576 1 1048576 (BSN.sqrt_natCast_div_one 9) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz315) Bool.false 3145729 1048576 1 1048576 3145729 1048576 1 1048576 (BSN.sqrt_enclosure 9 1 1572864 1572865 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep185 := BSN.log_dyadic_bound 1 17 2 1 867 524288 141176 1 1 61752 18 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 1) (BSN.artanhQ 17) 0 1 1 867 1 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep186 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz554 119766 1000 0 1 9895417793173221 4503599627370496 125000000052941 17647000000000000000 592567303708591993143 2251799813685248000 7485375003170265903 8823500000000000000000 qz19 (BSN.isNear_log_sfrac 9 1 9895417793173221 4503599627370496 125000000052941 17647000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz315) Bool.false 41504390431577613533184 18889465931478580854784 1000000000423528 141176000000000000000 9895417793173221 4503599627370496 125000000052941 17647000000000000000 (BSN.log_rat_reduce_isNear 9 1 3 18 16 61752 524288 24973259072661432 36028797018963968 141176 1000000000000000 rfl rfl rfl rfl (ep185 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep187 := nat_lit 10081535006845056849163792526553760000

noncomputable def ep188 := BSN.sin_dyadic_bound_f 1781893180 2147483648 2 1 1048576 282628 ep187 ep144 ep187 ep187 ep145 ep187 773605 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1781893180) qz21 0 1 ep187 ep144 ep187 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1781893180) qz285 0 1 ep187 ep145 ep187 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz316 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 275935653) qz17)

noncomputable def ep189 := @Enclosure.Real.IsNear.cos_image qz40 qz316 Bool.false 275935653 1048576 891 1048576 Bool.false 773605 1048576 1 141176 (@Enclosure.Real.IsNear.recentre' qz40 Bool.false 592567303708591993143 2251799813685248000 7485375003170265903 8823500000000000000000 275935653 1048576 891 1048576 (ep186 rfl) rfl) (Enclosure.sfrac_false_div 275935653 1048576) (BSN.cos_reduce3 qz316 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 125389585349821182509056) qz20) 226375608064910080 72057594037927936 Bool.false 773605 1048576 41 1000000000000000 282352 141176 (BSN.sin_reduce_arg_pos_rat_q3 275935653 1048576 226375608064910080 72057594037927936 41 125389585349821182509056 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 773605 1048576 125389585349821182509056 151115727451828646838272 1781893180 2147483648 282628 282352 (ep188 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep190 := nat_lit 360311339752275469712827758544587141783259327858388861983585818146484428800000

noncomputable def ep191 := nat_lit 101637348094242360450523793446664468755630486501159344174702170137600000000

noncomputable def ep192 := nat_lit 1080730744560637924417582228046868096412266722602164267262408050099178086400000

noncomputable def ep193 := BSN.cos_dyadic_bound_f 1781893180 2147483648 3 2 1048576 282628 ep190 ep58 ep191 ep192 ep61 ep191 707845 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1781893180) qz16 0 2 ep190 ep58 ep191 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1781893180) qz282 0 2 ep192 ep61 ep191 rfl rfl rfl rfl) rfl rfl

noncomputable def ep194 := @Enclosure.Real.IsNear.sin_image qz40 qz316 Bool.false 275935653 1048576 891 1048576 Bool.true 707845 1048576 1 141176 (@Enclosure.Real.IsNear.recentre' qz40 Bool.false 592567303708591993143 2251799813685248000 7485375003170265903 8823500000000000000000 275935653 1048576 891 1048576 (ep186 rfl) rfl) (Enclosure.sfrac_false_div 275935653 1048576) (BSN.sin_reduce3 qz316 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 125389585349821182509056) qz20) 226375608064910080 72057594037927936 Bool.false 707845 1048576 41 1000000000000000 282352 141176 (BSN.sin_reduce_arg_pos_rat_q3 275935653 1048576 226375608064910080 72057594037927936 41 125389585349821182509056 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 707845 1048576 125389585349821182509056 151115727451828646838272 1781893180 2147483648 282628 282352 (ep193 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz317 := (@Enclosure.Real.IsNear.recentre' qz39 Bool.false 349525 1048576 1 1048576 349525 1048576 1 1048576 (ep184 rfl rfl) rfl)

noncomputable def ep195 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz39 (Real.cos qz40)) (@HMul.hMul Real Real Real qz0 qz39 (@Neg.neg Real Real.instNeg (Real.sin qz40))) Bool.false 270394287625 1099511627776 5555228901209 19403081695363072 Bool.false 247409523625 1099511627776 5554068434489 19403081695363072 (@Enclosure.Real.IsNear.mulLit_ff qz39 (Real.cos qz40) 349525 1048576 1 1048576 773605 1048576 15854549 18504220672 270394287625 1099511627776 5555228901209 19403081695363072 qz317 (@Enclosure.Real.IsNear.recentre' (Real.cos qz40) Bool.false 773605 1048576 126836392 148033765376 773605 1048576 15854549 18504220672 (ep189 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz39 (@Neg.neg Real Real.instNeg (Real.sin qz40)) 349525 1048576 1 1048576 707845 1048576 15854549 18504220672 247409523625 1099511627776 5554068434489 19403081695363072 qz317 (@Enclosure.Real.IsNear.neg (Real.sin qz40) Bool.true 707845 1048576 15854549 18504220672 (@Enclosure.Real.IsNear.recentre' (Real.sin qz40) Bool.true 707845 1048576 126836392 148033765376 707845 1048576 15854549 18504220672 (ep194 rfl rfl) rfl)) rfl)

noncomputable def ep196 := @ep182 270394287625 1099511627776 5555228901209 19403081695363072 Bool.false 247409523625 1099511627776 5554068434489 19403081695363072 Bool.false 492377032968197455740928 1791257211037 1099511627776 61651406553389 19403081695363072 Bool.true 425582938332100221206528 193532713789 549755813888 15413757322093 4850770423840768 EMRow39.d6 (ep183 ep195) rfl rfl

noncomputable abbrev qz318 := (@Nat.cast Real Real.instNatCast 10)

noncomputable abbrev qz41 := (@Inv.inv Real Real.instInv (Real.sqrt qz318))

noncomputable abbrev qz555 := (Real.log (Enclosure.sfrac Bool.false 10 1))

noncomputable abbrev qz42 := (@HMul.hMul Real Real Real qz268 qz279 qz555)

noncomputable def ep197 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz314 qz7) (Complex.mk (@HMul.hMul Real Real Real qz0 qz41 (Real.cos qz42)) (@HMul.hMul Real Real Real qz0 qz41 (@Neg.neg Real Real.instNeg (Real.sin qz42)))) Bool.false 268411679419 1099511627776 753070662521 2771868813623296 Bool.false 110507671263 549755813888 94088789793 346483601702912 (BSN.cpow_neg_s_mk qz13 119766 1000 10 qz14 rfl)

noncomputable abbrev qz319 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 10) qz15)

noncomputable def ep198 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz318) 3315889 1048576 1 1048576 165794 165795 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz318) (Real.sqrt qz319) Bool.false 3315889 1048576 1 1048576 (BSN.sqrt_natCast_div_one 10) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz319) Bool.false 3315889 1048576 1 1048576 3315889 1048576 1 1048576 (BSN.sqrt_enclosure 10 1 1657944 1657945 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep199 := BSN.log_dyadic_bound 2 18 3 2 1574640 524288 141176 6528 48 116991 20 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 2) (BSN.artanhQ 18) 0 2 6528 1574640 48 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep200 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz555 119766 1000 0 1 10369917190100709 4503599627370496 125000000052941 17647000000000000000 620981751094800757047 2251799813685248000 7485375003170265903 8823500000000000000000 qz19 (BSN.isNear_log_sfrac 10 1 10369917190100709 4503599627370496 125000000052941 17647000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz319) Bool.false 43494585150108164161536 18889465931478580854784 1000000000423528 141176000000000000000 10369917190100709 4503599627370496 125000000052941 17647000000000000000 (BSN.log_rat_reduce_isNear 10 1 3 20 16 116991 524288 24973259072661432 36028797018963968 141176 1000000000000000 rfl rfl rfl rfl (ep199 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep201 := nat_lit 827672715026415238147186636261529665622827147264998176617071550871398345430625

noncomputable def ep202 := nat_lit 165554512438440532472212659308876946699911597443613705617609666315250390625

noncomputable def ep203 := nat_lit 2167446213001425291428152845903220466336556957393419849902282693774866213590625

noncomputable def ep204 := BSN.sin_dyadic_bound_f 1893946155 2147483648 3 2 1048576 282628 ep201 ep65 ep202 ep203 ep67 ep202 809471 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1893946155) qz21 0 2 ep201 ep65 ep202 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1893946155) qz285 0 2 ep203 ep67 ep202 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz320 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 289167161) qz17)

noncomputable def ep205 := @Enclosure.Real.IsNear.cos_image qz42 qz320 Bool.false 289167161 1048576 891 1048576 Bool.false 809471 1048576 1 141176 (@Enclosure.Real.IsNear.recentre' qz42 Bool.false 620981751094800757047 2251799813685248000 7485375003170265903 8823500000000000000000 289167161 1048576 891 1048576 (ep200 rfl) rfl) (Enclosure.sfrac_false_div 289167161 1048576) (BSN.cos_reduce3 qz320 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 133274612478843543355392) qz20) 226375608064910080 72057594037927936 Bool.false 809471 1048576 43 1000000000000000 282352 141176 (BSN.sin_reduce_arg_pos_rat_q3 289167161 1048576 226375608064910080 72057594037927936 43 133274612478843543355392 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 809471 1048576 133274612478843543355392 151115727451828646838272 1893946155 2147483648 282628 282352 (ep204 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep206 := nat_lit 459891754797981105873980225771653759544548375857196148656425354780250303190625

noncomputable def ep207 := nat_lit 1379344155369066436556996251996343524740245304376701218558040845008120408790625

noncomputable def ep208 := BSN.cos_dyadic_bound_f 1893946155 2147483648 3 2 1048576 282628 ep206 ep58 ep202 ep207 ep61 ep202 666534 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1893946155) qz16 0 2 ep206 ep58 ep202 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1893946155) qz282 0 2 ep207 ep61 ep202 rfl rfl rfl rfl) rfl rfl

noncomputable def ep209 := @Enclosure.Real.IsNear.sin_image qz42 qz320 Bool.false 289167161 1048576 891 1048576 Bool.true 666534 1048576 1 141176 (@Enclosure.Real.IsNear.recentre' qz42 Bool.false 620981751094800757047 2251799813685248000 7485375003170265903 8823500000000000000000 289167161 1048576 891 1048576 (ep200 rfl) rfl) (Enclosure.sfrac_false_div 289167161 1048576) (BSN.sin_reduce3 qz320 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 133274612478843543355392) qz20) 226375608064910080 72057594037927936 Bool.false 666534 1048576 43 1000000000000000 282352 141176 (BSN.sin_reduce_arg_pos_rat_q3 289167161 1048576 226375608064910080 72057594037927936 43 133274612478843543355392 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 666534 1048576 133274612478843543355392 151115727451828646838272 1893946155 2147483648 282628 282352 (ep208 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz321 := (@Enclosure.Real.IsNear.recentre' qz41 Bool.false 331589 1048576 1 1048576 331589 1048576 1 1048576 (ep198 rfl rfl) rfl)

noncomputable def ep210 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz41 (Real.cos qz42)) (@HMul.hMul Real Real Real qz0 qz41 (@Neg.neg Real Real.instNeg (Real.sin qz42))) Bool.false 268411679419 1099511627776 753070662521 2771868813623296 Bool.false 110507671263 549755813888 94088789793 346483601702912 (@Enclosure.Real.IsNear.mulLit_ff qz41 (Real.cos qz42) 331589 1048576 1 1048576 809471 1048576 15854549 18504220672 268411679419 1099511627776 753070662521 2771868813623296 qz321 (@Enclosure.Real.IsNear.recentre' (Real.cos qz42) Bool.false 809471 1048576 126836392 148033765376 809471 1048576 15854549 18504220672 (ep205 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz41 (@Neg.neg Real Real.instNeg (Real.sin qz42)) 331589 1048576 1 1048576 333267 524288 15854549 18504220672 110507671263 549755813888 94088789793 346483601702912 qz321 (@Enclosure.Real.IsNear.neg (Real.sin qz42) Bool.true 333267 524288 15854549 18504220672 (@Enclosure.Real.IsNear.recentre' (Real.sin qz42) Bool.true 666534 1048576 126836392 148033765376 333267 524288 15854549 18504220672 (ep209 rfl rfl) rfl)) rfl)

noncomputable def ep211 := @ep179 268411679419 1099511627776 753070662521 2771868813623296 Bool.false 110507671263 549755813888 94088789793 346483601702912 Bool.false ep180 257458611307 137438953472 16730725297759 4850770423840768 Bool.true 45643499826966941401088 41512521263 274877906944 16731000379195 4850770423840768 (ep181 (BSN.head_sum_c_succ qz5 9 10 rfl rfl) (ep196 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep197 ep210) rfl rfl

noncomputable abbrev qz322 := (@Nat.cast Real Real.instNatCast 11)

noncomputable abbrev qz43 := (@Inv.inv Real Real.instInv (Real.sqrt qz322))

noncomputable abbrev qz556 := (Real.log (Enclosure.sfrac Bool.false 11 1))

noncomputable abbrev qz44 := (@HMul.hMul Real Real Real qz268 qz279 qz556)

noncomputable def ep212 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz313 qz7) (Complex.mk (@HMul.hMul Real Real Real qz0 qz43 (Real.cos qz44)) (@HMul.hMul Real Real Real qz0 qz43 (@Neg.neg Real Real.instNeg (Real.sin qz44)))) Bool.true 88268821301 1099511627776 5017469421613 19403081695363072 Bool.false 319547151511 1099511627776 5030378731523 19403081695363072 (BSN.cpow_neg_s_mk qz13 119766 1000 11 qz14 rfl)

noncomputable abbrev qz323 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 11) qz15)

noncomputable def ep213 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz322) 3477733 1048576 1 1048576 158078 158079 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz322) (Real.sqrt qz323) Bool.false 3477733 1048576 1 1048576 (BSN.sqrt_natCast_div_one 11) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz323) Bool.false 3477733 1048576 1 1048576 3477733 1048576 1 1048576 (BSN.sqrt_enclosure 11 1 1738866 1738867 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep214 := BSN.log_dyadic_bound 3 19 4 3 4939817505 524288 141176 41676111 10935 166961 22 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 3) (BSN.artanhQ 19) 0 3 41676111 4939817505 10935 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep215 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz556 119766 1000 0 1 10799156221662949 4503599627370496 125000000052941 17647000000000000000 646685872021842374967 2251799813685248000 7485375003170265903 8823500000000000000000 qz19 (BSN.isNear_log_sfrac 11 1 10799156221662949 4503599627370496 125000000052941 17647000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz323) Bool.false 45294944137145793642496 18889465931478580854784 1000000000423528 141176000000000000000 10799156221662949 4503599627370496 125000000052941 17647000000000000000 (BSN.log_rat_reduce_isNear 11 1 3 22 16 166961 524288 24973259072661432 36028797018963968 141176 1000000000000000 rfl rfl rfl rfl (ep214 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep216 := nat_lit 2182627540504812719467968937310080984004157700855317144499687552676957163421696

noncomputable def ep217 := nat_lit 3718951661292584519643014470223645290036933045491049381839002819948634505216

noncomputable def ep218 := nat_lit 6540444718191852989364620782989795661432399236474969334735384652390974221254656

noncomputable def ep219 := BSN.cos_dyadic_bound_f 2794490044 2147483648 3 2 1048576 282628 ep216 ep58 ep217 ep218 ep61 ep217 279193 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2794490044) qz16 0 2 ep216 ep58 ep217 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2794490044) qz282 0 2 ep218 ep61 ep217 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz324 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 301136575) qz17)

noncomputable def ep220 := @Enclosure.Real.IsNear.cos_image qz44 qz324 Bool.false 301136575 1048576 891 1048576 Bool.true 279193 1048576 1 141176 (@Enclosure.Real.IsNear.recentre' qz44 Bool.false 646685872021842374967 2251799813685248000 7485375003170265903 8823500000000000000000 301136575 1048576 891 1048576 (ep215 rfl) rfl) (Enclosure.sfrac_false_div 301136575 1048576) (BSN.cos_reduce2 qz324 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 196644755030727815331840) qz20) 226375608064910080 72057594037927936 Bool.false 279193 1048576 45 1000000000000000 282352 141176 (BSN.sin_reduce_arg_pos_rat_q2 301136575 1048576 226375608064910080 72057594037927936 45 196644755030727815331840 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 279193 1048576 196644755030727815331840 151115727451828646838272 2794490044 2147483648 282628 282352 (ep219 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep221 := nat_lit 3925754411579628827426629675581966854975454315103178020593966392562563986554880

noncomputable def ep222 := nat_lit 10275716584780744649276036650715265384942320552720385497794553595002988842254336

noncomputable def ep223 := BSN.sin_dyadic_bound_f 2794490044 2147483648 3 2 1048576 282628 ep221 ep65 ep217 ep222 ep67 ep217 1010723 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2794490044) qz21 0 2 ep221 ep65 ep217 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2794490044) qz285 0 2 ep222 ep67 ep217 rfl rfl rfl rfl) rfl rfl

noncomputable def ep224 := @Enclosure.Real.IsNear.sin_image qz44 qz324 Bool.false 301136575 1048576 891 1048576 Bool.true 1010723 1048576 1 141176 (@Enclosure.Real.IsNear.recentre' qz44 Bool.false 646685872021842374967 2251799813685248000 7485375003170265903 8823500000000000000000 301136575 1048576 891 1048576 (ep215 rfl) rfl) (Enclosure.sfrac_false_div 301136575 1048576) (BSN.sin_reduce2 qz324 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 196644755030727815331840) qz20) 226375608064910080 72057594037927936 Bool.false 1010723 1048576 45 1000000000000000 282352 141176 (BSN.sin_reduce_arg_pos_rat_q2 301136575 1048576 226375608064910080 72057594037927936 45 196644755030727815331840 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1010723 1048576 196644755030727815331840 151115727451828646838272 2794490044 2147483648 282628 282352 (ep223 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz325 := (@Enclosure.Real.IsNear.recentre' qz43 Bool.false 316157 1048576 1 1048576 316157 1048576 1 1048576 (ep213 rfl rfl) rfl)

noncomputable def ep225 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz43 (Real.cos qz44)) (@HMul.hMul Real Real Real qz0 qz43 (@Neg.neg Real Real.instNeg (Real.sin qz44))) Bool.true 88268821301 1099511627776 5017469421613 19403081695363072 Bool.false 319547151511 1099511627776 5030378731523 19403081695363072 (@Enclosure.Real.IsNear.mulLit_ft qz43 (Real.cos qz44) 316157 1048576 1 1048576 279193 1048576 15854549 18504220672 88268821301 1099511627776 5017469421613 19403081695363072 qz325 (@Enclosure.Real.IsNear.recentre' (Real.cos qz44) Bool.true 279193 1048576 126836392 148033765376 279193 1048576 15854549 18504220672 (ep220 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz43 (@Neg.neg Real Real.instNeg (Real.sin qz44)) 316157 1048576 1 1048576 1010723 1048576 15854549 18504220672 319547151511 1099511627776 5030378731523 19403081695363072 qz325 (@Enclosure.Real.IsNear.neg (Real.sin qz44) Bool.true 1010723 1048576 15854549 18504220672 (@Enclosure.Real.IsNear.recentre' (Real.sin qz44) Bool.true 1010723 1048576 126836392 148033765376 1010723 1048576 15854549 18504220672 (ep224 rfl rfl) rfl)) rfl)

noncomputable def ep226 := @ep177 88268821301 1099511627776 5017469421613 19403081695363072 Bool.false 319547151511 1099511627776 5030378731523 19403081695363072 Bool.false 270947162379291627356160 1971400069155 1099511627776 10277195801807 2771868813623296 Bool.false 42192952350293985591296 153497066459 1099511627776 10279197178329 2771868813623296 (ep178 (BSN.head_sum_c_succ qz5 10 11 rfl rfl) (ep211 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep212 ep225) rfl rfl

noncomputable abbrev qz326 := (@Nat.cast Real Real.instNatCast 12)

noncomputable abbrev qz45 := (@Inv.inv Real Real.instInv (Real.sqrt qz326))

noncomputable abbrev qz557 := (Real.log (Enclosure.sfrac Bool.false 12 1))

noncomputable abbrev qz46 := (@HMul.hMul Real Real Real qz268 qz279 qz557)

noncomputable def ep227 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz312 qz7) (Complex.mk (@HMul.hMul Real Real Real qz0 qz45 (Real.cos qz46)) (@HMul.hMul Real Real Real qz0 qz45 (@Neg.neg Real Real.instNeg (Real.sin qz46)))) Bool.true 210885670233 1099511627776 4811434743985 19403081695363072 Bool.true 237213649899 1099511627776 4812969644751 19403081695363072 (BSN.cpow_neg_s_mk qz13 119766 1000 12 qz14 rfl)

noncomputable abbrev qz327 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 12) qz15)

noncomputable def ep228 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz326) 3632373 1048576 1 1048576 151348 151349 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz326) (Real.sqrt qz327) Bool.false 3632373 1048576 1 1048576 (BSN.sqrt_natCast_div_one 12) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz327) Bool.false 3632373 1048576 1 1048576 3632373 1048576 1 1048576 (BSN.sqrt_enclosure 12 1 1816186 1816187 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep229 := BSN.log_dyadic_bound 4 20 4 3 6720000000 524288 141176 91811840 61440 212580 24 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 4) (BSN.artanhQ 20) 0 3 91811840 6720000000 61440 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep230 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz557 119766 1000 0 1 11191020447815397 4503599627370496 125000000052941 17647000000000000000 670151877476529418551 2251799813685248000 7485375003170265903 8823500000000000000000 qz19 (BSN.isNear_log_sfrac 12 1 11191020447815397 4503599627370496 125000000052941 17647000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz327) Bool.false 46938541828353910898688 18889465931478580854784 1000000000423528 141176000000000000000 11191020447815397 4503599627370496 125000000052941 17647000000000000000 (BSN.log_rat_reduce_isNear 12 1 3 24 16 212580 524288 24973259072661432 36028797018963968 141176 1000000000000000 rfl rfl rfl rfl (ep229 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep231 := nat_lit 5931527759974425186797433787165654161

noncomputable def ep232 := BSN.sin_dyadic_bound_f 1560600141 2147483648 2 1 1048576 282628 ep231 ep144 ep231 ep231 ep145 ep231 696689 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1560600141) qz21 0 1 ep231 ep144 ep231 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1560600141) qz285 0 1 ep231 ep145 ep231 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz328 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 312063785) qz17)

noncomputable def ep233 := @Enclosure.Real.IsNear.cos_image qz46 qz328 Bool.false 312063785 1048576 891 1048576 Bool.true 696689 1048576 1 141176 (@Enclosure.Real.IsNear.recentre' qz46 Bool.false 670151877476529418551 2251799813685248000 7485375003170265903 8823500000000000000000 312063785 1048576 891 1048576 (ep230 rfl) rfl) (Enclosure.sfrac_false_div 312063785 1048576) (BSN.cos_reduce1 qz328 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 109817472109202794086400) qz20) 226375608064910080 72057594037927936 Bool.false 696689 1048576 47 1000000000000000 282352 141176 (BSN.sin_reduce_arg_pos_rat_q1 312063785 1048576 226375608064910080 72057594037927936 47 109817472109202794086400 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 696689 1048576 109817472109202794086400 151115727451828646838272 1560600141 2147483648 282628 282352 (ep232 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep234 := nat_lit 211966585111809051370206388622796645935982527463043528389381727643872554797601

noncomputable def ep235 := nat_lit 35183021567347222171064982081740364904129764980201555710904516715056613921

noncomputable def ep236 := nat_lit 635829389292292459666277035904226457078139322859170182056723373898187551164961

noncomputable def ep237 := BSN.cos_dyadic_bound_f 1560600141 2147483648 3 2 1048576 282628 ep234 ep58 ep235 ep236 ep61 ep235 783667 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1560600141) qz16 0 2 ep234 ep58 ep235 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1560600141) qz282 0 2 ep236 ep61 ep235 rfl rfl rfl rfl) rfl rfl

noncomputable def ep238 := @Enclosure.Real.IsNear.sin_image qz46 qz328 Bool.false 312063785 1048576 891 1048576 Bool.false 783667 1048576 1 141176 (@Enclosure.Real.IsNear.recentre' qz46 Bool.false 670151877476529418551 2251799813685248000 7485375003170265903 8823500000000000000000 312063785 1048576 891 1048576 (ep230 rfl) rfl) (Enclosure.sfrac_false_div 312063785 1048576) (BSN.sin_reduce1 qz328 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 109817472109202794086400) qz20) 226375608064910080 72057594037927936 Bool.false 783667 1048576 47 1000000000000000 282352 141176 (BSN.sin_reduce_arg_pos_rat_q1 312063785 1048576 226375608064910080 72057594037927936 47 109817472109202794086400 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 783667 1048576 109817472109202794086400 151115727451828646838272 1560600141 2147483648 282628 282352 (ep237 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz329 := (@Enclosure.Real.IsNear.recentre' qz45 Bool.false 302697 1048576 1 1048576 302697 1048576 1 1048576 (ep228 rfl rfl) rfl)

noncomputable def ep239 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz45 (Real.cos qz46)) (@HMul.hMul Real Real Real qz0 qz45 (@Neg.neg Real Real.instNeg (Real.sin qz46))) Bool.true 210885670233 1099511627776 4811434743985 19403081695363072 Bool.true 237213649899 1099511627776 4812969644751 19403081695363072 (@Enclosure.Real.IsNear.mulLit_ft qz45 (Real.cos qz46) 302697 1048576 1 1048576 696689 1048576 15854549 18504220672 210885670233 1099511627776 4811434743985 19403081695363072 qz329 (@Enclosure.Real.IsNear.recentre' (Real.cos qz46) Bool.true 696689 1048576 126836392 148033765376 696689 1048576 15854549 18504220672 (ep233 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz45 (@Neg.neg Real Real.instNeg (Real.sin qz46)) 302697 1048576 1 1048576 783667 1048576 15854549 18504220672 237213649899 1099511627776 4812969644751 19403081695363072 qz329 (@Enclosure.Real.IsNear.neg (Real.sin qz46) Bool.false 783667 1048576 15854549 18504220672 (@Enclosure.Real.IsNear.recentre' (Real.sin qz46) Bool.false 783667 1048576 126836392 148033765376 783667 1048576 15854549 18504220672 (ep238 rfl rfl) rfl)) rfl)

noncomputable def ep240 := @ep174 210885670233 1099511627776 4811434743985 19403081695363072 Bool.true 237213649899 1099511627776 4812969644751 19403081695363072 Bool.false ep175 880257199461 549755813888 38375902678317 9701540847681536 Bool.true 92047356929959725629440 5232286465 68719476736 38383674946527 9701540847681536 (ep176 (BSN.head_sum_c_succ qz5 11 12 rfl rfl) (ep226 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep227 ep239) rfl rfl

noncomputable abbrev qz330 := (@Nat.cast Real Real.instNatCast 13)

noncomputable abbrev qz47 := (@Inv.inv Real Real.instInv (Real.sqrt qz330))

noncomputable abbrev qz558 := (Real.log (Enclosure.sfrac Bool.false 13 1))

noncomputable abbrev qz48 := (@HMul.hMul Real Real Real qz268 qz279 qz558)

noncomputable def ep241 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz311 qz7) (Complex.mk (@HMul.hMul Real Real Real qz0 qz47 (Real.cos qz48)) (@HMul.hMul Real Real Real qz0 qz47 (@Neg.neg Real Real.instNeg (Real.sin qz48)))) Bool.false 236627843127 1099511627776 4620109651151 19403081695363072 Bool.false 192358184421 1099511627776 4617423389517 19403081695363072 (BSN.cpow_neg_s_mk qz13 119766 1000 13 qz14 rfl)

noncomputable abbrev qz331 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 13) qz15)

noncomputable def ep242 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz330) 3780695 1048576 1 1048576 145411 145412 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz330) (Real.sqrt qz331) Bool.false 3780695 1048576 1 1048576 (BSN.sqrt_natCast_div_one 13) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz331) Bool.false 3780695 1048576 1 1048576 3780695 1048576 1 1048576 (BSN.sqrt_enclosure 13 1 1890347 1890348 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep243 := BSN.log_dyadic_bound 5 21 5 4 35742602096145 524288 141176 699352521000 41015625 254545 26 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 5) (BSN.artanhQ 21) 0 4 699352521000 35742602096145 41015625 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep244 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz558 119766 1000 0 1 11551497052968677 4503599627370496 125000000052941 17647000000000000000 691738298022923284791 2251799813685248000 7485375003170265903 8823500000000000000000 qz19 (BSN.isNear_log_sfrac 13 1 11551497052968677 4503599627370496 125000000052941 17647000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz331) Bool.false 48450490295254733815808 18889465931478580854784 1000000000423528 141176000000000000000 11551497052968677 4503599627370496 125000000052941 17647000000000000000 (BSN.log_rat_reduce_isNear 13 1 3 26 16 254545 524288 24973259072661432 36028797018963968 141176 1000000000000000 rfl rfl rfl rfl (ep243 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep245 := nat_lit 851553873234568383650712746044375714535869397735863226925398343285957218795520

noncomputable def ep246 := nat_lit 175243932775191297540113227615091141815009498501992179374705669527878762496

noncomputable def ep247 := nat_lit 2229976415913662123651087484890559580983386026310638559371341375617319007420416

noncomputable def ep248 := BSN.sin_dyadic_bound_f 1907459712 2147483648 3 2 1048576 282628 ep245 ep65 ep246 ep247 ep67 ep246 813649 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1907459712) qz21 0 2 ep245 ep65 ep246 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1907459712) qz285 0 2 ep247 ep67 ep246 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz332 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 161057873) qz34)

noncomputable def ep249 := @Enclosure.Real.IsNear.cos_image qz48 qz332 Bool.false 161057873 524288 445 524288 Bool.false 813649 1048576 1 141176 (@Enclosure.Real.IsNear.recentre' qz48 Bool.false 691738298022923284791 2251799813685248000 7485375003170265903 8823500000000000000000 161057873 524288 445 524288 (ep244 rfl) rfl) (Enclosure.sfrac_false_div 161057873 524288) (BSN.cos_reduce3 qz332 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 67112772270872074387456) qz35) 226375608064910080 72057594037927936 Bool.false 813649 1048576 48 1000000000000000 282352 141176 (BSN.sin_reduce_arg_pos_rat_q3 161057873 524288 226375608064910080 72057594037927936 48 67112772270872074387456 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 813649 1048576 67112772270872074387456 75557863725914323419136 1907459712 2147483648 282628 282352 (ep248 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep250 := nat_lit 473163371322660298160413798125815437471845225185924900371610059900877512114176

noncomputable def ep251 := nat_lit 1419139626102430511886161167922216130131905656560770716756080768363576778817536

noncomputable def ep252 := BSN.cos_dyadic_bound_f 1907459712 2147483648 3 2 1048576 282628 ep250 ep58 ep246 ep251 ep61 ep246 661427 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1907459712) qz16 0 2 ep250 ep58 ep246 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1907459712) qz282 0 2 ep251 ep61 ep246 rfl rfl rfl rfl) rfl rfl

noncomputable def ep253 := @Enclosure.Real.IsNear.sin_image qz48 qz332 Bool.false 161057873 524288 445 524288 Bool.true 661427 1048576 1 141176 (@Enclosure.Real.IsNear.recentre' qz48 Bool.false 691738298022923284791 2251799813685248000 7485375003170265903 8823500000000000000000 161057873 524288 445 524288 (ep244 rfl) rfl) (Enclosure.sfrac_false_div 161057873 524288) (BSN.sin_reduce3 qz332 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 67112772270872074387456) qz35) 226375608064910080 72057594037927936 Bool.false 661427 1048576 48 1000000000000000 282352 141176 (BSN.sin_reduce_arg_pos_rat_q3 161057873 524288 226375608064910080 72057594037927936 48 67112772270872074387456 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 661427 1048576 67112772270872074387456 75557863725914323419136 1907459712 2147483648 282628 282352 (ep252 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz333 := (@Enclosure.Real.IsNear.recentre' qz47 Bool.false 290823 1048576 1 1048576 290823 1048576 1 1048576 (ep242 rfl rfl) rfl)

noncomputable def ep254 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz47 (Real.cos qz48)) (@HMul.hMul Real Real Real qz0 qz47 (@Neg.neg Real Real.instNeg (Real.sin qz48))) Bool.false 236627843127 1099511627776 4620109651151 19403081695363072 Bool.false 192358184421 1099511627776 4617423389517 19403081695363072 (@Enclosure.Real.IsNear.mulLit_ff qz47 (Real.cos qz48) 290823 1048576 1 1048576 813649 1048576 7918451 9252110336 236627843127 1099511627776 4620109651151 19403081695363072 qz333 (@Enclosure.Real.IsNear.recentre' (Real.cos qz48) Bool.false 813649 1048576 63347608 74016882688 813649 1048576 7918451 9252110336 (ep249 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz47 (@Neg.neg Real Real.instNeg (Real.sin qz48)) 290823 1048576 1 1048576 661427 1048576 7918451 9252110336 192358184421 1099511627776 4617423389517 19403081695363072 qz333 (@Enclosure.Real.IsNear.neg (Real.sin qz48) Bool.true 661427 1048576 7918451 9252110336 (@Enclosure.Real.IsNear.recentre' (Real.sin qz48) Bool.true 661427 1048576 63347608 74016882688 661427 1048576 7918451 9252110336 (ep253 rfl rfl) rfl)) rfl)

noncomputable def ep255 := @ep172 236627843127 1099511627776 4620109651151 19403081695363072 Bool.false 192358184421 1099511627776 4617423389517 19403081695363072 Bool.false 1097940558727753091776512 1997142242049 1099511627776 81371915007785 19403081695363072 Bool.false 7465793971175624278016 108641600981 1099511627776 81384773282571 19403081695363072 (ep173 (BSN.head_sum_c_succ qz5 12 13 rfl rfl) (ep240 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep241 ep254) rfl rfl

noncomputable abbrev qz334 := (@Nat.cast Real Real.instNatCast 14)

noncomputable abbrev qz49 := (@Inv.inv Real Real.instInv (Real.sqrt qz334))

noncomputable abbrev qz559 := (Real.log (Enclosure.sfrac Bool.false 14 1))

noncomputable abbrev qz50 := (@HMul.hMul Real Real Real qz268 qz279 qz559)

noncomputable def ep256 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz310 qz7) (Complex.mk (@HMul.hMul Real Real Real qz0 qz49 (Real.cos qz50)) (@HMul.hMul Real Real Real qz0 qz49 (@Neg.neg Real Real.instNeg (Real.sin qz50)))) Bool.true 48871857013 549755813888 2224648592955 9701540847681536 Bool.true 277123615167 1099511627776 4460592801199 19403081695363072 (BSN.cpow_neg_s_mk qz13 119766 1000 14 qz14 rfl)

noncomputable abbrev qz335 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 14) qz15)

noncomputable def ep257 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz334) 3923413 1048576 1 1048576 140121 140122 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz334) (Real.sqrt qz335) Bool.false 3923413 1048576 1 1048576 (BSN.sqrt_natCast_div_one 14) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz335) Bool.false 3923413 1048576 1 1048576 3923413 1048576 1 1048576 (BSN.sqrt_enclosure 14 1 1961706 1961707 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep258 := BSN.log_dyadic_bound 6 22 5 4 51857700491520 524288 141176 1346332575744 176359680 293399 28 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 6) (BSN.artanhQ 22) 0 4 1346332575744 51857700491520 176359680 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep259 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz559 119766 1000 0 1 11885250371606245 4503599627370496 125000000052941 17647000000000000000 142344889600579353867 450359962737049600 7485375003170265903 8823500000000000000000 qz19 (BSN.isNear_log_sfrac 14 1 11885250371606245 4503599627370496 125000000052941 17647000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz335) Bool.false 49850353174629559828480 18889465931478580854784 1000000000423528 141176000000000000000 11885250371606245 4503599627370496 125000000052941 17647000000000000000 (BSN.log_rat_reduce_isNear 14 1 3 28 16 293399 524288 24973259072661432 36028797018963968 141176 1000000000000000 rfl rfl rfl rfl (ep258 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep260 := nat_lit 281161562132588107816236588796123281

noncomputable def ep261 := BSN.sin_dyadic_bound_f 728180403 2147483648 2 1 1048576 282628 ep260 ep144 ep260 ep260 ep145 ep260 348782 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 728180403) qz21 0 1 ep260 ep144 ep260 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 728180403) qz285 0 1 ep260 ep145 ep260 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz336 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 165711261) qz34)

noncomputable def ep262 := @Enclosure.Real.IsNear.cos_image qz50 qz336 Bool.false 165711261 524288 891 1048576 Bool.true 348782 1048576 1 141176 (@Enclosure.Real.IsNear.recentre' qz50 Bool.false 142344889600579353867 450359962737049600 7485375003170265903 8823500000000000000000 165711261 524288 891 1048576 (ep259 rfl) rfl) (Enclosure.sfrac_false_div 165711261 524288) (BSN.cos_reduce1 qz336 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 25620570273989422743552) qz35) 226375608064910080 72057594037927936 Bool.false 348782 1048576 50 1000000000000000 282352 141176 (BSN.sin_reduce_arg_pos_rat_q1 165711261 524288 226375608064910080 72057594037927936 50 25620570273989422743552 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 348782 1048576 25620570273989422743552 75557863725914323419136 728180403 2147483648 282628 282352 (ep261 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep263 := BSN.cos_dyadic_bound_f 728180403 2147483648 2 1 1048576 282628 ep260 ep140 ep260 ep260 ep141 ep260 988869 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 728180403) qz16 0 1 ep260 ep140 ep260 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 728180403) qz282 0 1 ep260 ep141 ep260 rfl rfl rfl rfl) rfl rfl

noncomputable def ep264 := @Enclosure.Real.IsNear.sin_image qz50 qz336 Bool.false 165711261 524288 891 1048576 Bool.false 988869 1048576 1 141176 (@Enclosure.Real.IsNear.recentre' qz50 Bool.false 142344889600579353867 450359962737049600 7485375003170265903 8823500000000000000000 165711261 524288 891 1048576 (ep259 rfl) rfl) (Enclosure.sfrac_false_div 165711261 524288) (BSN.sin_reduce1 qz336 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 25620570273989422743552) qz35) 226375608064910080 72057594037927936 Bool.false 988869 1048576 50 1000000000000000 282352 141176 (BSN.sin_reduce_arg_pos_rat_q1 165711261 524288 226375608064910080 72057594037927936 50 25620570273989422743552 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 988869 1048576 25620570273989422743552 75557863725914323419136 728180403 2147483648 282628 282352 (ep263 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz337 := (@Enclosure.Real.IsNear.recentre' qz49 Bool.false 280243 1048576 1 1048576 280243 1048576 1 1048576 (ep257 rfl rfl) rfl)

noncomputable def ep265 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz49 (Real.cos qz50)) (@HMul.hMul Real Real Real qz0 qz49 (@Neg.neg Real Real.instNeg (Real.sin qz50))) Bool.true 48871857013 549755813888 2224648592955 9701540847681536 Bool.true 277123615167 1099511627776 4460592801199 19403081695363072 (@Enclosure.Real.IsNear.mulLit_ft qz49 (Real.cos qz50) 280243 1048576 1 1048576 174391 524288 15854549 18504220672 48871857013 549755813888 2224648592955 9701540847681536 qz337 (@Enclosure.Real.IsNear.recentre' (Real.cos qz50) Bool.true 348782 1048576 126836392 148033765376 174391 524288 15854549 18504220672 (ep262 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz49 (@Neg.neg Real Real.instNeg (Real.sin qz50)) 280243 1048576 1 1048576 988869 1048576 15854549 18504220672 277123615167 1099511627776 4460592801199 19403081695363072 qz337 (@Enclosure.Real.IsNear.neg (Real.sin qz50) Bool.false 988869 1048576 15854549 18504220672 (@Enclosure.Real.IsNear.recentre' (Real.sin qz50) Bool.false 988869 1048576 126836392 148033765376 988869 1048576 15854549 18504220672 (ep264 rfl rfl) rfl)) rfl)

noncomputable def ep266 := @ep170 48871857013 549755813888 2224648592955 9701540847681536 Bool.true 277123615167 1099511627776 4460592801199 19403081695363072 Bool.false 1044205383670953540583424 1899398528023 1099511627776 85821212193695 19403081695363072 Bool.true 185247933668627983630336 84241007093 549755813888 42922683041885 9701540847681536 (ep171 (BSN.head_sum_c_succ qz5 13 14 rfl rfl) (ep255 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep256 ep265) rfl rfl

noncomputable abbrev qz51 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 15)))

noncomputable abbrev qz560 := (Real.log (Enclosure.sfrac Bool.false 15 1))

noncomputable abbrev qz52 := (@HMul.hMul Real Real Real qz268 qz279 qz560)

noncomputable def ep267 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz309 qz7) (Complex.mk (@HMul.hMul Real Real Real qz0 qz51 (Real.cos qz52)) (@HMul.hMul Real Real Real qz0 qz51 (@Neg.neg Real Real.instNeg (Real.sin qz52)))) Bool.true 104046578523 549755813888 2150639055683 9701540847681536 Bool.false 96555716535 549755813888 2150150798487 9701540847681536 (BSN.cpow_neg_s_mk qz13 119766 1000 15 qz14 rfl)

noncomputable abbrev qz338 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 15) qz15)

noncomputable def ep268 := @Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 15)) 4061117 1048576 1 1048576 135370 135371 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 15)) (Real.sqrt qz338) Bool.false 4061117 1048576 1 1048576 (BSN.sqrt_natCast_div_one 15) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz338) Bool.false 4061117 1048576 1 1048576 4061117 1048576 1 1048576 (BSN.sqrt_enclosure 15 1 2030558 2030559 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep269 := BSN.log_dyadic_bound 7 23 6 5 430628584065881355 524288 141176 14087658153505881 266939110305 329571 30 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 7) (BSN.artanhQ 23) 0 5 14087658153505881 430628584065881355 266939110305 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep270 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz560 119766 1000 0 1 12195965485668069 4503599627370496 125000000052941 17647000000000000000 730331001178260975927 2251799813685248000 7485375003170265903 8823500000000000000000 qz19 (BSN.isNear_log_sfrac 15 1 12195965485668069 4503599627370496 125000000052941 17647000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz338) Bool.false 51153586820399524478976 18889465931478580854784 1000000000423528 141176000000000000000 12195965485668069 4503599627370496 125000000052941 17647000000000000000 (BSN.log_rat_reduce_isNear 15 1 3 30 16 329571 524288 24973259072661432 36028797018963968 141176 1000000000000000 rfl rfl rfl rfl (ep269 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep271 := nat_lit 238016378553721266975109537492663472389570267565647433571920990725965514048321

noncomputable def ep272 := nat_lit 44360282145422260759726731182902601251725280627144890339745475518715691841

noncomputable def ep273 := nat_lit 713960415096872956403809159015624611966207352135688010935083481226859110761281

noncomputable def ep274 := BSN.cos_dyadic_bound_f 1606476169 2147483648 3 2 1048576 282628 ep271 ep58 ep272 ep273 ep61 ep272 768606 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1606476169) qz16 0 2 ep271 ep58 ep272 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1606476169) qz282 0 2 ep273 ep61 ep272 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz339 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 170043437) qz34)

noncomputable def ep275 := @Enclosure.Real.IsNear.cos_image qz52 qz339 Bool.false 170043437 524288 445 524288 Bool.true 768606 1048576 1 141176 (@Enclosure.Real.IsNear.recentre' qz52 Bool.false 730331001178260975927 2251799813685248000 7485375003170265903 8823500000000000000000 170043437 524288 445 524288 (ep270 rfl) rfl) (Enclosure.sfrac_false_div 170043437 524288) (BSN.cos_reduce2 qz339 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 56522855286020530765824) qz35) 226375608064910080 72057594037927936 Bool.false 768606 1048576 51 1000000000000000 282352 141176 (BSN.sin_reduce_arg_pos_rat_q2 170043437 524288 226375608064910080 72057594037927936 51 56522855286020530765824 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 768606 1048576 56522855286020530765824 75557863725914323419136 1606476169 2147483648 282628 282352 (ep274 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep276 := nat_lit 6660351503143228307833816802892066721

noncomputable def ep277 := BSN.sin_dyadic_bound_f 1606476169 2147483648 2 1 1048576 282628 ep276 ep144 ep276 ep276 ep145 ep276 713270 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1606476169) qz21 0 1 ep276 ep144 ep276 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1606476169) qz285 0 1 ep276 ep145 ep276 rfl rfl rfl rfl) rfl rfl

noncomputable def ep278 := @Enclosure.Real.IsNear.sin_image qz52 qz339 Bool.false 170043437 524288 445 524288 Bool.true 713270 1048576 1 141176 (@Enclosure.Real.IsNear.recentre' qz52 Bool.false 730331001178260975927 2251799813685248000 7485375003170265903 8823500000000000000000 170043437 524288 445 524288 (ep270 rfl) rfl) (Enclosure.sfrac_false_div 170043437 524288) (BSN.sin_reduce2 qz339 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 56522855286020530765824) qz35) 226375608064910080 72057594037927936 Bool.false 713270 1048576 51 1000000000000000 282352 141176 (BSN.sin_reduce_arg_pos_rat_q2 170043437 524288 226375608064910080 72057594037927936 51 56522855286020530765824 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 713270 1048576 56522855286020530765824 75557863725914323419136 1606476169 2147483648 282628 282352 (ep277 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz340 := (@Enclosure.Real.IsNear.recentre' qz51 Bool.false 270741 1048576 1 1048576 270741 1048576 1 1048576 (ep268 rfl rfl) rfl)

noncomputable def ep279 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz51 (Real.cos qz52)) (@HMul.hMul Real Real Real qz0 qz51 (@Neg.neg Real Real.instNeg (Real.sin qz52))) Bool.true 104046578523 549755813888 2150639055683 9701540847681536 Bool.false 96555716535 549755813888 2150150798487 9701540847681536 (@Enclosure.Real.IsNear.mulLit_ft qz51 (Real.cos qz52) 270741 1048576 1 1048576 384303 524288 7918451 9252110336 104046578523 549755813888 2150639055683 9701540847681536 qz340 (@Enclosure.Real.IsNear.recentre' (Real.cos qz52) Bool.true 768606 1048576 63347608 74016882688 384303 524288 7918451 9252110336 (ep275 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz51 (@Neg.neg Real Real.instNeg (Real.sin qz52)) 270741 1048576 1 1048576 356635 524288 7918451 9252110336 96555716535 549755813888 2150150798487 9701540847681536 qz340 (@Enclosure.Real.IsNear.neg (Real.sin qz52) Bool.true 356635 524288 7918451 9252110336 (@Enclosure.Real.IsNear.recentre' (Real.sin qz52) Bool.true 713270 1048576 63347608 74016882688 356635 524288 7918451 9252110336 (ep278 rfl rfl) rfl)) rfl)

noncomputable def ep280 := @ep168 104046578523 549755813888 2150639055683 9701540847681536 Bool.false 96555716535 549755813888 2150150798487 9701540847681536 Bool.false 929804960754606408728576 1691305370977 1099511627776 90122490305061 19403081695363072 Bool.false 6770083112080948330496 6157354721 274877906944 11268208460093 2425385211920384 (ep169 (BSN.head_sum_c_succ qz5 14 15 rfl rfl) (ep266 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep267 ep279) rfl rfl

noncomputable abbrev qz53 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 16)))

noncomputable abbrev qz561 := (Real.log (Enclosure.sfrac Bool.false 16 1))

noncomputable abbrev qz54 := (@HMul.hMul Real Real Real qz268 qz279 qz561)

noncomputable def ep281 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz308 qz7) (Complex.mk (@HMul.hMul Real Real Real qz0 qz53 (Real.cos qz54)) (@HMul.hMul Real Real Real qz0 qz53 (@Neg.neg Real Real.instNeg (Real.sin qz54)))) Bool.false 160569665361 1099511627776 4166984157025 19403081695363072 Bool.false 223101780867 1099511627776 4171193707699 19403081695363072 (BSN.cpow_neg_s_mk qz13 119766 1000 16 qz14 rfl)

noncomputable abbrev qz341 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 16) qz15)

noncomputable def ep282 := @Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 16)) 4194305 1048576 1 1048576 131071 131072 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 16)) (Real.sqrt qz341) Bool.false 4194305 1048576 1 1048576 (BSN.sqrt_natCast_div_one 16) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz341) Bool.false 4194305 1048576 1 1048576 4194305 1048576 1 1048576 (BSN.sqrt_enclosure 16 1 2097152 2097153 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep283 := BSN.log_dyadic_bound 0 32 1 0 1 524288 141176 0 1 0 32 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 0) (BSN.artanhQ 32) 0 0 rfl) rfl rfl rfl

noncomputable def ep284 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz561 119766 1000 0 1 3121657384082679 1125899906842624 31250000017647 4411750000000000000 186934209131023066557 562949953421312000 1871343751056755301 2205875000000000000000 qz19 (BSN.isNear_log_sfrac 16 1 3121657384082679 1125899906842624 31250000017647 4411750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz341) Bool.false 52372720210750067441664 18889465931478580854784 1000000000564704 141176000000000000000 3121657384082679 1125899906842624 31250000017647 4411750000000000000 (BSN.log_rat_reduce_isNear 16 1 4 32 32 0 524288 24973259072661432 36028797018963968 141176 1000000000000000 rfl rfl rfl rfl (ep283 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep285 := nat_lit 3221059698705265956255734259766318096

noncomputable def ep286 := BSN.sin_dyadic_bound_f 1339675742 2147483648 2 1 1048576 282628 ep285 ep144 ep285 ep285 ep145 ep285 612527 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1339675742) qz21 0 1 ep285 ep144 ep285 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1339675742) qz285 0 1 ep285 ep145 ep285 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz342 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 348192097) qz17)

noncomputable def ep287 := @Enclosure.Real.IsNear.cos_image qz54 qz342 Bool.false 348192097 1048576 891 1048576 Bool.false 612527 1048576 1 141176 (@Enclosure.Real.IsNear.recentre' qz54 Bool.false 186934209131023066557 562949953421312000 1871343751056755301 2205875000000000000000 348192097 1048576 891 1048576 (ep284 rfl) rfl) (Enclosure.sfrac_false_div 348192097 1048576) (BSN.cos_reduce3 qz342 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 94271299602438059720704) qz20) 226375608064910080 72057594037927936 Bool.false 612527 1048576 52 1000000000000000 282352 141176 (BSN.sin_reduce_arg_pos_rat_q3 348192097 1048576 226375608064910080 72057594037927936 52 94271299602438059720704 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 612527 1048576 94271299602438059720704 151115727451828646838272 1339675742 2147483648 282628 282352 (ep286 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep288 := BSN.cos_dyadic_bound_f 1339675742 2147483648 2 1 1048576 282628 ep285 ep140 ep285 ep285 ep141 ep285 851069 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1339675742) qz16 0 1 ep285 ep140 ep285 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1339675742) qz282 0 1 ep285 ep141 ep285 rfl rfl rfl rfl) rfl rfl

noncomputable def ep289 := @Enclosure.Real.IsNear.sin_image qz54 qz342 Bool.false 348192097 1048576 891 1048576 Bool.true 851069 1048576 1 141176 (@Enclosure.Real.IsNear.recentre' qz54 Bool.false 186934209131023066557 562949953421312000 1871343751056755301 2205875000000000000000 348192097 1048576 891 1048576 (ep284 rfl) rfl) (Enclosure.sfrac_false_div 348192097 1048576) (BSN.sin_reduce3 qz342 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 94271299602438059720704) qz20) 226375608064910080 72057594037927936 Bool.false 851069 1048576 52 1000000000000000 282352 141176 (BSN.sin_reduce_arg_pos_rat_q3 348192097 1048576 226375608064910080 72057594037927936 52 94271299602438059720704 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 851069 1048576 94271299602438059720704 151115727451828646838272 1339675742 2147483648 282628 282352 (ep288 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz343 := (@Enclosure.Real.IsNear.recentre' qz53 Bool.false 262143 1048576 1 1048576 262143 1048576 1 1048576 (ep282 rfl rfl) rfl)

noncomputable def ep290 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz53 (Real.cos qz54)) (@HMul.hMul Real Real Real qz0 qz53 (@Neg.neg Real Real.instNeg (Real.sin qz54))) Bool.false 160569665361 1099511627776 4166984157025 19403081695363072 Bool.false 223101780867 1099511627776 4171193707699 19403081695363072 (@Enclosure.Real.IsNear.mulLit_ff qz53 (Real.cos qz54) 262143 1048576 1 1048576 612527 1048576 15854549 18504220672 160569665361 1099511627776 4166984157025 19403081695363072 qz343 (@Enclosure.Real.IsNear.recentre' (Real.cos qz54) Bool.false 612527 1048576 126836392 148033765376 612527 1048576 15854549 18504220672 (ep287 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz53 (@Neg.neg Real Real.instNeg (Real.sin qz54)) 262143 1048576 1 1048576 851069 1048576 15854549 18504220672 223101780867 1099511627776 4171193707699 19403081695363072 qz343 (@Enclosure.Real.IsNear.neg (Real.sin qz54) Bool.true 851069 1048576 15854549 18504220672 (@Enclosure.Real.IsNear.recentre' (Real.sin qz54) Bool.true 851069 1048576 126836392 148033765376 851069 1048576 15854549 18504220672 (ep289 rfl rfl) rfl)) rfl)

noncomputable def ep291 := @ep165 160569665361 1099511627776 4166984157025 19403081695363072 Bool.false 223101780867 1099511627776 4171193707699 19403081695363072 Bool.false ep166 925937518169 549755813888 47144737231043 9701540847681536 Bool.false 68095833672280853970944 247731199751 1099511627776 94316861388443 19403081695363072 (ep167 (BSN.head_sum_c_succ qz5 15 16 rfl rfl) (ep280 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep281 ep290) rfl rfl

theorem EMRow39.d7 : Enclosure.Complex.IsNear qz38 Bool.false 925937518169 549755813888 47144737231043 9701540847681536 Bool.false 247731199751 1099511627776 94316861388443 19403081695363072 := ep164 (BSN.head_sum_c_succ qz5 16 17 rfl rfl) (ep291 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable abbrev qz55 := (BSN.headSumC qz272 25)

noncomputable abbrev qz344 := (@Nat.cast Complex Complex.instNatCast 24)

noncomputable def ep292 := @Enclosure.Complex.IsNear.of_eq qz55 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 24) (@HPow.hPow Complex Complex Complex qz6 qz344 qz7)) Bool.false 2974059790119 1099511627776 123920373848123 19403081695363072 Bool.false 83469755161 549755813888 30973528808913 4850770423840768

noncomputable def ep293 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 24) (@HPow.hPow Complex Complex Complex qz6 qz344 qz7) Bool.false 396511271399 137438953472 60257158108057 9701540847681536 Bool.false 30659912691 549755813888 15061959580369 2425385211920384 Bool.true

noncomputable abbrev qz345 := (@Nat.cast Complex Complex.instNatCast 23)

noncomputable def ep294 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 24) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 23) (@HPow.hPow Complex Complex Complex qz6 qz345 qz7)) Bool.false 396511271399 137438953472 60257158108057 9701540847681536 Bool.false 30659912691 549755813888 15061959580369 2425385211920384

noncomputable def ep295 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 23) (@HPow.hPow Complex Complex Complex qz6 qz345 qz7) Bool.false 1574025186671 549755813888 14631216540947 2425385211920384 Bool.true 166680001803 1099511627776 117014630838699 19403081695363072 Bool.false

noncomputable abbrev qz346 := (@Nat.cast Complex Complex.instNatCast 22)

noncomputable def ep296 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 23) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 22) (@HPow.hPow Complex Complex Complex qz6 qz346 qz7)) Bool.false 1574025186671 549755813888 14631216540947 2425385211920384 Bool.true 166680001803 1099511627776 117014630838699 19403081695363072

noncomputable def ep297 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 22) (@HPow.hPow Complex Complex Complex qz6 qz346 qz7) Bool.false 1471518489689 549755813888 7093317685851 1212692605960192 Bool.true 140174338119 549755813888 56732595997999 9701540847681536 Bool.false

noncomputable abbrev qz347 := (@Nat.cast Complex Complex.instNatCast 21)

noncomputable def ep298 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 22) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 21) (@HPow.hPow Complex Complex Complex qz6 qz347 qz7)) Bool.false 1471518489689 549755813888 7093317685851 1212692605960192 Bool.true 140174338119 549755813888 56732595997999 9701540847681536

noncomputable def ep299 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 21) (@HPow.hPow Complex Complex Complex qz6 qz347 qz7) Bool.false 677036823437 274877906944 54914507272573 9701540847681536 Bool.true 115707058197 549755813888 54914903094783 9701540847681536 Bool.false

noncomputable abbrev qz348 := (@Nat.cast Complex Complex.instNatCast 20)

noncomputable def ep300 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 21) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 20) (@HPow.hPow Complex Complex Complex qz6 qz348 qz7)) Bool.false 677036823437 274877906944 54914507272573 9701540847681536 Bool.true 115707058197 549755813888 54914903094783 9701540847681536

noncomputable def ep301 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 20) (@HPow.hPow Complex Complex Complex qz6 qz348 qz7) Bool.false 2511711275769 1099511627776 106100951635429 19403081695363072 Bool.true 83565702471 1099511627776 106105400161777 19403081695363072 Bool.false

noncomputable def ep302 := nat_lit 2977639439206032707944448

noncomputable abbrev qz349 := (@Nat.cast Complex Complex.instNatCast 19)

noncomputable def ep303 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 20) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 19) (@HPow.hPow Complex Complex Complex qz6 qz349 qz7)) Bool.false 2511711275769 1099511627776 106100951635429 19403081695363072 Bool.true 83565702471 1099511627776 106105400161777 19403081695363072

noncomputable def ep304 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 19) (@HPow.hPow Complex Complex Complex qz6 qz349 qz7) Bool.false 583332329985 274877906944 1598029617663 303173151490048 Bool.false 94779447831 1099511627776 102278346756771 19403081695363072 Bool.false

noncomputable abbrev qz350 := (@Nat.cast Complex Complex.instNatCast 18)

noncomputable def ep305 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 19) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 18) (@HPow.hPow Complex Complex Complex qz6 qz350 qz7)) Bool.false 583332329985 274877906944 1598029617663 303173151490048 Bool.false 94779447831 1099511627776 102278346756771 19403081695363072

noncomputable def ep306 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 18) (@HPow.hPow Complex Complex Complex qz6 qz350 qz7) Bool.false 2118421886551 1099511627776 98340067281251 19403081695363072 Bool.false 119806573397 549755813888 3073422559091 606346302980096 Bool.false

noncomputable def ep307 := nat_lit 2565522718704696494653440

noncomputable abbrev qz351 := (@Nat.cast Complex Complex.instNatCast 17)

noncomputable def ep308 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 18) (@HAdd.hAdd Complex Complex Complex qz4 qz38 (@HPow.hPow Complex Complex Complex qz6 qz351 qz7)) Bool.false 2118421886551 1099511627776 98340067281251 19403081695363072 Bool.false 119806573397 549755813888 3073422559091 606346302980096

noncomputable def ep309 := @Enclosure.Complex.IsNear.addLitP qz38 (@HPow.hPow Complex Complex Complex qz6 qz351 qz7) Bool.false 925937518169 549755813888 47144737231043 9701540847681536 Bool.false 247731199751 1099511627776 94316861388443 19403081695363072 Bool.false

noncomputable abbrev qz56 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 17)))

noncomputable abbrev qz562 := (Real.log (Enclosure.sfrac Bool.false 17 1))

noncomputable abbrev qz57 := (@HMul.hMul Real Real Real qz268 qz279 qz562)

noncomputable def ep310 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz351 qz7) (Complex.mk (@HMul.hMul Real Real Real qz0 qz56 (Real.cos qz57)) (@HMul.hMul Real Real Real qz0 qz56 (@Neg.neg Real Real.instNeg (Real.sin qz57)))) Bool.false 266546850213 1099511627776 4050592819165 19403081695363072 Bool.true 8118052957 1099511627776 4032660502469 19403081695363072 (BSN.cpow_neg_s_mk qz13 119766 1000 17 qz14 rfl)

noncomputable abbrev qz352 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 17) qz15)

noncomputable def ep311 := @Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 17)) 4323389 1048576 1 1048576 127158 127159 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 17)) (Real.sqrt qz352) Bool.false 4323389 1048576 1 1048576 (BSN.sqrt_natCast_div_one 17) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz352) Bool.false 4323389 1048576 1 1048576 4323389 1048576 1 1048576 (BSN.sqrt_enclosure 17 1 2161694 2161695 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep312 := BSN.log_dyadic_bound 1 33 2 1 3267 524288 141176 1 1 31784 34 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 1) (BSN.artanhQ 33) 0 1 1 3267 1 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep313 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz562 119766 1000 0 1 3189913004350711 1125899906842624 31250000017647 4411750000000000000 191021560439533626813 562949953421312000 1871343751056755301 2205875000000000000000 qz19 (BSN.isNear_log_sfrac 17 1 3189913004350711 1125899906842624 31250000017647 4411750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz352) Bool.false 53517859495200818200576 18889465931478580854784 1000000000564704 141176000000000000000 3189913004350711 1125899906842624 31250000017647 4411750000000000000 (BSN.log_rat_reduce_isNear 17 1 4 34 32 31784 524288 24973259072661432 36028797018963968 141176 1000000000000000 rfl rfl rfl rfl (ep312 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep314 := BSN.cos_dyadic_bound_f 65386291 2147483648 1 0 1048576 282628 0 1 1 0 1 1 1048089 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 65386291) qz16 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 65386291) qz282 0 0 rfl) rfl rfl

noncomputable abbrev qz353 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 177902691) qz34)

noncomputable def ep315 := @Enclosure.Real.IsNear.cos_image qz57 qz353 Bool.false 177902691 524288 891 1048576 Bool.false 1048089 1048576 1 141176 (@Enclosure.Real.IsNear.recentre' qz57 Bool.false 191021560439533626813 562949953421312000 1871343751056755301 2205875000000000000000 177902691 524288 891 1048576 (ep313 rfl) rfl) (Enclosure.sfrac_false_div 177902691 524288) (BSN.cos_reduce0 qz353 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 2300575620587335974912) qz35) 226375608064910080 72057594037927936 Bool.false 1048089 1048576 54 1000000000000000 282352 141176 (BSN.sin_reduce_arg_pos_rat_q0 177902691 524288 226375608064910080 72057594037927936 54 2300575620587335974912 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1048089 1048576 2300575620587335974912 75557863725914323419136 65386291 2147483648 282628 282352 (ep314 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep316 := BSN.sin_dyadic_bound_f 65386291 2147483648 1 0 1048576 282628 0 1 1 0 1 1 31921 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 65386291) qz21 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 65386291) qz285 0 0 rfl) rfl rfl

noncomputable def ep317 := @Enclosure.Real.IsNear.sin_image qz57 qz353 Bool.false 177902691 524288 891 1048576 Bool.false 31921 1048576 1 141176 (@Enclosure.Real.IsNear.recentre' qz57 Bool.false 191021560439533626813 562949953421312000 1871343751056755301 2205875000000000000000 177902691 524288 891 1048576 (ep313 rfl) rfl) (Enclosure.sfrac_false_div 177902691 524288) (BSN.sin_reduce0 qz353 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 2300575620587335974912) qz35) 226375608064910080 72057594037927936 Bool.false 31921 1048576 54 1000000000000000 282352 141176 (BSN.sin_reduce_arg_pos_rat_q0 177902691 524288 226375608064910080 72057594037927936 54 2300575620587335974912 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 31921 1048576 2300575620587335974912 75557863725914323419136 65386291 2147483648 282628 282352 (ep316 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz354 := (@Enclosure.Real.IsNear.recentre' qz56 Bool.false 254317 1048576 1 1048576 254317 1048576 1 1048576 (ep311 rfl rfl) rfl)

noncomputable def ep318 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz56 (Real.cos qz57)) (@HMul.hMul Real Real Real qz0 qz56 (@Neg.neg Real Real.instNeg (Real.sin qz57))) Bool.false 266546850213 1099511627776 4050592819165 19403081695363072 Bool.true 8118052957 1099511627776 4032660502469 19403081695363072 (@Enclosure.Real.IsNear.mulLit_ff qz56 (Real.cos qz57) 254317 1048576 1 1048576 1048089 1048576 15854549 18504220672 266546850213 1099511627776 4050592819165 19403081695363072 qz354 (@Enclosure.Real.IsNear.recentre' (Real.cos qz57) Bool.false 1048089 1048576 126836392 148033765376 1048089 1048576 15854549 18504220672 (ep315 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz56 (@Neg.neg Real Real.instNeg (Real.sin qz57)) 254317 1048576 1 1048576 31921 1048576 15854549 18504220672 8118052957 1099511627776 4032660502469 19403081695363072 qz354 (@Enclosure.Real.IsNear.neg (Real.sin qz57) Bool.false 31921 1048576 15854549 18504220672 (@Enclosure.Real.IsNear.recentre' (Real.sin qz57) Bool.false 31921 1048576 126836392 148033765376 31921 1048576 15854549 18504220672 (ep317 rfl rfl) rfl)) rfl)

noncomputable def ep319 := @ep309 266546850213 1099511627776 4050592819165 19403081695363072 Bool.true 8118052957 1099511627776 4032660502469 19403081695363072 Bool.false 1164614748398997406220288 2118421886551 1099511627776 98340067281251 19403081695363072 Bool.false 263457441068000575750144 119806573397 549755813888 3073422559091 606346302980096 EMRow39.d7 (ep310 ep318) rfl rfl

noncomputable abbrev qz58 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 18)))

noncomputable abbrev qz563 := (Real.log (Enclosure.sfrac Bool.false 18 1))

noncomputable abbrev qz59 := (@HMul.hMul Real Real Real qz268 qz279 qz563)

noncomputable def ep320 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz350 qz7) (Complex.mk (@HMul.hMul Real Real Real qz0 qz58 (Real.cos qz59)) (@HMul.hMul Real Real Real qz0 qz58 (@Neg.neg Real Real.instNeg (Real.sin qz59)))) Bool.false 214907433389 1099511627776 3933828249181 19403081695363072 Bool.true 144833698963 1099511627776 3928824865859 19403081695363072 (BSN.cpow_neg_s_mk qz13 119766 1000 18 qz14 rfl)

noncomputable abbrev qz355 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 18) qz15)

noncomputable def ep321 := @Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 18)) 4448731 1048576 1 1048576 123575 123576 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 18)) (Real.sqrt qz355) Bool.false 4448731 1048576 1 1048576 (BSN.sqrt_natCast_div_one 18) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz355) Bool.false 4448731 1048576 1 1048576 4448731 1048576 1 1048576 (BSN.sqrt_enclosure 18 1 2224365 2224366 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep322 := BSN.log_dyadic_bound 2 34 2 1 3468 524288 141176 4 4 61752 36 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 2) (BSN.artanhQ 34) 0 1 4 3468 4 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep323 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz563 119766 1000 0 1 3254268794313975 1125899906842624 31250000017647 4411750000000000000 7795015128396150597 22517998136852480 1871343751056755301 2205875000000000000000 qz19 (BSN.isNear_log_sfrac 18 1 3254268794313975 1125899906842624 31250000017647 4411750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz355) Bool.false 54597570484265130393600 18889465931478580854784 1000000000564704 141176000000000000000 3254268794313975 1125899906842624 31250000017647 4411750000000000000 (BSN.log_rat_reduce_isNear 18 1 4 36 32 61752 524288 24973259072661432 36028797018963968 141176 1000000000000000 rfl rfl rfl rfl (ep322 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep324 := nat_lit 2630215663676502021182269217876476081

noncomputable def ep325 := BSN.cos_dyadic_bound_f 1273496747 2147483648 2 1 1048576 282628 ep324 ep140 ep324 ep324 ep141 ep324 869539 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1273496747) qz16 0 1 ep324 ep140 ep324 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1273496747) qz282 0 1 ep324 ep141 ep324 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz356 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 362983677) qz17)

noncomputable def ep326 := @Enclosure.Real.IsNear.cos_image qz59 qz356 Bool.false 362983677 1048576 891 1048576 Bool.false 869539 1048576 1 141176 (@Enclosure.Real.IsNear.recentre' qz59 Bool.false 7795015128396150597 22517998136852480 1871343751056755301 2205875000000000000000 362983677 1048576 891 1048576 (ep323 rfl) rfl) (Enclosure.sfrac_false_div 362983677 1048576) (BSN.cos_reduce0 qz356 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 89614366821065890463744) qz20) 226375608064910080 72057594037927936 Bool.false 869539 1048576 55 1000000000000000 282352 141176 (BSN.sin_reduce_arg_pos_rat_q0 362983677 1048576 226375608064910080 72057594037927936 55 89614366821065890463744 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 869539 1048576 89614366821065890463744 151115727451828646838272 1273496747 2147483648 282628 282352 (ep325 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep327 := BSN.sin_dyadic_bound_f 1273496747 2147483648 2 1 1048576 282628 ep324 ep144 ep324 ep324 ep145 ep324 586013 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1273496747) qz21 0 1 ep324 ep144 ep324 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1273496747) qz285 0 1 ep324 ep145 ep324 rfl rfl rfl rfl) rfl rfl

noncomputable def ep328 := @Enclosure.Real.IsNear.sin_image qz59 qz356 Bool.false 362983677 1048576 891 1048576 Bool.false 586013 1048576 1 141176 (@Enclosure.Real.IsNear.recentre' qz59 Bool.false 7795015128396150597 22517998136852480 1871343751056755301 2205875000000000000000 362983677 1048576 891 1048576 (ep323 rfl) rfl) (Enclosure.sfrac_false_div 362983677 1048576) (BSN.sin_reduce0 qz356 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 89614366821065890463744) qz20) 226375608064910080 72057594037927936 Bool.false 586013 1048576 55 1000000000000000 282352 141176 (BSN.sin_reduce_arg_pos_rat_q0 362983677 1048576 226375608064910080 72057594037927936 55 89614366821065890463744 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 586013 1048576 89614366821065890463744 151115727451828646838272 1273496747 2147483648 282628 282352 (ep327 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz357 := (@Enclosure.Real.IsNear.recentre' qz58 Bool.false 247151 1048576 1 1048576 247151 1048576 1 1048576 (ep321 rfl rfl) rfl)

noncomputable def ep329 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz58 (Real.cos qz59)) (@HMul.hMul Real Real Real qz0 qz58 (@Neg.neg Real Real.instNeg (Real.sin qz59))) Bool.false 214907433389 1099511627776 3933828249181 19403081695363072 Bool.true 144833698963 1099511627776 3928824865859 19403081695363072 (@Enclosure.Real.IsNear.mulLit_ff qz58 (Real.cos qz59) 247151 1048576 1 1048576 869539 1048576 15854549 18504220672 214907433389 1099511627776 3933828249181 19403081695363072 qz357 (@Enclosure.Real.IsNear.recentre' (Real.cos qz59) Bool.false 869539 1048576 126836392 148033765376 869539 1048576 15854549 18504220672 (ep326 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz58 (@Neg.neg Real Real.instNeg (Real.sin qz59)) 247151 1048576 1 1048576 586013 1048576 15854549 18504220672 144833698963 1099511627776 3928824865859 19403081695363072 qz357 (@Enclosure.Real.IsNear.neg (Real.sin qz59) Bool.false 586013 1048576 15854549 18504220672 (@Enclosure.Real.IsNear.recentre' (Real.sin qz59) Bool.false 586013 1048576 126836392 148033765376 586013 1048576 15854549 18504220672 (ep328 rfl rfl) rfl)) rfl)

noncomputable def ep330 := @ep306 214907433389 1099511627776 3933828249181 19403081695363072 Bool.true 144833698963 1099511627776 3928824865859 19403081695363072 Bool.false ep307 583332329985 274877906944 1598029617663 303173151490048 Bool.false 52105552482186641276928 94779447831 1099511627776 102278346756771 19403081695363072 (ep308 (BSN.head_sum_c_succ qz5 17 18 rfl rfl) (ep319 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep320 ep329) rfl rfl

noncomputable abbrev qz60 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 19)))

noncomputable abbrev qz564 := (Real.log (Enclosure.sfrac Bool.false 19 1))

noncomputable abbrev qz61 := (@HMul.hMul Real Real Real qz268 qz279 qz564)

noncomputable def ep331 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz349 qz7) (Complex.mk (@HMul.hMul Real Real Real qz0 qz60 (Real.cos qz61)) (@HMul.hMul Real Real Real qz0 qz60 (@Neg.neg Real Real.instNeg (Real.sin qz61)))) Bool.false 178381955829 1099511627776 3827056104997 19403081695363072 Bool.true 89172575151 549755813888 1913526702503 9701540847681536 (BSN.cpow_neg_s_mk qz13 119766 1000 19 qz14 rfl)

noncomputable abbrev qz358 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 19) qz15)

noncomputable def ep332 := @Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 19)) 4570637 1048576 1 1048576 120279 120280 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 19)) (Real.sqrt qz358) Bool.false 4570637 1048576 1 1048576 (BSN.sqrt_natCast_div_one 19) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz358) Bool.false 4570637 1048576 1 1048576 4570637 1048576 1 1048576 (BSN.sqrt_enclosure 19 1 2285318 2285319 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep333 := BSN.log_dyadic_bound 3 35 3 2 22509375 524288 141176 55368 243 90099 38 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 3) (BSN.artanhQ 35) 0 2 55368 22509375 243 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep334 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz564 119766 1000 0 1 3315143513283831 1125899906842624 31250000017647 4411750000000000000 198520739005975651773 562949953421312000 1871343751056755301 2205875000000000000000 qz19 (BSN.isNear_log_sfrac 19 1 3315143513283831 1125899906842624 31250000017647 4411750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz358) Bool.false 55618878793361701994496 18889465931478580854784 1000000000564704 141176000000000000000 3315143513283831 1125899906842624 31250000017647 4411750000000000000 (BSN.log_rat_reduce_isNear 19 1 4 38 32 90099 524288 24973259072661432 36028797018963968 141176 1000000000000000 rfl rfl rfl rfl (ep333 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep335 := nat_lit 289052922803984641674812941190621395515188316903635885852086635480671865569536

noncomputable def ep336 := nat_lit 65418508876246946984543686722189837800525990414239400657873113556648755456

noncomputable def ep337 := nat_lit 867027931394201431130469736198419806869963898730079178754944160214902299197696

noncomputable def ep338 := BSN.cos_dyadic_bound_f 1686407714 2147483648 3 2 1048576 282628 ep335 ep58 ep336 ep337 ep61 ep336 741531 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1686407714) qz16 0 2 ep335 ep58 ep336 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1686407714) qz282 0 2 ep337 ep61 ep336 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz359 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 369773691) qz17)

noncomputable def ep339 := @Enclosure.Real.IsNear.cos_image qz61 qz359 Bool.false 369773691 1048576 891 1048576 Bool.false 741531 1048576 1 141176 (@Enclosure.Real.IsNear.recentre' qz61 Bool.false 198520739005975651773 562949953421312000 1871343751056755301 2205875000000000000000 369773691 1048576 891 1048576 (ep334 rfl) rfl) (Enclosure.sfrac_false_div 369773691 1048576) (BSN.cos_reduce0 qz359 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 118670393059675715141632) qz20) 226375608064910080 72057594037927936 Bool.false 741531 1048576 56 1000000000000000 282352 141176 (BSN.sin_reduce_arg_pos_rat_q0 369773691 1048576 226375608064910080 72057594037927936 56 118670393059675715141632 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 741531 1048576 118670393059675715141632 151115727451828646838272 1686407714 2147483648 282628 282352 (ep338 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep340 := nat_lit 8088170922788844413834792796243993616

noncomputable def ep341 := BSN.sin_dyadic_bound_f 1686407714 2147483648 2 1 1048576 282628 ep340 ep144 ep340 ep340 ep145 ep340 741378 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1686407714) qz21 0 1 ep340 ep144 ep340 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1686407714) qz285 0 1 ep340 ep145 ep340 rfl rfl rfl rfl) rfl rfl

noncomputable def ep342 := @Enclosure.Real.IsNear.sin_image qz61 qz359 Bool.false 369773691 1048576 891 1048576 Bool.false 741378 1048576 1 141176 (@Enclosure.Real.IsNear.recentre' qz61 Bool.false 198520739005975651773 562949953421312000 1871343751056755301 2205875000000000000000 369773691 1048576 891 1048576 (ep334 rfl) rfl) (Enclosure.sfrac_false_div 369773691 1048576) (BSN.sin_reduce0 qz359 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 118670393059675715141632) qz20) 226375608064910080 72057594037927936 Bool.false 741378 1048576 56 1000000000000000 282352 141176 (BSN.sin_reduce_arg_pos_rat_q0 369773691 1048576 226375608064910080 72057594037927936 56 118670393059675715141632 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 741378 1048576 118670393059675715141632 151115727451828646838272 1686407714 2147483648 282628 282352 (ep341 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz360 := (@Enclosure.Real.IsNear.recentre' qz60 Bool.false 240559 1048576 1 1048576 240559 1048576 1 1048576 (ep332 rfl rfl) rfl)

noncomputable def ep343 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz60 (Real.cos qz61)) (@HMul.hMul Real Real Real qz0 qz60 (@Neg.neg Real Real.instNeg (Real.sin qz61))) Bool.false 178381955829 1099511627776 3827056104997 19403081695363072 Bool.true 89172575151 549755813888 1913526702503 9701540847681536 (@Enclosure.Real.IsNear.mulLit_ff qz60 (Real.cos qz61) 240559 1048576 1 1048576 741531 1048576 15854549 18504220672 178381955829 1099511627776 3827056104997 19403081695363072 qz360 (@Enclosure.Real.IsNear.recentre' (Real.cos qz61) Bool.false 741531 1048576 126836392 148033765376 741531 1048576 15854549 18504220672 (ep339 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz60 (@Neg.neg Real Real.instNeg (Real.sin qz61)) 240559 1048576 1 1048576 370689 524288 15854549 18504220672 89172575151 549755813888 1913526702503 9701540847681536 qz360 (@Enclosure.Real.IsNear.neg (Real.sin qz61) Bool.false 370689 524288 15854549 18504220672 (@Enclosure.Real.IsNear.recentre' (Real.sin qz61) Bool.false 741378 1048576 126836392 148033765376 370689 524288 15854549 18504220672 (ep342 rfl rfl) rfl)) rfl)

noncomputable def ep344 := @ep304 178381955829 1099511627776 3827056104997 19403081695363072 Bool.true 89172575151 549755813888 1913526702503 9701540847681536 Bool.false 690413938331026704039936 2511711275769 1099511627776 106100951635429 19403081695363072 Bool.true 45940730775067057717248 83565702471 1099511627776 106105400161777 19403081695363072 (ep305 (BSN.head_sum_c_succ qz5 18 19 rfl rfl) (ep330 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep331 ep343) rfl rfl

noncomputable abbrev qz62 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 20)))

noncomputable abbrev qz565 := (Real.log (Enclosure.sfrac Bool.false 20 1))

noncomputable abbrev qz63 := (@HMul.hMul Real Real Real qz268 qz279 qz565)

noncomputable def ep345 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz348 qz7) (Complex.mk (@HMul.hMul Real Real Real qz0 qz62 (Real.cos qz63)) (@HMul.hMul Real Real Real qz0 qz62 (@Neg.neg Real Real.instNeg (Real.sin qz63)))) Bool.false 196436017979 1099511627776 3728062909717 19403081695363072 Bool.true 147848413923 1099511627776 3724406027789 19403081695363072 (BSN.cpow_neg_s_mk qz13 119766 1000 20 qz14 rfl)

noncomputable abbrev qz361 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 20) qz15)

noncomputable def ep346 := @Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 20)) 4689375 1048576 1 1048576 117234 117235 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 20)) (Real.sqrt qz361) Bool.false 4689375 1048576 1 1048576 (BSN.sqrt_natCast_div_one 20) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz361) Bool.false 4689375 1048576 1 1048576 4689375 1048576 1 1048576 (BSN.sqrt_enclosure 20 1 2344687 2344688 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep347 := BSN.log_dyadic_bound 4 36 3 2 25194240 524288 141176 104448 768 116991 40 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 4) (BSN.artanhQ 36) 0 2 104448 25194240 768 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep348 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz565 119766 1000 0 1 3372893643545847 1125899906842624 31250000017647 4411750000000000000 201978990056455955901 562949953421312000 1871343751056755301 2205875000000000000000 qz19 (BSN.isNear_log_sfrac 20 1 3372893643545847 1125899906842624 31250000017647 4411750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz361) Bool.false 56587765202795681021952 18889465931478580854784 1000000000564704 141176000000000000000 3372893643545847 1125899906842624 31250000017647 4411750000000000000 (BSN.log_rat_reduce_isNear 20 1 4 40 32 116991 524288 24973259072661432 36028797018963968 141176 1000000000000000 rfl rfl rfl rfl (ep347 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep349 := nat_lit 3685454296884579714557913647662410000

noncomputable def ep350 := BSN.cos_dyadic_bound_f 1385551770 2147483648 2 1 1048576 282628 ep349 ep140 ep349 ep349 ep141 ep349 837791 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1385551770) qz16 0 1 ep349 ep140 ep349 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1385551770) qz282 0 1 ep349 ep141 ep349 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz362 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 188107593) qz34)

noncomputable def ep351 := @Enclosure.Real.IsNear.cos_image qz63 qz362 Bool.false 188107593 524288 445 524288 Bool.false 837791 1048576 1 141176 (@Enclosure.Real.IsNear.recentre' qz63 Bool.false 201978990056455955901 562949953421312000 1871343751056755301 2205875000000000000000 188107593 524288 445 524288 (ep348 rfl) rfl) (Enclosure.sfrac_false_div 188107593 524288) (BSN.cos_reduce0 qz362 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 48749769032638163582976) qz35) 226375608064910080 72057594037927936 Bool.false 837791 1048576 57 1000000000000000 282352 141176 (BSN.sin_reduce_arg_pos_rat_q0 188107593 524288 226375608064910080 72057594037927936 57 48749769032638163582976 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 837791 1048576 48749769032638163582976 75557863725914323419136 1385551770 2147483648 282628 282352 (ep350 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep352 := BSN.sin_dyadic_bound_f 1385551770 2147483648 2 1 1048576 282628 ep349 ep144 ep349 ep349 ep145 ep349 630567 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1385551770) qz21 0 1 ep349 ep144 ep349 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1385551770) qz285 0 1 ep349 ep145 ep349 rfl rfl rfl rfl) rfl rfl

noncomputable def ep353 := @Enclosure.Real.IsNear.sin_image qz63 qz362 Bool.false 188107593 524288 445 524288 Bool.false 630567 1048576 1 141176 (@Enclosure.Real.IsNear.recentre' qz63 Bool.false 201978990056455955901 562949953421312000 1871343751056755301 2205875000000000000000 188107593 524288 445 524288 (ep348 rfl) rfl) (Enclosure.sfrac_false_div 188107593 524288) (BSN.sin_reduce0 qz362 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 48749769032638163582976) qz35) 226375608064910080 72057594037927936 Bool.false 630567 1048576 57 1000000000000000 282352 141176 (BSN.sin_reduce_arg_pos_rat_q0 188107593 524288 226375608064910080 72057594037927936 57 48749769032638163582976 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 630567 1048576 48749769032638163582976 75557863725914323419136 1385551770 2147483648 282628 282352 (ep352 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz363 := (@Enclosure.Real.IsNear.recentre' qz62 Bool.false 234469 1048576 1 1048576 234469 1048576 1 1048576 (ep346 rfl rfl) rfl)

noncomputable def ep354 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz62 (Real.cos qz63)) (@HMul.hMul Real Real Real qz0 qz62 (@Neg.neg Real Real.instNeg (Real.sin qz63))) Bool.false 196436017979 1099511627776 3728062909717 19403081695363072 Bool.true 147848413923 1099511627776 3724406027789 19403081695363072 (@Enclosure.Real.IsNear.mulLit_ff qz62 (Real.cos qz63) 234469 1048576 1 1048576 837791 1048576 7918451 9252110336 196436017979 1099511627776 3728062909717 19403081695363072 qz363 (@Enclosure.Real.IsNear.recentre' (Real.cos qz63) Bool.false 837791 1048576 63347608 74016882688 837791 1048576 7918451 9252110336 (ep351 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz62 (@Neg.neg Real Real.instNeg (Real.sin qz63)) 234469 1048576 1 1048576 630567 1048576 7918451 9252110336 147848413923 1099511627776 3724406027789 19403081695363072 qz363 (@Enclosure.Real.IsNear.neg (Real.sin qz63) Bool.false 630567 1048576 7918451 9252110336 (@Enclosure.Real.IsNear.recentre' (Real.sin qz63) Bool.false 630567 1048576 63347608 74016882688 630567 1048576 7918451 9252110336 (ep353 rfl rfl) rfl)) rfl)

noncomputable def ep355 := @ep301 196436017979 1099511627776 3728062909717 19403081695363072 Bool.true 147848413923 1099511627776 3724406027789 19403081695363072 Bool.false ep302 677036823437 274877906944 54914507272573 9701540847681536 Bool.true 254442511806711667359744 115707058197 549755813888 54914903094783 9701540847681536 (ep303 (BSN.head_sum_c_succ qz5 19 20 rfl rfl) (ep344 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep345 ep354) rfl rfl

noncomputable abbrev qz64 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 21)))

noncomputable abbrev qz566 := (Real.log (Enclosure.sfrac Bool.false 21 1))

noncomputable abbrev qz65 := (@HMul.hMul Real Real Real qz268 qz279 qz566)

noncomputable def ep356 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz347 qz7) (Complex.mk (@HMul.hMul Real Real Real qz0 qz64 (Real.cos qz65)) (@HMul.hMul Real Real Real qz0 qz64 (@Neg.neg Real Real.instNeg (Real.sin qz65)))) Bool.false 117444842815 549755813888 1832034214235 9701540847681536 Bool.true 12233639961 274877906944 113605806451 606346302980096 (BSN.cpow_neg_s_mk qz13 119766 1000 21 qz14 rfl)

noncomputable abbrev qz364 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 21) qz15)

noncomputable def ep357 := @Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 21)) 4805179 1048576 1 1048576 114408 114410 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 21)) (Real.sqrt qz364) Bool.false 4805179 1048576 1 1048576 (BSN.sqrt_natCast_div_one 21) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz364) Bool.false 4805179 1048576 1 1048576 4805179 1048576 1 1048576 (BSN.sqrt_enclosure 21 1 2402589 2402590 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep358 := BSN.log_dyadic_bound 5 37 3 2 28112415 524288 141176 173000 1875 142571 42 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 5) (BSN.artanhQ 37) 0 2 173000 28112415 1875 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep359 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz566 119766 1000 0 1 3427826275261687 1125899906842624 31250000017647 4411750000000000000 205268520841495602621 562949953421312000 1871343751056755301 2205875000000000000000 qz19 (BSN.isNear_log_sfrac 21 1 3427826275261687 1125899906842624 31250000017647 4411750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz364) Bool.false 57509381830540779323392 18889465931478580854784 1000000000564704 141176000000000000000 3427826275261687 1125899906842624 31250000017647 4411750000000000000 (BSN.log_rat_reduce_isNear 21 1 4 42 32 142571 524288 24973259072661432 36028797018963968 141176 1000000000000000 rfl rfl rfl rfl (ep358 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep360 := nat_lit 37849285334738490314664559674538561

noncomputable def ep361 := BSN.cos_dyadic_bound_f 441077009 2147483648 2 1 1048576 282628 ep360 ep140 ep360 ep360 ep141 ep360 1026535 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 441077009) qz16 0 1 ep360 ep140 ep360 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 441077009) qz282 0 1 ep360 ep141 ep360 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz365 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 191171207) qz34)

noncomputable def ep362 := @Enclosure.Real.IsNear.cos_image qz65 qz365 Bool.false 191171207 524288 891 1048576 Bool.false 1026535 1048576 1 141176 (@Enclosure.Real.IsNear.recentre' qz65 Bool.false 205268520841495602621 562949953421312000 1871343751056755301 2205875000000000000000 191171207 524288 891 1048576 (ep359 rfl) rfl) (Enclosure.sfrac_false_div 191171207 524288) (BSN.cos_reduce0 qz365 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 15519017629920970932224) qz35) 226375608064910080 72057594037927936 Bool.false 1026535 1048576 58 1000000000000000 282352 141176 (BSN.sin_reduce_arg_pos_rat_q0 191171207 524288 226375608064910080 72057594037927936 58 15519017629920970932224 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1026535 1048576 15519017629920970932224 75557863725914323419136 441077009 2147483648 282628 282352 (ep361 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep363 := BSN.sin_dyadic_bound_f 441077009 2147483648 2 1 1048576 282628 ep360 ep144 ep360 ep360 ep145 ep360 213858 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 441077009) qz21 0 1 ep360 ep144 ep360 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 441077009) qz285 0 1 ep360 ep145 ep360 rfl rfl rfl rfl) rfl rfl

noncomputable def ep364 := @Enclosure.Real.IsNear.sin_image qz65 qz365 Bool.false 191171207 524288 891 1048576 Bool.false 213858 1048576 1 141176 (@Enclosure.Real.IsNear.recentre' qz65 Bool.false 205268520841495602621 562949953421312000 1871343751056755301 2205875000000000000000 191171207 524288 891 1048576 (ep359 rfl) rfl) (Enclosure.sfrac_false_div 191171207 524288) (BSN.sin_reduce0 qz365 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 15519017629920970932224) qz35) 226375608064910080 72057594037927936 Bool.false 213858 1048576 58 1000000000000000 282352 141176 (BSN.sin_reduce_arg_pos_rat_q0 191171207 524288 226375608064910080 72057594037927936 58 15519017629920970932224 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 213858 1048576 15519017629920970932224 75557863725914323419136 441077009 2147483648 282628 282352 (ep363 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz366 := (@Enclosure.Real.IsNear.recentre' qz64 Bool.false 228818 1048576 2 1048576 114409 524288 1 524288 (ep357 rfl rfl) rfl)

noncomputable def ep365 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz64 (Real.cos qz65)) (@HMul.hMul Real Real Real qz0 qz64 (@Neg.neg Real Real.instNeg (Real.sin qz65))) Bool.false 117444842815 549755813888 1832034214235 9701540847681536 Bool.true 12233639961 274877906944 113605806451 606346302980096 (@Enclosure.Real.IsNear.mulLit_ff qz64 (Real.cos qz65) 114409 524288 1 524288 1026535 1048576 15854549 18504220672 117444842815 549755813888 1832034214235 9701540847681536 qz366 (@Enclosure.Real.IsNear.recentre' (Real.cos qz65) Bool.false 1026535 1048576 126836392 148033765376 1026535 1048576 15854549 18504220672 (ep362 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz64 (@Neg.neg Real Real.instNeg (Real.sin qz65)) 114409 524288 1 524288 106929 524288 15854549 18504220672 12233639961 274877906944 113605806451 606346302980096 qz366 (@Enclosure.Real.IsNear.neg (Real.sin qz65) Bool.false 106929 524288 15854549 18504220672 (@Enclosure.Real.IsNear.recentre' (Real.sin qz65) Bool.false 213858 1048576 126836392 148033765376 106929 524288 15854549 18504220672 (ep364 rfl rfl) rfl)) rfl)

noncomputable def ep366 := @ep299 117444842815 549755813888 1832034214235 9701540847681536 Bool.true 12233639961 274877906944 113605806451 606346302980096 Bool.false 404487922475108365500416 1471518489689 549755813888 7093317685851 1212692605960192 Bool.true 38530828669411273998336 140174338119 549755813888 56732595997999 9701540847681536 (ep300 (BSN.head_sum_c_succ qz5 20 21 rfl rfl) (ep355 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep356 ep365) rfl rfl

noncomputable abbrev qz66 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 22)))

noncomputable abbrev qz567 := (Real.log (Enclosure.sfrac Bool.false 22 1))

noncomputable abbrev qz67 := (@HMul.hMul Real Real Real qz268 qz279 qz567)

noncomputable def ep367 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz346 qz7) (Complex.mk (@HMul.hMul Real Real Real qz0 qz66 (Real.cos qz67)) (@HMul.hMul Real Real Real qz0 qz66 (@Neg.neg Real Real.instNeg (Real.sin qz67)))) Bool.false 51253348491 274877906944 444581169245 2425385211920384 Bool.false 113668674435 1099511627776 3549438842701 19403081695363072 (BSN.cpow_neg_s_mk qz13 119766 1000 22 qz14 rfl)

noncomputable abbrev qz367 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 22) qz15)

noncomputable def ep368 := @Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 22)) 4918257 1048576 1 1048576 111778 111779 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 22)) (Real.sqrt qz367) Bool.false 4918257 1048576 1 1048576 (BSN.sqrt_natCast_div_one 22) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz367) Bool.false 4918257 1048576 1 1048576 4918257 1048576 1 1048576 (BSN.sqrt_enclosure 22 1 2459128 2459129 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep369 := BSN.log_dyadic_bound 6 38 4 3 316148320320 524288 141176 2667271104 699840 166961 44 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 6) (BSN.artanhQ 38) 0 3 2667271104 316148320320 699840 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep370 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz567 119766 1000 0 1 3480203401436407 1125899906842624 31250000017647 4411750000000000000 208405020288216360381 562949953421312000 1871343751056755301 2205875000000000000000 qz19 (BSN.isNear_log_sfrac 22 1 3480203401436407 1125899906842624 31250000017647 4411750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz367) Bool.false 58388124189833310502912 18889465931478580854784 1000000000564704 141176000000000000000 3480203401436407 1125899906842624 31250000017647 4411750000000000000 (BSN.log_rat_reduce_isNear 22 1 4 44 32 166961 524288 24973259072661432 36028797018963968 141176 1000000000000000 rfl rfl rfl rfl (ep369 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep371 := nat_lit 1757370161847636628097485830519487821745970596858994526527324786062772762101345

noncomputable def ep372 := nat_lit 746028110128582017056581391972147466512710616984433893395299591658476455521

noncomputable def ep373 := nat_lit 4601428283136935369370561757678322722960330984107963247934639192730291129337441

noncomputable def ep374 := BSN.sin_dyadic_bound_f 2286095659 2147483648 3 2 1048576 282628 ep371 ep65 ep372 ep373 ep67 ep372 917052 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2286095659) qz21 0 2 ep371 ep65 ep372 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2286095659) qz285 0 2 ep373 ep67 ep372 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz568 := (@Nat.cast Real Real.instNatCast 131072)

noncomputable abbrev qz368 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 48523075) qz568)

noncomputable abbrev qz369 := (@Nat.cast Real Real.instNatCast 18889465931478580854784)

noncomputable def ep375 := @Enclosure.Real.IsNear.cos_image qz67 qz368 Bool.false 48523075 131072 445 524288 Bool.false 917052 1048576 1 141176 (@Enclosure.Real.IsNear.recentre' qz67 Bool.false 208405020288216360381 562949953421312000 1871343751056755301 2205875000000000000000 48523075 131072 445 524288 (ep370 rfl) rfl) (Enclosure.sfrac_false_div 48523075 131072) (BSN.cos_reduce3 qz368 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 20108710077145074892800) qz369) 226375608064910080 72057594037927936 Bool.false 917052 1048576 58 1000000000000000 282352 141176 (BSN.sin_reduce_arg_pos_rat_q3 48523075 131072 226375608064910080 72057594037927936 58 20108710077145074892800 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 917052 1048576 20108710077145074892800 18889465931478580854784 2286095659 2147483648 282628 282352 (ep374 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep376 := nat_lit 976648324630966385395072830907258633177322647418101152023356125408944190703201

noncomputable def ep377 := nat_lit 2928452917672641992151105329937831604598942521020334588283277777043515619198561

noncomputable def ep378 := BSN.cos_dyadic_bound_f 2286095659 2147483648 3 2 1048576 282628 ep376 ep58 ep372 ep377 ep61 ep372 508455 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2286095659) qz16 0 2 ep376 ep58 ep372 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2286095659) qz282 0 2 ep377 ep61 ep372 rfl rfl rfl rfl) rfl rfl

noncomputable def ep379 := @Enclosure.Real.IsNear.sin_image qz67 qz368 Bool.false 48523075 131072 445 524288 Bool.true 508455 1048576 1 141176 (@Enclosure.Real.IsNear.recentre' qz67 Bool.false 208405020288216360381 562949953421312000 1871343751056755301 2205875000000000000000 48523075 131072 445 524288 (ep370 rfl) rfl) (Enclosure.sfrac_false_div 48523075 131072) (BSN.sin_reduce3 qz368 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 20108710077145074892800) qz369) 226375608064910080 72057594037927936 Bool.false 508455 1048576 58 1000000000000000 282352 141176 (BSN.sin_reduce_arg_pos_rat_q3 48523075 131072 226375608064910080 72057594037927936 58 20108710077145074892800 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 508455 1048576 20108710077145074892800 18889465931478580854784 2286095659 2147483648 282628 282352 (ep378 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz370 := (@Enclosure.Real.IsNear.recentre' qz66 Bool.false 223557 1048576 1 1048576 223557 1048576 1 1048576 (ep368 rfl rfl) rfl)

noncomputable def ep380 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz66 (Real.cos qz67)) (@HMul.hMul Real Real Real qz0 qz66 (@Neg.neg Real Real.instNeg (Real.sin qz67))) Bool.false 51253348491 274877906944 444581169245 2425385211920384 Bool.false 113668674435 1099511627776 3549438842701 19403081695363072 (@Enclosure.Real.IsNear.mulLit_ff qz66 (Real.cos qz67) 223557 1048576 1 1048576 229263 262144 7918451 9252110336 51253348491 274877906944 444581169245 2425385211920384 qz370 (@Enclosure.Real.IsNear.recentre' (Real.cos qz67) Bool.false 917052 1048576 63347608 74016882688 229263 262144 7918451 9252110336 (ep375 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz66 (@Neg.neg Real Real.instNeg (Real.sin qz67)) 223557 1048576 1 1048576 508455 1048576 7918451 9252110336 113668674435 1099511627776 3549438842701 19403081695363072 qz370 (@Enclosure.Real.IsNear.neg (Real.sin qz67) Bool.true 508455 1048576 7918451 9252110336 (@Enclosure.Real.IsNear.recentre' (Real.sin qz67) Bool.true 508455 1048576 63347608 74016882688 508455 1048576 7918451 9252110336 (ep379 rfl rfl) rfl)) rfl)

noncomputable def ep381 := @ep297 51253348491 274877906944 444581169245 2425385211920384 Bool.false 113668674435 1099511627776 3549438842701 19403081695363072 Bool.false 432664748789263367143424 1574025186671 549755813888 14631216540947 2425385211920384 Bool.true 91633300050061572440064 166680001803 1099511627776 117014630838699 19403081695363072 (ep298 (BSN.head_sum_c_succ qz5 21 22 rfl rfl) (ep366 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep367 ep380) rfl rfl

noncomputable abbrev qz68 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 23)))

noncomputable abbrev qz569 := (Real.log (Enclosure.sfrac Bool.false 23 1))

noncomputable abbrev qz69 := (@HMul.hMul Real Real Real qz268 qz279 qz569)

noncomputable def ep382 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz345 qz7) (Complex.mk (@HMul.hMul Real Real Real qz0 qz68 (Real.cos qz69)) (@HMul.hMul Real Real Real qz0 qz68 (@Neg.neg Real Real.instNeg (Real.sin qz69)))) Bool.false 12019898925 549755813888 1732291944269 9701540847681536 Bool.false 227999827185 1099511627776 3481045804253 19403081695363072 (BSN.cpow_neg_s_mk qz13 119766 1000 23 qz14 rfl)

noncomputable abbrev qz371 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 23) qz15)

noncomputable def ep383 := @Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 23)) 5028793 1048576 1 1048576 109321 109322 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 23)) (Real.sqrt qz371) Bool.false 5028793 1048576 1 1048576 (BSN.sqrt_natCast_div_one 23) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz371) Bool.false 5028793 1048576 1 1048576 5028793 1048576 1 1048576 (BSN.sqrt_enclosure 23 1 2514396 2514397 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep384 := BSN.log_dyadic_bound 7 39 4 3 369468094905 524288 141176 4046006391 1764735 190266 46 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 7) (BSN.artanhQ 39) 0 3 4046006391 369468094905 1764735 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep385 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz569 119766 1000 0 1 3530250507853047 1125899906842624 31250000017647 4411750000000000000 211401991161764013501 562949953421312000 1871343751056755301 2205875000000000000000 qz19 (BSN.isNear_log_sfrac 23 1 3530250507853047 1125899906842624 31250000017647 4411750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz371) Bool.false 59227775304360265777152 18889465931478580854784 1000000000564704 141176000000000000000 3530250507853047 1125899906842624 31250000017647 4411750000000000000 (BSN.log_rat_reduce_isNear 23 1 4 46 32 190266 524288 24973259072661432 36028797018963968 141176 1000000000000000 rfl rfl rfl rfl (ep384 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep386 := BSN.sin_dyadic_bound_f 225594018 2147483648 1 0 1048576 282628 0 1 1 0 1 1 109950 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 225594018) qz21 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 225594018) qz285 0 0 rfl) rfl rfl

noncomputable abbrev qz372 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 393766893) qz17)

noncomputable def ep387 := @Enclosure.Real.IsNear.cos_image qz69 qz372 Bool.false 393766893 1048576 445 524288 Bool.false 109950 1048576 1 141176 (@Enclosure.Real.IsNear.recentre' qz69 Bool.false 211401991161764013501 562949953421312000 1871343751056755301 2205875000000000000000 393766893 1048576 445 524288 (ep385 rfl) rfl) (Enclosure.sfrac_false_div 393766893 1048576) (BSN.cos_reduce3 qz372 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 15874767797609694232576) qz20) 226375608064910080 72057594037927936 Bool.false 109950 1048576 59 1000000000000000 282352 141176 (BSN.sin_reduce_arg_pos_rat_q3 393766893 1048576 226375608064910080 72057594037927936 59 15874767797609694232576 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 109950 1048576 15874767797609694232576 151115727451828646838272 225594018 2147483648 282628 282352 (ep386 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep388 := nat_lit 2590062939323270697908423840936976

noncomputable def ep389 := BSN.cos_dyadic_bound_f 225594018 2147483648 2 1 1048576 282628 ep388 ep140 ep388 ep388 ep141 ep388 1042795 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 225594018) qz16 0 1 ep388 ep140 ep388 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 225594018) qz282 0 1 ep388 ep141 ep388 rfl rfl rfl rfl) rfl rfl

noncomputable def ep390 := @Enclosure.Real.IsNear.sin_image qz69 qz372 Bool.false 393766893 1048576 445 524288 Bool.true 1042795 1048576 1 141176 (@Enclosure.Real.IsNear.recentre' qz69 Bool.false 211401991161764013501 562949953421312000 1871343751056755301 2205875000000000000000 393766893 1048576 445 524288 (ep385 rfl) rfl) (Enclosure.sfrac_false_div 393766893 1048576) (BSN.sin_reduce3 qz372 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 15874767797609694232576) qz20) 226375608064910080 72057594037927936 Bool.false 1042795 1048576 59 1000000000000000 282352 141176 (BSN.sin_reduce_arg_pos_rat_q3 393766893 1048576 226375608064910080 72057594037927936 59 15874767797609694232576 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1042795 1048576 15874767797609694232576 151115727451828646838272 225594018 2147483648 282628 282352 (ep389 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz373 := (@Enclosure.Real.IsNear.recentre' qz68 Bool.false 218643 1048576 1 1048576 218643 1048576 1 1048576 (ep383 rfl rfl) rfl)

noncomputable def ep391 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz68 (Real.cos qz69)) (@HMul.hMul Real Real Real qz0 qz68 (@Neg.neg Real Real.instNeg (Real.sin qz69))) Bool.false 12019898925 549755813888 1732291944269 9701540847681536 Bool.false 227999827185 1099511627776 3481045804253 19403081695363072 (@Enclosure.Real.IsNear.mulLit_ff qz68 (Real.cos qz69) 218643 1048576 1 1048576 54975 524288 7918451 9252110336 12019898925 549755813888 1732291944269 9701540847681536 qz373 (@Enclosure.Real.IsNear.recentre' (Real.cos qz69) Bool.false 109950 1048576 63347608 74016882688 54975 524288 7918451 9252110336 (ep387 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz68 (@Neg.neg Real Real.instNeg (Real.sin qz69)) 218643 1048576 1 1048576 1042795 1048576 7918451 9252110336 227999827185 1099511627776 3481045804253 19403081695363072 qz373 (@Enclosure.Real.IsNear.neg (Real.sin qz69) Bool.true 1042795 1048576 7918451 9252110336 (@Enclosure.Real.IsNear.recentre' (Real.sin qz69) Bool.true 1042795 1048576 63347608 74016882688 1042795 1048576 7918451 9252110336 (ep390 rfl rfl) rfl)) rfl)

noncomputable def ep392 := @ep295 12019898925 549755813888 1732291944269 9701540847681536 Bool.false 227999827185 1099511627776 3481045804253 19403081695363072 Bool.false 871937506894891605557248 396511271399 137438953472 60257158108057 9701540847681536 Bool.false 67421861020702901010432 30659912691 549755813888 15061959580369 2425385211920384 (ep296 (BSN.head_sum_c_succ qz5 22 23 rfl rfl) (ep381 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep382 ep391) rfl rfl

noncomputable abbrev qz70 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 24)))

noncomputable abbrev qz570 := (Real.log (Enclosure.sfrac Bool.false 24 1))

noncomputable abbrev qz71 := (@HMul.hMul Real Real Real qz268 qz279 qz570)

noncomputable def ep393 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz344 qz7) (Complex.mk (@HMul.hMul Real Real Real qz0 qz70 (Real.cos qz71)) (@HMul.hMul Real Real Real qz0 qz70 (@Neg.neg Real Real.instNeg (Real.sin qz71)))) Bool.true 198030381073 1099511627776 3406057632009 19403081695363072 Bool.false 26404921235 274877906944 849609648175 4850770423840768 (BSN.cpow_neg_s_mk qz13 119766 1000 24 qz14 rfl)

noncomputable abbrev qz374 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 24) qz15)

noncomputable def ep394 := @Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 24)) 5136953 1048576 1 1048576 107019 107020 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 24)) (Real.sqrt qz374) Bool.false 5136953 1048576 1 1048576 (BSN.sqrt_natCast_div_one 24) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz374) Bool.false 5136953 1048576 1 1048576 5136953 1048576 1 1048576 (BSN.sqrt_enclosure 24 1 2568476 2568477 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep395 := BSN.log_dyadic_bound 8 40 4 3 430080000000 524288 141176 5875957760 3932160 212580 48 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 8) (BSN.artanhQ 40) 0 3 5875957760 430080000000 3932160 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep396 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz570 119766 1000 0 1 3578169457974519 1125899906842624 31250000017647 4411750000000000000 214271521651888121277 562949953421312000 1871343751056755301 2205875000000000000000 qz19 (BSN.isNear_log_sfrac 24 1 3578169457974519 1125899906842624 31250000017647 4411750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz374) Bool.false 60031721881041427759104 18889465931478580854784 1000000000564704 141176000000000000000 3578169457974519 1125899906842624 31250000017647 4411750000000000000 (BSN.log_rat_reduce_isNear 24 1 4 48 32 212580 524288 24973259072661432 36028797018963968 141176 1000000000000000 rfl rfl rfl rfl (ep395 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep397 := nat_lit 1225752232608515945150537312578519296

noncomputable def ep398 := BSN.cos_dyadic_bound_f 1052205756 2147483648 2 1 1048576 282628 ep397 ep140 ep397 ep397 ep141 ep397 925207 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1052205756) qz16 0 1 ep397 ep140 ep397 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1052205756) qz282 0 1 ep397 ep141 ep397 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz375 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 199555905) qz34)

noncomputable def ep399 := @Enclosure.Real.IsNear.cos_image qz71 qz375 Bool.false 199555905 524288 445 524288 Bool.true 925207 1048576 1 141176 (@Enclosure.Real.IsNear.recentre' qz71 Bool.false 214271521651888121277 562949953421312000 1871343751056755301 2205875000000000000000 199555905 524288 445 524288 (ep396 rfl) rfl) (Enclosure.sfrac_false_div 199555905 524288) (BSN.cos_reduce2 qz375 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 37021198847817788948480) qz35) 226375608064910080 72057594037927936 Bool.false 925207 1048576 60 1000000000000000 282352 141176 (BSN.sin_reduce_arg_pos_rat_q2 199555905 524288 226375608064910080 72057594037927936 60 37021198847817788948480 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 925207 1048576 37021198847817788948480 75557863725914323419136 1052205756 2147483648 282628 282352 (ep398 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep400 := BSN.sin_dyadic_bound_f 1052205756 2147483648 2 1 1048576 282628 ep397 ep144 ep397 ep397 ep145 ep397 493460 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1052205756) qz21 0 1 ep397 ep144 ep397 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1052205756) qz285 0 1 ep397 ep145 ep397 rfl rfl rfl rfl) rfl rfl

noncomputable def ep401 := @Enclosure.Real.IsNear.sin_image qz71 qz375 Bool.false 199555905 524288 445 524288 Bool.true 493460 1048576 1 141176 (@Enclosure.Real.IsNear.recentre' qz71 Bool.false 214271521651888121277 562949953421312000 1871343751056755301 2205875000000000000000 199555905 524288 445 524288 (ep396 rfl) rfl) (Enclosure.sfrac_false_div 199555905 524288) (BSN.sin_reduce2 qz375 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 37021198847817788948480) qz35) 226375608064910080 72057594037927936 Bool.false 493460 1048576 60 1000000000000000 282352 141176 (BSN.sin_reduce_arg_pos_rat_q2 199555905 524288 226375608064910080 72057594037927936 60 37021198847817788948480 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 493460 1048576 37021198847817788948480 75557863725914323419136 1052205756 2147483648 282628 282352 (ep400 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz376 := (@Enclosure.Real.IsNear.recentre' qz70 Bool.false 214039 1048576 1 1048576 214039 1048576 1 1048576 (ep394 rfl rfl) rfl)

noncomputable def ep402 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz70 (Real.cos qz71)) (@HMul.hMul Real Real Real qz0 qz70 (@Neg.neg Real Real.instNeg (Real.sin qz71))) Bool.true 198030381073 1099511627776 3406057632009 19403081695363072 Bool.false 26404921235 274877906944 849609648175 4850770423840768 (@Enclosure.Real.IsNear.mulLit_ft qz70 (Real.cos qz71) 214039 1048576 1 1048576 925207 1048576 7918451 9252110336 198030381073 1099511627776 3406057632009 19403081695363072 qz376 (@Enclosure.Real.IsNear.recentre' (Real.cos qz71) Bool.true 925207 1048576 63347608 74016882688 925207 1048576 7918451 9252110336 (ep399 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz70 (@Neg.neg Real Real.instNeg (Real.sin qz71)) 214039 1048576 1 1048576 123365 262144 7918451 9252110336 26404921235 274877906944 849609648175 4850770423840768 qz376 (@Enclosure.Real.IsNear.neg (Real.sin qz71) Bool.true 123365 262144 7918451 9252110336 (@Enclosure.Real.IsNear.recentre' (Real.sin qz71) Bool.true 493460 1048576 63347608 74016882688 123365 262144 7918451 9252110336 (ep401 rfl rfl) rfl)) rfl)

noncomputable def ep403 := @ep293 198030381073 1099511627776 3406057632009 19403081695363072 Bool.false 26404921235 274877906944 849609648175 4850770423840768 Bool.false 408751665117111326343168 2974059790119 1099511627776 123920373848123 19403081695363072 Bool.false 22943991591783821737984 83469755161 549755813888 30973528808913 4850770423840768 (ep294 (BSN.head_sum_c_succ qz5 23 24 rfl rfl) (ep392 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep393 ep402) rfl rfl

theorem EMRow39.d8 : Enclosure.Complex.IsNear qz55 Bool.false 2974059790119 1099511627776 123920373848123 19403081695363072 Bool.false 83469755161 549755813888 30973528808913 4850770423840768 := ep292 (BSN.head_sum_c_succ qz5 24 25 rfl rfl) (ep403 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

theorem EMRow39.d9 : @Eq Nat (BSN.factNat (Nat.mul 2 1)) 2 := @Eq.refl Nat 2

theorem EMRow39.d10 : @Eq Nat (Nat.pow 30 1) 30 := @Eq.refl Nat 30

noncomputable def ep404 := nat_lit 407767748096107201513672372682443

noncomputable def ep405 := nat_lit 148839056589473405032363720704000

noncomputable def ep406 := nat_lit 76904559035837036587562619116667273539

noncomputable def ep407 := nat_lit 9270190857970582578172449031252554547200

noncomputable abbrev qz612 := (@instHMul Complex Complex.instMul)

noncomputable abbrev qz571 := qz612

noncomputable abbrev qz377 := qz571

noncomputable abbrev qz72 := qz377

noncomputable abbrev qz572 := (@instHSub Complex Complex.instSub)

noncomputable abbrev qz378 := qz572

noncomputable abbrev qz73 := qz378

noncomputable abbrev qz613 := (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (4 : Complex))

noncomputable abbrev qz614 := (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid))

noncomputable abbrev qz573 := (@HAdd.hAdd Complex Complex Complex qz610 (@HAdd.hAdd Complex Complex Complex qz610 qz613 (@HMul.hMul Complex Complex Complex qz612 Complex.I (@HDiv.hDiv Complex Complex Complex qz614 (↑qz611) (2 : Complex)))) (@Nat.cast Complex Complex.instNatCast 2))

noncomputable abbrev qz379 := qz573

noncomputable abbrev qz74 := (Complex.Stirling.logGammaStirling 1 qz379)

noncomputable abbrev qz574 := (@HAdd.hAdd Complex Complex Complex qz610 qz613 (@HMul.hMul Complex Complex Complex qz612 Complex.I (@HDiv.hDiv Complex Complex Complex qz614 (↑qz611) (2 : Complex))))

noncomputable abbrev qz380 := qz574

noncomputable abbrev qz75 := qz380

noncomputable abbrev qz76 := (@HMul.hMul Real Real Real qz268 (@HDiv.hDiv Real Real Real qz271 qz279 (2 : Real)) (Real.log Real.pi))

noncomputable abbrev qz381 := (@instHSub Real Real.instSub)

noncomputable def ep408 := Complex.re (@HMul.hMul Complex Complex Complex qz72 (Complex.exp (@HMul.hMul Complex Complex Complex qz72 Complex.I ↑(@HSub.hSub Real Real Real qz381 (Complex.im (@HSub.hSub Complex Complex Complex qz73 qz74 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz75 (@Nat.cast Complex Complex.instNatCast j))))) qz76))) (zetaApproximant qz5 1 30))

noncomputable def ep409 := @Enclosure.Real.IsNear.of_eq ep408 (@HSub.hSub Real Real Real qz381 (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz381 (Complex.im (@HSub.hSub Complex Complex Complex qz73 qz74 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz75 (@Nat.cast Complex Complex.instNatCast j))))) qz76)) (Complex.re (zetaApproximant qz5 1 30))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz381 (Complex.im (@HSub.hSub Complex Complex Complex qz73 qz74 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz75 (@Nat.cast Complex Complex.instNatCast j))))) qz76)) (Complex.im (zetaApproximant qz5 1 30))))

noncomputable def ep410 := nat_lit 5436889242010216776847266608689

noncomputable def ep411 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz381 (Complex.im (@HSub.hSub Complex Complex Complex qz73 qz74 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz75 (@Nat.cast Complex Complex.instNatCast j))))) qz76)) (Complex.re (zetaApproximant qz5 1 30))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz381 (Complex.im (@HSub.hSub Complex Complex Complex qz73 qz74 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz75 (@Nat.cast Complex Complex.instNatCast j))))) qz76)) (Complex.im (zetaApproximant qz5 1 30))) ep410

noncomputable def ep412 := nat_lit 1984520754526312067098182942720

noncomputable def ep413 := nat_lit 1919942370640984691394600936957710163643

noncomputable def ep414 := nat_lit 231754771449264564454311225781313863680000

noncomputable def ep415 := nat_lit 65934083808953132961064423

noncomputable def ep416 := nat_lit 9302441036842087814522732544000

noncomputable def ep417 := nat_lit 166975328433826455904033809935729677

noncomputable def ep418 := nat_lit 14484673215579035278394451611332116480000

noncomputable def ep419 := nat_lit 50576472445198863400573523230085043910656831362725487113666560

noncomputable def ep420 := @Enclosure.Real.IsNear.mulLit_tf (Real.cos (@HSub.hSub Real Real Real qz381 (Complex.im (@HSub.hSub Complex Complex Complex qz73 qz74 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz75 (@Nat.cast Complex Complex.instNatCast j))))) qz76)) (Complex.re (zetaApproximant qz5 1 30)) 1048575 1048576 3294937

noncomputable def ep421 := nat_lit 388876993205794776972124069

noncomputable def ep422 := nat_lit 141943985547517209083904000

noncomputable def ep423 := nat_lit 30501609214514077578513335189

noncomputable def ep424 := nat_lit 4174809188261726981172756480000

noncomputable def ep425 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HSub.hSub Real Real Real qz381 (Complex.im (@HSub.hSub Complex Complex Complex qz73 qz74 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz75 (@Nat.cast Complex Complex.instNatCast j))))) qz76)) Bool.true 1048575 1048576 26359496

noncomputable abbrev qz382 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 121885817) qz17)

noncomputable def ep426 := @Enclosure.Real.IsNear.cos_image (@HSub.hSub Real Real Real qz381 (Complex.im (@HSub.hSub Complex Complex Complex qz73 qz74 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz75 (@Nat.cast Complex Complex.instNatCast j))))) qz76) qz382 Bool.false 121885817 1048576 183

noncomputable def ep427 := nat_lit 1608767588403114284176267

noncomputable def ep428 := nat_lit 4626055168000000000000000000

noncomputable def ep429 := @Enclosure.Real.IsNear.recentre' (@HSub.hSub Real Real Real qz381 (Complex.im (@HSub.hSub Complex Complex Complex qz73 qz74 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz75 (@Nat.cast Complex Complex.instNatCast j))))) qz76) Bool.false 209398240314421494387 1801439850948198400 ep427 ep428

noncomputable def ep430 := @Enclosure.Real.IsNear.subLit_ff_p (Complex.im (@HSub.hSub Complex Complex Complex qz73 qz74 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz75 (@Nat.cast Complex Complex.instNatCast j))))) qz76 1664433300773256711231 9007199254740992000 552012287403114284176267 ep428 4492482543 65536000

noncomputable def ep431 := nat_lit 68615615386229635280732160000

noncomputable def ep432 := nat_lit 2313027584000000000000000000

noncomputable def ep433 := @Enclosure.Complex.IsNear.im_isNear (@HSub.hSub Complex Complex Complex qz73 qz74 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz75 (@Nat.cast Complex Complex.instNatCast j)))) Bool.true 424095897480856522673 4503599627370496000 512539363070849648779461 ep432 Bool.false 1664433300773256711231 9007199254740992000

noncomputable def ep434 := @Enclosure.Complex.IsNear.subLitP qz74 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz75 (@Nat.cast Complex Complex.instNatCast j))) Bool.true 387233883343275309673 4503599627370496000 504347363045406345355461 ep432 Bool.false 1692504671509049959231 9007199254740992000 519244287398488229008267

noncomputable def ep435 := nat_lit 1909958125864141508783707261195255808

noncomputable def ep436 := nat_lit 468496324571592726029904176832577536

noncomputable abbrev qz615 := (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (2 : Complex))

noncomputable abbrev qz575 := qz615

noncomputable abbrev qz383 := (@HSub.hSub Complex Complex Complex qz572 qz573 qz575)

noncomputable abbrev qz384 := (Complex.log qz573)

noncomputable abbrev qz77 := (@HSub.hSub Complex Complex Complex qz378 (@HMul.hMul Complex Complex Complex qz377 qz383 qz384) qz379)

noncomputable abbrev qz385 := qz575

noncomputable abbrev qz78 := (@HMul.hMul Complex Complex Complex qz377 qz385 ↑(Real.log (@HMul.hMul Real Real Real qz268 (2 : Real) Real.pi)))

noncomputable abbrev qz576 := qz614

noncomputable abbrev qz386 := qz576

noncomputable abbrev qz79 := qz386

noncomputable abbrev qz80 := (@instHMul Nat instMulNat)

noncomputable abbrev qz577 := (@instHPow Complex Int (@ZPow.toPow Complex (@DivInvMonoid.toZPow Complex Complex.instDivInvMonoid)))

noncomputable abbrev qz387 := qz577

noncomputable abbrev qz81 := qz387

noncomputable abbrev qz82 := qz379

noncomputable abbrev qz83 := (@OfNat.ofNat Int 1 (@instOfNat 1))

noncomputable abbrev qz84 := (@OfNat.ofNat Int 2 (@instOfNat 2))

noncomputable abbrev qz388 := (@instHSub Int Int.instSub)

noncomputable abbrev qz389 := (@instHMul Int Int.instMul)

noncomputable def ep437 := @Enclosure.Complex.IsNear.of_eq qz74 (@HAdd.hAdd Complex Complex Complex qz4 (@HAdd.hAdd Complex Complex Complex qz4 qz77 qz78) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz72 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz81 qz82 (@HSub.hSub Int Int Int qz388 qz83 (@HMul.hMul Int Int Int qz389 qz84 (@Nat.cast Int instNatCastInt k)))))) Bool.true 387233883343275309673

noncomputable def ep438 := @Enclosure.Complex.IsNear.addLitP (@HAdd.hAdd Complex Complex Complex qz4 qz77 qz78) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz72 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz81 qz82 (@HSub.hSub Int Int Int qz388 qz83 (@HMul.hMul Int Int Int qz389 qz84 (@Nat.cast Int instNatCastInt k))))) Bool.true 387234118491555117673 4503599627370496000

noncomputable def ep439 := nat_lit 13305254918899572772558459633664

noncomputable def ep440 := nat_lit 14538504424917185085854556618752000

noncomputable def ep441 := @ep438 15391453890732373227 70588000000000000000000 Bool.false 1692517188295218619199 9007199254740992000 3961437511655190561 35294000000000000000000 Bool.false 1794039 34359738368 3 34359738368 Bool.true 11936937493 8589934592000 19961 8589934592000 Bool.true ep439 387233883343275309673 4503599627370496000 504347363045406345355461 ep432 Bool.false ep440

noncomputable def ep442 := @Enclosure.Complex.IsNear.addLitP qz77 qz78 Bool.true 391372645898765613673 4503599627370496000 7594750001396460051 35294000000000000000000

noncomputable def ep443 := nat_lit 50755550378925112383635456

noncomputable def ep444 := @ep442 Bool.false 1692517188295218619199 9007199254740992000 3961437511655190561 35294000000000000000000 Bool.false 120447 131072 3 1048576 Bool.false 0 1 0 1 Bool.true ep443 387234118491555117673 4503599627370496000 15391453890732373227 70588000000000000000000 Bool.false 1692517188295218619199 1692517188295218619199 9007199254740992000

noncomputable abbrev qz85 := (@HMul.hMul Complex Complex Complex qz377 qz383 qz384)

noncomputable def ep445 := @Enclosure.Complex.IsNear.subLitP qz85 qz82 Bool.true 381239546737181997673 4503599627370496000 7594750001396460051 35294000000000000000000 Bool.false 446379060253374688627

noncomputable def ep446 := nat_lit 1565490583595062454692000

noncomputable def ep447 := nat_lit 1354013750636174895359200

noncomputable def ep448 := @ep445 1801439850948198400 3961437511655190561 35294000000000000000000 Bool.false 9000 4000 0 1 Bool.false 239532 4000 0 1 Bool.true ep446 391372645898765613673 4503599627370496000 7594750001396460051 35294000000000000000000 Bool.false ep447 1692517188295218619199 9007199254740992000 3961437511655190561 35294000000000000000000

noncomputable abbrev qz86 := qz383

noncomputable abbrev qz87 := qz384

noncomputable def ep449 := @Enclosure.Complex.IsNear.mul qz86 qz87 Bool.true 381239546737181997673 4503599627370496000 7594750001396460051 35294000000000000000000 Bool.false 446379060253374688627 1801439850948198400 3961437511655190561

noncomputable abbrev qz88 := (Complex.re qz383)

noncomputable abbrev qz89 := (Complex.re qz384)

noncomputable abbrev qz90 := (Complex.im qz383)

noncomputable abbrev qz91 := (Complex.im qz384)

noncomputable def ep450 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 qz88 qz89) (@HMul.hMul Real Real Real qz0 qz90 qz91) 258071439408739915 36028797018963968 62500000194117 20168000000000000000 51687309582909310881 562949953421312000

noncomputable def ep451 := nat_lit 1716950280624469638859176649380855808

noncomputable def ep452 := @Enclosure.Real.IsNear.mulLit_ff qz88 qz89 7000 4000 0 1 36867348486962845 9007199254740992 62500000194117 35294000000000000000

noncomputable def ep453 := @Enclosure.Complex.IsNear.re_isNear qz86 Bool.false 7000 4000 0 1 Bool.false 239532 4000 0 1

noncomputable abbrev qz578 := (Enclosure.sfrac Bool.false 239532 4000)

noncomputable abbrev qz390 := qz578

noncomputable def ep454 := @Enclosure.Complex.IsNear.of_eq qz86 (Complex.mk (Enclosure.sfrac Bool.false 7000 4000) qz390) Bool.false 7000 4000 0 1 Bool.false 239532 4000 0

noncomputable abbrev qz579 := (Enclosure.sfrac Bool.false 9000 4000)

noncomputable abbrev qz391 := (Complex.log (Complex.mk qz579 qz578))

noncomputable def ep455 := @Enclosure.Complex.IsNear.of_eq qz87 qz391 Bool.false 36867348486962845 9007199254740992 62500000194117 35294000000000000000 Bool.false 863138279359907 562949953421312 125000000017647 35294000000000000000

noncomputable def ep456 := nat_lit 371597802807114879789914766876751923558251699039857990058449156807334373210086528375635986897916129606473634283520

noncomputable def ep457 := nat_lit 9714909696409618477010097632727502773108969610381313931995066846055269022436495219105274547570468917409956757504

noncomputable def ep458 := nat_lit 79504690717676269950680768970409259684065340878012105811023377699323546363078778685076336699326056439480320

noncomputable def ep459 := BSN.log_dyadic_bound 24688579024 90224579024 6 5 ep456 1048576 282352 ep457 ep458 588856 114913158048 65536000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 24688579024) (BSN.artanhQ 90224579024) 0 5 ep457 ep456 ep458 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz92 := (Enclosure.sfrac Bool.false 1 2)

noncomputable abbrev qz392 := (Enclosure.Real.IsNear.const Bool.false 1 2)

noncomputable abbrev qz393 := (@Nat.cast Real Real.instNatCast 16000000)

noncomputable abbrev qz580 := (Real.log (Enclosure.sfrac Bool.false 57456579024 16000000))

noncomputable def ep460 := @Enclosure.Real.IsNear.mulLit_ff qz92 qz580 1 2 0 1 36867348486962845 4503599627370496 62500000194117 17647000000000000000 36867348486962845 9007199254740992 62500000194117 35294000000000000000 qz392 (BSN.isNear_log_sfrac 57456579024 16000000 36867348486962845 4503599627370496 62500000194117 17647000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 57456579024) qz393)) Bool.false 309265734456524417269760 37778931862957161709568 1000000003105872 282352000000000000000 36867348486962845 4503599627370496 62500000194117 17647000000000000000 (BSN.log_rat_reduce_isNear 57456579024 16000000 11 114913158048 65536000000 588856 1048576 24973259072661432 36028797018963968 282352 1000000000000000 rfl rfl rfl rfl (ep459 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep461 := BSN.arctan_dyadic_bound_f 9000 239532 1 0 1048576 282352 0 1 1 0 1 1 39379 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 9000) (BSN.arctanEvenQ 239532) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 9000) (BSN.arctanOddQ 239532) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz93 := (@HMul.hMul Real Real Real qz268 (Enclosure.sfrac Bool.false 1 2) Real.pi)

noncomputable abbrev qz94 := (@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 2) Real.pi 1 2 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 qz392 BSN.pi_near_15 rfl)

noncomputable abbrev qz394 := (Real.arctan (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 9000) (@Nat.cast Real Real.instNatCast 239532)))

noncomputable def ep462 := @Enclosure.Real.IsNear.subLit_ff_p qz93 qz394 884279719003555 562949953421312 1 2000000000000000 39379 1048576 1 282352 905066084418093842432 863138279359907 562949953421312 125000000017647 35294000000000000000 qz94 (ep461 rfl) rfl rfl

noncomputable abbrev qz395 := (Complex.mk qz579 qz578)

noncomputable abbrev qz396 := (Real.arctan (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 239532) (@Nat.cast Real Real.instNatCast 9000)))

noncomputable def ep463 := @Enclosure.Complex.IsNear.re_isNear qz87 Bool.false 36867348486962845 9007199254740992 62500000194117 35294000000000000000 Bool.false 863138279359907 562949953421312 125000000017647 35294000000000000000 (ep455 (@congrArg Complex Complex qz82 qz395 Complex.log (BSN.w_shift_mk qz13 Bool.false 119766 1000 2 qz14 rfl)) (@Enclosure.Complex.IsNear.of_parts qz391 Bool.false 36867348486962845 9007199254740992 62500000194117 35294000000000000000 Bool.false 863138279359907 562949953421312 125000000017647 35294000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz391) (@HMul.hMul Real Real Real qz0 qz92 qz580) Bool.false 36867348486962845 9007199254740992 62500000194117 35294000000000000000 (Enclosure.clog_re_eq 9000 239532 4000 57456579024 16000000 rfl rfl rfl) (ep460 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz391) qz396 Bool.false 863138279359907 562949953421312 125000000017647 35294000000000000000 (Enclosure.clog_im_eq 9000 239532 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz396 (@HSub.hSub Real Real Real qz381 qz93 qz394) Bool.false 863138279359907 562949953421312 125000000017647 35294000000000000000 (BSN.arctan_recip 239532 9000 rfl rfl) ep462))))

noncomputable def ep464 := @Enclosure.Real.IsNear.mulLit_ff qz90 qz91 239532 4000 0 1 863138279359907 562949953421312 125000000017647 35294000000000000000

noncomputable def ep465 := @Enclosure.Complex.IsNear.im_isNear qz86 Bool.false 7000 4000 0 1 Bool.false 239532 4000 0 1

noncomputable def ep466 := @Enclosure.Complex.IsNear.im_isNear qz87 Bool.false 36867348486962845 9007199254740992 62500000194117 35294000000000000000 Bool.false 863138279359907 562949953421312 125000000017647 35294000000000000000 (ep455 (@congrArg Complex Complex qz82 qz395 Complex.log (BSN.w_shift_mk qz13 Bool.false 119766 1000 2 qz14 rfl)) (@Enclosure.Complex.IsNear.of_parts qz391 Bool.false 36867348486962845 9007199254740992 62500000194117 35294000000000000000 Bool.false 863138279359907 562949953421312 125000000017647 35294000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz391) (@HMul.hMul Real Real Real qz0 qz92 qz580) Bool.false 36867348486962845 9007199254740992 62500000194117 35294000000000000000 (Enclosure.clog_re_eq 9000 239532 4000 57456579024 16000000 rfl rfl rfl) (ep460 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz391) qz396 Bool.false 863138279359907 562949953421312 125000000017647 35294000000000000000 (Enclosure.clog_im_eq 9000 239532 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz396 (@HSub.hSub Real Real Real qz381 qz93 qz394) Bool.false 863138279359907 562949953421312 125000000017647 35294000000000000000 (BSN.arctan_recip 239532 9000 rfl rfl) ep462))))

noncomputable abbrev qz95 := (@ep454 1 (BSN.w_sub_half_mk qz279 Bool.false 119766 1000 2 qz281 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7000 4000) qz390 Bool.false 7000 4000 0 1 Bool.false 239532 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 7000 4000) (Enclosure.Real.IsNear.const Bool.false 239532 4000)))

noncomputable def ep467 := @ep450 7485375001056755301 35294000000000000000000 ep451 381239546737181997673 4503599627370496000 7594750001396460051 35294000000000000000000 (@ep452 258071439408739915 36028797018963968 62500000194117 20168000000000000000 (ep453 qz95) ep463 rfl) (@ep464 51687309582909310881 562949953421312000 7485375001056755301 35294000000000000000000 (ep465 qz95) ep466 rfl) rfl

noncomputable def ep468 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz88 qz91) (@HMul.hMul Real Real Real qz0 qz90 qz89) 6041967955519349 2251799813685248 125000000017647 20168000000000000000 441545485888959209427 1801439850948198400

noncomputable def ep469 := nat_lit 1005156284711545214749716325383274496

noncomputable def ep470 := @Enclosure.Real.IsNear.mulLit_ff qz88 qz91 7000 4000 0 1 863138279359907 562949953421312 125000000017647 35294000000000000000

noncomputable def ep471 := @Enclosure.Real.IsNear.mulLit_ff qz90 qz89 239532 4000 0 1 36867348486962845 9007199254740992 62500000194117 35294000000000000000

noncomputable def ep472 := @ep468 3742687511624308311 35294000000000000000000 ep469 446379060253374688627 1801439850948198400 3961437511655190561 35294000000000000000000 (@ep470 6041967955519349 2251799813685248 125000000017647 20168000000000000000 (ep453 qz95) ep466 rfl) (@ep471 441545485888959209427 1801439850948198400 3742687511624308311 35294000000000000000000 (ep465 qz95) ep463 rfl) rfl

noncomputable def ep473 := @Enclosure.Complex.IsNear.of_eq qz82 qz395 Bool.false 9000 4000 0 1 Bool.false 239532 4000 0 1 (BSN.w_shift_mk qz13 Bool.false 119766 1000 2 qz14 rfl)

noncomputable abbrev qz397 := (ep473 (@Enclosure.Complex.IsNear.mk qz579 qz578 Bool.false 9000 4000 0 1 Bool.false 239532 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 9000 4000) (Enclosure.Real.IsNear.const Bool.false 239532 4000)))

noncomputable abbrev qz96 := qz397

noncomputable def ep474 := ep448 (@ep449 35294000000000000000000 (ep467 rfl) (ep472 rfl)) qz96 rfl rfl rfl rfl rfl rfl

noncomputable abbrev qz97 := qz385

noncomputable def ep475 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re qz97) (Complex.re ↑qz2)) (@HMul.hMul Real Real Real qz0 (Complex.im qz97) (Complex.im ↑qz2)) 120447 131072 3 1048576 0 1 0 1 120447 120447

noncomputable def ep476 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re qz97) (Complex.re ↑qz2) 1 2 0 1 120447 65536 3 524288 120447 131072 3 1048576

noncomputable abbrev qz98 := (@Enclosure.Complex.IsNear.of_eq qz385 (Complex.mk (Enclosure.sfrac Bool.false 1 2) qz278) Bool.false 1 2 0 1 Bool.false 0 1 0 1 BSN.half_c_mk (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 2) qz278 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz392 qz287))

noncomputable def ep477 := ep476 (@Enclosure.Complex.IsNear.re_isNear qz97 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz98) (@Enclosure.Real.IsNear.of_eq (Complex.re ↑qz2) qz2 Bool.false 120447 65536 3 524288 (Complex.ofReal_re qz2) EMRow39.d4)

noncomputable def ep478 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz97) (Complex.im ↑qz2) 0 1 0 1 0 1 0 1 0 1 0 1

noncomputable def ep479 := ep478 (@Enclosure.Complex.IsNear.im_isNear qz97 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz98) (@Enclosure.Real.IsNear.of_eq (Complex.im ↑qz2) qz10 Bool.false 0 1 0 1 (@Eq.trans Real (Complex.im ↑qz2) (0 : Real) qz10 (Complex.ofReal_im qz2) Enclosure.sfrac_zero_eq) qz22)

noncomputable def ep480 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re qz97) (Complex.im ↑qz2)) (@HMul.hMul Real Real Real qz0 (Complex.im qz97) (Complex.re ↑qz2)) 0 1 0 1 0 1 0 1 0 0

noncomputable def ep481 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re qz97) (Complex.im ↑qz2) 1 2 0 1 0 1 0 1 0 1 0 1

noncomputable def ep482 := ep481 (@Enclosure.Complex.IsNear.re_isNear qz97 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz98) (@Enclosure.Real.IsNear.of_eq (Complex.im ↑qz2) qz10 Bool.false 0 1 0 1 (@Eq.trans Real (Complex.im ↑qz2) (0 : Real) qz10 (Complex.ofReal_im qz2) Enclosure.sfrac_zero_eq) qz22)

noncomputable def ep483 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz97) (Complex.re ↑qz2) 0 1 0 1 120447 65536 3 524288 0 1 0 1

noncomputable def ep484 := ep483 (@Enclosure.Complex.IsNear.im_isNear qz97 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz98) (@Enclosure.Real.IsNear.of_eq (Complex.re ↑qz2) qz2 Bool.false 120447 65536 3 524288 (Complex.ofReal_re qz2) EMRow39.d4)

noncomputable def ep485 := @ep444 3961437511655190561 35294000000000000000000 (ep474 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@Enclosure.Complex.IsNear.mul qz97 (↑qz2) Bool.false 120447 131072 3 1048576 Bool.false 0 1 0 1 (@ep475 131072 3 1048576 (ep477 rfl) (ep479 rfl) rfl rfl) (@ep480 1 0 1 (ep482 rfl) (ep484 rfl) rfl rfl))

noncomputable abbrev qz99 := (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 1)

noncomputable abbrev qz398 := (@Nat.cast Complex Complex.instNatCast 1)

noncomputable abbrev qz100 := (@HMul.hMul Complex Complex Complex qz377 (@HMul.hMul Complex Complex Complex qz377 (2 : Complex) qz398) (@HSub.hSub Complex Complex Complex qz378 (@HMul.hMul Complex Complex Complex qz377 (2 : Complex) qz398) (1 : Complex)))

noncomputable abbrev qz399 := (@HPow.hPow Complex Int Complex qz577 qz573 (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) (@OfNat.ofNat Int 1 (@instOfNat 1)) (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (@OfNat.ofNat Int 2 (@instOfNat 2)) (@Nat.cast Int instNatCastInt 1))))

noncomputable abbrev qz101 := qz399

noncomputable def ep486 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz72 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz81 qz82 (@HSub.hSub Int Int Int qz388 qz83 (@HMul.hMul Int Int Int qz389 qz84 (@Nat.cast Int instNatCastInt k))))) (@HAdd.hAdd Complex Complex Complex qz4 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz72 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz81 qz82 (@HSub.hSub Int Int Int qz388 qz83 (@HMul.hMul Int Int Int qz389 qz84 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 (@Rat.cast Complex Complex.instRatCast (bernoulli qz99)) qz100) qz101)) Bool.false 1794039 34359738368 3 34359738368

noncomputable def ep487 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz72 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz81 qz82 (@HSub.hSub Int Int Int qz388 qz83 (@HMul.hMul Int Int Int qz389 qz84 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 (@Rat.cast Complex Complex.instRatCast (bernoulli qz99)) qz100) qz101) Bool.false 0 1 0 1 Bool.false

noncomputable def ep488 := @ep487 0 1 0 1 Bool.false 1794039 34359738368 3 34359738368 Bool.true 11936937493 8589934592000 19961 8589934592000 Bool.false 1794039 1794039 34359738368 3 34359738368 Bool.true 11936937493 11936937493 8589934592000 19961

noncomputable def ep489 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz72 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz81 qz82 (@HSub.hSub Int Int Int qz388 qz83 (@HMul.hMul Int Int Int qz389 qz84 (@Nat.cast Int instNatCastInt k))))) (Complex.mk qz10 qz10) Bool.false 0 1 0 1 Bool.false

noncomputable def ep490 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz79 (@Rat.cast Complex Complex.instRatCast (bernoulli qz99)) qz100) qz101 Bool.false 1794039 34359738368 3 34359738368 Bool.true 11936937493 8589934592000 19961 8589934592000

noncomputable abbrev qz102 := (Complex.re qz399)

noncomputable abbrev qz103 := (Complex.im qz399)

noncomputable def ep491 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz79 (@Rat.cast Complex Complex.instRatCast (bernoulli qz99)) qz100)) qz102) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz79 (@Rat.cast Complex Complex.instRatCast (bernoulli qz99)) qz100)) qz103) 1794039 34359738368 3 34359738368 0 1 0

noncomputable def ep492 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz79 (@Rat.cast Complex Complex.instRatCast (bernoulli qz99)) qz100)) qz102 1 12 0 1 5382117 8589934592 9 8589934592 1794039

noncomputable def ep493 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz79 (@Rat.cast Complex Complex.instRatCast (bernoulli qz99)) qz100) (Complex.mk (Enclosure.sfrac Bool.false 1 12) qz10) Bool.false 1 12 0 1 Bool.false 0 1 0 1

noncomputable abbrev qz400 := (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 12) qz10 Bool.false 1 12 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 12) qz22)

noncomputable def ep494 := @Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz79 (@Rat.cast Complex Complex.instRatCast (bernoulli qz99)) qz100) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (ep493 (BSN.stirling_coeff_mk 1 1 6 Bool.false BSN.bern_real_1 rfl rfl) qz400)

noncomputable def ep495 := @Enclosure.Complex.IsNear.re_isNear qz101 Bool.false 5382117 8589934592 9 8589934592 Bool.true 35810812479 2147483648000 59883 2147483648000

noncomputable abbrev qz581 := (@instHPow Complex Nat (@NPow.toPow Complex (@Monoid.toNPow Complex (@Semiring.toMonoid Complex Complex.instSemiring))))

noncomputable abbrev qz401 := (@HPow.hPow Complex Nat Complex qz581 qz573 1)

noncomputable abbrev qz104 := (@Inv.inv Complex Complex.instInv qz401)

noncomputable def ep496 := @Enclosure.Complex.IsNear.of_eq qz101 qz104 Bool.false 5382117 8589934592 9 8589934592 Bool.true 35810812479 2147483648000 59883

noncomputable def ep497 := @Enclosure.Complex.IsNear.of_parts qz104 Bool.false 5382117 8589934592 9 8589934592 Bool.true 35810812479 2147483648000 59883

noncomputable abbrev qz105 := (Complex.re qz401)

noncomputable abbrev qz106 := (@MonoidWithZeroHom Complex Real (@instMulZeroOneClassOfSemiring Complex Complex.instSemiring) (@instMulZeroOneClassOfSemiring Real Real.semiring))

noncomputable abbrev qz107 := (@MonoidWithZeroHom.funLike Complex Real (@instMulZeroOneClassOfSemiring Complex Complex.instSemiring) (@instMulZeroOneClassOfSemiring Real Real.semiring))

noncomputable abbrev qz108 := qz401

noncomputable def ep498 := @Enclosure.Real.IsNear.mulLit_ff qz105 (@Inv.inv Real Real.instInv (@DFunLike.coe qz106 Complex (fun (x : Complex) => Real) qz107 Complex.normSq qz108)) 9000 4000 0 1 598013 2147483648 1 2147483648

noncomputable def ep499 := @Enclosure.Complex.IsNear.re_isNear qz108 Bool.false 9000 4000 0 1 Bool.false 239532 4000 0 1

noncomputable def ep500 := @Enclosure.Complex.IsNear.of_eq qz108 qz82 Bool.false 9000 4000 0 1 Bool.false 239532 4000 0

noncomputable def ep501 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (@DFunLike.coe qz106 Complex (fun (x : Complex) => Real) qz107 Complex.normSq qz108)) Bool.false 598013 2147483648 1 2147483648 598013 2147483648 1

noncomputable abbrev qz109 := (Complex.im qz401)

noncomputable abbrev qz402 := (@instHAdd Real Real.instAdd)

noncomputable def ep502 := @Enclosure.Real.IsNear.of_eq (@DFunLike.coe qz106 Complex (fun (x : Complex) => Real) qz107 Complex.normSq qz108) (@HAdd.hAdd Real Real Real qz402 (@HMul.hMul Real Real Real qz0 qz105 qz105) (@HMul.hMul Real Real Real qz0 qz109 qz109)) Bool.false 3591036189 1000000 0 1

noncomputable def ep503 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz105 qz105) (@HMul.hMul Real Real Real qz0 qz109 qz109) 81 16 0 1 3585973689 1000000

noncomputable def ep504 := @Enclosure.Real.IsNear.mulLit_ff qz105 qz105 9000 4000 0 1 9000 4000 0 1

noncomputable def ep505 := @Enclosure.Real.IsNear.mulLit_ff qz109 qz109 239532 4000 0 1 239532 4000 0 1

noncomputable def ep506 := @Enclosure.Complex.IsNear.im_isNear qz108 Bool.false 9000 4000 0 1 Bool.false 239532 4000 0 1

noncomputable abbrev qz110 := (ep499 (@ep500 1 (BSN.pow_one_c qz379) qz397))

noncomputable abbrev qz111 := (ep506 (@ep500 1 (BSN.pow_one_c qz379) qz397))

noncomputable def ep507 := @ep503 0 1 57456579024 3591036189 1000000 0 1 (@ep504 81 16 0 1 qz110 qz110 rfl) (@ep505 3585973689 1000000 0 1 qz111 qz111 rfl)

noncomputable def ep508 := @Enclosure.Real.IsNear.inv_image (@DFunLike.coe qz106 Complex (fun (x : Complex) => Real) qz107 Complex.normSq qz108) 3591036189 1000000 0 1 299006 299007 1073741824 (ep502 (Enclosure.Complex.normSq_eq_mul_add_mul qz108) (ep507 rfl rfl)) rfl

noncomputable def ep509 := @Enclosure.Real.IsNear.of_eq (Complex.re qz104) (@HMul.hMul Real Real Real qz0 qz105 (@Inv.inv Real Real.instInv (@DFunLike.coe qz106 Complex (fun (x : Complex) => Real) qz107 Complex.normSq qz108))) Bool.false 5382117 8589934592 9 8589934592 (Enclosure.Complex.inv_re_eq_mul qz108) (@ep498 5382117 8589934592 9 8589934592 qz110 (@ep501 2147483648 (ep508 rfl rfl rfl rfl rfl) rfl) rfl)

noncomputable def ep510 := @Enclosure.Real.IsNear.of_eq (Complex.im qz104) (@HMul.hMul Real Real Real qz0 (@Neg.neg Real Real.instNeg qz109) (@Inv.inv Real Real.instInv (@DFunLike.coe qz106 Complex (fun (x : Complex) => Real) qz107 Complex.normSq qz108))) Bool.true 35810812479 2147483648000 59883 2147483648000 (Enclosure.Complex.inv_im_eq_mul qz108)

noncomputable def ep511 := @Enclosure.Real.IsNear.mulLit_tf (@Neg.neg Real Real.instNeg qz109) (@Inv.inv Real Real.instInv (@DFunLike.coe qz106 Complex (fun (x : Complex) => Real) qz107 Complex.normSq qz108)) 239532 4000 0 1 598013 2147483648 1

noncomputable def ep512 := @ep511 2147483648 35810812479 2147483648000 59883 2147483648000 (@Enclosure.Real.IsNear.neg qz109 Bool.false 239532 4000 0 1 qz111) (@ep501 2147483648 (ep508 rfl rfl rfl rfl rfl) rfl) rfl

noncomputable def ep513 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz79 (@Rat.cast Complex Complex.instRatCast (bernoulli qz99)) qz100)) qz103 0 1 0 1 35810812479 2147483648000 59883 2147483648000 0

noncomputable def ep514 := @Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz79 (@Rat.cast Complex Complex.instRatCast (bernoulli qz99)) qz100) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (ep493 (BSN.stirling_coeff_mk 1 1 6 Bool.false BSN.bern_real_1 rfl rfl) qz400)

noncomputable def ep515 := @Enclosure.Complex.IsNear.im_isNear qz101 Bool.false 5382117 8589934592 9 8589934592 Bool.true 35810812479 2147483648000 59883 2147483648000

noncomputable abbrev qz112 := (@ep496 2147483648000 (BSN.zpow_one_sub_two_mul qz379 1 1 rfl rfl) (@ep497 2147483648000 ep509 (ep510 ep512)))

noncomputable def ep516 := @ep491 1 1794039 1794039 34359738368 3 34359738368 (@ep492 34359738368 3 34359738368 ep494 (ep495 qz112) rfl) (@ep513 1 0 1 ep514 (ep515 qz112) rfl) rfl

noncomputable def ep517 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz79 (@Rat.cast Complex Complex.instRatCast (bernoulli qz99)) qz100)) qz103) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz79 (@Rat.cast Complex Complex.instRatCast (bernoulli qz99)) qz100)) qz102) 11936937493 8589934592000 19961 8589934592000 0 1 0

noncomputable def ep518 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HDiv.hDiv Complex Complex Complex qz79 (@Rat.cast Complex Complex.instRatCast (bernoulli qz99)) qz100)) qz103 1 12 0 1 35810812479 2147483648000 59883 2147483648000 11936937493

noncomputable def ep519 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz79 (@Rat.cast Complex Complex.instRatCast (bernoulli qz99)) qz100)) qz102 0 1 0 1 5382117 8589934592 9 8589934592 0

noncomputable def ep520 := @ep517 1 11936937493 11936937493 8589934592000 19961 8589934592000 (@ep518 8589934592000 19961 8589934592000 ep494 (ep515 qz112) rfl) (@ep519 1 0 1 ep514 (ep495 qz112) rfl) rfl

noncomputable abbrev qz113 := (@Enclosure.Complex.IsNear.mk qz278 qz278 Bool.false 0 1 0 1 Bool.false 0 1 0 1 qz287 qz287)

noncomputable def ep521 := @ep488 8589934592000 (@ep489 0 1 0 1 (BSN.stirling_sum_base qz82) qz113) (ep490 (ep516 rfl) (ep520 rfl)) rfl rfl rfl rfl rfl

noncomputable def ep522 := @ep441 1692504671509049959231 9007199254740992000 519244287398488229008267 ep428 (ep485 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep486 Bool.true 11936937493 8589934592000 19961 8589934592000 (BSN.stirling_sum_succ qz82 0 1 rfl) (ep521 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl

noncomputable def ep523 := @Enclosure.Complex.IsNear.of_eq (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz75 (@Nat.cast Complex Complex.instNatCast j))) (BSN.logSumC qz13 2) Bool.false 36862014137581213 4503599627370496 62500000194117 17647000000000000000 Bool.false 877230335493539 281474976710656

noncomputable abbrev qz114 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz273 qz380 qz398))

noncomputable def ep524 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz13 2) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.logSumC qz13 1) qz114) Bool.false 36862014137581213 4503599627370496 62500000194117 17647000000000000000 Bool.false 877230335493539 281474976710656 125000000017647 17647000000000000000

noncomputable def ep525 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz13 1) qz114 Bool.false 36861073539743389 9007199254740992 62500000194117 35294000000000000000 Bool.false 881929835021731 562949953421312 125000000017647 35294000000000000000 Bool.false

noncomputable def ep526 := nat_lit 664047012536546825355699360366592

noncomputable def ep527 := nat_lit 987673553011699357922241806336

noncomputable abbrev qz115 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz273 qz380 (@Nat.cast Complex Complex.instNatCast 0)))

noncomputable def ep528 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz13 1) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.logSumC qz13 0) qz115) Bool.false 36861073539743389 9007199254740992 62500000194117 35294000000000000000 Bool.false 881929835021731 562949953421312 125000000017647 35294000000000000000

noncomputable def ep529 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz13 0) qz115 Bool.false 0 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable abbrev qz403 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz578))

noncomputable def ep530 := @Enclosure.Complex.IsNear.of_eq qz115 qz403 Bool.false 36861073539743389 9007199254740992 62500000194117 35294000000000000000 Bool.false 881929835021731 562949953421312 125000000017647 35294000000000000000

noncomputable def ep531 := nat_lit 368316048626703791933615093043796859193534317180072500210906894555977821157504985964557618740620178127689634283520

noncomputable def ep532 := nat_lit 9581637881863152349782852315105332581727859255637912651674836435361589350379443833289057306961969038293156757504

noncomputable def ep533 := nat_lit 76965691847254715455887912781467403108436102770818493612015575018277027145313778419036594484100712439480320

noncomputable def ep534 := BSN.log_dyadic_bound 24608579024 90144579024 6 5 ep531 1048576 282352 ep532 ep533 587395 114753158048 65536000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 24608579024) (BSN.artanhQ 90144579024) 0 5 ep532 ep531 ep533 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep535 := @Enclosure.Real.IsNear.mulLit_ff qz92 (Real.log (Enclosure.sfrac Bool.false 57376579024 16000000)) 1 2 0 1 36861073539743389 4503599627370496 62500000194117 17647000000000000000 36861073539743389 9007199254740992 62500000194117 35294000000000000000 qz392 (BSN.isNear_log_sfrac 57376579024 16000000 36861073539743389 4503599627370496 62500000194117 17647000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 57376579024) qz393)) Bool.false 309213096384079710912512 37778931862957161709568 1000000003105872 282352000000000000000 36861073539743389 4503599627370496 62500000194117 17647000000000000000 (BSN.log_rat_reduce_isNear 57376579024 16000000 11 114753158048 65536000000 587395 1048576 24973259072661432 36028797018963968 282352 1000000000000000 rfl rfl rfl rfl (ep534 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep536 := BSN.arctan_dyadic_bound_f 1000 239532 1 0 1048576 282352 0 1 1 0 1 1 4377 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 239532) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 239532) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz404 := (@Nat.cast Real Real.instNatCast 1000)

noncomputable abbrev qz405 := (@Nat.cast Real Real.instNatCast 239532)

noncomputable def ep537 := @Enclosure.Real.IsNear.subLit_ff_p qz93 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz404 qz405)) 884279719003555 562949953421312 1 2000000000000000 4377 1048576 1 282352 924770458687746605056 881929835021731 562949953421312 125000000017647 35294000000000000000 qz94 (ep536 rfl) rfl rfl

noncomputable abbrev qz116 := (@HAdd.hAdd Complex Complex Complex qz273 qz380 (@Nat.cast Complex Complex.instNatCast 0))

noncomputable abbrev qz406 := (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz578)

noncomputable def ep538 := @ep529 36861073539743389 9007199254740992 62500000194117 35294000000000000000 Bool.false 881929835021731 562949953421312 125000000017647 35294000000000000000 Bool.false 36861073539743389 36861073539743389 9007199254740992 62500000194117 35294000000000000000 Bool.false 881929835021731 881929835021731 562949953421312 125000000017647 35294000000000000000 (@Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz13 0) (Complex.mk qz10 qz10) Bool.false 0 1 0 1 Bool.false 0 1 0 1 (BSN.log_sum_c_base qz13) qz113) (ep530 (@congrArg Complex Complex qz116 qz406 Complex.log (BSN.w_shift_mk qz13 Bool.false 119766 1000 0 qz14 rfl)) (@Enclosure.Complex.IsNear.of_parts qz403 Bool.false 36861073539743389 9007199254740992 62500000194117 35294000000000000000 Bool.false 881929835021731 562949953421312 125000000017647 35294000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz403) (@HMul.hMul Real Real Real qz0 qz92 (Real.log (Enclosure.sfrac Bool.false 57376579024 16000000))) Bool.false 36861073539743389 9007199254740992 62500000194117 35294000000000000000 (Enclosure.clog_re_eq 1000 239532 4000 57376579024 16000000 rfl rfl rfl) (ep535 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz403) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz405 qz404)) Bool.false 881929835021731 562949953421312 125000000017647 35294000000000000000 (Enclosure.clog_im_eq 1000 239532 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz405 qz404)) (@HSub.hSub Real Real Real qz381 qz93 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz404 qz405))) Bool.false 881929835021731 562949953421312 125000000017647 35294000000000000000 (BSN.arctan_recip 239532 1000 rfl rfl) ep537)))) rfl rfl

noncomputable abbrev qz407 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz578))

noncomputable def ep539 := @Enclosure.Complex.IsNear.of_eq qz114 qz407 Bool.false 36862954735419037 9007199254740992 62500000194117 35294000000000000000 Bool.false 872530835965347 562949953421312 125000000017647 35294000000000000000

noncomputable def ep540 := nat_lit 369297825154431267436734504090460416147556038263072640329756819737479728026186238590112620501892393971324834283520

noncomputable def ep541 := nat_lit 9621453757908525450691663500109953708869008761523550207915772593899832641477370600366214366725621082028196757504

noncomputable def ep542 := nat_lit 77719617724303764116333637208597567715181168691169366818530432599259047324090244549807542915068315639480320

noncomputable def ep543 := BSN.log_dyadic_bound 24632579024 90168579024 6 5 ep540 1048576 282352 ep541 ep542 587833 114801158048 65536000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 24632579024) (BSN.artanhQ 90168579024) 0 5 ep541 ep540 ep542 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep544 := @Enclosure.Real.IsNear.mulLit_ff qz92 (Real.log (Enclosure.sfrac Bool.false 57400579024 16000000)) 1 2 0 1 36862954735419037 4503599627370496 62500000194117 17647000000000000000 36862954735419037 9007199254740992 62500000194117 35294000000000000000 qz392 (BSN.isNear_log_sfrac 57400579024 16000000 36862954735419037 4503599627370496 62500000194117 17647000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 57400579024) qz393)) Bool.false 309228876997174017130496 37778931862957161709568 1000000003105872 282352000000000000000 36862954735419037 4503599627370496 62500000194117 17647000000000000000 (BSN.log_rat_reduce_isNear 57400579024 16000000 11 114801158048 65536000000 587833 1048576 24973259072661432 36028797018963968 282352 1000000000000000 rfl rfl rfl rfl (ep543 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep545 := BSN.arctan_dyadic_bound_f 5000 239532 1 0 1048576 282352 0 1 1 0 1 1 21884 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 5000) (BSN.arctanEvenQ 239532) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 5000) (BSN.arctanOddQ 239532) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz408 := (@Nat.cast Real Real.instNatCast 5000)

noncomputable def ep546 := @Enclosure.Real.IsNear.subLit_ff_p qz93 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz408 qz405)) 884279719003555 562949953421312 1 2000000000000000 21884 1048576 1 282352 914914893853199695872 872530835965347 562949953421312 125000000017647 35294000000000000000 qz94 (ep545 rfl) rfl rfl

noncomputable abbrev qz117 := (@HAdd.hAdd Complex Complex Complex qz273 qz380 qz398)

noncomputable abbrev qz409 := (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz578)

noncomputable def ep547 := @ep525 36862954735419037 9007199254740992 62500000194117 35294000000000000000 Bool.false 872530835965347 562949953421312 125000000017647 35294000000000000000 Bool.false ep526 36862014137581213 4503599627370496 62500000194117 17647000000000000000 Bool.false ep527 877230335493539 281474976710656 125000000017647 17647000000000000000 (ep528 (BSN.log_sum_c_succ qz13 0 1 rfl) (ep538 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep539 (@congrArg Complex Complex qz117 qz409 Complex.log (BSN.w_shift_mk qz13 Bool.false 119766 1000 1 qz14 rfl)) (@Enclosure.Complex.IsNear.of_parts qz407 Bool.false 36862954735419037 9007199254740992 62500000194117 35294000000000000000 Bool.false 872530835965347 562949953421312 125000000017647 35294000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz407) (@HMul.hMul Real Real Real qz0 qz92 (Real.log (Enclosure.sfrac Bool.false 57400579024 16000000))) Bool.false 36862954735419037 9007199254740992 62500000194117 35294000000000000000 (Enclosure.clog_re_eq 5000 239532 4000 57400579024 16000000 rfl rfl rfl) (ep544 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz407) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz405 qz408)) Bool.false 872530835965347 562949953421312 125000000017647 35294000000000000000 (Enclosure.clog_im_eq 5000 239532 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz405 qz408)) (@HSub.hSub Real Real Real qz381 qz93 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz408 qz405))) Bool.false 872530835965347 562949953421312 125000000017647 35294000000000000000 (BSN.arctan_recip 239532 5000 rfl rfl) ep546)))) rfl rfl

noncomputable def ep548 := @ep434 ep428 Bool.false 36862014137581213 4503599627370496 62500000194117 17647000000000000000 Bool.false 877230335493539 281474976710656 125000000017647 17647000000000000000 Bool.true ep435 424095897480856522673 4503599627370496000 512539363070849648779461 ep432 Bool.false ep436 1664433300773256711231 9007199254740992000 552012287403114284176267 ep428 (@ep437 4503599627370496000 504347363045406345355461 ep432 Bool.false 1692504671509049959231 9007199254740992000 519244287398488229008267 ep428 (BSN.logGammaStirling_unfold 1 qz82) (ep522 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (@ep523 125000000017647 17647000000000000000 (BSN.log_sum_c_eq qz13 2) (ep524 (BSN.log_sum_c_succ qz13 1 2 rfl) (ep547 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)))

noncomputable abbrev qz118 := (@HDiv.hDiv Real Real Real qz271 qz279 (2 : Real))

noncomputable def ep549 := @Enclosure.Real.IsNear.mulLit_ff qz118 (Real.log Real.pi) 119766 2000 0 1 75021 65536 1 262144 4492482543 65536000 59883 262144000 (@Enclosure.Real.IsNear.of_eq qz118 (Enclosure.sfrac Bool.false 119766 2000) Bool.false 119766 2000 0 1 (BSN.t_half_eq qz13 Bool.false 119766 1000 qz14) (Enclosure.Real.IsNear.const Bool.false 119766 2000)) EMRow39.d5 rfl

noncomputable def ep550 := @ep430 59883 262144000 ep431 209398240314421494387 1801439850948198400 ep427 ep428 (@ep433 552012287403114284176267 ep428 (ep548 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) ep549 rfl rfl

noncomputable def ep551 := BSN.cos_dyadic_bound_f 955682 2147483648 1 0 1048576 282628 0 1 1 0 1 1 1048575 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 955682) qz16 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 955682) qz282 0 0 rfl) rfl rfl

noncomputable def ep552 := @ep426 524288 Bool.true 1048575 1048576 1 141176 (@ep429 121885817 1048576 183 524288 ep550 rfl) (Enclosure.sfrac_false_div 121885817 1048576) (BSN.cos_reduce2 qz382 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 67250166285681557504) qz20) 226375608064910080 72057594037927936 Bool.false 1048575 1048576 18 1000000000000000 282352 141176 (BSN.sin_reduce_arg_pos_rat_q2 121885817 1048576 226375608064910080 72057594037927936 18 67250166285681557504 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1048575 1048576 67250166285681557504 151115727451828646838272 955682 2147483648 282628 282352 (ep551 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep553 := nat_lit 17742998193439651135488000

noncomputable def ep554 := nat_lit 22872631287198944615699593403

noncomputable def ep555 := nat_lit 3131106891196295235879567360000

noncomputable abbrev qz410 := (@HPow.hPow Complex Complex Complex qz536 (@Nat.cast Complex Complex.instNatCast 30) qz537)

noncomputable abbrev qz119 := qz410

noncomputable abbrev qz411 := (@Nat.cast Complex Complex.instNatCast 30)

noncomputable abbrev qz120 := (@HAdd.hAdd Complex Complex Complex qz273 (@HDiv.hDiv Complex Complex Complex qz386 qz411 (@HSub.hSub Complex Complex Complex qz378 qz272 (1 : Complex))) qz385)

noncomputable abbrev qz121 := (@instHSub Nat instSubNat)

noncomputable abbrev qz412 := qz581

noncomputable abbrev qz122 := qz412

noncomputable abbrev qz123 := qz411

noncomputable def ep556 := @Enclosure.Complex.IsNear.of_eq (zetaApproximant qz5 1 30) (@HAdd.hAdd Complex Complex Complex qz4 (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 30, @HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast n) qz7) (@HMul.hMul Complex Complex Complex qz72 qz119 (@HAdd.hAdd Complex Complex Complex qz4 qz120 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz80 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz122 qz123 (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1))))))) Bool.false ep421 ep422 ep423

noncomputable def ep557 := @Enclosure.Complex.IsNear.addLitP (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 30, @HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast n) qz7) (@HMul.hMul Complex Complex Complex qz72 qz119 (@HAdd.hAdd Complex Complex Complex qz4 qz120 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz80 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz122 qz123 (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))))) Bool.false 2977519143225 1099511627776 139986997884941 19403081695363072

noncomputable def ep558 := nat_lit 4487302768170306869224069

noncomputable def ep559 := nat_lit 381702790222184530722395189

noncomputable def ep560 := nat_lit 1543803984352674074270569

noncomputable def ep561 := nat_lit 286754997816122650004233403

noncomputable def ep562 := nat_lit 427574775804339907784419015682418540544

noncomputable def ep563 := nat_lit 155569295739702286318701507644489728

noncomputable def ep564 := @ep557 Bool.true 56601736679 549755813888 1093452177099 151586575745024 Bool.false ep558 ep422 ep559 ep424 Bool.false ep560 ep553 ep561 ep555 Bool.false ep562 ep421 ep422 ep423 ep424 Bool.true ep563 282978900467610012708431 ep553

noncomputable def ep565 := @Enclosure.Complex.IsNear.of_eq (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 30, @HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast n) qz7) (BSN.headSumC qz5 30) Bool.false 2977519143225 1099511627776 139986997884941 19403081695363072 Bool.true 56601736679 549755813888 1093452177099

noncomputable abbrev qz413 := (@Nat.cast Complex Complex.instNatCast 29)

noncomputable def ep566 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 30) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 29) (@HPow.hPow Complex Complex Complex qz6 qz413 qz7)) Bool.false 2977519143225 1099511627776 139986997884941 19403081695363072 Bool.true 56601736679 549755813888 1093452177099 151586575745024

noncomputable def ep567 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 29) (@HPow.hPow Complex Complex Complex qz6 qz413 qz7) Bool.false 1448321063055 549755813888 68446266823145 9701540847681536 Bool.false 74268323357 1099511627776 136857753756341 19403081695363072 Bool.false

noncomputable def ep568 := nat_lit 1636908459950760316108800

noncomputable abbrev qz414 := (@Nat.cast Complex Complex.instNatCast 28)

noncomputable def ep569 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 29) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 28) (@HPow.hPow Complex Complex Complex qz6 qz414 qz7)) Bool.false 1448321063055 549755813888 68446266823145 9701540847681536 Bool.false 74268323357 1099511627776 136857753756341 19403081695363072

noncomputable def ep570 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 28) (@HPow.hPow Complex Complex Complex qz6 qz414 qz7) Bool.false 3103343771617 1099511627776 133735822406779 19403081695363072 Bool.false 53039121167 1099511627776 133717559385303 19403081695363072 Bool.true

noncomputable def ep571 := nat_lit 3184891699163739570831360

noncomputable abbrev qz415 := (@Nat.cast Complex Complex.instNatCast 27)

noncomputable def ep572 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 28) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 27) (@HPow.hPow Complex Complex Complex qz6 qz415 qz7)) Bool.false 3103343771617 1099511627776 133735822406779 19403081695363072 Bool.false 53039121167 1099511627776 133717559385303 19403081695363072

noncomputable def ep573 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 27) (@HPow.hPow Complex Complex Complex qz6 qz415 qz7) Bool.false 3009564143935 1099511627776 130528173540033 19403081695363072 Bool.true 136646288461 1099511627776 130501523711219 19403081695363072 Bool.false

noncomputable def ep574 := nat_lit 1706081280939559428816896

noncomputable abbrev qz416 := (@Nat.cast Complex Complex.instNatCast 26)

noncomputable def ep575 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 27) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 26) (@HPow.hPow Complex Complex Complex qz6 qz416 qz7)) Bool.false 3009564143935 1099511627776 130528173540033 19403081695363072 Bool.true 136646288461 1099511627776 130501523711219 19403081695363072

noncomputable def ep576 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 26) (@HPow.hPow Complex Complex Complex qz6 qz416 qz7) Bool.false 1419048785517 549755813888 31813266618337 4850770423840768 Bool.true 5893122343 1099511627776 127229910415241 19403081695363072 Bool.false

noncomputable def ep577 := nat_lit 1654525385397127903969280

noncomputable abbrev qz417 := (@Nat.cast Complex Complex.instNatCast 25)

noncomputable def ep578 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 26) (@HAdd.hAdd Complex Complex Complex qz4 qz55 (@HPow.hPow Complex Complex Complex qz6 qz417 qz7)) Bool.false 1419048785517 549755813888 31813266618337 4850770423840768 Bool.true 5893122343 1099511627776 127229910415241 19403081695363072

noncomputable def ep579 := @Enclosure.Complex.IsNear.addLitP qz55 (@HPow.hPow Complex Complex Complex qz6 qz417 qz7) Bool.false 2974059790119 1099511627776 123920373848123 19403081695363072 Bool.false 83469755161 549755813888 30973528808913 4850770423840768 Bool.true

noncomputable def ep580 := nat_lit 3120521280114705127440384

noncomputable abbrev qz124 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 25)))

noncomputable abbrev qz582 := (Real.log (Enclosure.sfrac Bool.false 25 1))

noncomputable abbrev qz125 := (@HMul.hMul Real Real Real qz268 qz279 qz582)

noncomputable def ep581 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz417 qz7) (Complex.mk (@HMul.hMul Real Real Real qz0 qz124 (Real.cos qz125)) (@HMul.hMul Real Real Real qz0 qz124 (@Neg.neg Real Real.instNeg (Real.sin qz125)))) Bool.true 135962219085 1099511627776 3332692625225 19403081695363072 Bool.true 172832632665 1099511627776 3335795179589 19403081695363072 (BSN.cpow_neg_s_mk qz13 119766 1000 25 qz14 rfl)

noncomputable abbrev qz418 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 25) qz15)

noncomputable def ep582 := @Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 25)) 5242881 1048576 1 1048576 104857 104858 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 25)) (Real.sqrt qz418) Bool.false 5242881 1048576 1 1048576 (BSN.sqrt_natCast_div_one 25) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz418) Bool.false 5242881 1048576 1 1048576 5242881 1048576 1 1048576 (BSN.sqrt_enclosure 25 1 2621440 2621441 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep583 := BSN.log_dyadic_bound 9 41 5 4 7545754341519345 524288 141176 124828057765224 4519905705 233982 50 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 9) (BSN.artanhQ 41) 0 4 124828057765224 7545754341519345 4519905705 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep584 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz582 119766 1000 0 1 3624129903009015 1125899906842624 31250000017647 4411750000000000000 43404754196377769049 112589990684262400 1871343751056755301 2205875000000000000000 qz19 (BSN.isNear_log_sfrac 25 1 3624129903009015 1125899906842624 31250000017647 4411750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz418) Bool.false 60802810194841294602240 18889465931478580854784 1000000000564704 141176000000000000000 3624129903009015 1125899906842624 31250000017647 4411750000000000000 (BSN.log_rat_reduce_isNear 25 1 4 50 32 233982 524288 24973259072661432 36028797018963968 141176 1000000000000000 rfl rfl rfl rfl (ep583 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep585 := nat_lit 4198317719886023439143889378906250000

noncomputable def ep586 := BSN.sin_dyadic_bound_f 1431425750 2147483648 2 1 1048576 282628 ep585 ep144 ep585 ep585 ep145 ep585 648319 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1431425750) qz21 0 1 ep585 ep144 ep585 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1431425750) qz285 0 1 ep585 ep145 ep585 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz419 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 202119137) qz34)

noncomputable def ep587 := @Enclosure.Real.IsNear.cos_image qz125 qz419 Bool.false 202119137 524288 445 524288 Bool.true 648319 1048576 1 141176 (@Enclosure.Real.IsNear.recentre' qz125 Bool.false 43404754196377769049 112589990684262400 1871343751056755301 2205875000000000000000 202119137 524288 445 524288 (ep584 rfl) rfl) (Enclosure.sfrac_false_div 202119137 524288) (BSN.cos_reduce1 qz419 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 50363816206463259377664) qz35) 226375608064910080 72057594037927936 Bool.false 648319 1048576 61 1000000000000000 282352 141176 (BSN.sin_reduce_arg_pos_rat_q1 202119137 524288 226375608064910080 72057594037927936 61 50363816206463259377664 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 648319 1048576 50363816206463259377664 75557863725914323419136 1431425750 2147483648 282628 282352 (ep586 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep588 := nat_lit 150022042406615134488824209534688993010274651172172229884722153169062500000000

noncomputable def ep589 := nat_lit 17625871677108978769799255474788393875376383520549526382446289062500000000

noncomputable def ep590 := nat_lit 450030875476491185508933030093117402243073200749475590601401566929062500000000

noncomputable def ep591 := BSN.cos_dyadic_bound_f 1431425750 2147483648 3 2 1048576 282628 ep588 ep58 ep589 ep590 ep61 ep589 824131 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1431425750) qz16 0 2 ep588 ep58 ep589 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1431425750) qz282 0 2 ep590 ep61 ep589 rfl rfl rfl rfl) rfl rfl

noncomputable def ep592 := @Enclosure.Real.IsNear.sin_image qz125 qz419 Bool.false 202119137 524288 445 524288 Bool.false 824131 1048576 1 141176 (@Enclosure.Real.IsNear.recentre' qz125 Bool.false 43404754196377769049 112589990684262400 1871343751056755301 2205875000000000000000 202119137 524288 445 524288 (ep584 rfl) rfl) (Enclosure.sfrac_false_div 202119137 524288) (BSN.sin_reduce1 qz419 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 50363816206463259377664) qz35) 226375608064910080 72057594037927936 Bool.false 824131 1048576 61 1000000000000000 282352 141176 (BSN.sin_reduce_arg_pos_rat_q1 202119137 524288 226375608064910080 72057594037927936 61 50363816206463259377664 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 824131 1048576 50363816206463259377664 75557863725914323419136 1431425750 2147483648 282628 282352 (ep591 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz420 := (@Enclosure.Real.IsNear.recentre' qz124 Bool.false 209715 1048576 1 1048576 209715 1048576 1 1048576 (ep582 rfl rfl) rfl)

noncomputable def ep593 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz124 (Real.cos qz125)) (@HMul.hMul Real Real Real qz0 qz124 (@Neg.neg Real Real.instNeg (Real.sin qz125))) Bool.true 135962219085 1099511627776 3332692625225 19403081695363072 Bool.true 172832632665 1099511627776 3335795179589 19403081695363072 (@Enclosure.Real.IsNear.mulLit_ft qz124 (Real.cos qz125) 209715 1048576 1 1048576 648319 1048576 7918451 9252110336 135962219085 1099511627776 3332692625225 19403081695363072 qz420 (@Enclosure.Real.IsNear.recentre' (Real.cos qz125) Bool.true 648319 1048576 63347608 74016882688 648319 1048576 7918451 9252110336 (ep587 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz124 (@Neg.neg Real Real.instNeg (Real.sin qz125)) 209715 1048576 1 1048576 824131 1048576 7918451 9252110336 172832632665 1099511627776 3335795179589 19403081695363072 qz420 (@Enclosure.Real.IsNear.neg (Real.sin qz125) Bool.false 824131 1048576 7918451 9252110336 (@Enclosure.Real.IsNear.recentre' (Real.sin qz125) Bool.false 824131 1048576 63347608 74016882688 824131 1048576 7918451 9252110336 (ep592 rfl rfl) rfl)) rfl)

noncomputable def ep594 := @ep579 135962219085 1099511627776 3332692625225 19403081695363072 Bool.true 172832632665 1099511627776 3335795179589 19403081695363072 Bool.false ep580 1419048785517 549755813888 31813266618337 4850770423840768 Bool.true 3239778270017522499584 5893122343 1099511627776 127229910415241 19403081695363072 EMRow39.d8 (ep581 ep593) rfl rfl

noncomputable abbrev qz126 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 26)))

noncomputable abbrev qz583 := (Real.log (Enclosure.sfrac Bool.false 26 1))

noncomputable abbrev qz127 := (@HMul.hMul Real Real Real qz268 qz279 qz583)

noncomputable def ep595 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz416 qz7) (Complex.mk (@HMul.hMul Real Real Real qz0 qz126 (Real.cos qz127)) (@HMul.hMul Real Real Real qz0 qz126 (@Neg.neg Real Real.instNeg (Real.sin qz127)))) Bool.false 171466572901 1099511627776 3275107066685 19403081695363072 Bool.true 65376583059 549755813888 1635806647989 9701540847681536 (BSN.cpow_neg_s_mk qz13 119766 1000 26 qz14 rfl)

noncomputable abbrev qz421 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 26) qz15)

noncomputable def ep596 := @Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 26)) 5346709 1048576 1 1048576 102821 102822 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 26)) (Real.sqrt qz421) Bool.false 5346709 1048576 1 1048576 (BSN.sqrt_natCast_div_one 26) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz421) Bool.false 5346709 1048576 1 1048576 5346709 1048576 1 1048576 (BSN.sqrt_enclosure 26 1 2673354 2673355 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep597 := BSN.log_dyadic_bound 10 42 5 4 9150106136613120 524288 141176 179034245376000 10500000000 254545 52 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 10) (BSN.artanhQ 42) 0 4 179034245376000 9150106136613120 10500000000 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep598 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz583 119766 1000 0 1 3668288609262839 1125899906842624 31250000017647 4411750000000000000 219668126788486587837 562949953421312000 1871343751056755301 2205875000000000000000 qz19 (BSN.isNear_log_sfrac 26 1 3668288609262839 1125899906842624 31250000017647 4411750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz421) Bool.false 61543670347942250676224 18889465931478580854784 1000000000564704 141176000000000000000 3668288609262839 1125899906842624 31250000017647 4411750000000000000 (BSN.log_rat_reduce_isNear 26 1 4 52 32 254545 524288 24973259072661432 36028797018963968 141176 1000000000000000 rfl rfl rfl rfl (ep597 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep599 := nat_lit 3831328864469691416326305148322249281

noncomputable def ep600 := BSN.cos_dyadic_bound_f 1399063279 2147483648 2 1 1048576 282628 ep599 ep140 ep599 ep599 ep141 ep599 833807 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1399063279) qz16 0 1 ep599 ep140 ep599 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1399063279) qz282 0 1 ep599 ep141 ep599 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz422 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 204581885) qz34)

noncomputable def ep601 := @Enclosure.Real.IsNear.cos_image qz127 qz422 Bool.false 204581885 524288 891 1048576 Bool.false 833807 1048576 1 141176 (@Enclosure.Real.IsNear.recentre' qz127 Bool.false 219668126788486587837 562949953421312000 1871343751056755301 2205875000000000000000 204581885 524288 891 1048576 (ep598 rfl) rfl) (Enclosure.sfrac_false_div 204581885 524288) (BSN.cos_reduce0 qz422 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 49225163006494428364800) qz35) 226375608064910080 72057594037927936 Bool.false 833807 1048576 62 1000000000000000 282352 141176 (BSN.sin_reduce_arg_pos_rat_q0 204581885 524288 226375608064910080 72057594037927936 62 49225163006494428364800 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 833807 1048576 49225163006494428364800 75557863725914323419136 1399063279 2147483648 282628 282352 (ep600 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep602 := BSN.sin_dyadic_bound_f 1399063279 2147483648 2 1 1048576 282628 ep599 ep144 ep599 ep599 ep145 ep599 635826 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1399063279) qz21 0 1 ep599 ep144 ep599 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1399063279) qz285 0 1 ep599 ep145 ep599 rfl rfl rfl rfl) rfl rfl

noncomputable def ep603 := @Enclosure.Real.IsNear.sin_image qz127 qz422 Bool.false 204581885 524288 891 1048576 Bool.false 635826 1048576 1 141176 (@Enclosure.Real.IsNear.recentre' qz127 Bool.false 219668126788486587837 562949953421312000 1871343751056755301 2205875000000000000000 204581885 524288 891 1048576 (ep598 rfl) rfl) (Enclosure.sfrac_false_div 204581885 524288) (BSN.sin_reduce0 qz422 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 49225163006494428364800) qz35) 226375608064910080 72057594037927936 Bool.false 635826 1048576 62 1000000000000000 282352 141176 (BSN.sin_reduce_arg_pos_rat_q0 204581885 524288 226375608064910080 72057594037927936 62 49225163006494428364800 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 635826 1048576 49225163006494428364800 75557863725914323419136 1399063279 2147483648 282628 282352 (ep602 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz423 := (@Enclosure.Real.IsNear.recentre' qz126 Bool.false 205643 1048576 1 1048576 205643 1048576 1 1048576 (ep596 rfl rfl) rfl)

noncomputable def ep604 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz126 (Real.cos qz127)) (@HMul.hMul Real Real Real qz0 qz126 (@Neg.neg Real Real.instNeg (Real.sin qz127))) Bool.false 171466572901 1099511627776 3275107066685 19403081695363072 Bool.true 65376583059 549755813888 1635806647989 9701540847681536 (@Enclosure.Real.IsNear.mulLit_ff qz126 (Real.cos qz127) 205643 1048576 1 1048576 833807 1048576 15854549 18504220672 171466572901 1099511627776 3275107066685 19403081695363072 qz423 (@Enclosure.Real.IsNear.recentre' (Real.cos qz127) Bool.false 833807 1048576 126836392 148033765376 833807 1048576 15854549 18504220672 (ep601 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz126 (@Neg.neg Real Real.instNeg (Real.sin qz127)) 205643 1048576 1 1048576 317913 524288 15854549 18504220672 65376583059 549755813888 1635806647989 9701540847681536 qz423 (@Enclosure.Real.IsNear.neg (Real.sin qz127) Bool.false 317913 524288 15854549 18504220672 (@Enclosure.Real.IsNear.recentre' (Real.sin qz127) Bool.false 635826 1048576 126836392 148033765376 317913 524288 15854549 18504220672 (ep603 rfl rfl) rfl)) rfl)

noncomputable def ep605 := @ep576 171466572901 1099511627776 3275107066685 19403081695363072 Bool.true 65376583059 549755813888 1635806647989 9701540847681536 Bool.false ep577 3009564143935 1099511627776 130528173540033 19403081695363072 Bool.true 75122091527651477946368 136646288461 1099511627776 130501523711219 19403081695363072 (ep578 (BSN.head_sum_c_succ qz5 25 26 rfl rfl) (ep594 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep595 ep604) rfl rfl

noncomputable abbrev qz128 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 27)))

noncomputable abbrev qz584 := (Real.log (Enclosure.sfrac Bool.false 27 1))

noncomputable abbrev qz129 := (@HMul.hMul Real Real Real qz268 qz279 qz584)

noncomputable def ep606 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz415 qz7) (Complex.mk (@HMul.hMul Real Real Real qz0 qz128 (Real.cos qz129)) (@HMul.hMul Real Real Real qz0 qz128 (@Neg.neg Real Real.instNeg (Real.sin qz129)))) Bool.false 46889813841 549755813888 1603824433373 9701540847681536 Bool.false 47421352407 274877906944 804008918521 4850770423840768 (BSN.cpow_neg_s_mk qz13 119766 1000 27 qz14 rfl)

noncomputable abbrev qz424 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 27) qz15)

noncomputable def ep607 := @Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 27)) 5448561 1048576 1 1048576 100899 100900 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 27)) (Real.sqrt qz424) Bool.false 5448561 1048576 1 1048576 (BSN.sqrt_natCast_div_one 27) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz424) Bool.false 5448561 1048576 1 1048576 5448561 1048576 1 1048576 (BSN.sqrt_enclosure 27 1 2724280 2724281 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep608 := BSN.log_dyadic_bound 11 43 5 4 11045349262332945 524288 141176 250863800262504 22507682505 274332 54 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 11) (BSN.artanhQ 43) 0 4 250863800262504 11045349262332945 22507682505 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep609 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz584 119766 1000 0 1 3710780868205815 1125899906842624 31250000017647 4411750000000000000 44442538146153763929 112589990684262400 1871343751056755301 2205875000000000000000 qz19 (BSN.isNear_log_sfrac 27 1 3710780868205815 1125899906842624 31250000017647 4411750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz424) Bool.false 62256572154556490711040 18889465931478580854784 1000000000564704 141176000000000000000 3710780868205815 1125899906842624 31250000017647 4411750000000000000 (BSN.log_rat_reduce_isNear 27 1 4 54 32 274332 524288 24973259072661432 36028797018963968 141176 1000000000000000 rfl rfl rfl rfl (ep608 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep610 := nat_lit 945267677393654382348236403573556641

noncomputable def ep611 := BSN.sin_dyadic_bound_f 986026761 2147483648 2 1 1048576 282628 ep610 ep144 ep610 ep610 ep145 ep610 464718 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 986026761) qz21 0 1 ep610 ep144 ep610 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 986026761) qz285 0 1 ep610 ep145 ep610 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz425 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 206951695) qz34)

noncomputable def ep612 := @Enclosure.Real.IsNear.cos_image qz129 qz425 Bool.false 206951695 524288 891 1048576 Bool.false 464718 1048576 1 141176 (@Enclosure.Real.IsNear.recentre' qz129 Bool.false 44442538146153763929 112589990684262400 1871343751056755301 2205875000000000000000 206951695 524288 891 1048576 (ep609 rfl) rfl) (Enclosure.sfrac_false_div 206951695 524288) (BSN.cos_reduce3 qz425 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 34692732457131704320000) qz35) 226375608064910080 72057594037927936 Bool.false 464718 1048576 62 1000000000000000 282352 141176 (BSN.sin_reduce_arg_pos_rat_q3 206951695 524288 226375608064910080 72057594037927936 62 34692732457131704320000 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 464718 1048576 34692732457131704320000 75557863725914323419136 986026761 2147483648 282628 282352 (ep611 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep613 := BSN.cos_dyadic_bound_f 986026761 2147483648 2 1 1048576 282628 ep610 ep140 ep610 ep610 ep141 ep610 939972 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 986026761) qz16 0 1 ep610 ep140 ep610 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 986026761) qz282 0 1 ep610 ep141 ep610 rfl rfl rfl rfl) rfl rfl

noncomputable def ep614 := @Enclosure.Real.IsNear.sin_image qz129 qz425 Bool.false 206951695 524288 891 1048576 Bool.true 939972 1048576 1 141176 (@Enclosure.Real.IsNear.recentre' qz129 Bool.false 44442538146153763929 112589990684262400 1871343751056755301 2205875000000000000000 206951695 524288 891 1048576 (ep609 rfl) rfl) (Enclosure.sfrac_false_div 206951695 524288) (BSN.sin_reduce3 qz425 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 34692732457131704320000) qz35) 226375608064910080 72057594037927936 Bool.false 939972 1048576 62 1000000000000000 282352 141176 (BSN.sin_reduce_arg_pos_rat_q3 206951695 524288 226375608064910080 72057594037927936 62 34692732457131704320000 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 939972 1048576 34692732457131704320000 75557863725914323419136 986026761 2147483648 282628 282352 (ep613 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz426 := (@Enclosure.Real.IsNear.recentre' qz128 Bool.false 201799 1048576 1 1048576 201799 1048576 1 1048576 (ep607 rfl rfl) rfl)

noncomputable def ep615 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz128 (Real.cos qz129)) (@HMul.hMul Real Real Real qz0 qz128 (@Neg.neg Real Real.instNeg (Real.sin qz129))) Bool.false 46889813841 549755813888 1603824433373 9701540847681536 Bool.false 47421352407 274877906944 804008918521 4850770423840768 (@Enclosure.Real.IsNear.mulLit_ff qz128 (Real.cos qz129) 201799 1048576 1 1048576 232359 524288 15854549 18504220672 46889813841 549755813888 1603824433373 9701540847681536 qz426 (@Enclosure.Real.IsNear.recentre' (Real.cos qz129) Bool.false 464718 1048576 126836392 148033765376 232359 524288 15854549 18504220672 (ep612 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz128 (@Neg.neg Real Real.instNeg (Real.sin qz129)) 201799 1048576 1 1048576 234993 262144 15854549 18504220672 47421352407 274877906944 804008918521 4850770423840768 qz426 (@Enclosure.Real.IsNear.neg (Real.sin qz129) Bool.true 234993 262144 15854549 18504220672 (@Enclosure.Real.IsNear.recentre' (Real.sin qz129) Bool.true 939972 1048576 126836392 148033765376 234993 262144 15854549 18504220672 (ep614 rfl rfl) rfl)) rfl)

noncomputable def ep616 := @ep573 46889813841 549755813888 1603824433373 9701540847681536 Bool.false 47421352407 274877906944 804008918521 4850770423840768 Bool.false ep574 3103343771617 1099511627776 133735822406779 19403081695363072 Bool.false 14579282612534166683648 53039121167 1099511627776 133717559385303 19403081695363072 (ep575 (BSN.head_sum_c_succ qz5 26 27 rfl rfl) (ep605 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep606 ep615) rfl rfl

noncomputable abbrev qz130 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 28)))

noncomputable abbrev qz585 := (Real.log (Enclosure.sfrac Bool.false 28 1))

noncomputable abbrev qz131 := (@HMul.hMul Real Real Real qz268 qz279 qz585)

noncomputable def ep617 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz414 qz7) (Complex.mk (@HMul.hMul Real Real Real qz0 qz130 (Real.cos qz131)) (@HMul.hMul Real Real Real qz0 qz130 (@Neg.neg Real Real.instNeg (Real.sin qz131)))) Bool.true 206701645507 1099511627776 3156711239511 19403081695363072 Bool.false 10614601095 549755813888 1570097185519 9701540847681536 (BSN.cpow_neg_s_mk qz13 119766 1000 28 qz14 rfl)

noncomputable abbrev qz427 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 28) qz15)

noncomputable def ep618 := @Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 28)) 5548543 1048576 1 1048576 99081 99082 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 28)) (Real.sqrt qz427) Bool.false 5548543 1048576 1 1048576 (BSN.sqrt_natCast_div_one 28) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz427) Bool.false 5548543 1048576 1 1048576 5548543 1048576 1 1048576 (BSN.sqrt_enclosure 28 1 2774271 2774272 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep619 := BSN.log_dyadic_bound 12 44 5 4 13275571325829120 524288 141176 344661139390464 45148078080 293399 56 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 12) (BSN.artanhQ 44) 0 4 344661139390464 13275571325829120 45148078080 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep620 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz585 119766 1000 0 1 3751726938922231 1125899906842624 31250000017647 4411750000000000000 224664664283479958973 562949953421312000 1871343751056755301 2205875000000000000000 qz19 (BSN.isNear_log_sfrac 28 1 3751726938922231 1125899906842624 31250000017647 4411750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz427) Bool.false 62943533227317076688896 18889465931478580854784 1000000000564704 141176000000000000000 3751726938922231 1125899906842624 31250000017647 4411750000000000000 (BSN.log_rat_reduce_isNear 28 1 4 56 32 293399 524288 24973259072661432 36028797018963968 141176 1000000000000000 rfl rfl rfl rfl (ep619 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep621 := nat_lit 2333459366957222380558346591912976

noncomputable def ep622 := BSN.cos_dyadic_bound_f 219786018 2147483648 2 1 1048576 282628 ep621 ep140 ep621 ep621 ep141 ep621 1043089 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 219786018) qz16 0 1 ep621 ep140 ep621 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 219786018) qz282 0 1 ep621 ep141 ep621 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz428 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 418470547) qz17)

noncomputable def ep623 := @Enclosure.Real.IsNear.cos_image qz131 qz428 Bool.false 418470547 1048576 445 524288 Bool.true 1043089 1048576 1 141176 (@Enclosure.Real.IsNear.recentre' qz131 Bool.false 224664664283479958973 562949953421312000 1871343751056755301 2205875000000000000000 418470547 1048576 445 524288 (ep620 rfl) rfl) (Enclosure.sfrac_false_div 418470547 1048576) (BSN.cos_reduce2 qz428 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 15466066134411629297664) qz20) 226375608064910080 72057594037927936 Bool.false 1043089 1048576 63 1000000000000000 282352 141176 (BSN.sin_reduce_arg_pos_rat_q2 418470547 1048576 226375608064910080 72057594037927936 63 15466066134411629297664 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1043089 1048576 15466066134411629297664 151115727451828646838272 219786018 2147483648 282628 282352 (ep622 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep624 := BSN.sin_dyadic_bound_f 219786018 2147483648 1 0 1048576 282628 0 1 1 0 1 1 107130 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 219786018) qz21 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 219786018) qz285 0 0 rfl) rfl rfl

noncomputable def ep625 := @Enclosure.Real.IsNear.sin_image qz131 qz428 Bool.false 418470547 1048576 445 524288 Bool.true 107130 1048576 1 141176 (@Enclosure.Real.IsNear.recentre' qz131 Bool.false 224664664283479958973 562949953421312000 1871343751056755301 2205875000000000000000 418470547 1048576 445 524288 (ep620 rfl) rfl) (Enclosure.sfrac_false_div 418470547 1048576) (BSN.sin_reduce2 qz428 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 15466066134411629297664) qz20) 226375608064910080 72057594037927936 Bool.false 107130 1048576 63 1000000000000000 282352 141176 (BSN.sin_reduce_arg_pos_rat_q2 418470547 1048576 226375608064910080 72057594037927936 63 15466066134411629297664 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 107130 1048576 15466066134411629297664 151115727451828646838272 219786018 2147483648 282628 282352 (ep624 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz429 := (@Enclosure.Real.IsNear.recentre' qz130 Bool.false 198163 1048576 1 1048576 198163 1048576 1 1048576 (ep618 rfl rfl) rfl)

noncomputable def ep626 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz130 (Real.cos qz131)) (@HMul.hMul Real Real Real qz0 qz130 (@Neg.neg Real Real.instNeg (Real.sin qz131))) Bool.true 206701645507 1099511627776 3156711239511 19403081695363072 Bool.false 10614601095 549755813888 1570097185519 9701540847681536 (@Enclosure.Real.IsNear.mulLit_ft qz130 (Real.cos qz131) 198163 1048576 1 1048576 1043089 1048576 7918451 9252110336 206701645507 1099511627776 3156711239511 19403081695363072 qz429 (@Enclosure.Real.IsNear.recentre' (Real.cos qz131) Bool.true 1043089 1048576 63347608 74016882688 1043089 1048576 7918451 9252110336 (ep623 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz130 (@Neg.neg Real Real.instNeg (Real.sin qz131)) 198163 1048576 1 1048576 53565 524288 7918451 9252110336 10614601095 549755813888 1570097185519 9701540847681536 qz429 (@Enclosure.Real.IsNear.neg (Real.sin qz131) Bool.true 53565 524288 7918451 9252110336 (@Enclosure.Real.IsNear.recentre' (Real.sin qz131) Bool.true 107130 1048576 63347608 74016882688 53565 524288 7918451 9252110336 (ep625 rfl rfl) rfl)) rfl)

noncomputable def ep627 := @ep570 206701645507 1099511627776 3156711239511 19403081695363072 Bool.false 10614601095 549755813888 1570097185519 9701540847681536 Bool.false ep571 1448321063055 549755813888 68446266823145 9701540847681536 Bool.false 40829442553224695382016 74268323357 1099511627776 136857753756341 19403081695363072 (ep572 (BSN.head_sum_c_succ qz5 27 28 rfl rfl) (ep616 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep617 ep626) rfl rfl

noncomputable abbrev qz132 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 29)))

noncomputable abbrev qz586 := (Real.log (Enclosure.sfrac Bool.false 29 1))

noncomputable abbrev qz133 := (@HMul.hMul Real Real Real qz268 qz279 qz586)

noncomputable def ep628 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz413 qz7) (Complex.mk (@HMul.hMul Real Real Real qz0 qz132 (Real.cos qz133)) (@HMul.hMul Real Real Real qz0 qz132 (@Neg.neg Real Real.instNeg (Real.sin qz133)))) Bool.false 80877017115 1099511627776 3094464238651 19403081695363072 Bool.true 187471796715 1099511627776 3104124912331 19403081695363072 (BSN.cpow_neg_s_mk qz13 119766 1000 29 qz14 rfl)

noncomputable abbrev qz430 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 29) qz15)

noncomputable def ep629 := @Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 29)) 5646755 1048576 1 1048576 97357 97358 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 29)) (Real.sqrt qz430) Bool.false 5646755 1048576 1 1048576 (BSN.sqrt_natCast_div_one 29) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz430) Bool.false 5646755 1048576 1 1048576 5646755 1048576 1 1048576 (BSN.sqrt_enclosure 29 1 2823377 2823378 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep630 := BSN.log_dyadic_bound 13 45 6 5 353956287581982421875 524288 141176 10371179520995104305 130276274797305 311797 58 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 13) (BSN.artanhQ 45) 0 5 10371179520995104305 353956287581982421875 130276274797305 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep631 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz586 119766 1000 0 1 3791236343078135 1125899906842624 31250000017647 4411750000000000000 45406121186509591641 112589990684262400 1871343751056755301 2205875000000000000000 qz19 (BSN.isNear_log_sfrac 29 1 3791236343078135 1125899906842624 31250000017647 4411750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz430) Bool.false 63606391034871975772160 18889465931478580854784 1000000000564704 141176000000000000000 3791236343078135 1125899906842624 31250000017647 4411750000000000000 (BSN.log_rat_reduce_isNear 29 1 4 58 32 311797 524288 24973259072661432 36028797018963968 141176 1000000000000000 rfl rfl rfl rfl (ep630 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep632 := nat_lit 1394122263589657508182308977411612378660527076266922073695468320008616666235136

noncomputable def ep633 := nat_lit 1519138054614032151968843806046361293935690599231164894960659087174966477056

noncomputable def ep634 := nat_lit 4179328514659744460242989244622744413393709847602303891296483641851500065751296

noncomputable def ep635 := BSN.cos_dyadic_bound_f 2498616798 2147483648 3 2 1048576 282628 ep632 ep58 ep633 ep634 ep61 ep633 415361 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2498616798) qz16 0 2 ep632 ep58 ep633 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2498616798) qz282 0 2 ep634 ep61 ep633 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz431 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 26429841) (@Nat.cast Real Real.instNatCast 65536))

noncomputable abbrev qz432 := (@Nat.cast Real Real.instNatCast 9444732965739290427392)

noncomputable def ep636 := @Enclosure.Real.IsNear.cos_image qz133 qz431 Bool.false 26429841 65536 891 1048576 Bool.false 415361 1048576 1 141176 (@Enclosure.Real.IsNear.recentre' qz133 Bool.false 45406121186509591641 112589990684262400 1871343751056755301 2205875000000000000000 26429841 65536 891 1048576 (ep631 rfl) rfl) (Enclosure.sfrac_false_div 26429841 65536) (BSN.cos_reduce0 qz431 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 10989032893628203139072) qz432) 226375608064910080 72057594037927936 Bool.false 415361 1048576 64 1000000000000000 282352 141176 (BSN.sin_reduce_arg_pos_rat_q0 26429841 65536 226375608064910080 72057594037927936 64 10989032893628203139072 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 415361 1048576 10989032893628203139072 9444732965739290427392 2498616798 2147483648 282628 282352 (ep635 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep637 := nat_lit 2508204764017692289006581084296065192553800184801074800735874448745770026041600

noncomputable def ep638 := nat_lit 6566648158434104704866429473660857586022152223032631163525925346288257265336576

noncomputable def ep639 := BSN.sin_dyadic_bound_f 2498616798 2147483648 3 2 1048576 282628 ep637 ep65 ep633 ep638 ep67 ep633 962801 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2498616798) qz21 0 2 ep637 ep65 ep633 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2498616798) qz285 0 2 ep638 ep67 ep633 rfl rfl rfl rfl) rfl rfl

noncomputable def ep640 := @Enclosure.Real.IsNear.sin_image qz133 qz431 Bool.false 26429841 65536 891 1048576 Bool.false 962801 1048576 1 141176 (@Enclosure.Real.IsNear.recentre' qz133 Bool.false 45406121186509591641 112589990684262400 1871343751056755301 2205875000000000000000 26429841 65536 891 1048576 (ep631 rfl) rfl) (Enclosure.sfrac_false_div 26429841 65536) (BSN.sin_reduce0 qz431 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 10989032893628203139072) qz432) 226375608064910080 72057594037927936 Bool.false 962801 1048576 64 1000000000000000 282352 141176 (BSN.sin_reduce_arg_pos_rat_q0 26429841 65536 226375608064910080 72057594037927936 64 10989032893628203139072 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 962801 1048576 10989032893628203139072 9444732965739290427392 2498616798 2147483648 282628 282352 (ep639 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz433 := (@Enclosure.Real.IsNear.recentre' qz132 Bool.false 194715 1048576 1 1048576 194715 1048576 1 1048576 (ep629 rfl rfl) rfl)

noncomputable def ep641 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz132 (Real.cos qz133)) (@HMul.hMul Real Real Real qz0 qz132 (@Neg.neg Real Real.instNeg (Real.sin qz133))) Bool.false 80877017115 1099511627776 3094464238651 19403081695363072 Bool.true 187471796715 1099511627776 3104124912331 19403081695363072 (@Enclosure.Real.IsNear.mulLit_ff qz132 (Real.cos qz133) 194715 1048576 1 1048576 415361 1048576 15854549 18504220672 80877017115 1099511627776 3094464238651 19403081695363072 qz433 (@Enclosure.Real.IsNear.recentre' (Real.cos qz133) Bool.false 415361 1048576 126836392 148033765376 415361 1048576 15854549 18504220672 (ep636 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz132 (@Neg.neg Real Real.instNeg (Real.sin qz133)) 194715 1048576 1 1048576 962801 1048576 15854549 18504220672 187471796715 1099511627776 3104124912331 19403081695363072 qz433 (@Enclosure.Real.IsNear.neg (Real.sin qz133) Bool.false 962801 1048576 15854549 18504220672 (@Enclosure.Real.IsNear.recentre' (Real.sin qz133) Bool.false 962801 1048576 126836392 148033765376 962801 1048576 15854549 18504220672 (ep640 rfl rfl) rfl)) rfl)

noncomputable def ep642 := @ep567 80877017115 1099511627776 3094464238651 19403081695363072 Bool.true 187471796715 1099511627776 3104124912331 19403081695363072 Bool.false ep568 2977519143225 1099511627776 139986997884941 19403081695363072 Bool.true 124468535261751628791808 56601736679 549755813888 1093452177099 151586575745024 (ep569 (BSN.head_sum_c_succ qz5 28 29 rfl rfl) (ep627 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep628 ep641) rfl rfl

noncomputable def ep643 := @Enclosure.Complex.IsNear.mul qz119 (@HAdd.hAdd Complex Complex Complex qz4 qz120 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz80 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz122 qz123 (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1))))) Bool.false ep558 ep422 ep559 ep424 Bool.false

noncomputable abbrev qz134 := (Complex.re qz410)

noncomputable abbrev qz135 := (Complex.im qz410)

noncomputable def ep644 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 qz134 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz120 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz80 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz122 qz123 (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz135 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz120 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz80 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz122 qz123 (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1))))))) 12690101820065937648017 283887971095034418167808 655470585423019920041009

noncomputable def ep645 := nat_lit 8349618376523453962345512960

noncomputable def ep646 := nat_lit 1278774644572227108864000

noncomputable def ep647 := nat_lit 53967497510674570701890689

noncomputable def ep648 := nat_lit 11476498004909909975380564269308408685744095232

noncomputable def ep649 := @Enclosure.Real.IsNear.mulLit_ff qz134 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz120 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz80 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz122 qz123 (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))))) 49115658865 549755813888 1522156565463 9701540847681536 1291859064229

noncomputable abbrev qz434 := (@Nat.cast Real Real.instNatCast 30)

noncomputable abbrev qz136 := (@Inv.inv Real Real.instInv (Real.sqrt qz434))

noncomputable abbrev qz435 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) qz546 (Real.log (Enclosure.sfrac Bool.false 30 1)))

noncomputable abbrev qz137 := (Real.cos qz435)

noncomputable abbrev qz138 := (Real.sin qz435)

noncomputable abbrev qz587 := (@Neg.neg Real Real.instNeg qz138)

noncomputable def ep650 := @Enclosure.Complex.IsNear.of_eq qz119 (Complex.mk (@HMul.hMul Real Real Real qz0 qz136 qz137) (@HMul.hMul Real Real Real qz0 qz136 qz587)) Bool.false 49115658865 549755813888 1522156565463 9701540847681536 Bool.false 175066008565 1099511627776 3051395666141 19403081695363072 (BSN.cpow_neg_s_mk qz13 119766 1000 30 qz14 rfl)

noncomputable abbrev qz436 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 30) qz15)

noncomputable def ep651 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz434) 5743287 1048576 1 1048576 95721 95722 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz434) (Real.sqrt qz436) Bool.false 5743287 1048576 1 1048576 (BSN.sqrt_natCast_div_one 30) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz436) Bool.false 5743287 1048576 1 1048576 5743287 1048576 1 1048576 (BSN.sqrt_enclosure 30 1 2871643 2871644 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep652 := BSN.log_dyadic_bound 14 46 6 5 440963670083462507520 524288 141176 14425761949190022144 273345648952320 329571 60 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 14) (BSN.artanhQ 46) 0 5 14425761949190022144 440963670083462507520 273345648952320 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz139 := (Real.log (Enclosure.sfrac Bool.false 30 1))

noncomputable def ep653 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz139 119766 1000 0 1 3829405717437687 1125899906842624 31250000017647 4411750000000000000 229316302577321010621 562949953421312000 1871343751056755301 2205875000000000000000 qz19 (BSN.isNear_log_sfrac 30 1 3829405717437687 1125899906842624 31250000017647 4411750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz436) Bool.false 64246766873087041339392 18889465931478580854784 1000000000564704 141176000000000000000 3829405717437687 1125899906842624 31250000017647 4411750000000000000 (BSN.log_rat_reduce_isNear 30 1 4 60 32 329571 524288 24973259072661432 36028797018963968 141176 1000000000000000 rfl rfl rfl rfl (ep652 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep654 := nat_lit 1453903253946445280535050447691452416

noncomputable def ep655 := BSN.sin_dyadic_bound_f 1098079736 2147483648 2 1 1048576 282628 ep654 ep144 ep654 ep654 ep145 ep654 513110 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1098079736) qz21 0 1 ep654 ep144 ep654 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1098079736) qz285 0 1 ep654 ep145 ep654 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz140 := qz435

noncomputable abbrev qz437 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 213567449) qz34)

noncomputable def ep656 := @Enclosure.Real.IsNear.cos_image qz140 qz437 Bool.false 213567449 524288 891 1048576 Bool.false 513110 1048576 1 141176 (@Enclosure.Real.IsNear.recentre' qz140 Bool.false 229316302577321010621 562949953421312000 1871343751056755301 2205875000000000000000 213567449 524288 891 1048576 (ep653 rfl) rfl) (Enclosure.sfrac_false_div 213567449 524288) (BSN.cos_reduce3 qz437 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 38635246021642884743168) qz35) 226375608064910080 72057594037927936 Bool.false 513110 1048576 64 1000000000000000 282352 141176 (BSN.sin_reduce_arg_pos_rat_q3 213567449 524288 226375608064910080 72057594037927936 64 38635246021642884743168 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 513110 1048576 38635246021642884743168 75557863725914323419136 1098079736 2147483648 282628 282352 (ep655 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep657 := BSN.cos_dyadic_bound_f 1098079736 2147483648 2 1 1048576 282628 ep654 ep140 ep654 ep654 ep141 ep654 914455 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1098079736) qz16 0 1 ep654 ep140 ep654 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1098079736) qz282 0 1 ep654 ep141 ep654 rfl rfl rfl rfl) rfl rfl

noncomputable def ep658 := @Enclosure.Real.IsNear.sin_image qz140 qz437 Bool.false 213567449 524288 891 1048576 Bool.true 914455 1048576 1 141176 (@Enclosure.Real.IsNear.recentre' qz140 Bool.false 229316302577321010621 562949953421312000 1871343751056755301 2205875000000000000000 213567449 524288 891 1048576 (ep653 rfl) rfl) (Enclosure.sfrac_false_div 213567449 524288) (BSN.sin_reduce3 qz437 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 38635246021642884743168) qz35) 226375608064910080 72057594037927936 Bool.false 914455 1048576 64 1000000000000000 282352 141176 (BSN.sin_reduce_arg_pos_rat_q3 213567449 524288 226375608064910080 72057594037927936 64 38635246021642884743168 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 914455 1048576 38635246021642884743168 75557863725914323419136 1098079736 2147483648 282628 282352 (ep657 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz438 := (@Enclosure.Real.IsNear.recentre' qz136 Bool.false 191443 1048576 1 1048576 191443 1048576 1 1048576 (ep651 rfl rfl) rfl)

noncomputable def ep659 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz136 qz137) (@HMul.hMul Real Real Real qz0 qz136 qz587) Bool.false 49115658865 549755813888 1522156565463 9701540847681536 Bool.false 175066008565 1099511627776 3051395666141 19403081695363072 (@Enclosure.Real.IsNear.mulLit_ff qz136 qz137 191443 1048576 1 1048576 256555 524288 15854549 18504220672 49115658865 549755813888 1522156565463 9701540847681536 qz438 (@Enclosure.Real.IsNear.recentre' qz137 Bool.false 513110 1048576 126836392 148033765376 256555 524288 15854549 18504220672 (ep656 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz136 qz587 191443 1048576 1 1048576 914455 1048576 15854549 18504220672 175066008565 1099511627776 3051395666141 19403081695363072 qz438 (@Enclosure.Real.IsNear.neg qz138 Bool.true 914455 1048576 15854549 18504220672 (@Enclosure.Real.IsNear.recentre' qz138 Bool.true 914455 1048576 126836392 148033765376 914455 1048576 15854549 18504220672 (ep658 rfl rfl) rfl)) rfl)

noncomputable def ep660 := @ep649 2581946056080 0 1 12690101820065937648017 283887971095034418167808 655470585423019920041009 ep645 (@Enclosure.Complex.IsNear.re_isNear qz119 Bool.false 49115658865 549755813888 1522156565463 9701540847681536 Bool.false 175066008565 1099511627776 3051395666141 19403081695363072 (ep650 ep659))

noncomputable def ep661 := @Enclosure.Complex.IsNear.re_isNear (@HAdd.hAdd Complex Complex Complex qz4 qz120 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz80 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz122 qz123 (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1))))) Bool.false 1291859064229 2581946056080 0 1 Bool.false

noncomputable def ep662 := @Enclosure.Complex.IsNear.addLitP qz120 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz80 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz122 qz123 (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) Bool.false 3578536189 7172072378 0 1 Bool.true 898245000

noncomputable def ep663 := @ep662 3586036189 0 1 Bool.false 1 720 0 1 Bool.false 19961 60000 0 1 Bool.false 2583718128458 1291859064229 2581946056080 0 1 Bool.false 17686168368629 17686168368629 215162171340000 0 1

noncomputable abbrev qz141 := (@HDiv.hDiv Complex Complex Complex qz386 qz411 (@HSub.hSub Complex Complex Complex qz378 qz272 (1 : Complex)))

noncomputable def ep664 := @Enclosure.Complex.IsNear.addLitP qz141 qz97 Bool.true 60000000 57376579024 0 1 Bool.true 14371920000 57376579024 0 1

noncomputable def ep665 := @Enclosure.Complex.IsNear.of_eq qz141 (Complex.mk (Enclosure.sfrac Bool.true 60000000 57376579024) (Enclosure.sfrac Bool.true 14371920000 57376579024)) Bool.true 60000000 57376579024 0 1 Bool.true 14371920000 57376579024 0 1

noncomputable def ep666 := @ep664 Bool.false 1 2 0 1 Bool.false 0 1 0 1 Bool.false 57256579024 3578536189 7172072378 0 1 Bool.true 14371920000 898245000 3586036189 0 1 (ep665 (BSN.N_div_s_sub_one_mk qz13 119766 1000 30 qz14 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 60000000 57376579024) (Enclosure.sfrac Bool.true 14371920000 57376579024) Bool.true 60000000 57376579024 0 1 Bool.true 14371920000 57376579024 0 1 (Enclosure.Real.IsNear.const Bool.true 60000000 57376579024) (Enclosure.Real.IsNear.const Bool.true 14371920000 57376579024))) qz98 rfl

noncomputable abbrev qz142 := (@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 1)))

noncomputable abbrev qz143 := (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz412 qz411 1))

noncomputable def ep667 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz80 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz122 qz123 (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) (@HAdd.hAdd Complex Complex Complex qz4 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz80 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz122 qz123 (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz99)) ↑qz142) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz143)) Bool.false 1 720 0 1

noncomputable def ep668 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz80 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz122 qz123 (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz99)) ↑qz142) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz143) Bool.false 0 1 0 1 Bool.false

noncomputable def ep669 := @ep668 0 1 0 1 Bool.false 1 720 0 1 Bool.false 19961 60000 0 1 Bool.false 1 1 720 0 1 Bool.false 19961 19961 60000 0

noncomputable def ep670 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz80 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz122 qz123 (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) (Complex.mk qz10 qz10) Bool.false 0 1 0 1 Bool.false

noncomputable def ep671 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz99)) ↑qz142) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz143 Bool.false 1 720 0 1 Bool.false 19961 60000 0 1

noncomputable def ep672 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz99)) ↑qz142) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz143)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz99)) ↑qz142) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz143)) 1 720 0 1 0 1 0

noncomputable def ep673 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz99)) ↑qz142) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz143) 1 24 0 1 1 30 0 1 1

noncomputable def ep674 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz99)) ↑qz142)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz99)) ↑qz142)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) 1 24 0 1 0 1 0 1 1

noncomputable def ep675 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz99)) ↑qz142)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 1 2 0 1 1 24 0

noncomputable def ep676 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz99)) ↑qz142) (Complex.mk (Enclosure.sfrac Bool.false 1 12) qz10) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (BSN.bern_coeff_mk 1 1 6 2 Bool.false BSN.bern_real_1 EMRow39.d9 rfl) qz400

noncomputable def ep677 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) qz5 Bool.false 1 2 0 1 Bool.false 119766 1000 0 1 (BSN.ascPochhammer_one_eval qz5)

noncomputable def ep678 := ep677 (@Enclosure.Complex.IsNear.of_eq qz5 (Complex.mk qz92 qz13) Bool.false 1 2 0 1 Bool.false 119766 1000 0 1 (BSN.s_crit_mk qz13 Bool.false 119766 1000 qz14) (@Enclosure.Complex.IsNear.mk qz92 qz13 Bool.false 1 2 0 1 Bool.false 119766 1000 0 1 qz392 qz19))

noncomputable def ep679 := @ep675 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz99)) ↑qz142) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep676) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 119766 1000 0 1 ep678)

noncomputable def ep680 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz99)) ↑qz142)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 119766 1000 0 1 0 1 0

noncomputable def ep681 := @ep680 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz99)) ↑qz142) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep676) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 119766 1000 0 1 ep678)

noncomputable def ep682 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz99)) ↑qz142)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz99)) ↑qz142)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) 19961 2000 0 1 0 1 0 1 19961

noncomputable def ep683 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz99)) ↑qz142)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 119766 1000 0 1 19961 2000 0

noncomputable def ep684 := @ep683 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz99)) ↑qz142) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep676) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 119766 1000 0 1 ep678)

noncomputable def ep685 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz99)) ↑qz142)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 1 2 0 1 0 1 0

noncomputable def ep686 := @ep685 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz99)) ↑qz142) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep676) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 119766 1000 0 1 ep678)

noncomputable def ep687 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz99)) ↑qz142) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 24 0 1 Bool.false 19961 2000 0 1 (@ep674 1 24 0 1 (ep679 rfl) (ep681 rfl) rfl rfl) (@ep682 19961 2000 0 1 (ep684 rfl) (ep686 rfl) rfl rfl)

noncomputable def ep688 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz99)) ↑qz142) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 19961 2000 0 1 ep687

noncomputable abbrev qz144 := (@Enclosure.Complex.IsNear.of_eq (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz412 qz411 1)) (Complex.mk (Enclosure.sfrac Bool.false 1 30) qz278) Bool.false 1 30 0 1 Bool.false 0 1 0 1 (BSN.natCast_pow_inv_mk 30 1 30 EMRow39.d10 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 30) qz278 Bool.false 1 30 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 30) qz287))

noncomputable def ep689 := @ep673 720 0 1 ep688 (@Enclosure.Complex.IsNear.re_isNear qz143 Bool.false 1 30 0 1 Bool.false 0 1 0 1 qz144)

noncomputable def ep690 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz99)) ↑qz142) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz143) 19961 2000 0 1 0 1 0 1 0

noncomputable def ep691 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz99)) ↑qz142) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 19961 2000 0 1 ep687

noncomputable def ep692 := @ep690 1 0 1 ep691 (@Enclosure.Complex.IsNear.im_isNear qz143 Bool.false 1 30 0 1 Bool.false 0 1 0 1 qz144)

noncomputable def ep693 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz99)) ↑qz142) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz143)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz99)) ↑qz142) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz143)) 0 1 0 1 19961 60000 0

noncomputable def ep694 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz99)) ↑qz142) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz143) 1 24 0 1 0 1 0 1 0

noncomputable def ep695 := @ep694 1 0 1 ep688 (@Enclosure.Complex.IsNear.im_isNear qz143 Bool.false 1 30 0 1 Bool.false 0 1 0 1 qz144)

noncomputable def ep696 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz99)) ↑qz142) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz143) 19961 2000 0 1 1 30 0 1 19961

noncomputable def ep697 := @ep696 60000 0 1 ep691 (@Enclosure.Complex.IsNear.re_isNear qz143 Bool.false 1 30 0 1 Bool.false 0 1 0 1 qz144)

noncomputable def ep698 := @ep669 1 (@ep670 0 1 0 1 (BSN.bern_sum_base qz5 30) qz113) (ep671 (@ep672 1 1 1 720 0 1 (ep689 rfl) (ep692 rfl) rfl rfl) (@ep693 1 19961 19961 60000 0 1 (ep695 rfl) (ep697 rfl) rfl rfl)) rfl rfl rfl rfl rfl

noncomputable def ep699 := ep663 (ep666 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep667 Bool.false 19961 60000 0 1 (BSN.bern_sum_succ qz5 30 0 1 1 rfl rfl) (ep698 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl rfl

noncomputable def ep700 := @Enclosure.Real.IsNear.mulLit_ff qz135 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz120 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz80 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz122 qz123 (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))))) 175066008565 1099511627776 3051395666141 19403081695363072 17686168368629

noncomputable def ep701 := @ep700 215162171340000 0 1 16736469746510468061121 ep646 ep647 ep424 (@Enclosure.Complex.IsNear.im_isNear qz119 Bool.false 49115658865 549755813888 1522156565463 9701540847681536 Bool.false 175066008565 1099511627776 3051395666141 19403081695363072 (ep650 ep659))

noncomputable def ep702 := @Enclosure.Complex.IsNear.im_isNear (@HAdd.hAdd Complex Complex Complex qz4 qz120 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz80 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz122 qz123 (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1))))) Bool.false 1291859064229 2581946056080 0 1 Bool.false

noncomputable def ep703 := nat_lit 23657330924586201513984000

noncomputable def ep704 := nat_lit 8973705766730889451353409

noncomputable def ep705 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz134 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz120 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz80 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz122 qz123 (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz135 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz120 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz80 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz122 qz123 (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1))))))) 173733562444507106349217 ep703 ep704

noncomputable def ep706 := nat_lit 695801531376954496862126080000

noncomputable def ep707 := nat_lit 3941973149853338359570289

noncomputable def ep708 := nat_lit 50097710259140723774073077760

noncomputable def ep709 := nat_lit 31586838262076461606275696203513140936867577856

noncomputable def ep710 := @Enclosure.Real.IsNear.mulLit_ff qz134 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz120 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz80 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz122 qz123 (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))))) 49115658865 549755813888 1522156565463 9701540847681536 17686168368629

noncomputable def ep711 := @ep710 215162171340000 0 1 173733562444507106349217 ep703 ep704 ep706 (@Enclosure.Complex.IsNear.re_isNear qz119 Bool.false 49115658865 549755813888 1522156565463 9701540847681536 Bool.false 175066008565 1099511627776 3051395666141 19403081695363072 (ep650 ep659))

noncomputable def ep712 := @Enclosure.Real.IsNear.mulLit_ff qz135 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz120 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz80 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz122 qz123 (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))))) 175066008565 1099511627776 3051395666141 19403081695363072 1291859064229

noncomputable def ep713 := @ep712 2581946056080 0 1 1222489783800470265521 15345295734866725306368 ep707 ep708 (@Enclosure.Complex.IsNear.im_isNear qz119 Bool.false 49115658865 549755813888 1522156565463 9701540847681536 Bool.false 175066008565 1099511627776 3051395666141 19403081695363072 (ep650 ep659))

noncomputable abbrev qz588 := (ep699 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable def ep714 := @ep643 ep560 ep553 ep561 ep555 (@ep644 ep645 16736469746510468061121 ep646 ep647 ep424 ep648 ep558 ep422 ep559 ep424 (ep660 (@ep661 17686168368629 215162171340000 0 1 qz588) rfl) (ep701 (@ep702 17686168368629 215162171340000 0 1 qz588) rfl) rfl rfl) (@ep705 ep706 1222489783800470265521 15345295734866725306368 ep707 ep708 ep709 ep560 ep553 ep561 ep555 (ep711 (@ep702 17686168368629 215162171340000 0 1 qz588) rfl) (ep713 (@ep661 17686168368629 215162171340000 0 1 qz588) rfl) rfl rfl)

noncomputable def ep715 := @ep564 ep554 ep555 (@ep565 151586575745024 (BSN.head_sum_c_eq qz5 30) (ep566 (BSN.head_sum_c_succ qz5 29 30 rfl rfl) (ep642 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))) ep714 rfl rfl rfl

noncomputable def ep716 := @Enclosure.Complex.IsNear.re_isNear (zetaApproximant qz5 1 30) Bool.false ep421 ep422 ep423 ep424 Bool.true 282978900467610012708431 ep553 ep554 ep555 (@ep556 ep424 Bool.true 282978900467610012708431 ep553 ep554 ep555 (BSN.zetaApproximant_eq_folded' qz5 1 30 rfl) (ep715 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

noncomputable def ep717 := @Enclosure.Real.IsNear.mulLit_tt (Real.sin (@HSub.hSub Real Real Real qz381 (Complex.im (@HSub.hSub Complex Complex Complex qz73 qz74 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz75 (@Nat.cast Complex Complex.instNatCast j))))) qz76)) (Complex.im (zetaApproximant qz5 1 30)) 233 524288 3294937

noncomputable def ep718 := @Enclosure.Real.IsNear.recentre' (Real.sin (@HSub.hSub Real Real Real qz381 (Complex.im (@HSub.hSub Complex Complex Complex qz73 qz74 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz75 (@Nat.cast Complex Complex.instNatCast j))))) qz76)) Bool.true 466 1048576 26359496

noncomputable def ep719 := @Enclosure.Real.IsNear.sin_image (@HSub.hSub Real Real Real qz381 (Complex.im (@HSub.hSub Complex Complex Complex qz73 qz74 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz75 (@Nat.cast Complex Complex.instNatCast j))))) qz76) qz382 Bool.false 121885817 1048576 183

noncomputable def ep720 := BSN.sin_dyadic_bound_f 955682 2147483648 1 0 1048576 282628 0 1 1 0 1 1 466 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 955682) qz21 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 955682) qz285 0 0 rfl) rfl rfl

noncomputable def ep721 := @ep719 524288 Bool.true 466 1048576 1 141176 (@ep429 121885817 1048576 183 524288 ep550 rfl) (Enclosure.sfrac_false_div 121885817 1048576) (BSN.sin_reduce2 qz382 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 67250166285681557504) qz20) 226375608064910080 72057594037927936 Bool.false 466 1048576 18 1000000000000000 282352 141176 (BSN.sin_reduce_arg_pos_rat_q2 121885817 1048576 226375608064910080 72057594037927936 18 67250166285681557504 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 466 1048576 67250166285681557504 151115727451828646838272 955682 2147483648 282628 282352 (ep720 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep722 := @Enclosure.Complex.IsNear.im_isNear (zetaApproximant qz5 1 30) Bool.false ep421 ep422 ep423 ep424 Bool.true 282978900467610012708431 ep553 ep554 ep555 (@ep556 ep424 Bool.true 282978900467610012708431 ep553 ep554 ep555 (BSN.zetaApproximant_eq_folded' qz5 1 30 rfl) (ep715 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

theorem EMRow39.d11 : Enclosure.Real.IsNear (hardyZApproximantEM 1 30 qz13) Bool.true ep404 ep405 ep406 ep407 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantEM 1 30 qz13) ep408 Bool.true ep404 ep405 ep406 ep407 (@Eq.refl Real ep408) (@ep409 Bool.true ep404 ep405 ep406 ep407 (BSN.re_exp_mul (@HSub.hSub Real Real Real qz381 (Complex.im (@HSub.hSub Complex Complex Complex qz73 qz74 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz75 (@Nat.cast Complex Complex.instNatCast j))))) qz76) (zetaApproximant qz5 1 30)) (@ep411 ep412 ep413 ep414 ep415 ep416 ep417 ep418 ep419 ep404 ep405 ep406 ep407 (@ep420 9252110336 ep421 ep422 ep423 ep424 ep410 ep412 ep413 ep414 (@ep425 74016882688 1048575 1048576 3294937 9252110336 (ep552 rfl rfl) rfl) ep716 rfl) (@ep717 9252110336 282978900467610012708431 ep553 ep554 ep555 ep415 ep416 ep417 ep418 (@ep718 74016882688 233 524288 3294937 9252110336 (ep721 rfl rfl) rfl) ep722 rfl) rfl rfl))

noncomputable abbrev qz616 := (@HAdd.hAdd Complex Complex Complex (@instHAdd Complex Complex.instAdd) (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (2 : Complex)) (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul) Complex.I ↑(Enclosure.sfrac Bool.false 121891 1000)))

noncomputable abbrev qz589 := qz616

noncomputable abbrev qz439 := qz589

noncomputable abbrev qz145 := (BSN.headSumC qz439 9)

noncomputable abbrev qz146 := qz439

noncomputable abbrev qz590 := (@Neg.neg Complex Complex.instNeg qz616)

noncomputable abbrev qz440 := qz590

noncomputable abbrev qz147 := qz440

noncomputable abbrev qz591 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 8) qz147)

noncomputable def ep723 := @Enclosure.Complex.IsNear.of_eq qz145 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz146 8) qz591) Bool.false 454985951451 1099511627776 57069931682793 19403081695363072 Bool.true 449240310407 1099511627776 57122067591359 19403081695363072

noncomputable def ep724 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz146 8) qz591 Bool.false 331888401381 549755813888 25538795990997 9701540847681536 Bool.true 121335986177 1099511627776 51124057962401 19403081695363072 Bool.true

noncomputable abbrev qz592 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 7) qz147)

noncomputable def ep725 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz146 8) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz146 7) qz592) Bool.false 331888401381 549755813888 25538795990997 9701540847681536 Bool.true 121335986177 1099511627776 51124057962401 19403081695363072

noncomputable def ep726 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz146 7) qz592 Bool.false 332201498131 549755813888 22344542319465 9701540847681536 Bool.true 536912076727 1099511627776 44717074316219 19403081695363072 Bool.true

noncomputable abbrev qz593 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 6) qz147)

noncomputable def ep727 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz146 7) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz146 6) qz593) Bool.false 332201498131 549755813888 22344542319465 9701540847681536 Bool.true 536912076727 1099511627776 44717074316219 19403081695363072

noncomputable def ep728 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz146 6) qz593 Bool.false 159534231245 274877906944 2361257329639 1212692605960192 Bool.true 985015756189 1099511627776 37790717244773 19403081695363072 Bool.false

noncomputable abbrev qz594 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 5) qz147)

noncomputable def ep729 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz146 6) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz146 5) qz594) Bool.false 159534231245 274877906944 2361257329639 1212692605960192 Bool.true 985015756189 1099511627776 37790717244773 19403081695363072

noncomputable def ep730 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz146 5) qz594 Bool.false 553119115817 1099511627776 30209711809633 19403081695363072 Bool.true 250352797259 549755813888 15102642821017 9701540847681536 Bool.false

noncomputable abbrev qz595 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 4) qz147)

noncomputable def ep731 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz146 5) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz146 4) qz595) Bool.false 553119115817 1099511627776 30209711809633 19403081695363072 Bool.true 250352797259 549755813888 15102642821017 9701540847681536

noncomputable def ep732 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz146 4) qz595 Bool.false 7623460711 68719476736 2716852046403 2425385211920384 Bool.true 210449844175 274877906944 5433355299851 4850770423840768 Bool.false

noncomputable def ep733 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz146 4) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz146 3) (@HPow.hPow Complex Complex Complex qz6 qz8 qz147)) Bool.false 7623460711 68719476736 2716852046403 2425385211920384 Bool.true 210449844175 274877906944 5433355299851 4850770423840768

noncomputable def ep734 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz146 3) (@HPow.hPow Complex Complex Complex qz6 qz8 qz147) Bool.false 91300322039 274877906944 2992298636833 4850770423840768 Bool.true 127720813935 549755813888 5978898616191 9701540847681536 Bool.true

noncomputable def ep735 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz146 3) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz146 2) (@HPow.hPow Complex Complex Complex qz6 qz9 qz147)) Bool.false 91300322039 274877906944 2992298636833 4850770423840768 Bool.true 127720813935 549755813888 5978898616191 9701540847681536

noncomputable def ep736 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz146 2) (@HPow.hPow Complex Complex Complex qz6 qz9 qz147) Bool.false 1 1 0 1 Bool.false 0 1 0 1 Bool.true

noncomputable def ep737 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz146 2) (Complex.mk (Enclosure.sfrac Bool.false 1 1) qz10) Bool.false 1 1 0 1 Bool.false 0 1 0 1 (BSN.head_sum_c_two qz146)

noncomputable abbrev qz617 := (Enclosure.sfrac Bool.false 121891 1000)

noncomputable abbrev qz596 := qz617

noncomputable abbrev qz441 := qz596

noncomputable abbrev qz148 := (@HMul.hMul Real Real Real qz268 qz441 (Real.log qz280))

noncomputable abbrev qz149 := qz441

noncomputable abbrev qz442 := (@Eq.refl Real qz596)

noncomputable abbrev qz150 := qz442

noncomputable def ep738 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz9 qz147) (Complex.mk (@HMul.hMul Real Real Real qz0 qz11 (Real.cos qz148)) (@HMul.hMul Real Real Real qz0 qz11 (@Neg.neg Real Real.instNeg (Real.sin qz148)))) Bool.true 183577584905 274877906944 2992298636833 4850770423840768 Bool.true 127720813935 549755813888 5978898616191 9701540847681536 (BSN.cpow_neg_s_mk qz149 121891 1000 2 qz150 rfl)

noncomputable def ep739 := nat_lit 3194939705726343685706566568366050159169921218616892521677388970403911246329985

noncomputable def ep740 := nat_lit 2464067980215566598231588645392985899451260949740948910662489129479031273601

noncomputable def ep741 := nat_lit 8363709785886741592834347011723304630179253531030376020442565178181563404040321

noncomputable def ep742 := BSN.sin_dyadic_bound_f 2654340207 2147483648 3 2 1048576 282628 ep739 ep65 ep740 ep741 ep67 ep740 990364 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2654340207) qz21 0 2 ep739 ep65 ep740 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2654340207) qz285 0 2 ep741 ep67 ep740 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz151 := (Enclosure.Real.IsNear.const Bool.false 121891 1000)

noncomputable abbrev qz443 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 88592329) qz17)

noncomputable def ep743 := @Enclosure.Real.IsNear.cos_image qz148 qz443 Bool.false 88592329 1048576 453 524288 Bool.true 990364 1048576 1 141176 (@Enclosure.Real.IsNear.recentre' qz148 Bool.false 2768510283 32768000 17413 20168000 88592329 1048576 453 524288 (@Enclosure.Real.IsNear.mulLit_ff qz149 qz18 121891 1000 0 1 363408 524288 1 141176 2768510283 32768000 17413 20168000 qz151 qz284 rfl) rfl) (Enclosure.sfrac_false_div 88592329 1048576) (BSN.cos_reduce1 qz443 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 186782586992729310363648) qz20) 226375608064910080 72057594037927936 Bool.false 990364 1048576 13 1000000000000000 282352 141176 (BSN.sin_reduce_arg_pos_rat_q1 88592329 1048576 226375608064910080 72057594037927936 13 186782586992729310363648 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 990364 1048576 186782586992729310363648 151115727451828646838272 2654340207 2147483648 282628 282352 (ep742 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep744 := nat_lit 1776061644505842299436195466267980304383045681875936267114399423170830261860481

noncomputable def ep745 := nat_lit 5323256797557095765112123221513154941350234523728326903521873291253532723034241

noncomputable def ep746 := BSN.cos_dyadic_bound_f 2654340207 2147483648 3 2 1048576 282628 ep744 ep58 ep740 ep745 ep61 ep740 344514 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2654340207) qz16 0 2 ep744 ep58 ep740 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2654340207) qz282 0 2 ep745 ep61 ep740 rfl rfl rfl rfl) rfl rfl

noncomputable def ep747 := @Enclosure.Real.IsNear.sin_image qz148 qz443 Bool.false 88592329 1048576 453 524288 Bool.false 344514 1048576 1 141176 (@Enclosure.Real.IsNear.recentre' qz148 Bool.false 2768510283 32768000 17413 20168000 88592329 1048576 453 524288 (@Enclosure.Real.IsNear.mulLit_ff qz149 qz18 121891 1000 0 1 363408 524288 1 141176 2768510283 32768000 17413 20168000 qz151 qz284 rfl) rfl) (Enclosure.sfrac_false_div 88592329 1048576) (BSN.sin_reduce1 qz443 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 186782586992729310363648) qz20) 226375608064910080 72057594037927936 Bool.false 344514 1048576 13 1000000000000000 282352 141176 (BSN.sin_reduce_arg_pos_rat_q1 88592329 1048576 226375608064910080 72057594037927936 13 186782586992729310363648 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 344514 1048576 186782586992729310363648 151115727451828646838272 2654340207 2147483648 282628 282352 (ep746 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep748 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz11 (Real.cos qz148)) (@HMul.hMul Real Real Real qz0 qz11 (@Neg.neg Real Real.instNeg (Real.sin qz148))) Bool.true 183577584905 274877906944 2992298636833 4850770423840768 Bool.true 127720813935 549755813888 5978898616191 9701540847681536 (@Enclosure.Real.IsNear.mulLit_ft qz11 (Real.cos qz148) 741455 1048576 1 1048576 247591 262144 8059627 9252110336 183577584905 274877906944 2992298636833 4850770423840768 qz286 (@Enclosure.Real.IsNear.recentre' (Real.cos qz148) Bool.true 990364 1048576 64477016 74016882688 247591 262144 8059627 9252110336 (ep743 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz11 (@Neg.neg Real Real.instNeg (Real.sin qz148)) 741455 1048576 1 1048576 172257 524288 8059627 9252110336 127720813935 549755813888 5978898616191 9701540847681536 qz286 (@Enclosure.Real.IsNear.neg (Real.sin qz148) Bool.false 172257 524288 8059627 9252110336 (@Enclosure.Real.IsNear.recentre' (Real.sin qz148) Bool.false 344514 1048576 64477016 74016882688 172257 524288 8059627 9252110336 (ep747 rfl rfl) rfl)) rfl)

noncomputable def ep749 := @ep736 183577584905 274877906944 2992298636833 4850770423840768 Bool.true 127720813935 549755813888 5978898616191 9701540847681536 Bool.false 91300322039 91300322039 274877906944 2992298636833 4850770423840768 Bool.true 127720813935 127720813935 549755813888 5978898616191 9701540847681536 (ep737 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 1) qz10 Bool.false 1 1 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 1) qz22)) (ep738 ep748) rfl rfl

noncomputable abbrev qz152 := (@HMul.hMul Real Real Real qz268 qz441 (Real.log (Enclosure.sfrac Bool.false 3 1)))

noncomputable def ep750 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz8 qz147) (Complex.mk (@HMul.hMul Real Real Real qz0 qz23 (Real.cos qz152)) (@HMul.hMul Real Real Real qz0 qz23 (@Neg.neg Real Real.instNeg (Real.sin qz152)))) Bool.true 60806479195 274877906944 2441405455973 4850770423840768 Bool.true 293178874415 549755813888 4887811983511 9701540847681536 (BSN.cpow_neg_s_mk qz149 121891 1000 3 qz150 rfl)

noncomputable def ep751 := nat_lit 508396706287251244427448708483152656

noncomputable def ep752 := BSN.sin_dyadic_bound_f 844404778 2147483648 2 1 1048576 282628 ep751 ep144 ep751 ep751 ep145 ep751 401764 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 844404778) qz21 0 1 ep751 ep144 ep751 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 844404778) qz285 0 1 ep751 ep145 ep751 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz444 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 70207875) qz34)

noncomputable def ep753 := @Enclosure.Real.IsNear.cos_image qz152 qz444 Bool.false 70207875 524288 453 524288 Bool.true 401764 1048576 1 141176 (@Enclosure.Real.IsNear.recentre' qz152 Bool.false 70207875199 524288000 17413 20168000 70207875 524288 453 524288 (@Enclosure.Real.IsNear.mulLit_ff qz149 qz25 121891 1000 0 1 575989 524288 1 141176 70207875199 524288000 17413 20168000 qz151 qz289 rfl) rfl) (Enclosure.sfrac_false_div 70207875 524288) (BSN.cos_reduce1 qz444 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 29709851934655617433600) qz35) 226375608064910080 72057594037927936 Bool.false 401764 1048576 21 1000000000000000 282352 141176 (BSN.sin_reduce_arg_pos_rat_q1 70207875 524288 226375608064910080 72057594037927936 21 29709851934655617433600 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 401764 1048576 29709851934655617433600 75557863725914323419136 844404778 2147483648 282628 282352 (ep752 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep754 := BSN.cos_dyadic_bound_f 844404778 2147483648 2 1 1048576 282628 ep751 ep140 ep751 ep751 ep141 ep751 968554 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 844404778) qz16 0 1 ep751 ep140 ep751 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 844404778) qz282 0 1 ep751 ep141 ep751 rfl rfl rfl rfl) rfl rfl

noncomputable def ep755 := @Enclosure.Real.IsNear.sin_image qz152 qz444 Bool.false 70207875 524288 453 524288 Bool.false 968554 1048576 1 141176 (@Enclosure.Real.IsNear.recentre' qz152 Bool.false 70207875199 524288000 17413 20168000 70207875 524288 453 524288 (@Enclosure.Real.IsNear.mulLit_ff qz149 qz25 121891 1000 0 1 575989 524288 1 141176 70207875199 524288000 17413 20168000 qz151 qz289 rfl) rfl) (Enclosure.sfrac_false_div 70207875 524288) (BSN.sin_reduce1 qz444 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 29709851934655617433600) qz35) 226375608064910080 72057594037927936 Bool.false 968554 1048576 21 1000000000000000 282352 141176 (BSN.sin_reduce_arg_pos_rat_q1 70207875 524288 226375608064910080 72057594037927936 21 29709851934655617433600 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 968554 1048576 29709851934655617433600 75557863725914323419136 844404778 2147483648 282628 282352 (ep754 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep756 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz23 (Real.cos qz152)) (@HMul.hMul Real Real Real qz0 qz23 (@Neg.neg Real Real.instNeg (Real.sin qz152))) Bool.true 60806479195 274877906944 2441405455973 4850770423840768 Bool.true 293178874415 549755813888 4887811983511 9701540847681536 (@Enclosure.Real.IsNear.mulLit_ft qz23 (Real.cos qz152) 605395 1048576 1 1048576 100441 262144 8059627 9252110336 60806479195 274877906944 2441405455973 4850770423840768 qz290 (@Enclosure.Real.IsNear.recentre' (Real.cos qz152) Bool.true 401764 1048576 64477016 74016882688 100441 262144 8059627 9252110336 (ep753 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz23 (@Neg.neg Real Real.instNeg (Real.sin qz152)) 605395 1048576 1 1048576 484277 524288 8059627 9252110336 293178874415 549755813888 4887811983511 9701540847681536 qz290 (@Enclosure.Real.IsNear.neg (Real.sin qz152) Bool.false 484277 524288 8059627 9252110336 (@Enclosure.Real.IsNear.recentre' (Real.sin qz152) Bool.false 968554 1048576 64477016 74016882688 484277 524288 8059627 9252110336 (ep755 rfl rfl) rfl)) rfl)

noncomputable def ep757 := @ep734 60806479195 274877906944 2441405455973 4850770423840768 Bool.true 293178874415 549755813888 4887811983511 9701540847681536 Bool.false 8382083695637992308736 7623460711 68719476736 2716852046403 2425385211920384 Bool.true 231392050734059801804800 210449844175 274877906944 5433355299851 4850770423840768 (ep735 (BSN.head_sum_c_succ qz146 2 3 rfl rfl) (ep749 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep750 ep756) rfl rfl

noncomputable abbrev qz153 := (@HMul.hMul Real Real Real qz268 qz441 qz291)

noncomputable def ep758 := @Enclosure.Complex.IsNear.of_eq qz595 (Complex.mk (@HMul.hMul Real Real Real qz0 qz26 (Real.cos qz153)) (@HMul.hMul Real Real Real qz0 qz26 (@Neg.neg Real Real.instNeg (Real.sin qz153)))) Bool.false 431143744441 1099511627776 8474895438409 19403081695363072 Bool.false 170546891091 549755813888 4235932221315 9701540847681536 (BSN.cpow_neg_s_mk qz149 121891 1000 4 qz150 rfl)

noncomputable def ep759 := nat_lit 903534009143033965062466672133268118836840641319844201463011780069438431232000

noncomputable def ep760 := nat_lit 197286256952053160915495520879656289210970046507706722286439046088826617856

noncomputable def ep761 := nat_lit 2366079179530023727188787624743801820104431537667150907233709951250099695845376

noncomputable def ep762 := BSN.sin_dyadic_bound_f 1935918652 2147483648 3 2 1048576 282628 ep759 ep65 ep760 ep761 ep67 ep760 822343 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1935918652) qz21 0 2 ep759 ep65 ep760 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1935918652) qz285 0 2 ep761 ep67 ep760 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz445 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 177184901) qz17)

noncomputable def ep763 := @Enclosure.Real.IsNear.cos_image qz153 qz445 Bool.false 177184901 1048576 907 1048576 Bool.false 822343 1048576 1 141176 (@Enclosure.Real.IsNear.recentre' qz153 Bool.false 88592450947 524288000 17413 20168000 177184901 1048576 907 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz149 qz291 121891 1000 0 1 726817 524288 1 141176 88592450947 524288000 17413 20168000 qz151 qz293 rfl) rfl) (Enclosure.sfrac_false_div 177184901 1048576) (BSN.cos_reduce3 qz445 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 136228164373889901658112) qz20) 226375608064910080 72057594037927936 Bool.false 822343 1048576 26 1000000000000000 282352 141176 (BSN.sin_reduce_arg_pos_rat_q3 177184901 1048576 226375608064910080 72057594037927936 26 136228164373889901658112 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 822343 1048576 136228164373889901658112 151115727451828646838272 1935918652 2147483648 282628 282352 (ep762 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep764 := nat_lit 502051021193664226439555038083317691037894120753916870467133850725727495847936

noncomputable def ep765 := nat_lit 1505758491067088572996834123208193760535260422168735197956828674085004834308096

noncomputable def ep766 := BSN.cos_dyadic_bound_f 1935918652 2147483648 3 2 1048576 282628 ep764 ep58 ep760 ep765 ep61 ep760 650586 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1935918652) qz16 0 2 ep764 ep58 ep760 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1935918652) qz282 0 2 ep765 ep61 ep760 rfl rfl rfl rfl) rfl rfl

noncomputable def ep767 := @Enclosure.Real.IsNear.sin_image qz153 qz445 Bool.false 177184901 1048576 907 1048576 Bool.true 650586 1048576 1 141176 (@Enclosure.Real.IsNear.recentre' qz153 Bool.false 88592450947 524288000 17413 20168000 177184901 1048576 907 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz149 qz291 121891 1000 0 1 726817 524288 1 141176 88592450947 524288000 17413 20168000 qz151 qz293 rfl) rfl) (Enclosure.sfrac_false_div 177184901 1048576) (BSN.sin_reduce3 qz445 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 136228164373889901658112) qz20) 226375608064910080 72057594037927936 Bool.false 650586 1048576 26 1000000000000000 282352 141176 (BSN.sin_reduce_arg_pos_rat_q3 177184901 1048576 226375608064910080 72057594037927936 26 136228164373889901658112 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 650586 1048576 136228164373889901658112 151115727451828646838272 1935918652 2147483648 282628 282352 (ep766 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep768 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz26 (Real.cos qz153)) (@HMul.hMul Real Real Real qz0 qz26 (@Neg.neg Real Real.instNeg (Real.sin qz153))) Bool.false 431143744441 1099511627776 8474895438409 19403081695363072 Bool.false 170546891091 549755813888 4235932221315 9701540847681536 (@Enclosure.Real.IsNear.mulLit_ff qz26 (Real.cos qz153) 524287 1048576 1 1048576 822343 1048576 16136901 18504220672 431143744441 1099511627776 8474895438409 19403081695363072 qz294 (@Enclosure.Real.IsNear.recentre' (Real.cos qz153) Bool.false 822343 1048576 129095208 148033765376 822343 1048576 16136901 18504220672 (ep763 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz26 (@Neg.neg Real Real.instNeg (Real.sin qz153)) 524287 1048576 1 1048576 325293 524288 16136901 18504220672 170546891091 549755813888 4235932221315 9701540847681536 qz294 (@Enclosure.Real.IsNear.neg (Real.sin qz153) Bool.true 325293 524288 16136901 18504220672 (@Enclosure.Real.IsNear.recentre' (Real.sin qz153) Bool.true 650586 1048576 129095208 148033765376 325293 524288 16136901 18504220672 (ep767 rfl rfl) rfl)) rfl)

noncomputable def ep769 := @ep732 431143744441 1099511627776 8474895438409 19403081695363072 Bool.false 170546891091 549755813888 4235932221315 9701540847681536 Bool.false 38010056211623221133312 553119115817 1099511627776 30209711809633 19403081695363072 Bool.true 68816452908129500266496 250352797259 549755813888 15102642821017 9701540847681536 (ep733 (BSN.head_sum_c_succ qz146 3 4 rfl rfl) (ep757 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep758 ep768) rfl rfl

noncomputable abbrev qz154 := (@HMul.hMul Real Real Real qz268 qz441 qz295)

noncomputable def ep770 := @Enclosure.Complex.IsNear.of_eq qz594 (Complex.mk (@HMul.hMul Real Real Real qz0 qz28 (Real.cos qz154)) (@HMul.hMul Real Real Real qz0 qz28 (@Neg.neg Real Real.instNeg (Real.sin qz154)))) Bool.false 85017809163 1099511627776 7570405464591 19403081695363072 Bool.true 484310161671 1099511627776 7585431602739 19403081695363072 (BSN.cpow_neg_s_mk qz149 121891 1000 5 qz150 rfl)

noncomputable def ep771 := nat_lit 2900983528644570663247712150391455483546057197348180811335344598086321435650881

noncomputable def ep772 := nat_lit 6562448931244795662149371340301105140789758321064969719838005094959669128001

noncomputable def ep773 := nat_lit 8689825688071222398418837708493764240356592075402412494566357784069044968696641

noncomputable def ep774 := BSN.cos_dyadic_bound_f 3000082807 2147483648 3 2 1048576 282628 ep771 ep58 ep772 ep773 ep61 ep772 181299 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3000082807) qz16 0 2 ep771 ep58 ep772 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3000082807) qz282 0 2 ep773 ep61 ep772 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz446 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 205705201) qz17)

noncomputable def ep775 := @Enclosure.Real.IsNear.cos_image qz154 qz446 Bool.false 205705201 1048576 907 1048576 Bool.false 181299 1048576 1 141176 (@Enclosure.Real.IsNear.recentre' qz154 Bool.false 3214143779 16384000 17413 20168000 205705201 1048576 907 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz149 qz295 121891 1000 0 1 843808 524288 1 141176 3214143779 16384000 17413 20168000 qz151 qz297 rfl) rfl) (Enclosure.sfrac_false_div 205705201 1048576) (BSN.cos_reduce0 qz446 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 211112059615112543076352) qz20) 226375608064910080 72057594037927936 Bool.false 181299 1048576 31 1000000000000000 282352 141176 (BSN.sin_reduce_arg_pos_rat_q0 205705201 1048576 226375608064910080 72057594037927936 31 211112059615112543076352 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 181299 1048576 211112059615112543076352 151115727451828646838272 3000082807 2147483648 282628 282352 (ep774 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep776 := nat_lit 5216520392415231357316162373632378986270271148569873484627749872479410848869185

noncomputable def ep777 := nat_lit 13651690396151209599994088186867171746194193399448896794478654800625665139878721

noncomputable def ep778 := BSN.sin_dyadic_bound_f 3000082807 2147483648 3 2 1048576 282628 ep776 ep65 ep772 ep777 ep67 ep772 1032783 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3000082807) qz21 0 2 ep776 ep65 ep772 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3000082807) qz285 0 2 ep777 ep67 ep772 rfl rfl rfl rfl) rfl rfl

noncomputable def ep779 := @Enclosure.Real.IsNear.sin_image qz154 qz446 Bool.false 205705201 1048576 907 1048576 Bool.false 1032783 1048576 1 141176 (@Enclosure.Real.IsNear.recentre' qz154 Bool.false 3214143779 16384000 17413 20168000 205705201 1048576 907 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz149 qz295 121891 1000 0 1 843808 524288 1 141176 3214143779 16384000 17413 20168000 qz151 qz297 rfl) rfl) (Enclosure.sfrac_false_div 205705201 1048576) (BSN.sin_reduce0 qz446 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 211112059615112543076352) qz20) 226375608064910080 72057594037927936 Bool.false 1032783 1048576 31 1000000000000000 282352 141176 (BSN.sin_reduce_arg_pos_rat_q0 205705201 1048576 226375608064910080 72057594037927936 31 211112059615112543076352 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1032783 1048576 211112059615112543076352 151115727451828646838272 3000082807 2147483648 282628 282352 (ep778 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep780 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz28 (Real.cos qz154)) (@HMul.hMul Real Real Real qz0 qz28 (@Neg.neg Real Real.instNeg (Real.sin qz154))) Bool.false 85017809163 1099511627776 7570405464591 19403081695363072 Bool.true 484310161671 1099511627776 7585431602739 19403081695363072 (@Enclosure.Real.IsNear.mulLit_ff qz28 (Real.cos qz154) 468937 1048576 1 1048576 181299 1048576 16136901 18504220672 85017809163 1099511627776 7570405464591 19403081695363072 qz298 (@Enclosure.Real.IsNear.recentre' (Real.cos qz154) Bool.false 181299 1048576 129095208 148033765376 181299 1048576 16136901 18504220672 (ep775 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz28 (@Neg.neg Real Real.instNeg (Real.sin qz154)) 468937 1048576 1 1048576 1032783 1048576 16136901 18504220672 484310161671 1099511627776 7585431602739 19403081695363072 qz298 (@Enclosure.Real.IsNear.neg (Real.sin qz154) Bool.false 1032783 1048576 16136901 18504220672 (@Enclosure.Real.IsNear.recentre' (Real.sin qz154) Bool.false 1032783 1048576 129095208 148033765376 1032783 1048576 16136901 18504220672 (ep779 rfl rfl) rfl)) rfl)

noncomputable def ep781 := @ep730 85017809163 1099511627776 7570405464591 19403081695363072 Bool.true 484310161671 1099511627776 7585431602739 19403081695363072 Bool.false 701638969128730996244480 159534231245 274877906944 2361257329639 1212692605960192 Bool.true 541518138736187468152832 985015756189 1099511627776 37790717244773 19403081695363072 (ep731 (BSN.head_sum_c_succ qz146 4 5 rfl rfl) (ep769 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep770 ep780) rfl rfl

noncomputable abbrev qz155 := (@HMul.hMul Real Real Real qz268 qz441 qz550)

noncomputable def ep782 := @Enclosure.Complex.IsNear.of_eq qz593 (Complex.mk (@HMul.hMul Real Real Real qz0 qz30 (Real.cos qz155)) (@HMul.hMul Real Real Real qz0 qz30 (@Neg.neg Real Real.instNeg (Real.sin qz155)))) Bool.false 13133035641 549755813888 3454483682353 9701540847681536 Bool.false 224051839731 549755813888 3463178535723 9701540847681536 (BSN.cpow_neg_s_mk qz149 121891 1000 6 qz150 rfl)

noncomputable def ep783 := @Enclosure.Real.IsNear.mulLit_ff qz149 qz550 121891 1000 0 1 4034681531866359 2251799813685248 62500000017647 8823500000000000000 491791366600722364869 2251799813685248000 1088312500307287211 1260500000000000000000 qz151 (BSN.isNear_log_sfrac 6 1 4034681531866359 2251799813685248 62500000017647 8823500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz299) Bool.false 33845361775666394038272 18889465931478580854784 1000000000282352 141176000000000000000 4034681531866359 2251799813685248 62500000017647 8823500000000000000 (BSN.log_rat_reduce_isNear 6 1 2 12 8 212580 524288 24973259072661432 36028797018963968 141176 1000000000000000 rfl rfl rfl rfl (ep122 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep784 := BSN.sin_dyadic_bound_f 125733367 2147483648 1 0 1048576 282628 0 1 1 0 1 1 61358 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 125733367) qz21 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 125733367) qz285 0 0 rfl) rfl rfl

noncomputable abbrev qz447 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 28626025) qz568)

noncomputable def ep785 := @Enclosure.Real.IsNear.cos_image qz155 qz447 Bool.false 28626025 131072 907 1048576 Bool.false 61358 1048576 1 141176 (@Enclosure.Real.IsNear.recentre' qz155 Bool.false 491791366600722364869 2251799813685248000 1088312500307287211 1260500000000000000000 28626025 131072 907 1048576 (ep783 rfl) rfl) (Enclosure.sfrac_false_div 28626025 131072) (BSN.cos_reduce3 qz447 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 1105962399690821468160) qz369) 226375608064910080 72057594037927936 Bool.false 61358 1048576 34 1000000000000000 282352 141176 (BSN.sin_reduce_arg_pos_rat_q3 28626025 131072 226375608064910080 72057594037927936 34 1105962399690821468160 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 61358 1048576 1105962399690821468160 18889465931478580854784 125733367 2147483648 282628 282352 (ep784 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep786 := BSN.cos_dyadic_bound_f 125733367 2147483648 1 0 1048576 282628 0 1 1 0 1 1 1046778 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 125733367) qz16 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 125733367) qz282 0 0 rfl) rfl rfl

noncomputable def ep787 := @Enclosure.Real.IsNear.sin_image qz155 qz447 Bool.false 28626025 131072 907 1048576 Bool.true 1046778 1048576 1 141176 (@Enclosure.Real.IsNear.recentre' qz155 Bool.false 491791366600722364869 2251799813685248000 1088312500307287211 1260500000000000000000 28626025 131072 907 1048576 (ep783 rfl) rfl) (Enclosure.sfrac_false_div 28626025 131072) (BSN.sin_reduce3 qz447 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 1105962399690821468160) qz369) 226375608064910080 72057594037927936 Bool.false 1046778 1048576 34 1000000000000000 282352 141176 (BSN.sin_reduce_arg_pos_rat_q3 28626025 131072 226375608064910080 72057594037927936 34 1105962399690821468160 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1046778 1048576 1105962399690821468160 18889465931478580854784 125733367 2147483648 282628 282352 (ep786 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep788 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz30 (Real.cos qz155)) (@HMul.hMul Real Real Real qz0 qz30 (@Neg.neg Real Real.instNeg (Real.sin qz155))) Bool.false 13133035641 549755813888 3454483682353 9701540847681536 Bool.false 224051839731 549755813888 3463178535723 9701540847681536 (@Enclosure.Real.IsNear.mulLit_ff qz30 (Real.cos qz155) 428079 1048576 1 1048576 30679 524288 16136901 18504220672 13133035641 549755813888 3454483682353 9701540847681536 qz301 (@Enclosure.Real.IsNear.recentre' (Real.cos qz155) Bool.false 61358 1048576 129095208 148033765376 30679 524288 16136901 18504220672 (ep785 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz30 (@Neg.neg Real Real.instNeg (Real.sin qz155)) 428079 1048576 1 1048576 523389 524288 16136901 18504220672 224051839731 549755813888 3463178535723 9701540847681536 qz301 (@Enclosure.Real.IsNear.neg (Real.sin qz155) Bool.true 523389 524288 16136901 18504220672 (@Enclosure.Real.IsNear.recentre' (Real.sin qz155) Bool.true 1046778 1048576 129095208 148033765376 523389 524288 16136901 18504220672 (ep787 rfl rfl) rfl)) rfl)

noncomputable def ep789 := @ep728 13133035641 549755813888 3454483682353 9701540847681536 Bool.false 224051839731 549755813888 3463178535723 9701540847681536 Bool.false 91314852489910407921664 332201498131 549755813888 22344542319465 9701540847681536 Bool.true 295170535727348188184576 536912076727 1099511627776 44717074316219 19403081695363072 (ep729 (BSN.head_sum_c_succ qz146 5 6 rfl rfl) (ep781 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep782 ep788) rfl rfl

noncomputable abbrev qz156 := (@HMul.hMul Real Real Real qz268 qz441 qz551)

noncomputable def ep790 := @Enclosure.Complex.IsNear.of_eq qz592 (Complex.mk (@HMul.hMul Real Real Real qz0 qz32 (Real.cos qz156)) (@HMul.hMul Real Real Real qz0 qz32 (@Neg.neg Real Real.instNeg (Real.sin qz156)))) Bool.true 156548375 274877906944 114080488269 346483601702912 Bool.false 207788045275 549755813888 457641689013 1385934406811648 (BSN.cpow_neg_s_mk qz149 121891 1000 7 qz150 rfl)

noncomputable def ep791 := @Enclosure.Real.IsNear.mulLit_ff qz149 qz551 121891 1000 0 1 4381796493761783 2251799813685248 62500000017647 8823500000000000000 534101556421117491653 2251799813685248000 1088312500307287211 1260500000000000000000 qz151 (BSN.isNear_log_sfrac 7 1 4381796493761783 2251799813685248 62500000017647 8823500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz302) Bool.false 36757173121942042968064 18889465931478580854784 1000000000282352 141176000000000000000 4381796493761783 2251799813685248 62500000017647 8823500000000000000 (BSN.log_rat_reduce_isNear 7 1 2 14 8 293399 524288 24973259072661432 36028797018963968 141176 1000000000000000 rfl rfl rfl rfl (ep137 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep792 := nat_lit 4625138312430903642093739781418920964364121388952690462670526717443610190544896

noncomputable def ep793 := nat_lit 16636502768107539587344834641291365044798203006808538399418739717710247100416

noncomputable def ep794 := nat_lit 13842141931756495847106529674974180163002767760844454311212742672895410077433856

noncomputable def ep795 := BSN.cos_dyadic_bound_f 3370022144 2147483648 3 2 1048576 282628 ep792 ep58 ep793 ep794 ep61 ep793 1580 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3370022144) qz16 0 2 ep792 ep58 ep793 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3370022144) qz282 0 2 ep794 ep61 ep793 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz448 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 124355209) qz34)

noncomputable def ep796 := @Enclosure.Real.IsNear.cos_image qz156 qz448 Bool.false 124355209 524288 453 524288 Bool.true 1580 1048576 1 141176 (@Enclosure.Real.IsNear.recentre' qz156 Bool.false 534101556421117491653 2251799813685248000 1088312500307287211 1260500000000000000000 124355209 524288 453 524288 (ep791 rfl) rfl) (Enclosure.sfrac_false_div 124355209 524288) (BSN.cos_reduce2 qz448 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 118572113077028412981248) qz35) 226375608064910080 72057594037927936 Bool.false 1580 1048576 37 1000000000000000 282352 141176 (BSN.sin_reduce_arg_pos_rat_q2 124355209 524288 226375608064910080 72057594037927936 37 118572113077028412981248 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1580 1048576 118572113077028412981248 75557863725914323419136 3370022144 2147483648 282628 282352 (ep795 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep797 := nat_lit 8311939760161140524098855738841024643819579937709396002087413099624330145300480

noncomputable def ep798 := nat_lit 21742430748321289165688921012307259476121607508180251895677499206139809980481536

noncomputable def ep799 := BSN.sin_dyadic_bound_f 3370022144 2147483648 3 2 1048576 282628 ep797 ep65 ep793 ep798 ep67 ep793 1048574 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3370022144) qz21 0 2 ep797 ep65 ep793 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3370022144) qz285 0 2 ep798 ep67 ep793 rfl rfl rfl rfl) rfl rfl

noncomputable def ep800 := @Enclosure.Real.IsNear.sin_image qz156 qz448 Bool.false 124355209 524288 453 524288 Bool.true 1048574 1048576 1 141176 (@Enclosure.Real.IsNear.recentre' qz156 Bool.false 534101556421117491653 2251799813685248000 1088312500307287211 1260500000000000000000 124355209 524288 453 524288 (ep791 rfl) rfl) (Enclosure.sfrac_false_div 124355209 524288) (BSN.sin_reduce2 qz448 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 118572113077028412981248) qz35) 226375608064910080 72057594037927936 Bool.false 1048574 1048576 37 1000000000000000 282352 141176 (BSN.sin_reduce_arg_pos_rat_q2 124355209 524288 226375608064910080 72057594037927936 37 118572113077028412981248 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1048574 1048576 118572113077028412981248 75557863725914323419136 3370022144 2147483648 282628 282352 (ep799 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep801 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz32 (Real.cos qz156)) (@HMul.hMul Real Real Real qz0 qz32 (@Neg.neg Real Real.instNeg (Real.sin qz156))) Bool.true 156548375 274877906944 114080488269 346483601702912 Bool.false 207788045275 549755813888 457641689013 1385934406811648 (@Enclosure.Real.IsNear.mulLit_ft qz32 (Real.cos qz156) 396325 1048576 1 1048576 395 262144 8059627 9252110336 156548375 274877906944 114080488269 346483601702912 qz304 (@Enclosure.Real.IsNear.recentre' (Real.cos qz156) Bool.true 1580 1048576 64477016 74016882688 395 262144 8059627 9252110336 (ep796 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz32 (@Neg.neg Real Real.instNeg (Real.sin qz156)) 396325 1048576 1 1048576 524287 524288 8059627 9252110336 207788045275 549755813888 457641689013 1385934406811648 qz304 (@Enclosure.Real.IsNear.neg (Real.sin qz156) Bool.true 524287 524288 8059627 9252110336 (@Enclosure.Real.IsNear.recentre' (Real.sin qz156) Bool.true 1048574 1048576 64477016 74016882688 524287 524288 8059627 9252110336 (ep800 rfl rfl) rfl)) rfl)

noncomputable def ep802 := @ep726 156548375 274877906944 114080488269 346483601702912 Bool.false 207788045275 549755813888 457641689013 1385934406811648 Bool.false 91228789110599439089664 331888401381 549755813888 25538795990997 9701540847681536 Bool.true 66705163834639752626176 121335986177 1099511627776 51124057962401 19403081695363072 (ep727 (BSN.head_sum_c_succ qz146 6 7 rfl rfl) (ep789 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep790 ep801) rfl rfl

noncomputable abbrev qz157 := (@HMul.hMul Real Real Real qz268 qz441 qz552)

noncomputable def ep803 := @Enclosure.Complex.IsNear.of_eq qz591 (Complex.mk (@HMul.hMul Real Real Real qz0 qz36 (Real.cos qz157)) (@HMul.hMul Real Real Real qz0 qz36 (@Neg.neg Real Real.instNeg (Real.sin qz157)))) Bool.true 208790851311 1099511627776 5992339700799 19403081695363072 Bool.true 163952162115 549755813888 2999004814479 9701540847681536 (BSN.cpow_neg_s_mk qz149 121891 1000 8 qz150 rfl)

noncomputable def ep804 := @Enclosure.Real.IsNear.mulLit_ff qz149 qz552 121891 1000 0 1 9364972152248037 4503599627370496 125000000052941 17647000000000000000 1141505820609665477967 4503599627370496000 2176625000921861633 2521000000000000000000 qz151 (BSN.isNear_log_sfrac 8 1 9364972152248037 4503599627370496 125000000052941 17647000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz305) Bool.false 39279540158062550581248 18889465931478580854784 1000000000423528 141176000000000000000 9364972152248037 4503599627370496 125000000052941 17647000000000000000 (BSN.log_rat_reduce_isNear 8 1 3 16 16 0 524288 24973259072661432 36028797018963968 141176 1000000000000000 rfl rfl rfl rfl (ep152 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep805 := nat_lit 2198112821913205406670730096730443776

noncomputable def ep806 := BSN.sin_dyadic_bound_f 1217622024 2147483648 2 1 1048576 282628 ep805 ep144 ep805 ep805 ep145 ep805 563193 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1217622024) qz21 0 1 ep805 ep144 ep805 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1217622024) qz285 0 1 ep805 ep145 ep805 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz449 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 132888767) qz34)

noncomputable def ep807 := @Enclosure.Real.IsNear.cos_image qz157 qz449 Bool.false 132888767 524288 907 1048576 Bool.true 563193 1048576 1 141176 (@Enclosure.Real.IsNear.recentre' qz157 Bool.false 1141505820609665477967 4503599627370496000 2176625000921861633 2521000000000000000000 132888767 524288 907 1048576 (ep804 rfl) rfl) (Enclosure.sfrac_false_div 132888767 524288) (BSN.cos_reduce1 qz449 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 42841266390761560080384) qz35) 226375608064910080 72057594037927936 Bool.false 563193 1048576 40 1000000000000000 282352 141176 (BSN.sin_reduce_arg_pos_rat_q1 132888767 524288 226375608064910080 72057594037927936 40 42841266390761560080384 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 563193 1048576 42841266390761560080384 75557863725914323419136 1217622024 2147483648 282628 282352 (ep806 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep808 := BSN.cos_dyadic_bound_f 1217622024 2147483648 2 1 1048576 282628 ep805 ep140 ep805 ep805 ep141 ep805 884490 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1217622024) qz16 0 1 ep805 ep140 ep805 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1217622024) qz282 0 1 ep805 ep141 ep805 rfl rfl rfl rfl) rfl rfl

noncomputable def ep809 := @Enclosure.Real.IsNear.sin_image qz157 qz449 Bool.false 132888767 524288 907 1048576 Bool.false 884490 1048576 1 141176 (@Enclosure.Real.IsNear.recentre' qz157 Bool.false 1141505820609665477967 4503599627370496000 2176625000921861633 2521000000000000000000 132888767 524288 907 1048576 (ep804 rfl) rfl) (Enclosure.sfrac_false_div 132888767 524288) (BSN.sin_reduce1 qz449 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 42841266390761560080384) qz35) 226375608064910080 72057594037927936 Bool.false 884490 1048576 40 1000000000000000 282352 141176 (BSN.sin_reduce_arg_pos_rat_q1 132888767 524288 226375608064910080 72057594037927936 40 42841266390761560080384 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 884490 1048576 42841266390761560080384 75557863725914323419136 1217622024 2147483648 282628 282352 (ep808 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep810 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz36 (Real.cos qz157)) (@HMul.hMul Real Real Real qz0 qz36 (@Neg.neg Real Real.instNeg (Real.sin qz157))) Bool.true 208790851311 1099511627776 5992339700799 19403081695363072 Bool.true 163952162115 549755813888 2999004814479 9701540847681536 (@Enclosure.Real.IsNear.mulLit_ft qz36 (Real.cos qz157) 370727 1048576 1 1048576 563193 1048576 16136901 18504220672 208790851311 1099511627776 5992339700799 19403081695363072 qz307 (@Enclosure.Real.IsNear.recentre' (Real.cos qz157) Bool.true 563193 1048576 129095208 148033765376 563193 1048576 16136901 18504220672 (ep807 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz36 (@Neg.neg Real Real.instNeg (Real.sin qz157)) 370727 1048576 1 1048576 442245 524288 16136901 18504220672 163952162115 549755813888 2999004814479 9701540847681536 qz307 (@Enclosure.Real.IsNear.neg (Real.sin qz157) Bool.false 442245 524288 16136901 18504220672 (@Enclosure.Real.IsNear.recentre' (Real.sin qz157) Bool.false 884490 1048576 129095208 148033765376 442245 524288 16136901 18504220672 (ep809 rfl rfl) rfl)) rfl)

noncomputable def ep811 := @ep724 208790851311 1099511627776 5992339700799 19403081695363072 Bool.true 163952162115 549755813888 2999004814479 9701540847681536 Bool.false 250131172047550559551488 454985951451 1099511627776 57069931682793 19403081695363072 Bool.true 246972472479098041532416 449240310407 1099511627776 57122067591359 19403081695363072 (ep725 (BSN.head_sum_c_succ qz146 7 8 rfl rfl) (ep802 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep803 ep810) rfl rfl

theorem EMRow39.d12 : Enclosure.Complex.IsNear qz145 Bool.false 454985951451 1099511627776 57069931682793 19403081695363072 Bool.true 449240310407 1099511627776 57122067591359 19403081695363072 := ep723 (BSN.head_sum_c_succ qz146 8 9 rfl rfl) (ep811 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable abbrev qz158 := (BSN.headSumC qz439 17)

noncomputable def ep812 := @Enclosure.Complex.IsNear.of_eq qz158 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz146 16) (@HPow.hPow Complex Complex Complex qz6 qz308 qz147)) Bool.true 315889795643 1099511627776 95905178952857 19403081695363072 Bool.false 101254527637 549755813888 47994751962357 9701540847681536

noncomputable def ep813 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz146 16) (@HPow.hPow Complex Complex Complex qz6 qz308 qz147) Bool.true 379197854429 1099511627776 91675351446487 19403081695363072 Bool.true 16244497981 274877906944 22936482863099 4850770423840768 Bool.false

noncomputable def ep814 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz146 16) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz146 15) (@HPow.hPow Complex Complex Complex qz6 qz309 qz147)) Bool.true 379197854429 1099511627776 91675351446487 19403081695363072 Bool.true 16244497981 274877906944 22936482863099 4850770423840768

noncomputable def ep815 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz146 15) (@HPow.hPow Complex Complex Complex qz6 qz309 qz147) Bool.true 51058185475 549755813888 43646566052463 9701540847681536 Bool.true 126790598893 1099511627776 87377743417005 19403081695363072 Bool.true

noncomputable def ep816 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz146 15) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz146 14) (@HPow.hPow Complex Complex Complex qz6 qz310 qz147)) Bool.true 51058185475 549755813888 43646566052463 9701540847681536 Bool.true 126790598893 1099511627776 87377743417005 19403081695363072

noncomputable def ep817 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz146 14) (@HPow.hPow Complex Complex Complex qz6 qz310 qz147) Bool.true 199034208855 1099511627776 82764759470837 19403081695363072 Bool.false 9413924221 68719476736 10354750614365 2425385211920384 Bool.false

noncomputable def ep818 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz146 14) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz146 13) (@HPow.hPow Complex Complex Complex qz6 qz311 qz147)) Bool.true 199034208855 1099511627776 82764759470837 19403081695363072 Bool.false 9413924221 68719476736 10354750614365 2425385211920384

noncomputable def ep819 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz146 13) (@HPow.hPow Complex Complex Complex qz6 qz311 qz147) Bool.true 53991989919 274877906944 9759483251709 2425385211920384 Bool.true 153856388075 1099511627776 78131663339445 19403081695363072 Bool.false

noncomputable def ep820 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz146 13) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz146 12) (@HPow.hPow Complex Complex Complex qz6 qz312 qz147)) Bool.true 53991989919 274877906944 9759483251709 2425385211920384 Bool.true 153856388075 1099511627776 78131663339445 19403081695363072

noncomputable def ep821 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz146 12) (@HPow.hPow Complex Complex Complex qz6 qz312 qz147) Bool.true 2363105871 8589934592 653496041289 173241800851456 Bool.false 151527350497 1099511627776 10462084822483 2771868813623296 Bool.false

noncomputable def ep822 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz146 12) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz146 11) (@HPow.hPow Complex Complex Complex qz6 qz313 qz147)) Bool.true 2363105871 8589934592 653496041289 173241800851456 Bool.false 151527350497 1099511627776 10462084822483 2771868813623296

noncomputable def ep823 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz146 11) (@HPow.hPow Complex Complex Complex qz6 qz313 qz147) Bool.false 13449618655 549755813888 34038470313289 9701540847681536 Bool.false 28484940231 274877906944 34068132308533 9701540847681536 Bool.true

noncomputable def ep824 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz146 11) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz146 10) (@HPow.hPow Complex Complex Complex qz6 qz314 qz147)) Bool.false 13449618655 549755813888 34038470313289 9701540847681536 Bool.false 28484940231 274877906944 34068132308533 9701540847681536

noncomputable def ep825 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz146 10) (@HPow.hPow Complex Complex Complex qz6 qz314 qz147) Bool.false 49026778619 274877906944 31358550232885 9701540847681536 Bool.true 189805379157 1099511627776 62769264450713 19403081695363072 Bool.true

noncomputable abbrev qz597 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 9) qz147)

noncomputable def ep826 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz146 10) (@HAdd.hAdd Complex Complex Complex qz4 qz145 qz597) Bool.false 49026778619 274877906944 31358550232885 9701540847681536 Bool.true 189805379157 1099511627776 62769264450713 19403081695363072

noncomputable def ep827 := @Enclosure.Complex.IsNear.addLitP qz145 qz597 Bool.false 454985951451 1099511627776 57069931682793 19403081695363072 Bool.true 449240310407 1099511627776 57122067591359 19403081695363072 Bool.true

noncomputable abbrev qz159 := (@HMul.hMul Real Real Real qz268 qz441 qz554)

noncomputable def ep828 := @Enclosure.Complex.IsNear.of_eq qz597 (Complex.mk (@HMul.hMul Real Real Real qz0 qz39 (Real.cos qz159)) (@HMul.hMul Real Real Real qz0 qz39 (@Neg.neg Real Real.instNeg (Real.sin qz159)))) Bool.true 258878836975 1099511627776 5647168782977 19403081695363072 Bool.false 129717465625 549755813888 2823598429677 9701540847681536 (BSN.cpow_neg_s_mk qz149 121891 1000 9 qz150 rfl)

noncomputable def ep829 := @Enclosure.Real.IsNear.mulLit_ff qz149 qz554 121891 1000 0 1 9895417793173221 4503599627370496 125000000052941 17647000000000000000 1206162370227677080911 4503599627370496000 2176625000921861633 2521000000000000000000 qz151 (BSN.isNear_log_sfrac 9 1 9895417793173221 4503599627370496 125000000052941 17647000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz315) Bool.false 41504390431577613533184 18889465931478580854784 1000000000423528 141176000000000000000 9895417793173221 4503599627370496 125000000052941 17647000000000000000 (BSN.log_rat_reduce_isNear 9 1 3 18 16 61752 524288 24973259072661432 36028797018963968 141176 1000000000000000 rfl rfl rfl rfl (ep185 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep830 := nat_lit 290789585486353048206084823928631359049095882590924512205169283357084911190625

noncomputable def ep831 := nat_lit 66206773920526342076830926704904685466324759178637958327141403017250390625

noncomputable def ep832 := nat_lit 872236342911218091934100809932484267776354998254416260698853567265220232790625

noncomputable def ep833 := BSN.cos_dyadic_bound_f 1688934485 2147483648 3 2 1048576 282628 ep830 ep58 ep831 ep832 ep61 ep831 740659 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1688934485) qz16 0 2 ep830 ep58 ep831 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1688934485) qz282 0 2 ep832 ep61 ep831 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz450 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 280831561) qz17)

noncomputable def ep834 := @Enclosure.Real.IsNear.cos_image qz159 qz450 Bool.false 280831561 1048576 453 524288 Bool.true 740659 1048576 1 141176 (@Enclosure.Real.IsNear.recentre' qz159 Bool.false 1206162370227677080911 4503599627370496000 2176625000921861633 2521000000000000000000 280831561 1048576 453 524288 (ep829 rfl) rfl) (Enclosure.sfrac_false_div 280831561 1048576) (BSN.cos_reduce2 qz450 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 118848198765095096942592) qz20) 226375608064910080 72057594037927936 Bool.false 740659 1048576 42 1000000000000000 282352 141176 (BSN.sin_reduce_arg_pos_rat_q2 280831561 1048576 226375608064910080 72057594037927936 42 118848198765095096942592 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 740659 1048576 118848198765095096942592 151115727451828646838272 1688934485 2147483648 282628 282352 (ep833 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep835 := nat_lit 8136754507819831114216434086221800625

noncomputable def ep836 := BSN.sin_dyadic_bound_f 1688934485 2147483648 2 1 1048576 282628 ep835 ep144 ep835 ep835 ep145 ep835 742250 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1688934485) qz21 0 1 ep835 ep144 ep835 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1688934485) qz285 0 1 ep835 ep145 ep835 rfl rfl rfl rfl) rfl rfl

noncomputable def ep837 := @Enclosure.Real.IsNear.sin_image qz159 qz450 Bool.false 280831561 1048576 453 524288 Bool.true 742250 1048576 1 141176 (@Enclosure.Real.IsNear.recentre' qz159 Bool.false 1206162370227677080911 4503599627370496000 2176625000921861633 2521000000000000000000 280831561 1048576 453 524288 (ep829 rfl) rfl) (Enclosure.sfrac_false_div 280831561 1048576) (BSN.sin_reduce2 qz450 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 118848198765095096942592) qz20) 226375608064910080 72057594037927936 Bool.false 742250 1048576 42 1000000000000000 282352 141176 (BSN.sin_reduce_arg_pos_rat_q2 280831561 1048576 226375608064910080 72057594037927936 42 118848198765095096942592 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 742250 1048576 118848198765095096942592 151115727451828646838272 1688934485 2147483648 282628 282352 (ep836 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep838 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz39 (Real.cos qz159)) (@HMul.hMul Real Real Real qz0 qz39 (@Neg.neg Real Real.instNeg (Real.sin qz159))) Bool.true 258878836975 1099511627776 5647168782977 19403081695363072 Bool.false 129717465625 549755813888 2823598429677 9701540847681536 (@Enclosure.Real.IsNear.mulLit_ft qz39 (Real.cos qz159) 349525 1048576 1 1048576 740659 1048576 8059627 9252110336 258878836975 1099511627776 5647168782977 19403081695363072 qz317 (@Enclosure.Real.IsNear.recentre' (Real.cos qz159) Bool.true 740659 1048576 64477016 74016882688 740659 1048576 8059627 9252110336 (ep834 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz39 (@Neg.neg Real Real.instNeg (Real.sin qz159)) 349525 1048576 1 1048576 371125 524288 8059627 9252110336 129717465625 549755813888 2823598429677 9701540847681536 qz317 (@Enclosure.Real.IsNear.neg (Real.sin qz159) Bool.true 371125 524288 8059627 9252110336 (@Enclosure.Real.IsNear.recentre' (Real.sin qz159) Bool.true 742250 1048576 64477016 74016882688 371125 524288 8059627 9252110336 (ep837 rfl rfl) rfl)) rfl)

noncomputable def ep839 := @ep827 258878836975 1099511627776 5647168782977 19403081695363072 Bool.false 129717465625 549755813888 2823598429677 9701540847681536 Bool.false 215622052655961133285376 49026778619 274877906944 31358550232885 9701540847681536 Bool.true 104346610698776966332416 189805379157 1099511627776 62769264450713 19403081695363072 EMRow39.d12 (ep828 ep838) rfl rfl

noncomputable abbrev qz160 := (@HMul.hMul Real Real Real qz268 qz441 qz555)

noncomputable def ep840 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz314 qz147) (Complex.mk (@HMul.hMul Real Real Real qz0 qz41 (Real.cos qz160)) (@HMul.hMul Real Real Real qz0 qz41 (@Neg.neg Real Real.instNeg (Real.sin qz160)))) Bool.true 84603938583 549755813888 95711431443 346483601702912 Bool.false 303745140081 1099511627776 766714309479 2771868813623296 (BSN.cpow_neg_s_mk qz149 121891 1000 10 qz150 rfl)

noncomputable def ep841 := @Enclosure.Real.IsNear.mulLit_ff qz149 qz555 121891 1000 0 1 10369917190100709 4503599627370496 125000000052941 17647000000000000000 1263999576218565520719 4503599627370496000 2176625000921861633 2521000000000000000000 qz151 (BSN.isNear_log_sfrac 10 1 10369917190100709 4503599627370496 125000000052941 17647000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz319) Bool.false 43494585150108164161536 18889465931478580854784 1000000000423528 141176000000000000000 10369917190100709 4503599627370496 125000000052941 17647000000000000000 (BSN.log_rat_reduce_isNear 10 1 3 20 16 116991 524288 24973259072661432 36028797018963968 141176 1000000000000000 rfl rfl rfl rfl (ep199 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep842 := nat_lit 969299303772193697236105669748922265723417475635416375491554230290591948800000

noncomputable def ep843 := nat_lit 734851463503666059838706622251531575200840838576065219462518280217600000000

noncomputable def ep844 := nat_lit 2906428208389573759588639596002263734019850745229096996035737654311340646400000

noncomputable def ep845 := BSN.cos_dyadic_bound_f 2281786180 2147483648 3 2 1048576 282628 ep842 ep58 ep843 ep844 ep61 ep843 510294 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2281786180) qz16 0 2 ep842 ep58 ep843 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2281786180) qz282 0 2 ep844 ep61 ep843 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz451 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 147148917) qz34)

noncomputable def ep846 := @Enclosure.Real.IsNear.cos_image qz160 qz451 Bool.false 147148917 524288 907 1048576 Bool.true 510294 1048576 1 141176 (@Enclosure.Real.IsNear.recentre' qz160 Bool.false 1263999576218565520719 4503599627370496000 2176625000921861633 2521000000000000000000 147148917 524288 907 1048576 (ep841 rfl) rfl) (Enclosure.sfrac_false_div 147148917 524288) (BSN.cos_reduce2 qz451 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 80283214011372880789504) qz35) 226375608064910080 72057594037927936 Bool.false 510294 1048576 44 1000000000000000 282352 141176 (BSN.sin_reduce_arg_pos_rat_q2 147148917 524288 226375608064910080 72057594037927936 44 80283214011372880789504 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 510294 1048576 80283214011372880789504 75557863725914323419136 2281786180 2147483648 282628 282352 (ep845 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep847 := nat_lit 1744150865619145722177119240250258853041990783472888623709227599898891427840000

noncomputable def ep848 := nat_lit 4566824412347328098747954389933699278273936404880823242216466303471982387200000

noncomputable def ep849 := BSN.sin_dyadic_bound_f 2281786180 2147483648 3 2 1048576 282628 ep847 ep65 ep843 ep848 ep67 ep843 916029 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2281786180) qz21 0 2 ep847 ep65 ep843 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2281786180) qz285 0 2 ep848 ep67 ep843 rfl rfl rfl rfl) rfl rfl

noncomputable def ep850 := @Enclosure.Real.IsNear.sin_image qz160 qz451 Bool.false 147148917 524288 907 1048576 Bool.true 916029 1048576 1 141176 (@Enclosure.Real.IsNear.recentre' qz160 Bool.false 1263999576218565520719 4503599627370496000 2176625000921861633 2521000000000000000000 147148917 524288 907 1048576 (ep841 rfl) rfl) (Enclosure.sfrac_false_div 147148917 524288) (BSN.sin_reduce2 qz451 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 80283214011372880789504) qz35) 226375608064910080 72057594037927936 Bool.false 916029 1048576 44 1000000000000000 282352 141176 (BSN.sin_reduce_arg_pos_rat_q2 147148917 524288 226375608064910080 72057594037927936 44 80283214011372880789504 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 916029 1048576 80283214011372880789504 75557863725914323419136 2281786180 2147483648 282628 282352 (ep849 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep851 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz41 (Real.cos qz160)) (@HMul.hMul Real Real Real qz0 qz41 (@Neg.neg Real Real.instNeg (Real.sin qz160))) Bool.true 84603938583 549755813888 95711431443 346483601702912 Bool.false 303745140081 1099511627776 766714309479 2771868813623296 (@Enclosure.Real.IsNear.mulLit_ft qz41 (Real.cos qz160) 331589 1048576 1 1048576 255147 524288 16136901 18504220672 84603938583 549755813888 95711431443 346483601702912 qz321 (@Enclosure.Real.IsNear.recentre' (Real.cos qz160) Bool.true 510294 1048576 129095208 148033765376 255147 524288 16136901 18504220672 (ep846 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz41 (@Neg.neg Real Real.instNeg (Real.sin qz160)) 331589 1048576 1 1048576 916029 1048576 16136901 18504220672 303745140081 1099511627776 766714309479 2771868813623296 qz321 (@Enclosure.Real.IsNear.neg (Real.sin qz160) Bool.true 916029 1048576 16136901 18504220672 (@Enclosure.Real.IsNear.recentre' (Real.sin qz160) Bool.true 916029 1048576 129095208 148033765376 916029 1048576 16136901 18504220672 (ep850 rfl rfl) rfl)) rfl)

noncomputable def ep852 := @ep825 84603938583 549755813888 95711431443 346483601702912 Bool.false 303745140081 1099511627776 766714309479 2771868813623296 Bool.false 3697003025081376440320 13449618655 549755813888 34038470313289 9701540847681536 Bool.false 125278092001955517825024 28484940231 274877906944 34068132308533 9701540847681536 (ep826 (BSN.head_sum_c_succ qz146 9 10 rfl rfl) (ep839 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep840 ep851) rfl rfl

noncomputable abbrev qz161 := (@HMul.hMul Real Real Real qz268 qz441 qz556)

noncomputable def ep853 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz313 qz147) (Complex.mk (@HMul.hMul Real Real Real qz0 qz43 (Real.cos qz161)) (@HMul.hMul Real Real Real qz0 qz43 (@Neg.neg Real Real.instNeg (Real.sin qz161)))) Bool.true 164688394399 549755813888 2557307998895 9701540847681536 Bool.false 37587589573 1099511627776 5098329140315 19403081695363072 (BSN.cpow_neg_s_mk qz149 121891 1000 11 qz150 rfl)

noncomputable def ep854 := @Enclosure.Real.IsNear.mulLit_ff qz149 qz556 121891 1000 0 1 10799156221662949 4503599627370496 125000000052941 17647000000000000000 1316319951014718516559 4503599627370496000 2176625000921861633 2521000000000000000000 qz151 (BSN.isNear_log_sfrac 11 1 10799156221662949 4503599627370496 125000000052941 17647000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz323) Bool.false 45294944137145793642496 18889465931478580854784 1000000000423528 141176000000000000000 10799156221662949 4503599627370496 125000000052941 17647000000000000000 (BSN.log_rat_reduce_isNear 11 1 3 22 16 166961 524288 24973259072661432 36028797018963968 141176 1000000000000000 rfl rfl rfl rfl (ep214 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep855 := nat_lit 3545148191700962376696988866945681

noncomputable def ep856 := BSN.cos_dyadic_bound_f 244010547 2147483648 2 1 1048576 282628 ep855 ep140 ep855 ep855 ep141 ep855 1041814 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 244010547) qz16 0 1 ep855 ep140 ep855 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 244010547) qz282 0 1 ep855 ep141 ep855 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz452 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 306479621) qz17)

noncomputable def ep857 := @Enclosure.Real.IsNear.cos_image qz161 qz452 Bool.false 306479621 1048576 453 524288 Bool.true 1041814 1048576 1 141176 (@Enclosure.Real.IsNear.recentre' qz161 Bool.false 1316319951014718516559 4503599627370496000 2176625000921861633 2521000000000000000000 306479621 1048576 453 524288 (ep854 rfl) rfl) (Enclosure.sfrac_false_div 306479621 1048576) (BSN.cos_reduce2 qz452 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 17170715809592620613632) qz20) 226375608064910080 72057594037927936 Bool.false 1041814 1048576 46 1000000000000000 282352 141176 (BSN.sin_reduce_arg_pos_rat_q2 306479621 1048576 226375608064910080 72057594037927936 46 17170715809592620613632 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1041814 1048576 17170715809592620613632 151115727451828646838272 244010547 2147483648 282628 282352 (ep856 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep858 := BSN.sin_dyadic_bound_f 244010547 2147483648 1 0 1048576 282628 0 1 1 0 1 1 118889 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 244010547) qz21 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 244010547) qz285 0 0 rfl) rfl rfl

noncomputable def ep859 := @Enclosure.Real.IsNear.sin_image qz161 qz452 Bool.false 306479621 1048576 453 524288 Bool.true 118889 1048576 1 141176 (@Enclosure.Real.IsNear.recentre' qz161 Bool.false 1316319951014718516559 4503599627370496000 2176625000921861633 2521000000000000000000 306479621 1048576 453 524288 (ep854 rfl) rfl) (Enclosure.sfrac_false_div 306479621 1048576) (BSN.sin_reduce2 qz452 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 17170715809592620613632) qz20) 226375608064910080 72057594037927936 Bool.false 118889 1048576 46 1000000000000000 282352 141176 (BSN.sin_reduce_arg_pos_rat_q2 306479621 1048576 226375608064910080 72057594037927936 46 17170715809592620613632 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 118889 1048576 17170715809592620613632 151115727451828646838272 244010547 2147483648 282628 282352 (ep858 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep860 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz43 (Real.cos qz161)) (@HMul.hMul Real Real Real qz0 qz43 (@Neg.neg Real Real.instNeg (Real.sin qz161))) Bool.true 164688394399 549755813888 2557307998895 9701540847681536 Bool.false 37587589573 1099511627776 5098329140315 19403081695363072 (@Enclosure.Real.IsNear.mulLit_ft qz43 (Real.cos qz161) 316157 1048576 1 1048576 520907 524288 8059627 9252110336 164688394399 549755813888 2557307998895 9701540847681536 qz325 (@Enclosure.Real.IsNear.recentre' (Real.cos qz161) Bool.true 1041814 1048576 64477016 74016882688 520907 524288 8059627 9252110336 (ep857 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz43 (@Neg.neg Real Real.instNeg (Real.sin qz161)) 316157 1048576 1 1048576 118889 1048576 8059627 9252110336 37587589573 1099511627776 5098329140315 19403081695363072 qz325 (@Enclosure.Real.IsNear.neg (Real.sin qz161) Bool.true 118889 1048576 8059627 9252110336 (@Enclosure.Real.IsNear.recentre' (Real.sin qz161) Bool.true 118889 1048576 64477016 74016882688 118889 1048576 8059627 9252110336 (ep859 rfl rfl) rfl)) rfl)

noncomputable def ep861 := @ep823 164688394399 549755813888 2557307998895 9701540847681536 Bool.false 37587589573 1099511627776 5098329140315 19403081695363072 Bool.true 83144396250567432732672 2363105871 8589934592 653496041289 173241800851456 Bool.false 41651520949385238151168 151527350497 1099511627776 10462084822483 2771868813623296 (ep824 (BSN.head_sum_c_succ qz146 10 11 rfl rfl) (ep852 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep853 ep860) rfl rfl

noncomputable abbrev qz162 := (@HMul.hMul Real Real Real qz268 qz441 qz557)

noncomputable def ep862 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz312 qz147) (Complex.mk (@HMul.hMul Real Real Real qz0 qz45 (Real.cos qz162)) (@HMul.hMul Real Real Real qz0 qz45 (@Neg.neg Real Real.instNeg (Real.sin qz162)))) Bool.false 21627397953 274877906944 610538673663 2425385211920384 Bool.true 76345934643 274877906944 306066848879 1212692605960192 (BSN.cpow_neg_s_mk qz149 121891 1000 12 qz150 rfl)

noncomputable def ep863 := @Enclosure.Real.IsNear.mulLit_ff qz149 qz557 121891 1000 0 1 11191020447815397 4503599627370496 125000000052941 17647000000000000000 1364084673404666555727 4503599627370496000 2176625000921861633 2521000000000000000000 qz151 (BSN.isNear_log_sfrac 12 1 11191020447815397 4503599627370496 125000000052941 17647000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz327) Bool.false 46938541828353910898688 18889465931478580854784 1000000000423528 141176000000000000000 11191020447815397 4503599627370496 125000000052941 17647000000000000000 (BSN.log_rat_reduce_isNear 12 1 3 24 16 212580 524288 24973259072661432 36028797018963968 141176 1000000000000000 rfl rfl rfl rfl (ep229 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep864 := nat_lit 2139015518460308628683421817458719806660261149731485277538933932716526712791296

noncomputable def ep865 := nat_lit 3572059347270240348129124413333635238520599166953155984155203411987466690816

noncomputable def ep866 := nat_lit 6409902436686385405354007203549492149503742250860549520648491391325605204992256

noncomputable def ep867 := BSN.cos_dyadic_bound_f 2780448358 2147483648 3 2 1048576 282628 ep864 ep58 ep865 ep866 ep61 ep865 285796 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2780448358) qz16 0 2 ep864 ep58 ep865 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2780448358) qz282 0 2 ep866 ep61 ep865 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz453 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 39700089) qz568)

noncomputable def ep868 := @Enclosure.Real.IsNear.cos_image qz162 qz453 Bool.false 39700089 131072 453 524288 Bool.false 285796 1048576 1 141176 (@Enclosure.Real.IsNear.recentre' qz162 Bool.false 1364084673404666555727 4503599627370496000 2176625000921861633 2521000000000000000000 39700089 131072 453 524288 (ep863 rfl) rfl) (Enclosure.sfrac_false_div 39700089 131072) (BSN.cos_reduce0 qz453 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 24457082408709220466688) qz369) 226375608064910080 72057594037927936 Bool.false 285796 1048576 48 1000000000000000 282352 141176 (BSN.sin_reduce_arg_pos_rat_q0 39700089 131072 226375608064910080 72057594037927936 48 24457082408709220466688 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 285796 1048576 24457082408709220466688 18889465931478580854784 2780448358 2147483648 282628 282352 (ep867 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep869 := nat_lit 3847370285750739339351655971895028743797653590183110974782756916160158109671680

noncomputable def ep870 := nat_lit 10070662652308736928214508963055868443369583194685461729028112070133386769735936

noncomputable def ep871 := BSN.sin_dyadic_bound_f 2780448358 2147483648 3 2 1048576 282628 ep869 ep65 ep865 ep870 ep67 ep865 1008876 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2780448358) qz21 0 2 ep869 ep65 ep865 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2780448358) qz285 0 2 ep870 ep67 ep865 rfl rfl rfl rfl) rfl rfl

noncomputable def ep872 := @Enclosure.Real.IsNear.sin_image qz162 qz453 Bool.false 39700089 131072 453 524288 Bool.false 1008876 1048576 1 141176 (@Enclosure.Real.IsNear.recentre' qz162 Bool.false 1364084673404666555727 4503599627370496000 2176625000921861633 2521000000000000000000 39700089 131072 453 524288 (ep863 rfl) rfl) (Enclosure.sfrac_false_div 39700089 131072) (BSN.sin_reduce0 qz453 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 24457082408709220466688) qz369) 226375608064910080 72057594037927936 Bool.false 1008876 1048576 48 1000000000000000 282352 141176 (BSN.sin_reduce_arg_pos_rat_q0 39700089 131072 226375608064910080 72057594037927936 48 24457082408709220466688 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1008876 1048576 24457082408709220466688 18889465931478580854784 2780448358 2147483648 282628 282352 (ep871 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep873 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz45 (Real.cos qz162)) (@HMul.hMul Real Real Real qz0 qz45 (@Neg.neg Real Real.instNeg (Real.sin qz162))) Bool.false 21627397953 274877906944 610538673663 2425385211920384 Bool.true 76345934643 274877906944 306066848879 1212692605960192 (@Enclosure.Real.IsNear.mulLit_ff qz45 (Real.cos qz162) 302697 1048576 1 1048576 71449 262144 8059627 9252110336 21627397953 274877906944 610538673663 2425385211920384 qz329 (@Enclosure.Real.IsNear.recentre' (Real.cos qz162) Bool.false 285796 1048576 64477016 74016882688 71449 262144 8059627 9252110336 (ep868 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz45 (@Neg.neg Real Real.instNeg (Real.sin qz162)) 302697 1048576 1 1048576 252219 262144 8059627 9252110336 76345934643 274877906944 306066848879 1212692605960192 qz329 (@Enclosure.Real.IsNear.neg (Real.sin qz162) Bool.false 252219 262144 8059627 9252110336 (@Enclosure.Real.IsNear.recentre' (Real.sin qz162) Bool.false 1008876 1048576 64477016 74016882688 252219 262144 8059627 9252110336 (ep872 rfl rfl) rfl)) rfl)

noncomputable def ep874 := @ep821 21627397953 274877906944 610538673663 2425385211920384 Bool.true 76345934643 274877906944 306066848879 1212692605960192 Bool.true 463787661896133378048 53991989919 274877906944 9759483251709 2425385211920384 Bool.true 42291721924019801292800 153856388075 1099511627776 78131663339445 19403081695363072 (ep822 (BSN.head_sum_c_succ qz146 11 12 rfl rfl) (ep861 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep862 ep873) rfl rfl

noncomputable abbrev qz163 := (@HMul.hMul Real Real Real qz268 qz441 qz558)

noncomputable def ep875 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz311 qz147) (Complex.mk (@HMul.hMul Real Real Real qz0 qz47 (Real.cos qz163)) (@HMul.hMul Real Real Real qz0 qz47 (@Neg.neg Real Real.instNeg (Real.sin qz163)))) Bool.false 16933750821 1099511627776 4688893457165 19403081695363072 Bool.false 304479175611 1099511627776 4706341575475 19403081695363072 (BSN.cpow_neg_s_mk qz149 121891 1000 13 qz150 rfl)

noncomputable def ep876 := @Enclosure.Real.IsNear.mulLit_ff qz149 qz558 121891 1000 0 1 11551497052968677 4503599627370496 125000000052941 17647000000000000000 1408023527283405008207 4503599627370496000 2176625000921861633 2521000000000000000000 qz151 (BSN.isNear_log_sfrac 13 1 11551497052968677 4503599627370496 125000000052941 17647000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz331) Bool.false 48450490295254733815808 18889465931478580854784 1000000000423528 141176000000000000000 11551497052968677 4503599627370496 125000000052941 17647000000000000000 (BSN.log_rat_reduce_isNear 13 1 3 26 16 254545 524288 24973259072661432 36028797018963968 141176 1000000000000000 rfl rfl rfl rfl (ep243 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep877 := BSN.sin_dyadic_bound_f 119311352 2147483648 1 0 1048576 282628 0 1 1 0 1 1 58227 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 119311352) qz21 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 119311352) qz285 0 0 rfl) rfl rfl

noncomputable abbrev qz454 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 20489439) (@Nat.cast Real Real.instNatCast 65536))

noncomputable def ep878 := @Enclosure.Real.IsNear.cos_image qz163 qz454 Bool.false 20489439 65536 453 524288 Bool.false 58227 1048576 1 141176 (@Enclosure.Real.IsNear.recentre' qz163 Bool.false 1408023527283405008207 4503599627370496000 2176625000921861633 2521000000000000000000 20489439 65536 453 524288 (ep876 rfl) rfl) (Enclosure.sfrac_false_div 20489439 65536) (BSN.cos_reduce3 qz454 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 524736875528808562688) qz432) 226375608064910080 72057594037927936 Bool.false 58227 1048576 49 1000000000000000 282352 141176 (BSN.sin_reduce_arg_pos_rat_q3 20489439 65536 226375608064910080 72057594037927936 49 524736875528808562688 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 58227 1048576 524736875528808562688 9444732965739290427392 119311352 2147483648 282628 282352 (ep877 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep879 := BSN.cos_dyadic_bound_f 119311352 2147483648 1 0 1048576 282628 0 1 1 0 1 1 1046957 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 119311352) qz16 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 119311352) qz282 0 0 rfl) rfl rfl

noncomputable def ep880 := @Enclosure.Real.IsNear.sin_image qz163 qz454 Bool.false 20489439 65536 453 524288 Bool.true 1046957 1048576 1 141176 (@Enclosure.Real.IsNear.recentre' qz163 Bool.false 1408023527283405008207 4503599627370496000 2176625000921861633 2521000000000000000000 20489439 65536 453 524288 (ep876 rfl) rfl) (Enclosure.sfrac_false_div 20489439 65536) (BSN.sin_reduce3 qz454 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 524736875528808562688) qz432) 226375608064910080 72057594037927936 Bool.false 1046957 1048576 49 1000000000000000 282352 141176 (BSN.sin_reduce_arg_pos_rat_q3 20489439 65536 226375608064910080 72057594037927936 49 524736875528808562688 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1046957 1048576 524736875528808562688 9444732965739290427392 119311352 2147483648 282628 282352 (ep879 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep881 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz47 (Real.cos qz163)) (@HMul.hMul Real Real Real qz0 qz47 (@Neg.neg Real Real.instNeg (Real.sin qz163))) Bool.false 16933750821 1099511627776 4688893457165 19403081695363072 Bool.false 304479175611 1099511627776 4706341575475 19403081695363072 (@Enclosure.Real.IsNear.mulLit_ff qz47 (Real.cos qz163) 290823 1048576 1 1048576 58227 1048576 8059627 9252110336 16933750821 1099511627776 4688893457165 19403081695363072 qz333 (@Enclosure.Real.IsNear.recentre' (Real.cos qz163) Bool.false 58227 1048576 64477016 74016882688 58227 1048576 8059627 9252110336 (ep878 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz47 (@Neg.neg Real Real.instNeg (Real.sin qz163)) 290823 1048576 1 1048576 1046957 1048576 8059627 9252110336 304479175611 1099511627776 4706341575475 19403081695363072 qz333 (@Enclosure.Real.IsNear.neg (Real.sin qz163) Bool.true 1046957 1048576 8059627 9252110336 (@Enclosure.Real.IsNear.recentre' (Real.sin qz163) Bool.true 1046957 1048576 64477016 74016882688 1046957 1048576 8059627 9252110336 (ep880 rfl rfl) rfl)) rfl)

noncomputable def ep882 := @ep819 16933750821 1099511627776 4688893457165 19403081695363072 Bool.false 304479175611 1099511627776 4706341575475 19403081695363072 Bool.true 54710106740317350789120 199034208855 1099511627776 82764759470837 19403081695363072 Bool.false 165611506303865964199936 9413924221 68719476736 10354750614365 2425385211920384 (ep820 (BSN.head_sum_c_succ qz146 12 13 rfl rfl) (ep874 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep875 ep881) rfl rfl

noncomputable abbrev qz164 := (@HMul.hMul Real Real Real qz268 qz441 qz559)

noncomputable def ep883 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz310 qz147) (Complex.mk (@HMul.hMul Real Real Real qz0 qz49 (Real.cos qz164)) (@HMul.hMul Real Real Real qz0 qz49 (@Neg.neg Real Real.instNeg (Real.sin qz164)))) Bool.false 96917837905 1099511627776 4528372634089 19403081695363072 Bool.true 277413386429 1099511627776 4539738502085 19403081695363072 (BSN.cpow_neg_s_mk qz149 121891 1000 14 qz150 rfl)

noncomputable def ep884 := @Enclosure.Real.IsNear.mulLit_ff qz149 qz559 121891 1000 0 1 11885250371606245 4503599627370496 125000000052941 17647000000000000000 289741010609091361859 900719925474099200 2176625000921861633 2521000000000000000000 qz151 (BSN.isNear_log_sfrac 14 1 11885250371606245 4503599627370496 125000000052941 17647000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz335) Bool.false 49850353174629559828480 18889465931478580854784 1000000000423528 141176000000000000000 11885250371606245 4503599627370496 125000000052941 17647000000000000000 (BSN.log_rat_reduce_isNear 14 1 3 28 16 293399 524288 24973259072661432 36028797018963968 141176 1000000000000000 rfl rfl rfl rfl (ep258 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep885 := nat_lit 1768396617897830227337189854997782207947834635004563068808549763431307516272161

noncomputable def ep886 := nat_lit 2442874517320855409987657546149760081316646229639487720906677589722288578081

noncomputable def ep887 := nat_lit 5300304104658848971191594249901047103680870612554410230983835935114477971660321

noncomputable def ep888 := BSN.cos_dyadic_bound_f 2651475661 2147483648 3 2 1048576 282628 ep885 ep58 ep886 ep887 ep61 ep886 345835 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2651475661) qz16 0 2 ep885 ep58 ep886 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2651475661) qz282 0 2 ep887 ep61 ep886 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz455 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 337302929) qz17)

noncomputable def ep889 := @Enclosure.Real.IsNear.cos_image qz164 qz455 Bool.false 337302929 1048576 907 1048576 Bool.false 345835 1048576 1 141176 (@Enclosure.Real.IsNear.recentre' qz164 Bool.false 289741010609091361859 900719925474099200 2176625000921861633 2521000000000000000000 337302929 1048576 907 1048576 (ep884 rfl) rfl) (Enclosure.sfrac_false_div 337302929 1048576) (BSN.cos_reduce0 qz455 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 186581012508744790048768) qz20) 226375608064910080 72057594037927936 Bool.false 345835 1048576 51 1000000000000000 282352 141176 (BSN.sin_reduce_arg_pos_rat_q0 337302929 1048576 226375608064910080 72057594037927936 51 186581012508744790048768 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 345835 1048576 186581012508744790048768 151115727451828646838272 2651475661 2147483648 282628 282352 (ep888 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep890 := nat_lit 3181159612602237724878951612959088166241049026024501933678664232104575698427425

noncomputable def ep891 := nat_lit 8327653379025436465923940874103845585737758593311422084276938367985766933421601

noncomputable def ep892 := BSN.sin_dyadic_bound_f 2651475661 2147483648 3 2 1048576 282628 ep890 ep65 ep886 ep891 ep67 ep886 989903 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2651475661) qz21 0 2 ep890 ep65 ep886 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2651475661) qz285 0 2 ep891 ep67 ep886 rfl rfl rfl rfl) rfl rfl

noncomputable def ep893 := @Enclosure.Real.IsNear.sin_image qz164 qz455 Bool.false 337302929 1048576 907 1048576 Bool.false 989903 1048576 1 141176 (@Enclosure.Real.IsNear.recentre' qz164 Bool.false 289741010609091361859 900719925474099200 2176625000921861633 2521000000000000000000 337302929 1048576 907 1048576 (ep884 rfl) rfl) (Enclosure.sfrac_false_div 337302929 1048576) (BSN.sin_reduce0 qz455 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 186581012508744790048768) qz20) 226375608064910080 72057594037927936 Bool.false 989903 1048576 51 1000000000000000 282352 141176 (BSN.sin_reduce_arg_pos_rat_q0 337302929 1048576 226375608064910080 72057594037927936 51 186581012508744790048768 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 989903 1048576 186581012508744790048768 151115727451828646838272 2651475661 2147483648 282628 282352 (ep892 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep894 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz49 (Real.cos qz164)) (@HMul.hMul Real Real Real qz0 qz49 (@Neg.neg Real Real.instNeg (Real.sin qz164))) Bool.false 96917837905 1099511627776 4528372634089 19403081695363072 Bool.true 277413386429 1099511627776 4539738502085 19403081695363072 (@Enclosure.Real.IsNear.mulLit_ff qz49 (Real.cos qz164) 280243 1048576 1 1048576 345835 1048576 16136901 18504220672 96917837905 1099511627776 4528372634089 19403081695363072 qz337 (@Enclosure.Real.IsNear.recentre' (Real.cos qz164) Bool.false 345835 1048576 129095208 148033765376 345835 1048576 16136901 18504220672 (ep889 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz49 (@Neg.neg Real Real.instNeg (Real.sin qz164)) 280243 1048576 1 1048576 989903 1048576 16136901 18504220672 277413386429 1099511627776 4539738502085 19403081695363072 qz337 (@Enclosure.Real.IsNear.neg (Real.sin qz164) Bool.false 989903 1048576 16136901 18504220672 (@Enclosure.Real.IsNear.recentre' (Real.sin qz164) Bool.false 989903 1048576 129095208 148033765376 989903 1048576 16136901 18504220672 (ep893 rfl rfl) rfl)) rfl)

noncomputable def ep895 := @ep817 96917837905 1099511627776 4528372634089 19403081695363072 Bool.true 277413386429 1099511627776 4539738502085 19403081695363072 Bool.true 112278137245812339507200 51058185475 549755813888 43646566052463 9701540847681536 Bool.true 8712983610971020853248 126790598893 1099511627776 87377743417005 19403081695363072 (ep818 (BSN.head_sum_c_succ qz146 13 14 rfl rfl) (ep882 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep883 ep894) rfl rfl

noncomputable abbrev qz165 := (@HMul.hMul Real Real Real qz268 qz441 qz560)

noncomputable def ep896 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz309 qz147) (Complex.mk (@HMul.hMul Real Real Real qz0 qz51 (Real.cos qz165)) (@HMul.hMul Real Real Real qz0 qz51 (@Neg.neg Real Real.instNeg (Real.sin qz165)))) Bool.true 277081483479 1099511627776 4382219341561 19403081695363072 Bool.false 61812606969 1099511627776 4368188035391 19403081695363072 (BSN.cpow_neg_s_mk qz149 121891 1000 15 qz150 rfl)

noncomputable def ep897 := @Enclosure.Real.IsNear.mulLit_ff qz149 qz560 121891 1000 0 1 12195965485668069 4503599627370496 125000000052941 17647000000000000000 1486578429013566598479 4503599627370496000 2176625000921861633 2521000000000000000000 qz151 (BSN.isNear_log_sfrac 15 1 12195965485668069 4503599627370496 125000000052941 17647000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz338) Bool.false 51153586820399524478976 18889465931478580854784 1000000000423528 141176000000000000000 12195965485668069 4503599627370496 125000000052941 17647000000000000000 (BSN.log_rat_reduce_isNear 15 1 3 30 16 329571 524288 24973259072661432 36028797018963968 141176 1000000000000000 rfl rfl rfl rfl (ep269 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep898 := nat_lit 49361167887160620046067656122433536

noncomputable def ep899 := BSN.cos_dyadic_bound_f 471353088 2147483648 2 1 1048576 282628 ep898 ep140 ep898 ep898 ep141 ep898 1023419 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 471353088) qz16 0 1 ep898 ep140 ep898 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 471353088) qz282 0 1 ep898 ep141 ep898 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz456 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 86530253) (@Nat.cast Real Real.instNatCast 262144))

noncomputable abbrev qz598 := (@Nat.cast Real Real.instNatCast 37778931862957161709568)

noncomputable def ep900 := @Enclosure.Real.IsNear.cos_image qz165 qz456 Bool.false 86530253 262144 453 524288 Bool.true 1023419 1048576 1 141176 (@Enclosure.Real.IsNear.recentre' qz165 Bool.false 1486578429013566598479 4503599627370496000 2176625000921861633 2521000000000000000000 86530253 262144 453 524288 (ep897 rfl) rfl) (Enclosure.sfrac_false_div 86530253 262144) (BSN.cos_reduce2 qz456 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 8292131227156313276416) qz598) 226375608064910080 72057594037927936 Bool.false 1023419 1048576 52 1000000000000000 282352 141176 (BSN.sin_reduce_arg_pos_rat_q2 86530253 262144 226375608064910080 72057594037927936 52 8292131227156313276416 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1023419 1048576 8292131227156313276416 37778931862957161709568 471353088 2147483648 282628 282352 (ep899 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep901 := BSN.sin_dyadic_bound_f 471353088 2147483648 2 1 1048576 282628 ep898 ep144 ep898 ep898 ep145 ep898 228309 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 471353088) qz21 0 1 ep898 ep144 ep898 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 471353088) qz285 0 1 ep898 ep145 ep898 rfl rfl rfl rfl) rfl rfl

noncomputable def ep902 := @Enclosure.Real.IsNear.sin_image qz165 qz456 Bool.false 86530253 262144 453 524288 Bool.true 228309 1048576 1 141176 (@Enclosure.Real.IsNear.recentre' qz165 Bool.false 1486578429013566598479 4503599627370496000 2176625000921861633 2521000000000000000000 86530253 262144 453 524288 (ep897 rfl) rfl) (Enclosure.sfrac_false_div 86530253 262144) (BSN.sin_reduce2 qz456 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 8292131227156313276416) qz598) 226375608064910080 72057594037927936 Bool.false 228309 1048576 52 1000000000000000 282352 141176 (BSN.sin_reduce_arg_pos_rat_q2 86530253 262144 226375608064910080 72057594037927936 52 8292131227156313276416 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 228309 1048576 8292131227156313276416 37778931862957161709568 471353088 2147483648 282628 282352 (ep901 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep903 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz51 (Real.cos qz165)) (@HMul.hMul Real Real Real qz0 qz51 (@Neg.neg Real Real.instNeg (Real.sin qz165))) Bool.true 277081483479 1099511627776 4382219341561 19403081695363072 Bool.false 61812606969 1099511627776 4368188035391 19403081695363072 (@Enclosure.Real.IsNear.mulLit_ft qz51 (Real.cos qz165) 270741 1048576 1 1048576 1023419 1048576 8059627 9252110336 277081483479 1099511627776 4382219341561 19403081695363072 qz340 (@Enclosure.Real.IsNear.recentre' (Real.cos qz165) Bool.true 1023419 1048576 64477016 74016882688 1023419 1048576 8059627 9252110336 (ep900 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz51 (@Neg.neg Real Real.instNeg (Real.sin qz165)) 270741 1048576 1 1048576 228309 1048576 8059627 9252110336 61812606969 1099511627776 4368188035391 19403081695363072 qz340 (@Enclosure.Real.IsNear.neg (Real.sin qz165) Bool.true 228309 1048576 8059627 9252110336 (@Enclosure.Real.IsNear.recentre' (Real.sin qz165) Bool.true 228309 1048576 64477016 74016882688 228309 1048576 8059627 9252110336 (ep902 rfl rfl) rfl)) rfl)

noncomputable def ep904 := @ep815 277081483479 1099511627776 4382219341561 19403081695363072 Bool.false 61812606969 1099511627776 4368188035391 19403081695363072 Bool.true 208466225086198240509952 379197854429 1099511627776 91675351446487 19403081695363072 Bool.true 71444057669973022081024 16244497981 274877906944 22936482863099 4850770423840768 (ep816 (BSN.head_sum_c_succ qz146 14 15 rfl rfl) (ep895 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep896 ep903) rfl rfl

noncomputable abbrev qz166 := (@HMul.hMul Real Real Real qz268 qz441 qz561)

noncomputable def ep905 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz308 qz147) (Complex.mk (@HMul.hMul Real Real Real qz0 qz53 (Real.cos qz166)) (@HMul.hMul Real Real Real qz0 qz53 (@Neg.neg Real Real.instNeg (Real.sin qz166)))) Bool.false 31654029393 549755813888 2114913753185 9701540847681536 Bool.false 133743523599 549755813888 2121786236159 9701540847681536 (BSN.cpow_neg_s_mk qz149 121891 1000 16 qz150 rfl)

noncomputable def ep906 := @Enclosure.Real.IsNear.mulLit_ff qz149 qz561 121891 1000 0 1 3121657384082679 1125899906842624 31250000017647 4411750000000000000 380501940203221825989 1125899906842624000 544156250307287211 630250000000000000000 qz151 (BSN.isNear_log_sfrac 16 1 3121657384082679 1125899906842624 31250000017647 4411750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz341) Bool.false 52372720210750067441664 18889465931478580854784 1000000000564704 141176000000000000000 3121657384082679 1125899906842624 31250000017647 4411750000000000000 (BSN.log_rat_reduce_isNear 16 1 4 32 32 0 524288 24973259072661432 36028797018963968 141176 1000000000000000 rfl rfl rfl rfl (ep283 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep907 := nat_lit 62040069194151175945193759764632241

noncomputable def ep908 := BSN.sin_dyadic_bound_f 499077589 2147483648 2 1 1048576 282628 ep907 ep144 ep907 ep907 ep145 ep907 241502 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 499077589) qz21 0 1 ep907 ep144 ep907 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 499077589) qz285 0 1 ep907 ep145 ep907 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz457 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 177185023) qz34)

noncomputable def ep909 := @Enclosure.Real.IsNear.cos_image qz166 qz457 Bool.false 177185023 524288 453 524288 Bool.false 241502 1048576 1 141176 (@Enclosure.Real.IsNear.recentre' qz166 Bool.false 380501940203221825989 1125899906842624000 544156250307287211 630250000000000000000 177185023 524288 453 524288 (ep906 rfl) rfl) (Enclosure.sfrac_false_div 177185023 524288) (BSN.cos_reduce3 qz457 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 17559731625699580051456) qz35) 226375608064910080 72057594037927936 Bool.false 241502 1048576 53 1000000000000000 282352 141176 (BSN.sin_reduce_arg_pos_rat_q3 177185023 524288 226375608064910080 72057594037927936 53 17559731625699580051456 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 241502 1048576 17559731625699580051456 75557863725914323419136 499077589 2147483648 282628 282352 (ep908 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep910 := BSN.cos_dyadic_bound_f 499077589 2147483648 2 1 1048576 282628 ep907 ep140 ep907 ep907 ep141 ep907 1020386 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 499077589) qz16 0 1 ep907 ep140 ep907 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 499077589) qz282 0 1 ep907 ep141 ep907 rfl rfl rfl rfl) rfl rfl

noncomputable def ep911 := @Enclosure.Real.IsNear.sin_image qz166 qz457 Bool.false 177185023 524288 453 524288 Bool.true 1020386 1048576 1 141176 (@Enclosure.Real.IsNear.recentre' qz166 Bool.false 380501940203221825989 1125899906842624000 544156250307287211 630250000000000000000 177185023 524288 453 524288 (ep906 rfl) rfl) (Enclosure.sfrac_false_div 177185023 524288) (BSN.sin_reduce3 qz457 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 17559731625699580051456) qz35) 226375608064910080 72057594037927936 Bool.false 1020386 1048576 53 1000000000000000 282352 141176 (BSN.sin_reduce_arg_pos_rat_q3 177185023 524288 226375608064910080 72057594037927936 53 17559731625699580051456 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1020386 1048576 17559731625699580051456 75557863725914323419136 499077589 2147483648 282628 282352 (ep910 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep912 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz53 (Real.cos qz166)) (@HMul.hMul Real Real Real qz0 qz53 (@Neg.neg Real Real.instNeg (Real.sin qz166))) Bool.false 31654029393 549755813888 2114913753185 9701540847681536 Bool.false 133743523599 549755813888 2121786236159 9701540847681536 (@Enclosure.Real.IsNear.mulLit_ff qz53 (Real.cos qz166) 262143 1048576 1 1048576 120751 524288 8059627 9252110336 31654029393 549755813888 2114913753185 9701540847681536 qz343 (@Enclosure.Real.IsNear.recentre' (Real.cos qz166) Bool.false 241502 1048576 64477016 74016882688 120751 524288 8059627 9252110336 (ep909 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz53 (@Neg.neg Real Real.instNeg (Real.sin qz166)) 262143 1048576 1 1048576 510193 524288 8059627 9252110336 133743523599 549755813888 2121786236159 9701540847681536 qz343 (@Enclosure.Real.IsNear.neg (Real.sin qz166) Bool.true 510193 524288 8059627 9252110336 (@Enclosure.Real.IsNear.recentre' (Real.sin qz166) Bool.true 1020386 1048576 64477016 74016882688 510193 524288 8059627 9252110336 (ep911 rfl rfl) rfl)) rfl)

noncomputable def ep913 := @ep813 31654029393 549755813888 2114913753185 9701540847681536 Bool.false 133743523599 549755813888 2121786236159 9701540847681536 Bool.true 173662251702631461289984 315889795643 1099511627776 95905178952857 19403081695363072 Bool.false 27832632625461962211328 101254527637 549755813888 47994751962357 9701540847681536 (ep814 (BSN.head_sum_c_succ qz146 15 16 rfl rfl) (ep904 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep905 ep912) rfl rfl

theorem EMRow39.d13 : Enclosure.Complex.IsNear qz158 Bool.true 315889795643 1099511627776 95905178952857 19403081695363072 Bool.false 101254527637 549755813888 47994751962357 9701540847681536 := ep812 (BSN.head_sum_c_succ qz146 16 17 rfl rfl) (ep913 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable abbrev qz167 := (BSN.headSumC qz439 25)

noncomputable def ep914 := @Enclosure.Complex.IsNear.of_eq qz167 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz146 24) (@HPow.hPow Complex Complex Complex qz6 qz344 qz147)) Bool.false 485967511519 549755813888 31512510753477 4850770423840768 Bool.false 160003348715 1099511627776 126088086645919 19403081695363072

noncomputable def ep915 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz146 24) (@HPow.hPow Complex Complex Complex qz6 qz344 qz147) Bool.false 1100626185827 1099511627776 122589267611351 19403081695363072 Bool.true 23871991171 1099511627776 122622761440881 19403081695363072 Bool.true

noncomputable def ep916 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz146 24) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz146 23) (@HPow.hPow Complex Complex Complex qz6 qz345 qz147)) Bool.false 1100626185827 1099511627776 122589267611351 19403081695363072 Bool.true 23871991171 1099511627776 122622761440881 19403081695363072

noncomputable def ep917 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz146 23) (@HPow.hPow Complex Complex Complex qz6 qz345 qz147) Bool.false 993784972019 1099511627776 119056266127343 19403081695363072 Bool.true 113359345175 549755813888 59541005606057 9701540847681536 Bool.false

noncomputable def ep918 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz146 23) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz146 22) (@HPow.hPow Complex Complex Complex qz6 qz346 qz147)) Bool.false 993784972019 1099511627776 119056266127343 19403081695363072 Bool.true 113359345175 549755813888 59541005606057 9701540847681536

noncomputable def ep919 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz146 22) (@HPow.hPow Complex Complex Complex qz6 qz346 qz147) Bool.false 47816781251 68719476736 57717311833249 9701540847681536 Bool.true 139048727159 549755813888 57737183661127 9701540847681536 Bool.false

noncomputable def ep920 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz146 22) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz146 21) (@HPow.hPow Complex Complex Complex qz6 qz347 qz147)) Bool.false 47816781251 68719476736 57717311833249 9701540847681536 Bool.true 139048727159 549755813888 57737183661127 9701540847681536

noncomputable def ep921 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz146 21) (@HPow.hPow Complex Complex Complex qz6 qz347 qz147) Bool.false 4244673675 8589934592 55856006063645 9701540847681536 Bool.true 93237533015 549755813888 55885913669835 9701540847681536 Bool.false

noncomputable def ep922 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz146 21) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz146 20) (@HPow.hPow Complex Complex Complex qz6 qz348 qz147)) Bool.false 4244673675 8589934592 55856006063645 9701540847681536 Bool.true 93237533015 549755813888 55885913669835 9701540847681536

noncomputable def ep923 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz146 20) (@HPow.hPow Complex Complex Complex qz6 qz348 qz147) Bool.false 179886776255 549755813888 6744919774615 1212692605960192 Bool.true 22897064773 1099511627776 107980034371799 19403081695363072 Bool.false

noncomputable def ep924 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz146 20) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz146 19) (@HPow.hPow Complex Complex Complex qz6 qz349 qz147)) Bool.false 179886776255 549755813888 6744919774615 1212692605960192 Bool.true 22897064773 1099511627776 107980034371799 19403081695363072

noncomputable def ep925 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz146 19) (@HPow.hPow Complex Complex Complex qz6 qz349 qz147) Bool.false 88385830543 549755813888 6501727746463 1212692605960192 Bool.false 150704262049 1099511627776 104089651530833 19403081695363072 Bool.false

noncomputable def ep926 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz146 19) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz146 18) (@HPow.hPow Complex Complex Complex qz6 qz350 qz147)) Bool.false 88385830543 549755813888 6501727746463 1212692605960192 Bool.false 150704262049 1099511627776 104089651530833 19403081695363072

noncomputable def ep927 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz146 18) (@HPow.hPow Complex Complex Complex qz6 qz350 qz147) Bool.true 56373538895 1099511627776 100027091116643 19403081695363072 Bool.false 65966266515 274877906944 50048832896579 9701540847681536 Bool.false

noncomputable def ep928 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz146 18) (@HAdd.hAdd Complex Complex Complex qz4 qz158 (@HPow.hPow Complex Complex Complex qz6 qz351 qz147)) Bool.true 56373538895 1099511627776 100027091116643 19403081695363072 Bool.false 65966266515 274877906944 50048832896579 9701540847681536

noncomputable def ep929 := @Enclosure.Complex.IsNear.addLitP qz158 (@HPow.hPow Complex Complex Complex qz6 qz351 qz147) Bool.true 315889795643 1099511627776 95905178952857 19403081695363072 Bool.false 101254527637 549755813888 47994751962357 9701540847681536 Bool.false

noncomputable abbrev qz168 := (@HMul.hMul Real Real Real qz268 qz441 qz562)

noncomputable def ep930 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz351 qz147) (Complex.mk (@HMul.hMul Real Real Real qz0 qz56 (Real.cos qz168)) (@HMul.hMul Real Real Real qz0 qz56 (@Neg.neg Real Real.instNeg (Real.sin qz168)))) Bool.false 64879064187 274877906944 2060956081893 9701540847681536 Bool.false 30678005393 549755813888 1027040467111 4850770423840768 (BSN.cpow_neg_s_mk qz149 121891 1000 17 qz150 rfl)

noncomputable def ep931 := @Enclosure.Real.IsNear.mulLit_ff qz149 qz562 121891 1000 0 1 3189913004350711 1125899906842624 31250000017647 4411750000000000000 388821686013312514501 1125899906842624000 544156250307287211 630250000000000000000 qz151 (BSN.isNear_log_sfrac 17 1 3189913004350711 1125899906842624 31250000017647 4411750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz352) Bool.false 53517859495200818200576 18889465931478580854784 1000000000564704 141176000000000000000 3189913004350711 1125899906842624 31250000017647 4411750000000000000 (BSN.log_rat_reduce_isNear 17 1 4 34 32 31784 524288 24973259072661432 36028797018963968 141176 1000000000000000 rfl rfl rfl rfl (ep312 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep932 := nat_lit 4396727607552763561016672286238769736204755615109337965164672535959140418417185

noncomputable def ep933 := nat_lit 4663744977240775338331481105591426838425181476701613483976798116791164564001

noncomputable def ep934 := nat_lit 11507688146960752833067319304073439379940719174324082534552465635322943972274721

noncomputable def ep935 := BSN.sin_dyadic_bound_f 2874695501 2147483648 3 2 1048576 282628 ep932 ep65 ep933 ep934 ep67 ep933 1020444 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2874695501) qz21 0 2 ep932 ep65 ep933 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2874695501) qz285 0 2 ep934 ep67 ep933 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz458 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 362118413) qz17)

noncomputable def ep936 := @Enclosure.Real.IsNear.cos_image qz168 qz458 Bool.false 362118413 1048576 907 1048576 Bool.false 1020444 1048576 1 141176 (@Enclosure.Real.IsNear.recentre' qz168 Bool.false 388821686013312514501 1125899906842624000 544156250307287211 630250000000000000000 362118413 1048576 907 1048576 (ep931 rfl) rfl) (Enclosure.sfrac_false_div 362118413 1048576) (BSN.cos_reduce3 qz458 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 202288712328069687279616) qz20) 226375608064910080 72057594037927936 Bool.false 1020444 1048576 54 1000000000000000 282352 141176 (BSN.sin_reduce_arg_pos_rat_q3 362118413 1048576 226375608064910080 72057594037927936 54 202288712328069687279616 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1020444 1048576 202288712328069687279616 151115727451828646838272 2874695501 2147483648 282628 282352 (ep935 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep937 := nat_lit 2444699224185864545159631928401801598708608755717055142195474430251429638926881

noncomputable def ep938 := nat_lit 7324770182603112084802232822994221942448975904197762199618469694520706587652641

noncomputable def ep939 := BSN.cos_dyadic_bound_f 2874695501 2147483648 3 2 1048576 282628 ep937 ep58 ep933 ep938 ep61 ep933 241258 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2874695501) qz16 0 2 ep937 ep58 ep933 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2874695501) qz282 0 2 ep938 ep61 ep933 rfl rfl rfl rfl) rfl rfl

noncomputable def ep940 := @Enclosure.Real.IsNear.sin_image qz168 qz458 Bool.false 362118413 1048576 907 1048576 Bool.true 241258 1048576 1 141176 (@Enclosure.Real.IsNear.recentre' qz168 Bool.false 388821686013312514501 1125899906842624000 544156250307287211 630250000000000000000 362118413 1048576 907 1048576 (ep931 rfl) rfl) (Enclosure.sfrac_false_div 362118413 1048576) (BSN.sin_reduce3 qz458 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 202288712328069687279616) qz20) 226375608064910080 72057594037927936 Bool.false 241258 1048576 54 1000000000000000 282352 141176 (BSN.sin_reduce_arg_pos_rat_q3 362118413 1048576 226375608064910080 72057594037927936 54 202288712328069687279616 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 241258 1048576 202288712328069687279616 151115727451828646838272 2874695501 2147483648 282628 282352 (ep939 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep941 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz56 (Real.cos qz168)) (@HMul.hMul Real Real Real qz0 qz56 (@Neg.neg Real Real.instNeg (Real.sin qz168))) Bool.false 64879064187 274877906944 2060956081893 9701540847681536 Bool.false 30678005393 549755813888 1027040467111 4850770423840768 (@Enclosure.Real.IsNear.mulLit_ff qz56 (Real.cos qz168) 254317 1048576 1 1048576 255111 262144 16136901 18504220672 64879064187 274877906944 2060956081893 9701540847681536 qz354 (@Enclosure.Real.IsNear.recentre' (Real.cos qz168) Bool.false 1020444 1048576 129095208 148033765376 255111 262144 16136901 18504220672 (ep936 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz56 (@Neg.neg Real Real.instNeg (Real.sin qz168)) 254317 1048576 1 1048576 120629 524288 16136901 18504220672 30678005393 549755813888 1027040467111 4850770423840768 qz354 (@Enclosure.Real.IsNear.neg (Real.sin qz168) Bool.true 120629 524288 16136901 18504220672 (@Enclosure.Real.IsNear.recentre' (Real.sin qz168) Bool.true 241258 1048576 129095208 148033765376 120629 524288 16136901 18504220672 (ep940 rfl rfl) rfl)) rfl)

noncomputable def ep942 := @ep929 64879064187 274877906944 2060956081893 9701540847681536 Bool.false 30678005393 549755813888 1027040467111 4850770423840768 Bool.true 15495840378483774586880 56373538895 1099511627776 100027091116643 19403081695363072 Bool.false 72530677074213092720640 65966266515 274877906944 50048832896579 9701540847681536 EMRow39.d13 (ep930 ep941) rfl rfl

noncomputable abbrev qz169 := (@HMul.hMul Real Real Real qz268 qz441 qz563)

noncomputable def ep943 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz350 qz147) (Complex.mk (@HMul.hMul Real Real Real qz0 qz58 (Real.cos qz169)) (@HMul.hMul Real Real Real qz0 qz58 (@Neg.neg Real Real.instNeg (Real.sin qz169)))) Bool.false 233145199981 1099511627776 4000552826765 19403081695363072 Bool.true 113160804011 1099511627776 3991985737675 19403081695363072 (BSN.cpow_neg_s_mk qz149 121891 1000 18 qz150 rfl)

noncomputable def ep944 := @Enclosure.Real.IsNear.mulLit_ff qz149 qz563 121891 1000 0 1 3254268794313975 1125899906842624 31250000017647 4411750000000000000 15866643104308989069 45035996273704960 544156250307287211 630250000000000000000 qz151 (BSN.isNear_log_sfrac 18 1 3254268794313975 1125899906842624 31250000017647 4411750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz355) Bool.false 54597570484265130393600 18889465931478580854784 1000000000564704 141176000000000000000 3254268794313975 1125899906842624 31250000017647 4411750000000000000 (BSN.log_rat_reduce_isNear 18 1 4 36 32 61752 524288 24973259072661432 36028797018963968 141176 1000000000000000 rfl rfl rfl rfl (ep322 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep945 := nat_lit 886710135913904411387213500108416016

noncomputable def ep946 := BSN.cos_dyadic_bound_f 970388002 2147483648 2 1 1048576 282628 ep945 ep140 ep945 ep945 ep141 ep945 943331 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 970388002) qz16 0 1 ep945 ep140 ep945 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 970388002) qz282 0 1 ep945 ep141 ep945 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz459 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 46178009) qz568)

noncomputable def ep947 := @Enclosure.Real.IsNear.cos_image qz169 qz459 Bool.false 46178009 131072 453 524288 Bool.false 943331 1048576 1 141176 (@Enclosure.Real.IsNear.recentre' qz169 Bool.false 15866643104308989069 45035996273704960 544156250307287211 630250000000000000000 46178009 131072 453 524288 (ep944 rfl) rfl) (Enclosure.sfrac_false_div 46178009 131072) (BSN.cos_reduce0 qz459 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 8535623139972882628608) qz369) 226375608064910080 72057594037927936 Bool.false 943331 1048576 56 1000000000000000 282352 141176 (BSN.sin_reduce_arg_pos_rat_q0 46178009 131072 226375608064910080 72057594037927936 56 8535623139972882628608 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 943331 1048576 8535623139972882628608 18889465931478580854784 970388002 2147483648 282628 282352 (ep946 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep948 := BSN.sin_dyadic_bound_f 970388002 2147483648 2 1 1048576 282628 ep945 ep144 ep945 ep945 ep145 ep945 457861 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 970388002) qz21 0 1 ep945 ep144 ep945 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 970388002) qz285 0 1 ep945 ep145 ep945 rfl rfl rfl rfl) rfl rfl

noncomputable def ep949 := @Enclosure.Real.IsNear.sin_image qz169 qz459 Bool.false 46178009 131072 453 524288 Bool.false 457861 1048576 1 141176 (@Enclosure.Real.IsNear.recentre' qz169 Bool.false 15866643104308989069 45035996273704960 544156250307287211 630250000000000000000 46178009 131072 453 524288 (ep944 rfl) rfl) (Enclosure.sfrac_false_div 46178009 131072) (BSN.sin_reduce0 qz459 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 8535623139972882628608) qz369) 226375608064910080 72057594037927936 Bool.false 457861 1048576 56 1000000000000000 282352 141176 (BSN.sin_reduce_arg_pos_rat_q0 46178009 131072 226375608064910080 72057594037927936 56 8535623139972882628608 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 457861 1048576 8535623139972882628608 18889465931478580854784 970388002 2147483648 282628 282352 (ep948 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep950 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz58 (Real.cos qz169)) (@HMul.hMul Real Real Real qz0 qz58 (@Neg.neg Real Real.instNeg (Real.sin qz169))) Bool.false 233145199981 1099511627776 4000552826765 19403081695363072 Bool.true 113160804011 1099511627776 3991985737675 19403081695363072 (@Enclosure.Real.IsNear.mulLit_ff qz58 (Real.cos qz169) 247151 1048576 1 1048576 943331 1048576 8059627 9252110336 233145199981 1099511627776 4000552826765 19403081695363072 qz357 (@Enclosure.Real.IsNear.recentre' (Real.cos qz169) Bool.false 943331 1048576 64477016 74016882688 943331 1048576 8059627 9252110336 (ep947 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz58 (@Neg.neg Real Real.instNeg (Real.sin qz169)) 247151 1048576 1 1048576 457861 1048576 8059627 9252110336 113160804011 1099511627776 3991985737675 19403081695363072 qz357 (@Enclosure.Real.IsNear.neg (Real.sin qz169) Bool.false 457861 1048576 8059627 9252110336 (@Enclosure.Real.IsNear.recentre' (Real.sin qz169) Bool.false 457861 1048576 64477016 74016882688 457861 1048576 8059627 9252110336 (ep949 rfl rfl) rfl)) rfl)

noncomputable def ep951 := @ep927 233145199981 1099511627776 4000552826765 19403081695363072 Bool.true 113160804011 1099511627776 3991985737675 19403081695363072 Bool.false 194362496825335255924736 88385830543 549755813888 6501727746463 1212692605960192 Bool.false 41425272119569212768256 150704262049 1099511627776 104089651530833 19403081695363072 (ep928 (BSN.head_sum_c_succ qz146 17 18 rfl rfl) (ep942 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep943 ep950) rfl rfl

noncomputable abbrev qz170 := (@HMul.hMul Real Real Real qz268 qz441 qz564)

noncomputable def ep952 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz349 qz147) (Complex.mk (@HMul.hMul Real Real Real qz0 qz60 (Real.cos qz170)) (@HMul.hMul Real Real Real qz0 qz60 (@Neg.neg Real Real.instNeg (Real.sin qz170)))) Bool.false 5718809107 34359738368 30399003519 151586575745024 Bool.true 86800663411 549755813888 1945191420483 9701540847681536 (BSN.cpow_neg_s_mk qz149 121891 1000 19 qz150 rfl)

noncomputable def ep953 := @Enclosure.Real.IsNear.mulLit_ff qz149 qz564 121891 1000 0 1 3315143513283831 1125899906842624 31250000017647 4411750000000000000 404086157977679444421 1125899906842624000 544156250307287211 630250000000000000000 qz151 (BSN.isNear_log_sfrac 19 1 3315143513283831 1125899906842624 31250000017647 4411750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz358) Bool.false 55618878793361701994496 18889465931478580854784 1000000000564704 141176000000000000000 3315143513283831 1125899906842624 31250000017647 4411750000000000000 (BSN.log_rat_reduce_isNear 19 1 4 38 32 90099 524288 24973259072661432 36028797018963968 141176 1000000000000000 rfl rfl rfl rfl (ep333 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep954 := nat_lit 252289294460326331277092653754610940749153840396542141173361954093614640800000

noncomputable def ep955 := nat_lit 49838911951397371957041978986340702137793538812546862721264162208100000000

noncomputable def ep956 := nat_lit 756768205557076199087363877305860140843185934112001329794643333956427722400000

noncomputable def ep957 := BSN.cos_dyadic_bound_f 1630031770 2147483648 3 2 1048576 282628 ep954 ep58 ep955 ep956 ep61 ep955 760736 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1630031770) qz16 0 2 ep954 ep58 ep955 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1630031770) qz282 0 2 ep956 ep61 ep955 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz460 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 376334561) qz17)

noncomputable def ep958 := @Enclosure.Real.IsNear.cos_image qz170 qz460 Bool.false 376334561 1048576 453 524288 Bool.false 760736 1048576 1 141176 (@Enclosure.Real.IsNear.recentre' qz170 Bool.false 404086157977679444421 1125899906842624000 544156250307287211 630250000000000000000 376334561 1048576 453 524288 (ep953 rfl) rfl) (Enclosure.sfrac_false_div 376334561 1048576) (BSN.cos_reduce0 qz460 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 114703288641831621885952) qz20) 226375608064910080 72057594037927936 Bool.false 760736 1048576 57 1000000000000000 282352 141176 (BSN.sin_reduce_arg_pos_rat_q0 376334561 1048576 226375608064910080 72057594037927936 57 114703288641831621885952 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 760736 1048576 114703288641831621885952 151115727451828646838272 1630031770 2147483648 282628 282352 (ep957 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep959 := nat_lit 7059667977419148566699392063022410000

noncomputable def ep960 := BSN.sin_dyadic_bound_f 1630031770 2147483648 2 1 1048576 282628 ep959 ep144 ep959 ep959 ep145 ep959 721658 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1630031770) qz21 0 1 ep959 ep144 ep959 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1630031770) qz285 0 1 ep959 ep145 ep959 rfl rfl rfl rfl) rfl rfl

noncomputable def ep961 := @Enclosure.Real.IsNear.sin_image qz170 qz460 Bool.false 376334561 1048576 453 524288 Bool.false 721658 1048576 1 141176 (@Enclosure.Real.IsNear.recentre' qz170 Bool.false 404086157977679444421 1125899906842624000 544156250307287211 630250000000000000000 376334561 1048576 453 524288 (ep953 rfl) rfl) (Enclosure.sfrac_false_div 376334561 1048576) (BSN.sin_reduce0 qz460 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 114703288641831621885952) qz20) 226375608064910080 72057594037927936 Bool.false 721658 1048576 57 1000000000000000 282352 141176 (BSN.sin_reduce_arg_pos_rat_q0 376334561 1048576 226375608064910080 72057594037927936 57 114703288641831621885952 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 721658 1048576 114703288641831621885952 151115727451828646838272 1630031770 2147483648 282628 282352 (ep960 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep962 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz60 (Real.cos qz170)) (@HMul.hMul Real Real Real qz0 qz60 (@Neg.neg Real Real.instNeg (Real.sin qz170))) Bool.false 5718809107 34359738368 30399003519 151586575745024 Bool.true 86800663411 549755813888 1945191420483 9701540847681536 (@Enclosure.Real.IsNear.mulLit_ff qz60 (Real.cos qz170) 240559 1048576 1 1048576 23773 32768 8059627 9252110336 5718809107 34359738368 30399003519 151586575745024 qz360 (@Enclosure.Real.IsNear.recentre' (Real.cos qz170) Bool.false 760736 1048576 64477016 74016882688 23773 32768 8059627 9252110336 (ep958 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz60 (@Neg.neg Real Real.instNeg (Real.sin qz170)) 240559 1048576 1 1048576 360829 524288 8059627 9252110336 86800663411 549755813888 1945191420483 9701540847681536 qz360 (@Enclosure.Real.IsNear.neg (Real.sin qz170) Bool.false 360829 524288 8059627 9252110336 (@Enclosure.Real.IsNear.recentre' (Real.sin qz170) Bool.false 721658 1048576 64477016 74016882688 360829 524288 8059627 9252110336 (ep961 rfl rfl) rfl)) rfl)

noncomputable def ep963 := @ep925 5718809107 34359738368 30399003519 151586575745024 Bool.true 86800663411 549755813888 1945191420483 9701540847681536 Bool.false 6180862567984754851840 179886776255 549755813888 6744919774615 1212692605960192 Bool.true 12587794479926868967424 22897064773 1099511627776 107980034371799 19403081695363072 (ep926 (BSN.head_sum_c_succ qz146 18 19 rfl rfl) (ep951 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep952 ep962) rfl rfl

noncomputable abbrev qz171 := (@HMul.hMul Real Real Real qz268 qz441 qz565)

noncomputable def ep964 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz348 qz147) (Complex.mk (@HMul.hMul Real Real Real qz0 qz62 (Real.cos qz171)) (@HMul.hMul Real Real Real qz0 qz62 (@Neg.neg Real Real.instNeg (Real.sin qz171)))) Bool.false 91772338945 549755813888 1896647866725 9701540847681536 Bool.true 163578001257 1099511627776 3791792967871 19403081695363072 (BSN.cpow_neg_s_mk qz149 121891 1000 20 qz150 rfl)

noncomputable def ep965 := @Enclosure.Real.IsNear.mulLit_ff qz149 qz565 121891 1000 0 1 3372893643545847 1125899906842624 31250000017647 4411750000000000000 411125379105446836677 1125899906842624000 544156250307287211 630250000000000000000 qz151 (BSN.isNear_log_sfrac 20 1 3372893643545847 1125899906842624 31250000017647 4411750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz361) Bool.false 56587765202795681021952 18889465931478580854784 1000000000564704 141176000000000000000 3372893643545847 1125899906842624 31250000017647 4411750000000000000 (BSN.log_rat_reduce_isNear 20 1 4 40 32 116991 524288 24973259072661432 36028797018963968 141176 1000000000000000 rfl rfl rfl rfl (ep347 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep966 := nat_lit 213405643995892786509304176375416341158394776423639276307792879662132819690625

noncomputable def ep967 := nat_lit 35662283805620329606681147246890351709581654046000093548770004509062890625

noncomputable def ep968 := nat_lit 640145607420067118868699166831755242771765165962825828736281098977380333290625

noncomputable def ep969 := BSN.cos_dyadic_bound_f 1563241745 2147483648 3 2 1048576 282628 ep966 ep58 ep967 ep968 ep61 ep967 782810 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1563241745) qz16 0 2 ep966 ep58 ep967 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1563241745) qz282 0 2 ep968 ep61 ep967 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz461 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 191445173) qz34)

noncomputable def ep970 := @Enclosure.Real.IsNear.cos_image qz171 qz461 Bool.false 191445173 524288 453 524288 Bool.false 782810 1048576 1 141176 (@Enclosure.Real.IsNear.recentre' qz171 Bool.false 411125379105446836677 1125899906842624000 544156250307287211 630250000000000000000 191445173 524288 453 524288 (ep965 rfl) rfl) (Enclosure.sfrac_false_div 191445173 524288) (BSN.cos_reduce0 qz461 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 55001679246310900760576) qz35) 226375608064910080 72057594037927936 Bool.false 782810 1048576 58 1000000000000000 282352 141176 (BSN.sin_reduce_arg_pos_rat_q0 191445173 524288 226375608064910080 72057594037927936 58 55001679246310900760576 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 782810 1048576 55001679246310900760576 75557863725914323419136 1563241745 2147483648 282628 282352 (ep969 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep971 := nat_lit 5971790669943172883074107981557250625

noncomputable def ep972 := BSN.sin_dyadic_bound_f 1563241745 2147483648 2 1 1048576 282628 ep971 ep144 ep971 ep971 ep145 ep971 697653 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1563241745) qz21 0 1 ep971 ep144 ep971 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1563241745) qz285 0 1 ep971 ep145 ep971 rfl rfl rfl rfl) rfl rfl

noncomputable def ep973 := @Enclosure.Real.IsNear.sin_image qz171 qz461 Bool.false 191445173 524288 453 524288 Bool.false 697653 1048576 1 141176 (@Enclosure.Real.IsNear.recentre' qz171 Bool.false 411125379105446836677 1125899906842624000 544156250307287211 630250000000000000000 191445173 524288 453 524288 (ep965 rfl) rfl) (Enclosure.sfrac_false_div 191445173 524288) (BSN.sin_reduce0 qz461 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 55001679246310900760576) qz35) 226375608064910080 72057594037927936 Bool.false 697653 1048576 58 1000000000000000 282352 141176 (BSN.sin_reduce_arg_pos_rat_q0 191445173 524288 226375608064910080 72057594037927936 58 55001679246310900760576 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 697653 1048576 55001679246310900760576 75557863725914323419136 1563241745 2147483648 282628 282352 (ep972 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep974 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz62 (Real.cos qz171)) (@HMul.hMul Real Real Real qz0 qz62 (@Neg.neg Real Real.instNeg (Real.sin qz171))) Bool.false 91772338945 549755813888 1896647866725 9701540847681536 Bool.true 163578001257 1099511627776 3791792967871 19403081695363072 (@Enclosure.Real.IsNear.mulLit_ff qz62 (Real.cos qz171) 234469 1048576 1 1048576 391405 524288 8059627 9252110336 91772338945 549755813888 1896647866725 9701540847681536 qz363 (@Enclosure.Real.IsNear.recentre' (Real.cos qz171) Bool.false 782810 1048576 64477016 74016882688 391405 524288 8059627 9252110336 (ep970 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz62 (@Neg.neg Real Real.instNeg (Real.sin qz171)) 234469 1048576 1 1048576 697653 1048576 8059627 9252110336 163578001257 1099511627776 3791792967871 19403081695363072 qz363 (@Enclosure.Real.IsNear.neg (Real.sin qz171) Bool.false 697653 1048576 8059627 9252110336 (@Enclosure.Real.IsNear.recentre' (Real.sin qz171) Bool.false 697653 1048576 64477016 74016882688 697653 1048576 8059627 9252110336 (ep973 rfl rfl) rfl)) rfl)

noncomputable def ep975 := @ep923 91772338945 549755813888 1896647866725 9701540847681536 Bool.true 163578001257 1099511627776 3791792967871 19403081695363072 Bool.false 149346177976869951897600 4244673675 8589934592 55856006063645 9701540847681536 Bool.true 205031503390282382049280 93237533015 549755813888 55885913669835 9701540847681536 (ep924 (BSN.head_sum_c_succ qz146 19 20 rfl rfl) (ep963 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep964 ep974) rfl rfl

noncomputable abbrev qz172 := (@HMul.hMul Real Real Real qz268 qz441 qz566)

noncomputable def ep976 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz347 qz147) (Complex.mk (@HMul.hMul Real Real Real qz0 qz64 (Real.cos qz172)) (@HMul.hMul Real Real Real qz0 qz64 (@Neg.neg Real Real.instNeg (Real.sin qz172)))) Bool.false 13859391851 68719476736 465326442401 2425385211920384 Bool.true 1431599817 17179869184 462817497823 2425385211920384 (BSN.cpow_neg_s_mk qz149 121891 1000 21 qz150 rfl)

noncomputable def ep977 := @Enclosure.Real.IsNear.mulLit_ff qz149 qz566 121891 1000 0 1 3427826275261687 1125899906842624 31250000017647 4411750000000000000 417821172517922290117 1125899906842624000 544156250307287211 630250000000000000000 qz151 (BSN.isNear_log_sfrac 21 1 3427826275261687 1125899906842624 31250000017647 4411750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz364) Bool.false 57509381830540779323392 18889465931478580854784 1000000000564704 141176000000000000000 3427826275261687 1125899906842624 31250000017647 4411750000000000000 (BSN.log_rat_reduce_isNear 21 1 4 42 32 142571 524288 24973259072661432 36028797018963968 141176 1000000000000000 rfl rfl rfl rfl (ep358 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep978 := nat_lit 501240157575730295610881814839038881

noncomputable def ep979 := BSN.cos_dyadic_bound_f 841417353 2147483648 2 1 1048576 282628 ep978 ep140 ep978 ep978 ep141 ep978 969112 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 841417353) qz16 0 1 ep978 ep140 ep978 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 841417353) qz282 0 1 ep978 ep141 ep978 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz462 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 194563145) qz34)

noncomputable def ep980 := @Enclosure.Real.IsNear.cos_image qz172 qz462 Bool.false 194563145 524288 453 524288 Bool.false 969112 1048576 1 141176 (@Enclosure.Real.IsNear.recentre' qz172 Bool.false 417821172517922290117 1125899906842624000 544156250307287211 630250000000000000000 194563145 524288 453 524288 (ep977 rfl) rfl) (Enclosure.sfrac_false_div 194563145 524288) (BSN.cos_reduce0 qz462 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 29604741237021081600000) qz35) 226375608064910080 72057594037927936 Bool.false 969112 1048576 59 1000000000000000 282352 141176 (BSN.sin_reduce_arg_pos_rat_q0 194563145 524288 226375608064910080 72057594037927936 59 29604741237021081600000 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 969112 1048576 29604741237021081600000 75557863725914323419136 841417353 2147483648 282628 282352 (ep979 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep981 := BSN.sin_dyadic_bound_f 841417353 2147483648 2 1 1048576 282628 ep978 ep144 ep978 ep978 ep145 ep978 400416 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 841417353) qz21 0 1 ep978 ep144 ep978 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 841417353) qz285 0 1 ep978 ep145 ep978 rfl rfl rfl rfl) rfl rfl

noncomputable def ep982 := @Enclosure.Real.IsNear.sin_image qz172 qz462 Bool.false 194563145 524288 453 524288 Bool.false 400416 1048576 1 141176 (@Enclosure.Real.IsNear.recentre' qz172 Bool.false 417821172517922290117 1125899906842624000 544156250307287211 630250000000000000000 194563145 524288 453 524288 (ep977 rfl) rfl) (Enclosure.sfrac_false_div 194563145 524288) (BSN.sin_reduce0 qz462 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 29604741237021081600000) qz35) 226375608064910080 72057594037927936 Bool.false 400416 1048576 59 1000000000000000 282352 141176 (BSN.sin_reduce_arg_pos_rat_q0 194563145 524288 226375608064910080 72057594037927936 59 29604741237021081600000 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 400416 1048576 29604741237021081600000 75557863725914323419136 841417353 2147483648 282628 282352 (ep981 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep983 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz64 (Real.cos qz172)) (@HMul.hMul Real Real Real qz0 qz64 (@Neg.neg Real Real.instNeg (Real.sin qz172))) Bool.false 13859391851 68719476736 465326442401 2425385211920384 Bool.true 1431599817 17179869184 462817497823 2425385211920384 (@Enclosure.Real.IsNear.mulLit_ff qz64 (Real.cos qz172) 114409 524288 1 524288 121139 131072 8059627 9252110336 13859391851 68719476736 465326442401 2425385211920384 qz366 (@Enclosure.Real.IsNear.recentre' (Real.cos qz172) Bool.false 969112 1048576 64477016 74016882688 121139 131072 8059627 9252110336 (ep980 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz64 (@Neg.neg Real Real.instNeg (Real.sin qz172)) 114409 524288 1 524288 12513 32768 8059627 9252110336 1431599817 17179869184 462817497823 2425385211920384 qz366 (@Enclosure.Real.IsNear.neg (Real.sin qz172) Bool.false 12513 32768 8059627 9252110336 (@Enclosure.Real.IsNear.recentre' (Real.sin qz172) Bool.false 400416 1048576 64477016 74016882688 12513 32768 8059627 9252110336 (ep982 rfl rfl) rfl)) rfl)

noncomputable def ep984 := @ep921 13859391851 68719476736 465326442401 2425385211920384 Bool.true 1431599817 17179869184 462817497823 2425385211920384 Bool.false 410743023346061934592 47816781251 68719476736 57717311833249 9701540847681536 Bool.true 2388838942793327968256 139048727159 549755813888 57737183661127 9701540847681536 (ep922 (BSN.head_sum_c_succ qz146 20 21 rfl rfl) (ep975 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep976 ep983) rfl rfl

noncomputable abbrev qz173 := (@HMul.hMul Real Real Real qz268 qz441 qz567)

noncomputable def ep985 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz346 qz147) (Complex.mk (@HMul.hMul Real Real Real qz0 qz66 (Real.cos qz173)) (@HMul.hMul Real Real Real qz0 qz66 (@Neg.neg Real Real.instNeg (Real.sin qz173)))) Bool.false 228716472003 1099511627776 3621642460845 19403081695363072 Bool.false 802793187 17179869184 901910972465 4850770423840768 (BSN.cpow_neg_s_mk qz149 121891 1000 22 qz150 rfl)

noncomputable def ep986 := @Enclosure.Real.IsNear.mulLit_ff qz149 qz567 121891 1000 0 1 3480203401436407 1125899906842624 31250000017647 4411750000000000000 424205472804485085637 1125899906842624000 544156250307287211 630250000000000000000 qz151 (BSN.isNear_log_sfrac 22 1 3480203401436407 1125899906842624 31250000017647 4411750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz367) Bool.false 58388124189833310502912 18889465931478580854784 1000000000564704 141176000000000000000 3480203401436407 1125899906842624 31250000017647 4411750000000000000 (BSN.log_rat_reduce_isNear 22 1 4 44 32 166961 524288 24973259072661432 36028797018963968 141176 1000000000000000 rfl rfl rfl rfl (ep369 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep987 := nat_lit 4545756278449193310612206295179604828286570763018786328035509289534015700107520

noncomputable def ep988 := nat_lit 4984903708383818256764894919266508857869173502623371018654230376143972106496

noncomputable def ep989 := nat_lit 11897481361362884869663873324172533535933040003187812067967560337694379450204416

noncomputable def ep990 := BSN.sin_dyadic_bound_f 2898725538 2147483648 3 2 1048576 282628 ep987 ep65 ep988 ep989 ep67 ep988 1023079 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2898725538) qz21 0 2 ep987 ep65 ep988 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2898725538) qz285 0 2 ep989 ep67 ep988 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz463 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 395072133) qz17)

noncomputable def ep991 := @Enclosure.Real.IsNear.cos_image qz173 qz463 Bool.false 395072133 1048576 453 524288 Bool.false 1023079 1048576 1 141176 (@Enclosure.Real.IsNear.recentre' qz173 Bool.false 424205472804485085637 1125899906842624000 544156250307287211 630250000000000000000 395072133 1048576 453 524288 (ep986 rfl) rfl) (Enclosure.sfrac_false_div 395072133 1048576) (BSN.cos_reduce3 qz463 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 203979675881739812601856) qz20) 226375608064910080 72057594037927936 Bool.false 1023079 1048576 59 1000000000000000 282352 141176 (BSN.sin_reduce_arg_pos_rat_q3 395072133 1048576 226375608064910080 72057594037927936 59 203979675881739812601856 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1023079 1048576 203979675881739812601856 151115727451828646838272 2898725538 2147483648 282628 282352 (ep990 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep992 := nat_lit 2527635667453277980676454561730565575207147834344936124916907041019406043218176

noncomputable def ep993 := nat_lit 7572937194943066305515833895353163707905705156029561632713412662305930185441536

noncomputable def ep994 := BSN.cos_dyadic_bound_f 2898725538 2147483648 3 2 1048576 282628 ep992 ep58 ep988 ep993 ep61 ep988 229824 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2898725538) qz16 0 2 ep992 ep58 ep988 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2898725538) qz282 0 2 ep993 ep61 ep988 rfl rfl rfl rfl) rfl rfl

noncomputable def ep995 := @Enclosure.Real.IsNear.sin_image qz173 qz463 Bool.false 395072133 1048576 453 524288 Bool.true 229824 1048576 1 141176 (@Enclosure.Real.IsNear.recentre' qz173 Bool.false 424205472804485085637 1125899906842624000 544156250307287211 630250000000000000000 395072133 1048576 453 524288 (ep986 rfl) rfl) (Enclosure.sfrac_false_div 395072133 1048576) (BSN.sin_reduce3 qz463 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 203979675881739812601856) qz20) 226375608064910080 72057594037927936 Bool.false 229824 1048576 59 1000000000000000 282352 141176 (BSN.sin_reduce_arg_pos_rat_q3 395072133 1048576 226375608064910080 72057594037927936 59 203979675881739812601856 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 229824 1048576 203979675881739812601856 151115727451828646838272 2898725538 2147483648 282628 282352 (ep994 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep996 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz66 (Real.cos qz173)) (@HMul.hMul Real Real Real qz0 qz66 (@Neg.neg Real Real.instNeg (Real.sin qz173))) Bool.false 228716472003 1099511627776 3621642460845 19403081695363072 Bool.false 802793187 17179869184 901910972465 4850770423840768 (@Enclosure.Real.IsNear.mulLit_ff qz66 (Real.cos qz173) 223557 1048576 1 1048576 1023079 1048576 8059627 9252110336 228716472003 1099511627776 3621642460845 19403081695363072 qz370 (@Enclosure.Real.IsNear.recentre' (Real.cos qz173) Bool.false 1023079 1048576 64477016 74016882688 1023079 1048576 8059627 9252110336 (ep991 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz66 (@Neg.neg Real Real.instNeg (Real.sin qz173)) 223557 1048576 1 1048576 3591 16384 8059627 9252110336 802793187 17179869184 901910972465 4850770423840768 qz370 (@Enclosure.Real.IsNear.neg (Real.sin qz173) Bool.true 3591 16384 8059627 9252110336 (@Enclosure.Real.IsNear.recentre' (Real.sin qz173) Bool.true 229824 1048576 64477016 74016882688 3591 16384 8059627 9252110336 (ep995 rfl rfl) rfl)) rfl)

noncomputable def ep997 := @ep919 228716472003 1099511627776 3621642460845 19403081695363072 Bool.false 802793187 17179869184 901910972465 4850770423840768 Bool.false 68292383265246081449984 993784972019 1099511627776 119056266127343 19403081695363072 Bool.true 1947498720890401587200 113359345175 549755813888 59541005606057 9701540847681536 (ep920 (BSN.head_sum_c_succ qz146 21 22 rfl rfl) (ep984 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep985 ep996) rfl rfl

noncomputable abbrev qz174 := (@HMul.hMul Real Real Real qz268 qz441 qz569)

noncomputable def ep998 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz345 qz147) (Complex.mk (@HMul.hMul Real Real Real qz0 qz68 (Real.cos qz174)) (@HMul.hMul Real Real Real qz0 qz68 (@Neg.neg Real Real.instNeg (Real.sin qz174)))) Bool.false 6677575863 68719476736 441625185501 2425385211920384 Bool.false 202846699179 1099511627776 3540750228767 19403081695363072 (BSN.cpow_neg_s_mk qz149 121891 1000 23 qz150 rfl)

noncomputable def ep999 := @Enclosure.Real.IsNear.mulLit_ff qz149 qz569 121891 1000 0 1 3530250507853047 1125899906842624 31250000017647 4411750000000000000 430305764652715751877 1125899906842624000 544156250307287211 630250000000000000000 qz151 (BSN.isNear_log_sfrac 23 1 3530250507853047 1125899906842624 31250000017647 4411750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz371) Bool.false 59227775304360265777152 18889465931478580854784 1000000000564704 141176000000000000000 3530250507853047 1125899906842624 31250000017647 4411750000000000000 (BSN.log_rat_reduce_isNear 23 1 4 46 32 190266 524288 24973259072661432 36028797018963968 141176 1000000000000000 rfl rfl rfl rfl (ep384 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1000 := nat_lit 1174680891376554692009025902634727696

noncomputable def ep1001 := BSN.sin_dyadic_bound_f 1041070106 2147483648 2 1 1048576 282628 ep1000 ep144 ep1000 ep1000 ep145 ep1000 488656 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1041070106) qz21 0 1 ep1000 ep144 ep1000 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1041070106) qz285 0 1 ep1000 ep145 ep1000 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz464 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 6261773) (@Nat.cast Real Real.instNatCast 16384))

noncomputable def ep1002 := @Enclosure.Real.IsNear.cos_image qz174 qz464 Bool.false 6261773 16384 453 524288 Bool.false 488656 1048576 1 141176 (@Enclosure.Real.IsNear.recentre' qz174 Bool.false 430305764652715751877 1125899906842624000 544156250307287211 630250000000000000000 6261773 16384 453 524288 (ep999 rfl) rfl) (Enclosure.sfrac_false_div 6261773 16384) (BSN.cos_reduce3 qz464 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 1144668687192970756096) (@Nat.cast Real Real.instNatCast 2361183241434822606848)) 226375608064910080 72057594037927936 Bool.false 488656 1048576 60 1000000000000000 282352 141176 (BSN.sin_reduce_arg_pos_rat_q3 6261773 16384 226375608064910080 72057594037927936 60 1144668687192970756096 2361183241434822606848 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 488656 1048576 1144668687192970756096 2361183241434822606848 1041070106 2147483648 282628 282352 (ep1001 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1003 := BSN.cos_dyadic_bound_f 1041070106 2147483648 2 1 1048576 282628 ep1000 ep140 ep1000 ep1000 ep141 ep1000 927753 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1041070106) qz16 0 1 ep1000 ep140 ep1000 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1041070106) qz282 0 1 ep1000 ep141 ep1000 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1004 := @Enclosure.Real.IsNear.sin_image qz174 qz464 Bool.false 6261773 16384 453 524288 Bool.true 927753 1048576 1 141176 (@Enclosure.Real.IsNear.recentre' qz174 Bool.false 430305764652715751877 1125899906842624000 544156250307287211 630250000000000000000 6261773 16384 453 524288 (ep999 rfl) rfl) (Enclosure.sfrac_false_div 6261773 16384) (BSN.sin_reduce3 qz464 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 1144668687192970756096) (@Nat.cast Real Real.instNatCast 2361183241434822606848)) 226375608064910080 72057594037927936 Bool.false 927753 1048576 60 1000000000000000 282352 141176 (BSN.sin_reduce_arg_pos_rat_q3 6261773 16384 226375608064910080 72057594037927936 60 1144668687192970756096 2361183241434822606848 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 927753 1048576 1144668687192970756096 2361183241434822606848 1041070106 2147483648 282628 282352 (ep1003 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1005 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz68 (Real.cos qz174)) (@HMul.hMul Real Real Real qz0 qz68 (@Neg.neg Real Real.instNeg (Real.sin qz174))) Bool.false 6677575863 68719476736 441625185501 2425385211920384 Bool.false 202846699179 1099511627776 3540750228767 19403081695363072 (@Enclosure.Real.IsNear.mulLit_ff qz68 (Real.cos qz174) 218643 1048576 1 1048576 30541 65536 8059627 9252110336 6677575863 68719476736 441625185501 2425385211920384 qz373 (@Enclosure.Real.IsNear.recentre' (Real.cos qz174) Bool.false 488656 1048576 64477016 74016882688 30541 65536 8059627 9252110336 (ep1002 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz68 (@Neg.neg Real Real.instNeg (Real.sin qz174)) 218643 1048576 1 1048576 927753 1048576 8059627 9252110336 202846699179 1099511627776 3540750228767 19403081695363072 qz373 (@Enclosure.Real.IsNear.neg (Real.sin qz174) Bool.true 927753 1048576 8059627 9252110336 (@Enclosure.Real.IsNear.recentre' (Real.sin qz174) Bool.true 927753 1048576 64477016 74016882688 927753 1048576 8059627 9252110336 (ep1004 rfl rfl) rfl)) rfl)

noncomputable def ep1006 := @ep917 6677575863 68719476736 441625185501 2425385211920384 Bool.false 202846699179 1099511627776 3540750228767 19403081695363072 Bool.false 75634455571970939420672 1100626185827 1099511627776 122589267611351 19403081695363072 Bool.true 13123765935340255182848 23871991171 1099511627776 122622761440881 19403081695363072 (ep918 (BSN.head_sum_c_succ qz146 22 23 rfl rfl) (ep997 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep998 ep1005) rfl rfl

noncomputable abbrev qz175 := (@HMul.hMul Real Real Real qz268 qz441 qz570)

noncomputable def ep1007 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz344 qz147) (Complex.mk (@HMul.hMul Real Real Real qz0 qz70 (Real.cos qz175)) (@HMul.hMul Real Real Real qz0 qz70 (@Neg.neg Real Real.instNeg (Real.sin qz175)))) Bool.true 128691162789 1099511627776 3460775402557 19403081695363072 Bool.false 91937669943 549755813888 1732662602519 9701540847681536 (BSN.cpow_neg_s_mk qz149 121891 1000 24 qz150 rfl)

noncomputable def ep1008 := @Enclosure.Real.IsNear.mulLit_ff qz149 qz570 121891 1000 0 1 3578169457974519 1125899906842624 31250000017647 4411750000000000000 436146653401972095429 1125899906842624000 544156250307287211 630250000000000000000 qz151 (BSN.isNear_log_sfrac 24 1 3578169457974519 1125899906842624 31250000017647 4411750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz374) Bool.false 60031721881041427759104 18889465931478580854784 1000000000564704 141176000000000000000 3578169457974519 1125899906842624 31250000017647 4411750000000000000 (BSN.log_rat_reduce_isNear 24 1 4 48 32 212580 524288 24973259072661432 36028797018963968 141176 1000000000000000 rfl rfl rfl rfl (ep395 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1009 := nat_lit 646133246133695066591860717059678969173891862612562589795409792444079784969761

noncomputable def ep1010 := nat_lit 326698694770605121416067685776362902683432111568866293094238394948418651681

noncomputable def ep1011 := nat_lit 1937746341011543989532750015807484181716308723614550036800040900542342517605921

noncomputable def ep1012 := BSN.cos_dyadic_bound_f 2061903923 2147483648 3 2 1048576 282628 ep1009 ep58 ep1010 ep1011 ep61 ep1010 601251 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2061903923) qz16 0 2 ep1009 ep58 ep1010 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2061903923) qz282 0 2 ep1011 ep61 ep1010 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz465 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 50774153) qz568)

noncomputable def ep1013 := @Enclosure.Real.IsNear.cos_image qz175 qz465 Bool.false 50774153 131072 453 524288 Bool.true 601251 1048576 1 141176 (@Enclosure.Real.IsNear.recentre' qz175 Bool.false 436146653401972095429 1125899906842624000 544156250307287211 630250000000000000000 50774153 131072 453 524288 (ep1008 rfl) rfl) (Enclosure.sfrac_false_div 50774153 131072) (BSN.cos_reduce2 qz465 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 18136698717443725459456) qz369) 226375608064910080 72057594037927936 Bool.false 601251 1048576 61 1000000000000000 282352 141176 (BSN.sin_reduce_arg_pos_rat_q2 50774153 131072 226375608064910080 72057594037927936 61 18136698717443725459456 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 601251 1048576 18136698717443725459456 18889465931478580854784 2061903923 2147483648 282628 282352 (ep1012 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1014 := nat_lit 1162778484084834635768216436558801054190858607013357568597262235683384878024225

noncomputable def ep1015 := nat_lit 3044843279478271637767797986162745792466951747330539277089724707483710574151201

noncomputable def ep1016 := BSN.sin_dyadic_bound_f 2061903923 2147483648 3 2 1048576 282628 ep1014 ep65 ep1010 ep1015 ep67 ep1010 859074 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2061903923) qz21 0 2 ep1014 ep65 ep1010 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2061903923) qz285 0 2 ep1015 ep67 ep1010 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1017 := @Enclosure.Real.IsNear.sin_image qz175 qz465 Bool.false 50774153 131072 453 524288 Bool.true 859074 1048576 1 141176 (@Enclosure.Real.IsNear.recentre' qz175 Bool.false 436146653401972095429 1125899906842624000 544156250307287211 630250000000000000000 50774153 131072 453 524288 (ep1008 rfl) rfl) (Enclosure.sfrac_false_div 50774153 131072) (BSN.sin_reduce2 qz465 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 18136698717443725459456) qz369) 226375608064910080 72057594037927936 Bool.false 859074 1048576 61 1000000000000000 282352 141176 (BSN.sin_reduce_arg_pos_rat_q2 50774153 131072 226375608064910080 72057594037927936 61 18136698717443725459456 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 859074 1048576 18136698717443725459456 18889465931478580854784 2061903923 2147483648 282628 282352 (ep1016 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1018 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz70 (Real.cos qz175)) (@HMul.hMul Real Real Real qz0 qz70 (@Neg.neg Real Real.instNeg (Real.sin qz175))) Bool.true 128691162789 1099511627776 3460775402557 19403081695363072 Bool.false 91937669943 549755813888 1732662602519 9701540847681536 (@Enclosure.Real.IsNear.mulLit_ft qz70 (Real.cos qz175) 214039 1048576 1 1048576 601251 1048576 8059627 9252110336 128691162789 1099511627776 3460775402557 19403081695363072 qz376 (@Enclosure.Real.IsNear.recentre' (Real.cos qz175) Bool.true 601251 1048576 64477016 74016882688 601251 1048576 8059627 9252110336 (ep1013 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz70 (@Neg.neg Real Real.instNeg (Real.sin qz175)) 214039 1048576 1 1048576 429537 524288 8059627 9252110336 91937669943 549755813888 1732662602519 9701540847681536 qz376 (@Enclosure.Real.IsNear.neg (Real.sin qz175) Bool.true 429537 524288 8059627 9252110336 (@Enclosure.Real.IsNear.recentre' (Real.sin qz175) Bool.true 859074 1048576 64477016 74016882688 429537 524288 8059627 9252110336 (ep1017 rfl rfl) rfl)) rfl)

noncomputable def ep1019 := @ep915 128691162789 1099511627776 3460775402557 19403081695363072 Bool.false 91937669943 549755813888 1732662602519 9701540847681536 Bool.false 1068653859273015440703488 485967511519 549755813888 31512510753477 4850770423840768 Bool.false 87962771197620303953920 160003348715 1099511627776 126088086645919 19403081695363072 (ep916 (BSN.head_sum_c_succ qz146 23 24 rfl rfl) (ep1006 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1007 ep1018) rfl rfl

theorem EMRow39.d14 : Enclosure.Complex.IsNear qz167 Bool.false 485967511519 549755813888 31512510753477 4850770423840768 Bool.false 160003348715 1099511627776 126088086645919 19403081695363072 := ep914 (BSN.head_sum_c_succ qz146 24 25 rfl rfl) (ep1019 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

theorem EMRow39.d15 : @Eq Nat (Nat.pow 31 1) 31 := @Eq.refl Nat 31

noncomputable def ep1020 := nat_lit 2654825777109682479417800884197751

noncomputable def ep1021 := nat_lit 3186128385459110241980400009216000

noncomputable def ep1022 := nat_lit 3920586641205525908745412931493746115281

noncomputable def ep1023 := nat_lit 496106648819160509857352807666807734272000

noncomputable abbrev qz599 := (@HAdd.hAdd Complex Complex Complex qz610 (@HAdd.hAdd Complex Complex Complex qz610 qz613 (@HMul.hMul Complex Complex Complex qz612 Complex.I (@HDiv.hDiv Complex Complex Complex qz614 (↑qz617) (2 : Complex)))) (@Nat.cast Complex Complex.instNatCast 2))

noncomputable abbrev qz466 := qz599

noncomputable abbrev qz176 := (Complex.Stirling.logGammaStirling 1 qz466)

noncomputable abbrev qz600 := (@HAdd.hAdd Complex Complex Complex qz610 qz613 (@HMul.hMul Complex Complex Complex qz612 Complex.I (@HDiv.hDiv Complex Complex Complex qz614 (↑qz617) (2 : Complex))))

noncomputable abbrev qz467 := qz600

noncomputable abbrev qz177 := qz467

noncomputable abbrev qz178 := (@HMul.hMul Real Real Real qz268 (@HDiv.hDiv Real Real Real qz271 qz441 (2 : Real)) (Real.log Real.pi))

noncomputable def ep1024 := Complex.re (@HMul.hMul Complex Complex Complex qz72 (Complex.exp (@HMul.hMul Complex Complex Complex qz72 Complex.I ↑(@HSub.hSub Real Real Real qz381 (Complex.im (@HSub.hSub Complex Complex Complex qz73 qz176 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz177 (@Nat.cast Complex Complex.instNatCast j))))) qz178))) (zetaApproximant qz146 1 31))

noncomputable def ep1025 := @Enclosure.Real.IsNear.of_eq ep1024 (@HSub.hSub Real Real Real qz381 (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz381 (Complex.im (@HSub.hSub Complex Complex Complex qz73 qz176 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz177 (@Nat.cast Complex Complex.instNatCast j))))) qz178)) (Complex.re (zetaApproximant qz146 1 31))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz381 (Complex.im (@HSub.hSub Complex Complex Complex qz73 qz176 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz177 (@Nat.cast Complex Complex.instNatCast j))))) qz178)) (Complex.im (zetaApproximant qz146 1 31))))

noncomputable def ep1026 := nat_lit 2283725717778567305145820646421

noncomputable def ep1027 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz381 (Complex.im (@HSub.hSub Complex Complex Complex qz73 qz176 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz177 (@Nat.cast Complex Complex.instNatCast j))))) qz178)) (Complex.re (zetaApproximant qz146 1 31))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz381 (Complex.im (@HSub.hSub Complex Complex Complex qz73 qz176 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz177 (@Nat.cast Complex Complex.instNatCast j))))) qz178)) (Complex.im (zetaApproximant qz146 1 31))) ep1026

noncomputable def ep1028 := nat_lit 2740755600394933541488516136960

noncomputable def ep1029 := nat_lit 5221229451918440978266781439936831205633

noncomputable def ep1030 := nat_lit 661475531758880679809803743555743645696000

noncomputable def ep1031 := nat_lit 10739615804025628431234533323

noncomputable def ep1032 := nat_lit 6372256770918220483960800018432000

noncomputable def ep1033 := nat_lit 746328362671228007252296246579633769

noncomputable def ep1034 := nat_lit 79377063811065681577176449226689237483520

noncomputable def ep1035 := nat_lit 14552457233372387631750302785935042722684255088946097254479953920

noncomputable def ep1036 := @Enclosure.Real.IsNear.mulLit_ff (Real.cos (@HSub.hSub Real Real Real qz381 (Complex.im (@HSub.hSub Complex Complex Complex qz73 qz176 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz177 (@Nat.cast Complex Complex.instNatCast j))))) qz178)) (Complex.re (zetaApproximant qz146 1 31)) 1048575 1048576 1673939

noncomputable def ep1037 := nat_lit 1687897795845208651253378157

noncomputable def ep1038 := nat_lit 2025685873323510641721344000

noncomputable def ep1039 := nat_lit 271288147454280104515680503489

noncomputable def ep1040 := nat_lit 35747278606539992294456557568000

noncomputable def ep1041 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HSub.hSub Real Real Real qz381 (Complex.im (@HSub.hSub Complex Complex Complex qz73 qz176 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz177 (@Nat.cast Complex Complex.instNatCast j))))) qz178)) Bool.false 1048575 1048576 13391512

noncomputable abbrev qz468 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 125179659) qz17)

noncomputable def ep1042 := @Enclosure.Real.IsNear.cos_image (@HSub.hSub Real Real Real qz381 (Complex.im (@HSub.hSub Complex Complex Complex qz73 qz176 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz177 (@Nat.cast Complex Complex.instNatCast j))))) qz178) qz468 Bool.false 125179659 1048576 93

noncomputable def ep1043 := nat_lit 9817330299986251754619977

noncomputable def ep1044 := nat_lit 27756331008000000000000000000

noncomputable def ep1045 := @Enclosure.Real.IsNear.recentre' (@HSub.hSub Real Real Real qz381 (Complex.im (@HSub.hSub Complex Complex Complex qz73 qz176 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz177 (@Nat.cast Complex Complex.instNatCast j))))) qz178) Bool.false 2150570172105945798071 18014398509481984000 ep1043 ep1044

noncomputable def ep1046 := nat_lit 3364298868986251754619977

noncomputable def ep1047 := @Enclosure.Real.IsNear.subLit_ff_p (Complex.im (@HSub.hSub Complex Complex Complex qz73 qz176 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz177 (@Nat.cast Complex Complex.instNatCast j))))) qz178 3407364836931142964663 18014398509481984000 ep1046 ep1044 9144384711 131072000

noncomputable def ep1048 := nat_lit 281879533598270527644762112000

noncomputable def ep1049 := @Enclosure.Complex.IsNear.im_isNear (@HSub.hSub Complex Complex Complex qz73 qz176 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz177 (@Nat.cast Complex Complex.instNatCast j)))) Bool.true 431632106310731036621 4503599627370496000 521243363072078444683461 ep432 Bool.false 3407364836931142964663 18014398509481984000

noncomputable def ep1050 := nat_lit 330432512000000000000000000

noncomputable def ep1051 := @Enclosure.Complex.IsNear.subLitP qz176 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz177 (@Nat.cast Complex Complex.instNatCast j))) Bool.true 394611715254109823621 4503599627370496000 73293051863805020179923 ep1050 Bool.false 3463515429602946548663 18014398509481984000 452527266994070774801711

noncomputable def ep1052 := nat_lit 3965190144000000000000000000

noncomputable def ep1053 := nat_lit 1943898193142150611483359546510934016

noncomputable def ep1054 := nat_lit 959087938119901645185225107783548928

noncomputable abbrev qz469 := (@HSub.hSub Complex Complex Complex qz572 qz599 qz575)

noncomputable abbrev qz470 := (Complex.log qz599)

noncomputable abbrev qz179 := (@HSub.hSub Complex Complex Complex qz378 (@HMul.hMul Complex Complex Complex qz377 qz469 qz470) qz466)

noncomputable abbrev qz180 := qz466

noncomputable def ep1055 := @Enclosure.Complex.IsNear.of_eq qz176 (@HAdd.hAdd Complex Complex Complex qz4 (@HAdd.hAdd Complex Complex Complex qz4 qz179 qz78) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz72 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz81 qz180 (@HSub.hSub Int Int Int qz388 qz83 (@HMul.hMul Int Int Int qz389 qz84 (@Nat.cast Int instNatCastInt k)))))) Bool.true 394611715254109823621

noncomputable def ep1056 := @Enclosure.Complex.IsNear.addLitP (@HAdd.hAdd Complex Complex Complex qz4 qz179 qz78) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz72 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz81 qz180 (@HSub.hSub Int Int Int qz388 qz83 (@HMul.hMul Int Int Int qz389 qz84 (@Nat.cast Int instNatCastInt k))))) Bool.true 394611942285624959621 4503599627370496000

noncomputable def ep1057 := nat_lit 13558755293078928176356186390528

noncomputable def ep1058 := nat_lit 476021935978753462135797040807936

noncomputable def ep1059 := @ep1056 1118362777912133793 5042000000000000000000 Bool.false 27708320223301164867 144115188075855872 1150812503388982821 10084000000000000000000 Bool.false 1732113 34359738368 3 34359738368 Bool.true 23458776187 17179869184000 121891 51539607552000 Bool.true ep1057 394611715254109823621 4503599627370496000 73293051863805020179923 ep1050 Bool.false ep1058

noncomputable def ep1060 := @Enclosure.Complex.IsNear.addLitP qz179 qz78 Bool.true 398750469692835455621 4503599627370496000 2207875000404345711 10084000000000000000000

noncomputable def ep1061 := nat_lit 51722576499261434707443712

noncomputable def ep1062 := @ep1060 Bool.false 27708320223301164867 144115188075855872 1150812503388982821 10084000000000000000000 Bool.false 120447 131072 3 1048576 Bool.false 0 1 0 1 Bool.true ep1061 394611942285624959621 4503599627370496000 1118362777912133793 5042000000000000000000 Bool.false 27708320223301164867 27708320223301164867 144115188075855872

noncomputable abbrev qz181 := (@HMul.hMul Complex Complex Complex qz377 qz469 qz470)

noncomputable def ep1063 := @Enclosure.Complex.IsNear.subLitP qz181 qz180 Bool.true 388617370531251839621 4503599627370496000 2207875000404345711 10084000000000000000000 Bool.false 4561436552272279864247

noncomputable def ep1064 := nat_lit 1595001878771341822484000

noncomputable def ep1065 := nat_lit 13854160111650582433500000

noncomputable def ep1066 := @ep1063 18014398509481984000 1150812503388982821 10084000000000000000000 Bool.false 9000 4000 0 1 Bool.false 243782 4000 0 1 Bool.true ep1064 398750469692835455621 4503599627370496000 2207875000404345711 10084000000000000000000 Bool.false ep1065 27708320223301164867 144115188075855872 1150812503388982821 10084000000000000000000

noncomputable abbrev qz182 := qz469

noncomputable abbrev qz183 := qz470

noncomputable def ep1067 := @Enclosure.Complex.IsNear.mul qz182 qz183 Bool.true 388617370531251839621 4503599627370496000 2207875000404345711 10084000000000000000000 Bool.false 4561436552272279864247 18014398509481984000 1150812503388982821

noncomputable abbrev qz184 := (Complex.re qz469)

noncomputable abbrev qz185 := (Complex.re qz470)

noncomputable abbrev qz186 := (Complex.im qz469)

noncomputable abbrev qz187 := (Complex.im qz470)

noncomputable def ep1068 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 qz184 qz185) (@HMul.hMul Real Real Real qz0 qz186 qz187) 259178785056863819 36028797018963968 62500000194117 20168000000000000000 105253679665839954249 1125899906842624000

noncomputable def ep1069 := nat_lit 3500354090228495516145092205878444032

noncomputable def ep1070 := @Enclosure.Real.IsNear.mulLit_ff qz184 qz185 7000 4000 0 1 37025540722409117 9007199254740992 62500000194117 35294000000000000000

noncomputable def ep1071 := @Enclosure.Complex.IsNear.re_isNear qz182 Bool.false 7000 4000 0 1 Bool.false 243782 4000 0 1

noncomputable abbrev qz601 := (Enclosure.sfrac Bool.false 243782 4000)

noncomputable abbrev qz471 := qz601

noncomputable def ep1072 := @Enclosure.Complex.IsNear.of_eq qz182 (Complex.mk (Enclosure.sfrac Bool.false 7000 4000) qz471) Bool.false 7000 4000 0 1 Bool.false 243782 4000 0

noncomputable abbrev qz472 := (Complex.log (Complex.mk qz579 qz601))

noncomputable def ep1073 := @Enclosure.Complex.IsNear.of_eq qz183 qz472 Bool.false 37025540722409117 9007199254740992 62500000194117 35294000000000000000 Bool.false 863506572805539 562949953421312 125000000017647 35294000000000000000

noncomputable def ep1074 := nat_lit 465411867947754566899734167764530467622907982418247077224455617146862423908222157333174646528787741466947899883520

noncomputable def ep1075 := nat_lit 13728062400644194431579034004711108030715361212633355742392379291367838993437750938465934401449077099144233877504

noncomputable def ep1076 := nat_lit 176798432106634289558297419188003627708024191550252447653011092703230849385212735202450502313551045009080320

noncomputable def ep1077 := BSN.log_dyadic_bound 26742663524 92278663524 6 5 ep1074 1048576 282352 ep1075 ep1076 625688 119021327048 65536000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 26742663524) (BSN.artanhQ 92278663524) 0 5 ep1075 ep1074 ep1076 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz602 := (Real.log (Enclosure.sfrac Bool.false 59510663524 16000000))

noncomputable def ep1078 := @Enclosure.Real.IsNear.mulLit_ff qz92 qz602 1 2 0 1 37025540722409117 4503599627370496 62500000194117 17647000000000000000 37025540722409117 9007199254740992 62500000194117 35294000000000000000 qz392 (BSN.isNear_log_sfrac 59510663524 16000000 37025540722409117 4503599627370496 62500000194117 17647000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 59510663524) qz393)) Bool.false 310592747108326898139136 37778931862957161709568 1000000003105872 282352000000000000000 37025540722409117 4503599627370496 62500000194117 17647000000000000000 (BSN.log_rat_reduce_isNear 59510663524 16000000 11 119021327048 65536000000 625688 1048576 24973259072661432 36028797018963968 282352 1000000000000000 rfl rfl rfl rfl (ep1077 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1079 := BSN.arctan_dyadic_bound_f 9000 243782 1 0 1048576 282352 0 1 1 0 1 1 38693 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 9000) (BSN.arctanEvenQ 243782) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 9000) (BSN.arctanOddQ 243782) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz473 := (Real.arctan (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 9000) (@Nat.cast Real Real.instNatCast 243782)))

noncomputable def ep1080 := @Enclosure.Real.IsNear.subLit_ff_p qz93 qz473 884279719003555 562949953421312 1 2000000000000000 38693 1048576 1 282352 905452268086140862464 863506572805539 562949953421312 125000000017647 35294000000000000000 qz94 (ep1079 rfl) rfl rfl

noncomputable abbrev qz474 := (Complex.mk qz579 qz601)

noncomputable abbrev qz475 := (Real.arctan (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 243782) (@Nat.cast Real Real.instNatCast 9000)))

noncomputable def ep1081 := @Enclosure.Complex.IsNear.re_isNear qz183 Bool.false 37025540722409117 9007199254740992 62500000194117 35294000000000000000 Bool.false 863506572805539 562949953421312 125000000017647 35294000000000000000 (ep1073 (@congrArg Complex Complex qz180 qz474 Complex.log (BSN.w_shift_mk qz149 Bool.false 121891 1000 2 qz150 rfl)) (@Enclosure.Complex.IsNear.of_parts qz472 Bool.false 37025540722409117 9007199254740992 62500000194117 35294000000000000000 Bool.false 863506572805539 562949953421312 125000000017647 35294000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz472) (@HMul.hMul Real Real Real qz0 qz92 qz602) Bool.false 37025540722409117 9007199254740992 62500000194117 35294000000000000000 (Enclosure.clog_re_eq 9000 243782 4000 59510663524 16000000 rfl rfl rfl) (ep1078 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz472) qz475 Bool.false 863506572805539 562949953421312 125000000017647 35294000000000000000 (Enclosure.clog_im_eq 9000 243782 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz475 (@HSub.hSub Real Real Real qz381 qz93 qz473) Bool.false 863506572805539 562949953421312 125000000017647 35294000000000000000 (BSN.arctan_recip 243782 9000 rfl rfl) ep1080))))

noncomputable def ep1082 := @Enclosure.Real.IsNear.mulLit_ff qz186 qz187 243782 4000 0 1 863506572805539 562949953421312 125000000017647 35294000000000000000

noncomputable def ep1083 := @Enclosure.Complex.IsNear.im_isNear qz182 Bool.false 7000 4000 0 1 Bool.false 243782 4000 0 1

noncomputable def ep1084 := @Enclosure.Complex.IsNear.im_isNear qz183 Bool.false 37025540722409117 9007199254740992 62500000194117 35294000000000000000 Bool.false 863506572805539 562949953421312 125000000017647 35294000000000000000 (ep1073 (@congrArg Complex Complex qz180 qz474 Complex.log (BSN.w_shift_mk qz149 Bool.false 121891 1000 2 qz150 rfl)) (@Enclosure.Complex.IsNear.of_parts qz472 Bool.false 37025540722409117 9007199254740992 62500000194117 35294000000000000000 Bool.false 863506572805539 562949953421312 125000000017647 35294000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz472) (@HMul.hMul Real Real Real qz0 qz92 qz602) Bool.false 37025540722409117 9007199254740992 62500000194117 35294000000000000000 (Enclosure.clog_re_eq 9000 243782 4000 59510663524 16000000 rfl rfl rfl) (ep1078 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz472) qz475 Bool.false 863506572805539 562949953421312 125000000017647 35294000000000000000 (Enclosure.clog_im_eq 9000 243782 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz475 (@HSub.hSub Real Real Real qz381 qz93 qz473) Bool.false 863506572805539 562949953421312 125000000017647 35294000000000000000 (BSN.arctan_recip 243782 9000 rfl rfl) ep1080))))

noncomputable abbrev qz188 := (@ep1072 1 (BSN.w_sub_half_mk qz441 Bool.false 121891 1000 2 qz442 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7000 4000) qz471 Bool.false 7000 4000 0 1 Bool.false 243782 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 7000 4000) (Enclosure.Real.IsNear.const Bool.false 243782 4000)))

noncomputable def ep1085 := @ep1068 2176625000307287211 10084000000000000000000 ep1069 388617370531251839621 4503599627370496000 2207875000404345711 10084000000000000000000 (@ep1070 259178785056863819 36028797018963968 62500000194117 20168000000000000000 (ep1071 qz188) ep1081 rfl) (@ep1082 105253679665839954249 1125899906842624000 2176625000307287211 10084000000000000000000 (ep1083 qz188) ep1084 rfl) rfl

noncomputable def ep1086 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz184 qz187) (@HMul.hMul Real Real Real qz0 qz186 qz185) 6044546009638773 2251799813685248 125000000017647 20168000000000000000 4513080184195169680247 18014398509481984000

noncomputable def ep1087 := nat_lit 10271441978543799797966535218226528256

noncomputable def ep1088 := @Enclosure.Real.IsNear.mulLit_ff qz184 qz187 7000 4000 0 1 863506572805539 562949953421312 125000000017647 35294000000000000000

noncomputable def ep1089 := @Enclosure.Real.IsNear.mulLit_ff qz186 qz185 243782 4000 0 1 37025540722409117 9007199254740992 62500000194117 35294000000000000000

noncomputable def ep1090 := @ep1086 1088312503380159321 10084000000000000000000 ep1087 4561436552272279864247 18014398509481984000 1150812503388982821 10084000000000000000000 (@ep1088 6044546009638773 2251799813685248 125000000017647 20168000000000000000 (ep1071 qz188) ep1084 rfl) (@ep1089 4513080184195169680247 18014398509481984000 1088312503380159321 10084000000000000000000 (ep1083 qz188) ep1081 rfl) rfl

noncomputable def ep1091 := @Enclosure.Complex.IsNear.of_eq qz180 qz474 Bool.false 9000 4000 0 1 Bool.false 243782 4000 0 1 (BSN.w_shift_mk qz149 Bool.false 121891 1000 2 qz150 rfl)

noncomputable abbrev qz476 := (ep1091 (@Enclosure.Complex.IsNear.mk qz579 qz601 Bool.false 9000 4000 0 1 Bool.false 243782 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 9000 4000) (Enclosure.Real.IsNear.const Bool.false 243782 4000)))

noncomputable abbrev qz189 := qz476

noncomputable def ep1092 := ep1066 (@ep1067 10084000000000000000000 (ep1085 rfl) (ep1090 rfl)) qz189 rfl rfl rfl rfl rfl rfl

noncomputable def ep1093 := @ep1062 1150812503388982821 10084000000000000000000 (ep1092 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@Enclosure.Complex.IsNear.mul qz97 (↑qz2) Bool.false 120447 131072 3 1048576 Bool.false 0 1 0 1 (@ep475 131072 3 1048576 (ep477 rfl) (ep479 rfl) rfl rfl) (@ep480 1 0 1 (ep482 rfl) (ep484 rfl) rfl rfl))

noncomputable abbrev qz477 := (@HPow.hPow Complex Int Complex qz577 qz599 (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) (@OfNat.ofNat Int 1 (@instOfNat 1)) (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (@OfNat.ofNat Int 2 (@instOfNat 2)) (@Nat.cast Int instNatCastInt 1))))

noncomputable abbrev qz190 := qz477

noncomputable def ep1094 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz72 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz81 qz180 (@HSub.hSub Int Int Int qz388 qz83 (@HMul.hMul Int Int Int qz389 qz84 (@Nat.cast Int instNatCastInt k))))) (@HAdd.hAdd Complex Complex Complex qz4 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz72 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz81 qz180 (@HSub.hSub Int Int Int qz388 qz83 (@HMul.hMul Int Int Int qz389 qz84 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 (@Rat.cast Complex Complex.instRatCast (bernoulli qz99)) qz100) qz190)) Bool.false 1732113 34359738368 3 34359738368

noncomputable def ep1095 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz72 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz81 qz180 (@HSub.hSub Int Int Int qz388 qz83 (@HMul.hMul Int Int Int qz389 qz84 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 (@Rat.cast Complex Complex.instRatCast (bernoulli qz99)) qz100) qz190) Bool.false 0 1 0 1 Bool.false

noncomputable def ep1096 := @ep1095 0 1 0 1 Bool.false 1732113 34359738368 3 34359738368 Bool.true 23458776187 17179869184000 121891 51539607552000 Bool.false 1732113 1732113 34359738368 3 34359738368 Bool.true 23458776187 23458776187 17179869184000 121891

noncomputable def ep1097 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz72 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz81 qz180 (@HSub.hSub Int Int Int qz388 qz83 (@HMul.hMul Int Int Int qz389 qz84 (@Nat.cast Int instNatCastInt k))))) (Complex.mk qz10 qz10) Bool.false 0 1 0 1 Bool.false

noncomputable def ep1098 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz79 (@Rat.cast Complex Complex.instRatCast (bernoulli qz99)) qz100) qz190 Bool.false 1732113 34359738368 3 34359738368 Bool.true 23458776187 17179869184000 121891 51539607552000

noncomputable abbrev qz191 := (Complex.re qz477)

noncomputable abbrev qz192 := (Complex.im qz477)

noncomputable def ep1099 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz79 (@Rat.cast Complex Complex.instRatCast (bernoulli qz99)) qz100)) qz191) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz79 (@Rat.cast Complex Complex.instRatCast (bernoulli qz99)) qz100)) qz192) 1732113 34359738368 3 34359738368 0 1 0

noncomputable def ep1100 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz79 (@Rat.cast Complex Complex.instRatCast (bernoulli qz99)) qz100)) qz191 1 12 0 1 5196339 8589934592 9 8589934592 1732113

noncomputable def ep1101 := @Enclosure.Complex.IsNear.re_isNear qz190 Bool.false 5196339 8589934592 9 8589934592 Bool.true 70376328561 4294967296000 121891 4294967296000

noncomputable abbrev qz478 := (@HPow.hPow Complex Nat Complex qz581 qz599 1)

noncomputable abbrev qz193 := (@Inv.inv Complex Complex.instInv qz478)

noncomputable def ep1102 := @Enclosure.Complex.IsNear.of_eq qz190 qz193 Bool.false 5196339 8589934592 9 8589934592 Bool.true 70376328561 4294967296000 121891

noncomputable def ep1103 := @Enclosure.Complex.IsNear.of_parts qz193 Bool.false 5196339 8589934592 9 8589934592 Bool.true 70376328561 4294967296000 121891

noncomputable abbrev qz194 := (Complex.re qz478)

noncomputable abbrev qz195 := qz478

noncomputable def ep1104 := @Enclosure.Real.IsNear.mulLit_ff qz194 (@Inv.inv Real Real.instInv (@DFunLike.coe qz106 Complex (fun (x : Complex) => Real) qz107 Complex.normSq qz195)) 9000 4000 0 1 577371 2147483648 1 2147483648

noncomputable def ep1105 := @Enclosure.Complex.IsNear.re_isNear qz195 Bool.false 9000 4000 0 1 Bool.false 243782 4000 0 1

noncomputable def ep1106 := @Enclosure.Complex.IsNear.of_eq qz195 qz180 Bool.false 9000 4000 0 1 Bool.false 243782 4000 0

noncomputable def ep1107 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (@DFunLike.coe qz106 Complex (fun (x : Complex) => Real) qz107 Complex.normSq qz195)) Bool.false 577371 2147483648 1 2147483648 577371 2147483648 1

noncomputable abbrev qz196 := (Complex.im qz478)

noncomputable def ep1108 := @Enclosure.Real.IsNear.of_eq (@DFunLike.coe qz106 Complex (fun (x : Complex) => Real) qz107 Complex.normSq qz195) (@HAdd.hAdd Real Real Real qz402 (@HMul.hMul Real Real Real qz0 qz194 qz194) (@HMul.hMul Real Real Real qz0 qz196 qz196)) Bool.false 14877665881 4000000 0 1

noncomputable def ep1109 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz194 qz194) (@HMul.hMul Real Real Real qz0 qz196 qz196) 81 16 0 1 14857415881 4000000

noncomputable def ep1110 := @Enclosure.Real.IsNear.mulLit_ff qz194 qz194 9000 4000 0 1 9000 4000 0 1

noncomputable def ep1111 := @Enclosure.Real.IsNear.mulLit_ff qz196 qz196 243782 4000 0 1 243782 4000 0 1

noncomputable def ep1112 := @Enclosure.Complex.IsNear.im_isNear qz195 Bool.false 9000 4000 0 1 Bool.false 243782 4000 0 1

noncomputable abbrev qz197 := (ep1105 (@ep1106 1 (BSN.pow_one_c qz466) qz476))

noncomputable abbrev qz198 := (ep1112 (@ep1106 1 (BSN.pow_one_c qz466) qz476))

noncomputable def ep1113 := @ep1109 0 1 238042654096 14877665881 4000000 0 1 (@ep1110 81 16 0 1 qz197 qz197 rfl) (@ep1111 14857415881 4000000 0 1 qz198 qz198 rfl)

noncomputable def ep1114 := @Enclosure.Real.IsNear.inv_image (@DFunLike.coe qz106 Complex (fun (x : Complex) => Real) qz107 Complex.normSq qz195) 14877665881 4000000 0 1 288685 288686 1073741824 (ep1108 (Enclosure.Complex.normSq_eq_mul_add_mul qz195) (ep1113 rfl rfl)) rfl

noncomputable def ep1115 := @Enclosure.Real.IsNear.of_eq (Complex.re qz193) (@HMul.hMul Real Real Real qz0 qz194 (@Inv.inv Real Real.instInv (@DFunLike.coe qz106 Complex (fun (x : Complex) => Real) qz107 Complex.normSq qz195))) Bool.false 5196339 8589934592 9 8589934592 (Enclosure.Complex.inv_re_eq_mul qz195) (@ep1104 5196339 8589934592 9 8589934592 qz197 (@ep1107 2147483648 (ep1114 rfl rfl rfl rfl rfl) rfl) rfl)

noncomputable def ep1116 := @Enclosure.Real.IsNear.of_eq (Complex.im qz193) (@HMul.hMul Real Real Real qz0 (@Neg.neg Real Real.instNeg qz196) (@Inv.inv Real Real.instInv (@DFunLike.coe qz106 Complex (fun (x : Complex) => Real) qz107 Complex.normSq qz195))) Bool.true 70376328561 4294967296000 121891 4294967296000 (Enclosure.Complex.inv_im_eq_mul qz195)

noncomputable def ep1117 := @Enclosure.Real.IsNear.mulLit_tf (@Neg.neg Real Real.instNeg qz196) (@Inv.inv Real Real.instInv (@DFunLike.coe qz106 Complex (fun (x : Complex) => Real) qz107 Complex.normSq qz195)) 243782 4000 0 1 577371 2147483648 1

noncomputable def ep1118 := @ep1117 2147483648 70376328561 4294967296000 121891 4294967296000 (@Enclosure.Real.IsNear.neg qz196 Bool.false 243782 4000 0 1 qz198) (@ep1107 2147483648 (ep1114 rfl rfl rfl rfl rfl) rfl) rfl

noncomputable def ep1119 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz79 (@Rat.cast Complex Complex.instRatCast (bernoulli qz99)) qz100)) qz192 0 1 0 1 70376328561 4294967296000 121891 4294967296000 0

noncomputable def ep1120 := @Enclosure.Complex.IsNear.im_isNear qz190 Bool.false 5196339 8589934592 9 8589934592 Bool.true 70376328561 4294967296000 121891 4294967296000

noncomputable abbrev qz199 := (@ep1102 4294967296000 (BSN.zpow_one_sub_two_mul qz466 1 1 rfl rfl) (@ep1103 4294967296000 ep1115 (ep1116 ep1118)))

noncomputable def ep1121 := @ep1099 1 1732113 1732113 34359738368 3 34359738368 (@ep1100 34359738368 3 34359738368 ep494 (ep1101 qz199) rfl) (@ep1119 1 0 1 ep514 (ep1120 qz199) rfl) rfl

noncomputable def ep1122 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz79 (@Rat.cast Complex Complex.instRatCast (bernoulli qz99)) qz100)) qz192) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz79 (@Rat.cast Complex Complex.instRatCast (bernoulli qz99)) qz100)) qz191) 23458776187 17179869184000 121891 51539607552000 0 1 0

noncomputable def ep1123 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HDiv.hDiv Complex Complex Complex qz79 (@Rat.cast Complex Complex.instRatCast (bernoulli qz99)) qz100)) qz192 1 12 0 1 70376328561 4294967296000 121891 4294967296000 23458776187

noncomputable def ep1124 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz79 (@Rat.cast Complex Complex.instRatCast (bernoulli qz99)) qz100)) qz191 0 1 0 1 5196339 8589934592 9 8589934592 0

noncomputable def ep1125 := @ep1122 1 23458776187 23458776187 17179869184000 121891 51539607552000 (@ep1123 17179869184000 121891 51539607552000 ep494 (ep1120 qz199) rfl) (@ep1124 1 0 1 ep514 (ep1101 qz199) rfl) rfl

noncomputable def ep1126 := @ep1096 51539607552000 (@ep1097 0 1 0 1 (BSN.stirling_sum_base qz180) qz113) (ep1098 (ep1121 rfl) (ep1125 rfl)) rfl rfl rfl rfl rfl

noncomputable def ep1127 := @ep1059 3463515429602946548663 18014398509481984000 452527266994070774801711 ep1052 (ep1093 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep1094 Bool.true 23458776187 17179869184000 121891 51539607552000 (BSN.stirling_sum_succ qz180 0 1 rfl) (ep1126 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl

noncomputable def ep1128 := @Enclosure.Complex.IsNear.of_eq (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz177 (@Nat.cast Complex Complex.instNatCast j))) (BSN.logSumC qz149 2) Bool.false 37020391056621213 4503599627370496 62500000194117 17647000000000000000 Bool.false 877353010496931 281474976710656

noncomputable abbrev qz200 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz273 qz467 qz398))

noncomputable def ep1129 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz149 2) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.logSumC qz149 1) qz200) Bool.false 37020391056621213 4503599627370496 62500000194117 17647000000000000000 Bool.false 877353010496931 281474976710656 125000000017647 17647000000000000000

noncomputable def ep1130 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz149 1) qz200 Bool.false 37019480523554461 9007199254740992 62500000194117 35294000000000000000 Bool.false 881970637211043 562949953421312 125000000017647 35294000000000000000 Bool.false

noncomputable def ep1131 := nat_lit 666900077470837350208005935726592

noncomputable def ep1132 := nat_lit 987811672786590329305451986944

noncomputable abbrev qz201 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz273 qz467 (@Nat.cast Complex Complex.instNatCast 0)))

noncomputable def ep1133 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz149 1) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.logSumC qz149 0) qz201) Bool.false 37019480523554461 9007199254740992 62500000194117 35294000000000000000 Bool.false 881970637211043 562949953421312 125000000017647 35294000000000000000

noncomputable def ep1134 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz149 0) qz201 Bool.false 0 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable abbrev qz479 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz601))

noncomputable def ep1135 := @Enclosure.Complex.IsNear.of_eq qz201 qz479 Bool.false 37019480523554461 9007199254740992 62500000194117 35294000000000000000 Bool.false 881970637211043 562949953421312 125000000017647 35294000000000000000

noncomputable def ep1136 := nat_lit 461392734040458355133747531962461570213188925568658760772192859758875253351424471275389824334904442020163899883520

noncomputable def ep1137 := nat_lit 13548576979567389425210095184143802918913400364898782009818739141581948946904467292104430576940164906427433877504

noncomputable def ep1138 := nat_lit 171580183815096838409762786655001594989583689877705293700221015247130697059093147184005944521237701009080320

noncomputable def ep1139 := BSN.log_dyadic_bound 26662663524 92198663524 6 5 ep1136 1048576 282352 ep1137 ep1138 624277 118861327048 65536000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 26662663524) (BSN.artanhQ 92198663524) 0 5 ep1137 ep1136 ep1138 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep1140 := @Enclosure.Real.IsNear.mulLit_ff qz92 (Real.log (Enclosure.sfrac Bool.false 59430663524 16000000)) 1 2 0 1 37019480523554461 4503599627370496 62500000194117 17647000000000000000 37019480523554461 9007199254740992 62500000194117 35294000000000000000 qz392 (BSN.isNear_log_sfrac 59430663524 16000000 37019480523554461 4503599627370496 62500000194117 17647000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 59430663524) qz393)) Bool.false 310541910475733139980288 37778931862957161709568 1000000003105872 282352000000000000000 37019480523554461 4503599627370496 62500000194117 17647000000000000000 (BSN.log_rat_reduce_isNear 59430663524 16000000 11 118861327048 65536000000 624277 1048576 24973259072661432 36028797018963968 282352 1000000000000000 rfl rfl rfl rfl (ep1139 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1141 := BSN.arctan_dyadic_bound_f 1000 243782 1 0 1048576 282352 0 1 1 0 1 1 4301 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 243782) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 243782) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz480 := (@Nat.cast Real Real.instNatCast 243782)

noncomputable def ep1142 := @Enclosure.Real.IsNear.subLit_ff_p qz93 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz404 qz480)) 884279719003555 562949953421312 1 2000000000000000 4301 1048576 1 282352 924813242884206624768 881970637211043 562949953421312 125000000017647 35294000000000000000 qz94 (ep1141 rfl) rfl rfl

noncomputable abbrev qz202 := (@HAdd.hAdd Complex Complex Complex qz273 qz467 (@Nat.cast Complex Complex.instNatCast 0))

noncomputable abbrev qz481 := (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz601)

noncomputable def ep1143 := @ep1134 37019480523554461 9007199254740992 62500000194117 35294000000000000000 Bool.false 881970637211043 562949953421312 125000000017647 35294000000000000000 Bool.false 37019480523554461 37019480523554461 9007199254740992 62500000194117 35294000000000000000 Bool.false 881970637211043 881970637211043 562949953421312 125000000017647 35294000000000000000 (@Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz149 0) (Complex.mk qz10 qz10) Bool.false 0 1 0 1 Bool.false 0 1 0 1 (BSN.log_sum_c_base qz149) qz113) (ep1135 (@congrArg Complex Complex qz202 qz481 Complex.log (BSN.w_shift_mk qz149 Bool.false 121891 1000 0 qz150 rfl)) (@Enclosure.Complex.IsNear.of_parts qz479 Bool.false 37019480523554461 9007199254740992 62500000194117 35294000000000000000 Bool.false 881970637211043 562949953421312 125000000017647 35294000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz479) (@HMul.hMul Real Real Real qz0 qz92 (Real.log (Enclosure.sfrac Bool.false 59430663524 16000000))) Bool.false 37019480523554461 9007199254740992 62500000194117 35294000000000000000 (Enclosure.clog_re_eq 1000 243782 4000 59430663524 16000000 rfl rfl rfl) (ep1140 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz479) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz480 qz404)) Bool.false 881970637211043 562949953421312 125000000017647 35294000000000000000 (Enclosure.clog_im_eq 1000 243782 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz480 qz404)) (@HSub.hSub Real Real Real qz381 qz93 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz404 qz480))) Bool.false 881970637211043 562949953421312 125000000017647 35294000000000000000 (BSN.arctan_recip 243782 1000 rfl rfl) ep1142)))) rfl rfl

noncomputable abbrev qz482 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz601))

noncomputable def ep1144 := @Enclosure.Complex.IsNear.of_eq qz200 qz482 Bool.false 37021301589687965 9007199254740992 62500000194117 35294000000000000000 Bool.false 872735383782819 562949953421312 125000000017647 35294000000000000000

noncomputable def ep1145 := nat_lit 462595181606423832493278488718822211157060143804583396299768811813661822155126586919598802596842462254199099883520

noncomputable def ep1146 := nat_lit 13602208810877889828875886856738576001277338977723253723190472474241851688796660551967670902195860644242473877504

noncomputable def ep1147 := nat_lit 173130908335575075277807226674741302636210795504829414461324505862434162137404085085906491225331704209080320

noncomputable def ep1148 := BSN.log_dyadic_bound 26686663524 92222663524 6 5 ep1145 1048576 282352 ep1146 ep1147 624701 118909327048 65536000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 26686663524) (BSN.artanhQ 92222663524) 0 5 ep1146 ep1145 ep1147 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep1149 := @Enclosure.Real.IsNear.mulLit_ff qz92 (Real.log (Enclosure.sfrac Bool.false 59454663524 16000000)) 1 2 0 1 37021301589687965 4503599627370496 62500000194117 17647000000000000000 37021301589687965 9007199254740992 62500000194117 35294000000000000000 qz392 (BSN.isNear_log_sfrac 59454663524 16000000 37021301589687965 4503599627370496 62500000194117 17647000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 59454663524) qz393)) Bool.false 310557186685669180702720 37778931862957161709568 1000000003105872 282352000000000000000 37021301589687965 4503599627370496 62500000194117 17647000000000000000 (BSN.log_rat_reduce_isNear 59454663524 16000000 11 118909327048 65536000000 624701 1048576 24973259072661432 36028797018963968 282352 1000000000000000 rfl rfl rfl rfl (ep1148 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1150 := BSN.arctan_dyadic_bound_f 5000 243782 1 0 1048576 282352 0 1 1 0 1 1 21503 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 5000) (BSN.arctanEvenQ 243782) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 5000) (BSN.arctanOddQ 243782) 0 0 rfl) rfl rfl rfl

noncomputable def ep1151 := @Enclosure.Real.IsNear.subLit_ff_p qz93 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz408 qz480)) 884279719003555 562949953421312 1 2000000000000000 21503 1048576 1 282352 915129377785453215744 872735383782819 562949953421312 125000000017647 35294000000000000000 qz94 (ep1150 rfl) rfl rfl

noncomputable abbrev qz203 := (@HAdd.hAdd Complex Complex Complex qz273 qz467 qz398)

noncomputable abbrev qz483 := (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz601)

noncomputable def ep1152 := @ep1130 37021301589687965 9007199254740992 62500000194117 35294000000000000000 Bool.false 872735383782819 562949953421312 125000000017647 35294000000000000000 Bool.false ep1131 37020391056621213 4503599627370496 62500000194117 17647000000000000000 Bool.false ep1132 877353010496931 281474976710656 125000000017647 17647000000000000000 (ep1133 (BSN.log_sum_c_succ qz149 0 1 rfl) (ep1143 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1144 (@congrArg Complex Complex qz203 qz483 Complex.log (BSN.w_shift_mk qz149 Bool.false 121891 1000 1 qz150 rfl)) (@Enclosure.Complex.IsNear.of_parts qz482 Bool.false 37021301589687965 9007199254740992 62500000194117 35294000000000000000 Bool.false 872735383782819 562949953421312 125000000017647 35294000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz482) (@HMul.hMul Real Real Real qz0 qz92 (Real.log (Enclosure.sfrac Bool.false 59454663524 16000000))) Bool.false 37021301589687965 9007199254740992 62500000194117 35294000000000000000 (Enclosure.clog_re_eq 5000 243782 4000 59454663524 16000000 rfl rfl rfl) (ep1149 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz482) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz480 qz408)) Bool.false 872735383782819 562949953421312 125000000017647 35294000000000000000 (Enclosure.clog_im_eq 5000 243782 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz480 qz408)) (@HSub.hSub Real Real Real qz381 qz93 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz408 qz480))) Bool.false 872735383782819 562949953421312 125000000017647 35294000000000000000 (BSN.arctan_recip 243782 5000 rfl rfl) ep1151)))) rfl rfl

noncomputable def ep1153 := @ep1051 ep1052 Bool.false 37020391056621213 4503599627370496 62500000194117 17647000000000000000 Bool.false 877353010496931 281474976710656 125000000017647 17647000000000000000 Bool.true ep1053 431632106310731036621 4503599627370496000 521243363072078444683461 ep432 Bool.false ep1054 3407364836931142964663 18014398509481984000 ep1046 ep1044 (@ep1055 4503599627370496000 73293051863805020179923 ep1050 Bool.false 3463515429602946548663 18014398509481984000 452527266994070774801711 ep1052 (BSN.logGammaStirling_unfold 1 qz180) (ep1127 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (@ep1128 125000000017647 17647000000000000000 (BSN.log_sum_c_eq qz149 2) (ep1129 (BSN.log_sum_c_succ qz149 1 2 rfl) (ep1152 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)))

noncomputable abbrev qz204 := (@HDiv.hDiv Real Real Real qz271 qz441 (2 : Real))

noncomputable def ep1154 := @Enclosure.Real.IsNear.mulLit_ff qz204 (Real.log Real.pi) 121891 2000 0 1 75021 65536 1 262144 9144384711 131072000 121891 524288000 (@Enclosure.Real.IsNear.of_eq qz204 (Enclosure.sfrac Bool.false 121891 2000) Bool.false 121891 2000 0 1 (BSN.t_half_eq qz149 Bool.false 121891 1000 qz150) (Enclosure.Real.IsNear.const Bool.false 121891 2000)) EMRow39.d5 rfl

noncomputable def ep1155 := @ep1047 121891 524288000 ep1048 2150570172105945798071 18014398509481984000 ep1043 ep1044 (@ep1049 ep1046 ep1044 (ep1153 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) ep1154 rfl rfl

noncomputable def ep1156 := BSN.cos_dyadic_bound_f 225246 2147483648 1 0 1048576 282628 0 1 1 0 1 1 1048575 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 225246) qz16 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 225246) qz282 0 0 rfl) rfl rfl

noncomputable def ep1157 := @ep1042 262144 Bool.false 1048575 1048576 1 141176 (@ep1045 125179659 1048576 93 262144 ep1155 rfl) (Enclosure.sfrac_false_div 125179659 1048576) (BSN.cos_reduce0 qz468 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 15850283896634605568) qz20) 226375608064910080 72057594037927936 Bool.false 1048575 1048576 19 1000000000000000 282352 141176 (BSN.sin_reduce_arg_pos_rat_q0 125179659 1048576 226375608064910080 72057594037927936 19 15850283896634605568 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1048575 1048576 15850283896634605568 151115727451828646838272 225246 2147483648 282628 282352 (ep1156 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1158 := nat_lit 98528585358033288359949847

noncomputable def ep1159 := nat_lit 6077057619970531925164032000

noncomputable def ep1160 := nat_lit 271332471339277195274902847433

noncomputable abbrev qz484 := (@HPow.hPow Complex Complex Complex qz536 (@Nat.cast Complex Complex.instNatCast 31) qz590)

noncomputable abbrev qz205 := qz484

noncomputable abbrev qz485 := (@Nat.cast Complex Complex.instNatCast 31)

noncomputable abbrev qz206 := (@HAdd.hAdd Complex Complex Complex qz273 (@HDiv.hDiv Complex Complex Complex qz386 qz485 (@HSub.hSub Complex Complex Complex qz378 qz439 (1 : Complex))) qz385)

noncomputable abbrev qz207 := qz485

noncomputable def ep1161 := @Enclosure.Complex.IsNear.of_eq (zetaApproximant qz146 1 31) (@HAdd.hAdd Complex Complex Complex qz4 (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 31, @HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast n) qz147) (@HMul.hMul Complex Complex Complex qz72 qz205 (@HAdd.hAdd Complex Complex Complex qz4 qz206 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz80 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz122 qz207 (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1))))))) Bool.false ep1037 ep1038 ep1039

noncomputable def ep1162 := @Enclosure.Complex.IsNear.addLitP (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 31, @HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast n) qz147) (@HMul.hMul Complex Complex Complex qz72 qz205 (@HAdd.hAdd Complex Complex Complex qz4 qz206 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz80 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz122 qz207 (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))))) Bool.false 998876950005 1099511627776 145501917345191 19403081695363072

noncomputable def ep1163 := nat_lit 152383721601213627392841843

noncomputable def ep1164 := nat_lit 3222607207274028419774899489

noncomputable def ep1165 := nat_lit 309199316607812125530861847

noncomputable def ep1166 := nat_lit 3221678052089069349565591433

noncomputable def ep1167 := nat_lit 1855863253029287893869959320021952888832

noncomputable def ep1168 := nat_lit 13541665658684717580330306210086518784

noncomputable def ep1169 := @ep1162 Bool.true 4764536827 137438953472 72763240005187 9701540847681536 Bool.true ep1163 ep1038 ep1164 ep1040 Bool.false ep1165 ep1159 ep1166 ep1040 Bool.false ep1167 ep1037 ep1038 ep1039 ep1040 Bool.false ep1168 ep1158 ep1159

noncomputable def ep1170 := @Enclosure.Complex.IsNear.of_eq (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 31, @HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast n) qz147) (BSN.headSumC qz146 31) Bool.false 998876950005 1099511627776 145501917345191 19403081695363072 Bool.true 4764536827 137438953472 72763240005187

noncomputable def ep1171 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz146 31) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz146 30) (@HPow.hPow Complex Complex Complex qz6 qz123 qz147)) Bool.false 998876950005 1099511627776 145501917345191 19403081695363072 Bool.true 4764536827 137438953472 72763240005187 9701540847681536

noncomputable def ep1172 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz146 30) (@HPow.hPow Complex Complex Complex qz6 qz123 qz147) Bool.false 799463029257 1099511627776 142397601131923 19403081695363072 Bool.true 7646519749 137438953472 71219210142047 9701540847681536 Bool.false

noncomputable def ep1173 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz146 30) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz146 29) (@HPow.hPow Complex Complex Complex qz6 qz413 qz147)) Bool.false 799463029257 1099511627776 142397601131923 19403081695363072 Bool.true 7646519749 137438953472 71219210142047 9701540847681536

noncomputable def ep1174 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz146 29) (@HPow.hPow Complex Complex Complex qz6 qz413 qz147) Bool.false 445512029211 549755813888 69623595075175 9701540847681536 Bool.false 60659901299 549755813888 34819942060439 4850770423840768 Bool.true

noncomputable def ep1175 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz146 29) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz146 28) (@HPow.hPow Complex Complex Complex qz6 qz414 qz147)) Bool.false 445512029211 549755813888 69623595075175 9701540847681536 Bool.false 60659901299 549755813888 34819942060439 4850770423840768

noncomputable def ep1176 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz146 28) (@HPow.hPow Complex Complex Complex qz6 qz414 qz147) Bool.false 255043207603 274877906944 17005179152673 2425385211920384 Bool.true 41458617633 1099511627776 136071016493361 19403081695363072 Bool.true

noncomputable def ep1177 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz146 28) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz146 27) (@HPow.hPow Complex Complex Complex qz6 qz415 qz147)) Bool.false 255043207603 274877906944 17005179152673 2425385211920384 Bool.true 41458617633 1099511627776 136071016493361 19403081695363072

noncomputable def ep1178 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz146 27) (@HPow.hPow Complex Complex Complex qz6 qz415 qz147) Bool.false 824555539179 1099511627776 132771461344735 19403081695363072 Bool.true 30534313109 274877906944 66405547909251 9701540847681536 Bool.false

noncomputable def ep1179 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz146 27) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz146 26) (@HPow.hPow Complex Complex Complex qz6 qz416 qz147)) Bool.false 824555539179 1099511627776 132771461344735 19403081695363072 Bool.true 30534313109 274877906944 66405547909251 9701540847681536

noncomputable def ep1180 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz146 26) (@HPow.hPow Complex Complex Complex qz6 qz416 qz147) Bool.false 765163373063 1099511627776 129447907810127 19403081695363072 Bool.false 85154387495 1099511627776 129474850473259 19403081695363072 Bool.false

noncomputable def ep1181 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz146 26) (@HAdd.hAdd Complex Complex Complex qz4 qz167 (@HPow.hPow Complex Complex Complex qz6 qz417 qz147)) Bool.false 765163373063 1099511627776 129447907810127 19403081695363072 Bool.false 85154387495 1099511627776 129474850473259 19403081695363072

noncomputable def ep1182 := @Enclosure.Complex.IsNear.addLitP qz167 (@HPow.hPow Complex Complex Complex qz6 qz417 qz147) Bool.false 485967511519 549755813888 31512510753477 4850770423840768 Bool.false 160003348715 1099511627776 126088086645919 19403081695363072 Bool.true

noncomputable abbrev qz208 := (@HMul.hMul Real Real Real qz268 qz441 qz582)

noncomputable def ep1183 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz417 qz147) (Complex.mk (@HMul.hMul Real Real Real qz0 qz124 (Real.cos qz208)) (@HMul.hMul Real Real Real qz0 qz124 (@Neg.neg Real Real.instNeg (Real.sin qz208)))) Bool.true 206771649975 1099511627776 3397864796219 19403081695363072 Bool.true 18712240305 274877906944 846690956835 4850770423840768 (BSN.cpow_neg_s_mk qz149 121891 1000 25 qz150 rfl)

noncomputable def ep1184 := @Enclosure.Real.IsNear.mulLit_ff qz149 qz582 121891 1000 0 1 3624129903009015 1125899906842624 31250000017647 4411750000000000000 88349763601534369473 225179981368524800 544156250307287211 630250000000000000000 qz151 (BSN.isNear_log_sfrac 25 1 3624129903009015 1125899906842624 31250000017647 4411750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz418) Bool.false 60802810194841294602240 18889465931478580854784 1000000000564704 141176000000000000000 3624129903009015 1125899906842624 31250000017647 4411750000000000000 (BSN.log_rat_reduce_isNear 25 1 4 50 32 233982 524288 24973259072661432 36028797018963968 141176 1000000000000000 rfl rfl rfl rfl (ep583 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1185 := nat_lit 3067126004355654670464638802059769742702519906881479780438414734716234468874785

noncomputable def ep1186 := nat_lit 2271001221509762900144414211424094304802826488626195063745038363255177927201

noncomputable def ep1187 := nat_lit 8029272199906174996997629715718996030584538037041337966283118052621058082789921

noncomputable def ep1188 := BSN.sin_dyadic_bound_f 2627405901 2147483648 3 2 1048576 282628 ep1185 ep65 ep1186 ep1187 ep67 ep1186 985965 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2627405901) qz21 0 2 ep1185 ep65 ep1186 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2627405901) qz285 0 2 ep1187 ep67 ep1186 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz486 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 205705323) qz34)

noncomputable def ep1189 := @Enclosure.Real.IsNear.cos_image qz208 qz486 Bool.false 205705323 524288 453 524288 Bool.true 985965 1048576 1 141176 (@Enclosure.Real.IsNear.recentre' qz208 Bool.false 88349763601534369473 225179981368524800 544156250307287211 630250000000000000000 205705323 524288 453 524288 (ep1184 rfl) rfl) (Enclosure.sfrac_false_div 205705323 524288) (BSN.cos_reduce1 qz486 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 92443626866922221469696) qz35) 226375608064910080 72057594037927936 Bool.false 985965 1048576 62 1000000000000000 282352 141176 (BSN.sin_reduce_arg_pos_rat_q1 205705323 524288 226375608064910080 72057594037927936 62 92443626866922221469696 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 985965 1048576 92443626866922221469696 75557863725914323419136 2627405901 2147483648 282628 282352 (ep1188 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1190 := nat_lit 1704968225184923600435974629682727232303534537817989298049672647448243672898081

noncomputable def ep1191 := nat_lit 5110362673111751275507635060625333508300997960476715504021527865618220662839841

noncomputable def ep1192 := BSN.cos_dyadic_bound_f 2627405901 2147483648 3 2 1048576 282628 ep1190 ep58 ep1186 ep1191 ep61 ep1186 356908 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2627405901) qz16 0 2 ep1190 ep58 ep1186 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2627405901) qz282 0 2 ep1191 ep61 ep1186 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1193 := @Enclosure.Real.IsNear.sin_image qz208 qz486 Bool.false 205705323 524288 453 524288 Bool.false 356908 1048576 1 141176 (@Enclosure.Real.IsNear.recentre' qz208 Bool.false 88349763601534369473 225179981368524800 544156250307287211 630250000000000000000 205705323 524288 453 524288 (ep1184 rfl) rfl) (Enclosure.sfrac_false_div 205705323 524288) (BSN.sin_reduce1 qz486 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 92443626866922221469696) qz35) 226375608064910080 72057594037927936 Bool.false 356908 1048576 62 1000000000000000 282352 141176 (BSN.sin_reduce_arg_pos_rat_q1 205705323 524288 226375608064910080 72057594037927936 62 92443626866922221469696 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 356908 1048576 92443626866922221469696 75557863725914323419136 2627405901 2147483648 282628 282352 (ep1192 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1194 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz124 (Real.cos qz208)) (@HMul.hMul Real Real Real qz0 qz124 (@Neg.neg Real Real.instNeg (Real.sin qz208))) Bool.true 206771649975 1099511627776 3397864796219 19403081695363072 Bool.true 18712240305 274877906944 846690956835 4850770423840768 (@Enclosure.Real.IsNear.mulLit_ft qz124 (Real.cos qz208) 209715 1048576 1 1048576 985965 1048576 8059627 9252110336 206771649975 1099511627776 3397864796219 19403081695363072 qz420 (@Enclosure.Real.IsNear.recentre' (Real.cos qz208) Bool.true 985965 1048576 64477016 74016882688 985965 1048576 8059627 9252110336 (ep1189 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz124 (@Neg.neg Real Real.instNeg (Real.sin qz208)) 209715 1048576 1 1048576 89227 262144 8059627 9252110336 18712240305 274877906944 846690956835 4850770423840768 qz420 (@Enclosure.Real.IsNear.neg (Real.sin qz208) Bool.false 89227 262144 8059627 9252110336 (@Enclosure.Real.IsNear.recentre' (Real.sin qz208) Bool.false 356908 1048576 64477016 74016882688 89227 262144 8059627 9252110336 (ep1193 rfl rfl) rfl)) rfl)

noncomputable def ep1195 := @ep1182 206771649975 1099511627776 3397864796219 19403081695363072 Bool.true 18712240305 274877906944 846690956835 4850770423840768 Bool.false 420653012915536940498944 765163373063 1099511627776 129447907810127 19403081695363072 Bool.false 23407059801723927265280 85154387495 1099511627776 129474850473259 19403081695363072 EMRow39.d14 (ep1183 ep1194) rfl rfl

noncomputable abbrev qz209 := (@HMul.hMul Real Real Real qz268 qz441 qz583)

noncomputable def ep1196 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz416 qz147) (Complex.mk (@HMul.hMul Real Real Real qz0 qz126 (Real.cos qz209)) (@HMul.hMul Real Real Real qz0 qz126 (@Neg.neg Real Real.instNeg (Real.sin qz209)))) Bool.false 14848041529 274877906944 207722095913 1212692605960192 Bool.true 207291639931 1099511627776 3336245345243 19403081695363072 (BSN.cpow_neg_s_mk qz149 121891 1000 26 qz150 rfl)

noncomputable def ep1197 := @Enclosure.Real.IsNear.mulLit_ff qz149 qz583 121891 1000 0 1 3668288609262839 1125899906842624 31250000017647 4411750000000000000 447131366871656708549 1125899906842624000 544156250307287211 630250000000000000000 qz151 (BSN.isNear_log_sfrac 26 1 3668288609262839 1125899906842624 31250000017647 4411750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz421) Bool.false 61543670347942250676224 18889465931478580854784 1000000000564704 141176000000000000000 3668288609262839 1125899906842624 31250000017647 4411750000000000000 (BSN.log_rat_reduce_isNear 26 1 4 52 32 254545 524288 24973259072661432 36028797018963968 141176 1000000000000000 rfl rfl rfl rfl (ep597 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1198 := nat_lit 2119283048208653836936133080931933252155534251883138806599552791570724552690625

noncomputable def ep1199 := nat_lit 3506566525056941464404967040891528314898238956535751971687715185224187890625

noncomputable def ep1200 := nat_lit 6350836011575847627879589308714016699836806277736344915855282944341725282290625

noncomputable def ep1201 := BSN.cos_dyadic_bound_f 2774024295 2147483648 3 2 1048576 282628 ep1198 ep58 ep1199 ep1200 ep61 ep1199 288812 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2774024295) qz16 0 2 ep1198 ep58 ep1199 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2774024295) qz282 0 2 ep1200 ep61 ep1199 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz487 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 416423535) qz17)

noncomputable def ep1202 := @Enclosure.Real.IsNear.cos_image qz209 qz487 Bool.false 416423535 1048576 907 1048576 Bool.false 288812 1048576 1 141176 (@Enclosure.Real.IsNear.recentre' qz209 Bool.false 447131366871656708549 1125899906842624000 544156250307287211 630250000000000000000 416423535 1048576 907 1048576 (ep1197 rfl) rfl) (Enclosure.sfrac_false_div 416423535 1048576) (BSN.cos_reduce0 qz487 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 195204605965420053135360) qz20) 226375608064910080 72057594037927936 Bool.false 288812 1048576 63 1000000000000000 282352 141176 (BSN.sin_reduce_arg_pos_rat_q0 416423535 1048576 226375608064910080 72057594037927936 63 195204605965420053135360 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 288812 1048576 195204605965420053135360 151115727451828646838272 2774024295 2147483648 282628 282352 (ep1201 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1203 := nat_lit 3811904233555531353313515572044766631228043062224421250301844852679124844530625

noncomputable def ep1204 := nat_lit 9977881408747728020116837503955802512135039442753378723788765932431154479090625

noncomputable def ep1205 := BSN.sin_dyadic_bound_f 2774024295 2147483648 3 2 1048576 282628 ep1203 ep65 ep1199 ep1204 ep67 ep1199 1008017 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2774024295) qz21 0 2 ep1203 ep65 ep1199 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2774024295) qz285 0 2 ep1204 ep67 ep1199 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1206 := @Enclosure.Real.IsNear.sin_image qz209 qz487 Bool.false 416423535 1048576 907 1048576 Bool.false 1008017 1048576 1 141176 (@Enclosure.Real.IsNear.recentre' qz209 Bool.false 447131366871656708549 1125899906842624000 544156250307287211 630250000000000000000 416423535 1048576 907 1048576 (ep1197 rfl) rfl) (Enclosure.sfrac_false_div 416423535 1048576) (BSN.sin_reduce0 qz487 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 195204605965420053135360) qz20) 226375608064910080 72057594037927936 Bool.false 1008017 1048576 63 1000000000000000 282352 141176 (BSN.sin_reduce_arg_pos_rat_q0 416423535 1048576 226375608064910080 72057594037927936 63 195204605965420053135360 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1008017 1048576 195204605965420053135360 151115727451828646838272 2774024295 2147483648 282628 282352 (ep1205 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1207 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz126 (Real.cos qz209)) (@HMul.hMul Real Real Real qz0 qz126 (@Neg.neg Real Real.instNeg (Real.sin qz209))) Bool.false 14848041529 274877906944 207722095913 1212692605960192 Bool.true 207291639931 1099511627776 3336245345243 19403081695363072 (@Enclosure.Real.IsNear.mulLit_ff qz126 (Real.cos qz209) 205643 1048576 1 1048576 72203 262144 16136901 18504220672 14848041529 274877906944 207722095913 1212692605960192 qz423 (@Enclosure.Real.IsNear.recentre' (Real.cos qz209) Bool.false 288812 1048576 129095208 148033765376 72203 262144 16136901 18504220672 (ep1202 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz126 (@Neg.neg Real Real.instNeg (Real.sin qz209)) 205643 1048576 1 1048576 1008017 1048576 16136901 18504220672 207291639931 1099511627776 3336245345243 19403081695363072 qz423 (@Enclosure.Real.IsNear.neg (Real.sin qz209) Bool.false 1008017 1048576 16136901 18504220672 (@Enclosure.Real.IsNear.recentre' (Real.sin qz209) Bool.false 1008017 1048576 129095208 148033765376 1008017 1048576 16136901 18504220672 (ep1206 rfl rfl) rfl)) rfl)

noncomputable def ep1208 := @ep1180 14848041529 274877906944 207722095913 1212692605960192 Bool.true 207291639931 1099511627776 3336245345243 19403081695363072 Bool.false 226652100768604908158976 824555539179 1099511627776 132771461344735 19403081695363072 Bool.true 134291329237994581262336 30534313109 274877906944 66405547909251 9701540847681536 (ep1181 (BSN.head_sum_c_succ qz146 25 26 rfl rfl) (ep1195 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1196 ep1207) rfl rfl

noncomputable abbrev qz210 := (@HMul.hMul Real Real Real qz268 qz441 qz584)

noncomputable def ep1209 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz415 qz147) (Complex.mk (@HMul.hMul Real Real Real qz0 qz128 (Real.cos qz210)) (@HMul.hMul Real Real Real qz0 qz128 (@Neg.neg Real Real.instNeg (Real.sin qz210)))) Bool.false 195617291233 1099511627776 3269971876649 19403081695363072 Bool.false 80678634803 1099511627776 3259920674859 19403081695363072 (BSN.cpow_neg_s_mk qz149 121891 1000 27 qz150 rfl)

noncomputable def ep1210 := @Enclosure.Real.IsNear.mulLit_ff qz149 qz584 121891 1000 0 1 3710780868205815 1125899906842624 31250000017647 4411750000000000000 90462158161294999233 225179981368524800 544156250307287211 630250000000000000000 qz151 (BSN.isNear_log_sfrac 27 1 3710780868205815 1125899906842624 31250000017647 4411750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz424) Bool.false 62256572154556490711040 18889465931478580854784 1000000000564704 141176000000000000000 3710780868205815 1125899906842624 31250000017647 4411750000000000000 (BSN.log_rat_reduce_isNear 27 1 4 54 32 274332 524288 24973259072661432 36028797018963968 141176 1000000000000000 rfl rfl rfl rfl (ep608 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1211 := nat_lit 2650128846275257251263510087187110431775006494972817138948178060663668604928000

noncomputable def ep1212 := nat_lit 1695803381843843955926719071630331128378834974019023050828328977138614009856

noncomputable def ep1213 := nat_lit 6938068058578878958332930778421697261393356039732775993258172864346621923557376

noncomputable def ep1214 := BSN.sin_dyadic_bound_f 2533214336 2147483648 3 2 1048576 282628 ep1211 ep65 ep1212 ep1213 ep67 ep1212 969367 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2533214336) qz21 0 2 ep1211 ep65 ep1212 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2533214336) qz285 0 2 ep1213 ep67 ep1212 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz488 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 210623625) qz34)

noncomputable def ep1215 := @Enclosure.Real.IsNear.cos_image qz210 qz488 Bool.false 210623625 524288 453 524288 Bool.false 969367 1048576 1 141176 (@Enclosure.Real.IsNear.recentre' qz210 Bool.false 90462158161294999233 225179981368524800 544156250307287211 630250000000000000000 210623625 524288 453 524288 (ep1210 rfl) rfl) (Enclosure.sfrac_false_div 210623625 524288) (BSN.cos_reduce3 qz488 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 89129555803966852300800) qz35) 226375608064910080 72057594037927936 Bool.false 969367 1048576 63 1000000000000000 282352 141176 (BSN.sin_reduce_arg_pos_rat_q3 210623625 524288 226375608064910080 72057594037927936 63 89129555803966852300800 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 969367 1048576 89129555803966852300800 75557863725914323419136 2533214336 2147483648 282628 282352 (ep1214 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1216 := nat_lit 1473047493878184625793473034691341498154283090528906865216022624358544164519936

noncomputable def ep1217 := nat_lit 4415750874870866189468565665930763832206091601638682549546411215121355265540096

noncomputable def ep1218 := BSN.cos_dyadic_bound_f 2533214336 2147483648 3 2 1048576 282628 ep1216 ep58 ep1212 ep1217 ep61 ep1212 399797 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2533214336) qz16 0 2 ep1216 ep58 ep1212 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2533214336) qz282 0 2 ep1217 ep61 ep1212 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1219 := @Enclosure.Real.IsNear.sin_image qz210 qz488 Bool.false 210623625 524288 453 524288 Bool.true 399797 1048576 1 141176 (@Enclosure.Real.IsNear.recentre' qz210 Bool.false 90462158161294999233 225179981368524800 544156250307287211 630250000000000000000 210623625 524288 453 524288 (ep1210 rfl) rfl) (Enclosure.sfrac_false_div 210623625 524288) (BSN.sin_reduce3 qz488 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 89129555803966852300800) qz35) 226375608064910080 72057594037927936 Bool.false 399797 1048576 63 1000000000000000 282352 141176 (BSN.sin_reduce_arg_pos_rat_q3 210623625 524288 226375608064910080 72057594037927936 63 89129555803966852300800 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 399797 1048576 89129555803966852300800 75557863725914323419136 2533214336 2147483648 282628 282352 (ep1218 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1220 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz128 (Real.cos qz210)) (@HMul.hMul Real Real Real qz0 qz128 (@Neg.neg Real Real.instNeg (Real.sin qz210))) Bool.false 195617291233 1099511627776 3269971876649 19403081695363072 Bool.false 80678634803 1099511627776 3259920674859 19403081695363072 (@Enclosure.Real.IsNear.mulLit_ff qz128 (Real.cos qz210) 201799 1048576 1 1048576 969367 1048576 8059627 9252110336 195617291233 1099511627776 3269971876649 19403081695363072 qz426 (@Enclosure.Real.IsNear.recentre' (Real.cos qz210) Bool.false 969367 1048576 64477016 74016882688 969367 1048576 8059627 9252110336 (ep1215 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz128 (@Neg.neg Real Real.instNeg (Real.sin qz210)) 201799 1048576 1 1048576 399797 1048576 8059627 9252110336 80678634803 1099511627776 3259920674859 19403081695363072 qz426 (@Enclosure.Real.IsNear.neg (Real.sin qz210) Bool.true 399797 1048576 8059627 9252110336 (@Enclosure.Real.IsNear.recentre' (Real.sin qz210) Bool.true 399797 1048576 64477016 74016882688 399797 1048576 8059627 9252110336 (ep1219 rfl rfl) rfl)) rfl)

noncomputable def ep1221 := @ep1178 195617291233 1099511627776 3269971876649 19403081695363072 Bool.false 80678634803 1099511627776 3259920674859 19403081695363072 Bool.false 1121691889379147316723712 255043207603 274877906944 17005179152673 2425385211920384 Bool.true 11396058039750651543552 41458617633 1099511627776 136071016493361 19403081695363072 (ep1179 (BSN.head_sum_c_succ qz146 26 27 rfl rfl) (ep1208 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1209 ep1220) rfl rfl

noncomputable abbrev qz211 := (@HMul.hMul Real Real Real qz268 qz441 qz585)

noncomputable def ep1222 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz414 qz147) (Complex.mk (@HMul.hMul Real Real Real qz0 qz130 (Real.cos qz211)) (@HMul.hMul Real Real Real qz0 qz130 (@Neg.neg Real Real.instNeg (Real.sin qz211)))) Bool.true 64574385995 549755813888 1602878464483 9701540847681536 Bool.false 162778420231 1099511627776 3208751748395 19403081695363072 (BSN.cpow_neg_s_mk qz149 121891 1000 28 qz150 rfl)

noncomputable def ep1223 := @Enclosure.Real.IsNear.mulLit_ff qz149 qz585 121891 1000 0 1 3751726938922231 1125899906842624 31250000017647 4411750000000000000 457301748312169658821 1125899906842624000 544156250307287211 630250000000000000000 qz151 (BSN.isNear_log_sfrac 28 1 3751726938922231 1125899906842624 31250000017647 4411750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz427) Bool.false 62943533227317076688896 18889465931478580854784 1000000000564704 141176000000000000000 3751726938922231 1125899906842624 31250000017647 4411750000000000000 (BSN.log_rat_reduce_isNear 28 1 4 56 32 293399 524288 24973259072661432 36028797018963968 141176 1000000000000000 rfl rfl rfl rfl (ep619 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1224 := nat_lit 498958005888022298610105599971818652012441652287746249583944337400598913229056

noncomputable def ep1225 := nat_lit 194863821944649527359369663832602880487348451017198268161029253311122514176

noncomputable def ep1226 := nat_lit 1496484290020177596775598060587790750276350259961204352215510953695174494658816

noncomputable def ep1227 := BSN.cos_dyadic_bound_f 1932931226 2147483648 3 2 1048576 282628 ep1224 ep58 ep1225 ep1226 ep61 ep1225 651730 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1932931226) qz16 0 2 ep1224 ep58 ep1225 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1932931226) qz282 0 2 ep1226 ep61 ep1225 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz489 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 425895441) qz17)

noncomputable def ep1228 := @Enclosure.Real.IsNear.cos_image qz211 qz489 Bool.false 425895441 1048576 453 524288 Bool.true 651730 1048576 1 141176 (@Enclosure.Real.IsNear.recentre' qz211 Bool.false 457301748312169658821 1125899906842624000 544156250307287211 630250000000000000000 425895441 1048576 453 524288 (ep1223 rfl) rfl) (Enclosure.sfrac_false_div 425895441 1048576) (BSN.cos_reduce2 qz489 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 136017942978620829990912) qz20) 226375608064910080 72057594037927936 Bool.false 651730 1048576 64 1000000000000000 282352 141176 (BSN.sin_reduce_arg_pos_rat_q2 425895441 1048576 226375608064910080 72057594037927936 64 136017942978620829990912 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 651730 1048576 136017942978620829990912 151115727451828646838272 1932931226 2147483648 282628 282352 (ep1227 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1229 := nat_lit 897968519540884417876302584218207491318005095357129490636570983918429145800960

noncomputable def ep1230 := nat_lit 2351506819276310709488877312544338263073986209395597011613996624804810707312896

noncomputable def ep1231 := BSN.sin_dyadic_bound_f 1932931226 2147483648 3 2 1048576 282628 ep1229 ep65 ep1225 ep1230 ep67 ep1225 821437 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1932931226) qz21 0 2 ep1229 ep65 ep1225 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1932931226) qz285 0 2 ep1230 ep67 ep1225 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1232 := @Enclosure.Real.IsNear.sin_image qz211 qz489 Bool.false 425895441 1048576 453 524288 Bool.true 821437 1048576 1 141176 (@Enclosure.Real.IsNear.recentre' qz211 Bool.false 457301748312169658821 1125899906842624000 544156250307287211 630250000000000000000 425895441 1048576 453 524288 (ep1223 rfl) rfl) (Enclosure.sfrac_false_div 425895441 1048576) (BSN.sin_reduce2 qz489 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 136017942978620829990912) qz20) 226375608064910080 72057594037927936 Bool.false 821437 1048576 64 1000000000000000 282352 141176 (BSN.sin_reduce_arg_pos_rat_q2 425895441 1048576 226375608064910080 72057594037927936 64 136017942978620829990912 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 821437 1048576 136017942978620829990912 151115727451828646838272 1932931226 2147483648 282628 282352 (ep1231 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1233 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz130 (Real.cos qz211)) (@HMul.hMul Real Real Real qz0 qz130 (@Neg.neg Real Real.instNeg (Real.sin qz211))) Bool.true 64574385995 549755813888 1602878464483 9701540847681536 Bool.false 162778420231 1099511627776 3208751748395 19403081695363072 (@Enclosure.Real.IsNear.mulLit_ft qz130 (Real.cos qz211) 198163 1048576 1 1048576 325865 524288 8059627 9252110336 64574385995 549755813888 1602878464483 9701540847681536 qz429 (@Enclosure.Real.IsNear.recentre' (Real.cos qz211) Bool.true 651730 1048576 64477016 74016882688 325865 524288 8059627 9252110336 (ep1228 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz130 (@Neg.neg Real Real.instNeg (Real.sin qz211)) 198163 1048576 1 1048576 821437 1048576 8059627 9252110336 162778420231 1099511627776 3208751748395 19403081695363072 qz429 (@Enclosure.Real.IsNear.neg (Real.sin qz211) Bool.true 821437 1048576 8059627 9252110336 (@Enclosure.Real.IsNear.recentre' (Real.sin qz211) Bool.true 821437 1048576 64477016 74016882688 821437 1048576 8059627 9252110336 (ep1232 rfl rfl) rfl)) rfl)

noncomputable def ep1234 := @ep1176 64574385995 549755813888 1602878464483 9701540847681536 Bool.false 162778420231 1099511627776 3208751748395 19403081695363072 Bool.false 122461414107893867741184 445512029211 549755813888 69623595075175 9701540847681536 Bool.false 133392533635989973762048 60659901299 549755813888 34819942060439 4850770423840768 (ep1177 (BSN.head_sum_c_succ qz146 27 28 rfl rfl) (ep1221 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1222 ep1233) rfl rfl

noncomputable abbrev qz212 := (@HMul.hMul Real Real Real qz268 qz441 qz586)

noncomputable def ep1235 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz413 qz147) (Complex.mk (@HMul.hMul Real Real Real qz0 qz132 (Real.cos qz212)) (@HMul.hMul Real Real Real qz0 qz132 (@Neg.neg Real Real.instNeg (Real.sin qz212)))) Bool.true 91561029165 1099511627776 3150410981573 19403081695363072 Bool.true 91245980295 549755813888 1579326021169 9701540847681536 (BSN.cpow_neg_s_mk qz149 121891 1000 29 qz150 rfl)

noncomputable def ep1236 := @Enclosure.Real.IsNear.mulLit_ff qz149 qz586 121891 1000 0 1 3791236343078135 1125899906842624 31250000017647 4411750000000000000 92423517818827390657 225179981368524800 544156250307287211 630250000000000000000 qz151 (BSN.isNear_log_sfrac 29 1 3791236343078135 1125899906842624 31250000017647 4411750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz430) Bool.false 63606391034871975772160 18889465931478580854784 1000000000564704 141176000000000000000 3791236343078135 1125899906842624 31250000017647 4411750000000000000 (BSN.log_rat_reduce_isNear 29 1 4 58 32 311797 524288 24973259072661432 36028797018963968 141176 1000000000000000 rfl rfl rfl rfl (ep630 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1237 := nat_lit 994570270882900531417883008046100625

noncomputable def ep1238 := BSN.sin_dyadic_bound_f 998639795 2147483648 2 1 1048576 282628 ep1237 ep144 ep1237 ep1237 ep145 ep1237 470231 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 998639795) qz21 0 1 ep1237 ep144 ep1237 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 998639795) qz285 0 1 ep1237 ep145 ep1237 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz490 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 215190271) qz34)

noncomputable def ep1239 := @Enclosure.Real.IsNear.cos_image qz212 qz490 Bool.false 215190271 524288 907 1048576 Bool.true 470231 1048576 1 141176 (@Enclosure.Real.IsNear.recentre' qz212 Bool.false 92423517818827390657 225179981368524800 544156250307287211 630250000000000000000 215190271 524288 907 1048576 (ep1236 rfl) rfl) (Enclosure.sfrac_false_div 215190271 524288) (BSN.cos_reduce1 qz490 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 35136514163008310607872) qz35) 226375608064910080 72057594037927936 Bool.false 470231 1048576 65 1000000000000000 282352 141176 (BSN.sin_reduce_arg_pos_rat_q1 215190271 524288 226375608064910080 72057594037927936 65 35136514163008310607872 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 470231 1048576 35136514163008310607872 75557863725914323419136 998639795 2147483648 282628 282352 (ep1238 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1240 := BSN.cos_dyadic_bound_f 998639795 2147483648 2 1 1048576 282628 ep1237 ep140 ep1237 ep1237 ep141 ep1237 937226 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 998639795) qz16 0 1 ep1237 ep140 ep1237 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 998639795) qz282 0 1 ep1237 ep141 ep1237 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1241 := @Enclosure.Real.IsNear.sin_image qz212 qz490 Bool.false 215190271 524288 907 1048576 Bool.false 937226 1048576 1 141176 (@Enclosure.Real.IsNear.recentre' qz212 Bool.false 92423517818827390657 225179981368524800 544156250307287211 630250000000000000000 215190271 524288 907 1048576 (ep1236 rfl) rfl) (Enclosure.sfrac_false_div 215190271 524288) (BSN.sin_reduce1 qz490 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 35136514163008310607872) qz35) 226375608064910080 72057594037927936 Bool.false 937226 1048576 65 1000000000000000 282352 141176 (BSN.sin_reduce_arg_pos_rat_q1 215190271 524288 226375608064910080 72057594037927936 65 35136514163008310607872 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 937226 1048576 35136514163008310607872 75557863725914323419136 998639795 2147483648 282628 282352 (ep1240 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1242 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz132 (Real.cos qz212)) (@HMul.hMul Real Real Real qz0 qz132 (@Neg.neg Real Real.instNeg (Real.sin qz212))) Bool.true 91561029165 1099511627776 3150410981573 19403081695363072 Bool.true 91245980295 549755813888 1579326021169 9701540847681536 (@Enclosure.Real.IsNear.mulLit_ft qz132 (Real.cos qz212) 194715 1048576 1 1048576 470231 1048576 16136901 18504220672 91561029165 1099511627776 3150410981573 19403081695363072 qz433 (@Enclosure.Real.IsNear.recentre' (Real.cos qz212) Bool.true 470231 1048576 129095208 148033765376 470231 1048576 16136901 18504220672 (ep1239 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz132 (@Neg.neg Real Real.instNeg (Real.sin qz212)) 194715 1048576 1 1048576 468613 524288 16136901 18504220672 91245980295 549755813888 1579326021169 9701540847681536 qz433 (@Enclosure.Real.IsNear.neg (Real.sin qz212) Bool.false 468613 524288 16136901 18504220672 (@Enclosure.Real.IsNear.recentre' (Real.sin qz212) Bool.false 937226 1048576 129095208 148033765376 468613 524288 16136901 18504220672 (ep1241 rfl rfl) rfl)) rfl)

noncomputable def ep1243 := @ep1174 91561029165 1099511627776 3150410981573 19403081695363072 Bool.true 91245980295 549755813888 1579326021169 9701540847681536 Bool.false 439509448322547990921216 799463029257 1099511627776 142397601131923 19403081695363072 Bool.true 16814874752088641896448 7646519749 137438953472 71219210142047 9701540847681536 (ep1175 (BSN.head_sum_c_succ qz146 28 29 rfl rfl) (ep1234 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1235 ep1242) rfl rfl

noncomputable abbrev qz213 := (@HMul.hMul Real Real Real qz268 qz441 (Real.log (Enclosure.sfrac Bool.false 30 1)))

noncomputable def ep1244 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz123 qz147) (Complex.mk (@HMul.hMul Real Real Real qz0 qz136 (Real.cos qz213)) (@HMul.hMul Real Real Real qz0 qz136 (@Neg.neg Real Real.instNeg (Real.sin qz213)))) Bool.false 49853480187 274877906944 776079053317 4850770423840768 Bool.false 1440991461 68719476736 386007465785 2425385211920384 (BSN.cpow_neg_s_mk qz149 121891 1000 30 qz150 rfl)

noncomputable def ep1245 := @Enclosure.Real.IsNear.mulLit_ff qz149 qz139 121891 1000 0 1 3829405717437687 1125899906842624 31250000017647 4411750000000000000 466770092304197106117 1125899906842624000 544156250307287211 630250000000000000000 qz151 (BSN.isNear_log_sfrac 30 1 3829405717437687 1125899906842624 31250000017647 4411750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz436) Bool.false 64246766873087041339392 18889465931478580854784 1000000000564704 141176000000000000000 3829405717437687 1125899906842624 31250000017647 4411750000000000000 (BSN.log_rat_reduce_isNear 30 1 4 60 32 329571 524288 24973259072661432 36028797018963968 141176 1000000000000000 rfl rfl rfl rfl (ep652 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1246 := nat_lit 6150910033235269596939560384671879760175008360148675171993342354015460906254465

noncomputable def ep1247 := nat_lit 9119844938666637323699873247203690958486435556197280863178587331252464402561

noncomputable def ep1248 := nat_lit 16094760814286912483936667879359450538906520047584115567156464642932750764490881

noncomputable def ep1249 := BSN.sin_dyadic_bound_f 3126068079 2147483648 3 2 1048576 282628 ep1246 ep65 ep1247 ep1248 ep67 ep1247 1041636 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3126068079) qz21 0 2 ep1246 ep65 ep1247 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3126068079) qz285 0 2 ep1248 ep67 ep1247 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz491 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 108678381) (@Nat.cast Real Real.instNatCast 262144))

noncomputable def ep1250 := @Enclosure.Real.IsNear.cos_image qz213 qz491 Bool.false 108678381 262144 453 524288 Bool.false 1041636 1048576 1 141176 (@Enclosure.Real.IsNear.recentre' qz213 Bool.false 466770092304197106117 1125899906842624000 544156250307287211 630250000000000000000 108678381 262144 453 524288 (ep1245 rfl) rfl) (Enclosure.sfrac_false_div 108678381 262144) (BSN.cos_reduce3 qz491 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 54994371245193111273472) qz598) 226375608064910080 72057594037927936 Bool.false 1041636 1048576 65 1000000000000000 282352 141176 (BSN.sin_reduce_arg_pos_rat_q3 108678381 262144 226375608064910080 72057594037927936 65 54994371245193111273472 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1041636 1048576 54994371245193111273472 37778931862957161709568 3126068079 2147483648 282628 282352 (ep1249 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1251 := nat_lit 3421225505103446059332511268483134840523220838107573887046602902155812709875841

noncomputable def ep1252 := nat_lit 10245436825433004903350134058954997139652689643210327099413451531804933200822401

noncomputable def ep1253 := BSN.cos_dyadic_bound_f 3126068079 2147483648 3 2 1048576 282628 ep1251 ep58 ep1247 ep1252 ep61 ep1247 120432 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3126068079) qz16 0 2 ep1251 ep58 ep1247 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3126068079) qz282 0 2 ep1252 ep61 ep1247 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1254 := @Enclosure.Real.IsNear.sin_image qz213 qz491 Bool.false 108678381 262144 453 524288 Bool.true 120432 1048576 1 141176 (@Enclosure.Real.IsNear.recentre' qz213 Bool.false 466770092304197106117 1125899906842624000 544156250307287211 630250000000000000000 108678381 262144 453 524288 (ep1245 rfl) rfl) (Enclosure.sfrac_false_div 108678381 262144) (BSN.sin_reduce3 qz491 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 54994371245193111273472) qz598) 226375608064910080 72057594037927936 Bool.false 120432 1048576 65 1000000000000000 282352 141176 (BSN.sin_reduce_arg_pos_rat_q3 108678381 262144 226375608064910080 72057594037927936 65 54994371245193111273472 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 120432 1048576 54994371245193111273472 37778931862957161709568 3126068079 2147483648 282628 282352 (ep1253 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1255 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz136 (Real.cos qz213)) (@HMul.hMul Real Real Real qz0 qz136 (@Neg.neg Real Real.instNeg (Real.sin qz213))) Bool.false 49853480187 274877906944 776079053317 4850770423840768 Bool.false 1440991461 68719476736 386007465785 2425385211920384 (@Enclosure.Real.IsNear.mulLit_ff qz136 (Real.cos qz213) 191443 1048576 1 1048576 260409 262144 8059627 9252110336 49853480187 274877906944 776079053317 4850770423840768 qz438 (@Enclosure.Real.IsNear.recentre' (Real.cos qz213) Bool.false 1041636 1048576 64477016 74016882688 260409 262144 8059627 9252110336 (ep1250 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz136 (@Neg.neg Real Real.instNeg (Real.sin qz213)) 191443 1048576 1 1048576 7527 65536 8059627 9252110336 1440991461 68719476736 386007465785 2425385211920384 qz438 (@Enclosure.Real.IsNear.neg (Real.sin qz213) Bool.true 7527 65536 8059627 9252110336 (@Enclosure.Real.IsNear.recentre' (Real.sin qz213) Bool.true 120432 1048576 64477016 74016882688 7527 65536 8059627 9252110336 (ep1254 rfl rfl) rfl)) rfl)

noncomputable def ep1256 := @ep1172 49853480187 274877906944 776079053317 4850770423840768 Bool.false 1440991461 68719476736 386007465785 2425385211920384 Bool.false 274569205311980930334720 998876950005 1099511627776 145501917345191 19403081695363072 Bool.true 327416477640841756672 4764536827 137438953472 72763240005187 9701540847681536 (ep1173 (BSN.head_sum_c_succ qz146 29 30 rfl rfl) (ep1243 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1244 ep1255) rfl rfl

noncomputable def ep1257 := @Enclosure.Complex.IsNear.mul qz205 (@HAdd.hAdd Complex Complex Complex qz4 qz206 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz80 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz122 qz207 (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1))))) Bool.true ep1163 ep1038 ep1164 ep1040 Bool.false

noncomputable def ep1258 := nat_lit 12154115239941063850328064

noncomputable def ep1259 := nat_lit 5621445786038200078819899

noncomputable abbrev qz214 := (Complex.re qz484)

noncomputable abbrev qz215 := (Complex.im qz484)

noncomputable def ep1260 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 qz214 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz206 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz80 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz122 qz207 (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz215 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz206 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz80 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz122 qz207 (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1))))))) 806318496449401904165059 ep1258 ep1259

noncomputable def ep1261 := nat_lit 71494557213079984588913115136

noncomputable def ep1262 := nat_lit 53991916578939930095996029

noncomputable def ep1263 := nat_lit 58840616322132625766421427

noncomputable def ep1264 := nat_lit 5106754086648570327779508224000

noncomputable def ep1265 := nat_lit 5556267939096740524101494272899897695015042449145856

noncomputable def ep1266 := @Enclosure.Real.IsNear.mulLit_tf qz214 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz206 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz80 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz122 qz207 (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))))) 145798096943 1099511627776 3049400830869 19403081695363072 5530377373613

noncomputable abbrev qz492 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) qz596 (Real.log (Enclosure.sfrac Bool.false 31 1)))

noncomputable abbrev qz216 := (Real.cos qz492)

noncomputable abbrev qz217 := (Real.sin qz492)

noncomputable abbrev qz493 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 31)))

noncomputable abbrev qz603 := (@Neg.neg Real Real.instNeg qz217)

noncomputable def ep1267 := @Enclosure.Complex.IsNear.of_eq qz205 (Complex.mk (@HMul.hMul Real Real Real qz0 qz493 qz216) (@HMul.hMul Real Real Real qz0 qz493 qz603)) Bool.true 145798096943 1099511627776 3049400830869 19403081695363072 Bool.false 133192106999 1099511627776 3048219611277 19403081695363072 (BSN.cpow_neg_s_mk qz149 121891 1000 31 qz150 rfl)

noncomputable abbrev qz494 := (Real.sqrt (@Nat.cast Real Real.instNatCast 31))

noncomputable abbrev qz495 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 31) qz15)

noncomputable def ep1268 := @Enclosure.Real.IsNear.inv_image qz494 5838225 1048576 1 1048576 94164 94165 524288 (@Enclosure.Real.IsNear.of_eq qz494 (Real.sqrt qz495) Bool.false 5838225 1048576 1 1048576 (BSN.sqrt_natCast_div_one 31) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz495) Bool.false 5838225 1048576 1 1048576 5838225 1048576 1 1048576 (BSN.sqrt_enclosure 31 1 2919112 2919113 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep1269 := BSN.log_dyadic_bound 15 47 6 5 546767979591453359355 524288 141176 19788004106328479625 544934619140625 346763 62 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 15) (BSN.artanhQ 47) 0 5 19788004106328479625 546767979591453359355 544934619140625 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep1270 := @Enclosure.Real.IsNear.mulLit_ff qz149 (Real.log (Enclosure.sfrac Bool.false 31 1)) 121891 1000 0 1 3866325256314103 1125899906842624 31250000017647 4411750000000000000 471270251817382328773 1125899906842624000 544156250307287211 630250000000000000000 qz151 (BSN.isNear_log_sfrac 31 1 3866325256314103 1125899906842624 31250000017647 4411750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz495) Bool.false 64866173951437069877248 18889465931478580854784 1000000000564704 141176000000000000000 3866325256314103 1125899906842624 31250000017647 4411750000000000000 (BSN.log_rat_reduce_isNear 31 1 4 62 32 346763 524288 24973259072661432 36028797018963968 141176 1000000000000000 rfl rfl rfl rfl (ep1269 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1271 := nat_lit 228205541079259483850692834232571074102045601213980840977663147152238006735681

noncomputable def ep1272 := nat_lit 40779289599725115262156894337569722948699637278969524087749479429258580801

noncomputable def ep1273 := nat_lit 684535064658579001321554188909038082860239404367384583884813942497855503045441

noncomputable def ep1274 := BSN.cos_dyadic_bound_f 1589662601 2147483648 3 2 1048576 282628 ep1271 ep58 ep1272 ep1273 ep61 ep1272 774167 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1589662601) qz16 0 2 ep1271 ep58 ep1272 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1589662601) qz282 0 2 ep1273 ep61 ep1272 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz218 := qz492

noncomputable abbrev qz496 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 27431539) (@Nat.cast Real Real.instNatCast 65536))

noncomputable def ep1275 := @Enclosure.Real.IsNear.cos_image qz218 qz496 Bool.false 27431539 65536 453 524288 Bool.true 774167 1048576 1 141176 (@Enclosure.Real.IsNear.recentre' qz218 Bool.false 471270251817382328773 1125899906842624000 544156250307287211 630250000000000000000 27431539 65536 453 524288 (ep1270 rfl) rfl) (Enclosure.sfrac_false_div 27431539 65536) (BSN.cos_reduce2 qz496 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 6991410057417408380928) qz432) 226375608064910080 72057594037927936 Bool.false 774167 1048576 66 1000000000000000 282352 141176 (BSN.sin_reduce_arg_pos_rat_q2 27431539 65536 226375608064910080 72057594037927936 66 6991410057417408380928 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 774167 1048576 6991410057417408380928 9444732965739290427392 1589662601 2147483648 282628 282352 (ep1274 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1276 := nat_lit 6385866393820427814146705444495210401

noncomputable def ep1277 := BSN.sin_dyadic_bound_f 1589662601 2147483648 2 1 1048576 282628 ep1276 ep144 ep1276 ep1276 ep145 ep1276 707231 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1589662601) qz21 0 1 ep1276 ep144 ep1276 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1589662601) qz285 0 1 ep1276 ep145 ep1276 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1278 := @Enclosure.Real.IsNear.sin_image qz218 qz496 Bool.false 27431539 65536 453 524288 Bool.true 707231 1048576 1 141176 (@Enclosure.Real.IsNear.recentre' qz218 Bool.false 471270251817382328773 1125899906842624000 544156250307287211 630250000000000000000 27431539 65536 453 524288 (ep1270 rfl) rfl) (Enclosure.sfrac_false_div 27431539 65536) (BSN.sin_reduce2 qz496 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 6991410057417408380928) qz432) 226375608064910080 72057594037927936 Bool.false 707231 1048576 66 1000000000000000 282352 141176 (BSN.sin_reduce_arg_pos_rat_q2 27431539 65536 226375608064910080 72057594037927936 66 6991410057417408380928 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 707231 1048576 6991410057417408380928 9444732965739290427392 1589662601 2147483648 282628 282352 (ep1277 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1279 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz493 qz216) (@HMul.hMul Real Real Real qz0 qz493 qz603) Bool.true 145798096943 1099511627776 3049400830869 19403081695363072 Bool.false 133192106999 1099511627776 3048219611277 19403081695363072 (@Enclosure.Real.IsNear.mulLit_ft qz493 qz216 188329 1048576 1 1048576 774167 1048576 8059627 9252110336 145798096943 1099511627776 3049400830869 19403081695363072 (@Enclosure.Real.IsNear.recentre' qz493 Bool.false 188329 1048576 1 1048576 188329 1048576 1 1048576 (ep1268 rfl rfl) rfl) (@Enclosure.Real.IsNear.recentre' qz216 Bool.true 774167 1048576 64477016 74016882688 774167 1048576 8059627 9252110336 (ep1275 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz493 qz603 188329 1048576 1 1048576 707231 1048576 8059627 9252110336 133192106999 1099511627776 3048219611277 19403081695363072 (@Enclosure.Real.IsNear.recentre' qz493 Bool.false 188329 1048576 1 1048576 188329 1048576 1 1048576 (ep1268 rfl rfl) rfl) (@Enclosure.Real.IsNear.neg qz217 Bool.true 707231 1048576 8059627 9252110336 (@Enclosure.Real.IsNear.recentre' qz217 Bool.true 707231 1048576 64477016 74016882688 707231 1048576 8059627 9252110336 (ep1278 rfl rfl) rfl)) rfl)

noncomputable def ep1280 := @ep1266 11054103415464 0 1 806318496449401904165059 ep1258 ep1259 ep1261 (@Enclosure.Complex.IsNear.re_isNear qz205 Bool.true 145798096943 1099511627776 3049400830869 19403081695363072 Bool.false 133192106999 1099511627776 3048219611277 19403081695363072 (ep1267 ep1279))

noncomputable def ep1281 := @Enclosure.Complex.IsNear.re_isNear (@HAdd.hAdd Complex Complex Complex qz4 qz206 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz80 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz122 qz207 (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1))))) Bool.false 5530377373613 11054103415464 0 1 Bool.false

noncomputable def ep1282 := @Enclosure.Complex.IsNear.addLitP qz206 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz80 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz122 qz207 (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) Bool.false 14826665881 29715331762 0 1 Bool.true 3778621000

noncomputable def ep1283 := @ep1282 14857665881 0 1 Bool.false 1 744 0 1 Bool.false 121891 372000 0 1 Bool.false 11060754747226 5530377373613 11054103415464 0 1 Bool.false 405368739900971 405368739900971 5527051707732000 0 1

noncomputable abbrev qz219 := (@HDiv.hDiv Complex Complex Complex qz386 qz485 (@HSub.hSub Complex Complex Complex qz378 qz439 (1 : Complex)))

noncomputable def ep1284 := @Enclosure.Complex.IsNear.addLitP qz219 qz97 Bool.true 62000000 59430663524 0 1 Bool.true 15114484000 59430663524 0 1

noncomputable def ep1285 := @Enclosure.Complex.IsNear.of_eq qz219 (Complex.mk (Enclosure.sfrac Bool.true 62000000 59430663524) (Enclosure.sfrac Bool.true 15114484000 59430663524)) Bool.true 62000000 59430663524 0 1 Bool.true 15114484000 59430663524 0 1

noncomputable def ep1286 := @ep1284 Bool.false 1 2 0 1 Bool.false 0 1 0 1 Bool.false 59306663524 14826665881 29715331762 0 1 Bool.true 15114484000 3778621000 14857665881 0 1 (ep1285 (BSN.N_div_s_sub_one_mk qz149 121891 1000 31 qz150 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 62000000 59430663524) (Enclosure.sfrac Bool.true 15114484000 59430663524) Bool.true 62000000 59430663524 0 1 Bool.true 15114484000 59430663524 0 1 (Enclosure.Real.IsNear.const Bool.true 62000000 59430663524) (Enclosure.Real.IsNear.const Bool.true 15114484000 59430663524))) qz98 rfl

noncomputable abbrev qz220 := (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz412 qz485 1))

noncomputable def ep1287 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz80 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz122 qz207 (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) (@HAdd.hAdd Complex Complex Complex qz4 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz80 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz122 qz207 (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz99)) ↑qz142) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1))) qz220)) Bool.false 1 744 0 1

noncomputable def ep1288 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz80 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz122 qz207 (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz99)) ↑qz142) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1))) qz220) Bool.false 0 1 0 1 Bool.false

noncomputable def ep1289 := @ep1288 0 1 0 1 Bool.false 1 744 0 1 Bool.false 121891 372000 0 1 Bool.false 1 1 744 0 1 Bool.false 121891 121891 372000 0

noncomputable def ep1290 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz80 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz122 qz207 (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) (Complex.mk qz10 qz10) Bool.false 0 1 0 1 Bool.false

noncomputable def ep1291 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz99)) ↑qz142) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1))) qz220 Bool.false 1 744 0 1 Bool.false 121891 372000 0 1

noncomputable def ep1292 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz99)) ↑qz142) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz220)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz99)) ↑qz142) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz220)) 1 744 0 1 0 1 0

noncomputable def ep1293 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz99)) ↑qz142) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz220) 1 24 0 1 1 31 0 1 1

noncomputable def ep1294 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz99)) ↑qz142)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz99)) ↑qz142)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1)))) 1 24 0 1 0 1 0 1 1

noncomputable def ep1295 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz99)) ↑qz142)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 1 2 0 1 1 24 0

noncomputable def ep1296 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1)) qz146 Bool.false 1 2 0 1 Bool.false 121891 1000 0 1 (BSN.ascPochhammer_one_eval qz146)

noncomputable def ep1297 := ep1296 (@Enclosure.Complex.IsNear.of_eq qz146 (Complex.mk qz92 qz149) Bool.false 1 2 0 1 Bool.false 121891 1000 0 1 (BSN.s_crit_mk qz149 Bool.false 121891 1000 qz150) (@Enclosure.Complex.IsNear.mk qz92 qz149 Bool.false 1 2 0 1 Bool.false 121891 1000 0 1 qz392 qz151))

noncomputable def ep1298 := @ep1295 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz99)) ↑qz142) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep676) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 121891 1000 0 1 ep1297)

noncomputable def ep1299 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz99)) ↑qz142)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 121891 1000 0 1 0 1 0

noncomputable def ep1300 := @ep1299 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz99)) ↑qz142) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep676) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 121891 1000 0 1 ep1297)

noncomputable def ep1301 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz99)) ↑qz142)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz99)) ↑qz142)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1)))) 121891 12000 0 1 0 1 0 1 121891

noncomputable def ep1302 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz99)) ↑qz142)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 121891 1000 0 1 121891 12000 0

noncomputable def ep1303 := @ep1302 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz99)) ↑qz142) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep676) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 121891 1000 0 1 ep1297)

noncomputable def ep1304 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz99)) ↑qz142)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 1 2 0 1 0 1 0

noncomputable def ep1305 := @ep1304 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz99)) ↑qz142) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep676) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 121891 1000 0 1 ep1297)

noncomputable def ep1306 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz99)) ↑qz142) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 24 0 1 Bool.false 121891 12000 0 1 (@ep1294 1 24 0 1 (ep1298 rfl) (ep1300 rfl) rfl rfl) (@ep1301 121891 12000 0 1 (ep1303 rfl) (ep1305 rfl) rfl rfl)

noncomputable def ep1307 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz99)) ↑qz142) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 121891 12000 0 1 ep1306

noncomputable abbrev qz221 := (@Enclosure.Complex.IsNear.of_eq (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz412 qz485 1)) (Complex.mk (Enclosure.sfrac Bool.false 1 31) qz278) Bool.false 1 31 0 1 Bool.false 0 1 0 1 (BSN.natCast_pow_inv_mk 31 1 31 EMRow39.d15 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 31) qz278 Bool.false 1 31 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 31) qz287))

noncomputable def ep1308 := @ep1293 744 0 1 ep1307 (@Enclosure.Complex.IsNear.re_isNear qz220 Bool.false 1 31 0 1 Bool.false 0 1 0 1 qz221)

noncomputable def ep1309 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz99)) ↑qz142) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz220) 121891 12000 0 1 0 1 0 1 0

noncomputable def ep1310 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz99)) ↑qz142) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 121891 12000 0 1 ep1306

noncomputable def ep1311 := @ep1309 1 0 1 ep1310 (@Enclosure.Complex.IsNear.im_isNear qz220 Bool.false 1 31 0 1 Bool.false 0 1 0 1 qz221)

noncomputable def ep1312 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz99)) ↑qz142) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz220)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz99)) ↑qz142) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz220)) 0 1 0 1 121891 372000 0

noncomputable def ep1313 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz99)) ↑qz142) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz220) 1 24 0 1 0 1 0 1 0

noncomputable def ep1314 := @ep1313 1 0 1 ep1307 (@Enclosure.Complex.IsNear.im_isNear qz220 Bool.false 1 31 0 1 Bool.false 0 1 0 1 qz221)

noncomputable def ep1315 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz99)) ↑qz142) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz220) 121891 12000 0 1 1 31 0 1 121891

noncomputable def ep1316 := @ep1315 372000 0 1 ep1310 (@Enclosure.Complex.IsNear.re_isNear qz220 Bool.false 1 31 0 1 Bool.false 0 1 0 1 qz221)

noncomputable def ep1317 := @ep1289 1 (@ep1290 0 1 0 1 (BSN.bern_sum_base qz146 31) qz113) (ep1291 (@ep1292 1 1 1 744 0 1 (ep1308 rfl) (ep1311 rfl) rfl rfl) (@ep1312 1 121891 121891 372000 0 1 (ep1314 rfl) (ep1316 rfl) rfl rfl)) rfl rfl rfl rfl rfl

noncomputable def ep1318 := ep1283 (ep1286 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep1287 Bool.false 121891 372000 0 1 (BSN.bern_sum_succ qz146 31 0 1 1 rfl rfl) (ep1317 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl rfl

noncomputable def ep1319 := @Enclosure.Real.IsNear.mulLit_ff qz215 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz206 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz80 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz122 qz207 (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))))) 133192106999 1099511627776 3048219611277 19403081695363072 405368739900971

noncomputable def ep1320 := @ep1319 5527051707732000 0 1 ep1262 ep1159 ep1263 ep1264 (@Enclosure.Complex.IsNear.im_isNear qz205 Bool.true 145798096943 1099511627776 3049400830869 19403081695363072 Bool.false 133192106999 1099511627776 3048219611277 19403081695363072 (ep1267 ep1279))

noncomputable def ep1321 := @Enclosure.Complex.IsNear.im_isNear (@HAdd.hAdd Complex Complex Complex qz4 qz206 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz80 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz122 qz207 (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1))))) Bool.false 5530377373613 11054103415464 0 1 Bool.false

noncomputable def ep1322 := nat_lit 59101990837743522077831653

noncomputable def ep1323 := nat_lit 58863417726778120008565419

noncomputable def ep1324 := @Enclosure.Real.IsNear.addLit_tf_p (@HMul.hMul Real Real Real qz0 qz214 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz206 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz80 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz122 qz207 (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz215 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz206 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz80 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz122 qz207 (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1))))))) ep1322 ep1159 ep1323

noncomputable def ep1325 := nat_lit 5619268256003245019011267

noncomputable def ep1326 := nat_lit 3758044126162371440769382722958767853706087610974208

noncomputable def ep1327 := @Enclosure.Real.IsNear.mulLit_tf qz214 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz206 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz80 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz122 qz207 (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))))) 145798096943 1099511627776 3049400830869 19403081695363072 405368739900971

noncomputable def ep1328 := @ep1327 5527051707732000 0 1 ep1322 ep1159 ep1323 ep1264 (@Enclosure.Complex.IsNear.re_isNear qz205 Bool.true 145798096943 1099511627776 3049400830869 19403081695363072 Bool.false 133192106999 1099511627776 3048219611277 19403081695363072 (ep1267 ep1279))

noncomputable def ep1329 := @Enclosure.Real.IsNear.mulLit_ff qz215 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz206 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz80 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz122 qz207 (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))))) 133192106999 1099511627776 3048219611277 19403081695363072 5530377373613

noncomputable def ep1330 := @ep1329 11054103415464 0 1 736602614891111295217387 ep1258 ep1325 ep1261 (@Enclosure.Complex.IsNear.im_isNear qz205 Bool.true 145798096943 1099511627776 3049400830869 19403081695363072 Bool.false 133192106999 1099511627776 3048219611277 19403081695363072 (ep1267 ep1279))

noncomputable abbrev qz604 := (ep1318 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable def ep1331 := @ep1257 ep1165 ep1159 ep1166 ep1040 (@ep1260 ep1261 ep1262 ep1159 ep1263 ep1264 ep1265 ep1163 ep1038 ep1164 ep1040 (ep1280 (@ep1281 405368739900971 5527051707732000 0 1 qz604) rfl) (ep1320 (@ep1321 405368739900971 5527051707732000 0 1 qz604) rfl) rfl rfl) (@ep1324 ep1264 736602614891111295217387 ep1258 ep1325 ep1261 ep1326 ep1165 ep1159 ep1166 ep1040 (ep1328 (@ep1321 405368739900971 5527051707732000 0 1 qz604) rfl) (ep1330 (@ep1281 405368739900971 5527051707732000 0 1 qz604) rfl) rfl rfl)

noncomputable def ep1332 := @ep1169 ep1160 ep1040 (@ep1170 9701540847681536 (BSN.head_sum_c_eq qz146 31) (ep1171 (BSN.head_sum_c_succ qz146 30 31 rfl rfl) (ep1256 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))) ep1331 rfl rfl rfl

noncomputable def ep1333 := @Enclosure.Complex.IsNear.re_isNear (zetaApproximant qz146 1 31) Bool.false ep1037 ep1038 ep1039 ep1040 Bool.false ep1158 ep1159 ep1160 ep1040 (@ep1161 ep1040 Bool.false ep1158 ep1159 ep1160 ep1040 (BSN.zetaApproximant_eq_folded' qz146 1 31 rfl) (ep1332 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

noncomputable def ep1334 := @Enclosure.Real.IsNear.mulLit_ff (Real.sin (@HSub.hSub Real Real Real qz381 (Complex.im (@HSub.hSub Complex Complex Complex qz73 qz176 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz177 (@Nat.cast Complex Complex.instNatCast j))))) qz178)) (Complex.im (zetaApproximant qz146 1 31)) 109 1048576 1673939

noncomputable def ep1335 := @Enclosure.Real.IsNear.recentre' (Real.sin (@HSub.hSub Real Real Real qz381 (Complex.im (@HSub.hSub Complex Complex Complex qz73 qz176 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz177 (@Nat.cast Complex Complex.instNatCast j))))) qz178)) Bool.false 109 1048576 13391512

noncomputable def ep1336 := @Enclosure.Real.IsNear.sin_image (@HSub.hSub Real Real Real qz381 (Complex.im (@HSub.hSub Complex Complex Complex qz73 qz176 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz177 (@Nat.cast Complex Complex.instNatCast j))))) qz178) qz468 Bool.false 125179659 1048576 93

noncomputable def ep1337 := BSN.sin_dyadic_bound_f 225246 2147483648 1 0 1048576 282628 0 1 1 0 1 1 109 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 225246) qz21 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 225246) qz285 0 0 rfl) rfl rfl

noncomputable def ep1338 := @ep1336 262144 Bool.false 109 1048576 1 141176 (@ep1045 125179659 1048576 93 262144 ep1155 rfl) (Enclosure.sfrac_false_div 125179659 1048576) (BSN.sin_reduce0 qz468 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 15850283896634605568) qz20) 226375608064910080 72057594037927936 Bool.false 109 1048576 19 1000000000000000 282352 141176 (BSN.sin_reduce_arg_pos_rat_q0 125179659 1048576 226375608064910080 72057594037927936 19 15850283896634605568 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 109 1048576 15850283896634605568 151115727451828646838272 225246 2147483648 282628 282352 (ep1337 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1339 := @Enclosure.Complex.IsNear.im_isNear (zetaApproximant qz146 1 31) Bool.false ep1037 ep1038 ep1039 ep1040 Bool.false ep1158 ep1159 ep1160 ep1040 (@ep1161 ep1040 Bool.false ep1158 ep1159 ep1160 ep1040 (BSN.zetaApproximant_eq_folded' qz146 1 31 rfl) (ep1332 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

theorem EMRow39.d16 : Enclosure.Real.IsNear (hardyZApproximantEM 1 31 qz149) Bool.false ep1020 ep1021 ep1022 ep1023 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantEM 1 31 qz149) ep1024 Bool.false ep1020 ep1021 ep1022 ep1023 (@Eq.refl Real ep1024) (@ep1025 Bool.false ep1020 ep1021 ep1022 ep1023 (BSN.re_exp_mul (@HSub.hSub Real Real Real qz381 (Complex.im (@HSub.hSub Complex Complex Complex qz73 qz176 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz177 (@Nat.cast Complex Complex.instNatCast j))))) qz178) (zetaApproximant qz146 1 31)) (@ep1027 ep1028 ep1029 ep1030 ep1031 ep1032 ep1033 ep1034 ep1035 ep1020 ep1021 ep1022 ep1023 (@ep1036 4626055168 ep1037 ep1038 ep1039 ep1040 ep1026 ep1028 ep1029 ep1030 (@ep1041 37008441344 1048575 1048576 1673939 4626055168 (ep1157 rfl rfl) rfl) ep1333 rfl) (@ep1334 4626055168 ep1158 ep1159 ep1160 ep1040 ep1031 ep1032 ep1033 ep1034 (@ep1335 37008441344 109 1048576 1673939 4626055168 (ep1338 rfl rfl) rfl) ep1339 rfl) rfl rfl))

theorem EMRow39.d17 : @Eq Nat (Nat.mul (BSN.factNat (Nat.succ (Nat.mul 2 1))) (Nat.pow 4 (Nat.mul 2 1))) 96 := @Eq.refl Nat 96

theorem EMRow39.d18 : @Eq Nat (Nat.mul (Nat.mul 2 1) (Nat.pow (Nat.succ (Nat.mul 4 2)) (Nat.mul 2 1))) 162 := @Eq.refl Nat 162

theorem EMRow39.d19 : @Eq Nat (BSN.factNat (Nat.mul 2 2)) 24 := @Eq.refl Nat 24

theorem EMRow39.d20 : @Eq Nat (Nat.pow 30 (Nat.succ (Nat.mul 2 3))) 21870000000 := @Eq.refl Nat 21870000000

noncomputable abbrev qz605 := (@HAdd.hAdd Complex Complex Complex qz610 qz609 (@Nat.cast Complex Complex.instNatCast 3))

noncomputable abbrev qz497 := qz605

noncomputable abbrev qz222 := (@HDiv.hDiv Real Real Real qz271 (@Norm.norm Complex Complex.instNorm qz497) (@HAdd.hAdd Real Real Real qz402 (Complex.re qz272) qz547))

noncomputable abbrev qz223 := (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 2)

noncomputable abbrev qz224 := (@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 2)))

noncomputable abbrev qz498 := (@HPow.hPow Complex Complex Complex qz536 (@Nat.cast Complex Complex.instNatCast 30) (@HSub.hSub Complex Complex Complex qz572 qz537 qz543))

noncomputable abbrev qz225 := qz498

noncomputable def ep1340 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 30))) (@HMul.hMul Real Real Real qz0 qz222 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225))) 76303670531 1855425871872 208117345 1855425871872 278679421237348797 504403158265495552 79987656083

noncomputable def ep1341 := nat_lit 555556820525178466748749316096

noncomputable def ep1342 := @Enclosure.Real.IsNear.mulLit_ff (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 30)) 26561 1769472 1 1769472 2872771 1048576 7727 1048576 76303670531 1855425871872

noncomputable abbrev qz226 := (@HMul.hMul Real Real Real qz268 (2 : Real) Real.pi)

noncomputable abbrev qz606 := (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid)))

noncomputable abbrev qz499 := (@Inv.inv Real Real.instInv (@HPow.hPow Real Nat Real qz606 qz226 2))

noncomputable def ep1343 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 96 162) qz499 96 162 0 1 26561 1048576 1 1048576 26561 1769472 1 1769472

noncomputable def ep1344 := nat_lit 781950621441006189802102638025

noncomputable def ep1345 := nat_lit 19807040628566084398385987584

noncomputable def ep1346 := nat_lit 26986075409044041160201671

noncomputable def ep1347 := nat_lit 1073741824000000000000000000000000000000

noncomputable abbrev qz500 := (@HPow.hPow Real Nat Real qz606 qz226 1)

noncomputable def ep1348 := @Enclosure.Real.IsNear.mulLit_ff qz500 qz226 884279719003555 140737488355328 1 500000000000000 884279719003555 140737488355328 1 500000000000000 ep1344 ep1345 ep1346 ep1347

noncomputable def ep1349 := ep1348 (@Enclosure.Real.IsNear.of_eq qz500 qz226 Bool.false 884279719003555 140737488355328 1 500000000000000 (BSN.pow_one_r qz226) (@Enclosure.Real.IsNear.of_eq qz226 qz269 Bool.false 884279719003555 140737488355328 1 500000000000000 BSN.two_pi_eq qz270)) (@Enclosure.Real.IsNear.of_eq qz226 qz269 Bool.false 884279719003555 140737488355328 1 500000000000000 BSN.two_pi_eq qz270) rfl

noncomputable abbrev qz501 := (@HPow.hPow Real Nat Real qz606 qz226 2)

noncomputable def ep1350 := @Enclosure.Real.IsNear.inv_image qz501 ep1344 ep1345 ep1346 ep1347 13280 13281 524288 (@Enclosure.Real.IsNear.of_eq qz501 (@HMul.hMul Real Real Real qz0 qz500 qz226) Bool.false ep1344 ep1345 ep1346 ep1347 (BSN.pow_succ_r qz226 1 2 rfl) ep1349) rfl rfl rfl

noncomputable def ep1351 := ep1343 (Enclosure.Real.IsNear.const Bool.false 96 162) (@Enclosure.Real.IsNear.recentre' qz499 Bool.false 26561 1048576 1 1048576 26561 1048576 1 1048576 (ep1350 rfl rfl rfl) rfl)

noncomputable def ep1352 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 30)) (Real.sqrt (@HAdd.hAdd Real Real Real qz402 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz5 1 30)) (Complex.re (zetaApproximant qz5 1 30))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz5 1 30)) (Complex.im (zetaApproximant qz5 1 30))))) Bool.false 2872771 1048576 7727 1048576

noncomputable def ep1353 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz402 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz5 1 30)) (Complex.re (zetaApproximant qz5 1 30))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz5 1 30)) (Complex.im (zetaApproximant qz5 1 30))))) Bool.false 2872771 1048576 7727 1048576

noncomputable def ep1354 := nat_lit 8434406838413464098624310779137200037288137

noncomputable def ep1355 := nat_lit 1123697250737018389117553909766606028800000

noncomputable def ep1356 := nat_lit 703647112173770628434029994802183481018511327341864547162507

noncomputable def ep1357 := nat_lit 17429031758394539755563554548654880904947018561381990400000000

noncomputable def ep1358 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz402 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz5 1 30)) (Complex.re (zetaApproximant qz5 1 30))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz5 1 30)) (Complex.im (zetaApproximant qz5 1 30)))) ep1354 ep1355 ep1356 ep1357 1432522 1440249

noncomputable def ep1359 := nat_lit 151225315844779757130401995780295320993152293529116761

noncomputable def ep1360 := nat_lit 20148095033113774326670160477907448814911881216000000

noncomputable def ep1361 := nat_lit 2095967728264283740106485497773080627445656459930401103312433

noncomputable def ep1362 := nat_lit 52287095275183619266690663645964642714841055684145971200000000

noncomputable def ep1363 := nat_lit 80077058109857534269094774196979001324218481761

noncomputable def ep1364 := nat_lit 314813984892402723854221257467303887732998144000000

noncomputable def ep1365 := nat_lit 935850516064259074725280414591863475617345130949533635943

noncomputable def ep1366 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz5 1 30)) (Complex.re (zetaApproximant qz5 1 30))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz5 1 30)) (Complex.im (zetaApproximant qz5 1 30))) ep1359 ep1360 ep1361 ep1362 ep1363 ep1364 ep1365

noncomputable def ep1367 := nat_lit 3267943454698976204168166477872790169677565980259123200000000

noncomputable def ep1368 := nat_lit 47609457697884094304038552825473179081401816610588201976656445494248881610860656852376654666792960000000

noncomputable def ep1369 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (zetaApproximant qz5 1 30)) (Complex.re (zetaApproximant qz5 1 30)) ep421 ep422 ep423 ep424 ep421 ep422 ep423 ep424 ep1359

noncomputable def ep1370 := @Enclosure.Real.IsNear.mulLit_tt (Complex.im (zetaApproximant qz5 1 30)) (Complex.im (zetaApproximant qz5 1 30)) 282978900467610012708431 ep553 ep554 ep555 282978900467610012708431 ep553 ep554 ep555 ep1363

noncomputable def ep1371 := @ep1340 504403158265495552 ep1341 8084415756823414511 13618885273168379904 1529747638769281 13618885273168379904 (@ep1342 208117345 1855425871872 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaStirlingErrorBound 1 2) (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 96 162) qz499) Bool.false 26561 1769472 1 1769472 (BSN.theta_err_eq 1 2 96 162 EMRow39.d17 EMRow39.d18 rfl) (ep1351 rfl)) (ep1352 (BSN.norm_eq_sqrt_mul_add (zetaApproximant qz5 1 30)) (@ep1353 2872771 1048576 7727 1048576 (@ep1358 524288 (@ep1366 ep1367 ep1368 ep1354 ep1355 ep1356 ep1357 (@ep1369 ep1360 ep1361 ep1362 ep716 ep716 rfl) (@ep1370 ep1364 ep1365 ep1367 ep722 ep722 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl)

noncomputable abbrev qz227 := (@Norm.norm Complex Complex.instNorm qz497)

noncomputable abbrev qz607 := (Enclosure.sfrac Bool.false 2 7)

noncomputable def ep1372 := @Enclosure.Real.IsNear.of_eq (@HMul.hMul Real Real Real qz0 qz222 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225))) (@HMul.hMul Real Real Real qz0 (@HMul.hMul Real Real Real qz0 qz227 qz607) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225))) Bool.false 278679421237348797 504403158265495552 79987656083 504403158265495552 (BSN.zrb_shape_eq qz227 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)) qz13 3)

noncomputable def ep1373 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz0 qz227 qz607) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)) 125637367 3670016 1 3670016 2218125291 137438953472 619 137438953472

noncomputable def ep1374 := @Enclosure.Real.IsNear.mulLit_ff qz227 qz607 125637367 1048576 1 1048576 2 7 0 1 125637367 3670016

noncomputable abbrev qz502 := (Complex.re qz605)

noncomputable abbrev qz503 := (Complex.im qz605)

noncomputable abbrev qz228 := (@HAdd.hAdd Real Real Real qz402 (@HMul.hMul Real Real Real qz268 qz502 qz502) (@HMul.hMul Real Real Real qz268 qz503 qz503))

noncomputable abbrev qz229 := qz497

noncomputable def ep1375 := @Enclosure.Real.IsNear.of_eq qz227 (Real.sqrt qz228) Bool.false 125637367 1048576 1 1048576 (BSN.norm_eq_sqrt_mul_add qz229)

noncomputable def ep1376 := @Enclosure.Real.IsNear.recentre' (Real.sqrt qz228) Bool.false 125637367 1048576 1 1048576 125637367

noncomputable def ep1377 := @Enclosure.Real.IsNear.sqrt_image qz228 3589036189 250000 0 1 62818683 62818684 524288

noncomputable abbrev qz230 := (@HMul.hMul Real Real Real qz268 qz502 qz502)

noncomputable abbrev qz231 := (@HMul.hMul Real Real Real qz268 qz503 qz503)

noncomputable def ep1378 := @Enclosure.Real.IsNear.addLit_ff qz230 qz231 49 4 0 1 3585973689 250000 0 1

noncomputable abbrev qz232 := qz502

noncomputable def ep1379 := @Enclosure.Real.IsNear.mulLit_ff qz232 qz232 7 2 0 1 7 2 0 1 49 4

noncomputable abbrev qz504 := (Enclosure.sfrac Bool.false 7 2)

noncomputable def ep1380 := @Enclosure.Complex.IsNear.of_eq qz229 (Complex.mk qz504 qz13) Bool.false 7 2 0 1 Bool.false 119766 1000 0 1 (BSN.s_add_nat_mk qz13 Bool.false 119766 1000 3 qz14)

noncomputable abbrev qz505 := (ep1380 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7 2) qz13 Bool.false 7 2 0 1 Bool.false 119766 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 7 2) qz19))

noncomputable def ep1381 := @ep1379 0 1 (@Enclosure.Complex.IsNear.re_isNear qz229 Bool.false 7 2 0 1 Bool.false 119766 1000 0 1 qz505)

noncomputable def ep1382 := ep1381 (@Enclosure.Complex.IsNear.re_isNear qz229 Bool.false 7 2 0 1 Bool.false 119766 1000 0 1 qz505)

noncomputable abbrev qz233 := qz503

noncomputable def ep1383 := @Enclosure.Real.IsNear.mulLit_ff qz233 qz233 119766 1000 0 1 119766 1000 0 1 3585973689 250000

noncomputable def ep1384 := @ep1383 0 1 (@Enclosure.Complex.IsNear.im_isNear qz229 Bool.false 7 2 0 1 Bool.false 119766 1000 0 1 qz505)

noncomputable def ep1385 := ep1384 (@Enclosure.Complex.IsNear.im_isNear qz229 Bool.false 7 2 0 1 Bool.false 119766 1000 0 1 qz505)

noncomputable def ep1386 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)) (Real.sqrt (@HAdd.hAdd Real Real Real qz402 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)) (Complex.re (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)) (Complex.im (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225))))) Bool.false 2218125291 137438953472

noncomputable def ep1387 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz402 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)) (Complex.re (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)) (Complex.im (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225))))) Bool.false 8872501164 549755813888

noncomputable def ep1388 := nat_lit 1189602302431598699237206939136568199990396427696882296041271033

noncomputable def ep1389 := nat_lit 4567192616659071619386515102238384436424789196800000000000000000000

noncomputable def ep1390 := nat_lit 10810134202042957856007933457216977850959283481721011452725285659089080031

noncomputable def ep1391 := nat_lit 74391804213335862226915764320255319402377330986089185280000000000000000000000000000

noncomputable def ep1392 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz402 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)) (Complex.re (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)) (Complex.im (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)))) ep1388 ep1389 ep1390 ep1391

noncomputable def ep1393 := nat_lit 1731052544081014815326138446839873861465498072950297315482596841

noncomputable def ep1394 := nat_lit 9134385233318143238773030204476768872849578393600000000000000000000

noncomputable def ep1395 := nat_lit 15896023266532048291667159645230064843816232677803730345443071492023535031

noncomputable def ep1396 := nat_lit 148783608426671724453831528640510638804754661972178370560000000000000000000000000000

noncomputable def ep1397 := nat_lit 25926082431287303325931017257330501540611791297738691063997809

noncomputable def ep1398 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)) (Complex.re (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)) (Complex.im (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225))) ep1393 ep1394 ep1395 ep1396 ep1397

noncomputable def ep1399 := nat_lit 365375409332725729550921208179070754913983135744000000000000000000

noncomputable def ep1400 := nat_lit 5724245137553867420348707269203890858102334285638292560007499826154625031

noncomputable def ep1401 := nat_lit 869302856388196726419343521904067621549575512719102115407091083076768216526204292458363471731896596761468207104000000000000000000

noncomputable def ep1402 := nat_lit 41605919579802761707473592437971

noncomputable def ep1403 := nat_lit 3022314549036572936765440000000000

noncomputable def ep1404 := nat_lit 1496805690926150269741549406977841

noncomputable def ep1405 := nat_lit 385724783267385768912774758400000000000000

noncomputable def ep1406 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)) (Complex.re (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)) ep1402 ep1403 ep1404 ep1405 ep1402 ep1403 ep1404

noncomputable def ep1407 := nat_lit 5091766140671358771936872051303

noncomputable def ep1408 := nat_lit 604462909807314587353088000000000

noncomputable def ep1409 := nat_lit 880870030430018773004059230570341

noncomputable def ep1410 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225) Bool.true ep1402 ep1403 ep1404 ep1405 Bool.false ep1407 ep1408 ep1409

noncomputable def ep1411 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225 Bool.true ep1402 ep1403 ep1404 ep1405 Bool.false ep1407 ep1408 ep1409 ep1405

noncomputable def ep1412 := nat_lit 717503429679928605677010219

noncomputable def ep1413 := nat_lit 2417851639229258349412352000000

noncomputable def ep1414 := nat_lit 2607245733738174309843205740853

noncomputable def ep1415 := nat_lit 32400881794460404588673079705600000000000

noncomputable def ep1416 := nat_lit 42502798866902672464569855211721

noncomputable def ep1417 := nat_lit 30781108076014612087111736111321411

noncomputable abbrev qz234 := (Complex.re qz498)

noncomputable abbrev qz235 := (Complex.im qz498)

noncomputable def ep1418 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz234) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz235) ep1412 ep1413 ep1414 ep1415 ep1416 ep1403 ep1417

noncomputable def ep1419 := nat_lit 8100220448615101147168269926400000000000000

noncomputable def ep1420 := nat_lit 100596940857666803139790103070632833343497267158861217792000000

noncomputable def ep1421 := nat_lit 270007348287170038238942330880000

noncomputable def ep1422 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz234 10757608567 120000000 0 1 1000459477417136355 302231454903657293676544 242362948744589166259 ep1421 ep1412

noncomputable def ep1423 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) 10757608567 120000000 0 1 0 1 0 1 10757608567

noncomputable def ep1424 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 32272825701 500000 0 1 10757608567 120000000 0

noncomputable def ep1425 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (Complex.mk (Enclosure.sfrac Bool.true 1 720) qz10) Bool.true 1 720 0 1 Bool.false 0 1 0 1 (BSN.bern_coeff_mk 2 1 30 24 Bool.true BSN.bern_real_2 EMRow39.d19 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 1 720) qz10 Bool.true 1 720 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.true 1 720) qz22)

noncomputable abbrev qz506 := (@HAdd.hAdd Complex Complex Complex qz535 qz534 qz544)

noncomputable abbrev qz236 := qz506

noncomputable def ep1426 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) (@HMul.hMul Complex Complex Complex qz72 (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) qz236) Bool.true 32272825701 500000 0 1 Bool.true 214652780605887 125000000 0 1

noncomputable abbrev qz237 := (Complex.re qz506)

noncomputable abbrev qz238 := (Complex.im qz506)

noncomputable def ep1427 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz237) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz238) 3585786189 100000 0 1 3585973689 125000 0 1

noncomputable def ep1428 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz237 3585786189 250000 0 1 5 2 0 1 3585786189 100000

noncomputable abbrev qz507 := (@HAdd.hAdd Complex Complex Complex qz535 qz534 (@Nat.cast Complex Complex.instNatCast 1))

noncomputable abbrev qz239 := qz507

noncomputable def ep1429 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) (@HMul.hMul Complex Complex Complex qz72 (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) qz239) Bool.true 3585786189 250000 0 1 Bool.false 59883 250 0 1

noncomputable abbrev qz240 := (Complex.re qz507)

noncomputable abbrev qz241 := (Complex.im qz507)

noncomputable def ep1430 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz240) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz241) 3 4 0 1 3585973689 250000 0 1

noncomputable def ep1431 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz240 1 2 0 1 3 2 0 1 3 4

noncomputable def ep1432 := @ep1431 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 119766 1000 0 1 ep678)

noncomputable abbrev qz508 := (Enclosure.sfrac Bool.false 3 2)

noncomputable def ep1433 := @Enclosure.Complex.IsNear.of_eq qz239 (Complex.mk qz508 qz13) Bool.false 3 2 0 1 Bool.false 119766 1000 0 1 (BSN.s_add_nat_mk qz13 Bool.false 119766 1000 1 qz14)

noncomputable abbrev qz509 := (ep1433 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 3 2) qz13 Bool.false 3 2 0 1 Bool.false 119766 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 3 2) qz19))

noncomputable def ep1434 := ep1432 (@Enclosure.Complex.IsNear.re_isNear qz239 Bool.false 3 2 0 1 Bool.false 119766 1000 0 1 qz509)

noncomputable def ep1435 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz241 119766 1000 0 1 119766 1000 0 1 3585973689 250000

noncomputable def ep1436 := @ep1435 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 119766 1000 0 1 ep678)

noncomputable def ep1437 := ep1436 (@Enclosure.Complex.IsNear.im_isNear qz239 Bool.false 3 2 0 1 Bool.false 119766 1000 0 1 qz509)

noncomputable def ep1438 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) qz239 Bool.true 3585786189 250000 0 1 Bool.false 59883 250 0 1 (@ep1430 14343144756 3585786189 250000 0 1 (ep1434 rfl) (ep1437 rfl) rfl rfl)

noncomputable def ep1439 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz241) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz240) 59883 1000 0 1 179649 1000 0 1

noncomputable def ep1440 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz241 1 2 0 1 119766 1000 0 1 59883 1000

noncomputable def ep1441 := @ep1440 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 119766 1000 0 1 ep678)

noncomputable def ep1442 := ep1441 (@Enclosure.Complex.IsNear.im_isNear qz239 Bool.false 3 2 0 1 Bool.false 119766 1000 0 1 qz509)

noncomputable def ep1443 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz240 119766 1000 0 1 3 2 0 1 179649 1000

noncomputable def ep1444 := @ep1443 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 119766 1000 0 1 ep678)

noncomputable def ep1445 := ep1444 (@Enclosure.Complex.IsNear.re_isNear qz239 Bool.false 3 2 0 1 Bool.false 119766 1000 0 1 qz509)

noncomputable abbrev qz242 := (ep1429 (BSN.ascPochhammer_succ_eval_c 1 2 qz272 rfl) (ep1438 (@ep1439 239532000 59883 250 0 1 (ep1442 rfl) (ep1445 rfl) rfl rfl)))

noncomputable def ep1446 := @ep1428 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 3585786189 250000 0 1 Bool.false 59883 250 0 1 qz242)

noncomputable abbrev qz510 := (Enclosure.sfrac Bool.false 5 2)

noncomputable def ep1447 := @Enclosure.Complex.IsNear.of_eq qz236 (Complex.mk qz510 qz13) Bool.false 5 2 0 1 Bool.false 119766 1000 0 1 (BSN.s_add_nat_mk qz13 Bool.false 119766 1000 2 qz14)

noncomputable abbrev qz511 := (ep1447 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 5 2) qz13 Bool.false 5 2 0 1 Bool.false 119766 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 5 2) qz19))

noncomputable def ep1448 := ep1446 (@Enclosure.Complex.IsNear.re_isNear qz236 Bool.false 5 2 0 1 Bool.false 119766 1000 0 1 qz511)

noncomputable def ep1449 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz238 59883 250 0 1 119766 1000 0 1 3585973689 125000

noncomputable def ep1450 := @ep1449 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 3585786189 250000 0 1 Bool.false 59883 250 0 1 qz242)

noncomputable def ep1451 := ep1450 (@Enclosure.Complex.IsNear.im_isNear qz236 Bool.false 5 2 0 1 Bool.false 119766 1000 0 1 qz511)

noncomputable def ep1452 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) qz236 Bool.true 32272825701 500000 0 1 Bool.true 214652780605887 125000000 0 1 (@ep1427 806820642525000 32272825701 500000 0 1 (ep1448 rfl) (ep1451 rfl) rfl rfl)

noncomputable def ep1453 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz238) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz237) 214727634355887 125000000 0 1 59883 100 0 1

noncomputable def ep1454 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz238 3585786189 250000 0 1 119766 1000 0 1 214727634355887 125000000

noncomputable def ep1455 := @ep1454 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 3585786189 250000 0 1 Bool.false 59883 250 0 1 qz242)

noncomputable def ep1456 := ep1455 (@Enclosure.Complex.IsNear.im_isNear qz236 Bool.false 5 2 0 1 Bool.false 119766 1000 0 1 qz511)

noncomputable def ep1457 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz237 59883 250 0 1 5 2 0 1 59883 100

noncomputable def ep1458 := @ep1457 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 3585786189 250000 0 1 Bool.false 59883 250 0 1 qz242)

noncomputable def ep1459 := ep1458 (@Enclosure.Complex.IsNear.re_isNear qz236 Bool.false 5 2 0 1 Bool.false 119766 1000 0 1 qz511)

noncomputable abbrev qz243 := (ep1426 (BSN.ascPochhammer_succ_eval_c 2 3 qz272 rfl) (ep1452 (@ep1453 21465278060588700 214652780605887 125000000 0 1 (ep1456 rfl) (ep1459 rfl) rfl rfl)))

noncomputable def ep1460 := @ep1424 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1425) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 32272825701 500000 0 1 Bool.true 214652780605887 125000000 0 1 qz243)

noncomputable def ep1461 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 214652780605887 125000000 0 1 0 1 0

noncomputable def ep1462 := @ep1461 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1425) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 32272825701 500000 0 1 Bool.true 214652780605887 125000000 0 1 qz243)

noncomputable def ep1463 := @Enclosure.Real.IsNear.addLit_ft_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) 71550926868629 30000000000 0 1 0 1 0 1 71550926868629

noncomputable def ep1464 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 214652780605887 125000000 0 1 71550926868629 30000000000 0

noncomputable def ep1465 := @ep1464 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1425) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 32272825701 500000 0 1 Bool.true 214652780605887 125000000 0 1 qz243)

noncomputable def ep1466 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 32272825701 500000 0 1 0 1 0

noncomputable def ep1467 := @ep1466 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1425) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 32272825701 500000 0 1 Bool.true 214652780605887 125000000 0 1 qz243)

noncomputable def ep1468 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.false 10757608567 120000000 0 1 Bool.false 71550926868629 30000000000 0 1 (@ep1423 10757608567 120000000 0 1 (ep1460 rfl) (ep1462 rfl) rfl rfl) (@ep1463 71550926868629 30000000000 0 1 (ep1465 rfl) (ep1467 rfl) rfl rfl)

noncomputable def ep1469 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 10757608567 120000000 0 1 Bool.false 71550926868629 30000000000 0 1 ep1468

noncomputable def ep1470 := @Enclosure.Complex.IsNear.re_isNear qz225 Bool.false 1000459477417136355 302231454903657293676544 242362948744589166259 ep1421 Bool.false 1782064917688902447 302231454903657293676544 430198593129761008759 ep1421

noncomputable abbrev qz512 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 21870000000)))

noncomputable def ep1471 := @Enclosure.Complex.IsNear.of_eq qz225 (Complex.mk (@HMul.hMul Real Real Real qz0 qz512 qz137) (@HMul.hMul Real Real Real qz0 qz512 qz587)) Bool.false 1000459477417136355 302231454903657293676544 242362948744589166259 ep1421 Bool.false 1782064917688902447 302231454903657293676544 430198593129761008759

noncomputable abbrev qz513 := (Real.sqrt (@Nat.cast Real Real.instNatCast 21870000000))

noncomputable abbrev qz514 := (@Nat.cast Real Real.instNatCast 21870000000)

noncomputable def ep1472 := @Enclosure.Real.IsNear.inv_image qz513 81300688304238759 549755813888 1 549755813888 1858726 1858727 274877906944 (@Enclosure.Real.IsNear.of_eq qz513 (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz514 qz15)) Bool.false 81300688304238759 549755813888 1 549755813888 (BSN.sqrt_natCast_div_one 21870000000) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz514 qz15)) Bool.false 81300688304238759 549755813888 1 549755813888 81300688304238759 549755813888 1 549755813888 (BSN.sqrt_enclosure 21870000000 1 40650344152119379 40650344152119380 274877906944 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep1473 := nat_lit 33683827362145164021953724416

noncomputable def ep1474 := nat_lit 9903520314283042199192993792

noncomputable def ep1475 := nat_lit 114352560000000000000000000

noncomputable def ep1476 := nat_lit 1204151289564398334826260378898323241051462041600

noncomputable def ep1477 := nat_lit 39392877658465530327996816403800675588306370560

noncomputable def ep1478 := nat_lit 225474642505691211118786403578675200

noncomputable def ep1479 := BSN.log_dyadic_bound 14 46 12 11 ep1476 274877906944 114352560000 ep1477 ep1478 172790632588 60 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base11 (BSN.artanhP 14) (BSN.artanhQ 46) 0 11 ep1477 ep1476 ep1478 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep1480 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz139 119766 1000 0 1 3829407815163127 1125899906842624 3126429407 357351750000000000000 229316428195413534141 562949953421312000 62406657393127 59558625000000000000000 qz19 (BSN.isNear_log_sfrac 30 1 3829407815163127 1125899906842624 3126429407 357351750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz436) Bool.false ep1473 ep1474 1000457410240000 ep1475 3829407815163127 1125899906842624 3126429407 357351750000000000000 (BSN.log_rat_reduce_isNear 30 1 4 60 32 172790632588 274877906944 24973259072661432 36028797018963968 114352560000 1000000000000000 rfl rfl rfl rfl (ep1479 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1481 := nat_lit 40529718903421133604589142016

noncomputable def ep1482 := nat_lit 79228162514264337593543950336

noncomputable def ep1483 := nat_lit 534768624941353663620942151731296899000128195515928399884776472595459846907431788352375373368426374050598615970312751038720

noncomputable def ep1484 := nat_lit 937046835760177389014339949136452948956763638101868628335989667301470209077471332707205705798296416271460543045470610396282880

noncomputable def ep1485 := nat_lit 12110172490790941247417798885778747404531232469100569109337869031950110612275941166269867720932415741918013462489743616

noncomputable def ep1486 := nat_lit 1400564886948084028911876482859962522266442699593910122586332785962057394102282427494332969512425660507033269805213174087936

noncomputable def ep1487 := nat_lit 17179191988936585465262899067501637397540666698534258186159810567193620499753641099632104606302100964976776622500294523931852800

noncomputable def ep1488 := BSN.sin_dyadic_bound_f 575961946984494 1125899906842624 3 2 549755813888 228928464844 ep1483 ep1484 ep1485 ep1486 ep1487 ep1485 269124983535 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 575961946984494) (BSN.sinEvenQ 1125899906842624) 0 2 ep1483 ep1484 ep1485 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 575961946984494) (BSN.sinOddQ 1125899906842624) 0 2 ep1486 ep1487 ep1485 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz515 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 223941824409583) (@Nat.cast Real Real.instNatCast 549755813888))

noncomputable def ep1489 := @Enclosure.Real.IsNear.cos_image qz140 qz515 Bool.false 223941824409583 549755813888 577 549755813888 Bool.false 269124983535 549755813888 1 114352560000 (@Enclosure.Real.IsNear.recentre' qz140 Bool.false 229316428195413534141 562949953421312000 62406657393127 59558625000000000000000 223941824409583 549755813888 577 549755813888 (ep1480 rfl) rfl) (Enclosure.sfrac_false_div 223941824409583 549755813888) (BSN.cos_reduce3 qz515 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep1481) (@Nat.cast Real Real.instNatCast ep1482)) 226375608064910080 72057594037927936 Bool.false 269124983535 549755813888 64 1000000000000000 228705120000 114352560000 (BSN.sin_reduce_arg_pos_rat_q3 223941824409583 549755813888 226375608064910080 72057594037927936 64 ep1481 ep1482 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 269124983535 549755813888 ep1481 ep1482 575961946984494 1125899906842624 228928464844 228705120000 (ep1488 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1490 := nat_lit 297099062821859053541077825539114178887806566945502044633368857161491892775512005058504660701446177768440083545045968240896

noncomputable def ep1491 := nat_lit 104116315084464154334926661015161438772973737566874292037332185255718912119719036967467300644255157363495615893941178932920320

noncomputable def ep1492 := nat_lit 891272968120595578740738641019570979168610638371567932761887895746411778105311463293181442368896668473836414608212925235456

noncomputable def ep1493 := nat_lit 4685234178800886945071699745682264744783818190509343141679948336507351045387356663536028528991482081357302715227353051981414400

noncomputable def ep1494 := BSN.cos_dyadic_bound_f 575961946984494 1125899906842624 3 2 549755813888 228928464844 ep1490 ep1491 ep1485 ep1492 ep1493 ep1485 479377928299 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 575961946984494) (BSN.cosEvenQ 1125899906842624) 0 2 ep1490 ep1491 ep1485 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 575961946984494) (BSN.cosOddQ 1125899906842624) 0 2 ep1492 ep1493 ep1485 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1495 := @Enclosure.Real.IsNear.sin_image qz140 qz515 Bool.false 223941824409583 549755813888 577 549755813888 Bool.true 479377928299 549755813888 1 114352560000 (@Enclosure.Real.IsNear.recentre' qz140 Bool.false 229316428195413534141 562949953421312000 62406657393127 59558625000000000000000 223941824409583 549755813888 577 549755813888 (ep1480 rfl) rfl) (Enclosure.sfrac_false_div 223941824409583 549755813888) (BSN.sin_reduce3 qz515 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep1481) (@Nat.cast Real Real.instNatCast ep1482)) 226375608064910080 72057594037927936 Bool.false 479377928299 549755813888 64 1000000000000000 228705120000 114352560000 (BSN.sin_reduce_arg_pos_rat_q3 223941824409583 549755813888 226375608064910080 72057594037927936 64 ep1481 ep1482 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 479377928299 549755813888 ep1481 ep1482 575961946984494 1125899906842624 228928464844 228705120000 (ep1494 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1496 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz512 qz137) (@HMul.hMul Real Real Real qz0 qz512 qz587) Bool.false 1000459477417136355 302231454903657293676544 242362948744589166259 ep1421 Bool.false 1782064917688902447 302231454903657293676544 430198593129761008759 ep1421 (@Enclosure.Real.IsNear.mulLit_ff qz512 qz137 3717453 549755813888 1 549755813888 269124983535 549755813888 519774866671 491140505413877760000 1000459477417136355 302231454903657293676544 242362948744589166259 ep1421 (@Enclosure.Real.IsNear.recentre' qz512 Bool.false 3717453 549755813888 1 549755813888 3717453 549755813888 1 549755813888 (ep1472 rfl rfl) rfl) (@Enclosure.Real.IsNear.recentre' qz137 Bool.false 269124983535 549755813888 66531182933888 62865984692976353280000 269124983535 549755813888 519774866671 491140505413877760000 (ep1489 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz512 qz587 3717453 549755813888 1 549755813888 479377928299 549755813888 519774866671 491140505413877760000 1782064917688902447 302231454903657293676544 430198593129761008759 ep1421 (@Enclosure.Real.IsNear.recentre' qz512 Bool.false 3717453 549755813888 1 549755813888 3717453 549755813888 1 549755813888 (ep1472 rfl rfl) rfl) (@Enclosure.Real.IsNear.neg qz138 Bool.true 479377928299 549755813888 519774866671 491140505413877760000 (@Enclosure.Real.IsNear.recentre' qz138 Bool.true 479377928299 549755813888 66531182933888 62865984692976353280000 479377928299 549755813888 519774866671 491140505413877760000 (ep1495 rfl rfl) rfl)) rfl)

noncomputable def ep1497 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz235 71550926868629 30000000000 0 1 1782064917688902447 302231454903657293676544 430198593129761008759 ep1421 ep1416

noncomputable def ep1498 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 10757608567 120000000 0 1 Bool.false 71550926868629 30000000000 0 1 ep1468

noncomputable def ep1499 := @Enclosure.Complex.IsNear.im_isNear qz225 Bool.false 1000459477417136355 302231454903657293676544 242362948744589166259 ep1421 Bool.false 1782064917688902447 302231454903657293676544 430198593129761008759 ep1421

noncomputable def ep1500 := nat_lit 6390252275160095601558154483

noncomputable def ep1501 := nat_lit 12089258196146291747061760000000

noncomputable def ep1502 := nat_lit 4627908070964064370488380438353

noncomputable def ep1503 := nat_lit 4772253526913353991858964327153

noncomputable def ep1504 := nat_lit 17341293621289378140463148732388911

noncomputable def ep1505 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz235) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz234) ep1500 ep1501 ep1502 ep1415 ep1503 ep1408 ep1504

noncomputable def ep1506 := nat_lit 61555675548971396340443053545276407933243410714229473280000000

noncomputable def ep1507 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz235 10757608567 120000000 0 1 1782064917688902447 302231454903657293676544 430198593129761008759 ep1421 ep1500

noncomputable def ep1508 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz234 71550926868629 30000000000 0 1 1000459477417136355 302231454903657293676544 242362948744589166259 ep1421 ep1503

noncomputable abbrev qz516 := (@ep1471 ep1421 (BSN.cpow_neg_s_sub_mk qz13 119766 1000 30 3 21870000000 qz14 rfl EMRow39.d20) ep1496)

noncomputable def ep1509 := ep1411 (@ep1418 ep1419 ep1420 ep1402 ep1403 ep1404 ep1405 (@ep1422 ep1413 ep1414 ep1415 ep1469 (ep1470 qz516) rfl) (@ep1497 ep1403 ep1417 ep1419 ep1498 (ep1499 qz516) rfl) rfl rfl) (@ep1505 ep1419 ep1506 ep1407 ep1408 ep1409 ep1405 (@ep1507 ep1501 ep1502 ep1415 ep1469 (ep1499 qz516) rfl) (@ep1508 ep1408 ep1504 ep1419 ep1498 (ep1470 qz516) rfl) rfl rfl)

noncomputable def ep1510 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)) (Complex.im (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)) ep1407 ep1408 ep1409 ep1405 ep1407 ep1408 ep1409

noncomputable def ep1511 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225) Bool.true ep1402 ep1403 ep1404 ep1405 Bool.false ep1407 ep1408 ep1409

noncomputable def ep1512 := @ep1373 278679421237348797 504403158265495552 79987656083 504403158265495552 (@ep1374 1 3670016 (ep1375 (@ep1376 1048576 1 1048576 (ep1377 (@ep1378 14356144756 3589036189 250000 0 1 (ep1382 rfl) (ep1385 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) (Enclosure.Real.IsNear.const Bool.false 2 7) rfl) (@ep1386 619 137438953472 (BSN.norm_eq_sqrt_mul_add (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)) (@ep1387 2476 549755813888 2218125291 137438953472 619 137438953472 (@ep1392 4436249344 4436251820 274877906944 (@ep1398 ep1399 ep1400 ep1396 ep1401 ep1388 ep1389 ep1390 ep1391 (@ep1406 ep1405 ep1393 ep1394 ep1395 ep1396 (@ep1410 ep1405 ep1509) (@ep1410 ep1405 ep1509) rfl) (@ep1510 ep1405 ep1397 ep1399 ep1400 ep1396 (@ep1511 ep1405 ep1509) (@ep1511 ep1405 ep1509) rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl

theorem EMRow39.d21 : Enclosure.Real.IsNear (@HAdd.hAdd Real Real Real qz402 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 30))) (@HMul.hMul Real Real Real qz0 qz222 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)))) Bool.false 8084415756823414511 13618885273168379904 1529747638769281 13618885273168379904 := ep1371 (ep1372 ep1512) rfl rfl

theorem EMRow39.d22 : @Eq Nat (Nat.pow 31 (Nat.succ (Nat.mul 2 3))) 27512614111 := @Eq.refl Nat 27512614111

noncomputable abbrev qz608 := (@HAdd.hAdd Complex Complex Complex qz610 qz616 (@Nat.cast Complex Complex.instNatCast 3))

noncomputable abbrev qz517 := qz608

noncomputable abbrev qz244 := (@HDiv.hDiv Real Real Real qz271 (@Norm.norm Complex Complex.instNorm qz517) (@HAdd.hAdd Real Real Real qz402 (Complex.re qz439) qz547))

noncomputable abbrev qz518 := (@HPow.hPow Complex Complex Complex qz536 (@Nat.cast Complex Complex.instNatCast 31) (@HSub.hSub Complex Complex Complex qz572 qz590 qz543))

noncomputable abbrev qz245 := qz518

noncomputable def ep1513 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz146 1 31))) (@HMul.hMul Real Real Real qz0 qz244 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) qz245))) 23210356411 1855425871872 218283821 1855425871872 266566037651434669 504403158265495552 42886085089

noncomputable def ep1514 := nat_lit 506300899899053742286427914240

noncomputable def ep1515 := @Enclosure.Real.IsNear.mulLit_ff (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz146 1 31)) 26561 1769472 1 1769472 873851 1048576 8185 1048576 23210356411 1855425871872

noncomputable def ep1516 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (zetaApproximant qz146 1 31)) (Real.sqrt (@HAdd.hAdd Real Real Real qz402 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz146 1 31)) (Complex.re (zetaApproximant qz146 1 31))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz146 1 31)) (Complex.im (zetaApproximant qz146 1 31))))) Bool.false 873851 1048576 8185 1048576

noncomputable def ep1517 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz402 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz146 1 31)) (Complex.re (zetaApproximant qz146 1 31))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz146 1 31)) (Complex.im (zetaApproximant qz146 1 31))))) Bool.false 873851 1048576 8185 1048576

noncomputable def ep1518 := nat_lit 6905714211249512811926076739368004436027453

noncomputable def ep1519 := nat_lit 9942511727543647815738243602109501014016000

noncomputable def ep1520 := nat_lit 1662309309558491730666904901326907094421568198374767078149547

noncomputable def ep1521 := nat_lit 127786792777359181322635509717202003798918320679689807462400000

noncomputable def ep1522 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz402 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz146 1 31)) (Complex.re (zetaApproximant qz146 1 31))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz146 1 31)) (Complex.im (zetaApproximant qz146 1 31)))) ep1518 ep1519 ep1520 ep1521 432833 441018

noncomputable def ep1523 := nat_lit 2848998969219113663245379619156482251605872904444716649

noncomputable def ep1524 := nat_lit 4103403257382434002504841022053579801163345166336000000

noncomputable def ep1525 := nat_lit 16234955133235842903721004867273316245660918851528968900821383

noncomputable def ep1526 := nat_lit 1277867927773591813226355097172020037989183206796898074624000000

noncomputable def ep1527 := nat_lit 9707882132655251698193493765591988602577764355323409

noncomputable def ep1528 := nat_lit 36930629316441906022543569198482218210470106497024000000

noncomputable def ep1529 := nat_lit 388137962349074402948044145995754698554763132218701880674087

noncomputable def ep1530 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz146 1 31)) (Complex.re (zetaApproximant qz146 1 31))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz146 1 31)) (Complex.im (zetaApproximant qz146 1 31))) ep1523 ep1524 ep1525 ep1526 ep1527 ep1528 ep1529

noncomputable def ep1531 := nat_lit 105255160210321592772200673859500033592531436090196152201214714484222739722720939118874097636775821312000000000

noncomputable def ep1532 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (zetaApproximant qz146 1 31)) (Complex.re (zetaApproximant qz146 1 31)) ep1037 ep1038 ep1039 ep1040 ep1037 ep1038 ep1039 ep1040 ep1523

noncomputable def ep1533 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (zetaApproximant qz146 1 31)) (Complex.im (zetaApproximant qz146 1 31)) ep1158 ep1159 ep1160 ep1040 ep1158 ep1159 ep1160 ep1040 ep1527

noncomputable def ep1534 := @ep1513 252201579132747776 ep1514 7367647775376881215 13618885273168379904 802263039908539 6809442636584189952 (@ep1515 218283821 1855425871872 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaStirlingErrorBound 1 2) (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 96 162) qz499) Bool.false 26561 1769472 1 1769472 (BSN.theta_err_eq 1 2 96 162 EMRow39.d17 EMRow39.d18 rfl) (ep1351 rfl)) (ep1516 (BSN.norm_eq_sqrt_mul_add (zetaApproximant qz146 1 31)) (@ep1517 873851 1048576 8185 1048576 (@ep1522 524288 (@ep1530 ep1526 ep1531 ep1518 ep1519 ep1520 ep1521 (@ep1532 ep1524 ep1525 ep1526 ep1333 ep1333 rfl) (@ep1533 ep1528 ep1529 ep1526 ep1339 ep1339 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl)

noncomputable abbrev qz246 := (@Norm.norm Complex Complex.instNorm qz517)

noncomputable def ep1535 := @Enclosure.Real.IsNear.of_eq (@HMul.hMul Real Real Real qz0 qz244 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) qz245))) (@HMul.hMul Real Real Real qz0 (@HMul.hMul Real Real Real qz0 qz246 qz607) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) qz245))) Bool.false 266566037651434669 504403158265495552 42886085089 252201579132747776 (BSN.zrb_shape_eq qz246 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)) qz149 3)

noncomputable def ep1536 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz0 qz246 qz607) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)) 127864657 3670016 1 3670016 2084751517 137438953472 1309 274877906944

noncomputable def ep1537 := @Enclosure.Real.IsNear.mulLit_ff qz246 qz607 127864657 1048576 1 1048576 2 7 0 1 127864657 3670016

noncomputable abbrev qz519 := (Complex.re qz608)

noncomputable abbrev qz520 := (Complex.im qz608)

noncomputable abbrev qz247 := (@HAdd.hAdd Real Real Real qz402 (@HMul.hMul Real Real Real qz268 qz519 qz519) (@HMul.hMul Real Real Real qz268 qz520 qz520))

noncomputable abbrev qz248 := qz517

noncomputable def ep1538 := @Enclosure.Real.IsNear.of_eq qz246 (Real.sqrt qz247) Bool.false 127864657 1048576 1 1048576 (BSN.norm_eq_sqrt_mul_add qz248)

noncomputable def ep1539 := @Enclosure.Real.IsNear.recentre' (Real.sqrt qz247) Bool.false 127864657 1048576 1 1048576 127864657

noncomputable def ep1540 := @Enclosure.Real.IsNear.sqrt_image qz247 14869665881 1000000 0 1 63932328 63932329 524288

noncomputable abbrev qz249 := (@HMul.hMul Real Real Real qz268 qz519 qz519)

noncomputable abbrev qz250 := (@HMul.hMul Real Real Real qz268 qz520 qz520)

noncomputable def ep1541 := @Enclosure.Real.IsNear.addLit_ff qz249 qz250 49 4 0 1 14857415881 1000000 0 1

noncomputable abbrev qz251 := qz519

noncomputable def ep1542 := @Enclosure.Real.IsNear.mulLit_ff qz251 qz251 7 2 0 1 7 2 0 1 49 4

noncomputable def ep1543 := @Enclosure.Complex.IsNear.of_eq qz248 (Complex.mk qz504 qz149) Bool.false 7 2 0 1 Bool.false 121891 1000 0 1 (BSN.s_add_nat_mk qz149 Bool.false 121891 1000 3 qz150)

noncomputable abbrev qz521 := (ep1543 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7 2) qz149 Bool.false 7 2 0 1 Bool.false 121891 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 7 2) qz151))

noncomputable def ep1544 := @ep1542 0 1 (@Enclosure.Complex.IsNear.re_isNear qz248 Bool.false 7 2 0 1 Bool.false 121891 1000 0 1 qz521)

noncomputable def ep1545 := ep1544 (@Enclosure.Complex.IsNear.re_isNear qz248 Bool.false 7 2 0 1 Bool.false 121891 1000 0 1 qz521)

noncomputable abbrev qz252 := qz520

noncomputable def ep1546 := @Enclosure.Real.IsNear.mulLit_ff qz252 qz252 121891 1000 0 1 121891 1000 0 1 14857415881 1000000

noncomputable def ep1547 := @ep1546 0 1 (@Enclosure.Complex.IsNear.im_isNear qz248 Bool.false 7 2 0 1 Bool.false 121891 1000 0 1 qz521)

noncomputable def ep1548 := ep1547 (@Enclosure.Complex.IsNear.im_isNear qz248 Bool.false 7 2 0 1 Bool.false 121891 1000 0 1 qz521)

noncomputable def ep1549 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)) (Real.sqrt (@HAdd.hAdd Real Real Real qz402 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)) (Complex.re (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) qz245))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)) (Complex.im (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) qz245))))) Bool.false 2084751517 137438953472

noncomputable def ep1550 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz402 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)) (Complex.re (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) qz245))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)) (Complex.im (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) qz245))))) Bool.false 8339006068 549755813888

noncomputable def ep1551 := nat_lit 5447575257698568086385725430085971953733569096790646318077584492401

noncomputable def ep1552 := nat_lit 23676326524760627274899694290003784918426107196211200000000000000000000

noncomputable def ep1553 := nat_lit 36323772405983602512233727838444219548857959325671750324764129668973839613573911

noncomputable def ep1554 := nat_lit 251541492920238617450390787086153394471885207931408600258093653700902912000000000000000000

noncomputable def ep1555 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz402 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)) (Complex.re (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) qz245))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)) (Complex.im (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)))) ep1551 ep1552 ep1553 ep1554

noncomputable def ep1556 := nat_lit 5358543633683413651740723454584927668412907475963959608216667786681

noncomputable def ep1557 := nat_lit 47352653049521254549799388580007569836852214392422400000000000000000000

noncomputable def ep1558 := nat_lit 172560827168547822890169103573519742815355470589162856529201098703220062193019403

noncomputable def ep1559 := nat_lit 2515414929202386174503907870861533944718852079314086002580936537009029120000000000000000000

noncomputable def ep1560 := nat_lit 5536606881713722521030727405587016239054230717617333027938501198121

noncomputable def ep1561 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)) (Complex.re (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) qz245))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)) (Complex.im (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) qz245))) ep1556 ep1557 ep1558 ep1559 ep1560

noncomputable def ep1562 := nat_lit 190676896891288202232168174810922452673224122667554646718440197986518333942719707

noncomputable def ep1563 := nat_lit 515914282277913268414354144025176300365475624573711574792456948466740154746881878738779593440391030196024237049564364800000000000000000000

noncomputable def ep1564 := nat_lit 2314852831970839059314305708338709

noncomputable def ep1565 := nat_lit 217606647530633251447111680000000000

noncomputable def ep1566 := nat_lit 2287026019746347542901446665433372813

noncomputable def ep1567 := nat_lit 709283431246266484293592918347743232000000000

noncomputable def ep1568 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)) (Complex.re (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)) ep1564 ep1565 ep1566 ep1567 ep1564 ep1565 ep1566

noncomputable def ep1569 := nat_lit 2352999549875376096229001889990989

noncomputable def ep1570 := nat_lit 2486156734521783347557925869373916317

noncomputable def ep1571 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) qz245) Bool.true ep1564 ep1565 ep1566 ep1567 Bool.true ep1569 ep1565 ep1570

noncomputable def ep1572 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) qz245 Bool.true ep1564 ep1565 ep1566 ep1567 Bool.true ep1569 ep1565 ep1570 ep1567

noncomputable def ep1573 := nat_lit 59956278547187209092104194537

noncomputable def ep1574 := nat_lit 145071098353755500964741120000000

noncomputable def ep1575 := nat_lit 59212837629721997234114446784161

noncomputable def ep1576 := nat_lit 472855620830844322862395278898495488000000

noncomputable def ep1577 := nat_lit 2224918414150058245676149416533209

noncomputable def ep1578 := nat_lit 314029537614537792435753570751018759

noncomputable abbrev qz253 := (Complex.re qz518)

noncomputable abbrev qz254 := (Complex.im qz518)

noncomputable def ep1579 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3)))) qz253) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3)))) qz254) ep1573 ep1574 ep1575 ep1576 ep1577 ep1565 ep1578

noncomputable def ep1580 := nat_lit 101326204463752354899084702621106176000000000

noncomputable def ep1581 := nat_lit 335818242861311049549507326814345224961325892734579460014080000000

noncomputable def ep1582 := nat_lit 4925579383654628363149950821859328

noncomputable def ep1583 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3)))) qz253 44570997643 480000000 0 1 1345185921738135259 302231454903657293676544 6642529981491399173135 ep1582 ep1573

noncomputable def ep1584 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3)))) 44570997643 480000000 0 1 0 1 0 1 44570997643

noncomputable def ep1585 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 133712992929 2000000 0 1 44570997643 480000000 0

noncomputable abbrev qz522 := (@HAdd.hAdd Complex Complex Complex qz535 qz589 qz544)

noncomputable abbrev qz255 := qz522

noncomputable def ep1586 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3)) (@HMul.hMul Complex Complex Complex qz72 (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 2)) qz255) Bool.true 133712992929 2000000 0 1 Bool.true 1810284405900971 1000000000 0 1

noncomputable abbrev qz256 := (Complex.re qz522)

noncomputable abbrev qz257 := (Complex.im qz522)

noncomputable def ep1587 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 2))) qz256) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 2))) qz257) 14856665881 400000 0 1 14857415881 500000 0 1

noncomputable def ep1588 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 2))) qz256 14856665881 1000000 0 1 5 2 0 1 14856665881 400000

noncomputable abbrev qz523 := (@HAdd.hAdd Complex Complex Complex qz535 qz589 (@Nat.cast Complex Complex.instNatCast 1))

noncomputable abbrev qz258 := qz523

noncomputable def ep1589 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 2)) (@HMul.hMul Complex Complex Complex qz72 (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1)) qz258) Bool.true 14856665881 1000000 0 1 Bool.false 121891 500 0 1

noncomputable abbrev qz259 := (Complex.re qz523)

noncomputable abbrev qz260 := (Complex.im qz523)

noncomputable def ep1590 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1))) qz259) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1))) qz260) 3 4 0 1 14857415881 1000000 0 1

noncomputable def ep1591 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1))) qz259 1 2 0 1 3 2 0 1 3 4

noncomputable def ep1592 := @ep1591 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 121891 1000 0 1 ep1297)

noncomputable def ep1593 := @Enclosure.Complex.IsNear.of_eq qz258 (Complex.mk qz508 qz149) Bool.false 3 2 0 1 Bool.false 121891 1000 0 1 (BSN.s_add_nat_mk qz149 Bool.false 121891 1000 1 qz150)

noncomputable abbrev qz524 := (ep1593 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 3 2) qz149 Bool.false 3 2 0 1 Bool.false 121891 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 3 2) qz151))

noncomputable def ep1594 := ep1592 (@Enclosure.Complex.IsNear.re_isNear qz258 Bool.false 3 2 0 1 Bool.false 121891 1000 0 1 qz524)

noncomputable def ep1595 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1))) qz260 121891 1000 0 1 121891 1000 0 1 14857415881 1000000

noncomputable def ep1596 := @ep1595 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 121891 1000 0 1 ep1297)

noncomputable def ep1597 := ep1596 (@Enclosure.Complex.IsNear.im_isNear qz258 Bool.false 3 2 0 1 Bool.false 121891 1000 0 1 qz524)

noncomputable def ep1598 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1)) qz258 Bool.true 14856665881 1000000 0 1 Bool.false 121891 500 0 1 (@ep1590 59426663524 14856665881 1000000 0 1 (ep1594 rfl) (ep1597 rfl) rfl rfl)

noncomputable def ep1599 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1))) qz260) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1))) qz259) 121891 2000 0 1 365673 2000 0 1

noncomputable def ep1600 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1))) qz260 1 2 0 1 121891 1000 0 1 121891 2000

noncomputable def ep1601 := @ep1600 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 121891 1000 0 1 ep1297)

noncomputable def ep1602 := ep1601 (@Enclosure.Complex.IsNear.im_isNear qz258 Bool.false 3 2 0 1 Bool.false 121891 1000 0 1 qz524)

noncomputable def ep1603 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1))) qz259 121891 1000 0 1 3 2 0 1 365673 2000

noncomputable def ep1604 := @ep1603 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 121891 1000 0 1 ep1297)

noncomputable def ep1605 := ep1604 (@Enclosure.Complex.IsNear.re_isNear qz258 Bool.false 3 2 0 1 Bool.false 121891 1000 0 1 qz524)

noncomputable abbrev qz261 := (ep1589 (BSN.ascPochhammer_succ_eval_c 1 2 qz439 rfl) (ep1598 (@ep1599 975128000 121891 500 0 1 (ep1602 rfl) (ep1605 rfl) rfl rfl)))

noncomputable def ep1606 := @ep1588 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 14856665881 1000000 0 1 Bool.false 121891 500 0 1 qz261)

noncomputable def ep1607 := @Enclosure.Complex.IsNear.of_eq qz255 (Complex.mk qz510 qz149) Bool.false 5 2 0 1 Bool.false 121891 1000 0 1 (BSN.s_add_nat_mk qz149 Bool.false 121891 1000 2 qz150)

noncomputable abbrev qz525 := (ep1607 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 5 2) qz149 Bool.false 5 2 0 1 Bool.false 121891 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 5 2) qz151))

noncomputable def ep1608 := ep1606 (@Enclosure.Complex.IsNear.re_isNear qz255 Bool.false 5 2 0 1 Bool.false 121891 1000 0 1 qz525)

noncomputable def ep1609 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 2))) qz257 121891 500 0 1 121891 1000 0 1 14857415881 500000

noncomputable def ep1610 := @ep1609 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 14856665881 1000000 0 1 Bool.false 121891 500 0 1 qz261)

noncomputable def ep1611 := ep1610 (@Enclosure.Complex.IsNear.im_isNear qz255 Bool.false 5 2 0 1 Bool.false 121891 1000 0 1 qz525)

noncomputable def ep1612 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 2)) qz255 Bool.true 133712992929 2000000 0 1 Bool.true 1810284405900971 1000000000 0 1 (@ep1587 13371299292900000 133712992929 2000000 0 1 (ep1608 rfl) (ep1611 rfl) rfl rfl)

noncomputable def ep1613 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 2))) qz257) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 2))) qz256) 1810893860900971 1000000000 0 1 121891 200 0 1

noncomputable def ep1614 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 2))) qz257 14856665881 1000000 0 1 121891 1000 0 1 1810893860900971 1000000000

noncomputable def ep1615 := @ep1614 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 14856665881 1000000 0 1 Bool.false 121891 500 0 1 qz261)

noncomputable def ep1616 := ep1615 (@Enclosure.Complex.IsNear.im_isNear qz255 Bool.false 5 2 0 1 Bool.false 121891 1000 0 1 qz525)

noncomputable def ep1617 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 2))) qz256 121891 500 0 1 5 2 0 1 121891 200

noncomputable def ep1618 := @ep1617 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 14856665881 1000000 0 1 Bool.false 121891 500 0 1 qz261)

noncomputable def ep1619 := ep1618 (@Enclosure.Complex.IsNear.re_isNear qz255 Bool.false 5 2 0 1 Bool.false 121891 1000 0 1 qz525)

noncomputable abbrev qz262 := (ep1586 (BSN.ascPochhammer_succ_eval_c 2 3 qz439 rfl) (ep1612 (@ep1613 362056881180194200 1810284405900971 1000000000 0 1 (ep1616 rfl) (ep1619 rfl) rfl rfl)))

noncomputable def ep1620 := @ep1585 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1425) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 133712992929 2000000 0 1 Bool.true 1810284405900971 1000000000 0 1 qz262)

noncomputable def ep1621 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 1810284405900971 1000000000 0 1 0 1 0

noncomputable def ep1622 := @ep1621 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1425) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 133712992929 2000000 0 1 Bool.true 1810284405900971 1000000000 0 1 qz262)

noncomputable def ep1623 := @Enclosure.Real.IsNear.addLit_ft_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3)))) 1810284405900971 720000000000 0 1 0 1 0 1 1810284405900971

noncomputable def ep1624 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 1810284405900971 1000000000 0 1 1810284405900971 720000000000 0

noncomputable def ep1625 := @ep1624 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1425) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 133712992929 2000000 0 1 Bool.true 1810284405900971 1000000000 0 1 qz262)

noncomputable def ep1626 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 133712992929 2000000 0 1 0 1 0

noncomputable def ep1627 := @ep1626 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1425) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 133712992929 2000000 0 1 Bool.true 1810284405900971 1000000000 0 1 qz262)

noncomputable def ep1628 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.false 44570997643 480000000 0 1 Bool.false 1810284405900971 720000000000 0 1 (@ep1584 44570997643 480000000 0 1 (ep1620 rfl) (ep1622 rfl) rfl rfl) (@ep1623 1810284405900971 720000000000 0 1 (ep1625 rfl) (ep1627 rfl) rfl rfl)

noncomputable def ep1629 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 44570997643 480000000 0 1 Bool.false 1810284405900971 720000000000 0 1 ep1628

noncomputable def ep1630 := @Enclosure.Complex.IsNear.re_isNear qz245 Bool.true 1345185921738135259 302231454903657293676544 6642529981491399173135 ep1582 Bool.false 1229043572875901579 302231454903657293676544 6071440366321131202015 ep1582

noncomputable abbrev qz526 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 27512614111)))

noncomputable def ep1631 := @Enclosure.Complex.IsNear.of_eq qz245 (Complex.mk (@HMul.hMul Real Real Real qz0 qz526 qz216) (@HMul.hMul Real Real Real qz0 qz526 qz603)) Bool.true 1345185921738135259 302231454903657293676544 6642529981491399173135 ep1582 Bool.false 1229043572875901579 302231454903657293676544 6071440366321131202015

noncomputable abbrev qz527 := (Real.sqrt (@Nat.cast Real Real.instNatCast 27512614111))

noncomputable abbrev qz528 := (@Nat.cast Real Real.instNatCast 27512614111)

noncomputable def ep1632 := @Enclosure.Real.IsNear.inv_image qz527 91187594501502351 549755813888 1 549755813888 1657196 1657197 274877906944 (@Enclosure.Real.IsNear.of_eq qz527 (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz528 qz15)) Bool.false 91187594501502351 549755813888 1 549755813888 (BSN.sqrt_natCast_div_one 27512614111) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz528 qz15)) Bool.false 91187594501502351 549755813888 1 549755813888 91187594501502351 549755813888 1 549755813888 (BSN.sqrt_enclosure 27512614111 1 45593797250751175 45593797250751176 274877906944 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep1633 := nat_lit 582049110250000000000000000

noncomputable def ep1634 := nat_lit 4074343771750000000000000

noncomputable def ep1635 := nat_lit 34008562038587066016881180672

noncomputable def ep1636 := nat_lit 130379000696000000000000000

noncomputable def ep1637 := nat_lit 1932687477360045273135609688841741008029787544025

noncomputable def ep1638 := nat_lit 69945806522721216552359532071859192006272604375

noncomputable def ep1639 := nat_lit 1028699719278166449487209320068359375

noncomputable def ep1640 := BSN.log_dyadic_bound 15 47 12 11 ep1637 274877906944 130379000696 ep1638 ep1639 181803830455 62 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base11 (BSN.artanhP 15) (BSN.artanhQ 47) 0 11 ep1638 ep1637 ep1639 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep1641 := @Enclosure.Real.IsNear.mulLit_ff qz149 (Real.log (Enclosure.sfrac Bool.false 31 1)) 121891 1000 0 1 3866325873626359 1125899906842624 31266297375087 ep1634 471270327062190524869 1125899906842624000 544440036192389931 ep1633 qz151 (BSN.isNear_log_sfrac 31 1 3866325873626359 1125899906842624 31266297375087 ep1634 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz495) Bool.false ep1635 ep1474 1000521516002784 ep1636 3866325873626359 1125899906842624 31266297375087 ep1634 (BSN.log_rat_reduce_isNear 31 1 4 62 32 181803830455 274877906944 24973259072661432 36028797018963968 130379000696 1000000000000000 rfl rfl rfl rfl (ep1640 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1642 := nat_lit 58653513036564160829697556480

noncomputable def ep1643 := nat_lit 24880468048827306259708008730932842717170830230898692305163342732704686863117151734485868176318534475631255950971657508588448485403843654669582046317967204544237854537033363268829184000000

noncomputable def ep1644 := nat_lit 1987624596718905836716176986560648097192803365158098862996959853973550201711281262778493915976941032830117648803431656099629969197363961031318305664540323188444205381720208504260533000601600

noncomputable def ep1645 := nat_lit 112452921731519307459630431505578857239926473720099975269906610821950189512901268791574165123278792054744814900369686856787657613418865850620591870723091765834944024576000000000000

noncomputable def ep1646 := nat_lit 150923517369548765079492964467636658187766131842220615852862940120766512015406403244778402774799812877392462992731586734718245318576071960133883689045249639903087515620062593900452249600000

noncomputable def ep1647 := nat_lit 180873838301420431141172105777018976844545106229386996532723346711593068355726594912842946353901633987540706041112280705066327196960120453849965815473169410148422689736538973887708503054745600

noncomputable def ep1648 := BSN.cos_dyadic_bound_f 833516552298820 1125899906842624 4 3 549755813888 261012647878 ep1643 ep1644 ep1645 ep1646 ep1647 ep1645 405861924563 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 833516552298820) (BSN.cosEvenQ 1125899906842624) 0 3 ep1643 ep1644 ep1645 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 833516552298820) (BSN.cosOddQ 1125899906842624) 0 3 ep1646 ep1647 ep1645 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz529 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 230112464385835) (@Nat.cast Real Real.instNatCast 549755813888))

noncomputable def ep1649 := @Enclosure.Real.IsNear.cos_image qz218 qz529 Bool.false 230112464385835 549755813888 515 549755813888 Bool.true 405861924563 549755813888 1 130379000696 (@Enclosure.Real.IsNear.recentre' qz218 Bool.false 471270327062190524869 1125899906842624000 544440036192389931 ep1633 230112464385835 549755813888 515 549755813888 (ep1641 rfl) rfl) (Enclosure.sfrac_false_div 230112464385835 549755813888) (BSN.cos_reduce2 qz529 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep1642) (@Nat.cast Real Real.instNatCast ep1482)) 226375608064910080 72057594037927936 Bool.false 405861924563 549755813888 66 1000000000000000 260758001392 130379000696 (BSN.sin_reduce_arg_pos_rat_q2 230112464385835 549755813888 226375608064910080 72057594037927936 66 ep1642 ep1482 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 405861924563 549755813888 ep1642 ep1482 833516552298820 1125899906842624 261012647878 260758001392 (ep1648 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1650 := nat_lit 64684077254576200707751512468475252655297788480376913293658597980767772303377617837858531301178994110778642937566203780163630304956470567278539269298695570276655256934407709345343078400000

noncomputable def ep1651 := nat_lit 25839119757345775877310300825288425263506443747055285218960478101656152622246656416120420907700233426791529434444611529295189599565731493407137973639024201449774669962362710555386929007820800

noncomputable def ep1652 := nat_lit 323400528693148395351318261812671669979822746370970810517596667058068050993788820076377165398139439018395901194928388315982080150821358108247413004852876990653618818618292873617211392000000

noncomputable def ep1653 := nat_lit 904369191507102155705860528885094884222725531146934982663616733557965341778632974564214731769508169937703530205561403525331635984800602269249829077365847050742113448682694869438542515273728000

noncomputable def ep1654 := BSN.sin_dyadic_bound_f 833516552298820 1125899906842624 4 3 549755813888 261012647878 ep1650 ep1651 ep1645 ep1652 ep1653 ep1645 370820108803 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 833516552298820) (BSN.sinEvenQ 1125899906842624) 0 3 ep1650 ep1651 ep1645 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 833516552298820) (BSN.sinOddQ 1125899906842624) 0 3 ep1652 ep1653 ep1645 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1655 := @Enclosure.Real.IsNear.sin_image qz218 qz529 Bool.false 230112464385835 549755813888 515 549755813888 Bool.true 370820108803 549755813888 1 130379000696 (@Enclosure.Real.IsNear.recentre' qz218 Bool.false 471270327062190524869 1125899906842624000 544440036192389931 ep1633 230112464385835 549755813888 515 549755813888 (ep1641 rfl) rfl) (Enclosure.sfrac_false_div 230112464385835 549755813888) (BSN.sin_reduce2 qz529 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep1642) (@Nat.cast Real Real.instNatCast ep1482)) 226375608064910080 72057594037927936 Bool.false 370820108803 549755813888 66 1000000000000000 260758001392 130379000696 (BSN.sin_reduce_arg_pos_rat_q2 230112464385835 549755813888 226375608064910080 72057594037927936 66 ep1642 ep1482 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 370820108803 549755813888 ep1642 ep1482 833516552298820 1125899906842624 261012647878 260758001392 (ep1654 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1656 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz526 qz216) (@HMul.hMul Real Real Real qz0 qz526 qz603) Bool.true 1345185921738135259 302231454903657293676544 6642529981491399173135 ep1582 Bool.false 1229043572875901579 302231454903657293676544 6071440366321131202015 ep1582 (@Enclosure.Real.IsNear.mulLit_ft qz526 qz216 3314393 549755813888 1 549755813888 405861924563 549755813888 8461867646541 8959576705191699808256 1345185921738135259 302231454903657293676544 6642529981491399173135 ep1582 (@Enclosure.Real.IsNear.recentre' qz526 Bool.false 3314393 549755813888 1 549755813888 3314393 549755813888 1 549755813888 (ep1632 rfl rfl) rfl) (@Enclosure.Real.IsNear.recentre' qz216 Bool.true 405861924563 549755813888 67694941172328 71676613641533598466048 405861924563 549755813888 8461867646541 8959576705191699808256 (ep1649 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz526 qz603 3314393 549755813888 1 549755813888 370820108803 549755813888 8461867646541 8959576705191699808256 1229043572875901579 302231454903657293676544 6071440366321131202015 ep1582 (@Enclosure.Real.IsNear.recentre' qz526 Bool.false 3314393 549755813888 1 549755813888 3314393 549755813888 1 549755813888 (ep1632 rfl rfl) rfl) (@Enclosure.Real.IsNear.neg qz217 Bool.true 370820108803 549755813888 8461867646541 8959576705191699808256 (@Enclosure.Real.IsNear.recentre' qz217 Bool.true 370820108803 549755813888 67694941172328 71676613641533598466048 370820108803 549755813888 8461867646541 8959576705191699808256 (ep1655 rfl rfl) rfl)) rfl)

noncomputable def ep1657 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3)))) qz254 1810284405900971 720000000000 0 1 1229043572875901579 302231454903657293676544 6071440366321131202015 ep1582 ep1577

noncomputable def ep1658 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 44570997643 480000000 0 1 Bool.false 1810284405900971 720000000000 0 1 ep1628

noncomputable def ep1659 := @Enclosure.Complex.IsNear.im_isNear qz245 Bool.true 1345185921738135259 302231454903657293676544 6642529981491399173135 ep1582 Bool.false 1229043572875901579 302231454903657293676544 6071440366321131202015 ep1582

noncomputable def ep1660 := nat_lit 54779698189796108009108978297

noncomputable def ep1661 := nat_lit 54122030851382839077220864370129

noncomputable def ep1662 := nat_lit 2435169097160070258242665357436489

noncomputable def ep1663 := nat_lit 343567669749244155563156367545531831

noncomputable def ep1664 := @Enclosure.Real.IsNear.addLit_ft_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3)))) qz254) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3)))) qz253) ep1660 ep1574 ep1661 ep1576 ep1662 ep1565 ep1663

noncomputable def ep1665 := nat_lit 341352229126313107978868993340872857927824369021523517767680000000

noncomputable def ep1666 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3)))) qz254 44570997643 480000000 0 1 1229043572875901579 302231454903657293676544 6071440366321131202015 ep1582 ep1660

noncomputable def ep1667 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3)))) qz253 1810284405900971 720000000000 0 1 1345185921738135259 302231454903657293676544 6642529981491399173135 ep1582 ep1662

noncomputable abbrev qz530 := (@ep1631 ep1582 (BSN.cpow_neg_s_sub_mk qz149 121891 1000 31 3 27512614111 qz150 rfl EMRow39.d22) ep1656)

noncomputable def ep1668 := ep1572 (@ep1579 ep1580 ep1581 ep1564 ep1565 ep1566 ep1567 (@ep1583 ep1574 ep1575 ep1576 ep1629 (ep1630 qz530) rfl) (@ep1657 ep1565 ep1578 ep1580 ep1658 (ep1659 qz530) rfl) rfl rfl) (@ep1664 ep1580 ep1665 ep1569 ep1565 ep1570 ep1567 (@ep1666 ep1574 ep1661 ep1576 ep1629 (ep1659 qz530) rfl) (@ep1667 ep1565 ep1663 ep1580 ep1658 (ep1630 qz530) rfl) rfl rfl)

noncomputable def ep1669 := @Enclosure.Real.IsNear.mulLit_tt (Complex.im (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)) (Complex.im (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)) ep1569 ep1565 ep1570 ep1567 ep1569 ep1565 ep1570

noncomputable def ep1670 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) qz245) Bool.true ep1564 ep1565 ep1566 ep1567 Bool.true ep1569 ep1565 ep1570

noncomputable def ep1671 := @ep1536 266566037651434669 504403158265495552 42886085089 252201579132747776 (@ep1537 1 3670016 (ep1538 (@ep1539 1048576 1 1048576 (ep1540 (@ep1541 59478663524 14869665881 1000000 0 1 (ep1545 rfl) (ep1548 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) (Enclosure.Real.IsNear.const Bool.false 2 7) rfl) (@ep1549 1309 274877906944 (BSN.norm_eq_sqrt_mul_add (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)) (@ep1550 2618 549755813888 2084751517 137438953472 1309 274877906944 (@ep1555 4169501725 4169504343 274877906944 (@ep1561 ep1557 ep1562 ep1559 ep1563 ep1551 ep1552 ep1553 ep1554 (@ep1568 ep1567 ep1556 ep1557 ep1558 ep1559 (@ep1571 ep1567 ep1668) (@ep1571 ep1567 ep1668) rfl) (@ep1669 ep1567 ep1560 ep1557 ep1562 ep1559 (@ep1670 ep1567 ep1668) (@ep1670 ep1567 ep1668) rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl

theorem EMRow39.d23 : Enclosure.Real.IsNear (@HAdd.hAdd Real Real Real qz402 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz146 1 31))) (@HMul.hMul Real Real Real qz0 qz244 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)))) Bool.false 7367647775376881215 13618885273168379904 802263039908539 6809442636584189952 := ep1534 (ep1535 ep1671) rfl rfl

noncomputable def EMRow39.d24 := fun (I J : @NonemptyInterval Real Real.instLE) => @LE.le Real Real.instLE (@Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE I)) (@Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE J))

noncomputable abbrev qz531 := (EMRow39.d3 qz546 qz596 (@Enclosure.dec_le_dec qz546 qz596 119766 1000 121891 1000 (@Eq.refl Real qz546) (@Eq.refl Real qz596) rfl rfl rfl) 30 31 1 1)

noncomputable abbrev qz263 := qz531

noncomputable def ep1672 := @Zeta.Certificates.ZIntervalEM.Certificate.mk qz263 (@Enclosure.dec_nonneg qz13 119766 1000 qz14) (@Enclosure.pos_of_ble 1 rfl) (@Enclosure.pos_of_ble 30 rfl)

noncomputable abbrev qz264 := (Zeta.Certificates.ZIntervalEM.fstVal qz531)

noncomputable def ep1673 := @Enclosure.Real.IsNear.neg_val qz264 ep404 ep405

noncomputable def ep1674 := @Enclosure.Real.IsNear.of_eq qz264 (hardyZApproximantEM 1 30 qz13) Bool.true

noncomputable abbrev qz265 := (Zeta.Certificates.ZIntervalEM.sndVal qz531)

noncomputable def ep1675 := BSN.mul_neg_of_neg_pos_r qz264 qz265 (@ep1673 ep406 ep407 (@ep1674 ep404 ep405 ep406 ep407 (@Eq.refl Real (hardyZApproximantEM 1 30 qz13)) EMRow39.d11) rfl rfl rfl)

noncomputable def ep1676 := @Enclosure.Real.IsNear.pos_val qz265 ep1020 ep1021

noncomputable def ep1677 := @Enclosure.Real.IsNear.of_eq qz265 (hardyZApproximantEM 1 31 qz149) Bool.false

noncomputable def ep1678 := BSN.gt_trans_le (@Norm.norm Real Real.norm qz264) (BSN.hardyZErrorBoundStrong 1 30 qz13)

noncomputable def ep1679 := @Enclosure.norm_gt_of_isNear qz264 (BSN.hardyZErrorBoundStrong 1 30 qz13) Bool.true

noncomputable def ep1680 := @Enclosure.Real.IsNear.of_eq (BSN.hardyZErrorBoundStrong 1 30 qz13) (@HAdd.hAdd Real Real Real qz402 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 30))) (@HMul.hMul Real Real Real qz0 qz222 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)))) Bool.false 8084415756823414511 13618885273168379904 1529747638769281 13618885273168379904 (@Eq.refl Real (@HAdd.hAdd Real Real Real qz402 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 30))) (@HMul.hMul Real Real Real qz0 qz222 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)))))

noncomputable def ep1681 := BSN.gt_trans_le (@Norm.norm Real Real.norm qz265) (BSN.hardyZErrorBoundStrong 1 31 qz149)

noncomputable def ep1682 := @Enclosure.norm_gt_of_isNear qz265 (BSN.hardyZErrorBoundStrong 1 31 qz149) Bool.false

noncomputable def ep1683 := @Enclosure.Real.IsNear.of_eq (BSN.hardyZErrorBoundStrong 1 31 qz149) (@HAdd.hAdd Real Real Real qz402 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz146 1 31))) (@HMul.hMul Real Real Real qz0 qz244 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)))) Bool.false 7367647775376881215 13618885273168379904 802263039908539 6809442636584189952 (@Eq.refl Real (@HAdd.hAdd Real Real Real qz402 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz146 1 31))) (@HMul.hMul Real Real Real qz0 qz244 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)))))

noncomputable def ep1684 := @List.cons EMRow39.d0 (@PSigma.mk Zeta.Certificates.ZIntervalEM Zeta.Certificates.ZIntervalEM.Certificate qz263 (ep1672 (@Enclosure.pos_of_ble 1 rfl) (@Enclosure.pos_of_ble 31 rfl) (ep1675 (@ep1676 ep1022 ep1023 (@ep1677 ep1020 ep1021 ep1022 ep1023 (@Eq.refl Real (hardyZApproximantEM 1 31 qz149)) EMRow39.d16) rfl rfl rfl)) (ep1678 (hardyZErrorBoundEM 1 30 qz13) (BSN.hardyZErrorBoundEM_le_strong 1 30 qz13 rfl) (@ep1679 Bool.false ep404 ep405 ep406 ep407 8084415756823414511 13618885273168379904 1529747638769281 13618885273168379904 (@ep1674 ep404 ep405 ep406 ep407 (@Eq.refl Real (hardyZApproximantEM 1 30 qz13)) EMRow39.d11) (ep1680 EMRow39.d21) rfl rfl rfl rfl rfl)) (ep1681 (hardyZErrorBoundEM 1 31 qz149) (BSN.hardyZErrorBoundEM_le_strong 1 31 qz149 rfl) (@ep1682 Bool.false ep1020 ep1021 ep1022 ep1023 7367647775376881215 13618885273168379904 802263039908539 6809442636584189952 (@ep1677 ep1020 ep1021 ep1022 ep1023 (@Eq.refl Real (hardyZApproximantEM 1 31 qz149)) EMRow39.d16) (ep1683 EMRow39.d23) rfl rfl rfl rfl rfl)))) (@List.nil EMRow39.d0)

noncomputable abbrev qz532 := (@Enclosure.dec_le_dec qz546 qz596 119766 1000 121891 1000 (@Eq.refl Real qz546) (@Eq.refl Real qz596) rfl rfl rfl)

noncomputable abbrev qz266 := (Zeta.Certificates.CertifiedZeroIntervals.intervals (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedEM ep1684 (@List.IsChain.singleton EMRow39.d1 EMRow39.d24 (EMRow39.d2 qz279 qz441 qz532))))

noncomputable abbrev qz533 := (@NonemptyInterval Real Real.instLE)

noncomputable def ep1685 := And (@Eq (Option Real) (@Option.map qz533 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz533 qz266)) (@Option.some Real qz13))

noncomputable def ep1686 := ep1685 (@Eq (Option Real) (@Option.map qz533 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz533 qz266)) (@Option.some Real qz149))

noncomputable def ep1687 := @And.intro (@Eq Nat (@List.length qz533 qz266) 1) ep1686

noncomputable def ep1688 := @And.intro (@Eq (Option Real) (@Option.map qz533 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz533 qz266)) (@Option.some Real qz13))

noncomputable def ep1689 := @ep1688 (@Eq (Option Real) (@Option.map qz533 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz533 qz266)) (@Option.some Real qz149))

noncomputable abbrev qz267 := (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedEM ep1684 (@List.IsChain.singleton EMRow39.d1 EMRow39.d24 (EMRow39.d2 qz279 qz441 qz532)))

theorem EMRow39.d25 : Zeta.Certificates.BatchSpec 1 119766 1000 121891 1000 := @Exists.intro Zeta.Certificates.CertifiedZeroIntervals (fun (C : Zeta.Certificates.CertifiedZeroIntervals) => And (@Eq Nat (@List.length qz533 (Zeta.Certificates.CertifiedZeroIntervals.intervals C)) 1) (And (@Eq (Option Real) (@Option.map qz533 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz533 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz13)) (@Eq (Option Real) (@Option.map qz533 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz533 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz149)))) qz267 (ep1687 (@Eq.refl Nat 1) (ep1689 (@Eq.refl (Option Real) (@Option.some Real qz13)) (@Eq.refl (Option Real) (@Option.some Real qz149))))

theorem solution : Zeta.Certificates.BatchSpec 1 119766 1000 121891 1000 := EMRow39.d25
#print axioms solution
#check solution
