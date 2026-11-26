-- Prove2me | solution 1 for RHHeight1000.em_main_0044_0044
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-20T08:29:59.756114+00:00
-- url     : https://prove2.me/submissions/cb8b3ba0-c7aa-4dd6-90b6-163e2595db1a

import Definitions.Def_RHT1000_Support_20261118_S005
/- Copyright (c) 2026 Salvatore Mercuri, Bhavik Mehta.
Apache 2.0 license; see the source project LICENSE. -/
set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable def EMRow44.d0 := @PSigma Zeta.Certificates.ZIntervalEM fun (I : Zeta.Certificates.ZIntervalEM) => Zeta.Certificates.ZIntervalEM.Certificate I

noncomputable def EMRow44.d1 := @NonemptyInterval Real Real.instLE

noncomputable def EMRow44.d2 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @NonemptyInterval.mk Real Real.instLE (@Prod.mk Real Real a b) h

noncomputable def EMRow44.d3 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) (fc sc fb sb : Nat) => Zeta.Certificates.ZIntervalEM.mk (EMRow44.d2 a b h) fc sc fb sb

noncomputable def ep0 := nat_lit 26986075409044028275299783

noncomputable def ep1 := nat_lit 4294967296000000000000000

noncomputable def ep2 := nat_lit 26986075409044045455168967

noncomputable abbrev qz268 := (@instHMul Real Real.instMul)

noncomputable abbrev qz0 := qz268

noncomputable abbrev qz269 := (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 2 1) Real.pi)

noncomputable def ep3 := @BSN.isNear_log_image_fff qz269 884279719003555 140737488355328 1 500000000000000 ep0 ep1 ep2 ep1 4138529546116343 2251799813685248 250000000193517 96758500000000000000 4138529546116343 2251799813685248 250000000193517 96758500000000000000 963576 524288

noncomputable abbrev qz270 := (@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 2 1) Real.pi 2 1 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 140737488355328 1 500000000000000 (Enclosure.Real.IsNear.const Bool.false 2 1) BSN.pi_near_15 rfl)

noncomputable def ep4 := @ep3 2 524288 qz270 rfl rfl rfl rfl

noncomputable def ep5 := nat_lit 53972150818088056550599566

noncomputable def ep6 := nat_lit 34359738368000000000000000

noncomputable def ep7 := nat_lit 9806206225044028275299783

noncomputable def ep8 := nat_lit 44165944593044028275299783

noncomputable def ep9 := nat_lit 13681445815609410487519367394620474863599256634174726093703677122907123617368241606644861540940610176751640793056574796245399519365549113997355475306157239709119582688278313060810592403844863400465080549957745

noncomputable def ep10 := nat_lit 231714499556395493334623298703961145503103241611736774613091488581016477543539392410113701224645713379230392133956226737605624599560350113120270717249177907454870984269546186598262646369758174842349131395304

noncomputable def ep11 := nat_lit 8978369550011295664474073352761810093897501552430546263638635096022803738134167562509900960712119243631997923545019968443113540909076206607473711060286601587364321108377403290080403445693385008949995305

noncomputable def ep12 := BSN.log_dyadic_bound ep7 ep8 5 4 ep9 1048576 387034 ep10 ep11 473518 ep5 ep6 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP ep7) (BSN.artanhQ ep8) 0 4 ep10 ep9 ep11 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz271 := (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))

noncomputable abbrev qz1 := qz271

noncomputable def ep13 := ep4 rfl rfl rfl rfl (BSN.isNear_log_sfrac ep0 ep1 4138529546116343 2251799813685248 250000000193517 96758500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep0) (@Nat.cast Real Real.instNatCast ep1))) Bool.false 69433004117575847641088 37778931862957161709568 1000000000774068 387034000000000000000 4138529546116343 2251799813685248 250000000193517 96758500000000000000 (BSN.log_rat_reduce_isNear ep0 ep1 2 ep5 ep6 473518 1048576 24973259072661432 36028797018963968 387034 1000000000000000 rfl rfl rfl rfl (ep12 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep14 := nat_lit 53972150818088090910337934

noncomputable def ep15 := nat_lit 9806206225044045455168967

noncomputable def ep16 := nat_lit 44165944593044045455168967

noncomputable def ep17 := nat_lit 13681445815609453062485491347592146866046743284321690683909457683007658987562290830600045658905080811372395010565947827677605470036294121079488508864180301737865471494204890974265645509835068840465080549957745

noncomputable def ep18 := nat_lit 231714499556396865510889920206523150079811393376960301632499817942333196803513131357563499488546302200815366867712007119763002650772307103678175657719139104636874731038771518520299266622696414842349131395304

noncomputable def ep19 := nat_lit 8978369550011421500876706511871067098718760264493934208903156435737864998391937547068187824077011975074541700434630537294838404525415248443919841847024664017658842168336182958576672102333385008949995305

noncomputable def ep20 := BSN.log_dyadic_bound ep15 ep16 5 4 ep17 1048576 387034 ep18 ep19 473518 ep14 ep6 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP ep15) (BSN.artanhQ ep16) 0 4 ep18 ep17 ep19 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep21 := ep13 (BSN.isNear_log_sfrac ep2 ep1 4138529546116343 2251799813685248 250000000193517 96758500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep2) (@Nat.cast Real Real.instNatCast ep1))) Bool.false 69433004117575847641088 37778931862957161709568 1000000000774068 387034000000000000000 4138529546116343 2251799813685248 250000000193517 96758500000000000000 (BSN.log_rat_reduce_isNear ep2 ep1 2 ep14 ep6 473518 1048576 24973259072661432 36028797018963968 387034 1000000000000000 rfl rfl rfl rfl (ep20 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable abbrev qz2 := (Real.log (@HMul.hMul Real Real Real qz268 (2 : Real) Real.pi))

theorem EMRow44.d4 : Enclosure.Real.IsNear qz2 Bool.false 120447 65536 1 262144 := @Enclosure.Real.IsNear.of_eq qz2 (Real.log qz269) Bool.false 120447 65536 1 262144 BSN.log_two_pi_eq (@Enclosure.Real.IsNear.recentre' (Real.log qz269) Bool.false 963576 524288 2 524288 120447 65536 1 262144 (ep21 rfl rfl rfl rfl rfl rfl rfl rfl) rfl)

noncomputable def ep22 := nat_lit 8589934592000000000000000

noncomputable def ep23 := @BSN.isNear_log_image_fff Real.pi 226375608064910080 72057594037927936 1 1000000000000000 ep0 ep22 ep2 ep22 1200336 1048576 1 387034 1200336 1048576 1 387034 600168 524288 2 524288 BSN.pi_near_15 rfl rfl rfl

noncomputable def ep24 := nat_lit 17179869184000000000000000

noncomputable def ep25 := nat_lit 18396140817044028275299783

noncomputable def ep26 := nat_lit 35576010001044028275299783

noncomputable def ep27 := nat_lit 145019262663961446558303139663424756232419223153299357158415217874016130572233056993847515999529612750616182853355499335896178729185698845314776375864537073527142908641610750276034469165612529925303649396973267518946591078603565291376312767403717761600170009932259137778521478520425507632472584532570900560707662248426541531715360699177249902784721815296292248142738824858695953661559845440650653128788875447728828657762006237171740033404723254477174341920697506370253193455781322964835857351124092897592956162654178130575

noncomputable def ep28 := nat_lit 15500762873619990602332184736899274490522931101512051618692838888825382235673431503644115344741331161500627469184702974962114537943617674254904297224139410345221262767191485292268260077615645253784097850065864022184521411511133693085443040736512010941548648374196772723338837137976260321103066698629790037694560548409922339907589559883712609967105556007429010014773911317423638534096849366294542840133852248768895750397896505791271178551667935288585787166713880920071720072716082683081155281219708172458141800988558163320

noncomputable def ep29 := nat_lit 12900190794487083783367107939442176642390171280542213571554777169279725287102813254708993369099729304728646904879886535518616983985412662170766446331701281703998252143668221340329975389245922410714088123244705567402747658401492589451585970559635763980329972215329212888079422466283203384882259392047898400615815810081169907384366653346471604103896809335921621947903075223769953790093549808584241881353287841076643853121427928248525828402335494512605306631304432120211393210317325496757155861061354331245840675149075

noncomputable def ep30 := BSN.log_dyadic_bound ep25 ep26 11 10 ep27 1048576 387034 ep28 ep29 1200336 ep5 ep24 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base10 (BSN.artanhP ep25) (BSN.artanhQ ep26) 0 10 ep28 ep27 ep29 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep31 := nat_lit 18396140817044045455168967

noncomputable def ep32 := nat_lit 35576010001044045455168967

noncomputable def ep33 := nat_lit 145019262663962847171784895425483977818796535899227200426399035286881207006285364467913811844950531107314785650583974625982406238691319033447632878979985852280879486690814033867010958364699188952871572448188560932645032521756218245629809291975913196623825614492380080480004685076434733043183791438169545293975334857826316990371107134320667652578346815517853870648072772035977941843998949310557583393428557296298890786965786350523173236912472938174255438182435383147950274229549088258679583524155427309880956162654178130575

noncomputable def ep34 := nat_lit 15500762873620157189619721156942591192100275120160672416764593300158228469749443299607348495591439275767946573253526107895503597951484257520435868240203420954375895980141891044871083424251900562230440202302413072793440172565998181227591194192658878334739610458454844032013325963992941389843551995646587189684848765634635122388286241104146031552341815777883628509454807838726994150833304950745987647656768534710890974432620160470644835720379148964170536679305861738540146791997074363921127776563807649880221800988558163320

noncomputable def ep35 := nat_lit 12900190794487324729109480814509220959173684627296055849229843377126536688487849343376525559792931631054411655715865486295286288812423905434305314401904993536755333953308594664509631000767632482919425633906965368325056855874260596615770736441041599390097968820060635361729170158825410327022636428624381203910573184452046894301676992229743752846881064485858738985580654099214803581683226335297196686880535448467637789069028262446657986458573827723305156755787640135484017403116612632808333639900906331245840675149075

noncomputable def ep36 := BSN.log_dyadic_bound ep31 ep32 11 10 ep33 1048576 387034 ep34 ep35 1200336 ep14 ep24 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base10 (BSN.artanhP ep31) (BSN.artanhQ ep32) 0 10 ep34 ep33 ep35 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep37 := @Enclosure.Real.IsNear.recentre' (Real.log Real.pi) Bool.false 600168 524288 2 524288 75021 65536 1 262144 (ep23 rfl rfl rfl rfl rfl (BSN.isNear_log_sfrac ep0 ep22 1200336 1048576 1 387034 Bool.false (BSN.logfrac_isNear ep5 ep24 1 ep0 ep22 1200336 1048576 387034 rfl rfl rfl (ep30 rfl))) (BSN.isNear_log_sfrac ep2 ep22 1200336 1048576 1 387034 Bool.false (BSN.logfrac_isNear ep14 ep24 1 ep2 ep22 1200336 1048576 387034 rfl rfl rfl (ep36 rfl))) rfl rfl rfl rfl rfl rfl rfl rfl) rfl

theorem EMRow44.d5 : Enclosure.Real.IsNear (Real.log Real.pi) Bool.false 75021 65536 1 262144 := ep37

noncomputable abbrev qz664 := (@HAdd.hAdd Complex Complex Complex (@instHAdd Complex Complex.instAdd) (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (2 : Complex)) (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul) Complex.I ↑(Enclosure.sfrac Bool.false 130272 1000)))

noncomputable abbrev qz534 := qz664

noncomputable abbrev qz272 := qz534

noncomputable abbrev qz3 := (BSN.headSumC qz272 9)

noncomputable abbrev qz665 := (@instHAdd Complex Complex.instAdd)

noncomputable abbrev qz535 := qz665

noncomputable abbrev qz273 := qz535

noncomputable abbrev qz4 := qz273

noncomputable abbrev qz5 := qz272

noncomputable abbrev qz536 := (@instHPow Complex Complex Complex.instPow)

noncomputable abbrev qz274 := qz536

noncomputable abbrev qz6 := qz274

noncomputable abbrev qz537 := (@Neg.neg Complex Complex.instNeg qz664)

noncomputable abbrev qz275 := qz537

noncomputable abbrev qz7 := qz275

noncomputable abbrev qz538 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 8) qz7)

noncomputable def ep38 := @Enclosure.Complex.IsNear.of_eq qz3 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 8) qz538) Bool.false 637992116669 1099511627776 487975807065441 212774191672328192 Bool.true 354427700139 549755813888 122106883981807 53193547918082048

noncomputable def ep39 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 8) qz538 Bool.false 172362964115 549755813888 109178068287203 53193547918082048 Bool.true 453688825629 1099511627776 437183889752689 212774191672328192 Bool.false

noncomputable abbrev qz539 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 7) qz7)

noncomputable def ep40 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 8) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 7) qz539) Bool.false 172362964115 549755813888 109178068287203 53193547918082048 Bool.true 453688825629 1099511627776 437183889752689 212774191672328192

noncomputable def ep41 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 7) qz539 Bool.false 289549925415 549755813888 190979155873293 106387095836164096 Bool.true 110508630179 1099511627776 382376800580317 212774191672328192 Bool.true

noncomputable abbrev qz540 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 6) qz7)

noncomputable def ep42 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 7) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 6) qz540) Bool.false 289549925415 549755813888 190979155873293 106387095836164096 Bool.true 110508630179 1099511627776 382376800580317 212774191672328192

noncomputable def ep43 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 6) qz540 Bool.false 156837729993 549755813888 161410517186187 106387095836164096 Bool.false 251481821485 1099511627776 323195869641245 212774191672328192 Bool.false

noncomputable abbrev qz541 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 5) qz7)

noncomputable def ep44 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 6) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 5) qz541) Bool.false 156837729993 549755813888 161410517186187 106387095836164096 Bool.false 251481821485 1099511627776 323195869641245 212774191672328192

noncomputable def ep45 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 5) qz541 Bool.false 324161016711 549755813888 64508188325897 53193547918082048 Bool.false 611753926223 1099511627776 258397013642477 212774191672328192 Bool.true

noncomputable abbrev qz542 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 4) qz7)

noncomputable def ep46 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 5) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 4) qz542) Bool.false 324161016711 549755813888 64508188325897 53193547918082048 Bool.false 611753926223 1099511627776 258397013642477 212774191672328192

noncomputable def ep47 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 4) qz542 Bool.false 673800808761 1099511627776 185742334030579 212774191672328192 Bool.false 7823754045 137438953472 23239162440873 26596773959041024 Bool.true

noncomputable abbrev qz543 := (@Nat.cast Complex Complex.instNatCast 3)

noncomputable abbrev qz276 := qz543

noncomputable abbrev qz8 := qz276

noncomputable def ep48 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 4) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 3) (@HPow.hPow Complex Complex Complex qz6 qz8 qz7)) Bool.false 673800808761 1099511627776 185742334030579 212774191672328192 Bool.false 7823754045 137438953472 23239162440873 26596773959041024

noncomputable def ep49 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 3) (@HPow.hPow Complex Complex Complex qz6 qz8 qz7) Bool.false 281358742803 549755813888 51180501577439 106387095836164096 Bool.true 140604336015 274877906944 25591922678841 53193547918082048 Bool.false

noncomputable abbrev qz544 := (@Nat.cast Complex Complex.instNatCast 2)

noncomputable abbrev qz277 := qz544

noncomputable abbrev qz9 := qz277

noncomputable def ep50 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 3) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 2) (@HPow.hPow Complex Complex Complex qz6 qz9 qz7)) Bool.false 281358742803 549755813888 51180501577439 106387095836164096 Bool.true 140604336015 274877906944 25591922678841 53193547918082048

noncomputable def ep51 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 2) (@HPow.hPow Complex Complex Complex qz6 qz9 qz7) Bool.false 1 1 0 1 Bool.false 0 1 0 1 Bool.true

noncomputable abbrev qz278 := (Enclosure.sfrac Bool.false 0 1)

noncomputable abbrev qz10 := qz278

noncomputable def ep52 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 2) (Complex.mk (Enclosure.sfrac Bool.false 1 1) qz10) Bool.false 1 1 0 1 Bool.false 0 1 0 1 (BSN.head_sum_c_two qz5)

noncomputable abbrev qz666 := (Enclosure.sfrac Bool.false 130272 1000)

noncomputable abbrev qz545 := qz666

noncomputable abbrev qz279 := qz545

noncomputable abbrev qz280 := (Enclosure.sfrac Bool.false 2 1)

noncomputable abbrev qz11 := (@HMul.hMul Real Real Real qz268 qz279 (Real.log qz280))

noncomputable abbrev qz12 := qz279

noncomputable abbrev qz281 := (@Eq.refl Real qz545)

noncomputable abbrev qz13 := qz281

noncomputable abbrev qz282 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 2)))

noncomputable def ep53 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz9 qz7) (Complex.mk (@HMul.hMul Real Real Real qz0 qz282 (Real.cos qz11)) (@HMul.hMul Real Real Real qz0 qz282 (@Neg.neg Real Real.instNeg (Real.sin qz11)))) Bool.true 268397071085 549755813888 51180501577439 106387095836164096 Bool.true 140604336015 274877906944 25591922678841 53193547918082048 (BSN.cpow_neg_s_mk qz12 130272 1000 2 qz13 rfl)

noncomputable abbrev qz14 := (@Nat.cast Real Real.instNatCast 1)

noncomputable abbrev qz283 := (Real.sqrt (@Nat.cast Real Real.instNatCast 2))

noncomputable abbrev qz284 := (@Nat.cast Real Real.instNatCast 2)

noncomputable def ep54 := @Enclosure.Real.IsNear.inv_image qz283 1482911 1048576 1 1048576 370727 370728 524288 (@Enclosure.Real.IsNear.of_eq qz283 (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz284 qz14)) Bool.false 1482911 1048576 1 1048576 (BSN.sqrt_natCast_div_one 2) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz284 qz14)) Bool.false 1482911 1048576 1 1048576 1482911 1048576 1 1048576 (BSN.sqrt_enclosure 2 1 741455 741456 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep55 := BSN.log_dyadic_bound 1 3 6 5 613814355 524288 193517 24381081 945 363408 4 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 1) (BSN.artanhQ 3) 0 5 24381081 613814355 945 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep56 := nat_lit 7173791674376708010234701701066963216

noncomputable def ep57 := nat_lit 2552117751907038475975309555738261585920

noncomputable def ep58 := nat_lit 17864824263349269331827166890167831101440

noncomputable abbrev qz15 := (BSN.sinEvenQ 2147483648)

noncomputable abbrev qz16 := (BSN.sinOddQ 2147483648)

noncomputable def ep59 := BSN.sin_dyadic_bound_f 1636579814 2147483648 2 1 1048576 387412 ep56 ep57 ep56 ep56 ep58 ep56 723974 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1636579814) qz15 0 1 ep56 ep57 ep56 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1636579814) qz16 0 1 ep56 ep58 ep56 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz17 := (@Nat.cast Real Real.instNatCast 1048576)

noncomputable abbrev qz18 := (Enclosure.Real.IsNear.const Bool.false 130272 1000)

noncomputable abbrev qz19 := (@Nat.cast Real Real.instNatCast 151115727451828646838272)

noncomputable abbrev qz285 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 94683773) qz17)

noncomputable abbrev qz286 := (BSN.isNear_log_sfrac 2 1 363408 524288 1 193517 Bool.false (BSN.logfrac_isNear 4 2 1 2 1 363408 524288 193517 rfl rfl rfl (ep55 rfl)))

noncomputable def ep60 := @Enclosure.Real.IsNear.cos_image qz11 qz285 Bool.false 94683773 1048576 707 1048576 Bool.true 723974 1048576 1 193517 (@Enclosure.Real.IsNear.recentre' qz11 Bool.false 92464623 1024000 16284 24189625 94683773 1048576 707 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz12 (Real.log qz280) 130272 1000 0 1 363408 524288 1 193517 92464623 1024000 16284 24189625 qz18 qz286 rfl) rfl) (Enclosure.sfrac_false_div 94683773 1048576) (BSN.cos_reduce1 qz285 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 115164066297188498538496) qz19) 226375608064910080 72057594037927936 Bool.false 723974 1048576 14 1000000000000000 387034 193517 (BSN.sin_reduce_arg_pos_rat_q1 94683773 1048576 226375608064910080 72057594037927936 14 115164066297188498538496 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 723974 1048576 115164066297188498538496 151115727451828646838272 1636579814 2147483648 387412 387034 (ep59 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep61 := nat_lit 256368518416223344748019237273646015576426772600520486687528460344378786324736

noncomputable def ep62 := nat_lit 18237254054877300779212430138868345486890022584838388836214569481246317918289920

noncomputable def ep63 := nat_lit 51463286987356571850843528622950623392370313236168846482403744904297062656

noncomputable def ep64 := nat_lit 769002628674695321100356024763692145482495577175089122369620573543327764848896

noncomputable def ep65 := nat_lit 820676432469478535064559356249075546910051016317727497629655626656084306323046400

noncomputable abbrev qz20 := (BSN.cosEvenQ 2147483648)

noncomputable abbrev qz21 := (BSN.cosOddQ 2147483648)

noncomputable def ep66 := BSN.cos_dyadic_bound_f 1636579814 2147483648 3 2 1048576 387412 ep61 ep62 ep63 ep64 ep65 ep63 758532 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1636579814) qz20 0 2 ep61 ep62 ep63 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1636579814) qz21 0 2 ep64 ep65 ep63 rfl rfl rfl rfl) rfl rfl

noncomputable def ep67 := @Enclosure.Real.IsNear.sin_image qz11 qz285 Bool.false 94683773 1048576 707 1048576 Bool.false 758532 1048576 1 193517 (@Enclosure.Real.IsNear.recentre' qz11 Bool.false 92464623 1024000 16284 24189625 94683773 1048576 707 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz12 (Real.log qz280) 130272 1000 0 1 363408 524288 1 193517 92464623 1024000 16284 24189625 qz18 qz286 rfl) rfl) (Enclosure.sfrac_false_div 94683773 1048576) (BSN.sin_reduce1 qz285 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 115164066297188498538496) qz19) 226375608064910080 72057594037927936 Bool.false 758532 1048576 14 1000000000000000 387034 193517 (BSN.sin_reduce_arg_pos_rat_q1 94683773 1048576 226375608064910080 72057594037927936 14 115164066297188498538496 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 758532 1048576 115164066297188498538496 151115727451828646838272 1636579814 2147483648 387412 387034 (ep66 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz287 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 2))) Bool.false 741455 1048576 1 1048576 741455 1048576 1 1048576 (ep54 rfl rfl) rfl)

noncomputable def ep68 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz282 (Real.cos qz11)) (@HMul.hMul Real Real Real qz0 qz282 (@Neg.neg Real Real.instNeg (Real.sin qz11))) Bool.true 268397071085 549755813888 51180501577439 106387095836164096 Bool.true 140604336015 274877906944 25591922678841 53193547918082048 (@Enclosure.Real.IsNear.mulLit_ft qz282 (Real.cos qz11) 741455 1048576 1 1048576 361987 524288 137865095 202917281792 268397071085 549755813888 51180501577439 106387095836164096 qz287 (@Enclosure.Real.IsNear.recentre' (Real.cos qz11) Bool.true 723974 1048576 137865095 202917281792 361987 524288 137865095 202917281792 (ep60 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz282 (@Neg.neg Real Real.instNeg (Real.sin qz11)) 741455 1048576 1 1048576 189633 262144 137865095 202917281792 140604336015 274877906944 25591922678841 53193547918082048 qz287 (@Enclosure.Real.IsNear.neg (Real.sin qz11) Bool.false 189633 262144 137865095 202917281792 (@Enclosure.Real.IsNear.recentre' (Real.sin qz11) Bool.false 758532 1048576 137865095 202917281792 189633 262144 137865095 202917281792 (ep67 rfl rfl) rfl)) rfl)

noncomputable abbrev qz546 := (Enclosure.Real.IsNear.const Bool.false 0 1)

noncomputable abbrev qz22 := qz546

noncomputable def ep69 := @ep51 268397071085 549755813888 51180501577439 106387095836164096 Bool.true 140604336015 274877906944 25591922678841 53193547918082048 Bool.false 281358742803 281358742803 549755813888 51180501577439 106387095836164096 Bool.true 140604336015 140604336015 274877906944 25591922678841 53193547918082048 (ep52 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 1) qz10 Bool.false 1 1 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 1) qz22)) (ep53 ep68) rfl rfl

noncomputable abbrev qz547 := (Real.log (Enclosure.sfrac Bool.false 3 1))

noncomputable abbrev qz23 := (@HMul.hMul Real Real Real qz268 qz279 qz547)

noncomputable abbrev qz288 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 3)))

noncomputable def ep70 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz8 qz7) (Complex.mk (@HMul.hMul Real Real Real qz0 qz288 (Real.cos qz23)) (@HMul.hMul Real Real Real qz0 qz288 (@Neg.neg Real Real.instNeg (Real.sin qz23)))) Bool.false 111083323155 1099511627776 83381330875701 212774191672328192 Bool.false 156251844105 274877906944 20886402202905 53193547918082048 (BSN.cpow_neg_s_mk qz12 130272 1000 3 qz13 rfl)

noncomputable abbrev qz289 := (Real.sqrt (@Nat.cast Real Real.instNatCast 3))

noncomputable abbrev qz290 := (@Nat.cast Real Real.instNatCast 3)

noncomputable def ep71 := @Enclosure.Real.IsNear.inv_image qz289 1816187 1048576 1 1048576 302697 302698 524288 (@Enclosure.Real.IsNear.of_eq qz289 (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz290 qz14)) Bool.false 1816187 1048576 1 1048576 (BSN.sqrt_natCast_div_one 3) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz290 qz14)) Bool.false 1816187 1048576 1 1048576 1816187 1048576 1 1048576 (BSN.sqrt_enclosure 3 1 908093 908094 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep72 := BSN.log_dyadic_bound 1 2 10 9 171633298636800 524288 193517 16925142283965 34459425 575989 3 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base9 (BSN.artanhP 1) (BSN.artanhQ 2) 0 9 16925142283965 171633298636800 34459425 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep73 := nat_lit 20357820324651621110333612664837136

noncomputable def ep74 := BSN.sin_dyadic_bound_f 377731166 2147483648 2 1 1048576 387412 ep73 ep57 ep73 ep73 ep58 ep73 183489 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 377731166) qz15 0 1 ep73 ep57 ep73 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 377731166) qz16 0 1 ep73 ep58 ep73 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz24 := (@Nat.cast Real Real.instNatCast 524288)

noncomputable abbrev qz25 := (@Nat.cast Real Real.instNatCast 75557863725914323419136)

noncomputable abbrev qz291 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 75035239) qz24)

noncomputable abbrev qz292 := (BSN.isNear_log_sfrac 3 1 575989 524288 1 193517 Bool.false (BSN.logfrac_isNear 3 1 2 3 1 575989 524288 193517 rfl rfl rfl (ep72 rfl)))

noncomputable def ep75 := @Enclosure.Real.IsNear.cos_image qz23 qz291 Bool.false 75035239 524288 353 524288 Bool.false 183489 1048576 1 193517 (@Enclosure.Real.IsNear.recentre' qz23 Bool.false 2344851219 16384000 16284 24189625 75035239 524288 353 524288 (@Enclosure.Real.IsNear.mulLit_ff qz12 qz547 130272 1000 0 1 575989 524288 1 193517 2344851219 16384000 16284 24189625 qz18 qz292 rfl) rfl) (Enclosure.sfrac_false_div 75035239 524288) (BSN.cos_reduce3 qz291 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 13290233898458066976768) qz25) 226375608064910080 72057594037927936 Bool.false 183489 1048576 22 1000000000000000 387034 193517 (BSN.sin_reduce_arg_pos_rat_q3 75035239 524288 226375608064910080 72057594037927936 22 13290233898458066976768 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 183489 1048576 13290233898458066976768 75557863725914323419136 377731166 2147483648 387412 387034 (ep74 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep76 := nat_lit 510423550381407695195061911147652317184

noncomputable def ep77 := nat_lit 7656353255721115427925928667214784757760

noncomputable def ep78 := BSN.cos_dyadic_bound_f 377731166 2147483648 2 1 1048576 387412 ep73 ep76 ep73 ep73 ep77 ep73 1032396 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 377731166) qz20 0 1 ep73 ep76 ep73 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 377731166) qz21 0 1 ep73 ep77 ep73 rfl rfl rfl rfl) rfl rfl

noncomputable def ep79 := @Enclosure.Real.IsNear.sin_image qz23 qz291 Bool.false 75035239 524288 353 524288 Bool.true 1032396 1048576 1 193517 (@Enclosure.Real.IsNear.recentre' qz23 Bool.false 2344851219 16384000 16284 24189625 75035239 524288 353 524288 (@Enclosure.Real.IsNear.mulLit_ff qz12 qz547 130272 1000 0 1 575989 524288 1 193517 2344851219 16384000 16284 24189625 qz18 qz292 rfl) rfl) (Enclosure.sfrac_false_div 75035239 524288) (BSN.sin_reduce3 qz291 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 13290233898458066976768) qz25) 226375608064910080 72057594037927936 Bool.false 1032396 1048576 22 1000000000000000 387034 193517 (BSN.sin_reduce_arg_pos_rat_q3 75035239 524288 226375608064910080 72057594037927936 22 13290233898458066976768 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1032396 1048576 13290233898458066976768 75557863725914323419136 377731166 2147483648 387412 387034 (ep78 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz293 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 3))) Bool.false 605395 1048576 1 1048576 605395 1048576 1 1048576 (ep71 rfl rfl) rfl)

noncomputable def ep80 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz288 (Real.cos qz23)) (@HMul.hMul Real Real Real qz0 qz288 (@Neg.neg Real Real.instNeg (Real.sin qz23))) Bool.false 111083323155 1099511627776 83381330875701 212774191672328192 Bool.false 156251844105 274877906944 20886402202905 53193547918082048 (@Enclosure.Real.IsNear.mulLit_ff qz288 (Real.cos qz23) 605395 1048576 1 1048576 183489 1048576 68835789 101458640896 111083323155 1099511627776 83381330875701 212774191672328192 qz293 (@Enclosure.Real.IsNear.recentre' (Real.cos qz23) Bool.false 183489 1048576 68835789 101458640896 183489 1048576 68835789 101458640896 (ep75 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz288 (@Neg.neg Real Real.instNeg (Real.sin qz23)) 605395 1048576 1 1048576 258099 262144 68835789 101458640896 156251844105 274877906944 20886402202905 53193547918082048 qz293 (@Enclosure.Real.IsNear.neg (Real.sin qz23) Bool.true 258099 262144 68835789 101458640896 (@Enclosure.Real.IsNear.recentre' (Real.sin qz23) Bool.true 1032396 1048576 68835789 101458640896 258099 262144 68835789 101458640896 (ep79 rfl rfl) rfl)) rfl)

noncomputable def ep81 := @ep49 111083323155 1099511627776 83381330875701 212774191672328192 Bool.false 156251844105 274877906944 20886402202905 53193547918082048 Bool.false 370425912018796195872768 673800808761 1099511627776 185742334030579 212774191672328192 Bool.false 4301154272668507176960 7823754045 137438953472 23239162440873 26596773959041024 (ep50 (BSN.head_sum_c_succ qz5 2 3 rfl rfl) (ep69 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep70 ep80) rfl rfl

noncomputable abbrev qz548 := (Real.log (Enclosure.sfrac Bool.false 4 1))

noncomputable abbrev qz26 := (@HMul.hMul Real Real Real qz268 qz279 qz548)

noncomputable abbrev qz294 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 4)))

noncomputable def ep82 := @Enclosure.Complex.IsNear.of_eq qz542 (Complex.mk (@HMul.hMul Real Real Real qz0 qz294 (Real.cos qz26)) (@HMul.hMul Real Real Real qz0 qz294 (@Neg.neg Real Real.instNeg (Real.sin qz26)))) Bool.true 25478775339 1099511627776 72290419273009 212774191672328192 Bool.false 549163893863 1099511627776 72483714115493 212774191672328192 (BSN.cpow_neg_s_mk qz12 130272 1000 4 qz13 rfl)

noncomputable abbrev qz295 := (Real.sqrt (@Nat.cast Real Real.instNatCast 4))

noncomputable abbrev qz296 := (@Nat.cast Real Real.instNatCast 4)

noncomputable def ep83 := @Enclosure.Real.IsNear.inv_image qz295 2097153 1048576 1 1048576 262143 262144 524288 (@Enclosure.Real.IsNear.of_eq qz295 (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz296 qz14)) Bool.false 2097153 1048576 1 1048576 (BSN.sqrt_natCast_div_one 4) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz296 qz14)) Bool.false 2097153 1048576 1 1048576 2097153 1048576 1 1048576 (BSN.sqrt_enclosure 4 1 1048576 1048577 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep84 := nat_lit 318077276165597140789031982421875

noncomputable def ep85 := nat_lit 49379992292270016474244603430625

noncomputable def ep86 := nat_lit 20095619060363156210525625

noncomputable def ep87 := BSN.log_dyadic_bound 3 5 14 13 ep84 524288 193517 ep85 ep86 726817 8 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base13 (BSN.artanhP 3) (BSN.artanhQ 5) 0 13 ep85 ep84 ep86 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep88 := nat_lit 4116954628064624453698687877334111275255071524513042215757053750298547910190625

noncomputable def ep89 := nat_lit 13191889340565136142537054767657356953217901643688899745690942982277625390625

noncomputable def ep90 := nat_lit 12324480105512743088810989522467019111858778770251748847779779364931088479790625

noncomputable def ep91 := BSN.cos_dyadic_bound_f 3273696205 2147483648 3 2 1048576 387412 ep88 ep62 ep89 ep90 ep65 ep89 48597 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3273696205) qz20 0 2 ep88 ep62 ep89 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3273696205) qz21 0 2 ep90 ep65 ep89 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz297 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 369859) (@Nat.cast Real Real.instNatCast 2048))

noncomputable abbrev qz298 := (BSN.isNear_log_sfrac 4 1 726817 524288 1 193517 Bool.false (BSN.logfrac_isNear 8 2 1 4 1 726817 524288 193517 rfl rfl rfl (ep87 rfl)))

noncomputable def ep92 := @Enclosure.Real.IsNear.cos_image qz26 qz297 Bool.false 369859 2048 707 1048576 Bool.true 48597 1048576 1 193517 (@Enclosure.Real.IsNear.recentre' qz26 Bool.false 2958872007 16384000 16284 24189625 369859 2048 707 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz12 qz548 130272 1000 0 1 726817 524288 1 193517 2958872007 16384000 16284 24189625 qz18 qz298 rfl) rfl) (Enclosure.sfrac_false_div 369859 2048) (BSN.cos_reduce2 qz297 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 449933380417290764288) (@Nat.cast Real Real.instNatCast 295147905179352825856)) 226375608064910080 72057594037927936 Bool.false 48597 1048576 28 1000000000000000 387034 193517 (BSN.sin_reduce_arg_pos_rat_q2 369859 2048 226375608064910080 72057594037927936 28 449933380417290764288 295147905179352825856 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 48597 1048576 449933380417290764288 295147905179352825856 3273696205 2147483648 387412 387034 (ep91 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep93 := nat_lit 7399964819043871907743608535387274409896554422808524868566143996151564138030625

noncomputable def ep94 := nat_lit 164135286493895707012911871249815109382010203263545499525931125331216861264609280

noncomputable def ep95 := nat_lit 19359501943325416204621533789723797257519099266599211675227829891758980396590625

noncomputable def ep96 := nat_lit 3009146919054754628570050972913277005336853726498334157975403964405642456517836800

noncomputable def ep97 := BSN.sin_dyadic_bound_f 3273696205 2147483648 3 2 1048576 387412 ep93 ep94 ep89 ep95 ep96 ep89 1047449 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3273696205) qz15 0 2 ep93 ep94 ep89 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3273696205) qz16 0 2 ep95 ep96 ep89 rfl rfl rfl rfl) rfl rfl

noncomputable def ep98 := @Enclosure.Real.IsNear.sin_image qz26 qz297 Bool.false 369859 2048 707 1048576 Bool.true 1047449 1048576 1 193517 (@Enclosure.Real.IsNear.recentre' qz26 Bool.false 2958872007 16384000 16284 24189625 369859 2048 707 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz12 qz548 130272 1000 0 1 726817 524288 1 193517 2958872007 16384000 16284 24189625 qz18 qz298 rfl) rfl) (Enclosure.sfrac_false_div 369859 2048) (BSN.sin_reduce2 qz297 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 449933380417290764288) (@Nat.cast Real Real.instNatCast 295147905179352825856)) 226375608064910080 72057594037927936 Bool.false 1047449 1048576 28 1000000000000000 387034 193517 (BSN.sin_reduce_arg_pos_rat_q2 369859 2048 226375608064910080 72057594037927936 28 449933380417290764288 295147905179352825856 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1047449 1048576 449933380417290764288 295147905179352825856 3273696205 2147483648 387412 387034 (ep97 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz299 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 4))) Bool.false 524287 1048576 1 1048576 524287 1048576 1 1048576 (ep83 rfl rfl) rfl)

noncomputable def ep99 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz294 (Real.cos qz26)) (@HMul.hMul Real Real Real qz0 qz294 (@Neg.neg Real Real.instNeg (Real.sin qz26))) Bool.true 25478775339 1099511627776 72290419273009 212774191672328192 Bool.false 549163893863 1099511627776 72483714115493 212774191672328192 (@Enclosure.Real.IsNear.mulLit_ft qz294 (Real.cos qz26) 524287 1048576 1 1048576 48597 1048576 137865095 202917281792 25478775339 1099511627776 72290419273009 212774191672328192 qz299 (@Enclosure.Real.IsNear.recentre' (Real.cos qz26) Bool.true 48597 1048576 137865095 202917281792 48597 1048576 137865095 202917281792 (ep92 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz294 (@Neg.neg Real Real.instNeg (Real.sin qz26)) 524287 1048576 1 1048576 1047449 1048576 137865095 202917281792 549163893863 1099511627776 72483714115493 212774191672328192 qz299 (@Enclosure.Real.IsNear.neg (Real.sin qz26) Bool.true 1047449 1048576 137865095 202917281792 (@Enclosure.Real.IsNear.recentre' (Real.sin qz26) Bool.true 1047449 1048576 137865095 202917281792 1047449 1048576 137865095 202917281792 (ep98 rfl rfl) rfl)) rfl)

noncomputable def ep100 := @ep47 25478775339 1099511627776 72290419273009 212774191672328192 Bool.false 549163893863 1099511627776 72483714115493 212774191672328192 Bool.false 712837614290869495529472 324161016711 549755813888 64508188325897 53193547918082048 Bool.false 84078819402476217696256 611753926223 1099511627776 258397013642477 212774191672328192 (ep48 (BSN.head_sum_c_succ qz5 3 4 rfl rfl) (ep81 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep82 ep99) rfl rfl

noncomputable abbrev qz549 := (Real.log (Enclosure.sfrac Bool.false 5 1))

noncomputable abbrev qz27 := (@HMul.hMul Real Real Real qz268 qz279 qz549)

noncomputable abbrev qz300 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 5)))

noncomputable def ep101 := @Enclosure.Complex.IsNear.of_eq qz541 (Complex.mk (@HMul.hMul Real Real Real qz0 qz300 (Real.cos qz27)) (@HMul.hMul Real Real Real qz0 qz300 (@Neg.neg Real Real.instNeg (Real.sin qz27)))) Bool.true 83661643359 274877906944 32394140534393 106387095836164096 Bool.true 180136052369 549755813888 4049928499923 13298386979520512 (BSN.cpow_neg_s_mk qz12 130272 1000 5 qz13 rfl)

noncomputable abbrev qz301 := (Real.sqrt (@Nat.cast Real Real.instNatCast 5))

noncomputable abbrev qz302 := (@Nat.cast Real Real.instNatCast 5)

noncomputable def ep102 := @Enclosure.Real.IsNear.inv_image qz301 2344687 1048576 1 1048576 234468 234469 524288 (@Enclosure.Real.IsNear.of_eq qz301 (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz302 qz14)) Bool.false 2344687 1048576 1 1048576 (BSN.sqrt_natCast_div_one 5) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz302 qz14)) Bool.false 2344687 1048576 1 1048576 2344687 1048576 1 1048576 (BSN.sqrt_enclosure 5 1 1172343 1172344 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep103 := nat_lit 3696382175741467532940033205863946875

noncomputable def ep104 := nat_lit 765440954430599474856563326857688500

noncomputable def ep105 := nat_lit 108794268166472120024432640000

noncomputable def ep106 := BSN.log_dyadic_bound 2 3 18 17 ep103 524288 193517 ep104 ep105 843808 5 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_rec (BSN.artanhP 2) (BSN.artanhQ 3) 0 17 8 307084260767580 1483365253795425 132843110400 1663129201793174588340 2491889415829100854875 818968088287641600 ep104 ep103 ep105 rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.artanhP 2) (BSN.artanhQ 3) 0 8 307084260767580 1483365253795425 132843110400 rfl rfl rfl rfl) (@BSN.binarySplit_of_base9 (BSN.artanhP 2) (BSN.artanhQ 3) 8 17 1663129201793174588340 2491889415829100854875 818968088287641600 rfl rfl rfl rfl)) rfl rfl

noncomputable def ep107 := nat_lit 6676942158607202929940826609372610816

noncomputable def ep108 := BSN.sin_dyadic_bound_f 1607475652 2147483648 2 1 1048576 387412 ep107 ep57 ep107 ep107 ep58 ep107 713628 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1607475652) qz15 0 1 ep107 ep57 ep107 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1607475652) qz16 0 1 ep107 ep58 ep107 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz303 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 219849111) qz17)

noncomputable abbrev qz304 := (BSN.isNear_log_sfrac 5 1 843808 524288 1 193517 Bool.false (BSN.logfrac_isNear 5 1 2 5 1 843808 524288 193517 rfl rfl rfl (ep106 rfl rfl)))

noncomputable def ep109 := @Enclosure.Real.IsNear.cos_image qz27 qz303 Bool.false 219849111 1048576 707 1048576 Bool.true 713628 1048576 1 193517 (@Enclosure.Real.IsNear.recentre' qz27 Bool.false 107348199 512000 16284 24189625 219849111 1048576 707 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz12 qz549 130272 1000 0 1 843808 524288 1 193517 107348199 512000 16284 24189625 qz18 qz304 rfl) rfl) (Enclosure.sfrac_false_div 219849111 1048576) (BSN.cos_reduce1 qz303 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 113116042972650801201152) qz19) 226375608064910080 72057594037927936 Bool.false 713628 1048576 33 1000000000000000 387034 193517 (BSN.sin_reduce_arg_pos_rat_q1 219849111 1048576 226375608064910080 72057594037927936 33 113116042972650801201152 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 713628 1048576 113116042972650801201152 151115727451828646838272 1607475652 2147483648 387412 387034 (ep108 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep110 := nat_lit 238609378116720594846161029758031342347891140276807079162802423125943674535936

noncomputable def ep111 := nat_lit 44581556589386214647134746665105090563423892844608123350126844708200185856

noncomputable def ep112 := nat_lit 715738971236983012109188819780763816862546573044732021241707015688414623236096

noncomputable def ep113 := BSN.cos_dyadic_bound_f 1607475652 2147483648 3 2 1048576 387412 ep110 ep62 ep111 ep112 ep65 ep111 768274 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1607475652) qz20 0 2 ep110 ep62 ep111 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1607475652) qz21 0 2 ep112 ep65 ep111 rfl rfl rfl rfl) rfl rfl

noncomputable def ep114 := @Enclosure.Real.IsNear.sin_image qz27 qz303 Bool.false 219849111 1048576 707 1048576 Bool.false 768274 1048576 1 193517 (@Enclosure.Real.IsNear.recentre' qz27 Bool.false 107348199 512000 16284 24189625 219849111 1048576 707 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz12 qz549 130272 1000 0 1 843808 524288 1 193517 107348199 512000 16284 24189625 qz18 qz304 rfl) rfl) (Enclosure.sfrac_false_div 219849111 1048576) (BSN.sin_reduce1 qz303 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 113116042972650801201152) qz19) 226375608064910080 72057594037927936 Bool.false 768274 1048576 33 1000000000000000 387034 193517 (BSN.sin_reduce_arg_pos_rat_q1 219849111 1048576 226375608064910080 72057594037927936 33 113116042972650801201152 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 768274 1048576 113116042972650801201152 151115727451828646838272 1607475652 2147483648 387412 387034 (ep113 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz305 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 5))) Bool.false 468937 1048576 1 1048576 468937 1048576 1 1048576 (ep102 rfl rfl) rfl)

noncomputable def ep115 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz300 (Real.cos qz27)) (@HMul.hMul Real Real Real qz0 qz300 (@Neg.neg Real Real.instNeg (Real.sin qz27))) Bool.true 83661643359 274877906944 32394140534393 106387095836164096 Bool.true 180136052369 549755813888 4049928499923 13298386979520512 (@Enclosure.Real.IsNear.mulLit_ft qz300 (Real.cos qz27) 468937 1048576 1 1048576 178407 262144 137865095 202917281792 83661643359 274877906944 32394140534393 106387095836164096 qz305 (@Enclosure.Real.IsNear.recentre' (Real.cos qz27) Bool.true 713628 1048576 137865095 202917281792 178407 262144 137865095 202917281792 (ep109 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz300 (@Neg.neg Real Real.instNeg (Real.sin qz27)) 468937 1048576 1 1048576 384137 524288 137865095 202917281792 180136052369 549755813888 4049928499923 13298386979520512 qz305 (@Enclosure.Real.IsNear.neg (Real.sin qz27) Bool.false 384137 524288 137865095 202917281792 (@Enclosure.Real.IsNear.recentre' (Real.sin qz27) Bool.false 768274 1048576 137865095 202917281792 384137 524288 137865095 202917281792 (ep114 rfl rfl) rfl)) rfl)

noncomputable def ep116 := @ep45 83661643359 274877906944 32394140534393 106387095836164096 Bool.true 180136052369 549755813888 4049928499923 13298386979520512 Bool.false 43111226950324051771392 156837729993 549755813888 161410517186187 106387095836164096 Bool.false 138253593448522899783680 251481821485 1099511627776 323195869641245 212774191672328192 (ep46 (BSN.head_sum_c_succ qz5 4 5 rfl rfl) (ep100 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep101 ep115) rfl rfl

noncomputable abbrev qz550 := (Real.log (Enclosure.sfrac Bool.false 6 1))

noncomputable abbrev qz28 := (@HMul.hMul Real Real Real qz268 qz279 qz550)

noncomputable abbrev qz306 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 6)))

noncomputable def ep117 := @Enclosure.Complex.IsNear.of_eq qz540 (Complex.mk (@HMul.hMul Real Real Real qz0 qz306 (Real.cos qz28)) (@HMul.hMul Real Real Real qz0 qz306 (@Neg.neg Real Real.instNeg (Real.sin qz28)))) Bool.false 66356097711 274877906944 14784319343553 53193547918082048 Bool.true 22624403229 68719476736 924702045923 3324596744880128 (BSN.cpow_neg_s_mk qz12 130272 1000 6 qz13 rfl)

noncomputable abbrev qz307 := (Real.sqrt (@Nat.cast Real Real.instNatCast 6))

noncomputable abbrev qz308 := (@Nat.cast Real Real.instNatCast 6)

noncomputable abbrev qz551 := (@HDiv.hDiv Real Real Real qz1 qz308 qz14)

noncomputable def ep118 := @Enclosure.Real.IsNear.inv_image qz307 2568477 1048576 1 1048576 214039 214040 524288 (@Enclosure.Real.IsNear.of_eq qz307 (Real.sqrt qz551) Bool.false 2568477 1048576 1 1048576 (BSN.sqrt_natCast_div_one 6) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz551) Bool.false 2568477 1048576 1 1048576 2568477 1048576 1 1048576 (BSN.sqrt_enclosure 6 1 1284238 1284239 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep119 := BSN.log_dyadic_bound 2 10 4 3 105000000 524288 193517 1434560 960 212580 12 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 2) (BSN.artanhQ 10) 0 3 1434560 105000000 960 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep120 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz550 130272 1000 0 1 4034681531866359 2251799813685248 500000000193517 96758500000000000000 16425188516227947489 70368744177664000 2035500000787807707 3023703125000000000000 qz18 (BSN.isNear_log_sfrac 6 1 4034681531866359 2251799813685248 500000000193517 96758500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz551) Bool.false 33845361775666394038272 18889465931478580854784 1000000000387034 193517000000000000000 4034681531866359 2251799813685248 500000000193517 96758500000000000000 (BSN.log_rat_reduce_isNear 6 1 2 12 8 212580 524288 24973259072661432 36028797018963968 193517 1000000000000000 rfl rfl rfl rfl (ep119 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep121 := nat_lit 588795640435092169811770877751466960759983167466102287426085288069542092800000

noncomputable def ep122 := nat_lit 271313466686994288252949187574657456274539798541335140554274705433600000000

noncomputable def ep123 := nat_lit 1765844294371902520858806734879251567367400422801224191997147314797759078400000

noncomputable def ep124 := BSN.cos_dyadic_bound_f 2014577220 2147483648 3 2 1048576 387412 ep121 ep62 ep122 ep123 ep65 ep122 620036 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2014577220) qz20 0 2 ep121 ep62 ep122 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2014577220) qz21 0 2 ep123 ep65 ep122 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz309 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 244754381) qz17)

noncomputable def ep125 := @Enclosure.Real.IsNear.cos_image qz28 qz309 Bool.false 244754381 1048576 707 1048576 Bool.false 620036 1048576 1 193517 (@Enclosure.Real.IsNear.recentre' qz28 Bool.false 16425188516227947489 70368744177664000 2035500000787807707 3023703125000000000000 244754381 1048576 707 1048576 (ep120 rfl) rfl) (Enclosure.sfrac_false_div 244754381 1048576) (BSN.cos_reduce0 qz309 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 141763269068554493755392) qz19) 226375608064910080 72057594037927936 Bool.false 620036 1048576 37 1000000000000000 387034 193517 (BSN.sin_reduce_arg_pos_rat_q0 244754381 1048576 226375608064910080 72057594037927936 37 141763269068554493755392 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 620036 1048576 141763269068554493755392 151115727451828646838272 2014577220 2147483648 387412 387034 (ep124 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep126 := nat_lit 1059615102009816310230585220602580803402950069600151049254510098760828887040000

noncomputable def ep127 := nat_lit 2774743140603454250327694612417352658745186641659900110200914766279087923200000

noncomputable def ep128 := BSN.sin_dyadic_bound_f 2014577220 2147483648 3 2 1048576 387412 ep126 ep94 ep122 ep127 ep96 ep122 845616 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2014577220) qz15 0 2 ep126 ep94 ep122 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2014577220) qz16 0 2 ep127 ep96 ep122 rfl rfl rfl rfl) rfl rfl

noncomputable def ep129 := @Enclosure.Real.IsNear.sin_image qz28 qz309 Bool.false 244754381 1048576 707 1048576 Bool.false 845616 1048576 1 193517 (@Enclosure.Real.IsNear.recentre' qz28 Bool.false 16425188516227947489 70368744177664000 2035500000787807707 3023703125000000000000 244754381 1048576 707 1048576 (ep120 rfl) rfl) (Enclosure.sfrac_false_div 244754381 1048576) (BSN.sin_reduce0 qz309 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 141763269068554493755392) qz19) 226375608064910080 72057594037927936 Bool.false 845616 1048576 37 1000000000000000 387034 193517 (BSN.sin_reduce_arg_pos_rat_q0 244754381 1048576 226375608064910080 72057594037927936 37 141763269068554493755392 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 845616 1048576 141763269068554493755392 151115727451828646838272 2014577220 2147483648 387412 387034 (ep128 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz310 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 6))) Bool.false 428079 1048576 1 1048576 428079 1048576 1 1048576 (ep118 rfl rfl) rfl)

noncomputable def ep130 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz306 (Real.cos qz28)) (@HMul.hMul Real Real Real qz0 qz306 (@Neg.neg Real Real.instNeg (Real.sin qz28))) Bool.false 66356097711 274877906944 14784319343553 53193547918082048 Bool.true 22624403229 68719476736 924702045923 3324596744880128 (@Enclosure.Real.IsNear.mulLit_ff qz306 (Real.cos qz28) 428079 1048576 1 1048576 155009 262144 137865095 202917281792 66356097711 274877906944 14784319343553 53193547918082048 qz310 (@Enclosure.Real.IsNear.recentre' (Real.cos qz28) Bool.false 620036 1048576 137865095 202917281792 155009 262144 137865095 202917281792 (ep125 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz306 (@Neg.neg Real Real.instNeg (Real.sin qz28)) 428079 1048576 1 1048576 52851 65536 137865095 202917281792 22624403229 68719476736 924702045923 3324596744880128 qz310 (@Enclosure.Real.IsNear.neg (Real.sin qz28) Bool.false 52851 65536 137865095 202917281792 (@Enclosure.Real.IsNear.recentre' (Real.sin qz28) Bool.false 845616 1048576 137865095 202917281792 52851 65536 137865095 202917281792 (ep129 rfl rfl) rfl)) rfl)

noncomputable def ep131 := @ep43 66356097711 274877906944 14784319343553 53193547918082048 Bool.true 22624403229 68719476736 924702045923 3324596744880128 Bool.false 79590877453866510581760 289549925415 549755813888 190979155873293 106387095836164096 Bool.true 7594095240713018015744 110508630179 1099511627776 382376800580317 212774191672328192 (ep44 (BSN.head_sum_c_succ qz5 5 6 rfl rfl) (ep116 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep117 ep130) rfl rfl

noncomputable abbrev qz552 := (Real.log (Enclosure.sfrac Bool.false 7 1))

noncomputable abbrev qz29 := (@HMul.hMul Real Real Real qz268 qz279 qz552)

noncomputable abbrev qz311 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 7)))

noncomputable def ep132 := @Enclosure.Complex.IsNear.of_eq qz539 (Complex.mk (@HMul.hMul Real Real Real qz0 qz311 (Real.cos qz29)) (@HMul.hMul Real Real Real qz0 qz311 (@Neg.neg Real Real.instNeg (Real.sin qz29)))) Bool.true 29296740325 137438953472 27376980701113 106387095836164096 Bool.true 171590097725 549755813888 13701772293093 53193547918082048 (BSN.cpow_neg_s_mk qz12 130272 1000 7 qz13 rfl)

noncomputable abbrev qz312 := (Real.sqrt (@Nat.cast Real Real.instNatCast 7))

noncomputable abbrev qz313 := (@Nat.cast Real Real.instNatCast 7)

noncomputable abbrev qz553 := (@HDiv.hDiv Real Real Real qz1 qz313 qz14)

noncomputable def ep133 := @Enclosure.Real.IsNear.inv_image qz312 2774271 1048576 1 1048576 198162 198163 524288 (@Enclosure.Real.IsNear.of_eq qz312 (Real.sqrt qz553) Bool.false 2774271 1048576 1 1048576 (BSN.sqrt_natCast_div_one 7) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz553) Bool.false 2774271 1048576 1 1048576 2774271 1048576 1 1048576 (BSN.sqrt_enclosure 7 1 1387135 1387136 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep134 := BSN.log_dyadic_bound 3 11 5 4 202569142545 524288 193517 5259111624 688905 293399 14 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 3) (BSN.artanhQ 11) 0 4 5259111624 202569142545 688905 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep135 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz552 130272 1000 0 1 4381796493761783 2251799813685248 500000000193517 96758500000000000000 17838293526104218593 70368744177664000 2035500000787807707 3023703125000000000000 qz18 (BSN.isNear_log_sfrac 7 1 4381796493761783 2251799813685248 500000000193517 96758500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz553) Bool.false 36757173121942042968064 18889465931478580854784 1000000000387034 193517000000000000000 4381796493761783 2251799813685248 500000000193517 96758500000000000000 (BSN.log_rat_reduce_isNear 7 1 2 14 8 293399 524288 24973259072661432 36028797018963968 193517 1000000000000000 rfl rfl rfl rfl (ep134 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep136 := nat_lit 2741411526009613906324810876143538176

noncomputable def ep137 := BSN.sin_dyadic_bound_f 1286748168 2147483648 2 1 1048576 387412 ep136 ep57 ep136 ep136 ep58 ep136 591368 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1286748168) qz15 0 1 ep136 ep57 ep136 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1286748168) qz16 0 1 ep136 ep58 ep136 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz314 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 265811287) qz17)

noncomputable def ep138 := @Enclosure.Real.IsNear.cos_image qz29 qz314 Bool.false 265811287 1048576 707 1048576 Bool.true 591368 1048576 1 193517 (@Enclosure.Real.IsNear.recentre' qz29 Bool.false 17838293526104218593 70368744177664000 2035500000787807707 3023703125000000000000 265811287 1048576 707 1048576 (ep135 rfl) rfl) (Enclosure.sfrac_false_div 265811287 1048576) (BSN.cos_reduce1 qz314 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 90546852724647483408384) qz19) 226375608064910080 72057594037927936 Bool.false 591368 1048576 40 1000000000000000 387034 193517 (BSN.sin_reduce_arg_pos_rat_q1 265811287 1048576 226375608064910080 72057594037927936 40 90546852724647483408384 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 591368 1048576 90546852724647483408384 151115727451828646838272 1286748168 2147483648 387412 387034 (ep137 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep139 := BSN.cos_dyadic_bound_f 1286748168 2147483648 2 1 1048576 387412 ep136 ep76 ep136 ep136 ep77 ep136 865906 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1286748168) qz20 0 1 ep136 ep76 ep136 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1286748168) qz21 0 1 ep136 ep77 ep136 rfl rfl rfl rfl) rfl rfl

noncomputable def ep140 := @Enclosure.Real.IsNear.sin_image qz29 qz314 Bool.false 265811287 1048576 707 1048576 Bool.false 865906 1048576 1 193517 (@Enclosure.Real.IsNear.recentre' qz29 Bool.false 17838293526104218593 70368744177664000 2035500000787807707 3023703125000000000000 265811287 1048576 707 1048576 (ep135 rfl) rfl) (Enclosure.sfrac_false_div 265811287 1048576) (BSN.sin_reduce1 qz314 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 90546852724647483408384) qz19) 226375608064910080 72057594037927936 Bool.false 865906 1048576 40 1000000000000000 387034 193517 (BSN.sin_reduce_arg_pos_rat_q1 265811287 1048576 226375608064910080 72057594037927936 40 90546852724647483408384 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 865906 1048576 90546852724647483408384 151115727451828646838272 1286748168 2147483648 387412 387034 (ep139 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz315 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 7))) Bool.false 396325 1048576 1 1048576 396325 1048576 1 1048576 (ep133 rfl rfl) rfl)

noncomputable def ep141 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz311 (Real.cos qz29)) (@HMul.hMul Real Real Real qz0 qz311 (@Neg.neg Real Real.instNeg (Real.sin qz29))) Bool.true 29296740325 137438953472 27376980701113 106387095836164096 Bool.true 171590097725 549755813888 13701772293093 53193547918082048 (@Enclosure.Real.IsNear.mulLit_ft qz311 (Real.cos qz29) 396325 1048576 1 1048576 73921 131072 137865095 202917281792 29296740325 137438953472 27376980701113 106387095836164096 qz315 (@Enclosure.Real.IsNear.recentre' (Real.cos qz29) Bool.true 591368 1048576 137865095 202917281792 73921 131072 137865095 202917281792 (ep138 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz311 (@Neg.neg Real Real.instNeg (Real.sin qz29)) 396325 1048576 1 1048576 432953 524288 137865095 202917281792 171590097725 549755813888 13701772293093 53193547918082048 qz315 (@Enclosure.Real.IsNear.neg (Real.sin qz29) Bool.false 432953 524288 137865095 202917281792 (@Enclosure.Real.IsNear.recentre' (Real.sin qz29) Bool.false 865906 1048576 137865095 202917281792 432953 524288 137865095 202917281792 (ep140 rfl rfl) rfl)) rfl)

noncomputable def ep142 := @ep41 29296740325 137438953472 27376980701113 106387095836164096 Bool.true 171590097725 549755813888 13701772293093 53193547918082048 Bool.false 23689385405297490657280 172362964115 549755813888 109178068287203 53193547918082048 Bool.true 249418069585561808535552 453688825629 1099511627776 437183889752689 212774191672328192 (ep42 (BSN.head_sum_c_succ qz5 6 7 rfl rfl) (ep131 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep132 ep141) rfl rfl

noncomputable abbrev qz554 := (Real.log (Enclosure.sfrac Bool.false 8 1))

noncomputable abbrev qz30 := (@HMul.hMul Real Real Real qz268 qz279 qz554)

noncomputable abbrev qz316 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 8)))

noncomputable def ep143 := @Enclosure.Complex.IsNear.of_eq qz538 (Complex.mk (@HMul.hMul Real Real Real qz0 qz316 (Real.cos qz30)) (@HMul.hMul Real Real Real qz0 qz316 (@Neg.neg Real Real.instNeg (Real.sin qz30)))) Bool.false 293266188439 1099511627776 51263533916629 212774191672328192 Bool.true 255166574649 1099511627776 51243646174539 212774191672328192 (BSN.cpow_neg_s_mk qz12 130272 1000 8 qz13 rfl)

noncomputable abbrev qz317 := (Real.sqrt (@Nat.cast Real Real.instNatCast 8))

noncomputable abbrev qz318 := (@Nat.cast Real Real.instNatCast 8)

noncomputable abbrev qz555 := (@HDiv.hDiv Real Real Real qz1 qz318 qz14)

noncomputable def ep144 := @Enclosure.Real.IsNear.inv_image qz317 2965821 1048576 1 1048576 185363 185364 524288 (@Enclosure.Real.IsNear.of_eq qz317 (Real.sqrt qz555) Bool.false 2965821 1048576 1 1048576 (BSN.sqrt_natCast_div_one 8) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz555) Bool.false 2965821 1048576 1 1048576 2965821 1048576 1 1048576 (BSN.sqrt_enclosure 8 1 1482910 1482911 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep145 := BSN.log_dyadic_bound 0 16 1 0 1 524288 193517 0 1 0 16 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 0) (BSN.artanhQ 16) 0 0 rfl) rfl rfl rfl

noncomputable def ep146 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz554 130272 1000 0 1 9364972152248037 4503599627370496 1000000000580551 193517000000000000000 38124801631801758627 140737488355328000 4071000002363423121 6047406250000000000000 qz18 (BSN.isNear_log_sfrac 8 1 9364972152248037 4503599627370496 1000000000580551 193517000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz555) Bool.false 39279540158062550581248 18889465931478580854784 1000000000580551 193517000000000000000 9364972152248037 4503599627370496 1000000000580551 193517000000000000000 (BSN.log_rat_reduce_isNear 8 1 3 16 16 0 524288 24973259072661432 36028797018963968 193517 1000000000000000 rfl rfl rfl rfl (ep145 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep147 := nat_lit 199786136367826746535059932482945338678611985586102077441784891817209121846401

noncomputable def ep148 := nat_lit 31256281391515484543478755755830163219935496071303952737528673716234990721

noncomputable def ep149 := nat_lit 599295896540697208636092839937324355709396085766163624419879618104194895557761

noncomputable def ep150 := BSN.cos_dyadic_bound_f 1537684241 2147483648 3 2 1048576 387412 ep147 ep62 ep148 ep149 ep65 ep148 791057 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1537684241) qz20 0 2 ep147 ep62 ep148 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1537684241) qz21 0 2 ep149 ep65 ep148 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz319 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 284051907) qz17)

noncomputable def ep151 := @Enclosure.Real.IsNear.cos_image qz30 qz319 Bool.false 284051907 1048576 707 1048576 Bool.false 791057 1048576 1 193517 (@Enclosure.Real.IsNear.recentre' qz30 Bool.false 38124801631801758627 140737488355328000 4071000002363423121 6047406250000000000000 284051907 1048576 707 1048576 (ep146 rfl) rfl) (Enclosure.sfrac_false_div 284051907 1048576) (BSN.cos_reduce0 qz319 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 108204909019882946822144) qz19) 226375608064910080 72057594037927936 Bool.false 791057 1048576 43 1000000000000000 387034 193517 (BSN.sin_reduce_arg_pos_rat_q0 284051907 1048576 226375608064910080 72057594037927936 43 108204909019882946822144 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 791057 1048576 108204909019882946822144 151115727451828646838272 1537684241 2147483648 387412 387034 (ep150 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep152 := nat_lit 5590731740256858768849887557714858561

noncomputable def ep153 := BSN.sin_dyadic_bound_f 1537684241 2147483648 2 1 1048576 387412 ep152 ep57 ep152 ep152 ep58 ep152 688287 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1537684241) qz15 0 1 ep152 ep57 ep152 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1537684241) qz16 0 1 ep152 ep58 ep152 rfl rfl rfl rfl) rfl rfl

noncomputable def ep154 := @Enclosure.Real.IsNear.sin_image qz30 qz319 Bool.false 284051907 1048576 707 1048576 Bool.false 688287 1048576 1 193517 (@Enclosure.Real.IsNear.recentre' qz30 Bool.false 38124801631801758627 140737488355328000 4071000002363423121 6047406250000000000000 284051907 1048576 707 1048576 (ep146 rfl) rfl) (Enclosure.sfrac_false_div 284051907 1048576) (BSN.sin_reduce0 qz319 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 108204909019882946822144) qz19) 226375608064910080 72057594037927936 Bool.false 688287 1048576 43 1000000000000000 387034 193517 (BSN.sin_reduce_arg_pos_rat_q0 284051907 1048576 226375608064910080 72057594037927936 43 108204909019882946822144 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 688287 1048576 108204909019882946822144 151115727451828646838272 1537684241 2147483648 387412 387034 (ep153 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz320 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 8))) Bool.false 370727 1048576 1 1048576 370727 1048576 1 1048576 (ep144 rfl rfl) rfl)

noncomputable def ep155 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz316 (Real.cos qz30)) (@HMul.hMul Real Real Real qz0 qz316 (@Neg.neg Real Real.instNeg (Real.sin qz30))) Bool.false 293266188439 1099511627776 51263533916629 212774191672328192 Bool.true 255166574649 1099511627776 51243646174539 212774191672328192 (@Enclosure.Real.IsNear.mulLit_ff qz316 (Real.cos qz30) 370727 1048576 1 1048576 791057 1048576 137865095 202917281792 293266188439 1099511627776 51263533916629 212774191672328192 qz320 (@Enclosure.Real.IsNear.recentre' (Real.cos qz30) Bool.false 791057 1048576 137865095 202917281792 791057 1048576 137865095 202917281792 (ep151 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz316 (@Neg.neg Real Real.instNeg (Real.sin qz30)) 370727 1048576 1 1048576 688287 1048576 137865095 202917281792 255166574649 1099511627776 51243646174539 212774191672328192 qz320 (@Enclosure.Real.IsNear.neg (Real.sin qz30) Bool.false 688287 1048576 137865095 202917281792 (@Enclosure.Real.IsNear.recentre' (Real.sin qz30) Bool.false 688287 1048576 137865095 202917281792 688287 1048576 137865095 202917281792 (ep154 rfl rfl) rfl)) rfl)

noncomputable def ep156 := @ep39 293266188439 1099511627776 51263533916629 212774191672328192 Bool.true 255166574649 1099511627776 51243646174539 212774191672328192 Bool.false 350739875353493946499072 637992116669 1099511627776 487975807065441 212774191672328192 Bool.true 779394755017471822921728 354427700139 549755813888 122106883981807 53193547918082048 (ep40 (BSN.head_sum_c_succ qz5 7 8 rfl rfl) (ep142 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep143 ep155) rfl rfl

theorem EMRow44.d6 : Enclosure.Complex.IsNear qz3 Bool.false 637992116669 1099511627776 487975807065441 212774191672328192 Bool.true 354427700139 549755813888 122106883981807 53193547918082048 := ep38 (BSN.head_sum_c_succ qz5 8 9 rfl rfl) (ep156 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable abbrev qz31 := (BSN.headSumC qz272 17)

noncomputable abbrev qz556 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 16) qz7)

noncomputable def ep157 := @Enclosure.Complex.IsNear.of_eq qz31 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 16) qz556) Bool.true 144940736397 1099511627776 820230870611539 212774191672328192 Bool.true 110863325915 1099511627776 820843924339825 212774191672328192

noncomputable def ep158 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 16) qz556 Bool.false 32190364797 274877906944 12248254890871 3324596744880128 Bool.true 42739878541 549755813888 392342339215759 106387095836164096 Bool.true

noncomputable abbrev qz557 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 15) qz7)

noncomputable def ep159 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 16) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 15) qz557) Bool.false 32190364797 274877906944 12248254890871 3324596744880128 Bool.true 42739878541 549755813888 392342339215759 106387095836164096

noncomputable def ep160 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 15) qz557 Bool.true 1319041137 34359738368 373220118513945 106387095836164096 Bool.false 141156180313 1099511627776 747196814767913 212774191672328192 Bool.false

noncomputable abbrev qz558 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 14) qz7)

noncomputable def ep161 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 15) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 14) qz558) Bool.true 1319041137 34359738368 373220118513945 106387095836164096 Bool.false 141156180313 1099511627776 747196814767913 212774191672328192

noncomputable def ep162 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 14) qz558 Bool.false 18854792587 1099511627776 707762204570961 212774191672328192 Bool.true 146285141385 1099511627776 708362461407071 212774191672328192 Bool.true

noncomputable abbrev qz559 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 13) qz7)

noncomputable def ep163 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 14) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 13) qz559) Bool.false 18854792587 1099511627776 707762204570961 212774191672328192 Bool.true 146285141385 1099511627776 708362461407071 212774191672328192

noncomputable def ep164 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 13) qz559 Bool.true 27673587131 274877906944 166895380670103 53193547918082048 Bool.false 32444720547 274877906944 20877633962907 6649193489760256 Bool.false

noncomputable abbrev qz560 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 12) qz7)

noncomputable def ep165 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 13) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 12) qz560) Bool.true 27673587131 274877906944 166895380670103 53193547918082048 Bool.false 32444720547 274877906944 20877633962907 6649193489760256

noncomputable def ep166 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 12) qz560 Bool.false 204044846227 1099511627776 625648818467291 212774191672328192 Bool.false 88761319809 1099511627776 626326575378595 212774191672328192 Bool.true

noncomputable abbrev qz561 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 11) qz7)

noncomputable def ep167 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 12) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 11) qz561) Bool.false 204044846227 1099511627776 625648818467291 212774191672328192 Bool.false 88761319809 1099511627776 626326575378595 212774191672328192

noncomputable def ep168 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 11) qz561 Bool.false 273143487833 1099511627776 582080553021481 212774191672328192 Bool.true 58867977689 274877906944 291301072114753 106387095836164096 Bool.true

noncomputable abbrev qz562 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 10) qz7)

noncomputable def ep169 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 11) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 10) qz562) Bool.false 273143487833 1099511627776 582080553021481 212774191672328192 Bool.true 58867977689 274877906944 291301072114753 106387095836164096

noncomputable def ep170 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 10) qz562 Bool.false 293942076269 1099511627776 536353728010123 212774191672328192 Bool.true 291272726939 549755813888 268342451760795 106387095836164096 Bool.true

noncomputable abbrev qz563 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 9) qz7)

noncomputable def ep171 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 10) (@HAdd.hAdd Complex Complex Complex qz4 qz3 qz563) Bool.false 293942076269 1099511627776 536353728010123 212774191672328192 Bool.true 291272726939 549755813888 268342451760795 106387095836164096

noncomputable def ep172 := @Enclosure.Complex.IsNear.addLitP qz3 qz563 Bool.false 637992116669 1099511627776 487975807065441 212774191672328192 Bool.true 354427700139 549755813888 122106883981807 53193547918082048 Bool.true

noncomputable abbrev qz564 := (Real.log (Enclosure.sfrac Bool.false 9 1))

noncomputable abbrev qz32 := (@HMul.hMul Real Real Real qz268 qz279 qz564)

noncomputable abbrev qz321 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 9)))

noncomputable def ep173 := @Enclosure.Complex.IsNear.of_eq qz563 (Complex.mk (@HMul.hMul Real Real Real qz0 qz321 (Real.cos qz32)) (@HMul.hMul Real Real Real qz0 qz321 (@Neg.neg Real Real.instNeg (Real.sin qz32)))) Bool.true 21503127525 68719476736 24188960472341 106387095836164096 Bool.false 3947185825 34359738368 24128683797181 106387095836164096 (BSN.cpow_neg_s_mk qz12 130272 1000 9 qz13 rfl)

noncomputable abbrev qz322 := (Real.sqrt (@Nat.cast Real Real.instNatCast 9))

noncomputable abbrev qz323 := (@Nat.cast Real Real.instNatCast 9)

noncomputable abbrev qz565 := (@HDiv.hDiv Real Real Real qz1 qz323 qz14)

noncomputable def ep174 := @Enclosure.Real.IsNear.inv_image qz322 3145729 1048576 1 1048576 174762 174763 524288 (@Enclosure.Real.IsNear.of_eq qz322 (Real.sqrt qz565) Bool.false 3145729 1048576 1 1048576 (BSN.sqrt_natCast_div_one 9) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz565) Bool.false 3145729 1048576 1 1048576 3145729 1048576 1 1048576 (BSN.sqrt_enclosure 9 1 1572864 1572865 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep175 := BSN.log_dyadic_bound 1 17 3 2 1252815 524288 193517 1448 3 61752 18 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 1) (BSN.artanhQ 17) 0 2 1448 1252815 3 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep176 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz564 130272 1000 0 1 9895417793173221 4503599627370496 1000000000580551 193517000000000000000 40284245836008182691 140737488355328000 4071000002363423121 6047406250000000000000 qz18 (BSN.isNear_log_sfrac 9 1 9895417793173221 4503599627370496 1000000000580551 193517000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz565) Bool.false 41504390431577613533184 18889465931478580854784 1000000000580551 193517000000000000000 9895417793173221 4503599627370496 1000000000580551 193517000000000000000 (BSN.log_rat_reduce_isNear 9 1 3 18 16 61752 524288 24973259072661432 36028797018963968 193517 1000000000000000 rfl rfl rfl rfl (ep175 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep177 := nat_lit 325951236035398044113056662957670656

noncomputable def ep178 := BSN.cos_dyadic_bound_f 755593404 2147483648 2 1 1048576 387412 ep177 ep76 ep177 ep177 ep77 ep177 984336 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 755593404) qz20 0 1 ep177 ep76 ep177 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 755593404) qz21 0 1 ep177 ep77 ep177 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz566 := (@Nat.cast Real Real.instNatCast 262144)

noncomputable abbrev qz324 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 75035255) qz566)

noncomputable abbrev qz325 := (@Nat.cast Real Real.instNatCast 37778931862957161709568)

noncomputable def ep179 := @Enclosure.Real.IsNear.cos_image qz32 qz324 Bool.false 75035255 262144 707 1048576 Bool.true 984336 1048576 1 193517 (@Enclosure.Real.IsNear.recentre' qz32 Bool.false 40284245836008182691 140737488355328000 4071000002363423121 6047406250000000000000 75035255 262144 707 1048576 (ep176 rfl) rfl) (Enclosure.sfrac_false_div 75035255 262144) (BSN.cos_reduce2 qz324 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 13292539741467280670720) qz325) 226375608064910080 72057594037927936 Bool.false 984336 1048576 45 1000000000000000 387034 193517 (BSN.sin_reduce_arg_pos_rat_q2 75035255 262144 226375608064910080 72057594037927936 45 13292539741467280670720 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 984336 1048576 13292539741467280670720 37778931862957161709568 755593404 2147483648 387412 387034 (ep178 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep180 := BSN.sin_dyadic_bound_f 755593404 2147483648 2 1 1048576 387412 ep177 ep57 ep177 ep177 ep58 ep177 361376 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 755593404) qz15 0 1 ep177 ep57 ep177 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 755593404) qz16 0 1 ep177 ep58 ep177 rfl rfl rfl rfl) rfl rfl

noncomputable def ep181 := @Enclosure.Real.IsNear.sin_image qz32 qz324 Bool.false 75035255 262144 707 1048576 Bool.true 361376 1048576 1 193517 (@Enclosure.Real.IsNear.recentre' qz32 Bool.false 40284245836008182691 140737488355328000 4071000002363423121 6047406250000000000000 75035255 262144 707 1048576 (ep176 rfl) rfl) (Enclosure.sfrac_false_div 75035255 262144) (BSN.sin_reduce2 qz324 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 13292539741467280670720) qz325) 226375608064910080 72057594037927936 Bool.false 361376 1048576 45 1000000000000000 387034 193517 (BSN.sin_reduce_arg_pos_rat_q2 75035255 262144 226375608064910080 72057594037927936 45 13292539741467280670720 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 361376 1048576 13292539741467280670720 37778931862957161709568 755593404 2147483648 387412 387034 (ep180 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz326 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 9))) Bool.false 349525 1048576 1 1048576 349525 1048576 1 1048576 (ep174 rfl rfl) rfl)

noncomputable def ep182 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz321 (Real.cos qz32)) (@HMul.hMul Real Real Real qz0 qz321 (@Neg.neg Real Real.instNeg (Real.sin qz32))) Bool.true 21503127525 68719476736 24188960472341 106387095836164096 Bool.false 3947185825 34359738368 24128683797181 106387095836164096 (@Enclosure.Real.IsNear.mulLit_ft qz321 (Real.cos qz32) 349525 1048576 1 1048576 61521 65536 137865095 202917281792 21503127525 68719476736 24188960472341 106387095836164096 qz326 (@Enclosure.Real.IsNear.recentre' (Real.cos qz32) Bool.true 984336 1048576 137865095 202917281792 61521 65536 137865095 202917281792 (ep179 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz321 (@Neg.neg Real Real.instNeg (Real.sin qz32)) 349525 1048576 1 1048576 11293 32768 137865095 202917281792 3947185825 34359738368 24128683797181 106387095836164096 qz326 (@Enclosure.Real.IsNear.neg (Real.sin qz32) Bool.true 11293 32768 137865095 202917281792 (@Enclosure.Real.IsNear.recentre' (Real.sin qz32) Bool.true 361376 1048576 137865095 202917281792 11293 32768 137865095 202917281792 (ep181 rfl rfl) rfl)) rfl)

noncomputable def ep183 := @ep172 21503127525 68719476736 24188960472341 106387095836164096 Bool.false 3947185825 34359738368 24128683797181 106387095836164096 Bool.false 20199545671899083177984 293942076269 1099511627776 536353728010123 212774191672328192 Bool.true 10008054691357945495552 291272726939 549755813888 268342451760795 106387095836164096 EMRow44.d6 (ep173 ep182) rfl rfl

noncomputable abbrev qz33 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 10)))

noncomputable abbrev qz567 := (Real.log (Enclosure.sfrac Bool.false 10 1))

noncomputable abbrev qz34 := (@HMul.hMul Real Real Real qz268 qz279 qz567)

noncomputable def ep184 := @Enclosure.Complex.IsNear.of_eq qz562 (Complex.mk (@HMul.hMul Real Real Real qz0 qz33 (Real.cos qz34)) (@HMul.hMul Real Real Real qz0 qz33 (@Neg.neg Real Real.instNeg (Real.sin qz34)))) Bool.true 5199647109 274877906944 22863412505679 106387095836164096 Bool.false 173536771561 549755813888 11479310176979 53193547918082048 (BSN.cpow_neg_s_mk qz12 130272 1000 10 qz13 rfl)

noncomputable abbrev qz327 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 10) qz14)

noncomputable def ep185 := @Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 10)) 3315889 1048576 1 1048576 165794 165795 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 10)) (Real.sqrt qz327) Bool.false 3315889 1048576 1 1048576 (BSN.sqrt_natCast_div_one 10) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz327) Bool.false 3315889 1048576 1 1048576 3315889 1048576 1 1048576 (BSN.sqrt_enclosure 10 1 1657944 1657945 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep186 := BSN.log_dyadic_bound 2 18 3 2 1574640 524288 193517 6528 48 116991 20 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 2) (BSN.artanhQ 18) 0 2 6528 1574640 48 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep187 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz567 130272 1000 0 1 10369917190100709 4503599627370496 1000000000580551 193517000000000000000 42215932880899986339 140737488355328000 4071000002363423121 6047406250000000000000 qz18 (BSN.isNear_log_sfrac 10 1 10369917190100709 4503599627370496 1000000000580551 193517000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz327) Bool.false 43494585150108164161536 18889465931478580854784 1000000000580551 193517000000000000000 10369917190100709 4503599627370496 1000000000580551 193517000000000000000 (BSN.log_rat_reduce_isNear 10 1 3 20 16 116991 524288 24973259072661432 36028797018963968 193517 1000000000000000 rfl rfl rfl rfl (ep186 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep188 := nat_lit 3972688697766373587816199880557886431742976168791583816430970706364640879190625

noncomputable def ep189 := nat_lit 12286300729935418217494114873446194864665730537826391734191076529529250390625

noncomputable def ep190 := nat_lit 11893493491839249927013611411926766905499597045299098665824529966034864136790625

noncomputable def ep191 := BSN.cos_dyadic_bound_f 3244723115 2147483648 3 2 1048576 387412 ep188 ep62 ep189 ep190 ep65 ep189 62724 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3244723115) qz20 0 2 ep188 ep62 ep189 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3244723115) qz21 0 2 ep190 ep65 ep189 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz328 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 157266605) qz24)

noncomputable def ep192 := @Enclosure.Real.IsNear.cos_image qz34 qz328 Bool.false 157266605 524288 707 1048576 Bool.true 62724 1048576 1 193517 (@Enclosure.Real.IsNear.recentre' qz34 Bool.false 42215932880899986339 140737488355328000 4071000002363423121 6047406250000000000000 157266605 524288 707 1048576 (ep187 rfl) rfl) (Enclosure.sfrac_false_div 157266605 524288) (BSN.cos_reduce2 qz328 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 114163545410576014376960) qz25) 226375608064910080 72057594037927936 Bool.false 62724 1048576 47 1000000000000000 387034 193517 (BSN.sin_reduce_arg_pos_rat_q2 157266605 524288 226375608064910080 72057594037927936 47 114163545410576014376960 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 62724 1048576 114163545410576014376960 75557863725914323419136 3244723115 2147483648 387412 387034 (ep191 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep193 := nat_lit 7141010615395524123495164493105438621245624519394589756188394410232730182230625

noncomputable def ep194 := nat_lit 18682754743901715360611392724528664454433843510876968536733295045752198357590625

noncomputable def ep195 := BSN.sin_dyadic_bound_f 3244723115 2147483648 3 2 1048576 387412 ep193 ep94 ep189 ep194 ep96 ep189 1046698 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3244723115) qz15 0 2 ep193 ep94 ep189 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3244723115) qz16 0 2 ep194 ep96 ep189 rfl rfl rfl rfl) rfl rfl

noncomputable def ep196 := @Enclosure.Real.IsNear.sin_image qz34 qz328 Bool.false 157266605 524288 707 1048576 Bool.true 1046698 1048576 1 193517 (@Enclosure.Real.IsNear.recentre' qz34 Bool.false 42215932880899986339 140737488355328000 4071000002363423121 6047406250000000000000 157266605 524288 707 1048576 (ep187 rfl) rfl) (Enclosure.sfrac_false_div 157266605 524288) (BSN.sin_reduce2 qz328 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 114163545410576014376960) qz25) 226375608064910080 72057594037927936 Bool.false 1046698 1048576 47 1000000000000000 387034 193517 (BSN.sin_reduce_arg_pos_rat_q2 157266605 524288 226375608064910080 72057594037927936 47 114163545410576014376960 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1046698 1048576 114163545410576014376960 75557863725914323419136 3244723115 2147483648 387412 387034 (ep195 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz329 := (@Enclosure.Real.IsNear.recentre' qz33 Bool.false 331589 1048576 1 1048576 331589 1048576 1 1048576 (ep185 rfl rfl) rfl)

noncomputable def ep197 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz33 (Real.cos qz34)) (@HMul.hMul Real Real Real qz0 qz33 (@Neg.neg Real Real.instNeg (Real.sin qz34))) Bool.true 5199647109 274877906944 22863412505679 106387095836164096 Bool.false 173536771561 549755813888 11479310176979 53193547918082048 (@Enclosure.Real.IsNear.mulLit_ft qz33 (Real.cos qz34) 331589 1048576 1 1048576 15681 262144 137865095 202917281792 5199647109 274877906944 22863412505679 106387095836164096 qz329 (@Enclosure.Real.IsNear.recentre' (Real.cos qz34) Bool.true 62724 1048576 137865095 202917281792 15681 262144 137865095 202917281792 (ep192 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz33 (@Neg.neg Real Real.instNeg (Real.sin qz34)) 331589 1048576 1 1048576 523349 524288 137865095 202917281792 173536771561 549755813888 11479310176979 53193547918082048 qz329 (@Enclosure.Real.IsNear.neg (Real.sin qz34) Bool.true 523349 524288 137865095 202917281792 (@Enclosure.Real.IsNear.recentre' (Real.sin qz34) Bool.true 1046698 1048576 137865095 202917281792 523349 524288 137865095 202917281792 (ep196 rfl rfl) rfl)) rfl)

noncomputable def ep198 := @ep170 5199647109 274877906944 22863412505679 106387095836164096 Bool.false 173536771561 549755813888 11479310176979 53193547918082048 Bool.false 75081110230918970212352 273143487833 1099511627776 582080553021481 212774191672328192 Bool.true 64726025972713640689664 58867977689 274877906944 291301072114753 106387095836164096 (ep171 (BSN.head_sum_c_succ qz5 9 10 rfl rfl) (ep183 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep184 ep197) rfl rfl

noncomputable abbrev qz35 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 11)))

noncomputable abbrev qz568 := (Real.log (Enclosure.sfrac Bool.false 11 1))

noncomputable abbrev qz36 := (@HMul.hMul Real Real Real qz268 qz279 qz568)

noncomputable def ep199 := @Enclosure.Complex.IsNear.of_eq qz561 (Complex.mk (@HMul.hMul Real Real Real qz0 qz35 (Real.cos qz36)) (@HMul.hMul Real Real Real qz0 qz35 (@Neg.neg Real Real.instNeg (Real.sin qz36)))) Bool.true 34549320803 549755813888 751176990445 3668520546074624 Bool.false 324233230565 1099511627776 1507739005141 7337041092149248 (BSN.cpow_neg_s_mk qz12 130272 1000 11 qz13 rfl)

noncomputable abbrev qz330 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 11) qz14)

noncomputable def ep200 := @Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 11)) 3477733 1048576 1 1048576 158078 158079 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 11)) (Real.sqrt qz330) Bool.false 3477733 1048576 1 1048576 (BSN.sqrt_natCast_div_one 11) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz330) Bool.false 3477733 1048576 1 1048576 3477733 1048576 1 1048576 (BSN.sqrt_enclosure 11 1 1738866 1738867 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep201 := BSN.log_dyadic_bound 3 19 4 3 4939817505 524288 193517 41676111 10935 166961 22 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 3) (BSN.artanhQ 19) 0 3 41676111 4939817505 10935 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep202 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz568 130272 1000 0 1 10799156221662949 4503599627370496 1000000000580551 193517000000000000000 43963364978389865379 140737488355328000 4071000002363423121 6047406250000000000000 qz18 (BSN.isNear_log_sfrac 11 1 10799156221662949 4503599627370496 1000000000580551 193517000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz330) Bool.false 45294944137145793642496 18889465931478580854784 1000000000580551 193517000000000000000 10799156221662949 4503599627370496 1000000000580551 193517000000000000000 (BSN.log_rat_reduce_isNear 11 1 3 22 16 166961 524288 24973259072661432 36028797018963968 193517 1000000000000000 rfl rfl rfl rfl (ep201 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep203 := nat_lit 2611204987368270322019119452812176632277997371946113182124349651102945437163776

noncomputable def ep204 := nat_lit 5319284733454303091656813461861444751125487096769708099508621683497370788096

noncomputable def ep205 := nat_lit 7822976392637902359874044731512807007331741141644800130174031709941841569915136

noncomputable def ep206 := BSN.cos_dyadic_bound_f 2922346138 2147483648 3 2 1048576 387412 ep203 ep62 ep204 ep205 ep65 ep204 218558 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2922346138) qz20 0 2 ep203 ep62 ep204 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2922346138) qz21 0 2 ep205 ep65 ep204 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz331 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 163776297) qz24)

noncomputable def ep207 := @Enclosure.Real.IsNear.cos_image qz36 qz331 Bool.false 163776297 524288 353 524288 Bool.true 218558 1048576 1 193517 (@Enclosure.Real.IsNear.recentre' qz36 Bool.false 43963364978389865379 140737488355328000 4071000002363423121 6047406250000000000000 163776297 524288 353 524288 (ep202 rfl) rfl) (Enclosure.sfrac_false_div 163776297 524288) (BSN.cos_reduce2 qz331 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 102820913897385769304064) qz25) 226375608064910080 72057594037927936 Bool.false 218558 1048576 49 1000000000000000 387034 193517 (BSN.sin_reduce_arg_pos_rat_q2 163776297 524288 226375608064910080 72057594037927936 49 102820913897385769304064 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 218558 1048576 102820913897385769304064 75557863725914323419136 2922346138 2147483648 387412 387034 (ep206 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep208 := nat_lit 4695913549476123137161089564292428782299494879825587961344222474638503890264320

noncomputable def ep209 := nat_lit 12290209025726158392321123541827633043092092944243674657073759188946609683702016

noncomputable def ep210 := BSN.sin_dyadic_bound_f 2922346138 2147483648 3 2 1048576 387412 ep208 ep94 ep204 ep209 ep96 ep204 1025545 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2922346138) qz15 0 2 ep208 ep94 ep204 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2922346138) qz16 0 2 ep209 ep96 ep204 rfl rfl rfl rfl) rfl rfl

noncomputable def ep211 := @Enclosure.Real.IsNear.sin_image qz36 qz331 Bool.false 163776297 524288 353 524288 Bool.true 1025545 1048576 1 193517 (@Enclosure.Real.IsNear.recentre' qz36 Bool.false 43963364978389865379 140737488355328000 4071000002363423121 6047406250000000000000 163776297 524288 353 524288 (ep202 rfl) rfl) (Enclosure.sfrac_false_div 163776297 524288) (BSN.sin_reduce2 qz331 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 102820913897385769304064) qz25) 226375608064910080 72057594037927936 Bool.false 1025545 1048576 49 1000000000000000 387034 193517 (BSN.sin_reduce_arg_pos_rat_q2 163776297 524288 226375608064910080 72057594037927936 49 102820913897385769304064 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1025545 1048576 102820913897385769304064 75557863725914323419136 2922346138 2147483648 387412 387034 (ep210 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz332 := (@Enclosure.Real.IsNear.recentre' qz35 Bool.false 316157 1048576 1 1048576 316157 1048576 1 1048576 (ep200 rfl rfl) rfl)

noncomputable def ep212 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz35 (Real.cos qz36)) (@HMul.hMul Real Real Real qz0 qz35 (@Neg.neg Real Real.instNeg (Real.sin qz36))) Bool.true 34549320803 549755813888 751176990445 3668520546074624 Bool.false 324233230565 1099511627776 1507739005141 7337041092149248 (@Enclosure.Real.IsNear.mulLit_ft qz35 (Real.cos qz36) 316157 1048576 1 1048576 109279 524288 68835789 101458640896 34549320803 549755813888 751176990445 3668520546074624 qz332 (@Enclosure.Real.IsNear.recentre' (Real.cos qz36) Bool.true 218558 1048576 68835789 101458640896 109279 524288 68835789 101458640896 (ep207 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz35 (@Neg.neg Real Real.instNeg (Real.sin qz36)) 316157 1048576 1 1048576 1025545 1048576 68835789 101458640896 324233230565 1099511627776 1507739005141 7337041092149248 qz332 (@Enclosure.Real.IsNear.neg (Real.sin qz36) Bool.true 1025545 1048576 68835789 101458640896 (@Enclosure.Real.IsNear.recentre' (Real.sin qz36) Bool.true 1025545 1048576 68835789 101458640896 1025545 1048576 68835789 101458640896 (ep211 rfl rfl) rfl)) rfl)

noncomputable def ep213 := @ep168 34549320803 549755813888 751176990445 3668520546074624 Bool.false 324233230565 1099511627776 1507739005141 7337041092149248 Bool.false 112174840507176191000576 204044846227 1099511627776 625648818467291 212774191672328192 Bool.false 24398525806684925853696 88761319809 1099511627776 626326575378595 212774191672328192 (ep169 (BSN.head_sum_c_succ qz5 10 11 rfl rfl) (ep198 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep199 ep212) rfl rfl

noncomputable abbrev qz37 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 12)))

noncomputable abbrev qz569 := (Real.log (Enclosure.sfrac Bool.false 12 1))

noncomputable abbrev qz38 := (@HMul.hMul Real Real Real qz268 qz279 qz569)

noncomputable def ep214 := @Enclosure.Complex.IsNear.of_eq qz560 (Complex.mk (@HMul.hMul Real Real Real qz0 qz37 (Real.cos qz38)) (@HMul.hMul Real Real Real qz0 qz37 (@Neg.neg Real Real.instNeg (Real.sin qz38)))) Bool.true 314739194751 1099511627776 41932704213121 212774191672328192 Bool.false 41017562379 1099511627776 41757711434429 212774191672328192 (BSN.cpow_neg_s_mk qz12 130272 1000 12 qz13 rfl)

noncomputable abbrev qz333 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 12) qz14)

noncomputable def ep215 := @Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 12)) 3632373 1048576 1 1048576 151348 151349 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 12)) (Real.sqrt qz333) Bool.false 3632373 1048576 1 1048576 (BSN.sqrt_natCast_div_one 12) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz333) Bool.false 3632373 1048576 1 1048576 3632373 1048576 1 1048576 (BSN.sqrt_enclosure 12 1 1816186 1816187 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep216 := BSN.log_dyadic_bound 4 20 4 3 6720000000 524288 193517 91811840 61440 212580 24 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 4) (BSN.artanhQ 20) 0 3 91811840 6720000000 61440 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep217 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz569 130272 1000 0 1 11191020447815397 4503599627370496 1000000000580551 193517000000000000000 45558644243056481187 140737488355328000 4071000002363423121 6047406250000000000000 qz18 (BSN.isNear_log_sfrac 12 1 11191020447815397 4503599627370496 1000000000580551 193517000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz333) Bool.false 46938541828353910898688 18889465931478580854784 1000000000580551 193517000000000000000 11191020447815397 4503599627370496 1000000000580551 193517000000000000000 (BSN.log_rat_reduce_isNear 12 1 3 24 16 212580 524288 24973259072661432 36028797018963968 193517 1000000000000000 rfl rfl rfl rfl (ep216 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep218 := nat_lit 5998555609622013316897718466031521

noncomputable def ep219 := BSN.cos_dyadic_bound_f 278299017 2147483648 2 1 1048576 387412 ep218 ep76 ep218 ep218 ep77 ep218 1039783 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 278299017) qz20 0 1 ep218 ep76 ep218 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 278299017) qz21 0 1 ep218 ep77 ep218 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz334 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 169719175) qz24)

noncomputable def ep220 := @Enclosure.Real.IsNear.cos_image qz38 qz334 Bool.false 169719175 524288 707 1048576 Bool.true 1039783 1048576 1 193517 (@Enclosure.Real.IsNear.recentre' qz38 Bool.false 45558644243056481187 140737488355328000 4071000002363423121 6047406250000000000000 169719175 524288 707 1048576 (ep217 rfl) rfl) (Enclosure.sfrac_false_div 169719175 524288) (BSN.cos_reduce2 qz334 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 9791776170167353999360) qz25) 226375608064910080 72057594037927936 Bool.false 1039783 1048576 51 1000000000000000 387034 193517 (BSN.sin_reduce_arg_pos_rat_q2 169719175 524288 226375608064910080 72057594037927936 51 9791776170167353999360 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1039783 1048576 9791776170167353999360 75557863725914323419136 278299017 2147483648 387412 387034 (ep219 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep221 := BSN.sin_dyadic_bound_f 278299017 2147483648 1 0 1048576 387412 0 1 1 0 1 1 135507 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 278299017) qz15 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 278299017) qz16 0 0 rfl) rfl rfl

noncomputable def ep222 := @Enclosure.Real.IsNear.sin_image qz38 qz334 Bool.false 169719175 524288 707 1048576 Bool.true 135507 1048576 1 193517 (@Enclosure.Real.IsNear.recentre' qz38 Bool.false 45558644243056481187 140737488355328000 4071000002363423121 6047406250000000000000 169719175 524288 707 1048576 (ep217 rfl) rfl) (Enclosure.sfrac_false_div 169719175 524288) (BSN.sin_reduce2 qz334 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 9791776170167353999360) qz25) 226375608064910080 72057594037927936 Bool.false 135507 1048576 51 1000000000000000 387034 193517 (BSN.sin_reduce_arg_pos_rat_q2 169719175 524288 226375608064910080 72057594037927936 51 9791776170167353999360 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 135507 1048576 9791776170167353999360 75557863725914323419136 278299017 2147483648 387412 387034 (ep221 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz335 := (@Enclosure.Real.IsNear.recentre' qz37 Bool.false 302697 1048576 1 1048576 302697 1048576 1 1048576 (ep215 rfl rfl) rfl)

noncomputable def ep223 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz37 (Real.cos qz38)) (@HMul.hMul Real Real Real qz0 qz37 (@Neg.neg Real Real.instNeg (Real.sin qz38))) Bool.true 314739194751 1099511627776 41932704213121 212774191672328192 Bool.false 41017562379 1099511627776 41757711434429 212774191672328192 (@Enclosure.Real.IsNear.mulLit_ft qz37 (Real.cos qz38) 302697 1048576 1 1048576 1039783 1048576 137865095 202917281792 314739194751 1099511627776 41932704213121 212774191672328192 qz335 (@Enclosure.Real.IsNear.recentre' (Real.cos qz38) Bool.true 1039783 1048576 137865095 202917281792 1039783 1048576 137865095 202917281792 (ep220 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz37 (@Neg.neg Real Real.instNeg (Real.sin qz38)) 302697 1048576 1 1048576 135507 1048576 137865095 202917281792 41017562379 1099511627776 41757711434429 212774191672328192 qz335 (@Enclosure.Real.IsNear.neg (Real.sin qz38) Bool.true 135507 1048576 137865095 202917281792 (@Enclosure.Real.IsNear.recentre' (Real.sin qz38) Bool.true 135507 1048576 137865095 202917281792 135507 1048576 137865095 202917281792 (ep222 rfl rfl) rfl)) rfl)

noncomputable def ep224 := @ep166 314739194751 1099511627776 41932704213121 212774191672328192 Bool.false 41017562379 1099511627776 41757711434429 212774191672328192 Bool.true 121709723331227103002624 27673587131 274877906944 166895380670103 53193547918082048 Bool.false 142693390005477612453888 32444720547 274877906944 20877633962907 6649193489760256 (ep167 (BSN.head_sum_c_succ qz5 11 12 rfl rfl) (ep213 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep214 ep223) rfl rfl

noncomputable abbrev qz39 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 13)))

noncomputable abbrev qz570 := (Real.log (Enclosure.sfrac Bool.false 13 1))

noncomputable abbrev qz40 := (@HMul.hMul Real Real Real qz268 qz279 qz570)

noncomputable def ep225 := @Enclosure.Complex.IsNear.of_eq qz559 (Complex.mk (@HMul.hMul Real Real Real qz0 qz39 (Real.cos qz40)) (@HMul.hMul Real Real Real qz0 qz39 (@Neg.neg Real Real.instNeg (Real.sin qz40)))) Bool.false 129549141111 1099511627776 40180681890549 212774191672328192 Bool.true 276064023573 1099511627776 40278174594047 212774191672328192 (BSN.cpow_neg_s_mk qz12 130272 1000 13 qz13 rfl)

noncomputable abbrev qz336 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 13) qz14)

noncomputable def ep226 := @Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 13)) 3780695 1048576 1 1048576 145411 145412 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 13)) (Real.sqrt qz336) Bool.false 3780695 1048576 1 1048576 (BSN.sqrt_natCast_div_one 13) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz336) Bool.false 3780695 1048576 1 1048576 3780695 1048576 1 1048576 (BSN.sqrt_enclosure 13 1 1890347 1890348 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep227 := BSN.log_dyadic_bound 5 21 5 4 35742602096145 524288 193517 699352521000 41015625 254545 26 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 5) (BSN.artanhQ 21) 0 4 699352521000 35742602096145 41015625 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep228 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz570 130272 1000 0 1 11551497052968677 4503599627370496 1000000000580551 193517000000000000000 47026144502635484067 140737488355328000 4071000002363423121 6047406250000000000000 qz18 (BSN.isNear_log_sfrac 13 1 11551497052968677 4503599627370496 1000000000580551 193517000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz336) Bool.false 48450490295254733815808 18889465931478580854784 1000000000580551 193517000000000000000 11551497052968677 4503599627370496 1000000000580551 193517000000000000000 (BSN.log_rat_reduce_isNear 13 1 3 26 16 254545 524288 24973259072661432 36028797018963968 193517 1000000000000000 rfl rfl rfl rfl (ep227 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep229 := nat_lit 1249127596588959967639811794405250974342774270199090397796179637718791854555136

noncomputable def ep230 := nat_lit 1219852923045320649894467808392855509806669601567053557545581391666237997056

noncomputable def ep231 := nat_lit 3744943083920789261619646447598967212008709471394137086273447750373043087671296

noncomputable def ep232 := BSN.cos_dyadic_bound_f 2431019452 2147483648 3 2 1048576 387412 ep229 ep62 ep230 ep231 ep65 ep230 445457 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2431019452) qz20 0 2 ep229 ep62 ep230 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2431019452) qz21 0 2 ep231 ep65 ep230 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz337 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 350372079) qz17)

noncomputable def ep233 := @Enclosure.Real.IsNear.cos_image qz40 qz337 Bool.false 350372079 1048576 707 1048576 Bool.false 445457 1048576 1 193517 (@Enclosure.Real.IsNear.recentre' qz40 Bool.false 47026144502635484067 140737488355328000 4071000002363423121 6047406250000000000000 350372079 1048576 707 1048576 (ep228 rfl) rfl) (Enclosure.sfrac_false_div 350372079 1048576) (BSN.cos_reduce0 qz337 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 171067785932147343228928) qz19) 226375608064910080 72057594037927936 Bool.false 445457 1048576 53 1000000000000000 387034 193517 (BSN.sin_reduce_arg_pos_rat_q0 350372079 1048576 226375608064910080 72057594037927936 53 171067785932147343228928 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 445457 1048576 171067785932147343228928 151115727451828646838272 2431019452 2147483648 387412 387034 (ep232 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep234 := nat_lit 2247453791521691685231745655682737469409148350677109073187086882780492347801600

noncomputable def ep235 := nat_lit 5884213501633785799316647578907866844293796786704177104968248989790972716056576

noncomputable def ep236 := BSN.sin_dyadic_bound_f 2431019452 2147483648 3 2 1048576 387412 ep234 ep94 ep230 ep235 ep96 ep230 949251 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2431019452) qz15 0 2 ep234 ep94 ep230 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2431019452) qz16 0 2 ep235 ep96 ep230 rfl rfl rfl rfl) rfl rfl

noncomputable def ep237 := @Enclosure.Real.IsNear.sin_image qz40 qz337 Bool.false 350372079 1048576 707 1048576 Bool.false 949251 1048576 1 193517 (@Enclosure.Real.IsNear.recentre' qz40 Bool.false 47026144502635484067 140737488355328000 4071000002363423121 6047406250000000000000 350372079 1048576 707 1048576 (ep228 rfl) rfl) (Enclosure.sfrac_false_div 350372079 1048576) (BSN.sin_reduce0 qz337 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 171067785932147343228928) qz19) 226375608064910080 72057594037927936 Bool.false 949251 1048576 53 1000000000000000 387034 193517 (BSN.sin_reduce_arg_pos_rat_q0 350372079 1048576 226375608064910080 72057594037927936 53 171067785932147343228928 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 949251 1048576 171067785932147343228928 151115727451828646838272 2431019452 2147483648 387412 387034 (ep236 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz338 := (@Enclosure.Real.IsNear.recentre' qz39 Bool.false 290823 1048576 1 1048576 290823 1048576 1 1048576 (ep226 rfl rfl) rfl)

noncomputable def ep238 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz39 (Real.cos qz40)) (@HMul.hMul Real Real Real qz0 qz39 (@Neg.neg Real Real.instNeg (Real.sin qz40))) Bool.false 129549141111 1099511627776 40180681890549 212774191672328192 Bool.true 276064023573 1099511627776 40278174594047 212774191672328192 (@Enclosure.Real.IsNear.mulLit_ff qz39 (Real.cos qz40) 290823 1048576 1 1048576 445457 1048576 137865095 202917281792 129549141111 1099511627776 40180681890549 212774191672328192 qz338 (@Enclosure.Real.IsNear.recentre' (Real.cos qz40) Bool.false 445457 1048576 137865095 202917281792 445457 1048576 137865095 202917281792 (ep233 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz39 (@Neg.neg Real Real.instNeg (Real.sin qz40)) 290823 1048576 1 1048576 949251 1048576 137865095 202917281792 276064023573 1099511627776 40278174594047 212774191672328192 qz338 (@Enclosure.Real.IsNear.neg (Real.sin qz40) Bool.false 949251 1048576 137865095 202917281792 (@Enclosure.Real.IsNear.recentre' (Real.sin qz40) Bool.false 949251 1048576 137865095 202917281792 949251 1048576 137865095 202917281792 (ep237 rfl rfl) rfl)) rfl)

noncomputable def ep239 := @ep164 129549141111 1099511627776 40180681890549 212774191672328192 Bool.true 276064023573 1099511627776 40278174594047 212774191672328192 Bool.false 5182765922177807024128 18854792587 1099511627776 707762204570961 212774191672328192 Bool.true 40210553480915913277440 146285141385 1099511627776 708362461407071 212774191672328192 (ep165 (BSN.head_sum_c_succ qz5 12 13 rfl rfl) (ep224 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep225 ep238) rfl rfl

noncomputable abbrev qz41 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 14)))

noncomputable abbrev qz571 := (Real.log (Enclosure.sfrac Bool.false 14 1))

noncomputable abbrev qz42 := (@HMul.hMul Real Real Real qz268 qz279 qz571)

noncomputable def ep240 := @Enclosure.Complex.IsNear.of_eq qz558 (Complex.mk (@HMul.hMul Real Real Real qz0 qz41 (Real.cos qz42)) (@HMul.hMul Real Real Real qz0 qz41 (@Neg.neg Real Real.instNeg (Real.sin qz42)))) Bool.true 61064108971 1099511627776 38678032456929 212774191672328192 Bool.false 143720660849 549755813888 19417176680421 106387095836164096 (BSN.cpow_neg_s_mk qz12 130272 1000 14 qz13 rfl)

noncomputable abbrev qz339 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 14) qz14)

noncomputable def ep241 := @Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 14)) 3923413 1048576 1 1048576 140121 140122 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 14)) (Real.sqrt qz339) Bool.false 3923413 1048576 1 1048576 (BSN.sqrt_natCast_div_one 14) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz339) Bool.false 3923413 1048576 1 1048576 3923413 1048576 1 1048576 (BSN.sqrt_enclosure 14 1 1961706 1961707 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep242 := BSN.log_dyadic_bound 6 22 5 4 51857700491520 524288 193517 1346332575744 176359680 293399 28 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 6) (BSN.artanhQ 22) 0 4 1346332575744 51857700491520 176359680 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep243 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz571 130272 1000 0 1 11885250371606245 4503599627370496 1000000000580551 193517000000000000000 9676970852561804679 28147497671065600 4071000002363423121 6047406250000000000000 qz18 (BSN.isNear_log_sfrac 14 1 11885250371606245 4503599627370496 1000000000580551 193517000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz339) Bool.false 49850353174629559828480 18889465931478580854784 1000000000580551 193517000000000000000 11885250371606245 4503599627370496 1000000000580551 193517000000000000000 (BSN.log_rat_reduce_isNear 14 1 3 28 16 293399 524288 24973259072661432 36028797018963968 193517 1000000000000000 rfl rfl rfl rfl (ep242 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep244 := nat_lit 2616162510359042547484812887866848727752691374345830571441392411889185465961601

noncomputable def ep245 := nat_lit 5339460626273836594056139031831249653959816361104265542398451861198947617921

noncomputable def ep246 := nat_lit 7837808609824579969266326385536883683950154490315283183239380331945158502648961

noncomputable def ep247 := BSN.cos_dyadic_bound_f 2923729391 2147483648 3 2 1048576 387412 ep244 ep62 ep245 ep246 ep65 ep245 217897 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2923729391) qz20 0 2 ep244 ep62 ep245 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2923729391) qz21 0 2 ep246 ep65 ep245 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz340 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 45061907) (@Nat.cast Real Real.instNatCast 131072))

noncomputable def ep248 := @Enclosure.Real.IsNear.cos_image qz42 qz340 Bool.false 45061907 131072 707 1048576 Bool.true 217897 1048576 1 193517 (@Enclosure.Real.IsNear.recentre' qz42 Bool.false 9676970852561804679 28147497671065600 4071000002363423121 6047406250000000000000 45061907 131072 707 1048576 (ep243 rfl) rfl) (Enclosure.sfrac_false_div 45061907 131072) (BSN.cos_reduce2 qz340 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 25717395699837356212224) (@Nat.cast Real Real.instNatCast 18889465931478580854784)) 226375608064910080 72057594037927936 Bool.false 217897 1048576 54 1000000000000000 387034 193517 (BSN.sin_reduce_arg_pos_rat_q2 45061907 131072 226375608064910080 72057594037927936 54 25717395699837356212224 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 217897 1048576 25717395699837356212224 18889465931478580854784 2923729391 2147483648 387412 387034 (ep247 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep249 := nat_lit 4704820950145257516197418286934862710231676620733611616160587579911574680636545

noncomputable def ep250 := nat_lit 12313505266509326330793337954968342217833694304003385421923369977707421105523841

noncomputable def ep251 := BSN.sin_dyadic_bound_f 2923729391 2147483648 3 2 1048576 387412 ep249 ep94 ep245 ep250 ep96 ep245 1025686 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2923729391) qz15 0 2 ep249 ep94 ep245 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2923729391) qz16 0 2 ep250 ep96 ep245 rfl rfl rfl rfl) rfl rfl

noncomputable def ep252 := @Enclosure.Real.IsNear.sin_image qz42 qz340 Bool.false 45061907 131072 707 1048576 Bool.true 1025686 1048576 1 193517 (@Enclosure.Real.IsNear.recentre' qz42 Bool.false 9676970852561804679 28147497671065600 4071000002363423121 6047406250000000000000 45061907 131072 707 1048576 (ep243 rfl) rfl) (Enclosure.sfrac_false_div 45061907 131072) (BSN.sin_reduce2 qz340 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 25717395699837356212224) (@Nat.cast Real Real.instNatCast 18889465931478580854784)) 226375608064910080 72057594037927936 Bool.false 1025686 1048576 54 1000000000000000 387034 193517 (BSN.sin_reduce_arg_pos_rat_q2 45061907 131072 226375608064910080 72057594037927936 54 25717395699837356212224 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1025686 1048576 25717395699837356212224 18889465931478580854784 2923729391 2147483648 387412 387034 (ep251 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz341 := (@Enclosure.Real.IsNear.recentre' qz41 Bool.false 280243 1048576 1 1048576 280243 1048576 1 1048576 (ep241 rfl rfl) rfl)

noncomputable def ep253 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz41 (Real.cos qz42)) (@HMul.hMul Real Real Real qz0 qz41 (@Neg.neg Real Real.instNeg (Real.sin qz42))) Bool.true 61064108971 1099511627776 38678032456929 212774191672328192 Bool.false 143720660849 549755813888 19417176680421 106387095836164096 (@Enclosure.Real.IsNear.mulLit_ft qz41 (Real.cos qz42) 280243 1048576 1 1048576 217897 1048576 137865095 202917281792 61064108971 1099511627776 38678032456929 212774191672328192 qz341 (@Enclosure.Real.IsNear.recentre' (Real.cos qz42) Bool.true 217897 1048576 137865095 202917281792 217897 1048576 137865095 202917281792 (ep248 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz41 (@Neg.neg Real Real.instNeg (Real.sin qz42)) 280243 1048576 1 1048576 512843 524288 137865095 202917281792 143720660849 549755813888 19417176680421 106387095836164096 qz341 (@Enclosure.Real.IsNear.neg (Real.sin qz42) Bool.true 512843 524288 137865095 202917281792 (@Enclosure.Real.IsNear.recentre' (Real.sin qz42) Bool.true 1025686 1048576 137865095 202917281792 512843 524288 137865095 202917281792 (ep252 rfl rfl) rfl)) rfl)

noncomputable def ep254 := @ep162 61064108971 1099511627776 38678032456929 212774191672328192 Bool.false 143720660849 549755813888 19417176680421 106387095836164096 Bool.true 46409634164684026281984 1319041137 34359738368 373220118513945 106387095836164096 Bool.false 77601430793294597586944 141156180313 1099511627776 747196814767913 212774191672328192 (ep163 (BSN.head_sum_c_succ qz5 13 14 rfl rfl) (ep239 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep240 ep253) rfl rfl

noncomputable abbrev qz43 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 15)))

noncomputable abbrev qz572 := (Real.log (Enclosure.sfrac Bool.false 15 1))

noncomputable abbrev qz44 := (@HMul.hMul Real Real Real qz268 qz279 qz572)

noncomputable def ep255 := @Enclosure.Complex.IsNear.of_eq qz557 (Complex.mk (@HMul.hMul Real Real Real qz0 qz43 (Real.cos qz44)) (@HMul.hMul Real Real Real qz0 qz43 (@Neg.neg Real Real.instNeg (Real.sin qz44)))) Bool.false 42742693893 274877906944 18724037993927 106387095836164096 Bool.true 226635937395 1099511627776 37487863663605 212774191672328192 (BSN.cpow_neg_s_mk qz12 130272 1000 15 qz13 rfl)

noncomputable abbrev qz342 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 15) qz14)

noncomputable def ep256 := @Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 15)) 4061117 1048576 1 1048576 135370 135371 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 15)) (Real.sqrt qz342) Bool.false 4061117 1048576 1 1048576 (BSN.sqrt_natCast_div_one 15) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz342) Bool.false 4061117 1048576 1 1048576 4061117 1048576 1 1048576 (BSN.sqrt_enclosure 15 1 2030558 2030559 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep257 := BSN.log_dyadic_bound 7 23 6 5 430628584065881355 524288 193517 14087658153505881 266939110305 329571 30 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 7) (BSN.artanhQ 23) 0 5 14087658153505881 430628584065881355 266939110305 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep258 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz572 130272 1000 0 1 12195965485668069 4503599627370496 1000000000580551 193517000000000000000 49649775492154708899 140737488355328000 4071000002363423121 6047406250000000000000 qz18 (BSN.isNear_log_sfrac 15 1 12195965485668069 4503599627370496 1000000000580551 193517000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz342) Bool.false 51153586820399524478976 18889465931478580854784 1000000000580551 193517000000000000000 12195965485668069 4503599627370496 1000000000580551 193517000000000000000 (BSN.log_rat_reduce_isNear 15 1 3 30 16 329571 524288 24973259072661432 36028797018963968 193517 1000000000000000 rfl rfl rfl rfl (ep257 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep259 := nat_lit 555335283238623154838840769555308675371359196114930690025615656286049200800000

noncomputable def ep260 := nat_lit 241365642018538717071919053969761456795743857897712289148027084048100000000

noncomputable def ep261 := nat_lit 1665523118431832387082378470557986503200486100628996645498550914690051402400000

noncomputable def ep262 := BSN.cos_dyadic_bound_f 1985337890 2147483648 3 2 1048576 387412 ep259 ep62 ep260 ep261 ep65 ep260 631492 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1985337890) qz20 0 2 ep259 ep62 ep260 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1985337890) qz21 0 2 ep261 ep65 ep260 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz343 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 369919653) qz17)

noncomputable def ep263 := @Enclosure.Real.IsNear.cos_image qz44 qz343 Bool.false 369919653 1048576 707 1048576 Bool.false 631492 1048576 1 193517 (@Enclosure.Real.IsNear.recentre' qz44 Bool.false 49649775492154708899 140737488355328000 4071000002363423121 6047406250000000000000 369919653 1048576 707 1048576 (ep258 rfl) rfl) (Enclosure.sfrac_false_div 369919653 1048576) (BSN.cos_reduce0 qz343 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 139705734141603789930496) qz19) 226375608064910080 72057594037927936 Bool.false 631492 1048576 56 1000000000000000 387034 193517 (BSN.sin_reduce_arg_pos_rat_q0 369919653 1048576 226375608064910080 72057594037927936 56 139705734141603789930496 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 631492 1048576 139705734141603789930496 151115727451828646838272 1985337890 2147483648 387412 387034 (ep262 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep264 := nat_lit 999410417315906847736255849956379806503009957920557072214789759647650081440000

noncomputable def ep265 := nat_lit 2617112691454583157576839357131710355625452018783910321618209707607767575200000

noncomputable def ep266 := BSN.sin_dyadic_bound_f 1985337890 2147483648 3 2 1048576 387412 ep264 ep94 ep260 ep265 ep96 ep260 837095 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1985337890) qz15 0 2 ep264 ep94 ep260 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1985337890) qz16 0 2 ep265 ep96 ep260 rfl rfl rfl rfl) rfl rfl

noncomputable def ep267 := @Enclosure.Real.IsNear.sin_image qz44 qz343 Bool.false 369919653 1048576 707 1048576 Bool.false 837095 1048576 1 193517 (@Enclosure.Real.IsNear.recentre' qz44 Bool.false 49649775492154708899 140737488355328000 4071000002363423121 6047406250000000000000 369919653 1048576 707 1048576 (ep258 rfl) rfl) (Enclosure.sfrac_false_div 369919653 1048576) (BSN.sin_reduce0 qz343 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 139705734141603789930496) qz19) 226375608064910080 72057594037927936 Bool.false 837095 1048576 56 1000000000000000 387034 193517 (BSN.sin_reduce_arg_pos_rat_q0 369919653 1048576 226375608064910080 72057594037927936 56 139705734141603789930496 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 837095 1048576 139705734141603789930496 151115727451828646838272 1985337890 2147483648 387412 387034 (ep266 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz344 := (@Enclosure.Real.IsNear.recentre' qz43 Bool.false 270741 1048576 1 1048576 270741 1048576 1 1048576 (ep256 rfl rfl) rfl)

noncomputable def ep268 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz43 (Real.cos qz44)) (@HMul.hMul Real Real Real qz0 qz43 (@Neg.neg Real Real.instNeg (Real.sin qz44))) Bool.false 42742693893 274877906944 18724037993927 106387095836164096 Bool.true 226635937395 1099511627776 37487863663605 212774191672328192 (@Enclosure.Real.IsNear.mulLit_ff qz43 (Real.cos qz44) 270741 1048576 1 1048576 157873 262144 137865095 202917281792 42742693893 274877906944 18724037993927 106387095836164096 qz344 (@Enclosure.Real.IsNear.recentre' (Real.cos qz44) Bool.false 631492 1048576 137865095 202917281792 157873 262144 137865095 202917281792 (ep263 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz43 (@Neg.neg Real Real.instNeg (Real.sin qz44)) 270741 1048576 1 1048576 837095 1048576 137865095 202917281792 226635937395 1099511627776 37487863663605 212774191672328192 qz344 (@Enclosure.Real.IsNear.neg (Real.sin qz44) Bool.false 837095 1048576 137865095 202917281792 (@Enclosure.Real.IsNear.recentre' (Real.sin qz44) Bool.false 837095 1048576 137865095 202917281792 837095 1048576 137865095 202917281792 (ep267 rfl rfl) rfl)) rfl)

noncomputable def ep269 := @ep160 42742693893 274877906944 18724037993927 106387095836164096 Bool.true 226635937395 1099511627776 37487863663605 212774191672328192 Bool.false 1106052512395397431296 32190364797 274877906944 12248254890871 3324596744880128 Bool.true 93985986851126883909632 42739878541 549755813888 392342339215759 106387095836164096 (ep161 (BSN.head_sum_c_succ qz5 14 15 rfl rfl) (ep254 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep255 ep268) rfl rfl

noncomputable abbrev qz45 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 16)))

noncomputable abbrev qz573 := (Real.log (Enclosure.sfrac Bool.false 16 1))

noncomputable abbrev qz46 := (@HMul.hMul Real Real Real qz268 qz279 qz573)

noncomputable def ep270 := @Enclosure.Complex.IsNear.of_eq qz556 (Complex.mk (@HMul.hMul Real Real Real qz0 qz45 (Real.cos qz46)) (@HMul.hMul Real Real Real qz0 qz45 (@Neg.neg Real Real.instNeg (Real.sin qz46)))) Bool.true 273702195585 1099511627776 36342557595795 212774191672328192 Bool.true 25383568833 1099511627776 36159245908307 212774191672328192 (BSN.cpow_neg_s_mk qz12 130272 1000 16 qz13 rfl)

noncomputable abbrev qz345 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 16) qz14)

noncomputable def ep271 := @Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 16)) 4194305 1048576 1 1048576 131071 131072 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 16)) (Real.sqrt qz345) Bool.false 4194305 1048576 1 1048576 (BSN.sqrt_natCast_div_one 16) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz345) Bool.false 4194305 1048576 1 1048576 4194305 1048576 1 1048576 (BSN.sqrt_enclosure 16 1 2097152 2097153 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep272 := BSN.log_dyadic_bound 0 32 1 0 1 524288 193517 0 1 0 32 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 0) (BSN.artanhQ 32) 0 0 rfl) rfl rfl rfl

noncomputable def ep273 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz573 130272 1000 0 1 3121657384082679 1125899906842624 250000000193517 48379250000000000000 12708267210600586209 35184372088832000 1017750000787807707 1511851562500000000000 qz18 (BSN.isNear_log_sfrac 16 1 3121657384082679 1125899906842624 250000000193517 48379250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz345) Bool.false 52372720210750067441664 18889465931478580854784 1000000000774068 193517000000000000000 3121657384082679 1125899906842624 250000000193517 48379250000000000000 (BSN.log_rat_reduce_isNear 16 1 4 32 32 0 524288 24973259072661432 36028797018963968 193517 1000000000000000 rfl rfl rfl rfl (ep272 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep274 := nat_lit 6543023804507654185973017083520337143398342535131249149699712521464011607244800

noncomputable def ep275 := nat_lit 10317720047438563080080892971932296358547725425653015390340993027951302803456

noncomputable def ep276 := nat_lit 17119786036490860432561580439646325943367534131797452414772028329408109243006976

noncomputable def ep277 := BSN.sin_dyadic_bound_f 3174665464 2147483648 3 2 1048576 387412 ep274 ep94 ep275 ep276 ep96 ep275 1044095 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3174665464) qz15 0 2 ep274 ep94 ep275 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3174665464) qz16 0 2 ep276 ep96 ep275 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz346 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 94683969) qz566)

noncomputable def ep278 := @Enclosure.Real.IsNear.cos_image qz46 qz346 Bool.false 94683969 262144 707 1048576 Bool.true 1044095 1048576 1 193517 (@Enclosure.Real.IsNear.recentre' qz46 Bool.false 12708267210600586209 35184372088832000 1017750000787807707 1511851562500000000000 94683969 262144 707 1048576 (ep273 rfl) rfl) (Enclosure.sfrac_false_div 94683969 262144) (BSN.cos_reduce1 qz346 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 55849305473483578277888) qz325) 226375608064910080 72057594037927936 Bool.false 1044095 1048576 57 1000000000000000 387034 193517 (BSN.sin_reduce_arg_pos_rat_q1 94683969 262144 226375608064910080 72057594037927936 57 55849305473483578277888 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1044095 1048576 55849305473483578277888 37778931862957161709568 3174665464 2147483648 387412 387034 (ep277 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep279 := nat_lit 3639598878080891686909489887721046100269544841928761978895547397714651471937536

noncomputable def ep280 := nat_lit 10898161194147797934568307877219273708091539074934979905905960207088051810205696

noncomputable def ep281 := BSN.cos_dyadic_bound_f 3174665464 2147483648 3 2 1048576 387412 ep279 ep62 ep275 ep280 ep65 ep275 96831 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3174665464) qz20 0 2 ep279 ep62 ep275 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3174665464) qz21 0 2 ep280 ep65 ep275 rfl rfl rfl rfl) rfl rfl

noncomputable def ep282 := @Enclosure.Real.IsNear.sin_image qz46 qz346 Bool.false 94683969 262144 707 1048576 Bool.false 96831 1048576 1 193517 (@Enclosure.Real.IsNear.recentre' qz46 Bool.false 12708267210600586209 35184372088832000 1017750000787807707 1511851562500000000000 94683969 262144 707 1048576 (ep273 rfl) rfl) (Enclosure.sfrac_false_div 94683969 262144) (BSN.sin_reduce1 qz346 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 55849305473483578277888) qz325) 226375608064910080 72057594037927936 Bool.false 96831 1048576 57 1000000000000000 387034 193517 (BSN.sin_reduce_arg_pos_rat_q1 94683969 262144 226375608064910080 72057594037927936 57 55849305473483578277888 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 96831 1048576 55849305473483578277888 37778931862957161709568 3174665464 2147483648 387412 387034 (ep281 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz347 := (@Enclosure.Real.IsNear.recentre' qz45 Bool.false 262143 1048576 1 1048576 262143 1048576 1 1048576 (ep271 rfl rfl) rfl)

noncomputable def ep283 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz45 (Real.cos qz46)) (@HMul.hMul Real Real Real qz0 qz45 (@Neg.neg Real Real.instNeg (Real.sin qz46))) Bool.true 273702195585 1099511627776 36342557595795 212774191672328192 Bool.true 25383568833 1099511627776 36159245908307 212774191672328192 (@Enclosure.Real.IsNear.mulLit_ft qz45 (Real.cos qz46) 262143 1048576 1 1048576 1044095 1048576 137865095 202917281792 273702195585 1099511627776 36342557595795 212774191672328192 qz347 (@Enclosure.Real.IsNear.recentre' (Real.cos qz46) Bool.true 1044095 1048576 137865095 202917281792 1044095 1048576 137865095 202917281792 (ep278 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz45 (@Neg.neg Real Real.instNeg (Real.sin qz46)) 262143 1048576 1 1048576 96831 1048576 137865095 202917281792 25383568833 1099511627776 36159245908307 212774191672328192 qz347 (@Enclosure.Real.IsNear.neg (Real.sin qz46) Bool.false 96831 1048576 137865095 202917281792 (@Enclosure.Real.IsNear.recentre' (Real.sin qz46) Bool.false 96831 1048576 137865095 202917281792 96831 1048576 137865095 202917281792 (ep282 rfl rfl) rfl)) rfl)

noncomputable def ep284 := @ep158 273702195585 1099511627776 36342557595795 212774191672328192 Bool.true 25383568833 1099511627776 36159245908307 212774191672328192 Bool.true 39841006251729399840768 144940736397 1099511627776 820230870611539 212774191672328192 Bool.true 60947757968731427307520 110863325915 1099511627776 820843924339825 212774191672328192 (ep159 (BSN.head_sum_c_succ qz5 15 16 rfl rfl) (ep269 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep270 ep283) rfl rfl

theorem EMRow44.d7 : Enclosure.Complex.IsNear qz31 Bool.true 144940736397 1099511627776 820230870611539 212774191672328192 Bool.true 110863325915 1099511627776 820843924339825 212774191672328192 := ep157 (BSN.head_sum_c_succ qz5 16 17 rfl rfl) (ep284 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable abbrev qz47 := (BSN.headSumC qz272 25)

noncomputable abbrev qz574 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 24) qz7)

noncomputable def ep285 := @Enclosure.Complex.IsNear.of_eq qz47 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 24) qz574) Bool.false 1277433911845 1099511627776 1078152370102097 212774191672328192 Bool.true 128172929219 1099511627776 1078415719259683 212774191672328192

noncomputable def ep286 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 24) qz574 Bool.false 1102766957817 1099511627776 1048485805233413 212774191672328192 Bool.true 16819302195 68719476736 262194912828895 53193547918082048 Bool.false

noncomputable abbrev qz575 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 23) qz7)

noncomputable def ep287 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 24) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 23) qz575) Bool.false 1102766957817 1099511627776 1048485805233413 212774191672328192 Bool.true 16819302195 68719476736 262194912828895 53193547918082048

noncomputable def ep288 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 23) qz575 Bool.false 873913329717 1099511627776 1018182186489281 212774191672328192 Bool.true 127702364583 549755813888 509333228778411 106387095836164096 Bool.false

noncomputable abbrev qz576 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 22) qz7)

noncomputable def ep289 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 23) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 22) qz576) Bool.false 873913329717 1099511627776 1018182186489281 212774191672328192 Bool.true 127702364583 549755813888 509333228778411 106387095836164096

noncomputable def ep290 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 22) qz576 Bool.false 674350702527 1099511627776 987188594760881 212774191672328192 Bool.true 132417751857 1099511627776 987739151786983 212774191672328192 Bool.false

noncomputable abbrev qz577 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 21) qz7)

noncomputable def ep291 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 22) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 21) qz577) Bool.false 674350702527 1099511627776 987188594760881 212774191672328192 Bool.true 132417751857 1099511627776 987739151786983 212774191672328192

noncomputable def ep292 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 21) qz577 Bool.false 502972427431 1099511627776 955396706653873 212774191672328192 Bool.false 35502625623 1099511627776 955953112537783 212774191672328192 Bool.false

noncomputable abbrev qz578 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 20) qz7)

noncomputable def ep293 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 21) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 20) qz578) Bool.false 502972427431 1099511627776 955396706653873 212774191672328192 Bool.false 35502625623 1099511627776 955953112537783 212774191672328192

noncomputable def ep294 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 20) qz578 Bool.false 39414248867 137438953472 14420571805167 3324596744880128 Bool.false 24293044135 137438953472 230874196260233 53193547918082048 Bool.false

noncomputable abbrev qz579 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 19) qz7)

noncomputable def ep295 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 20) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 19) qz579) Bool.false 39414248867 137438953472 14420571805167 3324596744880128 Bool.false 24293044135 137438953472 230874196260233 53193547918082048

noncomputable def ep296 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 19) qz579 Bool.false 74608971623 1099511627776 889558133812669 212774191672328192 Bool.false 269765132437 1099511627776 890271285757341 212774191672328192 Bool.false

noncomputable abbrev qz580 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 18) qz7)

noncomputable def ep297 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 19) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 18) qz580) Bool.false 74608971623 1099511627776 889558133812669 212774191672328192 Bool.false 269765132437 1099511627776 890271285757341 212774191672328192

noncomputable def ep298 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 18) qz580 Bool.true 39497753313 274877906944 213825594041651 53193547918082048 Bool.false 9717981263 68719476736 428054086800479 106387095836164096 Bool.false

noncomputable abbrev qz581 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 17) qz7)

noncomputable def ep299 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 18) (@HAdd.hAdd Complex Complex Complex qz4 qz31 qz581) Bool.true 39497753313 274877906944 213825594041651 53193547918082048 Bool.false 9717981263 68719476736 428054086800479 106387095836164096

noncomputable def ep300 := @Enclosure.Complex.IsNear.addLitP qz31 qz581 Bool.true 144940736397 1099511627776 820230870611539 212774191672328192 Bool.true 110863325915 1099511627776 820843924339825 212774191672328192 Bool.true

noncomputable abbrev qz48 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 17)))

noncomputable abbrev qz582 := (Real.log (Enclosure.sfrac Bool.false 17 1))

noncomputable abbrev qz49 := (@HMul.hMul Real Real Real qz268 qz279 qz582)

noncomputable def ep301 := @Enclosure.Complex.IsNear.of_eq qz581 (Complex.mk (@HMul.hMul Real Real Real qz0 qz48 (Real.cos qz49)) (@HMul.hMul Real Real Real qz0 qz48 (@Neg.neg Real Real.instNeg (Real.sin qz49)))) Bool.true 13050276855 1099511627776 35071505555065 212774191672328192 Bool.false 266351026123 1099511627776 35264249261133 212774191672328192 (BSN.cpow_neg_s_mk qz12 130272 1000 17 qz13 rfl)

noncomputable abbrev qz348 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 17) qz14)

noncomputable def ep302 := @Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 17)) 4323389 1048576 1 1048576 127158 127159 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 17)) (Real.sqrt qz348) Bool.false 4323389 1048576 1 1048576 (BSN.sqrt_natCast_div_one 17) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz348) Bool.false 4323389 1048576 1 1048576 4323389 1048576 1 1048576 (BSN.sqrt_enclosure 17 1 2161694 2161695 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep303 := BSN.log_dyadic_bound 1 33 2 1 3267 524288 193517 1 1 31784 34 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 1) (BSN.artanhQ 33) 0 1 1 3267 1 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep304 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz582 130272 1000 0 1 3189913004350711 1125899906842624 250000000193517 48379250000000000000 12986135840711744481 35184372088832000 1017750000787807707 1511851562500000000000 qz18 (BSN.isNear_log_sfrac 17 1 3189913004350711 1125899906842624 250000000193517 48379250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz348) Bool.false 53517859495200818200576 18889465931478580854784 1000000000774068 193517000000000000000 3189913004350711 1125899906842624 250000000193517 48379250000000000000 (BSN.log_rat_reduce_isNear 17 1 4 34 32 31784 524288 24973259072661432 36028797018963968 193517 1000000000000000 rfl rfl rfl rfl (ep303 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep305 := nat_lit 4088899860572209815454038182156476462591113150225466419970980350547347237488161

noncomputable def ep306 := nat_lit 13013277568713056384036523371748490048984088636580149451337751834231349954081

noncomputable def ep307 := nat_lit 12240673026579203333594041499725932407675371273403238961010265547973579012556321

noncomputable def ep308 := BSN.cos_dyadic_bound_f 3268122573 2147483648 3 2 1048576 387412 ep305 ep62 ep306 ep307 ep65 ep306 51315 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3268122573) qz20 0 2 ep305 ep62 ep306 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3268122573) qz21 0 2 ep307 ep65 ep306 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz349 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 193508503) qz24)

noncomputable def ep309 := @Enclosure.Real.IsNear.cos_image qz49 qz349 Bool.false 193508503 524288 707 1048576 Bool.true 51315 1048576 1 193517 (@Enclosure.Real.IsNear.recentre' qz49 Bool.false 12986135840711744481 35184372088832000 1017750000787807707 1511851562500000000000 193508503 524288 707 1048576 (ep304 rfl) rfl) (Enclosure.sfrac_false_div 193508503 524288) (BSN.cos_reduce2 qz349 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 114986840656595445088256) qz25) 226375608064910080 72057594037927936 Bool.false 51315 1048576 58 1000000000000000 387034 193517 (BSN.sin_reduce_arg_pos_rat_q2 193508503 524288 226375608064910080 72057594037927936 58 114986840656595445088256 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 51315 1048576 114986840656595445088256 75557863725914323419136 3268122573 2147483648 387412 387034 (ep308 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep310 := nat_lit 7349609126975007222710039509184258840624816399496575436386694429517839947515425

noncomputable def ep311 := nat_lit 19227907168870912063428330057642608932033306807555615424758224288624634819757601

noncomputable def ep312 := BSN.sin_dyadic_bound_f 3268122573 2147483648 3 2 1048576 387412 ep310 ep94 ep306 ep311 ep96 ep306 1047319 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3268122573) qz15 0 2 ep310 ep94 ep306 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3268122573) qz16 0 2 ep311 ep96 ep306 rfl rfl rfl rfl) rfl rfl

noncomputable def ep313 := @Enclosure.Real.IsNear.sin_image qz49 qz349 Bool.false 193508503 524288 707 1048576 Bool.true 1047319 1048576 1 193517 (@Enclosure.Real.IsNear.recentre' qz49 Bool.false 12986135840711744481 35184372088832000 1017750000787807707 1511851562500000000000 193508503 524288 707 1048576 (ep304 rfl) rfl) (Enclosure.sfrac_false_div 193508503 524288) (BSN.sin_reduce2 qz349 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 114986840656595445088256) qz25) 226375608064910080 72057594037927936 Bool.false 1047319 1048576 58 1000000000000000 387034 193517 (BSN.sin_reduce_arg_pos_rat_q2 193508503 524288 226375608064910080 72057594037927936 58 114986840656595445088256 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1047319 1048576 114986840656595445088256 75557863725914323419136 3268122573 2147483648 387412 387034 (ep312 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz350 := (@Enclosure.Real.IsNear.recentre' qz48 Bool.false 254317 1048576 1 1048576 254317 1048576 1 1048576 (ep302 rfl rfl) rfl)

noncomputable def ep314 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz48 (Real.cos qz49)) (@HMul.hMul Real Real Real qz0 qz48 (@Neg.neg Real Real.instNeg (Real.sin qz49))) Bool.true 13050276855 1099511627776 35071505555065 212774191672328192 Bool.false 266351026123 1099511627776 35264249261133 212774191672328192 (@Enclosure.Real.IsNear.mulLit_ft qz48 (Real.cos qz49) 254317 1048576 1 1048576 51315 1048576 137865095 202917281792 13050276855 1099511627776 35071505555065 212774191672328192 qz350 (@Enclosure.Real.IsNear.recentre' (Real.cos qz49) Bool.true 51315 1048576 137865095 202917281792 51315 1048576 137865095 202917281792 (ep309 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz48 (@Neg.neg Real Real.instNeg (Real.sin qz49)) 254317 1048576 1 1048576 1047319 1048576 137865095 202917281792 266351026123 1099511627776 35264249261133 212774191672328192 qz350 (@Enclosure.Real.IsNear.neg (Real.sin qz49) Bool.true 1047319 1048576 137865095 202917281792 (@Enclosure.Real.IsNear.recentre' (Real.sin qz49) Bool.true 1047319 1048576 137865095 202917281792 1047319 1048576 137865095 202917281792 (ep313 rfl rfl) rfl)) rfl)

noncomputable def ep315 := @ep300 13050276855 1099511627776 35071505555065 212774191672328192 Bool.false 266351026123 1099511627776 35264249261133 212774191672328192 Bool.true 173712956154686107287552 39497753313 274877906944 213825594041651 53193547918082048 Bool.false 170960534354844773777408 9717981263 68719476736 428054086800479 106387095836164096 EMRow44.d7 (ep301 ep314) rfl rfl

noncomputable abbrev qz50 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 18)))

noncomputable abbrev qz583 := (Real.log (Enclosure.sfrac Bool.false 18 1))

noncomputable abbrev qz51 := (@HMul.hMul Real Real Real qz268 qz279 qz583)

noncomputable def ep316 := @Enclosure.Complex.IsNear.of_eq qz580 (Complex.mk (@HMul.hMul Real Real Real qz0 qz50 (Real.cos qz51)) (@HMul.hMul Real Real Real qz0 qz50 (@Neg.neg Real Real.instNeg (Real.sin qz51)))) Bool.false 232599984875 1099511627776 34255757646065 212774191672328192 Bool.false 114277432229 1099511627776 34163112156383 212774191672328192 (BSN.cpow_neg_s_mk qz12 130272 1000 18 qz13 rfl)

noncomputable abbrev qz351 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 18) qz14)

noncomputable def ep317 := @Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 18)) 4448731 1048576 1 1048576 123575 123576 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 18)) (Real.sqrt qz351) Bool.false 4448731 1048576 1 1048576 (BSN.sqrt_natCast_div_one 18) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz351) Bool.false 4448731 1048576 1 1048576 4448731 1048576 1 1048576 (BSN.sqrt_enclosure 18 1 2224365 2224366 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep318 := BSN.log_dyadic_bound 2 34 3 2 20045040 524288 193517 23168 48 61752 36 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 2) (BSN.artanhQ 34) 0 2 23168 20045040 48 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep319 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz583 130272 1000 0 1 3254268794313975 1125899906842624 250000000193517 48379250000000000000 529925130466087689 1407374883553280 1017750000787807707 1511851562500000000000 qz18 (BSN.isNear_log_sfrac 18 1 3254268794313975 1125899906842624 250000000193517 48379250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz351) Bool.false 54597570484265130393600 18889465931478580854784 1000000000774068 193517000000000000000 3254268794313975 1125899906842624 250000000193517 48379250000000000000 (BSN.log_rat_reduce_isNear 18 1 4 36 32 61752 524288 24973259072661432 36028797018963968 193517 1000000000000000 rfl rfl rfl rfl (ep318 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep320 := nat_lit 2108552625463728688489824922234540989549330506242653423020802666833346895970560

noncomputable def ep321 := nat_lit 1073801337959996584130945154562207778468338363894528501741039466245192581376

noncomputable def ep322 := nat_lit 5520661197857830380146662789887839969559297825665405918908807206380082987172096

noncomputable def ep323 := BSN.sin_dyadic_bound_f 2392574626 2147483648 3 2 1048576 387412 ep320 ep94 ep321 ep322 ep96 ep321 941125 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2392574626) qz15 0 2 ep320 ep94 ep321 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2392574626) qz16 0 2 ep322 ep96 ep321 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz352 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 394824989) qz17)

noncomputable def ep324 := @Enclosure.Real.IsNear.cos_image qz51 qz352 Bool.false 394824989 1048576 707 1048576 Bool.false 941125 1048576 1 193517 (@Enclosure.Real.IsNear.recentre' qz51 Bool.false 529925130466087689 1407374883553280 1017750000787807707 1511851562500000000000 394824989 1048576 707 1048576 (ep319 rfl) rfl) (Enclosure.sfrac_false_div 394824989 1048576) (BSN.cos_reduce3 qz352 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 168362471839920488972288) qz19) 226375608064910080 72057594037927936 Bool.false 941125 1048576 59 1000000000000000 387034 193517 (BSN.sin_reduce_arg_pos_rat_q3 394824989 1048576 226375608064910080 72057594037927936 59 168362471839920488972288 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 941125 1048576 168362471839920488972288 151115727451828646838272 2392574626 2147483648 387412 387034 (ep323 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep325 := nat_lit 1171895370296720380976183154643439308762280653852093914345664165781301694464256

noncomputable def ep326 := nat_lit 3513538508214241149760287573621193510729905284828492686033510418411414698230016

noncomputable def ep327 := BSN.cos_dyadic_bound_f 2392574626 2147483648 3 2 1048576 387412 ep325 ep62 ep321 ep326 ep65 ep321 462379 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2392574626) qz20 0 2 ep325 ep62 ep321 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2392574626) qz21 0 2 ep326 ep65 ep321 rfl rfl rfl rfl) rfl rfl

noncomputable def ep328 := @Enclosure.Real.IsNear.sin_image qz51 qz352 Bool.false 394824989 1048576 707 1048576 Bool.true 462379 1048576 1 193517 (@Enclosure.Real.IsNear.recentre' qz51 Bool.false 529925130466087689 1407374883553280 1017750000787807707 1511851562500000000000 394824989 1048576 707 1048576 (ep319 rfl) rfl) (Enclosure.sfrac_false_div 394824989 1048576) (BSN.sin_reduce3 qz352 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 168362471839920488972288) qz19) 226375608064910080 72057594037927936 Bool.false 462379 1048576 59 1000000000000000 387034 193517 (BSN.sin_reduce_arg_pos_rat_q3 394824989 1048576 226375608064910080 72057594037927936 59 168362471839920488972288 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 462379 1048576 168362471839920488972288 151115727451828646838272 2392574626 2147483648 387412 387034 (ep327 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz353 := (@Enclosure.Real.IsNear.recentre' qz50 Bool.false 247151 1048576 1 1048576 247151 1048576 1 1048576 (ep317 rfl rfl) rfl)

noncomputable def ep329 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz50 (Real.cos qz51)) (@HMul.hMul Real Real Real qz0 qz50 (@Neg.neg Real Real.instNeg (Real.sin qz51))) Bool.false 232599984875 1099511627776 34255757646065 212774191672328192 Bool.false 114277432229 1099511627776 34163112156383 212774191672328192 (@Enclosure.Real.IsNear.mulLit_ff qz50 (Real.cos qz51) 247151 1048576 1 1048576 941125 1048576 137865095 202917281792 232599984875 1099511627776 34255757646065 212774191672328192 qz353 (@Enclosure.Real.IsNear.recentre' (Real.cos qz51) Bool.false 941125 1048576 137865095 202917281792 941125 1048576 137865095 202917281792 (ep324 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz50 (@Neg.neg Real Real.instNeg (Real.sin qz51)) 247151 1048576 1 1048576 462379 1048576 137865095 202917281792 114277432229 1099511627776 34163112156383 212774191672328192 qz353 (@Enclosure.Real.IsNear.neg (Real.sin qz51) Bool.true 462379 1048576 137865095 202917281792 (@Enclosure.Real.IsNear.recentre' (Real.sin qz51) Bool.true 462379 1048576 137865095 202917281792 462379 1048576 137865095 202917281792 (ep328 rfl rfl) rfl)) rfl)

noncomputable def ep330 := @ep298 232599984875 1099511627776 34255757646065 212774191672328192 Bool.false 114277432229 1099511627776 34163112156383 212774191672328192 Bool.false 20508357958974530650112 74608971623 1099511627776 889558133812669 212774191672328192 Bool.false 18538118742688380485632 269765132437 1099511627776 890271285757341 212774191672328192 (ep299 (BSN.head_sum_c_succ qz5 17 18 rfl rfl) (ep315 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep316 ep329) rfl rfl

noncomputable abbrev qz52 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 19)))

noncomputable abbrev qz584 := (Real.log (Enclosure.sfrac Bool.false 19 1))

noncomputable abbrev qz53 := (@HMul.hMul Real Real Real qz268 qz279 qz584)

noncomputable def ep331 := @Enclosure.Complex.IsNear.of_eq qz579 (Complex.mk (@HMul.hMul Real Real Real qz0 qz52 (Real.cos qz53)) (@HMul.hMul Real Real Real qz0 qz52 (@Neg.neg Real Real.instNeg (Real.sin qz53)))) Bool.false 240705019313 1099511627776 33358461718019 212774191672328192 Bool.true 75420779357 1099511627776 33225499283591 212774191672328192 (BSN.cpow_neg_s_mk qz12 130272 1000 19 qz13 rfl)

noncomputable abbrev qz354 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 19) qz14)

noncomputable def ep332 := @Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 19)) 4570637 1048576 1 1048576 120279 120280 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 19)) (Real.sqrt qz354) Bool.false 4570637 1048576 1 1048576 (BSN.sqrt_natCast_div_one 19) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz354) Bool.false 4570637 1048576 1 1048576 4570637 1048576 1 1048576 (BSN.sqrt_enclosure 19 1 2285318 2285319 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep333 := BSN.log_dyadic_bound 3 35 3 2 22509375 524288 193517 55368 243 90099 38 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 3) (BSN.artanhQ 35) 0 2 55368 22509375 243 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep334 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz584 130272 1000 0 1 3315143513283831 1125899906842624 250000000193517 48379250000000000000 13495949242578476001 35184372088832000 1017750000787807707 1511851562500000000000 qz18 (BSN.isNear_log_sfrac 19 1 3315143513283831 1125899906842624 250000000193517 48379250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz354) Bool.false 55618878793361701994496 18889465931478580854784 1000000000774068 193517000000000000000 3315143513283831 1125899906842624 250000000193517 48379250000000000000 (BSN.log_rat_reduce_isNear 19 1 4 38 32 90099 524288 24973259072661432 36028797018963968 193517 1000000000000000 rfl rfl rfl rfl (ep333 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep335 := nat_lit 180791323084856407050058031537852416

noncomputable def ep336 := BSN.cos_dyadic_bound_f 652070264 2147483648 2 1 1048576 387412 ep335 ep76 ep335 ep335 ep77 ep335 1000607 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 652070264) qz20 0 1 ep335 ep76 ep335 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 652070264) qz21 0 1 ep335 ep77 ep335 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz355 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 201105315) qz24)

noncomputable def ep337 := @Enclosure.Real.IsNear.cos_image qz53 qz355 Bool.false 201105315 524288 707 1048576 Bool.false 1000607 1048576 1 193517 (@Enclosure.Real.IsNear.recentre' qz53 Bool.false 13495949242578476001 35184372088832000 1017750000787807707 1511851562500000000000 201105315 524288 707 1048576 (ep334 rfl) rfl) (Enclosure.sfrac_false_div 201105315 524288) (BSN.cos_reduce0 qz355 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 22942682802158483537920) qz25) 226375608064910080 72057594037927936 Bool.false 1000607 1048576 61 1000000000000000 387034 193517 (BSN.sin_reduce_arg_pos_rat_q0 201105315 524288 226375608064910080 72057594037927936 61 22942682802158483537920 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1000607 1048576 22942682802158483537920 75557863725914323419136 652070264 2147483648 387412 387034 (ep336 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep338 := BSN.sin_dyadic_bound_f 652070264 2147483648 2 1 1048576 387412 ep335 ep57 ep335 ep335 ep58 ep335 313523 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 652070264) qz15 0 1 ep335 ep57 ep335 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 652070264) qz16 0 1 ep335 ep58 ep335 rfl rfl rfl rfl) rfl rfl

noncomputable def ep339 := @Enclosure.Real.IsNear.sin_image qz53 qz355 Bool.false 201105315 524288 707 1048576 Bool.false 313523 1048576 1 193517 (@Enclosure.Real.IsNear.recentre' qz53 Bool.false 13495949242578476001 35184372088832000 1017750000787807707 1511851562500000000000 201105315 524288 707 1048576 (ep334 rfl) rfl) (Enclosure.sfrac_false_div 201105315 524288) (BSN.sin_reduce0 qz355 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 22942682802158483537920) qz25) 226375608064910080 72057594037927936 Bool.false 313523 1048576 61 1000000000000000 387034 193517 (BSN.sin_reduce_arg_pos_rat_q0 201105315 524288 226375608064910080 72057594037927936 61 22942682802158483537920 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 313523 1048576 22942682802158483537920 75557863725914323419136 652070264 2147483648 387412 387034 (ep338 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz356 := (@Enclosure.Real.IsNear.recentre' qz52 Bool.false 240559 1048576 1 1048576 240559 1048576 1 1048576 (ep332 rfl rfl) rfl)

noncomputable def ep340 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz52 (Real.cos qz53)) (@HMul.hMul Real Real Real qz0 qz52 (@Neg.neg Real Real.instNeg (Real.sin qz53))) Bool.false 240705019313 1099511627776 33358461718019 212774191672328192 Bool.true 75420779357 1099511627776 33225499283591 212774191672328192 (@Enclosure.Real.IsNear.mulLit_ff qz52 (Real.cos qz53) 240559 1048576 1 1048576 1000607 1048576 137865095 202917281792 240705019313 1099511627776 33358461718019 212774191672328192 qz356 (@Enclosure.Real.IsNear.recentre' (Real.cos qz53) Bool.false 1000607 1048576 137865095 202917281792 1000607 1048576 137865095 202917281792 (ep337 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz52 (@Neg.neg Real Real.instNeg (Real.sin qz53)) 240559 1048576 1 1048576 313523 1048576 137865095 202917281792 75420779357 1099511627776 33225499283591 212774191672328192 qz356 (@Enclosure.Real.IsNear.neg (Real.sin qz53) Bool.false 313523 1048576 137865095 202917281792 (@Enclosure.Real.IsNear.recentre' (Real.sin qz53) Bool.false 313523 1048576 137865095 202917281792 313523 1048576 137865095 202917281792 (ep339 rfl rfl) rfl)) rfl)

noncomputable def ep341 := @ep296 240705019313 1099511627776 33358461718019 212774191672328192 Bool.true 75420779357 1099511627776 33225499283591 212774191672328192 Bool.false 346691399434588269838336 39414248867 137438953472 14420571805167 3324596744880128 Bool.false 213683876004064479150080 24293044135 137438953472 230874196260233 53193547918082048 (ep297 (BSN.head_sum_c_succ qz5 18 19 rfl rfl) (ep330 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep331 ep340) rfl rfl

noncomputable abbrev qz54 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 20)))

noncomputable abbrev qz585 := (Real.log (Enclosure.sfrac Bool.false 20 1))

noncomputable abbrev qz55 := (@HMul.hMul Real Real Real qz268 qz279 qz585)

noncomputable def ep342 := @Enclosure.Complex.IsNear.of_eq qz578 (Complex.mk (@HMul.hMul Real Real Real qz0 qz54 (Real.cos qz55)) (@HMul.hMul Real Real Real qz0 qz54 (@Neg.neg Real Real.instNeg (Real.sin qz55)))) Bool.false 187658436495 1099511627776 32480111123185 212774191672328192 Bool.true 158841727457 1099511627776 32456327496851 212774191672328192 (BSN.cpow_neg_s_mk qz12 130272 1000 20 qz13 rfl)

noncomputable abbrev qz357 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 20) qz14)

noncomputable def ep343 := @Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 20)) 4689375 1048576 1 1048576 117234 117235 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 20)) (Real.sqrt qz357) Bool.false 4689375 1048576 1 1048576 (BSN.sqrt_natCast_div_one 20) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz357) Bool.false 4689375 1048576 1 1048576 4689375 1048576 1 1048576 (BSN.sqrt_enclosure 20 1 2344687 2344688 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep344 := BSN.log_dyadic_bound 4 36 3 2 25194240 524288 193517 104448 768 116991 40 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 4) (BSN.artanhQ 36) 0 2 104448 25194240 768 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep345 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz585 130272 1000 0 1 3372893643545847 1125899906842624 250000000193517 48379250000000000000 13731050022875143137 35184372088832000 1017750000787807707 1511851562500000000000 qz18 (BSN.isNear_log_sfrac 20 1 3372893643545847 1125899906842624 250000000193517 48379250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz357) Bool.false 56587765202795681021952 18889465931478580854784 1000000000774068 193517000000000000000 3372893643545847 1125899906842624 250000000193517 48379250000000000000 (BSN.log_rat_reduce_isNear 20 1 4 40 32 116991 524288 24973259072661432 36028797018963968 193517 1000000000000000 rfl rfl rfl rfl (ep344 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep346 := nat_lit 185016085700898222649050845558586009324335106597626642459843997553035132716161

noncomputable def ep347 := nat_lit 26806223457770912199154210811146630200435090759856469133657256115566462081

noncomputable def ep348 := nat_lit 554994644655779126122754228254135734712604449611360214441264678146874265224321

noncomputable def ep349 := BSN.cos_dyadic_bound_f 1508444911 2147483648 3 2 1048576 387412 ep346 ep62 ep347 ep348 ep65 ep347 800355 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1508444911) qz20 0 2 ep346 ep62 ep347 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1508444911) qz21 0 2 ep348 ep65 ep347 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz358 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 409217179) qz17)

noncomputable def ep350 := @Enclosure.Real.IsNear.cos_image qz55 qz358 Bool.false 409217179 1048576 707 1048576 Bool.false 800355 1048576 1 193517 (@Enclosure.Real.IsNear.recentre' qz55 Bool.false 13731050022875143137 35184372088832000 1017750000787807707 1511851562500000000000 409217179 1048576 707 1048576 (ep345 rfl) rfl) (Enclosure.sfrac_false_div 409217179 1048576) (BSN.cos_reduce0 qz358 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 106147374092932242997248) qz19) 226375608064910080 72057594037927936 Bool.false 800355 1048576 62 1000000000000000 387034 193517 (BSN.sin_reduce_arg_pos_rat_q0 409217179 1048576 226375608064910080 72057594037927936 62 106147374092932242997248 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 800355 1048576 106147374092932242997248 151115727451828646838272 1508444911 2147483648 387412 387034 (ep349 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep351 := nat_lit 5177472690200394692870321328359922241

noncomputable def ep352 := BSN.sin_dyadic_bound_f 1508444911 2147483648 2 1 1048576 387412 ep351 ep57 ep351 ep351 ep58 ep351 677453 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1508444911) qz15 0 1 ep351 ep57 ep351 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1508444911) qz16 0 1 ep351 ep58 ep351 rfl rfl rfl rfl) rfl rfl

noncomputable def ep353 := @Enclosure.Real.IsNear.sin_image qz55 qz358 Bool.false 409217179 1048576 707 1048576 Bool.false 677453 1048576 1 193517 (@Enclosure.Real.IsNear.recentre' qz55 Bool.false 13731050022875143137 35184372088832000 1017750000787807707 1511851562500000000000 409217179 1048576 707 1048576 (ep345 rfl) rfl) (Enclosure.sfrac_false_div 409217179 1048576) (BSN.sin_reduce0 qz358 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 106147374092932242997248) qz19) 226375608064910080 72057594037927936 Bool.false 677453 1048576 62 1000000000000000 387034 193517 (BSN.sin_reduce_arg_pos_rat_q0 409217179 1048576 226375608064910080 72057594037927936 62 106147374092932242997248 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 677453 1048576 106147374092932242997248 151115727451828646838272 1508444911 2147483648 387412 387034 (ep352 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz359 := (@Enclosure.Real.IsNear.recentre' qz54 Bool.false 234469 1048576 1 1048576 234469 1048576 1 1048576 (ep343 rfl rfl) rfl)

noncomputable def ep354 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz54 (Real.cos qz55)) (@HMul.hMul Real Real Real qz0 qz54 (@Neg.neg Real Real.instNeg (Real.sin qz55))) Bool.false 187658436495 1099511627776 32480111123185 212774191672328192 Bool.true 158841727457 1099511627776 32456327496851 212774191672328192 (@Enclosure.Real.IsNear.mulLit_ff qz54 (Real.cos qz55) 234469 1048576 1 1048576 800355 1048576 137865095 202917281792 187658436495 1099511627776 32480111123185 212774191672328192 qz359 (@Enclosure.Real.IsNear.recentre' (Real.cos qz55) Bool.false 800355 1048576 137865095 202917281792 800355 1048576 137865095 202917281792 (ep350 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz54 (@Neg.neg Real Real.instNeg (Real.sin qz55)) 234469 1048576 1 1048576 677453 1048576 137865095 202917281792 158841727457 1099511627776 32456327496851 212774191672328192 qz359 (@Enclosure.Real.IsNear.neg (Real.sin qz55) Bool.false 677453 1048576 137865095 202917281792 (@Enclosure.Real.IsNear.recentre' (Real.sin qz55) Bool.false 677453 1048576 137865095 202917281792 677453 1048576 137865095 202917281792 (ep353 rfl rfl) rfl)) rfl)

noncomputable def ep355 := @ep294 187658436495 1099511627776 32480111123185 212774191672328192 Bool.true 158841727457 1099511627776 32456327496851 212774191672328192 Bool.false 69128004051388105490432 502972427431 1099511627776 955396706653873 212774191672328192 Bool.false 4879443711133332013056 35502625623 1099511627776 955953112537783 212774191672328192 (ep295 (BSN.head_sum_c_succ qz5 19 20 rfl rfl) (ep341 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep342 ep354) rfl rfl

noncomputable abbrev qz56 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 21)))

noncomputable abbrev qz586 := (Real.log (Enclosure.sfrac Bool.false 21 1))

noncomputable abbrev qz57 := (@HMul.hMul Real Real Real qz268 qz279 qz586)

noncomputable def ep356 := @Enclosure.Complex.IsNear.of_eq qz577 (Complex.mk (@HMul.hMul Real Real Real qz0 qz56 (Real.cos qz57)) (@HMul.hMul Real Real Real qz0 qz56 (@Neg.neg Real Real.instNeg (Real.sin qz57)))) Bool.false 21422284387 137438953472 62093531459 415574593110016 Bool.true 20990047185 137438953472 1986627453075 13298386979520512 (BSN.cpow_neg_s_mk qz12 130272 1000 21 qz13 rfl)

noncomputable abbrev qz360 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 21) qz14)

noncomputable def ep357 := @Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 21)) 4805179 1048576 1 1048576 114408 114410 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 21)) (Real.sqrt qz360) Bool.false 4805179 1048576 1 1048576 (BSN.sqrt_natCast_div_one 21) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz360) Bool.false 4805179 1048576 1 1048576 4805179 1048576 1 1048576 (BSN.sqrt_enclosure 21 1 2402589 2402590 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep358 := BSN.log_dyadic_bound 5 37 4 3 269401272945 524288 193517 1658093375 234375 142571 42 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 5) (BSN.artanhQ 37) 0 3 1658093375 269401272945 234375 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep359 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz586 130272 1000 0 1 3427826275261687 1125899906842624 250000000193517 48379250000000000000 13954680766590327777 35184372088832000 1017750000787807707 1511851562500000000000 qz18 (BSN.isNear_log_sfrac 21 1 3427826275261687 1125899906842624 250000000193517 48379250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz360) Bool.false 57509381830540779323392 18889465931478580854784 1000000000774068 193517000000000000000 3427826275261687 1125899906842624 250000000193517 48379250000000000000 (BSN.log_rat_reduce_isNear 21 1 4 42 32 142571 524288 24973259072661432 36028797018963968 193517 1000000000000000 rfl rfl rfl rfl (ep358 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep360 := nat_lit 274481809300901667947431849744038461778299187283035432114874005591470587890625

noncomputable def ep361 := nat_lit 58990619019024168686287254548422322376505990738450055165983593902587890625

noncomputable def ep362 := nat_lit 823327446664666955504922974723018540690144549867629396234290049586606587890625

noncomputable def ep363 := BSN.cos_dyadic_bound_f 1664745575 2147483648 3 2 1048576 387412 ep360 ep62 ep361 ep362 ep65 ep361 748972 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1664745575) qz20 0 2 ep360 ep62 ep361 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1664745575) qz21 0 2 ep362 ep65 ep361 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz361 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 415881895) qz17)

noncomputable def ep364 := @Enclosure.Real.IsNear.cos_image qz57 qz361 Bool.false 415881895 1048576 353 524288 Bool.false 748972 1048576 1 193517 (@Enclosure.Real.IsNear.recentre' qz57 Bool.false 13954680766590327777 35184372088832000 1017750000787807707 1511851562500000000000 415881895 1048576 353 524288 (ep359 rfl) rfl) (Enclosure.sfrac_false_div 415881895 1048576) (BSN.cos_reduce0 qz361 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 117146055496013478625280) qz19) 226375608064910080 72057594037927936 Bool.false 748972 1048576 63 1000000000000000 387034 193517 (BSN.sin_reduce_arg_pos_rat_q0 415881895 1048576 226375608064910080 72057594037927936 63 117146055496013478625280 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 748972 1048576 117146055496013478625280 151115727451828646838272 1664745575 2147483648 387412 387034 (ep363 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep365 := nat_lit 7680535073744808353063327979000390625

noncomputable def ep366 := BSN.sin_dyadic_bound_f 1664745575 2147483648 2 1 1048576 387412 ep365 ep57 ep365 ep365 ep58 ep365 733860 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1664745575) qz15 0 1 ep365 ep57 ep365 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1664745575) qz16 0 1 ep365 ep58 ep365 rfl rfl rfl rfl) rfl rfl

noncomputable def ep367 := @Enclosure.Real.IsNear.sin_image qz57 qz361 Bool.false 415881895 1048576 353 524288 Bool.false 733860 1048576 1 193517 (@Enclosure.Real.IsNear.recentre' qz57 Bool.false 13954680766590327777 35184372088832000 1017750000787807707 1511851562500000000000 415881895 1048576 353 524288 (ep359 rfl) rfl) (Enclosure.sfrac_false_div 415881895 1048576) (BSN.sin_reduce0 qz361 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 117146055496013478625280) qz19) 226375608064910080 72057594037927936 Bool.false 733860 1048576 63 1000000000000000 387034 193517 (BSN.sin_reduce_arg_pos_rat_q0 415881895 1048576 226375608064910080 72057594037927936 63 117146055496013478625280 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 733860 1048576 117146055496013478625280 151115727451828646838272 1664745575 2147483648 387412 387034 (ep366 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz362 := (@Enclosure.Real.IsNear.recentre' qz56 Bool.false 228818 1048576 2 1048576 114409 524288 1 524288 (ep357 rfl rfl) rfl)

noncomputable def ep368 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz56 (Real.cos qz57)) (@HMul.hMul Real Real Real qz0 qz56 (@Neg.neg Real Real.instNeg (Real.sin qz57))) Bool.false 21422284387 137438953472 62093531459 415574593110016 Bool.true 20990047185 137438953472 1986627453075 13298386979520512 (@Enclosure.Real.IsNear.mulLit_ff qz56 (Real.cos qz57) 114409 524288 1 524288 187243 262144 68835789 101458640896 21422284387 137438953472 62093531459 415574593110016 qz362 (@Enclosure.Real.IsNear.recentre' (Real.cos qz57) Bool.false 748972 1048576 68835789 101458640896 187243 262144 68835789 101458640896 (ep364 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz56 (@Neg.neg Real Real.instNeg (Real.sin qz57)) 114409 524288 1 524288 183465 262144 68835789 101458640896 20990047185 137438953472 1986627453075 13298386979520512 qz362 (@Enclosure.Real.IsNear.neg (Real.sin qz57) Bool.false 183465 262144 68835789 101458640896 (@Enclosure.Real.IsNear.recentre' (Real.sin qz57) Bool.false 733860 1048576 68835789 101458640896 183465 262144 68835789 101458640896 (ep367 rfl rfl) rfl)) rfl)

noncomputable def ep369 := @ep292 21422284387 137438953472 62093531459 415574593110016 Bool.true 20990047185 137438953472 1986627453075 13298386979520512 Bool.false 92682054828418865823744 674350702527 1099511627776 987188594760881 212774191672328192 Bool.true 18199357236341064597504 132417751857 1099511627776 987739151786983 212774191672328192 (ep293 (BSN.head_sum_c_succ qz5 20 21 rfl rfl) (ep355 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep356 ep368) rfl rfl

noncomputable abbrev qz58 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 22)))

noncomputable abbrev qz587 := (Real.log (Enclosure.sfrac Bool.false 22 1))

noncomputable abbrev qz59 := (@HMul.hMul Real Real Real qz268 qz279 qz587)

noncomputable def ep370 := @Enclosure.Complex.IsNear.of_eq qz576 (Complex.mk (@HMul.hMul Real Real Real qz0 qz58 (Real.cos qz59)) (@HMul.hMul Real Real Real qz0 qz58 (@Neg.neg Real Real.instNeg (Real.sin qz59)))) Bool.false 99781313595 549755813888 1937099483025 13298386979520512 Bool.true 122986977309 1099511627776 30927305769839 212774191672328192 (BSN.cpow_neg_s_mk qz12 130272 1000 22 qz13 rfl)

noncomputable abbrev qz363 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 22) qz14)

noncomputable def ep371 := @Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 22)) 4918257 1048576 1 1048576 111778 111779 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 22)) (Real.sqrt qz363) Bool.false 4918257 1048576 1 1048576 (BSN.sqrt_natCast_div_one 22) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz363) Bool.false 4918257 1048576 1 1048576 4918257 1048576 1 1048576 (BSN.sqrt_enclosure 22 1 2459128 2459129 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep372 := BSN.log_dyadic_bound 6 38 4 3 316148320320 524288 193517 2667271104 699840 166961 44 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 6) (BSN.artanhQ 38) 0 3 2667271104 316148320320 699840 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep373 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz587 130272 1000 0 1 3480203401436407 1125899906842624 250000000193517 48379250000000000000 14167908047247612897 35184372088832000 1017750000787807707 1511851562500000000000 qz18 (BSN.isNear_log_sfrac 22 1 3480203401436407 1125899906842624 250000000193517 48379250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz363) Bool.false 58388124189833310502912 18889465931478580854784 1000000000774068 193517000000000000000 3480203401436407 1125899906842624 250000000193517 48379250000000000000 (BSN.log_rat_reduce_isNear 22 1 4 44 32 166961 524288 24973259072661432 36028797018963968 193517 1000000000000000 rfl rfl rfl rfl (ep372 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep374 := nat_lit 1978965662372367916159123101660062736

noncomputable def ep375 := BSN.cos_dyadic_bound_f 1186067934 2147483648 2 1 1048576 387412 ep374 ep76 ep374 ep374 ep77 ep374 892670 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1186067934) qz20 0 1 ep374 ep76 ep374 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1186067934) qz21 0 1 ep374 ep77 ep374 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz364 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 422236563) qz17)

noncomputable def ep376 := @Enclosure.Real.IsNear.cos_image qz59 qz364 Bool.false 422236563 1048576 707 1048576 Bool.false 892670 1048576 1 193517 (@Enclosure.Real.IsNear.recentre' qz59 Bool.false 14167908047247612897 35184372088832000 1017750000787807707 1511851562500000000000 422236563 1048576 707 1048576 (ep373 rfl) rfl) (Enclosure.sfrac_false_div 422236563 1048576) (BSN.cos_reduce0 qz364 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 83462111066551752851456) qz19) 226375608064910080 72057594037927936 Bool.false 892670 1048576 64 1000000000000000 387034 193517 (BSN.sin_reduce_arg_pos_rat_q0 422236563 1048576 226375608064910080 72057594037927936 64 83462111066551752851456 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 892670 1048576 83462111066551752851456 151115727451828646838272 1186067934 2147483648 387412 387034 (ep375 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep377 := BSN.sin_dyadic_bound_f 1186067934 2147483648 2 1 1048576 387412 ep374 ep57 ep374 ep374 ep58 ep374 550137 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1186067934) qz15 0 1 ep374 ep57 ep374 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1186067934) qz16 0 1 ep374 ep58 ep374 rfl rfl rfl rfl) rfl rfl

noncomputable def ep378 := @Enclosure.Real.IsNear.sin_image qz59 qz364 Bool.false 422236563 1048576 707 1048576 Bool.false 550137 1048576 1 193517 (@Enclosure.Real.IsNear.recentre' qz59 Bool.false 14167908047247612897 35184372088832000 1017750000787807707 1511851562500000000000 422236563 1048576 707 1048576 (ep373 rfl) rfl) (Enclosure.sfrac_false_div 422236563 1048576) (BSN.sin_reduce0 qz364 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 83462111066551752851456) qz19) 226375608064910080 72057594037927936 Bool.false 550137 1048576 64 1000000000000000 387034 193517 (BSN.sin_reduce_arg_pos_rat_q0 422236563 1048576 226375608064910080 72057594037927936 64 83462111066551752851456 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 550137 1048576 83462111066551752851456 151115727451828646838272 1186067934 2147483648 387412 387034 (ep377 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz365 := (@Enclosure.Real.IsNear.recentre' qz58 Bool.false 223557 1048576 1 1048576 223557 1048576 1 1048576 (ep371 rfl rfl) rfl)

noncomputable def ep379 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz58 (Real.cos qz59)) (@HMul.hMul Real Real Real qz0 qz58 (@Neg.neg Real Real.instNeg (Real.sin qz59))) Bool.false 99781313595 549755813888 1937099483025 13298386979520512 Bool.true 122986977309 1099511627776 30927305769839 212774191672328192 (@Enclosure.Real.IsNear.mulLit_ff qz58 (Real.cos qz59) 223557 1048576 1 1048576 446335 524288 137865095 202917281792 99781313595 549755813888 1937099483025 13298386979520512 qz365 (@Enclosure.Real.IsNear.recentre' (Real.cos qz59) Bool.false 892670 1048576 137865095 202917281792 446335 524288 137865095 202917281792 (ep376 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz58 (@Neg.neg Real Real.instNeg (Real.sin qz59)) 223557 1048576 1 1048576 550137 1048576 137865095 202917281792 122986977309 1099511627776 30927305769839 212774191672328192 qz365 (@Enclosure.Real.IsNear.neg (Real.sin qz59) Bool.false 550137 1048576 137865095 202917281792 (@Enclosure.Real.IsNear.recentre' (Real.sin qz59) Bool.false 550137 1048576 137865095 202917281792 550137 1048576 137865095 202917281792 (ep378 rfl rfl) rfl)) rfl)

noncomputable def ep380 := @ep290 99781313595 549755813888 1937099483025 13298386979520512 Bool.true 122986977309 1099511627776 30927305769839 212774191672328192 Bool.false 480438933846141431709696 873913329717 1099511627776 1018182186489281 212774191672328192 Bool.true 280820469506997082914816 127702364583 549755813888 509333228778411 106387095836164096 (ep291 (BSN.head_sum_c_succ qz5 21 22 rfl rfl) (ep369 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep370 ep379) rfl rfl

noncomputable abbrev qz60 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 23)))

noncomputable abbrev qz588 := (Real.log (Enclosure.sfrac Bool.false 23 1))

noncomputable abbrev qz61 := (@HMul.hMul Real Real Real qz268 qz279 qz588)

noncomputable def ep381 := @Enclosure.Complex.IsNear.of_eq qz575 (Complex.mk (@HMul.hMul Real Real Real qz0 qz60 (Real.cos qz61)) (@HMul.hMul Real Real Real qz0 qz60 (@Neg.neg Real Real.instNeg (Real.sin qz61)))) Bool.false 57213407025 274877906944 7575904686033 53193547918082048 Bool.true 6852052977 549755813888 15056596879379 106387095836164096 (BSN.cpow_neg_s_mk qz12 130272 1000 23 qz13 rfl)

noncomputable abbrev qz366 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 23) qz14)

noncomputable def ep382 := @Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 23)) 5028793 1048576 1 1048576 109321 109322 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 23)) (Real.sqrt qz366) Bool.false 5028793 1048576 1 1048576 (BSN.sqrt_natCast_div_one 23) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz366) Bool.false 5028793 1048576 1 1048576 5028793 1048576 1 1048576 (BSN.sqrt_enclosure 23 1 2514396 2514397 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep383 := BSN.log_dyadic_bound 7 39 4 3 369468094905 524288 193517 4046006391 1764735 190266 46 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 7) (BSN.artanhQ 39) 0 3 4046006391 369468094905 1764735 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep384 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz588 130272 1000 0 1 3530250507853047 1125899906842624 250000000193517 48379250000000000000 14371649817469754337 35184372088832000 1017750000787807707 1511851562500000000000 qz18 (BSN.isNear_log_sfrac 23 1 3530250507853047 1125899906842624 250000000193517 48379250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz366) Bool.false 59227775304360265777152 18889465931478580854784 1000000000774068 193517000000000000000 3530250507853047 1125899906842624 250000000193517 48379250000000000000 (BSN.log_rat_reduce_isNear 23 1 4 46 32 190266 524288 24973259072661432 36028797018963968 193517 1000000000000000 rfl rfl rfl rfl (ep383 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep385 := BSN.cos_dyadic_bound_f 128441174 2147483648 1 0 1048576 387412 0 1 1 0 1 1 1046700 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 128441174) qz20 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 128441174) qz21 0 0 rfl) rfl rfl

noncomputable abbrev qz367 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 428308541) qz17)

noncomputable def ep386 := @Enclosure.Real.IsNear.cos_image qz61 qz367 Bool.false 428308541 1048576 353 524288 Bool.false 1046700 1048576 1 193517 (@Enclosure.Real.IsNear.recentre' qz61 Bool.false 14371649817469754337 35184372088832000 1017750000787807707 1511851562500000000000 428308541 1048576 353 524288 (ep384 rfl) rfl) (Enclosure.sfrac_false_div 428308541 1048576) (BSN.cos_reduce0 qz367 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 9038244119926330621952) qz19) 226375608064910080 72057594037927936 Bool.false 1046700 1048576 65 1000000000000000 387034 193517 (BSN.sin_reduce_arg_pos_rat_q0 428308541 1048576 226375608064910080 72057594037927936 65 9038244119926330621952 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1046700 1048576 9038244119926330621952 151115727451828646838272 128441174 2147483648 387412 387034 (ep385 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep387 := BSN.sin_dyadic_bound_f 128441174 2147483648 1 0 1048576 387412 0 1 1 0 1 1 62678 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 128441174) qz15 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 128441174) qz16 0 0 rfl) rfl rfl

noncomputable def ep388 := @Enclosure.Real.IsNear.sin_image qz61 qz367 Bool.false 428308541 1048576 353 524288 Bool.false 62678 1048576 1 193517 (@Enclosure.Real.IsNear.recentre' qz61 Bool.false 14371649817469754337 35184372088832000 1017750000787807707 1511851562500000000000 428308541 1048576 353 524288 (ep384 rfl) rfl) (Enclosure.sfrac_false_div 428308541 1048576) (BSN.sin_reduce0 qz367 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 9038244119926330621952) qz19) 226375608064910080 72057594037927936 Bool.false 62678 1048576 65 1000000000000000 387034 193517 (BSN.sin_reduce_arg_pos_rat_q0 428308541 1048576 226375608064910080 72057594037927936 65 9038244119926330621952 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 62678 1048576 9038244119926330621952 151115727451828646838272 128441174 2147483648 387412 387034 (ep387 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz368 := (@Enclosure.Real.IsNear.recentre' qz60 Bool.false 218643 1048576 1 1048576 218643 1048576 1 1048576 (ep382 rfl rfl) rfl)

noncomputable def ep389 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz60 (Real.cos qz61)) (@HMul.hMul Real Real Real qz0 qz60 (@Neg.neg Real Real.instNeg (Real.sin qz61))) Bool.false 57213407025 274877906944 7575904686033 53193547918082048 Bool.true 6852052977 549755813888 15056596879379 106387095836164096 (@Enclosure.Real.IsNear.mulLit_ff qz60 (Real.cos qz61) 218643 1048576 1 1048576 261675 262144 68835789 101458640896 57213407025 274877906944 7575904686033 53193547918082048 qz368 (@Enclosure.Real.IsNear.recentre' (Real.cos qz61) Bool.false 1046700 1048576 68835789 101458640896 261675 262144 68835789 101458640896 (ep386 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz60 (@Neg.neg Real Real.instNeg (Real.sin qz61)) 218643 1048576 1 1048576 31339 524288 68835789 101458640896 6852052977 549755813888 15056596879379 106387095836164096 qz368 (@Enclosure.Real.IsNear.neg (Real.sin qz61) Bool.false 31339 524288 68835789 101458640896 (@Enclosure.Real.IsNear.recentre' (Real.sin qz61) Bool.false 62678 1048576 68835789 101458640896 31339 524288 68835789 101458640896 (ep388 rfl rfl) rfl)) rfl)

noncomputable def ep390 := @ep288 57213407025 274877906944 7575904686033 53193547918082048 Bool.true 6852052977 549755813888 15056596879379 106387095836164096 Bool.false 303126273211739299381248 1102766957817 1099511627776 1048485805233413 212774191672328192 Bool.true 73972073337923599073280 16819302195 68719476736 262194912828895 53193547918082048 (ep289 (BSN.head_sum_c_succ qz5 22 23 rfl rfl) (ep380 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep381 ep389) rfl rfl

noncomputable abbrev qz62 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 24)))

noncomputable abbrev qz589 := (Real.log (Enclosure.sfrac Bool.false 24 1))

noncomputable abbrev qz63 := (@HMul.hMul Real Real Real qz268 qz279 qz589)

noncomputable def ep391 := @Enclosure.Complex.IsNear.of_eq qz574 (Complex.mk (@HMul.hMul Real Real Real qz0 qz62 (Real.cos qz63)) (@HMul.hMul Real Real Real qz0 qz62 (@Neg.neg Real Real.instNeg (Real.sin qz63)))) Bool.false 43666738507 274877906944 7416641217171 53193547918082048 Bool.false 140935905901 1099511627776 29636067944103 212774191672328192 (BSN.cpow_neg_s_mk qz12 130272 1000 24 qz13 rfl)

noncomputable abbrev qz369 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 24) qz14)

noncomputable def ep392 := @Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 24)) 5136953 1048576 1 1048576 107019 107020 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 24)) (Real.sqrt qz369) Bool.false 5136953 1048576 1 1048576 (BSN.sqrt_natCast_div_one 24) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz369) Bool.false 5136953 1048576 1 1048576 5136953 1048576 1 1048576 (BSN.sqrt_enclosure 24 1 2568476 2568477 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep393 := BSN.log_dyadic_bound 8 40 4 3 430080000000 524288 193517 5875957760 3932160 212580 48 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 8) (BSN.artanhQ 40) 0 3 5875957760 430080000000 3932160 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep394 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz589 130272 1000 0 1 3578169457974519 1125899906842624 250000000193517 48379250000000000000 14566727863414266849 35184372088832000 1017750000787807707 1511851562500000000000 qz18 (BSN.isNear_log_sfrac 24 1 3578169457974519 1125899906842624 250000000193517 48379250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz369) Bool.false 60031721881041427759104 18889465931478580854784 1000000000774068 193517000000000000000 3578169457974519 1125899906842624 250000000193517 48379250000000000000 (BSN.log_rat_reduce_isNear 24 1 4 48 32 212580 524288 24973259072661432 36028797018963968 193517 1000000000000000 rfl rfl rfl rfl (ep393 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep395 := nat_lit 865608314373261585762823615478582335116713940486233122402955630150061875101825

noncomputable def ep396 := nat_lit 181075053698649585591769946359472212521316515725003249280298450713121226881

noncomputable def ep397 := nat_lit 2266776225652553958621198984435514589342549617390865315318429976710912238518401

noncomputable def ep398 := BSN.sin_dyadic_bound_f 1915280239 2147483648 3 2 1048576 387412 ep395 ep94 ep396 ep397 ep96 ep396 816052 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1915280239) qz15 0 2 ep395 ep94 ep396 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1915280239) qz16 0 2 ep397 ep96 ep396 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz370 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 434122319) qz17)

noncomputable def ep399 := @Enclosure.Real.IsNear.cos_image qz63 qz370 Bool.false 434122319 1048576 707 1048576 Bool.false 816052 1048576 1 193517 (@Enclosure.Real.IsNear.recentre' qz63 Bool.false 14566727863414266849 35184372088832000 1017750000787807707 1511851562500000000000 434122319 1048576 707 1048576 (ep394 rfl) rfl) (Enclosure.sfrac_false_div 434122319 1048576) (BSN.cos_reduce3 qz370 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 134775865214386074288128) qz19) 226375608064910080 72057594037927936 Bool.false 816052 1048576 65 1000000000000000 387034 193517 (BSN.sin_reduce_arg_pos_rat_q3 434122319 1048576 226375608064910080 72057594037927936 65 134775865214386074288128 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 816052 1048576 134775865214386074288128 151115727451828646838272 1915280239 2147483648 387412 387034 (ep398 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep400 := nat_lit 480973985786789169684053906353149951603739440943785069445766593839240206712961

noncomputable def ep401 := nat_lit 1442559807252970209880978179166730910386175689799905201838739184616294377685121

noncomputable def ep402 := BSN.cos_dyadic_bound_f 1915280239 2147483648 3 2 1048576 387412 ep400 ep62 ep396 ep401 ep65 ep396 658459 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1915280239) qz20 0 2 ep400 ep62 ep396 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1915280239) qz21 0 2 ep401 ep65 ep396 rfl rfl rfl rfl) rfl rfl

noncomputable def ep403 := @Enclosure.Real.IsNear.sin_image qz63 qz370 Bool.false 434122319 1048576 707 1048576 Bool.true 658459 1048576 1 193517 (@Enclosure.Real.IsNear.recentre' qz63 Bool.false 14566727863414266849 35184372088832000 1017750000787807707 1511851562500000000000 434122319 1048576 707 1048576 (ep394 rfl) rfl) (Enclosure.sfrac_false_div 434122319 1048576) (BSN.sin_reduce3 qz370 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 134775865214386074288128) qz19) 226375608064910080 72057594037927936 Bool.false 658459 1048576 65 1000000000000000 387034 193517 (BSN.sin_reduce_arg_pos_rat_q3 434122319 1048576 226375608064910080 72057594037927936 65 134775865214386074288128 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 658459 1048576 134775865214386074288128 151115727451828646838272 1915280239 2147483648 387412 387034 (ep402 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz371 := (@Enclosure.Real.IsNear.recentre' qz62 Bool.false 214039 1048576 1 1048576 214039 1048576 1 1048576 (ep392 rfl rfl) rfl)

noncomputable def ep404 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz62 (Real.cos qz63)) (@HMul.hMul Real Real Real qz0 qz62 (@Neg.neg Real Real.instNeg (Real.sin qz63))) Bool.false 43666738507 274877906944 7416641217171 53193547918082048 Bool.false 140935905901 1099511627776 29636067944103 212774191672328192 (@Enclosure.Real.IsNear.mulLit_ff qz62 (Real.cos qz63) 214039 1048576 1 1048576 204013 262144 137865095 202917281792 43666738507 274877906944 7416641217171 53193547918082048 qz371 (@Enclosure.Real.IsNear.recentre' (Real.cos qz63) Bool.false 816052 1048576 137865095 202917281792 204013 262144 137865095 202917281792 (ep399 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz62 (@Neg.neg Real Real.instNeg (Real.sin qz63)) 214039 1048576 1 1048576 658459 1048576 137865095 202917281792 140935905901 1099511627776 29636067944103 212774191672328192 qz371 (@Enclosure.Real.IsNear.neg (Real.sin qz63) Bool.true 658459 1048576 137865095 202917281792 (@Enclosure.Real.IsNear.recentre' (Real.sin qz63) Bool.true 658459 1048576 137865095 202917281792 658459 1048576 137865095 202917281792 (ep403 rfl rfl) rfl)) rfl)

noncomputable def ep405 := @ep286 43666738507 274877906944 7416641217171 53193547918082048 Bool.false 140935905901 1099511627776 29636067944103 212774191672328192 Bool.false 351138359947239809351680 1277433911845 1099511627776 1078152370102097 212774191672328192 Bool.true 8807976627650045149184 128172929219 1099511627776 1078415719259683 212774191672328192 (ep287 (BSN.head_sum_c_succ qz5 23 24 rfl rfl) (ep390 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep391 ep404) rfl rfl

theorem EMRow44.d8 : Enclosure.Complex.IsNear qz47 Bool.false 1277433911845 1099511627776 1078152370102097 212774191672328192 Bool.true 128172929219 1099511627776 1078415719259683 212774191672328192 := ep285 (BSN.head_sum_c_succ qz5 24 25 rfl rfl) (ep405 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable abbrev qz590 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 32) qz7)

noncomputable def ep406 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 33) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 32) qz590) Bool.false 596571813335 549755813888 162024248047477 26596773959041024 Bool.false 10816593261 274877906944 648305631188839 106387095836164096

noncomputable def ep407 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 32) qz590 Bool.false 1072474723389 1099511627776 1270512781858957 212774191672328192 Bool.true 109106647031 1099511627776 1270896961096173 212774191672328192 Bool.false

noncomputable def ep408 := nat_lit 1311875291130491746385920

noncomputable abbrev qz591 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 31) qz7)

noncomputable def ep409 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 32) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 31) qz591) Bool.false 1072474723389 1099511627776 1270512781858957 212774191672328192 Bool.true 109106647031 1099511627776 1270896961096173 212774191672328192

noncomputable def ep410 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 31) qz591 Bool.false 252371316101 274877906944 622241961927101 106387095836164096 Bool.false 78055089827 1099511627776 1244740510173189 212774191672328192 Bool.false

noncomputable abbrev qz592 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 30) qz7)

noncomputable def ep411 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 31) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 30) qz592) Bool.false 252371316101 274877906944 622241961927101 106387095836164096 Bool.false 78055089827 1099511627776 1244740510173189 212774191672328192

noncomputable def ep412 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 30) qz592 Bool.false 1208879083637 1099511627776 1217925972321043 212774191672328192 Bool.false 27412793825 549755813888 609180315717647 106387095836164096 Bool.true

noncomputable abbrev qz593 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 29) qz7)

noncomputable def ep413 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 30) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 29) qz593) Bool.false 1208879083637 1099511627776 1217925972321043 212774191672328192 Bool.false 27412793825 549755813888 609180315717647 106387095836164096

noncomputable def ep414 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 29) qz593 Bool.false 1127121760007 1099511627776 1191000178178029 212774191672328192 Bool.true 4133249485 34359738368 297832538277507 53193547918082048 Bool.false

noncomputable abbrev qz594 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 28) qz7)

noncomputable def ep415 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 29) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 28) qz594) Bool.false 1127121760007 1099511627776 1191000178178029 212774191672328192 Bool.true 4133249485 34359738368 297832538277507 53193547918082048

noncomputable def ep416 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 28) qz594 Bool.false 475148971331 549755813888 581753800685297 106387095836164096 Bool.true 2891655183 137438953472 145487960286293 26596773959041024 Bool.false

noncomputable abbrev qz595 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 27) qz7)

noncomputable def ep417 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 28) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 27) qz595) Bool.false 475148971331 549755813888 581753800685297 106387095836164096 Bool.true 2891655183 137438953472 145487960286293 26596773959041024

noncomputable def ep418 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 27) qz595 Bool.false 528423100135 549755813888 567811650751165 106387095836164096 Bool.false 9980334487 68719476736 35498320071403 6649193489760256 Bool.true

noncomputable abbrev qz596 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 26) qz7)

noncomputable def ep419 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 27) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 26) qz596) Bool.false 528423100135 549755813888 567811650751165 106387095836164096 Bool.false 9980334487 68719476736 35498320071403 6649193489760256

noncomputable def ep420 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 26) qz596 Bool.false 630646179005 549755813888 553539890587545 106387095836164096 Bool.false 45567951443 549755813888 553765302672451 106387095836164096 Bool.true

noncomputable abbrev qz597 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 25) qz7)

noncomputable def ep421 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 26) (@HAdd.hAdd Complex Complex Complex qz4 qz47 qz597) Bool.false 630646179005 549755813888 553539890587545 106387095836164096 Bool.false 45567951443 549755813888 553765302672451 106387095836164096

noncomputable def ep422 := @Enclosure.Complex.IsNear.addLitP qz47 qz597 Bool.false 1277433911845 1099511627776 1078152370102097 212774191672328192 Bool.true 128172929219 1099511627776 1078415719259683 212774191672328192 Bool.true

noncomputable def ep423 := nat_lit 1386805613657004452085760

noncomputable abbrev qz64 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 25)))

noncomputable abbrev qz598 := (Real.log (Enclosure.sfrac Bool.false 25 1))

noncomputable abbrev qz65 := (@HMul.hMul Real Real Real qz268 qz279 qz598)

noncomputable def ep424 := @Enclosure.Complex.IsNear.of_eq qz597 (Complex.mk (@HMul.hMul Real Real Real qz0 qz64 (Real.cos qz65)) (@HMul.hMul Real Real Real qz0 qz64 (@Neg.neg Real Real.instNeg (Real.sin qz65)))) Bool.true 16141553835 1099511627776 28927411072993 212774191672328192 Bool.false 219308832105 1099511627776 29114886085219 212774191672328192 (BSN.cpow_neg_s_mk qz12 130272 1000 25 qz13 rfl)

noncomputable abbrev qz372 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 25) qz14)

noncomputable def ep425 := @Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 25)) 5242881 1048576 1 1048576 104857 104858 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 25)) (Real.sqrt qz372) Bool.false 5242881 1048576 1 1048576 (BSN.sqrt_natCast_div_one 25) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz372) Bool.false 5242881 1048576 1 1048576 5242881 1048576 1 1048576 (BSN.sqrt_enclosure 25 1 2621440 2621441 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep426 := BSN.log_dyadic_bound 9 41 5 4 7545754341519345 524288 193517 124828057765224 4519905705 233982 50 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 9) (BSN.artanhQ 41) 0 4 124828057765224 7545754341519345 4519905705 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep427 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz598 130272 1000 0 1 3624129903009015 1125899906842624 250000000193517 48379250000000000000 2950766567029940013 7036874417766400 1017750000787807707 1511851562500000000000 qz18 (BSN.isNear_log_sfrac 25 1 3624129903009015 1125899906842624 250000000193517 48379250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz372) Bool.false 60802810194841294602240 18889465931478580854784 1000000000774068 193517000000000000000 3624129903009015 1125899906842624 250000000193517 48379250000000000000 (BSN.log_rat_reduce_isNear 25 1 4 50 32 233982 524288 24973259072661432 36028797018963968 193517 1000000000000000 rfl rfl rfl rfl (ep426 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep428 := nat_lit 3830994191859385943274474841620759230928666823144879601673086840142242934690625

noncomputable def ep429 := nat_lit 11428009453209824877217858439490184096447467572342167400232597978240937890625

noncomputable def ep430 := nat_lit 11470126556671738180068988807983297324593105534289954470218795324470246928290625

noncomputable def ep431 := BSN.cos_dyadic_bound_f 3215483785 2147483648 3 2 1048576 387412 ep428 ep62 ep429 ep430 ep65 ep429 76969 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3215483785) qz20 0 2 ep428 ep62 ep429 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3215483785) qz21 0 2 ep430 ep65 ep429 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz373 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 219849241) qz24)

noncomputable def ep432 := @Enclosure.Real.IsNear.cos_image qz65 qz373 Bool.false 219849241 524288 707 1048576 Bool.true 76969 1048576 1 193517 (@Enclosure.Real.IsNear.recentre' qz65 Bool.false 2950766567029940013 7036874417766400 1017750000787807707 1511851562500000000000 219849241 524288 707 1048576 (ep427 rfl) rfl) (Enclosure.sfrac_false_div 219849241 524288) (BSN.cos_reduce2 qz373 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 113134777947100662464512) qz25) 226375608064910080 72057594037927936 Bool.false 76969 1048576 66 1000000000000000 387034 193517 (BSN.sin_reduce_arg_pos_rat_q2 219849241 524288 226375608064910080 72057594037927936 66 113134777947100662464512 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 76969 1048576 113134777947100662464512 75557863725914323419136 3215483785 2147483648 387412 387034 (ep431 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep433 := nat_lit 6886647137784326837992280428165774468394442307602909549091370233873444532130625

noncomputable def ep434 := nat_lit 18017954297939468668750000779151187119162624429557161500400831168179964637090625

noncomputable def ep435 := BSN.sin_dyadic_bound_f 3215483785 2147483648 3 2 1048576 387412 ep433 ep94 ep429 ep434 ep96 ep429 1045747 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3215483785) qz15 0 2 ep433 ep94 ep429 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3215483785) qz16 0 2 ep434 ep96 ep429 rfl rfl rfl rfl) rfl rfl

noncomputable def ep436 := @Enclosure.Real.IsNear.sin_image qz65 qz373 Bool.false 219849241 524288 707 1048576 Bool.true 1045747 1048576 1 193517 (@Enclosure.Real.IsNear.recentre' qz65 Bool.false 2950766567029940013 7036874417766400 1017750000787807707 1511851562500000000000 219849241 524288 707 1048576 (ep427 rfl) rfl) (Enclosure.sfrac_false_div 219849241 524288) (BSN.sin_reduce2 qz373 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 113134777947100662464512) qz25) 226375608064910080 72057594037927936 Bool.false 1045747 1048576 66 1000000000000000 387034 193517 (BSN.sin_reduce_arg_pos_rat_q2 219849241 524288 226375608064910080 72057594037927936 66 113134777947100662464512 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1045747 1048576 113134777947100662464512 75557863725914323419136 3215483785 2147483648 387412 387034 (ep435 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz374 := (@Enclosure.Real.IsNear.recentre' qz64 Bool.false 209715 1048576 1 1048576 209715 1048576 1 1048576 (ep425 rfl rfl) rfl)

noncomputable def ep437 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz64 (Real.cos qz65)) (@HMul.hMul Real Real Real qz0 qz64 (@Neg.neg Real Real.instNeg (Real.sin qz65))) Bool.true 16141553835 1099511627776 28927411072993 212774191672328192 Bool.false 219308832105 1099511627776 29114886085219 212774191672328192 (@Enclosure.Real.IsNear.mulLit_ft qz64 (Real.cos qz65) 209715 1048576 1 1048576 76969 1048576 137865095 202917281792 16141553835 1099511627776 28927411072993 212774191672328192 qz374 (@Enclosure.Real.IsNear.recentre' (Real.cos qz65) Bool.true 76969 1048576 137865095 202917281792 76969 1048576 137865095 202917281792 (ep432 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz64 (@Neg.neg Real Real.instNeg (Real.sin qz65)) 209715 1048576 1 1048576 1045747 1048576 137865095 202917281792 219308832105 1099511627776 29114886085219 212774191672328192 qz374 (@Enclosure.Real.IsNear.neg (Real.sin qz65) Bool.true 1045747 1048576 137865095 202917281792 (@Enclosure.Real.IsNear.recentre' (Real.sin qz65) Bool.true 1045747 1048576 137865095 202917281792 1045747 1048576 137865095 202917281792 (ep436 rfl rfl) rfl)) rfl)

noncomputable def ep438 := @ep422 16141553835 1099511627776 28927411072993 212774191672328192 Bool.false 219308832105 1099511627776 29114886085219 212774191672328192 Bool.false ep423 630646179005 549755813888 553539890587545 106387095836164096 Bool.false 100204984931021316161536 45567951443 549755813888 553765302672451 106387095836164096 EMRow44.d8 (ep424 ep437) rfl rfl

noncomputable abbrev qz66 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 26)))

noncomputable abbrev qz599 := (Real.log (Enclosure.sfrac Bool.false 26 1))

noncomputable abbrev qz67 := (@HMul.hMul Real Real Real qz268 qz279 qz599)

noncomputable def ep439 := @Enclosure.Complex.IsNear.of_eq qz596 (Complex.mk (@HMul.hMul Real Real Real qz0 qz66 (Real.cos qz67)) (@HMul.hMul Real Real Real qz0 qz66 (@Neg.neg Real Real.instNeg (Real.sin qz67)))) Bool.true 51111539435 274877906944 3567940040905 26596773959041024 Bool.false 34274724453 549755813888 14207818469997 106387095836164096 (BSN.cpow_neg_s_mk qz12 130272 1000 26 qz13 rfl)

noncomputable abbrev qz375 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 26) qz14)

noncomputable def ep440 := @Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 26)) 5346709 1048576 1 1048576 102821 102822 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 26)) (Real.sqrt qz375) Bool.false 5346709 1048576 1 1048576 (BSN.sqrt_natCast_div_one 26) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz375) Bool.false 5346709 1048576 1 1048576 5346709 1048576 1 1048576 (BSN.sqrt_enclosure 26 1 2673354 2673355 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep441 := BSN.log_dyadic_bound 10 42 5 4 9150106136613120 524288 193517 179034245376000 10500000000 254545 52 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 10) (BSN.artanhQ 42) 0 4 179034245376000 9150106136613120 10500000000 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep442 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz599 130272 1000 0 1 3668288609262839 1125899906842624 250000000193517 48379250000000000000 14933602928309017569 35184372088832000 1017750000787807707 1511851562500000000000 qz18 (BSN.isNear_log_sfrac 26 1 3668288609262839 1125899906842624 250000000193517 48379250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz375) Bool.false 61543670347942250676224 18889465931478580854784 1000000000774068 193517000000000000000 3668288609262839 1125899906842624 250000000193517 48379250000000000000 (BSN.log_rat_reduce_isNear 26 1 4 52 32 254545 524288 24973259072661432 36028797018963968 193517 1000000000000000 rfl rfl rfl rfl (ep441 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep443 := nat_lit 232965889971769889411905610387030016

noncomputable def ep444 := BSN.cos_dyadic_bound_f 694741248 2147483648 2 1 1048576 387412 ep443 ep76 ep443 ep443 ep77 ep443 994180 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 694741248) qz20 0 1 ep443 ep76 ep443 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 694741248) qz21 0 1 ep443 ep77 ep443 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz376 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 27816003) (@Nat.cast Real Real.instNatCast 65536))

noncomputable abbrev qz377 := (@Nat.cast Real Real.instNatCast 9444732965739290427392)

noncomputable def ep445 := @Enclosure.Real.IsNear.cos_image qz67 qz376 Bool.false 27816003 65536 707 1048576 Bool.true 994180 1048576 1 193517 (@Enclosure.Real.IsNear.recentre' qz67 Bool.false 14933602928309017569 35184372088832000 1017750000787807707 1511851562500000000000 27816003 65536 707 1048576 (ep442 rfl) rfl) (Enclosure.sfrac_false_div 27816003 65536) (BSN.cos_reduce2 qz376 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 3055504325245472342016) qz377) 226375608064910080 72057594037927936 Bool.false 994180 1048576 67 1000000000000000 387034 193517 (BSN.sin_reduce_arg_pos_rat_q2 27816003 65536 226375608064910080 72057594037927936 67 3055504325245472342016 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 994180 1048576 3055504325245472342016 9444732965739290427392 694741248 2147483648 387412 387034 (ep444 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep446 := BSN.sin_dyadic_bound_f 694741248 2147483648 2 1 1048576 387412 ep443 ep57 ep443 ep443 ep58 ep443 333342 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 694741248) qz15 0 1 ep443 ep57 ep443 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 694741248) qz16 0 1 ep443 ep58 ep443 rfl rfl rfl rfl) rfl rfl

noncomputable def ep447 := @Enclosure.Real.IsNear.sin_image qz67 qz376 Bool.false 27816003 65536 707 1048576 Bool.true 333342 1048576 1 193517 (@Enclosure.Real.IsNear.recentre' qz67 Bool.false 14933602928309017569 35184372088832000 1017750000787807707 1511851562500000000000 27816003 65536 707 1048576 (ep442 rfl) rfl) (Enclosure.sfrac_false_div 27816003 65536) (BSN.sin_reduce2 qz376 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 3055504325245472342016) qz377) 226375608064910080 72057594037927936 Bool.false 333342 1048576 67 1000000000000000 387034 193517 (BSN.sin_reduce_arg_pos_rat_q2 27816003 65536 226375608064910080 72057594037927936 67 3055504325245472342016 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 333342 1048576 3055504325245472342016 9444732965739290427392 694741248 2147483648 387412 387034 (ep446 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz378 := (@Enclosure.Real.IsNear.recentre' qz66 Bool.false 205643 1048576 1 1048576 205643 1048576 1 1048576 (ep440 rfl rfl) rfl)

noncomputable def ep448 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz66 (Real.cos qz67)) (@HMul.hMul Real Real Real qz0 qz66 (@Neg.neg Real Real.instNeg (Real.sin qz67))) Bool.true 51111539435 274877906944 3567940040905 26596773959041024 Bool.false 34274724453 549755813888 14207818469997 106387095836164096 (@Enclosure.Real.IsNear.mulLit_ft qz66 (Real.cos qz67) 205643 1048576 1 1048576 248545 262144 137865095 202917281792 51111539435 274877906944 3567940040905 26596773959041024 qz378 (@Enclosure.Real.IsNear.recentre' (Real.cos qz67) Bool.true 994180 1048576 137865095 202917281792 248545 262144 137865095 202917281792 (ep445 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz66 (@Neg.neg Real Real.instNeg (Real.sin qz67)) 205643 1048576 1 1048576 166671 524288 137865095 202917281792 34274724453 549755813888 14207818469997 106387095836164096 qz378 (@Enclosure.Real.IsNear.neg (Real.sin qz67) Bool.true 166671 524288 137865095 202917281792 (@Enclosure.Real.IsNear.recentre' (Real.sin qz67) Bool.true 333342 1048576 137865095 202917281792 166671 524288 137865095 202917281792 (ep447 rfl rfl) rfl)) rfl)

noncomputable def ep449 := @ep420 51111539435 274877906944 3567940040905 26596773959041024 Bool.false 34274724453 549755813888 14207818469997 106387095836164096 Bool.false 145251835745968523837440 528423100135 549755813888 567811650751165 106387095836164096 Bool.false 43893975270201279643648 9980334487 68719476736 35498320071403 6649193489760256 (ep421 (BSN.head_sum_c_succ qz5 25 26 rfl rfl) (ep438 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep439 ep448) rfl rfl

noncomputable abbrev qz68 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 27)))

noncomputable abbrev qz600 := (Real.log (Enclosure.sfrac Bool.false 27 1))

noncomputable abbrev qz69 := (@HMul.hMul Real Real Real qz268 qz279 qz600)

noncomputable def ep450 := @Enclosure.Complex.IsNear.of_eq qz595 (Complex.mk (@HMul.hMul Real Real Real qz0 qz68 (Real.cos qz69)) (@HMul.hMul Real Real Real qz0 qz68 (@Neg.neg Real Real.instNeg (Real.sin qz69)))) Bool.true 13318532201 137438953472 3485537483533 26596773959041024 Bool.true 22852324157 137438953472 3494680000681 26596773959041024 (BSN.cpow_neg_s_mk qz12 130272 1000 27 qz13 rfl)

noncomputable abbrev qz379 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 27) qz14)

noncomputable def ep451 := @Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 27)) 5448561 1048576 1 1048576 100899 100900 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 27)) (Real.sqrt qz379) Bool.false 5448561 1048576 1 1048576 (BSN.sqrt_natCast_div_one 27) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz379) Bool.false 5448561 1048576 1 1048576 5448561 1048576 1 1048576 (BSN.sqrt_enclosure 27 1 2724280 2724281 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep452 := BSN.log_dyadic_bound 11 43 5 4 11045349262332945 524288 193517 250863800262504 22507682505 274332 54 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 11) (BSN.artanhQ 43) 0 4 250863800262504 11045349262332945 22507682505 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep453 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz600 130272 1000 0 1 3710780868205815 1125899906842624 250000000193517 48379250000000000000 3021317782893174573 7036874417766400 1017750000787807707 1511851562500000000000 qz18 (BSN.isNear_log_sfrac 27 1 3710780868205815 1125899906842624 250000000193517 48379250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz379) Bool.false 62256572154556490711040 18889465931478580854784 1000000000774068 193517000000000000000 3710780868205815 1125899906842624 250000000193517 48379250000000000000 (BSN.log_rat_reduce_isNear 27 1 4 54 32 274332 524288 24973259072661432 36028797018963968 193517 1000000000000000 rfl rfl rfl rfl (ep452 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep454 := nat_lit 1648971525617925029883391375506250000

noncomputable def ep455 := BSN.sin_dyadic_bound_f 1133191450 2147483648 2 1 1048576 387412 ep454 ep57 ep454 ep454 ep58 ep454 527992 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1133191450) qz15 0 1 ep454 ep57 ep454 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1133191450) qz16 0 1 ep454 ep58 ep454 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz380 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 450211433) qz17)

noncomputable def ep456 := @Enclosure.Real.IsNear.cos_image qz69 qz380 Bool.false 450211433 1048576 353 524288 Bool.true 527992 1048576 1 193517 (@Enclosure.Real.IsNear.recentre' qz69 Bool.false 3021317782893174573 7036874417766400 1017750000787807707 1511851562500000000000 450211433 1048576 353 524288 (ep453 rfl) rfl) (Enclosure.sfrac_false_div 450211433 1048576) (BSN.cos_reduce1 qz380 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 79741259275560326004736) qz19) 226375608064910080 72057594037927936 Bool.false 527992 1048576 68 1000000000000000 387034 193517 (BSN.sin_reduce_arg_pos_rat_q1 450211433 1048576 226375608064910080 72057594037927936 68 79741259275560326004736 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 527992 1048576 79741259275560326004736 151115727451828646838272 1133191450 2147483648 387412 387034 (ep455 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep457 := BSN.cos_dyadic_bound_f 1133191450 2147483648 2 1 1048576 387412 ep454 ep76 ep454 ep454 ep77 ep454 905944 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1133191450) qz20 0 1 ep454 ep76 ep454 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1133191450) qz21 0 1 ep454 ep77 ep454 rfl rfl rfl rfl) rfl rfl

noncomputable def ep458 := @Enclosure.Real.IsNear.sin_image qz69 qz380 Bool.false 450211433 1048576 353 524288 Bool.false 905944 1048576 1 193517 (@Enclosure.Real.IsNear.recentre' qz69 Bool.false 3021317782893174573 7036874417766400 1017750000787807707 1511851562500000000000 450211433 1048576 353 524288 (ep453 rfl) rfl) (Enclosure.sfrac_false_div 450211433 1048576) (BSN.sin_reduce1 qz380 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 79741259275560326004736) qz19) 226375608064910080 72057594037927936 Bool.false 905944 1048576 68 1000000000000000 387034 193517 (BSN.sin_reduce_arg_pos_rat_q1 450211433 1048576 226375608064910080 72057594037927936 68 79741259275560326004736 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 905944 1048576 79741259275560326004736 151115727451828646838272 1133191450 2147483648 387412 387034 (ep457 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz381 := (@Enclosure.Real.IsNear.recentre' qz68 Bool.false 201799 1048576 1 1048576 201799 1048576 1 1048576 (ep451 rfl rfl) rfl)

noncomputable def ep459 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz68 (Real.cos qz69)) (@HMul.hMul Real Real Real qz0 qz68 (@Neg.neg Real Real.instNeg (Real.sin qz69))) Bool.true 13318532201 137438953472 3485537483533 26596773959041024 Bool.true 22852324157 137438953472 3494680000681 26596773959041024 (@Enclosure.Real.IsNear.mulLit_ft qz68 (Real.cos qz69) 201799 1048576 1 1048576 65999 131072 68835789 101458640896 13318532201 137438953472 3485537483533 26596773959041024 qz381 (@Enclosure.Real.IsNear.recentre' (Real.cos qz69) Bool.true 527992 1048576 68835789 101458640896 65999 131072 68835789 101458640896 (ep456 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz68 (@Neg.neg Real Real.instNeg (Real.sin qz69)) 201799 1048576 1 1048576 113243 131072 68835789 101458640896 22852324157 137438953472 3494680000681 26596773959041024 qz381 (@Enclosure.Real.IsNear.neg (Real.sin qz69) Bool.false 113243 131072 68835789 101458640896 (@Enclosure.Real.IsNear.recentre' (Real.sin qz69) Bool.false 905944 1048576 68835789 101458640896 113243 131072 68835789 101458640896 (ep458 rfl rfl) rfl)) rfl)

noncomputable def ep460 := @ep418 13318532201 137438953472 3485537483533 26596773959041024 Bool.true 22852324157 137438953472 3494680000681 26596773959041024 Bool.false 65303977363029970911232 475148971331 549755813888 581753800685297 106387095836164096 Bool.true 198713031076702322688 2891655183 137438953472 145487960286293 26596773959041024 (ep419 (BSN.head_sum_c_succ qz5 26 27 rfl rfl) (ep449 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep450 ep459) rfl rfl

noncomputable abbrev qz70 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 28)))

noncomputable abbrev qz601 := (Real.log (Enclosure.sfrac Bool.false 28 1))

noncomputable abbrev qz71 := (@HMul.hMul Real Real Real qz268 qz279 qz601)

noncomputable def ep461 := @Enclosure.Complex.IsNear.of_eq qz594 (Complex.mk (@HMul.hMul Real Real Real qz0 qz70 (Real.cos qz71)) (@HMul.hMul Real Real Real qz0 qz70 (@Neg.neg Real Real.instNeg (Real.sin qz71)))) Bool.false 176823817345 1099511627776 27492576807435 212774191672328192 Bool.true 13641342757 137438953472 6856617704921 53193547918082048 (BSN.cpow_neg_s_mk qz12 130272 1000 28 qz13 rfl)

noncomputable abbrev qz382 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 28) qz14)

noncomputable def ep462 := @Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 28)) 5548543 1048576 1 1048576 99081 99082 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 28)) (Real.sqrt qz382) Bool.false 5548543 1048576 1 1048576 (BSN.sqrt_natCast_div_one 28) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz382) Bool.false 5548543 1048576 1 1048576 5548543 1048576 1 1048576 (BSN.sqrt_enclosure 28 1 2774271 2774272 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep463 := BSN.log_dyadic_bound 12 44 5 4 13275571325829120 524288 193517 344661139390464 45148078080 293399 56 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 12) (BSN.artanhQ 44) 0 4 344661139390464 13275571325829120 45148078080 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep464 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz601 130272 1000 0 1 3751726938922231 1125899906842624 250000000193517 48379250000000000000 15273280368352402401 35184372088832000 1017750000787807707 1511851562500000000000 qz18 (BSN.isNear_log_sfrac 28 1 3751726938922231 1125899906842624 250000000193517 48379250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz382) Bool.false 62943533227317076688896 18889465931478580854784 1000000000774068 193517000000000000000 3751726938922231 1125899906842624 250000000193517 48379250000000000000 (BSN.log_rat_reduce_isNear 28 1 4 56 32 293399 524288 24973259072661432 36028797018963968 193517 1000000000000000 rfl rfl rfl rfl (ep463 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep465 := nat_lit 1988213708277563276504446495203042961

noncomputable def ep466 := BSN.cos_dyadic_bound_f 1187451187 2147483648 2 1 1048576 387412 ep465 ep76 ep465 ep465 ep77 ep465 892315 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1187451187) qz20 0 1 ep465 ep76 ep465 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1187451187) qz21 0 1 ep465 ep77 ep465 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz383 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 455179225) qz17)

noncomputable def ep467 := @Enclosure.Real.IsNear.cos_image qz71 qz383 Bool.false 455179225 1048576 707 1048576 Bool.false 892315 1048576 1 193517 (@Enclosure.Real.IsNear.recentre' qz71 Bool.false 15273280368352402401 35184372088832000 1017750000787807707 1511851562500000000000 455179225 1048576 707 1048576 (ep464 rfl) rfl) (Enclosure.sfrac_false_div 455179225 1048576) (BSN.cos_reduce0 qz383 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 83559448870479063941120) qz19) 226375608064910080 72057594037927936 Bool.false 892315 1048576 69 1000000000000000 387034 193517 (BSN.sin_reduce_arg_pos_rat_q0 455179225 1048576 226375608064910080 72057594037927936 69 83559448870479063941120 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 892315 1048576 83559448870479063941120 151115727451828646838272 1187451187 2147483648 387412 387034 (ep466 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep468 := BSN.sin_dyadic_bound_f 1187451187 2147483648 2 1 1048576 387412 ep465 ep57 ep465 ep465 ep58 ep465 550712 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1187451187) qz15 0 1 ep465 ep57 ep465 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1187451187) qz16 0 1 ep465 ep58 ep465 rfl rfl rfl rfl) rfl rfl

noncomputable def ep469 := @Enclosure.Real.IsNear.sin_image qz71 qz383 Bool.false 455179225 1048576 707 1048576 Bool.false 550712 1048576 1 193517 (@Enclosure.Real.IsNear.recentre' qz71 Bool.false 15273280368352402401 35184372088832000 1017750000787807707 1511851562500000000000 455179225 1048576 707 1048576 (ep464 rfl) rfl) (Enclosure.sfrac_false_div 455179225 1048576) (BSN.sin_reduce0 qz383 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 83559448870479063941120) qz19) 226375608064910080 72057594037927936 Bool.false 550712 1048576 69 1000000000000000 387034 193517 (BSN.sin_reduce_arg_pos_rat_q0 455179225 1048576 226375608064910080 72057594037927936 69 83559448870479063941120 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 550712 1048576 83559448870479063941120 151115727451828646838272 1187451187 2147483648 387412 387034 (ep468 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz384 := (@Enclosure.Real.IsNear.recentre' qz70 Bool.false 198163 1048576 1 1048576 198163 1048576 1 1048576 (ep462 rfl rfl) rfl)

noncomputable def ep470 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz70 (Real.cos qz71)) (@HMul.hMul Real Real Real qz0 qz70 (@Neg.neg Real Real.instNeg (Real.sin qz71))) Bool.false 176823817345 1099511627776 27492576807435 212774191672328192 Bool.true 13641342757 137438953472 6856617704921 53193547918082048 (@Enclosure.Real.IsNear.mulLit_ff qz70 (Real.cos qz71) 198163 1048576 1 1048576 892315 1048576 137865095 202917281792 176823817345 1099511627776 27492576807435 212774191672328192 qz384 (@Enclosure.Real.IsNear.recentre' (Real.cos qz71) Bool.false 892315 1048576 137865095 202917281792 892315 1048576 137865095 202917281792 (ep467 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz70 (@Neg.neg Real Real.instNeg (Real.sin qz71)) 198163 1048576 1 1048576 68839 131072 137865095 202917281792 13641342757 137438953472 6856617704921 53193547918082048 qz384 (@Enclosure.Real.IsNear.neg (Real.sin qz71) Bool.false 68839 131072 137865095 202917281792 (@Enclosure.Real.IsNear.recentre' (Real.sin qz71) Bool.false 550712 1048576 137865095 202917281792 68839 131072 137865095 202917281792 (ep469 rfl rfl) rfl)) rfl)

noncomputable def ep471 := @ep416 176823817345 1099511627776 27492576807435 212774191672328192 Bool.true 13641342757 137438953472 6856617704921 53193547918082048 Bool.false 619641740523523293577216 1127121760007 1099511627776 1191000178178029 212774191672328192 Bool.true 2272277934628331847680 4133249485 34359738368 297832538277507 53193547918082048 (ep417 (BSN.head_sum_c_succ qz5 27 28 rfl rfl) (ep460 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep461 ep470) rfl rfl

noncomputable abbrev qz72 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 29)))

noncomputable abbrev qz602 := (Real.log (Enclosure.sfrac Bool.false 29 1))

noncomputable abbrev qz73 := (@HMul.hMul Real Real Real qz268 qz279 qz602)

noncomputable def ep472 := @Enclosure.Complex.IsNear.of_eq qz593 (Complex.mk (@HMul.hMul Real Real Real qz0 qz72 (Real.cos qz73)) (@HMul.hMul Real Real Real qz0 qz72 (@Neg.neg Real Real.instNeg (Real.sin qz73)))) Bool.false 40878661815 549755813888 13462897071507 106387095836164096 Bool.false 93544785585 549755813888 13515239162633 106387095836164096 (BSN.cpow_neg_s_mk qz12 130272 1000 29 qz13 rfl)

noncomputable abbrev qz385 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 29) qz14)

noncomputable def ep473 := @Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 29)) 5646755 1048576 1 1048576 97357 97358 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 29)) (Real.sqrt qz385) Bool.false 5646755 1048576 1 1048576 (BSN.sqrt_natCast_div_one 29) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz385) Bool.false 5646755 1048576 1 1048576 5646755 1048576 1 1048576 (BSN.sqrt_enclosure 29 1 2823377 2823378 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep474 := BSN.log_dyadic_bound 13 45 6 5 353956287581982421875 524288 193517 10371179520995104305 130276274797305 311797 58 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 13) (BSN.artanhQ 45) 0 5 10371179520995104305 353956287581982421875 130276274797305 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep475 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz602 130272 1000 0 1 3791236343078135 1125899906842624 250000000193517 48379250000000000000 3086824630534217517 7036874417766400 1017750000787807707 1511851562500000000000 qz18 (BSN.isNear_log_sfrac 29 1 3791236343078135 1125899906842624 250000000193517 48379250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz385) Bool.false 63606391034871975772160 18889465931478580854784 1000000000774068 193517000000000000000 3791236343078135 1125899906842624 250000000193517 48379250000000000000 (BSN.log_rat_reduce_isNear 29 1 4 58 32 311797 524288 24973259072661432 36028797018963968 193517 1000000000000000 rfl rfl rfl rfl (ep474 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep476 := nat_lit 612710679785570597482045779845298321

noncomputable def ep477 := BSN.sin_dyadic_bound_f 884736333 2147483648 2 1 1048576 387412 ep476 ep57 ep476 ep476 ep58 ep476 419882 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 884736333) qz15 0 1 ep476 ep57 ep476 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 884736333) qz16 0 1 ep476 ep58 ep476 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz386 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 459972713) qz17)

noncomputable def ep478 := @Enclosure.Real.IsNear.cos_image qz73 qz386 Bool.false 459972713 1048576 707 1048576 Bool.false 419882 1048576 1 193517 (@Enclosure.Real.IsNear.recentre' qz73 Bool.false 3086824630534217517 7036874417766400 1017750000787807707 1511851562500000000000 459972713 1048576 707 1048576 (ep475 rfl) rfl) (Enclosure.sfrac_false_div 459972713 1048576) (BSN.cos_reduce3 qz386 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 62257784723023819964416) qz19) 226375608064910080 72057594037927936 Bool.false 419882 1048576 69 1000000000000000 387034 193517 (BSN.sin_reduce_arg_pos_rat_q3 459972713 1048576 226375608064910080 72057594037927936 69 62257784723023819964416 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 419882 1048576 62257784723023819964416 151115727451828646838272 884736333 2147483648 387412 387034 (ep477 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep479 := BSN.cos_dyadic_bound_f 884736333 2147483648 2 1 1048576 387412 ep476 ep76 ep476 ep476 ep77 ep476 960838 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 884736333) qz20 0 1 ep476 ep76 ep476 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 884736333) qz21 0 1 ep476 ep77 ep476 rfl rfl rfl rfl) rfl rfl

noncomputable def ep480 := @Enclosure.Real.IsNear.sin_image qz73 qz386 Bool.false 459972713 1048576 707 1048576 Bool.true 960838 1048576 1 193517 (@Enclosure.Real.IsNear.recentre' qz73 Bool.false 3086824630534217517 7036874417766400 1017750000787807707 1511851562500000000000 459972713 1048576 707 1048576 (ep475 rfl) rfl) (Enclosure.sfrac_false_div 459972713 1048576) (BSN.sin_reduce3 qz386 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 62257784723023819964416) qz19) 226375608064910080 72057594037927936 Bool.false 960838 1048576 69 1000000000000000 387034 193517 (BSN.sin_reduce_arg_pos_rat_q3 459972713 1048576 226375608064910080 72057594037927936 69 62257784723023819964416 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 960838 1048576 62257784723023819964416 151115727451828646838272 884736333 2147483648 387412 387034 (ep479 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz387 := (@Enclosure.Real.IsNear.recentre' qz72 Bool.false 194715 1048576 1 1048576 194715 1048576 1 1048576 (ep473 rfl rfl) rfl)

noncomputable def ep481 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz72 (Real.cos qz73)) (@HMul.hMul Real Real Real qz0 qz72 (@Neg.neg Real Real.instNeg (Real.sin qz73))) Bool.false 40878661815 549755813888 13462897071507 106387095836164096 Bool.false 93544785585 549755813888 13515239162633 106387095836164096 (@Enclosure.Real.IsNear.mulLit_ff qz72 (Real.cos qz73) 194715 1048576 1 1048576 209941 524288 137865095 202917281792 40878661815 549755813888 13462897071507 106387095836164096 qz387 (@Enclosure.Real.IsNear.recentre' (Real.cos qz73) Bool.false 419882 1048576 137865095 202917281792 209941 524288 137865095 202917281792 (ep478 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz72 (@Neg.neg Real Real.instNeg (Real.sin qz73)) 194715 1048576 1 1048576 480419 524288 137865095 202917281792 93544785585 549755813888 13515239162633 106387095836164096 qz387 (@Enclosure.Real.IsNear.neg (Real.sin qz73) Bool.true 480419 524288 137865095 202917281792 (@Enclosure.Real.IsNear.recentre' (Real.sin qz73) Bool.true 960838 1048576 137865095 202917281792 480419 524288 137865095 202917281792 (ep480 rfl rfl) rfl)) rfl)

noncomputable def ep482 := @ep414 40878661815 549755813888 13462897071507 106387095836164096 Bool.false 93544785585 549755813888 13515239162633 106387095836164096 Bool.false 664588304517038558150656 1208879083637 1099511627776 1217925972321043 212774191672328192 Bool.false 941896423762925977600 27412793825 549755813888 609180315717647 106387095836164096 (ep415 (BSN.head_sum_c_succ qz5 28 29 rfl rfl) (ep471 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep472 ep481) rfl rfl

noncomputable abbrev qz74 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 30)))

noncomputable abbrev qz603 := (Real.log (Enclosure.sfrac Bool.false 30 1))

noncomputable abbrev qz75 := (@HMul.hMul Real Real Real qz268 qz279 qz603)

noncomputable def ep483 := @Enclosure.Complex.IsNear.of_eq qz592 (Complex.mk (@HMul.hMul Real Real Real qz0 qz74 (Real.cos qz75)) (@HMul.hMul Real Real Real qz0 qz74 (@Neg.neg Real Real.instNeg (Real.sin qz75)))) Bool.true 199393819233 1099511627776 26557951533159 212774191672328192 Bool.false 23229502177 1099511627776 26379878737895 212774191672328192 (BSN.cpow_neg_s_mk qz12 130272 1000 30 qz13 rfl)

noncomputable abbrev qz388 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 30) qz14)

noncomputable def ep484 := @Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 30)) 5743287 1048576 1 1048576 95721 95722 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 30)) (Real.sqrt qz388) Bool.false 5743287 1048576 1 1048576 (BSN.sqrt_natCast_div_one 30) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz388) Bool.false 5743287 1048576 1 1048576 5743287 1048576 1 1048576 (BSN.sqrt_enclosure 30 1 2871643 2871644 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep485 := BSN.log_dyadic_bound 14 46 6 5 440963670083462507520 524288 193517 14425761949190022144 273345648952320 329571 60 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 14) (BSN.artanhQ 46) 0 5 14425761949190022144 440963670083462507520 273345648952320 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep486 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz603 130272 1000 0 1 3829405717437687 1125899906842624 250000000193517 48379250000000000000 15589510675688823777 35184372088832000 1017750000787807707 1511851562500000000000 qz18 (BSN.isNear_log_sfrac 30 1 3829405717437687 1125899906842624 250000000193517 48379250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz388) Bool.false 64246766873087041339392 18889465931478580854784 1000000000774068 193517000000000000000 3829405717437687 1125899906842624 250000000193517 48379250000000000000 (BSN.log_rat_reduce_isNear 30 1 4 60 32 329571 524288 24973259072661432 36028797018963968 193517 1000000000000000 rfl rfl rfl rfl (ep485 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep487 := nat_lit 3847937740235489409660792644550625

noncomputable def ep488 := BSN.cos_dyadic_bound_f 249061735 2147483648 2 1 1048576 387412 ep487 ep76 ep487 ep487 ep77 ep487 1041531 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 249061735) qz20 0 1 ep487 ep76 ep487 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 249061735) qz21 0 1 ep487 ep77 ep487 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz389 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 464603623) qz17)

noncomputable def ep489 := @Enclosure.Real.IsNear.cos_image qz75 qz389 Bool.false 464603623 1048576 353 524288 Bool.true 1041531 1048576 1 193517 (@Enclosure.Real.IsNear.recentre' qz75 Bool.false 15589510675688823777 35184372088832000 1017750000787807707 1511851562500000000000 464603623 1048576 353 524288 (ep486 rfl) rfl) (Enclosure.sfrac_false_div 464603623 1048576) (BSN.cos_reduce2 qz389 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 17526161528572080029696) qz19) 226375608064910080 72057594037927936 Bool.false 1041531 1048576 70 1000000000000000 387034 193517 (BSN.sin_reduce_arg_pos_rat_q2 464603623 1048576 226375608064910080 72057594037927936 70 17526161528572080029696 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1041531 1048576 17526161528572080029696 151115727451828646838272 249061735 2147483648 387412 387034 (ep488 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep490 := BSN.sin_dyadic_bound_f 249061735 2147483648 1 0 1048576 387412 0 1 1 0 1 1 121339 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 249061735) qz15 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 249061735) qz16 0 0 rfl) rfl rfl

noncomputable def ep491 := @Enclosure.Real.IsNear.sin_image qz75 qz389 Bool.false 464603623 1048576 353 524288 Bool.true 121339 1048576 1 193517 (@Enclosure.Real.IsNear.recentre' qz75 Bool.false 15589510675688823777 35184372088832000 1017750000787807707 1511851562500000000000 464603623 1048576 353 524288 (ep486 rfl) rfl) (Enclosure.sfrac_false_div 464603623 1048576) (BSN.sin_reduce2 qz389 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 17526161528572080029696) qz19) 226375608064910080 72057594037927936 Bool.false 121339 1048576 70 1000000000000000 387034 193517 (BSN.sin_reduce_arg_pos_rat_q2 464603623 1048576 226375608064910080 72057594037927936 70 17526161528572080029696 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 121339 1048576 17526161528572080029696 151115727451828646838272 249061735 2147483648 387412 387034 (ep490 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz390 := (@Enclosure.Real.IsNear.recentre' qz74 Bool.false 191443 1048576 1 1048576 191443 1048576 1 1048576 (ep484 rfl rfl) rfl)

noncomputable def ep492 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz74 (Real.cos qz75)) (@HMul.hMul Real Real Real qz0 qz74 (@Neg.neg Real Real.instNeg (Real.sin qz75))) Bool.true 199393819233 1099511627776 26557951533159 212774191672328192 Bool.false 23229502177 1099511627776 26379878737895 212774191672328192 (@Enclosure.Real.IsNear.mulLit_ft qz74 (Real.cos qz75) 191443 1048576 1 1048576 1041531 1048576 68835789 101458640896 199393819233 1099511627776 26557951533159 212774191672328192 qz390 (@Enclosure.Real.IsNear.recentre' (Real.cos qz75) Bool.true 1041531 1048576 68835789 101458640896 1041531 1048576 68835789 101458640896 (ep489 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz74 (@Neg.neg Real Real.instNeg (Real.sin qz75)) 191443 1048576 1 1048576 121339 1048576 68835789 101458640896 23229502177 1099511627776 26379878737895 212774191672328192 qz390 (@Enclosure.Real.IsNear.neg (Real.sin qz75) Bool.true 121339 1048576 68835789 101458640896 (@Enclosure.Real.IsNear.recentre' (Real.sin qz75) Bool.true 121339 1048576 68835789 101458640896 121339 1048576 68835789 101458640896 (ep491 rfl rfl) rfl)) rfl)

noncomputable def ep493 := @ep412 199393819233 1099511627776 26557951533159 212774191672328192 Bool.false 23229502177 1099511627776 26379878737895 212774191672328192 Bool.false 1109940786280727790485504 252371316101 274877906944 622241961927101 106387095836164096 Bool.false 42911239435943334117376 78055089827 1099511627776 1244740510173189 212774191672328192 (ep413 (BSN.head_sum_c_succ qz5 29 30 rfl rfl) (ep482 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep483 ep492) rfl rfl

noncomputable abbrev qz76 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 31)))

noncomputable abbrev qz604 := (Real.log (Enclosure.sfrac Bool.false 31 1))

noncomputable abbrev qz77 := (@HMul.hMul Real Real Real qz268 qz279 qz604)

noncomputable def ep494 := @Enclosure.Complex.IsNear.of_eq qz591 (Complex.mk (@HMul.hMul Real Real Real qz0 qz76 (Real.cos qz77)) (@HMul.hMul Real Real Real qz0 qz76 (@Neg.neg Real Real.instNeg (Real.sin qz77)))) Bool.false 62989458985 1099511627776 26028858004755 212774191672328192 Bool.true 93580868429 549755813888 3269556365373 26596773959041024 (BSN.cpow_neg_s_mk qz12 130272 1000 31 qz13 rfl)

noncomputable abbrev qz391 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 31) qz14)

noncomputable def ep495 := @Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 31)) 5838225 1048576 1 1048576 94164 94165 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 31)) (Real.sqrt qz391) Bool.false 5838225 1048576 1 1048576 (BSN.sqrt_natCast_div_one 31) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz391) Bool.false 5838225 1048576 1 1048576 5838225 1048576 1 1048576 (BSN.sqrt_enclosure 31 1 2919112 2919113 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep496 := BSN.log_dyadic_bound 15 47 6 5 546767979591453359355 524288 193517 19788004106328479625 544934619140625 346763 62 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 15) (BSN.artanhQ 47) 0 5 19788004106328479625 546767979591453359355 544934619140625 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep497 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz604 130272 1000 0 1 3866325256314103 1125899906842624 250000000193517 48379250000000000000 15739810118454713313 35184372088832000 1017750000787807707 1511851562500000000000 qz18 (BSN.isNear_log_sfrac 31 1 3866325256314103 1125899906842624 250000000193517 48379250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz391) Bool.false 64866173951437069877248 18889465931478580854784 1000000000774068 193517000000000000000 3866325256314103 1125899906842624 250000000193517 48379250000000000000 (BSN.log_rat_reduce_isNear 31 1 4 62 32 346763 524288 24973259072661432 36028797018963968 193517 1000000000000000 rfl rfl rfl rfl (ep496 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep498 := nat_lit 1835083395513347303087574334040977318167029950823674676223561245806416228024576

noncomputable def ep499 := nat_lit 2630317881673618279643705477276025619434335050579692543649526315684400496896

noncomputable def ep500 := nat_lit 5499989550776694672703435591168379903262221182369864643583384684787879883079936

noncomputable def ep501 := BSN.cos_dyadic_bound_f 2676091938 2147483648 3 2 1048576 387412 ep498 ep62 ep499 ep500 ep65 ep499 334465 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2676091938) qz20 0 2 ep498 ep62 ep499 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2676091938) qz21 0 2 ep500 ep65 ep499 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz392 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 469082895) qz17)

noncomputable def ep502 := @Enclosure.Real.IsNear.cos_image qz77 qz392 Bool.false 469082895 1048576 707 1048576 Bool.false 334465 1048576 1 193517 (@Enclosure.Real.IsNear.recentre' qz77 Bool.false 15739810118454713313 35184372088832000 1017750000787807707 1511851562500000000000 469082895 1048576 707 1048576 (ep497 rfl) rfl) (Enclosure.sfrac_false_div 469082895 1048576) (BSN.cos_reduce0 qz392 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 188313229046944859422720) qz19) 226375608064910080 72057594037927936 Bool.false 334465 1048576 71 1000000000000000 387034 193517 (BSN.sin_reduce_arg_pos_rat_q0 469082895 1048576 226375608064910080 72057594037927936 71 188313229046944859422720 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 334465 1048576 188313229046944859422720 151115727451828646838272 2676091938 2147483648 387412 387034 (ep501 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep503 := nat_lit 3301045857618686250933918836891938352205106443442150663167490621399001690046720

noncomputable def ep504 := nat_lit 8641337683859563846659888097277582119058099380838027472748947632486277301698816

noncomputable def ep505 := BSN.sin_dyadic_bound_f 2676091938 2147483648 3 2 1048576 387412 ep503 ep94 ep499 ep504 ep96 ep499 993802 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2676091938) qz15 0 2 ep503 ep94 ep499 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2676091938) qz16 0 2 ep504 ep96 ep499 rfl rfl rfl rfl) rfl rfl

noncomputable def ep506 := @Enclosure.Real.IsNear.sin_image qz77 qz392 Bool.false 469082895 1048576 707 1048576 Bool.false 993802 1048576 1 193517 (@Enclosure.Real.IsNear.recentre' qz77 Bool.false 15739810118454713313 35184372088832000 1017750000787807707 1511851562500000000000 469082895 1048576 707 1048576 (ep497 rfl) rfl) (Enclosure.sfrac_false_div 469082895 1048576) (BSN.sin_reduce0 qz392 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 188313229046944859422720) qz19) 226375608064910080 72057594037927936 Bool.false 993802 1048576 71 1000000000000000 387034 193517 (BSN.sin_reduce_arg_pos_rat_q0 469082895 1048576 226375608064910080 72057594037927936 71 188313229046944859422720 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 993802 1048576 188313229046944859422720 151115727451828646838272 2676091938 2147483648 387412 387034 (ep505 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz393 := (@Enclosure.Real.IsNear.recentre' qz76 Bool.false 188329 1048576 1 1048576 188329 1048576 1 1048576 (ep495 rfl rfl) rfl)

noncomputable def ep507 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz76 (Real.cos qz77)) (@HMul.hMul Real Real Real qz0 qz76 (@Neg.neg Real Real.instNeg (Real.sin qz77))) Bool.false 62989458985 1099511627776 26028858004755 212774191672328192 Bool.true 93580868429 549755813888 3269556365373 26596773959041024 (@Enclosure.Real.IsNear.mulLit_ff qz76 (Real.cos qz77) 188329 1048576 1 1048576 334465 1048576 137865095 202917281792 62989458985 1099511627776 26028858004755 212774191672328192 qz393 (@Enclosure.Real.IsNear.recentre' (Real.cos qz77) Bool.false 334465 1048576 137865095 202917281792 334465 1048576 137865095 202917281792 (ep502 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz76 (@Neg.neg Real Real.instNeg (Real.sin qz77)) 188329 1048576 1 1048576 496901 524288 137865095 202917281792 93580868429 549755813888 3269556365373 26596773959041024 qz393 (@Enclosure.Real.IsNear.neg (Real.sin qz77) Bool.false 496901 524288 137865095 202917281792 (@Enclosure.Real.IsNear.recentre' (Real.sin qz77) Bool.false 993802 1048576 137865095 202917281792 496901 524288 137865095 202917281792 (ep506 rfl rfl) rfl)) rfl)

noncomputable def ep508 := @ep410 62989458985 1099511627776 26028858004755 212774191672328192 Bool.true 93580868429 549755813888 3269556365373 26596773959041024 Bool.false 294799607215513682313216 1072474723389 1099511627776 1270512781858957 212774191672328192 Bool.true 59982013539118143766528 109106647031 1099511627776 1270896961096173 212774191672328192 (ep411 (BSN.head_sum_c_succ qz5 30 31 rfl rfl) (ep493 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep494 ep507) rfl rfl

noncomputable abbrev qz78 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 32)))

noncomputable abbrev qz605 := (Real.log (Enclosure.sfrac Bool.false 32 1))

noncomputable abbrev qz79 := (@HMul.hMul Real Real Real qz268 qz279 qz605)

noncomputable def ep509 := @Enclosure.Complex.IsNear.of_eq qz590 (Complex.mk (@HMul.hMul Real Real Real qz0 qz78 (Real.cos qz79)) (@HMul.hMul Real Real Real qz0 qz78 (@Neg.neg Real Real.instNeg (Real.sin qz79)))) Bool.false 120668903281 1099511627776 25681202520859 212774191672328192 Bool.false 152373020075 1099511627776 25714301281505 212774191672328192 (BSN.cpow_neg_s_mk qz12 130272 1000 32 qz13 rfl)

noncomputable abbrev qz394 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 32) qz14)

noncomputable def ep510 := @Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 32)) 5931641 1048576 1 1048576 92681 92682 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 32)) (Real.sqrt qz394) Bool.false 5931641 1048576 1 1048576 (BSN.sqrt_natCast_div_one 32) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz394) Bool.false 5931641 1048576 1 1048576 5931641 1048576 1 1048576 (BSN.sqrt_enclosure 32 1 2965820 2965821 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep511 := BSN.log_dyadic_bound 0 64 1 0 1 524288 193517 0 1 0 64 64 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 0) (BSN.artanhQ 64) 0 0 rfl) rfl rfl rfl

noncomputable def ep512 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz605 130272 1000 0 1 15608286920413395 4503599627370496 200000000193517 38703400000000000000 12708267210600586209 28147497671065600 814200000787807707 1209481250000000000000 qz18 (BSN.isNear_log_sfrac 32 1 15608286920413395 4503599627370496 200000000193517 38703400000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz394) Bool.false 65465900263437584302080 18889465931478580854784 1000000000967585 193517000000000000000 15608286920413395 4503599627370496 200000000193517 38703400000000000000 (BSN.log_rat_reduce_isNear 32 1 5 64 64 0 524288 24973259072661432 36028797018963968 193517 1000000000000000 rfl rfl rfl rfl (ep511 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep513 := nat_lit 4280586832235603651578965990617760000

noncomputable def ep514 := BSN.sin_dyadic_bound_f 1438387260 2147483648 2 1 1048576 387412 ep513 ep57 ep513 ep513 ep58 ep513 650987 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1438387260) qz15 0 1 ep513 ep57 ep513 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1438387260) qz16 0 1 ep513 ep58 ep513 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz395 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 473419845) qz17)

noncomputable def ep515 := @Enclosure.Real.IsNear.cos_image qz79 qz395 Bool.false 473419845 1048576 707 1048576 Bool.false 650987 1048576 1 193517 (@Enclosure.Real.IsNear.recentre' qz79 Bool.false 12708267210600586209 28147497671065600 814200000787807707 1209481250000000000000 473419845 1048576 707 1048576 (ep512 rfl) rfl) (Enclosure.sfrac_false_div 473419845 1048576) (BSN.cos_reduce3 qz395 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 101217505165714527354880) qz19) 226375608064910080 72057594037927936 Bool.false 650987 1048576 71 1000000000000000 387034 193517 (BSN.sin_reduce_arg_pos_rat_q3 473419845 1048576 226375608064910080 72057594037927936 71 101217505165714527354880 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 650987 1048576 101217505165714527354880 151115727451828646838272 1438387260 2147483648 387412 387034 (ep514 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep516 := nat_lit 152962186427420309539805911803779512529883548710063986674776505161068748800000

noncomputable def ep517 := nat_lit 18323423628308840001095584735865780806396593621175524160346427417600000000

noncomputable def ep518 := nat_lit 458849912435004310939415544241866806028037852942949608976008822628371046400000

noncomputable def ep519 := BSN.cos_dyadic_bound_f 1438387260 2147483648 3 2 1048576 387412 ep516 ep62 ep517 ep518 ep65 ep517 822025 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1438387260) qz20 0 2 ep516 ep62 ep517 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1438387260) qz21 0 2 ep518 ep65 ep517 rfl rfl rfl rfl) rfl rfl

noncomputable def ep520 := @Enclosure.Real.IsNear.sin_image qz79 qz395 Bool.false 473419845 1048576 707 1048576 Bool.true 822025 1048576 1 193517 (@Enclosure.Real.IsNear.recentre' qz79 Bool.false 12708267210600586209 28147497671065600 814200000787807707 1209481250000000000000 473419845 1048576 707 1048576 (ep512 rfl) rfl) (Enclosure.sfrac_false_div 473419845 1048576) (BSN.sin_reduce3 qz395 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 101217505165714527354880) qz19) 226375608064910080 72057594037927936 Bool.false 822025 1048576 71 1000000000000000 387034 193517 (BSN.sin_reduce_arg_pos_rat_q3 473419845 1048576 226375608064910080 72057594037927936 71 101217505165714527354880 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 822025 1048576 101217505165714527354880 151115727451828646838272 1438387260 2147483648 387412 387034 (ep519 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz396 := (@Enclosure.Real.IsNear.recentre' qz78 Bool.false 185363 1048576 1 1048576 185363 1048576 1 1048576 (ep510 rfl rfl) rfl)

noncomputable def ep521 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz78 (Real.cos qz79)) (@HMul.hMul Real Real Real qz0 qz78 (@Neg.neg Real Real.instNeg (Real.sin qz79))) Bool.false 120668903281 1099511627776 25681202520859 212774191672328192 Bool.false 152373020075 1099511627776 25714301281505 212774191672328192 (@Enclosure.Real.IsNear.mulLit_ff qz78 (Real.cos qz79) 185363 1048576 1 1048576 650987 1048576 137865095 202917281792 120668903281 1099511627776 25681202520859 212774191672328192 qz396 (@Enclosure.Real.IsNear.recentre' (Real.cos qz79) Bool.false 650987 1048576 137865095 202917281792 650987 1048576 137865095 202917281792 (ep515 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz78 (@Neg.neg Real Real.instNeg (Real.sin qz79)) 185363 1048576 1 1048576 822025 1048576 137865095 202917281792 152373020075 1099511627776 25714301281505 212774191672328192 qz396 (@Enclosure.Real.IsNear.neg (Real.sin qz79) Bool.true 822025 1048576 137865095 202917281792 (@Enclosure.Real.IsNear.recentre' (Real.sin qz79) Bool.true 822025 1048576 137865095 202917281792 822025 1048576 137865095 202917281792 (ep520 rfl rfl) rfl)) rfl)

noncomputable def ep522 := @ep407 120668903281 1099511627776 25681202520859 212774191672328192 Bool.false 152373020075 1099511627776 25714301281505 212774191672328192 Bool.false ep408 596571813335 549755813888 162024248047477 26596773959041024 Bool.false 47571880253572088070144 10816593261 274877906944 648305631188839 106387095836164096 (ep409 (BSN.head_sum_c_succ qz5 31 32 rfl rfl) (ep508 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep509 ep521) rfl rfl

theorem EMRow44.d9 : Enclosure.Complex.IsNear (BSN.headSumC qz5 33) Bool.false 596571813335 549755813888 162024248047477 26596773959041024 Bool.false 10816593261 274877906944 648305631188839 106387095836164096 := ep406 (BSN.head_sum_c_succ qz5 32 33 rfl rfl) (ep522 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

theorem EMRow44.d10 : @Eq Nat (BSN.factNat (Nat.mul 2 1)) 2 := @Eq.refl Nat 2

theorem EMRow44.d11 : @Eq Nat (Nat.pow 33 1) 33 := @Eq.refl Nat 33

noncomputable def ep523 := nat_lit 40297100595218266164337937798693

noncomputable def ep524 := nat_lit 40355455727363408480585121792000

noncomputable def ep525 := nat_lit 29577608723948199970955382824415425774131

noncomputable def ep526 := nat_lit 4533793717241488830763821290465645297664000

noncomputable abbrev qz667 := (@instHMul Complex Complex.instMul)

noncomputable abbrev qz606 := qz667

noncomputable abbrev qz397 := qz606

noncomputable abbrev qz80 := qz397

noncomputable abbrev qz607 := (@instHSub Complex Complex.instSub)

noncomputable abbrev qz398 := qz607

noncomputable abbrev qz81 := qz398

noncomputable abbrev qz668 := (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (4 : Complex))

noncomputable abbrev qz669 := (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid))

noncomputable abbrev qz608 := (@HAdd.hAdd Complex Complex Complex qz665 (@HAdd.hAdd Complex Complex Complex qz665 qz668 (@HMul.hMul Complex Complex Complex qz667 Complex.I (@HDiv.hDiv Complex Complex Complex qz669 (↑qz666) (2 : Complex)))) (@Nat.cast Complex Complex.instNatCast 2))

noncomputable abbrev qz399 := qz608

noncomputable abbrev qz82 := (Complex.Stirling.logGammaStirling 1 qz399)

noncomputable abbrev qz609 := (@HAdd.hAdd Complex Complex Complex qz665 qz668 (@HMul.hMul Complex Complex Complex qz667 Complex.I (@HDiv.hDiv Complex Complex Complex qz669 (↑qz666) (2 : Complex))))

noncomputable abbrev qz400 := qz609

noncomputable abbrev qz83 := qz400

noncomputable abbrev qz84 := (@HMul.hMul Real Real Real qz268 (@HDiv.hDiv Real Real Real qz271 qz279 (2 : Real)) (Real.log Real.pi))

noncomputable abbrev qz401 := (@instHSub Real Real.instSub)

noncomputable def ep527 := Complex.re (@HMul.hMul Complex Complex Complex qz80 (Complex.exp (@HMul.hMul Complex Complex Complex qz80 Complex.I ↑(@HSub.hSub Real Real Real qz401 (Complex.im (@HSub.hSub Complex Complex Complex qz81 qz82 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz83 (@Nat.cast Complex Complex.instNatCast j))))) qz84))) (zetaApproximant qz5 1 33))

noncomputable def ep528 := @Enclosure.Real.IsNear.of_eq ep527 (@HSub.hSub Real Real Real qz401 (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz401 (Complex.im (@HSub.hSub Complex Complex Complex qz81 qz82 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz83 (@Nat.cast Complex Complex.instNatCast j))))) qz84)) (Complex.re (zetaApproximant qz5 1 33))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz401 (Complex.im (@HSub.hSub Complex Complex Complex qz81 qz82 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz83 (@Nat.cast Complex Complex.instNatCast j))))) qz84)) (Complex.im (zetaApproximant qz5 1 33))))

noncomputable def ep529 := nat_lit 146536549868351157296915172847

noncomputable def ep530 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz401 (Complex.im (@HSub.hSub Complex Complex Complex qz81 qz82 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz83 (@Nat.cast Complex Complex.instNatCast j))))) qz84)) (Complex.re (zetaApproximant qz5 1 33))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz401 (Complex.im (@HSub.hSub Complex Complex Complex qz81 qz82 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz83 (@Nat.cast Complex Complex.instNatCast j))))) qz84)) (Complex.im (zetaApproximant qz5 1 33))) ep529

noncomputable def ep531 := nat_lit 146747111735866939929400442880

noncomputable def ep532 := nat_lit 29517739334930223505964234117275476980987

noncomputable def ep533 := nat_lit 18775774095920513072280593

noncomputable def ep534 := nat_lit 1681477321973475353357713408000

noncomputable def ep535 := nat_lit 7483673627247058123893588392493599143

noncomputable def ep536 := nat_lit 566724214655186103845477661308205662208000

noncomputable def ep537 := nat_lit 246395130153248544878172095786262281617542265117423603548160

noncomputable def ep538 := @Enclosure.Real.IsNear.mulLit_ff (Real.cos (@HSub.hSub Real Real Real qz401 (Complex.im (@HSub.hSub Complex Complex Complex qz81 qz82 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz83 (@Nat.cast Complex Complex.instNatCast j))))) qz84)) (Complex.re (zetaApproximant qz5 1 33)) 1048575 1048576 8839337

noncomputable def ep539 := nat_lit 115292328771322704403552457

noncomputable def ep540 := nat_lit 115457884962167954866176000

noncomputable def ep541 := nat_lit 137643846251689708182059453353

noncomputable def ep542 := nat_lit 22343063524223856121837780992000

noncomputable def ep543 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HSub.hSub Real Real Real qz401 (Complex.im (@HSub.hSub Complex Complex Complex qz81 qz82 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz83 (@Nat.cast Complex Complex.instNatCast j))))) qz84)) Bool.false 1048575 1048576 8839337

noncomputable abbrev qz402 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 8647303) (@Nat.cast Real Real.instNatCast 65536))

noncomputable def ep544 := @Enclosure.Real.IsNear.cos_image (@HSub.hSub Real Real Real qz401 (Complex.im (@HSub.hSub Complex Complex Complex qz81 qz82 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz83 (@Nat.cast Complex Complex.instNatCast j))))) qz84) qz402 Bool.false 8647303 65536 45

noncomputable def ep545 := nat_lit 2170657542484533730208821

noncomputable def ep546 := nat_lit 6341165056000000000000000000

noncomputable def ep547 := @Enclosure.Real.IsNear.recentre' (@HSub.hSub Real Real Real qz401 (Complex.im (@HSub.hSub Complex Complex Complex qz81 qz82 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz83 (@Nat.cast Complex Complex.instNatCast j))))) qz84) Bool.false 37139883604264904367 281474976710656000 ep545 ep546

noncomputable def ep548 := @Enclosure.Real.IsNear.subLit_ff_p (Complex.im (@HSub.hSub Complex Complex Complex qz81 qz82 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz83 (@Nat.cast Complex Complex.instNatCast j))))) qz84 58127532735469741743 281474976710656000 595042128484533730208821 ep546 305410491 4096000

noncomputable def ep549 := nat_lit 152124963243069048287232000

noncomputable def ep550 := nat_lit 8880026509419874474289839

noncomputable def ep551 := nat_lit 50729320448000000000000000000

noncomputable def ep552 := @Enclosure.Complex.IsNear.im_isNear (@HSub.hSub Complex Complex Complex qz81 qz82 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz83 (@Nat.cast Complex Complex.instNatCast j)))) Bool.true 115337875166168076401 1125899906842624000 ep550 ep551 Bool.false 58127532735469741743 281474976710656000

noncomputable def ep553 := nat_lit 8748954508811122628913839

noncomputable def ep554 := @Enclosure.Complex.IsNear.subLitP qz82 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz83 (@Nat.cast Complex Complex.instNatCast j))) Bool.true 105933068802862375401 1125899906842624000 ep553 ep551 Bool.false 59005331348823632743 281474976710656000 562274128478192565152821

noncomputable def ep555 := nat_lit 129858902905014833324103927515316224

noncomputable def ep556 := nat_lit 16361445922964239809495107956113408

noncomputable abbrev qz670 := (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (2 : Complex))

noncomputable abbrev qz610 := qz670

noncomputable abbrev qz403 := (@HSub.hSub Complex Complex Complex qz607 qz608 qz610)

noncomputable abbrev qz404 := (Complex.log qz608)

noncomputable abbrev qz85 := (@HSub.hSub Complex Complex Complex qz398 (@HMul.hMul Complex Complex Complex qz397 qz403 qz404) qz399)

noncomputable abbrev qz405 := qz610

noncomputable abbrev qz86 := (@HMul.hMul Complex Complex Complex qz397 qz405 ↑(Real.log (@HMul.hMul Real Real Real qz268 (2 : Real) Real.pi)))

noncomputable abbrev qz611 := qz669

noncomputable abbrev qz406 := qz611

noncomputable abbrev qz87 := qz406

noncomputable abbrev qz88 := (@instHMul Nat instMulNat)

noncomputable abbrev qz612 := (@instHPow Complex Int (@ZPow.toPow Complex (@DivInvMonoid.toZPow Complex Complex.instDivInvMonoid)))

noncomputable abbrev qz407 := qz612

noncomputable abbrev qz89 := qz407

noncomputable abbrev qz90 := qz399

noncomputable abbrev qz91 := (@OfNat.ofNat Int 1 (@instOfNat 1))

noncomputable abbrev qz92 := (@OfNat.ofNat Int 2 (@instOfNat 2))

noncomputable abbrev qz408 := (@instHSub Int Int.instSub)

noncomputable abbrev qz409 := (@instHMul Int Int.instMul)

noncomputable def ep557 := @Enclosure.Complex.IsNear.of_eq qz82 (@HAdd.hAdd Complex Complex Complex qz4 (@HAdd.hAdd Complex Complex Complex qz4 qz85 qz86) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz80 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz89 qz90 (@HSub.hSub Int Int Int qz408 qz91 (@HMul.hMul Int Int Int qz409 qz92 (@Nat.cast Int instNatCastInt k)))))) Bool.true 105933068802862375401

noncomputable def ep558 := @Enclosure.Complex.IsNear.addLitP (@HAdd.hAdd Complex Complex Complex qz4 qz85 qz86) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz80 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz89 qz90 (@HSub.hSub Int Int Int qz408 qz91 (@HMul.hMul Int Int Int qz409 qz92 (@Nat.cast Int instNatCastInt k))))) Bool.true 105933118501088551401 1125899906842624000

noncomputable def ep559 := nat_lit 7279665057171388376578718171136

noncomputable def ep560 := nat_lit 63356492108210267675774943232000

noncomputable def ep561 := @ep558 66749208787420733437 387034000000000000000000 Bool.false 59005691031452543847 281474976710656000 17159000075798867247 193517000000000000000000 Bool.false 3033339 68719476736 3 68719476736 Bool.true 1372080341 1073741824000 1357 1073741824000 Bool.true ep559 105933068802862375401 1125899906842624000 ep553 ep551 Bool.false ep560

noncomputable def ep562 := @Enclosure.Complex.IsNear.addLitP qz85 qz86 Bool.true 106967750352891175401 1125899906842624000 8251375002083597539 48379250000000000000000

noncomputable def ep563 := nat_lit 13884865708174678609231872

noncomputable def ep564 := @ep562 Bool.false 59005691031452543847 281474976710656000 17159000075798867247 193517000000000000000000 Bool.false 120447 131072 1 524288 Bool.false 0 1 0 1 Bool.true ep563 105933118501088551401 1125899906842624000 66749208787420733437 387034000000000000000000 Bool.false 59005691031452543847 59005691031452543847 281474976710656000

noncomputable abbrev qz93 := (@HMul.hMul Complex Complex Complex qz397 qz403 qz404)

noncomputable def ep565 := @Enclosure.Complex.IsNear.subLitP qz93 qz90 Bool.true 104434475562495271401 1125899906842624000 8251375002083597539 48379250000000000000000 Bool.false 77339845114477833063

noncomputable def ep566 := @ep565 281474976710656000 17159000075798867247 193517000000000000000000 Bool.false 9000 4000 0 1 Bool.false 260544 4000 0 1 Bool.true 427871001411564701604000 106967750352891175401 1125899906842624000 8251375002083597539 48379250000000000000000 Bool.false 236022764125810175388000 59005691031452543847 281474976710656000 17159000075798867247 193517000000000000000000

noncomputable abbrev qz94 := qz403

noncomputable abbrev qz95 := qz404

noncomputable def ep567 := @Enclosure.Complex.IsNear.mul qz94 qz95 Bool.true 104434475562495271401 1125899906842624000 8251375002083597539 48379250000000000000000 Bool.false 77339845114477833063 281474976710656000 17159000075798867247

noncomputable abbrev qz96 := (Complex.re qz403)

noncomputable abbrev qz97 := (Complex.re qz404)

noncomputable abbrev qz98 := (Complex.im qz403)

noncomputable abbrev qz99 := (Complex.im qz404)

noncomputable def ep568 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 qz96 qz97) (@HMul.hMul Real Real Real qz0 qz98 qz99) 65841532787449923 9007199254740992 875000004063857 387034000000000000000 3520770848778953493 35184372088832000

noncomputable def ep569 := nat_lit 29395691576742929683050600968749056

noncomputable def ep570 := @Enclosure.Real.IsNear.mulLit_ff qz96 qz97 7000 4000 0 1 9405933255349989 2251799813685248 125000000580551 96758500000000000000

noncomputable def ep571 := @Enclosure.Complex.IsNear.re_isNear qz94 Bool.false 7000 4000 0 1 Bool.false 260544 4000 0 1

noncomputable abbrev qz613 := (Enclosure.sfrac Bool.false 260544 4000)

noncomputable abbrev qz410 := qz613

noncomputable def ep572 := @Enclosure.Complex.IsNear.of_eq qz94 (Complex.mk (Enclosure.sfrac Bool.false 7000 4000) qz410) Bool.false 7000 4000 0 1 Bool.false 260544 4000 0

noncomputable abbrev qz614 := (Enclosure.sfrac Bool.false 9000 4000)

noncomputable abbrev qz411 := (Complex.log (Complex.mk qz614 qz613))

noncomputable def ep573 := @Enclosure.Complex.IsNear.of_eq qz95 qz411 Bool.false 9405933255349989 2251799813685248 125000000580551 96758500000000000000 Bool.false 864841770763683 562949953421312 1000000000193517 387034000000000000000

noncomputable def ep574 := BSN.log_dyadic_bound 2428175936 133500175936 2 1 53466890924828860428288 1048576 387034 5896038376169476096 5896038376169476096 38148 135928351872 131072000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 2428175936) (BSN.artanhQ 133500175936) 0 1 5896038376169476096 53466890924828860428288 5896038376169476096 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz100 := (Enclosure.sfrac Bool.false 1 2)

noncomputable abbrev qz412 := (Enclosure.Real.IsNear.const Bool.false 1 2)

noncomputable abbrev qz615 := (Real.log (Enclosure.sfrac Bool.false 67964175936 16000000))

noncomputable abbrev qz616 := (@Nat.cast Real Real.instNatCast 16000000)

noncomputable def ep575 := @Enclosure.Real.IsNear.mulLit_ff qz100 qz615 1 2 0 1 9405933255349989 1125899906842624 125000000580551 48379250000000000000 9405933255349989 2251799813685248 125000000580551 96758500000000000000 qz412 (BSN.isNear_log_sfrac 67964175936 16000000 9405933255349989 1125899906842624 125000000580551 48379250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 67964175936) qz616)) Bool.false 315610747813179842101248 37778931862957161709568 1000000004644408 387034000000000000000 9405933255349989 1125899906842624 125000000580551 48379250000000000000 (BSN.log_rat_reduce_isNear 67964175936 16000000 12 135928351872 131072000000 38148 1048576 24973259072661432 36028797018963968 387034 1000000000000000 rfl rfl rfl rfl (ep574 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep576 := BSN.arctan_dyadic_bound_f 9000 260544 1 0 1048576 387034 0 1 1 0 1 1 36206 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 9000) (BSN.arctanEvenQ 260544) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 9000) (BSN.arctanOddQ 260544) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz101 := (@HMul.hMul Real Real Real qz268 (Enclosure.sfrac Bool.false 1 2) Real.pi)

noncomputable abbrev qz102 := (@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 2) Real.pi 1 2 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 qz412 BSN.pi_near_15 rfl)

noncomputable abbrev qz413 := (Real.arctan (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 9000) (@Nat.cast Real Real.instNatCast 260544)))

noncomputable def ep577 := @Enclosure.Real.IsNear.subLit_ff_p qz101 qz413 884279719003555 562949953421312 1 2000000000000000 36206 1048576 1 387034 906852324620299665408 864841770763683 562949953421312 1000000000193517 387034000000000000000 qz102 (ep576 rfl) rfl rfl

noncomputable abbrev qz414 := (Complex.mk qz614 qz613)

noncomputable abbrev qz415 := (Real.arctan (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 260544) (@Nat.cast Real Real.instNatCast 9000)))

noncomputable def ep578 := @Enclosure.Complex.IsNear.re_isNear qz95 Bool.false 9405933255349989 2251799813685248 125000000580551 96758500000000000000 Bool.false 864841770763683 562949953421312 1000000000193517 387034000000000000000 (ep573 (@congrArg Complex Complex qz90 qz414 Complex.log (BSN.w_shift_mk qz12 Bool.false 130272 1000 2 qz13 rfl)) (@Enclosure.Complex.IsNear.of_parts qz411 Bool.false 9405933255349989 2251799813685248 125000000580551 96758500000000000000 Bool.false 864841770763683 562949953421312 1000000000193517 387034000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz411) (@HMul.hMul Real Real Real qz0 qz100 qz615) Bool.false 9405933255349989 2251799813685248 125000000580551 96758500000000000000 (Enclosure.clog_re_eq 9000 260544 4000 67964175936 16000000 rfl rfl rfl) (ep575 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz411) qz415 Bool.false 864841770763683 562949953421312 1000000000193517 387034000000000000000 (Enclosure.clog_im_eq 9000 260544 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz415 (@HSub.hSub Real Real Real qz401 qz101 qz413) Bool.false 864841770763683 562949953421312 1000000000193517 387034000000000000000 (BSN.arctan_recip 260544 9000 rfl rfl) ep577))))

noncomputable def ep579 := @Enclosure.Real.IsNear.mulLit_ff qz98 qz99 260544 4000 0 1 864841770763683 562949953421312 1000000000193517 387034000000000000000

noncomputable def ep580 := @Enclosure.Complex.IsNear.im_isNear qz94 Bool.false 7000 4000 0 1 Bool.false 260544 4000 0 1

noncomputable def ep581 := @Enclosure.Complex.IsNear.im_isNear qz95 Bool.false 9405933255349989 2251799813685248 125000000580551 96758500000000000000 Bool.false 864841770763683 562949953421312 1000000000193517 387034000000000000000 (ep573 (@congrArg Complex Complex qz90 qz414 Complex.log (BSN.w_shift_mk qz12 Bool.false 130272 1000 2 qz13 rfl)) (@Enclosure.Complex.IsNear.of_parts qz411 Bool.false 9405933255349989 2251799813685248 125000000580551 96758500000000000000 Bool.false 864841770763683 562949953421312 1000000000193517 387034000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz411) (@HMul.hMul Real Real Real qz0 qz100 qz615) Bool.false 9405933255349989 2251799813685248 125000000580551 96758500000000000000 (Enclosure.clog_re_eq 9000 260544 4000 67964175936 16000000 rfl rfl rfl) (ep575 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz411) qz415 Bool.false 864841770763683 562949953421312 1000000000193517 387034000000000000000 (Enclosure.clog_im_eq 9000 260544 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz415 (@HSub.hSub Real Real Real qz401 qz101 qz413) Bool.false 864841770763683 562949953421312 1000000000193517 387034000000000000000 (BSN.arctan_recip 260544 9000 rfl rfl) ep577))))

noncomputable abbrev qz103 := (@ep572 1 (BSN.w_sub_half_mk qz279 Bool.false 130272 1000 2 qz281 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7000 4000) qz410 Bool.false 7000 4000 0 1 Bool.false 260544 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 7000 4000) (Enclosure.Real.IsNear.const Bool.false 260544 4000)))

noncomputable def ep582 := @ep568 4071000000787807707 24189625000000000000000 ep569 104434475562495271401 1125899906842624000 8251375002083597539 48379250000000000000000 (@ep570 65841532787449923 9007199254740992 875000004063857 387034000000000000000 (ep571 qz103) ep578 rfl) (@ep579 3520770848778953493 35184372088832000 4071000000787807707 24189625000000000000000 (ep580 qz103) ep581 rfl) rfl

noncomputable def ep583 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz96 qz99) (@HMul.hMul Real Real Real qz0 qz98 qz97) 6053892395345781 2251799813685248 7000000001354619 1548136000000000000000 38291554282529805219 140737488355328000

noncomputable def ep584 := nat_lit 87076924409613561134457161684877312

noncomputable def ep585 := @Enclosure.Real.IsNear.mulLit_ff qz96 qz99 7000 4000 0 1 864841770763683 562949953421312 1000000000193517 387034000000000000000

noncomputable def ep586 := @Enclosure.Real.IsNear.mulLit_ff qz98 qz97 260544 4000 0 1 9405933255349989 2251799813685248 125000000580551 96758500000000000000

noncomputable def ep587 := @ep583 508875002363423121 6047406250000000000000 ep584 77339845114477833063 281474976710656000 17159000075798867247 193517000000000000000000 (@ep585 6053892395345781 2251799813685248 7000000001354619 1548136000000000000000 (ep571 qz103) ep581 rfl) (@ep586 38291554282529805219 140737488355328000 508875002363423121 6047406250000000000000 (ep580 qz103) ep578 rfl) rfl

noncomputable def ep588 := @Enclosure.Complex.IsNear.of_eq qz90 qz414 Bool.false 9000 4000 0 1 Bool.false 260544 4000 0 1 (BSN.w_shift_mk qz12 Bool.false 130272 1000 2 qz13 rfl)

noncomputable abbrev qz416 := (ep588 (@Enclosure.Complex.IsNear.mk qz614 qz613 Bool.false 9000 4000 0 1 Bool.false 260544 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 9000 4000) (Enclosure.Real.IsNear.const Bool.false 260544 4000)))

noncomputable abbrev qz104 := qz416

noncomputable def ep589 := ep566 (@ep567 193517000000000000000000 (ep582 rfl) (ep587 rfl)) qz104 rfl rfl rfl rfl rfl rfl

noncomputable abbrev qz105 := qz405

noncomputable def ep590 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re qz105) (Complex.re ↑qz2)) (@HMul.hMul Real Real Real qz0 (Complex.im qz105) (Complex.im ↑qz2)) 120447 131072 1 524288 0 1 0 1 120447 120447

noncomputable def ep591 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re qz105) (Complex.re ↑qz2) 1 2 0 1 120447 65536 1 262144 120447 131072 1 524288

noncomputable abbrev qz106 := (@Enclosure.Complex.IsNear.of_eq qz405 (Complex.mk (Enclosure.sfrac Bool.false 1 2) qz278) Bool.false 1 2 0 1 Bool.false 0 1 0 1 BSN.half_c_mk (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 2) qz278 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz412 qz546))

noncomputable def ep592 := ep591 (@Enclosure.Complex.IsNear.re_isNear qz105 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz106) (@Enclosure.Real.IsNear.of_eq (Complex.re ↑qz2) qz2 Bool.false 120447 65536 1 262144 (Complex.ofReal_re qz2) EMRow44.d4)

noncomputable def ep593 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz105) (Complex.im ↑qz2) 0 1 0 1 0 1 0 1 0 1 0 1

noncomputable def ep594 := ep593 (@Enclosure.Complex.IsNear.im_isNear qz105 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz106) (@Enclosure.Real.IsNear.of_eq (Complex.im ↑qz2) qz10 Bool.false 0 1 0 1 (@Eq.trans Real (Complex.im ↑qz2) (0 : Real) qz10 (Complex.ofReal_im qz2) Enclosure.sfrac_zero_eq) qz22)

noncomputable def ep595 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re qz105) (Complex.im ↑qz2)) (@HMul.hMul Real Real Real qz0 (Complex.im qz105) (Complex.re ↑qz2)) 0 1 0 1 0 1 0 1 0 0

noncomputable def ep596 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re qz105) (Complex.im ↑qz2) 1 2 0 1 0 1 0 1 0 1 0 1

noncomputable def ep597 := ep596 (@Enclosure.Complex.IsNear.re_isNear qz105 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz106) (@Enclosure.Real.IsNear.of_eq (Complex.im ↑qz2) qz10 Bool.false 0 1 0 1 (@Eq.trans Real (Complex.im ↑qz2) (0 : Real) qz10 (Complex.ofReal_im qz2) Enclosure.sfrac_zero_eq) qz22)

noncomputable def ep598 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz105) (Complex.re ↑qz2) 0 1 0 1 120447 65536 1 262144 0 1 0 1

noncomputable def ep599 := ep598 (@Enclosure.Complex.IsNear.im_isNear qz105 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz106) (@Enclosure.Real.IsNear.of_eq (Complex.re ↑qz2) qz2 Bool.false 120447 65536 1 262144 (Complex.ofReal_re qz2) EMRow44.d4)

noncomputable def ep600 := @ep564 17159000075798867247 193517000000000000000000 (ep589 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@Enclosure.Complex.IsNear.mul qz105 (↑qz2) Bool.false 120447 131072 1 524288 Bool.false 0 1 0 1 (@ep590 131072 1 524288 (ep592 rfl) (ep594 rfl) rfl rfl) (@ep595 1 0 1 (ep597 rfl) (ep599 rfl) rfl rfl))

noncomputable abbrev qz107 := (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 1)

noncomputable abbrev qz417 := (@Nat.cast Complex Complex.instNatCast 1)

noncomputable abbrev qz108 := (@HMul.hMul Complex Complex Complex qz397 (@HMul.hMul Complex Complex Complex qz397 (2 : Complex) qz417) (@HSub.hSub Complex Complex Complex qz398 (@HMul.hMul Complex Complex Complex qz397 (2 : Complex) qz417) (1 : Complex)))

noncomputable abbrev qz418 := (@HPow.hPow Complex Int Complex qz612 qz608 (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) (@OfNat.ofNat Int 1 (@instOfNat 1)) (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (@OfNat.ofNat Int 2 (@instOfNat 2)) (@Nat.cast Int instNatCastInt 1))))

noncomputable abbrev qz109 := qz418

noncomputable def ep601 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz80 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz89 qz90 (@HSub.hSub Int Int Int qz408 qz91 (@HMul.hMul Int Int Int qz409 qz92 (@Nat.cast Int instNatCastInt k))))) (@HAdd.hAdd Complex Complex Complex qz4 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz80 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz89 qz90 (@HSub.hSub Int Int Int qz408 qz91 (@HMul.hMul Int Int Int qz409 qz92 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli qz107)) qz108) qz109)) Bool.false 3033339 68719476736 3 68719476736

noncomputable def ep602 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz80 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz89 qz90 (@HSub.hSub Int Int Int qz408 qz91 (@HMul.hMul Int Int Int qz409 qz92 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli qz107)) qz108) qz109) Bool.false 0 1 0 1 Bool.false

noncomputable def ep603 := @ep602 0 1 0 1 Bool.false 3033339 68719476736 3 68719476736 Bool.true 1372080341 1073741824000 1357 1073741824000 Bool.false 3033339 3033339 68719476736 3 68719476736 Bool.true 1372080341 1372080341 1073741824000 1357

noncomputable def ep604 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz80 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz89 qz90 (@HSub.hSub Int Int Int qz408 qz91 (@HMul.hMul Int Int Int qz409 qz92 (@Nat.cast Int instNatCastInt k))))) (Complex.mk qz10 qz10) Bool.false 0 1 0 1 Bool.false

noncomputable def ep605 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli qz107)) qz108) qz109 Bool.false 3033339 68719476736 3 68719476736 Bool.true 1372080341 1073741824000 1357 1073741824000

noncomputable abbrev qz110 := (Complex.re qz418)

noncomputable abbrev qz111 := (Complex.im qz418)

noncomputable def ep606 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli qz107)) qz108)) qz110) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli qz107)) qz108)) qz111) 3033339 68719476736 3 68719476736 0 1 0

noncomputable def ep607 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli qz107)) qz108)) qz110 1 12 0 1 9100017 17179869184 9 17179869184 3033339

noncomputable def ep608 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli qz107)) qz108) (Complex.mk (Enclosure.sfrac Bool.false 1 12) qz10) Bool.false 1 12 0 1 Bool.false 0 1 0 1

noncomputable abbrev qz419 := (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 12) qz10 Bool.false 1 12 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 12) qz22)

noncomputable def ep609 := @Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli qz107)) qz108) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (ep608 (BSN.stirling_coeff_mk 1 1 6 Bool.false BSN.bern_real_1 rfl rfl) qz419)

noncomputable def ep610 := @Enclosure.Complex.IsNear.re_isNear qz109 Bool.false 9100017 17179869184 9 17179869184 Bool.true 4116241023 268435456000 4071 268435456000

noncomputable abbrev qz617 := (@instHPow Complex Nat (@NPow.toPow Complex (@Monoid.toNPow Complex (@Semiring.toMonoid Complex Complex.instSemiring))))

noncomputable abbrev qz420 := (@HPow.hPow Complex Nat Complex qz617 qz608 1)

noncomputable abbrev qz112 := (@Inv.inv Complex Complex.instInv qz420)

noncomputable def ep611 := @Enclosure.Complex.IsNear.of_eq qz109 qz112 Bool.false 9100017 17179869184 9 17179869184 Bool.true 4116241023 268435456000 4071

noncomputable def ep612 := @Enclosure.Complex.IsNear.of_parts qz112 Bool.false 9100017 17179869184 9 17179869184 Bool.true 4116241023 268435456000 4071

noncomputable abbrev qz113 := (Complex.re qz420)

noncomputable abbrev qz114 := (@MonoidWithZeroHom Complex Real (@instMulZeroOneClassOfSemiring Complex Complex.instSemiring) (@instMulZeroOneClassOfSemiring Real Real.semiring))

noncomputable abbrev qz115 := (@MonoidWithZeroHom.funLike Complex Real (@instMulZeroOneClassOfSemiring Complex Complex.instSemiring) (@instMulZeroOneClassOfSemiring Real Real.semiring))

noncomputable abbrev qz116 := qz420

noncomputable def ep613 := @Enclosure.Real.IsNear.mulLit_ff qz113 (@Inv.inv Real Real.instInv (@DFunLike.coe qz114 Complex (fun (x : Complex) => Real) qz115 Complex.normSq qz116)) 9000 4000 0 1 1011113 4294967296 1 4294967296

noncomputable def ep614 := @Enclosure.Complex.IsNear.re_isNear qz116 Bool.false 9000 4000 0 1 Bool.false 260544 4000 0 1

noncomputable def ep615 := @Enclosure.Complex.IsNear.of_eq qz116 qz90 Bool.false 9000 4000 0 1 Bool.false 260544 4000 0

noncomputable def ep616 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (@DFunLike.coe qz114 Complex (fun (x : Complex) => Real) qz115 Complex.normSq qz116)) Bool.false 1011113 4294967296 1 4294967296 1011113 4294967296 1

noncomputable abbrev qz117 := (Complex.im qz420)

noncomputable abbrev qz421 := (@instHAdd Real Real.instAdd)

noncomputable def ep617 := @Enclosure.Real.IsNear.of_eq (@DFunLike.coe qz114 Complex (fun (x : Complex) => Real) qz115 Complex.normSq qz116) (@HAdd.hAdd Real Real Real qz421 (@HMul.hMul Real Real Real qz0 qz113 qz113) (@HMul.hMul Real Real Real qz0 qz117 qz117)) Bool.false 1061940249 250000 0 1

noncomputable def ep618 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz113 qz113) (@HMul.hMul Real Real Real qz0 qz117 qz117) 81 16 0 1 66292164 15625

noncomputable def ep619 := @Enclosure.Real.IsNear.mulLit_ff qz113 qz113 9000 4000 0 1 9000 4000 0 1

noncomputable def ep620 := @Enclosure.Real.IsNear.mulLit_ff qz117 qz117 260544 4000 0 1 260544 4000 0 1

noncomputable def ep621 := @Enclosure.Complex.IsNear.im_isNear qz116 Bool.false 9000 4000 0 1 Bool.false 260544 4000 0 1

noncomputable abbrev qz118 := (ep614 (@ep615 1 (BSN.pow_one_c qz399) qz416))

noncomputable abbrev qz119 := (ep621 (@ep615 1 (BSN.pow_one_c qz399) qz416))

noncomputable def ep622 := @ep618 0 1 1061940249 1061940249 250000 0 1 (@ep619 81 16 0 1 qz118 qz118 rfl) (@ep620 66292164 15625 0 1 qz119 qz119 rfl)

noncomputable def ep623 := @Enclosure.Real.IsNear.inv_image (@DFunLike.coe qz114 Complex (fun (x : Complex) => Real) qz115 Complex.normSq qz116) 1061940249 250000 0 1 505556 505557 2147483648 (ep617 (Enclosure.Complex.normSq_eq_mul_add_mul qz116) (ep622 rfl rfl)) rfl

noncomputable def ep624 := @Enclosure.Real.IsNear.of_eq (Complex.re qz112) (@HMul.hMul Real Real Real qz0 qz113 (@Inv.inv Real Real.instInv (@DFunLike.coe qz114 Complex (fun (x : Complex) => Real) qz115 Complex.normSq qz116))) Bool.false 9100017 17179869184 9 17179869184 (Enclosure.Complex.inv_re_eq_mul qz116) (@ep613 9100017 17179869184 9 17179869184 qz118 (@ep616 4294967296 (ep623 rfl rfl rfl rfl rfl) rfl) rfl)

noncomputable def ep625 := @Enclosure.Real.IsNear.of_eq (Complex.im qz112) (@HMul.hMul Real Real Real qz0 (@Neg.neg Real Real.instNeg qz117) (@Inv.inv Real Real.instInv (@DFunLike.coe qz114 Complex (fun (x : Complex) => Real) qz115 Complex.normSq qz116))) Bool.true 4116241023 268435456000 4071 268435456000 (Enclosure.Complex.inv_im_eq_mul qz116)

noncomputable def ep626 := @Enclosure.Real.IsNear.mulLit_tf (@Neg.neg Real Real.instNeg qz117) (@Inv.inv Real Real.instInv (@DFunLike.coe qz114 Complex (fun (x : Complex) => Real) qz115 Complex.normSq qz116)) 260544 4000 0 1 1011113 4294967296 1

noncomputable def ep627 := @ep626 4294967296 4116241023 268435456000 4071 268435456000 (@Enclosure.Real.IsNear.neg qz117 Bool.false 260544 4000 0 1 qz119) (@ep616 4294967296 (ep623 rfl rfl rfl rfl rfl) rfl) rfl

noncomputable def ep628 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli qz107)) qz108)) qz111 0 1 0 1 4116241023 268435456000 4071 268435456000 0

noncomputable def ep629 := @Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli qz107)) qz108) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (ep608 (BSN.stirling_coeff_mk 1 1 6 Bool.false BSN.bern_real_1 rfl rfl) qz419)

noncomputable def ep630 := @Enclosure.Complex.IsNear.im_isNear qz109 Bool.false 9100017 17179869184 9 17179869184 Bool.true 4116241023 268435456000 4071 268435456000

noncomputable abbrev qz120 := (@ep611 268435456000 (BSN.zpow_one_sub_two_mul qz399 1 1 rfl rfl) (@ep612 268435456000 ep624 (ep625 ep627)))

noncomputable def ep631 := @ep606 1 3033339 3033339 68719476736 3 68719476736 (@ep607 68719476736 3 68719476736 ep609 (ep610 qz120) rfl) (@ep628 1 0 1 ep629 (ep630 qz120) rfl) rfl

noncomputable def ep632 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli qz107)) qz108)) qz111) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli qz107)) qz108)) qz110) 1372080341 1073741824000 1357 1073741824000 0 1 0

noncomputable def ep633 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli qz107)) qz108)) qz111 1 12 0 1 4116241023 268435456000 4071 268435456000 1372080341

noncomputable def ep634 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli qz107)) qz108)) qz110 0 1 0 1 9100017 17179869184 9 17179869184 0

noncomputable def ep635 := @ep632 1 1372080341 1372080341 1073741824000 1357 1073741824000 (@ep633 1073741824000 1357 1073741824000 ep609 (ep630 qz120) rfl) (@ep634 1 0 1 ep629 (ep610 qz120) rfl) rfl

noncomputable abbrev qz121 := (@Enclosure.Complex.IsNear.mk qz278 qz278 Bool.false 0 1 0 1 Bool.false 0 1 0 1 qz546 qz546)

noncomputable def ep636 := @ep603 1073741824000 (@ep604 0 1 0 1 (BSN.stirling_sum_base qz90) qz121) (ep605 (ep631 rfl) (ep635 rfl)) rfl rfl rfl rfl rfl

noncomputable def ep637 := @ep561 59005331348823632743 281474976710656000 562274128478192565152821 ep546 (ep600 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep601 Bool.true 1372080341 1073741824000 1357 1073741824000 (BSN.stirling_sum_succ qz90 0 1 rfl) (ep636 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl

noncomputable def ep638 := @Enclosure.Complex.IsNear.of_eq (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz83 (@Nat.cast Complex Complex.instNatCast j))) (BSN.logSumC qz12 2) Bool.false 9404806363305701 1125899906842624 125000000580551 48379250000000000000 Bool.false 877798613353891 281474976710656

noncomputable abbrev qz122 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz273 qz400 qz417))

noncomputable def ep639 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz12 2) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.logSumC qz12 1) qz122) Bool.false 9404806363305701 1125899906842624 125000000580551 48379250000000000000 Bool.false 877798613353891 281474976710656 1000000000193517 193517000000000000000

noncomputable def ep640 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz12 1) qz122 Bool.false 9404607184197349 2251799813685248 125000000580551 96758500000000000000 Bool.false 882119350453667 562949953421312 1000000000193517 387034000000000000000 Bool.false

noncomputable def ep641 := nat_lit 42355482433275224648952835997696

noncomputable def ep642 := nat_lit 988313377001730400412955049984

noncomputable abbrev qz123 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz273 qz400 (@Nat.cast Complex Complex.instNatCast 0)))

noncomputable def ep643 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz12 1) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.logSumC qz12 0) qz123) Bool.false 9404607184197349 2251799813685248 125000000580551 96758500000000000000 Bool.false 882119350453667 562949953421312 1000000000193517 387034000000000000000

noncomputable def ep644 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz12 0) qz123 Bool.false 0 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable abbrev qz422 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz613))

noncomputable def ep645 := @Enclosure.Complex.IsNear.of_eq qz123 qz422 Bool.false 9404607184197349 2251799813685248 125000000580551 96758500000000000000 Bool.false 882119350453667 562949953421312 1000000000193517 387034000000000000000

noncomputable def ep646 := BSN.log_dyadic_bound 2348175936 133420175936 2 1 53402830040379580428288 1048576 387034 5513930226409476096 5513930226409476096 36913 135768351872 131072000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 2348175936) (BSN.artanhQ 133420175936) 0 1 5513930226409476096 53402830040379580428288 5513930226409476096 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep647 := @Enclosure.Real.IsNear.mulLit_ff qz100 (Real.log (Enclosure.sfrac Bool.false 67884175936 16000000)) 1 2 0 1 9404607184197349 1125899906842624 125000000580551 48379250000000000000 9404607184197349 2251799813685248 125000000580551 96758500000000000000 qz412 (BSN.isNear_log_sfrac 67884175936 16000000 9404607184197349 1125899906842624 125000000580551 48379250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 67884175936) qz616)) Bool.false 315566252248861421600768 37778931862957161709568 1000000004644408 387034000000000000000 9404607184197349 1125899906842624 125000000580551 48379250000000000000 (BSN.log_rat_reduce_isNear 67884175936 16000000 12 135768351872 131072000000 36913 1048576 24973259072661432 36028797018963968 387034 1000000000000000 rfl rfl rfl rfl (ep646 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep648 := BSN.arctan_dyadic_bound_f 1000 260544 1 0 1048576 387034 0 1 1 0 1 1 4024 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 260544) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 260544) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz423 := (@Nat.cast Real Real.instNatCast 1000)

noncomputable abbrev qz424 := (@Nat.cast Real Real.instNatCast 260544)

noncomputable def ep649 := @Enclosure.Real.IsNear.subLit_ff_p qz101 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz423 qz424)) 884279719003555 562949953421312 1 2000000000000000 4024 1048576 1 387034 924969180021304328192 882119350453667 562949953421312 1000000000193517 387034000000000000000 qz102 (ep648 rfl) rfl rfl

noncomputable abbrev qz124 := (@HAdd.hAdd Complex Complex Complex qz273 qz400 (@Nat.cast Complex Complex.instNatCast 0))

noncomputable abbrev qz425 := (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz613)

noncomputable def ep650 := @ep644 9404607184197349 2251799813685248 125000000580551 96758500000000000000 Bool.false 882119350453667 562949953421312 1000000000193517 387034000000000000000 Bool.false 9404607184197349 9404607184197349 2251799813685248 125000000580551 96758500000000000000 Bool.false 882119350453667 882119350453667 562949953421312 1000000000193517 387034000000000000000 (@Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz12 0) (Complex.mk qz10 qz10) Bool.false 0 1 0 1 Bool.false 0 1 0 1 (BSN.log_sum_c_base qz12) qz121) (ep645 (@congrArg Complex Complex qz124 qz425 Complex.log (BSN.w_shift_mk qz12 Bool.false 130272 1000 0 qz13 rfl)) (@Enclosure.Complex.IsNear.of_parts qz422 Bool.false 9404607184197349 2251799813685248 125000000580551 96758500000000000000 Bool.false 882119350453667 562949953421312 1000000000193517 387034000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz422) (@HMul.hMul Real Real Real qz0 qz100 (Real.log (Enclosure.sfrac Bool.false 67884175936 16000000))) Bool.false 9404607184197349 2251799813685248 125000000580551 96758500000000000000 (Enclosure.clog_re_eq 1000 260544 4000 67884175936 16000000 rfl rfl rfl) (ep647 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz422) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz424 qz423)) Bool.false 882119350453667 562949953421312 1000000000193517 387034000000000000000 (Enclosure.clog_im_eq 1000 260544 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz424 qz423)) (@HSub.hSub Real Real Real qz401 qz101 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz423 qz424))) Bool.false 882119350453667 562949953421312 1000000000193517 387034000000000000000 (BSN.arctan_recip 260544 1000 rfl rfl) ep649)))) rfl rfl

noncomputable abbrev qz426 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz613))

noncomputable def ep651 := @Enclosure.Complex.IsNear.of_eq qz122 qz426 Bool.false 9405005542414053 2251799813685248 125000000580551 96758500000000000000 Bool.false 873477876254115 562949953421312 1000000000193517 387034000000000000000

noncomputable def ep652 := BSN.log_dyadic_bound 2372175936 133444175936 2 1 53422044273714364428288 1048576 387034 5627218671337476096 5627218671337476096 37284 135816351872 131072000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 2372175936) (BSN.artanhQ 133444175936) 0 1 5627218671337476096 53422044273714364428288 5627218671337476096 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep653 := @Enclosure.Real.IsNear.mulLit_ff qz100 (Real.log (Enclosure.sfrac Bool.false 67908175936 16000000)) 1 2 0 1 9405005542414053 1125899906842624 125000000580551 48379250000000000000 9405005542414053 2251799813685248 125000000580551 96758500000000000000 qz412 (BSN.isNear_log_sfrac 67908175936 16000000 9405005542414053 1125899906842624 125000000580551 48379250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 67908175936) qz616)) Bool.false 315579618932555457232896 37778931862957161709568 1000000004644408 387034000000000000000 9405005542414053 1125899906842624 125000000580551 48379250000000000000 (BSN.log_rat_reduce_isNear 67908175936 16000000 12 135816351872 131072000000 37284 1048576 24973259072661432 36028797018963968 387034 1000000000000000 rfl rfl rfl rfl (ep652 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep654 := BSN.arctan_dyadic_bound_f 5000 260544 1 0 1048576 387034 0 1 1 0 1 1 20120 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 5000) (BSN.arctanEvenQ 260544) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 5000) (BSN.arctanOddQ 260544) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz427 := (@Nat.cast Real Real.instNatCast 5000)

noncomputable def ep655 := @Enclosure.Real.IsNear.subLit_ff_p qz101 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz427 qz424)) 884279719003555 562949953421312 1 2000000000000000 20120 1048576 1 387034 915907937571034890240 873477876254115 562949953421312 1000000000193517 387034000000000000000 qz102 (ep654 rfl) rfl rfl

noncomputable abbrev qz125 := (@HAdd.hAdd Complex Complex Complex qz273 qz400 qz417)

noncomputable abbrev qz428 := (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz613)

noncomputable def ep656 := @ep640 9405005542414053 2251799813685248 125000000580551 96758500000000000000 Bool.false 873477876254115 562949953421312 1000000000193517 387034000000000000000 Bool.false ep641 9404806363305701 1125899906842624 125000000580551 48379250000000000000 Bool.false ep642 877798613353891 281474976710656 1000000000193517 193517000000000000000 (ep643 (BSN.log_sum_c_succ qz12 0 1 rfl) (ep650 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep651 (@congrArg Complex Complex qz125 qz428 Complex.log (BSN.w_shift_mk qz12 Bool.false 130272 1000 1 qz13 rfl)) (@Enclosure.Complex.IsNear.of_parts qz426 Bool.false 9405005542414053 2251799813685248 125000000580551 96758500000000000000 Bool.false 873477876254115 562949953421312 1000000000193517 387034000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz426) (@HMul.hMul Real Real Real qz0 qz100 (Real.log (Enclosure.sfrac Bool.false 67908175936 16000000))) Bool.false 9405005542414053 2251799813685248 125000000580551 96758500000000000000 (Enclosure.clog_re_eq 5000 260544 4000 67908175936 16000000 rfl rfl rfl) (ep653 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz426) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz424 qz427)) Bool.false 873477876254115 562949953421312 1000000000193517 387034000000000000000 (Enclosure.clog_im_eq 5000 260544 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz424 qz427)) (@HSub.hSub Real Real Real qz401 qz101 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz427 qz424))) Bool.false 873477876254115 562949953421312 1000000000193517 387034000000000000000 (BSN.arctan_recip 260544 5000 rfl rfl) ep655)))) rfl rfl

noncomputable def ep657 := @ep554 ep546 Bool.false 9404806363305701 1125899906842624 125000000580551 48379250000000000000 Bool.false 877798613353891 281474976710656 1000000000193517 193517000000000000000 Bool.true ep555 115337875166168076401 1125899906842624000 ep550 ep551 Bool.false ep556 58127532735469741743 281474976710656000 595042128484533730208821 ep546 (@ep557 1125899906842624000 ep553 ep551 Bool.false 59005331348823632743 281474976710656000 562274128478192565152821 ep546 (BSN.logGammaStirling_unfold 1 qz90) (ep637 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (@ep638 1000000000193517 193517000000000000000 (BSN.log_sum_c_eq qz12 2) (ep639 (BSN.log_sum_c_succ qz12 1 2 rfl) (ep656 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)))

noncomputable abbrev qz126 := (@HDiv.hDiv Real Real Real qz271 qz279 (2 : Real))

noncomputable def ep658 := @Enclosure.Real.IsNear.mulLit_ff qz126 (Real.log Real.pi) 130272 2000 0 1 75021 65536 1 262144 305410491 4096000 4071 16384000 (@Enclosure.Real.IsNear.of_eq qz126 (Enclosure.sfrac Bool.false 130272 2000) Bool.false 130272 2000 0 1 (BSN.t_half_eq qz12 Bool.false 130272 1000 qz13) (Enclosure.Real.IsNear.const Bool.false 130272 2000)) EMRow44.d5 rfl

noncomputable def ep659 := @ep548 4071 16384000 ep549 37139883604264904367 281474976710656000 ep545 ep546 (@ep552 595042128484533730208821 ep546 (ep657 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) ep658 rfl rfl

noncomputable def ep660 := BSN.cos_dyadic_bound_f 1032909 2147483648 1 0 1048576 387412 0 1 1 0 1 1 1048575 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 1032909) qz20 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 1032909) qz21 0 0 rfl) rfl rfl

noncomputable def ep661 := @ep544 131072 Bool.false 1048575 1048576 1 193517 (@ep547 8647303 65536 45 131072 ep659 rfl) (Enclosure.sfrac_false_div 8647303 65536) (BSN.cos_reduce0 qz402 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 4542781989161271296) qz377) 226375608064910080 72057594037927936 Bool.false 1048575 1048576 21 1000000000000000 387034 193517 (BSN.sin_reduce_arg_pos_rat_q0 8647303 65536 226375608064910080 72057594037927936 21 4542781989161271296 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1048575 1048576 4542781989161271296 9444732965739290427392 1032909 2147483648 387412 387034 (ep660 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep662 := nat_lit 2682253442274359010325799

noncomputable def ep663 := nat_lit 137678928219299219901857733259

noncomputable abbrev qz429 := (@HPow.hPow Complex Complex Complex qz536 (@Nat.cast Complex Complex.instNatCast 33) qz537)

noncomputable abbrev qz127 := qz429

noncomputable abbrev qz430 := (@Nat.cast Complex Complex.instNatCast 33)

noncomputable abbrev qz128 := (@HAdd.hAdd Complex Complex Complex qz273 (@HDiv.hDiv Complex Complex Complex qz406 qz430 (@HSub.hSub Complex Complex Complex qz398 qz272 (1 : Complex))) qz405)

noncomputable abbrev qz129 := (@instHSub Nat instSubNat)

noncomputable abbrev qz431 := qz617

noncomputable abbrev qz130 := qz431

noncomputable abbrev qz131 := qz430

noncomputable def ep664 := @Enclosure.Complex.IsNear.of_eq (zetaApproximant qz5 1 33) (@HAdd.hAdd Complex Complex Complex qz4 (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 33, @HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast n) qz7) (@HMul.hMul Complex Complex Complex qz80 qz127 (@HAdd.hAdd Complex Complex Complex qz4 qz128 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz131 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1))))))) Bool.false ep539 ep540 ep541

noncomputable def ep665 := @Enclosure.Complex.IsNear.addLitP (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 33, @HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast n) qz7) (@HMul.hMul Complex Complex Complex qz80 qz127 (@HAdd.hAdd Complex Complex Complex qz4 qz128 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz131 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))))) Bool.false 596571813335 549755813888 162024248047477 26596773959041024

noncomputable def ep666 := nat_lit 9997696464748464338617543

noncomputable def ep667 := nat_lit 1532674567320922964255237353

noncomputable def ep668 := nat_lit 1861076337464998537318201

noncomputable def ep669 := nat_lit 1523938867288442525537355259

noncomputable def ep670 := nat_lit 63382628038721392393668222596537122816

noncomputable def ep671 := nat_lit 737292212105714931757582912644448256

noncomputable def ep672 := @ep665 Bool.false 10816593261 274877906944 648305631188839 106387095836164096 Bool.true ep666 ep540 ep667 ep542 Bool.true ep668 ep540 ep669 ep542 Bool.false ep670 ep539 ep540 ep541 ep542 Bool.false ep671 ep662 ep540

noncomputable def ep673 := @Enclosure.Complex.IsNear.of_eq (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 33, @HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast n) qz7) (BSN.headSumC qz5 33) Bool.false 596571813335 549755813888 162024248047477 26596773959041024 Bool.false 10816593261 274877906944 648305631188839

noncomputable def ep674 := @Enclosure.Complex.IsNear.mul qz127 (@HAdd.hAdd Complex Complex Complex qz4 qz128 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz131 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1))))) Bool.true ep666 ep540 ep667 ep542 Bool.true

noncomputable def ep675 := nat_lit 10661538304180445504776661

noncomputable abbrev qz132 := (Complex.re qz429)

noncomputable abbrev qz133 := (Complex.im qz429)

noncomputable def ep676 := @Enclosure.Real.IsNear.subLit_tt_n (@HMul.hMul Real Real Real qz0 qz132 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz128 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz131 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz133 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz128 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz131 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1))))))) 80394542503132946787179 923663079697343638929408 ep675

noncomputable def ep677 := nat_lit 178744508193790848974702247936

noncomputable def ep678 := nat_lit 4810745206756998119424000

noncomputable def ep679 := nat_lit 8332594970765303173256447

noncomputable def ep680 := nat_lit 930960980175994005076574208000

noncomputable def ep681 := nat_lit 384770962771200481882022930146194127927803641856

noncomputable def ep682 := @Enclosure.Real.IsNear.mulLit_tf qz132 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz128 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz131 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))))) 191289290543 1099511627776 25367867454737 212774191672328192 420277278853

noncomputable abbrev qz432 := (@Nat.cast Real Real.instNatCast 33)

noncomputable abbrev qz134 := (@Inv.inv Real Real.instInv (Real.sqrt qz432))

noncomputable abbrev qz618 := (Real.log (Enclosure.sfrac Bool.false 33 1))

noncomputable abbrev qz135 := (@HMul.hMul Real Real Real qz268 qz279 qz618)

noncomputable abbrev qz136 := (Real.sin (@HMul.hMul Real Real Real qz268 qz279 qz618))

noncomputable abbrev qz619 := (@Neg.neg Real Real.instNeg qz136)

noncomputable def ep683 := @Enclosure.Complex.IsNear.of_eq qz127 (Complex.mk (@HMul.hMul Real Real Real qz0 qz134 (Real.cos qz135)) (@HMul.hMul Real Real Real qz0 qz134 qz619)) Bool.true 191289290543 1099511627776 25367867454737 212774191672328192 Bool.true 6497627201 1099511627776 25171955875379 212774191672328192 (BSN.cpow_neg_s_mk qz12 130272 1000 33 qz13 rfl)

noncomputable abbrev qz433 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 33) qz14)

noncomputable def ep684 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz432) 6023611 1048576 1 1048576 91266 91267 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz432) (Real.sqrt qz433) Bool.false 6023611 1048576 1 1048576 (BSN.sqrt_natCast_div_one 33) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz433) Bool.false 6023611 1048576 1 1048576 6023611 1048576 1 1048576 (BSN.sqrt_enclosure 33 1 3011805 3011806 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep685 := BSN.log_dyadic_bound 1 65 2 1 12675 524288 193517 1 1 16133 66 64 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 1) (BSN.artanhQ 65) 0 1 1 12675 1 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz137 := qz618

noncomputable def ep686 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz137 130272 1000 0 1 15746868335186131 4503599627370496 200000000193517 38703400000000000000 64105500992542739301 140737488355328000 814200000787807707 1209481250000000000000 qz18 (BSN.isNear_log_sfrac 33 1 15746868335186131 4503599627370496 200000000193517 38703400000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz433) Bool.false 66047152845744529997824 18889465931478580854784 1000000000967585 193517000000000000000 15746868335186131 4503599627370496 200000000193517 38703400000000000000 (BSN.log_rat_reduce_isNear 33 1 5 66 64 16133 524288 24973259072661432 36028797018963968 193517 1000000000000000 rfl rfl rfl rfl (ep685 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep687 := nat_lit 7644290618089918539272419723473172618620666113988813756198675895729479368048640

noncomputable def ep688 := nat_lit 14075733622615629666959192369012499124268950849721472927475417422974246977536

noncomputable def ep689 := nat_lit 19997971859608408964347927250022765193043404378118772691018714765368582897401856

noncomputable def ep690 := BSN.sin_dyadic_bound_f 3300341496 2147483648 3 2 1048576 387412 ep687 ep94 ep688 ep689 ep96 ep688 1047971 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3300341496) qz15 0 2 ep687 ep94 ep688 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3300341496) qz16 0 2 ep689 ep96 ep688 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz434 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 477623201) qz17)

noncomputable def ep691 := @Enclosure.Real.IsNear.cos_image qz135 qz434 Bool.false 477623201 1048576 707 1048576 Bool.true 1047971 1048576 1 193517 (@Enclosure.Real.IsNear.recentre' qz135 Bool.false 64105500992542739301 140737488355328000 814200000787807707 1209481250000000000000 477623201 1048576 707 1048576 (ep686 rfl) rfl) (Enclosure.sfrac_false_div 477623201 1048576) (BSN.cos_reduce1 qz434 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 232240886450949457969152) qz19) 226375608064910080 72057594037927936 Bool.false 1047971 1048576 72 1000000000000000 387034 193517 (BSN.sin_reduce_arg_pos_rat_q1 477623201 1048576 226375608064910080 72057594037927936 72 232240886450949457969152 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1047971 1048576 232240886450949457969152 151115727451828646838272 3300341496 2147483648 387412 387034 (ep690 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep692 := nat_lit 4253084002771117246114437265204657009955600708149217185855920127593254869794816

noncomputable def ep693 := nat_lit 12731100541068120479009393410875946031618264222748208611712809547933816115429376

noncomputable def ep694 := BSN.cos_dyadic_bound_f 3300341496 2147483648 3 2 1048576 387412 ep692 ep62 ep688 ep693 ep65 ep688 35597 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3300341496) qz20 0 2 ep692 ep62 ep688 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3300341496) qz21 0 2 ep693 ep65 ep688 rfl rfl rfl rfl) rfl rfl

noncomputable def ep695 := @Enclosure.Real.IsNear.sin_image qz135 qz434 Bool.false 477623201 1048576 707 1048576 Bool.false 35597 1048576 1 193517 (@Enclosure.Real.IsNear.recentre' qz135 Bool.false 64105500992542739301 140737488355328000 814200000787807707 1209481250000000000000 477623201 1048576 707 1048576 (ep686 rfl) rfl) (Enclosure.sfrac_false_div 477623201 1048576) (BSN.sin_reduce1 qz434 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 232240886450949457969152) qz19) 226375608064910080 72057594037927936 Bool.false 35597 1048576 72 1000000000000000 387034 193517 (BSN.sin_reduce_arg_pos_rat_q1 477623201 1048576 226375608064910080 72057594037927936 72 232240886450949457969152 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 35597 1048576 232240886450949457969152 151115727451828646838272 3300341496 2147483648 387412 387034 (ep694 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz435 := (@Enclosure.Real.IsNear.recentre' qz134 Bool.false 182533 1048576 1 1048576 182533 1048576 1 1048576 (ep684 rfl rfl) rfl)

noncomputable def ep696 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz134 (Real.cos qz135)) (@HMul.hMul Real Real Real qz0 qz134 qz619) Bool.true 191289290543 1099511627776 25367867454737 212774191672328192 Bool.true 6497627201 1099511627776 25171955875379 212774191672328192 (@Enclosure.Real.IsNear.mulLit_ft qz134 (Real.cos qz135) 182533 1048576 1 1048576 1047971 1048576 137865095 202917281792 191289290543 1099511627776 25367867454737 212774191672328192 qz435 (@Enclosure.Real.IsNear.recentre' (Real.cos qz135) Bool.true 1047971 1048576 137865095 202917281792 1047971 1048576 137865095 202917281792 (ep691 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz134 qz619 182533 1048576 1 1048576 35597 1048576 137865095 202917281792 6497627201 1099511627776 25171955875379 212774191672328192 qz435 (@Enclosure.Real.IsNear.neg qz136 Bool.false 35597 1048576 137865095 202917281792 (@Enclosure.Real.IsNear.recentre' qz136 Bool.false 35597 1048576 137865095 202917281792 35597 1048576 137865095 202917281792 (ep695 rfl rfl) rfl)) rfl)

noncomputable def ep697 := @ep682 840066677208 0 1 80394542503132946787179 923663079697343638929408 ep675 ep677 (@Enclosure.Complex.IsNear.re_isNear qz127 Bool.true 191289290543 1099511627776 25367867454737 212774191672328192 Bool.true 6497627201 1099511627776 25171955875379 212774191672328192 (ep683 ep696))

noncomputable def ep698 := @Enclosure.Complex.IsNear.re_isNear (@HAdd.hAdd Complex Complex Complex qz4 qz128 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz131 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1))))) Bool.false 420277278853 840066677208 0 1 Bool.false

noncomputable def ep699 := @Enclosure.Complex.IsNear.addLitP qz128 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz131 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) Bool.false 1058627749 2121380498 0 1 Bool.true 268686000

noncomputable def ep700 := @ep699 1060690249 0 1 Bool.false 1 792 0 1 Bool.false 1357 4125 0 1 Bool.false 840554557706 420277278853 840066677208 0 1 Bool.false 331026917893 331026917893 4375347277125 0 1

noncomputable abbrev qz138 := (@HDiv.hDiv Complex Complex Complex qz406 qz430 (@HSub.hSub Complex Complex Complex qz398 qz272 (1 : Complex)))

noncomputable def ep701 := @Enclosure.Complex.IsNear.addLitP qz138 qz105 Bool.true 66000000 67884175936 0 1 Bool.true 17195904000 67884175936 0 1

noncomputable def ep702 := @Enclosure.Complex.IsNear.of_eq qz138 (Complex.mk (Enclosure.sfrac Bool.true 66000000 67884175936) (Enclosure.sfrac Bool.true 17195904000 67884175936)) Bool.true 66000000 67884175936 0 1 Bool.true 17195904000 67884175936 0 1

noncomputable def ep703 := @ep701 Bool.false 1 2 0 1 Bool.false 0 1 0 1 Bool.false 67752175936 1058627749 2121380498 0 1 Bool.true 17195904000 268686000 1060690249 0 1 (ep702 (BSN.N_div_s_sub_one_mk qz12 130272 1000 33 qz13 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 66000000 67884175936) (Enclosure.sfrac Bool.true 17195904000 67884175936) Bool.true 66000000 67884175936 0 1 Bool.true 17195904000 67884175936 0 1 (Enclosure.Real.IsNear.const Bool.true 66000000 67884175936) (Enclosure.Real.IsNear.const Bool.true 17195904000 67884175936))) qz106 rfl

noncomputable abbrev qz139 := (@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 1)))

noncomputable abbrev qz140 := (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz431 qz430 1))

noncomputable def ep704 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz131 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@HAdd.hAdd Complex Complex Complex qz4 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz131 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz140)) Bool.false 1 792 0 1

noncomputable def ep705 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz131 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz140) Bool.false 0 1 0 1 Bool.false

noncomputable def ep706 := @ep705 0 1 0 1 Bool.false 1 792 0 1 Bool.false 1357 4125 0 1 Bool.false 1 1 792 0 1 Bool.false 1357 1357 4125 0

noncomputable def ep707 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz131 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (Complex.mk qz10 qz10) Bool.false 0 1 0 1 Bool.false

noncomputable def ep708 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz140 Bool.false 1 792 0 1 Bool.false 1357 4125 0 1

noncomputable def ep709 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz140)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz140)) 1 792 0 1 0 1 0

noncomputable def ep710 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz140) 1 24 0 1 1 33 0 1 1

noncomputable def ep711 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) 1 24 0 1 0 1 0 1 1

noncomputable def ep712 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 1 2 0 1 1 24 0

noncomputable def ep713 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139) (Complex.mk (Enclosure.sfrac Bool.false 1 12) qz10) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (BSN.bern_coeff_mk 1 1 6 2 Bool.false BSN.bern_real_1 EMRow44.d10 rfl) qz419

noncomputable def ep714 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) qz5 Bool.false 1 2 0 1 Bool.false 130272 1000 0 1 (BSN.ascPochhammer_one_eval qz5)

noncomputable def ep715 := ep714 (@Enclosure.Complex.IsNear.of_eq qz5 (Complex.mk qz100 qz12) Bool.false 1 2 0 1 Bool.false 130272 1000 0 1 (BSN.s_crit_mk qz12 Bool.false 130272 1000 qz13) (@Enclosure.Complex.IsNear.mk qz100 qz12 Bool.false 1 2 0 1 Bool.false 130272 1000 0 1 qz412 qz18))

noncomputable def ep716 := @ep712 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep713) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 130272 1000 0 1 ep715)

noncomputable def ep717 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 130272 1000 0 1 0 1 0

noncomputable def ep718 := @ep717 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep713) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 130272 1000 0 1 ep715)

noncomputable def ep719 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) 1357 125 0 1 0 1 0 1 1357

noncomputable def ep720 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 130272 1000 0 1 1357 125 0

noncomputable def ep721 := @ep720 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep713) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 130272 1000 0 1 ep715)

noncomputable def ep722 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 1 2 0 1 0 1 0

noncomputable def ep723 := @ep722 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep713) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 130272 1000 0 1 ep715)

noncomputable def ep724 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 24 0 1 Bool.false 1357 125 0 1 (@ep711 1 24 0 1 (ep716 rfl) (ep718 rfl) rfl rfl) (@ep719 1357 125 0 1 (ep721 rfl) (ep723 rfl) rfl rfl)

noncomputable def ep725 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 1357 125 0 1 ep724

noncomputable abbrev qz141 := (@Enclosure.Complex.IsNear.of_eq (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz431 qz430 1)) (Complex.mk (Enclosure.sfrac Bool.false 1 33) qz278) Bool.false 1 33 0 1 Bool.false 0 1 0 1 (BSN.natCast_pow_inv_mk 33 1 33 EMRow44.d11 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 33) qz278 Bool.false 1 33 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 33) qz546))

noncomputable def ep726 := @ep710 792 0 1 ep725 (@Enclosure.Complex.IsNear.re_isNear qz140 Bool.false 1 33 0 1 Bool.false 0 1 0 1 qz141)

noncomputable def ep727 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz140) 1357 125 0 1 0 1 0 1 0

noncomputable def ep728 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 1357 125 0 1 ep724

noncomputable def ep729 := @ep727 1 0 1 ep728 (@Enclosure.Complex.IsNear.im_isNear qz140 Bool.false 1 33 0 1 Bool.false 0 1 0 1 qz141)

noncomputable def ep730 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz140)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz140)) 0 1 0 1 1357 4125 0

noncomputable def ep731 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz140) 1 24 0 1 0 1 0 1 0

noncomputable def ep732 := @ep731 1 0 1 ep725 (@Enclosure.Complex.IsNear.im_isNear qz140 Bool.false 1 33 0 1 Bool.false 0 1 0 1 qz141)

noncomputable def ep733 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz140) 1357 125 0 1 1 33 0 1 1357

noncomputable def ep734 := @ep733 4125 0 1 ep728 (@Enclosure.Complex.IsNear.re_isNear qz140 Bool.false 1 33 0 1 Bool.false 0 1 0 1 qz141)

noncomputable def ep735 := @ep706 1 (@ep707 0 1 0 1 (BSN.bern_sum_base qz5 33) qz121) (ep708 (@ep709 1 1 1 792 0 1 (ep726 rfl) (ep729 rfl) rfl rfl) (@ep730 1 1357 1357 4125 0 1 (ep732 rfl) (ep734 rfl) rfl rfl)) rfl rfl rfl rfl rfl

noncomputable def ep736 := ep700 (ep703 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep704 Bool.false 1357 4125 0 1 (BSN.bern_sum_succ qz5 33 0 1 1 rfl rfl) (ep735 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl rfl

noncomputable def ep737 := @Enclosure.Real.IsNear.mulLit_tf qz133 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz128 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz131 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))))) 6497627201 1099511627776 25171955875379 212774191672328192 331026917893

noncomputable def ep738 := @ep737 4375347277125 0 1 2150889505964750407493 ep678 ep679 ep680 (@Enclosure.Complex.IsNear.im_isNear qz127 Bool.true 191289290543 1099511627776 25367867454737 212774191672328192 Bool.true 6497627201 1099511627776 25171955875379 212774191672328192 (ep683 ep696))

noncomputable def ep739 := @Enclosure.Complex.IsNear.im_isNear (@HAdd.hAdd Complex Complex Complex qz4 qz128 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz131 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1))))) Bool.false 420277278853 840066677208 0 1 Bool.false

noncomputable def ep740 := nat_lit 8397446977059731792909141

noncomputable def ep741 := @Enclosure.Real.IsNear.addLit_tt (@HMul.hMul Real Real Real qz0 qz132 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz128 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz131 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz133 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz128 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz131 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1))))))) 63321904274387882385899 ep678 ep740

noncomputable def ep742 := nat_lit 10579201118712071700060287

noncomputable def ep743 := nat_lit 71625312558948889550128456363737558730294689792

noncomputable def ep744 := @Enclosure.Real.IsNear.mulLit_tf qz132 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz128 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz131 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))))) 191289290543 1099511627776 25367867454737 212774191672328192 331026917893

noncomputable def ep745 := @ep744 4375347277125 0 1 63321904274387882385899 ep678 ep740 ep680 (@Enclosure.Complex.IsNear.re_isNear qz127 Bool.true 191289290543 1099511627776 25367867454737 212774191672328192 Bool.true 6497627201 1099511627776 25171955875379 212774191672328192 (ep683 ep696))

noncomputable def ep746 := @Enclosure.Real.IsNear.mulLit_tf qz133 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz128 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz131 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))))) 6497627201 1099511627776 25171955875379 212774191672328192 420277278853

noncomputable def ep747 := @ep746 840066677208 0 1 2730805079037514880453 923663079697343638929408 ep742 ep677 (@Enclosure.Complex.IsNear.im_isNear qz127 Bool.true 191289290543 1099511627776 25367867454737 212774191672328192 Bool.true 6497627201 1099511627776 25171955875379 212774191672328192 (ep683 ep696))

noncomputable abbrev qz620 := (ep736 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable def ep748 := @ep674 ep668 ep540 ep669 ep542 (@ep676 ep677 2150889505964750407493 ep678 ep679 ep680 ep681 ep666 ep540 ep667 ep542 (ep697 (@ep698 331026917893 4375347277125 0 1 qz620) rfl) (ep738 (@ep739 331026917893 4375347277125 0 1 qz620) rfl) rfl rfl) (@ep741 ep680 2730805079037514880453 923663079697343638929408 ep742 ep677 ep743 ep668 ep540 ep669 ep542 (ep745 (@ep739 331026917893 4375347277125 0 1 qz620) rfl) (ep747 (@ep698 331026917893 4375347277125 0 1 qz620) rfl) rfl rfl)

noncomputable def ep749 := @ep672 ep663 ep542 (@ep673 106387095836164096 (BSN.head_sum_c_eq qz5 33) EMRow44.d9) ep748 rfl rfl rfl rfl rfl rfl rfl rfl rfl

noncomputable def ep750 := @Enclosure.Complex.IsNear.re_isNear (zetaApproximant qz5 1 33) Bool.false ep539 ep540 ep541 ep542 Bool.false ep662 ep540 ep663 ep542 (@ep664 ep542 Bool.false ep662 ep540 ep663 ep542 (BSN.zetaApproximant_eq_folded' qz5 1 33 rfl) (ep749 rfl rfl rfl rfl rfl rfl rfl rfl rfl))

noncomputable def ep751 := @Enclosure.Real.IsNear.mulLit_ff (Real.sin (@HSub.hSub Real Real Real qz401 (Complex.im (@HSub.hSub Complex Complex Complex qz81 qz82 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz83 (@Nat.cast Complex Complex.instNatCast j))))) qz84)) (Complex.im (zetaApproximant qz5 1 33)) 63 131072 8839337

noncomputable def ep752 := @Enclosure.Real.IsNear.recentre' (Real.sin (@HSub.hSub Real Real Real qz401 (Complex.im (@HSub.hSub Complex Complex Complex qz81 qz82 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz83 (@Nat.cast Complex Complex.instNatCast j))))) qz84)) Bool.false 504 1048576 8839337

noncomputable def ep753 := @Enclosure.Real.IsNear.sin_image (@HSub.hSub Real Real Real qz401 (Complex.im (@HSub.hSub Complex Complex Complex qz81 qz82 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz83 (@Nat.cast Complex Complex.instNatCast j))))) qz84) qz402 Bool.false 8647303 65536 45

noncomputable def ep754 := BSN.sin_dyadic_bound_f 1032909 2147483648 1 0 1048576 387412 0 1 1 0 1 1 504 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 1032909) qz15 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 1032909) qz16 0 0 rfl) rfl rfl

noncomputable def ep755 := @ep753 131072 Bool.false 504 1048576 1 193517 (@ep547 8647303 65536 45 131072 ep659 rfl) (Enclosure.sfrac_false_div 8647303 65536) (BSN.sin_reduce0 qz402 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 4542781989161271296) qz377) 226375608064910080 72057594037927936 Bool.false 504 1048576 21 1000000000000000 387034 193517 (BSN.sin_reduce_arg_pos_rat_q0 8647303 65536 226375608064910080 72057594037927936 21 4542781989161271296 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 504 1048576 4542781989161271296 9444732965739290427392 1032909 2147483648 387412 387034 (ep754 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep756 := @Enclosure.Complex.IsNear.im_isNear (zetaApproximant qz5 1 33) Bool.false ep539 ep540 ep541 ep542 Bool.false ep662 ep540 ep663 ep542 (@ep664 ep542 Bool.false ep662 ep540 ep663 ep542 (BSN.zetaApproximant_eq_folded' qz5 1 33 rfl) (ep749 rfl rfl rfl rfl rfl rfl rfl rfl rfl))

theorem EMRow44.d12 : Enclosure.Real.IsNear (hardyZApproximantEM 1 33 qz12) Bool.false ep523 ep524 ep525 ep526 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantEM 1 33 qz12) ep527 Bool.false ep523 ep524 ep525 ep526 (@Eq.refl Real ep527) (@ep528 Bool.false ep523 ep524 ep525 ep526 (BSN.re_exp_mul (@HSub.hSub Real Real Real qz401 (Complex.im (@HSub.hSub Complex Complex Complex qz81 qz82 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz83 (@Nat.cast Complex Complex.instNatCast j))))) qz84) (zetaApproximant qz5 1 33)) (@ep530 ep531 ep532 ep526 ep533 ep534 ep535 ep536 ep537 ep523 ep524 ep525 ep526 (@ep538 25364660224 ep539 ep540 ep541 ep542 ep529 ep531 ep532 ep526 (@ep543 25364660224 1048575 1048576 8839337 25364660224 (ep661 rfl rfl) rfl) ep750 rfl) (@ep751 25364660224 ep662 ep540 ep663 ep542 ep533 ep534 ep535 ep536 (@ep752 25364660224 63 131072 8839337 25364660224 (ep755 rfl rfl) rfl) ep756 rfl) rfl rfl))

noncomputable abbrev qz671 := (@HAdd.hAdd Complex Complex Complex (@instHAdd Complex Complex.instAdd) (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (2 : Complex)) (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul) Complex.I ↑(Enclosure.sfrac Bool.false 132339 1000)))

noncomputable abbrev qz621 := qz671

noncomputable abbrev qz436 := qz621

noncomputable abbrev qz142 := (BSN.headSumC qz436 9)

noncomputable abbrev qz143 := qz436

noncomputable abbrev qz622 := (@Neg.neg Complex Complex.instNeg qz671)

noncomputable abbrev qz437 := qz622

noncomputable abbrev qz144 := qz437

noncomputable abbrev qz623 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 8) qz144)

noncomputable def ep757 := @Enclosure.Complex.IsNear.of_eq qz142 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz143 8) qz623) Bool.false 971102621573 549755813888 123972687426123 53193547918082048 Bool.false 594454931325 1099511627776 496094198964517 212774191672328192

noncomputable def ep758 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz143 8) qz623 Bool.false 114164814533 68719476736 221965404531359 106387095836164096 Bool.false 111648017185 549755813888 111000210425979 53193547918082048 Bool.false

noncomputable abbrev qz624 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 7) qz144)

noncomputable def ep759 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz143 8) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz143 7) qz624) Bool.false 114164814533 68719476736 221965404531359 106387095836164096 Bool.false 111648017185 549755813888 111000210425979 53193547918082048

noncomputable def ep760 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz143 7) qz624 Bool.false 353195049957 274877906944 194122777999887 106387095836164096 Bool.false 92763923585 549755813888 48562403082869 26596773959041024 Bool.false

noncomputable abbrev qz625 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 6) qz144)

noncomputable def ep761 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz143 7) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz143 6) qz625) Bool.false 353195049957 274877906944 194122777999887 106387095836164096 Bool.false 92763923585 549755813888 48562403082869 26596773959041024

noncomputable def ep762 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz143 6) qz625 Bool.false 722247430311 549755813888 10256870004481 6649193489760256 Bool.true 262223523275 1099511627776 328285435633297 212774191672328192 Bool.true

noncomputable abbrev qz626 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 5) qz144)

noncomputable def ep763 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz143 6) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz143 5) qz626) Bool.false 722247430311 549755813888 10256870004481 6649193489760256 Bool.true 262223523275 1099511627776 328285435633297 212774191672328192

noncomputable def ep764 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz143 5) qz626 Bool.false 262313765417 274877906944 131204165872281 106387095836164096 Bool.true 138686723203 274877906944 16407269711979 13298386979520512 Bool.false

noncomputable abbrev qz627 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 4) qz144)

noncomputable def ep765 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz143 5) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz143 4) qz627) Bool.false 262313765417 274877906944 131204165872281 106387095836164096 Bool.true 138686723203 274877906944 16407269711979 13298386979520512

noncomputable def ep766 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz143 4) qz627 Bool.false 875023481541 1099511627776 188845503363493 212774191672328192 Bool.true 33332461285 1099511627776 188825340053195 212774191672328192 Bool.false

noncomputable def ep767 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz143 4) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz143 3) (@HPow.hPow Complex Complex Complex qz6 qz8 qz144)) Bool.false 875023481541 1099511627776 188845503363493 212774191672328192 Bool.true 33332461285 1099511627776 188825340053195 212774191672328192

noncomputable def ep768 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz143 3) (@HPow.hPow Complex Complex Complex qz6 qz8 qz144) Bool.false 468569754071 1099511627776 103963903111259 212774191672328192 Bool.false 113570886715 274877906944 25979448986089 53193547918082048 Bool.false

noncomputable def ep769 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz143 3) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz143 2) (@HPow.hPow Complex Complex Complex qz6 qz9 qz144)) Bool.false 468569754071 1099511627776 103963903111259 212774191672328192 Bool.false 113570886715 274877906944 25979448986089 53193547918082048

noncomputable def ep770 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz143 2) (@HPow.hPow Complex Complex Complex qz6 qz9 qz144) Bool.false 1 1 0 1 Bool.false 0 1 0 1 Bool.true

noncomputable def ep771 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz143 2) (Complex.mk (Enclosure.sfrac Bool.false 1 1) qz10) Bool.false 1 1 0 1 Bool.false 0 1 0 1 (BSN.head_sum_c_two qz143)

noncomputable abbrev qz672 := (Enclosure.sfrac Bool.false 132339 1000)

noncomputable abbrev qz628 := qz672

noncomputable abbrev qz438 := qz628

noncomputable abbrev qz145 := (@HMul.hMul Real Real Real qz268 qz438 (Real.log qz280))

noncomputable abbrev qz146 := qz438

noncomputable abbrev qz439 := (@Eq.refl Real qz628)

noncomputable abbrev qz147 := qz439

noncomputable def ep772 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz9 qz144) (Complex.mk (@HMul.hMul Real Real Real qz0 qz282 (Real.cos qz145)) (@HMul.hMul Real Real Real qz0 qz282 (@Neg.neg Real Real.instNeg (Real.sin qz145)))) Bool.true 630941873705 1099511627776 103963903111259 212774191672328192 Bool.false 113570886715 274877906944 25979448986089 53193547918082048 (BSN.cpow_neg_s_mk qz146 132339 1000 2 qz147 rfl)

noncomputable def ep773 := nat_lit 3225047377454384702336996260569760000

noncomputable def ep774 := BSN.cos_dyadic_bound_f 1340090180 2147483648 2 1 1048576 387412 ep773 ep76 ep773 ep773 ep77 ep773 850951 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1340090180) qz20 0 1 ep773 ep76 ep773 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1340090180) qz21 0 1 ep773 ep77 ep773 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz148 := (Enclosure.Real.IsNear.const Bool.false 132339 1000)

noncomputable abbrev qz440 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 48093051) qz24)

noncomputable def ep775 := @Enclosure.Real.IsNear.cos_image qz145 qz440 Bool.false 48093051 524288 359 524288 Bool.true 850951 1048576 1 193517 (@Enclosure.Real.IsNear.recentre' qz145 Bool.false 3005815707 32768000 132339 193517000 48093051 524288 359 524288 (@Enclosure.Real.IsNear.mulLit_ff qz146 (Real.log qz280) 132339 1000 0 1 363408 524288 1 193517 3005815707 32768000 132339 193517000 qz148 qz286 rfl) rfl) (Enclosure.sfrac_false_div 48093051 524288) (BSN.cos_reduce2 qz440 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 47150231540864911409152) qz25) 226375608064910080 72057594037927936 Bool.false 850951 1048576 14 1000000000000000 387034 193517 (BSN.sin_reduce_arg_pos_rat_q2 48093051 524288 226375608064910080 72057594037927936 14 47150231540864911409152 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 850951 1048576 47150231540864911409152 75557863725914323419136 1340090180 2147483648 387412 387034 (ep774 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep776 := BSN.sin_dyadic_bound_f 1340090180 2147483648 2 1 1048576 387412 ep773 ep57 ep773 ep773 ep58 ep773 612692 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1340090180) qz15 0 1 ep773 ep57 ep773 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1340090180) qz16 0 1 ep773 ep58 ep773 rfl rfl rfl rfl) rfl rfl

noncomputable def ep777 := @Enclosure.Real.IsNear.sin_image qz145 qz440 Bool.false 48093051 524288 359 524288 Bool.true 612692 1048576 1 193517 (@Enclosure.Real.IsNear.recentre' qz145 Bool.false 3005815707 32768000 132339 193517000 48093051 524288 359 524288 (@Enclosure.Real.IsNear.mulLit_ff qz146 (Real.log qz280) 132339 1000 0 1 363408 524288 1 193517 3005815707 32768000 132339 193517000 qz148 qz286 rfl) rfl) (Enclosure.sfrac_false_div 48093051 524288) (BSN.sin_reduce2 qz440 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 47150231540864911409152) qz25) 226375608064910080 72057594037927936 Bool.false 612692 1048576 14 1000000000000000 387034 193517 (BSN.sin_reduce_arg_pos_rat_q2 48093051 524288 226375608064910080 72057594037927936 14 47150231540864911409152 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 612692 1048576 47150231540864911409152 75557863725914323419136 1340090180 2147483648 387412 387034 (ep776 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep778 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz282 (Real.cos qz145)) (@HMul.hMul Real Real Real qz0 qz282 (@Neg.neg Real Real.instNeg (Real.sin qz145))) Bool.true 630941873705 1099511627776 103963903111259 212774191672328192 Bool.false 113570886715 274877906944 25979448986089 53193547918082048 (@Enclosure.Real.IsNear.mulLit_ft qz282 (Real.cos qz145) 741455 1048576 1 1048576 850951 1048576 69996891 101458640896 630941873705 1099511627776 103963903111259 212774191672328192 qz287 (@Enclosure.Real.IsNear.recentre' (Real.cos qz145) Bool.true 850951 1048576 69996891 101458640896 850951 1048576 69996891 101458640896 (ep775 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz282 (@Neg.neg Real Real.instNeg (Real.sin qz145)) 741455 1048576 1 1048576 153173 262144 69996891 101458640896 113570886715 274877906944 25979448986089 53193547918082048 qz287 (@Enclosure.Real.IsNear.neg (Real.sin qz145) Bool.true 153173 262144 69996891 101458640896 (@Enclosure.Real.IsNear.recentre' (Real.sin qz145) Bool.true 612692 1048576 69996891 101458640896 153173 262144 69996891 101458640896 (ep777 rfl rfl) rfl)) rfl)

noncomputable def ep779 := @ep770 630941873705 1099511627776 103963903111259 212774191672328192 Bool.false 113570886715 274877906944 25979448986089 53193547918082048 Bool.false 468569754071 468569754071 1099511627776 103963903111259 212774191672328192 Bool.false 113570886715 113570886715 274877906944 25979448986089 53193547918082048 (ep771 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 1) qz10 Bool.false 1 1 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 1) qz22)) (ep772 ep778) rfl rfl

noncomputable abbrev qz149 := (@HMul.hMul Real Real Real qz268 qz438 qz547)

noncomputable def ep780 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz8 qz144) (Complex.mk (@HMul.hMul Real Real Real qz0 qz288 (Real.cos qz149)) (@HMul.hMul Real Real Real qz0 qz288 (@Neg.neg Real Real.instNeg (Real.sin qz149)))) Bool.false 203226863735 549755813888 42440800126117 106387095836164096 Bool.true 487616008145 1099511627776 84907544108839 212774191672328192 (BSN.cpow_neg_s_mk qz146 132339 1000 3 qz147 rfl)

noncomputable def ep781 := nat_lit 447481618661006711759981812633140088178184724751251260302513769403092809900001

noncomputable def ep782 := nat_lit 156743164792234665190765030974392840374911601761675994089509982346991460321

noncomputable def ep783 := nat_lit 1342131369653435665949563907837471478853804351050230428919362288244584446779361

noncomputable def ep784 := BSN.cos_dyadic_bound_f 1881042363 2147483648 3 2 1048576 387412 ep781 ep62 ep782 ep783 ep65 ep782 671386 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1881042363) qz20 0 2 ep781 ep62 ep782 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1881042363) qz21 0 2 ep783 ep65 ep782 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz441 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 4764113) (@Nat.cast Real Real.instNatCast 32768))

noncomputable abbrev qz442 := (@Nat.cast Real Real.instNatCast 4722366482869645213696)

noncomputable def ep785 := @Enclosure.Real.IsNear.cos_image qz149 qz441 Bool.false 4764113 32768 359 524288 Bool.false 671386 1048576 1 193517 (@Enclosure.Real.IsNear.recentre' qz149 Bool.false 76225808271 524288000 132339 193517000 4764113 32768 359 524288 (@Enclosure.Real.IsNear.mulLit_ff qz146 qz547 132339 1000 0 1 575989 524288 1 193517 76225808271 524288000 132339 193517000 qz148 qz292 rfl) rfl) (Enclosure.sfrac_false_div 4764113 32768) (BSN.cos_reduce0 qz441 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 4136455903100383789056) qz442) 226375608064910080 72057594037927936 Bool.false 671386 1048576 23 1000000000000000 387034 193517 (BSN.sin_reduce_arg_pos_rat_q0 4764113 32768 226375608064910080 72057594037927936 23 4136455903100383789056 4722366482869645213696 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 671386 1048576 4136455903100383789056 4722366482869645213696 1881042363 2147483648 387412 387034 (ep784 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep786 := nat_lit 805341519057978293435814650714872644448432575270842927749253176939689464651745

noncomputable def ep787 := nat_lit 2108974013361231912397777132298326956575764030735069716305232447251577278390241

noncomputable def ep788 := BSN.sin_dyadic_bound_f 1881042363 2147483648 3 2 1048576 387412 ep786 ep94 ep782 ep787 ep96 ep782 805451 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1881042363) qz15 0 2 ep786 ep94 ep782 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1881042363) qz16 0 2 ep787 ep96 ep782 rfl rfl rfl rfl) rfl rfl

noncomputable def ep789 := @Enclosure.Real.IsNear.sin_image qz149 qz441 Bool.false 4764113 32768 359 524288 Bool.false 805451 1048576 1 193517 (@Enclosure.Real.IsNear.recentre' qz149 Bool.false 76225808271 524288000 132339 193517000 4764113 32768 359 524288 (@Enclosure.Real.IsNear.mulLit_ff qz146 qz547 132339 1000 0 1 575989 524288 1 193517 76225808271 524288000 132339 193517000 qz148 qz292 rfl) rfl) (Enclosure.sfrac_false_div 4764113 32768) (BSN.sin_reduce0 qz441 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 4136455903100383789056) qz442) 226375608064910080 72057594037927936 Bool.false 805451 1048576 23 1000000000000000 387034 193517 (BSN.sin_reduce_arg_pos_rat_q0 4764113 32768 226375608064910080 72057594037927936 23 4136455903100383789056 4722366482869645213696 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 805451 1048576 4136455903100383789056 4722366482869645213696 1881042363 2147483648 387412 387034 (ep788 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep790 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz288 (Real.cos qz149)) (@HMul.hMul Real Real Real qz0 qz288 (@Neg.neg Real Real.instNeg (Real.sin qz149))) Bool.false 203226863735 549755813888 42440800126117 106387095836164096 Bool.true 487616008145 1099511627776 84907544108839 212774191672328192 (@Enclosure.Real.IsNear.mulLit_ff qz288 (Real.cos qz149) 605395 1048576 1 1048576 335693 524288 69996891 101458640896 203226863735 549755813888 42440800126117 106387095836164096 qz293 (@Enclosure.Real.IsNear.recentre' (Real.cos qz149) Bool.false 671386 1048576 69996891 101458640896 335693 524288 69996891 101458640896 (ep785 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz288 (@Neg.neg Real Real.instNeg (Real.sin qz149)) 605395 1048576 1 1048576 805451 1048576 69996891 101458640896 487616008145 1099511627776 84907544108839 212774191672328192 qz293 (@Enclosure.Real.IsNear.neg (Real.sin qz149) Bool.false 805451 1048576 69996891 101458640896 (@Enclosure.Real.IsNear.recentre' (Real.sin qz149) Bool.false 805451 1048576 69996891 101458640896 805451 1048576 69996891 101458640896 (ep789 rfl rfl) rfl)) rfl)

noncomputable def ep791 := @ep768 203226863735 549755813888 42440800126117 106387095836164096 Bool.true 487616008145 1099511627776 84907544108839 212774191672328192 Bool.false 481049246265683799441408 875023481541 1099511627776 188845503363493 212774191672328192 Bool.true 9162357191312712663040 33332461285 1099511627776 188825340053195 212774191672328192 (ep769 (BSN.head_sum_c_succ qz143 2 3 rfl rfl) (ep779 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep780 ep790) rfl rfl

noncomputable abbrev qz150 := (@HMul.hMul Real Real Real qz268 qz438 qz548)

noncomputable def ep792 := @Enclosure.Complex.IsNear.of_eq qz627 (Complex.mk (@HMul.hMul Real Real Real qz0 qz294 (Real.cos qz150)) (@HMul.hMul Real Real Real qz0 qz294 (@Neg.neg Real Real.instNeg (Real.sin qz150)))) Bool.false 174231580127 1099511627776 73562828381069 212774191672328192 Bool.true 521414431527 1099511627776 73690975338469 212774191672328192 (BSN.cpow_neg_s_mk qz146 132339 1000 4 qz147 rfl)

noncomputable def ep793 := nat_lit 1847837689596997294120952943348640662126868254641076883517523987090427084800000

noncomputable def ep794 := nat_lit 2666954631069093632304545687722828985282950413887313905807390677401600000000

noncomputable def ep795 := nat_lit 5538179159528853695098249738670476328410038863095456022740957179916478054400000

noncomputable def ep796 := BSN.cos_dyadic_bound_f 2680723080 2147483648 3 2 1048576 387412 ep793 ep62 ep794 ep795 ep65 ep794 332321 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2680723080) qz20 0 2 ep793 ep62 ep794 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2680723080) qz21 0 2 ep795 ep65 ep794 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz443 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 192372469) qz17)

noncomputable def ep797 := @Enclosure.Real.IsNear.cos_image qz150 qz443 Bool.false 192372469 1048576 719 1048576 Bool.false 332321 1048576 1 193517 (@Enclosure.Real.IsNear.recentre' qz150 Bool.false 96186234963 524288000 132339 193517000 192372469 1048576 719 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz146 qz548 132339 1000 0 1 726817 524288 1 193517 96186234963 524288000 132339 193517000 qz148 qz298 rfl) rfl) (Enclosure.sfrac_false_div 192372469 1048576) (BSN.cos_reduce0 qz443 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 188639116688299747442688) qz19) 226375608064910080 72057594037927936 Bool.false 332321 1048576 29 1000000000000000 387034 193517 (BSN.sin_reduce_arg_pos_rat_q0 192372469 1048576 226375608064910080 72057594037927936 29 188639116688299747442688 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 332321 1048576 188639116688299747442688 151115727451828646838272 2680723080 2147483648 387412 387034 (ep796 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep798 := nat_lit 3323974277569739854511871661477374928640136498022828539206897264220847472640000

noncomputable def ep799 := nat_lit 8701328990899016324507361277517764042367042241770638142075328488053093171200000

noncomputable def ep800 := BSN.sin_dyadic_bound_f 2680723080 2147483648 3 2 1048576 387412 ep798 ep94 ep794 ep799 ep96 ep794 994521 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2680723080) qz15 0 2 ep798 ep94 ep794 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2680723080) qz16 0 2 ep799 ep96 ep794 rfl rfl rfl rfl) rfl rfl

noncomputable def ep801 := @Enclosure.Real.IsNear.sin_image qz150 qz443 Bool.false 192372469 1048576 719 1048576 Bool.false 994521 1048576 1 193517 (@Enclosure.Real.IsNear.recentre' qz150 Bool.false 96186234963 524288000 132339 193517000 192372469 1048576 719 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz146 qz548 132339 1000 0 1 726817 524288 1 193517 96186234963 524288000 132339 193517000 qz148 qz298 rfl) rfl) (Enclosure.sfrac_false_div 192372469 1048576) (BSN.sin_reduce0 qz443 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 188639116688299747442688) qz19) 226375608064910080 72057594037927936 Bool.false 994521 1048576 29 1000000000000000 387034 193517 (BSN.sin_reduce_arg_pos_rat_q0 192372469 1048576 226375608064910080 72057594037927936 29 188639116688299747442688 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 994521 1048576 188639116688299747442688 151115727451828646838272 2680723080 2147483648 387412 387034 (ep800 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep802 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz294 (Real.cos qz150)) (@HMul.hMul Real Real Real qz0 qz294 (@Neg.neg Real Real.instNeg (Real.sin qz150))) Bool.false 174231580127 1099511627776 73562828381069 212774191672328192 Bool.true 521414431527 1099511627776 73690975338469 212774191672328192 (@Enclosure.Real.IsNear.mulLit_ff qz294 (Real.cos qz150) 524287 1048576 1 1048576 332321 1048576 140187299 202917281792 174231580127 1099511627776 73562828381069 212774191672328192 qz299 (@Enclosure.Real.IsNear.recentre' (Real.cos qz150) Bool.false 332321 1048576 140187299 202917281792 332321 1048576 140187299 202917281792 (ep797 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz294 (@Neg.neg Real Real.instNeg (Real.sin qz150)) 524287 1048576 1 1048576 994521 1048576 140187299 202917281792 521414431527 1099511627776 73690975338469 212774191672328192 qz299 (@Enclosure.Real.IsNear.neg (Real.sin qz150) Bool.false 994521 1048576 140187299 202917281792 (@Enclosure.Real.IsNear.recentre' (Real.sin qz150) Bool.false 994521 1048576 140187299 202917281792 994521 1048576 140187299 202917281792 (ep801 rfl rfl) rfl)) rfl)

noncomputable def ep803 := @ep766 174231580127 1099511627776 73562828381069 212774191672328192 Bool.true 521414431527 1099511627776 73690975338469 212774191672328192 Bool.false 1153668140806789941690368 262313765417 274877906944 131204165872281 106387095836164096 Bool.true 609950659119400313946112 138686723203 274877906944 16407269711979 13298386979520512 (ep767 (BSN.head_sum_c_succ qz143 3 4 rfl rfl) (ep791 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep792 ep802) rfl rfl

noncomputable abbrev qz151 := (@HMul.hMul Real Real Real qz268 qz438 qz549)

noncomputable def ep804 := @Enclosure.Complex.IsNear.of_eq qz626 (Complex.mk (@HMul.hMul Real Real Real qz0 qz300 (Real.cos qz151)) (@HMul.hMul Real Real Real qz0 qz300 (@Neg.neg Real Real.instNeg (Real.sin qz151)))) Bool.false 197619899477 549755813888 32905754199415 106387095836164096 Bool.false 292523369537 1099511627776 65769120241633 212774191672328192 (BSN.cpow_neg_s_mk qz146 132339 1000 5 qz147 rfl)

noncomputable def ep805 := nat_lit 1039602373265328794538052583333383794226582118408420263070477379001414152355840

noncomputable def ep806 := nat_lit 261164291095610473109284212176473316906450892403544625341342006781920935936

noncomputable def ep807 := nat_lit 2722345283033134902071770305720100409032723675339113997695935724611771098464256

noncomputable def ep808 := BSN.sin_dyadic_bound_f 2004999296 2147483648 3 2 1048576 387412 ep805 ep94 ep806 ep807 ep96 ep806 842842 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2004999296) qz15 0 2 ep805 ep94 ep806 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2004999296) qz16 0 2 ep807 ep96 ep806 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz444 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 223337413) qz17)

noncomputable def ep809 := @Enclosure.Real.IsNear.cos_image qz151 qz444 Bool.false 223337413 1048576 359 524288 Bool.false 842842 1048576 1 193517 (@Enclosure.Real.IsNear.recentre' qz151 Bool.false 3489647091 16384000 132339 193517000 223337413 1048576 359 524288 (@Enclosure.Real.IsNear.mulLit_ff qz146 qz549 132339 1000 0 1 843808 524288 1 193517 3489647091 16384000 132339 193517000 qz148 qz304 rfl) rfl) (Enclosure.sfrac_false_div 223337413 1048576) (BSN.cos_reduce3 qz444 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 141089282563492687118336) qz19) 226375608064910080 72057594037927936 Bool.false 842842 1048576 33 1000000000000000 387034 193517 (BSN.sin_reduce_arg_pos_rat_q3 223337413 1048576 226375608064910080 72057594037927936 33 141089282563492687118336 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 842842 1048576 141089282563492687118336 151115727451828646838272 2004999296 2147483648 387412 387034 (ep808 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep810 := nat_lit 577672947054558490509188894835069429377837377290190610428194695892688716169216

noncomputable def ep811 := nat_lit 1732496512581484250581348116080855341499699230085764742033901403664502306635776

noncomputable def ep812 := BSN.cos_dyadic_bound_f 2004999296 2147483648 3 2 1048576 387412 ep810 ep62 ep806 ep811 ep65 ep806 623801 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2004999296) qz20 0 2 ep810 ep62 ep806 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2004999296) qz21 0 2 ep811 ep65 ep806 rfl rfl rfl rfl) rfl rfl

noncomputable def ep813 := @Enclosure.Real.IsNear.sin_image qz151 qz444 Bool.false 223337413 1048576 359 524288 Bool.true 623801 1048576 1 193517 (@Enclosure.Real.IsNear.recentre' qz151 Bool.false 3489647091 16384000 132339 193517000 223337413 1048576 359 524288 (@Enclosure.Real.IsNear.mulLit_ff qz146 qz549 132339 1000 0 1 843808 524288 1 193517 3489647091 16384000 132339 193517000 qz148 qz304 rfl) rfl) (Enclosure.sfrac_false_div 223337413 1048576) (BSN.sin_reduce3 qz444 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 141089282563492687118336) qz19) 226375608064910080 72057594037927936 Bool.false 623801 1048576 33 1000000000000000 387034 193517 (BSN.sin_reduce_arg_pos_rat_q3 223337413 1048576 226375608064910080 72057594037927936 33 141089282563492687118336 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 623801 1048576 141089282563492687118336 151115727451828646838272 2004999296 2147483648 387412 387034 (ep812 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep814 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz300 (Real.cos qz151)) (@HMul.hMul Real Real Real qz0 qz300 (@Neg.neg Real Real.instNeg (Real.sin qz151))) Bool.false 197619899477 549755813888 32905754199415 106387095836164096 Bool.false 292523369537 1099511627776 65769120241633 212774191672328192 (@Enclosure.Real.IsNear.mulLit_ff qz300 (Real.cos qz151) 468937 1048576 1 1048576 421421 524288 69996891 101458640896 197619899477 549755813888 32905754199415 106387095836164096 qz305 (@Enclosure.Real.IsNear.recentre' (Real.cos qz151) Bool.false 842842 1048576 69996891 101458640896 421421 524288 69996891 101458640896 (ep809 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz300 (@Neg.neg Real Real.instNeg (Real.sin qz151)) 468937 1048576 1 1048576 623801 1048576 69996891 101458640896 292523369537 1099511627776 65769120241633 212774191672328192 qz305 (@Enclosure.Real.IsNear.neg (Real.sin qz151) Bool.true 623801 1048576 69996891 101458640896 (@Enclosure.Real.IsNear.recentre' (Real.sin qz151) Bool.true 623801 1048576 69996891 101458640896 623801 1048576 69996891 101458640896 (ep813 rfl rfl) rfl)) rfl)

noncomputable def ep815 := @ep764 197619899477 549755813888 32905754199415 106387095836164096 Bool.false 292523369537 1099511627776 65769120241633 212774191672328192 Bool.false 198529861939570182979584 722247430311 549755813888 10256870004481 6649193489760256 Bool.true 72079453229313268121600 262223523275 1099511627776 328285435633297 212774191672328192 (ep765 (BSN.head_sum_c_succ qz143 4 5 rfl rfl) (ep803 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep804 ep814) rfl rfl

noncomputable abbrev qz152 := (@HMul.hMul Real Real Real qz268 qz438 qz550)

noncomputable def ep816 := @Enclosure.Complex.IsNear.of_eq qz625 (Complex.mk (@HMul.hMul Real Real Real qz0 qz306 (Real.cos qz152)) (@HMul.hMul Real Real Real qz0 qz306 (@Neg.neg Real Real.instNeg (Real.sin qz152)))) Bool.true 15857330397 549755813888 30012857928191 106387095836164096 Bool.false 447751370445 1099511627776 60213789029655 212774191672328192 (BSN.cpow_neg_s_mk qz146 132339 1000 6 qz147 rfl)

noncomputable def ep817 := @Enclosure.Real.IsNear.mulLit_ff qz146 qz550 132339 1000 0 1 4034681531866359 2251799813685248 500000000193517 96758500000000000000 533945719245662083701 2251799813685248000 66169500025609846263 96758500000000000000000 qz148 (BSN.isNear_log_sfrac 6 1 4034681531866359 2251799813685248 500000000193517 96758500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz551) Bool.false 33845361775666394038272 18889465931478580854784 1000000000387034 193517000000000000000 4034681531866359 2251799813685248 500000000193517 96758500000000000000 (BSN.log_rat_reduce_isNear 6 1 2 12 8 212580 524288 24973259072661432 36028797018963968 193517 1000000000000000 rfl rfl rfl rfl (ep119 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep818 := nat_lit 3859365711227162353811407160562688560316917286485825056227367087302823116800000

noncomputable def ep819 := nat_lit 11597392108220628202511961223418020251708816556231974676129046436249600000000

noncomputable def ep820 := nat_lit 11554902349465045805029197559241229640447334226345011219329843169035970150400000

noncomputable def ep821 := BSN.cos_dyadic_bound_f 3221402880 2147483648 3 2 1048576 387412 ep818 ep62 ep819 ep820 ep65 ep819 74086 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3221402880) qz20 0 2 ep818 ep62 ep819 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3221402880) qz21 0 2 ep820 ep65 ep819 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz445 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 124318925) qz24)

noncomputable def ep822 := @Enclosure.Real.IsNear.cos_image qz152 qz445 Bool.false 124318925 524288 719 1048576 Bool.true 74086 1048576 1 193517 (@Enclosure.Real.IsNear.recentre' qz152 Bool.false 533945719245662083701 2251799813685248000 66169500025609846263 96758500000000000000000 124318925 524288 719 1048576 (ep817 rfl) rfl) (Enclosure.sfrac_false_div 124318925 524288) (BSN.cos_reduce2 qz445 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 113343037592884058521600) qz25) 226375608064910080 72057594037927936 Bool.false 74086 1048576 37 1000000000000000 387034 193517 (BSN.sin_reduce_arg_pos_rat_q2 124318925 524288 226375608064910080 72057594037927936 37 113343037592884058521600 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 74086 1048576 113343037592884058521600 75557863725914323419136 3221402880 2147483648 387412 387034 (ep821 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep823 := nat_lit 6937580366522315734298523320034104992369084062429499521468357519996081930240000

noncomputable def ep824 := nat_lit 18151076610811803048930160758108550566273405889081456501989108381950096179200000

noncomputable def ep825 := BSN.sin_dyadic_bound_f 3221402880 2147483648 3 2 1048576 387412 ep823 ep94 ep819 ep824 ep96 ep819 1045955 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3221402880) qz15 0 2 ep823 ep94 ep819 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3221402880) qz16 0 2 ep824 ep96 ep819 rfl rfl rfl rfl) rfl rfl

noncomputable def ep826 := @Enclosure.Real.IsNear.sin_image qz152 qz445 Bool.false 124318925 524288 719 1048576 Bool.true 1045955 1048576 1 193517 (@Enclosure.Real.IsNear.recentre' qz152 Bool.false 533945719245662083701 2251799813685248000 66169500025609846263 96758500000000000000000 124318925 524288 719 1048576 (ep817 rfl) rfl) (Enclosure.sfrac_false_div 124318925 524288) (BSN.sin_reduce2 qz445 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 113343037592884058521600) qz25) 226375608064910080 72057594037927936 Bool.false 1045955 1048576 37 1000000000000000 387034 193517 (BSN.sin_reduce_arg_pos_rat_q2 124318925 524288 226375608064910080 72057594037927936 37 113343037592884058521600 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1045955 1048576 113343037592884058521600 75557863725914323419136 3221402880 2147483648 387412 387034 (ep825 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep827 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz306 (Real.cos qz152)) (@HMul.hMul Real Real Real qz0 qz306 (@Neg.neg Real Real.instNeg (Real.sin qz152))) Bool.true 15857330397 549755813888 30012857928191 106387095836164096 Bool.false 447751370445 1099511627776 60213789029655 212774191672328192 (@Enclosure.Real.IsNear.mulLit_ft qz306 (Real.cos qz152) 428079 1048576 1 1048576 37043 524288 140187299 202917281792 15857330397 549755813888 30012857928191 106387095836164096 qz310 (@Enclosure.Real.IsNear.recentre' (Real.cos qz152) Bool.true 74086 1048576 140187299 202917281792 37043 524288 140187299 202917281792 (ep822 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz306 (@Neg.neg Real Real.instNeg (Real.sin qz152)) 428079 1048576 1 1048576 1045955 1048576 140187299 202917281792 447751370445 1099511627776 60213789029655 212774191672328192 qz310 (@Enclosure.Real.IsNear.neg (Real.sin qz152) Bool.true 1045955 1048576 140187299 202917281792 (@Enclosure.Real.IsNear.recentre' (Real.sin qz152) Bool.true 1045955 1048576 140187299 202917281792 1045955 1048576 140187299 202917281792 (ep826 rfl rfl) rfl)) rfl)

noncomputable def ep828 := @ep762 15857330397 549755813888 30012857928191 106387095836164096 Bool.false 447751370445 1099511627776 60213789029655 212774191672328192 Bool.false 388342064300646708805632 353195049957 274877906944 194122777999887 106387095836164096 Bool.false 203990025239663654993920 92763923585 549755813888 48562403082869 26596773959041024 (ep763 (BSN.head_sum_c_succ qz143 5 6 rfl rfl) (ep815 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep816 ep827) rfl rfl

noncomputable abbrev qz153 := (@HMul.hMul Real Real Real qz268 qz438 qz552)

noncomputable def ep829 := @Enclosure.Complex.IsNear.of_eq qz624 (Complex.mk (@HMul.hMul Real Real Real qz0 qz311 (Real.cos qz153)) (@HMul.hMul Real Real Real qz0 qz311 (@Neg.neg Real Real.instNeg (Real.sin qz153)))) Bool.false 103464208175 274877906944 1740164158217 6649193489760256 Bool.false 590127925 17179869184 13875404260241 53193547918082048 (BSN.cpow_neg_s_mk qz146 132339 1000 7 qz147 rfl)

noncomputable def ep830 := @Enclosure.Real.IsNear.mulLit_ff qz146 qz552 132339 1000 0 1 4381796493761783 2251799813685248 500000000193517 96758500000000000000 579882566187940600437 2251799813685248000 66169500025609846263 96758500000000000000000 qz148 (BSN.isNear_log_sfrac 7 1 4381796493761783 2251799813685248 500000000193517 96758500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz553) Bool.false 36757173121942042968064 18889465931478580854784 1000000000387034 193517000000000000000 4381796493761783 2251799813685248 500000000193517 96758500000000000000 (BSN.log_rat_reduce_isNear 7 1 2 14 8 293399 524288 24973259072661432 36028797018963968 193517 1000000000000000 rfl rfl rfl rfl (ep134 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep831 := nat_lit 6569134122591783073357732753091623758001473671859820327126734527311741383147520

noncomputable def ep832 := nat_lit 10400100596207777002914681900052911898580582315717608457182168763506580586496

noncomputable def ep833 := nat_lit 17188036824870333553170295344544643223120443435883605681163152631627931063484416

noncomputable def ep834 := BSN.sin_dyadic_bound_f 3177822916 2147483648 3 2 1048576 387412 ep831 ep94 ep832 ep833 ep96 ep832 1044236 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3177822916) qz15 0 2 ep831 ep94 ep832 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3177822916) qz16 0 2 ep833 ep96 ep832 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz446 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 135014431) qz24)

noncomputable def ep835 := @Enclosure.Real.IsNear.cos_image qz153 qz446 Bool.false 135014431 524288 359 524288 Bool.false 1044236 1048576 1 193517 (@Enclosure.Real.IsNear.recentre' qz153 Bool.false 579882566187940600437 2251799813685248000 66169500025609846263 96758500000000000000000 135014431 524288 359 524288 (ep830 rfl) rfl) (Enclosure.sfrac_false_div 135014431 524288) (BSN.cos_reduce3 qz446 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 111809703934566504333312) qz25) 226375608064910080 72057594037927936 Bool.false 1044236 1048576 40 1000000000000000 387034 193517 (BSN.sin_reduce_arg_pos_rat_q3 135014431 524288 226375608064910080 72057594037927936 40 111809703934566504333312 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1044236 1048576 111809703934566504333312 75557863725914323419136 3177822916 2147483648 387412 387034 (ep834 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep836 := nat_lit 3654141223927082941644480277006481159733521187617996896606933479068081470898176

noncomputable def ep837 := nat_lit 10941623470588833270927611467219337655403402398222555472906436099677231251521536

noncomputable def ep838 := BSN.cos_dyadic_bound_f 3177822916 2147483648 3 2 1048576 387412 ep836 ep62 ep832 ep837 ep65 ep832 95296 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3177822916) qz20 0 2 ep836 ep62 ep832 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3177822916) qz21 0 2 ep837 ep65 ep832 rfl rfl rfl rfl) rfl rfl

noncomputable def ep839 := @Enclosure.Real.IsNear.sin_image qz153 qz446 Bool.false 135014431 524288 359 524288 Bool.true 95296 1048576 1 193517 (@Enclosure.Real.IsNear.recentre' qz153 Bool.false 579882566187940600437 2251799813685248000 66169500025609846263 96758500000000000000000 135014431 524288 359 524288 (ep830 rfl) rfl) (Enclosure.sfrac_false_div 135014431 524288) (BSN.sin_reduce3 qz446 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 111809703934566504333312) qz25) 226375608064910080 72057594037927936 Bool.false 95296 1048576 40 1000000000000000 387034 193517 (BSN.sin_reduce_arg_pos_rat_q3 135014431 524288 226375608064910080 72057594037927936 40 111809703934566504333312 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 95296 1048576 111809703934566504333312 75557863725914323419136 3177822916 2147483648 387412 387034 (ep838 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep840 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz311 (Real.cos qz153)) (@HMul.hMul Real Real Real qz0 qz311 (@Neg.neg Real Real.instNeg (Real.sin qz153))) Bool.false 103464208175 274877906944 1740164158217 6649193489760256 Bool.false 590127925 17179869184 13875404260241 53193547918082048 (@Enclosure.Real.IsNear.mulLit_ff qz311 (Real.cos qz153) 396325 1048576 1 1048576 261059 262144 69996891 101458640896 103464208175 274877906944 1740164158217 6649193489760256 qz315 (@Enclosure.Real.IsNear.recentre' (Real.cos qz153) Bool.false 1044236 1048576 69996891 101458640896 261059 262144 69996891 101458640896 (ep835 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz311 (@Neg.neg Real Real.instNeg (Real.sin qz153)) 396325 1048576 1 1048576 1489 16384 69996891 101458640896 590127925 17179869184 13875404260241 53193547918082048 qz315 (@Enclosure.Real.IsNear.neg (Real.sin qz153) Bool.true 1489 16384 69996891 101458640896 (@Enclosure.Real.IsNear.recentre' (Real.sin qz153) Bool.true 95296 1048576 69996891 101458640896 1489 16384 69996891 101458640896 (ep839 rfl rfl) rfl)) rfl)

noncomputable def ep841 := @ep760 103464208175 274877906944 1740164158217 6649193489760256 Bool.false 590127925 17179869184 13875404260241 53193547918082048 Bool.false 125525541061923971268608 114164814533 68719476736 221965404531359 106387095836164096 Bool.false 1918098329891283927040 111648017185 549755813888 111000210425979 53193547918082048 (ep761 (BSN.head_sum_c_succ qz143 6 7 rfl rfl) (ep828 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep829 ep840) rfl rfl

noncomputable abbrev qz154 := (@HMul.hMul Real Real Real qz268 qz438 qz554)

noncomputable def ep842 := @Enclosure.Complex.IsNear.of_eq qz623 (Complex.mk (@HMul.hMul Real Real Real qz0 qz316 (Real.cos qz154)) (@HMul.hMul Real Real Real qz0 qz316 (@Neg.neg Real Real.instNeg (Real.sin qz154)))) Bool.false 57784105309 549755813888 25979970320887 106387095836164096 Bool.false 371158896955 1099511627776 52093357260601 212774191672328192 (BSN.cpow_neg_s_mk qz146 132339 1000 8 qz147 rfl)

noncomputable def ep843 := @Enclosure.Real.IsNear.mulLit_ff qz146 qz554 132339 1000 0 1 9364972152248037 4503599627370496 1000000000580551 193517000000000000000 1239351049656352968543 4503599627370496000 132339000076829538789 193517000000000000000000 qz148 (BSN.isNear_log_sfrac 8 1 9364972152248037 4503599627370496 1000000000580551 193517000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz555) Bool.false 39279540158062550581248 18889465931478580854784 1000000000580551 193517000000000000000 9364972152248037 4503599627370496 1000000000580551 193517000000000000000 (BSN.log_rat_reduce_isNear 8 1 3 16 16 0 524288 24973259072661432 36028797018963968 193517 1000000000000000 rfl rfl rfl rfl (ep145 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep844 := nat_lit 176571709796730451734082442077515441

noncomputable def ep845 := BSN.sin_dyadic_bound_f 648231723 2147483648 2 1 1048576 387412 ep844 ep57 ep844 ep844 ep58 ep844 311734 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 648231723) qz15 0 1 ep844 ep57 ep844 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 648231723) qz16 0 1 ep844 ep58 ep844 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz447 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 144279451) qz24)

noncomputable def ep846 := @Enclosure.Real.IsNear.cos_image qz154 qz447 Bool.false 144279451 524288 359 524288 Bool.false 311734 1048576 1 193517 (@Enclosure.Real.IsNear.recentre' qz154 Bool.false 1239351049656352968543 4503599627370496000 132339000076829538789 193517000000000000000000 144279451 524288 359 524288 (ep843 rfl) rfl) (Enclosure.sfrac_false_div 144279451 524288) (BSN.cos_reduce3 qz447 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 22807626147505763254272) qz25) 226375608064910080 72057594037927936 Bool.false 311734 1048576 43 1000000000000000 387034 193517 (BSN.sin_reduce_arg_pos_rat_q3 144279451 524288 226375608064910080 72057594037927936 43 22807626147505763254272 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 311734 1048576 22807626147505763254272 75557863725914323419136 648231723 2147483648 387412 387034 (ep845 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep847 := BSN.cos_dyadic_bound_f 648231723 2147483648 2 1 1048576 387412 ep844 ep76 ep844 ep844 ep77 ep844 1001165 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 648231723) qz20 0 1 ep844 ep76 ep844 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 648231723) qz21 0 1 ep844 ep77 ep844 rfl rfl rfl rfl) rfl rfl

noncomputable def ep848 := @Enclosure.Real.IsNear.sin_image qz154 qz447 Bool.false 144279451 524288 359 524288 Bool.true 1001165 1048576 1 193517 (@Enclosure.Real.IsNear.recentre' qz154 Bool.false 1239351049656352968543 4503599627370496000 132339000076829538789 193517000000000000000000 144279451 524288 359 524288 (ep843 rfl) rfl) (Enclosure.sfrac_false_div 144279451 524288) (BSN.sin_reduce3 qz447 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 22807626147505763254272) qz25) 226375608064910080 72057594037927936 Bool.false 1001165 1048576 43 1000000000000000 387034 193517 (BSN.sin_reduce_arg_pos_rat_q3 144279451 524288 226375608064910080 72057594037927936 43 22807626147505763254272 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1001165 1048576 22807626147505763254272 75557863725914323419136 648231723 2147483648 387412 387034 (ep847 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep849 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz316 (Real.cos qz154)) (@HMul.hMul Real Real Real qz0 qz316 (@Neg.neg Real Real.instNeg (Real.sin qz154))) Bool.false 57784105309 549755813888 25979970320887 106387095836164096 Bool.false 371158896955 1099511627776 52093357260601 212774191672328192 (@Enclosure.Real.IsNear.mulLit_ff qz316 (Real.cos qz154) 370727 1048576 1 1048576 155867 524288 69996891 101458640896 57784105309 549755813888 25979970320887 106387095836164096 qz320 (@Enclosure.Real.IsNear.recentre' (Real.cos qz154) Bool.false 311734 1048576 69996891 101458640896 155867 524288 69996891 101458640896 (ep846 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz316 (@Neg.neg Real Real.instNeg (Real.sin qz154)) 370727 1048576 1 1048576 1001165 1048576 69996891 101458640896 371158896955 1099511627776 52093357260601 212774191672328192 qz320 (@Enclosure.Real.IsNear.neg (Real.sin qz154) Bool.true 1001165 1048576 69996891 101458640896 (@Enclosure.Real.IsNear.recentre' (Real.sin qz154) Bool.true 1001165 1048576 69996891 101458640896 1001165 1048576 69996891 101458640896 (ep848 rfl rfl) rfl)) rfl)

noncomputable def ep850 := @ep758 57784105309 549755813888 25979970320887 106387095836164096 Bool.false 371158896955 1099511627776 52093357260601 212774191672328192 Bool.false 66733664011454385225728 971102621573 549755813888 123972687426123 53193547918082048 Bool.false 326805054590310521241600 594454931325 1099511627776 496094198964517 212774191672328192 (ep759 (BSN.head_sum_c_succ qz143 7 8 rfl rfl) (ep841 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep842 ep849) rfl rfl

theorem EMRow44.d13 : Enclosure.Complex.IsNear qz142 Bool.false 971102621573 549755813888 123972687426123 53193547918082048 Bool.false 594454931325 1099511627776 496094198964517 212774191672328192 := ep757 (BSN.head_sum_c_succ qz143 8 9 rfl rfl) (ep850 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable abbrev qz155 := (BSN.headSumC qz436 17)

noncomputable abbrev qz629 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 16) qz144)

noncomputable def ep851 := @Enclosure.Complex.IsNear.of_eq qz155 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz143 16) qz629) Bool.false 1134916158007 1099511627776 833709072670963 212774191672328192 Bool.true 157955903609 1099511627776 833314161367961 212774191672328192

noncomputable def ep852 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz143 16) qz629 Bool.false 1354616109163 1099511627776 796848357632791 212774191672328192 Bool.false 3619244279 549755813888 199123420741245 53193547918082048 Bool.true

noncomputable abbrev qz630 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 15) qz144)

noncomputable def ep853 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz143 16) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz143 15) qz630) Bool.false 1354616109163 1099511627776 796848357632791 212774191672328192 Bool.false 3619244279 549755813888 199123420741245 53193547918082048

noncomputable def ep854 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz143 15) qz630 Bool.false 1078783012435 1099511627776 758749004438811 212774191672328192 Bool.false 74402020651 1099511627776 758543480095995 212774191672328192 Bool.false

noncomputable abbrev qz631 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 14) qz144)

noncomputable def ep855 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz143 15) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz143 14) qz631) Bool.false 1078783012435 1099511627776 758749004438811 212774191672328192 Bool.false 74402020651 1099511627776 758543480095995 212774191672328192

noncomputable def ep856 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz143 14) qz631 Bool.false 1331845804351 1099511627776 719341838822799 212774191672328192 Bool.true 74965256405 1099511627776 719207919640323 212774191672328192 Bool.true

noncomputable abbrev qz632 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 13) qz144)

noncomputable def ep857 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz143 14) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz143 13) qz632) Bool.false 1331845804351 1099511627776 719341838822799 212774191672328192 Bool.true 74965256405 1099511627776 719207919640323 212774191672328192

noncomputable def ep858 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz143 13) qz632 Bool.false 1030347273667 1099511627776 678427666544395 212774191672328192 Bool.true 29215308629 1099511627776 678463925437651 212774191672328192 Bool.false

noncomputable abbrev qz633 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 12) qz144)

noncomputable def ep859 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz143 13) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz143 12) qz633) Bool.false 1030347273667 1099511627776 678427666544395 212774191672328192 Bool.true 29215308629 1099511627776 678463925437651 212774191672328192

noncomputable def ep860 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz143 12) qz633 Bool.false 1197195676249 1099511627776 635945160989057 212774191672328192 Bool.false 240793442341 1099511627776 635915468514645 212774191672328192 Bool.true

noncomputable abbrev qz634 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 11) qz144)

noncomputable def ep861 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz143 12) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz143 11) qz634) Bool.false 1197195676249 1099511627776 635945160989057 212774191672328192 Bool.false 240793442341 1099511627776 635915468514645 212774191672328192

noncomputable def ep862 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz143 11) qz634 Bool.false 1528517462911 1099511627776 591482207623079 212774191672328192 Bool.false 229495888103 1099511627776 591648399248611 212774191672328192 Bool.true

noncomputable abbrev qz635 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 10) qz144)

noncomputable def ep863 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz143 11) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz143 10) qz635) Bool.false 1528517462911 1099511627776 591482207623079 212774191672328192 Bool.false 229495888103 1099511627776 591648399248611 212774191672328192

noncomputable def ep864 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz143 10) qz635 Bool.false 1876185213521 1099511627776 544858768810369 212774191672328192 Bool.false 116973403625 549755813888 136306315874135 53193547918082048 Bool.true

noncomputable abbrev qz636 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 9) qz144)

noncomputable def ep865 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz143 10) (@HAdd.hAdd Complex Complex Complex qz4 qz142 qz636) Bool.false 1876185213521 1099511627776 544858768810369 212774191672328192 Bool.false 116973403625 549755813888 136306315874135 53193547918082048

noncomputable def ep866 := @Enclosure.Complex.IsNear.addLitP qz142 qz636 Bool.false 971102621573 549755813888 123972687426123 53193547918082048 Bool.false 594454931325 1099511627776 496094198964517 212774191672328192 Bool.true

noncomputable abbrev qz156 := (@HMul.hMul Real Real Real qz268 qz438 qz564)

noncomputable def ep867 := @Enclosure.Complex.IsNear.of_eq qz636 (Complex.mk (@HMul.hMul Real Real Real qz0 qz321 (Real.cos qz156)) (@HMul.hMul Real Real Real qz0 qz321 (@Neg.neg Real Real.instNeg (Real.sin qz156)))) Bool.true 66020029625 1099511627776 48968019105877 212774191672328192 Bool.true 360508124075 1099511627776 49131064532023 212774191672328192 (BSN.cpow_neg_s_mk qz146 132339 1000 9 qz147 rfl)

noncomputable def ep868 := @Enclosure.Real.IsNear.mulLit_ff qz146 qz564 132339 1000 0 1 9895417793173221 4503599627370496 1000000000580551 193517000000000000000 1309549695330750893919 4503599627370496000 132339000076829538789 193517000000000000000000 qz148 (BSN.isNear_log_sfrac 9 1 9895417793173221 4503599627370496 1000000000580551 193517000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz565) Bool.false 41504390431577613533184 18889465931478580854784 1000000000580551 193517000000000000000 9895417793173221 4503599627370496 1000000000580551 193517000000000000000 (BSN.log_rat_reduce_isNear 9 1 3 18 16 61752 524288 24973259072661432 36028797018963968 193517 1000000000000000 rfl rfl rfl rfl (ep175 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep869 := nat_lit 22888738669298049189518867313401521

noncomputable def ep870 := BSN.sin_dyadic_bound_f 388960469 2147483648 2 1 1048576 387412 ep869 ep57 ep869 ep869 ep58 ep869 188885 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 388960469) qz15 0 1 ep869 ep57 ep869 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 388960469) qz16 0 1 ep869 ep58 ep869 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz448 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 152451649) qz24)

noncomputable def ep871 := @Enclosure.Real.IsNear.cos_image qz156 qz448 Bool.false 152451649 524288 359 524288 Bool.true 188885 1048576 1 193517 (@Enclosure.Real.IsNear.recentre' qz156 Bool.false 1309549695330750893919 4503599627370496000 132339000076829538789 193517000000000000000000 152451649 524288 359 524288 (ep868 rfl) rfl) (Enclosure.sfrac_false_div 152451649 524288) (BSN.cos_reduce1 qz448 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 13685329899283208470528) qz25) 226375608064910080 72057594037927936 Bool.false 188885 1048576 46 1000000000000000 387034 193517 (BSN.sin_reduce_arg_pos_rat_q1 152451649 524288 226375608064910080 72057594037927936 46 13685329899283208470528 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 188885 1048576 13685329899283208470528 75557863725914323419136 388960469 2147483648 387412 387034 (ep870 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep872 := BSN.cos_dyadic_bound_f 388960469 2147483648 2 1 1048576 387412 ep869 ep76 ep869 ep869 ep77 ep869 1031423 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 388960469) qz20 0 1 ep869 ep76 ep869 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 388960469) qz21 0 1 ep869 ep77 ep869 rfl rfl rfl rfl) rfl rfl

noncomputable def ep873 := @Enclosure.Real.IsNear.sin_image qz156 qz448 Bool.false 152451649 524288 359 524288 Bool.false 1031423 1048576 1 193517 (@Enclosure.Real.IsNear.recentre' qz156 Bool.false 1309549695330750893919 4503599627370496000 132339000076829538789 193517000000000000000000 152451649 524288 359 524288 (ep868 rfl) rfl) (Enclosure.sfrac_false_div 152451649 524288) (BSN.sin_reduce1 qz448 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 13685329899283208470528) qz25) 226375608064910080 72057594037927936 Bool.false 1031423 1048576 46 1000000000000000 387034 193517 (BSN.sin_reduce_arg_pos_rat_q1 152451649 524288 226375608064910080 72057594037927936 46 13685329899283208470528 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1031423 1048576 13685329899283208470528 75557863725914323419136 388960469 2147483648 387412 387034 (ep872 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep874 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz321 (Real.cos qz156)) (@HMul.hMul Real Real Real qz0 qz321 (@Neg.neg Real Real.instNeg (Real.sin qz156))) Bool.true 66020029625 1099511627776 48968019105877 212774191672328192 Bool.true 360508124075 1099511627776 49131064532023 212774191672328192 (@Enclosure.Real.IsNear.mulLit_ft qz321 (Real.cos qz156) 349525 1048576 1 1048576 188885 1048576 69996891 101458640896 66020029625 1099511627776 48968019105877 212774191672328192 qz326 (@Enclosure.Real.IsNear.recentre' (Real.cos qz156) Bool.true 188885 1048576 69996891 101458640896 188885 1048576 69996891 101458640896 (ep871 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz321 (@Neg.neg Real Real.instNeg (Real.sin qz156)) 349525 1048576 1 1048576 1031423 1048576 69996891 101458640896 360508124075 1099511627776 49131064532023 212774191672328192 qz326 (@Enclosure.Real.IsNear.neg (Real.sin qz156) Bool.false 1031423 1048576 69996891 101458640896 (@Enclosure.Real.IsNear.recentre' (Real.sin qz156) Bool.false 1031423 1048576 69996891 101458640896 1031423 1048576 69996891 101458640896 (ep873 rfl rfl) rfl)) rfl)

noncomputable def ep875 := @ep866 66020029625 1099511627776 48968019105877 212774191672328192 Bool.true 360508124075 1099511627776 49131064532023 212774191672328192 Bool.false 1031443729063868417179648 1876185213521 1099511627776 544858768810369 212774191672328192 Bool.false 257227234852445618176000 116973403625 549755813888 136306315874135 53193547918082048 EMRow44.d13 (ep867 ep874) rfl rfl

noncomputable abbrev qz157 := (@HMul.hMul Real Real Real qz268 qz438 qz567)

noncomputable def ep876 := @Enclosure.Complex.IsNear.of_eq qz635 (Complex.mk (@HMul.hMul Real Real Real qz0 qz33 (Real.cos qz157)) (@HMul.hMul Real Real Real qz0 qz33 (@Neg.neg Real Real.instNeg (Real.sin qz157)))) Bool.true 173833875305 549755813888 23311719406355 106387095836164096 Bool.true 4450919147 1099511627776 46423135752071 212774191672328192 (BSN.cpow_neg_s_mk qz146 132339 1000 10 qz147 rfl)

noncomputable def ep877 := @Enclosure.Real.IsNear.mulLit_ff qz146 qz567 132339 1000 0 1 10369917190100709 4503599627370496 1000000000580551 193517000000000000000 1372344471020737728351 4503599627370496000 132339000076829538789 193517000000000000000000 qz148 (BSN.isNear_log_sfrac 10 1 10369917190100709 4503599627370496 1000000000580551 193517000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz327) Bool.false 43494585150108164161536 18889465931478580854784 1000000000580551 193517000000000000000 10369917190100709 4503599627370496 1000000000580551 193517000000000000000 (BSN.log_rat_reduce_isNear 10 1 3 20 16 116991 524288 24973259072661432 36028797018963968 193517 1000000000000000 rfl rfl rfl rfl (ep186 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep878 := nat_lit 8074759097948956846160176153924339179500338528376157864139610638632716456755200

noncomputable def ep879 := nat_lit 15702395956528771021586429037677628985840995915236436620421919121457513824256

noncomputable def ep880 := nat_lit 21122755663079554682098845232312267404142858342836697318218297136889040459595776

noncomputable def ep881 := BSN.sin_dyadic_bound_f 3345767364 2147483648 3 2 1048576 387412 ep878 ep94 ep879 ep880 ep96 ep879 1048490 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3345767364) qz15 0 2 ep878 ep94 ep879 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3345767364) qz16 0 2 ep880 ep96 ep879 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz449 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 159761923) qz24)

noncomputable def ep882 := @Enclosure.Real.IsNear.cos_image qz157 qz449 Bool.false 159761923 524288 359 524288 Bool.true 1048490 1048576 1 193517 (@Enclosure.Real.IsNear.recentre' qz157 Bool.false 1372344471020737728351 4503599627370496000 132339000076829538789 193517000000000000000000 159761923 524288 359 524288 (ep877 rfl) rfl) (Enclosure.sfrac_false_div 159761923 524288) (BSN.cos_reduce1 qz449 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 117718723886237809115136) qz25) 226375608064910080 72057594037927936 Bool.false 1048490 1048576 48 1000000000000000 387034 193517 (BSN.sin_reduce_arg_pos_rat_q1 159761923 524288 226375608064910080 72057594037927936 48 117718723886237809115136 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1048490 1048576 117718723886237809115136 75557863725914323419136 3345767364 2147483648 387412 387034 (ep881 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep883 := nat_lit 4492956119285655479431914053974711823716117402837970563019971207738823593230336

noncomputable def ep884 := nat_lit 13447463565943908896252569303848780213176670216683438815819069784973555752042496

noncomputable def ep885 := BSN.cos_dyadic_bound_f 3345767364 2147483648 3 2 1048576 387412 ep883 ep62 ep879 ep884 ep65 ep879 13423 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3345767364) qz20 0 2 ep883 ep62 ep879 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3345767364) qz21 0 2 ep884 ep65 ep879 rfl rfl rfl rfl) rfl rfl

noncomputable def ep886 := @Enclosure.Real.IsNear.sin_image qz157 qz449 Bool.false 159761923 524288 359 524288 Bool.false 13423 1048576 1 193517 (@Enclosure.Real.IsNear.recentre' qz157 Bool.false 1372344471020737728351 4503599627370496000 132339000076829538789 193517000000000000000000 159761923 524288 359 524288 (ep877 rfl) rfl) (Enclosure.sfrac_false_div 159761923 524288) (BSN.sin_reduce1 qz449 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 117718723886237809115136) qz25) 226375608064910080 72057594037927936 Bool.false 13423 1048576 48 1000000000000000 387034 193517 (BSN.sin_reduce_arg_pos_rat_q1 159761923 524288 226375608064910080 72057594037927936 48 117718723886237809115136 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 13423 1048576 117718723886237809115136 75557863725914323419136 3345767364 2147483648 387412 387034 (ep885 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep887 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz33 (Real.cos qz157)) (@HMul.hMul Real Real Real qz0 qz33 (@Neg.neg Real Real.instNeg (Real.sin qz157))) Bool.true 173833875305 549755813888 23311719406355 106387095836164096 Bool.true 4450919147 1099511627776 46423135752071 212774191672328192 (@Enclosure.Real.IsNear.mulLit_ft qz33 (Real.cos qz157) 331589 1048576 1 1048576 524245 524288 69996891 101458640896 173833875305 549755813888 23311719406355 106387095836164096 qz329 (@Enclosure.Real.IsNear.recentre' (Real.cos qz157) Bool.true 1048490 1048576 69996891 101458640896 524245 524288 69996891 101458640896 (ep882 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz33 (@Neg.neg Real Real.instNeg (Real.sin qz157)) 331589 1048576 1 1048576 13423 1048576 69996891 101458640896 4450919147 1099511627776 46423135752071 212774191672328192 qz329 (@Enclosure.Real.IsNear.neg (Real.sin qz157) Bool.false 13423 1048576 69996891 101458640896 (@Enclosure.Real.IsNear.recentre' (Real.sin qz157) Bool.false 13423 1048576 69996891 101458640896 13423 1048576 69996891 101458640896 (ep886 rfl rfl) rfl)) rfl)

noncomputable def ep888 := @ep864 173833875305 549755813888 23311719406355 106387095836164096 Bool.true 4450919147 1099511627776 46423135752071 212774191672328192 Bool.false 840311361864657658707968 1528517462911 1099511627776 591482207623079 212774191672328192 Bool.false 126166698748014141374464 229495888103 1099511627776 591648399248611 212774191672328192 (ep865 (BSN.head_sum_c_succ qz143 9 10 rfl rfl) (ep875 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep876 ep887) rfl rfl

noncomputable abbrev qz158 := (@HMul.hMul Real Real Real qz268 qz438 qz568)

noncomputable def ep889 := @Enclosure.Complex.IsNear.of_eq qz634 (Complex.mk (@HMul.hMul Real Real Real qz0 qz35 (Real.cos qz158)) (@HMul.hMul Real Real Real qz0 qz35 (@Neg.neg Real Real.instNeg (Real.sin qz158)))) Bool.true 165660893331 549755813888 766602644241 3668520546074624 Bool.false 5648777119 549755813888 763225332173 3668520546074624 (BSN.cpow_neg_s_mk qz146 132339 1000 11 qz147 rfl)

noncomputable def ep890 := @Enclosure.Real.IsNear.mulLit_ff qz146 qz568 132339 1000 0 1 10799156221662949 4503599627370496 1000000000580551 193517000000000000000 1429149535218653007711 4503599627370496000 132339000076829538789 193517000000000000000000 qz148 (BSN.isNear_log_sfrac 11 1 10799156221662949 4503599627370496 1000000000580551 193517000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz330) Bool.false 45294944137145793642496 18889465931478580854784 1000000000580551 193517000000000000000 10799156221662949 4503599627370496 1000000000580551 193517000000000000000 (BSN.log_rat_reduce_isNear 11 1 3 22 16 166961 524288 24973259072661432 36028797018963968 193517 1000000000000000 rfl rfl rfl rfl (ep201 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep891 := BSN.cos_dyadic_bound_f 73198609 2147483648 1 0 1048576 387412 0 1 1 0 1 1 1047966 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 73198609) qz20 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 73198609) qz21 0 0 rfl) rfl rfl

noncomputable abbrev qz450 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 166374903) qz24)

noncomputable def ep892 := @Enclosure.Real.IsNear.cos_image qz158 qz450 Bool.false 166374903 524288 359 524288 Bool.true 1047966 1048576 1 193517 (@Enclosure.Real.IsNear.recentre' qz158 Bool.false 1429149535218653007711 4503599627370496000 132339000076829538789 193517000000000000000000 166374903 524288 359 524288 (ep890 rfl) rfl) (Enclosure.sfrac_false_div 166374903 524288) (BSN.cos_reduce2 qz450 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 2575447117890989326336) qz25) 226375608064910080 72057594037927936 Bool.false 1047966 1048576 50 1000000000000000 387034 193517 (BSN.sin_reduce_arg_pos_rat_q2 166374903 524288 226375608064910080 72057594037927936 50 2575447117890989326336 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1047966 1048576 2575447117890989326336 75557863725914323419136 73198609 2147483648 387412 387034 (ep891 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep893 := BSN.sin_dyadic_bound_f 73198609 2147483648 1 0 1048576 387412 0 1 1 0 1 1 35734 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 73198609) qz15 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 73198609) qz16 0 0 rfl) rfl rfl

noncomputable def ep894 := @Enclosure.Real.IsNear.sin_image qz158 qz450 Bool.false 166374903 524288 359 524288 Bool.true 35734 1048576 1 193517 (@Enclosure.Real.IsNear.recentre' qz158 Bool.false 1429149535218653007711 4503599627370496000 132339000076829538789 193517000000000000000000 166374903 524288 359 524288 (ep890 rfl) rfl) (Enclosure.sfrac_false_div 166374903 524288) (BSN.sin_reduce2 qz450 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 2575447117890989326336) qz25) 226375608064910080 72057594037927936 Bool.false 35734 1048576 50 1000000000000000 387034 193517 (BSN.sin_reduce_arg_pos_rat_q2 166374903 524288 226375608064910080 72057594037927936 50 2575447117890989326336 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 35734 1048576 2575447117890989326336 75557863725914323419136 73198609 2147483648 387412 387034 (ep893 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep895 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz35 (Real.cos qz158)) (@HMul.hMul Real Real Real qz0 qz35 (@Neg.neg Real Real.instNeg (Real.sin qz158))) Bool.true 165660893331 549755813888 766602644241 3668520546074624 Bool.false 5648777119 549755813888 763225332173 3668520546074624 (@Enclosure.Real.IsNear.mulLit_ft qz35 (Real.cos qz158) 316157 1048576 1 1048576 523983 524288 69996891 101458640896 165660893331 549755813888 766602644241 3668520546074624 qz332 (@Enclosure.Real.IsNear.recentre' (Real.cos qz158) Bool.true 1047966 1048576 69996891 101458640896 523983 524288 69996891 101458640896 (ep892 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz35 (@Neg.neg Real Real.instNeg (Real.sin qz158)) 316157 1048576 1 1048576 17867 524288 69996891 101458640896 5648777119 549755813888 763225332173 3668520546074624 qz332 (@Enclosure.Real.IsNear.neg (Real.sin qz158) Bool.true 17867 524288 69996891 101458640896 (@Enclosure.Real.IsNear.recentre' (Real.sin qz158) Bool.true 35734 1048576 69996891 101458640896 17867 524288 69996891 101458640896 (ep894 rfl rfl) rfl)) rfl)

noncomputable def ep896 := @ep862 165660893331 549755813888 766602644241 3668520546074624 Bool.false 5648777119 549755813888 763225332173 3668520546074624 Bool.false 658165283379463545946112 1197195676249 1099511627776 635945160989057 212774191672328192 Bool.false 132377594873069655031808 240793442341 1099511627776 635915468514645 212774191672328192 (ep863 (BSN.head_sum_c_succ qz143 10 11 rfl rfl) (ep888 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep889 ep895) rfl rfl

noncomputable abbrev qz159 := (@HMul.hMul Real Real Real qz268 qz438 qz569)

noncomputable def ep897 := @Enclosure.Complex.IsNear.of_eq qz633 (Complex.mk (@HMul.hMul Real Real Real qz0 qz37 (Real.cos qz159)) (@HMul.hMul Real Real Real qz0 qz37 (@Neg.neg Real Real.instNeg (Real.sin qz159)))) Bool.true 83424201291 549755813888 21241252777669 106387095836164096 Bool.true 135004375485 549755813888 21274228461503 106387095836164096 (BSN.cpow_neg_s_mk qz146 132339 1000 12 qz147 rfl)

noncomputable def ep898 := @Enclosure.Real.IsNear.mulLit_ff qz146 qz569 132339 1000 0 1 11191020447815397 4503599627370496 1000000000580551 193517000000000000000 1481008455043441823583 4503599627370496000 132339000076829538789 193517000000000000000000 qz148 (BSN.isNear_log_sfrac 12 1 11191020447815397 4503599627370496 1000000000580551 193517000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz333) Bool.false 46938541828353910898688 18889465931478580854784 1000000000580551 193517000000000000000 11191020447815397 4503599627370496 1000000000580551 193517000000000000000 (BSN.log_rat_reduce_isNear 12 1 3 24 16 212580 524288 24973259072661432 36028797018963968 193517 1000000000000000 rfl rfl rfl rfl (ep216 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep899 := nat_lit 1996195615409391618300246610335667216

noncomputable def ep900 := BSN.sin_dyadic_bound_f 1188641186 2147483648 2 1 1048576 387412 ep899 ep57 ep899 ep899 ep58 ep899 551206 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1188641186) qz15 0 1 ep899 ep57 ep899 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1188641186) qz16 0 1 ep899 ep58 ep899 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz451 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 344824151) qz17)

noncomputable def ep901 := @Enclosure.Real.IsNear.cos_image qz159 qz451 Bool.false 344824151 1048576 359 524288 Bool.true 551206 1048576 1 193517 (@Enclosure.Real.IsNear.recentre' qz159 Bool.false 1481008455043441823583 4503599627370496000 132339000076829538789 193517000000000000000000 344824151 1048576 359 524288 (ep898 rfl) rfl) (Enclosure.sfrac_false_div 344824151 1048576) (BSN.cos_reduce1 qz451 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 83643187587653883133952) qz19) 226375608064910080 72057594037927936 Bool.false 551206 1048576 52 1000000000000000 387034 193517 (BSN.sin_reduce_arg_pos_rat_q1 344824151 1048576 226375608064910080 72057594037927936 52 83643187587653883133952 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 551206 1048576 83643187587653883133952 151115727451828646838272 1188641186 2147483648 387412 387034 (ep900 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep902 := BSN.cos_dyadic_bound_f 1188641186 2147483648 2 1 1048576 387412 ep899 ep76 ep899 ep899 ep77 ep899 892010 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1188641186) qz20 0 1 ep899 ep76 ep899 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1188641186) qz21 0 1 ep899 ep77 ep899 rfl rfl rfl rfl) rfl rfl

noncomputable def ep903 := @Enclosure.Real.IsNear.sin_image qz159 qz451 Bool.false 344824151 1048576 359 524288 Bool.false 892010 1048576 1 193517 (@Enclosure.Real.IsNear.recentre' qz159 Bool.false 1481008455043441823583 4503599627370496000 132339000076829538789 193517000000000000000000 344824151 1048576 359 524288 (ep898 rfl) rfl) (Enclosure.sfrac_false_div 344824151 1048576) (BSN.sin_reduce1 qz451 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 83643187587653883133952) qz19) 226375608064910080 72057594037927936 Bool.false 892010 1048576 52 1000000000000000 387034 193517 (BSN.sin_reduce_arg_pos_rat_q1 344824151 1048576 226375608064910080 72057594037927936 52 83643187587653883133952 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 892010 1048576 83643187587653883133952 151115727451828646838272 1188641186 2147483648 387412 387034 (ep902 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep904 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz37 (Real.cos qz159)) (@HMul.hMul Real Real Real qz0 qz37 (@Neg.neg Real Real.instNeg (Real.sin qz159))) Bool.true 83424201291 549755813888 21241252777669 106387095836164096 Bool.true 135004375485 549755813888 21274228461503 106387095836164096 (@Enclosure.Real.IsNear.mulLit_ft qz37 (Real.cos qz159) 302697 1048576 1 1048576 275603 524288 69996891 101458640896 83424201291 549755813888 21241252777669 106387095836164096 qz335 (@Enclosure.Real.IsNear.recentre' (Real.cos qz159) Bool.true 551206 1048576 69996891 101458640896 275603 524288 69996891 101458640896 (ep901 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz37 (@Neg.neg Real Real.instNeg (Real.sin qz159)) 302697 1048576 1 1048576 446005 524288 69996891 101458640896 135004375485 549755813888 21274228461503 106387095836164096 qz335 (@Enclosure.Real.IsNear.neg (Real.sin qz159) Bool.false 446005 524288 69996891 101458640896 (@Enclosure.Real.IsNear.recentre' (Real.sin qz159) Bool.false 892010 1048576 69996891 101458640896 446005 524288 69996891 101458640896 (ep903 rfl rfl) rfl)) rfl)

noncomputable def ep905 := @ep860 83424201291 549755813888 21241252777669 106387095836164096 Bool.true 135004375485 549755813888 21274228461503 106387095836164096 Bool.false 566439404022083455287296 1030347273667 1099511627776 678427666544395 212774191672328192 Bool.true 16061285773325004439552 29215308629 1099511627776 678463925437651 212774191672328192 (ep861 (BSN.head_sum_c_succ qz143 11 12 rfl rfl) (ep896 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep897 ep904) rfl rfl

noncomputable abbrev qz160 := (@HMul.hMul Real Real Real qz268 qz438 qz570)

noncomputable def ep906 := @Enclosure.Complex.IsNear.of_eq qz632 (Complex.mk (@HMul.hMul Real Real Real qz0 qz39 (Real.cos qz160)) (@HMul.hMul Real Real Real qz0 qz39 (@Neg.neg Real Real.instNeg (Real.sin qz160)))) Bool.false 75374632671 274877906944 10228543069601 53193547918082048 Bool.true 357421467 8589934592 2546499637667 13298386979520512 (BSN.cpow_neg_s_mk qz146 132339 1000 13 qz147 rfl)

noncomputable def ep907 := @Enclosure.Real.IsNear.mulLit_ff qz146 qz570 132339 1000 0 1 11551497052968677 4503599627370496 1000000000580551 193517000000000000000 1528713568492821745503 4503599627370496000 132339000076829538789 193517000000000000000000 qz148 (BSN.isNear_log_sfrac 13 1 11551497052968677 4503599627370496 1000000000580551 193517000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz336) Bool.false 48450490295254733815808 18889465931478580854784 1000000000580551 193517000000000000000 11551497052968677 4503599627370496 1000000000580551 193517000000000000000 (BSN.log_rat_reduce_isNear 13 1 3 26 16 254545 524288 24973259072661432 36028797018963968 193517 1000000000000000 rfl rfl rfl rfl (ep227 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep908 := nat_lit 10938209598242826335767078364868241

noncomputable def ep909 := BSN.cos_dyadic_bound_f 323397427 2147483648 2 1 1048576 387412 ep908 ep76 ep908 ep908 ep77 ep908 1036708 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 323397427) qz20 0 1 ep908 ep76 ep908 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 323397427) qz21 0 1 ep908 ep77 ep908 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz452 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 88982841) qz566)

noncomputable def ep910 := @Enclosure.Real.IsNear.cos_image qz160 qz452 Bool.false 88982841 262144 359 524288 Bool.false 1036708 1048576 1 193517 (@Enclosure.Real.IsNear.recentre' qz160 Bool.false 1528713568492821745503 4503599627370496000 132339000076829538789 193517000000000000000000 88982841 262144 359 524288 (ep907 rfl) rfl) (Enclosure.sfrac_false_div 88982841 262144) (BSN.cos_reduce0 qz452 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 5689267716336786604032) qz325) 226375608064910080 72057594037927936 Bool.false 1036708 1048576 54 1000000000000000 387034 193517 (BSN.sin_reduce_arg_pos_rat_q0 88982841 262144 226375608064910080 72057594037927936 54 5689267716336786604032 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1036708 1048576 5689267716336786604032 37778931862957161709568 323397427 2147483648 387412 387034 (ep909 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep911 := BSN.sin_dyadic_bound_f 323397427 2147483648 2 1 1048576 387412 ep908 ep57 ep908 ep908 ep58 ep908 157312 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 323397427) qz15 0 1 ep908 ep57 ep908 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 323397427) qz16 0 1 ep908 ep58 ep908 rfl rfl rfl rfl) rfl rfl

noncomputable def ep912 := @Enclosure.Real.IsNear.sin_image qz160 qz452 Bool.false 88982841 262144 359 524288 Bool.false 157312 1048576 1 193517 (@Enclosure.Real.IsNear.recentre' qz160 Bool.false 1528713568492821745503 4503599627370496000 132339000076829538789 193517000000000000000000 88982841 262144 359 524288 (ep907 rfl) rfl) (Enclosure.sfrac_false_div 88982841 262144) (BSN.sin_reduce0 qz452 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 5689267716336786604032) qz325) 226375608064910080 72057594037927936 Bool.false 157312 1048576 54 1000000000000000 387034 193517 (BSN.sin_reduce_arg_pos_rat_q0 88982841 262144 226375608064910080 72057594037927936 54 5689267716336786604032 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 157312 1048576 5689267716336786604032 37778931862957161709568 323397427 2147483648 387412 387034 (ep911 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep913 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz39 (Real.cos qz160)) (@HMul.hMul Real Real Real qz0 qz39 (@Neg.neg Real Real.instNeg (Real.sin qz160))) Bool.false 75374632671 274877906944 10228543069601 53193547918082048 Bool.true 357421467 8589934592 2546499637667 13298386979520512 (@Enclosure.Real.IsNear.mulLit_ff qz39 (Real.cos qz160) 290823 1048576 1 1048576 259177 262144 69996891 101458640896 75374632671 274877906944 10228543069601 53193547918082048 qz338 (@Enclosure.Real.IsNear.recentre' (Real.cos qz160) Bool.false 1036708 1048576 69996891 101458640896 259177 262144 69996891 101458640896 (ep910 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz39 (@Neg.neg Real Real.instNeg (Real.sin qz160)) 290823 1048576 1 1048576 1229 8192 69996891 101458640896 357421467 8589934592 2546499637667 13298386979520512 qz338 (@Enclosure.Real.IsNear.neg (Real.sin qz160) Bool.false 1229 8192 69996891 101458640896 (@Enclosure.Real.IsNear.recentre' (Real.sin qz160) Bool.false 157312 1048576 69996891 101458640896 1229 8192 69996891 101458640896 (ep912 rfl rfl) rfl)) rfl)

noncomputable def ep914 := @ep858 75374632671 274877906944 10228543069601 53193547918082048 Bool.true 357421467 8589934592 2546499637667 13298386979520512 Bool.false 366094987072151008313344 1331845804351 1099511627776 719341838822799 212774191672328192 Bool.true 643946649191459061760 74965256405 1099511627776 719207919640323 212774191672328192 (ep859 (BSN.head_sum_c_succ qz143 12 13 rfl rfl) (ep905 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep906 ep913) rfl rfl

noncomputable abbrev qz161 := (@HMul.hMul Real Real Real qz268 qz438 qz571)

noncomputable def ep915 := @Enclosure.Complex.IsNear.of_eq qz631 (Complex.mk (@HMul.hMul Real Real Real qz0 qz41 (Real.cos qz161)) (@HMul.hMul Real Real Real qz0 qz41 (@Neg.neg Real Real.instNeg (Real.sin qz161)))) Bool.true 63265697979 274877906944 9851791404003 53193547918082048 Bool.false 291732963 2147483648 4916945056959 26596773959041024 (BSN.cpow_neg_s_mk qz146 132339 1000 14 qz147 rfl)

noncomputable def ep916 := @Enclosure.Real.IsNear.mulLit_ff qz146 qz571 132339 1000 0 1 11885250371606245 4503599627370496 1000000000580551 193517000000000000000 314576429785599771411 900719925474099200 132339000076829538789 193517000000000000000000 qz148 (BSN.isNear_log_sfrac 14 1 11885250371606245 4503599627370496 1000000000580551 193517000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz339) Bool.false 49850353174629559828480 18889465931478580854784 1000000000580551 193517000000000000000 11885250371606245 4503599627370496 1000000000580551 193517000000000000000 (BSN.log_rat_reduce_isNear 14 1 3 28 16 293399 524288 24973259072661432 36028797018963968 193517 1000000000000000 rfl rfl rfl rfl (ep242 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep917 := nat_lit 1719154193277166332651845286841321441

noncomputable def ep918 := BSN.cos_dyadic_bound_f 1145061223 2147483648 2 1 1048576 387412 ep917 ep76 ep917 ep917 ep77 ep917 903012 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1145061223) qz20 0 1 ep917 ep76 ep917 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1145061223) qz21 0 1 ep917 ep77 ep917 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz453 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 366215163) qz17)

noncomputable def ep919 := @Enclosure.Real.IsNear.cos_image qz161 qz453 Bool.false 366215163 1048576 359 524288 Bool.true 903012 1048576 1 193517 (@Enclosure.Real.IsNear.recentre' qz161 Bool.false 314576429785599771411 900719925474099200 132339000076829538789 193517000000000000000000 366215163 1048576 359 524288 (ep916 rfl) rfl) (Enclosure.sfrac_false_div 366215163 1048576) (BSN.cos_reduce2 qz453 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 80576520271018774757376) qz19) 226375608064910080 72057594037927936 Bool.false 903012 1048576 55 1000000000000000 387034 193517 (BSN.sin_reduce_arg_pos_rat_q2 366215163 1048576 226375608064910080 72057594037927936 55 80576520271018774757376 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 903012 1048576 80576520271018774757376 151115727451828646838272 1145061223 2147483648 387412 387034 (ep918 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep920 := BSN.sin_dyadic_bound_f 1145061223 2147483648 2 1 1048576 387412 ep917 ep57 ep917 ep917 ep58 ep917 532992 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1145061223) qz15 0 1 ep917 ep57 ep917 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1145061223) qz16 0 1 ep917 ep58 ep917 rfl rfl rfl rfl) rfl rfl

noncomputable def ep921 := @Enclosure.Real.IsNear.sin_image qz161 qz453 Bool.false 366215163 1048576 359 524288 Bool.true 532992 1048576 1 193517 (@Enclosure.Real.IsNear.recentre' qz161 Bool.false 314576429785599771411 900719925474099200 132339000076829538789 193517000000000000000000 366215163 1048576 359 524288 (ep916 rfl) rfl) (Enclosure.sfrac_false_div 366215163 1048576) (BSN.sin_reduce2 qz453 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 80576520271018774757376) qz19) 226375608064910080 72057594037927936 Bool.false 532992 1048576 55 1000000000000000 387034 193517 (BSN.sin_reduce_arg_pos_rat_q2 366215163 1048576 226375608064910080 72057594037927936 55 80576520271018774757376 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 532992 1048576 80576520271018774757376 151115727451828646838272 1145061223 2147483648 387412 387034 (ep920 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep922 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz41 (Real.cos qz161)) (@HMul.hMul Real Real Real qz0 qz41 (@Neg.neg Real Real.instNeg (Real.sin qz161))) Bool.true 63265697979 274877906944 9851791404003 53193547918082048 Bool.false 291732963 2147483648 4916945056959 26596773959041024 (@Enclosure.Real.IsNear.mulLit_ft qz41 (Real.cos qz161) 280243 1048576 1 1048576 225753 262144 69996891 101458640896 63265697979 274877906944 9851791404003 53193547918082048 qz341 (@Enclosure.Real.IsNear.recentre' (Real.cos qz161) Bool.true 903012 1048576 69996891 101458640896 225753 262144 69996891 101458640896 (ep919 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz41 (@Neg.neg Real Real.instNeg (Real.sin qz161)) 280243 1048576 1 1048576 1041 2048 69996891 101458640896 291732963 2147483648 4916945056959 26596773959041024 qz341 (@Enclosure.Real.IsNear.neg (Real.sin qz161) Bool.true 1041 2048 69996891 101458640896 (@Enclosure.Real.IsNear.recentre' (Real.sin qz161) Bool.true 532992 1048576 69996891 101458640896 1041 2048 69996891 101458640896 (ep921 rfl rfl) rfl)) rfl)

noncomputable def ep923 := @ep856 63265697979 274877906944 9851791404003 53193547918082048 Bool.false 291732963 2147483648 4916945056959 26596773959041024 Bool.false 296533616504875924848640 1078783012435 1099511627776 758749004438811 212774191672328192 Bool.false 159777122726180814848 74402020651 1099511627776 758543480095995 212774191672328192 (ep857 (BSN.head_sum_c_succ qz143 13 14 rfl rfl) (ep914 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep915 ep922) rfl rfl

noncomputable abbrev qz162 := (@HMul.hMul Real Real Real qz268 qz438 qz572)

noncomputable def ep924 := @Enclosure.Complex.IsNear.of_eq qz630 (Complex.mk (@HMul.hMul Real Real Real qz0 qz43 (Real.cos qz162)) (@HMul.hMul Real Real Real qz0 qz43 (@Neg.neg Real Real.instNeg (Real.sin qz162)))) Bool.false 34479137091 137438953472 9524838298495 53193547918082048 Bool.true 67163532093 1099511627776 37950202868985 212774191672328192 (BSN.cpow_neg_s_mk qz146 132339 1000 15 qz147 rfl)

noncomputable def ep925 := @Enclosure.Real.IsNear.mulLit_ff qz146 qz572 132339 1000 0 1 12195965485668069 4503599627370496 1000000000580551 193517000000000000000 1614001876407826583391 4503599627370496000 132339000076829538789 193517000000000000000000 qz148 (BSN.isNear_log_sfrac 15 1 12195965485668069 4503599627370496 1000000000580551 193517000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz342) Bool.false 51153586820399524478976 18889465931478580854784 1000000000580551 193517000000000000000 12195965485668069 4503599627370496 1000000000580551 193517000000000000000 (BSN.log_rat_reduce_isNear 15 1 3 30 16 329571 524288 24973259072661432 36028797018963968 193517 1000000000000000 rfl rfl rfl rfl (ep257 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep926 := nat_lit 69213328530312340205036895551596816

noncomputable def ep927 := BSN.cos_dyadic_bound_f 512917402 2147483648 2 1 1048576 387412 ep926 ep76 ep926 ep926 ep77 ep926 1018808 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 512917402) qz20 0 1 ep926 ep76 ep926 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 512917402) qz21 0 1 ep926 ep77 ep926 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz454 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 375789095) qz17)

noncomputable def ep928 := @Enclosure.Real.IsNear.cos_image qz162 qz454 Bool.false 375789095 1048576 359 524288 Bool.false 1018808 1048576 1 193517 (@Enclosure.Real.IsNear.recentre' qz162 Bool.false 1614001876407826583391 4503599627370496000 132339000076829538789 193517000000000000000000 375789095 1048576 359 524288 (ep925 rfl) rfl) (Enclosure.sfrac_false_div 375789095 1048576) (BSN.cos_reduce0 qz454 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 36093353462846822809600) qz19) 226375608064910080 72057594037927936 Bool.false 1018808 1048576 57 1000000000000000 387034 193517 (BSN.sin_reduce_arg_pos_rat_q0 375789095 1048576 226375608064910080 72057594037927936 57 36093353462846822809600 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1018808 1048576 36093353462846822809600 151115727451828646838272 512917402 2147483648 387412 387034 (ep927 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep929 := BSN.sin_dyadic_bound_f 512917402 2147483648 2 1 1048576 387412 ep926 ep57 ep926 ep926 ep58 ep926 248073 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 512917402) qz15 0 1 ep926 ep57 ep926 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 512917402) qz16 0 1 ep926 ep58 ep926 rfl rfl rfl rfl) rfl rfl

noncomputable def ep930 := @Enclosure.Real.IsNear.sin_image qz162 qz454 Bool.false 375789095 1048576 359 524288 Bool.false 248073 1048576 1 193517 (@Enclosure.Real.IsNear.recentre' qz162 Bool.false 1614001876407826583391 4503599627370496000 132339000076829538789 193517000000000000000000 375789095 1048576 359 524288 (ep925 rfl) rfl) (Enclosure.sfrac_false_div 375789095 1048576) (BSN.sin_reduce0 qz454 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 36093353462846822809600) qz19) 226375608064910080 72057594037927936 Bool.false 248073 1048576 57 1000000000000000 387034 193517 (BSN.sin_reduce_arg_pos_rat_q0 375789095 1048576 226375608064910080 72057594037927936 57 36093353462846822809600 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 248073 1048576 36093353462846822809600 151115727451828646838272 512917402 2147483648 387412 387034 (ep929 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep931 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz43 (Real.cos qz162)) (@HMul.hMul Real Real Real qz0 qz43 (@Neg.neg Real Real.instNeg (Real.sin qz162))) Bool.false 34479137091 137438953472 9524838298495 53193547918082048 Bool.true 67163532093 1099511627776 37950202868985 212774191672328192 (@Enclosure.Real.IsNear.mulLit_ff qz43 (Real.cos qz162) 270741 1048576 1 1048576 127351 131072 69996891 101458640896 34479137091 137438953472 9524838298495 53193547918082048 qz344 (@Enclosure.Real.IsNear.recentre' (Real.cos qz162) Bool.false 1018808 1048576 69996891 101458640896 127351 131072 69996891 101458640896 (ep928 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz43 (@Neg.neg Real Real.instNeg (Real.sin qz162)) 270741 1048576 1 1048576 248073 1048576 69996891 101458640896 67163532093 1099511627776 37950202868985 212774191672328192 qz344 (@Enclosure.Real.IsNear.neg (Real.sin qz162) Bool.false 248073 1048576 69996891 101458640896 (@Enclosure.Real.IsNear.recentre' (Real.sin qz162) Bool.false 248073 1048576 69996891 101458640896 248073 1048576 69996891 101458640896 (ep930 rfl rfl) rfl)) rfl)

noncomputable def ep932 := @ep854 34479137091 137438953472 9524838298495 53193547918082048 Bool.true 67163532093 1099511627776 37950202868985 212774191672328192 Bool.false 186177020399675229863936 1354616109163 1099511627776 796848357632791 212774191672328192 Bool.false 7958802337044530987008 3619244279 549755813888 199123420741245 53193547918082048 (ep855 (BSN.head_sum_c_succ qz143 14 15 rfl rfl) (ep923 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep924 ep931) rfl rfl

noncomputable abbrev qz163 := (@HMul.hMul Real Real Real qz268 qz438 qz573)

noncomputable def ep933 := @Enclosure.Complex.IsNear.of_eq qz629 (Complex.mk (@HMul.hMul Real Real Real qz0 qz45 (Real.cos qz163)) (@HMul.hMul Real Real Real qz0 qz45 (@Neg.neg Real Real.instNeg (Real.sin qz163)))) Bool.true 54924987789 274877906944 9215178759543 53193547918082048 Bool.true 165194392167 1099511627776 36820478402981 212774191672328192 (BSN.cpow_neg_s_mk qz146 132339 1000 16 qz147 rfl)

noncomputable def ep934 := @Enclosure.Real.IsNear.mulLit_ff qz146 qz573 132339 1000 0 1 3121657384082679 1125899906842624 250000000193517 48379250000000000000 413117016552117656181 1125899906842624000 33084750025609846263 48379250000000000000000 qz148 (BSN.isNear_log_sfrac 16 1 3121657384082679 1125899906842624 250000000193517 48379250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz345) Bool.false 52372720210750067441664 18889465931478580854784 1000000000774068 193517000000000000000 3121657384082679 1125899906842624 250000000193517 48379250000000000000 (BSN.log_rat_reduce_isNear 16 1 4 32 32 0 524288 24973259072661432 36028797018963968 193517 1000000000000000 rfl rfl rfl rfl (ep272 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep935 := nat_lit 1006258797650985392479572889417500128308953078192424804526844934937672839530625

noncomputable def ep936 := nat_lit 244684043536839394845518162748542245203835320354306092302433218871062890625

noncomputable def ep937 := nat_lit 2635043553015425906997702919068050315269308995223396087706580413910970954090625

noncomputable def ep938 := BSN.sin_dyadic_bound_f 1988729455 2147483648 3 2 1048576 387412 ep935 ep94 ep936 ep937 ep96 ep936 838092 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1988729455) qz15 0 2 ep935 ep94 ep936 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1988729455) qz16 0 2 ep937 ep96 ep936 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz455 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 384745203) qz17)

noncomputable def ep939 := @Enclosure.Real.IsNear.cos_image qz163 qz455 Bool.false 384745203 1048576 359 524288 Bool.true 838092 1048576 1 193517 (@Enclosure.Real.IsNear.recentre' qz163 Bool.false 413117016552117656181 1125899906842624000 33084750025609846263 48379250000000000000000 384745203 1048576 359 524288 (ep934 rfl) rfl) (Enclosure.sfrac_false_div 384745203 1048576) (BSN.cos_reduce1 qz455 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 139944394299168444645376) qz19) 226375608064910080 72057594037927936 Bool.false 838092 1048576 58 1000000000000000 387034 193517 (BSN.sin_reduce_arg_pos_rat_q1 384745203 1048576 226375608064910080 72057594037927936 58 139944394299168444645376 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 838092 1048576 139944394299168444645376 151115727451828646838272 1988729455 2147483648 387412 387034 (ep938 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep940 := nat_lit 559141413825452702219694057748721645613953414693726805222603823062649827690625

noncomputable def ep941 := nat_lit 1676934873389284427869391136920667852351452573440471803483206602750207357290625

noncomputable def ep942 := BSN.cos_dyadic_bound_f 1988729455 2147483648 3 2 1048576 387412 ep940 ep62 ep936 ep941 ep65 ep936 630169 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1988729455) qz20 0 2 ep940 ep62 ep936 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1988729455) qz21 0 2 ep941 ep65 ep936 rfl rfl rfl rfl) rfl rfl

noncomputable def ep943 := @Enclosure.Real.IsNear.sin_image qz163 qz455 Bool.false 384745203 1048576 359 524288 Bool.false 630169 1048576 1 193517 (@Enclosure.Real.IsNear.recentre' qz163 Bool.false 413117016552117656181 1125899906842624000 33084750025609846263 48379250000000000000000 384745203 1048576 359 524288 (ep934 rfl) rfl) (Enclosure.sfrac_false_div 384745203 1048576) (BSN.sin_reduce1 qz455 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 139944394299168444645376) qz19) 226375608064910080 72057594037927936 Bool.false 630169 1048576 58 1000000000000000 387034 193517 (BSN.sin_reduce_arg_pos_rat_q1 384745203 1048576 226375608064910080 72057594037927936 58 139944394299168444645376 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 630169 1048576 139944394299168444645376 151115727451828646838272 1988729455 2147483648 387412 387034 (ep942 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep944 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz45 (Real.cos qz163)) (@HMul.hMul Real Real Real qz0 qz45 (@Neg.neg Real Real.instNeg (Real.sin qz163))) Bool.true 54924987789 274877906944 9215178759543 53193547918082048 Bool.true 165194392167 1099511627776 36820478402981 212774191672328192 (@Enclosure.Real.IsNear.mulLit_ft qz45 (Real.cos qz163) 262143 1048576 1 1048576 209523 262144 69996891 101458640896 54924987789 274877906944 9215178759543 53193547918082048 qz347 (@Enclosure.Real.IsNear.recentre' (Real.cos qz163) Bool.true 838092 1048576 69996891 101458640896 209523 262144 69996891 101458640896 (ep939 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz45 (@Neg.neg Real Real.instNeg (Real.sin qz163)) 262143 1048576 1 1048576 630169 1048576 69996891 101458640896 165194392167 1099511627776 36820478402981 212774191672328192 qz347 (@Enclosure.Real.IsNear.neg (Real.sin qz163) Bool.false 630169 1048576 69996891 101458640896 (@Enclosure.Real.IsNear.recentre' (Real.sin qz163) Bool.false 630169 1048576 69996891 101458640896 630169 1048576 69996891 101458640896 (ep943 rfl rfl) rfl)) rfl)

noncomputable def ep945 := @ep852 54924987789 274877906944 9215178759543 53193547918082048 Bool.true 165194392167 1099511627776 36820478402981 212774191672328192 Bool.false 311963378069890146500608 1134916158007 1099511627776 833709072670963 212774191672328192 Bool.true 86837176346980271521792 157955903609 1099511627776 833314161367961 212774191672328192 (ep853 (BSN.head_sum_c_succ qz143 15 16 rfl rfl) (ep932 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep933 ep944) rfl rfl

theorem EMRow44.d14 : Enclosure.Complex.IsNear qz155 Bool.false 1134916158007 1099511627776 833709072670963 212774191672328192 Bool.true 157955903609 1099511627776 833314161367961 212774191672328192 := ep851 (BSN.head_sum_c_succ qz143 16 17 rfl rfl) (ep945 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable abbrev qz164 := (BSN.headSumC qz436 25)

noncomputable abbrev qz637 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 24) qz144)

noncomputable def ep946 := @Enclosure.Complex.IsNear.of_eq qz164 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz143 24) qz637) Bool.false 2435906542585 1099511627776 1095754620302167 212774191672328192 Bool.true 194796793641 1099511627776 1094920745486283 212774191672328192

noncomputable def ep947 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz143 24) qz637 Bool.false 139286679307 68719476736 266400727320517 53193547918082048 Bool.true 280762561445 1099511627776 1064878752993191 212774191672328192 Bool.false

noncomputable abbrev qz638 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 23) qz144)

noncomputable def ep948 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz143 24) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz143 23) qz638) Bool.false 139286679307 68719476736 266400727320517 53193547918082048 Bool.true 280762561445 1099511627776 1064878752993191 212774191672328192

noncomputable def ep949 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz143 23) qz638 Bool.false 1003446462245 549755813888 517398945737121 106387095836164096 Bool.true 13896007691 68719476736 258554560082073 53193547918082048 Bool.false

noncomputable abbrev qz639 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 22) qz144)

noncomputable def ep950 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz143 23) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz143 22) qz639) Bool.false 1003446462245 549755813888 517398945737121 106387095836164096 Bool.true 13896007691 68719476736 258554560082073 53193547918082048

noncomputable def ep951 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz143 22) qz639 Bool.false 910731114749 549755813888 501670323860567 106387095836164096 Bool.true 78925872455 1099511627776 1002797370611055 212774191672328192 Bool.false

noncomputable abbrev qz640 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 21) qz144)

noncomputable def ep952 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz143 22) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz143 21) qz640) Bool.false 910731114749 549755813888 501670323860567 106387095836164096 Bool.true 78925872455 1099511627776 1002797370611055 212774191672328192

noncomputable def ep953 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz143 21) qz640 Bool.false 412936121657 274877906944 121377525200073 26596773959041024 Bool.false 90672656237 1099511627776 970477126135219 212774191672328192 Bool.false

noncomputable abbrev qz641 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 20) qz144)

noncomputable def ep954 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz143 21) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz143 20) qz641) Bool.false 412936121657 274877906944 121377525200073 26596773959041024 Bool.false 90672656237 1099511627776 970477126135219 212774191672328192

noncomputable def ep955 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz143 20) qz641 Bool.false 1450426824069 1099511627776 938029703710157 212774191672328192 Bool.false 7243816453 34359738368 234384076014673 53193547918082048 Bool.false

noncomputable def ep956 := nat_lit 1816112269162385745379328

noncomputable abbrev qz642 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 19) qz144)

noncomputable def ep957 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz143 20) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz143 19) qz642) Bool.false 1450426824069 1099511627776 938029703710157 212774191672328192 Bool.false 7243816453 34359738368 234384076014673 53193547918082048

noncomputable def ep958 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz143 19) qz642 Bool.false 1199614718371 1099511627776 904151034430663 212774191672328192 Bool.false 64660924929 274877906944 112979725904239 26596773959041024 Bool.false

noncomputable abbrev qz643 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 18) qz144)

noncomputable def ep959 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz143 19) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz143 18) qz643) Bool.false 1199614718371 1099511627776 904151034430663 212774191672328192 Bool.false 64660924929 274877906944 112979725904239 26596773959041024

noncomputable def ep960 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz143 18) qz643 Bool.false 63296598583 68719476736 434702487186359 106387095836164096 Bool.false 79083308045 1099511627776 869097469860691 212774191672328192 Bool.false

noncomputable abbrev qz644 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 17) qz144)

noncomputable def ep961 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz143 18) (@HAdd.hAdd Complex Complex Complex qz4 qz155 qz644) Bool.false 63296598583 68719476736 434702487186359 106387095836164096 Bool.false 79083308045 1099511627776 869097469860691 212774191672328192

noncomputable def ep962 := @Enclosure.Complex.IsNear.addLitP qz155 qz644 Bool.false 1134916158007 1099511627776 833709072670963 212774191672328192 Bool.true 157955903609 1099511627776 833314161367961 212774191672328192 Bool.true

noncomputable abbrev qz165 := (@HMul.hMul Real Real Real qz268 qz438 qz582)

noncomputable def ep963 := @Enclosure.Complex.IsNear.of_eq qz644 (Complex.mk (@HMul.hMul Real Real Real qz0 qz48 (Real.cos qz165)) (@HMul.hMul Real Real Real qz0 qz48 (@Neg.neg Real Real.instNeg (Real.sin qz165)))) Bool.true 122170580679 1099511627776 35695901701755 212774191672328192 Bool.false 118519605827 549755813888 17891654246365 106387095836164096 (BSN.cpow_neg_s_mk qz146 132339 1000 17 qz147 rfl)

noncomputable def ep964 := @Enclosure.Real.IsNear.mulLit_ff qz146 qz582 132339 1000 0 1 3189913004350711 1125899906842624 250000000193517 48379250000000000000 422149897082768743029 1125899906842624000 33084750025609846263 48379250000000000000000 qz148 (BSN.isNear_log_sfrac 17 1 3189913004350711 1125899906842624 250000000193517 48379250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz348) Bool.false 53517859495200818200576 18889465931478580854784 1000000000774068 193517000000000000000 3189913004350711 1125899906842624 250000000193517 48379250000000000000 (BSN.log_rat_reduce_isNear 17 1 4 34 32 31784 524288 24973259072661432 36028797018963968 193517 1000000000000000 rfl rfl rfl rfl (ep303 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep965 := nat_lit 1093003661019818149506933213974114668715301866532293390751378154892327104086016

noncomputable def ep966 := nat_lit 934206815829311086663727000619131073742532278775135359939494009446282100736

noncomputable def ep967 := nat_lit 3277142569427795826347472187921105743998420535039329901534255476658088748056576

noncomputable def ep968 := BSN.cos_dyadic_bound_f 2351285572 2147483648 3 2 1048576 387412 ep965 ep62 ep966 ep967 ep65 ep966 480387 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2351285572) qz20 0 2 ep965 ep62 ep966 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2351285572) qz21 0 2 ep967 ep65 ep966 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz456 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 393157729) qz17)

noncomputable def ep969 := @Enclosure.Real.IsNear.cos_image qz165 qz456 Bool.false 393157729 1048576 359 524288 Bool.true 480387 1048576 1 193517 (@Enclosure.Real.IsNear.recentre' qz165 Bool.false 422149897082768743029 1125899906842624000 33084750025609846263 48379250000000000000000 393157729 1048576 359 524288 (ep964 rfl) rfl) (Enclosure.sfrac_false_div 393157729 1048576) (BSN.cos_reduce2 qz456 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 165457012970840179867648) qz19) 226375608064910080 72057594037927936 Bool.false 480387 1048576 59 1000000000000000 387034 193517 (BSN.sin_reduce_arg_pos_rat_q2 393157729 1048576 226375608064910080 72057594037927936 59 165457012970840179867648 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 480387 1048576 165457012970840179867648 151115727451828646838272 2351285572 2147483648 387412 387034 (ep968 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep970 := nat_lit 1966659224383009220243148803552911098828549333935107995064529083598631761674240

noncomputable def ep971 := nat_lit 5149261633777490977925077022732812379955379393759646910776721752457313014317056

noncomputable def ep972 := BSN.sin_dyadic_bound_f 2351285572 2147483648 3 2 1048576 387412 ep970 ep94 ep966 ep971 ep96 ep966 932062 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2351285572) qz15 0 2 ep970 ep94 ep966 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2351285572) qz16 0 2 ep971 ep96 ep966 rfl rfl rfl rfl) rfl rfl

noncomputable def ep973 := @Enclosure.Real.IsNear.sin_image qz165 qz456 Bool.false 393157729 1048576 359 524288 Bool.true 932062 1048576 1 193517 (@Enclosure.Real.IsNear.recentre' qz165 Bool.false 422149897082768743029 1125899906842624000 33084750025609846263 48379250000000000000000 393157729 1048576 359 524288 (ep964 rfl) rfl) (Enclosure.sfrac_false_div 393157729 1048576) (BSN.sin_reduce2 qz456 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 165457012970840179867648) qz19) 226375608064910080 72057594037927936 Bool.false 932062 1048576 59 1000000000000000 387034 193517 (BSN.sin_reduce_arg_pos_rat_q2 393157729 1048576 226375608064910080 72057594037927936 59 165457012970840179867648 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 932062 1048576 165457012970840179867648 151115727451828646838272 2351285572 2147483648 387412 387034 (ep972 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep974 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz48 (Real.cos qz165)) (@HMul.hMul Real Real Real qz0 qz48 (@Neg.neg Real Real.instNeg (Real.sin qz165))) Bool.true 122170580679 1099511627776 35695901701755 212774191672328192 Bool.false 118519605827 549755813888 17891654246365 106387095836164096 (@Enclosure.Real.IsNear.mulLit_ft qz48 (Real.cos qz165) 254317 1048576 1 1048576 480387 1048576 69996891 101458640896 122170580679 1099511627776 35695901701755 212774191672328192 qz350 (@Enclosure.Real.IsNear.recentre' (Real.cos qz165) Bool.true 480387 1048576 69996891 101458640896 480387 1048576 69996891 101458640896 (ep969 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz48 (@Neg.neg Real Real.instNeg (Real.sin qz165)) 254317 1048576 1 1048576 466031 524288 69996891 101458640896 118519605827 549755813888 17891654246365 106387095836164096 qz350 (@Enclosure.Real.IsNear.neg (Real.sin qz165) Bool.true 466031 524288 69996891 101458640896 (@Enclosure.Real.IsNear.recentre' (Real.sin qz165) Bool.true 932062 1048576 69996891 101458640896 466031 524288 69996891 101458640896 (ep973 rfl rfl) rfl)) rfl)

noncomputable def ep975 := @ep962 122170580679 1099511627776 35695901701755 212774191672328192 Bool.false 118519605827 549755813888 17891654246365 106387095836164096 Bool.false 1113525538250854160662528 63296598583 68719476736 434702487186359 106387095836164096 Bool.false 43476508379234393128960 79083308045 1099511627776 869097469860691 212774191672328192 EMRow44.d14 (ep963 ep974) rfl rfl

noncomputable abbrev qz166 := (@HMul.hMul Real Real Real qz268 qz438 qz583)

noncomputable def ep976 := @Enclosure.Complex.IsNear.of_eq qz643 (Complex.mk (@HMul.hMul Real Real Real qz0 qz50 (Real.cos qz166)) (@HMul.hMul Real Real Real qz0 qz50 (@Neg.neg Real Real.instNeg (Real.sin qz166)))) Bool.false 186869141043 1099511627776 34746060057945 212774191672328192 Bool.false 179560391671 1099511627776 34740337373221 212774191672328192 (BSN.cpow_neg_s_mk qz146 132339 1000 18 qz147 rfl)

noncomputable def ep977 := @Enclosure.Real.IsNear.mulLit_ff qz146 qz583 132339 1000 0 1 3254268794313975 1125899906842624 250000000193517 48379250000000000000 17226667118828685501 45035996273704960 33084750025609846263 48379250000000000000000 qz148 (BSN.isNear_log_sfrac 18 1 3254268794313975 1125899906842624 250000000193517 48379250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz351) Bool.false 54597570484265130393600 18889465931478580854784 1000000000774068 193517000000000000000 3254268794313975 1125899906842624 250000000193517 48379250000000000000 (BSN.log_rat_reduce_isNear 18 1 4 36 32 61752 524288 24973259072661432 36028797018963968 193517 1000000000000000 rfl rfl rfl rfl (ep318 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep978 := nat_lit 8946234573345140976442341289020422416

noncomputable def ep979 := BSN.sin_dyadic_bound_f 1729458202 2147483648 2 1 1048576 387412 ep978 ep57 ep978 ep978 ep58 ep978 756093 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1729458202) qz15 0 1 ep978 ep57 ep978 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1729458202) qz16 0 1 ep978 ep58 ep978 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz457 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 401089599) qz17)

noncomputable def ep980 := @Enclosure.Real.IsNear.cos_image qz166 qz457 Bool.false 401089599 1048576 359 524288 Bool.false 756093 1048576 1 193517 (@Enclosure.Real.IsNear.recentre' qz166 Bool.false 17226667118828685501 45035996273704960 33084750025609846263 48379250000000000000000 401089599 1048576 359 524288 (ep977 rfl) rfl) (Enclosure.sfrac_false_div 401089599 1048576) (BSN.cos_reduce3 qz457 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 121699801802723335077888) qz19) 226375608064910080 72057594037927936 Bool.false 756093 1048576 60 1000000000000000 387034 193517 (BSN.sin_reduce_arg_pos_rat_q3 401089599 1048576 226375608064910080 72057594037927936 60 121699801802723335077888 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 756093 1048576 121699801802723335077888 151115727451828646838272 1729458202 2147483648 387412 387034 (ep979 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep981 := nat_lit 319725852056062061838409147891269968833899234004464619051944022510985767035136

noncomputable def ep982 := nat_lit 80035113041315916601134026655419349426797655905153284908636285523075277056

noncomputable def ep983 := nat_lit 959017485942103553682025175620499067802844106701583550586014794961911150551296

noncomputable def ep984 := BSN.cos_dyadic_bound_f 1729458202 2147483648 3 2 1048576 387412 ep981 ep62 ep982 ep983 ep65 ep982 726521 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1729458202) qz20 0 2 ep981 ep62 ep982 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1729458202) qz21 0 2 ep983 ep65 ep982 rfl rfl rfl rfl) rfl rfl

noncomputable def ep985 := @Enclosure.Real.IsNear.sin_image qz166 qz457 Bool.false 401089599 1048576 359 524288 Bool.true 726521 1048576 1 193517 (@Enclosure.Real.IsNear.recentre' qz166 Bool.false 17226667118828685501 45035996273704960 33084750025609846263 48379250000000000000000 401089599 1048576 359 524288 (ep977 rfl) rfl) (Enclosure.sfrac_false_div 401089599 1048576) (BSN.sin_reduce3 qz457 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 121699801802723335077888) qz19) 226375608064910080 72057594037927936 Bool.false 726521 1048576 60 1000000000000000 387034 193517 (BSN.sin_reduce_arg_pos_rat_q3 401089599 1048576 226375608064910080 72057594037927936 60 121699801802723335077888 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 726521 1048576 121699801802723335077888 151115727451828646838272 1729458202 2147483648 387412 387034 (ep984 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep986 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz50 (Real.cos qz166)) (@HMul.hMul Real Real Real qz0 qz50 (@Neg.neg Real Real.instNeg (Real.sin qz166))) Bool.false 186869141043 1099511627776 34746060057945 212774191672328192 Bool.false 179560391671 1099511627776 34740337373221 212774191672328192 (@Enclosure.Real.IsNear.mulLit_ff qz50 (Real.cos qz166) 247151 1048576 1 1048576 756093 1048576 69996891 101458640896 186869141043 1099511627776 34746060057945 212774191672328192 qz353 (@Enclosure.Real.IsNear.recentre' (Real.cos qz166) Bool.false 756093 1048576 69996891 101458640896 756093 1048576 69996891 101458640896 (ep980 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz50 (@Neg.neg Real Real.instNeg (Real.sin qz166)) 247151 1048576 1 1048576 726521 1048576 69996891 101458640896 179560391671 1099511627776 34740337373221 212774191672328192 qz353 (@Enclosure.Real.IsNear.neg (Real.sin qz166) Bool.true 726521 1048576 69996891 101458640896 (@Enclosure.Real.IsNear.recentre' (Real.sin qz166) Bool.true 726521 1048576 69996891 101458640896 726521 1048576 69996891 101458640896 (ep985 rfl rfl) rfl)) rfl)

noncomputable def ep987 := @ep960 186869141043 1099511627776 34746060057945 212774191672328192 Bool.false 179560391671 1099511627776 34740337373221 212774191672328192 Bool.false 82436895731259126317056 1199614718371 1099511627776 904151034430663 212774191672328192 Bool.false 284381755288746108911616 64660924929 274877906944 112979725904239 26596773959041024 (ep961 (BSN.head_sum_c_succ qz143 17 18 rfl rfl) (ep975 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep976 ep986) rfl rfl

noncomputable abbrev qz167 := (@HMul.hMul Real Real Real qz268 qz438 qz584)

noncomputable def ep988 := @Enclosure.Complex.IsNear.of_eq qz642 (Complex.mk (@HMul.hMul Real Real Real qz0 qz52 (Real.cos qz167)) (@HMul.hMul Real Real Real qz0 qz52 (@Neg.neg Real Real.instNeg (Real.sin qz167)))) Bool.false 125406052849 549755813888 16939334639747 106387095836164096 Bool.true 6710393305 274877906944 8424624206195 53193547918082048 (BSN.cpow_neg_s_mk qz146 132339 1000 19 qz147 rfl)

noncomputable def ep989 := @Enclosure.Real.IsNear.mulLit_ff qz146 qz584 132339 1000 0 1 3315143513283831 1125899906842624 250000000193517 48379250000000000000 438722777404468910709 1125899906842624000 33084750025609846263 48379250000000000000000 qz148 (BSN.isNear_log_sfrac 19 1 3315143513283831 1125899906842624 250000000193517 48379250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz354) Bool.false 55618878793361701994496 18889465931478580854784 1000000000774068 193517000000000000000 3315143513283831 1125899906842624 250000000193517 48379250000000000000 (BSN.log_rat_reduce_isNear 19 1 4 38 32 90099 524288 24973259072661432 36028797018963968 193517 1000000000000000 rfl rfl rfl rfl (ep333 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep990 := nat_lit 2747694289335701328335216859347521

noncomputable def ep991 := BSN.cos_dyadic_bound_f 228950767 2147483648 2 1 1048576 387412 ep990 ep76 ep990 ep990 ep77 ep990 1042622 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 228950767) qz20 0 1 ep990 ep76 ep990 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 228950767) qz21 0 1 ep990 ep77 ep990 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz458 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 204296213) qz24)

noncomputable def ep992 := @Enclosure.Real.IsNear.cos_image qz167 qz458 Bool.false 204296213 524288 359 524288 Bool.false 1042622 1048576 1 193517 (@Enclosure.Real.IsNear.recentre' qz167 Bool.false 438722777404468910709 1125899906842624000 33084750025609846263 48379250000000000000000 204296213 524288 359 524288 (ep989 rfl) rfl) (Enclosure.sfrac_false_div 204296213 524288) (BSN.cos_reduce0 qz458 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 8055488998488529698816) qz25) 226375608064910080 72057594037927936 Bool.false 1042622 1048576 62 1000000000000000 387034 193517 (BSN.sin_reduce_arg_pos_rat_q0 204296213 524288 226375608064910080 72057594037927936 62 8055488998488529698816 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1042622 1048576 8055488998488529698816 75557863725914323419136 228950767 2147483648 387412 387034 (ep991 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep993 := BSN.sin_dyadic_bound_f 228950767 2147483648 1 0 1048576 387412 0 1 1 0 1 1 111580 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 228950767) qz15 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 228950767) qz16 0 0 rfl) rfl rfl

noncomputable def ep994 := @Enclosure.Real.IsNear.sin_image qz167 qz458 Bool.false 204296213 524288 359 524288 Bool.false 111580 1048576 1 193517 (@Enclosure.Real.IsNear.recentre' qz167 Bool.false 438722777404468910709 1125899906842624000 33084750025609846263 48379250000000000000000 204296213 524288 359 524288 (ep989 rfl) rfl) (Enclosure.sfrac_false_div 204296213 524288) (BSN.sin_reduce0 qz458 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 8055488998488529698816) qz25) 226375608064910080 72057594037927936 Bool.false 111580 1048576 62 1000000000000000 387034 193517 (BSN.sin_reduce_arg_pos_rat_q0 204296213 524288 226375608064910080 72057594037927936 62 8055488998488529698816 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 111580 1048576 8055488998488529698816 75557863725914323419136 228950767 2147483648 387412 387034 (ep993 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep995 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz52 (Real.cos qz167)) (@HMul.hMul Real Real Real qz0 qz52 (@Neg.neg Real Real.instNeg (Real.sin qz167))) Bool.false 125406052849 549755813888 16939334639747 106387095836164096 Bool.true 6710393305 274877906944 8424624206195 53193547918082048 (@Enclosure.Real.IsNear.mulLit_ff qz52 (Real.cos qz167) 240559 1048576 1 1048576 521311 524288 69996891 101458640896 125406052849 549755813888 16939334639747 106387095836164096 qz356 (@Enclosure.Real.IsNear.recentre' (Real.cos qz167) Bool.false 1042622 1048576 69996891 101458640896 521311 524288 69996891 101458640896 (ep992 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz52 (@Neg.neg Real Real.instNeg (Real.sin qz167)) 240559 1048576 1 1048576 27895 262144 69996891 101458640896 6710393305 274877906944 8424624206195 53193547918082048 qz356 (@Enclosure.Real.IsNear.neg (Real.sin qz167) Bool.false 27895 262144 69996891 101458640896 (@Enclosure.Real.IsNear.recentre' (Real.sin qz167) Bool.false 111580 1048576 69996891 101458640896 27895 262144 69996891 101458640896 (ep994 rfl rfl) rfl)) rfl)

noncomputable def ep996 := @ep958 125406052849 549755813888 16939334639747 106387095836164096 Bool.true 6710393305 274877906944 8424624206195 53193547918082048 Bool.false 797380579151040082870272 1450426824069 1099511627776 938029703710157 212774191672328192 Bool.false 15929320839097201197056 7243816453 34359738368 234384076014673 53193547918082048 (ep959 (BSN.head_sum_c_succ qz143 18 19 rfl rfl) (ep987 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep988 ep995) rfl rfl

noncomputable abbrev qz168 := (@HMul.hMul Real Real Real qz268 qz438 qz585)

noncomputable def ep997 := @Enclosure.Complex.IsNear.of_eq qz641 (Complex.mk (@HMul.hMul Real Real Real qz0 qz54 (Real.cos qz168)) (@HMul.hMul Real Real Real qz0 qz54 (@Neg.neg Real Real.instNeg (Real.sin qz168)))) Bool.false 201317662559 1099511627776 32990497890427 212774191672328192 Bool.true 141129470259 1099511627776 32940822076527 212774191672328192 (BSN.cpow_neg_s_mk qz146 132339 1000 20 qz147 rfl)

noncomputable def ep998 := @Enclosure.Real.IsNear.mulLit_ff qz146 qz585 132339 1000 0 1 3372893643545847 1125899906842624 250000000193517 48379250000000000000 446365371893213846133 1125899906842624000 33084750025609846263 48379250000000000000000 qz148 (BSN.isNear_log_sfrac 20 1 3372893643545847 1125899906842624 250000000193517 48379250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz357) Bool.false 56587765202795681021952 18889465931478580854784 1000000000774068 193517000000000000000 3372893643545847 1125899906842624 250000000193517 48379250000000000000 (BSN.log_rat_reduce_isNear 20 1 4 40 32 116991 524288 24973259072661432 36028797018963968 193517 1000000000000000 rfl rfl rfl rfl (ep344 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep999 := nat_lit 2972120460144961656963784967273178081

noncomputable def ep1000 := BSN.cos_dyadic_bound_f 1313005671 2147483648 2 1 1048576 387412 ep999 ep76 ep999 ep999 ep77 ep999 858611 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1313005671) qz20 0 1 ep999 ep76 ep999 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1313005671) qz21 0 1 ep999 ep77 ep999 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz459 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 415710147) qz17)

noncomputable def ep1001 := @Enclosure.Real.IsNear.cos_image qz168 qz459 Bool.false 415710147 1048576 359 524288 Bool.false 858611 1048576 1 193517 (@Enclosure.Real.IsNear.recentre' qz168 Bool.false 446365371893213846133 1125899906842624000 33084750025609846263 48379250000000000000000 415710147 1048576 359 524288 (ep998 rfl) rfl) (Enclosure.sfrac_false_div 415710147 1048576) (BSN.cos_reduce0 qz459 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 92394560174361384321024) qz19) 226375608064910080 72057594037927936 Bool.false 858611 1048576 63 1000000000000000 387034 193517 (BSN.sin_reduce_arg_pos_rat_q0 415710147 1048576 226375608064910080 72057594037927936 63 92394560174361384321024 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 858611 1048576 92394560174361384321024 151115727451828646838272 1313005671 2147483648 387412 387034 (ep1000 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1002 := BSN.sin_dyadic_bound_f 1313005671 2147483648 2 1 1048576 387412 ep999 ep57 ep999 ep999 ep58 ep999 601911 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1313005671) qz15 0 1 ep999 ep57 ep999 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1313005671) qz16 0 1 ep999 ep58 ep999 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1003 := @Enclosure.Real.IsNear.sin_image qz168 qz459 Bool.false 415710147 1048576 359 524288 Bool.false 601911 1048576 1 193517 (@Enclosure.Real.IsNear.recentre' qz168 Bool.false 446365371893213846133 1125899906842624000 33084750025609846263 48379250000000000000000 415710147 1048576 359 524288 (ep998 rfl) rfl) (Enclosure.sfrac_false_div 415710147 1048576) (BSN.sin_reduce0 qz459 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 92394560174361384321024) qz19) 226375608064910080 72057594037927936 Bool.false 601911 1048576 63 1000000000000000 387034 193517 (BSN.sin_reduce_arg_pos_rat_q0 415710147 1048576 226375608064910080 72057594037927936 63 92394560174361384321024 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 601911 1048576 92394560174361384321024 151115727451828646838272 1313005671 2147483648 387412 387034 (ep1002 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1004 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz54 (Real.cos qz168)) (@HMul.hMul Real Real Real qz0 qz54 (@Neg.neg Real Real.instNeg (Real.sin qz168))) Bool.false 201317662559 1099511627776 32990497890427 212774191672328192 Bool.true 141129470259 1099511627776 32940822076527 212774191672328192 (@Enclosure.Real.IsNear.mulLit_ff qz54 (Real.cos qz168) 234469 1048576 1 1048576 858611 1048576 69996891 101458640896 201317662559 1099511627776 32990497890427 212774191672328192 qz359 (@Enclosure.Real.IsNear.recentre' (Real.cos qz168) Bool.false 858611 1048576 69996891 101458640896 858611 1048576 69996891 101458640896 (ep1001 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz54 (@Neg.neg Real Real.instNeg (Real.sin qz168)) 234469 1048576 1 1048576 601911 1048576 69996891 101458640896 141129470259 1099511627776 32940822076527 212774191672328192 qz359 (@Enclosure.Real.IsNear.neg (Real.sin qz168) Bool.false 601911 1048576 69996891 101458640896 (@Enclosure.Real.IsNear.recentre' (Real.sin qz168) Bool.false 601911 1048576 69996891 101458640896 601911 1048576 69996891 101458640896 (ep1003 rfl rfl) rfl)) rfl)

noncomputable def ep1005 := @ep955 201317662559 1099511627776 32990497890427 212774191672328192 Bool.true 141129470259 1099511627776 32940822076527 212774191672328192 Bool.false ep956 412936121657 274877906944 121377525200073 26596773959041024 Bool.false 3115488745434923401216 90672656237 1099511627776 970477126135219 212774191672328192 (ep957 (BSN.head_sum_c_succ qz143 19 20 rfl rfl) (ep996 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep997 ep1004) rfl rfl

noncomputable abbrev qz169 := (@HMul.hMul Real Real Real qz268 qz438 qz586)

noncomputable def ep1006 := @Enclosure.Complex.IsNear.of_eq qz640 (Complex.mk (@HMul.hMul Real Real Real qz0 qz56 (Real.cos qz169)) (@HMul.hMul Real Real Real qz0 qz56 (@Neg.neg Real Real.instNeg (Real.sin qz169)))) Bool.false 84858871435 549755813888 16160223060275 106387095836164096 Bool.true 42399632173 274877906944 8080061118959 53193547918082048 (BSN.cpow_neg_s_mk qz146 132339 1000 21 qz147 rfl)

noncomputable def ep1007 := @Enclosure.Real.IsNear.mulLit_ff qz146 qz586 132339 1000 0 1 3427826275261687 1125899906842624 250000000193517 48379250000000000000 453635101441856395893 1125899906842624000 33084750025609846263 48379250000000000000000 qz148 (BSN.isNear_log_sfrac 21 1 3427826275261687 1125899906842624 250000000193517 48379250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz360) Bool.false 57509381830540779323392 18889465931478580854784 1000000000774068 193517000000000000000 3427826275261687 1125899906842624 250000000193517 48379250000000000000 (BSN.log_rat_reduce_isNear 21 1 4 42 32 142571 524288 24973259072661432 36028797018963968 193517 1000000000000000 rfl rfl rfl rfl (ep358 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1008 := nat_lit 288688596538106611733701451774331860111515813420509150547374708427183024800000

noncomputable def ep1009 := nat_lit 65253741252120627261389794412905053942865606236765341069852593424100000000

noncomputable def ep1010 := nat_lit 865935282131815593946581575734169770226661709049053920959984420094700874400000

noncomputable def ep1011 := BSN.cos_dyadic_bound_f 1685876190 2147483648 3 2 1048576 387412 ep1008 ep62 ep1009 ep1010 ep65 ep1009 741715 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1685876190) qz20 0 2 ep1008 ep62 ep1009 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1685876190) qz21 0 2 ep1010 ep65 ep1009 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz460 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 211240305) qz24)

noncomputable def ep1012 := @Enclosure.Real.IsNear.cos_image qz169 qz460 Bool.false 211240305 524288 359 524288 Bool.false 741715 1048576 1 193517 (@Enclosure.Real.IsNear.recentre' qz169 Bool.false 453635101441856395893 1125899906842624000 33084750025609846263 48379250000000000000000 211240305 524288 359 524288 (ep1007 rfl) rfl) (Enclosure.sfrac_false_div 211240305 524288) (BSN.cos_reduce0 qz460 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 59316495185450075422720) qz25) 226375608064910080 72057594037927936 Bool.false 741715 1048576 64 1000000000000000 387034 193517 (BSN.sin_reduce_arg_pos_rat_q0 211240305 524288 226375608064910080 72057594037927936 64 59316495185450075422720 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 741715 1048576 59316495185450075422720 75557863725914323419136 1685876190 2147483648 387412 387034 (ep1011 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1013 := nat_lit 8077978785074929079947081096839210000

noncomputable def ep1014 := BSN.sin_dyadic_bound_f 1685876190 2147483648 2 1 1048576 387412 ep1013 ep57 ep1013 ep1013 ep58 ep1013 741194 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1685876190) qz15 0 1 ep1013 ep57 ep1013 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1685876190) qz16 0 1 ep1013 ep58 ep1013 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1015 := @Enclosure.Real.IsNear.sin_image qz169 qz460 Bool.false 211240305 524288 359 524288 Bool.false 741194 1048576 1 193517 (@Enclosure.Real.IsNear.recentre' qz169 Bool.false 453635101441856395893 1125899906842624000 33084750025609846263 48379250000000000000000 211240305 524288 359 524288 (ep1007 rfl) rfl) (Enclosure.sfrac_false_div 211240305 524288) (BSN.sin_reduce0 qz460 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 59316495185450075422720) qz25) 226375608064910080 72057594037927936 Bool.false 741194 1048576 64 1000000000000000 387034 193517 (BSN.sin_reduce_arg_pos_rat_q0 211240305 524288 226375608064910080 72057594037927936 64 59316495185450075422720 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 741194 1048576 59316495185450075422720 75557863725914323419136 1685876190 2147483648 387412 387034 (ep1014 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1016 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz56 (Real.cos qz169)) (@HMul.hMul Real Real Real qz0 qz56 (@Neg.neg Real Real.instNeg (Real.sin qz169))) Bool.false 84858871435 549755813888 16160223060275 106387095836164096 Bool.true 42399632173 274877906944 8080061118959 53193547918082048 (@Enclosure.Real.IsNear.mulLit_ff qz56 (Real.cos qz169) 114409 524288 1 524288 741715 1048576 69996891 101458640896 84858871435 549755813888 16160223060275 106387095836164096 qz362 (@Enclosure.Real.IsNear.recentre' (Real.cos qz169) Bool.false 741715 1048576 69996891 101458640896 741715 1048576 69996891 101458640896 (ep1012 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz56 (@Neg.neg Real Real.instNeg (Real.sin qz169)) 114409 524288 1 524288 370597 524288 69996891 101458640896 42399632173 274877906944 8080061118959 53193547918082048 qz362 (@Enclosure.Real.IsNear.neg (Real.sin qz169) Bool.false 370597 524288 69996891 101458640896 (@Enclosure.Real.IsNear.recentre' (Real.sin qz169) Bool.false 741194 1048576 69996891 101458640896 370597 524288 69996891 101458640896 (ep1015 rfl rfl) rfl)) rfl)

noncomputable def ep1017 := @ep953 84858871435 549755813888 16160223060275 106387095836164096 Bool.true 42399632173 274877906944 8080061118959 53193547918082048 Bool.false 250339862610981007917056 910731114749 549755813888 501670323860567 106387095836164096 Bool.true 21694978624159502827520 78925872455 1099511627776 1002797370611055 212774191672328192 (ep954 (BSN.head_sum_c_succ qz143 20 21 rfl rfl) (ep1005 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1006 ep1016) rfl rfl

noncomputable abbrev qz170 := (@HMul.hMul Real Real Real qz268 qz438 qz587)

noncomputable def ep1018 := @Enclosure.Complex.IsNear.of_eq qz639 (Complex.mk (@HMul.hMul Real Real Real qz0 qz58 (Real.cos qz170)) (@HMul.hMul Real Real Real qz0 qz58 (@Neg.neg Real Real.instNeg (Real.sin qz170)))) Bool.false 11589418437 68719476736 7864310938277 53193547918082048 Bool.true 143410250601 1099511627776 31420869717237 212774191672328192 (BSN.cpow_neg_s_mk qz146 132339 1000 22 qz147 rfl)

noncomputable def ep1019 := @Enclosure.Real.IsNear.mulLit_ff qz146 qz587 132339 1000 0 1 3480203401436407 1125899906842624 250000000193517 48379250000000000000 460566637942692665973 1125899906842624000 33084750025609846263 48379250000000000000000 qz148 (BSN.isNear_log_sfrac 22 1 3480203401436407 1125899906842624 250000000193517 48379250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz363) Bool.false 58388124189833310502912 18889465931478580854784 1000000000774068 193517000000000000000 3480203401436407 1125899906842624 250000000193517 48379250000000000000 (BSN.log_rat_reduce_isNear 22 1 4 44 32 166961 524288 24973259072661432 36028797018963968 193517 1000000000000000 rfl rfl rfl rfl (ep372 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1020 := nat_lit 142725583536029539402625319659359941828322049264863033019474248330663865508096

noncomputable def ep1021 := nat_lit 15953246435729518887447014323475038958980724893449795813532053028142735616

noncomputable def ep1022 := nat_lit 428144844115217159170101064949432875407048186344802199466795680885935311053056

noncomputable def ep1023 := BSN.cos_dyadic_bound_f 1413696342 2147483648 3 2 1048576 387412 ep1020 ep62 ep1021 ep1022 ep65 ep1021 829456 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1413696342) qz20 0 2 ep1020 ep62 ep1021 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1413696342) qz21 0 2 ep1022 ep65 ep1021 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz461 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 428936107) qz17)

noncomputable def ep1024 := @Enclosure.Real.IsNear.cos_image qz170 qz461 Bool.false 428936107 1048576 359 524288 Bool.false 829456 1048576 1 193517 (@Enclosure.Real.IsNear.recentre' qz170 Bool.false 460566637942692665973 1125899906842624000 33084750025609846263 48379250000000000000000 428936107 1048576 359 524288 (ep1019 rfl) rfl) (Enclosure.sfrac_false_div 428936107 1048576) (BSN.cos_reduce0 qz461 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 99480036239938896789504) qz19) 226375608064910080 72057594037927936 Bool.false 829456 1048576 65 1000000000000000 387034 193517 (BSN.sin_reduce_arg_pos_rat_q0 428936107 1048576 226375608064910080 72057594037927936 65 99480036239938896789504 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 829456 1048576 99480036239938896789504 151115727451828646838272 1413696342 2147483648 387412 387034 (ep1023 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1025 := nat_lit 3994151528889398418268520029099969296

noncomputable def ep1026 := BSN.sin_dyadic_bound_f 1413696342 2147483648 2 1 1048576 387412 ep1025 ep57 ep1025 ep1025 ep58 ep1025 641493 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1413696342) qz15 0 1 ep1025 ep57 ep1025 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1413696342) qz16 0 1 ep1025 ep58 ep1025 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1027 := @Enclosure.Real.IsNear.sin_image qz170 qz461 Bool.false 428936107 1048576 359 524288 Bool.false 641493 1048576 1 193517 (@Enclosure.Real.IsNear.recentre' qz170 Bool.false 460566637942692665973 1125899906842624000 33084750025609846263 48379250000000000000000 428936107 1048576 359 524288 (ep1019 rfl) rfl) (Enclosure.sfrac_false_div 428936107 1048576) (BSN.sin_reduce0 qz461 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 99480036239938896789504) qz19) 226375608064910080 72057594037927936 Bool.false 641493 1048576 65 1000000000000000 387034 193517 (BSN.sin_reduce_arg_pos_rat_q0 428936107 1048576 226375608064910080 72057594037927936 65 99480036239938896789504 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 641493 1048576 99480036239938896789504 151115727451828646838272 1413696342 2147483648 387412 387034 (ep1026 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1028 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz58 (Real.cos qz170)) (@HMul.hMul Real Real Real qz0 qz58 (@Neg.neg Real Real.instNeg (Real.sin qz170))) Bool.false 11589418437 68719476736 7864310938277 53193547918082048 Bool.true 143410250601 1099511627776 31420869717237 212774191672328192 (@Enclosure.Real.IsNear.mulLit_ff qz58 (Real.cos qz170) 223557 1048576 1 1048576 51841 65536 69996891 101458640896 11589418437 68719476736 7864310938277 53193547918082048 qz365 (@Enclosure.Real.IsNear.recentre' (Real.cos qz170) Bool.false 829456 1048576 69996891 101458640896 51841 65536 69996891 101458640896 (ep1024 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz58 (@Neg.neg Real Real.instNeg (Real.sin qz170)) 223557 1048576 1 1048576 641493 1048576 69996891 101458640896 143410250601 1099511627776 31420869717237 212774191672328192 qz365 (@Enclosure.Real.IsNear.neg (Real.sin qz170) Bool.false 641493 1048576 69996891 101458640896 (@Enclosure.Real.IsNear.recentre' (Real.sin qz170) Bool.false 641493 1048576 69996891 101458640896 641493 1048576 69996891 101458640896 (ep1027 rfl rfl) rfl)) rfl)

noncomputable def ep1029 := @ep951 11589418437 68719476736 7864310938277 53193547918082048 Bool.true 143410250601 1099511627776 31420869717237 212774191672328192 Bool.false 68956315818066779832320 1003446462245 549755813888 517398945737121 106387095836164096 Bool.true 244461152574707603603456 13896007691 68719476736 258554560082073 53193547918082048 (ep952 (BSN.head_sum_c_succ qz143 21 22 rfl rfl) (ep1017 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1018 ep1028) rfl rfl

noncomputable abbrev qz171 := (@HMul.hMul Real Real Real qz268 qz438 qz588)

noncomputable def ep1030 := @Enclosure.Complex.IsNear.of_eq qz638 (Complex.mk (@HMul.hMul Real Real Real qz0 qz60 (Real.cos qz171)) (@HMul.hMul Real Real Real qz0 qz60 (@Neg.neg Real Real.instNeg (Real.sin qz171)))) Bool.false 110846972211 549755813888 15402508903913 106387095836164096 Bool.true 58426438389 1099511627776 30660512664899 212774191672328192 (BSN.cpow_neg_s_mk qz146 132339 1000 23 qz147 rfl)

noncomputable def ep1031 := @Enclosure.Real.IsNear.mulLit_ff qz146 qz588 132339 1000 0 1 3530250507853047 1125899906842624 250000000193517 48379250000000000000 467189821958764386933 1125899906842624000 33084750025609846263 48379250000000000000000 qz148 (BSN.isNear_log_sfrac 23 1 3530250507853047 1125899906842624 250000000193517 48379250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz366) Bool.false 59227775304360265777152 18889465931478580854784 1000000000774068 193517000000000000000 3530250507853047 1125899906842624 250000000193517 48379250000000000000 (BSN.log_rat_reduce_isNear 23 1 4 46 32 190266 524288 24973259072661432 36028797018963968 193517 1000000000000000 rfl rfl rfl rfl (ep383 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1032 := nat_lit 93775102652281006542931503971176081

noncomputable def ep1033 := BSN.cos_dyadic_bound_f 553377997 2147483648 2 1 1048576 387412 ep1032 ep76 ep1032 ep1032 ep77 ep1032 1013954 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 553377997) qz20 0 1 ep1032 ep76 ep1032 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 553377997) qz21 0 1 ep1032 ep77 ep1032 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz462 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 435104427) qz17)

noncomputable def ep1034 := @Enclosure.Real.IsNear.cos_image qz171 qz462 Bool.false 435104427 1048576 359 524288 Bool.false 1013954 1048576 1 193517 (@Enclosure.Real.IsNear.recentre' qz171 Bool.false 467189821958764386933 1125899906842624000 33084750025609846263 48379250000000000000000 435104427 1048576 359 524288 (ep1031 rfl) rfl) (Enclosure.sfrac_false_div 435104427 1048576) (BSN.cos_reduce0 qz462 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 38940514742917580980224) qz19) 226375608064910080 72057594037927936 Bool.false 1013954 1048576 66 1000000000000000 387034 193517 (BSN.sin_reduce_arg_pos_rat_q0 435104427 1048576 226375608064910080 72057594037927936 66 38940514742917580980224 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1013954 1048576 38940514742917580980224 151115727451828646838272 553377997 2147483648 387412 387034 (ep1033 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1035 := BSN.sin_dyadic_bound_f 553377997 2147483648 2 1 1048576 387412 ep1032 ep57 ep1032 ep1032 ep58 ep1032 267223 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 553377997) qz15 0 1 ep1032 ep57 ep1032 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 553377997) qz16 0 1 ep1032 ep58 ep1032 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1036 := @Enclosure.Real.IsNear.sin_image qz171 qz462 Bool.false 435104427 1048576 359 524288 Bool.false 267223 1048576 1 193517 (@Enclosure.Real.IsNear.recentre' qz171 Bool.false 467189821958764386933 1125899906842624000 33084750025609846263 48379250000000000000000 435104427 1048576 359 524288 (ep1031 rfl) rfl) (Enclosure.sfrac_false_div 435104427 1048576) (BSN.sin_reduce0 qz462 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 38940514742917580980224) qz19) 226375608064910080 72057594037927936 Bool.false 267223 1048576 66 1000000000000000 387034 193517 (BSN.sin_reduce_arg_pos_rat_q0 435104427 1048576 226375608064910080 72057594037927936 66 38940514742917580980224 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 267223 1048576 38940514742917580980224 151115727451828646838272 553377997 2147483648 387412 387034 (ep1035 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1037 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz60 (Real.cos qz171)) (@HMul.hMul Real Real Real qz0 qz60 (@Neg.neg Real Real.instNeg (Real.sin qz171))) Bool.false 110846972211 549755813888 15402508903913 106387095836164096 Bool.true 58426438389 1099511627776 30660512664899 212774191672328192 (@Enclosure.Real.IsNear.mulLit_ff qz60 (Real.cos qz171) 218643 1048576 1 1048576 506977 524288 69996891 101458640896 110846972211 549755813888 15402508903913 106387095836164096 qz368 (@Enclosure.Real.IsNear.recentre' (Real.cos qz171) Bool.false 1013954 1048576 69996891 101458640896 506977 524288 69996891 101458640896 (ep1034 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz60 (@Neg.neg Real Real.instNeg (Real.sin qz171)) 218643 1048576 1 1048576 267223 1048576 69996891 101458640896 58426438389 1099511627776 30660512664899 212774191672328192 qz368 (@Enclosure.Real.IsNear.neg (Real.sin qz171) Bool.false 267223 1048576 69996891 101458640896 (@Enclosure.Real.IsNear.recentre' (Real.sin qz171) Bool.false 267223 1048576 69996891 101458640896 267223 1048576 69996891 101458640896 (ep1036 rfl rfl) rfl)) rfl)

noncomputable def ep1038 := @ep949 110846972211 549755813888 15402508903913 106387095836164096 Bool.true 58426438389 1099511627776 30660512664899 212774191672328192 Bool.false 612589293969413062524928 139286679307 68719476736 266400727320517 53193547918082048 Bool.true 19293856309559448043520 280762561445 1099511627776 1064878752993191 212774191672328192 (ep950 (BSN.head_sum_c_succ qz143 22 23 rfl rfl) (ep1029 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1030 ep1037) rfl rfl

noncomputable abbrev qz172 := (@HMul.hMul Real Real Real qz268 qz438 qz589)

noncomputable def ep1039 := @Enclosure.Complex.IsNear.of_eq qz637 (Complex.mk (@HMul.hMul Real Real Real qz0 qz62 (Real.cos qz172)) (@HMul.hMul Real Real Real qz0 qz62 (@Neg.neg Real Real.instNeg (Real.sin qz172)))) Bool.false 207319673673 1099511627776 30151711020099 212774191672328192 Bool.false 21491441951 274877906944 7510498123273 53193547918082048 (BSN.cpow_neg_s_mk qz146 132339 1000 24 qz147 rfl)

noncomputable def ep1040 := @Enclosure.Real.IsNear.mulLit_ff qz146 qz589 132339 1000 0 1 3578169457974519 1125899906842624 250000000193517 48379250000000000000 473531367898889869941 1125899906842624000 33084750025609846263 48379250000000000000000 qz148 (BSN.isNear_log_sfrac 24 1 3578169457974519 1125899906842624 250000000193517 48379250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz369) Bool.false 60031721881041427759104 18889465931478580854784 1000000000774068 193517000000000000000 3578169457974519 1125899906842624 250000000193517 48379250000000000000 (BSN.log_rat_reduce_isNear 24 1 4 48 32 212580 524288 24973259072661432 36028797018963968 193517 1000000000000000 rfl rfl rfl rfl (ep393 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1041 := nat_lit 2633105107278173680910009765275521357517588070134696580480730724878978305517505

noncomputable def ep1042 := nat_lit 1674100311834860176451455599181162209690971809893220374106919637574548219841

noncomputable def ep1043 := nat_lit 6893517213795103200192913695227691197539897657898663925415264504793632007808961

noncomputable def ep1044 := BSN.sin_dyadic_bound_f 2529138919 2147483648 3 2 1048576 387412 ep1041 ep94 ep1042 ep1043 ep96 ep1042 968607 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2529138919) qz15 0 2 ep1041 ep94 ep1042 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2529138919) qz16 0 2 ep1043 ep96 ep1042 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz463 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 110252613) qz566)

noncomputable def ep1045 := @Enclosure.Real.IsNear.cos_image qz172 qz463 Bool.false 110252613 262144 359 524288 Bool.false 968607 1048576 1 193517 (@Enclosure.Real.IsNear.recentre' qz172 Bool.false 473531367898889869941 1125899906842624000 33084750025609846263 48379250000000000000000 110252613 262144 359 524288 (ep1040 rfl) rfl) (Enclosure.sfrac_false_div 110252613 262144) (BSN.cos_reduce3 qz463 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 44493082397952700317696) qz325) 226375608064910080 72057594037927936 Bool.false 968607 1048576 66 1000000000000000 387034 193517 (BSN.sin_reduce_arg_pos_rat_q3 110252613 262144 226375608064910080 72057594037927936 66 44493082397952700317696 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 968607 1048576 44493082397952700317696 37778931862957161709568 2529138919 2147483648 387412 387034 (ep1044 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1046 := nat_lit 1463580215293134205028428294308259048491856026434783975988897922549465524496321

noncomputable def ep1047 := nat_lit 4387392445255732894732381971726414821056186135684565487218479928373247477049281

noncomputable def ep1048 := BSN.cos_dyadic_bound_f 2529138919 2147483648 3 2 1048576 387412 ep1046 ep62 ep1042 ep1047 ep65 ep1042 401636 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2529138919) qz20 0 2 ep1046 ep62 ep1042 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2529138919) qz21 0 2 ep1047 ep65 ep1042 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1049 := @Enclosure.Real.IsNear.sin_image qz172 qz463 Bool.false 110252613 262144 359 524288 Bool.true 401636 1048576 1 193517 (@Enclosure.Real.IsNear.recentre' qz172 Bool.false 473531367898889869941 1125899906842624000 33084750025609846263 48379250000000000000000 110252613 262144 359 524288 (ep1040 rfl) rfl) (Enclosure.sfrac_false_div 110252613 262144) (BSN.sin_reduce3 qz463 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 44493082397952700317696) qz325) 226375608064910080 72057594037927936 Bool.false 401636 1048576 66 1000000000000000 387034 193517 (BSN.sin_reduce_arg_pos_rat_q3 110252613 262144 226375608064910080 72057594037927936 66 44493082397952700317696 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 401636 1048576 44493082397952700317696 37778931862957161709568 2529138919 2147483648 387412 387034 (ep1048 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1050 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz62 (Real.cos qz172)) (@HMul.hMul Real Real Real qz0 qz62 (@Neg.neg Real Real.instNeg (Real.sin qz172))) Bool.false 207319673673 1099511627776 30151711020099 212774191672328192 Bool.false 21491441951 274877906944 7510498123273 53193547918082048 (@Enclosure.Real.IsNear.mulLit_ff qz62 (Real.cos qz172) 214039 1048576 1 1048576 968607 1048576 69996891 101458640896 207319673673 1099511627776 30151711020099 212774191672328192 qz371 (@Enclosure.Real.IsNear.recentre' (Real.cos qz172) Bool.false 968607 1048576 69996891 101458640896 968607 1048576 69996891 101458640896 (ep1045 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz62 (@Neg.neg Real Real.instNeg (Real.sin qz172)) 214039 1048576 1 1048576 100409 262144 69996891 101458640896 21491441951 274877906944 7510498123273 53193547918082048 qz371 (@Enclosure.Real.IsNear.neg (Real.sin qz172) Bool.true 100409 262144 69996891 101458640896 (@Enclosure.Real.IsNear.recentre' (Real.sin qz172) Bool.true 401636 1048576 69996891 101458640896 100409 262144 69996891 101458640896 (ep1049 rfl rfl) rfl)) rfl)

noncomputable def ep1051 := @ep947 207319673673 1099511627776 30151711020099 212774191672328192 Bool.false 21491441951 274877906944 7510498123273 53193547918082048 Bool.false 167394222984240100802560 2435906542585 1099511627776 1095754620302167 212774191672328192 Bool.true 53545334915440368943104 194796793641 1099511627776 1094920745486283 212774191672328192 (ep948 (BSN.head_sum_c_succ qz143 23 24 rfl rfl) (ep1038 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1039 ep1050) rfl rfl

theorem EMRow44.d15 : Enclosure.Complex.IsNear qz164 Bool.false 2435906542585 1099511627776 1095754620302167 212774191672328192 Bool.true 194796793641 1099511627776 1094920745486283 212774191672328192 := ep946 (BSN.head_sum_c_succ qz143 24 25 rfl rfl) (ep1051 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable abbrev qz173 := (BSN.headSumC qz436 33)

noncomputable abbrev qz645 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 32) qz144)

noncomputable def ep1052 := @Enclosure.Complex.IsNear.of_eq qz173 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz143 32) qz645) Bool.false 2397094195321 1099511627776 1317420598410975 212774191672328192 Bool.true 51038480035 1099511627776 1316566967831595 212774191672328192

noncomputable def ep1053 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz143 32) qz645 Bool.false 68836498983 34359738368 20176061195153 3324596744880128 Bool.true 55023413809 1099511627776 1290613000196481 212774191672328192 Bool.false

noncomputable abbrev qz646 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 31) qz144)

noncomputable def ep1054 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz143 32) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz143 31) qz646) Bool.false 68836498983 34359738368 20176061195153 3324596744880128 Bool.true 55023413809 1099511627776 1290613000196481 212774191672328192

noncomputable def ep1055 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz143 31) qz646 Bool.false 2295744299795 1099511627776 1264807349924485 212774191672328192 Bool.false 59598271249 549755813888 632034475972755 106387095836164096 Bool.true

noncomputable def ep1056 := nat_lit 2421968993510377553657856

noncomputable abbrev qz647 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 30) qz144)

noncomputable def ep1057 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz143 31) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz143 30) qz647) Bool.false 2295744299795 1099511627776 1264807349924485 212774191672328192 Bool.false 59598271249 549755813888 632034475972755 106387095836164096

noncomputable def ep1058 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz143 30) qz647 Bool.false 2426249461351 1099511627776 1237874461332513 212774191672328192 Bool.true 33335093423 1099511627776 1237113798255103 212774191672328192 Bool.true

noncomputable abbrev qz648 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 29) qz144)

noncomputable def ep1059 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz143 30) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz143 29) qz648) Bool.false 2426249461351 1099511627776 1237874461332513 212774191672328192 Bool.true 33335093423 1099511627776 1237113798255103 212774191672328192

noncomputable def ep1060 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz143 29) qz648 Bool.false 2245318336201 1099511627776 1210435614145031 212774191672328192 Bool.true 127943217623 1099511627776 1209760742959231 212774191672328192 Bool.false

noncomputable def ep1061 := nat_lit 1333844747320340605042688

noncomputable abbrev qz649 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 28) qz144)

noncomputable def ep1062 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz143 29) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz143 28) qz649) Bool.false 2245318336201 1099511627776 1210435614145031 212774191672328192 Bool.true 127943217623 1099511627776 1209760742959231 212774191672328192

noncomputable def ep1063 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz143 28) qz649 Bool.false 1080925148567 549755813888 591287013561971 106387095836164096 Bool.false 15586047567 274877906944 590897420493163 106387095836164096 Bool.false

noncomputable def ep1064 := nat_lit 1234376809355830768959488

noncomputable abbrev qz650 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 27) qz144)

noncomputable def ep1065 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz143 28) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz143 27) qz650) Bool.false 1080925148567 549755813888 591287013561971 106387095836164096 Bool.false 15586047567 274877906944 590897420493163 106387095836164096

noncomputable def ep1066 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz143 27) qz650 Bool.false 2346129713351 1099511627776 1154146565481731 212774191672328192 Bool.false 83172670449 549755813888 288361090730609 53193547918082048 Bool.true

noncomputable def ep1067 := nat_lit 2376979539209833607593984

noncomputable abbrev qz651 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 26) qz144)

noncomputable def ep1068 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz143 27) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz143 26) qz651) Bool.false 2346129713351 1099511627776 1154146565481731 212774191672328192 Bool.false 83172670449 549755813888 288361090730609 53193547918082048

noncomputable def ep1069 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz143 26) qz651 Bool.false 625052601115 274877906944 281293223359551 53193547918082048 Bool.false 15493244889 1099511627776 1124473729095809 212774191672328192 Bool.true

noncomputable abbrev qz652 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 25) qz144)

noncomputable def ep1070 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz143 26) (@HAdd.hAdd Complex Complex Complex qz4 qz164 qz652) Bool.false 625052601115 274877906944 281293223359551 53193547918082048 Bool.false 15493244889 1099511627776 1124473729095809 212774191672328192

noncomputable def ep1071 := @Enclosure.Complex.IsNear.addLitP qz164 qz652 Bool.false 2435906542585 1099511627776 1095754620302167 212774191672328192 Bool.true 194796793641 1099511627776 1094920745486283 212774191672328192 Bool.false

noncomputable def ep1072 := nat_lit 2749010411590305930280960

noncomputable abbrev qz174 := (@HMul.hMul Real Real Real qz268 qz438 qz598)

noncomputable def ep1073 := @Enclosure.Complex.IsNear.of_eq qz652 (Complex.mk (@HMul.hMul Real Real Real qz0 qz64 (Real.cos qz174)) (@HMul.hMul Real Real Real qz0 qz64 (@Neg.neg Real Real.instNeg (Real.sin qz174)))) Bool.false 64303861875 1099511627776 29418273136037 212774191672328192 Bool.false 105145019265 549755813888 14776491804763 106387095836164096 (BSN.cpow_neg_s_mk qz146 132339 1000 25 qz147 rfl)

noncomputable def ep1074 := @Enclosure.Real.IsNear.mulLit_ff qz146 qz598 132339 1000 0 1 3624129903009015 1125899906842624 250000000193517 48379250000000000000 95922745446862007217 225179981368524800 33084750025609846263 48379250000000000000000 qz148 (BSN.isNear_log_sfrac 25 1 3624129903009015 1125899906842624 250000000193517 48379250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz372) Bool.false 60802810194841294602240 18889465931478580854784 1000000000774068 193517000000000000000 3624129903009015 1125899906842624 250000000193517 48379250000000000000 (BSN.log_rat_reduce_isNear 25 1 4 50 32 233982 524288 24973259072661432 36028797018963968 193517 1000000000000000 rfl rfl rfl rfl (ep426 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1075 := nat_lit 164940116641468366734691678299264016

noncomputable def ep1076 := BSN.sin_dyadic_bound_f 637281886 2147483648 2 1 1048576 387412 ep1075 ep57 ep1075 ep1075 ep58 ep1075 306625 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 637281886) qz15 0 1 ep1075 ep57 ep1075 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 637281886) qz16 0 1 ep1075 ep58 ep1075 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz464 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 446675091) qz17)

noncomputable def ep1077 := @Enclosure.Real.IsNear.cos_image qz174 qz464 Bool.false 446675091 1048576 359 524288 Bool.false 306625 1048576 1 193517 (@Enclosure.Real.IsNear.recentre' qz174 Bool.false 95922745446862007217 225179981368524800 33084750025609846263 48379250000000000000000 446675091 1048576 359 524288 (ep1074 rfl) rfl) (Enclosure.sfrac_false_div 446675091 1048576) (BSN.cos_reduce3 qz464 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 44844726049554323996672) qz19) 226375608064910080 72057594037927936 Bool.false 306625 1048576 67 1000000000000000 387034 193517 (BSN.sin_reduce_arg_pos_rat_q3 446675091 1048576 226375608064910080 72057594037927936 67 44844726049554323996672 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 306625 1048576 44844726049554323996672 151115727451828646838272 637281886 2147483648 387412 387034 (ep1076 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1078 := BSN.cos_dyadic_bound_f 637281886 2147483648 2 1 1048576 387412 ep1075 ep76 ep1075 ep1075 ep77 ep1075 1002742 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 637281886) qz20 0 1 ep1075 ep76 ep1075 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 637281886) qz21 0 1 ep1075 ep77 ep1075 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1079 := @Enclosure.Real.IsNear.sin_image qz174 qz464 Bool.false 446675091 1048576 359 524288 Bool.true 1002742 1048576 1 193517 (@Enclosure.Real.IsNear.recentre' qz174 Bool.false 95922745446862007217 225179981368524800 33084750025609846263 48379250000000000000000 446675091 1048576 359 524288 (ep1074 rfl) rfl) (Enclosure.sfrac_false_div 446675091 1048576) (BSN.sin_reduce3 qz464 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 44844726049554323996672) qz19) 226375608064910080 72057594037927936 Bool.false 1002742 1048576 67 1000000000000000 387034 193517 (BSN.sin_reduce_arg_pos_rat_q3 446675091 1048576 226375608064910080 72057594037927936 67 44844726049554323996672 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1002742 1048576 44844726049554323996672 151115727451828646838272 637281886 2147483648 387412 387034 (ep1078 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1080 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz64 (Real.cos qz174)) (@HMul.hMul Real Real Real qz0 qz64 (@Neg.neg Real Real.instNeg (Real.sin qz174))) Bool.false 64303861875 1099511627776 29418273136037 212774191672328192 Bool.false 105145019265 549755813888 14776491804763 106387095836164096 (@Enclosure.Real.IsNear.mulLit_ff qz64 (Real.cos qz174) 209715 1048576 1 1048576 306625 1048576 69996891 101458640896 64303861875 1099511627776 29418273136037 212774191672328192 qz374 (@Enclosure.Real.IsNear.recentre' (Real.cos qz174) Bool.false 306625 1048576 69996891 101458640896 306625 1048576 69996891 101458640896 (ep1077 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz64 (@Neg.neg Real Real.instNeg (Real.sin qz174)) 209715 1048576 1 1048576 501371 524288 69996891 101458640896 105145019265 549755813888 14776491804763 106387095836164096 qz374 (@Enclosure.Real.IsNear.neg (Real.sin qz174) Bool.true 501371 524288 69996891 101458640896 (@Enclosure.Real.IsNear.recentre' (Real.sin qz174) Bool.true 1002742 1048576 69996891 101458640896 501371 524288 69996891 101458640896 (ep1079 rfl rfl) rfl)) rfl)

noncomputable def ep1081 := @ep1071 64303861875 1099511627776 29418273136037 212774191672328192 Bool.false 105145019265 549755813888 14776491804763 106387095836164096 Bool.false ep1072 625052601115 274877906944 281293223359551 53193547918082048 Bool.false 8517501453718291218432 15493244889 1099511627776 1124473729095809 212774191672328192 EMRow44.d15 (ep1073 ep1080) rfl rfl

noncomputable abbrev qz175 := (@HMul.hMul Real Real Real qz268 qz438 qz599)

noncomputable def ep1082 := @Enclosure.Complex.IsNear.of_eq qz651 (Complex.mk (@HMul.hMul Real Real Real qz0 qz66 (Real.cos qz175)) (@HMul.hMul Real Real Real qz0 qz66 (@Neg.neg Real Real.instNeg (Real.sin qz175)))) Bool.true 154080691109 1099511627776 28973672043527 212774191672328192 Bool.false 150852096009 1099511627776 28970633826627 212774191672328192 (BSN.cpow_neg_s_mk qz146 132339 1000 26 qz147 rfl)

noncomputable def ep1083 := @Enclosure.Real.IsNear.mulLit_ff qz146 qz599 132339 1000 0 1 3668288609262839 1125899906842624 250000000193517 48379250000000000000 485457646261234850421 1125899906842624000 33084750025609846263 48379250000000000000000 qz148 (BSN.isNear_log_sfrac 26 1 3668288609262839 1125899906842624 250000000193517 48379250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz375) Bool.false 61543670347942250676224 18889465931478580854784 1000000000774068 193517000000000000000 3668288609262839 1125899906842624 250000000193517 48379250000000000000 (BSN.log_rat_reduce_isNear 26 1 4 52 32 254545 524288 24973259072661432 36028797018963968 193517 1000000000000000 rfl rfl rfl rfl (ep441 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1084 := nat_lit 273919907055865598332346455654482433397546442076872653880445271683814209355776

noncomputable def ep1085 := nat_lit 58749393999633024292265678961772143264501405399371318219016234888746500096

noncomputable def ep1086 := nat_lit 821642222379597528948454835605523755906110323419819219004897782581665135067136

noncomputable def ep1087 := BSN.cos_dyadic_bound_f 1663893112 2147483648 3 2 1048576 387412 ep1084 ep62 ep1085 ep1086 ep65 ep1085 749263 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1663893112) qz20 0 2 ep1084 ep62 ep1085 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1663893112) qz21 0 2 ep1086 ep65 ep1085 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz465 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 14128677) (@Nat.cast Real Real.instNatCast 32768))

noncomputable def ep1088 := @Enclosure.Real.IsNear.cos_image qz175 qz465 Bool.false 14128677 32768 719 1048576 Bool.true 749263 1048576 1 193517 (@Enclosure.Real.IsNear.recentre' qz175 Bool.false 485457646261234850421 1125899906842624000 33084750025609846263 48379250000000000000000 14128677 32768 719 1048576 (ep1083 rfl) rfl) (Enclosure.sfrac_false_div 14128677 32768) (BSN.cos_reduce2 qz465 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 3658939648572374646784) qz442) 226375608064910080 72057594037927936 Bool.false 749263 1048576 68 1000000000000000 387034 193517 (BSN.sin_reduce_arg_pos_rat_q2 14128677 32768 226375608064910080 72057594037927936 68 3658939648572374646784 4722366482869645213696 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 749263 1048576 3658939648572374646784 4722366482869645213696 1663893112 2147483648 387412 387034 (ep1087 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1089 := nat_lit 7664815327170839560479112689152167936

noncomputable def ep1090 := BSN.sin_dyadic_bound_f 1663893112 2147483648 2 1 1048576 387412 ep1089 ep57 ep1089 ep1089 ep58 ep1089 733563 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1663893112) qz15 0 1 ep1089 ep57 ep1089 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1663893112) qz16 0 1 ep1089 ep58 ep1089 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1091 := @Enclosure.Real.IsNear.sin_image qz175 qz465 Bool.false 14128677 32768 719 1048576 Bool.true 733563 1048576 1 193517 (@Enclosure.Real.IsNear.recentre' qz175 Bool.false 485457646261234850421 1125899906842624000 33084750025609846263 48379250000000000000000 14128677 32768 719 1048576 (ep1083 rfl) rfl) (Enclosure.sfrac_false_div 14128677 32768) (BSN.sin_reduce2 qz465 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 3658939648572374646784) qz442) 226375608064910080 72057594037927936 Bool.false 733563 1048576 68 1000000000000000 387034 193517 (BSN.sin_reduce_arg_pos_rat_q2 14128677 32768 226375608064910080 72057594037927936 68 3658939648572374646784 4722366482869645213696 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 733563 1048576 3658939648572374646784 4722366482869645213696 1663893112 2147483648 387412 387034 (ep1090 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1092 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz66 (Real.cos qz175)) (@HMul.hMul Real Real Real qz0 qz66 (@Neg.neg Real Real.instNeg (Real.sin qz175))) Bool.true 154080691109 1099511627776 28973672043527 212774191672328192 Bool.false 150852096009 1099511627776 28970633826627 212774191672328192 (@Enclosure.Real.IsNear.mulLit_ft qz66 (Real.cos qz175) 205643 1048576 1 1048576 749263 1048576 140187299 202917281792 154080691109 1099511627776 28973672043527 212774191672328192 qz378 (@Enclosure.Real.IsNear.recentre' (Real.cos qz175) Bool.true 749263 1048576 140187299 202917281792 749263 1048576 140187299 202917281792 (ep1088 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz66 (@Neg.neg Real Real.instNeg (Real.sin qz175)) 205643 1048576 1 1048576 733563 1048576 140187299 202917281792 150852096009 1099511627776 28970633826627 212774191672328192 qz378 (@Enclosure.Real.IsNear.neg (Real.sin qz175) Bool.true 733563 1048576 140187299 202917281792 (@Enclosure.Real.IsNear.recentre' (Real.sin qz175) Bool.true 733563 1048576 140187299 202917281792 733563 1048576 140187299 202917281792 (ep1091 rfl rfl) rfl)) rfl)

noncomputable def ep1093 := @ep1069 154080691109 1099511627776 28973672043527 212774191672328192 Bool.false 150852096009 1099511627776 28970633826627 212774191672328192 Bool.false 644899225025049572409344 2346129713351 1099511627776 1154146565481731 212774191672328192 Bool.false 182898636543713605582848 83172670449 549755813888 288361090730609 53193547918082048 (ep1070 (BSN.head_sum_c_succ qz143 25 26 rfl rfl) (ep1081 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1082 ep1092) rfl rfl

noncomputable abbrev qz176 := (@HMul.hMul Real Real Real qz268 qz438 qz600)

noncomputable def ep1094 := @Enclosure.Complex.IsNear.of_eq qz650 (Complex.mk (@HMul.hMul Real Real Real qz0 qz68 (Real.cos qz176)) (@HMul.hMul Real Real Real qz0 qz68 (@Neg.neg Real Real.instNeg (Real.sin qz176)))) Bool.true 184279416217 1099511627776 28427461642211 212774191672328192 Bool.true 52000575315 549755813888 14175239031945 106387095836164096 (BSN.cpow_neg_s_mk qz146 132339 1000 27 qz147 rfl)

noncomputable def ep1095 := @Enclosure.Real.IsNear.mulLit_ff qz146 qz600 132339 1000 0 1 3710780868205815 1125899906842624 250000000193517 48379250000000000000 98216205863497870257 225179981368524800 33084750025609846263 48379250000000000000000 qz148 (BSN.isNear_log_sfrac 27 1 3710780868205815 1125899906842624 250000000193517 48379250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz379) Bool.false 62256572154556490711040 18889465931478580854784 1000000000774068 193517000000000000000 3710780868205815 1125899906842624 250000000193517 48379250000000000000 (BSN.log_rat_reduce_isNear 27 1 4 54 32 274332 524288 24973259072661432 36028797018963968 193517 1000000000000000 rfl rfl rfl rfl (ep452 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1096 := nat_lit 1707979390265575733001350803967077963446931884914895889144973575044944141930625

noncomputable def ep1097 := nat_lit 704700055786895901795272587952596963637938078946684322043135706443062890625

noncomputable def ep1098 := nat_lit 4472138412509995754972059759533280937753217322649289839810670476831088746090625

noncomputable def ep1099 := BSN.sin_dyadic_bound_f 2269867665 2147483648 3 2 1048576 387412 ep1096 ep94 ep1097 ep1098 ep96 ep1097 913183 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2269867665) qz15 0 2 ep1096 ep94 ep1097 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2269867665) qz16 0 2 ep1098 ep96 ep1097 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz466 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 14292339) (@Nat.cast Real Real.instNatCast 32768))

noncomputable def ep1100 := @Enclosure.Real.IsNear.cos_image qz176 qz466 Bool.false 14292339 32768 359 524288 Bool.true 913183 1048576 1 193517 (@Enclosure.Real.IsNear.recentre' qz176 Bool.false 98216205863497870257 225179981368524800 33084750025609846263 48379250000000000000000 14292339 32768 359 524288 (ep1095 rfl) rfl) (Enclosure.sfrac_false_div 14292339 32768) (BSN.cos_reduce1 qz466 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 4991491784230177865728) qz442) 226375608064910080 72057594037927936 Bool.false 913183 1048576 69 1000000000000000 387034 193517 (BSN.sin_reduce_arg_pos_rat_q1 14292339 32768 226375608064910080 72057594037927936 69 4991491784230177865728 4722366482869645213696 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 913183 1048576 4991491784230177865728 4722366482869645213696 2269867665 2147483648 387412 387034 (ep1099 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1101 := nat_lit 949190639061225138734881678909688911676579019654474020334782268672276995690625

noncomputable def ep1102 := nat_lit 2846162517072101624401054491553161541102461182805528692360260534603944861290625

noncomputable def ep1103 := BSN.cos_dyadic_bound_f 2269867665 2147483648 3 2 1048576 387412 ep1101 ep62 ep1097 ep1102 ep65 ep1097 515370 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2269867665) qz20 0 2 ep1101 ep62 ep1097 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2269867665) qz21 0 2 ep1102 ep65 ep1097 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1104 := @Enclosure.Real.IsNear.sin_image qz176 qz466 Bool.false 14292339 32768 359 524288 Bool.false 515370 1048576 1 193517 (@Enclosure.Real.IsNear.recentre' qz176 Bool.false 98216205863497870257 225179981368524800 33084750025609846263 48379250000000000000000 14292339 32768 359 524288 (ep1095 rfl) rfl) (Enclosure.sfrac_false_div 14292339 32768) (BSN.sin_reduce1 qz466 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 4991491784230177865728) qz442) 226375608064910080 72057594037927936 Bool.false 515370 1048576 69 1000000000000000 387034 193517 (BSN.sin_reduce_arg_pos_rat_q1 14292339 32768 226375608064910080 72057594037927936 69 4991491784230177865728 4722366482869645213696 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 515370 1048576 4991491784230177865728 4722366482869645213696 2269867665 2147483648 387412 387034 (ep1103 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1105 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz68 (Real.cos qz176)) (@HMul.hMul Real Real Real qz0 qz68 (@Neg.neg Real Real.instNeg (Real.sin qz176))) Bool.true 184279416217 1099511627776 28427461642211 212774191672328192 Bool.true 52000575315 549755813888 14175239031945 106387095836164096 (@Enclosure.Real.IsNear.mulLit_ft qz68 (Real.cos qz176) 201799 1048576 1 1048576 913183 1048576 69996891 101458640896 184279416217 1099511627776 28427461642211 212774191672328192 qz381 (@Enclosure.Real.IsNear.recentre' (Real.cos qz176) Bool.true 913183 1048576 69996891 101458640896 913183 1048576 69996891 101458640896 (ep1100 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz68 (@Neg.neg Real Real.instNeg (Real.sin qz176)) 201799 1048576 1 1048576 257685 524288 69996891 101458640896 52000575315 549755813888 14175239031945 106387095836164096 qz381 (@Enclosure.Real.IsNear.neg (Real.sin qz176) Bool.false 257685 524288 69996891 101458640896 (@Enclosure.Real.IsNear.recentre' (Real.sin qz176) Bool.false 515370 1048576 69996891 101458640896 257685 524288 69996891 101458640896 (ep1104 rfl rfl) rfl)) rfl)

noncomputable def ep1106 := @ep1066 184279416217 1099511627776 28427461642211 212774191672328192 Bool.true 52000575315 549755813888 14175239031945 106387095836164096 Bool.false ep1067 1080925148567 549755813888 591287013561971 106387095836164096 Bool.false 17137040530986334420992 15586047567 274877906944 590897420493163 106387095836164096 (ep1068 (BSN.head_sum_c_succ qz143 26 27 rfl rfl) (ep1093 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1094 ep1105) rfl rfl

noncomputable abbrev qz177 := (@HMul.hMul Real Real Real qz268 qz438 qz601)

noncomputable def ep1107 := @Enclosure.Complex.IsNear.of_eq qz649 (Complex.mk (@HMul.hMul Real Real Real qz0 qz70 (Real.cos qz177)) (@HMul.hMul Real Real Real qz0 qz70 (@Neg.neg Real Real.instNeg (Real.sin qz177)))) Bool.false 83468039067 1099511627776 27861587021089 212774191672328192 Bool.true 190287407891 1099511627776 27965901972905 212774191672328192 (BSN.cpow_neg_s_mk qz146 132339 1000 28 qz147 rfl)

noncomputable def ep1108 := @Enclosure.Real.IsNear.mulLit_ff qz146 qz601 132339 1000 0 1 3751726938922231 1125899906842624 250000000193517 48379250000000000000 496499791370029128309 1125899906842624000 33084750025609846263 48379250000000000000000 qz148 (BSN.isNear_log_sfrac 28 1 3751726938922231 1125899906842624 250000000193517 48379250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz382) Bool.false 62943533227317076688896 18889465931478580854784 1000000000774068 193517000000000000000 3751726938922231 1125899906842624 250000000193517 48379250000000000000 (BSN.log_rat_reduce_isNear 28 1 4 56 32 293399 524288 24973259072661432 36028797018963968 193517 1000000000000000 rfl rfl rfl rfl (ep463 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1109 := nat_lit 1365171670595761838962999087833748035168900921020106114557172177108177552157281

noncomputable def ep1110 := nat_lit 1456765629636639290427258657504942970811787380259502748655958906288631458401

noncomputable def ep1111 := nat_lit 4092601480528012238308142746186234219565079188299799338174204613511955393555041

noncomputable def ep1112 := BSN.cos_dyadic_bound_f 2485556907 2147483648 3 2 1048576 387412 ep1109 ep62 ep1110 ep1111 ep65 ep1110 421209 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2485556907) qz20 0 2 ep1109 ep62 ep1110 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2485556907) qz21 0 2 ep1111 ep65 ep1110 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz467 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 462401463) qz17)

noncomputable def ep1113 := @Enclosure.Real.IsNear.cos_image qz177 qz467 Bool.false 462401463 1048576 719 1048576 Bool.false 421209 1048576 1 193517 (@Enclosure.Real.IsNear.recentre' qz177 Bool.false 496499791370029128309 1125899906842624000 33084750025609846263 48379250000000000000000 462401463 1048576 719 1048576 (ep1108 rfl) rfl) (Enclosure.sfrac_false_div 462401463 1048576) (BSN.cos_reduce0 qz467 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 174905518159987617038336) qz19) 226375608064910080 72057594037927936 Bool.false 421209 1048576 70 1000000000000000 387034 193517 (BSN.sin_reduce_arg_pos_rat_q0 462401463 1048576 226375608064910080 72057594037927936 70 174905518159987617038336 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 421209 1048576 174905518159987617038336 151115727451828646838272 2485556907 2147483648 387412 387034 (ep1112 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1114 := nat_lit 2456143594568661998701056551174742508927372227931983404003985151669688688716385

noncomputable def ep1115 := nat_lit 6430398460469941152032551596202650949047517703110964958417375273286622114753121

noncomputable def ep1116 := BSN.sin_dyadic_bound_f 2485556907 2147483648 3 2 1048576 387412 ep1114 ep94 ep1110 ep1115 ep96 ep1110 960257 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2485556907) qz15 0 2 ep1114 ep94 ep1110 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2485556907) qz16 0 2 ep1115 ep96 ep1110 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1117 := @Enclosure.Real.IsNear.sin_image qz177 qz467 Bool.false 462401463 1048576 719 1048576 Bool.false 960257 1048576 1 193517 (@Enclosure.Real.IsNear.recentre' qz177 Bool.false 496499791370029128309 1125899906842624000 33084750025609846263 48379250000000000000000 462401463 1048576 719 1048576 (ep1108 rfl) rfl) (Enclosure.sfrac_false_div 462401463 1048576) (BSN.sin_reduce0 qz467 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 174905518159987617038336) qz19) 226375608064910080 72057594037927936 Bool.false 960257 1048576 70 1000000000000000 387034 193517 (BSN.sin_reduce_arg_pos_rat_q0 462401463 1048576 226375608064910080 72057594037927936 70 174905518159987617038336 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 960257 1048576 174905518159987617038336 151115727451828646838272 2485556907 2147483648 387412 387034 (ep1116 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1118 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz70 (Real.cos qz177)) (@HMul.hMul Real Real Real qz0 qz70 (@Neg.neg Real Real.instNeg (Real.sin qz177))) Bool.false 83468039067 1099511627776 27861587021089 212774191672328192 Bool.true 190287407891 1099511627776 27965901972905 212774191672328192 (@Enclosure.Real.IsNear.mulLit_ff qz70 (Real.cos qz177) 198163 1048576 1 1048576 421209 1048576 140187299 202917281792 83468039067 1099511627776 27861587021089 212774191672328192 qz384 (@Enclosure.Real.IsNear.recentre' (Real.cos qz177) Bool.false 421209 1048576 140187299 202917281792 421209 1048576 140187299 202917281792 (ep1113 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz70 (@Neg.neg Real Real.instNeg (Real.sin qz177)) 198163 1048576 1 1048576 960257 1048576 140187299 202917281792 190287407891 1099511627776 27965901972905 212774191672328192 qz384 (@Enclosure.Real.IsNear.neg (Real.sin qz177) Bool.false 960257 1048576 140187299 202917281792 (@Enclosure.Real.IsNear.recentre' (Real.sin qz177) Bool.false 960257 1048576 140187299 202917281792 960257 1048576 140187299 202917281792 (ep1117 rfl rfl) rfl)) rfl)

noncomputable def ep1119 := @ep1063 83468039067 1099511627776 27861587021089 212774191672328192 Bool.true 190287407891 1099511627776 27965901972905 212774191672328192 Bool.false ep1064 2245318336201 1099511627776 1210435614145031 212774191672328192 Bool.true 35168763867890934874112 127943217623 1099511627776 1209760742959231 212774191672328192 (ep1065 (BSN.head_sum_c_succ qz143 27 28 rfl rfl) (ep1106 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1107 ep1118) rfl rfl

noncomputable abbrev qz178 := (@HMul.hMul Real Real Real qz268 qz438 qz602)

noncomputable def ep1120 := @Enclosure.Complex.IsNear.of_eq qz648 (Complex.mk (@HMul.hMul Real Real Real qz0 qz72 (Real.cos qz178)) (@HMul.hMul Real Real Real qz0 qz72 (@Neg.neg Real Real.instNeg (Real.sin qz178)))) Bool.false 90465562575 549755813888 13719423593741 106387095836164096 Bool.false 11826015525 137438953472 213695744499 1662298372440064 (BSN.cpow_neg_s_mk qz146 132339 1000 29 qz147 rfl)

noncomputable def ep1121 := @Enclosure.Real.IsNear.mulLit_ff qz146 qz602 132339 1000 0 1 3791236343078135 1125899906842624 250000000193517 48379250000000000000 100345685281323461553 225179981368524800 33084750025609846263 48379250000000000000000 qz148 (BSN.isNear_log_sfrac 29 1 3791236343078135 1125899906842624 250000000193517 48379250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz385) Bool.false 63606391034871975772160 18889465931478580854784 1000000000774068 193517000000000000000 3791236343078135 1125899906842624 250000000193517 48379250000000000000 (BSN.log_rat_reduce_isNear 29 1 4 58 32 311797 524288 24973259072661432 36028797018963968 193517 1000000000000000 rfl rfl rfl rfl (ep474 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1122 := nat_lit 1924569195779973899062952259989897954017505026699882961005230103860400731698145

noncomputable def ep1123 := nat_lit 894665502137295937656801499123264982839803034916867798156671914219806897121

noncomputable def ep1124 := nat_lit 5039089863848852208884859192784485545787915388824113778578587088916122228995041

noncomputable def ep1125 := BSN.sin_dyadic_bound_f 2338608837 2147483648 3 2 1048576 387412 ep1122 ep94 ep1123 ep1124 ep96 ep1123 929210 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2338608837) qz15 0 2 ep1122 ep94 ep1123 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2338608837) qz16 0 2 ep1124 ep96 ep1123 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz468 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 467271009) qz17)

noncomputable def ep1126 := @Enclosure.Real.IsNear.cos_image qz178 qz468 Bool.false 467271009 1048576 359 524288 Bool.false 929210 1048576 1 193517 (@Enclosure.Real.IsNear.recentre' qz178 Bool.false 100345685281323461553 225179981368524800 33084750025609846263 48379250000000000000000 467271009 1048576 359 524288 (ep1121 rfl) rfl) (Enclosure.sfrac_false_div 467271009 1048576) (BSN.cos_reduce3 qz468 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 164564966987205818974208) qz19) 226375608064910080 72057594037927936 Bool.false 929210 1048576 70 1000000000000000 387034 193517 (BSN.sin_reduce_arg_pos_rat_q3 467271009 1048576 226375608064910080 72057594037927936 70 164564966987205818974208 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 929210 1048576 164564966987205818974208 151115727451828646838272 2338608837 2147483648 387412 387034 (ep1125 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1127 := nat_lit 1069602737878713186562820945105109203335431593959898030690975245217653654008801

noncomputable def ep1128 := nat_lit 3207018882631864967813149232317081080040615175809860356476612391824521348232161

noncomputable def ep1129 := BSN.cos_dyadic_bound_f 2338608837 2147483648 3 2 1048576 387412 ep1127 ep62 ep1123 ep1128 ep65 ep1123 485880 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2338608837) qz20 0 2 ep1127 ep62 ep1123 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2338608837) qz21 0 2 ep1128 ep65 ep1123 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1130 := @Enclosure.Real.IsNear.sin_image qz178 qz468 Bool.false 467271009 1048576 359 524288 Bool.true 485880 1048576 1 193517 (@Enclosure.Real.IsNear.recentre' qz178 Bool.false 100345685281323461553 225179981368524800 33084750025609846263 48379250000000000000000 467271009 1048576 359 524288 (ep1121 rfl) rfl) (Enclosure.sfrac_false_div 467271009 1048576) (BSN.sin_reduce3 qz468 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 164564966987205818974208) qz19) 226375608064910080 72057594037927936 Bool.false 485880 1048576 70 1000000000000000 387034 193517 (BSN.sin_reduce_arg_pos_rat_q3 467271009 1048576 226375608064910080 72057594037927936 70 164564966987205818974208 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 485880 1048576 164564966987205818974208 151115727451828646838272 2338608837 2147483648 387412 387034 (ep1129 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1131 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz72 (Real.cos qz178)) (@HMul.hMul Real Real Real qz0 qz72 (@Neg.neg Real Real.instNeg (Real.sin qz178))) Bool.false 90465562575 549755813888 13719423593741 106387095836164096 Bool.false 11826015525 137438953472 213695744499 1662298372440064 (@Enclosure.Real.IsNear.mulLit_ff qz72 (Real.cos qz178) 194715 1048576 1 1048576 464605 524288 69996891 101458640896 90465562575 549755813888 13719423593741 106387095836164096 qz387 (@Enclosure.Real.IsNear.recentre' (Real.cos qz178) Bool.false 929210 1048576 69996891 101458640896 464605 524288 69996891 101458640896 (ep1126 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz72 (@Neg.neg Real Real.instNeg (Real.sin qz178)) 194715 1048576 1 1048576 60735 131072 69996891 101458640896 11826015525 137438953472 213695744499 1662298372440064 qz387 (@Enclosure.Real.IsNear.neg (Real.sin qz178) Bool.true 60735 131072 69996891 101458640896 (@Enclosure.Real.IsNear.recentre' (Real.sin qz178) Bool.true 485880 1048576 69996891 101458640896 60735 131072 69996891 101458640896 (ep1130 rfl rfl) rfl)) rfl)

noncomputable def ep1132 := @ep1060 90465562575 549755813888 13719423593741 106387095836164096 Bool.false 11826015525 137438953472 213695744499 1662298372440064 Bool.false ep1061 2426249461351 1099511627776 1237874461332513 212774191672328192 Bool.true 4581540353948470214656 33335093423 1099511627776 1237113798255103 212774191672328192 (ep1062 (BSN.head_sum_c_succ qz143 28 29 rfl rfl) (ep1119 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1120 ep1131) rfl rfl

noncomputable abbrev qz179 := (@HMul.hMul Real Real Real qz268 qz438 qz603)

noncomputable def ep1133 := @Enclosure.Complex.IsNear.of_eq qz647 (Complex.mk (@HMul.hMul Real Real Real qz0 qz74 (Real.cos qz179)) (@HMul.hMul Real Real Real qz0 qz74 (@Neg.neg Real Real.instNeg (Real.sin qz179)))) Bool.true 32626290389 274877906944 6733222147993 53193547918082048 Bool.false 152531635921 1099511627776 26955153690407 212774191672328192 (BSN.cpow_neg_s_mk qz146 132339 1000 30 qz147 rfl)

noncomputable def ep1134 := @Enclosure.Real.IsNear.mulLit_ff qz146 qz603 132339 1000 0 1 3829405717437687 1125899906842624 250000000193517 48379250000000000000 506779723239986059893 1125899906842624000 33084750025609846263 48379250000000000000000 qz148 (BSN.isNear_log_sfrac 30 1 3829405717437687 1125899906842624 250000000193517 48379250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz388) Bool.false 64246766873087041339392 18889465931478580854784 1000000000774068 193517000000000000000 3829405717437687 1125899906842624 250000000193517 48379250000000000000 (BSN.log_rat_reduce_isNear 30 1 4 60 32 329571 524288 24973259072661432 36028797018963968 193517 1000000000000000 rfl rfl rfl rfl (ep485 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1135 := nat_lit 421757653327256026844120542822344326046353774766308854027714216526529798635776

noncomputable def ep1136 := nat_lit 139245650811184200281093612161272777297605989705868489744123084483772580096

noncomputable def ep1137 := nat_lit 1264994468680145712131799441242710432584466112319514825103654403410621850747136

noncomputable def ep1138 := BSN.cos_dyadic_bound_f 1853415134 2147483648 3 2 1048576 387412 ep1135 ep62 ep1136 ep1137 ep65 ep1136 681692 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1853415134) qz20 0 2 ep1135 ep62 ep1136 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1853415134) qz21 0 2 ep1137 ep65 ep1136 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz469 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 117993849) qz566)

noncomputable def ep1139 := @Enclosure.Real.IsNear.cos_image qz179 qz469 Bool.false 117993849 262144 359 524288 Bool.true 681692 1048576 1 193517 (@Enclosure.Real.IsNear.recentre' qz179 Bool.false 506779723239986059893 1125899906842624000 33084750025609846263 48379250000000000000000 117993849 262144 359 524288 (ep1134 rfl) rfl) (Enclosure.sfrac_false_div 117993849 262144) (BSN.cos_reduce2 qz469 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 32605623866750935236608) qz325) 226375608064910080 72057594037927936 Bool.false 681692 1048576 71 1000000000000000 387034 193517 (BSN.sin_reduce_arg_pos_rat_q2 117993849 262144 226375608064910080 72057594037927936 71 32605623866750935236608 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 681692 1048576 32605623866750935236608 37778931862957161709568 1853415134 2147483648 387412 387034 (ep1138 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1140 := nat_lit 759052379468411900959192102190490768661598709787591242458090291280166619480320

noncomputable def ep1141 := nat_lit 1987768881839765442378381354174452809617133830222262800311603135025557895414016

noncomputable def ep1142 := BSN.sin_dyadic_bound_f 1853415134 2147483648 3 2 1048576 387412 ep1140 ep94 ep1136 ep1141 ep96 ep1136 796747 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1853415134) qz15 0 2 ep1140 ep94 ep1136 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1853415134) qz16 0 2 ep1141 ep96 ep1136 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1143 := @Enclosure.Real.IsNear.sin_image qz179 qz469 Bool.false 117993849 262144 359 524288 Bool.true 796747 1048576 1 193517 (@Enclosure.Real.IsNear.recentre' qz179 Bool.false 506779723239986059893 1125899906842624000 33084750025609846263 48379250000000000000000 117993849 262144 359 524288 (ep1134 rfl) rfl) (Enclosure.sfrac_false_div 117993849 262144) (BSN.sin_reduce2 qz469 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 32605623866750935236608) qz325) 226375608064910080 72057594037927936 Bool.false 796747 1048576 71 1000000000000000 387034 193517 (BSN.sin_reduce_arg_pos_rat_q2 117993849 262144 226375608064910080 72057594037927936 71 32605623866750935236608 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 796747 1048576 32605623866750935236608 37778931862957161709568 1853415134 2147483648 387412 387034 (ep1142 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1144 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz74 (Real.cos qz179)) (@HMul.hMul Real Real Real qz0 qz74 (@Neg.neg Real Real.instNeg (Real.sin qz179))) Bool.true 32626290389 274877906944 6733222147993 53193547918082048 Bool.false 152531635921 1099511627776 26955153690407 212774191672328192 (@Enclosure.Real.IsNear.mulLit_ft qz74 (Real.cos qz179) 191443 1048576 1 1048576 170423 262144 69996891 101458640896 32626290389 274877906944 6733222147993 53193547918082048 qz390 (@Enclosure.Real.IsNear.recentre' (Real.cos qz179) Bool.true 681692 1048576 69996891 101458640896 170423 262144 69996891 101458640896 (ep1139 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz74 (@Neg.neg Real Real.instNeg (Real.sin qz179)) 191443 1048576 1 1048576 796747 1048576 69996891 101458640896 152531635921 1099511627776 26955153690407 212774191672328192 qz390 (@Enclosure.Real.IsNear.neg (Real.sin qz179) Bool.true 796747 1048576 69996891 101458640896 (@Enclosure.Real.IsNear.recentre' (Real.sin qz179) Bool.true 796747 1048576 69996891 101458640896 796747 1048576 69996891 101458640896 (ep1143 rfl rfl) rfl)) rfl)

noncomputable def ep1145 := @ep1058 32626290389 274877906944 6733222147993 53193547918082048 Bool.false 152531635921 1099511627776 26955153690407 212774191672328192 Bool.false 631049388006268448276480 2295744299795 1099511627776 1264807349924485 212774191672328192 Bool.false 131057984467247141224448 59598271249 549755813888 632034475972755 106387095836164096 (ep1059 (BSN.head_sum_c_succ qz143 29 30 rfl rfl) (ep1132 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1133 ep1144) rfl rfl

noncomputable abbrev qz180 := (@HMul.hMul Real Real Real qz268 qz438 qz604)

noncomputable def ep1146 := @Enclosure.Complex.IsNear.of_eq qz646 (Complex.mk (@HMul.hMul Real Real Real qz0 qz76 (Real.cos qz180)) (@HMul.hMul Real Real Real qz0 qz76 (@Neg.neg Real Real.instNeg (Real.sin qz180)))) Bool.true 92976332339 1099511627776 26460566565307 212774191672328192 Bool.true 174219956307 1099511627776 26544048250971 212774191672328192 (BSN.cpow_neg_s_mk qz146 132339 1000 31 qz147 rfl)

noncomputable def ep1147 := @Enclosure.Real.IsNear.mulLit_ff qz146 qz604 132339 1000 0 1 3866325256314103 1125899906842624 250000000193517 48379250000000000000 511665618095352076917 1125899906842624000 33084750025609846263 48379250000000000000000 qz148 (BSN.isNear_log_sfrac 31 1 3866325256314103 1125899906842624 250000000193517 48379250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz391) Bool.false 64866173951437069877248 18889465931478580854784 1000000000774068 193517000000000000000 3866325256314103 1125899906842624 250000000193517 48379250000000000000 (BSN.log_rat_reduce_isNear 31 1 4 62 32 346763 524288 24973259072661432 36028797018963968 193517 1000000000000000 rfl rfl rfl rfl (ep496 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1148 := nat_lit 1228249953484062194871036955058507776

noncomputable def ep1149 := BSN.sin_dyadic_bound_f 1052741368 2147483648 2 1 1048576 387412 ep1148 ep57 ep1148 ep1148 ep58 ep1148 493691 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1052741368) qz15 0 1 ep1148 ep57 ep1148 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1052741368) qz16 0 1 ep1148 ep58 ep1148 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz470 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 119131435) qz566)

noncomputable def ep1150 := @Enclosure.Real.IsNear.cos_image qz180 qz470 Bool.false 119131435 262144 359 524288 Bool.true 493691 1048576 1 193517 (@Enclosure.Real.IsNear.recentre' qz180 Bool.false 511665618095352076917 1125899906842624000 33084750025609846263 48379250000000000000000 119131435 262144 359 524288 (ep1147 rfl) rfl) (Enclosure.sfrac_false_div 119131435 262144) (BSN.cos_reduce1 qz470 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 18520022007508149207040) qz325) 226375608064910080 72057594037927936 Bool.false 493691 1048576 72 1000000000000000 387034 193517 (BSN.sin_reduce_arg_pos_rat_q1 119131435 262144 226375608064910080 72057594037927936 72 18520022007508149207040 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 493691 1048576 18520022007508149207040 37778931862957161709568 1052741368 2147483648 387412 387034 (ep1149 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1151 := BSN.cos_dyadic_bound_f 1052741368 2147483648 2 1 1048576 387412 ep1148 ep76 ep1148 ep1148 ep77 ep1148 925083 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1052741368) qz20 0 1 ep1148 ep76 ep1148 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1052741368) qz21 0 1 ep1148 ep77 ep1148 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1152 := @Enclosure.Real.IsNear.sin_image qz180 qz470 Bool.false 119131435 262144 359 524288 Bool.false 925083 1048576 1 193517 (@Enclosure.Real.IsNear.recentre' qz180 Bool.false 511665618095352076917 1125899906842624000 33084750025609846263 48379250000000000000000 119131435 262144 359 524288 (ep1147 rfl) rfl) (Enclosure.sfrac_false_div 119131435 262144) (BSN.sin_reduce1 qz470 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 18520022007508149207040) qz325) 226375608064910080 72057594037927936 Bool.false 925083 1048576 72 1000000000000000 387034 193517 (BSN.sin_reduce_arg_pos_rat_q1 119131435 262144 226375608064910080 72057594037927936 72 18520022007508149207040 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 925083 1048576 18520022007508149207040 37778931862957161709568 1052741368 2147483648 387412 387034 (ep1151 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1153 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz76 (Real.cos qz180)) (@HMul.hMul Real Real Real qz0 qz76 (@Neg.neg Real Real.instNeg (Real.sin qz180))) Bool.true 92976332339 1099511627776 26460566565307 212774191672328192 Bool.true 174219956307 1099511627776 26544048250971 212774191672328192 (@Enclosure.Real.IsNear.mulLit_ft qz76 (Real.cos qz180) 188329 1048576 1 1048576 493691 1048576 69996891 101458640896 92976332339 1099511627776 26460566565307 212774191672328192 qz393 (@Enclosure.Real.IsNear.recentre' (Real.cos qz180) Bool.true 493691 1048576 69996891 101458640896 493691 1048576 69996891 101458640896 (ep1150 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz76 (@Neg.neg Real Real.instNeg (Real.sin qz180)) 188329 1048576 1 1048576 925083 1048576 69996891 101458640896 174219956307 1099511627776 26544048250971 212774191672328192 qz393 (@Enclosure.Real.IsNear.neg (Real.sin qz180) Bool.false 925083 1048576 69996891 101458640896 (@Enclosure.Real.IsNear.recentre' (Real.sin qz180) Bool.false 925083 1048576 69996891 101458640896 925083 1048576 69996891 101458640896 (ep1152 rfl rfl) rfl)) rfl)

noncomputable def ep1154 := @ep1055 92976332339 1099511627776 26460566565307 212774191672328192 Bool.true 174219956307 1099511627776 26544048250971 212774191672328192 Bool.false ep1056 68836498983 34359738368 20176061195153 3324596744880128 Bool.true 30249441641463013179392 55023413809 1099511627776 1290613000196481 212774191672328192 (ep1057 (BSN.head_sum_c_succ qz143 30 31 rfl rfl) (ep1145 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1146 ep1153) rfl rfl

noncomputable abbrev qz181 := (@HMul.hMul Real Real Real qz268 qz438 qz605)

noncomputable def ep1155 := @Enclosure.Complex.IsNear.of_eq qz645 (Complex.mk (@HMul.hMul Real Real Real qz0 qz78 (Real.cos qz181)) (@HMul.hMul Real Real Real qz0 qz78 (@Neg.neg Real Real.instNeg (Real.sin qz181)))) Bool.false 194326227865 1099511627776 26152681921183 212774191672328192 Bool.false 1992466887 549755813888 12976983817557 106387095836164096 (BSN.cpow_neg_s_mk qz146 132339 1000 32 qz147 rfl)

noncomputable def ep1156 := @Enclosure.Real.IsNear.mulLit_ff qz146 qz605 132339 1000 0 1 15608286920413395 4503599627370496 200000000193517 38703400000000000000 413117016552117656181 900719925474099200 26467800025609846263 38703400000000000000000 qz148 (BSN.isNear_log_sfrac 32 1 15608286920413395 4503599627370496 200000000193517 38703400000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz394) Bool.false 65465900263437584302080 18889465931478580854784 1000000000967585 193517000000000000000 15608286920413395 4503599627370496 200000000193517 38703400000000000000 (BSN.log_rat_reduce_isNear 32 1 5 64 64 0 524288 24973259072661432 36028797018963968 193517 1000000000000000 rfl rfl rfl rfl (ep511 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1157 := nat_lit 7915963180747796863384304052317298122195520293447553215688597739205423670558720

noncomputable def ep1158 := nat_lit 15092023090466749367768224317457694285562079770936098911737439749086495440896

noncomputable def ep1159 := nat_lit 20707849816954902762268219202412277862621166925114457119041609652610921954082816

noncomputable def ep1160 := BSN.sin_dyadic_bound_f 3329227188 2147483648 3 2 1048576 387412 ep1157 ep94 ep1158 ep1159 ep96 ep1158 1048355 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3329227188) qz15 0 2 ep1157 ep94 ep1158 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3329227188) qz16 0 2 ep1159 ep96 ep1158 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz471 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 30058219) (@Nat.cast Real Real.instNatCast 65536))

noncomputable def ep1161 := @Enclosure.Real.IsNear.cos_image qz181 qz471 Bool.false 30058219 65536 359 524288 Bool.false 1048355 1048576 1 193517 (@Enclosure.Real.IsNear.recentre' qz181 Bool.false 413117016552117656181 900719925474099200 26467800025609846263 38703400000000000000000 30058219 65536 359 524288 (ep1156 rfl) rfl) (Enclosure.sfrac_false_div 30058219 65536) (BSN.cos_reduce3 qz471 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 14642096018957835173888) qz377) 226375608064910080 72057594037927936 Bool.false 1048355 1048576 72 1000000000000000 387034 193517 (BSN.sin_reduce_arg_pos_rat_q3 30058219 65536 226375608064910080 72057594037927936 72 14642096018957835173888 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1048355 1048576 14642096018957835173888 9444732965739290427392 3329227188 2147483648 387412 387034 (ep1160 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1162 := nat_lit 4404464888455650146043621462095146820902205531813501163787770939447051592728576

noncomputable def ep1163 := nat_lit 13183210619186016939395327937650525074135492435898631293539837938842981787303936

noncomputable def ep1164 := BSN.cos_dyadic_bound_f 3329227188 2147483648 3 2 1048576 387412 ep1162 ep62 ep1158 ep1163 ep65 ep1158 21498 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3329227188) qz20 0 2 ep1162 ep62 ep1158 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3329227188) qz21 0 2 ep1163 ep65 ep1158 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1165 := @Enclosure.Real.IsNear.sin_image qz181 qz471 Bool.false 30058219 65536 359 524288 Bool.true 21498 1048576 1 193517 (@Enclosure.Real.IsNear.recentre' qz181 Bool.false 413117016552117656181 900719925474099200 26467800025609846263 38703400000000000000000 30058219 65536 359 524288 (ep1156 rfl) rfl) (Enclosure.sfrac_false_div 30058219 65536) (BSN.sin_reduce3 qz471 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 14642096018957835173888) qz377) 226375608064910080 72057594037927936 Bool.false 21498 1048576 72 1000000000000000 387034 193517 (BSN.sin_reduce_arg_pos_rat_q3 30058219 65536 226375608064910080 72057594037927936 72 14642096018957835173888 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 21498 1048576 14642096018957835173888 9444732965739290427392 3329227188 2147483648 387412 387034 (ep1164 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1166 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz78 (Real.cos qz181)) (@HMul.hMul Real Real Real qz0 qz78 (@Neg.neg Real Real.instNeg (Real.sin qz181))) Bool.false 194326227865 1099511627776 26152681921183 212774191672328192 Bool.false 1992466887 549755813888 12976983817557 106387095836164096 (@Enclosure.Real.IsNear.mulLit_ff qz78 (Real.cos qz181) 185363 1048576 1 1048576 1048355 1048576 69996891 101458640896 194326227865 1099511627776 26152681921183 212774191672328192 qz396 (@Enclosure.Real.IsNear.recentre' (Real.cos qz181) Bool.false 1048355 1048576 69996891 101458640896 1048355 1048576 69996891 101458640896 (ep1161 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz78 (@Neg.neg Real Real.instNeg (Real.sin qz181)) 185363 1048576 1 1048576 10749 524288 69996891 101458640896 1992466887 549755813888 12976983817557 106387095836164096 qz396 (@Enclosure.Real.IsNear.neg (Real.sin qz181) Bool.true 10749 524288 69996891 101458640896 (@Enclosure.Real.IsNear.recentre' (Real.sin qz181) Bool.true 21498 1048576 69996891 101458640896 10749 524288 69996891 101458640896 (ep1165 rfl rfl) rfl)) rfl)

noncomputable def ep1167 := @ep1053 194326227865 1099511627776 26152681921183 212774191672328192 Bool.false 1992466887 549755813888 12976983817557 106387095836164096 Bool.false 82363529394681049776128 2397094195321 1099511627776 1317420598410975 212774191672328192 Bool.true 28058701131247863726080 51038480035 1099511627776 1316566967831595 212774191672328192 (ep1054 (BSN.head_sum_c_succ qz143 31 32 rfl rfl) (ep1154 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1155 ep1166) rfl rfl

theorem EMRow44.d16 : Enclosure.Complex.IsNear qz173 Bool.false 2397094195321 1099511627776 1317420598410975 212774191672328192 Bool.true 51038480035 1099511627776 1316566967831595 212774191672328192 := ep1052 (BSN.head_sum_c_succ qz143 32 33 rfl rfl) (ep1167 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

theorem EMRow44.d17 : @Eq Nat (Nat.pow 34 1) 34 := @Eq.refl Nat 34

noncomputable def ep1168 := nat_lit 3937856506233751176424906779423

noncomputable def ep1169 := nat_lit 1900433589130765056187616460800

noncomputable def ep1170 := nat_lit 129212728040144213154640788497116065746101

noncomputable def ep1171 := nat_lit 18148098328882094554219818209057917894656000

noncomputable abbrev qz653 := (@HAdd.hAdd Complex Complex Complex qz665 (@HAdd.hAdd Complex Complex Complex qz665 qz668 (@HMul.hMul Complex Complex Complex qz667 Complex.I (@HDiv.hDiv Complex Complex Complex qz669 (↑qz672) (2 : Complex)))) (@Nat.cast Complex Complex.instNatCast 2))

noncomputable abbrev qz472 := qz653

noncomputable abbrev qz182 := (Complex.Stirling.logGammaStirling 1 qz472)

noncomputable abbrev qz654 := (@HAdd.hAdd Complex Complex Complex qz665 qz668 (@HMul.hMul Complex Complex Complex qz667 Complex.I (@HDiv.hDiv Complex Complex Complex qz669 (↑qz672) (2 : Complex))))

noncomputable abbrev qz473 := qz654

noncomputable abbrev qz183 := qz473

noncomputable abbrev qz184 := (@HMul.hMul Real Real Real qz268 (@HDiv.hDiv Real Real Real qz271 qz438 (2 : Real)) (Real.log Real.pi))

noncomputable def ep1172 := Complex.re (@HMul.hMul Complex Complex Complex qz80 (Complex.exp (@HMul.hMul Complex Complex Complex qz80 Complex.I ↑(@HSub.hSub Real Real Real qz401 (Complex.im (@HSub.hSub Complex Complex Complex qz81 qz182 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz183 (@Nat.cast Complex Complex.instNatCast j))))) qz184))) (zetaApproximant qz143 1 34))

noncomputable def ep1173 := @Enclosure.Real.IsNear.of_eq ep1172 (@HSub.hSub Real Real Real qz401 (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz401 (Complex.im (@HSub.hSub Complex Complex Complex qz81 qz182 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz183 (@Nat.cast Complex Complex.instNatCast j))))) qz184)) (Complex.re (zetaApproximant qz143 1 34))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz401 (Complex.im (@HSub.hSub Complex Complex Complex qz81 qz182 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz183 (@Nat.cast Complex Complex.instNatCast j))))) qz184)) (Complex.im (zetaApproximant qz143 1 34))))

noncomputable def ep1174 := nat_lit 6694361087395411925100992335983

noncomputable def ep1175 := @Enclosure.Real.IsNear.subLit_tt_n (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz401 (Complex.im (@HSub.hSub Complex Complex Complex qz81 qz182 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz183 (@Nat.cast Complex Complex.instNatCast j))))) qz184)) (Complex.re (zetaApproximant qz143 1 34))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz401 (Complex.im (@HSub.hSub Complex Complex Complex qz81 qz182 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz183 (@Nat.cast Complex Complex.instNatCast j))))) qz184)) (Complex.im (zetaApproximant qz143 1 34))) ep1174

noncomputable def ep1176 := nat_lit 3230737101522300595518947983360

noncomputable def ep1177 := nat_lit 12910291530888793727814601639571988811591

noncomputable def ep1178 := nat_lit 1814809832888209455421981820905791789465600

noncomputable def ep1179 := nat_lit 50267980349251786508109639

noncomputable def ep1180 := nat_lit 32307371015223005955189479833600

noncomputable def ep1181 := nat_lit 36604243752091958831590700465392543397

noncomputable def ep1182 := nat_lit 6049366109627364851406606069685972631552000

noncomputable def ep1183 := nat_lit 216277044957726162539990715237116827869551293273823489304821760

noncomputable def ep1184 := @Enclosure.Real.IsNear.mulLit_tf (Real.cos (@HSub.hSub Real Real Real qz401 (Complex.im (@HSub.hSub Complex Complex Complex qz81 qz182 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz183 (@Nat.cast Complex Complex.instNatCast j))))) qz184)) (Complex.re (zetaApproximant qz143 1 34)) 1048575 1048576 71682281

noncomputable def ep1185 := nat_lit 159606158057254176503850281

noncomputable def ep1186 := nat_lit 77026774919564738166784000

noncomputable def ep1187 := nat_lit 285283821997606286380971347749

noncomputable def ep1188 := nat_lit 44717971206328228307464617984000

noncomputable def ep1189 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HSub.hSub Real Real Real qz401 (Complex.im (@HSub.hSub Complex Complex Complex qz81 qz182 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz183 (@Nat.cast Complex Complex.instNatCast j))))) qz184)) Bool.true 1048575 1048576 71682281

noncomputable abbrev qz474 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 35412727) qz566)

noncomputable def ep1190 := @Enclosure.Real.IsNear.cos_image (@HSub.hSub Real Real Real qz401 (Complex.im (@HSub.hSub Complex Complex Complex qz81 qz182 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz183 (@Nat.cast Complex Complex.instNatCast j))))) qz184) qz474 Bool.false 35412727 262144 365

noncomputable def ep1191 := nat_lit 70531970531770113815840089

noncomputable def ep1192 := nat_lit 202917281792000000000000000000

noncomputable def ep1193 := @Enclosure.Real.IsNear.recentre' (@HSub.hSub Real Real Real qz401 (Complex.im (@HSub.hSub Complex Complex Complex qz81 qz182 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz183 (@Nat.cast Complex Complex.instNatCast j))))) qz184) Bool.false 608386017607191561711 4503599627370496000 ep1191 ep1192

noncomputable def ep1194 := nat_lit 19312278005770113815840089

noncomputable def ep1195 := @Enclosure.Real.IsNear.subLit_ff_p (Complex.im (@HSub.hSub Complex Complex Complex qz81 qz182 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz183 (@Nat.cast Complex Complex.instNatCast j))))) qz184 949516513600131499503 4503599627370496000 ep1194 ep1192 9928204119 131072000

noncomputable def ep1196 := nat_lit 79742372099809812376584192000

noncomputable def ep1197 := nat_lit 9015489421446088850631343

noncomputable def ep1198 := @Enclosure.Complex.IsNear.im_isNear (@HSub.hSub Complex Complex Complex qz81 qz182 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz183 (@Nat.cast Complex Complex.instNatCast j)))) Bool.true 58585053748199385541 562949953421312000 ep1197 ep551 Bool.false 949516513600131499503 4503599627370496000

noncomputable def ep1199 := nat_lit 8884417420837337005255343

noncomputable def ep1200 := nat_lit 18263702005567196534048089

noncomputable def ep1201 := @Enclosure.Complex.IsNear.subLitP qz182 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz183 (@Nat.cast Complex Complex.instNatCast j))) Bool.true 53864930068354151041 562949953421312000 ep1199 ep551 Bool.false 963562910616464347503 4503599627370496000 ep1200

noncomputable def ep1202 := nat_lit 65960906557467808179392418188099584

noncomputable def ep1203 := nat_lit 267265138551980294908465987838803968

noncomputable abbrev qz475 := (@HSub.hSub Complex Complex Complex qz607 qz653 qz610)

noncomputable abbrev qz476 := (Complex.log qz653)

noncomputable abbrev qz185 := (@HSub.hSub Complex Complex Complex qz398 (@HMul.hMul Complex Complex Complex qz397 qz475 qz476) qz472)

noncomputable abbrev qz186 := qz472

noncomputable def ep1204 := @Enclosure.Complex.IsNear.of_eq qz182 (@HAdd.hAdd Complex Complex Complex qz4 (@HAdd.hAdd Complex Complex Complex qz4 qz185 qz86) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz80 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz89 qz186 (@HSub.hSub Int Int Int qz408 qz91 (@HMul.hMul Int Int Int qz409 qz92 (@Nat.cast Int instNatCastInt k)))))) Bool.true 53864930068354151041

noncomputable def ep1205 := @Enclosure.Complex.IsNear.addLitP (@HAdd.hAdd Complex Complex Complex qz4 qz185 qz86) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz80 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz89 qz186 (@HSub.hSub Int Int Int qz408 qz91 (@HMul.hMul Int Int Int qz409 qz92 (@Nat.cast Int instNatCastInt k))))) Bool.true 53864954148189287041 562949953421312000

noncomputable def ep1206 := nat_lit 3701569808718529972271029682176

noncomputable def ep1207 := nat_lit 33107769509890284573402914095104000

noncomputable def ep1208 := @ep1205 135565417575241466513 774068000000000000000000 Bool.false 963568575863223570799 4503599627370496000 4354343769249716541 48379250000000000000000 Bool.false 2939433 68719476736 3 68719476736 Bool.true 43222402643 34359738368000 44113 34359738368000 Bool.true ep1206 53864930068354151041 562949953421312000 ep1199 ep551 Bool.false ep1207

noncomputable def ep1209 := @Enclosure.Complex.IsNear.addLitP qz185 qz86 Bool.true 54382270074090599041 562949953421312000 134089000033737560263 774068000000000000000000

noncomputable def ep1210 := nat_lit 7060187270111466231037952

noncomputable def ep1211 := @ep1209 Bool.false 963568575863223570799 4503599627370496000 4354343769249716541 48379250000000000000000 Bool.false 120447 131072 1 524288 Bool.false 0 1 0 1 Bool.true ep1210 53864954148189287041 562949953421312000 135565417575241466513 774068000000000000000000 Bool.false 963568575863223570799 963568575863223570799 4503599627370496000

noncomputable abbrev qz187 := (@HMul.hMul Complex Complex Complex qz397 qz475 qz476)

noncomputable def ep1212 := @Enclosure.Complex.IsNear.subLitP qz187 qz186 Bool.true 53115632678892647041 562949953421312000 134089000033737560263 774068000000000000000000 Bool.false 1261569511406515605871

noncomputable def ep1213 := nat_lit 3854274303452894283196000

noncomputable def ep1214 := @ep1212 4503599627370496000 4354343769249716541 48379250000000000000000 Bool.false 9000 4000 0 1 Bool.false 264678 4000 0 1 Bool.true 217529080296362396164000 54382270074090599041 562949953421312000 134089000033737560263 774068000000000000000000 Bool.false ep1213 963568575863223570799 4503599627370496000 4354343769249716541 48379250000000000000000

noncomputable abbrev qz188 := qz475

noncomputable abbrev qz189 := qz476

noncomputable def ep1215 := @Enclosure.Complex.IsNear.mul qz188 qz189 Bool.true 53115632678892647041 562949953421312000 134089000033737560263 774068000000000000000000 Bool.false 1261569511406515605871 4503599627370496000 4354343769249716541

noncomputable abbrev qz190 := (Complex.re qz475)

noncomputable abbrev qz191 := (Complex.re qz476)

noncomputable abbrev qz192 := (Complex.im qz475)

noncomputable abbrev qz193 := (Complex.im qz476)

noncomputable def ep1216 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 qz190 qz191) (@HMul.hMul Real Real Real qz0 qz192 qz193) 66089379243974723 9007199254740992 875000004063857 387034000000000000000 114492437763282134457 1125899906842624000

noncomputable def ep1217 := nat_lit 956846174160836261727557055460409344

noncomputable def ep1218 := @Enclosure.Real.IsNear.mulLit_ff qz190 qz191 7000 4000 0 1 9441339891996389 2251799813685248 125000000580551 96758500000000000000

noncomputable def ep1219 := @Enclosure.Complex.IsNear.re_isNear qz188 Bool.false 7000 4000 0 1 Bool.false 264678 4000 0 1

noncomputable abbrev qz655 := (Enclosure.sfrac Bool.false 264678 4000)

noncomputable abbrev qz477 := qz655

noncomputable def ep1220 := @Enclosure.Complex.IsNear.of_eq qz188 (Complex.mk (Enclosure.sfrac Bool.false 7000 4000) qz477) Bool.false 7000 4000 0 1 Bool.false 264678 4000 0

noncomputable abbrev qz478 := (Complex.log (Complex.mk qz614 qz655))

noncomputable def ep1221 := @Enclosure.Complex.IsNear.of_eq qz189 qz478 Bool.false 9441339891996389 2251799813685248 125000000580551 96758500000000000000 Bool.false 865145102828963 562949953421312 1000000000193517 387034000000000000000

noncomputable def ep1222 := BSN.log_dyadic_bound 4599443684 135671443684 2 1 55220221893902350475568 1048576 387034 21154882202287491856 21154882202287491856 71123 140270887368 131072000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 4599443684) (BSN.artanhQ 135671443684) 0 1 21154882202287491856 55220221893902350475568 21154882202287491856 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz656 := (Real.log (Enclosure.sfrac Bool.false 70135443684 16000000))

noncomputable def ep1223 := @Enclosure.Real.IsNear.mulLit_ff qz100 qz656 1 2 0 1 9441339891996389 1125899906842624 125000000580551 48379250000000000000 9441339891996389 2251799813685248 125000000580551 96758500000000000000 qz412 (BSN.isNear_log_sfrac 70135443684 16000000 9441339891996389 1125899906842624 125000000580551 48379250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 70135443684) qz616)) Bool.false 316798797394880178946048 37778931862957161709568 1000000004644408 387034000000000000000 9441339891996389 1125899906842624 125000000580551 48379250000000000000 (BSN.log_rat_reduce_isNear 70135443684 16000000 12 140270887368 131072000000 71123 1048576 24973259072661432 36028797018963968 387034 1000000000000000 rfl rfl rfl rfl (ep1222 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1224 := BSN.arctan_dyadic_bound_f 9000 264678 1 0 1048576 387034 0 1 1 0 1 1 35641 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 9000) (BSN.arctanEvenQ 264678) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 9000) (BSN.arctanOddQ 264678) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz479 := (Real.arctan (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 9000) (@Nat.cast Real Real.instNatCast 264678)))

noncomputable def ep1225 := @Enclosure.Real.IsNear.subLit_ff_p qz101 qz479 884279719003555 562949953421312 1 2000000000000000 35641 1048576 1 387034 907170391343982706688 865145102828963 562949953421312 1000000000193517 387034000000000000000 qz102 (ep1224 rfl) rfl rfl

noncomputable abbrev qz480 := (Complex.mk qz614 qz655)

noncomputable abbrev qz481 := (Real.arctan (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 264678) (@Nat.cast Real Real.instNatCast 9000)))

noncomputable def ep1226 := @Enclosure.Complex.IsNear.re_isNear qz189 Bool.false 9441339891996389 2251799813685248 125000000580551 96758500000000000000 Bool.false 865145102828963 562949953421312 1000000000193517 387034000000000000000 (ep1221 (@congrArg Complex Complex qz186 qz480 Complex.log (BSN.w_shift_mk qz146 Bool.false 132339 1000 2 qz147 rfl)) (@Enclosure.Complex.IsNear.of_parts qz478 Bool.false 9441339891996389 2251799813685248 125000000580551 96758500000000000000 Bool.false 865145102828963 562949953421312 1000000000193517 387034000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz478) (@HMul.hMul Real Real Real qz0 qz100 qz656) Bool.false 9441339891996389 2251799813685248 125000000580551 96758500000000000000 (Enclosure.clog_re_eq 9000 264678 4000 70135443684 16000000 rfl rfl rfl) (ep1223 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz478) qz481 Bool.false 865145102828963 562949953421312 1000000000193517 387034000000000000000 (Enclosure.clog_im_eq 9000 264678 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz481 (@HSub.hSub Real Real Real qz401 qz101 qz479) Bool.false 865145102828963 562949953421312 1000000000193517 387034000000000000000 (BSN.arctan_recip 264678 9000 rfl rfl) ep1225))))

noncomputable def ep1227 := @Enclosure.Real.IsNear.mulLit_ff qz192 qz193 264678 4000 0 1 865145102828963 562949953421312 1000000000193517 387034000000000000000

noncomputable def ep1228 := @Enclosure.Complex.IsNear.im_isNear qz188 Bool.false 7000 4000 0 1 Bool.false 264678 4000 0 1

noncomputable def ep1229 := @Enclosure.Complex.IsNear.im_isNear qz189 Bool.false 9441339891996389 2251799813685248 125000000580551 96758500000000000000 Bool.false 865145102828963 562949953421312 1000000000193517 387034000000000000000 (ep1221 (@congrArg Complex Complex qz186 qz480 Complex.log (BSN.w_shift_mk qz146 Bool.false 132339 1000 2 qz147 rfl)) (@Enclosure.Complex.IsNear.of_parts qz478 Bool.false 9441339891996389 2251799813685248 125000000580551 96758500000000000000 Bool.false 865145102828963 562949953421312 1000000000193517 387034000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz478) (@HMul.hMul Real Real Real qz0 qz100 qz656) Bool.false 9441339891996389 2251799813685248 125000000580551 96758500000000000000 (Enclosure.clog_re_eq 9000 264678 4000 70135443684 16000000 rfl rfl rfl) (ep1223 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz478) qz481 Bool.false 865145102828963 562949953421312 1000000000193517 387034000000000000000 (Enclosure.clog_im_eq 9000 264678 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz481 (@HSub.hSub Real Real Real qz401 qz101 qz479) Bool.false 865145102828963 562949953421312 1000000000193517 387034000000000000000 (BSN.arctan_recip 264678 9000 rfl rfl) ep1225))))

noncomputable abbrev qz194 := (@ep1220 1 (BSN.w_sub_half_mk qz438 Bool.false 132339 1000 2 qz439 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7000 4000) qz477 Bool.false 7000 4000 0 1 Bool.false 264678 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 7000 4000) (Enclosure.Real.IsNear.const Bool.false 264678 4000)))

noncomputable def ep1230 := @ep1216 132339000025609846263 774068000000000000000000 ep1217 53115632678892647041 562949953421312000 134089000033737560263 774068000000000000000000 (@ep1218 66089379243974723 9007199254740992 875000004063857 387034000000000000000 (ep1219 qz194) ep1226 rfl) (@ep1227 114492437763282134457 1125899906842624000 132339000025609846263 774068000000000000000000 (ep1228 qz194) ep1229 rfl) rfl

noncomputable def ep1231 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz190 qz193) (@HMul.hMul Real Real Real qz0 qz192 qz191) 6056015719802741 2251799813685248 7000000001354619 1548136000000000000000 1249457479966910123871 4503599627370496000

noncomputable def ep1232 := nat_lit 2840801990736181192834191508014891008

noncomputable def ep1233 := @Enclosure.Real.IsNear.mulLit_ff qz190 qz193 7000 4000 0 1 865145102828963 562949953421312 1000000000193517 387034000000000000000

noncomputable def ep1234 := @Enclosure.Real.IsNear.mulLit_ff qz192 qz191 264678 4000 0 1 9441339891996389 2251799813685248 125000000580551 96758500000000000000

noncomputable def ep1235 := @ep1231 16542375076829538789 193517000000000000000000 ep1232 1261569511406515605871 4503599627370496000 4354343769249716541 48379250000000000000000 (@ep1233 6056015719802741 2251799813685248 7000000001354619 1548136000000000000000 (ep1219 qz194) ep1229 rfl) (@ep1234 1249457479966910123871 4503599627370496000 16542375076829538789 193517000000000000000000 (ep1228 qz194) ep1226 rfl) rfl

noncomputable def ep1236 := @Enclosure.Complex.IsNear.of_eq qz186 qz480 Bool.false 9000 4000 0 1 Bool.false 264678 4000 0 1 (BSN.w_shift_mk qz146 Bool.false 132339 1000 2 qz147 rfl)

noncomputable abbrev qz482 := (ep1236 (@Enclosure.Complex.IsNear.mk qz614 qz655 Bool.false 9000 4000 0 1 Bool.false 264678 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 9000 4000) (Enclosure.Real.IsNear.const Bool.false 264678 4000)))

noncomputable abbrev qz195 := qz482

noncomputable def ep1237 := ep1214 (@ep1215 48379250000000000000000 (ep1230 rfl) (ep1235 rfl)) qz195 rfl rfl rfl rfl rfl rfl

noncomputable def ep1238 := @ep1211 4354343769249716541 48379250000000000000000 (ep1237 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@Enclosure.Complex.IsNear.mul qz105 (↑qz2) Bool.false 120447 131072 1 524288 Bool.false 0 1 0 1 (@ep590 131072 1 524288 (ep592 rfl) (ep594 rfl) rfl rfl) (@ep595 1 0 1 (ep597 rfl) (ep599 rfl) rfl rfl))

noncomputable abbrev qz483 := (@HPow.hPow Complex Int Complex qz612 qz653 (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) (@OfNat.ofNat Int 1 (@instOfNat 1)) (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (@OfNat.ofNat Int 2 (@instOfNat 2)) (@Nat.cast Int instNatCastInt 1))))

noncomputable abbrev qz196 := qz483

noncomputable def ep1239 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz80 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz89 qz186 (@HSub.hSub Int Int Int qz408 qz91 (@HMul.hMul Int Int Int qz409 qz92 (@Nat.cast Int instNatCastInt k))))) (@HAdd.hAdd Complex Complex Complex qz4 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz80 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz89 qz186 (@HSub.hSub Int Int Int qz408 qz91 (@HMul.hMul Int Int Int qz409 qz92 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli qz107)) qz108) qz196)) Bool.false 2939433 68719476736 3 68719476736

noncomputable def ep1240 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz80 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz89 qz186 (@HSub.hSub Int Int Int qz408 qz91 (@HMul.hMul Int Int Int qz409 qz92 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli qz107)) qz108) qz196) Bool.false 0 1 0 1 Bool.false

noncomputable def ep1241 := @ep1240 0 1 0 1 Bool.false 2939433 68719476736 3 68719476736 Bool.true 43222402643 34359738368000 44113 34359738368000 Bool.false 2939433 2939433 68719476736 3 68719476736 Bool.true 43222402643 43222402643 34359738368000 44113

noncomputable def ep1242 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz80 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz89 qz186 (@HSub.hSub Int Int Int qz408 qz91 (@HMul.hMul Int Int Int qz409 qz92 (@Nat.cast Int instNatCastInt k))))) (Complex.mk qz10 qz10) Bool.false 0 1 0 1 Bool.false

noncomputable def ep1243 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli qz107)) qz108) qz196 Bool.false 2939433 68719476736 3 68719476736 Bool.true 43222402643 34359738368000 44113 34359738368000

noncomputable abbrev qz197 := (Complex.re qz483)

noncomputable abbrev qz198 := (Complex.im qz483)

noncomputable def ep1244 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli qz107)) qz108)) qz197) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli qz107)) qz108)) qz198) 2939433 68719476736 3 68719476736 0 1 0

noncomputable def ep1245 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli qz107)) qz108)) qz197 1 12 0 1 8818299 17179869184 9 17179869184 2939433

noncomputable def ep1246 := @Enclosure.Complex.IsNear.re_isNear qz196 Bool.false 8818299 17179869184 9 17179869184 Bool.true 129667207929 8589934592000 132339 8589934592000

noncomputable abbrev qz484 := (@HPow.hPow Complex Nat Complex qz617 qz653 1)

noncomputable abbrev qz199 := (@Inv.inv Complex Complex.instInv qz484)

noncomputable def ep1247 := @Enclosure.Complex.IsNear.of_eq qz196 qz199 Bool.false 8818299 17179869184 9 17179869184 Bool.true 129667207929 8589934592000 132339

noncomputable def ep1248 := @Enclosure.Complex.IsNear.of_parts qz199 Bool.false 8818299 17179869184 9 17179869184 Bool.true 129667207929 8589934592000 132339

noncomputable abbrev qz200 := (Complex.re qz484)

noncomputable abbrev qz201 := qz484

noncomputable def ep1249 := @Enclosure.Real.IsNear.mulLit_ff qz200 (@Inv.inv Real Real.instInv (@DFunLike.coe qz114 Complex (fun (x : Complex) => Real) qz115 Complex.normSq qz201)) 9000 4000 0 1 979811 4294967296 1 4294967296

noncomputable def ep1250 := @Enclosure.Complex.IsNear.re_isNear qz201 Bool.false 9000 4000 0 1 Bool.false 264678 4000 0 1

noncomputable def ep1251 := @Enclosure.Complex.IsNear.of_eq qz201 qz186 Bool.false 9000 4000 0 1 Bool.false 264678 4000 0

noncomputable def ep1252 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (@DFunLike.coe qz114 Complex (fun (x : Complex) => Real) qz115 Complex.normSq qz201)) Bool.false 979811 4294967296 1 4294967296 979811 4294967296 1

noncomputable abbrev qz202 := (Complex.im qz484)

noncomputable def ep1253 := @Enclosure.Real.IsNear.of_eq (@DFunLike.coe qz114 Complex (fun (x : Complex) => Real) qz115 Complex.normSq qz201) (@HAdd.hAdd Real Real Real qz421 (@HMul.hMul Real Real Real qz0 qz200 qz200) (@HMul.hMul Real Real Real qz0 qz202 qz202)) Bool.false 17533860921 4000000 0 1

noncomputable def ep1254 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz200 qz200) (@HMul.hMul Real Real Real qz0 qz202 qz202) 81 16 0 1 17513610921 4000000

noncomputable def ep1255 := @Enclosure.Real.IsNear.mulLit_ff qz200 qz200 9000 4000 0 1 9000 4000 0 1

noncomputable def ep1256 := @Enclosure.Real.IsNear.mulLit_ff qz202 qz202 264678 4000 0 1 264678 4000 0 1

noncomputable def ep1257 := @Enclosure.Complex.IsNear.im_isNear qz201 Bool.false 9000 4000 0 1 Bool.false 264678 4000 0 1

noncomputable abbrev qz203 := (ep1250 (@ep1251 1 (BSN.pow_one_c qz472) qz482))

noncomputable abbrev qz204 := (ep1257 (@ep1251 1 (BSN.pow_one_c qz472) qz482))

noncomputable def ep1258 := @ep1254 0 1 280541774736 17533860921 4000000 0 1 (@ep1255 81 16 0 1 qz203 qz203 rfl) (@ep1256 17513610921 4000000 0 1 qz204 qz204 rfl)

noncomputable def ep1259 := @Enclosure.Real.IsNear.inv_image (@DFunLike.coe qz114 Complex (fun (x : Complex) => Real) qz115 Complex.normSq qz201) 17533860921 4000000 0 1 489905 489906 2147483648 (ep1253 (Enclosure.Complex.normSq_eq_mul_add_mul qz201) (ep1258 rfl rfl)) rfl

noncomputable def ep1260 := @Enclosure.Real.IsNear.of_eq (Complex.re qz199) (@HMul.hMul Real Real Real qz0 qz200 (@Inv.inv Real Real.instInv (@DFunLike.coe qz114 Complex (fun (x : Complex) => Real) qz115 Complex.normSq qz201))) Bool.false 8818299 17179869184 9 17179869184 (Enclosure.Complex.inv_re_eq_mul qz201) (@ep1249 8818299 17179869184 9 17179869184 qz203 (@ep1252 4294967296 (ep1259 rfl rfl rfl rfl rfl) rfl) rfl)

noncomputable def ep1261 := @Enclosure.Real.IsNear.of_eq (Complex.im qz199) (@HMul.hMul Real Real Real qz0 (@Neg.neg Real Real.instNeg qz202) (@Inv.inv Real Real.instInv (@DFunLike.coe qz114 Complex (fun (x : Complex) => Real) qz115 Complex.normSq qz201))) Bool.true 129667207929 8589934592000 132339 8589934592000 (Enclosure.Complex.inv_im_eq_mul qz201)

noncomputable def ep1262 := @Enclosure.Real.IsNear.mulLit_tf (@Neg.neg Real Real.instNeg qz202) (@Inv.inv Real Real.instInv (@DFunLike.coe qz114 Complex (fun (x : Complex) => Real) qz115 Complex.normSq qz201)) 264678 4000 0 1 979811 4294967296 1

noncomputable def ep1263 := @ep1262 4294967296 129667207929 8589934592000 132339 8589934592000 (@Enclosure.Real.IsNear.neg qz202 Bool.false 264678 4000 0 1 qz204) (@ep1252 4294967296 (ep1259 rfl rfl rfl rfl rfl) rfl) rfl

noncomputable def ep1264 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli qz107)) qz108)) qz198 0 1 0 1 129667207929 8589934592000 132339 8589934592000 0

noncomputable def ep1265 := @Enclosure.Complex.IsNear.im_isNear qz196 Bool.false 8818299 17179869184 9 17179869184 Bool.true 129667207929 8589934592000 132339 8589934592000

noncomputable abbrev qz205 := (@ep1247 8589934592000 (BSN.zpow_one_sub_two_mul qz472 1 1 rfl rfl) (@ep1248 8589934592000 ep1260 (ep1261 ep1263)))

noncomputable def ep1266 := @ep1244 1 2939433 2939433 68719476736 3 68719476736 (@ep1245 68719476736 3 68719476736 ep609 (ep1246 qz205) rfl) (@ep1264 1 0 1 ep629 (ep1265 qz205) rfl) rfl

noncomputable def ep1267 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli qz107)) qz108)) qz198) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli qz107)) qz108)) qz197) 43222402643 34359738368000 44113 34359738368000 0 1 0

noncomputable def ep1268 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli qz107)) qz108)) qz198 1 12 0 1 129667207929 8589934592000 132339 8589934592000 43222402643

noncomputable def ep1269 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli qz107)) qz108)) qz197 0 1 0 1 8818299 17179869184 9 17179869184 0

noncomputable def ep1270 := @ep1267 1 43222402643 43222402643 34359738368000 44113 34359738368000 (@ep1268 34359738368000 44113 34359738368000 ep609 (ep1265 qz205) rfl) (@ep1269 1 0 1 ep629 (ep1246 qz205) rfl) rfl

noncomputable def ep1271 := @ep1241 34359738368000 (@ep1242 0 1 0 1 (BSN.stirling_sum_base qz186) qz121) (ep1243 (ep1266 rfl) (ep1270 rfl)) rfl rfl rfl rfl rfl

noncomputable def ep1272 := @ep1208 963562910616464347503 4503599627370496000 ep1200 ep1192 (ep1238 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep1239 Bool.true 43222402643 34359738368000 44113 34359738368000 (BSN.stirling_sum_succ qz186 0 1 rfl) (ep1271 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl

noncomputable def ep1273 := @Enclosure.Complex.IsNear.of_eq (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz183 (@Nat.cast Complex Complex.instNatCast j))) (BSN.logSumC qz146 2) Bool.false 9440247359690469 1125899906842624 125000000580551 48379250000000000000 Bool.false 877899813520803 281474976710656

noncomputable abbrev qz206 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz273 qz473 qz417))

noncomputable def ep1274 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz146 2) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.logSumC qz146 1) qz206) Bool.false 9440247359690469 1125899906842624 125000000580551 48379250000000000000 Bool.false 877899813520803 281474976710656 1000000000193517 193517000000000000000

noncomputable def ep1275 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz146 1) qz206 Bool.false 9440054623033061 2251799813685248 125000000580551 96758500000000000000 Bool.false 882153173321123 562949953421312 1000000000193517 387034000000000000000 Bool.false

noncomputable def ep1276 := nat_lit 42515094491387304909630943002624

noncomputable def ep1277 := nat_lit 988427318260229079212671107072

noncomputable abbrev qz207 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz273 qz473 (@Nat.cast Complex Complex.instNatCast 0)))

noncomputable def ep1278 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz146 1) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.logSumC qz146 0) qz207) Bool.false 9440054623033061 2251799813685248 125000000580551 96758500000000000000 Bool.false 882153173321123 562949953421312 1000000000193517 387034000000000000000

noncomputable def ep1279 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz146 0) qz207 Bool.false 0 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable abbrev qz485 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz655))

noncomputable def ep1280 := @Enclosure.Complex.IsNear.of_eq qz207 qz485 Bool.false 9440054623033061 2251799813685248 125000000580551 96758500000000000000 Bool.false 882153173321123 562949953421312 1000000000193517 387034000000000000000

noncomputable def ep1281 := BSN.log_dyadic_bound 4519443684 135591443684 2 1 55155118800934030475568 1048576 387034 20425371212847491856 20425371212847491856 69926 140110887368 131072000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 4519443684) (BSN.artanhQ 135591443684) 0 1 20425371212847491856 55155118800934030475568 20425371212847491856 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep1282 := @Enclosure.Real.IsNear.mulLit_ff qz100 (Real.log (Enclosure.sfrac Bool.false 70055443684 16000000)) 1 2 0 1 9440054623033061 1125899906842624 125000000580551 48379250000000000000 9440054623033061 2251799813685248 125000000580551 96758500000000000000 qz412 (BSN.isNear_log_sfrac 70055443684 16000000 9440054623033061 1125899906842624 125000000580551 48379250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 70055443684) qz616)) Bool.false 316755670924848479076352 37778931862957161709568 1000000004644408 387034000000000000000 9440054623033061 1125899906842624 125000000580551 48379250000000000000 (BSN.log_rat_reduce_isNear 70055443684 16000000 12 140110887368 131072000000 69926 1048576 24973259072661432 36028797018963968 387034 1000000000000000 rfl rfl rfl rfl (ep1281 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1283 := BSN.arctan_dyadic_bound_f 1000 264678 1 0 1048576 387034 0 1 1 0 1 1 3961 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 264678) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 264678) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz486 := (@Nat.cast Real Real.instNatCast 264678)

noncomputable def ep1284 := @Enclosure.Real.IsNear.subLit_ff_p qz101 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz423 qz486)) 884279719003555 562949953421312 1 2000000000000000 3961 1048576 1 387034 925004645868369870848 882153173321123 562949953421312 1000000000193517 387034000000000000000 qz102 (ep1283 rfl) rfl rfl

noncomputable abbrev qz208 := (@HAdd.hAdd Complex Complex Complex qz273 qz473 (@Nat.cast Complex Complex.instNatCast 0))

noncomputable abbrev qz487 := (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz655)

noncomputable def ep1285 := @ep1279 9440054623033061 2251799813685248 125000000580551 96758500000000000000 Bool.false 882153173321123 562949953421312 1000000000193517 387034000000000000000 Bool.false 9440054623033061 9440054623033061 2251799813685248 125000000580551 96758500000000000000 Bool.false 882153173321123 882153173321123 562949953421312 1000000000193517 387034000000000000000 (@Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz146 0) (Complex.mk qz10 qz10) Bool.false 0 1 0 1 Bool.false 0 1 0 1 (BSN.log_sum_c_base qz146) qz121) (ep1280 (@congrArg Complex Complex qz208 qz487 Complex.log (BSN.w_shift_mk qz146 Bool.false 132339 1000 0 qz147 rfl)) (@Enclosure.Complex.IsNear.of_parts qz485 Bool.false 9440054623033061 2251799813685248 125000000580551 96758500000000000000 Bool.false 882153173321123 562949953421312 1000000000193517 387034000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz485) (@HMul.hMul Real Real Real qz0 qz100 (Real.log (Enclosure.sfrac Bool.false 70055443684 16000000))) Bool.false 9440054623033061 2251799813685248 125000000580551 96758500000000000000 (Enclosure.clog_re_eq 1000 264678 4000 70055443684 16000000 rfl rfl rfl) (ep1282 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz485) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz486 qz423)) Bool.false 882153173321123 562949953421312 1000000000193517 387034000000000000000 (Enclosure.clog_im_eq 1000 264678 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz486 qz423)) (@HSub.hSub Real Real Real qz401 qz101 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz423 qz486))) Bool.false 882153173321123 562949953421312 1000000000193517 387034000000000000000 (BSN.arctan_recip 264678 1000 rfl rfl) ep1284)))) rfl rfl

noncomputable abbrev qz488 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz655))

noncomputable def ep1286 := @Enclosure.Complex.IsNear.of_eq qz206 qz488 Bool.false 9440440096347877 2251799813685248 125000000580551 96758500000000000000 Bool.false 873646453720483 562949953421312 1000000000193517 387034000000000000000

noncomputable def ep1287 := BSN.log_dyadic_bound 4543443684 135615443684 2 1 55174645696824526475568 1048576 387034 20642880509679491856 20642880509679491856 70285 140158887368 131072000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 4543443684) (BSN.artanhQ 135615443684) 0 1 20642880509679491856 55174645696824526475568 20642880509679491856 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep1288 := @Enclosure.Real.IsNear.mulLit_ff qz100 (Real.log (Enclosure.sfrac Bool.false 70079443684 16000000)) 1 2 0 1 9440440096347877 1125899906842624 125000000580551 48379250000000000000 9440440096347877 2251799813685248 125000000580551 96758500000000000000 qz412 (BSN.isNear_log_sfrac 70079443684 16000000 9440440096347877 1125899906842624 125000000580551 48379250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 70079443684) qz616)) Bool.false 316768605262978287140864 37778931862957161709568 1000000004644408 387034000000000000000 9440440096347877 1125899906842624 125000000580551 48379250000000000000 (BSN.log_rat_reduce_isNear 70079443684 16000000 12 140158887368 131072000000 70285 1048576 24973259072661432 36028797018963968 387034 1000000000000000 rfl rfl rfl rfl (ep1287 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1289 := BSN.arctan_dyadic_bound_f 5000 264678 1 0 1048576 387034 0 1 1 0 1 1 19806 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 5000) (BSN.arctanEvenQ 264678) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 5000) (BSN.arctanOddQ 264678) 0 0 rfl) rfl rfl rfl

noncomputable def ep1290 := @Enclosure.Real.IsNear.subLit_ff_p qz101 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz427 qz486)) 884279719003555 562949953421312 1 2000000000000000 19806 1048576 1 387034 916084703856409182208 873646453720483 562949953421312 1000000000193517 387034000000000000000 qz102 (ep1289 rfl) rfl rfl

noncomputable abbrev qz209 := (@HAdd.hAdd Complex Complex Complex qz273 qz473 qz417)

noncomputable abbrev qz489 := (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz655)

noncomputable def ep1291 := @ep1275 9440440096347877 2251799813685248 125000000580551 96758500000000000000 Bool.false 873646453720483 562949953421312 1000000000193517 387034000000000000000 Bool.false ep1276 9440247359690469 1125899906842624 125000000580551 48379250000000000000 Bool.false ep1277 877899813520803 281474976710656 1000000000193517 193517000000000000000 (ep1278 (BSN.log_sum_c_succ qz146 0 1 rfl) (ep1285 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1286 (@congrArg Complex Complex qz209 qz489 Complex.log (BSN.w_shift_mk qz146 Bool.false 132339 1000 1 qz147 rfl)) (@Enclosure.Complex.IsNear.of_parts qz488 Bool.false 9440440096347877 2251799813685248 125000000580551 96758500000000000000 Bool.false 873646453720483 562949953421312 1000000000193517 387034000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz488) (@HMul.hMul Real Real Real qz0 qz100 (Real.log (Enclosure.sfrac Bool.false 70079443684 16000000))) Bool.false 9440440096347877 2251799813685248 125000000580551 96758500000000000000 (Enclosure.clog_re_eq 5000 264678 4000 70079443684 16000000 rfl rfl rfl) (ep1288 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz488) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz486 qz427)) Bool.false 873646453720483 562949953421312 1000000000193517 387034000000000000000 (Enclosure.clog_im_eq 5000 264678 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz486 qz427)) (@HSub.hSub Real Real Real qz401 qz101 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz427 qz486))) Bool.false 873646453720483 562949953421312 1000000000193517 387034000000000000000 (BSN.arctan_recip 264678 5000 rfl rfl) ep1290)))) rfl rfl

noncomputable def ep1292 := @ep1201 ep1192 Bool.false 9440247359690469 1125899906842624 125000000580551 48379250000000000000 Bool.false 877899813520803 281474976710656 1000000000193517 193517000000000000000 Bool.true ep1202 58585053748199385541 562949953421312000 ep1197 ep551 Bool.false ep1203 949516513600131499503 4503599627370496000 ep1194 ep1192 (@ep1204 562949953421312000 ep1199 ep551 Bool.false 963562910616464347503 4503599627370496000 ep1200 ep1192 (BSN.logGammaStirling_unfold 1 qz186) (ep1272 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (@ep1273 1000000000193517 193517000000000000000 (BSN.log_sum_c_eq qz146 2) (ep1274 (BSN.log_sum_c_succ qz146 1 2 rfl) (ep1291 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)))

noncomputable abbrev qz210 := (@HDiv.hDiv Real Real Real qz271 qz438 (2 : Real))

noncomputable def ep1293 := @Enclosure.Real.IsNear.mulLit_ff qz210 (Real.log Real.pi) 132339 2000 0 1 75021 65536 1 262144 9928204119 131072000 132339 524288000 (@Enclosure.Real.IsNear.of_eq qz210 (Enclosure.sfrac Bool.false 132339 2000) Bool.false 132339 2000 0 1 (BSN.t_half_eq qz146 Bool.false 132339 1000 qz147) (Enclosure.Real.IsNear.const Bool.false 132339 2000)) EMRow44.d5 rfl

noncomputable def ep1294 := @ep1195 132339 524288000 ep1196 608386017607191561711 4503599627370496000 ep1191 ep1192 (@ep1198 ep1194 ep1192 (ep1292 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) ep1293 rfl rfl

noncomputable def ep1295 := BSN.cos_dyadic_bound_f 748936 2147483648 1 0 1048576 387412 0 1 1 0 1 1 1048575 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 748936) qz20 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 748936) qz21 0 0 rfl) rfl rfl

noncomputable def ep1296 := @ep1190 1048576 Bool.true 1048575 1048576 1 193517 (@ep1193 35412727 262144 365 1048576 ep1294 rfl) (Enclosure.sfrac_false_div 35412727 262144) (BSN.cos_reduce2 qz474 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 13175435109517492224) qz325) 226375608064910080 72057594037927936 Bool.false 1048575 1048576 21 1000000000000000 387034 193517 (BSN.sin_reduce_arg_pos_rat_q2 35412727 262144 226375608064910080 72057594037927936 21 13175435109517492224 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1048575 1048576 13175435109517492224 37778931862957161709568 748936 2147483648 387412 387034 (ep1295 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1297 := nat_lit 154053549839129476333568000

noncomputable def ep1298 := nat_lit 570254897503759909907211960503

noncomputable def ep1299 := nat_lit 89435942412656456614929235968000

noncomputable abbrev qz490 := (@HPow.hPow Complex Complex Complex qz536 (@Nat.cast Complex Complex.instNatCast 34) qz622)

noncomputable abbrev qz211 := qz490

noncomputable abbrev qz491 := (@Nat.cast Complex Complex.instNatCast 34)

noncomputable abbrev qz212 := (@HAdd.hAdd Complex Complex Complex qz273 (@HDiv.hDiv Complex Complex Complex qz406 qz491 (@HSub.hSub Complex Complex Complex qz398 qz436 (1 : Complex))) qz405)

noncomputable abbrev qz213 := qz491

noncomputable def ep1300 := @Enclosure.Complex.IsNear.of_eq (zetaApproximant qz143 1 34) (@HAdd.hAdd Complex Complex Complex qz4 (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 34, @HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast n) qz144) (@HMul.hMul Complex Complex Complex qz80 qz211 (@HAdd.hAdd Complex Complex Complex qz4 qz212 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz213 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1))))))) Bool.false ep1185 ep1186 ep1187

noncomputable def ep1301 := @Enclosure.Complex.IsNear.addLitP (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 34, @HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast n) qz144) (@HMul.hMul Complex Complex Complex qz80 qz211 (@HAdd.hAdd Complex Complex Complex qz4 qz212 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz213 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))))) Bool.false 2279644796735 1099511627776 1343098740380077 212774191672328192

noncomputable def ep1302 := nat_lit 3009687491362823293720343749

noncomputable def ep1303 := nat_lit 13334903189715605012465457

noncomputable def ep1304 := nat_lit 6050429632814123410569936503

noncomputable def ep1305 := nat_lit 175488826648605077412722835193705005056

noncomputable def ep1306 := nat_lit 757126423271476887222022797281722368

noncomputable def ep1307 := @ep1301 Bool.false 100088622117 1099511627776 1342280814074231 212774191672328192 Bool.true 95369619938243067889719 ep1186 ep1302 ep1188 Bool.true ep1303 ep1297 ep1304 ep1299 Bool.false ep1305 ep1185 ep1186 ep1187 ep1188 Bool.false ep1306 688602470537695705590543 ep1297

noncomputable def ep1308 := @Enclosure.Complex.IsNear.of_eq (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 34, @HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast n) qz144) (BSN.headSumC qz143 34) Bool.false 2279644796735 1099511627776 1343098740380077 212774191672328192 Bool.false 100088622117 1099511627776 1342280814074231

noncomputable def ep1309 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz143 34) (@HAdd.hAdd Complex Complex Complex qz4 qz173 (@HPow.hPow Complex Complex Complex qz6 qz131 qz144)) Bool.false 2279644796735 1099511627776 1343098740380077 212774191672328192 Bool.false 100088622117 1099511627776 1342280814074231 212774191672328192

noncomputable def ep1310 := @Enclosure.Complex.IsNear.addLitP qz173 (@HPow.hPow Complex Complex Complex qz6 qz131 qz144) Bool.false 2397094195321 1099511627776 1317420598410975 212774191672328192 Bool.true 51038480035 1099511627776 1316566967831595 212774191672328192 Bool.true

noncomputable def ep1311 := nat_lit 1253247980604594250055680

noncomputable abbrev qz214 := (@HMul.hMul Real Real Real qz268 qz438 qz618)

noncomputable def ep1312 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz131 qz144) (Complex.mk (@HMul.hMul Real Real Real qz0 qz134 (Real.cos qz214)) (@HMul.hMul Real Real Real qz0 qz134 (@Neg.neg Real Real.instNeg (Real.sin qz214)))) Bool.true 58724699293 549755813888 12839070984551 106387095836164096 Bool.false 18890887769 137438953472 6428461560659 53193547918082048 (BSN.cpow_neg_s_mk qz146 132339 1000 33 qz147 rfl)

noncomputable def ep1313 := @Enclosure.Real.IsNear.mulLit_ff qz146 qz137 132339 1000 0 1 15746868335186131 4503599627370496 200000000193517 38703400000000000000 2083924808610197390409 4503599627370496000 26467800025609846263 38703400000000000000000 qz148 (BSN.isNear_log_sfrac 33 1 15746868335186131 4503599627370496 200000000193517 38703400000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz433) Bool.false 66047152845744529997824 18889465931478580854784 1000000000967585 193517000000000000000 15746868335186131 4503599627370496 200000000193517 38703400000000000000 (BSN.log_rat_reduce_isNear 33 1 5 66 64 16133 524288 24973259072661432 36028797018963968 193517 1000000000000000 rfl rfl rfl rfl (ep685 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1314 := nat_lit 521625531135130991840856984620086017054893576310744614034612971290383142164001

noncomputable def ep1315 := nat_lit 212963659600557676179189883025746746628306392822579171963413112083311564321

noncomputable def ep1316 := nat_lit 1564450666086191860170212574094206557671424116146588683759912087646982803363361

noncomputable def ep1317 := BSN.cos_dyadic_bound_f 1954511309 2147483648 3 2 1048576 387412 ep1314 ep62 ep1315 ep1316 ep65 ep1315 643442 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1954511309) qz20 0 2 ep1314 ep62 ep1315 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1954511309) qz21 0 2 ep1316 ep65 ep1315 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz492 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 242600777) qz24)

noncomputable def ep1318 := @Enclosure.Real.IsNear.cos_image qz214 qz492 Bool.false 242600777 524288 359 524288 Bool.true 643442 1048576 1 193517 (@Enclosure.Real.IsNear.recentre' qz214 Bool.false 2083924808610197390409 4503599627370496000 26467800025609846263 38703400000000000000000 242600777 524288 359 524288 (ep1313 rfl) rfl) (Enclosure.sfrac_false_div 242600777 524288) (BSN.cos_reduce2 qz492 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 68768253169910136438784) qz25) 226375608064910080 72057594037927936 Bool.false 643442 1048576 73 1000000000000000 387034 193517 (BSN.sin_reduce_arg_pos_rat_q2 242600777 524288 226375608064910080 72057594037927936 73 68768253169910136438784 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 643442 1048576 68768253169910136438784 75557863725914323419136 1954511309 2147483648 387412 387034 (ep1317 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1319 := nat_lit 938755585115555339172599220409734233301505792245082241924732617833023006643745

noncomputable def ep1320 := nat_lit 2458300781758529747309660222214881306771307436005883600667311330238353941534241

noncomputable def ep1321 := BSN.sin_dyadic_bound_f 1954511309 2147483648 3 2 1048576 387412 ep1319 ep94 ep1315 ep1320 ep96 ep1315 827944 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1954511309) qz15 0 2 ep1319 ep94 ep1315 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1954511309) qz16 0 2 ep1320 ep96 ep1315 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1322 := @Enclosure.Real.IsNear.sin_image qz214 qz492 Bool.false 242600777 524288 359 524288 Bool.true 827944 1048576 1 193517 (@Enclosure.Real.IsNear.recentre' qz214 Bool.false 2083924808610197390409 4503599627370496000 26467800025609846263 38703400000000000000000 242600777 524288 359 524288 (ep1313 rfl) rfl) (Enclosure.sfrac_false_div 242600777 524288) (BSN.sin_reduce2 qz492 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 68768253169910136438784) qz25) 226375608064910080 72057594037927936 Bool.false 827944 1048576 73 1000000000000000 387034 193517 (BSN.sin_reduce_arg_pos_rat_q2 242600777 524288 226375608064910080 72057594037927936 73 68768253169910136438784 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 827944 1048576 68768253169910136438784 75557863725914323419136 1954511309 2147483648 387412 387034 (ep1321 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1323 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz134 (Real.cos qz214)) (@HMul.hMul Real Real Real qz0 qz134 (@Neg.neg Real Real.instNeg (Real.sin qz214))) Bool.true 58724699293 549755813888 12839070984551 106387095836164096 Bool.false 18890887769 137438953472 6428461560659 53193547918082048 (@Enclosure.Real.IsNear.mulLit_ft qz134 (Real.cos qz214) 182533 1048576 1 1048576 321721 524288 69996891 101458640896 58724699293 549755813888 12839070984551 106387095836164096 qz435 (@Enclosure.Real.IsNear.recentre' (Real.cos qz214) Bool.true 643442 1048576 69996891 101458640896 321721 524288 69996891 101458640896 (ep1318 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz134 (@Neg.neg Real Real.instNeg (Real.sin qz214)) 182533 1048576 1 1048576 103493 131072 69996891 101458640896 18890887769 137438953472 6428461560659 53193547918082048 qz435 (@Enclosure.Real.IsNear.neg (Real.sin qz214) Bool.true 103493 131072 69996891 101458640896 (@Enclosure.Real.IsNear.recentre' (Real.sin qz214) Bool.true 827944 1048576 69996891 101458640896 103493 131072 69996891 101458640896 (ep1322 rfl rfl) rfl)) rfl)

noncomputable def ep1324 := @ep1310 58724699293 549755813888 12839070984551 106387095836164096 Bool.false 18890887769 137438953472 6428461560659 53193547918082048 Bool.false ep1311 2279644796735 1099511627776 1343098740380077 212774191672328192 Bool.false 13756075478214953140224 100088622117 1099511627776 1342280814074231 212774191672328192 EMRow44.d16 (ep1312 ep1323) rfl rfl

noncomputable def ep1325 := @Enclosure.Complex.IsNear.mul qz211 (@HAdd.hAdd Complex Complex Complex qz4 qz212 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz213 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1))))) Bool.true 95369619938243067889719 ep1186 ep1302 ep1188 Bool.true

noncomputable def ep1326 := nat_lit 10599913205196125333870893

noncomputable abbrev qz215 := (Complex.re qz490)

noncomputable abbrev qz216 := (Complex.im qz490)

noncomputable def ep1327 := @Enclosure.Real.IsNear.subLit_tt_n (@HMul.hMul Real Real Real qz0 qz215 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz212 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz213 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz216 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz212 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz213 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1))))))) 3906286557738113415867 308107099678258952667136 ep1326

noncomputable def ep1328 := nat_lit 178871884825312913229858471936

noncomputable def ep1329 := nat_lit 119903063354597320084206833

noncomputable def ep1330 := nat_lit 14905990402109409435821539328000

noncomputable def ep1331 := nat_lit 29384056996589929339936927730446387854163574784

noncomputable def ep1332 := @Enclosure.Real.IsNear.mulLit_tf qz215 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz212 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz213 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))))) 27865762353 1099511627776 25205068630829 212774191672328192 420546889217

noncomputable abbrev qz657 := (Real.log (Enclosure.sfrac Bool.false 34 1))

noncomputable abbrev qz217 := (@HMul.hMul Real Real Real qz268 qz438 qz657)

noncomputable abbrev qz218 := (Real.sin (@HMul.hMul Real Real Real qz268 qz438 qz657))

noncomputable abbrev qz493 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 34)))

noncomputable abbrev qz658 := (@Neg.neg Real Real.instNeg qz218)

noncomputable def ep1333 := @Enclosure.Complex.IsNear.of_eq qz211 (Complex.mk (@HMul.hMul Real Real Real qz0 qz493 (Real.cos qz217)) (@HMul.hMul Real Real Real qz0 qz493 qz658)) Bool.true 27865762353 1099511627776 25205068630829 212774191672328192 Bool.true 93246911199 549755813888 12687885472057 106387095836164096 (BSN.cpow_neg_s_mk qz146 132339 1000 34 qz147 rfl)

noncomputable abbrev qz494 := (Real.sqrt (@Nat.cast Real Real.instNatCast 34))

noncomputable abbrev qz495 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 34) qz14)

noncomputable def ep1334 := @Enclosure.Real.IsNear.inv_image qz494 6114197 1048576 1 1048576 89914 89915 524288 (@Enclosure.Real.IsNear.of_eq qz494 (Real.sqrt qz495) Bool.false 6114197 1048576 1 1048576 (BSN.sqrt_natCast_div_one 34) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz495) Bool.false 6114197 1048576 1 1048576 6114197 1048576 1 1048576 (BSN.sqrt_enclosure 34 1 3057098 3057099 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep1335 := BSN.log_dyadic_bound 2 66 2 1 13068 524288 193517 4 4 31784 68 64 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 2) (BSN.artanhQ 66) 0 1 4 13068 4 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep1336 := @Enclosure.Real.IsNear.mulLit_ff qz146 qz657 132339 1000 0 1 15881309401485523 4503599627370496 200000000193517 38703400000000000000 2101716604883192628297 4503599627370496000 26467800025609846263 38703400000000000000000 qz148 (BSN.isNear_log_sfrac 34 1 15881309401485523 4503599627370496 200000000193517 38703400000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz495) Bool.false 66611039547888335060992 18889465931478580854784 1000000000967585 193517000000000000000 15881309401485523 4503599627370496 200000000193517 38703400000000000000 (BSN.log_rat_reduce_isNear 34 1 5 68 64 31784 524288 24973259072661432 36028797018963968 193517 1000000000000000 rfl rfl rfl rfl (ep1335 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1337 := BSN.sin_dyadic_bound_f 318521831 2147483648 1 0 1048576 387412 0 1 1 0 1 1 154957 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 318521831) qz15 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 318521831) qz16 0 0 rfl) rfl rfl

noncomputable abbrev qz496 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 489344029) qz17)

noncomputable def ep1338 := @Enclosure.Real.IsNear.cos_image qz217 qz496 Bool.false 489344029 1048576 359 524288 Bool.true 154957 1048576 1 193517 (@Enclosure.Real.IsNear.recentre' qz217 Bool.false 2101716604883192628297 4503599627370496000 26467800025609846263 38703400000000000000000 489344029 1048576 359 524288 (ep1336 rfl) rfl) (Enclosure.sfrac_false_div 489344029 1048576) (BSN.cos_reduce1 qz496 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 22413981257537870102528) qz19) 226375608064910080 72057594037927936 Bool.false 154957 1048576 74 1000000000000000 387034 193517 (BSN.sin_reduce_arg_pos_rat_q1 489344029 1048576 226375608064910080 72057594037927936 74 22413981257537870102528 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 154957 1048576 22413981257537870102528 151115727451828646838272 318521831 2147483648 387412 387034 (ep1337 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1339 := nat_lit 10293351757413407376815738534538721

noncomputable def ep1340 := BSN.cos_dyadic_bound_f 318521831 2147483648 2 1 1048576 387412 ep1339 ep76 ep1339 ep1339 ep77 ep1339 1037062 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 318521831) qz20 0 1 ep1339 ep76 ep1339 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 318521831) qz21 0 1 ep1339 ep77 ep1339 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1341 := @Enclosure.Real.IsNear.sin_image qz217 qz496 Bool.false 489344029 1048576 359 524288 Bool.false 1037062 1048576 1 193517 (@Enclosure.Real.IsNear.recentre' qz217 Bool.false 2101716604883192628297 4503599627370496000 26467800025609846263 38703400000000000000000 489344029 1048576 359 524288 (ep1336 rfl) rfl) (Enclosure.sfrac_false_div 489344029 1048576) (BSN.sin_reduce1 qz496 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 22413981257537870102528) qz19) 226375608064910080 72057594037927936 Bool.false 1037062 1048576 74 1000000000000000 387034 193517 (BSN.sin_reduce_arg_pos_rat_q1 489344029 1048576 226375608064910080 72057594037927936 74 22413981257537870102528 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1037062 1048576 22413981257537870102528 151115727451828646838272 318521831 2147483648 387412 387034 (ep1340 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1342 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz493 (Real.cos qz217)) (@HMul.hMul Real Real Real qz0 qz493 qz658) Bool.true 27865762353 1099511627776 25205068630829 212774191672328192 Bool.true 93246911199 549755813888 12687885472057 106387095836164096 (@Enclosure.Real.IsNear.mulLit_ft qz493 (Real.cos qz217) 179829 1048576 1 1048576 154957 1048576 69996891 101458640896 27865762353 1099511627776 25205068630829 212774191672328192 (@Enclosure.Real.IsNear.recentre' qz493 Bool.false 179829 1048576 1 1048576 179829 1048576 1 1048576 (ep1334 rfl rfl) rfl) (@Enclosure.Real.IsNear.recentre' (Real.cos qz217) Bool.true 154957 1048576 69996891 101458640896 154957 1048576 69996891 101458640896 (ep1338 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz493 qz658 179829 1048576 1 1048576 518531 524288 69996891 101458640896 93246911199 549755813888 12687885472057 106387095836164096 (@Enclosure.Real.IsNear.recentre' qz493 Bool.false 179829 1048576 1 1048576 179829 1048576 1 1048576 (ep1334 rfl rfl) rfl) (@Enclosure.Real.IsNear.neg qz218 Bool.false 518531 524288 69996891 101458640896 (@Enclosure.Real.IsNear.recentre' qz218 Bool.false 1037062 1048576 69996891 101458640896 518531 524288 69996891 101458640896 (ep1341 rfl rfl) rfl)) rfl)

noncomputable def ep1343 := @ep1332 840665324208 0 1 3906286557738113415867 308107099678258952667136 ep1326 ep1328 (@Enclosure.Complex.IsNear.re_isNear qz211 Bool.true 27865762353 1099511627776 25205068630829 212774191672328192 Bool.true 93246911199 549755813888 12687885472057 106387095836164096 (ep1333 ep1342))

noncomputable def ep1344 := @Enclosure.Complex.IsNear.re_isNear (@HAdd.hAdd Complex Complex Complex qz4 qz212 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz213 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1))))) Bool.false 420546889217 840665324208 0 1 Bool.false

noncomputable def ep1345 := @Enclosure.Complex.IsNear.addLitP qz212 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz213 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) Bool.false 1028227113 2060454226 0 1 Bool.true 264678000

noncomputable def ep1346 := @ep1345 1030227113 0 1 Bool.false 1 816 0 1 Bool.false 44113 136000 0 1 Bool.false 841093778434 420546889217 840665324208 0 1 Bool.false 9450200635769 9450200635769 140110887368000 0 1

noncomputable abbrev qz219 := (@HDiv.hDiv Complex Complex Complex qz406 qz491 (@HSub.hSub Complex Complex Complex qz398 qz436 (1 : Complex)))

noncomputable def ep1347 := @Enclosure.Complex.IsNear.addLitP qz219 qz105 Bool.true 68000000 70055443684 0 1 Bool.true 17998104000 70055443684 0 1

noncomputable def ep1348 := @Enclosure.Complex.IsNear.of_eq qz219 (Complex.mk (Enclosure.sfrac Bool.true 68000000 70055443684) (Enclosure.sfrac Bool.true 17998104000 70055443684)) Bool.true 68000000 70055443684 0 1 Bool.true 17998104000 70055443684 0 1

noncomputable def ep1349 := @ep1347 Bool.false 1 2 0 1 Bool.false 0 1 0 1 Bool.false 69919443684 1028227113 2060454226 0 1 Bool.true 17998104000 264678000 1030227113 0 1 (ep1348 (BSN.N_div_s_sub_one_mk qz146 132339 1000 34 qz147 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 68000000 70055443684) (Enclosure.sfrac Bool.true 17998104000 70055443684) Bool.true 68000000 70055443684 0 1 Bool.true 17998104000 70055443684 0 1 (Enclosure.Real.IsNear.const Bool.true 68000000 70055443684) (Enclosure.Real.IsNear.const Bool.true 17998104000 70055443684))) qz106 rfl

noncomputable abbrev qz220 := (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz431 qz491 1))

noncomputable def ep1350 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz213 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@HAdd.hAdd Complex Complex Complex qz4 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz213 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1))) qz220)) Bool.false 1 816 0 1

noncomputable def ep1351 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz213 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1))) qz220) Bool.false 0 1 0 1 Bool.false

noncomputable def ep1352 := @ep1351 0 1 0 1 Bool.false 1 816 0 1 Bool.false 44113 136000 0 1 Bool.false 1 1 816 0 1 Bool.false 44113 44113 136000 0

noncomputable def ep1353 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz213 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (Complex.mk qz10 qz10) Bool.false 0 1 0 1 Bool.false

noncomputable def ep1354 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1))) qz220 Bool.false 1 816 0 1 Bool.false 44113 136000 0 1

noncomputable def ep1355 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz220)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz220)) 1 816 0 1 0 1 0

noncomputable def ep1356 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz220) 1 24 0 1 1 34 0 1 1

noncomputable def ep1357 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1)))) 1 24 0 1 0 1 0 1 1

noncomputable def ep1358 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 1 2 0 1 1 24 0

noncomputable def ep1359 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1)) qz143 Bool.false 1 2 0 1 Bool.false 132339 1000 0 1 (BSN.ascPochhammer_one_eval qz143)

noncomputable def ep1360 := ep1359 (@Enclosure.Complex.IsNear.of_eq qz143 (Complex.mk qz100 qz146) Bool.false 1 2 0 1 Bool.false 132339 1000 0 1 (BSN.s_crit_mk qz146 Bool.false 132339 1000 qz147) (@Enclosure.Complex.IsNear.mk qz100 qz146 Bool.false 1 2 0 1 Bool.false 132339 1000 0 1 qz412 qz148))

noncomputable def ep1361 := @ep1358 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep713) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 132339 1000 0 1 ep1360)

noncomputable def ep1362 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 132339 1000 0 1 0 1 0

noncomputable def ep1363 := @ep1362 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep713) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 132339 1000 0 1 ep1360)

noncomputable def ep1364 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1)))) 44113 4000 0 1 0 1 0 1 44113

noncomputable def ep1365 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 132339 1000 0 1 44113 4000 0

noncomputable def ep1366 := @ep1365 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep713) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 132339 1000 0 1 ep1360)

noncomputable def ep1367 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 1 2 0 1 0 1 0

noncomputable def ep1368 := @ep1367 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep713) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 132339 1000 0 1 ep1360)

noncomputable def ep1369 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 24 0 1 Bool.false 44113 4000 0 1 (@ep1357 1 24 0 1 (ep1361 rfl) (ep1363 rfl) rfl rfl) (@ep1364 44113 4000 0 1 (ep1366 rfl) (ep1368 rfl) rfl rfl)

noncomputable def ep1370 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 44113 4000 0 1 ep1369

noncomputable abbrev qz221 := (@Enclosure.Complex.IsNear.of_eq (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz431 qz491 1)) (Complex.mk (Enclosure.sfrac Bool.false 1 34) qz278) Bool.false 1 34 0 1 Bool.false 0 1 0 1 (BSN.natCast_pow_inv_mk 34 1 34 EMRow44.d17 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 34) qz278 Bool.false 1 34 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 34) qz546))

noncomputable def ep1371 := @ep1356 816 0 1 ep1370 (@Enclosure.Complex.IsNear.re_isNear qz220 Bool.false 1 34 0 1 Bool.false 0 1 0 1 qz221)

noncomputable def ep1372 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz220) 44113 4000 0 1 0 1 0 1 0

noncomputable def ep1373 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 44113 4000 0 1 ep1369

noncomputable def ep1374 := @ep1372 1 0 1 ep1373 (@Enclosure.Complex.IsNear.im_isNear qz220 Bool.false 1 34 0 1 Bool.false 0 1 0 1 qz221)

noncomputable def ep1375 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz220)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz220)) 0 1 0 1 44113 136000 0

noncomputable def ep1376 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz220) 1 24 0 1 0 1 0 1 0

noncomputable def ep1377 := @ep1376 1 0 1 ep1370 (@Enclosure.Complex.IsNear.im_isNear qz220 Bool.false 1 34 0 1 Bool.false 0 1 0 1 qz221)

noncomputable def ep1378 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz220) 44113 4000 0 1 1 34 0 1 44113

noncomputable def ep1379 := @ep1378 136000 0 1 ep1373 (@Enclosure.Complex.IsNear.re_isNear qz220 Bool.false 1 34 0 1 Bool.false 0 1 0 1 qz221)

noncomputable def ep1380 := @ep1352 1 (@ep1353 0 1 0 1 (BSN.bern_sum_base qz143 34) qz121) (ep1354 (@ep1355 1 1 1 816 0 1 (ep1371 rfl) (ep1374 rfl) rfl rfl) (@ep1375 1 44113 44113 136000 0 1 (ep1377 rfl) (ep1379 rfl) rfl rfl)) rfl rfl rfl rfl rfl

noncomputable def ep1381 := ep1346 (ep1349 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep1350 Bool.false 44113 136000 0 1 (BSN.bern_sum_succ qz143 34 0 1 1 rfl rfl) (ep1380 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl rfl

noncomputable def ep1382 := @Enclosure.Real.IsNear.mulLit_tf qz216 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz212 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz213 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))))) 93246911199 549755813888 12687885472057 106387095836164096 9450200635769

noncomputable def ep1383 := @ep1382 140110887368000 0 1 881202019496285286077031 ep1186 ep1329 ep1330 (@Enclosure.Complex.IsNear.im_isNear qz211 Bool.true 27865762353 1099511627776 25205068630829 212774191672328192 Bool.true 93246911199 549755813888 12687885472057 106387095836164096 (ep1333 ep1342))

noncomputable def ep1384 := @Enclosure.Complex.IsNear.im_isNear (@HAdd.hAdd Complex Complex Complex qz4 qz212 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz213 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1))))) Bool.false 420546889217 840665324208 0 1 Bool.false

noncomputable def ep1385 := nat_lit 238192955599661494153522501

noncomputable def ep1386 := @Enclosure.Real.IsNear.addLit_tt (@HMul.hMul Real Real Real qz0 qz215 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz212 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz213 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz216 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz212 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz213 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1))))))) 263337045104508465404457 ep1297 ep1385

noncomputable def ep1387 := nat_lit 29811980804218818871643078656000

noncomputable def ep1388 := nat_lit 5335850766015138928109369

noncomputable def ep1389 := nat_lit 89435942412656456614929235968

noncomputable def ep1390 := nat_lit 2054289173136819583397374101077060333308609560576

noncomputable def ep1391 := @Enclosure.Real.IsNear.mulLit_tf qz215 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz212 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz213 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))))) 27865762353 1099511627776 25205068630829 212774191672328192 9450200635769

noncomputable def ep1392 := @ep1391 140110887368000 0 1 263337045104508465404457 ep1297 ep1385 ep1387 (@Enclosure.Complex.IsNear.re_isNear qz211 Bool.true 27865762353 1099511627776 25205068630829 212774191672328192 Bool.true 93246911199 549755813888 12687885472057 106387095836164096 (ep1333 ep1342))

noncomputable def ep1393 := @Enclosure.Real.IsNear.mulLit_tf qz216 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz212 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz213 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))))) 93246911199 549755813888 12687885472057 106387095836164096 420546889217

noncomputable def ep1394 := @ep1393 840665324208 0 1 13071566144611096547061 154053549839129476333568 ep1388 ep1389 (@Enclosure.Complex.IsNear.im_isNear qz211 Bool.true 27865762353 1099511627776 25205068630829 212774191672328192 Bool.true 93246911199 549755813888 12687885472057 106387095836164096 (ep1333 ep1342))

noncomputable abbrev qz659 := (ep1381 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable def ep1395 := @ep1325 ep1303 ep1297 ep1304 ep1299 (@ep1327 ep1328 881202019496285286077031 ep1186 ep1329 ep1330 ep1331 95369619938243067889719 ep1186 ep1302 ep1188 (ep1343 (@ep1344 9450200635769 140110887368000 0 1 qz659) rfl) (ep1383 (@ep1384 9450200635769 140110887368000 0 1 qz659) rfl) rfl rfl) (@ep1386 ep1387 13071566144611096547061 154053549839129476333568 ep1388 ep1389 ep1390 ep1303 ep1297 ep1304 ep1299 (ep1392 (@ep1384 9450200635769 140110887368000 0 1 qz659) rfl) (ep1394 (@ep1344 9450200635769 140110887368000 0 1 qz659) rfl) rfl rfl)

noncomputable def ep1396 := @ep1307 ep1298 ep1299 (@ep1308 212774191672328192 (BSN.head_sum_c_eq qz143 34) (ep1309 (BSN.head_sum_c_succ qz143 33 34 rfl rfl) (ep1324 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))) ep1395 rfl rfl rfl

noncomputable def ep1397 := @Enclosure.Complex.IsNear.re_isNear (zetaApproximant qz143 1 34) Bool.false ep1185 ep1186 ep1187 ep1188 Bool.false 688602470537695705590543 ep1297 ep1298 ep1299 (@ep1300 ep1188 Bool.false 688602470537695705590543 ep1297 ep1298 ep1299 (BSN.zetaApproximant_eq_folded' qz143 1 34 rfl) (ep1396 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

noncomputable def ep1398 := @Enclosure.Real.IsNear.mulLit_tf (Real.sin (@HSub.hSub Real Real Real qz401 (Complex.im (@HSub.hSub Complex Complex Complex qz81 qz182 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz183 (@Nat.cast Complex Complex.instNatCast j))))) qz184)) (Complex.im (zetaApproximant qz143 1 34)) 365 1048576 71682281

noncomputable def ep1399 := @Enclosure.Real.IsNear.recentre' (Real.sin (@HSub.hSub Real Real Real qz401 (Complex.im (@HSub.hSub Complex Complex Complex qz81 qz182 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz183 (@Nat.cast Complex Complex.instNatCast j))))) qz184)) Bool.true 365 1048576 71682281

noncomputable def ep1400 := @Enclosure.Real.IsNear.sin_image (@HSub.hSub Real Real Real qz401 (Complex.im (@HSub.hSub Complex Complex Complex qz81 qz182 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz183 (@Nat.cast Complex Complex.instNatCast j))))) qz184) qz474 Bool.false 35412727 262144 365

noncomputable def ep1401 := BSN.sin_dyadic_bound_f 748936 2147483648 1 0 1048576 387412 0 1 1 0 1 1 365 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 748936) qz15 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 748936) qz16 0 0 rfl) rfl rfl

noncomputable def ep1402 := @ep1400 1048576 Bool.true 365 1048576 1 193517 (@ep1193 35412727 262144 365 1048576 ep1294 rfl) (Enclosure.sfrac_false_div 35412727 262144) (BSN.sin_reduce2 qz474 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 13175435109517492224) qz325) 226375608064910080 72057594037927936 Bool.false 365 1048576 21 1000000000000000 387034 193517 (BSN.sin_reduce_arg_pos_rat_q2 35412727 262144 226375608064910080 72057594037927936 21 13175435109517492224 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 365 1048576 13175435109517492224 37778931862957161709568 748936 2147483648 387412 387034 (ep1401 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1403 := @Enclosure.Complex.IsNear.im_isNear (zetaApproximant qz143 1 34) Bool.false ep1185 ep1186 ep1187 ep1188 Bool.false 688602470537695705590543 ep1297 ep1298 ep1299 (@ep1300 ep1188 Bool.false 688602470537695705590543 ep1297 ep1298 ep1299 (BSN.zetaApproximant_eq_folded' qz143 1 34 rfl) (ep1396 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

theorem EMRow44.d18 : Enclosure.Real.IsNear (hardyZApproximantEM 1 34 qz146) Bool.true ep1168 ep1169 ep1170 ep1171 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantEM 1 34 qz146) ep1172 Bool.true ep1168 ep1169 ep1170 ep1171 (@Eq.refl Real ep1172) (@ep1173 Bool.true ep1168 ep1169 ep1170 ep1171 (BSN.re_exp_mul (@HSub.hSub Real Real Real qz401 (Complex.im (@HSub.hSub Complex Complex Complex qz81 qz182 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz183 (@Nat.cast Complex Complex.instNatCast j))))) qz184) (zetaApproximant qz143 1 34)) (@ep1175 ep1176 ep1177 ep1178 ep1179 ep1180 ep1181 ep1182 ep1183 ep1168 ep1169 ep1170 ep1171 (@ep1184 202917281792 ep1185 ep1186 ep1187 ep1188 ep1174 ep1176 ep1177 ep1178 (@ep1189 202917281792 1048575 1048576 71682281 202917281792 (ep1296 rfl rfl) rfl) ep1397 rfl) (@ep1398 202917281792 688602470537695705590543 ep1297 ep1298 ep1299 ep1179 ep1180 ep1181 ep1182 (@ep1399 202917281792 365 1048576 71682281 202917281792 (ep1402 rfl rfl) rfl) ep1403 rfl) rfl rfl))

theorem EMRow44.d19 : @Eq Nat (Nat.mul (BSN.factNat (Nat.succ (Nat.mul 2 1))) (Nat.pow 4 (Nat.mul 2 1))) 96 := @Eq.refl Nat 96

theorem EMRow44.d20 : @Eq Nat (Nat.mul (Nat.mul 2 1) (Nat.pow (Nat.succ (Nat.mul 4 2)) (Nat.mul 2 1))) 162 := @Eq.refl Nat 162

theorem EMRow44.d21 : @Eq Nat (BSN.factNat (Nat.mul 2 2)) 24 := @Eq.refl Nat 24

theorem EMRow44.d22 : @Eq Nat (Nat.pow 33 (Nat.succ (Nat.mul 2 3))) 42618442977 := @Eq.refl Nat 42618442977

noncomputable abbrev qz660 := (@HAdd.hAdd Complex Complex Complex qz665 qz664 (@Nat.cast Complex Complex.instNatCast 3))

noncomputable abbrev qz497 := qz660

noncomputable abbrev qz222 := (@HDiv.hDiv Real Real Real qz271 (@Norm.norm Complex Complex.instNorm qz497) (@HAdd.hAdd Real Real Real qz421 (Complex.re qz272) qz290))

noncomputable abbrev qz223 := (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 2)

noncomputable abbrev qz224 := (@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 2)))

noncomputable abbrev qz498 := (@HPow.hPow Complex Complex Complex qz536 (@Nat.cast Complex Complex.instNatCast 33) (@HSub.hSub Complex Complex Complex qz607 qz537 qz543))

noncomputable abbrev qz225 := qz498

noncomputable def ep1404 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 33))) (@HMul.hMul Real Real Real qz0 qz222 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225))) 27818264935 1855425871872 177658073 1855425871872 279416123638677225 504403158265495552 109377885483

noncomputable def ep1405 := nat_lit 532467525508067529631014584320

noncomputable def ep1406 := @Enclosure.Real.IsNear.mulLit_ff (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 33)) 26561 1769472 1 1769472 1047335 1048576 6649 1048576 27818264935 1855425871872

noncomputable abbrev qz226 := (@HMul.hMul Real Real Real qz268 (2 : Real) Real.pi)

noncomputable abbrev qz661 := (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid)))

noncomputable abbrev qz499 := (@Inv.inv Real Real.instInv (@HPow.hPow Real Nat Real qz661 qz226 2))

noncomputable def ep1407 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 96 162) qz499 96 162 0 1 26561 1048576 1 1048576 26561 1769472 1 1769472

noncomputable def ep1408 := nat_lit 781950621441006189802102638025

noncomputable def ep1409 := nat_lit 19807040628566084398385987584

noncomputable def ep1410 := nat_lit 26986075409044041160201671

noncomputable def ep1411 := nat_lit 1073741824000000000000000000000000000000

noncomputable abbrev qz500 := (@HPow.hPow Real Nat Real qz661 qz226 1)

noncomputable def ep1412 := @Enclosure.Real.IsNear.mulLit_ff qz500 qz226 884279719003555 140737488355328 1 500000000000000 884279719003555 140737488355328 1 500000000000000 ep1408 ep1409 ep1410 ep1411

noncomputable def ep1413 := ep1412 (@Enclosure.Real.IsNear.of_eq qz500 qz226 Bool.false 884279719003555 140737488355328 1 500000000000000 (BSN.pow_one_r qz226) (@Enclosure.Real.IsNear.of_eq qz226 qz269 Bool.false 884279719003555 140737488355328 1 500000000000000 BSN.two_pi_eq qz270)) (@Enclosure.Real.IsNear.of_eq qz226 qz269 Bool.false 884279719003555 140737488355328 1 500000000000000 BSN.two_pi_eq qz270) rfl

noncomputable abbrev qz501 := (@HPow.hPow Real Nat Real qz661 qz226 2)

noncomputable def ep1414 := @Enclosure.Real.IsNear.inv_image qz501 ep1408 ep1409 ep1410 ep1411 13280 13281 524288 (@Enclosure.Real.IsNear.of_eq qz501 (@HMul.hMul Real Real Real qz0 qz500 qz226) Bool.false ep1408 ep1409 ep1410 ep1411 (BSN.pow_succ_r qz226 1 2 rfl) ep1413) rfl rfl rfl

noncomputable def ep1415 := ep1407 (Enclosure.Real.IsNear.const Bool.false 96 162) (@Enclosure.Real.IsNear.recentre' qz499 Bool.false 26561 1048576 1 1048576 26561 1048576 1 1048576 (ep1414 rfl rfl rfl) rfl)

noncomputable def ep1416 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 33)) (Real.sqrt (@HAdd.hAdd Real Real Real qz421 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz5 1 33)) (Complex.re (zetaApproximant qz5 1 33))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz5 1 33)) (Complex.im (zetaApproximant qz5 1 33))))) Bool.false 1047335 1048576 6649 1048576

noncomputable def ep1417 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz421 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz5 1 33)) (Complex.re (zetaApproximant qz5 1 33))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz5 1 33)) (Complex.im (zetaApproximant qz5 1 33))))) Bool.false 1047335 1048576 6649 1048576

noncomputable def ep1418 := nat_lit 50154191837181139969111560117282081694349

noncomputable def ep1419 := nat_lit 50271125665593666332194373305783812096000

noncomputable def ep1420 := nat_lit 1053796627875530157914038867619739706771173409032846237177433

noncomputable def ep1421 := nat_lit 83202081274583760279494293369699287177322530175759417344000000

noncomputable def ep1422 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz421 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz5 1 33)) (Complex.re (zetaApproximant qz5 1 33))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz5 1 33)) (Complex.im (zetaApproximant qz5 1 33)))) ep1418 ep1419 ep1420 ep1421 520343 526992

noncomputable def ep1423 := nat_lit 13292321073514765054821542803709752841022041550736849

noncomputable def ep1424 := nat_lit 13330523199937209168679541634527696198068862976000000

noncomputable def ep1425 := nat_lit 2053632193198671454788104039295420198816868427268759711490841

noncomputable def ep1426 := nat_lit 166404162549167520558988586739398574354645060351518834688000000

noncomputable def ep1427 := nat_lit 7194483528592648163655448684847267882304124988401

noncomputable def ep1428 := nat_lit 79942314892427942281442512509717355148856875254715204243

noncomputable def ep1429 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz5 1 33)) (Complex.re (zetaApproximant qz5 1 33))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz5 1 33)) (Complex.im (zetaApproximant qz5 1 33))) ep1423 ep1424 ep1425 ep1426 ep1427 ep1424 ep1428

noncomputable def ep1430 := nat_lit 246524685258025956383686795169479369414288978298546421760000

noncomputable def ep1431 := nat_lit 177289500681092315627556773209961390122461628177811504188712006068084270968645532660162671673344000000000

noncomputable def ep1432 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (zetaApproximant qz5 1 33)) (Complex.re (zetaApproximant qz5 1 33)) ep539 ep540 ep541 ep542 ep539 ep540 ep541 ep542 ep1423

noncomputable def ep1433 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (zetaApproximant qz5 1 33)) (Complex.im (zetaApproximant qz5 1 33)) ep662 ep540 ep663 ep542 ep662 ep540 ep663 ep542 ep1427

noncomputable def ep1434 := @ep1404 1008806316530991104 ep1405 7748422293051662995 13618885273168379904 2610985084664713 27237770546336759808 (@ep1406 177658073 1855425871872 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaStirlingErrorBound 1 2) (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 96 162) qz499) Bool.false 26561 1769472 1 1769472 (BSN.theta_err_eq 1 2 96 162 EMRow44.d19 EMRow44.d20 rfl) (ep1415 rfl)) (ep1416 (BSN.norm_eq_sqrt_mul_add (zetaApproximant qz5 1 33)) (@ep1417 1047335 1048576 6649 1048576 (@ep1422 524288 (@ep1429 ep1430 ep1431 ep1418 ep1419 ep1420 ep1421 (@ep1432 ep1424 ep1425 ep1426 ep750 ep750 rfl) (@ep1433 ep1424 ep1428 ep1430 ep756 ep756 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl)

noncomputable abbrev qz227 := (@Norm.norm Complex Complex.instNorm qz497)

noncomputable abbrev qz662 := (Enclosure.sfrac Bool.false 2 7)

noncomputable def ep1435 := @Enclosure.Real.IsNear.of_eq (@HMul.hMul Real Real Real qz0 qz222 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225))) (@HMul.hMul Real Real Real qz0 (@HMul.hMul Real Real Real qz0 qz227 qz662) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225))) Bool.false 279416123638677225 504403158265495552 109377885483 1008806316530991104 (BSN.zrb_shape_eq qz227 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)) qz12 3)

noncomputable def ep1436 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz0 qz227 qz662) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)) 136649385 3670016 1 3670016 2044766785 137438953472 1541 549755813888

noncomputable def ep1437 := @Enclosure.Real.IsNear.mulLit_ff qz227 qz662 136649385 1048576 1 1048576 2 7 0 1 136649385 3670016

noncomputable abbrev qz502 := (Complex.re qz660)

noncomputable abbrev qz503 := (Complex.im qz660)

noncomputable abbrev qz228 := (@HAdd.hAdd Real Real Real qz421 (@HMul.hMul Real Real Real qz268 qz502 qz502) (@HMul.hMul Real Real Real qz268 qz503 qz503))

noncomputable abbrev qz229 := qz497

noncomputable def ep1438 := @Enclosure.Real.IsNear.of_eq qz227 (Real.sqrt qz228) Bool.false 136649385 1048576 1 1048576 (BSN.norm_eq_sqrt_mul_add qz229)

noncomputable def ep1439 := @Enclosure.Real.IsNear.recentre' (Real.sqrt qz228) Bool.false 136649385 1048576 1 1048576 136649385

noncomputable def ep1440 := @Enclosure.Real.IsNear.sqrt_image qz228 1061440249 62500 0 1 68324692 68324693 524288

noncomputable abbrev qz230 := (@HMul.hMul Real Real Real qz268 qz502 qz502)

noncomputable abbrev qz231 := (@HMul.hMul Real Real Real qz268 qz503 qz503)

noncomputable def ep1441 := @Enclosure.Real.IsNear.addLit_ff qz230 qz231 49 4 0 1 265168656 15625 0 1

noncomputable abbrev qz232 := qz502

noncomputable def ep1442 := @Enclosure.Real.IsNear.mulLit_ff qz232 qz232 7 2 0 1 7 2 0 1 49 4

noncomputable abbrev qz504 := (Enclosure.sfrac Bool.false 7 2)

noncomputable def ep1443 := @Enclosure.Complex.IsNear.of_eq qz229 (Complex.mk qz504 qz12) Bool.false 7 2 0 1 Bool.false 130272 1000 0 1 (BSN.s_add_nat_mk qz12 Bool.false 130272 1000 3 qz13)

noncomputable abbrev qz505 := (ep1443 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7 2) qz12 Bool.false 7 2 0 1 Bool.false 130272 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 7 2) qz18))

noncomputable def ep1444 := @ep1442 0 1 (@Enclosure.Complex.IsNear.re_isNear qz229 Bool.false 7 2 0 1 Bool.false 130272 1000 0 1 qz505)

noncomputable def ep1445 := ep1444 (@Enclosure.Complex.IsNear.re_isNear qz229 Bool.false 7 2 0 1 Bool.false 130272 1000 0 1 qz505)

noncomputable abbrev qz233 := qz503

noncomputable def ep1446 := @Enclosure.Real.IsNear.mulLit_ff qz233 qz233 130272 1000 0 1 130272 1000 0 1 265168656 15625

noncomputable def ep1447 := @ep1446 0 1 (@Enclosure.Complex.IsNear.im_isNear qz229 Bool.false 7 2 0 1 Bool.false 130272 1000 0 1 qz505)

noncomputable def ep1448 := ep1447 (@Enclosure.Complex.IsNear.im_isNear qz229 Bool.false 7 2 0 1 Bool.false 130272 1000 0 1 qz505)

noncomputable def ep1449 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)) (Real.sqrt (@HAdd.hAdd Real Real Real qz421 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)) (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)) (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225))))) Bool.false 2044766785 137438953472

noncomputable def ep1450 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz421 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)) (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)) (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225))))) Bool.false 16358134280 1099511627776

noncomputable def ep1451 := nat_lit 25273024666232406324787666562272356117822583650270594947357193

noncomputable def ep1452 := nat_lit 114179815416476790484662877555959610910619729920000000000000000000

noncomputable def ep1453 := nat_lit 22565134594604563444411221616737937131601578127536639286153090865531809703592419

noncomputable def ep1454 := nat_lit 270614843797271056172342029089225854768808621226593553160367970556313600000000000000000000

noncomputable def ep1455 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz421 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)) (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)) (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)))) ep1451 ep1452 ep1453 ep1454

noncomputable def ep1456 := nat_lit 12879340430988794702537328010283480019070025087202507489

noncomputable def ep1457 := nat_lit 142724769270595988105828596944949513638274662400000000000000000000

noncomputable def ep1458 := nat_lit 256892960674353038189321298036798828765442341990278916541245243995511675247

noncomputable def ep1459 := nat_lit 67653710949317764043085507272306463692202155306648388290091992639078400000000000000000000

noncomputable def ep1460 := nat_lit 126365071813800307668759522662049739455192841971252625926756009

noncomputable def ep1461 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)) (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)) (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225))) ep1456 ep1457 ep1458 ep1459 ep1460

noncomputable def ep1462 := nat_lit 570899077082383952423314387779798054553098649600000000000000000000

noncomputable def ep1463 := nat_lit 22564107022761866032258464331545789936286516358168678170486925884555827656891431

noncomputable def ep1464 := nat_lit 18035433071290506875007978261025951016064233508760555368960174784796072153929674309443459105342835671433216000000000000000000000

noncomputable def ep1465 := nat_lit 3588779796948928810459239183

noncomputable def ep1466 := nat_lit 377789318629571617095680000000000

noncomputable def ep1467 := nat_lit 51984598174127052287168195764773943

noncomputable def ep1468 := nat_lit 260103269778212830607427501325025280000000000

noncomputable def ep1469 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)) (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)) ep1465 ep1466 ep1467 ep1468 ep1465 ep1466 ep1467

noncomputable def ep1470 := nat_lit 11241221989347968910999789717747

noncomputable def ep1471 := nat_lit 755578637259143234191360000000000

noncomputable def ep1472 := nat_lit 1457734569974649442844608692059071163

noncomputable def ep1473 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225) Bool.true ep1465 ep1466 ep1467 ep1468 Bool.true ep1470 ep1471 ep1472

noncomputable def ep1474 := nat_lit 520206539556425661214855002650050560000000000

noncomputable def ep1475 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225 Bool.true ep1465 ep1466 ep1467 ep1468 Bool.true ep1470 ep1471 ep1472 ep1474

noncomputable def ep1476 := nat_lit 1551896703585398769576198543

noncomputable def ep1477 := nat_lit 3022314549036572936765440000000

noncomputable def ep1478 := nat_lit 201225773314998918337173531831247

noncomputable def ep1479 := nat_lit 2080826158225702644859420010600202240000000

noncomputable def ep1480 := nat_lit 47599577037806479346641394673

noncomputable def ep1481 := nat_lit 94447329657392904273920000000000

noncomputable def ep1482 := nat_lit 6707844127438046873755376071467017

noncomputable abbrev qz234 := (Complex.re qz498)

noncomputable abbrev qz235 := (Complex.im qz498)

noncomputable def ep1483 := @Enclosure.Real.IsNear.subLit_tt_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz234) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz235) ep1476 ep1477 ep1478 ep1479 ep1480 ep1481 ep1482

noncomputable def ep1484 := nat_lit 65025817444553207651856875331256320000000000

noncomputable def ep1485 := nat_lit 2711605348401816392598780932670460855231617832058880000000

noncomputable def ep1486 := nat_lit 69360871940856754828647333686673408

noncomputable def ep1487 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz234 3181945747 30000000 0 1 1463158231137558207 302231454903657293676544 63239850492334279996501 ep1486 ep1476

noncomputable def ep1488 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) 3181945747 30000000 0 1 0 1 0 1 3181945747

noncomputable def ep1489 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 9545837241 125000 0 1 3181945747 30000000 0

noncomputable def ep1490 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (Complex.mk (Enclosure.sfrac Bool.true 1 720) qz10) Bool.true 1 720 0 1 Bool.false 0 1 0 1 (BSN.bern_coeff_mk 2 1 30 24 Bool.true BSN.bern_real_2 EMRow44.d21 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 1 720) qz10 Bool.true 1 720 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.true 1 720) qz22)

noncomputable abbrev qz506 := (@HAdd.hAdd Complex Complex Complex qz535 qz534 qz544)

noncomputable abbrev qz236 := qz506

noncomputable def ep1491 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) (@HMul.hMul Complex Complex Complex qz80 (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) qz236) Bool.true 9545837241 125000 0 1 Bool.true 4316543378679 1953125 0 1

noncomputable abbrev qz237 := (Complex.re qz506)

noncomputable abbrev qz238 := (Complex.im qz506)

noncomputable def ep1492 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz237) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz238) 1060627749 25000 0 1 530337312 15625 0 1

noncomputable def ep1493 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz237 1060627749 62500 0 1 5 2 0 1 1060627749 25000

noncomputable abbrev qz507 := (@HAdd.hAdd Complex Complex Complex qz535 qz534 (@Nat.cast Complex Complex.instNatCast 1))

noncomputable abbrev qz239 := qz507

noncomputable def ep1494 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) (@HMul.hMul Complex Complex Complex qz80 (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) qz239) Bool.true 1060627749 62500 0 1 Bool.false 32568 125 0 1

noncomputable abbrev qz240 := (Complex.re qz507)

noncomputable abbrev qz241 := (Complex.im qz507)

noncomputable def ep1495 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz240) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz241) 3 4 0 1 265168656 15625 0 1

noncomputable def ep1496 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz240 1 2 0 1 3 2 0 1 3 4

noncomputable def ep1497 := @ep1496 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 130272 1000 0 1 ep715)

noncomputable abbrev qz508 := (Enclosure.sfrac Bool.false 3 2)

noncomputable def ep1498 := @Enclosure.Complex.IsNear.of_eq qz239 (Complex.mk qz508 qz12) Bool.false 3 2 0 1 Bool.false 130272 1000 0 1 (BSN.s_add_nat_mk qz12 Bool.false 130272 1000 1 qz13)

noncomputable abbrev qz509 := (ep1498 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 3 2) qz12 Bool.false 3 2 0 1 Bool.false 130272 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 3 2) qz18))

noncomputable def ep1499 := ep1497 (@Enclosure.Complex.IsNear.re_isNear qz239 Bool.false 3 2 0 1 Bool.false 130272 1000 0 1 qz509)

noncomputable def ep1500 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz241 130272 1000 0 1 130272 1000 0 1 265168656 15625

noncomputable def ep1501 := @ep1500 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 130272 1000 0 1 ep715)

noncomputable def ep1502 := ep1501 (@Enclosure.Complex.IsNear.im_isNear qz239 Bool.false 3 2 0 1 Bool.false 130272 1000 0 1 qz509)

noncomputable def ep1503 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) qz239 Bool.true 1060627749 62500 0 1 Bool.false 32568 125 0 1 (@ep1495 1060627749 1060627749 62500 0 1 (ep1499 rfl) (ep1502 rfl) rfl rfl)

noncomputable def ep1504 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz241) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz240) 8142 125 0 1 24426 125 0 1

noncomputable def ep1505 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz241 1 2 0 1 130272 1000 0 1 8142 125

noncomputable def ep1506 := @ep1505 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 130272 1000 0 1 ep715)

noncomputable def ep1507 := ep1506 (@Enclosure.Complex.IsNear.im_isNear qz239 Bool.false 3 2 0 1 Bool.false 130272 1000 0 1 qz509)

noncomputable def ep1508 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz240 130272 1000 0 1 3 2 0 1 24426 125

noncomputable def ep1509 := @ep1508 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 130272 1000 0 1 ep715)

noncomputable def ep1510 := ep1509 (@Enclosure.Complex.IsNear.re_isNear qz239 Bool.false 3 2 0 1 Bool.false 130272 1000 0 1 qz509)

noncomputable abbrev qz242 := (ep1494 (BSN.ascPochhammer_succ_eval_c 1 2 qz272 rfl) (ep1503 (@ep1504 4071000 32568 125 0 1 (ep1507 rfl) (ep1510 rfl) rfl rfl)))

noncomputable def ep1511 := @ep1493 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 1060627749 62500 0 1 Bool.false 32568 125 0 1 qz242)

noncomputable abbrev qz510 := (Enclosure.sfrac Bool.false 5 2)

noncomputable def ep1512 := @Enclosure.Complex.IsNear.of_eq qz236 (Complex.mk qz510 qz12) Bool.false 5 2 0 1 Bool.false 130272 1000 0 1 (BSN.s_add_nat_mk qz12 Bool.false 130272 1000 2 qz13)

noncomputable abbrev qz511 := (ep1512 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 5 2) qz12 Bool.false 5 2 0 1 Bool.false 130272 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 5 2) qz18))

noncomputable def ep1513 := ep1511 (@Enclosure.Complex.IsNear.re_isNear qz236 Bool.false 5 2 0 1 Bool.false 130272 1000 0 1 qz511)

noncomputable def ep1514 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz238 32568 125 0 1 130272 1000 0 1 530337312 15625

noncomputable def ep1515 := @ep1514 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 1060627749 62500 0 1 Bool.false 32568 125 0 1 qz242)

noncomputable def ep1516 := ep1515 (@Enclosure.Complex.IsNear.im_isNear qz236 Bool.false 5 2 0 1 Bool.false 130272 1000 0 1 qz511)

noncomputable def ep1517 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) qz236 Bool.true 9545837241 125000 0 1 Bool.true 4316543378679 1953125 0 1 (@ep1492 29830741378125 9545837241 125000 0 1 (ep1513 rfl) (ep1516 rfl) rfl rfl)

noncomputable def ep1518 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz238) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz237) 4317815566179 1953125 0 1 16284 25 0 1

noncomputable def ep1519 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz238 1060627749 62500 0 1 130272 1000 0 1 4317815566179 1953125

noncomputable def ep1520 := @ep1519 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 1060627749 62500 0 1 Bool.false 32568 125 0 1 qz242)

noncomputable def ep1521 := ep1520 (@Enclosure.Complex.IsNear.im_isNear qz236 Bool.false 5 2 0 1 Bool.false 130272 1000 0 1 qz511)

noncomputable def ep1522 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz237 32568 125 0 1 5 2 0 1 16284 25

noncomputable def ep1523 := @ep1522 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 1060627749 62500 0 1 Bool.false 32568 125 0 1 qz242)

noncomputable def ep1524 := ep1523 (@Enclosure.Complex.IsNear.re_isNear qz236 Bool.false 5 2 0 1 Bool.false 130272 1000 0 1 qz511)

noncomputable abbrev qz243 := (ep1491 (BSN.ascPochhammer_succ_eval_c 2 3 qz272 rfl) (ep1517 (@ep1518 107913584466975 4316543378679 1953125 0 1 (ep1521 rfl) (ep1524 rfl) rfl rfl)))

noncomputable def ep1525 := @ep1489 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1490) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 9545837241 125000 0 1 Bool.true 4316543378679 1953125 0 1 qz243)

noncomputable def ep1526 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 4316543378679 1953125 0 1 0 1 0

noncomputable def ep1527 := @ep1526 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1490) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 9545837241 125000 0 1 Bool.true 4316543378679 1953125 0 1 qz243)

noncomputable def ep1528 := @Enclosure.Real.IsNear.addLit_ft_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) 1438847792893 468750000 0 1 0 1 0 1 1438847792893

noncomputable def ep1529 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 4316543378679 1953125 0 1 1438847792893 468750000 0

noncomputable def ep1530 := @ep1529 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1490) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 9545837241 125000 0 1 Bool.true 4316543378679 1953125 0 1 qz243)

noncomputable def ep1531 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 9545837241 125000 0 1 0 1 0

noncomputable def ep1532 := @ep1531 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1490) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 9545837241 125000 0 1 Bool.true 4316543378679 1953125 0 1 qz243)

noncomputable def ep1533 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.false 3181945747 30000000 0 1 Bool.false 1438847792893 468750000 0 1 (@ep1488 3181945747 30000000 0 1 (ep1525 rfl) (ep1527 rfl) rfl rfl) (@ep1528 1438847792893 468750000 0 1 (ep1530 rfl) (ep1532 rfl) rfl rfl)

noncomputable def ep1534 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 3181945747 30000000 0 1 Bool.false 1438847792893 468750000 0 1 ep1533

noncomputable def ep1535 := nat_lit 138721743881713509657294667373346816

noncomputable def ep1536 := @Enclosure.Complex.IsNear.re_isNear qz225 Bool.true 1463158231137558207 302231454903657293676544 63239850492334279996501 ep1486 Bool.true 99245195926042383 604462909807314587353088 4661955323259738351869 ep1535

noncomputable abbrev qz512 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 42618442977)))

noncomputable def ep1537 := @Enclosure.Complex.IsNear.of_eq qz225 (Complex.mk (@HMul.hMul Real Real Real qz0 qz512 (Real.cos qz135)) (@HMul.hMul Real Real Real qz0 qz512 qz619)) Bool.true 1463158231137558207 302231454903657293676544 63239850492334279996501 ep1486 Bool.true 99245195926042383 604462909807314587353088 4661955323259738351869

noncomputable abbrev qz513 := (Real.sqrt (@Nat.cast Real Real.instNatCast 42618442977))

noncomputable abbrev qz514 := (@Nat.cast Real Real.instNatCast 42618442977)

noncomputable def ep1538 := @Enclosure.Real.IsNear.inv_image qz513 226985761902963997 1099511627776 1 1099511627776 2662999 2663000 549755813888 (@Enclosure.Real.IsNear.of_eq qz513 (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz514 qz14)) Bool.false 226985761902963997 1099511627776 1 1099511627776 (BSN.sqrt_natCast_div_one 42618442977) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz514 qz14)) Bool.false 226985761902963997 1099511627776 1 1099511627776 226985761902963997 1099511627776 1 1099511627776 (BSN.sqrt_enclosure 42618442977 1 113492880951481998 113492880951481999 549755813888 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep1539 := nat_lit 478116404493750000000000000

noncomputable def ep1540 := nat_lit 45899174831400000000000000

noncomputable def ep1541 := nat_lit 69255467328018160352285949952

noncomputable def ep1542 := nat_lit 229495874157000000000000000

noncomputable def ep1543 := BSN.log_dyadic_bound 1 65 3 2 267759375 549755813888 229495874157 21128 3 16916898254 66 64 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 1) (BSN.artanhQ 65) 0 2 21128 267759375 3 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep1544 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz137 130272 1000 0 1 15746870150910163 4503599627370496 200229495874157 ep1540 64105508384355273573 140737488355328000 271711425901231049 ep1539 qz18 (BSN.isNear_log_sfrac 33 1 15746870150910163 4503599627370496 200229495874157 ep1540 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz433) Bool.false ep1541 ep1409 1001147479370785 ep1542 15746870150910163 4503599627370496 200229495874157 ep1540 (BSN.log_rat_reduce_isNear 33 1 5 66 64 16916898254 549755813888 24973259072661432 36028797018963968 229495874157 1000000000000000 rfl rfl rfl rfl (ep1543 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1545 := nat_lit 243530670809790619915575623680

noncomputable def ep1546 := nat_lit 158456325028528675187087900672

noncomputable def ep1547 := nat_lit 7240038326307631179018638304477333938429280593393601913693153859407293437526632686123795995201101790311842601963523478599103282956833474453493391911618751650418201533569131187553447242786307296909333698700090055414698316757518624578225836011149326286848000000

noncomputable def ep1548 := nat_lit 155433625461590811300248653684703508738906887282493828366197298645519518790118634907255632381243555533316827446940106385055636004350275585915152922536618788469110716965662258357051938969424840669115718701241640255984264744212126888020762883150876583925907456000

noncomputable def ep1549 := nat_lit 423430202173217892228079486230209860711313465080026788661143295392282609375659427926554669550389009024302109435469790843980946044483969489417801710220354858927452255167216532603340633995951144490282108690803322812238111733099319132160000000000000000

noncomputable def ep1550 := nat_lit 58887453308842257930338145444905283085479740602834837810985133143106674848215804442524400273715273114739565229172268065974324549323474115443392086540074350348914331799043975018251627372901805082684498390372575006377031235166184599552835570617436023554048000000

noncomputable def ep1551 := nat_lit 8859716651310676244114173260028099998117692575102148216873246022794612571036762189713571045730882665399059164475586063948171252247965708397163716584587270942739310867042748726351960521257215918139595965970773494591103090420091232617183484339599965283776724992000

noncomputable def ep1552 := BSN.sin_dyadic_bound_f 3460778981573620 2251799813685248 5 4 1099511627776 459439982444 ep1547 ep1548 ep1549 ep1550 ep1551 ep1549 1098879839172 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.sinEvenP 3460778981573620) (BSN.sinEvenQ 2251799813685248) 0 4 ep1547 ep1548 ep1549 rfl rfl rfl rfl) (@BSN.binarySplit_of_base4 (BSN.sinOddP 3460778981573620) (BSN.sinOddQ 2251799813685248) 0 4 ep1550 ep1551 ep1549 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz515 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 500824284252775) (@Nat.cast Real Real.instNatCast 1099511627776))

noncomputable def ep1553 := @Enclosure.Real.IsNear.cos_image qz135 qz515 Bool.false 500824284252775 1099511627776 313 549755813888 Bool.true 1098879839172 1099511627776 1 229495874157 (@Enclosure.Real.IsNear.recentre' qz135 Bool.false 64105508384355273573 140737488355328000 271711425901231049 ep1539 500824284252775 1099511627776 313 549755813888 (ep1544 rfl) rfl) (Enclosure.sfrac_false_div 500824284252775 1099511627776) (BSN.cos_reduce1 qz515 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep1545) (@Nat.cast Real Real.instNatCast ep1546)) 226375608064910080 72057594037927936 Bool.false 1098879839172 1099511627776 72 1000000000000000 458991748314 229495874157 (BSN.sin_reduce_arg_pos_rat_q1 500824284252775 1099511627776 226375608064910080 72057594037927936 72 ep1545 ep1546 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1098879839172 1099511627776 ep1545 ep1546 3460778981573620 2251799813685248 459439982444 458991748314 (ep1552 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1554 := nat_lit 2132562302700225523226175182538506660350198380924033125294855310017683994421356896440666160234057090832975925188667086203899308370896001810973689283885584204575489074286323259228711863822853725646167399392220161380349240975229177407688549284061087006720000000

noncomputable def ep1555 := nat_lit 9143154438917106547073450216747265219935699251911401668599841096795265811183449112191507787131973854900989849820006257944449176726486799171479583678624634615830042174450721079826584645260284745242101100073037662116721455541889816942397816655933916701523968000

noncomputable def ep1556 := nat_lit 21704107697893498715433470367943150037000813113502658159783797642808705831341248624367593883312854449979637474729848300327634813437163472010366061111849610004613120091936931556759812648110728317349705491889916192546732463739181503444165593073809352556544000000

noncomputable def ep1557 := nat_lit 1398902629154317301702237883162331578650161985542444455295775687809675669111067714165300691431191999799851447022460957465500724039152480273236376302829569096221996452690960325213467450724823566022041468311174762303858382697909141992186865948357889255333167104000

noncomputable def ep1558 := BSN.cos_dyadic_bound_f 3460778981573620 2251799813685248 5 4 1099511627776 459439982444 ep1554 ep1555 ep1549 ep1556 ep1557 ep1549 37268199234 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.cosEvenP 3460778981573620) (BSN.cosEvenQ 2251799813685248) 0 4 ep1554 ep1555 ep1549 rfl rfl rfl rfl) (@BSN.binarySplit_of_base4 (BSN.cosOddP 3460778981573620) (BSN.cosOddQ 2251799813685248) 0 4 ep1556 ep1557 ep1549 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1559 := @Enclosure.Real.IsNear.sin_image qz135 qz515 Bool.false 500824284252775 1099511627776 313 549755813888 Bool.false 37268199234 1099511627776 1 229495874157 (@Enclosure.Real.IsNear.recentre' qz135 Bool.false 64105508384355273573 140737488355328000 271711425901231049 ep1539 500824284252775 1099511627776 313 549755813888 (ep1544 rfl) rfl) (Enclosure.sfrac_false_div 500824284252775 1099511627776) (BSN.sin_reduce1 qz515 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep1545) (@Nat.cast Real Real.instNatCast ep1546)) 226375608064910080 72057594037927936 Bool.false 37268199234 1099511627776 72 1000000000000000 458991748314 229495874157 (BSN.sin_reduce_arg_pos_rat_q1 500824284252775 1099511627776 226375608064910080 72057594037927936 72 ep1545 ep1546 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 37268199234 1099511627776 ep1545 ep1546 3460778981573620 2251799813685248 459439982444 458991748314 (ep1558 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1560 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz512 (Real.cos qz135)) (@HMul.hMul Real Real Real qz0 qz512 qz619) Bool.true 1463158231137558207 302231454903657293676544 63239850492334279996501 ep1486 Bool.true 99245195926042383 604462909807314587353088 4661955323259738351869 ep1535 (@Enclosure.Real.IsNear.mulLit_ft qz512 (Real.cos qz135) 5325999 1099511627776 1 1099511627776 274719959793 274877906944 72381964425029 126166691081119560892416 1463158231137558207 302231454903657293676544 63239850492334279996501 ep1486 (@Enclosure.Real.IsNear.recentre' qz512 Bool.false 5325999 1099511627776 1 1099511627776 5325999 1099511627776 1 1099511627776 (ep1538 rfl rfl) rfl) (@Enclosure.Real.IsNear.recentre' (Real.cos qz135) Bool.true 1098879839172 1099511627776 72381964425029 126166691081119560892416 274719959793 274877906944 72381964425029 126166691081119560892416 (ep1553 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz512 qz619 5325999 1099511627776 1 1099511627776 18634099617 549755813888 72381964425029 126166691081119560892416 99245195926042383 604462909807314587353088 4661955323259738351869 ep1535 (@Enclosure.Real.IsNear.recentre' qz512 Bool.false 5325999 1099511627776 1 1099511627776 5325999 1099511627776 1 1099511627776 (ep1538 rfl rfl) rfl) (@Enclosure.Real.IsNear.neg qz136 Bool.false 18634099617 549755813888 72381964425029 126166691081119560892416 (@Enclosure.Real.IsNear.recentre' qz136 Bool.false 37268199234 1099511627776 72381964425029 126166691081119560892416 18634099617 549755813888 72381964425029 126166691081119560892416 (ep1559 rfl rfl) rfl)) rfl)

noncomputable def ep1561 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz235 1438847792893 468750000 0 1 99245195926042383 604462909807314587353088 4661955323259738351869 ep1535 ep1480

noncomputable def ep1562 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 3181945747 30000000 0 1 Bool.false 1438847792893 468750000 0 1 ep1533

noncomputable def ep1563 := @Enclosure.Complex.IsNear.im_isNear qz225 Bool.true 1463158231137558207 302231454903657293676544 63239850492334279996501 ep1486 Bool.true 99245195926042383 604462909807314587353088 4661955323259738351869 ep1535

noncomputable def ep1564 := nat_lit 105264276362350762376198367

noncomputable def ep1565 := nat_lit 6044629098073145873530880000000

noncomputable def ep1566 := nat_lit 14834088913550334625062354051143

noncomputable def ep1567 := nat_lit 4161652316451405289718840021200404480000000

noncomputable def ep1568 := nat_lit 701753997175167191606422807617

noncomputable def ep1569 := nat_lit 47223664828696452136960000000000

noncomputable def ep1570 := nat_lit 90992519303778478188529743612667393

noncomputable def ep1571 := @Enclosure.Real.IsNear.addLit_tt (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz235) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz234) ep1564 ep1565 ep1566 ep1567 ep1568 ep1569 ep1570

noncomputable def ep1572 := nat_lit 32512908722276603825928437665628160000000000

noncomputable def ep1573 := nat_lit 4246813595919526745537130938515731991212412267093032960000000

noncomputable def ep1574 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz235 3181945747 30000000 0 1 99245195926042383 604462909807314587353088 4661955323259738351869 ep1535 ep1564

noncomputable def ep1575 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz234 1438847792893 468750000 0 1 1463158231137558207 302231454903657293676544 63239850492334279996501 ep1486 ep1568

noncomputable abbrev qz516 := (@ep1537 ep1535 (BSN.cpow_neg_s_sub_mk qz12 130272 1000 33 3 42618442977 qz13 rfl EMRow44.d22) ep1560)

noncomputable def ep1576 := ep1475 (@ep1483 ep1484 ep1485 ep1465 ep1466 ep1467 ep1468 (@ep1487 ep1477 ep1478 ep1479 ep1534 (ep1536 qz516) rfl) (@ep1561 ep1481 ep1482 ep1484 ep1562 (ep1563 qz516) rfl) rfl rfl) (@ep1571 ep1572 ep1573 ep1470 ep1471 ep1472 ep1474 (@ep1574 ep1565 ep1566 ep1567 ep1534 (ep1563 qz516) rfl) (@ep1575 ep1569 ep1570 ep1572 ep1562 (ep1536 qz516) rfl) rfl rfl)

noncomputable def ep1577 := @Enclosure.Real.IsNear.mulLit_tt (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)) (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)) ep1470 ep1471 ep1472 ep1474 ep1470 ep1471 ep1472

noncomputable def ep1578 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225) Bool.true ep1465 ep1466 ep1467 ep1468 Bool.true ep1470 ep1471 ep1472

noncomputable def ep1579 := @ep1436 279416123638677225 504403158265495552 109377885483 1008806316530991104 (@ep1437 1 3670016 (ep1438 (@ep1439 1048576 1 1048576 (ep1440 (@ep1441 1061440249 1061440249 62500 0 1 (ep1445 rfl) (ep1448 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) (Enclosure.Real.IsNear.const Bool.false 2 7) rfl) (@ep1449 1541 549755813888 (BSN.norm_eq_sqrt_mul_add (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)) (@ep1450 3082 1099511627776 2044766785 137438953472 1541 549755813888 (@ep1455 8179065599 8179068681 549755813888 (@ep1461 ep1462 ep1463 ep1454 ep1464 ep1451 ep1452 ep1453 ep1454 (@ep1469 ep1468 ep1456 ep1457 ep1458 ep1459 (@ep1473 ep1474 ep1576) (@ep1473 ep1474 ep1576) rfl) (@ep1577 ep1474 ep1460 ep1462 ep1463 ep1454 (@ep1578 ep1474 ep1576) (@ep1578 ep1474 ep1576) rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl

theorem EMRow44.d23 : Enclosure.Real.IsNear (@HAdd.hAdd Real Real Real qz421 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 33))) (@HMul.hMul Real Real Real qz0 qz222 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)))) Bool.false 7748422293051662995 13618885273168379904 2610985084664713 27237770546336759808 := ep1434 (ep1435 ep1579) rfl rfl

theorem EMRow44.d24 : @Eq Nat (Nat.pow 34 (Nat.succ (Nat.mul 2 3))) 52523350144 := @Eq.refl Nat 52523350144

noncomputable abbrev qz663 := (@HAdd.hAdd Complex Complex Complex qz665 qz671 (@Nat.cast Complex Complex.instNatCast 3))

noncomputable abbrev qz517 := qz663

noncomputable abbrev qz244 := (@HDiv.hDiv Real Real Real qz271 (@Norm.norm Complex Complex.instNorm qz517) (@HAdd.hAdd Real Real Real qz421 (Complex.re qz436) qz290))

noncomputable abbrev qz518 := (@HPow.hPow Complex Complex Complex qz536 (@Nat.cast Complex Complex.instNatCast 34) (@HSub.hSub Complex Complex Complex qz607 qz622 qz543))

noncomputable abbrev qz245 := qz518

noncomputable def ep1580 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz143 1 34))) (@HMul.hMul Real Real Real qz0 qz244 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz245))) 6412223815 206158430208 60267395 618475290624 268048086322497237 504403158265495552 117066384535

noncomputable def ep1581 := nat_lit 58494718640295730685648306176

noncomputable def ep1582 := @Enclosure.Real.IsNear.mulLit_ff (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz143 1 34)) 26561 1769472 1 1769472 2172735 1048576 6725 1048576 6412223815 206158430208

noncomputable def ep1583 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (zetaApproximant qz143 1 34)) (Real.sqrt (@HAdd.hAdd Real Real Real qz421 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz143 1 34)) (Complex.re (zetaApproximant qz143 1 34))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz143 1 34)) (Complex.im (zetaApproximant qz143 1 34))))) Bool.false 2172735 1048576 6725 1048576

noncomputable def ep1584 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz421 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz143 1 34)) (Complex.re (zetaApproximant qz143 1 34))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz143 1 34)) (Complex.im (zetaApproximant qz143 1 34))))) Bool.false 2172735 1048576 6725 1048576

noncomputable def ep1585 := nat_lit 5818076173619241209975446770746229981184333

noncomputable def ep1586 := nat_lit 1355069354786339147698750560239878144000000

noncomputable def ep1587 := nat_lit 212580762284497625405502600884209434971381507020007211111172523

noncomputable def ep1588 := nat_lit 7998787795240002009762006150265698500823184064188224897024000000

noncomputable def ep1589 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz421 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz143 1 34)) (Complex.re (zetaApproximant qz143 1 34))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz143 1 34)) (Complex.im (zetaApproximant qz143 1 34)))) ep1585 ep1586 ep1587 ep1588 1083005 1089730

noncomputable def ep1590 := nat_lit 25474125689797202285744871842394837585912017663778961

noncomputable def ep1591 := nat_lit 5933124054509287375883398629378014553000902656000000

noncomputable def ep1592 := nat_lit 52949907835982469272380278327468951331775090003718426920357839

noncomputable def ep1593 := nat_lit 1999696948810000502440501537566424625205796016047056224256000000

noncomputable def ep1594 := nat_lit 474173362430618082245198108692931894784371034849

noncomputable def ep1595 := nat_lit 23732496218037149503533594517512058212003610624000000

noncomputable def ep1596 := nat_lit 781130940567748315981487574333629644281147005133503429741167

noncomputable def ep1597 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz143 1 34)) (Complex.re (zetaApproximant qz143 1 34))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz143 1 34)) (Complex.im (zetaApproximant qz143 1 34))) ep1590 ep1591 ep1592 ep1593 ep1594 ep1595 ep1596

noncomputable def ep1598 := nat_lit 604567404920297740206306800787150800583139984542320971746508391014769763537044982936381714079940608000000

noncomputable def ep1599 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (zetaApproximant qz143 1 34)) (Complex.re (zetaApproximant qz143 1 34)) ep1185 ep1186 ep1187 ep1188 ep1185 ep1186 ep1187 ep1188 ep1590

noncomputable def ep1600 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (zetaApproximant qz143 1 34)) (Complex.im (zetaApproximant qz143 1 34)) 688602470537695705590543 ep1297 ep1298 ep1299 688602470537695705590543 ep1297 ep1298 ep1299 ep1594

noncomputable def ep1601 := @ep1580 1008806316530991104 ep1581 851210186960753791 1513209474796486656 885782813174095 9079256848778919936 (@ep1582 60267395 618475290624 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaStirlingErrorBound 1 2) (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 96 162) qz499) Bool.false 26561 1769472 1 1769472 (BSN.theta_err_eq 1 2 96 162 EMRow44.d19 EMRow44.d20 rfl) (ep1415 rfl)) (ep1583 (BSN.norm_eq_sqrt_mul_add (zetaApproximant qz143 1 34)) (@ep1584 2172735 1048576 6725 1048576 (@ep1589 524288 (@ep1597 ep1588 ep1598 ep1585 ep1586 ep1587 ep1588 (@ep1599 ep1591 ep1592 ep1593 ep1397 ep1397 rfl) (@ep1600 ep1595 ep1596 ep1588 ep1403 ep1403 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl)

noncomputable abbrev qz246 := (@Norm.norm Complex Complex.instNorm qz517)

noncomputable def ep1602 := @Enclosure.Real.IsNear.of_eq (@HMul.hMul Real Real Real qz0 qz244 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz245))) (@HMul.hMul Real Real Real qz0 (@HMul.hMul Real Real Real qz0 qz246 qz662) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz245))) Bool.false 268048086322497237 504403158265495552 117066384535 1008806316530991104 (BSN.zrb_shape_eq qz246 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)) qz146 3)

noncomputable def ep1603 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz0 qz246 qz662) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)) 138816021 3670016 1 3670016 1930959297 137438953472 1631 549755813888

noncomputable def ep1604 := @Enclosure.Real.IsNear.mulLit_ff qz246 qz662 138816021 1048576 1 1048576 2 7 0 1 138816021 3670016

noncomputable abbrev qz519 := (Complex.re qz663)

noncomputable abbrev qz520 := (Complex.im qz663)

noncomputable abbrev qz247 := (@HAdd.hAdd Real Real Real qz421 (@HMul.hMul Real Real Real qz268 qz519 qz519) (@HMul.hMul Real Real Real qz268 qz520 qz520))

noncomputable abbrev qz248 := qz517

noncomputable def ep1605 := @Enclosure.Real.IsNear.of_eq qz246 (Real.sqrt qz247) Bool.false 138816021 1048576 1 1048576 (BSN.norm_eq_sqrt_mul_add qz248)

noncomputable def ep1606 := @Enclosure.Real.IsNear.recentre' (Real.sqrt qz247) Bool.false 138816021 1048576 1 1048576 138816021

noncomputable def ep1607 := @Enclosure.Real.IsNear.sqrt_image qz247 17525860921 1000000 0 1 69408010 69408011 524288

noncomputable abbrev qz249 := (@HMul.hMul Real Real Real qz268 qz519 qz519)

noncomputable abbrev qz250 := (@HMul.hMul Real Real Real qz268 qz520 qz520)

noncomputable def ep1608 := @Enclosure.Real.IsNear.addLit_ff qz249 qz250 49 4 0 1 17513610921 1000000 0 1

noncomputable abbrev qz251 := qz519

noncomputable def ep1609 := @Enclosure.Real.IsNear.mulLit_ff qz251 qz251 7 2 0 1 7 2 0 1 49 4

noncomputable def ep1610 := @Enclosure.Complex.IsNear.of_eq qz248 (Complex.mk qz504 qz146) Bool.false 7 2 0 1 Bool.false 132339 1000 0 1 (BSN.s_add_nat_mk qz146 Bool.false 132339 1000 3 qz147)

noncomputable abbrev qz521 := (ep1610 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7 2) qz146 Bool.false 7 2 0 1 Bool.false 132339 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 7 2) qz148))

noncomputable def ep1611 := @ep1609 0 1 (@Enclosure.Complex.IsNear.re_isNear qz248 Bool.false 7 2 0 1 Bool.false 132339 1000 0 1 qz521)

noncomputable def ep1612 := ep1611 (@Enclosure.Complex.IsNear.re_isNear qz248 Bool.false 7 2 0 1 Bool.false 132339 1000 0 1 qz521)

noncomputable abbrev qz252 := qz520

noncomputable def ep1613 := @Enclosure.Real.IsNear.mulLit_ff qz252 qz252 132339 1000 0 1 132339 1000 0 1 17513610921 1000000

noncomputable def ep1614 := @ep1613 0 1 (@Enclosure.Complex.IsNear.im_isNear qz248 Bool.false 7 2 0 1 Bool.false 132339 1000 0 1 qz521)

noncomputable def ep1615 := ep1614 (@Enclosure.Complex.IsNear.im_isNear qz248 Bool.false 7 2 0 1 Bool.false 132339 1000 0 1 qz521)

noncomputable def ep1616 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)) (Real.sqrt (@HAdd.hAdd Real Real Real qz421 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)) (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz245))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)) (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz245))))) Bool.false 1930959297 137438953472

noncomputable def ep1617 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz421 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)) (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz245))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)) (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz245))))) Bool.false 15447674376 1099511627776

noncomputable def ep1618 := nat_lit 166168365940566709797903870692499323551455617420612360932019067481

noncomputable def ep1619 := nat_lit 841824943102600080885322463644579019321817144754176000000000000000000

noncomputable def ep1620 := nat_lit 91645599358222126815651522719754230394312585780426117761237532421864125095623883

noncomputable def ep1621 := nat_lit 1099566273663977059629187370016813677482474814394914431798559156333445120000000000000000000

noncomputable def ep1622 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz421 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)) (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz245))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)) (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)))) ep1618 ep1619 ep1620 ep1621

noncomputable def ep1623 := nat_lit 44637241612171245390965578291186211946970090514196502775269081

noncomputable def ep1624 := nat_lit 233840261972944466912589573234605283144949206876160000000000000000

noncomputable def ep1625 := nat_lit 27694596260177437322947909661007821621678216147272642394814350636687515503747991

noncomputable def ep1626 := nat_lit 343614460519992831134121053130254274213273379498410759937049736354201600000000000000000000

noncomputable def ep1627 := nat_lit 5474296136750226390427788844228960542363291569504950941050375881

noncomputable def ep1628 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)) (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz245))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)) (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz245))) ep1623 ep1624 ep1625 ep1626 ep1627

noncomputable def ep1629 := nat_lit 5038152209423878970363686340882002008237156848589436829719350640773459139383853

noncomputable def ep1630 := nat_lit 1832610456106628432715312283361356129137458023991524052997598593889075200000000000000000000

noncomputable def ep1631 := nat_lit 38856854223158222124833881736136335565546829699508296125113983083897914951755965148299336210901412085429196250152960000000000000000

noncomputable def ep1632 := nat_lit 6681110806757454564688733054491

noncomputable def ep1633 := nat_lit 483570327845851669882470400000000

noncomputable def ep1634 := nat_lit 1709780070161327192259066650581332679

noncomputable def ep1635 := nat_lit 586186370124717955416266745273384960000000000

noncomputable def ep1636 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)) (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)) ep1632 ep1633 ep1634 ep1635 ep1632 ep1633 ep1634

noncomputable def ep1637 := nat_lit 73988486514796519322022162598109

noncomputable def ep1638 := nat_lit 29014219670751100192948224000000000

noncomputable def ep1639 := nat_lit 1263902406987149775307147227196330463

noncomputable def ep1640 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz245) Bool.false ep1632 ep1633 ep1634 ep1635 Bool.true ep1637 ep1638 ep1639

noncomputable def ep1641 := nat_lit 2344745480498871821665066981093539840000000000

noncomputable def ep1642 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz245 Bool.false ep1632 ep1633 ep1634 ep1635 Bool.true ep1637 ep1638 ep1639 ep1641

noncomputable def ep1643 := nat_lit 4100971449920574368795083879

noncomputable def ep1644 := nat_lit 58028439341502200385896448000000

noncomputable def ep1645 := nat_lit 70236847123958307582032013463853

noncomputable def ep1646 := nat_lit 4689490960997743643330133962187079680000000

noncomputable def ep1647 := nat_lit 629558022078761814165189883139

noncomputable def ep1648 := nat_lit 45334718235548594051481600000000

noncomputable def ep1649 := nat_lit 283500077378472067301885441483058509

noncomputable abbrev qz253 := (Complex.re qz518)

noncomputable abbrev qz254 := (Complex.im qz518)

noncomputable def ep1650 := @Enclosure.Real.IsNear.subLit_tt_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3)))) qz253) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3)))) qz254) ep1643 ep1644 ep1645 ep1646 ep1647 ep1648 ep1649

noncomputable def ep1651 := nat_lit 97697728354119659236044457545564160000000000

noncomputable def ep1652 := nat_lit 36346353110979354518622583997172697209859189832650063872000000

noncomputable def ep1653 := nat_lit 9769772835411965923604445754556416

noncomputable def ep1654 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3)))) qz253 52539582763 480000000 0 1 390274459203414665 604462909807314587353088 1336836789145978311431 ep1653 ep1643

noncomputable def ep1655 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3)))) 52539582763 480000000 0 1 0 1 0 1 52539582763

noncomputable def ep1656 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 157618748289 2000000 0 1 52539582763 480000000 0

noncomputable abbrev qz522 := (@HAdd.hAdd Complex Complex Complex qz535 qz621 qz544)

noncomputable abbrev qz255 := qz522

noncomputable def ep1657 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3)) (@HMul.hMul Complex Complex Complex qz80 (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 2)) qz255) Bool.true 157618748289 2000000 0 1 Bool.true 2316972806424219 1000000000 0 1

noncomputable abbrev qz256 := (Complex.re qz522)

noncomputable abbrev qz257 := (Complex.im qz522)

noncomputable def ep1658 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 2))) qz256) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 2))) qz257) 17512860921 400000 0 1 17513610921 500000 0 1

noncomputable def ep1659 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 2))) qz256 17512860921 1000000 0 1 5 2 0 1 17512860921 400000

noncomputable abbrev qz523 := (@HAdd.hAdd Complex Complex Complex qz535 qz621 (@Nat.cast Complex Complex.instNatCast 1))

noncomputable abbrev qz258 := qz523

noncomputable def ep1660 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 2)) (@HMul.hMul Complex Complex Complex qz80 (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1)) qz258) Bool.true 17512860921 1000000 0 1 Bool.false 132339 500 0 1

noncomputable abbrev qz259 := (Complex.re qz523)

noncomputable abbrev qz260 := (Complex.im qz523)

noncomputable def ep1661 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1))) qz259) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1))) qz260) 3 4 0 1 17513610921 1000000 0 1

noncomputable def ep1662 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1))) qz259 1 2 0 1 3 2 0 1 3 4

noncomputable def ep1663 := @ep1662 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 132339 1000 0 1 ep1360)

noncomputable def ep1664 := @Enclosure.Complex.IsNear.of_eq qz258 (Complex.mk qz508 qz146) Bool.false 3 2 0 1 Bool.false 132339 1000 0 1 (BSN.s_add_nat_mk qz146 Bool.false 132339 1000 1 qz147)

noncomputable abbrev qz524 := (ep1664 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 3 2) qz146 Bool.false 3 2 0 1 Bool.false 132339 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 3 2) qz148))

noncomputable def ep1665 := ep1663 (@Enclosure.Complex.IsNear.re_isNear qz258 Bool.false 3 2 0 1 Bool.false 132339 1000 0 1 qz524)

noncomputable def ep1666 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1))) qz260 132339 1000 0 1 132339 1000 0 1 17513610921 1000000

noncomputable def ep1667 := @ep1666 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 132339 1000 0 1 ep1360)

noncomputable def ep1668 := ep1667 (@Enclosure.Complex.IsNear.im_isNear qz258 Bool.false 3 2 0 1 Bool.false 132339 1000 0 1 qz524)

noncomputable def ep1669 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1)) qz258 Bool.true 17512860921 1000000 0 1 Bool.false 132339 500 0 1 (@ep1661 70051443684 17512860921 1000000 0 1 (ep1665 rfl) (ep1668 rfl) rfl rfl)

noncomputable def ep1670 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1))) qz260) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1))) qz259) 132339 2000 0 1 397017 2000 0 1

noncomputable def ep1671 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1))) qz260 1 2 0 1 132339 1000 0 1 132339 2000

noncomputable def ep1672 := @ep1671 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 132339 1000 0 1 ep1360)

noncomputable def ep1673 := ep1672 (@Enclosure.Complex.IsNear.im_isNear qz258 Bool.false 3 2 0 1 Bool.false 132339 1000 0 1 qz524)

noncomputable def ep1674 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1))) qz259 132339 1000 0 1 3 2 0 1 397017 2000

noncomputable def ep1675 := @ep1674 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 132339 1000 0 1 ep1360)

noncomputable def ep1676 := ep1675 (@Enclosure.Complex.IsNear.re_isNear qz258 Bool.false 3 2 0 1 Bool.false 132339 1000 0 1 qz524)

noncomputable abbrev qz261 := (ep1660 (BSN.ascPochhammer_succ_eval_c 1 2 qz436 rfl) (ep1669 (@ep1670 1058712000 132339 500 0 1 (ep1673 rfl) (ep1676 rfl) rfl rfl)))

noncomputable def ep1677 := @ep1659 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 17512860921 1000000 0 1 Bool.false 132339 500 0 1 qz261)

noncomputable def ep1678 := @Enclosure.Complex.IsNear.of_eq qz255 (Complex.mk qz510 qz146) Bool.false 5 2 0 1 Bool.false 132339 1000 0 1 (BSN.s_add_nat_mk qz146 Bool.false 132339 1000 2 qz147)

noncomputable abbrev qz525 := (ep1678 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 5 2) qz146 Bool.false 5 2 0 1 Bool.false 132339 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 5 2) qz148))

noncomputable def ep1679 := ep1677 (@Enclosure.Complex.IsNear.re_isNear qz255 Bool.false 5 2 0 1 Bool.false 132339 1000 0 1 qz525)

noncomputable def ep1680 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 2))) qz257 132339 500 0 1 132339 1000 0 1 17513610921 500000

noncomputable def ep1681 := @ep1680 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 17512860921 1000000 0 1 Bool.false 132339 500 0 1 qz261)

noncomputable def ep1682 := ep1681 (@Enclosure.Complex.IsNear.im_isNear qz255 Bool.false 5 2 0 1 Bool.false 132339 1000 0 1 qz525)

noncomputable def ep1683 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 2)) qz255 Bool.true 157618748289 2000000 0 1 Bool.true 2316972806424219 1000000000 0 1 (@ep1658 15761874828900000 157618748289 2000000 0 1 (ep1679 rfl) (ep1682 rfl) rfl rfl)

noncomputable def ep1684 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 2))) qz257) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 2))) qz256) 2317634501424219 1000000000 0 1 132339 200 0 1

noncomputable def ep1685 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 2))) qz257 17512860921 1000000 0 1 132339 1000 0 1 2317634501424219 1000000000

noncomputable def ep1686 := @ep1685 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 17512860921 1000000 0 1 Bool.false 132339 500 0 1 qz261)

noncomputable def ep1687 := ep1686 (@Enclosure.Complex.IsNear.im_isNear qz255 Bool.false 5 2 0 1 Bool.false 132339 1000 0 1 qz525)

noncomputable def ep1688 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 2))) qz256 132339 500 0 1 5 2 0 1 132339 200

noncomputable def ep1689 := @ep1688 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 17512860921 1000000 0 1 Bool.false 132339 500 0 1 qz261)

noncomputable def ep1690 := ep1689 (@Enclosure.Complex.IsNear.re_isNear qz255 Bool.false 5 2 0 1 Bool.false 132339 1000 0 1 qz525)

noncomputable abbrev qz262 := (ep1657 (BSN.ascPochhammer_succ_eval_c 2 3 qz436 rfl) (ep1683 (@ep1684 463394561284843800 2316972806424219 1000000000 0 1 (ep1687 rfl) (ep1690 rfl) rfl rfl)))

noncomputable def ep1691 := @ep1656 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1490) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 157618748289 2000000 0 1 Bool.true 2316972806424219 1000000000 0 1 qz262)

noncomputable def ep1692 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 2316972806424219 1000000000 0 1 0 1 0

noncomputable def ep1693 := @ep1692 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1490) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 157618748289 2000000 0 1 Bool.true 2316972806424219 1000000000 0 1 qz262)

noncomputable def ep1694 := @Enclosure.Real.IsNear.addLit_ft_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3)))) 772324268808073 240000000000 0 1 0 1 0 1 772324268808073

noncomputable def ep1695 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 2316972806424219 1000000000 0 1 772324268808073 240000000000 0

noncomputable def ep1696 := @ep1695 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1490) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 157618748289 2000000 0 1 Bool.true 2316972806424219 1000000000 0 1 qz262)

noncomputable def ep1697 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 157618748289 2000000 0 1 0 1 0

noncomputable def ep1698 := @ep1697 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1490) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 157618748289 2000000 0 1 Bool.true 2316972806424219 1000000000 0 1 qz262)

noncomputable def ep1699 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.false 52539582763 480000000 0 1 Bool.false 772324268808073 240000000000 0 1 (@ep1655 52539582763 480000000 0 1 (ep1691 rfl) (ep1693 rfl) rfl rfl) (@ep1694 772324268808073 240000000000 0 1 (ep1696 rfl) (ep1698 rfl) rfl rfl)

noncomputable def ep1700 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 52539582763 480000000 0 1 Bool.false 772324268808073 240000000000 0 1 ep1699

noncomputable def ep1701 := nat_lit 1221221604426495740450555719319552

noncomputable def ep1702 := @Enclosure.Complex.IsNear.re_isNear qz245 Bool.true 390274459203414665 604462909807314587353088 1336836789145978311431 ep1653 Bool.true 20378681840801075 4722366482869645213696 1101221684316604553199 ep1701

noncomputable abbrev qz526 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 52523350144)))

noncomputable def ep1703 := @Enclosure.Complex.IsNear.of_eq qz245 (Complex.mk (@HMul.hMul Real Real Real qz0 qz526 (Real.cos qz217)) (@HMul.hMul Real Real Real qz0 qz526 qz658)) Bool.true 390274459203414665 604462909807314587353088 1336836789145978311431 ep1653 Bool.true 20378681840801075 4722366482869645213696 1101221684316604553199

noncomputable abbrev qz527 := (Real.sqrt (@Nat.cast Real Real.instNatCast 52523350144))

noncomputable abbrev qz528 := (@Nat.cast Real Real.instNatCast 52523350144)

noncomputable def ep1704 := @Enclosure.Real.IsNear.inv_image qz527 251985781586464421 1099511627776 1 1099511627776 2398797 2398798 549755813888 (@Enclosure.Real.IsNear.of_eq qz527 (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz528 qz14)) Bool.false 251985781586464421 1099511627776 1 1099511627776 (BSN.sqrt_natCast_div_one 52523350144) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz528 qz14)) Bool.false 251985781586464421 1099511627776 1 1099511627776 251985781586464421 1099511627776 1 1099511627776 (BSN.sqrt_enclosure 52523350144 1 125992890793232210 125992890793232211 549755813888 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep1705 := nat_lit 3232546671400000000000000000

noncomputable def ep1706 := nat_lit 3232546671400000000000000

noncomputable def ep1707 := nat_lit 69846766182031428999891124224

noncomputable def ep1708 := nat_lit 258603733712000000000000000

noncomputable def ep1709 := BSN.log_dyadic_bound 2 66 4 3 8678664751680 549755813888 258603733712 2657927616 960 33328738308 68 64 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 2) (BSN.artanhQ 66) 0 3 2657927616 8678664751680 960 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep1710 := @Enclosure.Real.IsNear.mulLit_ff qz146 qz657 132339 1000 0 1 15881315944632531 4503599627370496 12516162733357 ep1706 2101717470796724520009 4503599627370496000 1656376459969732023 ep1705 qz148 (BSN.isNear_log_sfrac 34 1 15881315944632531 4503599627370496 12516162733357 ep1706 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz495) Bool.false ep1707 ep1409 1001293018668560 ep1708 15881315944632531 4503599627370496 12516162733357 ep1706 (BSN.log_rat_reduce_isNear 34 1 5 68 64 33328738308 549755813888 24973259072661432 36028797018963968 258603733712 1000000000000000 rfl rfl rfl rfl (ep1709 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1711 := nat_lit 23533364378146355070392860672

noncomputable def ep1712 := nat_lit 12508835313762184541296672880610778953562410208944324342016

noncomputable def ep1713 := nat_lit 3085321044977261329040567217295032196842629748062962243778641920

noncomputable def ep1714 := nat_lit 21597247314840829303283970521065225377898408236440735706450493440

noncomputable def ep1715 := BSN.sin_dyadic_bound_f 334429222137748 2251799813685248 2 1 1099511627776 517712552842 ep1712 ep1713 ep1712 ep1712 ep1714 ep1712 162695875414 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 334429222137748) (BSN.sinEvenQ 2251799813685248) 0 1 ep1712 ep1713 ep1712 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 334429222137748) (BSN.sinOddQ 2251799813685248) 0 1 ep1712 ep1714 ep1712 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz529 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 513114616893731) (@Nat.cast Real Real.instNatCast 1099511627776))

noncomputable def ep1716 := @Enclosure.Real.IsNear.cos_image qz217 qz529 Bool.false 513114616893731 1099511627776 141 274877906944 Bool.true 162695875414 1099511627776 1 258603733712 (@Enclosure.Real.IsNear.recentre' qz217 Bool.false 2101717470796724520009 4503599627370496000 1656376459969732023 ep1705 513114616893731 1099511627776 141 274877906944 (ep1710 rfl) rfl) (Enclosure.sfrac_false_div 513114616893731 1099511627776) (BSN.cos_reduce1 qz529 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep1711) (@Nat.cast Real Real.instNatCast ep1546)) 226375608064910080 72057594037927936 Bool.false 162695875414 1099511627776 74 1000000000000000 517207467424 258603733712 (BSN.sin_reduce_arg_pos_rat_q1 513114616893731 1099511627776 226375608064910080 72057594037927936 74 ep1711 ep1546 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 162695875414 1099511627776 ep1711 ep1546 334429222137748 2251799813685248 517712552842 517207467424 (ep1715 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1717 := nat_lit 540312976254833872026002729700965920045500638798267214456526442620944849123439409197599332272141482567243570909164391694336

noncomputable def ep1718 := nat_lit 26653776661622823509741225219881328325881276817119818761557039425464041502648073463671628964929320285054877668848941806827601920

noncomputable def ep1719 := nat_lit 156470960906823889779969982351778709213276291452905694943352892631337805720179340009102691342613111861579951342944256

noncomputable def ep1720 := nat_lit 1620938615822579802430228629162933056579083489842218737558189441157049284694706787234117978611041762475506989567590489194496

noncomputable def ep1721 := nat_lit 1199419949773027057938355134894659774664657456770391844270066774145881867619163305865223303421819412827469495098202381307242086400

noncomputable def ep1722 := BSN.cos_dyadic_bound_f 334429222137748 2251799813685248 3 2 1099511627776 517712552842 ep1717 ep1718 ep1719 ep1720 ep1721 ep1719 1087407868160 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 334429222137748) (BSN.cosEvenQ 2251799813685248) 0 2 ep1717 ep1718 ep1719 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 334429222137748) (BSN.cosOddQ 2251799813685248) 0 2 ep1720 ep1721 ep1719 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1723 := @Enclosure.Real.IsNear.sin_image qz217 qz529 Bool.false 513114616893731 1099511627776 141 274877906944 Bool.false 1087407868160 1099511627776 1 258603733712 (@Enclosure.Real.IsNear.recentre' qz217 Bool.false 2101717470796724520009 4503599627370496000 1656376459969732023 ep1705 513114616893731 1099511627776 141 274877906944 (ep1710 rfl) rfl) (Enclosure.sfrac_false_div 513114616893731 1099511627776) (BSN.sin_reduce1 qz529 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep1711) (@Nat.cast Real Real.instNatCast ep1546)) 226375608064910080 72057594037927936 Bool.false 1087407868160 1099511627776 74 1000000000000000 517207467424 258603733712 (BSN.sin_reduce_arg_pos_rat_q1 513114616893731 1099511627776 226375608064910080 72057594037927936 74 ep1711 ep1546 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1087407868160 1099511627776 ep1711 ep1546 334429222137748 2251799813685248 517712552842 517207467424 (ep1722 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1724 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz526 (Real.cos qz217)) (@HMul.hMul Real Real Real qz0 qz526 qz658) Bool.true 390274459203414665 604462909807314587353088 1336836789145978311431 ep1653 Bool.true 20378681840801075 4722366482869645213696 1101221684316604553199 ep1701 (@Enclosure.Real.IsNear.mulLit_ft qz526 (Real.cos qz217) 4797595 1099511627776 1 1099511627776 81347937707 549755813888 2296125272521 4442778315666130731008 390274459203414665 604462909807314587353088 1336836789145978311431 ep1653 (@Enclosure.Real.IsNear.recentre' qz526 Bool.false 4797595 1099511627776 1 1099511627776 4797595 1099511627776 1 1099511627776 (ep1704 rfl rfl) rfl) (@Enclosure.Real.IsNear.recentre' (Real.cos qz217) Bool.true 162695875414 1099511627776 36738004360336 71084453050658091696128 81347937707 549755813888 2296125272521 4442778315666130731008 (ep1716 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz526 qz658 4797595 1099511627776 1 1099511627776 4247686985 4294967296 2296125272521 4442778315666130731008 20378681840801075 4722366482869645213696 1101221684316604553199 ep1701 (@Enclosure.Real.IsNear.recentre' qz526 Bool.false 4797595 1099511627776 1 1099511627776 4797595 1099511627776 1 1099511627776 (ep1704 rfl rfl) rfl) (@Enclosure.Real.IsNear.neg qz218 Bool.false 4247686985 4294967296 2296125272521 4442778315666130731008 (@Enclosure.Real.IsNear.recentre' qz218 Bool.false 1087407868160 1099511627776 36738004360336 71084453050658091696128 4247686985 4294967296 2296125272521 4442778315666130731008 (ep1723 rfl rfl) rfl)) rfl)

noncomputable def ep1725 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3)))) qz254 772324268808073 240000000000 0 1 20378681840801075 4722366482869645213696 1101221684316604553199 ep1701 ep1647

noncomputable def ep1726 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 52539582763 480000000 0 1 Bool.false 772324268808073 240000000000 0 1 ep1699

noncomputable def ep1727 := @Enclosure.Complex.IsNear.im_isNear qz245 Bool.true 390274459203414665 604462909807314587353088 1336836789145978311431 ep1653 Bool.true 20378681840801075 4722366482869645213696 1101221684316604553199 ep1701

noncomputable def ep1728 := nat_lit 42827497647024530807274809

noncomputable def ep1729 := nat_lit 90669436471097188102963200000

noncomputable def ep1730 := nat_lit 19285909274520834672647165636279

noncomputable def ep1731 := nat_lit 195395456708239318472088915091128320000000

noncomputable def ep1732 := nat_lit 60283687267748669463694223718109

noncomputable def ep1733 := nat_lit 1032471495692899759235381239560982463

noncomputable def ep1734 := @Enclosure.Real.IsNear.addLit_tt (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3)))) qz254) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3)))) qz253) ep1728 ep1729 ep1730 ep1731 ep1732 ep1638 ep1733

noncomputable def ep1735 := nat_lit 6708494377645974010805503841783441948429156349513616588800000

noncomputable def ep1736 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3)))) qz254 52539582763 480000000 0 1 20378681840801075 4722366482869645213696 1101221684316604553199 ep1701 ep1728

noncomputable def ep1737 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3)))) qz253 772324268808073 240000000000 0 1 390274459203414665 604462909807314587353088 1336836789145978311431 ep1653 ep1732

noncomputable abbrev qz530 := (@ep1703 ep1701 (BSN.cpow_neg_s_sub_mk qz146 132339 1000 34 3 52523350144 qz147 rfl EMRow44.d24) ep1724)

noncomputable def ep1738 := ep1642 (@ep1650 ep1651 ep1652 ep1632 ep1633 ep1634 ep1635 (@ep1654 ep1644 ep1645 ep1646 ep1700 (ep1702 qz530) rfl) (@ep1725 ep1648 ep1649 ep1651 ep1726 (ep1727 qz530) rfl) rfl rfl) (@ep1734 ep1641 ep1735 ep1637 ep1638 ep1639 ep1641 (@ep1736 ep1729 ep1730 ep1731 ep1700 (ep1727 qz530) rfl) (@ep1737 ep1638 ep1733 ep1641 ep1726 (ep1702 qz530) rfl) rfl rfl)

noncomputable def ep1739 := @Enclosure.Real.IsNear.mulLit_tt (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)) (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)) ep1637 ep1638 ep1639 ep1641 ep1637 ep1638 ep1639

noncomputable def ep1740 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz245) Bool.false ep1632 ep1633 ep1634 ep1635 Bool.true ep1637 ep1638 ep1639

noncomputable def ep1741 := @ep1603 268048086322497237 504403158265495552 117066384535 1008806316530991104 (@ep1604 1 3670016 (ep1605 (@ep1606 1048576 1 1048576 (ep1607 (@ep1608 70103443684 17525860921 1000000 0 1 (ep1612 rfl) (ep1615 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) (Enclosure.Real.IsNear.const Bool.false 2 7) rfl) (@ep1616 1631 549755813888 (BSN.norm_eq_sqrt_mul_add (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)) (@ep1617 3262 1099511627776 1930959297 137438953472 1631 549755813888 (@ep1622 7723835557 7723838819 549755813888 (@ep1628 ep1619 ep1629 ep1630 ep1631 ep1618 ep1619 ep1620 ep1621 (@ep1636 ep1635 ep1623 ep1624 ep1625 ep1626 (@ep1640 ep1641 ep1738) (@ep1640 ep1641 ep1738) rfl) (@ep1739 ep1641 ep1627 ep1619 ep1629 ep1630 (@ep1740 ep1641 ep1738) (@ep1740 ep1641 ep1738) rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl

theorem EMRow44.d25 : Enclosure.Real.IsNear (@HAdd.hAdd Real Real Real qz421 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz143 1 34))) (@HMul.hMul Real Real Real qz0 qz244 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)))) Bool.false 851210186960753791 1513209474796486656 885782813174095 9079256848778919936 := ep1601 (ep1602 ep1741) rfl rfl

noncomputable def EMRow44.d26 := fun (I J : @NonemptyInterval Real Real.instLE) => @LE.le Real Real.instLE (@Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE I)) (@Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE J))

noncomputable abbrev qz531 := (EMRow44.d3 qz545 qz628 (@Enclosure.dec_le_dec qz545 qz628 130272 1000 132339 1000 (@Eq.refl Real qz545) (@Eq.refl Real qz628) rfl rfl rfl) 33 34 1 1)

noncomputable abbrev qz263 := qz531

noncomputable def ep1742 := @Zeta.Certificates.ZIntervalEM.Certificate.mk qz263 (@Enclosure.dec_nonneg qz12 130272 1000 qz13) (@Enclosure.pos_of_ble 1 rfl) (@Enclosure.pos_of_ble 33 rfl)

noncomputable abbrev qz264 := (Zeta.Certificates.ZIntervalEM.fstVal qz531)

noncomputable def ep1743 := @Enclosure.Real.IsNear.pos_val qz264 ep523 ep524

noncomputable def ep1744 := @Enclosure.Real.IsNear.of_eq qz264 (hardyZApproximantEM 1 33 qz12) Bool.false

noncomputable abbrev qz265 := (Zeta.Certificates.ZIntervalEM.sndVal qz531)

noncomputable def ep1745 := BSN.mul_neg_of_pos_neg_r qz264 qz265 (@ep1743 ep525 ep526 (@ep1744 ep523 ep524 ep525 ep526 (@Eq.refl Real (hardyZApproximantEM 1 33 qz12)) EMRow44.d12) rfl rfl rfl)

noncomputable def ep1746 := @Enclosure.Real.IsNear.neg_val qz265 ep1168 ep1169

noncomputable def ep1747 := @Enclosure.Real.IsNear.of_eq qz265 (hardyZApproximantEM 1 34 qz146) Bool.true

noncomputable def ep1748 := BSN.gt_trans_le (@Norm.norm Real Real.norm qz264) (BSN.hardyZErrorBoundStrong 1 33 qz12)

noncomputable def ep1749 := @Enclosure.norm_gt_of_isNear qz264 (BSN.hardyZErrorBoundStrong 1 33 qz12) Bool.false

noncomputable def ep1750 := @Enclosure.Real.IsNear.of_eq (BSN.hardyZErrorBoundStrong 1 33 qz12) (@HAdd.hAdd Real Real Real qz421 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 33))) (@HMul.hMul Real Real Real qz0 qz222 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)))) Bool.false 7748422293051662995 13618885273168379904 2610985084664713 27237770546336759808 (@Eq.refl Real (@HAdd.hAdd Real Real Real qz421 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 33))) (@HMul.hMul Real Real Real qz0 qz222 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)))))

noncomputable def ep1751 := BSN.gt_trans_le (@Norm.norm Real Real.norm qz265) (BSN.hardyZErrorBoundStrong 1 34 qz146)

noncomputable def ep1752 := @Enclosure.norm_gt_of_isNear qz265 (BSN.hardyZErrorBoundStrong 1 34 qz146) Bool.true

noncomputable def ep1753 := @Enclosure.Real.IsNear.of_eq (BSN.hardyZErrorBoundStrong 1 34 qz146) (@HAdd.hAdd Real Real Real qz421 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz143 1 34))) (@HMul.hMul Real Real Real qz0 qz244 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)))) Bool.false 851210186960753791 1513209474796486656 885782813174095 9079256848778919936 (@Eq.refl Real (@HAdd.hAdd Real Real Real qz421 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz143 1 34))) (@HMul.hMul Real Real Real qz0 qz244 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)))))

noncomputable def ep1754 := @List.cons EMRow44.d0 (@PSigma.mk Zeta.Certificates.ZIntervalEM Zeta.Certificates.ZIntervalEM.Certificate qz263 (ep1742 (@Enclosure.pos_of_ble 1 rfl) (@Enclosure.pos_of_ble 34 rfl) (ep1745 (@ep1746 ep1170 ep1171 (@ep1747 ep1168 ep1169 ep1170 ep1171 (@Eq.refl Real (hardyZApproximantEM 1 34 qz146)) EMRow44.d18) rfl rfl rfl)) (ep1748 (hardyZErrorBoundEM 1 33 qz12) (BSN.hardyZErrorBoundEM_le_strong 1 33 qz12 rfl) (@ep1749 Bool.false ep523 ep524 ep525 ep526 7748422293051662995 13618885273168379904 2610985084664713 27237770546336759808 (@ep1744 ep523 ep524 ep525 ep526 (@Eq.refl Real (hardyZApproximantEM 1 33 qz12)) EMRow44.d12) (ep1750 EMRow44.d23) rfl rfl rfl rfl rfl)) (ep1751 (hardyZErrorBoundEM 1 34 qz146) (BSN.hardyZErrorBoundEM_le_strong 1 34 qz146 rfl) (@ep1752 Bool.false ep1168 ep1169 ep1170 ep1171 851210186960753791 1513209474796486656 885782813174095 9079256848778919936 (@ep1747 ep1168 ep1169 ep1170 ep1171 (@Eq.refl Real (hardyZApproximantEM 1 34 qz146)) EMRow44.d18) (ep1753 EMRow44.d25) rfl rfl rfl rfl rfl)))) (@List.nil EMRow44.d0)

noncomputable abbrev qz532 := (@Enclosure.dec_le_dec qz545 qz628 130272 1000 132339 1000 (@Eq.refl Real qz545) (@Eq.refl Real qz628) rfl rfl rfl)

noncomputable abbrev qz266 := (Zeta.Certificates.CertifiedZeroIntervals.intervals (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedEM ep1754 (@List.IsChain.singleton EMRow44.d1 EMRow44.d26 (EMRow44.d2 qz279 qz438 qz532))))

noncomputable abbrev qz533 := (@NonemptyInterval Real Real.instLE)

noncomputable def ep1755 := And (@Eq (Option Real) (@Option.map qz533 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz533 qz266)) (@Option.some Real qz12))

noncomputable def ep1756 := ep1755 (@Eq (Option Real) (@Option.map qz533 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz533 qz266)) (@Option.some Real qz146))

noncomputable def ep1757 := @And.intro (@Eq Nat (@List.length qz533 qz266) 1) ep1756

noncomputable def ep1758 := @And.intro (@Eq (Option Real) (@Option.map qz533 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz533 qz266)) (@Option.some Real qz12))

noncomputable def ep1759 := @ep1758 (@Eq (Option Real) (@Option.map qz533 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz533 qz266)) (@Option.some Real qz146))

noncomputable abbrev qz267 := (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedEM ep1754 (@List.IsChain.singleton EMRow44.d1 EMRow44.d26 (EMRow44.d2 qz279 qz438 qz532)))

theorem EMRow44.d27 : Zeta.Certificates.BatchSpec 1 130272 1000 132339 1000 := @Exists.intro Zeta.Certificates.CertifiedZeroIntervals (fun (C : Zeta.Certificates.CertifiedZeroIntervals) => And (@Eq Nat (@List.length qz533 (Zeta.Certificates.CertifiedZeroIntervals.intervals C)) 1) (And (@Eq (Option Real) (@Option.map qz533 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz533 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz12)) (@Eq (Option Real) (@Option.map qz533 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz533 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz146)))) qz267 (ep1757 (@Eq.refl Nat 1) (ep1759 (@Eq.refl (Option Real) (@Option.some Real qz12)) (@Eq.refl (Option Real) (@Option.some Real qz146))))

theorem solution : Zeta.Certificates.BatchSpec 1 130272 1000 132339 1000 := EMRow44.d27
#print axioms solution
#check solution
