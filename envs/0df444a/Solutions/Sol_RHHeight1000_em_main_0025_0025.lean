-- Prove2me | solution 1 for RHHeight1000.em_main_0025_0025
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-20T08:25:56.549981+00:00
-- url     : https://prove2.me/submissions/3b46b251-f58b-441a-b502-4609f2606904

import Definitions.Def_RHT1000_Support_20261118_S005
/- Copyright (c) 2026 Salvatore Mercuri, Bhavik Mehta.
Apache 2.0 license; see the source project LICENSE. -/
set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable def EMRow25.d0 := @PSigma Zeta.Certificates.ZIntervalEM fun (I : Zeta.Certificates.ZIntervalEM) => Zeta.Certificates.ZIntervalEM.Certificate I

noncomputable def EMRow25.d1 := @NonemptyInterval Real Real.instLE

noncomputable def EMRow25.d2 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @NonemptyInterval.mk Real Real.instLE (@Prod.mk Real Real a b) h

noncomputable def EMRow25.d3 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) (fc sc fb sb : Nat) => Zeta.Certificates.ZIntervalEM.mk (EMRow25.d2 a b h) fc sc fb sb

noncomputable def ep0 := nat_lit 26986075409044028275299783

noncomputable def ep1 := nat_lit 4294967296000000000000000

noncomputable def ep2 := nat_lit 26986075409044045455168967

noncomputable abbrev qz267 := (@instHMul Real Real.instMul)

noncomputable abbrev qz0 := qz267

noncomputable abbrev qz268 := (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 2 1) Real.pi)

noncomputable def ep3 := @BSN.isNear_log_image_fff qz268 884279719003555 140737488355328 1 500000000000000 ep0 ep1 ep2 ep1 4138529546116343 2251799813685248 125000000042283 21141500000000000000 4138529546116343 2251799813685248 125000000042283 21141500000000000000 481788 262144

noncomputable abbrev qz269 := (@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 2 1) Real.pi 2 1 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 140737488355328 1 500000000000000 (Enclosure.Real.IsNear.const Bool.false 2 1) BSN.pi_near_15 rfl)

noncomputable def ep4 := @ep3 2 262144 qz269 rfl rfl rfl rfl

noncomputable def ep5 := nat_lit 53972150818088056550599566

noncomputable def ep6 := nat_lit 34359738368000000000000000

noncomputable def ep7 := nat_lit 9806206225044028275299783

noncomputable def ep8 := nat_lit 44165944593044028275299783

noncomputable def ep9 := nat_lit 13681445815609410487519367394620474863599256634174726093703677122907123617368241606644861540940610176751640793056574796245399519365549113997355475306157239709119582688278313060810592403844863400465080549957745

noncomputable def ep10 := nat_lit 231714499556395493334623298703961145503103241611736774613091488581016477543539392410113701224645713379230392133956226737605624599560350113120270717249177907454870984269546186598262646369758174842349131395304

noncomputable def ep11 := nat_lit 8978369550011295664474073352761810093897501552430546263638635096022803738134167562509900960712119243631997923545019968443113540909076206607473711060286601587364321108377403290080403445693385008949995305

noncomputable def ep12 := BSN.log_dyadic_bound ep7 ep8 5 4 ep9 524288 169132 ep10 ep11 236759 ep5 ep6 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP ep7) (BSN.artanhQ ep8) 0 4 ep10 ep9 ep11 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz270 := (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))

noncomputable abbrev qz1 := qz270

noncomputable def ep13 := ep4 rfl rfl rfl rfl (BSN.isNear_log_sfrac ep0 ep1 4138529546116343 2251799813685248 125000000042283 21141500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep0) (@Nat.cast Real Real.instNatCast ep1))) Bool.false 34716502058787923820544 18889465931478580854784 1000000000338264 169132000000000000000 4138529546116343 2251799813685248 125000000042283 21141500000000000000 (BSN.log_rat_reduce_isNear ep0 ep1 2 ep5 ep6 236759 524288 24973259072661432 36028797018963968 169132 1000000000000000 rfl rfl rfl rfl (ep12 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep14 := nat_lit 53972150818088090910337934

noncomputable def ep15 := nat_lit 9806206225044045455168967

noncomputable def ep16 := nat_lit 44165944593044045455168967

noncomputable def ep17 := nat_lit 13681445815609453062485491347592146866046743284321690683909457683007658987562290830600045658905080811372395010565947827677605470036294121079488508864180301737865471494204890974265645509835068840465080549957745

noncomputable def ep18 := nat_lit 231714499556396865510889920206523150079811393376960301632499817942333196803513131357563499488546302200815366867712007119763002650772307103678175657719139104636874731038771518520299266622696414842349131395304

noncomputable def ep19 := nat_lit 8978369550011421500876706511871067098718760264493934208903156435737864998391937547068187824077011975074541700434630537294838404525415248443919841847024664017658842168336182958576672102333385008949995305

noncomputable def ep20 := BSN.log_dyadic_bound ep15 ep16 5 4 ep17 524288 169132 ep18 ep19 236759 ep14 ep6 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP ep15) (BSN.artanhQ ep16) 0 4 ep18 ep17 ep19 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep21 := ep13 (BSN.isNear_log_sfrac ep2 ep1 4138529546116343 2251799813685248 125000000042283 21141500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep2) (@Nat.cast Real Real.instNatCast ep1))) Bool.false 34716502058787923820544 18889465931478580854784 1000000000338264 169132000000000000000 4138529546116343 2251799813685248 125000000042283 21141500000000000000 (BSN.log_rat_reduce_isNear ep2 ep1 2 ep14 ep6 236759 524288 24973259072661432 36028797018963968 169132 1000000000000000 rfl rfl rfl rfl (ep20 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable abbrev qz271 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)

noncomputable abbrev qz2 := (Real.log qz271)

theorem EMRow25.d4 : Enclosure.Real.IsNear qz2 Bool.false 120447 65536 1 131072 := @Enclosure.Real.IsNear.of_eq qz2 (Real.log qz268) Bool.false 120447 65536 1 131072 BSN.log_two_pi_eq (@Enclosure.Real.IsNear.recentre' (Real.log qz268) Bool.false 481788 262144 2 262144 120447 65536 1 131072 (ep21 rfl rfl rfl rfl rfl rfl rfl rfl) rfl)

noncomputable def ep22 := nat_lit 8589934592000000000000000

noncomputable def ep23 := @BSN.isNear_log_image_fff Real.pi 226375608064910080 72057594037927936 1 1000000000000000 ep0 ep22 ep2 ep22 600168 524288 1 169132 600168 524288 1 169132 300084 262144 2 262144 BSN.pi_near_15 rfl rfl rfl

noncomputable def ep24 := nat_lit 17179869184000000000000000

noncomputable def ep25 := nat_lit 18396140817044028275299783

noncomputable def ep26 := nat_lit 35576010001044028275299783

noncomputable def ep27 := nat_lit 145019262663961446558303139663424756232419223153299357158415217874016130572233056993847515999529612750616182853355499335896178729185698845314776375864537073527142908641610750276034469165612529925303649396973267518946591078603565291376312767403717761600170009932259137778521478520425507632472584532570900560707662248426541531715360699177249902784721815296292248142738824858695953661559845440650653128788875447728828657762006237171740033404723254477174341920697506370253193455781322964835857351124092897592956162654178130575

noncomputable def ep28 := nat_lit 15500762873619990602332184736899274490522931101512051618692838888825382235673431503644115344741331161500627469184702974962114537943617674254904297224139410345221262767191485292268260077615645253784097850065864022184521411511133693085443040736512010941548648374196772723338837137976260321103066698629790037694560548409922339907589559883712609967105556007429010014773911317423638534096849366294542840133852248768895750397896505791271178551667935288585787166713880920071720072716082683081155281219708172458141800988558163320

noncomputable def ep29 := nat_lit 12900190794487083783367107939442176642390171280542213571554777169279725287102813254708993369099729304728646904879886535518616983985412662170766446331701281703998252143668221340329975389245922410714088123244705567402747658401492589451585970559635763980329972215329212888079422466283203384882259392047898400615815810081169907384366653346471604103896809335921621947903075223769953790093549808584241881353287841076643853121427928248525828402335494512605306631304432120211393210317325496757155861061354331245840675149075

noncomputable def ep30 := BSN.log_dyadic_bound ep25 ep26 11 10 ep27 524288 169132 ep28 ep29 600168 ep5 ep24 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base10 (BSN.artanhP ep25) (BSN.artanhQ ep26) 0 10 ep28 ep27 ep29 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep31 := nat_lit 18396140817044045455168967

noncomputable def ep32 := nat_lit 35576010001044045455168967

noncomputable def ep33 := nat_lit 145019262663962847171784895425483977818796535899227200426399035286881207006285364467913811844950531107314785650583974625982406238691319033447632878979985852280879486690814033867010958364699188952871572448188560932645032521756218245629809291975913196623825614492380080480004685076434733043183791438169545293975334857826316990371107134320667652578346815517853870648072772035977941843998949310557583393428557296298890786965786350523173236912472938174255438182435383147950274229549088258679583524155427309880956162654178130575

noncomputable def ep34 := nat_lit 15500762873620157189619721156942591192100275120160672416764593300158228469749443299607348495591439275767946573253526107895503597951484257520435868240203420954375895980141891044871083424251900562230440202302413072793440172565998181227591194192658878334739610458454844032013325963992941389843551995646587189684848765634635122388286241104146031552341815777883628509454807838726994150833304950745987647656768534710890974432620160470644835720379148964170536679305861738540146791997074363921127776563807649880221800988558163320

noncomputable def ep35 := nat_lit 12900190794487324729109480814509220959173684627296055849229843377126536688487849343376525559792931631054411655715865486295286288812423905434305314401904993536755333953308594664509631000767632482919425633906965368325056855874260596615770736441041599390097968820060635361729170158825410327022636428624381203910573184452046894301676992229743752846881064485858738985580654099214803581683226335297196686880535448467637789069028262446657986458573827723305156755787640135484017403116612632808333639900906331245840675149075

noncomputable def ep36 := BSN.log_dyadic_bound ep31 ep32 11 10 ep33 524288 169132 ep34 ep35 600168 ep14 ep24 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base10 (BSN.artanhP ep31) (BSN.artanhQ ep32) 0 10 ep34 ep33 ep35 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep37 := @Enclosure.Real.IsNear.recentre' (Real.log Real.pi) Bool.false 300084 262144 2 262144 75021 65536 1 131072 (ep23 rfl rfl rfl rfl rfl (BSN.isNear_log_sfrac ep0 ep22 600168 524288 1 169132 Bool.false (BSN.logfrac_isNear ep5 ep24 1 ep0 ep22 600168 524288 169132 rfl rfl rfl (ep30 rfl))) (BSN.isNear_log_sfrac ep2 ep22 600168 524288 1 169132 Bool.false (BSN.logfrac_isNear ep14 ep24 1 ep2 ep22 600168 524288 169132 rfl rfl rfl (ep36 rfl))) rfl rfl rfl rfl rfl rfl rfl rfl) rfl

theorem EMRow25.d5 : Enclosure.Real.IsNear (Real.log Real.pi) Bool.false 75021 65536 1 131072 := ep37

noncomputable abbrev qz571 := (@HAdd.hAdd Complex Complex Complex (@instHAdd Complex Complex.instAdd) (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (2 : Complex)) (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul) Complex.I ↑(Enclosure.sfrac Bool.false 88388 1000)))

noncomputable abbrev qz524 := qz571

noncomputable abbrev qz272 := qz524

noncomputable abbrev qz3 := (BSN.headSumC qz272 9)

noncomputable abbrev qz572 := (@instHAdd Complex Complex.instAdd)

noncomputable abbrev qz525 := qz572

noncomputable abbrev qz273 := qz525

noncomputable abbrev qz4 := qz273

noncomputable abbrev qz5 := qz272

noncomputable abbrev qz526 := (@instHPow Complex Complex Complex.instPow)

noncomputable abbrev qz274 := qz526

noncomputable abbrev qz6 := qz274

noncomputable abbrev qz527 := (@Neg.neg Complex Complex.instNeg qz571)

noncomputable abbrev qz275 := qz527

noncomputable abbrev qz7 := qz275

noncomputable abbrev qz276 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 8) qz7)

noncomputable def ep38 := @Enclosure.Complex.IsNear.of_eq qz3 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 8) qz276) Bool.true 135207735647 274877906944 41596601721773 11622662539313152 Bool.true 33045197875 274877906944 41629014431951 11622662539313152

noncomputable def ep39 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 8) qz276 Bool.true 8362378127 17179869184 18622382769277 5811331269656576 Bool.false 64128018341 274877906944 37255333709291 11622662539313152 Bool.true

noncomputable abbrev qz277 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 7) qz7)

noncomputable def ep40 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 8) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 7) qz277) Bool.true 8362378127 17179869184 18622382769277 5811331269656576 Bool.false 64128018341 274877906944 37255333709291 11622662539313152

noncomputable def ep41 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 7) qz277 Bool.true 15219903649 68719476736 16288602708337 5811331269656576 Bool.false 34533542621 68719476736 4073442687003 1452832817414144 Bool.true

noncomputable abbrev qz278 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 6) qz7)

noncomputable def ep42 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 7) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 6) qz278) Bool.true 15219903649 68719476736 16288602708337 5811331269656576 Bool.false 34533542621 68719476736 4073442687003 1452832817414144

noncomputable def ep43 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 6) qz278 Bool.true 91942880627 274877906944 27546370552727 11622662539313152 Bool.false 61491754671 68719476736 3442692618273 1452832817414144 Bool.false

noncomputable abbrev qz279 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 5) qz7)

noncomputable def ep44 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 6) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 5) qz279) Bool.true 91942880627 274877906944 27546370552727 11622662539313152 Bool.false 61491754671 68719476736 3442692618273 1452832817414144

noncomputable def ep45 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 5) qz279 Bool.true 3479599257 68719476736 5506999233091 2905665634828288 Bool.false 75486889543 137438953472 5505026815707 2905665634828288 Bool.true

noncomputable abbrev qz280 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 4) qz7)

noncomputable def ep46 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 5) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 4) qz280) Bool.true 3479599257 68719476736 5506999233091 2905665634828288 Bool.false 75486889543 137438953472 5505026815707 2905665634828288

noncomputable def ep47 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 4) qz280 Bool.false 30878435181 68719476736 3962966280517 2905665634828288 Bool.false 18709914619 34359738368 7932967056895 5811331269656576 Bool.true

noncomputable abbrev qz528 := (@Nat.cast Complex Complex.instNatCast 3)

noncomputable abbrev qz281 := qz528

noncomputable abbrev qz8 := qz281

noncomputable def ep48 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 4) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 3) (@HPow.hPow Complex Complex Complex qz6 qz8 qz7)) Bool.false 30878435181 68719476736 3962966280517 2905665634828288 Bool.false 18709914619 34359738368 7932967056895 5811331269656576

noncomputable def ep49 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 3) (@HPow.hPow Complex Complex Complex qz6 qz8 qz7) Bool.false 34474154297 34359738368 2175821246621 2905665634828288 Bool.false 12147876081 17179869184 4373706312321 5811331269656576 Bool.true

noncomputable abbrev qz529 := (@Nat.cast Complex Complex.instNatCast 2)

noncomputable abbrev qz282 := qz529

noncomputable abbrev qz9 := qz282

noncomputable def ep50 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 3) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 2) (@HPow.hPow Complex Complex Complex qz6 qz9 qz7)) Bool.false 34474154297 34359738368 2175821246621 2905665634828288 Bool.false 12147876081 17179869184 4373706312321 5811331269656576

noncomputable def ep51 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 2) (@HPow.hPow Complex Complex Complex qz6 qz9 qz7) Bool.false 1 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable abbrev qz283 := (Enclosure.sfrac Bool.false 0 1)

noncomputable abbrev qz10 := qz283

noncomputable def ep52 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 2) (Complex.mk (Enclosure.sfrac Bool.false 1 1) qz10) Bool.false 1 1 0 1 Bool.false 0 1 0 1 (BSN.head_sum_c_two qz5)

noncomputable abbrev qz530 := (@Nat.cast Real Real.instNatCast 2)

noncomputable abbrev qz11 := (@Inv.inv Real Real.instInv (Real.sqrt qz530))

noncomputable abbrev qz573 := (Enclosure.sfrac Bool.false 88388 1000)

noncomputable abbrev qz531 := qz573

noncomputable abbrev qz284 := qz531

noncomputable abbrev qz285 := (Enclosure.sfrac Bool.false 2 1)

noncomputable abbrev qz12 := (@HMul.hMul Real Real Real qz267 qz284 (Real.log qz285))

noncomputable abbrev qz13 := qz284

noncomputable abbrev qz286 := (@Eq.refl Real qz531)

noncomputable abbrev qz14 := qz286

noncomputable def ep53 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz9 qz7) (Complex.mk (@HMul.hMul Real Real Real qz0 qz11 (Real.cos qz12)) (@HMul.hMul Real Real Real qz0 qz11 (@Neg.neg Real Real.instNeg (Real.sin qz12)))) Bool.false 114415929 34359738368 2175821246621 2905665634828288 Bool.false 12147876081 17179869184 4373706312321 5811331269656576 (BSN.cpow_neg_s_mk qz13 88388 1000 2 qz14 rfl)

noncomputable abbrev qz15 := (@Nat.cast Real Real.instNatCast 1)

noncomputable def ep54 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz530) 741455 524288 1 524288 185363 185365 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz530) (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz530 qz15)) Bool.false 741455 524288 1 524288 (BSN.sqrt_natCast_div_one 2) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz530 qz15)) Bool.false 741455 524288 1 524288 741455 524288 1 524288 (BSN.sqrt_enclosure 2 1 370727 370728 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep55 := BSN.log_dyadic_bound 1 3 6 5 613814355 262144 84566 24381081 945 181704 4 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 1) (BSN.artanhQ 3) 0 5 24381081 613814355 945 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz287 := (BSN.sinEvenQ 1073741824)

noncomputable abbrev qz288 := (BSN.sinOddQ 1073741824)

noncomputable def ep56 := BSN.sin_dyadic_bound_f 5056678 1073741824 1 0 524288 169298 0 1 1 0 1 1 2469 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 5056678) qz287 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 5056678) qz288 0 0 rfl) rfl rfl

noncomputable abbrev qz16 := (@Nat.cast Real Real.instNatCast 262144)

noncomputable abbrev qz17 := (Real.log qz285)

noncomputable abbrev qz18 := (Enclosure.Real.IsNear.const Bool.false 88388 1000)

noncomputable abbrev qz19 := (@Nat.cast Real Real.instNatCast 37778931862957161709568)

noncomputable abbrev qz289 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 16060453) qz16)

noncomputable abbrev qz290 := (BSN.isNear_log_sfrac 2 1 181704 262144 1 84566 Bool.false (BSN.logfrac_isNear 4 2 1 2 1 181704 262144 84566 rfl rfl rfl (ep55 rfl)))

noncomputable abbrev qz291 := (@Nat.cast Real Real.instNatCast 177916056299934580736)

noncomputable def ep57 := @Enclosure.Real.IsNear.cos_image qz12 qz289 Bool.false 16060453 262144 549 524288 Bool.false 2469 524288 1 84566 (@Enclosure.Real.IsNear.recentre' qz12 Bool.false 501889161 8192000 22097 21141500 16060453 262144 549 524288 (@Enclosure.Real.IsNear.mulLit_ff qz13 qz17 88388 1000 0 1 181704 262144 1 84566 501889161 8192000 22097 21141500 qz18 qz290 rfl) rfl) (Enclosure.sfrac_false_div 16060453 262144) (BSN.cos_reduce3 qz289 (@HDiv.hDiv Real Real Real qz1 qz291 qz19) 226375608064910080 72057594037927936 Bool.false 2469 524288 9 1000000000000000 169132 84566 (BSN.sin_reduce_arg_pos_rat_q3 16060453 262144 226375608064910080 72057594037927936 9 177916056299934580736 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 2469 524288 177916056299934580736 37778931862957161709568 5056678 1073741824 169298 169132 (ep56 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz292 := (BSN.cosEvenQ 1073741824)

noncomputable abbrev qz293 := (BSN.cosOddQ 1073741824)

noncomputable def ep58 := BSN.cos_dyadic_bound_f 5056678 1073741824 1 0 524288 169298 0 1 1 0 1 1 524282 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 5056678) qz292 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 5056678) qz293 0 0 rfl) rfl rfl

noncomputable def ep59 := @Enclosure.Real.IsNear.sin_image qz12 qz289 Bool.false 16060453 262144 549 524288 Bool.true 524282 524288 1 84566 (@Enclosure.Real.IsNear.recentre' qz12 Bool.false 501889161 8192000 22097 21141500 16060453 262144 549 524288 (@Enclosure.Real.IsNear.mulLit_ff qz13 qz17 88388 1000 0 1 181704 262144 1 84566 501889161 8192000 22097 21141500 qz18 qz290 rfl) rfl) (Enclosure.sfrac_false_div 16060453 262144) (BSN.sin_reduce3 qz289 (@HDiv.hDiv Real Real Real qz1 qz291 qz19) 226375608064910080 72057594037927936 Bool.false 524282 524288 9 1000000000000000 169132 84566 (BSN.sin_reduce_arg_pos_rat_q3 16060453 262144 226375608064910080 72057594037927936 9 177916056299934580736 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 524282 524288 177916056299934580736 37778931862957161709568 5056678 1073741824 169298 169132 (ep58 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz294 := (@Enclosure.Real.IsNear.recentre' qz11 Bool.false 370728 524288 2 524288 46341 65536 1 262144 (ep54 rfl rfl) rfl)

noncomputable def ep60 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz11 (Real.cos qz12)) (@HMul.hMul Real Real Real qz0 qz11 (@Neg.neg Real Real.instNeg (Real.sin qz12))) Bool.false 114415929 34359738368 2175821246621 2905665634828288 Bool.false 12147876081 17179869184 4373706312321 5811331269656576 (@Enclosure.Real.IsNear.mulLit_ff qz11 (Real.cos qz12) 46341 65536 1 262144 2469 524288 23475511 22168469504 114415929 34359738368 2175821246621 2905665634828288 qz294 (@Enclosure.Real.IsNear.recentre' (Real.cos qz12) Bool.false 2469 524288 46951022 44336939008 2469 524288 23475511 22168469504 (ep57 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz11 (@Neg.neg Real Real.instNeg (Real.sin qz12)) 46341 65536 1 262144 262141 262144 23475511 22168469504 12147876081 17179869184 4373706312321 5811331269656576 qz294 (@Enclosure.Real.IsNear.neg (Real.sin qz12) Bool.true 262141 262144 23475511 22168469504 (@Enclosure.Real.IsNear.recentre' (Real.sin qz12) Bool.true 524282 524288 46951022 44336939008 262141 262144 23475511 22168469504 (ep59 rfl rfl) rfl)) rfl)

noncomputable abbrev qz295 := (Enclosure.Real.IsNear.const Bool.false 0 1)

noncomputable abbrev qz20 := qz295

noncomputable def ep61 := @ep51 114415929 34359738368 2175821246621 2905665634828288 Bool.false 12147876081 17179869184 4373706312321 5811331269656576 Bool.false 34474154297 34474154297 34359738368 2175821246621 2905665634828288 Bool.false 12147876081 12147876081 17179869184 4373706312321 5811331269656576 (ep52 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 1) qz10 Bool.false 1 1 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 1) qz20)) (ep53 ep60) rfl rfl

noncomputable abbrev qz296 := (@Nat.cast Real Real.instNatCast 3)

noncomputable abbrev qz21 := (@Inv.inv Real Real.instInv (Real.sqrt qz296))

noncomputable abbrev qz22 := (@HMul.hMul Real Real Real qz267 qz284 (Real.log (Enclosure.sfrac Bool.false 3 1)))

noncomputable def ep62 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz8 qz7) (Complex.mk (@HMul.hMul Real Real Real qz0 qz21 (Real.cos qz22)) (@HMul.hMul Real Real Real qz0 qz21 (@Neg.neg Real Real.instNeg (Real.sin qz22)))) Bool.true 38069873413 68719476736 223393129237 363208204353536 Bool.true 5585837543 34359738368 1779630372287 2905665634828288 (BSN.cpow_neg_s_mk qz13 88388 1000 3 qz14 rfl)

noncomputable def ep63 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz296) 908093 524288 1 524288 151348 151350 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz296) (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz296 qz15)) Bool.false 908093 524288 1 524288 (BSN.sqrt_natCast_div_one 3) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz296 qz15)) Bool.false 908093 524288 1 524288 908093 524288 1 524288 (BSN.sqrt_enclosure 3 1 454046 454047 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep64 := BSN.log_dyadic_bound 1 2 10 9 171633298636800 262144 84566 16925142283965 34459425 287994 3 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base9 (BSN.artanhP 1) (BSN.artanhQ 2) 0 9 16925142283965 171633298636800 34459425 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep65 := nat_lit 14597153965355395647192303672205856230821016833667869026517940103640884829825

noncomputable def ep66 := nat_lit 641153462866780105519186997069590271023477356498224607523168458325065864314880

noncomputable def ep67 := nat_lit 13164069802710565108988460388455317071099663414261495991242790185550864001

noncomputable def ep68 := nat_lit 38209328081964504827708147348481648186416120823602281218799259563520949345921

noncomputable def ep69 := nat_lit 11754480152557635267851761612942488302097084869134117804591421735959540845772800

noncomputable def ep70 := BSN.sin_dyadic_bound_f 1380141999 1073741824 3 2 524288 169298 ep65 ep66 ep67 ep68 ep69 ep67 503074 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1380141999) qz287 0 2 ep65 ep66 ep67 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1380141999) qz288 0 2 ep68 ep69 ep67 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz23 := (@Nat.cast Real Real.instNatCast 524288)

noncomputable abbrev qz24 := (Real.log (Enclosure.sfrac Bool.false 3 1))

noncomputable abbrev qz25 := (@Nat.cast Real Real.instNatCast 75557863725914323419136)

noncomputable abbrev qz297 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 50910427) qz23)

noncomputable abbrev qz298 := (BSN.isNear_log_sfrac 3 1 287994 262144 1 84566 Bool.false (BSN.logfrac_isNear 3 1 2 3 1 287994 262144 84566 rfl rfl rfl (ep64 rfl)))

noncomputable def ep71 := @Enclosure.Real.IsNear.cos_image qz22 qz297 Bool.false 50910427 524288 549 524288 Bool.true 503074 524288 1 84566 (@Enclosure.Real.IsNear.recentre' qz22 Bool.false 3181901709 32768000 22097 21141500 50910427 524288 549 524288 (@Enclosure.Real.IsNear.mulLit_ff qz13 qz24 88388 1000 0 1 287994 262144 1 84566 3181901709 32768000 22097 21141500 qz18 qz298 rfl) rfl) (Enclosure.sfrac_false_div 50910427 524288) (BSN.cos_reduce1 qz297 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 97118859257860696571904) qz25) 226375608064910080 72057594037927936 Bool.false 503074 524288 15 1000000000000000 169132 84566 (BSN.sin_reduce_arg_pos_rat_q1 50910427 524288 226375608064910080 72057594037927936 15 97118859257860696571904 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 503074 524288 97118859257860696571904 75557863725914323419136 1380141999 1073741824 169298 169132 (ep70 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep72 := nat_lit 8115380678443091166266385800287011380265498091332932346283852408771847511681

noncomputable def ep73 := nat_lit 71239273651864456168798555229954474558164150722024956391463162036118429368320

noncomputable def ep74 := nat_lit 24319813895723852368581180480084123506654294947170274046869071645944440807041

noncomputable def ep75 := nat_lit 3205767314333900527595934985347951355117386782491123037615842291625329321574400

noncomputable def ep76 := BSN.cos_dyadic_bound_f 1380141999 1073741824 3 2 524288 169298 ep72 ep73 ep67 ep74 ep75 ep67 147628 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1380141999) qz292 0 2 ep72 ep73 ep67 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1380141999) qz293 0 2 ep74 ep75 ep67 rfl rfl rfl rfl) rfl rfl

noncomputable def ep77 := @Enclosure.Real.IsNear.sin_image qz22 qz297 Bool.false 50910427 524288 549 524288 Bool.false 147628 524288 1 84566 (@Enclosure.Real.IsNear.recentre' qz22 Bool.false 3181901709 32768000 22097 21141500 50910427 524288 549 524288 (@Enclosure.Real.IsNear.mulLit_ff qz13 qz24 88388 1000 0 1 287994 262144 1 84566 3181901709 32768000 22097 21141500 qz18 qz298 rfl) rfl) (Enclosure.sfrac_false_div 50910427 524288) (BSN.sin_reduce1 qz297 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 97118859257860696571904) qz25) 226375608064910080 72057594037927936 Bool.false 147628 524288 15 1000000000000000 169132 84566 (BSN.sin_reduce_arg_pos_rat_q1 50910427 524288 226375608064910080 72057594037927936 15 97118859257860696571904 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 147628 524288 97118859257860696571904 75557863725914323419136 1380141999 1073741824 169298 169132 (ep76 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz299 := (@Enclosure.Real.IsNear.recentre' qz21 Bool.false 302698 524288 2 524288 151349 262144 1 262144 (ep63 rfl rfl) rfl)

noncomputable def ep78 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz21 (Real.cos qz22)) (@HMul.hMul Real Real Real qz0 qz21 (@Neg.neg Real Real.instNeg (Real.sin qz22))) Bool.true 38069873413 68719476736 223393129237 363208204353536 Bool.true 5585837543 34359738368 1779630372287 2905665634828288 (@Enclosure.Real.IsNear.mulLit_ft qz21 (Real.cos qz22) 151349 262144 1 262144 251537 262144 23475511 22168469504 38069873413 68719476736 223393129237 363208204353536 qz299 (@Enclosure.Real.IsNear.recentre' (Real.cos qz22) Bool.true 503074 524288 46951022 44336939008 251537 262144 23475511 22168469504 (ep71 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz21 (@Neg.neg Real Real.instNeg (Real.sin qz22)) 151349 262144 1 262144 36907 131072 23475511 22168469504 5585837543 34359738368 1779630372287 2905665634828288 qz299 (@Enclosure.Real.IsNear.neg (Real.sin qz22) Bool.false 36907 131072 23475511 22168469504 (@Enclosure.Real.IsNear.recentre' (Real.sin qz22) Bool.false 147628 524288 46951022 44336939008 36907 131072 23475511 22168469504 (ep77 rfl rfl) rfl)) rfl)

noncomputable def ep79 := @ep49 38069873413 68719476736 223393129237 363208204353536 Bool.true 5585837543 34359738368 1779630372287 2905665634828288 Bool.false 1060974954032406724608 30878435181 68719476736 3962966280517 2905665634828288 Bool.false 321433885598229200896 18709914619 34359738368 7932967056895 5811331269656576 (ep50 (BSN.head_sum_c_succ qz5 2 3 rfl rfl) (ep61 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep62 ep78) rfl rfl

noncomputable abbrev qz532 := (@Nat.cast Real Real.instNatCast 4)

noncomputable abbrev qz26 := (@Inv.inv Real Real.instInv (Real.sqrt qz532))

noncomputable abbrev qz27 := (@HMul.hMul Real Real Real qz267 qz284 (Real.log (Enclosure.sfrac Bool.false 4 1)))

noncomputable def ep80 := @Enclosure.Complex.IsNear.of_eq qz280 (Complex.mk (@HMul.hMul Real Real Real qz0 qz26 (Real.cos qz27)) (@HMul.hMul Real Real Real qz0 qz26 (@Neg.neg Real Real.instNeg (Real.sin qz27)))) Bool.true 17179017219 34359738368 772016476287 1452832817414144 Bool.false 647231067 137438953472 3077086574519 5811331269656576 (BSN.cpow_neg_s_mk qz13 88388 1000 4 qz14 rfl)

noncomputable def ep81 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz532) 1048577 524288 1 524288 131071 131072 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz532) (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz532 qz15)) Bool.false 1048577 524288 1 524288 (BSN.sqrt_natCast_div_one 4) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz532 qz15)) Bool.false 1048577 524288 1 524288 1048577 524288 1 524288 (BSN.sqrt_enclosure 4 1 524288 524289 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep82 := nat_lit 471225594319403171539306640625

noncomputable def ep83 := nat_lit 73155514365408823868279100600

noncomputable def ep84 := BSN.log_dyadic_bound 3 5 13 12 ep82 262144 84566 ep83 89313862490502916491225 363408 8 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base12 (BSN.artanhP 3) (BSN.artanhQ 5) 0 12 ep83 ep82 89313862490502916491225 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep85 := BSN.cos_dyadic_bound_f 10113356 1073741824 1 0 524288 169298 0 1 1 0 1 1 524264 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 10113356) qz292 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 10113356) qz293 0 0 rfl) rfl rfl

noncomputable abbrev qz28 := (Real.log (Enclosure.sfrac Bool.false 4 1))

noncomputable abbrev qz300 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 16060453) (@Nat.cast Real Real.instNatCast 131072))

noncomputable abbrev qz301 := (BSN.isNear_log_sfrac 4 1 363408 262144 1 84566 Bool.false (BSN.logfrac_isNear 8 2 1 4 1 363408 262144 84566 rfl rfl rfl (ep84 rfl)))

noncomputable abbrev qz302 := (@Nat.cast Real Real.instNatCast 18889465931478580854784)

noncomputable def ep86 := @Enclosure.Real.IsNear.cos_image qz27 qz300 Bool.false 16060453 131072 549 524288 Bool.true 524264 524288 1 84566 (@Enclosure.Real.IsNear.recentre' qz27 Bool.false 501889161 4096000 22097 21141500 16060453 131072 549 524288 (@Enclosure.Real.IsNear.mulLit_ff qz13 qz28 88388 1000 0 1 363408 262144 1 84566 501889161 4096000 22097 21141500 qz18 qz301 rfl) rfl) (Enclosure.sfrac_false_div 16060453 131072) (BSN.cos_reduce2 qz300 (@HDiv.hDiv Real Real Real qz1 qz291 qz302) 226375608064910080 72057594037927936 Bool.false 524264 524288 19 1000000000000000 169132 84566 (BSN.sin_reduce_arg_pos_rat_q2 16060453 131072 226375608064910080 72057594037927936 19 177916056299934580736 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 524264 524288 177916056299934580736 18889465931478580854784 10113356 1073741824 169298 169132 (ep85 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep87 := BSN.sin_dyadic_bound_f 10113356 1073741824 1 0 524288 169298 0 1 1 0 1 1 4938 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 10113356) qz287 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 10113356) qz288 0 0 rfl) rfl rfl

noncomputable def ep88 := @Enclosure.Real.IsNear.sin_image qz27 qz300 Bool.false 16060453 131072 549 524288 Bool.true 4938 524288 1 84566 (@Enclosure.Real.IsNear.recentre' qz27 Bool.false 501889161 4096000 22097 21141500 16060453 131072 549 524288 (@Enclosure.Real.IsNear.mulLit_ff qz13 qz28 88388 1000 0 1 363408 262144 1 84566 501889161 4096000 22097 21141500 qz18 qz301 rfl) rfl) (Enclosure.sfrac_false_div 16060453 131072) (BSN.sin_reduce2 qz300 (@HDiv.hDiv Real Real Real qz1 qz291 qz302) 226375608064910080 72057594037927936 Bool.false 4938 524288 19 1000000000000000 169132 84566 (BSN.sin_reduce_arg_pos_rat_q2 16060453 131072 226375608064910080 72057594037927936 19 177916056299934580736 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 4938 524288 177916056299934580736 18889465931478580854784 10113356 1073741824 169298 169132 (ep87 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz303 := (@Enclosure.Real.IsNear.recentre' qz26 Bool.false 262143 524288 1 524288 262143 524288 1 524288 (ep81 rfl rfl) rfl)

noncomputable def ep89 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz26 (Real.cos qz27)) (@HMul.hMul Real Real Real qz0 qz26 (@Neg.neg Real Real.instNeg (Real.sin qz27))) Bool.true 17179017219 34359738368 772016476287 1452832817414144 Bool.false 647231067 137438953472 3077086574519 5811331269656576 (@Enclosure.Real.IsNear.mulLit_ft qz26 (Real.cos qz27) 262143 524288 1 524288 65533 65536 23475511 22168469504 17179017219 34359738368 772016476287 1452832817414144 qz303 (@Enclosure.Real.IsNear.recentre' (Real.cos qz27) Bool.true 524264 524288 46951022 44336939008 65533 65536 23475511 22168469504 (ep86 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz26 (@Neg.neg Real Real.instNeg (Real.sin qz27)) 262143 524288 1 524288 2469 262144 23475511 22168469504 647231067 137438953472 3077086574519 5811331269656576 qz303 (@Enclosure.Real.IsNear.neg (Real.sin qz27) Bool.true 2469 262144 23475511 22168469504 (@Enclosure.Real.IsNear.recentre' (Real.sin qz27) Bool.true 4938 524288 46951022 44336939008 2469 262144 23475511 22168469504 (ep88 rfl rfl) rfl)) rfl)

noncomputable def ep90 := @ep47 17179017219 34359738368 772016476287 1452832817414144 Bool.false 647231067 137438953472 3077086574519 5811331269656576 Bool.true 119558120096007192576 3479599257 68719476736 5506999233091 2905665634828288 Bool.false 2593709774911595085824 75486889543 137438953472 5505026815707 2905665634828288 (ep48 (BSN.head_sum_c_succ qz5 3 4 rfl rfl) (ep79 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep80 ep89) rfl rfl

noncomputable abbrev qz533 := (@Nat.cast Real Real.instNatCast 5)

noncomputable abbrev qz29 := (@Inv.inv Real Real.instInv (Real.sqrt qz533))

noncomputable abbrev qz30 := (@HMul.hMul Real Real Real qz267 qz284 (Real.log (Enclosure.sfrac Bool.false 5 1)))

noncomputable def ep91 := @Enclosure.Complex.IsNear.of_eq qz279 (Complex.mk (@HMul.hMul Real Real Real qz0 qz29 (Real.cos qz30)) (@HMul.hMul Real Real Real qz0 qz29 (@Neg.neg Real Real.instNeg (Real.sin qz30)))) Bool.true 78024483599 274877906944 5518373620363 11622662539313152 Bool.false 47496619799 137438953472 1380358420839 2905665634828288 (BSN.cpow_neg_s_mk qz13 88388 1000 5 qz14 rfl)

noncomputable def ep92 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz533) 1172343 524288 1 524288 117234 117235 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz533) (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz533 qz15)) Bool.false 1172343 524288 1 524288 (BSN.sqrt_natCast_div_one 5) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz533 qz15)) Bool.false 1172343 524288 1 524288 1172343 524288 1 524288 (BSN.sqrt_enclosure 5 1 586171 586172 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep93 := nat_lit 11734546589655452485523914939250625

noncomputable def ep94 := nat_lit 2429970938528035899633153341031900

noncomputable def ep95 := nat_lit 824199001261152424427520000

noncomputable def ep96 := BSN.log_dyadic_bound 2 3 17 16 ep93 262144 84566 ep94 ep95 421904 5 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base16 (BSN.artanhP 2) (BSN.artanhQ 3) 0 16 ep94 ep93 ep95 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep97 := nat_lit 1806453490010845928071807440616231524553931350661261129086441146291129942016

noncomputable def ep98 := nat_lit 653915406985652012085272300946601254267797296512684548212767566055079936

noncomputable def ep99 := nat_lit 5418052639218566480191251777246801371153258457390758018162897903741279666176

noncomputable def ep100 := BSN.cos_dyadic_bound_f 948287872 1073741824 3 2 524288 169298 ep97 ep73 ep98 ep99 ep75 ep98 332771 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 948287872) qz292 0 2 ep97 ep73 ep98 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 948287872) qz293 0 2 ep99 ep75 ep98 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz31 := (Real.log (Enclosure.sfrac Bool.false 5 1))

noncomputable abbrev qz304 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 74582501) qz23)

noncomputable abbrev qz305 := (BSN.isNear_log_sfrac 5 1 421904 262144 1 84566 Bool.false (BSN.logfrac_isNear 5 1 2 5 1 421904 262144 84566 rfl rfl rfl (ep96 rfl)))

noncomputable def ep101 := @Enclosure.Real.IsNear.cos_image qz30 qz304 Bool.false 74582501 524288 549 524288 Bool.true 332771 524288 1 84566 (@Enclosure.Real.IsNear.recentre' qz30 Bool.false 582675793 4096000 22097 21141500 74582501 524288 549 524288 (@Enclosure.Real.IsNear.mulLit_ff qz13 qz31 88388 1000 0 1 421904 262144 1 84566 582675793 4096000 22097 21141500 qz18 qz305 rfl) rfl) (Enclosure.sfrac_false_div 74582501 524288) (BSN.cos_reduce2 qz304 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 66729826680506807222272) qz25) 226375608064910080 72057594037927936 Bool.false 332771 524288 22 1000000000000000 169132 84566 (BSN.sin_reduce_arg_pos_rat_q2 74582501 524288 226375608064910080 72057594037927936 22 66729826680506807222272 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 332771 524288 66729826680506807222272 75557863725914323419136 948287872 1073741824 169298 169132 (ep100 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep102 := nat_lit 808650361395858161824631038941331456

noncomputable def ep103 := nat_lit 159507359494189904748456847233641349120

noncomputable def ep104 := nat_lit 1116551516459329333239197930635489443840

noncomputable def ep105 := BSN.sin_dyadic_bound_f 948287872 1073741824 2 1 524288 169298 ep102 ep103 ep102 ep102 ep104 ep102 405142 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 948287872) qz287 0 1 ep102 ep103 ep102 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 948287872) qz288 0 1 ep102 ep104 ep102 rfl rfl rfl rfl) rfl rfl

noncomputable def ep106 := @Enclosure.Real.IsNear.sin_image qz30 qz304 Bool.false 74582501 524288 549 524288 Bool.true 405142 524288 1 84566 (@Enclosure.Real.IsNear.recentre' qz30 Bool.false 582675793 4096000 22097 21141500 74582501 524288 549 524288 (@Enclosure.Real.IsNear.mulLit_ff qz13 qz31 88388 1000 0 1 421904 262144 1 84566 582675793 4096000 22097 21141500 qz18 qz305 rfl) rfl) (Enclosure.sfrac_false_div 74582501 524288) (BSN.sin_reduce2 qz304 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 66729826680506807222272) qz25) 226375608064910080 72057594037927936 Bool.false 405142 524288 22 1000000000000000 169132 84566 (BSN.sin_reduce_arg_pos_rat_q2 74582501 524288 226375608064910080 72057594037927936 22 66729826680506807222272 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 405142 524288 66729826680506807222272 75557863725914323419136 948287872 1073741824 169298 169132 (ep105 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz306 := (@Enclosure.Real.IsNear.recentre' qz29 Bool.false 234469 524288 1 524288 234469 524288 1 524288 (ep92 rfl rfl) rfl)

noncomputable def ep107 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz29 (Real.cos qz30)) (@HMul.hMul Real Real Real qz0 qz29 (@Neg.neg Real Real.instNeg (Real.sin qz30))) Bool.true 78024483599 274877906944 5518373620363 11622662539313152 Bool.false 47496619799 137438953472 1380358420839 2905665634828288 (@Enclosure.Real.IsNear.mulLit_ft qz29 (Real.cos qz30) 234469 524288 1 524288 332771 524288 23475511 22168469504 78024483599 274877906944 5518373620363 11622662539313152 qz306 (@Enclosure.Real.IsNear.recentre' (Real.cos qz30) Bool.true 332771 524288 46951022 44336939008 332771 524288 23475511 22168469504 (ep101 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz29 (@Neg.neg Real Real.instNeg (Real.sin qz30)) 234469 524288 1 524288 202571 262144 23475511 22168469504 47496619799 137438953472 1380358420839 2905665634828288 qz306 (@Enclosure.Real.IsNear.neg (Real.sin qz30) Bool.true 202571 262144 23475511 22168469504 (@Enclosure.Real.IsNear.recentre' (Real.sin qz30) Bool.true 405142 524288 46951022 44336939008 202571 262144 23475511 22168469504 (ep106 rfl rfl) rfl)) rfl)

noncomputable def ep108 := @ep45 78024483599 274877906944 5518373620363 11622662539313152 Bool.false 47496619799 137438953472 1380358420839 2905665634828288 Bool.true 6318266646287951593472 91942880627 274877906944 27546370552727 11622662539313152 Bool.false 16902724818278415335424 61491754671 68719476736 3442692618273 1452832817414144 (ep46 (BSN.head_sum_c_succ qz5 4 5 rfl rfl) (ep90 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep91 ep107) rfl rfl

noncomputable abbrev qz307 := (@Nat.cast Real Real.instNatCast 6)

noncomputable abbrev qz32 := (@Inv.inv Real Real.instInv (Real.sqrt qz307))

noncomputable abbrev qz534 := (Real.log (Enclosure.sfrac Bool.false 6 1))

noncomputable abbrev qz33 := (@HMul.hMul Real Real Real qz267 qz284 qz534)

noncomputable def ep109 := @Enclosure.Complex.IsNear.of_eq qz278 (Complex.mk (@HMul.hMul Real Real Real qz0 qz32 (Real.cos qz33)) (@HMul.hMul Real Real Real qz0 qz32 (@Neg.neg Real Real.instNeg (Real.sin qz33)))) Bool.false 31063266031 274877906944 5030834863947 11622662539313152 Bool.true 13479106025 34359738368 315375034365 726416408707072 (BSN.cpow_neg_s_mk qz13 88388 1000 6 qz14 rfl)

noncomputable abbrev qz308 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 6) qz15)

noncomputable def ep110 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz307) 1284239 524288 1 524288 107019 107020 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz307) (Real.sqrt qz308) Bool.false 1284239 524288 1 524288 (BSN.sqrt_natCast_div_one 6) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz308) Bool.false 1284239 524288 1 524288 1284239 524288 1 524288 (BSN.sqrt_enclosure 6 1 642119 642120 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep111 := BSN.log_dyadic_bound 2 10 4 3 105000000 262144 84566 1434560 960 106290 12 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 2) (BSN.artanhQ 10) 0 3 1434560 105000000 960 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep112 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz534 88388 1000 0 1 4034681531866359 2251799813685248 250000000042283 21141500000000000000 89154357809650934823 562949953421312000 5524250000934327451 5285375000000000000000 qz18 (BSN.isNear_log_sfrac 6 1 4034681531866359 2251799813685248 250000000042283 21141500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz308) Bool.false 16922680887833197019136 9444732965739290427392 1000000000169132 84566000000000000000 4034681531866359 2251799813685248 250000000042283 21141500000000000000 (BSN.log_rat_reduce_isNear 6 1 2 12 8 106290 262144 24973259072661432 36028797018963968 84566 1000000000000000 rfl rfl rfl rfl (ep111 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep113 := nat_lit 8241657976454095551109249049656991613026372895337354429936322028421048984161

noncomputable def ep114 := nat_lit 13576245137732837964114539336096596166751886903349168255242964522948125281

noncomputable def ep115 := nat_lit 24697821439086820977399518070298781646745614912205364953298480156217250701921

noncomputable def ep116 := BSN.cos_dyadic_bound_f 1385471061 1073741824 3 2 524288 169298 ep113 ep73 ep114 ep115 ep75 ep114 145129 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1385471061) qz292 0 2 ep113 ep73 ep114 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1385471061) qz293 0 2 ep115 ep75 ep114 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz309 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 41515733) qz16)

noncomputable def ep117 := @Enclosure.Real.IsNear.cos_image qz33 qz309 Bool.false 41515733 262144 549 524288 Bool.false 145129 524288 1 84566 (@Enclosure.Real.IsNear.recentre' qz33 Bool.false 89154357809650934823 562949953421312000 5524250000934327451 5285375000000000000000 41515733 262144 549 524288 (ep112 rfl) rfl) (Enclosure.sfrac_false_div 41515733 262144) (BSN.cos_reduce0 qz309 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 48746929345237327282176) qz19) 226375608064910080 72057594037927936 Bool.false 145129 524288 25 1000000000000000 169132 84566 (BSN.sin_reduce_arg_pos_rat_q0 41515733 262144 226375608064910080 72057594037927936 25 48746929345237327282176 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 145129 524288 48746929345237327282176 37778931862957161709568 1385471061 1073741824 169298 169132 (ep116 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep118 := nat_lit 14824123361507185721625356657913707626514069702084558639281185279539529671265

noncomputable def ep119 := nat_lit 38803104407057728485648320087991744532790679498092231116180329980042566460001

noncomputable def ep120 := BSN.sin_dyadic_bound_f 1385471061 1073741824 3 2 524288 169298 ep118 ep66 ep114 ep119 ep69 ep114 503800 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1385471061) qz287 0 2 ep118 ep66 ep114 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1385471061) qz288 0 2 ep119 ep69 ep114 rfl rfl rfl rfl) rfl rfl

noncomputable def ep121 := @Enclosure.Real.IsNear.sin_image qz33 qz309 Bool.false 41515733 262144 549 524288 Bool.false 503800 524288 1 84566 (@Enclosure.Real.IsNear.recentre' qz33 Bool.false 89154357809650934823 562949953421312000 5524250000934327451 5285375000000000000000 41515733 262144 549 524288 (ep112 rfl) rfl) (Enclosure.sfrac_false_div 41515733 262144) (BSN.sin_reduce0 qz309 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 48746929345237327282176) qz19) 226375608064910080 72057594037927936 Bool.false 503800 524288 25 1000000000000000 169132 84566 (BSN.sin_reduce_arg_pos_rat_q0 41515733 262144 226375608064910080 72057594037927936 25 48746929345237327282176 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 503800 524288 48746929345237327282176 37778931862957161709568 1385471061 1073741824 169298 169132 (ep120 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz310 := (@Enclosure.Real.IsNear.recentre' qz32 Bool.false 214039 524288 1 524288 214039 524288 1 524288 (ep110 rfl rfl) rfl)

noncomputable def ep122 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz32 (Real.cos qz33)) (@HMul.hMul Real Real Real qz0 qz32 (@Neg.neg Real Real.instNeg (Real.sin qz33))) Bool.false 31063266031 274877906944 5030834863947 11622662539313152 Bool.true 13479106025 34359738368 315375034365 726416408707072 (@Enclosure.Real.IsNear.mulLit_ff qz32 (Real.cos qz33) 214039 524288 1 524288 145129 524288 23475511 22168469504 31063266031 274877906944 5030834863947 11622662539313152 qz310 (@Enclosure.Real.IsNear.recentre' (Real.cos qz33) Bool.false 145129 524288 46951022 44336939008 145129 524288 23475511 22168469504 (ep117 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz32 (@Neg.neg Real Real.instNeg (Real.sin qz33)) 214039 524288 1 524288 62975 65536 23475511 22168469504 13479106025 34359738368 315375034365 726416408707072 qz310 (@Enclosure.Real.IsNear.neg (Real.sin qz33) Bool.false 62975 65536 23475511 22168469504 (@Enclosure.Real.IsNear.recentre' (Real.sin qz33) Bool.false 503800 524288 46951022 44336939008 62975 65536 23475511 22168469504 (ep121 rfl rfl) rfl)) rfl)

noncomputable def ep123 := @ep43 31063266031 274877906944 5030834863947 11622662539313152 Bool.true 13479106025 34359738368 315375034365 726416408707072 Bool.true 16734461035705872154624 15219903649 68719476736 16288602708337 5811331269656576 Bool.false 1186563489377736982528 34533542621 68719476736 4073442687003 1452832817414144 (ep44 (BSN.head_sum_c_succ qz5 5 6 rfl rfl) (ep108 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep109 ep122) rfl rfl

noncomputable abbrev qz311 := (@Nat.cast Real Real.instNatCast 7)

noncomputable abbrev qz34 := (@Inv.inv Real Real.instInv (Real.sqrt qz311))

noncomputable abbrev qz535 := (Real.log (Enclosure.sfrac Bool.false 7 1))

noncomputable abbrev qz35 := (@HMul.hMul Real Real Real qz267 qz284 qz535)

noncomputable def ep124 := @Enclosure.Complex.IsNear.of_eq qz277 (Complex.mk (@HMul.hMul Real Real Real qz0 qz34 (Real.cos qz35)) (@HMul.hMul Real Real Real qz0 qz34 (@Neg.neg Real Real.instNeg (Real.sin qz35)))) Bool.true 18229608859 68719476736 583445015235 1452832817414144 Bool.true 74006152143 274877906944 4667792213267 11622662539313152 (BSN.cpow_neg_s_mk qz13 88388 1000 7 qz14 rfl)

noncomputable abbrev qz312 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 7) qz15)

noncomputable def ep125 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz311) 1387135 524288 1 524288 99081 99082 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz311) (Real.sqrt qz312) Bool.false 1387135 524288 1 524288 (BSN.sqrt_natCast_div_one 7) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz312) Bool.false 1387135 524288 1 524288 1387135 524288 1 524288 (BSN.sqrt_enclosure 7 1 693567 693568 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep126 := BSN.log_dyadic_bound 3 11 5 4 202569142545 262144 84566 5259111624 688905 146699 14 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 3) (BSN.artanhQ 11) 0 4 5259111624 202569142545 688905 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep127 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz535 88388 1000 0 1 4381792198794487 2251799813685248 250000000042283 21141500000000000000 96824462216761779239 562949953421312000 5524250000934327451 5285375000000000000000 qz18 (BSN.isNear_log_sfrac 7 1 4381792198794487 2251799813685248 250000000042283 21141500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz312) Bool.false 18378568546572512002048 9444732965739290427392 1000000000169132 84566000000000000000 4381792198794487 2251799813685248 250000000042283 21141500000000000000 (BSN.log_rat_reduce_isNear 7 1 2 14 8 146699 262144 24973259072661432 36028797018963968 84566 1000000000000000 rfl rfl rfl rfl (ep126 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep128 := nat_lit 486975602552349824466680843544598641

noncomputable def ep129 := BSN.sin_dyadic_bound_f 835366011 1073741824 2 1 524288 169298 ep128 ep103 ep128 ep128 ep104 ep128 367972 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 835366011) qz287 0 1 ep128 ep103 ep128 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 835366011) qz288 0 1 ep128 ep104 ep128 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz313 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 90174807) qz23)

noncomputable def ep130 := @Enclosure.Real.IsNear.cos_image qz35 qz313 Bool.false 90174807 524288 549 524288 Bool.true 367972 524288 1 84566 (@Enclosure.Real.IsNear.recentre' qz35 Bool.false 96824462216761779239 562949953421312000 5524250000934327451 5285375000000000000000 90174807 524288 549 524288 (ep127 rfl) rfl) (Enclosure.sfrac_false_div 90174807 524288) (BSN.cos_reduce1 qz313 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 58783657185226830905344) qz25) 226375608064910080 72057594037927936 Bool.false 367972 524288 27 1000000000000000 169132 84566 (BSN.sin_reduce_arg_pos_rat_q1 90174807 524288 226375608064910080 72057594037927936 27 58783657185226830905344 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 367972 524288 58783657185226830905344 75557863725914323419136 835366011 1073741824 169298 169132 (ep129 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep131 := nat_lit 1087703840254524913570341375200683707188393949375167365488958005615998689761

noncomputable def ep132 := nat_lit 237145237481224180873602794042370613908565964745476523053656405779046881

noncomputable def ep133 := nat_lit 3262637230288612292349276920013966380337364716196011143420766704036437975521

noncomputable def ep134 := BSN.cos_dyadic_bound_f 835366011 1073741824 3 2 524288 169298 ep131 ep73 ep132 ep133 ep75 ep132 373461 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 835366011) qz292 0 2 ep131 ep73 ep132 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 835366011) qz293 0 2 ep133 ep75 ep132 rfl rfl rfl rfl) rfl rfl

noncomputable def ep135 := @Enclosure.Real.IsNear.sin_image qz35 qz313 Bool.false 90174807 524288 549 524288 Bool.false 373461 524288 1 84566 (@Enclosure.Real.IsNear.recentre' qz35 Bool.false 96824462216761779239 562949953421312000 5524250000934327451 5285375000000000000000 90174807 524288 549 524288 (ep127 rfl) rfl) (Enclosure.sfrac_false_div 90174807 524288) (BSN.sin_reduce1 qz313 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 58783657185226830905344) qz25) 226375608064910080 72057594037927936 Bool.false 373461 524288 27 1000000000000000 169132 84566 (BSN.sin_reduce_arg_pos_rat_q1 90174807 524288 226375608064910080 72057594037927936 27 58783657185226830905344 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 373461 524288 58783657185226830905344 75557863725914323419136 835366011 1073741824 169298 169132 (ep134 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz314 := (@Enclosure.Real.IsNear.recentre' qz34 Bool.false 198163 524288 1 524288 198163 524288 1 524288 (ep125 rfl rfl) rfl)

noncomputable def ep136 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz34 (Real.cos qz35)) (@HMul.hMul Real Real Real qz0 qz34 (@Neg.neg Real Real.instNeg (Real.sin qz35))) Bool.true 18229608859 68719476736 583445015235 1452832817414144 Bool.true 74006152143 274877906944 4667792213267 11622662539313152 (@Enclosure.Real.IsNear.mulLit_ft qz34 (Real.cos qz35) 198163 524288 1 524288 91993 131072 23475511 22168469504 18229608859 68719476736 583445015235 1452832817414144 qz314 (@Enclosure.Real.IsNear.recentre' (Real.cos qz35) Bool.true 367972 524288 46951022 44336939008 91993 131072 23475511 22168469504 (ep130 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz34 (@Neg.neg Real Real.instNeg (Real.sin qz35)) 198163 524288 1 524288 373461 524288 23475511 22168469504 74006152143 274877906944 4667792213267 11622662539313152 qz314 (@Enclosure.Real.IsNear.neg (Real.sin qz35) Bool.false 373461 524288 23475511 22168469504 (@Enclosure.Real.IsNear.recentre' (Real.sin qz35) Bool.false 373461 524288 46951022 44336939008 373461 524288 23475511 22168469504 (ep135 rfl rfl) rfl)) rfl)

noncomputable def ep137 := @ep41 18229608859 68719476736 583445015235 1452832817414144 Bool.true 74006152143 274877906944 4667792213267 11622662539313152 Bool.true 2298632996624047013888 8362378127 17179869184 18622382769277 5811331269656576 Bool.false 4406843864510130814976 64128018341 274877906944 37255333709291 11622662539313152 (ep42 (BSN.head_sum_c_succ qz5 6 7 rfl rfl) (ep123 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep124 ep136) rfl rfl

noncomputable abbrev qz315 := (@Nat.cast Real Real.instNatCast 8)

noncomputable abbrev qz36 := (@Inv.inv Real Real.instInv (Real.sqrt qz315))

noncomputable abbrev qz536 := (Real.log (Enclosure.sfrac Bool.false 8 1))

noncomputable abbrev qz37 := (@HMul.hMul Real Real Real qz267 qz284 qz536)

noncomputable def ep138 := @Enclosure.Complex.IsNear.of_eq qz276 (Complex.mk (@HMul.hMul Real Real Real qz0 qz36 (Real.cos qz37)) (@HMul.hMul Real Real Real qz0 qz36 (@Neg.neg Real Real.instNeg (Real.sin qz37)))) Bool.true 1409685615 274877906944 4351836183219 11622662539313152 Bool.true 12146652027 34359738368 1093420180665 2905665634828288 (BSN.cpow_neg_s_mk qz13 88388 1000 8 qz14 rfl)

noncomputable abbrev qz316 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 8) qz15)

noncomputable def ep139 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz315) 1482911 524288 1 524288 92681 92682 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz315) (Real.sqrt qz316) Bool.false 1482911 524288 1 524288 (BSN.sqrt_natCast_div_one 8) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz316) Bool.false 1482911 524288 1 524288 1482911 524288 1 524288 (BSN.sqrt_enclosure 8 1 741455 741456 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep140 := BSN.log_dyadic_bound 0 16 1 0 1 262144 84566 0 1 0 16 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 0) (BSN.artanhQ 16) 0 0 rfl) rfl rfl rfl

noncomputable def ep141 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz536 88388 1000 0 1 9364972152248037 4503599627370496 500000000126849 42283000000000000000 206937789648224873589 1125899906842624000 11048500002802982353 10570750000000000000000 qz18 (BSN.isNear_log_sfrac 8 1 9364972152248037 4503599627370496 500000000126849 42283000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz316) Bool.false 19639770079031275290624 9444732965739290427392 1000000000253698 84566000000000000000 9364972152248037 4503599627370496 500000000126849 42283000000000000000 (BSN.log_rat_reduce_isNear 8 1 3 16 16 0 262144 24973259072661432 36028797018963968 84566 1000000000000000 rfl rfl rfl rfl (ep140 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep142 := BSN.sin_dyadic_bound_f 15577587 1073741824 1 0 524288 169298 0 1 1 0 1 1 7605 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 15577587) qz287 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 15577587) qz288 0 0 rfl) rfl rfl

noncomputable abbrev qz317 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 96362917) qz23)

noncomputable def ep143 := @Enclosure.Real.IsNear.cos_image qz37 qz317 Bool.false 96362917 524288 549 524288 Bool.true 7605 524288 1 84566 (@Enclosure.Real.IsNear.recentre' qz37 Bool.false 206937789648224873589 1125899906842624000 11048500002802982353 10570750000000000000000 96362917 524288 549 524288 (ep141 rfl) rfl) (Enclosure.sfrac_false_div 96362917 524288) (BSN.cos_reduce1 qz317 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 1096175260226702802944) qz25) 226375608064910080 72057594037927936 Bool.false 7605 524288 29 1000000000000000 169132 84566 (BSN.sin_reduce_arg_pos_rat_q1 96362917 524288 226375608064910080 72057594037927936 29 1096175260226702802944 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 7605 524288 1096175260226702802944 75557863725914323419136 15577587 1073741824 169298 169132 (ep142 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep144 := BSN.cos_dyadic_bound_f 15577587 1073741824 1 0 524288 169298 0 1 1 0 1 1 524232 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 15577587) qz292 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 15577587) qz293 0 0 rfl) rfl rfl

noncomputable def ep145 := @Enclosure.Real.IsNear.sin_image qz37 qz317 Bool.false 96362917 524288 549 524288 Bool.false 524232 524288 1 84566 (@Enclosure.Real.IsNear.recentre' qz37 Bool.false 206937789648224873589 1125899906842624000 11048500002802982353 10570750000000000000000 96362917 524288 549 524288 (ep141 rfl) rfl) (Enclosure.sfrac_false_div 96362917 524288) (BSN.sin_reduce1 qz317 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 1096175260226702802944) qz25) 226375608064910080 72057594037927936 Bool.false 524232 524288 29 1000000000000000 169132 84566 (BSN.sin_reduce_arg_pos_rat_q1 96362917 524288 226375608064910080 72057594037927936 29 1096175260226702802944 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 524232 524288 1096175260226702802944 75557863725914323419136 15577587 1073741824 169298 169132 (ep144 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz318 := (@Enclosure.Real.IsNear.recentre' qz36 Bool.false 185363 524288 1 524288 185363 524288 1 524288 (ep139 rfl rfl) rfl)

noncomputable def ep146 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz36 (Real.cos qz37)) (@HMul.hMul Real Real Real qz0 qz36 (@Neg.neg Real Real.instNeg (Real.sin qz37))) Bool.true 1409685615 274877906944 4351836183219 11622662539313152 Bool.true 12146652027 34359738368 1093420180665 2905665634828288 (@Enclosure.Real.IsNear.mulLit_ft qz36 (Real.cos qz37) 185363 524288 1 524288 7605 524288 23475511 22168469504 1409685615 274877906944 4351836183219 11622662539313152 qz318 (@Enclosure.Real.IsNear.recentre' (Real.cos qz37) Bool.true 7605 524288 46951022 44336939008 7605 524288 23475511 22168469504 (ep143 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz36 (@Neg.neg Real Real.instNeg (Real.sin qz37)) 185363 524288 1 524288 65529 65536 23475511 22168469504 12146652027 34359738368 1093420180665 2905665634828288 qz318 (@Enclosure.Real.IsNear.neg (Real.sin qz37) Bool.false 65529 65536 23475511 22168469504 (@Enclosure.Real.IsNear.recentre' (Real.sin qz37) Bool.false 524232 524288 46951022 44336939008 65529 65536 23475511 22168469504 (ep145 rfl rfl) rfl)) rfl)

noncomputable def ep147 := @ep39 1409685615 274877906944 4351836183219 11622662539313152 Bool.true 12146652027 34359738368 1093420180665 2905665634828288 Bool.true 2322851211080313602048 135207735647 274877906944 41596601721773 11622662539313152 Bool.true 1135424353303789568000 33045197875 274877906944 41629014431951 11622662539313152 (ep40 (BSN.head_sum_c_succ qz5 7 8 rfl rfl) (ep137 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep138 ep146) rfl rfl

theorem EMRow25.d6 : Enclosure.Complex.IsNear qz3 Bool.true 135207735647 274877906944 41596601721773 11622662539313152 Bool.true 33045197875 274877906944 41629014431951 11622662539313152 := ep38 (BSN.head_sum_c_succ qz5 8 9 rfl rfl) (ep147 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable abbrev qz38 := (BSN.headSumC qz272 17)

noncomputable abbrev qz39 := (@HPow.hPow Complex Complex Complex qz274 (@Nat.cast Complex Complex.instNatCast 16) qz275)

noncomputable def ep148 := @Enclosure.Complex.IsNear.of_eq qz38 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 16) qz39) Bool.false 187291989515 274877906944 69941896866013 11622662539313152 Bool.true 65149037491 274877906944 69932639341427 11622662539313152

noncomputable def ep149 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 16) qz39 Bool.false 14823251637 34359738368 33421375202367 5811331269656576 Bool.true 3988740405 17179869184 16713807092933 2905665634828288 Bool.false

noncomputable abbrev qz40 := (@HPow.hPow Complex Complex Complex qz274 (@Nat.cast Complex Complex.instNatCast 15) qz275)

noncomputable def ep150 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 16) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 15) qz40) Bool.false 14823251637 34359738368 33421375202367 5811331269656576 Bool.true 3988740405 17179869184 16713807092933 2905665634828288

noncomputable def ep151 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 15) qz40 Bool.false 59919876713 274877906944 63646499219083 11622662539313152 Bool.true 23876331623 274877906944 63664825178679 11622662539313152 Bool.false

noncomputable abbrev qz41 := (@HPow.hPow Complex Complex Complex qz274 (@Nat.cast Complex Complex.instNatCast 14) qz275)

noncomputable def ep152 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 15) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 14) qz41) Bool.false 59919876713 274877906944 63646499219083 11622662539313152 Bool.true 23876331623 274877906944 63664825178679 11622662539313152

noncomputable def ep153 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 14) qz41 Bool.false 7839983675 274877906944 60341348005867 11622662539313152 Bool.false 27936771031 274877906944 60359754472295 11622662539313152 Bool.false

noncomputable abbrev qz42 := (@HPow.hPow Complex Complex Complex qz274 (@Nat.cast Complex Complex.instNatCast 13) qz275)

noncomputable def ep154 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 14) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 13) qz42) Bool.false 7839983675 274877906944 60341348005867 11622662539313152 Bool.false 27936771031 274877906944 60359754472295 11622662539313152

noncomputable def ep155 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 13) qz42 Bool.true 58480519315 274877906944 56908442146865 11622662539313152 Bool.false 8191979839 34359738368 28467600154585 5811331269656576 Bool.false

noncomputable abbrev qz43 := (@HPow.hPow Complex Complex Complex qz274 (@Nat.cast Complex Complex.instNatCast 12) qz275)

noncomputable def ep156 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 13) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 12) qz43) Bool.true 58480519315 274877906944 56908442146865 11622662539313152 Bool.false 8191979839 34359738368 28467600154585 5811331269656576

noncomputable def ep157 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 12) qz43 Bool.true 134835484419 274877906944 53334091952647 11622662539313152 Bool.false 43939698553 274877906944 53376148315767 11622662539313152 Bool.false

noncomputable abbrev qz44 := (@HPow.hPow Complex Complex Complex qz274 (@Nat.cast Complex Complex.instNatCast 11) qz275)

noncomputable def ep158 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 12) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 11) qz44) Bool.true 134835484419 274877906944 53334091952647 11622662539313152 Bool.false 43939698553 274877906944 53376148315767 11622662539313152

noncomputable def ep159 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 11) qz44 Bool.true 125524315161 274877906944 49627276717141 11622662539313152 Bool.true 38414401919 274877906944 49649795543583 11622662539313152 Bool.true

noncomputable abbrev qz45 := (@HPow.hPow Complex Complex Complex qz274 (@Nat.cast Complex Complex.instNatCast 10) qz275)

noncomputable def ep160 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 11) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 10) qz45) Bool.true 125524315161 274877906944 49627276717141 11622662539313152 Bool.true 38414401919 274877906944 49649795543583 11622662539313152

noncomputable def ep161 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 10) qz45 Bool.true 14523084639 68719476736 11429483398977 2905665634828288 Bool.false 16437547471 274877906944 45743660729541 11622662539313152 Bool.true

noncomputable abbrev qz319 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 9) qz7)

noncomputable def ep162 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 10) (@HAdd.hAdd Complex Complex Complex qz4 qz3 qz319) Bool.true 14523084639 68719476736 11429483398977 2905665634828288 Bool.false 16437547471 274877906944 45743660729541 11622662539313152

noncomputable def ep163 := @Enclosure.Complex.IsNear.addLitP qz3 qz319 Bool.true 135207735647 274877906944 41596601721773 11622662539313152 Bool.true 33045197875 274877906944 41629014431951 11622662539313152 Bool.false

noncomputable abbrev qz320 := (@Nat.cast Real Real.instNatCast 9)

noncomputable abbrev qz46 := (@Inv.inv Real Real.instInv (Real.sqrt qz320))

noncomputable abbrev qz537 := (Real.log (Enclosure.sfrac Bool.false 9 1))

noncomputable abbrev qz47 := (@HMul.hMul Real Real Real qz267 qz284 qz537)

noncomputable def ep164 := @Enclosure.Complex.IsNear.of_eq qz319 (Complex.mk (@HMul.hMul Real Real Real qz0 qz46 (Real.cos qz47)) (@HMul.hMul Real Real Real qz0 qz46 (@Neg.neg Real Real.instNeg (Real.sin qz47)))) Bool.false 77115397091 274877906944 4121331874135 11622662539313152 Bool.false 24741372673 137438953472 2057323148795 5811331269656576 (BSN.cpow_neg_s_mk qz13 88388 1000 9 qz14 rfl)

noncomputable abbrev qz321 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 9) qz15)

noncomputable def ep165 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz320) 1572865 524288 1 524288 87381 87382 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz320) (Real.sqrt qz321) Bool.false 1572865 524288 1 524288 (BSN.sqrt_natCast_div_one 9) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz321) Bool.false 1572865 524288 1 524288 1572865 524288 1 524288 (BSN.sqrt_enclosure 9 1 786432 786433 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep166 := BSN.log_dyadic_bound 1 17 2 1 867 262144 84566 1 1 30876 18 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 1) (BSN.artanhQ 17) 0 1 1 867 1 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep167 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz537 88388 1000 0 1 9895417793173221 4503599627370496 500000000126849 42283000000000000000 218659046975748664437 1125899906842624000 11048500002802982353 10570750000000000000000 qz18 (BSN.isNear_log_sfrac 9 1 9895417793173221 4503599627370496 500000000126849 42283000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz321) Bool.false 20752195215788806766592 9444732965739290427392 1000000000253698 84566000000000000000 9895417793173221 4503599627370496 500000000126849 42283000000000000000 (BSN.log_rat_reduce_isNear 9 1 3 18 16 30876 262144 24973259072661432 36028797018963968 84566 1000000000000000 rfl rfl rfl rfl (ep166 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep168 := nat_lit 5351088962322271007421113454446237927814571068681607632536906915104585482240

noncomputable def ep169 := nat_lit 1771064111334614531222004192124719580863348394262951559220676721712889856

noncomputable def ep170 := nat_lit 14011889368949501357814271040571945026859621663432546639834113205819712536576

noncomputable def ep171 := BSN.sin_dyadic_bound_f 1074061836 1073741824 3 2 524288 169298 ep168 ep66 ep169 ep170 ep69 ep169 441257 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1074061836) qz287 0 2 ep168 ep66 ep169 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1074061836) qz288 0 2 ep170 ep69 ep169 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz322 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 101821053) qz23)

noncomputable def ep172 := @Enclosure.Real.IsNear.cos_image qz47 qz322 Bool.false 101821053 524288 549 524288 Bool.false 441257 524288 1 84566 (@Enclosure.Real.IsNear.recentre' qz47 Bool.false 218659046975748664437 1125899906842624000 11048500002802982353 10570750000000000000000 101821053 524288 549 524288 (ep167 rfl) rfl) (Enclosure.sfrac_false_div 101821053 524288) (BSN.cos_reduce3 qz322 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 75580382637012912439296) qz25) 226375608064910080 72057594037927936 Bool.false 441257 524288 30 1000000000000000 169132 84566 (BSN.sin_reduce_arg_pos_rat_q3 101821053 524288 226375608064910080 72057594037927936 30 75580382637012912439296 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 441257 524288 75580382637012912439296 75557863725914323419136 1074061836 1073741824 169298 169132 (ep171 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep173 := nat_lit 2973614340895188166136717254333298724155145415220565552102379698045530996736

noncomputable def ep174 := nat_lit 8917300894462895269347707754615646733303709548873170753188697740693167210496

noncomputable def ep175 := BSN.cos_dyadic_bound_f 1074061836 1073741824 3 2 524288 169298 ep173 ep73 ep169 ep174 ep75 ep169 283142 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1074061836) qz292 0 2 ep173 ep73 ep169 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1074061836) qz293 0 2 ep174 ep75 ep169 rfl rfl rfl rfl) rfl rfl

noncomputable def ep176 := @Enclosure.Real.IsNear.sin_image qz47 qz322 Bool.false 101821053 524288 549 524288 Bool.true 283142 524288 1 84566 (@Enclosure.Real.IsNear.recentre' qz47 Bool.false 218659046975748664437 1125899906842624000 11048500002802982353 10570750000000000000000 101821053 524288 549 524288 (ep167 rfl) rfl) (Enclosure.sfrac_false_div 101821053 524288) (BSN.sin_reduce3 qz322 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 75580382637012912439296) qz25) 226375608064910080 72057594037927936 Bool.false 283142 524288 30 1000000000000000 169132 84566 (BSN.sin_reduce_arg_pos_rat_q3 101821053 524288 226375608064910080 72057594037927936 30 75580382637012912439296 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 283142 524288 75580382637012912439296 75557863725914323419136 1074061836 1073741824 169298 169132 (ep175 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz323 := (@Enclosure.Real.IsNear.recentre' qz46 Bool.false 174763 524288 1 524288 174763 524288 1 524288 (ep165 rfl rfl) rfl)

noncomputable def ep177 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz46 (Real.cos qz47)) (@HMul.hMul Real Real Real qz0 qz46 (@Neg.neg Real Real.instNeg (Real.sin qz47))) Bool.false 77115397091 274877906944 4121331874135 11622662539313152 Bool.false 24741372673 137438953472 2057323148795 5811331269656576 (@Enclosure.Real.IsNear.mulLit_ff qz46 (Real.cos qz47) 174763 524288 1 524288 441257 524288 23475511 22168469504 77115397091 274877906944 4121331874135 11622662539313152 qz323 (@Enclosure.Real.IsNear.recentre' (Real.cos qz47) Bool.false 441257 524288 46951022 44336939008 441257 524288 23475511 22168469504 (ep172 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz46 (@Neg.neg Real Real.instNeg (Real.sin qz47)) 174763 524288 1 524288 141571 262144 23475511 22168469504 24741372673 137438953472 2057323148795 5811331269656576 qz323 (@Enclosure.Real.IsNear.neg (Real.sin qz47) Bool.true 141571 262144 23475511 22168469504 (@Enclosure.Real.IsNear.recentre' (Real.sin qz47) Bool.true 283142 524288 46951022 44336939008 141571 262144 23475511 22168469504 (ep176 rfl rfl) rfl)) rfl)

noncomputable def ep178 := @ep163 77115397091 274877906944 4121331874135 11622662539313152 Bool.false 24741372673 137438953472 2057323148795 5811331269656576 Bool.true 15968300431755511332864 14523084639 68719476736 11429483398977 2905665634828288 Bool.false 2259159322060560269312 16437547471 274877906944 45743660729541 11622662539313152 EMRow25.d6 (ep164 ep177) rfl rfl

noncomputable abbrev qz324 := (@Nat.cast Real Real.instNatCast 10)

noncomputable abbrev qz48 := (@Inv.inv Real Real.instInv (Real.sqrt qz324))

noncomputable abbrev qz538 := (Real.log (Enclosure.sfrac Bool.false 10 1))

noncomputable abbrev qz49 := (@HMul.hMul Real Real Real qz267 qz284 qz538)

noncomputable def ep179 := @Enclosure.Complex.IsNear.of_eq qz45 (Complex.mk (@HMul.hMul Real Real Real qz0 qz48 (Real.cos qz49)) (@HMul.hMul Real Real Real qz0 qz48 (@Neg.neg Real Real.instNeg (Real.sin qz49)))) Bool.true 67431976605 274877906944 3909343121233 11622662539313152 Bool.true 27425974695 137438953472 1953067407021 5811331269656576 (BSN.cpow_neg_s_mk qz13 88388 1000 10 qz14 rfl)

noncomputable abbrev qz325 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 10) qz15)

noncomputable def ep180 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz324) 1657945 524288 1 524288 82897 82898 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz324) (Real.sqrt qz325) Bool.false 1657945 524288 1 524288 (BSN.sqrt_natCast_div_one 10) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz325) Bool.false 1657945 524288 1 524288 1657945 524288 1 524288 (BSN.sqrt_enclosure 10 1 828972 828973 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep181 := BSN.log_dyadic_bound 2 18 3 2 1574640 262144 84566 6528 48 58495 20 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 2) (BSN.artanhQ 18) 0 2 6528 1574640 48 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep182 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz538 88388 1000 0 1 10369908600166117 4503599627370496 500000000126849 42283000000000000000 229143870337870687349 1125899906842624000 11048500002802982353 10570750000000000000000 qz18 (BSN.isNear_log_sfrac 10 1 10369908600166117 4503599627370496 500000000126849 42283000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz325) Bool.false 21747274560655572598784 9444732965739290427392 1000000000253698 84566000000000000000 10369908600166117 4503599627370496 500000000126849 42283000000000000000 (BSN.log_rat_reduce_isNear 10 1 3 20 16 58495 262144 24973259072661432 36028797018963968 84566 1000000000000000 rfl rfl rfl rfl (ep181 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep183 := nat_lit 826193267155770060557989128435175696

noncomputable def ep184 := BSN.sin_dyadic_bound_f 953389606 1073741824 2 1 524288 169298 ep183 ep103 ep183 ep183 ep104 ep183 406719 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 953389606) qz287 0 1 ep183 ep103 ep183 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 953389606) qz288 0 1 ep183 ep104 ep183 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz326 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 106703429) qz23)

noncomputable def ep185 := @Enclosure.Real.IsNear.cos_image qz49 qz326 Bool.false 106703429 524288 549 524288 Bool.true 406719 524288 1 84566 (@Enclosure.Real.IsNear.recentre' qz49 Bool.false 229143870337870687349 1125899906842624000 11048500002802982353 10570750000000000000000 106703429 524288 549 524288 (ep182 rfl) rfl) (Enclosure.sfrac_false_div 106703429 524288) (BSN.cos_reduce1 qz326 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 67088829327244345212928) qz25) 226375608064910080 72057594037927936 Bool.false 406719 524288 32 1000000000000000 169132 84566 (BSN.sin_reduce_arg_pos_rat_q1 106703429 524288 226375608064910080 72057594037927936 32 67088829327244345212928 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 406719 524288 67088829327244345212928 75557863725914323419136 953389606 1073741824 169298 169132 (ep184 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep186 := nat_lit 1845657285977219269225108562257549262754645661773221900453555869149838909696

noncomputable def ep187 := nat_lit 682595314693525639490650073710920412337219580004770518465044062389084416

noncomputable def ep188 := nat_lit 5535606667302270756396344386625225947439262546159656160323737519324738560256

noncomputable def ep189 := BSN.cos_dyadic_bound_f 953389606 1073741824 3 2 524288 169298 ep186 ep73 ep187 ep188 ep75 ep187 330842 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 953389606) qz292 0 2 ep186 ep73 ep187 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 953389606) qz293 0 2 ep188 ep75 ep187 rfl rfl rfl rfl) rfl rfl

noncomputable def ep190 := @Enclosure.Real.IsNear.sin_image qz49 qz326 Bool.false 106703429 524288 549 524288 Bool.false 330842 524288 1 84566 (@Enclosure.Real.IsNear.recentre' qz49 Bool.false 229143870337870687349 1125899906842624000 11048500002802982353 10570750000000000000000 106703429 524288 549 524288 (ep182 rfl) rfl) (Enclosure.sfrac_false_div 106703429 524288) (BSN.sin_reduce1 qz326 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 67088829327244345212928) qz25) 226375608064910080 72057594037927936 Bool.false 330842 524288 32 1000000000000000 169132 84566 (BSN.sin_reduce_arg_pos_rat_q1 106703429 524288 226375608064910080 72057594037927936 32 67088829327244345212928 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 330842 524288 67088829327244345212928 75557863725914323419136 953389606 1073741824 169298 169132 (ep189 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz327 := (@Enclosure.Real.IsNear.recentre' qz48 Bool.false 165795 524288 1 524288 165795 524288 1 524288 (ep180 rfl rfl) rfl)

noncomputable def ep191 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz48 (Real.cos qz49)) (@HMul.hMul Real Real Real qz0 qz48 (@Neg.neg Real Real.instNeg (Real.sin qz49))) Bool.true 67431976605 274877906944 3909343121233 11622662539313152 Bool.true 27425974695 137438953472 1953067407021 5811331269656576 (@Enclosure.Real.IsNear.mulLit_ft qz48 (Real.cos qz49) 165795 524288 1 524288 406719 524288 23475511 22168469504 67431976605 274877906944 3909343121233 11622662539313152 qz327 (@Enclosure.Real.IsNear.recentre' (Real.cos qz49) Bool.true 406719 524288 46951022 44336939008 406719 524288 23475511 22168469504 (ep185 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz48 (@Neg.neg Real Real.instNeg (Real.sin qz49)) 165795 524288 1 524288 165421 262144 23475511 22168469504 27425974695 137438953472 1953067407021 5811331269656576 qz327 (@Enclosure.Real.IsNear.neg (Real.sin qz49) Bool.false 165421 262144 23475511 22168469504 (@Enclosure.Real.IsNear.recentre' (Real.sin qz49) Bool.false 330842 524288 46951022 44336939008 165421 262144 23475511 22168469504 (ep190 rfl rfl) rfl)) rfl)

noncomputable def ep192 := @ep161 67431976605 274877906944 3909343121233 11622662539313152 Bool.true 27425974695 137438953472 1953067407021 5811331269656576 Bool.true 8625965255508671594496 125524315161 274877906944 49627276717141 11622662539313152 Bool.true 5279635198000148512768 38414401919 274877906944 49649795543583 11622662539313152 (ep162 (BSN.head_sum_c_succ qz5 9 10 rfl rfl) (ep178 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep179 ep191) rfl rfl

noncomputable abbrev qz328 := (@Nat.cast Real Real.instNatCast 11)

noncomputable abbrev qz50 := (@Inv.inv Real Real.instInv (Real.sqrt qz328))

noncomputable abbrev qz539 := (Real.log (Enclosure.sfrac Bool.false 11 1))

noncomputable abbrev qz51 := (@HMul.hMul Real Real Real qz267 qz284 qz539)

noncomputable def ep193 := @Enclosure.Complex.IsNear.of_eq qz44 (Complex.mk (@HMul.hMul Real Real Real qz0 qz50 (Real.cos qz51)) (@HMul.hMul Real Real Real qz0 qz50 (@Neg.neg Real Real.instNeg (Real.sin qz51)))) Bool.true 4655584629 137438953472 1853407617753 5811331269656576 Bool.false 10294262559 34359738368 465794096523 1452832817414144 (BSN.cpow_neg_s_mk qz13 88388 1000 11 qz14 rfl)

noncomputable abbrev qz329 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 11) qz15)

noncomputable def ep194 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz328) 1738867 524288 1 524288 79039 79040 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz328) (Real.sqrt qz329) Bool.false 1738867 524288 1 524288 (BSN.sqrt_natCast_div_one 11) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz329) Bool.false 1738867 524288 1 524288 1738867 524288 1 524288 (BSN.sqrt_enclosure 11 1 869433 869434 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep195 := BSN.log_dyadic_bound 3 19 4 3 4939817505 262144 84566 41676111 10935 83480 22 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 3) (BSN.artanhQ 19) 0 3 41676111 4939817505 10935 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep196 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz539 88388 1000 0 1 10799147631728357 4503599627370496 500000000126849 42283000000000000000 238628765218301504629 1125899906842624000 11048500002802982353 10570750000000000000000 qz18 (BSN.isNear_log_sfrac 11 1 10799147631728357 4503599627370496 500000000126849 42283000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz329) Bool.false 22647454054174387339264 9444732965739290427392 1000000000253698 84566000000000000000 10799147631728357 4503599627370496 500000000126849 42283000000000000000 (BSN.log_rat_reduce_isNear 11 1 3 22 16 83480 262144 24973259072661432 36028797018963968 84566 1000000000000000 rfl rfl rfl rfl (ep195 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep197 := nat_lit 13457300338896643893646274155099464604454666971790574084894441119011482212481

noncomputable def ep198 := nat_lit 36121336803724780549000879389100982583872458340741555702036811040934172801

noncomputable def ep199 := nat_lit 40299658343082482119840820706520191848196255998690239143279249734952578291841

noncomputable def ep200 := BSN.cos_dyadic_bound_f 1565742993 1073741824 3 2 524288 169298 ep197 ep73 ep198 ep199 ep75 ep198 58902 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1565742993) qz292 0 2 ep197 ep73 ep198 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1565742993) qz293 0 2 ep199 ep75 ep198 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz330 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 55560089) qz16)

noncomputable def ep201 := @Enclosure.Real.IsNear.cos_image qz51 qz330 Bool.false 55560089 262144 137 131072 Bool.true 58902 524288 1 84566 (@Enclosure.Real.IsNear.recentre' qz51 Bool.false 238628765218301504629 1125899906842624000 11048500002802982353 10570750000000000000000 55560089 262144 137 131072 (ep196 rfl) rfl) (Enclosure.sfrac_false_div 55560089 262144) (BSN.cos_reduce2 qz330 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 55089684070207405948928) qz19) 226375608064910080 72057594037927936 Bool.false 58902 524288 33 1000000000000000 169132 84566 (BSN.sin_reduce_arg_pos_rat_q2 55560089 262144 226375608064910080 72057594037927936 33 55089684070207405948928 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 58902 524288 55089684070207405948928 37778931862957161709568 1565742993 1073741824 169298 169132 (ep200 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep202 := nat_lit 24194243540570979184124092775667755501951302582550440108248364565387920644225

noncomputable def ep203 := nat_lit 63307393775241772028007574893452243771403332307461380621894799977187803502721

noncomputable def ep204 := BSN.sin_dyadic_bound_f 1565742993 1073741824 3 2 524288 169298 ep202 ep66 ep198 ep203 ep69 ep198 520968 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1565742993) qz287 0 2 ep202 ep66 ep198 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1565742993) qz288 0 2 ep203 ep69 ep198 rfl rfl rfl rfl) rfl rfl

noncomputable def ep205 := @Enclosure.Real.IsNear.sin_image qz51 qz330 Bool.false 55560089 262144 137 131072 Bool.true 520968 524288 1 84566 (@Enclosure.Real.IsNear.recentre' qz51 Bool.false 238628765218301504629 1125899906842624000 11048500002802982353 10570750000000000000000 55560089 262144 137 131072 (ep196 rfl) rfl) (Enclosure.sfrac_false_div 55560089 262144) (BSN.sin_reduce2 qz330 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 55089684070207405948928) qz19) 226375608064910080 72057594037927936 Bool.false 520968 524288 33 1000000000000000 169132 84566 (BSN.sin_reduce_arg_pos_rat_q2 55560089 262144 226375608064910080 72057594037927936 33 55089684070207405948928 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 520968 524288 55089684070207405948928 37778931862957161709568 1565742993 1073741824 169298 169132 (ep204 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz331 := (@Enclosure.Real.IsNear.recentre' qz50 Bool.false 158079 524288 1 524288 158079 524288 1 524288 (ep194 rfl rfl) rfl)

noncomputable def ep206 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz50 (Real.cos qz51)) (@HMul.hMul Real Real Real qz0 qz50 (@Neg.neg Real Real.instNeg (Real.sin qz51))) Bool.true 4655584629 137438953472 1853407617753 5811331269656576 Bool.false 10294262559 34359738368 465794096523 1452832817414144 (@Enclosure.Real.IsNear.mulLit_ft qz50 (Real.cos qz51) 158079 524288 1 524288 29451 262144 5858307 5542117376 4655584629 137438953472 1853407617753 5811331269656576 qz331 (@Enclosure.Real.IsNear.recentre' (Real.cos qz51) Bool.true 58902 524288 11716614 11084234752 29451 262144 5858307 5542117376 (ep201 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz50 (@Neg.neg Real Real.instNeg (Real.sin qz51)) 158079 524288 1 524288 65121 65536 5858307 5542117376 10294262559 34359738368 465794096523 1452832817414144 qz331 (@Enclosure.Real.IsNear.neg (Real.sin qz51) Bool.true 65121 65536 5858307 5542117376 (@Enclosure.Real.IsNear.recentre' (Real.sin qz51) Bool.true 520968 524288 11716614 11084234752 65121 65536 5858307 5542117376 (ep205 rfl rfl) rfl)) rfl)

noncomputable def ep207 := @ep159 4655584629 137438953472 1853407617753 5811331269656576 Bool.false 10294262559 34359738368 465794096523 1452832817414144 Bool.true 18531647869437521952768 134835484419 274877906944 53334091952647 11622662539313152 Bool.false 1509756546249868181504 43939698553 274877906944 53376148315767 11622662539313152 (ep160 (BSN.head_sum_c_succ qz5 10 11 rfl rfl) (ep192 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep193 ep206) rfl rfl

noncomputable abbrev qz332 := (@Nat.cast Real Real.instNatCast 12)

noncomputable abbrev qz52 := (@Inv.inv Real Real.instInv (Real.sqrt qz332))

noncomputable abbrev qz540 := (Real.log (Enclosure.sfrac Bool.false 12 1))

noncomputable abbrev qz53 := (@HMul.hMul Real Real Real qz267 qz284 qz540)

noncomputable def ep208 := @Enclosure.Complex.IsNear.of_eq qz43 (Complex.mk (@HMul.hMul Real Real Real qz0 qz52 (Real.cos qz53)) (@HMul.hMul Real Real Real qz0 qz52 (@Neg.neg Real Real.instNeg (Real.sin qz53)))) Bool.false 4772185319 17179869184 1787175097109 5811331269656576 Bool.false 21596140159 274877906944 3559051993403 11622662539313152 (BSN.cpow_neg_s_mk qz13 88388 1000 12 qz14 rfl)

noncomputable abbrev qz333 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 12) qz15)

noncomputable def ep209 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz332) 1816187 524288 1 524288 75674 75675 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz332) (Real.sqrt qz333) Bool.false 1816187 524288 1 524288 (BSN.sqrt_natCast_div_one 12) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz333) Bool.false 1816187 524288 1 524288 1816187 524288 1 524288 (BSN.sqrt_enclosure 12 1 908093 908094 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep210 := BSN.log_dyadic_bound 4 20 4 3 6720000000 262144 84566 91811840 61440 106290 24 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 4) (BSN.artanhQ 20) 0 3 91811840 6720000000 61440 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep211 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz540 88388 1000 0 1 11191020447815397 4503599627370496 500000000126849 42283000000000000000 247287978835376827509 1125899906842624000 11048500002802982353 10570750000000000000000 qz18 (BSN.isNear_log_sfrac 12 1 11191020447815397 4503599627370496 500000000126849 42283000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz333) Bool.false 23469270914176955449344 9444732965739290427392 1000000000253698 84566000000000000000 11191020447815397 4503599627370496 500000000126849 42283000000000000000 (BSN.log_rat_reduce_isNear 12 1 3 24 16 106290 262144 24973259072661432 36028797018963968 84566 1000000000000000 rfl rfl rfl rfl (ep210 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep212 := nat_lit 15047787993231647483705304611451069509494641302227991022504155579004805869025

noncomputable def ep213 := nat_lit 13988623046904085046036546205531159231871008937836672352607928751469522401

noncomputable def ep214 := nat_lit 39388225068768851081534595764705750648015317015173955208463804155605445668321

noncomputable def ep215 := BSN.sin_dyadic_bound_f 1390662907 1073741824 3 2 524288 169298 ep212 ep66 ep213 ep214 ep69 ep213 504496 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1390662907) qz287 0 2 ep212 ep66 ep213 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1390662907) qz288 0 2 ep214 ep69 ep213 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz334 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 57576219) qz16)

noncomputable def ep216 := @Enclosure.Real.IsNear.cos_image qz53 qz334 Bool.false 57576219 262144 549 524288 Bool.false 504496 524288 1 84566 (@Enclosure.Real.IsNear.recentre' qz53 Bool.false 247287978835376827509 1125899906842624000 11048500002802982353 10570750000000000000000 57576219 262144 549 524288 (ep211 rfl) rfl) (Enclosure.sfrac_false_div 57576219 262144) (BSN.cos_reduce3 qz334 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 48929601202743765106688) qz19) 226375608064910080 72057594037927936 Bool.false 504496 524288 34 1000000000000000 169132 84566 (BSN.sin_reduce_arg_pos_rat_q3 57576219 262144 226375608064910080 72057594037927936 34 48929601202743765106688 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 504496 524288 48929601202743765106688 37778931862957161709568 1390662907 1073741824 169298 169132 (ep215 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep217 := nat_lit 8366099384260650417634518804675274687155632282987922422436801067781100826081

noncomputable def ep218 := nat_lit 25070320906688143082811483321614761743003154831088093922605187345840363433441

noncomputable def ep219 := BSN.cos_dyadic_bound_f 1390662907 1073741824 3 2 524288 169298 ep217 ep73 ep213 ep218 ep75 ep213 142691 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1390662907) qz292 0 2 ep217 ep73 ep213 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1390662907) qz293 0 2 ep218 ep75 ep213 rfl rfl rfl rfl) rfl rfl

noncomputable def ep220 := @Enclosure.Real.IsNear.sin_image qz53 qz334 Bool.false 57576219 262144 549 524288 Bool.true 142691 524288 1 84566 (@Enclosure.Real.IsNear.recentre' qz53 Bool.false 247287978835376827509 1125899906842624000 11048500002802982353 10570750000000000000000 57576219 262144 549 524288 (ep211 rfl) rfl) (Enclosure.sfrac_false_div 57576219 262144) (BSN.sin_reduce3 qz334 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 48929601202743765106688) qz19) 226375608064910080 72057594037927936 Bool.false 142691 524288 34 1000000000000000 169132 84566 (BSN.sin_reduce_arg_pos_rat_q3 57576219 262144 226375608064910080 72057594037927936 34 48929601202743765106688 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 142691 524288 48929601202743765106688 37778931862957161709568 1390662907 1073741824 169298 169132 (ep219 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz335 := (@Enclosure.Real.IsNear.recentre' qz52 Bool.false 151349 524288 1 524288 151349 524288 1 524288 (ep209 rfl rfl) rfl)

noncomputable def ep221 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz52 (Real.cos qz53)) (@HMul.hMul Real Real Real qz0 qz52 (@Neg.neg Real Real.instNeg (Real.sin qz53))) Bool.false 4772185319 17179869184 1787175097109 5811331269656576 Bool.false 21596140159 274877906944 3559051993403 11622662539313152 (@Enclosure.Real.IsNear.mulLit_ff qz52 (Real.cos qz53) 151349 524288 1 524288 31531 32768 23475511 22168469504 4772185319 17179869184 1787175097109 5811331269656576 qz335 (@Enclosure.Real.IsNear.recentre' (Real.cos qz53) Bool.false 504496 524288 46951022 44336939008 31531 32768 23475511 22168469504 (ep216 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz52 (@Neg.neg Real Real.instNeg (Real.sin qz53)) 151349 524288 1 524288 142691 524288 23475511 22168469504 21596140159 274877906944 3559051993403 11622662539313152 qz335 (@Enclosure.Real.IsNear.neg (Real.sin qz53) Bool.true 142691 524288 23475511 22168469504 (@Enclosure.Real.IsNear.recentre' (Real.sin qz53) Bool.true 142691 524288 46951022 44336939008 142691 524288 23475511 22168469504 (ep220 rfl rfl) rfl)) rfl)

noncomputable def ep222 := @ep157 4772185319 17179869184 1787175097109 5811331269656576 Bool.false 21596140159 274877906944 3559051993403 11622662539313152 Bool.true 1004687671644085288960 58480519315 274877906944 56908442146865 11622662539313152 Bool.false 18014354174974128816128 8191979839 34359738368 28467600154585 5811331269656576 (ep158 (BSN.head_sum_c_succ qz5 11 12 rfl rfl) (ep207 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep208 ep221) rfl rfl

noncomputable abbrev qz336 := (@Nat.cast Real Real.instNatCast 13)

noncomputable abbrev qz54 := (@Inv.inv Real Real.instInv (Real.sqrt qz336))

noncomputable abbrev qz541 := (Real.log (Enclosure.sfrac Bool.false 13 1))

noncomputable abbrev qz55 := (@HMul.hMul Real Real Real qz267 qz284 qz541)

noncomputable def ep223 := @Enclosure.Complex.IsNear.of_eq qz42 (Complex.mk (@HMul.hMul Real Real Real qz0 qz54 (Real.cos qz55)) (@HMul.hMul Real Real Real qz0 qz54 (@Neg.neg Real Real.instNeg (Real.sin qz55)))) Bool.false 33160251495 137438953472 1716452929501 5811331269656576 Bool.true 37599067681 274877906944 3424554163125 11622662539313152 (BSN.cpow_neg_s_mk qz13 88388 1000 13 qz14 rfl)

noncomputable abbrev qz337 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 13) qz15)

noncomputable def ep224 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz336) 1890347 524288 1 524288 72705 72706 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz336) (Real.sqrt qz337) Bool.false 1890347 524288 1 524288 (BSN.sqrt_natCast_div_one 13) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz337) Bool.false 1890347 524288 1 524288 1890347 524288 1 524288 (BSN.sqrt_enclosure 13 1 945173 945174 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep225 := BSN.log_dyadic_bound 5 21 5 4 35742602096145 262144 84566 699352521000 41015625 127272 26 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 5) (BSN.artanhQ 21) 0 4 699352521000 35742602096145 41015625 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep226 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz541 88388 1000 0 1 11551488463034085 4503599627370496 500000000126849 42283000000000000000 51050648113532835249 225179981368524800 11048500002802982353 10570750000000000000000 qz18 (BSN.isNear_log_sfrac 13 1 11551488463034085 4503599627370496 500000000126849 42283000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz337) Bool.false 24225227133228857425920 9444732965739290427392 1000000000253698 84566000000000000000 11551488463034085 4503599627370496 500000000126849 42283000000000000000 (BSN.log_rat_reduce_isNear 13 1 3 26 16 127272 262144 24973259072661432 36028797018963968 84566 1000000000000000 rfl rfl rfl rfl (ep225 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep227 := nat_lit 94047766119795408959594941374163216

noncomputable def ep228 := nat_lit 31901471898837980949691369446728269824

noncomputable def ep229 := nat_lit 478522078482569714245370541700924047360

noncomputable def ep230 := BSN.cos_dyadic_bound_f 553779814 1073741824 2 1 524288 169298 ep227 ep228 ep227 ep227 ep229 ep227 456090 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 553779814) qz292 0 1 ep227 ep228 ep227 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 553779814) qz293 0 1 ep227 ep229 ep227 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz338 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 7428847) (@Nat.cast Real Real.instNatCast 32768))

noncomputable abbrev qz339 := (@Nat.cast Real Real.instNatCast 4722366482869645213696)

noncomputable def ep231 := @Enclosure.Real.IsNear.cos_image qz55 qz338 Bool.false 7428847 32768 549 524288 Bool.false 456090 524288 1 84566 (@Enclosure.Real.IsNear.recentre' qz55 Bool.false 51050648113532835249 225179981368524800 11048500002802982353 10570750000000000000000 7428847 32768 549 524288 (ep226 rfl) rfl) (Enclosure.sfrac_false_div 7428847 32768) (BSN.cos_reduce0 qz338 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 2435549381537482932224) qz339) 226375608064910080 72057594037927936 Bool.false 456090 524288 36 1000000000000000 169132 84566 (BSN.sin_reduce_arg_pos_rat_q0 7428847 32768 226375608064910080 72057594037927936 36 2435549381537482932224 4722366482869645213696 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 456090 524288 2435549381537482932224 4722366482869645213696 553779814 1073741824 169298 169132 (ep230 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep232 := BSN.sin_dyadic_bound_f 553779814 1073741824 2 1 524288 169298 ep227 ep103 ep227 ep227 ep104 ep227 258571 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 553779814) qz287 0 1 ep227 ep103 ep227 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 553779814) qz288 0 1 ep227 ep104 ep227 rfl rfl rfl rfl) rfl rfl

noncomputable def ep233 := @Enclosure.Real.IsNear.sin_image qz55 qz338 Bool.false 7428847 32768 549 524288 Bool.false 258571 524288 1 84566 (@Enclosure.Real.IsNear.recentre' qz55 Bool.false 51050648113532835249 225179981368524800 11048500002802982353 10570750000000000000000 7428847 32768 549 524288 (ep226 rfl) rfl) (Enclosure.sfrac_false_div 7428847 32768) (BSN.sin_reduce0 qz338 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 2435549381537482932224) qz339) 226375608064910080 72057594037927936 Bool.false 258571 524288 36 1000000000000000 169132 84566 (BSN.sin_reduce_arg_pos_rat_q0 7428847 32768 226375608064910080 72057594037927936 36 2435549381537482932224 4722366482869645213696 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 258571 524288 2435549381537482932224 4722366482869645213696 553779814 1073741824 169298 169132 (ep232 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz340 := (@Enclosure.Real.IsNear.recentre' qz54 Bool.false 145411 524288 1 524288 145411 524288 1 524288 (ep224 rfl rfl) rfl)

noncomputable def ep234 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz54 (Real.cos qz55)) (@HMul.hMul Real Real Real qz0 qz54 (@Neg.neg Real Real.instNeg (Real.sin qz55))) Bool.false 33160251495 137438953472 1716452929501 5811331269656576 Bool.true 37599067681 274877906944 3424554163125 11622662539313152 (@Enclosure.Real.IsNear.mulLit_ff qz54 (Real.cos qz55) 145411 524288 1 524288 228045 262144 23475511 22168469504 33160251495 137438953472 1716452929501 5811331269656576 qz340 (@Enclosure.Real.IsNear.recentre' (Real.cos qz55) Bool.false 456090 524288 46951022 44336939008 228045 262144 23475511 22168469504 (ep231 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz54 (@Neg.neg Real Real.instNeg (Real.sin qz55)) 145411 524288 1 524288 258571 524288 23475511 22168469504 37599067681 274877906944 3424554163125 11622662539313152 qz340 (@Enclosure.Real.IsNear.neg (Real.sin qz55) Bool.false 258571 524288 23475511 22168469504 (@Enclosure.Real.IsNear.recentre' (Real.sin qz55) Bool.false 258571 524288 46951022 44336939008 258571 524288 23475511 22168469504 (ep233 rfl rfl) rfl)) rfl)

noncomputable def ep235 := @ep155 33160251495 137438953472 1716452929501 5811331269656576 Bool.true 37599067681 274877906944 3424554163125 11622662539313152 Bool.false 1077519151529564569600 7839983675 274877906944 60341348005867 11622662539313152 Bool.false 959900143471881617408 27936771031 274877906944 60359754472295 11622662539313152 (ep156 (BSN.head_sum_c_succ qz5 12 13 rfl rfl) (ep222 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep223 ep234) rfl rfl

noncomputable abbrev qz341 := (@Nat.cast Real Real.instNatCast 14)

noncomputable abbrev qz56 := (@Inv.inv Real Real.instInv (Real.sqrt qz341))

noncomputable abbrev qz542 := (Real.log (Enclosure.sfrac Bool.false 14 1))

noncomputable abbrev qz57 := (@HMul.hMul Real Real Real qz267 qz284 qz542)

noncomputable def ep236 := @Enclosure.Complex.IsNear.of_eq qz41 (Complex.mk (@HMul.hMul Real Real Real qz0 qz56 (Real.cos qz57)) (@HMul.hMul Real Real Real qz0 qz56 (@Neg.neg Real Real.instNeg (Real.sin qz57)))) Bool.false 26039946519 137438953472 103285975413 363208204353536 Bool.true 25906551327 137438953472 206566919149 726416408707072 (BSN.cpow_neg_s_mk qz13 88388 1000 14 qz14 rfl)

noncomputable abbrev qz342 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 14) qz15)

noncomputable def ep237 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz341) 1961707 524288 1 524288 70060 70061 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz341) (Real.sqrt qz342) Bool.false 1961707 524288 1 524288 (BSN.sqrt_natCast_div_one 14) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz342) Bool.false 1961707 524288 1 524288 1961707 524288 1 524288 (BSN.sqrt_enclosure 14 1 980853 980854 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep238 := BSN.log_dyadic_bound 6 22 5 4 51857700491520 262144 84566 1346332575744 176359680 146699 28 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 6) (BSN.artanhQ 22) 0 4 1346332575744 51857700491520 176359680 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep239 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz542 88388 1000 0 1 11885241781671653 4503599627370496 500000000126849 42283000000000000000 262628187649598516341 1125899906842624000 11048500002802982353 10570750000000000000000 qz18 (BSN.isNear_log_sfrac 14 1 11885241781671653 4503599627370496 500000000126849 42283000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz342) Bool.false 24925158572916270432256 9444732965739290427392 1000000000253698 84566000000000000000 11885241781671653 4503599627370496 500000000126849 42283000000000000000 (BSN.log_rat_reduce_isNear 14 1 3 28 16 146699 262144 24973259072661432 36028797018963968 84566 1000000000000000 rfl rfl rfl rfl (ep238 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep240 := nat_lit 1115003637828047851546471038990059545302552843294584287809599142298173604096

noncomputable def ep241 := nat_lit 249195904387015738746607815393010191773655502722037177242191347336642816

noncomputable def ep242 := nat_lit 3344512521675369523161919901339392615524111218878308789074313044199847526656

noncomputable def ep243 := BSN.cos_dyadic_bound_f 840557858 1073741824 3 2 524288 169298 ep240 ep73 ep241 ep242 ep75 ep241 371678 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 840557858) qz292 0 2 ep240 ep73 ep241 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 840557858) qz293 0 2 ep242 ep75 ep241 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz343 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 122295779) qz23)

noncomputable def ep244 := @Enclosure.Real.IsNear.cos_image qz57 qz343 Bool.false 122295779 524288 549 524288 Bool.false 371678 524288 1 84566 (@Enclosure.Real.IsNear.recentre' qz57 Bool.false 262628187649598516341 1125899906842624000 11048500002802982353 10570750000000000000000 122295779 524288 549 524288 (ep239 rfl) rfl) (Enclosure.sfrac_false_div 122295779 524288) (BSN.cos_reduce0 qz343 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 59149000900239706554368) qz25) 226375608064910080 72057594037927936 Bool.false 371678 524288 37 1000000000000000 169132 84566 (BSN.sin_reduce_arg_pos_rat_q0 122295779 524288 226375608064910080 72057594037927936 37 59149000900239706554368 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 371678 524288 59149000900239706554368 75557863725914323419136 840557858 1073741824 169298 169132 (ep243 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep245 := nat_lit 499195256775358131754188368043770896

noncomputable def ep246 := BSN.sin_dyadic_bound_f 840557858 1073741824 2 1 524288 169298 ep245 ep103 ep245 ep245 ep104 ep245 369774 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 840557858) qz287 0 1 ep245 ep103 ep245 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 840557858) qz288 0 1 ep245 ep104 ep245 rfl rfl rfl rfl) rfl rfl

noncomputable def ep247 := @Enclosure.Real.IsNear.sin_image qz57 qz343 Bool.false 122295779 524288 549 524288 Bool.false 369774 524288 1 84566 (@Enclosure.Real.IsNear.recentre' qz57 Bool.false 262628187649598516341 1125899906842624000 11048500002802982353 10570750000000000000000 122295779 524288 549 524288 (ep239 rfl) rfl) (Enclosure.sfrac_false_div 122295779 524288) (BSN.sin_reduce0 qz343 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 59149000900239706554368) qz25) 226375608064910080 72057594037927936 Bool.false 369774 524288 37 1000000000000000 169132 84566 (BSN.sin_reduce_arg_pos_rat_q0 122295779 524288 226375608064910080 72057594037927936 37 59149000900239706554368 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 369774 524288 59149000900239706554368 75557863725914323419136 840557858 1073741824 169298 169132 (ep246 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz344 := (@Enclosure.Real.IsNear.recentre' qz56 Bool.false 140121 524288 1 524288 140121 524288 1 524288 (ep237 rfl rfl) rfl)

noncomputable def ep248 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz56 (Real.cos qz57)) (@HMul.hMul Real Real Real qz0 qz56 (@Neg.neg Real Real.instNeg (Real.sin qz57))) Bool.false 26039946519 137438953472 103285975413 363208204353536 Bool.true 25906551327 137438953472 206566919149 726416408707072 (@Enclosure.Real.IsNear.mulLit_ff qz56 (Real.cos qz57) 140121 524288 1 524288 185839 262144 23475511 22168469504 26039946519 137438953472 103285975413 363208204353536 qz344 (@Enclosure.Real.IsNear.recentre' (Real.cos qz57) Bool.false 371678 524288 46951022 44336939008 185839 262144 23475511 22168469504 (ep244 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz56 (@Neg.neg Real Real.instNeg (Real.sin qz57)) 140121 524288 1 524288 184887 262144 23475511 22168469504 25906551327 137438953472 206566919149 726416408707072 qz344 (@Enclosure.Real.IsNear.neg (Real.sin qz57) Bool.false 184887 262144 23475511 22168469504 (@Enclosure.Real.IsNear.recentre' (Real.sin qz57) Bool.false 369774 524288 46951022 44336939008 184887 262144 23475511 22168469504 (ep247 rfl rfl) rfl)) rfl)

noncomputable def ep249 := @ep153 26039946519 137438953472 103285975413 363208204353536 Bool.true 25906551327 137438953472 206566919149 726416408707072 Bool.false 8235325147605983297536 59919876713 274877906944 63646499219083 11622662539313152 Bool.true 3281538031015539245056 23876331623 274877906944 63664825178679 11622662539313152 (ep154 (BSN.head_sum_c_succ qz5 13 14 rfl rfl) (ep235 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep236 ep248) rfl rfl

noncomputable abbrev qz345 := (@Nat.cast Real Real.instNatCast 15)

noncomputable abbrev qz58 := (@Inv.inv Real Real.instInv (Real.sqrt qz345))

noncomputable abbrev qz543 := (Real.log (Enclosure.sfrac Bool.false 15 1))

noncomputable abbrev qz59 := (@HMul.hMul Real Real Real qz267 qz284 qz543)

noncomputable def ep250 := @Enclosure.Complex.IsNear.of_eq qz40 (Complex.mk (@HMul.hMul Real Real Real qz0 qz58 (Real.cos qz59)) (@HMul.hMul Real Real Real qz0 qz58 (@Neg.neg Real Real.instNeg (Real.sin qz59)))) Bool.false 58666136383 274877906944 3196251185651 11622662539313152 Bool.true 39943514857 274877906944 3190403193053 11622662539313152 (BSN.cpow_neg_s_mk qz13 88388 1000 15 qz14 rfl)

noncomputable abbrev qz346 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 15) qz15)

noncomputable def ep251 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz345) 2030559 524288 1 524288 67685 67686 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz345) (Real.sqrt qz346) Bool.false 2030559 524288 1 524288 (BSN.sqrt_natCast_div_one 15) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz346) Bool.false 2030559 524288 1 524288 2030559 524288 1 524288 (BSN.sqrt_enclosure 15 1 1015279 1015280 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep252 := BSN.log_dyadic_bound 7 23 6 5 430628584065881355 262144 84566 14087658153505881 266939110305 164785 30 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 7) (BSN.artanhQ 23) 0 5 14087658153505881 430628584065881355 266939110305 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep253 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz543 88388 1000 0 1 12195956895733477 4503599627370496 500000000126849 42283000000000000000 269494059525022641269 1125899906842624000 11048500002802982353 10570750000000000000000 qz18 (BSN.isNear_log_sfrac 15 1 12195956895733477 4503599627370496 500000000126849 42283000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz346) Bool.false 25576775395801252757504 9444732965739290427392 1000000000253698 84566000000000000000 12195956895733477 4503599627370496 500000000126849 42283000000000000000 (BSN.log_rat_reduce_isNear 15 1 3 30 16 164785 262144 24973259072661432 36028797018963968 84566 1000000000000000 rfl rfl rfl rfl (ep252 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep254 := nat_lit 169715390882963839534495182675993616

noncomputable def ep255 := BSN.cos_dyadic_bound_f 641845214 1073741824 2 1 524288 169298 ep254 ep228 ep254 ep254 ep229 ep254 433373 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 641845214) qz292 0 1 ep254 ep228 ep254 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 641845214) qz293 0 1 ep254 ep229 ep254 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz347 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 62746475) qz16)

noncomputable def ep256 := @Enclosure.Real.IsNear.cos_image qz59 qz347 Bool.false 62746475 262144 549 524288 Bool.false 433373 524288 1 84566 (@Enclosure.Real.IsNear.recentre' qz59 Bool.false 269494059525022641269 1125899906842624000 11048500002802982353 10570750000000000000000 62746475 262144 549 524288 (ep253 rfl) rfl) (Enclosure.sfrac_false_div 62746475 262144) (BSN.cos_reduce0 qz347 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 22582920835684798300160) qz19) 226375608064910080 72057594037927936 Bool.false 433373 524288 38 1000000000000000 169132 84566 (BSN.sin_reduce_arg_pos_rat_q0 62746475 262144 226375608064910080 72057594037927936 38 22582920835684798300160 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 433373 524288 22582920835684798300160 37778931862957161709568 641845214 1073741824 169298 169132 (ep255 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep257 := BSN.sin_dyadic_bound_f 641845214 1073741824 2 1 524288 169298 ep254 ep103 ep254 ep254 ep104 ep254 295067 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 641845214) qz287 0 1 ep254 ep103 ep254 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 641845214) qz288 0 1 ep254 ep104 ep254 rfl rfl rfl rfl) rfl rfl

noncomputable def ep258 := @Enclosure.Real.IsNear.sin_image qz59 qz347 Bool.false 62746475 262144 549 524288 Bool.false 295067 524288 1 84566 (@Enclosure.Real.IsNear.recentre' qz59 Bool.false 269494059525022641269 1125899906842624000 11048500002802982353 10570750000000000000000 62746475 262144 549 524288 (ep253 rfl) rfl) (Enclosure.sfrac_false_div 62746475 262144) (BSN.sin_reduce0 qz347 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 22582920835684798300160) qz19) 226375608064910080 72057594037927936 Bool.false 295067 524288 38 1000000000000000 169132 84566 (BSN.sin_reduce_arg_pos_rat_q0 62746475 262144 226375608064910080 72057594037927936 38 22582920835684798300160 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 295067 524288 22582920835684798300160 37778931862957161709568 641845214 1073741824 169298 169132 (ep257 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz348 := (@Enclosure.Real.IsNear.recentre' qz58 Bool.false 135371 524288 1 524288 135371 524288 1 524288 (ep251 rfl rfl) rfl)

noncomputable def ep259 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz58 (Real.cos qz59)) (@HMul.hMul Real Real Real qz0 qz58 (@Neg.neg Real Real.instNeg (Real.sin qz59))) Bool.false 58666136383 274877906944 3196251185651 11622662539313152 Bool.true 39943514857 274877906944 3190403193053 11622662539313152 (@Enclosure.Real.IsNear.mulLit_ff qz58 (Real.cos qz59) 135371 524288 1 524288 433373 524288 23475511 22168469504 58666136383 274877906944 3196251185651 11622662539313152 qz348 (@Enclosure.Real.IsNear.recentre' (Real.cos qz59) Bool.false 433373 524288 46951022 44336939008 433373 524288 23475511 22168469504 (ep256 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz58 (@Neg.neg Real Real.instNeg (Real.sin qz59)) 135371 524288 1 524288 295067 524288 23475511 22168469504 39943514857 274877906944 3190403193053 11622662539313152 qz348 (@Enclosure.Real.IsNear.neg (Real.sin qz59) Bool.false 295067 524288 23475511 22168469504 (@Enclosure.Real.IsNear.recentre' (Real.sin qz59) Bool.false 295067 524288 46951022 44336939008 295067 524288 23475511 22168469504 (ep258 rfl rfl) rfl)) rfl)

noncomputable def ep260 := @ep151 58666136383 274877906944 3196251185651 11622662539313152 Bool.true 39943514857 274877906944 3190403193053 11622662539313152 Bool.false 32596675072662253338624 14823251637 34359738368 33421375202367 5811331269656576 Bool.true 17542665821909805957120 3988740405 17179869184 16713807092933 2905665634828288 (ep152 (BSN.head_sum_c_succ qz5 14 15 rfl rfl) (ep249 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep250 ep259) rfl rfl

noncomputable abbrev qz349 := (@Nat.cast Real Real.instNatCast 16)

noncomputable abbrev qz60 := (@Inv.inv Real Real.instInv (Real.sqrt qz349))

noncomputable abbrev qz544 := (Real.log (Enclosure.sfrac Bool.false 16 1))

noncomputable abbrev qz61 := (@HMul.hMul Real Real Real qz267 qz284 qz544)

noncomputable def ep261 := @Enclosure.Complex.IsNear.of_eq qz39 (Complex.mk (@HMul.hMul Real Real Real qz0 qz60 (Real.cos qz61)) (@HMul.hMul Real Real Real qz0 qz60 (@Neg.neg Real Real.instNeg (Real.sin qz61)))) Bool.false 68705976419 274877906944 3099146461279 11622662539313152 Bool.true 1329191011 274877906944 3077410969695 11622662539313152 (BSN.cpow_neg_s_mk qz13 88388 1000 16 qz14 rfl)

noncomputable abbrev qz350 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 16) qz15)

noncomputable def ep262 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz349) 2097153 524288 1 524288 65535 65536 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz349) (Real.sqrt qz350) Bool.false 2097153 524288 1 524288 (BSN.sqrt_natCast_div_one 16) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz350) Bool.false 2097153 524288 1 524288 2097153 524288 1 524288 (BSN.sqrt_enclosure 16 1 1048576 1048577 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep263 := BSN.log_dyadic_bound 0 32 1 0 1 262144 84566 0 1 0 32 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 0) (BSN.artanhQ 32) 0 0 rfl) rfl rfl rfl

noncomputable def ep264 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz544 88388 1000 0 1 3121657384082679 1125899906842624 125000000042283 10570750000000000000 68979263216074957863 281474976710656000 2762125000934327451 2642687500000000000000 qz18 (BSN.isNear_log_sfrac 16 1 3121657384082679 1125899906842624 125000000042283 10570750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz350) Bool.false 26186360105375033720832 9444732965739290427392 1000000000338264 84566000000000000000 3121657384082679 1125899906842624 125000000042283 10570750000000000000 (BSN.log_rat_reduce_isNear 16 1 4 32 32 0 262144 24973259072661432 36028797018963968 84566 1000000000000000 rfl rfl rfl rfl (ep263 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep265 := BSN.cos_dyadic_bound_f 20771481 1073741824 1 0 524288 169298 0 1 1 0 1 1 524189 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 20771481) qz292 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 20771481) qz293 0 0 rfl) rfl rfl

noncomputable abbrev qz351 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 64241945) qz16)

noncomputable def ep266 := @Enclosure.Real.IsNear.cos_image qz61 qz351 Bool.false 64241945 262144 549 524288 Bool.false 524189 524288 1 84566 (@Enclosure.Real.IsNear.recentre' qz61 Bool.false 68979263216074957863 281474976710656000 2762125000934327451 2642687500000000000000 64241945 262144 549 524288 (ep264 rfl) rfl) (Enclosure.sfrac_false_div 64241945 262144) (BSN.cos_reduce0 qz351 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 730831545213827153920) qz19) 226375608064910080 72057594037927936 Bool.false 524189 524288 39 1000000000000000 169132 84566 (BSN.sin_reduce_arg_pos_rat_q0 64241945 262144 226375608064910080 72057594037927936 39 730831545213827153920 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 524189 524288 730831545213827153920 37778931862957161709568 20771481 1073741824 169298 169132 (ep265 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep267 := BSN.sin_dyadic_bound_f 20771481 1073741824 1 0 524288 169298 0 1 1 0 1 1 10141 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 20771481) qz287 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 20771481) qz288 0 0 rfl) rfl rfl

noncomputable def ep268 := @Enclosure.Real.IsNear.sin_image qz61 qz351 Bool.false 64241945 262144 549 524288 Bool.false 10141 524288 1 84566 (@Enclosure.Real.IsNear.recentre' qz61 Bool.false 68979263216074957863 281474976710656000 2762125000934327451 2642687500000000000000 64241945 262144 549 524288 (ep264 rfl) rfl) (Enclosure.sfrac_false_div 64241945 262144) (BSN.sin_reduce0 qz351 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 730831545213827153920) qz19) 226375608064910080 72057594037927936 Bool.false 10141 524288 39 1000000000000000 169132 84566 (BSN.sin_reduce_arg_pos_rat_q0 64241945 262144 226375608064910080 72057594037927936 39 730831545213827153920 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 10141 524288 730831545213827153920 37778931862957161709568 20771481 1073741824 169298 169132 (ep267 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz352 := (@Enclosure.Real.IsNear.recentre' qz60 Bool.false 131071 524288 1 524288 131071 524288 1 524288 (ep262 rfl rfl) rfl)

noncomputable def ep269 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz60 (Real.cos qz61)) (@HMul.hMul Real Real Real qz0 qz60 (@Neg.neg Real Real.instNeg (Real.sin qz61))) Bool.false 68705976419 274877906944 3099146461279 11622662539313152 Bool.true 1329191011 274877906944 3077410969695 11622662539313152 (@Enclosure.Real.IsNear.mulLit_ff qz60 (Real.cos qz61) 131071 524288 1 524288 524189 524288 23475511 22168469504 68705976419 274877906944 3099146461279 11622662539313152 qz352 (@Enclosure.Real.IsNear.recentre' (Real.cos qz61) Bool.false 524189 524288 46951022 44336939008 524189 524288 23475511 22168469504 (ep266 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz60 (@Neg.neg Real Real.instNeg (Real.sin qz61)) 131071 524288 1 524288 10141 524288 23475511 22168469504 1329191011 274877906944 3077410969695 11622662539313152 qz352 (@Enclosure.Real.IsNear.neg (Real.sin qz61) Bool.false 10141 524288 23475511 22168469504 (@Enclosure.Real.IsNear.recentre' (Real.sin qz61) Bool.false 10141 524288 46951022 44336939008 10141 524288 23475511 22168469504 (ep268 rfl rfl) rfl)) rfl)

noncomputable def ep270 := @ep149 68705976419 274877906944 3099146461279 11622662539313152 Bool.true 1329191011 274877906944 3077410969695 11622662539313152 Bool.false 6435303758157599211520 187291989515 274877906944 69941896866013 11622662539313152 Bool.true 1119251941558891577344 65149037491 274877906944 69932639341427 11622662539313152 (ep150 (BSN.head_sum_c_succ qz5 15 16 rfl rfl) (ep260 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep261 ep269) rfl rfl

theorem EMRow25.d7 : Enclosure.Complex.IsNear qz38 Bool.false 187291989515 274877906944 69941896866013 11622662539313152 Bool.true 65149037491 274877906944 69932639341427 11622662539313152 := ep148 (BSN.head_sum_c_succ qz5 16 17 rfl rfl) (ep270 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

theorem EMRow25.d8 : @Eq Nat (BSN.factNat (Nat.mul 2 1)) 2 := @Eq.refl Nat 2

theorem EMRow25.d9 : @Eq Nat (Nat.pow 23 1) 23 := @Eq.refl Nat 23

noncomputable def ep271 := nat_lit 252442394366137549805911454671

noncomputable def ep272 := nat_lit 404630043978481643842174976000

noncomputable def ep273 := nat_lit 5734560541723191140673945410711645169

noncomputable def ep274 := nat_lit 723418669399090277991386517145124864000

noncomputable abbrev qz574 := (@instHMul Complex Complex.instMul)

noncomputable abbrev qz545 := qz574

noncomputable abbrev qz353 := qz545

noncomputable abbrev qz62 := qz353

noncomputable abbrev qz546 := (@instHSub Complex Complex.instSub)

noncomputable abbrev qz354 := qz546

noncomputable abbrev qz63 := qz354

noncomputable abbrev qz575 := (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (4 : Complex))

noncomputable abbrev qz576 := (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid))

noncomputable abbrev qz547 := (@HAdd.hAdd Complex Complex Complex qz572 (@HAdd.hAdd Complex Complex Complex qz572 qz575 (@HMul.hMul Complex Complex Complex qz574 Complex.I (@HDiv.hDiv Complex Complex Complex qz576 (↑qz573) (2 : Complex)))) (@Nat.cast Complex Complex.instNatCast 2))

noncomputable abbrev qz355 := qz547

noncomputable abbrev qz64 := (Complex.Stirling.logGammaStirling 1 qz355)

noncomputable abbrev qz548 := (@HAdd.hAdd Complex Complex Complex qz572 qz575 (@HMul.hMul Complex Complex Complex qz574 Complex.I (@HDiv.hDiv Complex Complex Complex qz576 (↑qz573) (2 : Complex))))

noncomputable abbrev qz356 := qz548

noncomputable abbrev qz65 := qz356

noncomputable abbrev qz66 := (@HMul.hMul Real Real Real qz267 (@HDiv.hDiv Real Real Real qz270 qz284 (2 : Real)) (Real.log Real.pi))

noncomputable abbrev qz357 := (@instHSub Real Real.instSub)

noncomputable def ep275 := Complex.re (@HMul.hMul Complex Complex Complex qz62 (Complex.exp (@HMul.hMul Complex Complex Complex qz62 Complex.I ↑(@HSub.hSub Real Real Real qz357 (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz64 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz65 (@Nat.cast Complex Complex.instNatCast j))))) qz66))) (zetaApproximant qz5 1 23))

noncomputable def ep276 := @Enclosure.Real.IsNear.of_eq ep275 (@HSub.hSub Real Real Real qz357 (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz357 (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz64 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz65 (@Nat.cast Complex Complex.instNatCast j))))) qz66)) (Complex.re (zetaApproximant qz5 1 23))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz357 (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz64 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz65 (@Nat.cast Complex Complex.instNatCast j))))) qz66)) (Complex.im (zetaApproximant qz5 1 23))))

noncomputable def ep277 := nat_lit 757335390727670351520063616613

noncomputable def ep278 := @Enclosure.Real.IsNear.subLit_tt_n (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz357 (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz64 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz65 (@Nat.cast Complex Complex.instNatCast j))))) qz66)) (Complex.re (zetaApproximant qz5 1 23))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz357 (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz64 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz65 (@Nat.cast Complex Complex.instNatCast j))))) qz66)) (Complex.im (zetaApproximant qz5 1 23))) ep277

noncomputable def ep279 := nat_lit 1213890131935444931526524928000

noncomputable def ep280 := nat_lit 3433941894363976797759224956441241287

noncomputable def ep281 := nat_lit 434051201639454166794831910287074918400

noncomputable def ep282 := nat_lit 6069450659677224657632624640

noncomputable def ep283 := nat_lit 2123259584355589576606965620545567

noncomputable def ep284 := nat_lit 135641000512329427123384971964710912000

noncomputable def ep285 := nat_lit 4596559971048154959152106342261882525862157480190353080320

noncomputable def ep286 := @Enclosure.Real.IsNear.mulLit_tf (Real.cos (@HSub.hSub Real Real Real qz357 (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz64 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz65 (@Nat.cast Complex Complex.instNatCast j))))) qz66)) (Complex.re (zetaApproximant qz5 1 23)) 524287 524288 5585579

noncomputable def ep287 := nat_lit 1444505377260298942220699

noncomputable def ep288 := nat_lit 2315311683531656134656000

noncomputable def ep289 := nat_lit 247786230821342628485360477

noncomputable def ep290 := nat_lit 32632774638256338780553216000

noncomputable def ep291 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HSub.hSub Real Real Real qz357 (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz64 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz65 (@Nat.cast Complex Complex.instNatCast j))))) qz66)) Bool.true 524287 524288 11171158

noncomputable abbrev qz358 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 9470771) (@Nat.cast Real Real.instNatCast 131072))

noncomputable def ep292 := @Enclosure.Real.IsNear.cos_image (@HSub.hSub Real Real Real qz357 (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz64 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz65 (@Nat.cast Complex Complex.instNatCast j))))) qz66) qz358 Bool.false 9470771 131072 129

noncomputable def ep293 := nat_lit 1662635212800000000000000000

noncomputable def ep294 := @Enclosure.Real.IsNear.recentre' (@HSub.hSub Real Real Real qz357 (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz64 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz65 (@Nat.cast Complex Complex.instNatCast j))))) qz66) Bool.false 488119823163395870753 6755399441055744000 814688522452705988918291 ep293

noncomputable def ep295 := @Enclosure.Real.IsNear.subLit_ff_p (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz64 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz65 (@Nat.cast Complex Complex.instNatCast j))))) qz66 829876700725837500449 6755399441055744000 254092051852705988918291 ep293 1657739037 32768000

noncomputable def ep296 := nat_lit 15994710365418155892834304000

noncomputable def ep297 := nat_lit 2771058688000000000000000000

noncomputable def ep298 := @Enclosure.Complex.IsNear.im_isNear (@HSub.hSub Complex Complex Complex qz63 qz64 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz65 (@Nat.cast Complex Complex.instNatCast j)))) Bool.true 156383031797185514399 2251799813685248000 765365730003722881494361 ep297 Bool.false 829876700725837500449 6755399441055744000

noncomputable def ep299 := @Enclosure.Complex.IsNear.subLitP qz64 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz65 (@Nat.cast Complex Complex.instNatCast j))) Bool.true 139319809672866583399 2251799813685248000 748981729976012294614361 ep297 Bool.false 850870191577335300449 6755399441055744000 234431251851043353705491

noncomputable def ep300 := nat_lit 352143281864436555022934786757885952

noncomputable def ep301 := nat_lit 233589525009521149649803038943084544

noncomputable abbrev qz577 := (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (2 : Complex))

noncomputable abbrev qz549 := qz577

noncomputable abbrev qz359 := (@HSub.hSub Complex Complex Complex qz546 qz547 qz549)

noncomputable abbrev qz360 := (Complex.log qz547)

noncomputable abbrev qz67 := (@HSub.hSub Complex Complex Complex qz354 (@HMul.hMul Complex Complex Complex qz353 qz359 qz360) qz355)

noncomputable abbrev qz361 := qz549

noncomputable abbrev qz68 := (@HMul.hMul Complex Complex Complex qz353 qz361 ↑(Real.log qz271))

noncomputable abbrev qz550 := qz576

noncomputable abbrev qz362 := qz550

noncomputable abbrev qz69 := qz362

noncomputable abbrev qz70 := (@instHMul Nat instMulNat)

noncomputable abbrev qz551 := (@instHPow Complex Int (@ZPow.toPow Complex (@DivInvMonoid.toZPow Complex Complex.instDivInvMonoid)))

noncomputable abbrev qz363 := qz551

noncomputable abbrev qz71 := qz363

noncomputable abbrev qz72 := qz355

noncomputable abbrev qz364 := (@OfNat.ofNat Int 1 (@instOfNat 1))

noncomputable abbrev qz73 := qz364

noncomputable abbrev qz365 := (@OfNat.ofNat Int 2 (@instOfNat 2))

noncomputable abbrev qz74 := qz365

noncomputable abbrev qz366 := (@instHSub Int Int.instSub)

noncomputable abbrev qz367 := (@instHMul Int Int.instMul)

noncomputable def ep302 := @Enclosure.Complex.IsNear.of_eq qz64 (@HAdd.hAdd Complex Complex Complex qz4 (@HAdd.hAdd Complex Complex Complex qz4 qz67 qz68) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz63 (@HMul.hMul Complex Complex Complex qz62 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz71 qz72 (@HSub.hSub Int Int Int qz366 qz73 (@HMul.hMul Int Int Int qz367 qz74 (@Nat.cast Int instNatCastInt k)))))) Bool.true 139319809672866583399

noncomputable def ep303 := @Enclosure.Complex.IsNear.addLitP (@HAdd.hAdd Complex Complex Complex qz4 qz67 qz68) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz63 (@HMul.hMul Complex Complex Complex qz62 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz71 qz72 (@HSub.hSub Int Int Int qz366 qz73 (@HMul.hMul Int Int Int qz367 qz74 (@Nat.cast Int instNatCastInt k))))) Bool.true 139320025288534807399 2251799813685248000

noncomputable def ep304 := nat_lit 2393496104919625737079846076416

noncomputable def ep305 := nat_lit 1827229822982954885127394557952000

noncomputable def ep306 := @ep303 1428568355723340697 5285375000000000000000 Bool.false 283627632267485763019 2251799813685248000 1192350001876054427 8456600000000000000000 Bool.false 1645017 17179869184 3 17179869184 Bool.true 12116646883 6442450944000 22097 6442450944000 Bool.true ep304 139319809672866583399 2251799813685248000 748981729976012294614361 ep297 Bool.false ep305

noncomputable def ep307 := @Enclosure.Complex.IsNear.addLitP qz67 qz68 Bool.true 141389288992140055399 2251799813685248000 11267250001304303701 42283000000000000000000

noncomputable def ep308 := nat_lit 18260954354618834275401728

noncomputable def ep309 := @ep307 Bool.false 283627632267485763019 2251799813685248000 1192350001876054427 8456600000000000000000 Bool.false 120447 131072 1 262144 Bool.false 0 1 0 1 Bool.true ep308 139320025288534807399 2251799813685248000 1428568355723340697 5285375000000000000000 Bool.false 283627632267485763019 283627632267485763019 2251799813685248000

noncomputable abbrev qz75 := (@HMul.hMul Complex Complex Complex qz353 qz359 qz360)

noncomputable def ep310 := @Enclosure.Complex.IsNear.subLitP qz75 qz72 Bool.true 136322739411348247399 2251799813685248000 11267250001304303701 42283000000000000000000 Bool.false 383143673233491613131

noncomputable def ep311 := @ep310 2251799813685248000 1192350001876054427 8456600000000000000000 Bool.false 9000 4000 0 1 Bool.false 176776 4000 0 1 Bool.true 565557155968560221596000 141389288992140055399 2251799813685248000 11267250001304303701 42283000000000000000000 Bool.false 1134510529069943052076000 283627632267485763019 2251799813685248000 1192350001876054427 8456600000000000000000

noncomputable abbrev qz76 := qz359

noncomputable abbrev qz77 := qz360

noncomputable def ep312 := @Enclosure.Complex.IsNear.mul qz76 qz77 Bool.true 136322739411348247399 2251799813685248000 11267250001304303701 42283000000000000000000 Bool.false 383143673233491613131 2251799813685248000 1192350001876054427

noncomputable abbrev qz78 := (Complex.re qz359)

noncomputable abbrev qz79 := (Complex.re qz360)

noncomputable abbrev qz80 := (Complex.im qz359)

noncomputable abbrev qz81 := (Complex.im qz360)

noncomputable def ep313 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 qz78 qz79) (@HMul.hMul Real Real Real qz0 qz80 qz81) 119476813676869061 18014398509481984 175000000295981 33826400000000000000 18907167640119610003 281474976710656000

noncomputable def ep314 := nat_lit 306971519207536598107093500220669952

noncomputable def ep315 := @Enclosure.Real.IsNear.mulLit_ff qz78 qz79 7000 4000 0 1 17068116239552723 4503599627370496 25000000042283 8456600000000000000

noncomputable def ep316 := @Enclosure.Complex.IsNear.re_isNear qz76 Bool.false 7000 4000 0 1 Bool.false 176776 4000 0 1

noncomputable abbrev qz368 := (Enclosure.sfrac Bool.false 176776 4000)

noncomputable abbrev qz82 := qz368

noncomputable def ep317 := @Enclosure.Complex.IsNear.of_eq qz76 (Complex.mk (Enclosure.sfrac Bool.false 7000 4000) qz82) Bool.false 7000 4000 0 1 Bool.false 176776 4000 0

noncomputable abbrev qz369 := (Enclosure.sfrac Bool.false 9000 4000)

noncomputable abbrev qz83 := qz369

noncomputable abbrev qz370 := (Complex.log (Complex.mk qz83 qz82))

noncomputable def ep318 := @Enclosure.Complex.IsNear.of_eq qz77 qz370 Bool.false 17068116239552723 4503599627370496 25000000042283 8456600000000000000 Bool.false 855644098299299 562949953421312 500000000042283 84566000000000000000

noncomputable def ep319 := nat_lit 635845205240609391031789047472803105248161392803457011794453470450906455375572602728609089761775607076114923520

noncomputable def ep320 := nat_lit 22115255609893088642736053231877506976201412914136884778055564371615889631045546043139032674287937586414485504

noncomputable def ep321 := nat_lit 525897041232995796544638717960618294729378022107211442356684574867799602066082088706993177617211137720320

noncomputable def ep322 := BSN.log_dyadic_bound 14946754176 47714754176 6 5 ep319 524288 169132 ep320 ep321 339893 62661508352 32768000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 14946754176) (BSN.artanhQ 47714754176) 0 5 ep320 ep319 ep321 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz84 := (Enclosure.sfrac Bool.false 1 2)

noncomputable abbrev qz371 := (Enclosure.Real.IsNear.const Bool.false 1 2)

noncomputable abbrev qz372 := (@Nat.cast Real Real.instNatCast 16000000)

noncomputable abbrev qz552 := (Real.log (Enclosure.sfrac Bool.false 31330754176 16000000))

noncomputable def ep323 := @Enclosure.Real.IsNear.mulLit_ff qz84 qz552 1 2 0 1 17068116239552723 2251799813685248 25000000042283 4228300000000000000 17068116239552723 4503599627370496 25000000042283 8456600000000000000 qz371 (BSN.isNear_log_sfrac 31330754176 16000000 17068116239552723 2251799813685248 25000000042283 4228300000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 31330754176) qz372)) Bool.false 143177736432041888579584 18889465931478580854784 1000000001691320 169132000000000000000 17068116239552723 2251799813685248 25000000042283 4228300000000000000 (BSN.log_rat_reduce_isNear 31330754176 16000000 10 62661508352 32768000000 339893 524288 24973259072661432 36028797018963968 169132 1000000000000000 rfl rfl rfl rfl (ep322 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep324 := BSN.arctan_dyadic_bound_f 9000 176776 1 0 524288 169132 0 1 1 0 1 1 26669 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 9000) (BSN.arctanEvenQ 176776) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 9000) (BSN.arctanOddQ 176776) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz85 := (@HMul.hMul Real Real Real qz267 (Enclosure.sfrac Bool.false 1 2) Real.pi)

noncomputable abbrev qz86 := (@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 2) Real.pi 1 2 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 qz371 BSN.pi_near_15 rfl)

noncomputable abbrev qz373 := (Real.arctan (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 9000) (@Nat.cast Real Real.instNatCast 176776)))

noncomputable def ep325 := @Enclosure.Real.IsNear.subLit_ff_p qz85 qz373 884279719003555 562949953421312 1 2000000000000000 26669 524288 1 169132 448603933009142874112 855644098299299 562949953421312 500000000042283 84566000000000000000 qz86 (ep324 rfl) rfl rfl

noncomputable abbrev qz374 := (Real.arctan (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 176776) (@Nat.cast Real Real.instNatCast 9000)))

noncomputable def ep326 := @Enclosure.Complex.IsNear.re_isNear qz77 Bool.false 17068116239552723 4503599627370496 25000000042283 8456600000000000000 Bool.false 855644098299299 562949953421312 500000000042283 84566000000000000000 (ep318 (@congrArg Complex Complex qz72 (Complex.mk qz83 qz82) Complex.log (BSN.w_shift_mk qz13 Bool.false 88388 1000 2 qz14 rfl)) (@Enclosure.Complex.IsNear.of_parts qz370 Bool.false 17068116239552723 4503599627370496 25000000042283 8456600000000000000 Bool.false 855644098299299 562949953421312 500000000042283 84566000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz370) (@HMul.hMul Real Real Real qz0 qz84 qz552) Bool.false 17068116239552723 4503599627370496 25000000042283 8456600000000000000 (Enclosure.clog_re_eq 9000 176776 4000 31330754176 16000000 rfl rfl rfl) (ep323 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz370) qz374 Bool.false 855644098299299 562949953421312 500000000042283 84566000000000000000 (Enclosure.clog_im_eq 9000 176776 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz374 (@HSub.hSub Real Real Real qz357 qz85 qz373) Bool.false 855644098299299 562949953421312 500000000042283 84566000000000000000 (BSN.arctan_recip 176776 9000 rfl rfl) ep325))))

noncomputable def ep327 := @Enclosure.Real.IsNear.mulLit_ff qz80 qz81 176776 4000 0 1 855644098299299 562949953421312 500000000042283 84566000000000000000

noncomputable def ep328 := @Enclosure.Complex.IsNear.im_isNear qz76 Bool.false 7000 4000 0 1 Bool.false 176776 4000 0 1

noncomputable def ep329 := @Enclosure.Complex.IsNear.im_isNear qz77 Bool.false 17068116239552723 4503599627370496 25000000042283 8456600000000000000 Bool.false 855644098299299 562949953421312 500000000042283 84566000000000000000 (ep318 (@congrArg Complex Complex qz72 (Complex.mk qz83 qz82) Complex.log (BSN.w_shift_mk qz13 Bool.false 88388 1000 2 qz14 rfl)) (@Enclosure.Complex.IsNear.of_parts qz370 Bool.false 17068116239552723 4503599627370496 25000000042283 8456600000000000000 Bool.false 855644098299299 562949953421312 500000000042283 84566000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz370) (@HMul.hMul Real Real Real qz0 qz84 qz552) Bool.false 17068116239552723 4503599627370496 25000000042283 8456600000000000000 (Enclosure.clog_re_eq 9000 176776 4000 31330754176 16000000 rfl rfl rfl) (ep323 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz370) qz374 Bool.false 855644098299299 562949953421312 500000000042283 84566000000000000000 (Enclosure.clog_im_eq 9000 176776 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz374 (@HSub.hSub Real Real Real qz357 qz85 qz373) Bool.false 855644098299299 562949953421312 500000000042283 84566000000000000000 (BSN.arctan_recip 176776 9000 rfl rfl) ep325))))

noncomputable abbrev qz375 := (Enclosure.Real.IsNear.const Bool.false 176776 4000)

noncomputable abbrev qz87 := (@ep317 1 (BSN.w_sub_half_mk qz284 Bool.false 88388 1000 2 qz286 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7000 4000) qz368 Bool.false 7000 4000 0 1 Bool.false 176776 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 7000 4000) qz375))

noncomputable def ep330 := @ep313 11048500000934327451 42283000000000000000000 ep314 136322739411348247399 2251799813685248000 11267250001304303701 42283000000000000000000 (@ep315 119476813676869061 18014398509481984 175000000295981 33826400000000000000 (ep316 qz87) ep326 rfl) (@ep327 18907167640119610003 281474976710656000 11048500000934327451 42283000000000000000000 (ep328 qz87) ep329 rfl) rfl

noncomputable def ep331 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz78 qz81) (@HMul.hMul Real Real Real qz0 qz80 qz79) 5989508688095093 2251799813685248 3500000000295981 338264000000000000000 377154164545396520131 2251799813685248000

noncomputable def ep332 := nat_lit 862762852001857955581357805417791488

noncomputable def ep333 := @Enclosure.Real.IsNear.mulLit_ff qz78 qz81 7000 4000 0 1 855644098299299 562949953421312 500000000042283 84566000000000000000

noncomputable def ep334 := @Enclosure.Real.IsNear.mulLit_ff qz80 qz79 176776 4000 0 1 17068116239552723 4503599627370496 25000000042283 8456600000000000000

noncomputable def ep335 := @ep331 552425000934327451 4228300000000000000000 ep332 383143673233491613131 2251799813685248000 1192350001876054427 8456600000000000000000 (@ep333 5989508688095093 2251799813685248 3500000000295981 338264000000000000000 (ep316 qz87) ep329 rfl) (@ep334 377154164545396520131 2251799813685248000 552425000934327451 4228300000000000000000 (ep328 qz87) ep326 rfl) rfl

noncomputable def ep336 := @Enclosure.Complex.IsNear.of_eq qz72 (Complex.mk qz83 qz82) Bool.false 9000 4000 0 1 Bool.false 176776 4000 0 1 (BSN.w_shift_mk qz13 Bool.false 88388 1000 2 qz14 rfl)

noncomputable abbrev qz376 := (ep336 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 9000 4000) (Enclosure.sfrac Bool.false 176776 4000) Bool.false 9000 4000 0 1 Bool.false 176776 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 9000 4000) (Enclosure.Real.IsNear.const Bool.false 176776 4000)))

noncomputable abbrev qz88 := qz376

noncomputable def ep337 := ep311 (@ep312 8456600000000000000000 (ep330 rfl) (ep335 rfl)) qz88 rfl rfl rfl rfl rfl rfl

noncomputable abbrev qz89 := qz361

noncomputable def ep338 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re qz89) (Complex.re ↑qz2)) (@HMul.hMul Real Real Real qz0 (Complex.im qz89) (Complex.im ↑qz2)) 120447 131072 1 262144 0 1 0 1 120447 120447

noncomputable def ep339 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re qz89) (Complex.re ↑qz2) 1 2 0 1 120447 65536 1 131072 120447 131072 1 262144

noncomputable abbrev qz90 := (@Enclosure.Complex.IsNear.of_eq qz361 (Complex.mk (Enclosure.sfrac Bool.false 1 2) qz283) Bool.false 1 2 0 1 Bool.false 0 1 0 1 BSN.half_c_mk (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 2) qz283 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz371 qz295))

noncomputable def ep340 := ep339 (@Enclosure.Complex.IsNear.re_isNear qz89 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz90) (@Enclosure.Real.IsNear.of_eq (Complex.re ↑qz2) qz2 Bool.false 120447 65536 1 131072 (Complex.ofReal_re qz2) EMRow25.d4)

noncomputable def ep341 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz89) (Complex.im ↑qz2) 0 1 0 1 0 1 0 1 0 1 0 1

noncomputable def ep342 := ep341 (@Enclosure.Complex.IsNear.im_isNear qz89 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz90) (@Enclosure.Real.IsNear.of_eq (Complex.im ↑qz2) qz10 Bool.false 0 1 0 1 (@Eq.trans Real (Complex.im ↑qz2) (0 : Real) qz10 (Complex.ofReal_im qz2) Enclosure.sfrac_zero_eq) qz20)

noncomputable def ep343 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re qz89) (Complex.im ↑qz2)) (@HMul.hMul Real Real Real qz0 (Complex.im qz89) (Complex.re ↑qz2)) 0 1 0 1 0 1 0 1 0 0

noncomputable def ep344 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re qz89) (Complex.im ↑qz2) 1 2 0 1 0 1 0 1 0 1 0 1

noncomputable def ep345 := ep344 (@Enclosure.Complex.IsNear.re_isNear qz89 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz90) (@Enclosure.Real.IsNear.of_eq (Complex.im ↑qz2) qz10 Bool.false 0 1 0 1 (@Eq.trans Real (Complex.im ↑qz2) (0 : Real) qz10 (Complex.ofReal_im qz2) Enclosure.sfrac_zero_eq) qz20)

noncomputable def ep346 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz89) (Complex.re ↑qz2) 0 1 0 1 120447 65536 1 131072 0 1 0 1

noncomputable def ep347 := ep346 (@Enclosure.Complex.IsNear.im_isNear qz89 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz90) (@Enclosure.Real.IsNear.of_eq (Complex.re ↑qz2) qz2 Bool.false 120447 65536 1 131072 (Complex.ofReal_re qz2) EMRow25.d4)

noncomputable def ep348 := @ep309 1192350001876054427 8456600000000000000000 (ep337 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@Enclosure.Complex.IsNear.mul qz89 (↑qz2) Bool.false 120447 131072 1 262144 Bool.false 0 1 0 1 (@ep338 131072 1 262144 (ep340 rfl) (ep342 rfl) rfl rfl) (@ep343 1 0 1 (ep345 rfl) (ep347 rfl) rfl rfl))

noncomputable abbrev qz91 := (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 1)

noncomputable abbrev qz377 := (@Nat.cast Complex Complex.instNatCast 1)

noncomputable abbrev qz92 := (@HMul.hMul Complex Complex Complex qz353 (@HMul.hMul Complex Complex Complex qz353 (2 : Complex) qz377) (@HSub.hSub Complex Complex Complex qz354 (@HMul.hMul Complex Complex Complex qz353 (2 : Complex) qz377) (1 : Complex)))

noncomputable abbrev qz378 := (@HPow.hPow Complex Int Complex qz551 qz547 (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) (@OfNat.ofNat Int 1 (@instOfNat 1)) (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (@OfNat.ofNat Int 2 (@instOfNat 2)) (@Nat.cast Int instNatCastInt 1))))

noncomputable abbrev qz93 := qz378

noncomputable def ep349 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz63 (@HMul.hMul Complex Complex Complex qz62 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz71 qz72 (@HSub.hSub Int Int Int qz366 qz73 (@HMul.hMul Int Int Int qz367 qz74 (@Nat.cast Int instNatCastInt k))))) (@HAdd.hAdd Complex Complex Complex qz4 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz63 (@HMul.hMul Complex Complex Complex qz62 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz71 qz72 (@HSub.hSub Int Int Int qz366 qz73 (@HMul.hMul Int Int Int qz367 qz74 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli qz91)) qz92) qz93)) Bool.false 1645017 17179869184 3 17179869184

noncomputable def ep350 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz63 (@HMul.hMul Complex Complex Complex qz62 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz71 qz72 (@HSub.hSub Int Int Int qz366 qz73 (@HMul.hMul Int Int Int qz367 qz74 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli qz91)) qz92) qz93) Bool.false 0 1 0 1 Bool.false

noncomputable def ep351 := @ep350 0 1 0 1 Bool.false 1645017 17179869184 3 17179869184 Bool.true 12116646883 6442450944000 22097 6442450944000 Bool.false 1645017 1645017 17179869184 3 17179869184 Bool.true 12116646883 12116646883 6442450944000 22097

noncomputable def ep352 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz63 (@HMul.hMul Complex Complex Complex qz62 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz71 qz72 (@HSub.hSub Int Int Int qz366 qz73 (@HMul.hMul Int Int Int qz367 qz74 (@Nat.cast Int instNatCastInt k))))) (Complex.mk qz10 qz10) Bool.false 0 1 0 1 Bool.false

noncomputable def ep353 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli qz91)) qz92) qz93 Bool.false 1645017 17179869184 3 17179869184 Bool.true 12116646883 6442450944000 22097 6442450944000

noncomputable abbrev qz94 := (Complex.re qz378)

noncomputable abbrev qz95 := (Complex.im qz378)

noncomputable def ep354 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli qz91)) qz92)) qz94) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli qz91)) qz92)) qz95) 1645017 17179869184 3 17179869184 0 1 0

noncomputable def ep355 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli qz91)) qz92)) qz94 1 12 0 1 4935051 4294967296 9 4294967296 1645017

noncomputable def ep356 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli qz91)) qz92) (Complex.mk (Enclosure.sfrac Bool.false 1 12) qz10) Bool.false 1 12 0 1 Bool.false 0 1 0 1

noncomputable abbrev qz379 := (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 12) qz10 Bool.false 1 12 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 12) qz20)

noncomputable def ep357 := @Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli qz91)) qz92) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (ep356 (BSN.stirling_coeff_mk 1 1 6 Bool.false BSN.bern_real_1 rfl rfl) qz379)

noncomputable def ep358 := @Enclosure.Complex.IsNear.re_isNear qz93 Bool.false 4935051 4294967296 9 4294967296 Bool.true 12116646883 536870912000 22097 536870912000

noncomputable abbrev qz553 := (@instHPow Complex Nat (@NPow.toPow Complex (@Monoid.toNPow Complex (@Semiring.toMonoid Complex Complex.instSemiring))))

noncomputable abbrev qz380 := (@HPow.hPow Complex Nat Complex qz553 qz547 1)

noncomputable abbrev qz96 := (@Inv.inv Complex Complex.instInv qz380)

noncomputable def ep359 := @Enclosure.Complex.IsNear.of_eq qz93 qz96 Bool.false 4935051 4294967296 9 4294967296 Bool.true 12116646883 536870912000 22097

noncomputable def ep360 := @Enclosure.Complex.IsNear.of_parts qz96 Bool.false 4935051 4294967296 9 4294967296 Bool.true 12116646883 536870912000 22097

noncomputable abbrev qz97 := (Complex.re qz380)

noncomputable abbrev qz98 := (@MonoidWithZeroHom Complex Real (@instMulZeroOneClassOfSemiring Complex Complex.instSemiring) (@instMulZeroOneClassOfSemiring Real Real.semiring))

noncomputable abbrev qz99 := (@MonoidWithZeroHom.funLike Complex Real (@instMulZeroOneClassOfSemiring Complex Complex.instSemiring) (@instMulZeroOneClassOfSemiring Real Real.semiring))

noncomputable abbrev qz100 := qz380

noncomputable def ep361 := @Enclosure.Real.IsNear.mulLit_ff qz97 (@Inv.inv Real Real.instInv (@DFunLike.coe qz98 Complex (fun (x : Complex) => Real) qz99 Complex.normSq qz100)) 9000 4000 0 1 548339 1073741824 1 1073741824

noncomputable def ep362 := @Enclosure.Complex.IsNear.re_isNear qz100 Bool.false 9000 4000 0 1 Bool.false 176776 4000 0 1

noncomputable def ep363 := @Enclosure.Complex.IsNear.of_eq qz100 qz72 Bool.false 9000 4000 0 1 Bool.false 176776 4000 0

noncomputable def ep364 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (@DFunLike.coe qz98 Complex (fun (x : Complex) => Real) qz99 Complex.normSq qz100)) Bool.false 548339 1073741824 1 1073741824 548339 1073741824 1

noncomputable abbrev qz101 := (Complex.im qz380)

noncomputable abbrev qz381 := (@instHAdd Real Real.instAdd)

noncomputable def ep365 := @Enclosure.Real.IsNear.of_eq (@DFunLike.coe qz98 Complex (fun (x : Complex) => Real) qz99 Complex.normSq qz100) (@HAdd.hAdd Real Real Real qz381 (@HMul.hMul Real Real Real qz0 qz97 qz97) (@HMul.hMul Real Real Real qz0 qz101 qz101)) Bool.false 244771517 125000 0 1

noncomputable def ep366 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz97 qz97) (@HMul.hMul Real Real Real qz0 qz101 qz101) 81 16 0 1 488277409 250000

noncomputable def ep367 := @Enclosure.Real.IsNear.mulLit_ff qz97 qz97 9000 4000 0 1 9000 4000 0 1

noncomputable def ep368 := @Enclosure.Real.IsNear.mulLit_ff qz101 qz101 176776 4000 0 1 176776 4000 0 1

noncomputable def ep369 := @Enclosure.Complex.IsNear.im_isNear qz100 Bool.false 9000 4000 0 1 Bool.false 176776 4000 0 1

noncomputable abbrev qz102 := (ep362 (@ep363 1 (BSN.pow_one_c qz355) qz376))

noncomputable abbrev qz103 := (ep369 (@ep363 1 (BSN.pow_one_c qz355) qz376))

noncomputable def ep370 := @ep366 0 1 7832688544 244771517 125000 0 1 (@ep367 81 16 0 1 qz102 qz102 rfl) (@ep368 488277409 250000 0 1 qz103 qz103 rfl)

noncomputable def ep371 := @Enclosure.Real.IsNear.inv_image (@DFunLike.coe qz98 Complex (fun (x : Complex) => Real) qz99 Complex.normSq qz100) 244771517 125000 0 1 274169 274170 536870912 (ep365 (Enclosure.Complex.normSq_eq_mul_add_mul qz100) (ep370 rfl rfl)) rfl

noncomputable def ep372 := @Enclosure.Real.IsNear.of_eq (Complex.re qz96) (@HMul.hMul Real Real Real qz0 qz97 (@Inv.inv Real Real.instInv (@DFunLike.coe qz98 Complex (fun (x : Complex) => Real) qz99 Complex.normSq qz100))) Bool.false 4935051 4294967296 9 4294967296 (Enclosure.Complex.inv_re_eq_mul qz100) (@ep361 4935051 4294967296 9 4294967296 qz102 (@ep364 1073741824 (ep371 rfl rfl rfl rfl rfl) rfl) rfl)

noncomputable def ep373 := @Enclosure.Real.IsNear.of_eq (Complex.im qz96) (@HMul.hMul Real Real Real qz0 (@Neg.neg Real Real.instNeg qz101) (@Inv.inv Real Real.instInv (@DFunLike.coe qz98 Complex (fun (x : Complex) => Real) qz99 Complex.normSq qz100))) Bool.true 12116646883 536870912000 22097 536870912000 (Enclosure.Complex.inv_im_eq_mul qz100)

noncomputable def ep374 := @Enclosure.Real.IsNear.mulLit_tf (@Neg.neg Real Real.instNeg qz101) (@Inv.inv Real Real.instInv (@DFunLike.coe qz98 Complex (fun (x : Complex) => Real) qz99 Complex.normSq qz100)) 176776 4000 0 1 548339 1073741824 1

noncomputable def ep375 := @ep374 1073741824 12116646883 536870912000 22097 536870912000 (@Enclosure.Real.IsNear.neg qz101 Bool.false 176776 4000 0 1 qz103) (@ep364 1073741824 (ep371 rfl rfl rfl rfl rfl) rfl) rfl

noncomputable def ep376 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli qz91)) qz92)) qz95 0 1 0 1 12116646883 536870912000 22097 536870912000 0

noncomputable def ep377 := @Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli qz91)) qz92) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (ep356 (BSN.stirling_coeff_mk 1 1 6 Bool.false BSN.bern_real_1 rfl rfl) qz379)

noncomputable def ep378 := @Enclosure.Complex.IsNear.im_isNear qz93 Bool.false 4935051 4294967296 9 4294967296 Bool.true 12116646883 536870912000 22097 536870912000

noncomputable abbrev qz104 := (@ep359 536870912000 (BSN.zpow_one_sub_two_mul qz355 1 1 rfl rfl) (@ep360 536870912000 ep372 (ep373 ep375)))

noncomputable def ep379 := @ep354 1 1645017 1645017 17179869184 3 17179869184 (@ep355 17179869184 3 17179869184 ep357 (ep358 qz104) rfl) (@ep376 1 0 1 ep377 (ep378 qz104) rfl) rfl

noncomputable def ep380 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli qz91)) qz92)) qz95) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli qz91)) qz92)) qz94) 12116646883 6442450944000 22097 6442450944000 0 1 0

noncomputable def ep381 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli qz91)) qz92)) qz95 1 12 0 1 12116646883 536870912000 22097 536870912000 12116646883

noncomputable def ep382 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli qz91)) qz92)) qz94 0 1 0 1 4935051 4294967296 9 4294967296 0

noncomputable def ep383 := @ep380 1 12116646883 12116646883 6442450944000 22097 6442450944000 (@ep381 6442450944000 22097 6442450944000 ep357 (ep378 qz104) rfl) (@ep382 1 0 1 ep377 (ep358 qz104) rfl) rfl

noncomputable abbrev qz105 := (@Enclosure.Complex.IsNear.mk qz283 qz283 Bool.false 0 1 0 1 Bool.false 0 1 0 1 qz295 qz295)

noncomputable def ep384 := @ep351 6442450944000 (@ep352 0 1 0 1 (BSN.stirling_sum_base qz72) qz105) (ep353 (ep379 rfl) (ep383 rfl)) rfl rfl rfl rfl rfl

noncomputable def ep385 := @ep306 850870191577335300449 6755399441055744000 234431251851043353705491 ep293 (ep348 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep349 Bool.true 12116646883 6442450944000 22097 6442450944000 (BSN.stirling_sum_succ qz72 0 1 rfl) (ep384 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl

noncomputable def ep386 := @Enclosure.Complex.IsNear.of_eq (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz65 (@Nat.cast Complex Complex.instNatCast j))) (BSN.logSumC qz13 2) Bool.false 17063222124318931 2251799813685248 25000000042283 4228300000000000000 Bool.false 874728785479075 281474976710656

noncomputable abbrev qz106 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz273 qz356 qz377))

noncomputable def ep387 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz13 2) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.logSumC qz13 1) qz106) Bool.false 17063222124318931 2251799813685248 25000000042283 4228300000000000000 Bool.false 874728785479075 281474976710656 500000000042283 42283000000000000000

noncomputable def ep388 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz13 1) qz106 Bool.false 17062356688408787 4503599627370496 25000000042283 8456600000000000000 Bool.false 881096074495395 562949953421312 500000000042283 84566000000000000000 Bool.false

noncomputable def ep389 := nat_lit 153691841601645481649620807319552

noncomputable def ep390 := nat_lit 984857058083452175602470092800

noncomputable abbrev qz107 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz273 qz356 (@Nat.cast Complex Complex.instNatCast 0)))

noncomputable def ep391 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz13 1) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.logSumC qz13 0) qz107) Bool.false 17062356688408787 4503599627370496 25000000042283 8456600000000000000 Bool.false 881096074495395 562949953421312 500000000042283 84566000000000000000

noncomputable def ep392 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz13 0) qz107 Bool.false 0 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable abbrev qz382 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz82))

noncomputable def ep393 := @Enclosure.Complex.IsNear.of_eq qz107 qz382 Bool.false 17062356688408787 4503599627370496 25000000042283 8456600000000000000 Bool.false 881096074495395 562949953421312 500000000042283 84566000000000000000

noncomputable def ep394 := nat_lit 625264507433737490040657385264243568138969179850704061998891533219893257442710145431721518388871585060114923520

noncomputable def ep395 := nat_lit 21577235711168552308956860924081194505997158173926035732955734712123165763921609486751860953946764543214485504

noncomputable def ep396 := nat_lit 498417648795060858570602414083608490111150741205530636785287824546941289758163696373335731069755137720320

noncomputable def ep397 := BSN.log_dyadic_bound 14866754176 47634754176 6 5 ep394 524288 169132 ep395 ep396 338552 62501508352 32768000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 14866754176) (BSN.artanhQ 47634754176) 0 5 ep395 ep394 ep396 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep398 := @Enclosure.Real.IsNear.mulLit_ff qz84 (Real.log (Enclosure.sfrac Bool.false 31250754176 16000000)) 1 2 0 1 17062356688408787 2251799813685248 25000000042283 4228300000000000000 17062356688408787 4503599627370496 25000000042283 8456600000000000000 qz371 (BSN.isNear_log_sfrac 31250754176 16000000 17062356688408787 2251799813685248 25000000042283 4228300000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 31250754176) qz372)) Bool.false 143129421815239457898496 18889465931478580854784 1000000001691320 169132000000000000000 17062356688408787 2251799813685248 25000000042283 4228300000000000000 (BSN.log_rat_reduce_isNear 31250754176 16000000 10 62501508352 32768000000 338552 524288 24973259072661432 36028797018963968 169132 1000000000000000 rfl rfl rfl rfl (ep397 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep399 := BSN.arctan_dyadic_bound_f 1000 176776 1 0 524288 169132 0 1 1 0 1 1 2965 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 176776) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 176776) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz383 := (@Nat.cast Real Real.instNatCast 1000)

noncomputable abbrev qz384 := (@Nat.cast Real Real.instNatCast 176776)

noncomputable def ep400 := @Enclosure.Real.IsNear.subLit_ff_p qz85 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz383 qz384)) 884279719003555 562949953421312 1 2000000000000000 2965 524288 1 169132 461948098705041653760 881096074495395 562949953421312 500000000042283 84566000000000000000 qz86 (ep399 rfl) rfl rfl

noncomputable abbrev qz108 := (@HAdd.hAdd Complex Complex Complex qz273 qz356 (@Nat.cast Complex Complex.instNatCast 0))

noncomputable abbrev qz385 := (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz82)

noncomputable def ep401 := @ep392 17062356688408787 4503599627370496 25000000042283 8456600000000000000 Bool.false 881096074495395 562949953421312 500000000042283 84566000000000000000 Bool.false 17062356688408787 17062356688408787 4503599627370496 25000000042283 8456600000000000000 Bool.false 881096074495395 881096074495395 562949953421312 500000000042283 84566000000000000000 (@Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz13 0) (Complex.mk qz10 qz10) Bool.false 0 1 0 1 Bool.false 0 1 0 1 (BSN.log_sum_c_base qz13) qz105) (ep393 (@congrArg Complex Complex qz108 qz385 Complex.log (BSN.w_shift_mk qz13 Bool.false 88388 1000 0 qz14 rfl)) (@Enclosure.Complex.IsNear.of_parts qz382 Bool.false 17062356688408787 4503599627370496 25000000042283 8456600000000000000 Bool.false 881096074495395 562949953421312 500000000042283 84566000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz382) (@HMul.hMul Real Real Real qz0 qz84 (Real.log (Enclosure.sfrac Bool.false 31250754176 16000000))) Bool.false 17062356688408787 4503599627370496 25000000042283 8456600000000000000 (Enclosure.clog_re_eq 1000 176776 4000 31250754176 16000000 rfl rfl rfl) (ep398 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz382) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz384 qz383)) Bool.false 881096074495395 562949953421312 500000000042283 84566000000000000000 (Enclosure.clog_im_eq 1000 176776 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz384 qz383)) (@HSub.hSub Real Real Real qz357 qz85 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz383 qz384))) Bool.false 881096074495395 562949953421312 500000000042283 84566000000000000000 (BSN.arctan_recip 176776 1000 rfl rfl) ep400)))) rfl rfl

noncomputable abbrev qz386 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz82))

noncomputable def ep402 := @Enclosure.Complex.IsNear.of_eq qz106 qz386 Bool.false 17064087560229075 4503599627370496 25000000042283 8456600000000000000 Bool.false 868361496462755 562949953421312 500000000042283 84566000000000000000

noncomputable def ep403 := nat_lit 628421953581308850485736092016143264236326173514042338478367504708031072299979416285804685462413191664914923520

noncomputable def ep404 := nat_lit 21737434578772462517084389606263932533425438614863911166506865068280002144453159292445884872399196456174485504

noncomputable def ep405 := nat_lit 506522509527336647338435361925863633575655418247527324852622971023090966745247311531438571433991937720320

noncomputable def ep406 := BSN.log_dyadic_bound 14890754176 47658754176 6 5 ep403 524288 169132 ep404 ep405 338955 62549508352 32768000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 14890754176) (BSN.artanhQ 47658754176) 0 5 ep404 ep403 ep405 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep407 := @Enclosure.Real.IsNear.mulLit_ff qz84 (Real.log (Enclosure.sfrac Bool.false 31274754176 16000000)) 1 2 0 1 17064087560229075 2251799813685248 25000000042283 4228300000000000000 17064087560229075 4503599627370496 25000000042283 8456600000000000000 qz371 (BSN.isNear_log_sfrac 31274754176 16000000 17064087560229075 2251799813685248 25000000042283 4228300000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 31274754176) qz372)) Bool.false 143143941420438100377600 18889465931478580854784 1000000001691320 169132000000000000000 17064087560229075 2251799813685248 25000000042283 4228300000000000000 (BSN.log_rat_reduce_isNear 31274754176 16000000 10 62549508352 32768000000 338955 524288 24973259072661432 36028797018963968 169132 1000000000000000 rfl rfl rfl rfl (ep406 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep408 := BSN.arctan_dyadic_bound_f 5000 176776 1 0 524288 169132 0 1 1 0 1 1 14825 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 5000) (BSN.arctanEvenQ 176776) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 5000) (BSN.arctanOddQ 176776) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz387 := (@Nat.cast Real Real.instNatCast 5000)

noncomputable def ep409 := @Enclosure.Real.IsNear.subLit_ff_p qz85 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz387 qz384)) 884279719003555 562949953421312 1 2000000000000000 14825 524288 1 169132 455271512257464893440 868361496462755 562949953421312 500000000042283 84566000000000000000 qz86 (ep408 rfl) rfl rfl

noncomputable abbrev qz109 := (@HAdd.hAdd Complex Complex Complex qz273 qz356 qz377)

noncomputable abbrev qz388 := (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz82)

noncomputable def ep410 := @ep388 17064087560229075 4503599627370496 25000000042283 8456600000000000000 Bool.false 868361496462755 562949953421312 500000000042283 84566000000000000000 Bool.false ep389 17063222124318931 2251799813685248 25000000042283 4228300000000000000 Bool.false ep390 874728785479075 281474976710656 500000000042283 42283000000000000000 (ep391 (BSN.log_sum_c_succ qz13 0 1 rfl) (ep401 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep402 (@congrArg Complex Complex qz109 qz388 Complex.log (BSN.w_shift_mk qz13 Bool.false 88388 1000 1 qz14 rfl)) (@Enclosure.Complex.IsNear.of_parts qz386 Bool.false 17064087560229075 4503599627370496 25000000042283 8456600000000000000 Bool.false 868361496462755 562949953421312 500000000042283 84566000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz386) (@HMul.hMul Real Real Real qz0 qz84 (Real.log (Enclosure.sfrac Bool.false 31274754176 16000000))) Bool.false 17064087560229075 4503599627370496 25000000042283 8456600000000000000 (Enclosure.clog_re_eq 5000 176776 4000 31274754176 16000000 rfl rfl rfl) (ep407 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz386) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz384 qz387)) Bool.false 868361496462755 562949953421312 500000000042283 84566000000000000000 (Enclosure.clog_im_eq 5000 176776 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz384 qz387)) (@HSub.hSub Real Real Real qz357 qz85 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz387 qz384))) Bool.false 868361496462755 562949953421312 500000000042283 84566000000000000000 (BSN.arctan_recip 176776 5000 rfl rfl) ep409)))) rfl rfl

noncomputable def ep411 := @ep299 ep293 Bool.false 17063222124318931 2251799813685248 25000000042283 4228300000000000000 Bool.false 874728785479075 281474976710656 500000000042283 42283000000000000000 Bool.true ep300 156383031797185514399 2251799813685248000 765365730003722881494361 ep297 Bool.false ep301 829876700725837500449 6755399441055744000 254092051852705988918291 ep293 (@ep302 2251799813685248000 748981729976012294614361 ep297 Bool.false 850870191577335300449 6755399441055744000 234431251851043353705491 ep293 (BSN.logGammaStirling_unfold 1 qz72) (ep385 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (@ep386 500000000042283 42283000000000000000 (BSN.log_sum_c_eq qz13 2) (ep387 (BSN.log_sum_c_succ qz13 1 2 rfl) (ep410 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)))

noncomputable abbrev qz110 := (@HDiv.hDiv Real Real Real qz270 qz284 (2 : Real))

noncomputable def ep412 := @Enclosure.Real.IsNear.mulLit_ff qz110 (Real.log Real.pi) 88388 2000 0 1 75021 65536 1 131072 1657739037 32768000 22097 65536000 (@Enclosure.Real.IsNear.of_eq qz110 (Enclosure.sfrac Bool.false 88388 2000) Bool.false 88388 2000 0 1 (BSN.t_half_eq qz13 Bool.false 88388 1000 qz14) (Enclosure.Real.IsNear.const Bool.false 88388 2000)) EMRow25.d5 rfl

noncomputable def ep413 := @ep295 22097 65536000 ep296 488119823163395870753 6755399441055744000 814688522452705988918291 ep293 (@ep298 254092051852705988918291 ep293 (ep411 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) ep412 rfl rfl

noncomputable def ep414 := nat_lit 32561899959495086425130797810549157745980795822231971188894044223523489054720

noncomputable def ep415 := nat_lit 65359950249731834054229282200537387833715038066547963599010892417404502016

noncomputable def ep416 := nat_lit 85175345688749470048778575427875495468695117091833132601276479140552387854336

noncomputable def ep417 := BSN.sin_dyadic_bound_f 1686218944 1073741824 3 2 524288 169298 ep414 ep66 ep415 ep416 ep69 ep415 524287 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1686218944) qz287 0 2 ep414 ep66 ep415 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1686218944) qz288 0 2 ep416 ep69 ep415 rfl rfl rfl rfl) rfl rfl

noncomputable def ep418 := @ep292 262144 Bool.true 524287 524288 1 84566 (@ep294 9470771 131072 129 262144 ep413 rfl) (Enclosure.sfrac_false_div 9470771 131072) (BSN.cos_reduce1 qz358 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 29664277375586362458112) qz302) 226375608064910080 72057594037927936 Bool.false 524287 524288 11 1000000000000000 169132 84566 (BSN.sin_reduce_arg_pos_rat_q1 9470771 131072 226375608064910080 72057594037927936 11 29664277375586362458112 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 524287 524288 29664277375586362458112 18889465931478580854784 1686218944 1073741824 169298 169132 (ep417 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep419 := nat_lit 49548134586489119264446017

noncomputable def ep420 := nat_lit 6526554927651267756110643200

noncomputable abbrev qz554 := (@Nat.cast Complex Complex.instNatCast 23)

noncomputable abbrev qz389 := (@HPow.hPow Complex Complex Complex qz526 qz554 qz527)

noncomputable abbrev qz111 := qz389

noncomputable abbrev qz390 := qz554

noncomputable abbrev qz112 := (@HAdd.hAdd Complex Complex Complex qz273 (@HDiv.hDiv Complex Complex Complex qz362 qz390 (@HSub.hSub Complex Complex Complex qz354 qz272 (1 : Complex))) qz361)

noncomputable abbrev qz113 := (@instHSub Nat instSubNat)

noncomputable abbrev qz391 := qz553

noncomputable abbrev qz114 := qz391

noncomputable abbrev qz115 := qz390

noncomputable def ep421 := @Enclosure.Complex.IsNear.of_eq (zetaApproximant qz5 1 23) (@HAdd.hAdd Complex Complex Complex qz4 (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 23, @HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast n) qz7) (@HMul.hMul Complex Complex Complex qz62 qz111 (@HAdd.hAdd Complex Complex Complex qz4 qz112 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1))))))) Bool.false ep287 ep288 ep289

noncomputable def ep422 := @Enclosure.Complex.IsNear.addLitP (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 23, @HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast n) qz7) (@HMul.hMul Complex Complex Complex qz62 qz111 (@HAdd.hAdd Complex Complex Complex qz4 qz112 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))))) Bool.false 147027886727 274877906944 86805250084043 11622662539313152

noncomputable def ep423 := nat_lit 4064436970012487610703977

noncomputable def ep424 := nat_lit 397062614670664066305362932432633856

noncomputable def ep425 := nat_lit 11280479756647451396667309159350272

noncomputable def ep426 := @ep422 Bool.false 10477849767 274877906944 86790479701917 11622662539313152 Bool.false 206081424864067437085199 ep288 ep423 ep290 Bool.true 129293649444560259741763 ep288 812069932129981586341317 ep420 Bool.false ep424 ep287 ep288 ep289 ep290 Bool.true ep425 41038146288510511646263 ep288

noncomputable def ep427 := @Enclosure.Complex.IsNear.of_eq (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 23, @HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast n) qz7) (BSN.headSumC qz5 23) Bool.false 147027886727 274877906944 86805250084043 11622662539313152 Bool.false 10477849767 274877906944 86790479701917

noncomputable abbrev qz116 := (@HPow.hPow Complex Complex Complex qz274 (@Nat.cast Complex Complex.instNatCast 22) qz275)

noncomputable def ep428 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 23) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 22) qz116) Bool.false 147027886727 274877906944 86805250084043 11622662539313152 Bool.false 10477849767 274877906944 86790479701917 11622662539313152

noncomputable def ep429 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 22) qz116 Bool.false 51323088785 68719476736 42079558788781 5811331269656576 Bool.false 16780173345 274877906944 84164003082231 11622662539313152 Bool.true

noncomputable abbrev qz117 := (@HPow.hPow Complex Complex Complex qz274 (@Nat.cast Complex Complex.instNatCast 21) qz275)

noncomputable def ep430 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 22) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 21) qz117) Bool.false 51323088785 68719476736 42079558788781 5811331269656576 Bool.false 16780173345 274877906944 84164003082231 11622662539313152

noncomputable def ep431 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 21) qz117 Bool.false 88457058981 137438953472 40731398202083 5811331269656576 Bool.true 9016364541 68719476736 40729319654369 5811331269656576 Bool.false

noncomputable abbrev qz118 := (@HPow.hPow Complex Complex Complex qz274 (@Nat.cast Complex Complex.instNatCast 20) qz275)

noncomputable def ep432 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 21) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 20) qz118) Bool.false 88457058981 137438953472 40731398202083 5811331269656576 Bool.true 9016364541 68719476736 40729319654369 5811331269656576

noncomputable def ep433 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 20) qz118 Bool.false 138358926277 274877906944 78696715744077 11622662539313152 Bool.false 5901616813 137438953472 9836149945035 1452832817414144 Bool.false

noncomputable abbrev qz119 := (@HPow.hPow Complex Complex Complex qz274 (@Nat.cast Complex Complex.instNatCast 19) qz275)

noncomputable def ep434 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 20) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 19) qz119) Bool.false 138358926277 274877906944 78696715744077 11622662539313152 Bool.false 5901616813 137438953472 9836149945035 1452832817414144

noncomputable def ep435 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 19) qz119 Bool.false 193721425513 274877906944 75853619092625 11622662539313152 Bool.false 10499217749 68719476736 37927475397855 5811331269656576 Bool.true

noncomputable abbrev qz120 := (@HPow.hPow Complex Complex Complex qz274 (@Nat.cast Complex Complex.instNatCast 18) qz275)

noncomputable def ep436 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 19) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 18) qz120) Bool.false 193721425513 274877906944 75853619092625 11622662539313152 Bool.false 10499217749 68719476736 37927475397855 5811331269656576

noncomputable def ep437 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 18) qz120 Bool.false 57111654597 68719476736 36470363805437 5811331269656576 Bool.true 12700019079 274877906944 72935225704631 11622662539313152 Bool.true

noncomputable abbrev qz121 := (@HPow.hPow Complex Complex Complex qz274 (@Nat.cast Complex Complex.instNatCast 17) qz275)

noncomputable def ep438 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 18) (@HAdd.hAdd Complex Complex Complex qz4 qz38 qz121) Bool.false 57111654597 68719476736 36470363805437 5811331269656576 Bool.true 12700019079 274877906944 72935225704631 11622662539313152

noncomputable def ep439 := @Enclosure.Complex.IsNear.addLitP qz38 qz121 Bool.false 187291989515 274877906944 69941896866013 11622662539313152 Bool.true 65149037491 274877906944 69932639341427 11622662539313152 Bool.false

noncomputable abbrev qz392 := (@Nat.cast Real Real.instNatCast 17)

noncomputable abbrev qz122 := (@Inv.inv Real Real.instInv (Real.sqrt qz392))

noncomputable abbrev qz555 := (Real.log (Enclosure.sfrac Bool.false 17 1))

noncomputable abbrev qz123 := (@HMul.hMul Real Real Real qz267 qz284 qz555)

noncomputable def ep440 := @Enclosure.Complex.IsNear.of_eq qz121 (Complex.mk (@HMul.hMul Real Real Real qz0 qz122 (Real.cos qz123)) (@HMul.hMul Real Real Real qz0 qz122 (@Neg.neg Real Real.instNeg (Real.sin qz123)))) Bool.false 41154628873 274877906944 2998830744861 11622662539313152 Bool.false 13112254603 68719476736 750646590801 2905665634828288 (BSN.cpow_neg_s_mk qz13 88388 1000 17 qz14 rfl)

noncomputable abbrev qz393 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 17) qz15)

noncomputable def ep441 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz392) 2161695 524288 1 524288 63579 63580 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz392) (Real.sqrt qz393) Bool.false 2161695 524288 1 524288 (BSN.sqrt_natCast_div_one 17) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz393) Bool.false 2161695 524288 1 524288 2161695 524288 1 524288 (BSN.sqrt_enclosure 17 1 1080847 1080848 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep442 := BSN.log_dyadic_bound 1 33 2 1 3267 262144 84566 1 1 15892 34 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 1) (BSN.artanhQ 33) 0 1 1 3267 1 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep443 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz555 88388 1000 0 1 3189913004350711 1125899906842624 125000000042283 10570750000000000000 70487507657137660967 281474976710656000 2762125000934327451 2642687500000000000000 qz18 (BSN.isNear_log_sfrac 17 1 3189913004350711 1125899906842624 125000000042283 10570750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz393) Bool.false 26758929747600409100288 9444732965739290427392 1000000000338264 84566000000000000000 3189913004350711 1125899906842624 125000000042283 10570750000000000000 (BSN.log_rat_reduce_isNear 17 1 4 34 32 15892 262144 24973259072661432 36028797018963968 84566 1000000000000000 rfl rfl rfl rfl (ep442 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep444 := nat_lit 260442603689736077924723021358055696

noncomputable def ep445 := BSN.sin_dyadic_bound_f 714377894 1073741824 2 1 524288 169298 ep444 ep103 ep444 ep444 ep104 ep444 323647 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 714377894) qz287 0 1 ep444 ep103 ep444 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 714377894) qz288 0 1 ep444 ep104 ep444 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz394 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 65646607) qz16)

noncomputable def ep446 := @Enclosure.Real.IsNear.cos_image qz123 qz394 Bool.false 65646607 262144 549 524288 Bool.false 323647 524288 1 84566 (@Enclosure.Real.IsNear.recentre' qz123 Bool.false 70487507657137660967 281474976710656000 2762125000934327451 2642687500000000000000 65646607 262144 549 524288 (ep443 rfl) rfl) (Enclosure.sfrac_false_div 65646607 262144) (BSN.cos_reduce3 qz394 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 25134937656518323994624) qz19) 226375608064910080 72057594037927936 Bool.false 323647 524288 39 1000000000000000 169132 84566 (BSN.sin_reduce_arg_pos_rat_q3 65646607 262144 226375608064910080 72057594037927936 39 25134937656518323994624 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 323647 524288 25134937656518323994624 37778931862957161709568 714377894 1073741824 169298 169132 (ep445 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep447 := BSN.cos_dyadic_bound_f 714377894 1073741824 2 1 524288 169298 ep444 ep228 ep444 ep444 ep229 ep444 412468 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 714377894) qz292 0 1 ep444 ep228 ep444 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 714377894) qz293 0 1 ep444 ep229 ep444 rfl rfl rfl rfl) rfl rfl

noncomputable def ep448 := @Enclosure.Real.IsNear.sin_image qz123 qz394 Bool.false 65646607 262144 549 524288 Bool.true 412468 524288 1 84566 (@Enclosure.Real.IsNear.recentre' qz123 Bool.false 70487507657137660967 281474976710656000 2762125000934327451 2642687500000000000000 65646607 262144 549 524288 (ep443 rfl) rfl) (Enclosure.sfrac_false_div 65646607 262144) (BSN.sin_reduce3 qz394 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 25134937656518323994624) qz19) 226375608064910080 72057594037927936 Bool.false 412468 524288 39 1000000000000000 169132 84566 (BSN.sin_reduce_arg_pos_rat_q3 65646607 262144 226375608064910080 72057594037927936 39 25134937656518323994624 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 412468 524288 25134937656518323994624 37778931862957161709568 714377894 1073741824 169298 169132 (ep447 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz395 := (@Enclosure.Real.IsNear.recentre' qz122 Bool.false 127159 524288 1 524288 127159 524288 1 524288 (ep441 rfl rfl) rfl)

noncomputable def ep449 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz122 (Real.cos qz123)) (@HMul.hMul Real Real Real qz0 qz122 (@Neg.neg Real Real.instNeg (Real.sin qz123))) Bool.false 41154628873 274877906944 2998830744861 11622662539313152 Bool.false 13112254603 68719476736 750646590801 2905665634828288 (@Enclosure.Real.IsNear.mulLit_ff qz122 (Real.cos qz123) 127159 524288 1 524288 323647 524288 23475511 22168469504 41154628873 274877906944 2998830744861 11622662539313152 qz395 (@Enclosure.Real.IsNear.recentre' (Real.cos qz123) Bool.false 323647 524288 46951022 44336939008 323647 524288 23475511 22168469504 (ep446 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz122 (@Neg.neg Real Real.instNeg (Real.sin qz123)) 127159 524288 1 524288 103117 131072 23475511 22168469504 13112254603 68719476736 750646590801 2905665634828288 qz395 (@Enclosure.Real.IsNear.neg (Real.sin qz123) Bool.true 103117 131072 23475511 22168469504 (@Enclosure.Real.IsNear.recentre' (Real.sin qz123) Bool.true 412468 524288 46951022 44336939008 103117 131072 23475511 22168469504 (ep448 rfl rfl) rfl)) rfl)

noncomputable def ep450 := @ep439 41154628873 274877906944 2998830744861 11622662539313152 Bool.false 13112254603 68719476736 750646590801 2905665634828288 Bool.false 62794928310928143286272 57111654597 68719476736 36470363805437 5811331269656576 Bool.true 872738665646096646144 12700019079 274877906944 72935225704631 11622662539313152 EMRow25.d7 (ep440 ep449) rfl rfl

noncomputable abbrev qz396 := (@Nat.cast Real Real.instNatCast 18)

noncomputable abbrev qz124 := (@Inv.inv Real Real.instInv (Real.sqrt qz396))

noncomputable abbrev qz556 := (Real.log (Enclosure.sfrac Bool.false 18 1))

noncomputable abbrev qz125 := (@HMul.hMul Real Real Real qz267 qz284 qz556)

noncomputable def ep451 := @Enclosure.Complex.IsNear.of_eq qz120 (Complex.mk (@HMul.hMul Real Real Real qz0 qz124 (Real.cos qz125)) (@HMul.hMul Real Real Real qz0 qz124 (@Neg.neg Real Real.instNeg (Real.sin qz125)))) Bool.true 34725192875 274877906944 2912891481751 11622662539313152 Bool.false 54696890075 274877906944 2919725091079 11622662539313152 (BSN.cpow_neg_s_mk qz13 88388 1000 18 qz14 rfl)

noncomputable abbrev qz397 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 18) qz15)

noncomputable def ep452 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz396) 2224365 524288 1 524288 61787 61788 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz396) (Real.sqrt qz397) Bool.false 2224365 524288 1 524288 (BSN.sqrt_natCast_div_one 18) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz397) Bool.false 2224365 524288 1 524288 2224365 524288 1 524288 (BSN.sqrt_enclosure 18 1 1112182 1112183 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep453 := BSN.log_dyadic_bound 2 34 2 1 3468 262144 84566 4 4 30876 36 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 2) (BSN.artanhQ 34) 0 1 4 3468 4 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep454 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz556 88388 1000 0 1 3254268794313975 1125899906842624 125000000042283 10570750000000000000 2876383101918236223 11258999068426240 2762125000934327451 2642687500000000000000 qz18 (BSN.isNear_log_sfrac 18 1 3254268794313975 1125899906842624 125000000042283 10570750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz397) Bool.false 27298785242132565196800 9444732965739290427392 1000000000338264 84566000000000000000 3254268794313975 1125899906842624 125000000042283 10570750000000000000 (BSN.log_rat_reduce_isNear 18 1 4 36 32 30876 262144 24973259072661432 36028797018963968 84566 1000000000000000 rfl rfl rfl rfl (ep453 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep455 := nat_lit 3031563688036610826136341820419318221250057683149922385166402057986149605921

noncomputable def ep456 := nat_lit 1840722475019044501588197797310523052779598305201061916438306898842116641

noncomputable def ep457 := nat_lit 9091009619159794389405849065663333617644613852839365031666329560160764584481

noncomputable def ep458 := BSN.cos_dyadic_bound_f 1079253683 1073741824 3 2 524288 169298 ep455 ep73 ep456 ep457 ep75 ep456 281005 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1079253683) qz292 0 2 ep455 ep73 ep456 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1079253683) qz293 0 2 ep457 ep75 ep456 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz398 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 133942025) qz23)

noncomputable def ep459 := @Enclosure.Real.IsNear.cos_image qz125 qz398 Bool.false 133942025 524288 549 524288 Bool.true 281005 524288 1 84566 (@Enclosure.Real.IsNear.recentre' qz125 Bool.false 2876383101918236223 11258999068426240 2762125000934327451 2642687500000000000000 133942025 524288 549 524288 (ep454 rfl) rfl) (Enclosure.sfrac_false_div 133942025 524288) (BSN.cos_reduce2 qz398 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 75945726352025788088320) qz25) 226375608064910080 72057594037927936 Bool.false 281005 524288 40 1000000000000000 169132 84566 (BSN.sin_reduce_arg_pos_rat_q2 133942025 524288 226375608064910080 72057594037927936 40 75945726352025788088320 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 281005 524288 75945726352025788088320 75557863725914323419136 1079253683 1073741824 169298 169132 (ep458 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep460 := nat_lit 5455342060485884251444144718516924379807880151025699443766373058855995597345

noncomputable def ep461 := nat_lit 14284820417265380300779712418729632528839947712573173014380553133453291708961

noncomputable def ep462 := BSN.sin_dyadic_bound_f 1079253683 1073741824 3 2 524288 169298 ep460 ep66 ep456 ep461 ep69 ep456 442621 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1079253683) qz287 0 2 ep460 ep66 ep456 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1079253683) qz288 0 2 ep461 ep69 ep456 rfl rfl rfl rfl) rfl rfl

noncomputable def ep463 := @Enclosure.Real.IsNear.sin_image qz125 qz398 Bool.false 133942025 524288 549 524288 Bool.true 442621 524288 1 84566 (@Enclosure.Real.IsNear.recentre' qz125 Bool.false 2876383101918236223 11258999068426240 2762125000934327451 2642687500000000000000 133942025 524288 549 524288 (ep454 rfl) rfl) (Enclosure.sfrac_false_div 133942025 524288) (BSN.sin_reduce2 qz398 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 75945726352025788088320) qz25) 226375608064910080 72057594037927936 Bool.false 442621 524288 40 1000000000000000 169132 84566 (BSN.sin_reduce_arg_pos_rat_q2 133942025 524288 226375608064910080 72057594037927936 40 75945726352025788088320 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 442621 524288 75945726352025788088320 75557863725914323419136 1079253683 1073741824 169298 169132 (ep462 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz399 := (@Enclosure.Real.IsNear.recentre' qz124 Bool.false 123575 524288 1 524288 123575 524288 1 524288 (ep452 rfl rfl) rfl)

noncomputable def ep464 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz124 (Real.cos qz125)) (@HMul.hMul Real Real Real qz0 qz124 (@Neg.neg Real Real.instNeg (Real.sin qz125))) Bool.true 34725192875 274877906944 2912891481751 11622662539313152 Bool.false 54696890075 274877906944 2919725091079 11622662539313152 (@Enclosure.Real.IsNear.mulLit_ft qz124 (Real.cos qz125) 123575 524288 1 524288 281005 524288 23475511 22168469504 34725192875 274877906944 2912891481751 11622662539313152 qz399 (@Enclosure.Real.IsNear.recentre' (Real.cos qz125) Bool.true 281005 524288 46951022 44336939008 281005 524288 23475511 22168469504 (ep459 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz124 (@Neg.neg Real Real.instNeg (Real.sin qz125)) 123575 524288 1 524288 442621 524288 23475511 22168469504 54696890075 274877906944 2919725091079 11622662539313152 qz399 (@Enclosure.Real.IsNear.neg (Real.sin qz125) Bool.true 442621 524288 23475511 22168469504 (@Enclosure.Real.IsNear.recentre' (Real.sin qz125) Bool.true 442621 524288 46951022 44336939008 442621 524288 23475511 22168469504 (ep463 rfl rfl) rfl)) rfl)

noncomputable def ep465 := @ep437 34725192875 274877906944 2912891481751 11622662539313152 Bool.false 54696890075 274877906944 2919725091079 11622662539313152 Bool.false 13312434993805360365568 193721425513 274877906944 75853619092625 11622662539313152 Bool.false 11544011997577660596224 10499217749 68719476736 37927475397855 5811331269656576 (ep438 (BSN.head_sum_c_succ qz5 17 18 rfl rfl) (ep450 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep451 ep464) rfl rfl

noncomputable abbrev qz400 := (@Nat.cast Real Real.instNatCast 19)

noncomputable abbrev qz126 := (@Inv.inv Real Real.instInv (Real.sqrt qz400))

noncomputable abbrev qz557 := (Real.log (Enclosure.sfrac Bool.false 19 1))

noncomputable abbrev qz127 := (@HMul.hMul Real Real Real qz267 qz284 qz557)

noncomputable def ep466 := @Enclosure.Complex.IsNear.of_eq qz119 (Complex.mk (@HMul.hMul Real Real Real qz0 qz126 (Real.cos qz127)) (@HMul.hMul Real Real Real qz0 qz126 (@Neg.neg Real Real.instNeg (Real.sin qz127)))) Bool.true 13840624809 68719476736 710774162863 2905665634828288 Bool.true 15096818685 137438953472 1417124382285 5811331269656576 (BSN.cpow_neg_s_mk qz13 88388 1000 19 qz14 rfl)

noncomputable abbrev qz401 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 19) qz15)

noncomputable def ep467 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz400) 2285319 524288 1 524288 60139 60140 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz400) (Real.sqrt qz401) Bool.false 2285319 524288 1 524288 (BSN.sqrt_natCast_div_one 19) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz401) Bool.false 2285319 524288 1 524288 2285319 524288 1 524288 (BSN.sqrt_enclosure 19 1 1142659 1142660 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep468 := BSN.log_dyadic_bound 3 35 3 2 22509375 262144 84566 55368 243 45049 38 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 3) (BSN.artanhQ 35) 0 2 55368 22509375 243 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep469 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz557 88388 1000 0 1 3315141365800183 1125899906842624 125000000042283 10570750000000000000 73254678760086643751 281474976710656000 2762125000934327451 2642687500000000000000 qz18 (BSN.isNear_log_sfrac 19 1 3315141365800183 1125899906842624 125000000042283 10570750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz401) Bool.false 27809421382282341515264 9444732965739290427392 1000000000338264 84566000000000000000 3315141365800183 1125899906842624 125000000042283 10570750000000000000 (BSN.log_rat_reduce_isNear 19 1 4 38 32 45049 262144 24973259072661432 36028797018963968 84566 1000000000000000 rfl rfl rfl rfl (ep468 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep470 := nat_lit 7046074460870067820137503429782288668640981604608620982435840000000000000000

noncomputable def ep471 := nat_lit 3070106073733959121869040404600525429145600000000000000000000000000000000

noncomputable def ep472 := nat_lit 18449033892445084547496149584012831376698239897784483525427200000000000000000

noncomputable def ep473 := BSN.sin_dyadic_bound_f 1150520000 1073741824 3 2 524288 169298 ep470 ep66 ep471 ep472 ep69 ep471 460284 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1150520000) qz287 0 2 ep470 ep66 ep471 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1150520000) qz288 0 2 ep472 ep69 ep471 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz402 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 8527967) (@Nat.cast Real Real.instNatCast 32768))

noncomputable def ep474 := @Enclosure.Real.IsNear.cos_image qz127 qz402 Bool.false 8527967 32768 549 524288 Bool.true 460284 524288 1 84566 (@Enclosure.Real.IsNear.recentre' qz127 Bool.false 73254678760086643751 281474976710656000 2762125000934327451 2642687500000000000000 8527967 32768 549 524288 (ep469 rfl) rfl) (Enclosure.sfrac_false_div 8527967 32768) (BSN.cos_reduce1 qz402 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 5060040472981745434624) qz339) 226375608064910080 72057594037927936 Bool.false 460284 524288 41 1000000000000000 169132 84566 (BSN.sin_reduce_arg_pos_rat_q1 8527967 32768 226375608064910080 72057594037927936 41 5060040472981745434624 4722366482869645213696 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 460284 524288 5060040472981745434624 4722366482869645213696 1150520000 1073741824 169298 169132 (ep473 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep475 := nat_lit 3915850303182808326352777034503316160546832269227011656908800000000000000000

noncomputable def ep476 := nat_lit 11741410697400957060814593022700747430782205607681034970726400000000000000000

noncomputable def ep477 := BSN.cos_dyadic_bound_f 1150520000 1073741824 3 2 524288 169298 ep475 ep73 ep471 ep476 ep75 ep471 251030 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1150520000) qz292 0 2 ep475 ep73 ep471 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1150520000) qz293 0 2 ep476 ep75 ep471 rfl rfl rfl rfl) rfl rfl

noncomputable def ep478 := @Enclosure.Real.IsNear.sin_image qz127 qz402 Bool.false 8527967 32768 549 524288 Bool.false 251030 524288 1 84566 (@Enclosure.Real.IsNear.recentre' qz127 Bool.false 73254678760086643751 281474976710656000 2762125000934327451 2642687500000000000000 8527967 32768 549 524288 (ep469 rfl) rfl) (Enclosure.sfrac_false_div 8527967 32768) (BSN.sin_reduce1 qz402 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 5060040472981745434624) qz339) 226375608064910080 72057594037927936 Bool.false 251030 524288 41 1000000000000000 169132 84566 (BSN.sin_reduce_arg_pos_rat_q1 8527967 32768 226375608064910080 72057594037927936 41 5060040472981745434624 4722366482869645213696 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 251030 524288 5060040472981745434624 4722366482869645213696 1150520000 1073741824 169298 169132 (ep477 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz403 := (@Enclosure.Real.IsNear.recentre' qz126 Bool.false 120279 524288 1 524288 120279 524288 1 524288 (ep467 rfl rfl) rfl)

noncomputable def ep479 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz126 (Real.cos qz127)) (@HMul.hMul Real Real Real qz0 qz126 (@Neg.neg Real Real.instNeg (Real.sin qz127))) Bool.true 13840624809 68719476736 710774162863 2905665634828288 Bool.true 15096818685 137438953472 1417124382285 5811331269656576 (@Enclosure.Real.IsNear.mulLit_ft qz126 (Real.cos qz127) 120279 524288 1 524288 115071 131072 23475511 22168469504 13840624809 68719476736 710774162863 2905665634828288 qz403 (@Enclosure.Real.IsNear.recentre' (Real.cos qz127) Bool.true 460284 524288 46951022 44336939008 115071 131072 23475511 22168469504 (ep474 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz126 (@Neg.neg Real Real.instNeg (Real.sin qz127)) 120279 524288 1 524288 125515 262144 23475511 22168469504 15096818685 137438953472 1417124382285 5811331269656576 qz403 (@Enclosure.Real.IsNear.neg (Real.sin qz127) Bool.false 125515 262144 23475511 22168469504 (@Enclosure.Real.IsNear.recentre' (Real.sin qz127) Bool.false 251030 524288 46951022 44336939008 125515 262144 23475511 22168469504 (ep478 rfl rfl) rfl)) rfl)

noncomputable def ep480 := @ep435 13840624809 68719476736 710774162863 2905665634828288 Bool.true 15096818685 137438953472 1417124382285 5811331269656576 Bool.false 9507953015510240591872 138358926277 274877906944 78696715744077 11622662539313152 Bool.false 405556019285739962368 5901616813 137438953472 9836149945035 1452832817414144 (ep436 (BSN.head_sum_c_succ qz5 18 19 rfl rfl) (ep465 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep466 ep479) rfl rfl

noncomputable abbrev qz404 := (@Nat.cast Real Real.instNatCast 20)

noncomputable abbrev qz128 := (@Inv.inv Real Real.instInv (Real.sqrt qz404))

noncomputable abbrev qz558 := (Real.log (Enclosure.sfrac Bool.false 20 1))

noncomputable abbrev qz129 := (@HMul.hMul Real Real Real qz267 qz284 qz558)

noncomputable def ep481 := @Enclosure.Complex.IsNear.of_eq qz118 (Complex.mk (@HMul.hMul Real Real Real qz0 qz128 (Real.cos qz129)) (@HMul.hMul Real Real Real qz0 qz128 (@Neg.neg Real Real.instNeg (Real.sin qz129)))) Bool.false 38555191685 274877906944 2766080660089 11622662539313152 Bool.true 23934345895 137438953472 1384719874229 5811331269656576 (BSN.cpow_neg_s_mk qz13 88388 1000 20 qz14 rfl)

noncomputable abbrev qz405 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 20) qz15)

noncomputable def ep482 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz404) 2344687 524288 1 524288 58617 58618 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz404) (Real.sqrt qz405) Bool.false 2344687 524288 1 524288 (BSN.sqrt_natCast_div_one 20) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz405) Bool.false 2344687 524288 1 524288 2344687 524288 1 524288 (BSN.sqrt_enclosure 20 1 1172343 1172344 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep483 := BSN.log_dyadic_bound 4 36 3 2 25194240 262144 84566 104448 768 58495 40 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 4) (BSN.artanhQ 36) 0 2 104448 25194240 768 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep484 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz558 88388 1000 0 1 3372891496062199 1125899906842624 125000000042283 10570750000000000000 74530783388486411303 281474976710656000 2762125000934327451 2642687500000000000000 qz18 (BSN.isNear_log_sfrac 20 1 3372891496062199 1125899906842624 125000000042283 10570750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz405) Bool.false 28293864586999331028992 9444732965739290427392 1000000000338264 84566000000000000000 3372891496062199 1125899906842624 125000000042283 10570750000000000000 (BSN.log_rat_reduce_isNear 20 1 4 40 32 58495 262144 24973259072661432 36028797018963968 84566 1000000000000000 rfl rfl rfl rfl (ep483 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep485 := nat_lit 1886221703072157623816998993816022594696856708287538174409165116590755675681

noncomputable def ep486 := nat_lit 712918028864824825352160571602640526255235526284200273062934764891668001

noncomputable def ep487 := nat_lit 5657239273158743221800292660304862503038059653810046122681369480242483691041

noncomputable def ep488 := BSN.cos_dyadic_bound_f 958583501 1073741824 3 2 524288 169298 ep485 ep73 ep486 ep487 ep75 ep486 328871 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 958583501) qz292 0 2 ep485 ep73 ep486 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 958583501) qz293 0 2 ep487 ep75 ep486 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz406 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 69412201) qz16)

noncomputable def ep489 := @Enclosure.Real.IsNear.cos_image qz129 qz406 Bool.false 69412201 262144 549 524288 Bool.false 328871 524288 1 84566 (@Enclosure.Real.IsNear.recentre' qz129 Bool.false 74530783388486411303 281474976710656000 2762125000934327451 2642687500000000000000 69412201 262144 549 524288 (ep484 rfl) rfl) (Enclosure.sfrac_false_div 69412201 262144) (BSN.cos_reduce0 qz406 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 33727158578722648358912) qz19) 226375608064910080 72057594037927936 Bool.false 328871 524288 42 1000000000000000 169132 84566 (BSN.sin_reduce_arg_pos_rat_q0 69412201 262144 226375608064910080 72057594037927936 42 33727158578722648358912 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 328871 524288 33727158578722648358912 37778931862957161709568 958583501 1073741824 169298 169132 (ep488 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep490 := nat_lit 844344733426356385034962256667834001

noncomputable def ep491 := BSN.sin_dyadic_bound_f 958583501 1073741824 2 1 524288 169298 ep490 ep103 ep490 ep490 ep104 ep490 408314 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 958583501) qz287 0 1 ep490 ep103 ep490 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 958583501) qz288 0 1 ep490 ep104 ep490 rfl rfl rfl rfl) rfl rfl

noncomputable def ep492 := @Enclosure.Real.IsNear.sin_image qz129 qz406 Bool.false 69412201 262144 549 524288 Bool.false 408314 524288 1 84566 (@Enclosure.Real.IsNear.recentre' qz129 Bool.false 74530783388486411303 281474976710656000 2762125000934327451 2642687500000000000000 69412201 262144 549 524288 (ep484 rfl) rfl) (Enclosure.sfrac_false_div 69412201 262144) (BSN.sin_reduce0 qz406 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 33727158578722648358912) qz19) 226375608064910080 72057594037927936 Bool.false 408314 524288 42 1000000000000000 169132 84566 (BSN.sin_reduce_arg_pos_rat_q0 69412201 262144 226375608064910080 72057594037927936 42 33727158578722648358912 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 408314 524288 33727158578722648358912 37778931862957161709568 958583501 1073741824 169298 169132 (ep491 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz407 := (@Enclosure.Real.IsNear.recentre' qz128 Bool.false 117235 524288 1 524288 117235 524288 1 524288 (ep482 rfl rfl) rfl)

noncomputable def ep493 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz128 (Real.cos qz129)) (@HMul.hMul Real Real Real qz0 qz128 (@Neg.neg Real Real.instNeg (Real.sin qz129))) Bool.false 38555191685 274877906944 2766080660089 11622662539313152 Bool.true 23934345895 137438953472 1384719874229 5811331269656576 (@Enclosure.Real.IsNear.mulLit_ff qz128 (Real.cos qz129) 117235 524288 1 524288 328871 524288 23475511 22168469504 38555191685 274877906944 2766080660089 11622662539313152 qz407 (@Enclosure.Real.IsNear.recentre' (Real.cos qz129) Bool.false 328871 524288 46951022 44336939008 328871 524288 23475511 22168469504 (ep489 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz128 (@Neg.neg Real Real.instNeg (Real.sin qz129)) 117235 524288 1 524288 204157 262144 23475511 22168469504 23934345895 137438953472 1384719874229 5811331269656576 qz407 (@Enclosure.Real.IsNear.neg (Real.sin qz129) Bool.false 204157 262144 23475511 22168469504 (@Enclosure.Real.IsNear.recentre' (Real.sin qz129) Bool.false 408314 524288 46951022 44336939008 204157 262144 23475511 22168469504 (ep492 rfl rfl) rfl)) rfl)

noncomputable def ep494 := @ep433 38555191685 274877906944 2766080660089 11622662539313152 Bool.true 23934345895 137438953472 1384719874229 5811331269656576 Bool.false 48629782454238474928128 88457058981 137438953472 40731398202083 5811331269656576 Bool.true 2478399413274179272704 9016364541 68719476736 40729319654369 5811331269656576 (ep434 (BSN.head_sum_c_succ qz5 19 20 rfl rfl) (ep480 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep481 ep493) rfl rfl

noncomputable abbrev qz408 := (@Nat.cast Real Real.instNatCast 21)

noncomputable abbrev qz130 := (@Inv.inv Real Real.instInv (Real.sqrt qz408))

noncomputable abbrev qz559 := (Real.log (Enclosure.sfrac Bool.false 21 1))

noncomputable abbrev qz131 := (@HMul.hMul Real Real Real qz267 qz284 qz559)

noncomputable def ep495 := @Enclosure.Complex.IsNear.of_eq qz117 (Complex.mk (@HMul.hMul Real Real Real qz0 qz130 (Real.cos qz131)) (@HMul.hMul Real Real Real qz0 qz130 (@Neg.neg Real Real.instNeg (Real.sin qz131)))) Bool.false 14189118589 137438953472 674080293349 2905665634828288 Bool.false 52845631509 274877906944 2705363773493 11622662539313152 (BSN.cpow_neg_s_mk qz13 88388 1000 21 qz14 rfl)

noncomputable abbrev qz409 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 21) qz15)

noncomputable def ep496 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz408) 2402589 524288 1 524288 57204 57205 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz408) (Real.sqrt qz409) Bool.false 2402589 524288 1 524288 (BSN.sqrt_natCast_div_one 21) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz409) Bool.false 2402589 524288 1 524288 2402589 524288 1 524288 (BSN.sqrt_enclosure 21 1 1201294 1201295 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep497 := BSN.log_dyadic_bound 5 37 3 2 28112415 262144 84566 173000 1875 71285 42 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 5) (BSN.artanhQ 37) 0 2 173000 28112415 1875 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep498 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz559 88388 1000 0 1 3427824127778039 1125899906842624 125000000042283 10570750000000000000 75744629751511327783 281474976710656000 2762125000934327451 2642687500000000000000 qz18 (BSN.isNear_log_sfrac 21 1 3427824127778039 1125899906842624 125000000042283 10570750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz409) Bool.false 28754672900871880179712 9444732965739290427392 1000000000338264 84566000000000000000 3427824127778039 1125899906842624 125000000042283 10570750000000000000 (BSN.log_rat_reduce_isNear 21 1 4 42 32 71285 262144 24973259072661432 36028797018963968 84566 1000000000000000 rfl rfl rfl rfl (ep497 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep499 := nat_lit 78400248193744134849805388774865121

noncomputable def ep500 := BSN.sin_dyadic_bound_f 529150681 1073741824 2 1 524288 169298 ep499 ep103 ep499 ep499 ep104 ep499 248042 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 529150681) qz287 0 1 ep499 ep103 ep499 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 529150681) qz288 0 1 ep499 ep104 ep499 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz410 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 141085367) qz23)

noncomputable def ep501 := @Enclosure.Real.IsNear.cos_image qz131 qz410 Bool.false 141085367 524288 549 524288 Bool.false 248042 524288 1 84566 (@Enclosure.Real.IsNear.recentre' qz131 Bool.false 75744629751511327783 281474976710656000 2762125000934327451 2642687500000000000000 141085367 524288 549 524288 (ep498 rfl) rfl) (Enclosure.sfrac_false_div 141085367 524288) (BSN.cos_reduce3 qz410 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 37235668961966040285184) qz25) 226375608064910080 72057594037927936 Bool.false 248042 524288 42 1000000000000000 169132 84566 (BSN.sin_reduce_arg_pos_rat_q3 141085367 524288 226375608064910080 72057594037927936 42 37235668961966040285184 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 248042 524288 37235668961966040285184 75557863725914323419136 529150681 1073741824 169298 169132 (ep500 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep502 := BSN.cos_dyadic_bound_f 529150681 1073741824 2 1 524288 169298 ep499 ep228 ep499 ep499 ep229 ep499 461901 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 529150681) qz292 0 1 ep499 ep228 ep499 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 529150681) qz293 0 1 ep499 ep229 ep499 rfl rfl rfl rfl) rfl rfl

noncomputable def ep503 := @Enclosure.Real.IsNear.sin_image qz131 qz410 Bool.false 141085367 524288 549 524288 Bool.true 461901 524288 1 84566 (@Enclosure.Real.IsNear.recentre' qz131 Bool.false 75744629751511327783 281474976710656000 2762125000934327451 2642687500000000000000 141085367 524288 549 524288 (ep498 rfl) rfl) (Enclosure.sfrac_false_div 141085367 524288) (BSN.sin_reduce3 qz410 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 37235668961966040285184) qz25) 226375608064910080 72057594037927936 Bool.false 461901 524288 42 1000000000000000 169132 84566 (BSN.sin_reduce_arg_pos_rat_q3 141085367 524288 226375608064910080 72057594037927936 42 37235668961966040285184 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 461901 524288 37235668961966040285184 75557863725914323419136 529150681 1073741824 169298 169132 (ep502 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz411 := (@Enclosure.Real.IsNear.recentre' qz130 Bool.false 114409 524288 1 524288 114409 524288 1 524288 (ep496 rfl rfl) rfl)

noncomputable def ep504 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz130 (Real.cos qz131)) (@HMul.hMul Real Real Real qz0 qz130 (@Neg.neg Real Real.instNeg (Real.sin qz131))) Bool.false 14189118589 137438953472 674080293349 2905665634828288 Bool.false 52845631509 274877906944 2705363773493 11622662539313152 (@Enclosure.Real.IsNear.mulLit_ff qz130 (Real.cos qz131) 114409 524288 1 524288 124021 262144 23475511 22168469504 14189118589 137438953472 674080293349 2905665634828288 qz411 (@Enclosure.Real.IsNear.recentre' (Real.cos qz131) Bool.false 248042 524288 46951022 44336939008 124021 262144 23475511 22168469504 (ep501 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz130 (@Neg.neg Real Real.instNeg (Real.sin qz131)) 114409 524288 1 524288 461901 524288 23475511 22168469504 52845631509 274877906944 2705363773493 11622662539313152 qz411 (@Enclosure.Real.IsNear.neg (Real.sin qz131) Bool.true 461901 524288 23475511 22168469504 (@Enclosure.Real.IsNear.recentre' (Real.sin qz131) Bool.true 461901 524288 46951022 44336939008 461901 524288 23475511 22168469504 (ep503 rfl rfl) rfl)) rfl)

noncomputable def ep505 := @ep431 14189118589 137438953472 674080293349 2905665634828288 Bool.false 52845631509 274877906944 2705363773493 11622662539313152 Bool.false 14107583223121880023040 51323088785 68719476736 42079558788781 5811331269656576 Bool.false 1153124731807774801920 16780173345 274877906944 84164003082231 11622662539313152 (ep432 (BSN.head_sum_c_succ qz5 20 21 rfl rfl) (ep494 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep495 ep504) rfl rfl

noncomputable abbrev qz412 := (@Nat.cast Real Real.instNatCast 22)

noncomputable abbrev qz132 := (@Inv.inv Real Real.instInv (Real.sqrt qz412))

noncomputable abbrev qz560 := (Real.log (Enclosure.sfrac Bool.false 22 1))

noncomputable abbrev qz133 := (@HMul.hMul Real Real Real qz267 qz284 qz560)

noncomputable def ep506 := @Enclosure.Complex.IsNear.of_eq qz116 (Complex.mk (@HMul.hMul Real Real Real qz0 qz132 (Real.cos qz133)) (@HMul.hMul Real Real Real qz0 qz132 (@Neg.neg Real Real.instNeg (Real.sin qz133)))) Bool.true 58264468413 274877906944 2646132506481 11622662539313152 Bool.true 3151161789 137438953472 1313238309843 5811331269656576 (BSN.cpow_neg_s_mk qz13 88388 1000 22 qz14 rfl)

noncomputable abbrev qz413 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 22) qz15)

noncomputable def ep507 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz412) 2459129 524288 1 524288 55889 55890 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz412) (Real.sqrt qz413) Bool.false 2459129 524288 1 524288 (BSN.sqrt_natCast_div_one 22) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz413) Bool.false 2459129 524288 1 524288 2459129 524288 1 524288 (BSN.sqrt_enclosure 22 1 1229564 1229565 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep508 := BSN.log_dyadic_bound 6 38 4 3 316148320320 262144 84566 2667271104 699840 83480 44 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 6) (BSN.artanhQ 38) 0 3 2667271104 316148320320 699840 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep509 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz560 88388 1000 0 1 3480201253952759 1125899906842624 125000000042283 10570750000000000000 76902007108594115623 281474976710656000 2762125000934327451 2642687500000000000000 qz18 (BSN.isNear_log_sfrac 22 1 3480201253952759 1125899906842624 125000000042283 10570750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz413) Bool.false 29194044080518145769472 9444732965739290427392 1000000000338264 84566000000000000000 3480201253952759 1125899906842624 125000000042283 10570750000000000000 (BSN.log_rat_reduce_isNear 22 1 4 44 32 83480 262144 24973259072661432 36028797018963968 84566 1000000000000000 rfl rfl rfl rfl (ep508 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep510 := nat_lit 24517233793602514712205713316709267663904552699232649586709200811455402681665

noncomputable def ep511 := nat_lit 37090729069764372334845404805795787827449360989030398770470960378365814081

noncomputable def ep512 := nat_lit 64151751136179348595806166126457745939457958104008033033848096760818224276801

noncomputable def ep513 := BSN.sin_dyadic_bound_f 1570934839 1073741824 3 2 524288 169298 ep510 ep66 ep511 ep512 ep69 ep511 521247 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1570934839) qz287 0 2 ep510 ep66 ep511 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1570934839) qz288 0 2 ep512 ep69 ep511 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz414 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 71620575) qz16)

noncomputable def ep514 := @Enclosure.Real.IsNear.cos_image qz133 qz414 Bool.false 71620575 262144 549 524288 Bool.true 521247 524288 1 84566 (@Enclosure.Real.IsNear.recentre' qz133 Bool.false 76902007108594115623 281474976710656000 2762125000934327451 2642687500000000000000 71620575 262144 549 524288 (ep509 rfl) rfl) (Enclosure.sfrac_false_div 71620575 262144) (BSN.cos_reduce1 qz414 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 55272355927713843773440) qz19) 226375608064910080 72057594037927936 Bool.false 521247 524288 43 1000000000000000 169132 84566 (BSN.sin_reduce_arg_pos_rat_q1 71620575 262144 226375608064910080 72057594037927936 43 55272355927713843773440 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 521247 524288 55272355927713843773440 37778931862957161709568 1570934839 1073741824 169298 169132 (ep513 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep515 := nat_lit 13637170209365736783374216466974391274536951215568818836514209766532275184961

noncomputable def ep516 := nat_lit 40837329169957681605452958591311582247955954924728395712001687378840093926721

noncomputable def ep517 := BSN.cos_dyadic_bound_f 1570934839 1073741824 3 2 524288 169298 ep515 ep73 ep511 ep516 ep75 ep511 56382 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1570934839) qz292 0 2 ep515 ep73 ep511 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1570934839) qz293 0 2 ep516 ep75 ep511 rfl rfl rfl rfl) rfl rfl

noncomputable def ep518 := @Enclosure.Real.IsNear.sin_image qz133 qz414 Bool.false 71620575 262144 549 524288 Bool.false 56382 524288 1 84566 (@Enclosure.Real.IsNear.recentre' qz133 Bool.false 76902007108594115623 281474976710656000 2762125000934327451 2642687500000000000000 71620575 262144 549 524288 (ep509 rfl) rfl) (Enclosure.sfrac_false_div 71620575 262144) (BSN.sin_reduce1 qz414 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 55272355927713843773440) qz19) 226375608064910080 72057594037927936 Bool.false 56382 524288 43 1000000000000000 169132 84566 (BSN.sin_reduce_arg_pos_rat_q1 71620575 262144 226375608064910080 72057594037927936 43 55272355927713843773440 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 56382 524288 55272355927713843773440 37778931862957161709568 1570934839 1073741824 169298 169132 (ep517 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz415 := (@Enclosure.Real.IsNear.recentre' qz132 Bool.false 111779 524288 1 524288 111779 524288 1 524288 (ep507 rfl rfl) rfl)

noncomputable def ep519 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz132 (Real.cos qz133)) (@HMul.hMul Real Real Real qz0 qz132 (@Neg.neg Real Real.instNeg (Real.sin qz133))) Bool.true 58264468413 274877906944 2646132506481 11622662539313152 Bool.true 3151161789 137438953472 1313238309843 5811331269656576 (@Enclosure.Real.IsNear.mulLit_ft qz132 (Real.cos qz133) 111779 524288 1 524288 521247 524288 23475511 22168469504 58264468413 274877906944 2646132506481 11622662539313152 qz415 (@Enclosure.Real.IsNear.recentre' (Real.cos qz133) Bool.true 521247 524288 46951022 44336939008 521247 524288 23475511 22168469504 (ep514 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz132 (@Neg.neg Real Real.instNeg (Real.sin qz133)) 111779 524288 1 524288 28191 262144 23475511 22168469504 3151161789 137438953472 1313238309843 5811331269656576 qz415 (@Enclosure.Real.IsNear.neg (Real.sin qz133) Bool.false 28191 262144 23475511 22168469504 (@Enclosure.Real.IsNear.recentre' (Real.sin qz133) Bool.false 56382 524288 46951022 44336939008 28191 262144 23475511 22168469504 (ep518 rfl rfl) rfl)) rfl)

noncomputable def ep520 := @ep429 58264468413 274877906944 2646132506481 11622662539313152 Bool.true 3151161789 137438953472 1313238309843 5811331269656576 Bool.false 10103679441479319683072 147027886727 274877906944 86805250084043 11622662539313152 Bool.false 1440064706613319041024 10477849767 274877906944 86790479701917 11622662539313152 (ep430 (BSN.head_sum_c_succ qz5 21 22 rfl rfl) (ep505 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep506 ep519) rfl rfl

noncomputable def ep521 := @Enclosure.Complex.IsNear.mul qz111 (@HAdd.hAdd Complex Complex Complex qz4 qz112 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1))))) Bool.false 206081424864067437085199 ep288 ep423 ep290 Bool.true

noncomputable abbrev qz134 := (Complex.re qz389)

noncomputable abbrev qz135 := (Complex.im qz389)

noncomputable def ep522 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 qz134 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz112 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz135 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz112 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1))))))) 751447213227699334571 9261246734126624538624 87107389384160636821205

noncomputable def ep523 := nat_lit 783186591318152130733277184

noncomputable def ep524 := nat_lit 48949161957384508170829824000

noncomputable def ep525 := nat_lit 636190307662168637001146259875667156918075392

noncomputable def ep526 := @Enclosure.Real.IsNear.mulLit_ff qz134 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz112 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))))) 11144073419 68719476736 1291815480245 5811331269656576 67430210209

noncomputable abbrev qz416 := (@Nat.cast Real Real.instNatCast 23)

noncomputable abbrev qz136 := (@Inv.inv Real Real.instInv (Real.sqrt qz416))

noncomputable abbrev qz417 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) qz531 (Real.log (Enclosure.sfrac Bool.false 23 1)))

noncomputable abbrev qz137 := (Real.cos qz417)

noncomputable abbrev qz138 := (Real.sin qz417)

noncomputable abbrev qz418 := (@Neg.neg Real Real.instNeg qz138)

noncomputable def ep527 := @Enclosure.Complex.IsNear.of_eq qz111 (Complex.mk (@HMul.hMul Real Real Real qz0 qz136 qz137) (@HMul.hMul Real Real Real qz0 qz136 qz418)) Bool.false 11144073419 68719476736 1291815480245 5811331269656576 Bool.true 18014023701 137438953472 645081170897 2905665634828288 (BSN.cpow_neg_s_mk qz13 88388 1000 23 qz14 rfl)

noncomputable abbrev qz419 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 23) qz15)

noncomputable def ep528 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz416) 2514397 524288 1 524288 54660 54661 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz416) (Real.sqrt qz419) Bool.false 2514397 524288 1 524288 (BSN.sqrt_natCast_div_one 23) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz419) Bool.false 2514397 524288 1 524288 2514397 524288 1 524288 (BSN.sqrt_enclosure 23 1 1257198 1257199 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep529 := BSN.log_dyadic_bound 7 39 4 3 369468094905 262144 84566 4046006391 1764735 95133 46 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 7) (BSN.artanhQ 39) 0 3 4046006391 369468094905 1764735 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz420 := (Real.log (Enclosure.sfrac Bool.false 23 1))

noncomputable abbrev qz139 := qz420

noncomputable abbrev qz421 := (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 23) qz15))

noncomputable def ep530 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz139 88388 1000 0 1 3530250507853047 1125899906842624 125000000042283 10570750000000000000 78007945472028779559 281474976710656000 2762125000934327451 2642687500000000000000 qz18 (BSN.isNear_log_sfrac 23 1 3530250507853047 1125899906842624 125000000042283 10570750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' qz421 Bool.false 29613887652180132888576 9444732965739290427392 1000000000338264 84566000000000000000 3530250507853047 1125899906842624 125000000042283 10570750000000000000 (BSN.log_rat_reduce_isNear 23 1 4 46 32 95133 262144 24973259072661432 36028797018963968 84566 1000000000000000 rfl rfl rfl rfl (ep529 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep531 := nat_lit 283774433298858363792059615035146496

noncomputable def ep532 := BSN.cos_dyadic_bound_f 729866308 1073741824 2 1 524288 169298 ep531 ep228 ep531 ep531 ep229 ep531 407756 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 729866308) qz292 0 1 ep531 ep228 ep531 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 729866308) qz293 0 1 ep531 ep229 ep531 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz140 := qz417

noncomputable abbrev qz422 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 145301121) qz23)

noncomputable def ep533 := @Enclosure.Real.IsNear.cos_image qz140 qz422 Bool.false 145301121 524288 549 524288 Bool.false 407756 524288 1 84566 (@Enclosure.Real.IsNear.recentre' qz140 Bool.false 78007945472028779559 281474976710656000 2762125000934327451 2642687500000000000000 145301121 524288 549 524288 (ep530 rfl) rfl) (Enclosure.sfrac_false_div 145301121 524288) (BSN.cos_reduce0 qz422 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 51359775547829855977472) qz25) 226375608064910080 72057594037927936 Bool.false 407756 524288 44 1000000000000000 169132 84566 (BSN.sin_reduce_arg_pos_rat_q0 145301121 524288 226375608064910080 72057594037927936 44 51359775547829855977472 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 407756 524288 51359775547829855977472 75557863725914323419136 729866308 1073741824 169298 169132 (ep532 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep534 := BSN.sin_dyadic_bound_f 729866308 1073741824 2 1 524288 169298 ep531 ep103 ep531 ep531 ep104 ep531 329562 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 729866308) qz287 0 1 ep531 ep103 ep531 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 729866308) qz288 0 1 ep531 ep104 ep531 rfl rfl rfl rfl) rfl rfl

noncomputable def ep535 := @Enclosure.Real.IsNear.sin_image qz140 qz422 Bool.false 145301121 524288 549 524288 Bool.false 329562 524288 1 84566 (@Enclosure.Real.IsNear.recentre' qz140 Bool.false 78007945472028779559 281474976710656000 2762125000934327451 2642687500000000000000 145301121 524288 549 524288 (ep530 rfl) rfl) (Enclosure.sfrac_false_div 145301121 524288) (BSN.sin_reduce0 qz422 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 51359775547829855977472) qz25) 226375608064910080 72057594037927936 Bool.false 329562 524288 44 1000000000000000 169132 84566 (BSN.sin_reduce_arg_pos_rat_q0 145301121 524288 226375608064910080 72057594037927936 44 51359775547829855977472 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 329562 524288 51359775547829855977472 75557863725914323419136 729866308 1073741824 169298 169132 (ep534 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz423 := (@Enclosure.Real.IsNear.recentre' qz136 Bool.false 109321 524288 1 524288 109321 524288 1 524288 (ep528 rfl rfl) rfl)

noncomputable def ep536 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz136 qz137) (@HMul.hMul Real Real Real qz0 qz136 qz418) Bool.false 11144073419 68719476736 1291815480245 5811331269656576 Bool.true 18014023701 137438953472 645081170897 2905665634828288 (@Enclosure.Real.IsNear.mulLit_ff qz136 qz137 109321 524288 1 524288 101939 131072 23475511 22168469504 11144073419 68719476736 1291815480245 5811331269656576 qz423 (@Enclosure.Real.IsNear.recentre' qz137 Bool.false 407756 524288 46951022 44336939008 101939 131072 23475511 22168469504 (ep533 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz136 qz418 109321 524288 1 524288 164781 262144 23475511 22168469504 18014023701 137438953472 645081170897 2905665634828288 qz423 (@Enclosure.Real.IsNear.neg qz138 Bool.false 164781 262144 23475511 22168469504 (@Enclosure.Real.IsNear.recentre' qz138 Bool.false 329562 524288 46951022 44336939008 164781 262144 23475511 22168469504 (ep535 rfl rfl) rfl)) rfl)

noncomputable def ep537 := @ep526 134768877384 0 1 751447213227699334571 9261246734126624538624 87107389384160636821205 ep523 (@Enclosure.Complex.IsNear.re_isNear qz111 Bool.false 11144073419 68719476736 1291815480245 5811331269656576 Bool.true 18014023701 137438953472 645081170897 2905665634828288 (ep527 ep536))

noncomputable def ep538 := @Enclosure.Complex.IsNear.re_isNear (@HAdd.hAdd Complex Complex Complex qz4 qz112 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1))))) Bool.false 67430210209 134768877384 0 1 Bool.false

noncomputable def ep539 := @Enclosure.Complex.IsNear.addLitP qz112 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) Bool.false 243427767 488293034 0 1 Bool.true 63528875

noncomputable def ep540 := @ep539 244146517 0 1 Bool.false 1 552 0 1 Bool.false 22097 69000 0 1 Bool.false 134860420418 67430210209 134768877384 0 1 Bool.false 1011413211149 1011413211149 16846109673000 0 1

noncomputable abbrev qz141 := (@HDiv.hDiv Complex Complex Complex qz362 qz390 (@HSub.hSub Complex Complex Complex qz354 qz272 (1 : Complex)))

noncomputable def ep541 := @Enclosure.Complex.IsNear.addLitP qz141 qz89 Bool.true 46000000 31250754176 0 1 Bool.true 8131696000 31250754176 0 1

noncomputable def ep542 := @Enclosure.Complex.IsNear.of_eq qz141 (Complex.mk (Enclosure.sfrac Bool.true 46000000 31250754176) (Enclosure.sfrac Bool.true 8131696000 31250754176)) Bool.true 46000000 31250754176 0 1 Bool.true 8131696000 31250754176 0 1

noncomputable def ep543 := @ep541 Bool.false 1 2 0 1 Bool.false 0 1 0 1 Bool.false 31158754176 243427767 488293034 0 1 Bool.true 8131696000 63528875 244146517 0 1 (ep542 (BSN.N_div_s_sub_one_mk qz13 88388 1000 23 qz14 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 46000000 31250754176) (Enclosure.sfrac Bool.true 8131696000 31250754176) Bool.true 46000000 31250754176 0 1 Bool.true 8131696000 31250754176 0 1 (Enclosure.Real.IsNear.const Bool.true 46000000 31250754176) (Enclosure.Real.IsNear.const Bool.true 8131696000 31250754176))) qz90 rfl

noncomputable abbrev qz142 := (@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 1)))

noncomputable abbrev qz424 := (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz553 qz554 1))

noncomputable abbrev qz143 := qz424

noncomputable def ep544 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@HAdd.hAdd Complex Complex Complex qz4 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz142) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz143)) Bool.false 1 552 0 1

noncomputable def ep545 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz142) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz143) Bool.false 0 1 0 1 Bool.false

noncomputable def ep546 := @ep545 0 1 0 1 Bool.false 1 552 0 1 Bool.false 22097 69000 0 1 Bool.false 1 1 552 0 1 Bool.false 22097 22097 69000 0

noncomputable def ep547 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (Complex.mk qz10 qz10) Bool.false 0 1 0 1 Bool.false

noncomputable def ep548 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz142) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz143 Bool.false 1 552 0 1 Bool.false 22097 69000 0 1

noncomputable abbrev qz144 := (Complex.re qz424)

noncomputable abbrev qz145 := (Complex.im qz424)

noncomputable def ep549 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz142) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) qz144) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz142) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) qz145) 1 552 0 1 0 1 0

noncomputable def ep550 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz142) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) qz144 1 24 0 1 1 23 0 1 1

noncomputable def ep551 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz142)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz142)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) 1 24 0 1 0 1 0 1 1

noncomputable def ep552 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz142)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 1 2 0 1 1 24 0

noncomputable def ep553 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz142) (Complex.mk (Enclosure.sfrac Bool.false 1 12) qz10) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (BSN.bern_coeff_mk 1 1 6 2 Bool.false BSN.bern_real_1 EMRow25.d8 rfl) qz379

noncomputable def ep554 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) qz5 Bool.false 1 2 0 1 Bool.false 88388 1000 0 1 (BSN.ascPochhammer_one_eval qz5)

noncomputable def ep555 := ep554 (@Enclosure.Complex.IsNear.of_eq qz5 (Complex.mk qz84 qz13) Bool.false 1 2 0 1 Bool.false 88388 1000 0 1 (BSN.s_crit_mk qz13 Bool.false 88388 1000 qz14) (@Enclosure.Complex.IsNear.mk qz84 qz13 Bool.false 1 2 0 1 Bool.false 88388 1000 0 1 qz371 qz18))

noncomputable def ep556 := @ep552 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz142) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep553) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 88388 1000 0 1 ep555)

noncomputable def ep557 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz142)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 88388 1000 0 1 0 1 0

noncomputable def ep558 := @ep557 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz142) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep553) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 88388 1000 0 1 ep555)

noncomputable def ep559 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz142)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz142)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) 22097 3000 0 1 0 1 0 1 22097

noncomputable def ep560 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz142)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 88388 1000 0 1 22097 3000 0

noncomputable def ep561 := @ep560 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz142) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep553) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 88388 1000 0 1 ep555)

noncomputable def ep562 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz142)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 1 2 0 1 0 1 0

noncomputable def ep563 := @ep562 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz142) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep553) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 88388 1000 0 1 ep555)

noncomputable def ep564 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz142) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 24 0 1 Bool.false 22097 3000 0 1 (@ep551 1 24 0 1 (ep556 rfl) (ep558 rfl) rfl rfl) (@ep559 22097 3000 0 1 (ep561 rfl) (ep563 rfl) rfl rfl)

noncomputable def ep565 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz142) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 22097 3000 0 1 ep564

noncomputable abbrev qz146 := (@Enclosure.Complex.IsNear.re_isNear qz424 Bool.false 1 23 0 1 Bool.false 0 1 0 1 (@Enclosure.Complex.IsNear.of_eq qz424 (Complex.mk (Enclosure.sfrac Bool.false 1 23) qz283) Bool.false 1 23 0 1 Bool.false 0 1 0 1 (BSN.natCast_pow_inv_mk 23 1 23 EMRow25.d9 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 23) qz283 Bool.false 1 23 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 23) qz295)))

noncomputable def ep566 := @ep550 552 0 1 ep565 qz146

noncomputable def ep567 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz142) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) qz145 22097 3000 0 1 0 1 0 1 0

noncomputable def ep568 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz142) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 22097 3000 0 1 ep564

noncomputable abbrev qz147 := (@Enclosure.Complex.IsNear.im_isNear qz424 Bool.false 1 23 0 1 Bool.false 0 1 0 1 (@Enclosure.Complex.IsNear.of_eq qz424 (Complex.mk (Enclosure.sfrac Bool.false 1 23) qz283) Bool.false 1 23 0 1 Bool.false 0 1 0 1 (BSN.natCast_pow_inv_mk 23 1 23 EMRow25.d9 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 23) qz283 Bool.false 1 23 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 23) qz295)))

noncomputable def ep569 := @ep567 1 0 1 ep568 qz147

noncomputable def ep570 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz142) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) qz145) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz142) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) qz144) 0 1 0 1 22097 69000 0

noncomputable def ep571 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz142) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) qz145 1 24 0 1 0 1 0 1 0

noncomputable def ep572 := @ep571 1 0 1 ep565 qz147

noncomputable def ep573 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz142) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) qz144 22097 3000 0 1 1 23 0 1 22097

noncomputable def ep574 := @ep573 69000 0 1 ep568 qz146

noncomputable def ep575 := @ep546 1 (@ep547 0 1 0 1 (BSN.bern_sum_base qz5 23) qz105) (ep548 (@ep549 1 1 1 552 0 1 (ep566 rfl) (ep569 rfl) rfl rfl) (@ep570 1 22097 22097 69000 0 1 (ep572 rfl) (ep574 rfl) rfl rfl)) rfl rfl rfl rfl rfl

noncomputable def ep576 := ep540 (ep543 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep544 Bool.false 22097 69000 0 1 (BSN.bern_sum_succ qz5 23 0 1 1 rfl rfl) (ep575 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl rfl

noncomputable def ep577 := @Enclosure.Real.IsNear.mulLit_tf qz135 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz112 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))))) 18014023701 137438953472 645081170897 2905665634828288 1011413211149

noncomputable def ep578 := @ep577 16846109673000 0 1 6073207185714201147483 771770561177218711552000 652443618508691614730653 ep524 (@Enclosure.Complex.IsNear.im_isNear qz111 Bool.false 11144073419 68719476736 1291815480245 5811331269656576 Bool.true 18014023701 137438953472 645081170897 2905665634828288 (ep527 ep536))

noncomputable def ep579 := @Enclosure.Complex.IsNear.im_isNear (@HAdd.hAdd Complex Complex Complex qz4 qz112 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1))))) Bool.false 67430210209 134768877384 0 1 Bool.false

noncomputable def ep580 := @Enclosure.Real.IsNear.addLit_ft_n (@HMul.hMul Real Real Real qz0 qz134 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz112 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz135 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz112 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1))))))) 11271263081991005348431 1157655841765828067328000 261311848617316604650301

noncomputable def ep581 := nat_lit 19579664782953803268331929600

noncomputable def ep582 := nat_lit 391593295659076065366638592

noncomputable def ep583 := nat_lit 399140129553915456102508301302802780419784704

noncomputable def ep584 := @Enclosure.Real.IsNear.mulLit_ff qz134 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz112 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))))) 11144073419 68719476736 1291815480245 5811331269656576 1011413211149

noncomputable def ep585 := @ep584 16846109673000 0 1 11271263081991005348431 1157655841765828067328000 261311848617316604650301 ep581 (@Enclosure.Complex.IsNear.re_isNear qz111 Bool.false 11144073419 68719476736 1291815480245 5811331269656576 Bool.true 18014023701 137438953472 645081170897 2905665634828288 (ep527 ep536))

noncomputable def ep586 := @Enclosure.Real.IsNear.mulLit_tf qz135 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz112 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))))) 18014023701 137438953472 645081170897 2905665634828288 67430210209

noncomputable def ep587 := @ep586 134768877384 0 1 404896468289446054503 6174164489417749692416 43497958955452563087473 ep582 (@Enclosure.Complex.IsNear.im_isNear qz111 Bool.false 11144073419 68719476736 1291815480245 5811331269656576 Bool.true 18014023701 137438953472 645081170897 2905665634828288 (ep527 ep536))

noncomputable abbrev qz425 := (ep576 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable def ep588 := @ep521 129293649444560259741763 ep288 812069932129981586341317 ep420 (@ep522 ep523 6073207185714201147483 771770561177218711552000 652443618508691614730653 ep524 ep525 206081424864067437085199 ep288 ep423 ep290 (ep537 (@ep538 1011413211149 16846109673000 0 1 qz425) rfl) (ep578 (@ep579 1011413211149 16846109673000 0 1 qz425) rfl) rfl rfl) (@ep580 ep581 404896468289446054503 6174164489417749692416 43497958955452563087473 ep582 ep583 129293649444560259741763 ep288 812069932129981586341317 ep420 (ep585 (@ep579 1011413211149 16846109673000 0 1 qz425) rfl) (ep587 (@ep538 1011413211149 16846109673000 0 1 qz425) rfl) rfl rfl)

noncomputable def ep589 := @ep426 ep419 ep420 (@ep427 11622662539313152 (BSN.head_sum_c_eq qz5 23) (ep428 (BSN.head_sum_c_succ qz5 22 23 rfl rfl) (ep520 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))) ep588 rfl rfl rfl

noncomputable def ep590 := @Enclosure.Complex.IsNear.re_isNear (zetaApproximant qz5 1 23) Bool.false ep287 ep288 ep289 ep290 Bool.true 41038146288510511646263 ep288 ep419 ep420 (@ep421 ep290 Bool.true 41038146288510511646263 ep288 ep419 ep420 (BSN.zetaApproximant_eq_folded' qz5 1 23 rfl) (ep589 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

noncomputable def ep591 := @Enclosure.Real.IsNear.mulLit_ft (Real.sin (@HSub.hSub Real Real Real qz357 (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz64 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz65 (@Nat.cast Complex Complex.instNatCast j))))) qz66)) (Complex.im (zetaApproximant qz5 1 23)) 25 65536 5585579

noncomputable def ep592 := @Enclosure.Real.IsNear.recentre' (Real.sin (@HSub.hSub Real Real Real qz357 (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz64 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz65 (@Nat.cast Complex Complex.instNatCast j))))) qz66)) Bool.false 200 524288 11171158

noncomputable def ep593 := @Enclosure.Real.IsNear.sin_image (@HSub.hSub Real Real Real qz357 (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz64 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz65 (@Nat.cast Complex Complex.instNatCast j))))) qz66) qz358 Bool.false 9470771 131072 129

noncomputable def ep594 := nat_lit 18118993288719373273541211797949770920137648807047338644318473854143007031296

noncomputable def ep595 := nat_lit 54226259965658656152515176829448237984745516345008920005757399777594212089856

noncomputable def ep596 := BSN.cos_dyadic_bound_f 1686218944 1073741824 3 2 524288 169298 ep594 ep73 ep415 ep595 ep75 ep415 200 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1686218944) qz292 0 2 ep594 ep73 ep415 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1686218944) qz293 0 2 ep595 ep75 ep415 rfl rfl rfl rfl) rfl rfl

noncomputable def ep597 := @ep593 262144 Bool.false 200 524288 1 84566 (@ep294 9470771 131072 129 262144 ep413 rfl) (Enclosure.sfrac_false_div 9470771 131072) (BSN.sin_reduce1 qz358 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 29664277375586362458112) qz302) 226375608064910080 72057594037927936 Bool.false 200 524288 11 1000000000000000 169132 84566 (BSN.sin_reduce_arg_pos_rat_q1 9470771 131072 226375608064910080 72057594037927936 11 29664277375586362458112 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 200 524288 29664277375586362458112 18889465931478580854784 1686218944 1073741824 169298 169132 (ep596 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep598 := @Enclosure.Complex.IsNear.im_isNear (zetaApproximant qz5 1 23) Bool.false ep287 ep288 ep289 ep290 Bool.true 41038146288510511646263 ep288 ep419 ep420 (@ep421 ep290 Bool.true 41038146288510511646263 ep288 ep419 ep420 (BSN.zetaApproximant_eq_folded' qz5 1 23 rfl) (ep589 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

theorem EMRow25.d10 : Enclosure.Real.IsNear (hardyZApproximantEM 1 23 qz13) Bool.true ep271 ep272 ep273 ep274 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantEM 1 23 qz13) ep275 Bool.true ep271 ep272 ep273 ep274 (@Eq.refl Real ep275) (@ep276 Bool.true ep271 ep272 ep273 ep274 (BSN.re_exp_mul (@HSub.hSub Real Real Real qz357 (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz64 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz65 (@Nat.cast Complex Complex.instNatCast j))))) qz66) (zetaApproximant qz5 1 23)) (@ep278 ep279 ep280 ep281 41038146288510511646263 ep282 ep283 ep284 ep285 ep271 ep272 ep273 ep274 (@ep286 11084234752 ep287 ep288 ep289 ep290 ep277 ep279 ep280 ep281 (@ep291 22168469504 524287 524288 5585579 11084234752 (ep418 rfl rfl) rfl) ep590 rfl) (@ep591 11084234752 41038146288510511646263 ep288 ep419 ep420 41038146288510511646263 ep282 ep283 ep284 (@ep592 22168469504 25 65536 5585579 11084234752 (ep597 rfl rfl) rfl) ep598 rfl) rfl rfl))

noncomputable abbrev qz578 := (@HAdd.hAdd Complex Complex Complex (@instHAdd Complex Complex.instAdd) (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (2 : Complex)) (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul) Complex.I ↑(Enclosure.sfrac Bool.false 90753 1000)))

noncomputable abbrev qz561 := qz578

noncomputable abbrev qz426 := qz561

noncomputable abbrev qz148 := (BSN.headSumC qz426 9)

noncomputable abbrev qz149 := qz426

noncomputable abbrev qz562 := (@Neg.neg Complex Complex.instNeg qz578)

noncomputable abbrev qz427 := qz562

noncomputable abbrev qz150 := qz427

noncomputable abbrev qz428 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 8) qz150)

noncomputable def ep599 := @Enclosure.Complex.IsNear.of_eq qz148 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz149 8) qz428) Bool.false 243218440123 68719476736 10683847080823 2905665634828288 Bool.true 48783384305 274877906944 42678671894393 11622662539313152

noncomputable def ep600 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz149 8) qz428 Bool.false 878032596179 274877906944 38244673372875 11622662539313152 Bool.true 27575262023 274877906944 38204753316047 11622662539313152 Bool.false

noncomputable abbrev qz429 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 7) qz150)

noncomputable def ep601 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz149 8) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz149 7) qz429) Bool.false 878032596179 274877906944 38244673372875 11622662539313152 Bool.true 27575262023 274877906944 38204753316047 11622662539313152

noncomputable def ep602 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz149 7) qz429 Bool.false 398224147295 137438953472 16728979307677 5811331269656576 Bool.false 18376106437 137438953472 16710860365649 5811331269656576 Bool.false

noncomputable abbrev qz430 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 6) qz150)

noncomputable def ep603 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz149 7) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz149 6) qz430) Bool.false 398224147295 137438953472 16728979307677 5811331269656576 Bool.false 18376106437 137438953472 16710860365649 5811331269656576

noncomputable def ep604 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz149 6) qz430 Bool.false 714750678485 274877906944 28290417484749 11622662539313152 Bool.true 20089270331 137438953472 14127560642693 5811331269656576 Bool.false

noncomputable abbrev qz431 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 5) qz150)

noncomputable def ep605 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz149 6) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz149 5) qz431) Bool.false 714750678485 274877906944 28290417484749 11622662539313152 Bool.true 20089270331 137438953472 14127560642693 5811331269656576

noncomputable def ep606 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz149 5) qz431 Bool.false 711934705795 274877906944 22636895176599 11622662539313152 Bool.false 10339798211 34359738368 1411246510101 726416408707072 Bool.false

noncomputable abbrev qz432 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 4) qz150)

noncomputable def ep607 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz149 5) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz149 4) qz432) Bool.false 711934705795 274877906944 22636895176599 11622662539313152 Bool.false 10339798211 34359738368 1411246510101 726416408707072

noncomputable def ep608 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz149 4) qz432 Bool.false 287983318349 137438953472 8147367997789 5811331269656576 Bool.false 25692032725 68719476736 4064120577945 2905665634828288 Bool.false

noncomputable def ep609 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz149 4) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz149 3) (@HPow.hPow Complex Complex Complex qz6 qz8 qz150)) Bool.false 287983318349 137438953472 8147367997789 5811331269656576 Bool.false 25692032725 68719476736 4064120577945 2905665634828288

noncomputable def ep610 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz149 3) (@HPow.hPow Complex Complex Complex qz6 qz8 qz150) Bool.false 58590659471 34359738368 2241688097267 2905665634828288 Bool.true 1776945645 34359738368 557861059285 726416408707072 Bool.false

noncomputable def ep611 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz149 3) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz149 2) (@HPow.hPow Complex Complex Complex qz6 qz9 qz150)) Bool.false 58590659471 34359738368 2241688097267 2905665634828288 Bool.true 1776945645 34359738368 557861059285 726416408707072

noncomputable def ep612 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz149 2) (@HPow.hPow Complex Complex Complex qz6 qz9 qz150) Bool.false 1 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable def ep613 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz149 2) (Complex.mk (Enclosure.sfrac Bool.false 1 1) qz10) Bool.false 1 1 0 1 Bool.false 0 1 0 1 (BSN.head_sum_c_two qz149)

noncomputable abbrev qz579 := (Enclosure.sfrac Bool.false 90753 1000)

noncomputable abbrev qz563 := qz579

noncomputable abbrev qz433 := qz563

noncomputable abbrev qz151 := (@HMul.hMul Real Real Real qz267 qz433 (Real.log qz285))

noncomputable abbrev qz152 := qz433

noncomputable abbrev qz434 := (@Eq.refl Real qz563)

noncomputable abbrev qz153 := qz434

noncomputable def ep614 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz9 qz150) (Complex.mk (@HMul.hMul Real Real Real qz0 qz11 (Real.cos qz151)) (@HMul.hMul Real Real Real qz0 qz11 (@Neg.neg Real Real.instNeg (Real.sin qz151)))) Bool.false 24230921103 34359738368 2241688097267 2905665634828288 Bool.true 1776945645 34359738368 557861059285 726416408707072 (BSN.cpow_neg_s_mk qz152 90753 1000 2 qz153 rfl)

noncomputable def ep615 := BSN.cos_dyadic_bound_f 78601045 1073741824 1 0 524288 169298 0 1 1 0 1 1 522883 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 78601045) qz292 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 78601045) qz293 0 0 rfl) rfl rfl

noncomputable abbrev qz154 := (Enclosure.Real.IsNear.const Bool.false 90753 1000)

noncomputable abbrev qz435 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 16490183) qz16)

noncomputable abbrev qz436 := (@Nat.cast Real Real.instNatCast 2765528427569690443776)

noncomputable def ep616 := @Enclosure.Real.IsNear.cos_image qz151 qz435 Bool.false 16490183 262144 563 524288 Bool.false 522883 524288 1 84566 (@Enclosure.Real.IsNear.recentre' qz151 Bool.false 2061272889 32768000 90753 84566000 16490183 262144 563 524288 (@Enclosure.Real.IsNear.mulLit_ff qz152 qz17 90753 1000 0 1 181704 262144 1 84566 2061272889 32768000 90753 84566000 qz154 qz290 rfl) rfl) (Enclosure.sfrac_false_div 16490183 262144) (BSN.cos_reduce0 qz435 (@HDiv.hDiv Real Real Real qz1 qz436 qz19) 226375608064910080 72057594037927936 Bool.false 522883 524288 10 1000000000000000 169132 84566 (BSN.sin_reduce_arg_pos_rat_q0 16490183 262144 226375608064910080 72057594037927936 10 2765528427569690443776 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 522883 524288 2765528427569690443776 37778931862957161709568 78601045 1073741824 169298 169132 (ep615 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep617 := BSN.sin_dyadic_bound_f 78601045 1073741824 1 0 524288 169298 0 1 1 0 1 1 38345 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 78601045) qz287 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 78601045) qz288 0 0 rfl) rfl rfl

noncomputable def ep618 := @Enclosure.Real.IsNear.sin_image qz151 qz435 Bool.false 16490183 262144 563 524288 Bool.false 38345 524288 1 84566 (@Enclosure.Real.IsNear.recentre' qz151 Bool.false 2061272889 32768000 90753 84566000 16490183 262144 563 524288 (@Enclosure.Real.IsNear.mulLit_ff qz152 qz17 90753 1000 0 1 181704 262144 1 84566 2061272889 32768000 90753 84566000 qz154 qz290 rfl) rfl) (Enclosure.sfrac_false_div 16490183 262144) (BSN.sin_reduce0 qz435 (@HDiv.hDiv Real Real Real qz1 qz436 qz19) 226375608064910080 72057594037927936 Bool.false 38345 524288 10 1000000000000000 169132 84566 (BSN.sin_reduce_arg_pos_rat_q0 16490183 262144 226375608064910080 72057594037927936 10 2765528427569690443776 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 38345 524288 2765528427569690443776 37778931862957161709568 78601045 1073741824 169298 169132 (ep617 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep619 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz11 (Real.cos qz151)) (@HMul.hMul Real Real Real qz0 qz11 (@Neg.neg Real Real.instNeg (Real.sin qz151))) Bool.false 24230921103 34359738368 2241688097267 2905665634828288 Bool.true 1776945645 34359738368 557861059285 726416408707072 (@Enclosure.Real.IsNear.mulLit_ff qz11 (Real.cos qz151) 46341 65536 1 262144 522883 524288 24067473 22168469504 24230921103 34359738368 2241688097267 2905665634828288 qz294 (@Enclosure.Real.IsNear.recentre' (Real.cos qz151) Bool.false 522883 524288 48134946 44336939008 522883 524288 24067473 22168469504 (ep616 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz11 (@Neg.neg Real Real.instNeg (Real.sin qz151)) 46341 65536 1 262144 38345 524288 24067473 22168469504 1776945645 34359738368 557861059285 726416408707072 qz294 (@Enclosure.Real.IsNear.neg (Real.sin qz151) Bool.false 38345 524288 24067473 22168469504 (@Enclosure.Real.IsNear.recentre' (Real.sin qz151) Bool.false 38345 524288 48134946 44336939008 38345 524288 24067473 22168469504 (ep618 rfl rfl) rfl)) rfl)

noncomputable def ep620 := @ep612 24230921103 34359738368 2241688097267 2905665634828288 Bool.true 1776945645 34359738368 557861059285 726416408707072 Bool.false 58590659471 58590659471 34359738368 2241688097267 2905665634828288 Bool.true 1776945645 1776945645 34359738368 557861059285 726416408707072 (ep613 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 1) qz10 Bool.false 1 1 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 1) qz20)) (ep614 ep619) rfl rfl

noncomputable abbrev qz155 := (@HMul.hMul Real Real Real qz267 qz433 (Real.log (Enclosure.sfrac Bool.false 3 1)))

noncomputable def ep621 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz8 qz150) (Complex.mk (@HMul.hMul Real Real Real qz0 qz21 (Real.cos qz155)) (@HMul.hMul Real Real Real qz0 qz21 (@Neg.neg Real Real.instNeg (Real.sin qz155)))) Bool.false 53620680465 137438953472 3663991803255 5811331269656576 Bool.false 29245924015 68719476736 1832676340805 2905665634828288 (BSN.cpow_neg_s_mk qz152 90753 1000 3 qz153 rfl)

noncomputable def ep622 := nat_lit 402864491377854441139192920100000000

noncomputable def ep623 := BSN.sin_dyadic_bound_f 796690700 1073741824 2 1 524288 169298 ep622 ep103 ep622 ep622 ep104 ep622 354285 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 796690700) qz287 0 1 ep622 ep103 ep622 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 796690700) qz288 0 1 ep622 ep104 ep622 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz437 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 26136319) qz16)

noncomputable def ep624 := @Enclosure.Real.IsNear.cos_image qz155 qz437 Bool.false 26136319 262144 141 131072 Bool.false 354285 524288 1 84566 (@Enclosure.Real.IsNear.recentre' qz155 Bool.false 13068159741 131072000 90753 84566000 26136319 262144 141 131072 (@Enclosure.Real.IsNear.mulLit_ff qz152 qz24 90753 1000 0 1 287994 262144 1 84566 13068159741 131072000 90753 84566000 qz154 qz298 rfl) rfl) (Enclosure.sfrac_false_div 26136319 262144) (BSN.cos_reduce3 qz437 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 28031062059794623889408) qz19) 226375608064910080 72057594037927936 Bool.false 354285 524288 15 1000000000000000 169132 84566 (BSN.sin_reduce_arg_pos_rat_q3 26136319 262144 226375608064910080 72057594037927936 15 28031062059794623889408 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 354285 524288 28031062059794623889408 37778931862957161709568 796690700 1073741824 169298 169132 (ep623 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep625 := nat_lit 899800217349532703938620246886056147101759012498396200625639114368000000000

noncomputable def ep626 := nat_lit 162299798413137355346034810502392145250460997205964984010000000000000000

noncomputable def ep627 := nat_lit 2699076052451771837105168671037163657014776115500776671908897343104000000000

noncomputable def ep628 := BSN.cos_dyadic_bound_f 796690700 1073741824 3 2 524288 169298 ep625 ep73 ep626 ep627 ep75 ep626 386470 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 796690700) qz292 0 2 ep625 ep73 ep626 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 796690700) qz293 0 2 ep627 ep75 ep626 rfl rfl rfl rfl) rfl rfl

noncomputable def ep629 := @Enclosure.Real.IsNear.sin_image qz155 qz437 Bool.false 26136319 262144 141 131072 Bool.true 386470 524288 1 84566 (@Enclosure.Real.IsNear.recentre' qz155 Bool.false 13068159741 131072000 90753 84566000 26136319 262144 141 131072 (@Enclosure.Real.IsNear.mulLit_ff qz152 qz24 90753 1000 0 1 287994 262144 1 84566 13068159741 131072000 90753 84566000 qz154 qz298 rfl) rfl) (Enclosure.sfrac_false_div 26136319 262144) (BSN.sin_reduce3 qz437 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 28031062059794623889408) qz19) 226375608064910080 72057594037927936 Bool.false 386470 524288 15 1000000000000000 169132 84566 (BSN.sin_reduce_arg_pos_rat_q3 26136319 262144 226375608064910080 72057594037927936 15 28031062059794623889408 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 386470 524288 28031062059794623889408 37778931862957161709568 796690700 1073741824 169298 169132 (ep628 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep630 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz21 (Real.cos qz155)) (@HMul.hMul Real Real Real qz0 qz21 (@Neg.neg Real Real.instNeg (Real.sin qz155))) Bool.false 53620680465 137438953472 3663991803255 5811331269656576 Bool.false 29245924015 68719476736 1832676340805 2905665634828288 (@Enclosure.Real.IsNear.mulLit_ff qz21 (Real.cos qz155) 151349 262144 1 262144 354285 524288 6027439 5542117376 53620680465 137438953472 3663991803255 5811331269656576 qz299 (@Enclosure.Real.IsNear.recentre' (Real.cos qz155) Bool.false 354285 524288 12054878 11084234752 354285 524288 6027439 5542117376 (ep624 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz21 (@Neg.neg Real Real.instNeg (Real.sin qz155)) 151349 262144 1 262144 193235 262144 6027439 5542117376 29245924015 68719476736 1832676340805 2905665634828288 qz299 (@Enclosure.Real.IsNear.neg (Real.sin qz155) Bool.true 193235 262144 6027439 5542117376 (@Enclosure.Real.IsNear.recentre' (Real.sin qz155) Bool.true 386470 524288 12054878 11084234752 193235 262144 6027439 5542117376 (ep629 rfl rfl) rfl)) rfl)

noncomputable def ep631 := @ep610 53620680465 137438953472 3663991803255 5811331269656576 Bool.false 29245924015 68719476736 1832676340805 2905665634828288 Bool.false 9895031472820093714432 287983318349 137438953472 8147367997789 5811331269656576 Bool.false 882771522573094092800 25692032725 68719476736 4064120577945 2905665634828288 (ep611 (BSN.head_sum_c_succ qz149 2 3 rfl rfl) (ep620 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep621 ep630) rfl rfl

noncomputable abbrev qz156 := (@HMul.hMul Real Real Real qz267 qz433 (Real.log (Enclosure.sfrac Bool.false 4 1)))

noncomputable def ep632 := @Enclosure.Complex.IsNear.of_eq qz432 (Complex.mk (@HMul.hMul Real Real Real qz0 qz26 (Real.cos qz156)) (@HMul.hMul Real Real Real qz0 qz26 (@Neg.neg Real Real.instNeg (Real.sin qz156)))) Bool.false 135968069097 274877906944 6342159181021 11622662539313152 Bool.true 5012436303 68719476736 1580865462459 2905665634828288 (BSN.cpow_neg_s_mk qz152 90753 1000 4 qz153 rfl)

noncomputable def ep633 := nat_lit 610707512935701750365155497610000

noncomputable def ep634 := BSN.cos_dyadic_bound_f 157202090 1073741824 2 1 524288 169298 ep633 ep228 ep633 ep633 ep229 ep633 518679 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 157202090) qz292 0 1 ep633 ep228 ep633 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 157202090) qz293 0 1 ep633 ep229 ep633 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz438 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 16490183) (@Nat.cast Real Real.instNatCast 131072))

noncomputable def ep635 := @Enclosure.Real.IsNear.cos_image qz156 qz438 Bool.false 16490183 131072 141 131072 Bool.false 518679 524288 1 84566 (@Enclosure.Real.IsNear.recentre' qz156 Bool.false 2061272889 16384000 90753 84566000 16490183 131072 141 131072 (@Enclosure.Real.IsNear.mulLit_ff qz152 qz28 90753 1000 0 1 363408 262144 1 84566 2061272889 16384000 90753 84566000 qz154 qz301 rfl) rfl) (Enclosure.sfrac_false_div 16490183 131072) (BSN.cos_reduce0 qz438 (@HDiv.hDiv Real Real Real qz1 qz436 qz302) 226375608064910080 72057594037927936 Bool.false 518679 524288 20 1000000000000000 169132 84566 (BSN.sin_reduce_arg_pos_rat_q0 16490183 131072 226375608064910080 72057594037927936 20 2765528427569690443776 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 518679 524288 2765528427569690443776 18889465931478580854784 157202090 1073741824 169298 169132 (ep634 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep636 := BSN.sin_dyadic_bound_f 157202090 1073741824 1 0 524288 169298 0 1 1 0 1 1 76484 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 157202090) qz287 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 157202090) qz288 0 0 rfl) rfl rfl

noncomputable def ep637 := @Enclosure.Real.IsNear.sin_image qz156 qz438 Bool.false 16490183 131072 141 131072 Bool.false 76484 524288 1 84566 (@Enclosure.Real.IsNear.recentre' qz156 Bool.false 2061272889 16384000 90753 84566000 16490183 131072 141 131072 (@Enclosure.Real.IsNear.mulLit_ff qz152 qz28 90753 1000 0 1 363408 262144 1 84566 2061272889 16384000 90753 84566000 qz154 qz301 rfl) rfl) (Enclosure.sfrac_false_div 16490183 131072) (BSN.sin_reduce0 qz438 (@HDiv.hDiv Real Real Real qz1 qz436 qz302) 226375608064910080 72057594037927936 Bool.false 76484 524288 20 1000000000000000 169132 84566 (BSN.sin_reduce_arg_pos_rat_q0 16490183 131072 226375608064910080 72057594037927936 20 2765528427569690443776 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 76484 524288 2765528427569690443776 18889465931478580854784 157202090 1073741824 169298 169132 (ep636 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep638 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz26 (Real.cos qz156)) (@HMul.hMul Real Real Real qz0 qz26 (@Neg.neg Real Real.instNeg (Real.sin qz156))) Bool.false 135968069097 274877906944 6342159181021 11622662539313152 Bool.true 5012436303 68719476736 1580865462459 2905665634828288 (@Enclosure.Real.IsNear.mulLit_ff qz26 (Real.cos qz156) 262143 524288 1 524288 518679 524288 6027439 5542117376 135968069097 274877906944 6342159181021 11622662539313152 qz303 (@Enclosure.Real.IsNear.recentre' (Real.cos qz156) Bool.false 518679 524288 12054878 11084234752 518679 524288 6027439 5542117376 (ep635 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz26 (@Neg.neg Real Real.instNeg (Real.sin qz156)) 262143 524288 1 524288 19121 131072 6027439 5542117376 5012436303 68719476736 1580865462459 2905665634828288 qz303 (@Enclosure.Real.IsNear.neg (Real.sin qz156) Bool.false 19121 131072 6027439 5542117376 (@Enclosure.Real.IsNear.recentre' (Real.sin qz156) Bool.false 76484 524288 12054878 11084234752 19121 131072 6027439 5542117376 (ep637 rfl rfl) rfl)) rfl)

noncomputable def ep639 := @ep608 135968069097 274877906944 6342159181021 11622662539313152 Bool.true 5012436303 68719476736 1580865462459 2905665634828288 Bool.false 97847560904861013770240 711934705795 274877906944 22636895176599 11622662539313152 Bool.false 1421091045231497838592 10339798211 34359738368 1411246510101 726416408707072 (ep609 (BSN.head_sum_c_succ qz149 3 4 rfl rfl) (ep631 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep632 ep638) rfl rfl

noncomputable abbrev qz157 := (@HMul.hMul Real Real Real qz267 qz433 (Real.log (Enclosure.sfrac Bool.false 5 1)))

noncomputable def ep640 := @Enclosure.Complex.IsNear.of_eq qz431 (Complex.mk (@HMul.hMul Real Real Real qz0 qz29 (Real.cos qz157)) (@HMul.hMul Real Real Real qz0 qz29 (@Neg.neg Real Real.instNeg (Real.sin qz157)))) Bool.false 1407986345 137438953472 2826761154075 5811331269656576 Bool.true 61448463175 137438953472 2837588561885 5811331269656576 (BSN.cpow_neg_s_mk qz152 90753 1000 5 qz153 rfl)

noncomputable def ep641 := nat_lit 17097994243407839456135547488003606775124251122594040885994261988400209423521

noncomputable def ep642 := nat_lit 58225053035468334353592355190318974722378021184944023586694491841766190241

noncomputable def ep643 := nat_lit 51177532624152581699699457753630182375927997325412234610809396981517095890081

noncomputable def ep644 := BSN.cos_dyadic_bound_f 1662029533 1073741824 3 2 524288 169298 ep641 ep73 ep642 ep643 ep75 ep642 12010 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1662029533) qz292 0 2 ep641 ep73 ep642 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1662029533) qz293 0 2 ep643 ep75 ep642 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz439 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 76578107) qz23)

noncomputable def ep645 := @Enclosure.Real.IsNear.cos_image qz157 qz439 Bool.false 76578107 524288 141 131072 Bool.false 12010 524288 1 84566 (@Enclosure.Real.IsNear.recentre' qz157 Bool.false 2393065857 16384000 90753 84566000 76578107 524288 141 131072 (@Enclosure.Real.IsNear.mulLit_ff qz152 qz31 90753 1000 0 1 421904 262144 1 84566 2393065857 16384000 90753 84566000 qz154 qz305 rfl) rfl) (Enclosure.sfrac_false_div 76578107 524288) (BSN.cos_reduce0 qz439 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 116954931093542088474624) qz25) 226375608064910080 72057594037927936 Bool.false 12010 524288 23 1000000000000000 169132 84566 (BSN.sin_reduce_arg_pos_rat_q0 76578107 524288 226375608064910080 72057594037927936 23 116954931093542088474624 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 12010 524288 116954931093542088474624 75557863725914323419136 1662029533 1073741824 169298 169132 (ep644 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep646 := nat_lit 30729809595705736353561111594254237015445749603721318375920315985646964010145

noncomputable def ep647 := nat_lit 80388565521933789337039952267024390033759779784970686374936655547045855718561

noncomputable def ep648 := BSN.sin_dyadic_bound_f 1662029533 1073741824 3 2 524288 169298 ep646 ep66 ep642 ep647 ep69 ep642 524150 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1662029533) qz287 0 2 ep646 ep66 ep642 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1662029533) qz288 0 2 ep647 ep69 ep642 rfl rfl rfl rfl) rfl rfl

noncomputable def ep649 := @Enclosure.Real.IsNear.sin_image qz157 qz439 Bool.false 76578107 524288 141 131072 Bool.false 524150 524288 1 84566 (@Enclosure.Real.IsNear.recentre' qz157 Bool.false 2393065857 16384000 90753 84566000 76578107 524288 141 131072 (@Enclosure.Real.IsNear.mulLit_ff qz152 qz31 90753 1000 0 1 421904 262144 1 84566 2393065857 16384000 90753 84566000 qz154 qz305 rfl) rfl) (Enclosure.sfrac_false_div 76578107 524288) (BSN.sin_reduce0 qz439 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 116954931093542088474624) qz25) 226375608064910080 72057594037927936 Bool.false 524150 524288 23 1000000000000000 169132 84566 (BSN.sin_reduce_arg_pos_rat_q0 76578107 524288 226375608064910080 72057594037927936 23 116954931093542088474624 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 524150 524288 116954931093542088474624 75557863725914323419136 1662029533 1073741824 169298 169132 (ep648 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep650 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz29 (Real.cos qz157)) (@HMul.hMul Real Real Real qz0 qz29 (@Neg.neg Real Real.instNeg (Real.sin qz157))) Bool.false 1407986345 137438953472 2826761154075 5811331269656576 Bool.true 61448463175 137438953472 2837588561885 5811331269656576 (@Enclosure.Real.IsNear.mulLit_ff qz29 (Real.cos qz157) 234469 524288 1 524288 6005 262144 6027439 5542117376 1407986345 137438953472 2826761154075 5811331269656576 qz306 (@Enclosure.Real.IsNear.recentre' (Real.cos qz157) Bool.false 12010 524288 12054878 11084234752 6005 262144 6027439 5542117376 (ep645 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz29 (@Neg.neg Real Real.instNeg (Real.sin qz157)) 234469 524288 1 524288 262075 262144 6027439 5542117376 61448463175 137438953472 2837588561885 5811331269656576 qz306 (@Enclosure.Real.IsNear.neg (Real.sin qz157) Bool.false 262075 262144 6027439 5542117376 (@Enclosure.Real.IsNear.recentre' (Real.sin qz157) Bool.false 524150 524288 12054878 11084234752 262075 262144 6027439 5542117376 (ep649 rfl rfl) rfl)) rfl)

noncomputable def ep651 := @ep606 1407986345 137438953472 2826761154075 5811331269656576 Bool.true 61448463175 137438953472 2837588561885 5811331269656576 Bool.false 98234585244380346449920 714750678485 274877906944 28290417484749 11622662539313152 Bool.true 690262072577184759808 20089270331 137438953472 14127560642693 5811331269656576 (ep607 (BSN.head_sum_c_succ qz149 4 5 rfl rfl) (ep639 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep640 ep650) rfl rfl

noncomputable abbrev qz158 := (@HMul.hMul Real Real Real qz267 qz433 qz534)

noncomputable def ep652 := @Enclosure.Complex.IsNear.of_eq qz430 (Complex.mk (@HMul.hMul Real Real Real qz0 qz32 (Real.cos qz158)) (@HMul.hMul Real Real Real qz0 qz32 (@Neg.neg Real Real.instNeg (Real.sin qz158)))) Bool.false 81697616105 274877906944 5167541130605 11622662539313152 Bool.false 75127689 268435456 645824930739 1452832817414144 (BSN.cpow_neg_s_mk qz152 90753 1000 6 qz153 rfl)

noncomputable def ep653 := @Enclosure.Real.IsNear.mulLit_ff qz152 qz534 90753 1000 0 1 4034681531866359 2251799813685248 250000000042283 21141500000000000000 366159453061467678327 2251799813685248000 22688250003837309099 21141500000000000000000 qz154 (BSN.isNear_log_sfrac 6 1 4034681531866359 2251799813685248 250000000042283 21141500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz308) Bool.false 16922680887833197019136 9444732965739290427392 1000000000169132 84566000000000000000 4034681531866359 2251799813685248 250000000042283 21141500000000000000 (BSN.log_rat_reduce_isNear 6 1 2 12 8 106290 262144 24973259072661432 36028797018963968 84566 1000000000000000 rfl rfl rfl rfl (ep111 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep654 := nat_lit 587716790084778288943662165621795856

noncomputable def ep655 := BSN.sin_dyadic_bound_f 875572322 1073741824 2 1 524288 169298 ep654 ep103 ep654 ep654 ep104 ep654 381695 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 875572322) qz287 0 1 ep654 ep103 ep654 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 875572322) qz288 0 1 ep654 ep104 ep654 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz440 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 85253141) qz23)

noncomputable def ep656 := @Enclosure.Real.IsNear.cos_image qz158 qz440 Bool.false 85253141 524288 563 524288 Bool.false 381695 524288 1 84566 (@Enclosure.Real.IsNear.recentre' qz158 Bool.false 366159453061467678327 2251799813685248000 22688250003837309099 21141500000000000000000 85253141 524288 563 524288 (ep653 rfl) rfl) (Enclosure.sfrac_false_div 85253141 524288) (BSN.cos_reduce3 qz440 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 61612924755495020920832) qz25) 226375608064910080 72057594037927936 Bool.false 381695 524288 25 1000000000000000 169132 84566 (BSN.sin_reduce_arg_pos_rat_q3 85253141 524288 226375608064910080 72057594037927936 25 61612924755495020920832 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 381695 524288 61612924755495020920832 75557863725914323419136 875572322 1073741824 169298 169132 (ep655 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep657 := nat_lit 1312777557460884612081796299632411935624410068829559307451954799189452226816

noncomputable def ep658 := nat_lit 345411025347555347686510595923595499641319379140366728708606566538772736

noncomputable def ep659 := nat_lit 3937641850331958725550015877705388615873947567730397188898447184435279134976

noncomputable def ep660 := BSN.cos_dyadic_bound_f 875572322 1073741824 3 2 524288 169298 ep657 ep73 ep658 ep659 ep75 ep658 359424 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 875572322) qz292 0 2 ep657 ep73 ep658 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 875572322) qz293 0 2 ep659 ep75 ep658 rfl rfl rfl rfl) rfl rfl

noncomputable def ep661 := @Enclosure.Real.IsNear.sin_image qz158 qz440 Bool.false 85253141 524288 563 524288 Bool.true 359424 524288 1 84566 (@Enclosure.Real.IsNear.recentre' qz158 Bool.false 366159453061467678327 2251799813685248000 22688250003837309099 21141500000000000000000 85253141 524288 563 524288 (ep653 rfl) rfl) (Enclosure.sfrac_false_div 85253141 524288) (BSN.sin_reduce3 qz440 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 61612924755495020920832) qz25) 226375608064910080 72057594037927936 Bool.false 359424 524288 25 1000000000000000 169132 84566 (BSN.sin_reduce_arg_pos_rat_q3 85253141 524288 226375608064910080 72057594037927936 25 61612924755495020920832 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 359424 524288 61612924755495020920832 75557863725914323419136 875572322 1073741824 169298 169132 (ep660 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep662 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz32 (Real.cos qz158)) (@HMul.hMul Real Real Real qz0 qz32 (@Neg.neg Real Real.instNeg (Real.sin qz158))) Bool.false 81697616105 274877906944 5167541130605 11622662539313152 Bool.false 75127689 268435456 645824930739 1452832817414144 (@Enclosure.Real.IsNear.mulLit_ff qz32 (Real.cos qz158) 214039 524288 1 524288 381695 524288 24067473 22168469504 81697616105 274877906944 5167541130605 11622662539313152 qz310 (@Enclosure.Real.IsNear.recentre' (Real.cos qz158) Bool.false 381695 524288 48134946 44336939008 381695 524288 24067473 22168469504 (ep656 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz32 (@Neg.neg Real Real.instNeg (Real.sin qz158)) 214039 524288 1 524288 351 512 24067473 22168469504 75127689 268435456 645824930739 1452832817414144 qz310 (@Enclosure.Real.IsNear.neg (Real.sin qz158) Bool.true 351 512 24067473 22168469504 (@Enclosure.Real.IsNear.recentre' (Real.sin qz158) Bool.true 359424 524288 48134946 44336939008 351 512 24067473 22168469504 (ep661 rfl rfl) rfl)) rfl)

noncomputable def ep663 := @ep604 81697616105 274877906944 5167541130605 11622662539313152 Bool.false 75127689 268435456 645824930739 1452832817414144 Bool.false 218926040206017518632960 398224147295 137438953472 16728979307677 5811331269656576 Bool.false 4932798510920630272 18376106437 137438953472 16710860365649 5811331269656576 (ep605 (BSN.head_sum_c_succ qz149 5 6 rfl rfl) (ep651 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep652 ep662) rfl rfl

noncomputable abbrev qz159 := (@HMul.hMul Real Real Real qz267 qz433 qz535)

noncomputable def ep664 := @Enclosure.Complex.IsNear.of_eq qz429 (Complex.mk (@HMul.hMul Real Real Real qz0 qz34 (Real.cos qz159)) (@HMul.hMul Real Real Real qz0 qz34 (@Neg.neg Real Real.instNeg (Real.sin qz159)))) Bool.false 81584301589 274877906944 4786714757521 11622662539313152 Bool.true 64327474897 274877906944 4783032584749 11622662539313152 (BSN.cpow_neg_s_mk qz152 90753 1000 7 qz153 rfl)

noncomputable def ep665 := @Enclosure.Real.IsNear.mulLit_ff qz152 qz535 90753 1000 0 1 4381792198794487 2251799813685248 250000000042283 21141500000000000000 397660787417196078711 2251799813685248000 22688250003837309099 21141500000000000000000 qz154 (BSN.isNear_log_sfrac 7 1 4381792198794487 2251799813685248 250000000042283 21141500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz312) Bool.false 18378568546572512002048 9444732965739290427392 1000000000169132 84566000000000000000 4381792198794487 2251799813685248 250000000042283 21141500000000000000 (BSN.log_rat_reduce_isNear 7 1 2 14 8 146699 262144 24973259072661432 36028797018963968 84566 1000000000000000 rfl rfl rfl rfl (ep126 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep666 := nat_lit 264157410449309279466685129635926016

noncomputable def ep667 := BSN.cos_dyadic_bound_f 716911752 1073741824 2 1 524288 169298 ep666 ep228 ep666 ep666 ep229 ep666 411703 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 716911752) qz292 0 1 ep666 ep228 ep666 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 716911752) qz293 0 1 ep666 ep229 ep666 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz441 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 92587617) qz23)

noncomputable def ep668 := @Enclosure.Real.IsNear.cos_image qz159 qz441 Bool.false 92587617 524288 563 524288 Bool.false 411703 524288 1 84566 (@Enclosure.Real.IsNear.recentre' qz159 Bool.false 397660787417196078711 2251799813685248000 22688250003837309099 21141500000000000000000 92587617 524288 563 524288 (ep665 rfl) rfl) (Enclosure.sfrac_false_div 92587617 524288) (BSN.cos_reduce0 qz441 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 50448179723125909356544) qz25) 226375608064910080 72057594037927936 Bool.false 411703 524288 28 1000000000000000 169132 84566 (BSN.sin_reduce_arg_pos_rat_q0 92587617 524288 226375608064910080 72057594037927936 28 50448179723125909356544 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 411703 524288 50448179723125909356544 75557863725914323419136 716911752 1073741824 169298 169132 (ep667 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep669 := BSN.sin_dyadic_bound_f 716911752 1073741824 2 1 524288 169298 ep666 ep103 ep666 ep666 ep104 ep666 324619 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 716911752) qz287 0 1 ep666 ep103 ep666 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 716911752) qz288 0 1 ep666 ep104 ep666 rfl rfl rfl rfl) rfl rfl

noncomputable def ep670 := @Enclosure.Real.IsNear.sin_image qz159 qz441 Bool.false 92587617 524288 563 524288 Bool.false 324619 524288 1 84566 (@Enclosure.Real.IsNear.recentre' qz159 Bool.false 397660787417196078711 2251799813685248000 22688250003837309099 21141500000000000000000 92587617 524288 563 524288 (ep665 rfl) rfl) (Enclosure.sfrac_false_div 92587617 524288) (BSN.sin_reduce0 qz441 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 50448179723125909356544) qz25) 226375608064910080 72057594037927936 Bool.false 324619 524288 28 1000000000000000 169132 84566 (BSN.sin_reduce_arg_pos_rat_q0 92587617 524288 226375608064910080 72057594037927936 28 50448179723125909356544 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 324619 524288 50448179723125909356544 75557863725914323419136 716911752 1073741824 169298 169132 (ep669 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep671 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz34 (Real.cos qz159)) (@HMul.hMul Real Real Real qz0 qz34 (@Neg.neg Real Real.instNeg (Real.sin qz159))) Bool.false 81584301589 274877906944 4786714757521 11622662539313152 Bool.true 64327474897 274877906944 4783032584749 11622662539313152 (@Enclosure.Real.IsNear.mulLit_ff qz34 (Real.cos qz159) 198163 524288 1 524288 411703 524288 24067473 22168469504 81584301589 274877906944 4786714757521 11622662539313152 qz314 (@Enclosure.Real.IsNear.recentre' (Real.cos qz159) Bool.false 411703 524288 48134946 44336939008 411703 524288 24067473 22168469504 (ep668 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz34 (@Neg.neg Real Real.instNeg (Real.sin qz159)) 198163 524288 1 524288 324619 524288 24067473 22168469504 64327474897 274877906944 4783032584749 11622662539313152 qz314 (@Enclosure.Real.IsNear.neg (Real.sin qz159) Bool.false 324619 524288 24067473 22168469504 (@Enclosure.Real.IsNear.recentre' (Real.sin qz159) Bool.false 324619 524288 48134946 44336939008 324619 524288 24067473 22168469504 (ep670 rfl rfl) rfl)) rfl)

noncomputable def ep672 := @ep602 81584301589 274877906944 4786714757521 11622662539313152 Bool.true 64327474897 274877906944 4783032584749 11622662539313152 Bool.false 120675881133144945983488 878032596179 274877906944 38244673372875 11622662539313152 Bool.true 3789915154157305593856 27575262023 274877906944 38204753316047 11622662539313152 (ep603 (BSN.head_sum_c_succ qz149 6 7 rfl rfl) (ep663 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep664 ep671) rfl rfl

noncomputable abbrev qz160 := (@HMul.hMul Real Real Real qz267 qz433 qz536)

noncomputable def ep673 := @Enclosure.Complex.IsNear.of_eq qz428 (Complex.mk (@HMul.hMul Real Real Real qz0 qz36 (Real.cos qz160)) (@HMul.hMul Real Real Real qz0 qz36 (@Neg.neg Real Real.instNeg (Real.sin qz160)))) Bool.false 94841164313 274877906944 4490714950417 11622662539313152 Bool.true 10604061141 137438953472 2236959289173 5811331269656576 (BSN.cpow_neg_s_mk qz152 90753 1000 8 qz153 rfl)

noncomputable def ep674 := @Enclosure.Real.IsNear.mulLit_ff qz152 qz536 90753 1000 0 1 9364972152248037 4503599627370496 500000000126849 42283000000000000000 849899317732966101861 4503599627370496000 45376500011511927297 42283000000000000000000 qz154 (BSN.isNear_log_sfrac 8 1 9364972152248037 4503599627370496 500000000126849 42283000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz316) Bool.false 19639770079031275290624 9444732965739290427392 1000000000253698 84566000000000000000 9364972152248037 4503599627370496 500000000126849 42283000000000000000 (BSN.log_rat_reduce_isNear 8 1 3 16 16 0 262144 24973259072661432 36028797018963968 84566 1000000000000000 rfl rfl rfl rfl (ep140 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep675 := nat_lit 3113676473797034833455954427641856

noncomputable def ep676 := BSN.cos_dyadic_bound_f 236220928 1073741824 2 1 524288 169298 ep675 ep228 ep675 ep675 ep229 ep675 511651 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 236220928) qz292 0 1 ep675 ep228 ep675 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 236220928) qz293 0 1 ep675 ep229 ep675 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz442 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 49470651) qz16)

noncomputable def ep677 := @Enclosure.Real.IsNear.cos_image qz160 qz442 Bool.false 49470651 262144 141 131072 Bool.false 511651 524288 1 84566 (@Enclosure.Real.IsNear.recentre' qz160 Bool.false 849899317732966101861 4503599627370496000 45376500011511927297 42283000000000000000000 49470651 262144 141 131072 (ep674 rfl) rfl) (Enclosure.sfrac_false_div 49470651 262144) (BSN.cos_reduce0 qz442 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 8311285031892808630272) qz19) 226375608064910080 72057594037927936 Bool.false 511651 524288 30 1000000000000000 169132 84566 (BSN.sin_reduce_arg_pos_rat_q0 49470651 262144 226375608064910080 72057594037927936 30 8311285031892808630272 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 511651 524288 8311285031892808630272 37778931862957161709568 236220928 1073741824 169298 169132 (ep676 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep678 := BSN.sin_dyadic_bound_f 236220928 1073741824 2 1 524288 169298 ep675 ep103 ep675 ep675 ep104 ep675 114414 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 236220928) qz287 0 1 ep675 ep103 ep675 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 236220928) qz288 0 1 ep675 ep104 ep675 rfl rfl rfl rfl) rfl rfl

noncomputable def ep679 := @Enclosure.Real.IsNear.sin_image qz160 qz442 Bool.false 49470651 262144 141 131072 Bool.false 114414 524288 1 84566 (@Enclosure.Real.IsNear.recentre' qz160 Bool.false 849899317732966101861 4503599627370496000 45376500011511927297 42283000000000000000000 49470651 262144 141 131072 (ep674 rfl) rfl) (Enclosure.sfrac_false_div 49470651 262144) (BSN.sin_reduce0 qz442 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 8311285031892808630272) qz19) 226375608064910080 72057594037927936 Bool.false 114414 524288 30 1000000000000000 169132 84566 (BSN.sin_reduce_arg_pos_rat_q0 49470651 262144 226375608064910080 72057594037927936 30 8311285031892808630272 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 114414 524288 8311285031892808630272 37778931862957161709568 236220928 1073741824 169298 169132 (ep678 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep680 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz36 (Real.cos qz160)) (@HMul.hMul Real Real Real qz0 qz36 (@Neg.neg Real Real.instNeg (Real.sin qz160))) Bool.false 94841164313 274877906944 4490714950417 11622662539313152 Bool.true 10604061141 137438953472 2236959289173 5811331269656576 (@Enclosure.Real.IsNear.mulLit_ff qz36 (Real.cos qz160) 185363 524288 1 524288 511651 524288 6027439 5542117376 94841164313 274877906944 4490714950417 11622662539313152 qz318 (@Enclosure.Real.IsNear.recentre' (Real.cos qz160) Bool.false 511651 524288 12054878 11084234752 511651 524288 6027439 5542117376 (ep677 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz36 (@Neg.neg Real Real.instNeg (Real.sin qz160)) 185363 524288 1 524288 57207 262144 6027439 5542117376 10604061141 137438953472 2236959289173 5811331269656576 qz318 (@Enclosure.Real.IsNear.neg (Real.sin qz160) Bool.false 57207 262144 6027439 5542117376 (@Enclosure.Real.IsNear.recentre' (Real.sin qz160) Bool.false 114414 524288 12054878 11084234752 57207 262144 6027439 5542117376 (ep679 rfl rfl) rfl)) rfl)

noncomputable def ep681 := @ep600 94841164313 274877906944 4490714950417 11622662539313152 Bool.true 10604061141 137438953472 2236959289173 5811331269656576 Bool.false 267421503004779319656448 243218440123 68719476736 10683847080823 2905665634828288 Bool.true 6704737285701590056960 48783384305 274877906944 42678671894393 11622662539313152 (ep601 (BSN.head_sum_c_succ qz149 7 8 rfl rfl) (ep672 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep673 ep680) rfl rfl

theorem EMRow25.d11 : Enclosure.Complex.IsNear qz148 Bool.false 243218440123 68719476736 10683847080823 2905665634828288 Bool.true 48783384305 274877906944 42678671894393 11622662539313152 := ep599 (BSN.head_sum_c_succ qz149 8 9 rfl rfl) (ep681 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable abbrev qz161 := (BSN.headSumC qz426 17)

noncomputable abbrev qz162 := (@HPow.hPow Complex Complex Complex qz274 (@Nat.cast Complex Complex.instNatCast 16) qz427)

noncomputable def ep682 := @Enclosure.Complex.IsNear.of_eq qz161 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz149 16) qz162) Bool.false 151686259201 34359738368 35899719707533 5811331269656576 Bool.true 70888791985 274877906944 71749640569533 11622662539313152

noncomputable def ep683 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz149 16) qz162 Bool.false 1147706456205 274877906944 68618103934915 11622662539313152 Bool.true 25509672941 137438953472 34291558412141 5811331269656576 Bool.false

noncomputable abbrev qz163 := (@HPow.hPow Complex Complex Complex qz274 (@Nat.cast Complex Complex.instNatCast 15) qz427)

noncomputable def ep684 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz149 16) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz149 15) qz163) Bool.false 1147706456205 274877906944 68618103934915 11622662539313152 Bool.true 25509672941 137438953472 34291558412141 5811331269656576

noncomputable def ep685 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz149 15) qz163 Bool.false 1094306657835 274877906944 65337638670673 11622662539313152 Bool.true 2134079403 137438953472 32652364123651 5811331269656576 Bool.false

noncomputable abbrev qz164 := (@HPow.hPow Complex Complex Complex qz274 (@Nat.cast Complex Complex.instNatCast 14) qz427)

noncomputable def ep686 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz149 15) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz149 14) qz164) Bool.false 1094306657835 274877906944 65337638670673 11622662539313152 Bool.true 2134079403 137438953472 32652364123651 5811331269656576

noncomputable def ep687 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz149 14) qz164 Bool.false 520053016731 137438953472 7743612575611 1452832817414144 Bool.false 45322204425 274877906944 61917381376783 11622662539313152 Bool.false

noncomputable abbrev qz165 := (@HPow.hPow Complex Complex Complex qz274 (@Nat.cast Complex Complex.instNatCast 13) qz427)

noncomputable def ep688 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz149 14) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz149 13) qz165) Bool.false 520053016731 137438953472 7743612575611 1452832817414144 Bool.false 45322204425 274877906944 61917381376783 11622662539313152

noncomputable def ep689 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz149 13) qz165 Bool.false 241810945101 68719476736 29214007069969 5811331269656576 Bool.false 67754177751 274877906944 58411159163629 11622662539313152 Bool.false

noncomputable abbrev qz166 := (@HPow.hPow Complex Complex Complex qz274 (@Nat.cast Complex Complex.instNatCast 12) qz427)

noncomputable def ep690 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz149 13) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz149 12) qz166) Bool.false 241810945101 68719476736 29214007069969 5811331269656576 Bool.false 67754177751 274877906944 58411159163629 11622662539313152

noncomputable def ep691 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz149 12) qz166 Bool.false 905644283357 274877906944 54768192793539 11622662539313152 Bool.false 17734544043 274877906944 54754572931843 11622662539313152 Bool.false

noncomputable abbrev qz167 := (@HPow.hPow Complex Complex Complex qz274 (@Nat.cast Complex Complex.instNatCast 11) qz427)

noncomputable def ep692 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz149 12) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz149 11) qz167) Bool.false 905644283357 274877906944 54768192793539 11622662539313152 Bool.false 17734544043 274877906944 54754572931843 11622662539313152

noncomputable def ep693 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz149 11) qz167 Bool.false 240147226985 68719476736 3183889122923 726416408707072 Bool.true 44313676563 274877906944 50926706033901 11622662539313152 Bool.true

noncomputable abbrev qz443 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 10) qz150)

noncomputable def ep694 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz149 11) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz149 10) qz443) Bool.false 240147226985 68719476736 3183889122923 726416408707072 Bool.true 44313676563 274877906944 50926706033901 11622662539313152

noncomputable def ep695 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz149 10) qz443 Bool.false 964962414245 274877906944 46950819830003 11622662539313152 Bool.false 21250199361 137438953472 11728568732271 2905665634828288 Bool.true

noncomputable abbrev qz444 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 9) qz150)

noncomputable def ep696 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz149 10) (@HAdd.hAdd Complex Complex Complex qz4 qz148 qz444) Bool.false 964962414245 274877906944 46950819830003 11622662539313152 Bool.false 21250199361 137438953472 11728568732271 2905665634828288

noncomputable def ep697 := @Enclosure.Complex.IsNear.addLitP qz148 qz444 Bool.false 243218440123 68719476736 10683847080823 2905665634828288 Bool.true 48783384305 274877906944 42678671894393 11622662539313152 Bool.true

noncomputable abbrev qz168 := (@HMul.hMul Real Real Real qz267 qz433 qz537)

noncomputable def ep698 := @Enclosure.Complex.IsNear.of_eq qz444 (Complex.mk (@HMul.hMul Real Real Real qz0 qz46 (Real.cos qz168)) (@HMul.hMul Real Real Real qz0 qz46 (@Neg.neg Real Real.instNeg (Real.sin qz168)))) Bool.true 7911346247 274877906944 4215431506711 11622662539313152 Bool.false 91283783027 274877906944 4235603034691 11622662539313152 (BSN.cpow_neg_s_mk qz152 90753 1000 9 qz153 rfl)

noncomputable def ep699 := @Enclosure.Real.IsNear.mulLit_ff qz152 qz537 90753 1000 0 1 9895417793173221 4503599627370496 500000000126849 42283000000000000000 898038850983849325413 4503599627370496000 45376500011511927297 42283000000000000000000 qz154 (BSN.isNear_log_sfrac 9 1 9895417793173221 4503599627370496 500000000126849 42283000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz321) Bool.false 20752195215788806766592 9444732965739290427392 1000000000253698 84566000000000000000 9895417793173221 4503599627370496 500000000126849 42283000000000000000 (BSN.log_rat_reduce_isNear 9 1 3 18 16 30876 262144 24973259072661432 36028797018963968 84566 1000000000000000 rfl rfl rfl rfl (ep166 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep700 := nat_lit 14451020040670555905798029387975205586048662664797559500830555228912526475201

noncomputable def ep701 := nat_lit 41636410838359849338411928890151365737616435151257715052327691137382006721

noncomputable def ep702 := nat_lit 43269787300334948018717264306145314026670755124090163072387010304462815412161

noncomputable def ep703 := BSN.cos_dyadic_bound_f 1593801241 1073741824 3 2 524288 169298 ep700 ep73 ep701 ep702 ep75 ep701 45269 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1593801241) qz292 0 2 ep700 ep73 ep701 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1593801241) qz293 0 2 ep702 ep75 ep701 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz445 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 104545481) qz23)

noncomputable def ep704 := @Enclosure.Real.IsNear.cos_image qz168 qz445 Bool.false 104545481 524288 141 131072 Bool.true 45269 524288 1 84566 (@Enclosure.Real.IsNear.recentre' qz168 Bool.false 898038850983849325413 4503599627370496000 45376500011511927297 42283000000000000000000 104545481 524288 141 131072 (ep699 rfl) rfl) (Enclosure.sfrac_false_div 104545481 524288) (BSN.cos_reduce2 qz445 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 112153791852734046011392) qz25) 226375608064910080 72057594037927936 Bool.false 45269 524288 31 1000000000000000 169132 84566 (BSN.sin_reduce_arg_pos_rat_q2 104545481 524288 226375608064910080 72057594037927936 31 112153791852734046011392 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 45269 524288 112153791852734046011392 75557863725914323419136 1593801241 1073741824 169298 169132 (ep703 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep705 := nat_lit 25978526944536312750965723355243248962297499648514600929453137259132642049985

noncomputable def ep706 := nat_lit 67971587808618712686933751378862549832918262946340966133721114654934491643841

noncomputable def ep707 := BSN.sin_dyadic_bound_f 1593801241 1073741824 3 2 524288 169298 ep705 ep66 ep701 ep706 ep69 ep701 522329 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1593801241) qz287 0 2 ep705 ep66 ep701 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1593801241) qz288 0 2 ep706 ep69 ep701 rfl rfl rfl rfl) rfl rfl

noncomputable def ep708 := @Enclosure.Real.IsNear.sin_image qz168 qz445 Bool.false 104545481 524288 141 131072 Bool.true 522329 524288 1 84566 (@Enclosure.Real.IsNear.recentre' qz168 Bool.false 898038850983849325413 4503599627370496000 45376500011511927297 42283000000000000000000 104545481 524288 141 131072 (ep699 rfl) rfl) (Enclosure.sfrac_false_div 104545481 524288) (BSN.sin_reduce2 qz445 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 112153791852734046011392) qz25) 226375608064910080 72057594037927936 Bool.false 522329 524288 31 1000000000000000 169132 84566 (BSN.sin_reduce_arg_pos_rat_q2 104545481 524288 226375608064910080 72057594037927936 31 112153791852734046011392 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 522329 524288 112153791852734046011392 75557863725914323419136 1593801241 1073741824 169298 169132 (ep707 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep709 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz46 (Real.cos qz168)) (@HMul.hMul Real Real Real qz0 qz46 (@Neg.neg Real Real.instNeg (Real.sin qz168))) Bool.true 7911346247 274877906944 4215431506711 11622662539313152 Bool.false 91283783027 274877906944 4235603034691 11622662539313152 (@Enclosure.Real.IsNear.mulLit_ft qz46 (Real.cos qz168) 174763 524288 1 524288 45269 524288 6027439 5542117376 7911346247 274877906944 4215431506711 11622662539313152 qz323 (@Enclosure.Real.IsNear.recentre' (Real.cos qz168) Bool.true 45269 524288 12054878 11084234752 45269 524288 6027439 5542117376 (ep704 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz46 (@Neg.neg Real Real.instNeg (Real.sin qz168)) 174763 524288 1 524288 522329 524288 6027439 5542117376 91283783027 274877906944 4235603034691 11622662539313152 qz323 (@Enclosure.Real.IsNear.neg (Real.sin qz168) Bool.true 522329 524288 6027439 5542117376 (@Enclosure.Real.IsNear.recentre' (Real.sin qz168) Bool.true 522329 524288 12054878 11084234752 522329 524288 6027439 5542117376 (ep708 rfl rfl) rfl)) rfl)

noncomputable def ep710 := @ep697 7911346247 274877906944 4215431506711 11622662539313152 Bool.false 91283783027 274877906944 4235603034691 11622662539313152 Bool.false 66311712176823672504320 964962414245 274877906944 46950819830003 11622662539313152 Bool.false 11682420644988812525568 21250199361 137438953472 11728568732271 2905665634828288 EMRow25.d11 (ep698 ep709) rfl rfl

noncomputable abbrev qz169 := (@HMul.hMul Real Real Real qz267 qz433 qz538)

noncomputable def ep711 := @Enclosure.Complex.IsNear.of_eq qz443 (Complex.mk (@HMul.hMul Real Real Real qz0 qz48 (Real.cos qz169)) (@HMul.hMul Real Real Real qz0 qz48 (@Neg.neg Real Real.instNeg (Real.sin qz169)))) Bool.true 4373506305 274877906944 3991406136765 11622662539313152 Bool.true 86814075285 274877906944 4012431104817 11622662539313152 (BSN.cpow_neg_s_mk qz152 90753 1000 10 qz153 rfl)

noncomputable def ep712 := @Enclosure.Real.IsNear.mulLit_ff qz152 qz538 90753 1000 0 1 10369908600166117 4503599627370496 500000000126849 42283000000000000000 941100315190875616101 4503599627370496000 45376500011511927297 42283000000000000000000 qz154 (BSN.isNear_log_sfrac 10 1 10369908600166117 4503599627370496 500000000126849 42283000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz325) Bool.false 21747274560655572598784 9444732965739290427392 1000000000253698 84566000000000000000 10369908600166117 4503599627370496 500000000126849 42283000000000000000 (BSN.log_rat_reduce_isNear 10 1 3 20 16 58495 262144 24973259072661432 36028797018963968 84566 1000000000000000 rfl rfl rfl rfl (ep181 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep713 := BSN.sin_dyadic_bound_f 54047970 1073741824 1 0 524288 169298 0 1 1 0 1 1 26379 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 54047970) qz287 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 54047970) qz288 0 0 rfl) rfl rfl

noncomputable abbrev qz446 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 3423703) (@Nat.cast Real Real.instNatCast 16384))

noncomputable abbrev qz447 := (@Nat.cast Real Real.instNatCast 2361183241434822606848)

noncomputable def ep714 := @Enclosure.Real.IsNear.cos_image qz169 qz446 Bool.false 3423703 16384 563 524288 Bool.true 26379 524288 1 84566 (@Enclosure.Real.IsNear.recentre' qz169 Bool.false 941100315190875616101 4503599627370496000 45376500011511927297 42283000000000000000000 3423703 16384 563 524288 (ep712 rfl) rfl) (Enclosure.sfrac_false_div 3423703 16384) (BSN.cos_reduce1 qz446 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 118852743652238688256) qz447) 226375608064910080 72057594037927936 Bool.false 26379 524288 33 1000000000000000 169132 84566 (BSN.sin_reduce_arg_pos_rat_q1 3423703 16384 226375608064910080 72057594037927936 33 118852743652238688256 2361183241434822606848 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 26379 524288 118852743652238688256 2361183241434822606848 54047970 1073741824 169298 169132 (ep713 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep715 := BSN.cos_dyadic_bound_f 54047970 1073741824 1 0 524288 169298 0 1 1 0 1 1 523623 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 54047970) qz292 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 54047970) qz293 0 0 rfl) rfl rfl

noncomputable def ep716 := @Enclosure.Real.IsNear.sin_image qz169 qz446 Bool.false 3423703 16384 563 524288 Bool.false 523623 524288 1 84566 (@Enclosure.Real.IsNear.recentre' qz169 Bool.false 941100315190875616101 4503599627370496000 45376500011511927297 42283000000000000000000 3423703 16384 563 524288 (ep712 rfl) rfl) (Enclosure.sfrac_false_div 3423703 16384) (BSN.sin_reduce1 qz446 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 118852743652238688256) qz447) 226375608064910080 72057594037927936 Bool.false 523623 524288 33 1000000000000000 169132 84566 (BSN.sin_reduce_arg_pos_rat_q1 3423703 16384 226375608064910080 72057594037927936 33 118852743652238688256 2361183241434822606848 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 523623 524288 118852743652238688256 2361183241434822606848 54047970 1073741824 169298 169132 (ep715 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep717 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz48 (Real.cos qz169)) (@HMul.hMul Real Real Real qz0 qz48 (@Neg.neg Real Real.instNeg (Real.sin qz169))) Bool.true 4373506305 274877906944 3991406136765 11622662539313152 Bool.true 86814075285 274877906944 4012431104817 11622662539313152 (@Enclosure.Real.IsNear.mulLit_ft qz48 (Real.cos qz169) 165795 524288 1 524288 26379 524288 24067473 22168469504 4373506305 274877906944 3991406136765 11622662539313152 qz327 (@Enclosure.Real.IsNear.recentre' (Real.cos qz169) Bool.true 26379 524288 48134946 44336939008 26379 524288 24067473 22168469504 (ep714 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz48 (@Neg.neg Real Real.instNeg (Real.sin qz169)) 165795 524288 1 524288 523623 524288 24067473 22168469504 86814075285 274877906944 4012431104817 11622662539313152 qz327 (@Enclosure.Real.IsNear.neg (Real.sin qz169) Bool.false 523623 524288 24067473 22168469504 (@Enclosure.Real.IsNear.recentre' (Real.sin qz169) Bool.false 523623 524288 48134946 44336939008 523623 524288 24067473 22168469504 (ep716 rfl rfl) rfl)) rfl)

noncomputable def ep718 := @ep695 4373506305 274877906944 3991406136765 11622662539313152 Bool.true 86814075285 274877906944 4012431104817 11622662539313152 Bool.false 264044668448169902735360 240147226985 68719476736 3183889122923 726416408707072 Bool.true 6090425331315413876736 44313676563 274877906944 50926706033901 11622662539313152 (ep696 (BSN.head_sum_c_succ qz149 9 10 rfl rfl) (ep710 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep711 ep717) rfl rfl

noncomputable abbrev qz170 := (@HMul.hMul Real Real Real qz267 qz433 qz539)

noncomputable def ep719 := @Enclosure.Complex.IsNear.of_eq qz167 (Complex.mk (@HMul.hMul Real Real Real qz0 qz50 (Real.cos qz170)) (@HMul.hMul Real Real Real qz0 qz50 (@Neg.neg Real Real.instNeg (Real.sin qz170)))) Bool.true 54944624583 274877906944 3825966826771 11622662539313152 Bool.false 31024110303 137438953472 1913933448971 5811331269656576 (BSN.cpow_neg_s_mk qz152 90753 1000 11 qz153 rfl)

noncomputable def ep720 := @Enclosure.Real.IsNear.mulLit_ff qz152 qz539 90753 1000 0 1 10799147631728357 4503599627370496 500000000126849 42283000000000000000 980055045022243582821 4503599627370496000 45376500011511927297 42283000000000000000000 qz154 (BSN.isNear_log_sfrac 11 1 10799147631728357 4503599627370496 500000000126849 42283000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz329) Bool.false 22647454054174387339264 9444732965739290427392 1000000000253698 84566000000000000000 10799147631728357 4503599627370496 500000000126849 42283000000000000000 (BSN.log_rat_reduce_isNear 11 1 3 22 16 83480 262144 24973259072661432 36028797018963968 84566 1000000000000000 rfl rfl rfl rfl (ep195 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep721 := nat_lit 1521271987942145618305668805844212827187514682374842321404089239168000000000

noncomputable def ep722 := nat_lit 463800658570788080222865640298580012718230018151170456010000000000000000

noncomputable def ep723 := nat_lit 4562888362509295278756560686252041321537107587088224623300247717504000000000

noncomputable def ep724 := BSN.cos_dyadic_bound_f 908429900 1073741824 3 2 524288 169298 ep721 ep73 ep722 ep723 ep75 ep722 347577 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 908429900) qz292 0 2 ep721 ep73 ep722 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 908429900) qz293 0 2 ep723 ep75 ep722 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz448 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 114093423) qz23)

noncomputable def ep725 := @Enclosure.Real.IsNear.cos_image qz170 qz448 Bool.false 114093423 524288 141 131072 Bool.true 347577 524288 1 84566 (@Enclosure.Real.IsNear.recentre' qz170 Bool.false 980055045022243582821 4503599627370496000 45376500011511927297 42283000000000000000000 114093423 524288 141 131072 (ep720 rfl) rfl) (Enclosure.sfrac_false_div 114093423 524288) (BSN.cos_reduce2 qz448 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 63925071306470599950336) qz25) 226375608064910080 72057594037927936 Bool.false 347577 524288 34 1000000000000000 169132 84566 (BSN.sin_reduce_arg_pos_rat_q2 114093423 524288 226375608064910080 72057594037927936 34 63925071306470599950336 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 347577 524288 63925071306470599950336 75557863725914323419136 908429900 1073741824 169298 169132 (ep724 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep726 := nat_lit 681029117270905003867460280100000000

noncomputable def ep727 := BSN.sin_dyadic_bound_f 908429900 1073741824 2 1 524288 169298 ep726 ep103 ep726 ep726 ep104 ep726 392514 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 908429900) qz287 0 1 ep726 ep103 ep726 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 908429900) qz288 0 1 ep726 ep104 ep726 rfl rfl rfl rfl) rfl rfl

noncomputable def ep728 := @Enclosure.Real.IsNear.sin_image qz170 qz448 Bool.false 114093423 524288 141 131072 Bool.true 392514 524288 1 84566 (@Enclosure.Real.IsNear.recentre' qz170 Bool.false 980055045022243582821 4503599627370496000 45376500011511927297 42283000000000000000000 114093423 524288 141 131072 (ep720 rfl) rfl) (Enclosure.sfrac_false_div 114093423 524288) (BSN.sin_reduce2 qz448 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 63925071306470599950336) qz25) 226375608064910080 72057594037927936 Bool.false 392514 524288 34 1000000000000000 169132 84566 (BSN.sin_reduce_arg_pos_rat_q2 114093423 524288 226375608064910080 72057594037927936 34 63925071306470599950336 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 392514 524288 63925071306470599950336 75557863725914323419136 908429900 1073741824 169298 169132 (ep727 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep729 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz50 (Real.cos qz170)) (@HMul.hMul Real Real Real qz0 qz50 (@Neg.neg Real Real.instNeg (Real.sin qz170))) Bool.true 54944624583 274877906944 3825966826771 11622662539313152 Bool.false 31024110303 137438953472 1913933448971 5811331269656576 (@Enclosure.Real.IsNear.mulLit_ft qz50 (Real.cos qz170) 158079 524288 1 524288 347577 524288 6027439 5542117376 54944624583 274877906944 3825966826771 11622662539313152 qz331 (@Enclosure.Real.IsNear.recentre' (Real.cos qz170) Bool.true 347577 524288 12054878 11084234752 347577 524288 6027439 5542117376 (ep725 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz50 (@Neg.neg Real Real.instNeg (Real.sin qz170)) 158079 524288 1 524288 196257 262144 6027439 5542117376 31024110303 137438953472 1913933448971 5811331269656576 qz331 (@Enclosure.Real.IsNear.neg (Real.sin qz170) Bool.true 196257 262144 6027439 5542117376 (@Enclosure.Real.IsNear.recentre' (Real.sin qz170) Bool.true 392514 524288 12054878 11084234752 196257 262144 6027439 5542117376 (ep728 rfl rfl) rfl)) rfl)

noncomputable def ep730 := @ep693 54944624583 274877906944 3825966826771 11622662539313152 Bool.false 31024110303 137438953472 1913933448971 5811331269656576 Bool.false 62235401261242753482752 905644283357 274877906944 54768192793539 11622662539313152 Bool.false 2437417173573011767296 17734544043 274877906944 54754572931843 11622662539313152 (ep694 (BSN.head_sum_c_succ qz149 10 11 rfl rfl) (ep718 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep719 ep729) rfl rfl

noncomputable abbrev qz171 := (@HMul.hMul Real Real Real qz267 qz433 qz540)

noncomputable def ep731 := @Enclosure.Complex.IsNear.of_eq qz166 (Complex.mk (@HMul.hMul Real Real Real qz0 qz52 (Real.cos qz171)) (@HMul.hMul Real Real Real qz0 qz52 (@Neg.neg Real Real.instNeg (Real.sin qz171)))) Bool.false 61599497047 274877906944 3659821346399 11622662539313152 Bool.false 12504908427 68719476736 1828293115893 5811331269656576 (BSN.cpow_neg_s_mk qz152 90753 1000 12 qz153 rfl)

noncomputable def ep732 := @Enclosure.Real.IsNear.mulLit_ff qz152 qz540 90753 1000 0 1 11191020447815397 4503599627370496 500000000126849 42283000000000000000 1015618678700590723941 4503599627370496000 45376500011511927297 42283000000000000000000 qz154 (BSN.isNear_log_sfrac 12 1 11191020447815397 4503599627370496 500000000126849 42283000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz333) Bool.false 23469270914176955449344 9444732965739290427392 1000000000253698 84566000000000000000 11191020447815397 4503599627370496 500000000126849 42283000000000000000 (BSN.log_rat_reduce_isNear 12 1 3 24 16 106290 262144 24973259072661432 36028797018963968 84566 1000000000000000 rfl rfl rfl rfl (ep210 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep733 := nat_lit 829397435584241028181795299101749921

noncomputable def ep734 := BSN.sin_dyadic_bound_f 954312631 1073741824 2 1 524288 169298 ep733 ep103 ep733 ep733 ep104 ep733 407003 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 954312631) qz287 0 1 ep733 ep103 ep733 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 954312631) qz288 0 1 ep733 ep104 ep733 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz449 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 118233575) qz23)

noncomputable def ep735 := @Enclosure.Real.IsNear.cos_image qz171 qz449 Bool.false 118233575 524288 563 524288 Bool.false 407003 524288 1 84566 (@Enclosure.Real.IsNear.recentre' qz171 Bool.false 1015618678700590723941 4503599627370496000 45376500011511927297 42283000000000000000000 118233575 524288 563 524288 (ep732 rfl) rfl) (Enclosure.sfrac_false_div 118233575 524288) (BSN.cos_reduce3 qz449 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 67153781443423560007680) qz25) 226375608064910080 72057594037927936 Bool.false 407003 524288 35 1000000000000000 169132 84566 (BSN.sin_reduce_arg_pos_rat_q3 118233575 524288 226375608064910080 72057594037927936 35 67153781443423560007680 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 407003 524288 67153781443423560007680 75557863725914323419136 954312631 1073741824 169298 169132 (ep734 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep736 := nat_lit 1852817829004280188851717448780236339002438666586385401331155273538531379521

noncomputable def ep737 := nat_lit 687900106153715245732825048551019705876302501663412291633195804423506241

noncomputable def ep738 := nat_lit 5557077686800533136063686696243606977595563394755829379410199429006747126081

noncomputable def ep739 := BSN.cos_dyadic_bound_f 954312631 1073741824 3 2 524288 169298 ep736 ep73 ep737 ep738 ep75 ep737 330492 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 954312631) qz292 0 2 ep736 ep73 ep737 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 954312631) qz293 0 2 ep738 ep75 ep737 rfl rfl rfl rfl) rfl rfl

noncomputable def ep740 := @Enclosure.Real.IsNear.sin_image qz171 qz449 Bool.false 118233575 524288 563 524288 Bool.true 330492 524288 1 84566 (@Enclosure.Real.IsNear.recentre' qz171 Bool.false 1015618678700590723941 4503599627370496000 45376500011511927297 42283000000000000000000 118233575 524288 563 524288 (ep732 rfl) rfl) (Enclosure.sfrac_false_div 118233575 524288) (BSN.sin_reduce3 qz449 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 67153781443423560007680) qz25) 226375608064910080 72057594037927936 Bool.false 330492 524288 35 1000000000000000 169132 84566 (BSN.sin_reduce_arg_pos_rat_q3 118233575 524288 226375608064910080 72057594037927936 35 67153781443423560007680 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 330492 524288 67153781443423560007680 75557863725914323419136 954312631 1073741824 169298 169132 (ep739 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep741 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz52 (Real.cos qz171)) (@HMul.hMul Real Real Real qz0 qz52 (@Neg.neg Real Real.instNeg (Real.sin qz171))) Bool.false 61599497047 274877906944 3659821346399 11622662539313152 Bool.false 12504908427 68719476736 1828293115893 5811331269656576 (@Enclosure.Real.IsNear.mulLit_ff qz52 (Real.cos qz171) 151349 524288 1 524288 407003 524288 24067473 22168469504 61599497047 274877906944 3659821346399 11622662539313152 qz335 (@Enclosure.Real.IsNear.recentre' (Real.cos qz171) Bool.false 407003 524288 48134946 44336939008 407003 524288 24067473 22168469504 (ep735 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz52 (@Neg.neg Real Real.instNeg (Real.sin qz171)) 151349 524288 1 524288 82623 131072 24067473 22168469504 12504908427 68719476736 1828293115893 5811331269656576 qz335 (@Enclosure.Real.IsNear.neg (Real.sin qz171) Bool.true 82623 131072 24067473 22168469504 (@Enclosure.Real.IsNear.recentre' (Real.sin qz171) Bool.true 330492 524288 48134946 44336939008 82623 131072 24067473 22168469504 (ep740 rfl rfl) rfl)) rfl)

noncomputable def ep742 := @ep691 61599497047 274877906944 3659821346399 11622662539313152 Bool.false 12504908427 68719476736 1828293115893 5811331269656576 Bool.false 265873945862053482725376 241810945101 68719476736 29214007069969 5811331269656576 Bool.false 4656031641726653300736 67754177751 274877906944 58411159163629 11622662539313152 (ep692 (BSN.head_sum_c_succ qz149 11 12 rfl rfl) (ep730 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep731 ep741) rfl rfl

noncomputable abbrev qz172 := (@HMul.hMul Real Real Real qz267 qz433 qz541)

noncomputable def ep743 := @Enclosure.Complex.IsNear.of_eq qz165 (Complex.mk (@HMul.hMul Real Real Real qz0 qz54 (Real.cos qz172)) (@HMul.hMul Real Real Real qz0 qz54 (@Neg.neg Real Real.instNeg (Real.sin qz172)))) Bool.false 36431126529 137438953472 1760443232475 5811331269656576 Bool.true 11215986663 137438953472 1753111106577 5811331269656576 (BSN.cpow_neg_s_mk qz152 90753 1000 13 qz153 rfl)

noncomputable def ep744 := @Enclosure.Real.IsNear.mulLit_ff qz152 qz541 90753 1000 0 1 11551488463034085 4503599627370496 500000000126849 42283000000000000000 209666446497146463201 900719925474099200 45376500011511927297 42283000000000000000000 qz154 (BSN.isNear_log_sfrac 13 1 11551488463034085 4503599627370496 500000000126849 42283000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz337) Bool.false 24225227133228857425920 9444732965739290427392 1000000000253698 84566000000000000000 11551488463034085 4503599627370496 500000000126849 42283000000000000000 (BSN.log_rat_reduce_isNear 13 1 3 26 16 127272 262144 24973259072661432 36028797018963968 84566 1000000000000000 rfl rfl rfl rfl (ep225 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep745 := nat_lit 10575608505030121393218623115494416

noncomputable def ep746 := BSN.cos_dyadic_bound_f 320683298 1073741824 2 1 524288 169298 ep745 ep228 ep745 ep745 ep229 ep745 501078 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 320683298) qz292 0 1 ep745 ep228 ep745 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 320683298) qz293 0 1 ep745 ep229 ep745 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz450 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 61020967) qz16)

noncomputable def ep747 := @Enclosure.Real.IsNear.cos_image qz172 qz450 Bool.false 61020967 262144 563 524288 Bool.false 501078 524288 1 84566 (@Enclosure.Real.IsNear.recentre' qz172 Bool.false 209666446497146463201 900719925474099200 45376500011511927297 42283000000000000000000 61020967 262144 563 524288 (ep744 rfl) rfl) (Enclosure.sfrac_false_div 61020967 262144) (BSN.cos_reduce0 qz450 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 11283040491562036363264) qz19) 226375608064910080 72057594037927936 Bool.false 501078 524288 37 1000000000000000 169132 84566 (BSN.sin_reduce_arg_pos_rat_q0 61020967 262144 226375608064910080 72057594037927936 37 11283040491562036363264 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 501078 524288 11283040491562036363264 37778931862957161709568 320683298 1073741824 169298 169132 (ep746 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep748 := BSN.sin_dyadic_bound_f 320683298 1073741824 2 1 524288 169298 ep745 ep103 ep745 ep745 ep104 ep745 154266 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 320683298) qz287 0 1 ep745 ep103 ep745 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 320683298) qz288 0 1 ep745 ep104 ep745 rfl rfl rfl rfl) rfl rfl

noncomputable def ep749 := @Enclosure.Real.IsNear.sin_image qz172 qz450 Bool.false 61020967 262144 563 524288 Bool.false 154266 524288 1 84566 (@Enclosure.Real.IsNear.recentre' qz172 Bool.false 209666446497146463201 900719925474099200 45376500011511927297 42283000000000000000000 61020967 262144 563 524288 (ep744 rfl) rfl) (Enclosure.sfrac_false_div 61020967 262144) (BSN.sin_reduce0 qz450 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 11283040491562036363264) qz19) 226375608064910080 72057594037927936 Bool.false 154266 524288 37 1000000000000000 169132 84566 (BSN.sin_reduce_arg_pos_rat_q0 61020967 262144 226375608064910080 72057594037927936 37 11283040491562036363264 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 154266 524288 11283040491562036363264 37778931862957161709568 320683298 1073741824 169298 169132 (ep748 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep750 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz54 (Real.cos qz172)) (@HMul.hMul Real Real Real qz0 qz54 (@Neg.neg Real Real.instNeg (Real.sin qz172))) Bool.false 36431126529 137438953472 1760443232475 5811331269656576 Bool.true 11215986663 137438953472 1753111106577 5811331269656576 (@Enclosure.Real.IsNear.mulLit_ff qz54 (Real.cos qz172) 145411 524288 1 524288 250539 262144 24067473 22168469504 36431126529 137438953472 1760443232475 5811331269656576 qz340 (@Enclosure.Real.IsNear.recentre' (Real.cos qz172) Bool.false 501078 524288 48134946 44336939008 250539 262144 24067473 22168469504 (ep747 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz54 (@Neg.neg Real Real.instNeg (Real.sin qz172)) 145411 524288 1 524288 77133 262144 24067473 22168469504 11215986663 137438953472 1753111106577 5811331269656576 qz340 (@Enclosure.Real.IsNear.neg (Real.sin qz172) Bool.false 77133 262144 24067473 22168469504 (@Enclosure.Real.IsNear.recentre' (Real.sin qz172) Bool.false 154266 524288 48134946 44336939008 77133 262144 24067473 22168469504 (ep749 rfl rfl) rfl)) rfl)

noncomputable def ep751 := @ep689 36431126529 137438953472 1760443232475 5811331269656576 Bool.true 11215986663 137438953472 1753111106577 5811331269656576 Bool.false 35737771184732573270016 520053016731 137438953472 7743612575611 1452832817414144 Bool.false 6229036345216047513600 45322204425 274877906944 61917381376783 11622662539313152 (ep690 (BSN.head_sum_c_succ qz149 12 13 rfl rfl) (ep742 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep743 ep750) rfl rfl

noncomputable abbrev qz173 := (@HMul.hMul Real Real Real qz267 qz433 qz542)

noncomputable def ep752 := @Enclosure.Complex.IsNear.of_eq qz164 (Complex.mk (@HMul.hMul Real Real Real qz0 qz56 (Real.cos qz173)) (@HMul.hMul Real Real Real qz0 qz56 (@Neg.neg Real Real.instNeg (Real.sin qz173)))) Bool.false 54200624373 274877906944 3388738065785 11622662539313152 Bool.true 49590363231 274877906944 3387346870519 11622662539313152 (BSN.cpow_neg_s_mk qz152 90753 1000 14 qz153 rfl)

noncomputable def ep753 := @Enclosure.Real.IsNear.mulLit_ff qz152 qz542 90753 1000 0 1 11885241781671653 4503599627370496 500000000126849 42283000000000000000 1078621347412047524709 4503599627370496000 45376500011511927297 42283000000000000000000 qz154 (BSN.isNear_log_sfrac 14 1 11885241781671653 4503599627370496 500000000126849 42283000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz342) Bool.false 24925158572916270432256 9444732965739290427392 1000000000253698 84566000000000000000 11885241781671653 4503599627370496 500000000126849 42283000000000000000 (BSN.log_rat_reduce_isNear 14 1 3 28 16 146699 262144 24973259072661432 36028797018963968 84566 1000000000000000 rfl rfl rfl rfl (ep238 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep754 := nat_lit 895116301378815309710484970732928239233888211160472656023120965185616773376

noncomputable def ep755 := nat_lit 160614792514440732087550626974227690933279534296647752377828925574512896

noncomputable def ep756 := nat_lit 2685027674551417047667279810944836262319798074412824672564607237705701294336

noncomputable def ep757 := BSN.cos_dyadic_bound_f 795652062 1073741824 3 2 524288 169298 ep754 ep73 ep755 ep756 ep75 ep755 386813 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 795652062) qz292 0 2 ep754 ep73 ep755 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 795652062) qz293 0 2 ep756 ep75 ep755 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz451 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 125568051) qz23)

noncomputable def ep758 := @Enclosure.Real.IsNear.cos_image qz173 qz451 Bool.false 125568051 524288 563 524288 Bool.false 386813 524288 1 84566 (@Enclosure.Real.IsNear.recentre' qz173 Bool.false 1078621347412047524709 4503599627370496000 45376500011511927297 42283000000000000000000 125568051 524288 563 524288 (ep753 rfl) rfl) (Enclosure.sfrac_false_div 125568051 524288) (BSN.cos_reduce0 qz451 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 55989036411054448443392) qz25) 226375608064910080 72057594037927936 Bool.false 386813 524288 38 1000000000000000 169132 84566 (BSN.sin_reduce_arg_pos_rat_q0 125568051 524288 226375608064910080 72057594037927936 38 55989036411054448443392 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 386813 524288 55989036411054448443392 75557863725914323419136 795652062 1073741824 169298 169132 (ep757 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep759 := nat_lit 400767753835610796247503007270200336

noncomputable def ep760 := BSN.sin_dyadic_bound_f 795652062 1073741824 2 1 524288 169298 ep759 ep103 ep759 ep759 ep104 ep759 353911 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 795652062) qz287 0 1 ep759 ep103 ep759 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 795652062) qz288 0 1 ep759 ep104 ep759 rfl rfl rfl rfl) rfl rfl

noncomputable def ep761 := @Enclosure.Real.IsNear.sin_image qz173 qz451 Bool.false 125568051 524288 563 524288 Bool.false 353911 524288 1 84566 (@Enclosure.Real.IsNear.recentre' qz173 Bool.false 1078621347412047524709 4503599627370496000 45376500011511927297 42283000000000000000000 125568051 524288 563 524288 (ep753 rfl) rfl) (Enclosure.sfrac_false_div 125568051 524288) (BSN.sin_reduce0 qz451 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 55989036411054448443392) qz25) 226375608064910080 72057594037927936 Bool.false 353911 524288 38 1000000000000000 169132 84566 (BSN.sin_reduce_arg_pos_rat_q0 125568051 524288 226375608064910080 72057594037927936 38 55989036411054448443392 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 353911 524288 55989036411054448443392 75557863725914323419136 795652062 1073741824 169298 169132 (ep760 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep762 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz56 (Real.cos qz173)) (@HMul.hMul Real Real Real qz0 qz56 (@Neg.neg Real Real.instNeg (Real.sin qz173))) Bool.false 54200624373 274877906944 3388738065785 11622662539313152 Bool.true 49590363231 274877906944 3387346870519 11622662539313152 (@Enclosure.Real.IsNear.mulLit_ff qz56 (Real.cos qz173) 140121 524288 1 524288 386813 524288 24067473 22168469504 54200624373 274877906944 3388738065785 11622662539313152 qz344 (@Enclosure.Real.IsNear.recentre' (Real.cos qz173) Bool.false 386813 524288 48134946 44336939008 386813 524288 24067473 22168469504 (ep758 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz56 (@Neg.neg Real Real.instNeg (Real.sin qz173)) 140121 524288 1 524288 353911 524288 24067473 22168469504 49590363231 274877906944 3387346870519 11622662539313152 qz344 (@Enclosure.Real.IsNear.neg (Real.sin qz173) Bool.false 353911 524288 24067473 22168469504 (@Enclosure.Real.IsNear.recentre' (Real.sin qz173) Bool.false 353911 524288 48134946 44336939008 353911 524288 24067473 22168469504 (ep761 rfl rfl) rfl)) rfl)

noncomputable def ep763 := @ep687 54200624373 274877906944 3388738065785 11622662539313152 Bool.true 49590363231 274877906944 3387346870519 11622662539313152 Bool.false 150400361830284389253120 1094306657835 274877906944 65337638670673 11622662539313152 Bool.true 1173222559097882148864 2134079403 137438953472 32652364123651 5811331269656576 (ep688 (BSN.head_sum_c_succ qz149 13 14 rfl rfl) (ep751 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep752 ep762) rfl rfl

noncomputable abbrev qz174 := (@HMul.hMul Real Real Real qz267 qz433 qz543)

noncomputable def ep764 := @Enclosure.Complex.IsNear.of_eq qz163 (Complex.mk (@HMul.hMul Real Real Real qz0 qz58 (Real.cos qz174)) (@HMul.hMul Real Real Real qz0 qz58 (@Neg.neg Real Real.instNeg (Real.sin qz174)))) Bool.false 26699899185 137438953472 1640232632121 5811331269656576 Bool.true 11687796769 68719476736 819597144245 2905665634828288 (BSN.cpow_neg_s_mk qz152 90753 1000 15 qz153 rfl)

noncomputable def ep765 := @Enclosure.Real.IsNear.mulLit_ff qz152 qz543 90753 1000 0 1 12195956895733477 4503599627370496 500000000126849 42283000000000000000 1106819676158500238181 4503599627370496000 45376500011511927297 42283000000000000000000 qz154 (BSN.isNear_log_sfrac 15 1 12195956895733477 4503599627370496 500000000126849 42283000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz346) Bool.false 25576775395801252757504 9444732965739290427392 1000000000253698 84566000000000000000 12195956895733477 4503599627370496 500000000126849 42283000000000000000 (BSN.log_rat_reduce_isNear 15 1 3 30 16 164785 262144 24973259072661432 36028797018963968 84566 1000000000000000 rfl rfl rfl rfl (ep252 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep766 := nat_lit 793883445120496832887300407759732456215553809404039131667754111402587890625

noncomputable def ep767 := nat_lit 126344902156476416557244795894636716077443555800252962172031402587890625

noncomputable def ep768 := nat_lit 2381397645557177545828786733687408095214506541100516889078918271402587890625

noncomputable def ep769 := BSN.cos_dyadic_bound_f 772137625 1073741824 3 2 524288 169298 ep766 ep73 ep767 ep768 ep75 ep767 394470 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 772137625) qz292 0 2 ep766 ep73 ep767 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 772137625) qz293 0 2 ep768 ep75 ep767 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz452 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 8053173) (@Nat.cast Real Real.instNatCast 32768))

noncomputable def ep770 := @Enclosure.Real.IsNear.cos_image qz174 qz452 Bool.false 8053173 32768 141 131072 Bool.false 394470 524288 1 84566 (@Enclosure.Real.IsNear.recentre' qz174 Bool.false 1106819676158500238181 4503599627370496000 45376500011511927297 42283000000000000000000 8053173 32768 141 131072 (ep765 rfl) rfl) (Enclosure.sfrac_false_div 8053173 32768) (BSN.cos_reduce0 qz452 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 3395897191332594057216) qz339) 226375608064910080 72057594037927936 Bool.false 394470 524288 39 1000000000000000 169132 84566 (BSN.sin_reduce_arg_pos_rat_q0 8053173 32768 226375608064910080 72057594037927936 39 3395897191332594057216 4722366482869645213696 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 394470 524288 3395897191332594057216 4722366482869645213696 772137625 1073741824 169298 169132 (ep769 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep771 := nat_lit 355450280850186439344523535400390625

noncomputable def ep772 := BSN.sin_dyadic_bound_f 772137625 1073741824 2 1 524288 169298 ep771 ep103 ep771 ep771 ep104 ep771 345356 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 772137625) qz287 0 1 ep771 ep103 ep771 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 772137625) qz288 0 1 ep771 ep104 ep771 rfl rfl rfl rfl) rfl rfl

noncomputable def ep773 := @Enclosure.Real.IsNear.sin_image qz174 qz452 Bool.false 8053173 32768 141 131072 Bool.false 345356 524288 1 84566 (@Enclosure.Real.IsNear.recentre' qz174 Bool.false 1106819676158500238181 4503599627370496000 45376500011511927297 42283000000000000000000 8053173 32768 141 131072 (ep765 rfl) rfl) (Enclosure.sfrac_false_div 8053173 32768) (BSN.sin_reduce0 qz452 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 3395897191332594057216) qz339) 226375608064910080 72057594037927936 Bool.false 345356 524288 39 1000000000000000 169132 84566 (BSN.sin_reduce_arg_pos_rat_q0 8053173 32768 226375608064910080 72057594037927936 39 3395897191332594057216 4722366482869645213696 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 345356 524288 3395897191332594057216 4722366482869645213696 772137625 1073741824 169298 169132 (ep772 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep774 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz58 (Real.cos qz174)) (@HMul.hMul Real Real Real qz0 qz58 (@Neg.neg Real Real.instNeg (Real.sin qz174))) Bool.false 26699899185 137438953472 1640232632121 5811331269656576 Bool.true 11687796769 68719476736 819597144245 2905665634828288 (@Enclosure.Real.IsNear.mulLit_ff qz58 (Real.cos qz174) 135371 524288 1 524288 197235 262144 6027439 5542117376 26699899185 137438953472 1640232632121 5811331269656576 qz348 (@Enclosure.Real.IsNear.recentre' (Real.cos qz174) Bool.false 394470 524288 12054878 11084234752 197235 262144 6027439 5542117376 (ep770 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz58 (@Neg.neg Real Real.instNeg (Real.sin qz174)) 135371 524288 1 524288 86339 131072 6027439 5542117376 11687796769 68719476736 819597144245 2905665634828288 qz348 (@Enclosure.Real.IsNear.neg (Real.sin qz174) Bool.false 86339 131072 6027439 5542117376 (@Enclosure.Real.IsNear.recentre' (Real.sin qz174) Bool.false 345356 524288 12054878 11084234752 86339 131072 6027439 5542117376 (ep773 rfl rfl) rfl)) rfl)

noncomputable def ep775 := @ep685 26699899185 137438953472 1640232632121 5811331269656576 Bool.true 11687796769 68719476736 819597144245 2905665634828288 Bool.false 157739574233873000693760 1147706456205 274877906944 68618103934915 11622662539313152 Bool.true 1753011376212018200576 25509672941 137438953472 34291558412141 5811331269656576 (ep686 (BSN.head_sum_c_succ qz149 14 15 rfl rfl) (ep763 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep764 ep774) rfl rfl

noncomputable abbrev qz175 := (@HMul.hMul Real Real Real qz267 qz433 qz544)

noncomputable def ep776 := @Enclosure.Complex.IsNear.of_eq qz162 (Complex.mk (@HMul.hMul Real Real Real qz0 qz60 (Real.cos qz175)) (@HMul.hMul Real Real Real qz0 qz60 (@Neg.neg Real Real.instNeg (Real.sin qz175)))) Bool.false 65783617403 274877906944 3181335480151 11622662539313152 Bool.true 19869446103 274877906944 3166523745251 11622662539313152 (BSN.cpow_neg_s_mk qz152 90753 1000 16 qz153 rfl)

noncomputable def ep777 := @Enclosure.Real.IsNear.mulLit_ff qz152 qz544 90753 1000 0 1 3121657384082679 1125899906842624 125000000042283 10570750000000000000 283299772577655367287 1125899906842624000 11344125003837309099 10570750000000000000000 qz154 (BSN.isNear_log_sfrac 16 1 3121657384082679 1125899906842624 125000000042283 10570750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz350) Bool.false 26186360105375033720832 9444732965739290427392 1000000000338264 84566000000000000000 3121657384082679 1125899906842624 125000000042283 10570750000000000000 (BSN.log_rat_reduce_isNear 16 1 4 32 32 0 262144 24973259072661432 36028797018963968 84566 1000000000000000 rfl rfl rfl rfl (ep263 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep778 := nat_lit 9840755233551264771266319548688561

noncomputable def ep779 := BSN.cos_dyadic_bound_f 314961237 1073741824 2 1 524288 169298 ep778 ep228 ep778 ep778 ep229 ep778 501893 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 314961237) qz292 0 1 ep778 ep228 ep778 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 314961237) qz293 0 1 ep778 ep229 ep778 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz453 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 16490217) (@Nat.cast Real Real.instNatCast 65536))

noncomputable abbrev qz454 := (@Nat.cast Real Real.instNatCast 9444732965739290427392)

noncomputable def ep780 := @Enclosure.Real.IsNear.cos_image qz175 qz453 Bool.false 16490217 65536 141 131072 Bool.false 501893 524288 1 84566 (@Enclosure.Real.IsNear.recentre' qz175 Bool.false 283299772577655367287 1125899906842624000 11344125003837309099 10570750000000000000000 16490217 65536 141 131072 (ep777 rfl) rfl) (Enclosure.sfrac_false_div 16490217 65536) (BSN.cos_reduce0 qz453 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 2770428343964269543424) qz454) 226375608064910080 72057594037927936 Bool.false 501893 524288 40 1000000000000000 169132 84566 (BSN.sin_reduce_arg_pos_rat_q0 16490217 65536 226375608064910080 72057594037927936 40 2770428343964269543424 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 501893 524288 2770428343964269543424 9444732965739290427392 314961237 1073741824 169298 169132 (ep779 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep781 := BSN.sin_dyadic_bound_f 314961237 1073741824 2 1 524288 169298 ep778 ep103 ep778 ep778 ep104 ep778 151593 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 314961237) qz287 0 1 ep778 ep103 ep778 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 314961237) qz288 0 1 ep778 ep104 ep778 rfl rfl rfl rfl) rfl rfl

noncomputable def ep782 := @Enclosure.Real.IsNear.sin_image qz175 qz453 Bool.false 16490217 65536 141 131072 Bool.false 151593 524288 1 84566 (@Enclosure.Real.IsNear.recentre' qz175 Bool.false 283299772577655367287 1125899906842624000 11344125003837309099 10570750000000000000000 16490217 65536 141 131072 (ep777 rfl) rfl) (Enclosure.sfrac_false_div 16490217 65536) (BSN.sin_reduce0 qz453 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 2770428343964269543424) qz454) 226375608064910080 72057594037927936 Bool.false 151593 524288 40 1000000000000000 169132 84566 (BSN.sin_reduce_arg_pos_rat_q0 16490217 65536 226375608064910080 72057594037927936 40 2770428343964269543424 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 151593 524288 2770428343964269543424 9444732965739290427392 314961237 1073741824 169298 169132 (ep781 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep783 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz60 (Real.cos qz175)) (@HMul.hMul Real Real Real qz0 qz60 (@Neg.neg Real Real.instNeg (Real.sin qz175))) Bool.false 65783617403 274877906944 3181335480151 11622662539313152 Bool.true 19869446103 274877906944 3166523745251 11622662539313152 (@Enclosure.Real.IsNear.mulLit_ff qz60 (Real.cos qz175) 131071 524288 1 524288 501893 524288 6027439 5542117376 65783617403 274877906944 3181335480151 11622662539313152 qz352 (@Enclosure.Real.IsNear.recentre' (Real.cos qz175) Bool.false 501893 524288 12054878 11084234752 501893 524288 6027439 5542117376 (ep780 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz60 (@Neg.neg Real Real.instNeg (Real.sin qz175)) 131071 524288 1 524288 151593 524288 6027439 5542117376 19869446103 274877906944 3166523745251 11622662539313152 qz352 (@Enclosure.Real.IsNear.neg (Real.sin qz175) Bool.false 151593 524288 6027439 5542117376 (@Enclosure.Real.IsNear.recentre' (Real.sin qz175) Bool.false 151593 524288 12054878 11084234752 151593 524288 6027439 5542117376 (ep782 rfl rfl) rfl)) rfl)

noncomputable def ep784 := @ep683 65783617403 274877906944 3181335480151 11622662539313152 Bool.true 19869446103 274877906944 3166523745251 11622662539313152 Bool.false 333561611530687534333952 151686259201 34359738368 35899719707533 5811331269656576 Bool.true 9742881383312701521920 70888791985 274877906944 71749640569533 11622662539313152 (ep684 (BSN.head_sum_c_succ qz149 15 16 rfl rfl) (ep775 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep776 ep783) rfl rfl

theorem EMRow25.d12 : Enclosure.Complex.IsNear qz161 Bool.false 151686259201 34359738368 35899719707533 5811331269656576 Bool.true 70888791985 274877906944 71749640569533 11622662539313152 := ep682 (BSN.head_sum_c_succ qz149 16 17 rfl rfl) (ep784 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable def ep785 := nat_lit 1457523241767869502089245535386759

noncomputable def ep786 := nat_lit 327607622477692330865797890048000

noncomputable def ep787 := nat_lit 5916841557439786816580467313855192575021

noncomputable def ep788 := nat_lit 585713972219065589637695936374109110272000

noncomputable abbrev qz564 := (@HAdd.hAdd Complex Complex Complex qz572 (@HAdd.hAdd Complex Complex Complex qz572 qz575 (@HMul.hMul Complex Complex Complex qz574 Complex.I (@HDiv.hDiv Complex Complex Complex qz576 (↑qz579) (2 : Complex)))) (@Nat.cast Complex Complex.instNatCast 2))

noncomputable abbrev qz455 := qz564

noncomputable abbrev qz176 := (Complex.Stirling.logGammaStirling 1 qz455)

noncomputable abbrev qz565 := (@HAdd.hAdd Complex Complex Complex qz572 qz575 (@HMul.hMul Complex Complex Complex qz574 Complex.I (@HDiv.hDiv Complex Complex Complex qz576 (↑qz579) (2 : Complex))))

noncomputable abbrev qz456 := qz565

noncomputable abbrev qz177 := qz456

noncomputable abbrev qz178 := (@HMul.hMul Real Real Real qz267 (@HDiv.hDiv Real Real Real qz270 qz433 (2 : Real)) (Real.log Real.pi))

noncomputable def ep789 := Complex.re (@HMul.hMul Complex Complex Complex qz62 (Complex.exp (@HMul.hMul Complex Complex Complex qz62 Complex.I ↑(@HSub.hSub Real Real Real qz357 (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz176 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz177 (@Nat.cast Complex Complex.instNatCast j))))) qz178))) (zetaApproximant qz149 1 23))

noncomputable def ep790 := @Enclosure.Real.IsNear.of_eq ep789 (@HSub.hSub Real Real Real qz357 (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz357 (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz176 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz177 (@Nat.cast Complex Complex.instNatCast j))))) qz178)) (Complex.re (zetaApproximant qz149 1 23))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz357 (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz176 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz177 (@Nat.cast Complex Complex.instNatCast j))))) qz178)) (Complex.im (zetaApproximant qz149 1 23))))

noncomputable def ep791 := nat_lit 485841128121074947149956093048623

noncomputable def ep792 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz357 (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz176 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz177 (@Nat.cast Complex Complex.instNatCast j))))) qz178)) (Complex.re (zetaApproximant qz149 1 23))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz357 (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz176 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz177 (@Nat.cast Complex Complex.instNatCast j))))) qz178)) (Complex.im (zetaApproximant qz149 1 23))) ep791

noncomputable def ep793 := nat_lit 109202540825897443621932630016000

noncomputable def ep794 := nat_lit 1970388989355332537746576788336050521909

noncomputable def ep795 := nat_lit 195237990739688529879231978791369703424000

noncomputable def ep796 := nat_lit 14259535533936062274375911

noncomputable def ep797 := nat_lit 32760762247769233086579789004800

noncomputable def ep798 := nat_lit 2837294686894601670368474423520504647

noncomputable def ep799 := nat_lit 292856986109532794818847968187054555136000

noncomputable def ep800 := nat_lit 15916524131385015941231640354322231144239115672951002061235814400

noncomputable def ep801 := @Enclosure.Real.IsNear.mulLit_ff (Real.cos (@HSub.hSub Real Real Real qz357 (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz176 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz177 (@Nat.cast Complex Complex.instNatCast j))))) qz178)) (Complex.re (zetaApproximant qz149 1 23)) 524287 524288 1428107

noncomputable def ep802 := nat_lit 926670178968913871886878929

noncomputable def ep803 := nat_lit 208287316943926703685632000

noncomputable def ep804 := nat_lit 68654009117497282516020278721

noncomputable def ep805 := nat_lit 8807012622340052811939577856000

noncomputable def ep806 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HSub.hSub Real Real Real qz357 (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz176 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz177 (@Nat.cast Complex Complex.instNatCast j))))) qz178)) Bool.false 524287 524288 2856214

noncomputable abbrev qz457 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 19765203) qz16)

noncomputable def ep807 := @Enclosure.Real.IsNear.cos_image (@HSub.hSub Real Real Real qz357 (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz176 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz177 (@Nat.cast Complex Complex.instNatCast j))))) qz178) qz457 Bool.false 19765203 262144 33

noncomputable def ep808 := nat_lit 5570005288913823222345829

noncomputable def ep809 := nat_lit 11084234752000000000000000000

noncomputable def ep810 := @Enclosure.Real.IsNear.recentre' (@HSub.hSub Real Real Real qz357 (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz176 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz177 (@Nat.cast Complex Complex.instNatCast j))))) qz178) Bool.false 271650884367938335609 3602879701896396800 ep808 ep809

noncomputable def ep811 := nat_lit 1732696189913823222345829

noncomputable def ep812 := @Enclosure.Real.IsNear.subLit_ff_p (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz176 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz177 (@Nat.cast Complex Complex.instNatCast j))))) qz178 2293991155617256210781 18014398509481984000 ep811 ep809 6808380813 131072000

noncomputable def ep813 := nat_lit 178029123579372067624714240000

noncomputable def ep814 := @Enclosure.Complex.IsNear.im_isNear (@HSub.hSub Complex Complex Complex qz63 qz176 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz177 (@Nat.cast Complex Complex.instNatCast j)))) Bool.true 64232229632228426097 900719925474099200 784739810010557004983641 ep297 Bool.false 2293991155617256210781 18014398509481984000

noncomputable def ep815 := nat_lit 1601624189902738987593829

noncomputable def ep816 := @Enclosure.Complex.IsNear.subLitP qz176 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz177 (@Nat.cast Complex Complex.instNatCast j))) Bool.true 57359392489772586697 900719925474099200 768355809980075359415641 ep297 Bool.false 2349989706446781394781 18014398509481984000 ep815

noncomputable def ep817 := nat_lit 289276245436880071099068368774234112

noncomputable def ep818 := nat_lit 645701107101818035801769745984782336

noncomputable abbrev qz458 := (@HSub.hSub Complex Complex Complex qz546 qz564 qz549)

noncomputable abbrev qz459 := (Complex.log qz564)

noncomputable abbrev qz179 := (@HSub.hSub Complex Complex Complex qz354 (@HMul.hMul Complex Complex Complex qz353 qz458 qz459) qz455)

noncomputable abbrev qz180 := qz455

noncomputable def ep819 := @Enclosure.Complex.IsNear.of_eq qz176 (@HAdd.hAdd Complex Complex Complex qz4 (@HAdd.hAdd Complex Complex Complex qz4 qz179 qz68) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz63 (@HMul.hMul Complex Complex Complex qz62 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz71 qz180 (@HSub.hSub Int Int Int qz366 qz73 (@HMul.hMul Int Int Int qz367 qz74 (@Nat.cast Int instNatCastInt k)))))) Bool.true 57359392489772586697

noncomputable def ep820 := @Enclosure.Complex.IsNear.addLitP (@HAdd.hAdd Complex Complex Complex qz4 qz179 qz68) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz63 (@HMul.hMul Complex Complex Complex qz62 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz71 qz180 (@HSub.hSub Int Int Int qz366 qz73 (@HMul.hMul Int Int Int qz367 qz74 (@Nat.cast Int instNatCastInt k))))) Bool.true 57359474310315153097 900719925474099200

noncomputable def ep821 := nat_lit 985426859448005097363758645248

noncomputable def ep822 := nat_lit 20186257870251132910091320164352000

noncomputable def ep823 := @ep820 46896687383394892099 169132000000000000000000 Bool.false 2350022708489890410333 18014398509481984000 24438250042358390589 169132000000000000000000 Bool.false 1560603 17179869184 3 17179869184 Bool.true 15736600451 8589934592000 30251 8589934592000 Bool.true ep821 57359392489772586697 900719925474099200 768355809980075359415641 ep297 Bool.false ep822

noncomputable def ep824 := @Enclosure.Complex.IsNear.addLitP qz179 qz68 Bool.true 58187179791757252297 900719925474099200 46251500005465204599 169132000000000000000000

noncomputable def ep825 := nat_lit 7518221016801627746729984

noncomputable def ep826 := @ep824 Bool.false 2350022708489890410333 18014398509481984000 24438250042358390589 169132000000000000000000 Bool.false 120447 131072 1 262144 Bool.false 0 1 0 1 Bool.true ep825 57359474310315153097 900719925474099200 46896687383394892099 169132000000000000000000 Bool.false 2350022708489890410333 2350022708489890410333 18014398509481984000

noncomputable abbrev qz181 := (@HMul.hMul Complex Complex Complex qz353 qz458 qz459)

noncomputable def ep827 := @Enclosure.Complex.IsNear.subLitP qz181 qz180 Bool.true 56160559959440529097 900719925474099200 46251500005465204599 169132000000000000000000 Bool.false 3167453062455399657309

noncomputable def ep828 := nat_lit 9400090833959561641332000

noncomputable def ep829 := @ep827 18014398509481984000 24438250042358390589 169132000000000000000000 Bool.false 9000 4000 0 1 Bool.false 181506 4000 0 1 Bool.true 232748719167029009188000 58187179791757252297 900719925474099200 46251500005465204599 169132000000000000000000 Bool.false ep828 2350022708489890410333 18014398509481984000 24438250042358390589 169132000000000000000000

noncomputable abbrev qz182 := qz458

noncomputable abbrev qz183 := qz459

noncomputable def ep830 := @Enclosure.Complex.IsNear.mul qz182 qz183 Bool.true 56160559959440529097 900719925474099200 46251500005465204599 169132000000000000000000 Bool.false 3167453062455399657309 18014398509481984000 24438250042358390589

noncomputable abbrev qz184 := (Complex.re qz458)

noncomputable abbrev qz185 := (Complex.re qz459)

noncomputable abbrev qz186 := (Complex.im qz458)

noncomputable abbrev qz187 := (Complex.im qz459)

noncomputable def ep831 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 qz184 qz185) (@HMul.hMul Real Real Real qz0 qz186 qz187) 240614269956240971 36028797018963968 1750000003255791 338264000000000000000 15543979177086638343 225179981368524800

noncomputable def ep832 := nat_lit 505849353812509529585329450174644224

noncomputable def ep833 := @Enclosure.Real.IsNear.mulLit_ff qz184 qz185 7000 4000 0 1 34373467136605853 9007199254740992 250000000465113 84566000000000000000

noncomputable def ep834 := @Enclosure.Complex.IsNear.re_isNear qz182 Bool.false 7000 4000 0 1 Bool.false 181506 4000 0 1

noncomputable abbrev qz460 := (Enclosure.sfrac Bool.false 181506 4000)

noncomputable abbrev qz188 := qz460

noncomputable def ep835 := @Enclosure.Complex.IsNear.of_eq qz182 (Complex.mk (Enclosure.sfrac Bool.false 7000 4000) qz188) Bool.false 7000 4000 0 1 Bool.false 181506 4000 0

noncomputable abbrev qz461 := (Complex.log (Complex.mk qz83 qz188))

noncomputable def ep836 := @Enclosure.Complex.IsNear.of_eq qz183 qz461 Bool.false 34373467136605853 9007199254740992 250000000465113 84566000000000000000 Bool.false 856389275125155 562949953421312 500000000042283 84566000000000000000

noncomputable def ep837 := BSN.log_dyadic_bound 257428036 65793428036 1 0 1 524288 169132 0 1 4102 66050856072 65536000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 257428036) (BSN.artanhQ 65793428036) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz566 := (Real.log (Enclosure.sfrac Bool.false 33025428036 16000000))

noncomputable def ep838 := @Enclosure.Real.IsNear.mulLit_ff qz84 qz566 1 2 0 1 34373467136605853 4503599627370496 250000000465113 42283000000000000000 34373467136605853 9007199254740992 250000000465113 84566000000000000000 qz371 (BSN.isNear_log_sfrac 33025428036 16000000 34373467136605853 4503599627370496 250000000465113 42283000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 33025428036) qz372)) Bool.false 144172770704934475661312 18889465931478580854784 1000000001860452 169132000000000000000 34373467136605853 4503599627370496 250000000465113 42283000000000000000 (BSN.log_rat_reduce_isNear 33025428036 16000000 11 66050856072 65536000000 4102 524288 24973259072661432 36028797018963968 169132 1000000000000000 rfl rfl rfl rfl (ep837 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep839 := BSN.arctan_dyadic_bound_f 9000 181506 1 0 524288 169132 0 1 1 0 1 1 25975 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 9000) (BSN.arctanEvenQ 181506) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 9000) (BSN.arctanOddQ 181506) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz462 := (Real.arctan (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 9000) (@Nat.cast Real Real.instNatCast 181506)))

noncomputable def ep840 := @Enclosure.Real.IsNear.subLit_ff_p qz85 qz462 884279719003555 562949953421312 1 2000000000000000 25975 524288 1 169132 448994620276817264640 856389275125155 562949953421312 500000000042283 84566000000000000000 qz86 (ep839 rfl) rfl rfl

noncomputable abbrev qz463 := (Complex.mk qz83 qz188)

noncomputable abbrev qz464 := (Real.arctan (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 181506) (@Nat.cast Real Real.instNatCast 9000)))

noncomputable def ep841 := @Enclosure.Complex.IsNear.re_isNear qz183 Bool.false 34373467136605853 9007199254740992 250000000465113 84566000000000000000 Bool.false 856389275125155 562949953421312 500000000042283 84566000000000000000 (ep836 (@congrArg Complex Complex qz180 qz463 Complex.log (BSN.w_shift_mk qz152 Bool.false 90753 1000 2 qz153 rfl)) (@Enclosure.Complex.IsNear.of_parts qz461 Bool.false 34373467136605853 9007199254740992 250000000465113 84566000000000000000 Bool.false 856389275125155 562949953421312 500000000042283 84566000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz461) (@HMul.hMul Real Real Real qz0 qz84 qz566) Bool.false 34373467136605853 9007199254740992 250000000465113 84566000000000000000 (Enclosure.clog_re_eq 9000 181506 4000 33025428036 16000000 rfl rfl rfl) (ep838 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz461) qz464 Bool.false 856389275125155 562949953421312 500000000042283 84566000000000000000 (Enclosure.clog_im_eq 9000 181506 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz464 (@HSub.hSub Real Real Real qz357 qz85 qz462) Bool.false 856389275125155 562949953421312 500000000042283 84566000000000000000 (BSN.arctan_recip 181506 9000 rfl rfl) ep840))))

noncomputable def ep842 := @Enclosure.Real.IsNear.mulLit_ff qz186 qz187 181506 4000 0 1 856389275125155 562949953421312 500000000042283 84566000000000000000

noncomputable def ep843 := @Enclosure.Complex.IsNear.im_isNear qz182 Bool.false 7000 4000 0 1 Bool.false 181506 4000 0 1

noncomputable def ep844 := @Enclosure.Complex.IsNear.im_isNear qz183 Bool.false 34373467136605853 9007199254740992 250000000465113 84566000000000000000 Bool.false 856389275125155 562949953421312 500000000042283 84566000000000000000 (ep836 (@congrArg Complex Complex qz180 qz463 Complex.log (BSN.w_shift_mk qz152 Bool.false 90753 1000 2 qz153 rfl)) (@Enclosure.Complex.IsNear.of_parts qz461 Bool.false 34373467136605853 9007199254740992 250000000465113 84566000000000000000 Bool.false 856389275125155 562949953421312 500000000042283 84566000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz461) (@HMul.hMul Real Real Real qz0 qz84 qz566) Bool.false 34373467136605853 9007199254740992 250000000465113 84566000000000000000 (Enclosure.clog_re_eq 9000 181506 4000 33025428036 16000000 rfl rfl rfl) (ep838 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz461) qz464 Bool.false 856389275125155 562949953421312 500000000042283 84566000000000000000 (Enclosure.clog_im_eq 9000 181506 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz464 (@HSub.hSub Real Real Real qz357 qz85 qz462) Bool.false 856389275125155 562949953421312 500000000042283 84566000000000000000 (BSN.arctan_recip 181506 9000 rfl rfl) ep840))))

noncomputable abbrev qz465 := (Enclosure.Real.IsNear.const Bool.false 181506 4000)

noncomputable abbrev qz189 := (@ep835 1 (BSN.w_sub_half_mk qz433 Bool.false 90753 1000 2 qz434 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7000 4000) qz460 Bool.false 7000 4000 0 1 Bool.false 181506 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 7000 4000) qz465))

noncomputable def ep845 := @ep831 45376500003837309099 169132000000000000000000 ep832 56160559959440529097 900719925474099200 46251500005465204599 169132000000000000000000 (@ep833 240614269956240971 36028797018963968 1750000003255791 338264000000000000000 (ep834 qz189) ep841 rfl) (@ep842 15543979177086638343 225179981368524800 45376500003837309099 169132000000000000000000 (ep843 qz189) ep844 rfl) rfl

noncomputable def ep846 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz184 qz187) (@HMul.hMul Real Real Real qz0 qz186 qz185) 5994724925876085 2251799813685248 3500000000295981 338264000000000000000 3119495263048390977309 18014398509481984000

noncomputable def ep847 := nat_lit 7132470215893837145310107987588677632

noncomputable def ep848 := @Enclosure.Real.IsNear.mulLit_ff qz184 qz187 7000 4000 0 1 856389275125155 562949953421312 500000000042283 84566000000000000000

noncomputable def ep849 := @Enclosure.Real.IsNear.mulLit_ff qz186 qz185 181506 4000 0 1 34373467136605853 9007199254740992 250000000465113 84566000000000000000

noncomputable def ep850 := @ep846 22688250042210400089 169132000000000000000000 ep847 3167453062455399657309 18014398509481984000 24438250042358390589 169132000000000000000000 (@ep848 5994724925876085 2251799813685248 3500000000295981 338264000000000000000 (ep834 qz189) ep844 rfl) (@ep849 3119495263048390977309 18014398509481984000 22688250042210400089 169132000000000000000000 (ep843 qz189) ep841 rfl) rfl

noncomputable def ep851 := @Enclosure.Complex.IsNear.of_eq qz180 qz463 Bool.false 9000 4000 0 1 Bool.false 181506 4000 0 1 (BSN.w_shift_mk qz152 Bool.false 90753 1000 2 qz153 rfl)

noncomputable abbrev qz466 := (ep851 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 9000 4000) (Enclosure.sfrac Bool.false 181506 4000) Bool.false 9000 4000 0 1 Bool.false 181506 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 9000 4000) (Enclosure.Real.IsNear.const Bool.false 181506 4000)))

noncomputable abbrev qz190 := qz466

noncomputable def ep852 := ep829 (@ep830 169132000000000000000000 (ep845 rfl) (ep850 rfl)) qz190 rfl rfl rfl rfl rfl rfl

noncomputable def ep853 := @ep826 24438250042358390589 169132000000000000000000 (ep852 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@Enclosure.Complex.IsNear.mul qz89 (↑qz2) Bool.false 120447 131072 1 262144 Bool.false 0 1 0 1 (@ep338 131072 1 262144 (ep340 rfl) (ep342 rfl) rfl rfl) (@ep343 1 0 1 (ep345 rfl) (ep347 rfl) rfl rfl))

noncomputable abbrev qz467 := (@HPow.hPow Complex Int Complex qz551 qz564 (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) (@OfNat.ofNat Int 1 (@instOfNat 1)) (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (@OfNat.ofNat Int 2 (@instOfNat 2)) (@Nat.cast Int instNatCastInt 1))))

noncomputable abbrev qz191 := qz467

noncomputable def ep854 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz63 (@HMul.hMul Complex Complex Complex qz62 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz71 qz180 (@HSub.hSub Int Int Int qz366 qz73 (@HMul.hMul Int Int Int qz367 qz74 (@Nat.cast Int instNatCastInt k))))) (@HAdd.hAdd Complex Complex Complex qz4 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz63 (@HMul.hMul Complex Complex Complex qz62 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz71 qz180 (@HSub.hSub Int Int Int qz366 qz73 (@HMul.hMul Int Int Int qz367 qz74 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli qz91)) qz92) qz191)) Bool.false 1560603 17179869184 3 17179869184

noncomputable def ep855 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz63 (@HMul.hMul Complex Complex Complex qz62 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz71 qz180 (@HSub.hSub Int Int Int qz366 qz73 (@HMul.hMul Int Int Int qz367 qz74 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli qz91)) qz92) qz191) Bool.false 0 1 0 1 Bool.false

noncomputable def ep856 := @ep855 0 1 0 1 Bool.false 1560603 17179869184 3 17179869184 Bool.true 15736600451 8589934592000 30251 8589934592000 Bool.false 1560603 1560603 17179869184 3 17179869184 Bool.true 15736600451 15736600451 8589934592000 30251

noncomputable def ep857 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz63 (@HMul.hMul Complex Complex Complex qz62 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz71 qz180 (@HSub.hSub Int Int Int qz366 qz73 (@HMul.hMul Int Int Int qz367 qz74 (@Nat.cast Int instNatCastInt k))))) (Complex.mk qz10 qz10) Bool.false 0 1 0 1 Bool.false

noncomputable def ep858 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli qz91)) qz92) qz191 Bool.false 1560603 17179869184 3 17179869184 Bool.true 15736600451 8589934592000 30251 8589934592000

noncomputable abbrev qz192 := (Complex.re qz467)

noncomputable abbrev qz193 := (Complex.im qz467)

noncomputable def ep859 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli qz91)) qz92)) qz192) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli qz91)) qz92)) qz193) 1560603 17179869184 3 17179869184 0 1 0

noncomputable def ep860 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli qz91)) qz92)) qz192 1 12 0 1 4681809 4294967296 9 4294967296 1560603

noncomputable def ep861 := @Enclosure.Complex.IsNear.re_isNear qz191 Bool.false 4681809 4294967296 9 4294967296 Bool.true 47209801353 2147483648000 90753 2147483648000

noncomputable abbrev qz468 := (@HPow.hPow Complex Nat Complex qz553 qz564 1)

noncomputable abbrev qz194 := (@Inv.inv Complex Complex.instInv qz468)

noncomputable def ep862 := @Enclosure.Complex.IsNear.of_eq qz191 qz194 Bool.false 4681809 4294967296 9 4294967296 Bool.true 47209801353 2147483648000 90753

noncomputable def ep863 := @Enclosure.Complex.IsNear.of_parts qz194 Bool.false 4681809 4294967296 9 4294967296 Bool.true 47209801353 2147483648000 90753

noncomputable abbrev qz195 := (Complex.re qz468)

noncomputable abbrev qz196 := qz468

noncomputable def ep864 := @Enclosure.Real.IsNear.mulLit_ff qz195 (@Inv.inv Real Real.instInv (@DFunLike.coe qz98 Complex (fun (x : Complex) => Real) qz99 Complex.normSq qz196)) 9000 4000 0 1 520201 1073741824 1 1073741824

noncomputable def ep865 := @Enclosure.Complex.IsNear.re_isNear qz196 Bool.false 9000 4000 0 1 Bool.false 181506 4000 0 1

noncomputable def ep866 := @Enclosure.Complex.IsNear.of_eq qz196 qz180 Bool.false 9000 4000 0 1 Bool.false 181506 4000 0

noncomputable def ep867 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (@DFunLike.coe qz98 Complex (fun (x : Complex) => Real) qz99 Complex.normSq qz196)) Bool.false 520201 1073741824 1 1073741824 520201 1073741824 1

noncomputable abbrev qz197 := (Complex.im qz468)

noncomputable def ep868 := @Enclosure.Real.IsNear.of_eq (@DFunLike.coe qz98 Complex (fun (x : Complex) => Real) qz99 Complex.normSq qz196) (@HAdd.hAdd Real Real Real qz381 (@HMul.hMul Real Real Real qz0 qz195 qz195) (@HMul.hMul Real Real Real qz0 qz197 qz197)) Bool.false 8256357009 4000000 0 1

noncomputable def ep869 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz195 qz195) (@HMul.hMul Real Real Real qz0 qz197 qz197) 81 16 0 1 8236107009 4000000

noncomputable def ep870 := @Enclosure.Real.IsNear.mulLit_ff qz195 qz195 9000 4000 0 1 9000 4000 0 1

noncomputable def ep871 := @Enclosure.Real.IsNear.mulLit_ff qz197 qz197 181506 4000 0 1 181506 4000 0 1

noncomputable def ep872 := @Enclosure.Complex.IsNear.im_isNear qz196 Bool.false 9000 4000 0 1 Bool.false 181506 4000 0 1

noncomputable abbrev qz198 := (ep865 (@ep866 1 (BSN.pow_one_c qz455) qz466))

noncomputable abbrev qz199 := (ep872 (@ep866 1 (BSN.pow_one_c qz455) qz466))

noncomputable def ep873 := @ep869 0 1 132101712144 8256357009 4000000 0 1 (@ep870 81 16 0 1 qz198 qz198 rfl) (@ep871 8236107009 4000000 0 1 qz199 qz199 rfl)

noncomputable def ep874 := @Enclosure.Real.IsNear.inv_image (@DFunLike.coe qz98 Complex (fun (x : Complex) => Real) qz99 Complex.normSq qz196) 8256357009 4000000 0 1 260100 260101 536870912 (ep868 (Enclosure.Complex.normSq_eq_mul_add_mul qz196) (ep873 rfl rfl)) rfl

noncomputable def ep875 := @Enclosure.Real.IsNear.of_eq (Complex.re qz194) (@HMul.hMul Real Real Real qz0 qz195 (@Inv.inv Real Real.instInv (@DFunLike.coe qz98 Complex (fun (x : Complex) => Real) qz99 Complex.normSq qz196))) Bool.false 4681809 4294967296 9 4294967296 (Enclosure.Complex.inv_re_eq_mul qz196) (@ep864 4681809 4294967296 9 4294967296 qz198 (@ep867 1073741824 (ep874 rfl rfl rfl rfl rfl) rfl) rfl)

noncomputable def ep876 := @Enclosure.Real.IsNear.of_eq (Complex.im qz194) (@HMul.hMul Real Real Real qz0 (@Neg.neg Real Real.instNeg qz197) (@Inv.inv Real Real.instInv (@DFunLike.coe qz98 Complex (fun (x : Complex) => Real) qz99 Complex.normSq qz196))) Bool.true 47209801353 2147483648000 90753 2147483648000 (Enclosure.Complex.inv_im_eq_mul qz196)

noncomputable def ep877 := @Enclosure.Real.IsNear.mulLit_tf (@Neg.neg Real Real.instNeg qz197) (@Inv.inv Real Real.instInv (@DFunLike.coe qz98 Complex (fun (x : Complex) => Real) qz99 Complex.normSq qz196)) 181506 4000 0 1 520201 1073741824 1

noncomputable def ep878 := @ep877 1073741824 47209801353 2147483648000 90753 2147483648000 (@Enclosure.Real.IsNear.neg qz197 Bool.false 181506 4000 0 1 qz199) (@ep867 1073741824 (ep874 rfl rfl rfl rfl rfl) rfl) rfl

noncomputable def ep879 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli qz91)) qz92)) qz193 0 1 0 1 47209801353 2147483648000 90753 2147483648000 0

noncomputable def ep880 := @Enclosure.Complex.IsNear.im_isNear qz191 Bool.false 4681809 4294967296 9 4294967296 Bool.true 47209801353 2147483648000 90753 2147483648000

noncomputable abbrev qz200 := (@ep862 2147483648000 (BSN.zpow_one_sub_two_mul qz455 1 1 rfl rfl) (@ep863 2147483648000 ep875 (ep876 ep878)))

noncomputable def ep881 := @ep859 1 1560603 1560603 17179869184 3 17179869184 (@ep860 17179869184 3 17179869184 ep357 (ep861 qz200) rfl) (@ep879 1 0 1 ep377 (ep880 qz200) rfl) rfl

noncomputable def ep882 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli qz91)) qz92)) qz193) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli qz91)) qz92)) qz192) 15736600451 8589934592000 30251 8589934592000 0 1 0

noncomputable def ep883 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli qz91)) qz92)) qz193 1 12 0 1 47209801353 2147483648000 90753 2147483648000 15736600451

noncomputable def ep884 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli qz91)) qz92)) qz192 0 1 0 1 4681809 4294967296 9 4294967296 0

noncomputable def ep885 := @ep882 1 15736600451 15736600451 8589934592000 30251 8589934592000 (@ep883 8589934592000 30251 8589934592000 ep357 (ep880 qz200) rfl) (@ep884 1 0 1 ep377 (ep861 qz200) rfl) rfl

noncomputable def ep886 := @ep856 8589934592000 (@ep857 0 1 0 1 (BSN.stirling_sum_base qz180) qz105) (ep858 (ep881 rfl) (ep885 rfl)) rfl rfl rfl rfl rfl

noncomputable def ep887 := @ep823 2349989706446781394781 18014398509481984000 ep815 ep809 (ep853 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep854 Bool.true 15736600451 8589934592000 30251 8589934592000 (BSN.stirling_sum_succ qz180 0 1 rfl) (ep886 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl

noncomputable def ep888 := @Enclosure.Complex.IsNear.of_eq (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz177 (@Nat.cast Complex Complex.instNatCast j))) (BSN.logSumC qz152 2) Bool.false 34364185712279197 4503599627370496 250000000465113 42283000000000000000 Bool.false 874977356711331 281474976710656

noncomputable abbrev qz201 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz273 qz456 qz377))

noncomputable def ep889 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz152 2) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.logSumC qz152 1) qz201) Bool.false 34364185712279197 4503599627370496 250000000465113 42283000000000000000 Bool.false 874977356711331 281474976710656 500000000042283 42283000000000000000

noncomputable def ep890 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz152 1) qz201 Bool.false 34362549329739421 9007199254740992 250000000465113 84566000000000000000 Bool.false 881178752615843 562949953421312 500000000042283 84566000000000000000 Bool.false

noncomputable def ep891 := nat_lit 619050135874844457114864449486848

noncomputable def ep892 := nat_lit 985136924410692962256414572544

noncomputable abbrev qz202 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz273 qz456 (@Nat.cast Complex Complex.instNatCast 0)))

noncomputable def ep893 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz152 1) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.logSumC qz152 0) qz202) Bool.false 34362549329739421 9007199254740992 250000000465113 84566000000000000000 Bool.false 881178752615843 562949953421312 500000000042283 84566000000000000000

noncomputable def ep894 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz152 0) qz202 Bool.false 0 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable abbrev qz469 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz188))

noncomputable def ep895 := @Enclosure.Complex.IsNear.of_eq qz202 qz469 Bool.false 34362549329739421 9007199254740992 250000000465113 84566000000000000000 Bool.false 881178752615843 562949953421312 500000000042283 84566000000000000000

noncomputable def ep896 := BSN.log_dyadic_bound 177428036 65713428036 1 0 1 524288 169132 0 1 2831 65890856072 65536000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 177428036) (BSN.artanhQ 65713428036) 0 0 rfl) rfl rfl rfl

noncomputable def ep897 := @Enclosure.Real.IsNear.mulLit_ff qz84 (Real.log (Enclosure.sfrac Bool.false 32945428036 16000000)) 1 2 0 1 34362549329739421 4503599627370496 250000000465113 42283000000000000000 34362549329739421 9007199254740992 250000000465113 84566000000000000000 qz371 (BSN.isNear_log_sfrac 32945428036 16000000 34362549329739421 4503599627370496 250000000465113 42283000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 32945428036) qz372)) Bool.false 144126978103923372457984 18889465931478580854784 1000000001860452 169132000000000000000 34362549329739421 4503599627370496 250000000465113 42283000000000000000 (BSN.log_rat_reduce_isNear 32945428036 16000000 11 65890856072 65536000000 2831 524288 24973259072661432 36028797018963968 169132 1000000000000000 rfl rfl rfl rfl (ep896 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep898 := BSN.arctan_dyadic_bound_f 1000 181506 1 0 524288 169132 0 1 1 0 1 1 2888 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 181506) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 181506) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz470 := (@Nat.cast Real Real.instNatCast 181506)

noncomputable def ep899 := @Enclosure.Real.IsNear.subLit_ff_p qz85 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz383 qz470)) 884279719003555 562949953421312 1 2000000000000000 2888 524288 1 169132 461991445851455094784 881178752615843 562949953421312 500000000042283 84566000000000000000 qz86 (ep898 rfl) rfl rfl

noncomputable abbrev qz203 := (@HAdd.hAdd Complex Complex Complex qz273 qz456 (@Nat.cast Complex Complex.instNatCast 0))

noncomputable abbrev qz471 := (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz188)

noncomputable def ep900 := @ep894 34362549329739421 9007199254740992 250000000465113 84566000000000000000 Bool.false 881178752615843 562949953421312 500000000042283 84566000000000000000 Bool.false 34362549329739421 34362549329739421 9007199254740992 250000000465113 84566000000000000000 Bool.false 881178752615843 881178752615843 562949953421312 500000000042283 84566000000000000000 (@Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz152 0) (Complex.mk qz10 qz10) Bool.false 0 1 0 1 Bool.false 0 1 0 1 (BSN.log_sum_c_base qz152) qz105) (ep895 (@congrArg Complex Complex qz203 qz471 Complex.log (BSN.w_shift_mk qz152 Bool.false 90753 1000 0 qz153 rfl)) (@Enclosure.Complex.IsNear.of_parts qz469 Bool.false 34362549329739421 9007199254740992 250000000465113 84566000000000000000 Bool.false 881178752615843 562949953421312 500000000042283 84566000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz469) (@HMul.hMul Real Real Real qz0 qz84 (Real.log (Enclosure.sfrac Bool.false 32945428036 16000000))) Bool.false 34362549329739421 9007199254740992 250000000465113 84566000000000000000 (Enclosure.clog_re_eq 1000 181506 4000 32945428036 16000000 rfl rfl rfl) (ep897 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz469) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz470 qz383)) Bool.false 881178752615843 562949953421312 500000000042283 84566000000000000000 (Enclosure.clog_im_eq 1000 181506 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz470 qz383)) (@HSub.hSub Real Real Real qz357 qz85 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz383 qz470))) Bool.false 881178752615843 562949953421312 500000000042283 84566000000000000000 (BSN.arctan_recip 181506 1000 rfl rfl) ep899)))) rfl rfl

noncomputable abbrev qz472 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz188))

noncomputable def ep901 := @Enclosure.Complex.IsNear.of_eq qz201 qz472 Bool.false 34365822094818973 9007199254740992 250000000465113 84566000000000000000 Bool.false 868775960806819 562949953421312 500000000042283 84566000000000000000

noncomputable def ep902 := BSN.log_dyadic_bound 201428036 65737428036 1 0 1 524288 169132 0 1 3212 65938856072 65536000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 201428036) (BSN.artanhQ 65737428036) 0 0 rfl) rfl rfl rfl

noncomputable def ep903 := @Enclosure.Real.IsNear.mulLit_ff qz84 (Real.log (Enclosure.sfrac Bool.false 32969428036 16000000)) 1 2 0 1 34365822094818973 4503599627370496 250000000465113 42283000000000000000 34365822094818973 9007199254740992 250000000465113 84566000000000000000 qz371 (BSN.isNear_log_sfrac 32969428036 16000000 34365822094818973 4503599627370496 250000000465113 42283000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 32969428036) qz372)) Bool.false 144140705075587597729792 18889465931478580854784 1000000001860452 169132000000000000000 34365822094818973 4503599627370496 250000000465113 42283000000000000000 (BSN.log_rat_reduce_isNear 32969428036 16000000 11 65938856072 65536000000 3212 524288 24973259072661432 36028797018963968 169132 1000000000000000 rfl rfl rfl rfl (ep902 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep904 := BSN.arctan_dyadic_bound_f 5000 181506 1 0 524288 169132 0 1 1 0 1 1 14439 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 5000) (BSN.arctanEvenQ 181506) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 5000) (BSN.arctanOddQ 181506) 0 0 rfl) rfl rfl rfl

noncomputable def ep905 := @Enclosure.Real.IsNear.subLit_ff_p qz85 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz387 qz470)) 884279719003555 562949953421312 1 2000000000000000 14439 524288 1 169132 455488810939485519872 868775960806819 562949953421312 500000000042283 84566000000000000000 qz86 (ep904 rfl) rfl rfl

noncomputable abbrev qz204 := (@HAdd.hAdd Complex Complex Complex qz273 qz456 qz377)

noncomputable abbrev qz473 := (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz188)

noncomputable def ep906 := @ep890 34365822094818973 9007199254740992 250000000465113 84566000000000000000 Bool.false 868775960806819 562949953421312 500000000042283 84566000000000000000 Bool.false ep891 34364185712279197 4503599627370496 250000000465113 42283000000000000000 Bool.false ep892 874977356711331 281474976710656 500000000042283 42283000000000000000 (ep893 (BSN.log_sum_c_succ qz152 0 1 rfl) (ep900 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep901 (@congrArg Complex Complex qz204 qz473 Complex.log (BSN.w_shift_mk qz152 Bool.false 90753 1000 1 qz153 rfl)) (@Enclosure.Complex.IsNear.of_parts qz472 Bool.false 34365822094818973 9007199254740992 250000000465113 84566000000000000000 Bool.false 868775960806819 562949953421312 500000000042283 84566000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz472) (@HMul.hMul Real Real Real qz0 qz84 (Real.log (Enclosure.sfrac Bool.false 32969428036 16000000))) Bool.false 34365822094818973 9007199254740992 250000000465113 84566000000000000000 (Enclosure.clog_re_eq 5000 181506 4000 32969428036 16000000 rfl rfl rfl) (ep903 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz472) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz470 qz387)) Bool.false 868775960806819 562949953421312 500000000042283 84566000000000000000 (Enclosure.clog_im_eq 5000 181506 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz470 qz387)) (@HSub.hSub Real Real Real qz357 qz85 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz387 qz470))) Bool.false 868775960806819 562949953421312 500000000042283 84566000000000000000 (BSN.arctan_recip 181506 5000 rfl rfl) ep905)))) rfl rfl

noncomputable def ep907 := @ep816 ep809 Bool.false 34364185712279197 4503599627370496 250000000465113 42283000000000000000 Bool.false 874977356711331 281474976710656 500000000042283 42283000000000000000 Bool.true ep817 64232229632228426097 900719925474099200 784739810010557004983641 ep297 Bool.false ep818 2293991155617256210781 18014398509481984000 ep811 ep809 (@ep819 900719925474099200 768355809980075359415641 ep297 Bool.false 2349989706446781394781 18014398509481984000 ep815 ep809 (BSN.logGammaStirling_unfold 1 qz180) (ep887 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (@ep888 500000000042283 42283000000000000000 (BSN.log_sum_c_eq qz152 2) (ep889 (BSN.log_sum_c_succ qz152 1 2 rfl) (ep906 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)))

noncomputable abbrev qz205 := (@HDiv.hDiv Real Real Real qz270 qz433 (2 : Real))

noncomputable def ep908 := @Enclosure.Real.IsNear.mulLit_ff qz205 (Real.log Real.pi) 90753 2000 0 1 75021 65536 1 131072 6808380813 131072000 90753 262144000 (@Enclosure.Real.IsNear.of_eq qz205 (Enclosure.sfrac Bool.false 90753 2000) Bool.false 90753 2000 0 1 (BSN.t_half_eq qz152 Bool.false 90753 1000 qz153) (Enclosure.Real.IsNear.const Bool.false 90753 2000)) EMRow25.d5 rfl

noncomputable def ep909 := @ep812 90753 262144000 ep813 271650884367938335609 3602879701896396800 ep808 ep809 (@ep814 ep811 ep809 (ep907 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) ep908 rfl rfl

noncomputable def ep910 := BSN.cos_dyadic_bound_f 45260 1073741824 1 0 524288 169298 0 1 1 0 1 1 524287 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 45260) qz292 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 45260) qz293 0 0 rfl) rfl rfl

noncomputable def ep911 := @ep807 65536 Bool.false 524287 524288 1 84566 (@ep810 19765203 262144 33 65536 ep909 rfl) (Enclosure.sfrac_false_div 19765203 262144) (BSN.cos_reduce0 qz457 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 1592475216884269056) qz19) 226375608064910080 72057594037927936 Bool.false 524287 524288 12 1000000000000000 169132 84566 (BSN.sin_reduce_arg_pos_rat_q0 19765203 262144 226375608064910080 72057594037927936 12 1592475216884269056 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 524287 524288 1592475216884269056 37778931862957161709568 45260 1073741824 169298 169132 (ep910 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep912 := nat_lit 1296321412176005661306901

noncomputable def ep913 := nat_lit 124972390166356022211379200

noncomputable def ep914 := nat_lit 205864507613475170113615412647

noncomputable def ep915 := nat_lit 26421037867020158435818733568000

noncomputable abbrev qz474 := (@HPow.hPow Complex Complex Complex qz526 qz554 qz562)

noncomputable abbrev qz206 := qz474

noncomputable abbrev qz207 := (@HAdd.hAdd Complex Complex Complex qz273 (@HDiv.hDiv Complex Complex Complex qz362 qz390 (@HSub.hSub Complex Complex Complex qz354 qz426 (1 : Complex))) qz361)

noncomputable def ep916 := @Enclosure.Complex.IsNear.of_eq (zetaApproximant qz149 1 23) (@HAdd.hAdd Complex Complex Complex qz4 (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 23, @HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast n) qz150) (@HMul.hMul Complex Complex Complex qz62 qz206 (@HAdd.hAdd Complex Complex Complex qz4 qz207 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1))))))) Bool.false ep802 ep803 ep804

noncomputable def ep917 := @Enclosure.Complex.IsNear.addLitP (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 23, @HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast n) qz150) (@HMul.hMul Complex Complex Complex qz62 qz206 (@HAdd.hAdd Complex Complex Complex qz4 qz207 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))))) Bool.false 9574898103 2147483648 44541899568219 5811331269656576

noncomputable def ep918 := nat_lit 2012019725696887957473071

noncomputable def ep919 := nat_lit 1151219564168349805377614721

noncomputable def ep920 := nat_lit 13131793232503070257245899

noncomputable def ep921 := nat_lit 3469341294309553784634008647

noncomputable def ep922 := nat_lit 1990009056424976040197439405783252992

noncomputable def ep923 := nat_lit 356330116505630752718335514503020544

noncomputable def ep924 := @ep917 Bool.false 31734769171 274877906944 89034001221131 11622662539313152 Bool.true ep918 ep803 ep919 ep805 Bool.true ep920 ep913 ep921 ep915 Bool.false ep922 ep802 ep803 ep804 ep805 Bool.false ep923 ep912 ep913

noncomputable def ep925 := @Enclosure.Complex.IsNear.of_eq (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 23, @HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast n) qz150) (BSN.headSumC qz149 23) Bool.false 9574898103 2147483648 44541899568219 5811331269656576 Bool.false 31734769171 274877906944 89034001221131

noncomputable abbrev qz475 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 22) qz150)

noncomputable def ep926 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz149 23) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz149 22) qz475) Bool.false 9574898103 2147483648 44541899568219 5811331269656576 Bool.false 31734769171 274877906944 89034001221131 11622662539313152

noncomputable def ep927 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz149 22) qz475 Bool.false 1261119824599 274877906944 86375369479303 11622662539313152 Bool.true 14868578625 274877906944 86321383897959 11622662539313152 Bool.true

noncomputable abbrev qz476 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 21) qz150)

noncomputable def ep928 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz149 22) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz149 21) qz476) Bool.false 1261119824599 274877906944 86375369479303 11622662539313152 Bool.true 14868578625 274877906944 86321383897959 11622662539313152

noncomputable def ep929 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz149 21) qz476 Bool.false 600955611073 137438953472 41799963861031 5811331269656576 Bool.true 12238609245 137438953472 41782136587137 5811331269656576 Bool.false

noncomputable abbrev qz477 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 20) qz150)

noncomputable def ep930 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz149 21) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz149 20) qz477) Bool.false 600955611073 137438953472 41799963861031 5811331269656576 Bool.true 12238609245 137438953472 41782136587137 5811331269656576

noncomputable def ep931 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz149 20) qz477 Bool.false 604746522033 137438953472 40387809465629 5811331269656576 Bool.false 36518159015 274877906944 80720699783557 11622662539313152 Bool.true

noncomputable abbrev qz478 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 19) qz150)

noncomputable def ep932 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz149 20) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz149 19) qz478) Bool.false 604746522033 137438953472 40387809465629 5811331269656576 Bool.false 36518159015 274877906944 80720699783557 11622662539313152

noncomputable def ep933 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz149 19) qz478 Bool.false 635761183857 137438953472 38926945814541 5811331269656576 Bool.false 25159250813 274877906944 77816785209923 11622662539313152 Bool.true

noncomputable abbrev qz479 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 18) qz150)

noncomputable def ep934 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz149 19) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz149 18) qz479) Bool.false 635761183857 137438953472 38926945814541 5811331269656576 Bool.false 25159250813 274877906944 77816785209923 11622662539313152

noncomputable def ep935 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz149 18) qz479 Bool.false 1272372192989 274877906944 74879438805443 11622662539313152 Bool.true 39623954337 274877906944 74820456641989 11622662539313152 Bool.true

noncomputable abbrev qz480 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 17) qz150)

noncomputable def ep936 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz149 18) (@HAdd.hAdd Complex Complex Complex qz4 qz161 qz480) Bool.false 1272372192989 274877906944 74879438805443 11622662539313152 Bool.true 39623954337 274877906944 74820456641989 11622662539313152

noncomputable def ep937 := @Enclosure.Complex.IsNear.addLitP qz161 qz480 Bool.false 151686259201 34359738368 35899719707533 5811331269656576 Bool.true 70888791985 274877906944 71749640569533 11622662539313152 Bool.false

noncomputable abbrev qz208 := (@HMul.hMul Real Real Real qz267 qz433 qz555)

noncomputable def ep938 := @Enclosure.Complex.IsNear.of_eq qz480 (Complex.mk (@HMul.hMul Real Real Real qz0 qz122 (Real.cos qz208)) (@HMul.hMul Real Real Real qz0 qz122 (@Neg.neg Real Real.instNeg (Real.sin qz208)))) Bool.false 58882119381 274877906944 3079999390377 11622662539313152 Bool.false 1954052353 17179869184 383852009057 1452832817414144 (BSN.cpow_neg_s_mk qz152 90753 1000 17 qz153 rfl)

noncomputable def ep939 := @Enclosure.Real.IsNear.mulLit_ff qz152 qz555 90753 1000 0 1 3189913004350711 1125899906842624 125000000042283 10570750000000000000 289494174883840075383 1125899906842624000 11344125003837309099 10570750000000000000000 qz154 (BSN.isNear_log_sfrac 17 1 3189913004350711 1125899906842624 125000000042283 10570750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz393) Bool.false 26758929747600409100288 9444732965739290427392 1000000000338264 84566000000000000000 3189913004350711 1125899906842624 125000000042283 10570750000000000000 (BSN.log_rat_reduce_isNear 17 1 4 34 32 15892 262144 24973259072661432 36028797018963968 84566 1000000000000000 rfl rfl rfl rfl (ep442 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep940 := nat_lit 7344699398926917978106428971269924528887525344619053124996360287010491040000

noncomputable def ep941 := nat_lit 3335730404043302094534458071488530580831350203762774782068138384100000000

noncomputable def ep942 := nat_lit 19230716767011572215459020087876916145193601335577142263438547575262743200000

noncomputable def ep943 := BSN.sin_dyadic_bound_f 1162515810 1073741824 3 2 524288 169298 ep940 ep66 ep941 ep942 ep69 ep941 463059 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1162515810) qz287 0 2 ep940 ep66 ep941 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1162515810) qz288 0 2 ep942 ep69 ep941 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz481 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 67403115) qz16)

noncomputable def ep944 := @Enclosure.Real.IsNear.cos_image qz208 qz481 Bool.false 67403115 262144 563 524288 Bool.false 463059 524288 1 84566 (@Enclosure.Real.IsNear.recentre' qz208 Bool.false 289494174883840075383 1125899906842624000 11344125003837309099 10570750000000000000000 67403115 262144 563 524288 (ep939 rfl) rfl) (Enclosure.sfrac_false_div 67403115 262144) (BSN.cos_reduce3 qz481 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 40902388830992617963520) qz19) 226375608064910080 72057594037927936 Bool.false 463059 524288 40 1000000000000000 169132 84566 (BSN.sin_reduce_arg_pos_rat_q3 67403115 262144 226375608064910080 72057594037927936 40 40902388830992617963520 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 463059 524288 40902388830992617963520 37778931862957161709568 1162515810 1073741824 169298 169132 (ep943 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep945 := nat_lit 4081871101805640344323364743181730751862328013767812969345563776509872800000

noncomputable def ep946 := nat_lit 12238941844608834428781025313402215194425321340895913358472555052761418400000

noncomputable def ep947 := BSN.cos_dyadic_bound_f 1162515810 1073741824 3 2 524288 169298 ep945 ep73 ep941 ep946 ep75 ep941 245872 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1162515810) qz292 0 2 ep945 ep73 ep941 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1162515810) qz293 0 2 ep946 ep75 ep941 rfl rfl rfl rfl) rfl rfl

noncomputable def ep948 := @Enclosure.Real.IsNear.sin_image qz208 qz481 Bool.false 67403115 262144 563 524288 Bool.true 245872 524288 1 84566 (@Enclosure.Real.IsNear.recentre' qz208 Bool.false 289494174883840075383 1125899906842624000 11344125003837309099 10570750000000000000000 67403115 262144 563 524288 (ep939 rfl) rfl) (Enclosure.sfrac_false_div 67403115 262144) (BSN.sin_reduce3 qz481 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 40902388830992617963520) qz19) 226375608064910080 72057594037927936 Bool.false 245872 524288 40 1000000000000000 169132 84566 (BSN.sin_reduce_arg_pos_rat_q3 67403115 262144 226375608064910080 72057594037927936 40 40902388830992617963520 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 245872 524288 40902388830992617963520 37778931862957161709568 1162515810 1073741824 169298 169132 (ep947 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep949 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz122 (Real.cos qz208)) (@HMul.hMul Real Real Real qz0 qz122 (@Neg.neg Real Real.instNeg (Real.sin qz208))) Bool.false 58882119381 274877906944 3079999390377 11622662539313152 Bool.false 1954052353 17179869184 383852009057 1452832817414144 (@Enclosure.Real.IsNear.mulLit_ff qz122 (Real.cos qz208) 127159 524288 1 524288 463059 524288 24067473 22168469504 58882119381 274877906944 3079999390377 11622662539313152 qz395 (@Enclosure.Real.IsNear.recentre' (Real.cos qz208) Bool.false 463059 524288 48134946 44336939008 463059 524288 24067473 22168469504 (ep944 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz122 (@Neg.neg Real Real.instNeg (Real.sin qz208)) 127159 524288 1 524288 15367 32768 24067473 22168469504 1954052353 17179869184 383852009057 1452832817414144 qz395 (@Enclosure.Real.IsNear.neg (Real.sin qz208) Bool.true 15367 32768 24067473 22168469504 (@Enclosure.Real.IsNear.recentre' (Real.sin qz208) Bool.true 245872 524288 48134946 44336939008 15367 32768 24067473 22168469504 (ep948 rfl rfl) rfl)) rfl)

noncomputable def ep950 := @ep937 58882119381 274877906944 3079999390377 11622662539313152 Bool.false 1954052353 17179869184 383852009057 1452832817414144 Bool.false 43718375657820443901952 1272372192989 274877906944 74879438805443 11622662539313152 Bool.true 680734352062449451008 39623954337 274877906944 74820456641989 11622662539313152 EMRow25.d12 (ep938 ep949) rfl rfl

noncomputable abbrev qz209 := (@HMul.hMul Real Real Real qz267 qz433 qz556)

noncomputable def ep951 := @Enclosure.Complex.IsNear.of_eq qz479 (Complex.mk (@HMul.hMul Real Real Real qz0 qz124 (Real.cos qz209)) (@HMul.hMul Real Real Real qz0 qz124 (@Neg.neg Real Real.instNeg (Real.sin qz209)))) Bool.true 849825275 274877906944 2974452823639 11622662539313152 Bool.false 32391602575 137438953472 1498164283967 5811331269656576 (BSN.cpow_neg_s_mk qz152 90753 1000 18 qz153 rfl)

noncomputable def ep952 := @Enclosure.Real.IsNear.mulLit_ff qz152 qz556 90753 1000 0 1 3254268794313975 1125899906842624 125000000042283 10570750000000000000 11813386235615046927 45035996273704960 11344125003837309099 10570750000000000000000 qz154 (BSN.isNear_log_sfrac 18 1 3254268794313975 1125899906842624 125000000042283 10570750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz397) Bool.false 27298785242132565196800 9444732965739290427392 1000000000338264 84566000000000000000 3254268794313975 1125899906842624 125000000042283 10570750000000000000 (BSN.log_rat_reduce_isNear 18 1 4 36 32 30876 262144 24973259072661432 36028797018963968 84566 1000000000000000 rfl rfl rfl rfl (ep453 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep953 := nat_lit 17536292812673165773860908202760344037644570618839561479552287385814394826881

noncomputable def ep954 := nat_lit 61237800050437782317904266851158115435837381986079053573819930383910531201

noncomputable def ep955 := nat_lit 52486402837918621756946916074578715882062037092546526331509222296675363418241

noncomputable def ep956 := BSN.cos_dyadic_bound_f 1672543599 1073741824 3 2 524288 169298 ep953 ep73 ep954 ep955 ep75 ep954 6877 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1672543599) qz292 0 2 ep953 ep73 ep954 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1672543599) qz293 0 2 ep955 ep75 ep954 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz482 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 34381479) (@Nat.cast Real Real.instNatCast 131072))

noncomputable def ep957 := @Enclosure.Real.IsNear.cos_image qz209 qz482 Bool.false 34381479 131072 563 524288 Bool.true 6877 524288 1 84566 (@Enclosure.Real.IsNear.recentre' qz209 Bool.false 11813386235615046927 45035996273704960 11344125003837309099 10570750000000000000000 34381479 131072 563 524288 (ep952 rfl) rfl) (Enclosure.sfrac_false_div 34381479 131072) (BSN.cos_reduce2 qz482 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 29423698163962665238528) qz302) 226375608064910080 72057594037927936 Bool.false 6877 524288 41 1000000000000000 169132 84566 (BSN.sin_reduce_arg_pos_rat_q2 34381479 131072 226375608064910080 72057594037927936 41 29423698163962665238528 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 6877 524288 29423698163962665238528 18889465931478580854784 1672543599 1073741824 169298 169132 (ep956 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep958 := nat_lit 31516336822771348167095311351487692775411557208322347420335061350158782263425

noncomputable def ep959 := nat_lit 82443640002414726885306351393280177462991294070009639061758023648841907925121

noncomputable def ep960 := BSN.sin_dyadic_bound_f 1672543599 1073741824 3 2 524288 169298 ep958 ep66 ep954 ep959 ep69 ep954 524242 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1672543599) qz287 0 2 ep958 ep66 ep954 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1672543599) qz288 0 2 ep959 ep69 ep954 rfl rfl rfl rfl) rfl rfl

noncomputable def ep961 := @Enclosure.Real.IsNear.sin_image qz209 qz482 Bool.false 34381479 131072 563 524288 Bool.true 524242 524288 1 84566 (@Enclosure.Real.IsNear.recentre' qz209 Bool.false 11813386235615046927 45035996273704960 11344125003837309099 10570750000000000000000 34381479 131072 563 524288 (ep952 rfl) rfl) (Enclosure.sfrac_false_div 34381479 131072) (BSN.sin_reduce2 qz482 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 29423698163962665238528) qz302) 226375608064910080 72057594037927936 Bool.false 524242 524288 41 1000000000000000 169132 84566 (BSN.sin_reduce_arg_pos_rat_q2 34381479 131072 226375608064910080 72057594037927936 41 29423698163962665238528 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 524242 524288 29423698163962665238528 18889465931478580854784 1672543599 1073741824 169298 169132 (ep960 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep962 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz124 (Real.cos qz209)) (@HMul.hMul Real Real Real qz0 qz124 (@Neg.neg Real Real.instNeg (Real.sin qz209))) Bool.true 849825275 274877906944 2974452823639 11622662539313152 Bool.false 32391602575 137438953472 1498164283967 5811331269656576 (@Enclosure.Real.IsNear.mulLit_ft qz124 (Real.cos qz209) 123575 524288 1 524288 6877 524288 24067473 22168469504 849825275 274877906944 2974452823639 11622662539313152 qz399 (@Enclosure.Real.IsNear.recentre' (Real.cos qz209) Bool.true 6877 524288 48134946 44336939008 6877 524288 24067473 22168469504 (ep957 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz124 (@Neg.neg Real Real.instNeg (Real.sin qz209)) 123575 524288 1 524288 262121 262144 24067473 22168469504 32391602575 137438953472 1498164283967 5811331269656576 qz399 (@Enclosure.Real.IsNear.neg (Real.sin qz209) Bool.true 262121 262144 24067473 22168469504 (@Enclosure.Real.IsNear.recentre' (Real.sin qz209) Bool.true 524242 524288 48134946 44336939008 262121 262144 24067473 22168469504 (ep961 rfl rfl) rfl)) rfl)

noncomputable def ep963 := @ep935 849825275 274877906944 2974452823639 11622662539313152 Bool.false 32391602575 137438953472 1498164283967 5811331269656576 Bool.false 349513407069703442006016 635761183857 137438953472 38926945814541 5811331269656576 Bool.false 3457861101878285172736 25159250813 274877906944 77816785209923 11622662539313152 (ep936 (BSN.head_sum_c_succ qz149 17 18 rfl rfl) (ep950 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep951 ep962) rfl rfl

noncomputable abbrev qz210 := (@HMul.hMul Real Real Real qz267 qz433 qz557)

noncomputable def ep964 := @Enclosure.Complex.IsNear.of_eq qz478 (Complex.mk (@HMul.hMul Real Real Real qz0 qz126 (Real.cos qz210)) (@HMul.hMul Real Real Real qz0 qz126 (@Neg.neg Real Real.instNeg (Real.sin qz210)))) Bool.true 484604091 2147483648 91303978193 363208204353536 Bool.false 5679454101 137438953472 1451957286817 5811331269656576 (BSN.cpow_neg_s_mk qz152 90753 1000 19 qz153 rfl)

noncomputable def ep965 := @Enclosure.Real.IsNear.mulLit_ff qz152 qz557 90753 1000 0 1 3315141365800183 1125899906842624 125000000042283 10570750000000000000 300859024370464007799 1125899906842624000 11344125003837309099 10570750000000000000000 qz154 (BSN.isNear_log_sfrac 19 1 3315141365800183 1125899906842624 125000000042283 10570750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz401) Bool.false 27809421382282341515264 9444732965739290427392 1000000000338264 84566000000000000000 3315141365800183 1125899906842624 125000000042283 10570750000000000000 (BSN.log_rat_reduce_isNear 19 1 4 38 32 45049 262144 24973259072661432 36028797018963968 84566 1000000000000000 rfl rfl rfl rfl (ep468 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep966 := nat_lit 1430303251610069739165401784810256

noncomputable def ep967 := BSN.cos_dyadic_bound_f 194471978 1073741824 2 1 524288 169298 ep966 ep228 ep966 ep966 ep229 ep966 515712 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 194471978) qz292 0 1 ep966 ep228 ep966 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 194471978) qz293 0 1 ep966 ep229 ep966 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz483 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 4378075) (@Nat.cast Real Real.instNatCast 16384))

noncomputable def ep968 := @Enclosure.Real.IsNear.cos_image qz210 qz483 Bool.false 4378075 16384 141 131072 Bool.true 515712 524288 1 84566 (@Enclosure.Real.IsNear.recentre' qz210 Bool.false 300859024370464007799 1125899906842624000 11344125003837309099 10570750000000000000000 4378075 16384 141 131072 (ep965 rfl) rfl) (Enclosure.sfrac_false_div 4378075 16384) (BSN.cos_reduce2 qz483 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 427648404169949184000) qz447) 226375608064910080 72057594037927936 Bool.false 515712 524288 42 1000000000000000 169132 84566 (BSN.sin_reduce_arg_pos_rat_q2 4378075 16384 226375608064910080 72057594037927936 42 427648404169949184000 2361183241434822606848 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 515712 524288 427648404169949184000 2361183241434822606848 194471978 1073741824 169298 169132 (ep967 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep969 := BSN.sin_dyadic_bound_f 194471978 1073741824 2 1 524288 169298 ep966 ep103 ep966 ep966 ep104 ep966 94438 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 194471978) qz287 0 1 ep966 ep103 ep966 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 194471978) qz288 0 1 ep966 ep104 ep966 rfl rfl rfl rfl) rfl rfl

noncomputable def ep970 := @Enclosure.Real.IsNear.sin_image qz210 qz483 Bool.false 4378075 16384 141 131072 Bool.true 94438 524288 1 84566 (@Enclosure.Real.IsNear.recentre' qz210 Bool.false 300859024370464007799 1125899906842624000 11344125003837309099 10570750000000000000000 4378075 16384 141 131072 (ep965 rfl) rfl) (Enclosure.sfrac_false_div 4378075 16384) (BSN.sin_reduce2 qz483 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 427648404169949184000) qz447) 226375608064910080 72057594037927936 Bool.false 94438 524288 42 1000000000000000 169132 84566 (BSN.sin_reduce_arg_pos_rat_q2 4378075 16384 226375608064910080 72057594037927936 42 427648404169949184000 2361183241434822606848 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 94438 524288 427648404169949184000 2361183241434822606848 194471978 1073741824 169298 169132 (ep969 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep971 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz126 (Real.cos qz210)) (@HMul.hMul Real Real Real qz0 qz126 (@Neg.neg Real Real.instNeg (Real.sin qz210))) Bool.true 484604091 2147483648 91303978193 363208204353536 Bool.false 5679454101 137438953472 1451957286817 5811331269656576 (@Enclosure.Real.IsNear.mulLit_ft qz126 (Real.cos qz210) 120279 524288 1 524288 4029 4096 6027439 5542117376 484604091 2147483648 91303978193 363208204353536 qz403 (@Enclosure.Real.IsNear.recentre' (Real.cos qz210) Bool.true 515712 524288 12054878 11084234752 4029 4096 6027439 5542117376 (ep968 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz126 (@Neg.neg Real Real.instNeg (Real.sin qz210)) 120279 524288 1 524288 47219 262144 6027439 5542117376 5679454101 137438953472 1451957286817 5811331269656576 qz403 (@Enclosure.Real.IsNear.neg (Real.sin qz210) Bool.true 47219 262144 6027439 5542117376 (@Enclosure.Real.IsNear.recentre' (Real.sin qz210) Bool.true 94438 524288 12054878 11084234752 47219 262144 6027439 5542117376 (ep970 rfl rfl) rfl)) rfl)

noncomputable def ep972 := @ep933 484604091 2147483648 91303978193 363208204353536 Bool.false 5679454101 137438953472 1451957286817 5811331269656576 Bool.false 1298683267250739216384 604746522033 137438953472 40387809465629 5811331269656576 Bool.false 5019017557745682350080 36518159015 274877906944 80720699783557 11622662539313152 (ep934 (BSN.head_sum_c_succ qz149 18 19 rfl rfl) (ep963 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep964 ep971) rfl rfl

noncomputable abbrev qz211 := (@HMul.hMul Real Real Real qz267 qz433 qz558)

noncomputable def ep973 := @Enclosure.Complex.IsNear.of_eq qz477 (Complex.mk (@HMul.hMul Real Real Real qz0 qz128 (Real.cos qz211)) (@HMul.hMul Real Real Real qz0 qz128 (@Neg.neg Real Real.instNeg (Real.sin qz211)))) Bool.true 236931935 8589934592 706077197701 2905665634828288 Bool.true 60995377505 274877906944 2843573390717 11622662539313152 (BSN.cpow_neg_s_mk qz152 90753 1000 20 qz153 rfl)

noncomputable def ep974 := @Enclosure.Real.IsNear.mulLit_ff qz152 qz558 90753 1000 0 1 3372891496062199 1125899906842624 125000000042283 10570750000000000000 306100021942132745847 1125899906842624000 11344125003837309099 10570750000000000000000 qz154 (BSN.isNear_log_sfrac 20 1 3372891496062199 1125899906842624 125000000042283 10570750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz405) Bool.false 28293864586999331028992 9444732965739290427392 1000000000338264 84566000000000000000 3372891496062199 1125899906842624 125000000042283 10570750000000000000 (BSN.log_rat_reduce_isNear 20 1 4 40 32 58495 262144 24973259072661432 36028797018963968 84566 1000000000000000 rfl rfl rfl rfl (ep483 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep975 := BSN.sin_dyadic_bound_f 132788279 1073741824 1 0 524288 169298 0 1 1 0 1 1 64672 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 132788279) qz287 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 132788279) qz288 0 0 rfl) rfl rfl

noncomputable abbrev qz484 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 71269465) qz16)

noncomputable def ep976 := @Enclosure.Real.IsNear.cos_image qz211 qz484 Bool.false 71269465 262144 563 524288 Bool.true 64672 524288 1 84566 (@Enclosure.Real.IsNear.recentre' qz211 Bool.false 306100021942132745847 1125899906842624000 11344125003837309099 10570750000000000000000 71269465 262144 563 524288 (ep974 rfl) rfl) (Enclosure.sfrac_false_div 71269465 262144) (BSN.cos_reduce1 qz484 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 4672072242400088555520) qz19) 226375608064910080 72057594037927936 Bool.false 64672 524288 43 1000000000000000 169132 84566 (BSN.sin_reduce_arg_pos_rat_q1 71269465 262144 226375608064910080 72057594037927936 43 4672072242400088555520 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 64672 524288 4672072242400088555520 37778931862957161709568 132788279 1073741824 169298 169132 (ep975 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep977 := nat_lit 310913062859453685403408873349281

noncomputable def ep978 := BSN.cos_dyadic_bound_f 132788279 1073741824 2 1 524288 169298 ep977 ep228 ep977 ep977 ep229 ep977 520283 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 132788279) qz292 0 1 ep977 ep228 ep977 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 132788279) qz293 0 1 ep977 ep229 ep977 rfl rfl rfl rfl) rfl rfl

noncomputable def ep979 := @Enclosure.Real.IsNear.sin_image qz211 qz484 Bool.false 71269465 262144 563 524288 Bool.false 520283 524288 1 84566 (@Enclosure.Real.IsNear.recentre' qz211 Bool.false 306100021942132745847 1125899906842624000 11344125003837309099 10570750000000000000000 71269465 262144 563 524288 (ep974 rfl) rfl) (Enclosure.sfrac_false_div 71269465 262144) (BSN.sin_reduce1 qz484 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 4672072242400088555520) qz19) 226375608064910080 72057594037927936 Bool.false 520283 524288 43 1000000000000000 169132 84566 (BSN.sin_reduce_arg_pos_rat_q1 71269465 262144 226375608064910080 72057594037927936 43 4672072242400088555520 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 520283 524288 4672072242400088555520 37778931862957161709568 132788279 1073741824 169298 169132 (ep978 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep980 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz128 (Real.cos qz211)) (@HMul.hMul Real Real Real qz0 qz128 (@Neg.neg Real Real.instNeg (Real.sin qz211))) Bool.true 236931935 8589934592 706077197701 2905665634828288 Bool.true 60995377505 274877906944 2843573390717 11622662539313152 (@Enclosure.Real.IsNear.mulLit_ft qz128 (Real.cos qz211) 117235 524288 1 524288 2021 16384 24067473 22168469504 236931935 8589934592 706077197701 2905665634828288 qz407 (@Enclosure.Real.IsNear.recentre' (Real.cos qz211) Bool.true 64672 524288 48134946 44336939008 2021 16384 24067473 22168469504 (ep976 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz128 (@Neg.neg Real Real.instNeg (Real.sin qz211)) 117235 524288 1 524288 520283 524288 24067473 22168469504 60995377505 274877906944 2843573390717 11622662539313152 qz407 (@Enclosure.Real.IsNear.neg (Real.sin qz211) Bool.false 520283 524288 24067473 22168469504 (@Enclosure.Real.IsNear.recentre' (Real.sin qz211) Bool.false 520283 524288 48134946 44336939008 520283 524288 24067473 22168469504 (ep979 rfl rfl) rfl)) rfl)

noncomputable def ep981 := @ep931 236931935 8589934592 706077197701 2905665634828288 Bool.true 60995377505 274877906944 2843573390717 11622662539313152 Bool.false 5162169391812460937216 600955611073 137438953472 41799963861031 5811331269656576 Bool.true 6728246586342176194560 12238609245 137438953472 41782136587137 5811331269656576 (ep932 (BSN.head_sum_c_succ qz149 19 20 rfl rfl) (ep972 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep973 ep980) rfl rfl

noncomputable abbrev qz212 := (@HMul.hMul Real Real Real qz267 qz433 qz559)

noncomputable def ep982 := @Enclosure.Complex.IsNear.of_eq qz476 (Complex.mk (@HMul.hMul Real Real Real qz0 qz130 (Real.cos qz212)) (@HMul.hMul Real Real Real qz0 qz130 (@Neg.neg Real Real.instNeg (Real.sin qz212)))) Bool.false 59208602453 274877906944 2775441757241 11622662539313152 Bool.false 9608639865 274877906944 2757110723685 11622662539313152 (BSN.cpow_neg_s_mk qz152 90753 1000 21 qz153 rfl)

noncomputable def ep983 := @Enclosure.Real.IsNear.mulLit_ff qz152 qz559 90753 1000 0 1 3427824127778039 1125899906842624 125000000042283 10570750000000000000 311085323068240373367 1125899906842624000 11344125003837309099 10570750000000000000000 qz154 (BSN.isNear_log_sfrac 21 1 3427824127778039 1125899906842624 125000000042283 10570750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz409) Bool.false 28754672900871880179712 9444732965739290427392 1000000000338264 84566000000000000000 3427824127778039 1125899906842624 125000000042283 10570750000000000000 (BSN.log_rat_reduce_isNear 21 1 4 42 32 71285 262144 24973259072661432 36028797018963968 84566 1000000000000000 rfl rfl rfl rfl (ep497 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep984 := nat_lit 21140618365435802767221096932786252757830605274615826747330719447309793297505

noncomputable def ep985 := nat_lit 27589165453671644750700529881932024632834546037940816016175923263361188961

noncomputable def ep986 := nat_lit 55323618022549729346458881585107533944912710263741927778982837533861159568481

noncomputable def ep987 := BSN.sin_dyadic_bound_f 1513883029 1073741824 3 2 524288 169298 ep984 ep66 ep985 ep986 ep69 ep985 517517 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1513883029) qz287 0 2 ep984 ep66 ep985 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1513883029) qz288 0 2 ep986 ep69 ep985 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz485 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 18107549) (@Nat.cast Real Real.instNatCast 65536))

noncomputable def ep988 := @Enclosure.Real.IsNear.cos_image qz212 qz485 Bool.false 18107549 65536 563 524288 Bool.false 517517 524288 1 84566 (@Enclosure.Real.IsNear.recentre' qz212 Bool.false 311085323068240373367 1125899906842624000 11344125003837309099 10570750000000000000000 18107549 65536 563 524288 (ep983 rfl) rfl) (Enclosure.sfrac_false_div 18107549 65536) (BSN.cos_reduce3 qz485 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 13316255952935193673728) qz454) 226375608064910080 72057594037927936 Bool.false 517517 524288 43 1000000000000000 169132 84566 (BSN.sin_reduce_arg_pos_rat_q3 18107549 65536 226375608064910080 72057594037927936 43 13316255952935193673728 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 517517 524288 13316255952935193673728 9444732965739290427392 1513883029 1073741824 169298 169132 (ep987 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep989 := nat_lit 11757049832110411157234254087050999098631596061914544111190922325511379027041

noncomputable def ep990 := nat_lit 35215971165423890182201361201389133246629119093667750701540415130007414703201

noncomputable def ep991 := BSN.cos_dyadic_bound_f 1513883029 1073741824 3 2 524288 169298 ep989 ep73 ep985 ep990 ep75 ep985 83985 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1513883029) qz292 0 2 ep989 ep73 ep985 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1513883029) qz293 0 2 ep990 ep75 ep985 rfl rfl rfl rfl) rfl rfl

noncomputable def ep992 := @Enclosure.Real.IsNear.sin_image qz212 qz485 Bool.false 18107549 65536 563 524288 Bool.true 83985 524288 1 84566 (@Enclosure.Real.IsNear.recentre' qz212 Bool.false 311085323068240373367 1125899906842624000 11344125003837309099 10570750000000000000000 18107549 65536 563 524288 (ep983 rfl) rfl) (Enclosure.sfrac_false_div 18107549 65536) (BSN.sin_reduce3 qz485 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 13316255952935193673728) qz454) 226375608064910080 72057594037927936 Bool.false 83985 524288 43 1000000000000000 169132 84566 (BSN.sin_reduce_arg_pos_rat_q3 18107549 65536 226375608064910080 72057594037927936 43 13316255952935193673728 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 83985 524288 13316255952935193673728 9444732965739290427392 1513883029 1073741824 169298 169132 (ep991 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep993 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz130 (Real.cos qz212)) (@HMul.hMul Real Real Real qz0 qz130 (@Neg.neg Real Real.instNeg (Real.sin qz212))) Bool.false 59208602453 274877906944 2775441757241 11622662539313152 Bool.false 9608639865 274877906944 2757110723685 11622662539313152 (@Enclosure.Real.IsNear.mulLit_ff qz130 (Real.cos qz212) 114409 524288 1 524288 517517 524288 24067473 22168469504 59208602453 274877906944 2775441757241 11622662539313152 qz411 (@Enclosure.Real.IsNear.recentre' (Real.cos qz212) Bool.false 517517 524288 48134946 44336939008 517517 524288 24067473 22168469504 (ep988 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz130 (@Neg.neg Real Real.instNeg (Real.sin qz212)) 114409 524288 1 524288 83985 524288 24067473 22168469504 9608639865 274877906944 2757110723685 11622662539313152 qz411 (@Enclosure.Real.IsNear.neg (Real.sin qz212) Bool.true 83985 524288 24067473 22168469504 (@Enclosure.Real.IsNear.recentre' (Real.sin qz212) Bool.true 83985 524288 48134946 44336939008 83985 524288 24067473 22168469504 (ep992 rfl rfl) rfl)) rfl)

noncomputable def ep994 := @ep929 59208602453 274877906944 2775441757241 11622662539313152 Bool.false 9608639865 274877906944 2757110723685 11622662539313152 Bool.false 173326988895678762057728 1261119824599 274877906944 86375369479303 11622662539313152 Bool.true 2043521885836148736000 14868578625 274877906944 86321383897959 11622662539313152 (ep930 (BSN.head_sum_c_succ qz149 20 21 rfl rfl) (ep981 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep982 ep993) rfl rfl

noncomputable abbrev qz213 := (@HMul.hMul Real Real Real qz267 qz433 qz560)

noncomputable def ep995 := @Enclosure.Complex.IsNear.of_eq qz475 (Complex.mk (@HMul.hMul Real Real Real qz0 qz132 (Real.cos qz213)) (@HMul.hMul Real Real Real qz0 qz132 (@Neg.neg Real Real.instNeg (Real.sin qz213)))) Bool.true 35532867415 274877906944 2708429657135 11622662539313152 Bool.false 11650836949 68719476736 678154330793 2905665634828288 (BSN.cpow_neg_s_mk qz152 90753 1000 22 qz153 rfl)

noncomputable def ep996 := @Enclosure.Real.IsNear.mulLit_ff qz152 qz560 90753 1000 0 1 3480201253952759 1125899906842624 125000000042283 10570750000000000000 315838704399974737527 1125899906842624000 11344125003837309099 10570750000000000000000 qz154 (BSN.isNear_log_sfrac 22 1 3480201253952759 1125899906842624 125000000042283 10570750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz413) Bool.false 29194044080518145769472 9444732965739290427392 1000000000338264 84566000000000000000 3480201253952759 1125899906842624 125000000042283 10570750000000000000 (BSN.log_rat_reduce_isNear 22 1 4 44 32 83480 262144 24973259072661432 36028797018963968 84566 1000000000000000 rfl rfl rfl rfl (ep508 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep997 := nat_lit 2121590571654834392863758550176746085419400171865717828241562667371440800000

noncomputable def ep998 := nat_lit 901854193185400735740865987934129651027762308226210984737003536100000000

noncomputable def ep999 := nat_lit 6362968006578132377119793918554369996956144990980701062755213995042122400000

noncomputable def ep1000 := BSN.cos_dyadic_bound_f 987170210 1073741824 3 2 524288 169298 ep997 ep73 ep998 ep999 ep75 ep998 317885 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 987170210) qz292 0 2 ep997 ep73 ep998 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 987170210) qz293 0 2 ep999 ep75 ep998 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz486 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 147073857) qz23)

noncomputable def ep1001 := @Enclosure.Real.IsNear.cos_image qz213 qz486 Bool.false 147073857 524288 141 131072 Bool.true 317885 524288 1 84566 (@Enclosure.Real.IsNear.recentre' qz213 Bool.false 315838704399974737527 1125899906842624000 11344125003837309099 10570750000000000000000 147073857 524288 141 131072 (ep996 rfl) rfl) (Enclosure.sfrac_false_div 147073857 524288) (BSN.cos_reduce2 qz486 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 69465927994399139037184) qz25) 226375608064910080 72057594037927936 Bool.false 317885 524288 44 1000000000000000 169132 84566 (BSN.sin_reduce_arg_pos_rat_q2 147073857 524288 226375608064910080 72057594037927936 44 69465927994399139037184 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 317885 524288 69465927994399139037184 75557863725914323419136 987170210 1073741824 169298 169132 (ep1000 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1002 := nat_lit 949660040849040218129003667424810000

noncomputable def ep1003 := BSN.sin_dyadic_bound_f 987170210 1073741824 2 1 524288 169298 ep1002 ep103 ep1002 ep1002 ep104 ep1002 416924 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 987170210) qz287 0 1 ep1002 ep103 ep1002 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 987170210) qz288 0 1 ep1002 ep104 ep1002 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1004 := @Enclosure.Real.IsNear.sin_image qz213 qz486 Bool.false 147073857 524288 141 131072 Bool.true 416924 524288 1 84566 (@Enclosure.Real.IsNear.recentre' qz213 Bool.false 315838704399974737527 1125899906842624000 11344125003837309099 10570750000000000000000 147073857 524288 141 131072 (ep996 rfl) rfl) (Enclosure.sfrac_false_div 147073857 524288) (BSN.sin_reduce2 qz486 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 69465927994399139037184) qz25) 226375608064910080 72057594037927936 Bool.false 416924 524288 44 1000000000000000 169132 84566 (BSN.sin_reduce_arg_pos_rat_q2 147073857 524288 226375608064910080 72057594037927936 44 69465927994399139037184 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 416924 524288 69465927994399139037184 75557863725914323419136 987170210 1073741824 169298 169132 (ep1003 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1005 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz132 (Real.cos qz213)) (@HMul.hMul Real Real Real qz0 qz132 (@Neg.neg Real Real.instNeg (Real.sin qz213))) Bool.true 35532867415 274877906944 2708429657135 11622662539313152 Bool.false 11650836949 68719476736 678154330793 2905665634828288 (@Enclosure.Real.IsNear.mulLit_ft qz132 (Real.cos qz213) 111779 524288 1 524288 317885 524288 6027439 5542117376 35532867415 274877906944 2708429657135 11622662539313152 qz415 (@Enclosure.Real.IsNear.recentre' (Real.cos qz213) Bool.true 317885 524288 12054878 11084234752 317885 524288 6027439 5542117376 (ep1001 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz132 (@Neg.neg Real Real.instNeg (Real.sin qz213)) 111779 524288 1 524288 104231 131072 6027439 5542117376 11650836949 68719476736 678154330793 2905665634828288 qz415 (@Enclosure.Real.IsNear.neg (Real.sin qz213) Bool.true 104231 131072 6027439 5542117376 (@Enclosure.Real.IsNear.recentre' (Real.sin qz213) Bool.true 416924 524288 12054878 11084234752 104231 131072 6027439 5542117376 (ep1004 rfl rfl) rfl)) rfl)

noncomputable def ep1006 := @ep927 35532867415 274877906944 2708429657135 11622662539313152 Bool.false 11650836949 68719476736 678154330793 2905665634828288 Bool.false 336886777568603664285696 9574898103 2147483648 44541899568219 5811331269656576 Bool.false 2180796731768864505856 31734769171 274877906944 89034001221131 11622662539313152 (ep928 (BSN.head_sum_c_succ qz149 21 22 rfl rfl) (ep994 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep995 ep1005) rfl rfl

noncomputable def ep1007 := @Enclosure.Complex.IsNear.mul qz206 (@HAdd.hAdd Complex Complex Complex qz4 qz207 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1))))) Bool.true ep918 ep803 ep919 ep805 Bool.true

noncomputable def ep1008 := nat_lit 1999377689759125306280941

noncomputable abbrev qz214 := (Complex.re qz474)

noncomputable abbrev qz215 := (Complex.im qz474)

noncomputable def ep1009 := @Enclosure.Real.IsNear.subLit_tt_n (@HMul.hMul Real Real Real qz0 qz214 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz207 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz215 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz207 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1))))))) 451424457961944849195 18111940603819713363968 ep1008

noncomputable def ep1010 := nat_lit 17614025244680105623879155712

noncomputable def ep1011 := nat_lit 3179361540865477808269429

noncomputable def ep1012 := nat_lit 151530719288787152237144221

noncomputable def ep1013 := nat_lit 36441581765535666925419220564730852554181705728

noncomputable def ep1014 := @Enclosure.Real.IsNear.mulLit_tf qz214 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz207 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))))) 13690815435 274877906944 2636399594811 11622662539313152 2275122891493

noncomputable abbrev qz487 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) qz563 (Real.log (Enclosure.sfrac Bool.false 23 1)))

noncomputable abbrev qz216 := (Real.cos qz487)

noncomputable abbrev qz217 := (Real.sin qz487)

noncomputable abbrev qz488 := (@Neg.neg Real Real.instNeg qz217)

noncomputable def ep1015 := @Enclosure.Complex.IsNear.of_eq qz206 (Complex.mk (@HMul.hMul Real Real Real qz0 qz136 qz216) (@HMul.hMul Real Real Real qz0 qz136 qz488)) Bool.true 13690815435 274877906944 2636399594811 11622662539313152 Bool.true 55656523631 274877906944 2652631023719 11622662539313152 (BSN.cpow_neg_s_mk qz152 90753 1000 23 qz153 rfl)

noncomputable def ep1016 := @Enclosure.Real.IsNear.mulLit_ff qz152 qz139 90753 1000 0 1 3530250507853047 1125899906842624 125000000042283 10570750000000000000 320380824339187574391 1125899906842624000 11344125003837309099 10570750000000000000000 qz154 (BSN.isNear_log_sfrac 23 1 3530250507853047 1125899906842624 125000000042283 10570750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' qz421 Bool.false 29613887652180132888576 9444732965739290427392 1000000000338264 84566000000000000000 3530250507853047 1125899906842624 125000000042283 10570750000000000000 (BSN.log_rat_reduce_isNear 23 1 4 46 32 95133 262144 24973259072661432 36028797018963968 84566 1000000000000000 rfl rfl rfl rfl (ep529 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1017 := nat_lit 4498845381059647588631530090340161

noncomputable def ep1018 := BSN.sin_dyadic_bound_f 258985391 1073741824 2 1 524288 169298 ep1017 ep103 ep1017 ep1017 ep104 ep1017 125235 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 258985391) qz287 0 1 ep1017 ep103 ep1017 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 258985391) qz288 0 1 ep1017 ep104 ep1017 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz218 := qz487

noncomputable abbrev qz489 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 149188947) qz23)

noncomputable def ep1019 := @Enclosure.Real.IsNear.cos_image qz218 qz489 Bool.false 149188947 524288 563 524288 Bool.true 125235 524288 1 84566 (@Enclosure.Real.IsNear.recentre' qz218 Bool.false 320380824339187574391 1125899906842624000 11344125003837309099 10570750000000000000000 149188947 524288 563 524288 (ep1016 rfl) rfl) (Enclosure.sfrac_false_div 149188947 524288) (BSN.cos_reduce1 qz489 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 18224476738354407276544) qz25) 226375608064910080 72057594037927936 Bool.false 125235 524288 45 1000000000000000 169132 84566 (BSN.sin_reduce_arg_pos_rat_q1 149188947 524288 226375608064910080 72057594037927936 45 18224476738354407276544 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 125235 524288 18224476738354407276544 75557863725914323419136 258985391 1073741824 169298 169132 (ep1018 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1020 := BSN.cos_dyadic_bound_f 258985391 1073741824 2 1 524288 169298 ep1017 ep228 ep1017 ep1017 ep229 ep1017 509111 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 258985391) qz292 0 1 ep1017 ep228 ep1017 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 258985391) qz293 0 1 ep1017 ep229 ep1017 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1021 := @Enclosure.Real.IsNear.sin_image qz218 qz489 Bool.false 149188947 524288 563 524288 Bool.false 509111 524288 1 84566 (@Enclosure.Real.IsNear.recentre' qz218 Bool.false 320380824339187574391 1125899906842624000 11344125003837309099 10570750000000000000000 149188947 524288 563 524288 (ep1016 rfl) rfl) (Enclosure.sfrac_false_div 149188947 524288) (BSN.sin_reduce1 qz489 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 18224476738354407276544) qz25) 226375608064910080 72057594037927936 Bool.false 509111 524288 45 1000000000000000 169132 84566 (BSN.sin_reduce_arg_pos_rat_q1 149188947 524288 226375608064910080 72057594037927936 45 18224476738354407276544 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 509111 524288 18224476738354407276544 75557863725914323419136 258985391 1073741824 169298 169132 (ep1020 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1022 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz136 qz216) (@HMul.hMul Real Real Real qz0 qz136 qz488) Bool.true 13690815435 274877906944 2636399594811 11622662539313152 Bool.true 55656523631 274877906944 2652631023719 11622662539313152 (@Enclosure.Real.IsNear.mulLit_ft qz136 qz216 109321 524288 1 524288 125235 524288 24067473 22168469504 13690815435 274877906944 2636399594811 11622662539313152 qz423 (@Enclosure.Real.IsNear.recentre' qz216 Bool.true 125235 524288 48134946 44336939008 125235 524288 24067473 22168469504 (ep1019 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz136 qz488 109321 524288 1 524288 509111 524288 24067473 22168469504 55656523631 274877906944 2652631023719 11622662539313152 qz423 (@Enclosure.Real.IsNear.neg qz217 Bool.false 509111 524288 24067473 22168469504 (@Enclosure.Real.IsNear.recentre' qz217 Bool.false 509111 524288 48134946 44336939008 509111 524288 24067473 22168469504 (ep1021 rfl rfl) rfl)) rfl)

noncomputable def ep1023 := @ep1014 4546469068968 0 1 451424457961944849195 18111940603819713363968 ep1008 ep1010 (@Enclosure.Complex.IsNear.re_isNear qz206 Bool.true 13690815435 274877906944 2636399594811 11622662539313152 Bool.true 55656523631 274877906944 2652631023719 11622662539313152 (ep1015 ep1022))

noncomputable def ep1024 := @Enclosure.Complex.IsNear.re_isNear (@HAdd.hAdd Complex Complex Complex qz4 qz207 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1))))) Bool.false 2275122891493 4546469068968 0 1 Bool.false

noncomputable def ep1025 := @Enclosure.Complex.IsNear.addLitP qz207 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) Bool.false 8213357009 16472714018 0 1 Bool.true 2087319000

noncomputable def ep1026 := @ep1025 8236357009 0 1 Bool.false 1 552 0 1 Bool.false 30251 92000 0 1 Bool.false 4550245782986 2275122891493 4546469068968 0 1 Bool.false 57124687879259 57124687879259 757744844828000 0 1

noncomputable abbrev qz219 := (@HDiv.hDiv Complex Complex Complex qz362 qz390 (@HSub.hSub Complex Complex Complex qz354 qz426 (1 : Complex)))

noncomputable def ep1027 := @Enclosure.Complex.IsNear.addLitP qz219 qz89 Bool.true 46000000 32945428036 0 1 Bool.true 8349276000 32945428036 0 1

noncomputable def ep1028 := @Enclosure.Complex.IsNear.of_eq qz219 (Complex.mk (Enclosure.sfrac Bool.true 46000000 32945428036) (Enclosure.sfrac Bool.true 8349276000 32945428036)) Bool.true 46000000 32945428036 0 1 Bool.true 8349276000 32945428036 0 1

noncomputable def ep1029 := @ep1027 Bool.false 1 2 0 1 Bool.false 0 1 0 1 Bool.false 32853428036 8213357009 16472714018 0 1 Bool.true 8349276000 2087319000 8236357009 0 1 (ep1028 (BSN.N_div_s_sub_one_mk qz152 90753 1000 23 qz153 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 46000000 32945428036) (Enclosure.sfrac Bool.true 8349276000 32945428036) Bool.true 46000000 32945428036 0 1 Bool.true 8349276000 32945428036 0 1 (Enclosure.Real.IsNear.const Bool.true 46000000 32945428036) (Enclosure.Real.IsNear.const Bool.true 8349276000 32945428036))) qz90 rfl

noncomputable def ep1030 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@HAdd.hAdd Complex Complex Complex qz4 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz142) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 1))) qz143)) Bool.false 1 552 0 1

noncomputable def ep1031 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz142) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 1))) qz143) Bool.false 0 1 0 1 Bool.false

noncomputable def ep1032 := @ep1031 0 1 0 1 Bool.false 1 552 0 1 Bool.false 30251 92000 0 1 Bool.false 1 1 552 0 1 Bool.false 30251 30251 92000 0

noncomputable def ep1033 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (Complex.mk qz10 qz10) Bool.false 0 1 0 1 Bool.false

noncomputable def ep1034 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz142) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 1))) qz143 Bool.false 1 552 0 1 Bool.false 30251 92000 0 1

noncomputable def ep1035 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz142) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 1)))) qz144) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz142) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 1)))) qz145) 1 552 0 1 0 1 0

noncomputable def ep1036 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz142) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 1)))) qz144 1 24 0 1 1 23 0 1 1

noncomputable def ep1037 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz142)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz142)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 1)))) 1 24 0 1 0 1 0 1 1

noncomputable def ep1038 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz142)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 1 2 0 1 1 24 0

noncomputable def ep1039 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 1)) qz149 Bool.false 1 2 0 1 Bool.false 90753 1000 0 1 (BSN.ascPochhammer_one_eval qz149)

noncomputable def ep1040 := ep1039 (@Enclosure.Complex.IsNear.of_eq qz149 (Complex.mk qz84 qz152) Bool.false 1 2 0 1 Bool.false 90753 1000 0 1 (BSN.s_crit_mk qz152 Bool.false 90753 1000 qz153) (@Enclosure.Complex.IsNear.mk qz84 qz152 Bool.false 1 2 0 1 Bool.false 90753 1000 0 1 qz371 qz154))

noncomputable def ep1041 := @ep1038 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz142) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep553) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 90753 1000 0 1 ep1040)

noncomputable def ep1042 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz142)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 90753 1000 0 1 0 1 0

noncomputable def ep1043 := @ep1042 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz142) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep553) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 90753 1000 0 1 ep1040)

noncomputable def ep1044 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz142)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz142)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 1)))) 30251 4000 0 1 0 1 0 1 30251

noncomputable def ep1045 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz142)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 90753 1000 0 1 30251 4000 0

noncomputable def ep1046 := @ep1045 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz142) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep553) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 90753 1000 0 1 ep1040)

noncomputable def ep1047 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz142)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 1 2 0 1 0 1 0

noncomputable def ep1048 := @ep1047 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz142) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep553) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 90753 1000 0 1 ep1040)

noncomputable def ep1049 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz142) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 24 0 1 Bool.false 30251 4000 0 1 (@ep1037 1 24 0 1 (ep1041 rfl) (ep1043 rfl) rfl rfl) (@ep1044 30251 4000 0 1 (ep1046 rfl) (ep1048 rfl) rfl rfl)

noncomputable def ep1050 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz142) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 30251 4000 0 1 ep1049

noncomputable def ep1051 := @ep1036 552 0 1 ep1050 qz146

noncomputable def ep1052 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz142) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 1)))) qz145 30251 4000 0 1 0 1 0 1 0

noncomputable def ep1053 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz142) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 30251 4000 0 1 ep1049

noncomputable def ep1054 := @ep1052 1 0 1 ep1053 qz147

noncomputable def ep1055 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz142) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 1)))) qz145) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz142) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 1)))) qz144) 0 1 0 1 30251 92000 0

noncomputable def ep1056 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz142) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 1)))) qz145 1 24 0 1 0 1 0 1 0

noncomputable def ep1057 := @ep1056 1 0 1 ep1050 qz147

noncomputable def ep1058 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz142) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 1)))) qz144 30251 4000 0 1 1 23 0 1 30251

noncomputable def ep1059 := @ep1058 92000 0 1 ep1053 qz146

noncomputable def ep1060 := @ep1032 1 (@ep1033 0 1 0 1 (BSN.bern_sum_base qz149 23) qz105) (ep1034 (@ep1035 1 1 1 552 0 1 (ep1051 rfl) (ep1054 rfl) rfl rfl) (@ep1055 1 30251 30251 92000 0 1 (ep1057 rfl) (ep1059 rfl) rfl rfl)) rfl rfl rfl rfl rfl

noncomputable def ep1061 := ep1026 (ep1029 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep1030 Bool.false 30251 92000 0 1 (BSN.bern_sum_succ qz149 23 0 1 1 rfl rfl) (ep1060 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl rfl

noncomputable def ep1062 := @Enclosure.Real.IsNear.mulLit_tf qz215 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz207 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))))) 55656523631 274877906944 2652631023719 11622662539313152 57124687879259

noncomputable def ep1063 := @ep1062 757744844828000 0 1 ep1011 ep803 ep1012 ep805 (@Enclosure.Complex.IsNear.im_isNear qz206 Bool.true 13690815435 274877906944 2636399594811 11622662539313152 Bool.true 55656523631 274877906944 2652631023719 11622662539313152 (ep1015 ep1022))

noncomputable def ep1064 := @Enclosure.Complex.IsNear.im_isNear (@HAdd.hAdd Complex Complex Complex qz4 qz207 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1))))) Bool.false 2275122891493 4546469068968 0 1 Bool.false

noncomputable def ep1065 := nat_lit 1811194060381971336396800

noncomputable def ep1066 := nat_lit 150603503978583270490925049

noncomputable def ep1067 := @Enclosure.Real.IsNear.addLit_tt (@HMul.hMul Real Real Real qz0 qz214 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz207 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz215 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz207 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1))))))) 6800726595973187248371 ep1065 ep1066

noncomputable def ep1068 := nat_lit 1249723901663560222113792

noncomputable def ep1069 := nat_lit 6035061564747607946322467

noncomputable def ep1070 := nat_lit 52842075734040316871637467136

noncomputable def ep1071 := nat_lit 237842259048737283919920961530792379996262367232

noncomputable def ep1072 := @Enclosure.Real.IsNear.mulLit_tf qz214 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz207 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))))) 13690815435 274877906944 2636399594811 11622662539313152 57124687879259

noncomputable def ep1073 := @ep1072 757744844828000 0 1 6800726595973187248371 ep1065 ep1066 ep805 (@Enclosure.Complex.IsNear.re_isNear qz206 Bool.true 13690815435 274877906944 2636399594811 11622662539313152 Bool.true 55656523631 274877906944 2652631023719 11622662539313152 (ep1015 ep1022))

noncomputable def ep1074 := @Enclosure.Real.IsNear.mulLit_tf qz215 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz207 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))))) 55656523631 274877906944 2652631023719 11622662539313152 2275122891493

noncomputable def ep1075 := @ep1074 4546469068968 0 1 126625430973809203371083 ep1068 ep1069 ep1070 (@Enclosure.Complex.IsNear.im_isNear qz206 Bool.true 13690815435 274877906944 2636399594811 11622662539313152 Bool.true 55656523631 274877906944 2652631023719 11622662539313152 (ep1015 ep1022))

noncomputable abbrev qz490 := (ep1061 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable def ep1076 := @ep1007 ep920 ep913 ep921 ep915 (@ep1009 ep1010 ep1011 ep803 ep1012 ep805 ep1013 ep918 ep803 ep919 ep805 (ep1023 (@ep1024 57124687879259 757744844828000 0 1 qz490) rfl) (ep1063 (@ep1064 57124687879259 757744844828000 0 1 qz490) rfl) rfl rfl) (@ep1067 ep805 126625430973809203371083 ep1068 ep1069 ep1070 ep1071 ep920 ep913 ep921 ep915 (ep1073 (@ep1064 57124687879259 757744844828000 0 1 qz490) rfl) (ep1075 (@ep1024 57124687879259 757744844828000 0 1 qz490) rfl) rfl rfl)

noncomputable def ep1077 := @ep924 ep914 ep915 (@ep925 11622662539313152 (BSN.head_sum_c_eq qz149 23) (ep926 (BSN.head_sum_c_succ qz149 22 23 rfl rfl) (ep1006 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))) ep1076 rfl rfl rfl

noncomputable def ep1078 := @Enclosure.Complex.IsNear.re_isNear (zetaApproximant qz149 1 23) Bool.false ep802 ep803 ep804 ep805 Bool.false ep912 ep913 ep914 ep915 (@ep916 ep805 Bool.false ep912 ep913 ep914 ep915 (BSN.zetaApproximant_eq_folded' qz149 1 23 rfl) (ep1077 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

noncomputable def ep1079 := @Enclosure.Real.IsNear.mulLit_ff (Real.sin (@HSub.hSub Real Real Real qz357 (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz176 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz177 (@Nat.cast Complex Complex.instNatCast j))))) qz178)) (Complex.im (zetaApproximant qz149 1 23)) 11 262144 1428107

noncomputable def ep1080 := @Enclosure.Real.IsNear.recentre' (Real.sin (@HSub.hSub Real Real Real qz357 (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz176 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz177 (@Nat.cast Complex Complex.instNatCast j))))) qz178)) Bool.false 22 524288 2856214

noncomputable def ep1081 := @Enclosure.Real.IsNear.sin_image (@HSub.hSub Real Real Real qz357 (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz176 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz177 (@Nat.cast Complex Complex.instNatCast j))))) qz178) qz457 Bool.false 19765203 262144 33

noncomputable def ep1082 := BSN.sin_dyadic_bound_f 45260 1073741824 1 0 524288 169298 0 1 1 0 1 1 22 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 45260) qz287 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 45260) qz288 0 0 rfl) rfl rfl

noncomputable def ep1083 := @ep1081 65536 Bool.false 22 524288 1 84566 (@ep810 19765203 262144 33 65536 ep909 rfl) (Enclosure.sfrac_false_div 19765203 262144) (BSN.sin_reduce0 qz457 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 1592475216884269056) qz19) 226375608064910080 72057594037927936 Bool.false 22 524288 12 1000000000000000 169132 84566 (BSN.sin_reduce_arg_pos_rat_q0 19765203 262144 226375608064910080 72057594037927936 12 1592475216884269056 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 22 524288 1592475216884269056 37778931862957161709568 45260 1073741824 169298 169132 (ep1082 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1084 := @Enclosure.Complex.IsNear.im_isNear (zetaApproximant qz149 1 23) Bool.false ep802 ep803 ep804 ep805 Bool.false ep912 ep913 ep914 ep915 (@ep916 ep805 Bool.false ep912 ep913 ep914 ep915 (BSN.zetaApproximant_eq_folded' qz149 1 23 rfl) (ep1077 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

theorem EMRow25.d13 : Enclosure.Real.IsNear (hardyZApproximantEM 1 23 qz152) Bool.false ep785 ep786 ep787 ep788 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantEM 1 23 qz152) ep789 Bool.false ep785 ep786 ep787 ep788 (@Eq.refl Real ep789) (@ep790 Bool.false ep785 ep786 ep787 ep788 (BSN.re_exp_mul (@HSub.hSub Real Real Real qz357 (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz176 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz177 (@Nat.cast Complex Complex.instNatCast j))))) qz178) (zetaApproximant qz149 1 23)) (@ep792 ep793 ep794 ep795 ep796 ep797 ep798 ep799 ep800 ep785 ep786 ep787 ep788 (@ep801 2771058688 ep802 ep803 ep804 ep805 ep791 ep793 ep794 ep795 (@ep806 5542117376 524287 524288 1428107 2771058688 (ep911 rfl rfl) rfl) ep1078 rfl) (@ep1079 2771058688 ep912 ep913 ep914 ep915 ep796 ep797 ep798 ep799 (@ep1080 5542117376 11 262144 1428107 2771058688 (ep1083 rfl rfl) rfl) ep1084 rfl) rfl rfl))

theorem EMRow25.d14 : @Eq Nat (Nat.mul (BSN.factNat (Nat.succ (Nat.mul 2 1))) (Nat.pow 4 (Nat.mul 2 1))) 96 := @Eq.refl Nat 96

theorem EMRow25.d15 : @Eq Nat (Nat.mul (Nat.mul 2 1) (Nat.pow (Nat.succ (Nat.mul 4 2)) (Nat.mul 2 1))) 162 := @Eq.refl Nat 162

theorem EMRow25.d16 : @Eq Nat (BSN.factNat (Nat.mul 2 2)) 24 := @Eq.refl Nat 24

theorem EMRow25.d17 : @Eq Nat (Nat.pow 23 (Nat.succ (Nat.mul 2 3))) 3404825447 := @Eq.refl Nat 3404825447

noncomputable abbrev qz567 := (@HAdd.hAdd Complex Complex Complex qz572 qz571 (@Nat.cast Complex Complex.instNatCast 3))

noncomputable abbrev qz491 := qz567

noncomputable abbrev qz220 := (@HDiv.hDiv Real Real Real qz270 (@Norm.norm Complex Complex.instNorm qz491) (@HAdd.hAdd Real Real Real qz381 (Complex.re qz272) qz296))

noncomputable abbrev qz221 := (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 2)

noncomputable abbrev qz222 := (@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 2)))

noncomputable abbrev qz492 := (@HPow.hPow Complex Complex Complex qz526 qz554 (@HSub.hSub Complex Complex Complex qz546 qz527 qz528))

noncomputable abbrev qz223 := qz492

noncomputable def ep1085 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 23))) (@HMul.hMul Real Real Real qz0 qz220 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))) 1448536535 154618822656 55354531 463856467968 104822925067503745 252201579132747776 49518481631

noncomputable def ep1086 := nat_lit 16572920462854017145246842880

noncomputable def ep1087 := @Enclosure.Real.IsNear.mulLit_ff (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 23)) 4427 294912 1 884736 327205 524288 4143 524288 1448536535 154618822656

noncomputable abbrev qz224 := qz271

noncomputable abbrev qz568 := (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid)))

noncomputable abbrev qz493 := (@Inv.inv Real Real.instInv (@HPow.hPow Real Nat Real qz568 qz224 2))

noncomputable def ep1088 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 96 162) qz493 96 162 0 1 13281 524288 1 524288 4427 294912 1 884736

noncomputable def ep1089 := nat_lit 781950621441006189802102638025

noncomputable def ep1090 := nat_lit 19807040628566084398385987584

noncomputable def ep1091 := nat_lit 26986075409044041160201671

noncomputable def ep1092 := nat_lit 1073741824000000000000000000000000000000

noncomputable abbrev qz494 := (@HPow.hPow Real Nat Real qz568 qz224 1)

noncomputable def ep1093 := @Enclosure.Real.IsNear.mulLit_ff qz494 qz224 884279719003555 140737488355328 1 500000000000000 884279719003555 140737488355328 1 500000000000000 ep1089 ep1090 ep1091 ep1092

noncomputable def ep1094 := ep1093 (@Enclosure.Real.IsNear.of_eq qz494 qz224 Bool.false 884279719003555 140737488355328 1 500000000000000 (BSN.pow_one_r qz224) (@Enclosure.Real.IsNear.of_eq qz224 qz268 Bool.false 884279719003555 140737488355328 1 500000000000000 BSN.two_pi_eq qz269)) (@Enclosure.Real.IsNear.of_eq qz224 qz268 Bool.false 884279719003555 140737488355328 1 500000000000000 BSN.two_pi_eq qz269) rfl

noncomputable abbrev qz495 := (@HPow.hPow Real Nat Real qz568 qz224 2)

noncomputable def ep1095 := @Enclosure.Real.IsNear.inv_image qz495 ep1089 ep1090 ep1091 ep1092 6640 6641 262144 (@Enclosure.Real.IsNear.of_eq qz495 (@HMul.hMul Real Real Real qz0 qz494 qz224) Bool.false ep1089 ep1090 ep1091 ep1092 (BSN.pow_succ_r qz224 1 2 rfl) ep1094) rfl rfl rfl

noncomputable def ep1096 := ep1088 (Enclosure.Real.IsNear.const Bool.false 96 162) (@Enclosure.Real.IsNear.recentre' qz493 Bool.false 13281 524288 1 524288 13281 524288 1 524288 (ep1095 rfl rfl rfl) rfl)

noncomputable def ep1097 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 23)) (Real.sqrt (@HAdd.hAdd Real Real Real qz381 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz5 1 23)) (Complex.re (zetaApproximant qz5 1 23))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz5 1 23)) (Complex.im (zetaApproximant qz5 1 23))))) Bool.false 327205 524288 4143 524288

noncomputable def ep1098 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz381 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz5 1 23)) (Complex.re (zetaApproximant qz5 1 23))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz5 1 23)) (Complex.im (zetaApproximant qz5 1 23))))) Bool.false 327205 524288 4143 524288

noncomputable def ep1099 := nat_lit 855338810499891653781145683821262645581

noncomputable def ep1100 := nat_lit 2195676701747988405297616520006860800000

noncomputable def ep1101 := nat_lit 3149667265387958325782084368151774343001987809398572661

noncomputable def ep1102 := nat_lit 319469394177367836707283413687606137748801702382796800000

noncomputable def ep1103 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz381 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz5 1 23)) (Complex.re (zetaApproximant qz5 1 23))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz5 1 23)) (Complex.im (zetaApproximant qz5 1 23)))) ep1099 ep1100 ep1101 ep1102 161531 165674

noncomputable def ep1104 := nat_lit 2086595784933918572398179591718260796449624048601

noncomputable def ep1105 := nat_lit 5360668191898191809097974217613358804238336000000

noncomputable def ep1106 := nat_lit 6090555840345276188430307827822619385125769590675106401

noncomputable def ep1107 := nat_lit 638938788354735673414566827375212275497603404765593600000

noncomputable def ep1108 := nat_lit 1684129450797189082186398027184458158441865169

noncomputable def ep1109 := nat_lit 69592896810213487711286969493643100292735342707346307

noncomputable def ep1110 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz5 1 23)) (Complex.re (zetaApproximant qz5 1 23))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz5 1 23)) (Complex.im (zetaApproximant qz5 1 23))) ep1104 ep1105 ep1106 ep1107 ep1108 ep1105 ep1109

noncomputable def ep1111 := nat_lit 212979596118245224471522275791737425165867801588531200000

noncomputable def ep1112 := nat_lit 11194575712822025033348311594791037444521433594460154395967632284061854505915402328704286720000000

noncomputable def ep1113 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (zetaApproximant qz5 1 23)) (Complex.re (zetaApproximant qz5 1 23)) ep287 ep288 ep289 ep290 ep287 ep288 ep289 ep290 ep1104

noncomputable def ep1114 := @Enclosure.Real.IsNear.mulLit_tt (Complex.im (zetaApproximant qz5 1 23)) (Complex.im (zetaApproximant qz5 1 23)) 41038146288510511646263 ep288 ep419 ep420 41038146288510511646263 ep288 ep419 ep420 ep1108

noncomputable def ep1115 := @ep1085 252201579132747776 ep1086 964670934647671945 2269814212194729984 813945056774021 6809442636584189952 (@ep1087 55354531 463856467968 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaStirlingErrorBound 1 2) (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 96 162) qz493) Bool.false 4427 294912 1 884736 (BSN.theta_err_eq 1 2 96 162 EMRow25.d14 EMRow25.d15 rfl) (ep1096 rfl)) (ep1097 (BSN.norm_eq_sqrt_mul_add (zetaApproximant qz5 1 23)) (@ep1098 327205 524288 4143 524288 (@ep1103 262144 (@ep1110 ep1111 ep1112 ep1099 ep1100 ep1101 ep1102 (@ep1113 ep1105 ep1106 ep1107 ep590 ep590 rfl) (@ep1114 ep1105 ep1109 ep1111 ep598 ep598 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl)

noncomputable abbrev qz225 := (@Norm.norm Complex Complex.instNorm qz491)

noncomputable abbrev qz569 := (Enclosure.sfrac Bool.false 2 7)

noncomputable def ep1116 := @Enclosure.Real.IsNear.of_eq (@HMul.hMul Real Real Real qz0 qz220 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))) (@HMul.hMul Real Real Real qz0 (@HMul.hMul Real Real Real qz0 qz225 qz569) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))) Bool.false 104822925067503745 252201579132747776 49518481631 252201579132747776 (BSN.zrb_shape_eq qz225 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) qz13 3)

noncomputable def ep1117 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz0 qz225 qz569) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) 46377085 1835008 1 1835008 2260230997 137438953472 1019 137438953472

noncomputable def ep1118 := @Enclosure.Real.IsNear.mulLit_ff qz225 qz569 46377085 524288 1 524288 2 7 0 1 46377085 1835008

noncomputable abbrev qz496 := (Complex.re qz567)

noncomputable abbrev qz497 := (Complex.im qz567)

noncomputable abbrev qz226 := (@HAdd.hAdd Real Real Real qz381 (@HMul.hMul Real Real Real qz267 qz496 qz496) (@HMul.hMul Real Real Real qz267 qz497 qz497))

noncomputable abbrev qz227 := qz491

noncomputable def ep1119 := @Enclosure.Real.IsNear.of_eq qz225 (Real.sqrt qz226) Bool.false 46377085 524288 1 524288 (BSN.norm_eq_sqrt_mul_add qz227)

noncomputable def ep1120 := @Enclosure.Real.IsNear.recentre' (Real.sqrt qz226) Bool.false 46377085 524288 1 524288 46377085

noncomputable def ep1121 := @Enclosure.Real.IsNear.sqrt_image qz226 244521517 31250 0 1 23188542 23188543 262144

noncomputable abbrev qz228 := (@HMul.hMul Real Real Real qz267 qz496 qz496)

noncomputable abbrev qz229 := (@HMul.hMul Real Real Real qz267 qz497 qz497)

noncomputable def ep1122 := @Enclosure.Real.IsNear.addLit_ff qz228 qz229 49 4 0 1 488277409 62500 0 1

noncomputable abbrev qz230 := qz496

noncomputable def ep1123 := @Enclosure.Real.IsNear.mulLit_ff qz230 qz230 7 2 0 1 7 2 0 1 49 4

noncomputable abbrev qz498 := (Enclosure.sfrac Bool.false 7 2)

noncomputable def ep1124 := @Enclosure.Complex.IsNear.of_eq qz227 (Complex.mk qz498 qz13) Bool.false 7 2 0 1 Bool.false 88388 1000 0 1 (BSN.s_add_nat_mk qz13 Bool.false 88388 1000 3 qz14)

noncomputable abbrev qz499 := (ep1124 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7 2) qz13 Bool.false 7 2 0 1 Bool.false 88388 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 7 2) qz18))

noncomputable def ep1125 := @ep1123 0 1 (@Enclosure.Complex.IsNear.re_isNear qz227 Bool.false 7 2 0 1 Bool.false 88388 1000 0 1 qz499)

noncomputable def ep1126 := ep1125 (@Enclosure.Complex.IsNear.re_isNear qz227 Bool.false 7 2 0 1 Bool.false 88388 1000 0 1 qz499)

noncomputable abbrev qz231 := qz497

noncomputable def ep1127 := @Enclosure.Real.IsNear.mulLit_ff qz231 qz231 88388 1000 0 1 88388 1000 0 1 488277409 62500

noncomputable def ep1128 := @ep1127 0 1 (@Enclosure.Complex.IsNear.im_isNear qz227 Bool.false 7 2 0 1 Bool.false 88388 1000 0 1 qz499)

noncomputable def ep1129 := ep1128 (@Enclosure.Complex.IsNear.im_isNear qz227 Bool.false 7 2 0 1 Bool.false 88388 1000 0 1 qz499)

noncomputable def ep1130 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Real.sqrt (@HAdd.hAdd Real Real Real qz381 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))))) Bool.false 2260230997 137438953472

noncomputable def ep1131 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz381 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))))) Bool.false 2260230997 137438953472

noncomputable def ep1132 := nat_lit 530087914034065243823085924695483777051081542171362821497

noncomputable def ep1133 := nat_lit 1960026433464605549549037738806984897986560000000000000000000

noncomputable def ep1134 := nat_lit 94014468821823998206501353864918223341994114907507622382176186918438829

noncomputable def ep1135 := nat_lit 385903518491464334109684622235938739561957809879899189962342400000000000000000000

noncomputable def ep1136 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz381 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)))) ep1132 ep1133 ep1134 ep1135

noncomputable def ep1137 := nat_lit 262406537021999708779401906024299050781133834166884255889

noncomputable def ep1138 := nat_lit 2177807148294006166165597487563316553318400000000000000000000

noncomputable def ep1139 := nat_lit 35587888206632341360059269848768183016039117806374432707301301563773327

noncomputable def ep1140 := nat_lit 343025349770190519208608553098612212943962497671021502188748800000000000000000000

noncomputable def ep1141 := nat_lit 2939220307142655059216242092736146313480610914211669911969

noncomputable def ep1142 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))) ep1137 ep1138 ep1139 ep1140 ep1141

noncomputable def ep1143 := nat_lit 19600264334646055495490377388069848979865600000000000000000000

noncomputable def ep1144 := nat_lit 431824756714900913411477402280432139591600859002691084691697781273550689

noncomputable def ep1145 := nat_lit 3087228147931714672877476977887509916495662479039193519698739200000000000000000000

noncomputable def ep1146 := nat_lit 11544292484076459188321537167020155014487228977482596962092597870938153509780933809844062622056448000000000000000000000

noncomputable def ep1147 := nat_lit 16198967159112327454666373417

noncomputable def ep1148 := nat_lit 1475739525896764129280000000000

noncomputable def ep1149 := nat_lit 123778838453000454204567169786061

noncomputable def ep1150 := nat_lit 26192569548258930573579135221760000000000

noncomputable def ep1151 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) ep1147 ep1148 ep1149 ep1150 ep1147 ep1148 ep1149

noncomputable def ep1152 := nat_lit 54214576519075154159438841937

noncomputable def ep1153 := nat_lit 4427218577690292387840000000000

noncomputable def ep1154 := nat_lit 448769124583163493508412654631409

noncomputable def ep1155 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223) Bool.false ep1147 ep1148 ep1149 ep1150 Bool.false ep1152 ep1153 ep1154

noncomputable def ep1156 := nat_lit 78577708644776791720737405665280000000000

noncomputable def ep1157 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223 Bool.false ep1147 ep1148 ep1149 ep1150 Bool.false ep1152 ep1153 ep1154 ep1156

noncomputable def ep1158 := nat_lit 1920474274364313960193447

noncomputable def ep1159 := nat_lit 2951479051793528258560000000

noncomputable def ep1160 := nat_lit 234202181990489064107653777789

noncomputable def ep1161 := nat_lit 838162225544285778354532327096320000000

noncomputable def ep1162 := nat_lit 15238730021930170474569649917

noncomputable def ep1163 := nat_lit 155280027021063561268270652306873

noncomputable abbrev qz232 := (Complex.re qz492)

noncomputable abbrev qz233 := (Complex.im qz492)

noncomputable def ep1164 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz232) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz233) ep1158 ep1159 ep1160 ep1161 ep1162 ep1148 ep1163

noncomputable def ep1165 := nat_lit 34923426064345240764772180295680000000000

noncomputable def ep1166 := nat_lit 47810912230811356438540988974948671910382686699520000000

noncomputable def ep1167 := nat_lit 55877481702952385223635488473088

noncomputable def ep1168 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz232 732377051 15000000 0 1 7866744070183791 590295810358705651712 319783616472833832839 ep1167 ep1158

noncomputable def ep1169 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) 732377051 15000000 0 1 0 1 0 1 732377051

noncomputable def ep1170 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 2197131153 62500 0 1 732377051 15000000 0

noncomputable def ep1171 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (Complex.mk (Enclosure.sfrac Bool.true 1 720) qz10) Bool.true 1 720 0 1 Bool.false 0 1 0 1 (BSN.bern_coeff_mk 2 1 30 24 Bool.true BSN.bern_real_2 EMRow25.d16 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 1 720) qz10 Bool.true 1 720 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.true 1 720) qz20)

noncomputable abbrev qz500 := (@HAdd.hAdd Complex Complex Complex qz525 qz524 qz529)

noncomputable abbrev qz234 := qz500

noncomputable def ep1172 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) (@HMul.hMul Complex Complex Complex qz62 (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) qz234) Bool.true 2197131153 62500 0 1 Bool.true 5390762398649 7812500 0 1

noncomputable abbrev qz235 := (Complex.re qz500)

noncomputable abbrev qz236 := (Complex.im qz500)

noncomputable def ep1173 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz235) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz236) 244115267 12500 0 1 488277409 31250 0 1

noncomputable def ep1174 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz235 244115267 31250 0 1 5 2 0 1 244115267 12500

noncomputable abbrev qz501 := (@HAdd.hAdd Complex Complex Complex qz525 qz524 (@Nat.cast Complex Complex.instNatCast 1))

noncomputable abbrev qz237 := qz501

noncomputable def ep1175 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) (@HMul.hMul Complex Complex Complex qz62 (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) qz237) Bool.true 244115267 31250 0 1 Bool.false 22097 125 0 1

noncomputable abbrev qz238 := (Complex.re qz501)

noncomputable abbrev qz239 := (Complex.im qz501)

noncomputable def ep1176 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz238) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz239) 3 4 0 1 488277409 62500 0 1

noncomputable def ep1177 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz238 1 2 0 1 3 2 0 1 3 4

noncomputable def ep1178 := @ep1177 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 88388 1000 0 1 ep555)

noncomputable abbrev qz502 := (Enclosure.sfrac Bool.false 3 2)

noncomputable def ep1179 := @Enclosure.Complex.IsNear.of_eq qz237 (Complex.mk qz502 qz13) Bool.false 3 2 0 1 Bool.false 88388 1000 0 1 (BSN.s_add_nat_mk qz13 Bool.false 88388 1000 1 qz14)

noncomputable abbrev qz503 := (ep1179 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 3 2) qz13 Bool.false 3 2 0 1 Bool.false 88388 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 3 2) qz18))

noncomputable def ep1180 := ep1178 (@Enclosure.Complex.IsNear.re_isNear qz237 Bool.false 3 2 0 1 Bool.false 88388 1000 0 1 qz503)

noncomputable def ep1181 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz239 88388 1000 0 1 88388 1000 0 1 488277409 62500

noncomputable def ep1182 := @ep1181 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 88388 1000 0 1 ep555)

noncomputable def ep1183 := ep1182 (@Enclosure.Complex.IsNear.im_isNear qz237 Bool.false 3 2 0 1 Bool.false 88388 1000 0 1 qz503)

noncomputable def ep1184 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) qz237 Bool.true 244115267 31250 0 1 Bool.false 22097 125 0 1 (@ep1176 1952922136 244115267 31250 0 1 (ep1180 rfl) (ep1183 rfl) rfl rfl)

noncomputable def ep1185 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz239) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz238) 22097 500 0 1 66291 500 0 1

noncomputable def ep1186 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz239 1 2 0 1 88388 1000 0 1 22097 500

noncomputable def ep1187 := @ep1186 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 88388 1000 0 1 ep555)

noncomputable def ep1188 := ep1187 (@Enclosure.Complex.IsNear.im_isNear qz237 Bool.false 3 2 0 1 Bool.false 88388 1000 0 1 qz503)

noncomputable def ep1189 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz238 88388 1000 0 1 3 2 0 1 66291 500

noncomputable def ep1190 := @ep1189 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 88388 1000 0 1 ep555)

noncomputable def ep1191 := ep1190 (@Enclosure.Complex.IsNear.re_isNear qz237 Bool.false 3 2 0 1 Bool.false 88388 1000 0 1 qz503)

noncomputable abbrev qz240 := (ep1175 (BSN.ascPochhammer_succ_eval_c 1 2 qz272 rfl) (ep1184 (@ep1185 44194000 22097 125 0 1 (ep1188 rfl) (ep1191 rfl) rfl rfl)))

noncomputable def ep1192 := @ep1174 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 244115267 31250 0 1 Bool.false 22097 125 0 1 qz240)

noncomputable abbrev qz504 := (Enclosure.sfrac Bool.false 5 2)

noncomputable def ep1193 := @Enclosure.Complex.IsNear.of_eq qz234 (Complex.mk qz504 qz13) Bool.false 5 2 0 1 Bool.false 88388 1000 0 1 (BSN.s_add_nat_mk qz13 Bool.false 88388 1000 2 qz14)

noncomputable abbrev qz505 := (ep1193 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 5 2) qz13 Bool.false 5 2 0 1 Bool.false 88388 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 5 2) qz18))

noncomputable def ep1194 := ep1192 (@Enclosure.Complex.IsNear.re_isNear qz234 Bool.false 5 2 0 1 Bool.false 88388 1000 0 1 qz505)

noncomputable def ep1195 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz236 22097 125 0 1 88388 1000 0 1 488277409 31250

noncomputable def ep1196 := @ep1195 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 244115267 31250 0 1 Bool.false 22097 125 0 1 qz240)

noncomputable def ep1197 := ep1196 (@Enclosure.Complex.IsNear.im_isNear qz234 Bool.false 5 2 0 1 Bool.false 88388 1000 0 1 qz505)

noncomputable def ep1198 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) qz234 Bool.true 2197131153 62500 0 1 Bool.true 5390762398649 7812500 0 1 (@ep1173 13732069706250 2197131153 62500 0 1 (ep1194 rfl) (ep1197 rfl) rfl rfl)

noncomputable def ep1199 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz236) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz235) 5394215054899 7812500 0 1 22097 50 0 1

noncomputable def ep1200 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz236 244115267 31250 0 1 88388 1000 0 1 5394215054899 7812500

noncomputable def ep1201 := @ep1200 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 244115267 31250 0 1 Bool.false 22097 125 0 1 qz240)

noncomputable def ep1202 := ep1201 (@Enclosure.Complex.IsNear.im_isNear qz234 Bool.false 5 2 0 1 Bool.false 88388 1000 0 1 qz505)

noncomputable def ep1203 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz235 22097 125 0 1 5 2 0 1 22097 50

noncomputable def ep1204 := @ep1203 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 244115267 31250 0 1 Bool.false 22097 125 0 1 qz240)

noncomputable def ep1205 := ep1204 (@Enclosure.Complex.IsNear.re_isNear qz234 Bool.false 5 2 0 1 Bool.false 88388 1000 0 1 qz505)

noncomputable abbrev qz241 := (ep1172 (BSN.ascPochhammer_succ_eval_c 2 3 qz272 rfl) (ep1198 (@ep1199 269538119932450 5390762398649 7812500 0 1 (ep1202 rfl) (ep1205 rfl) rfl rfl)))

noncomputable def ep1206 := @ep1170 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1171) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 2197131153 62500 0 1 Bool.true 5390762398649 7812500 0 1 qz241)

noncomputable def ep1207 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 5390762398649 7812500 0 1 0 1 0

noncomputable def ep1208 := @ep1207 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1171) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 2197131153 62500 0 1 Bool.true 5390762398649 7812500 0 1 qz241)

noncomputable def ep1209 := @Enclosure.Real.IsNear.addLit_ft_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) 5390762398649 5625000000 0 1 0 1 0 1 5390762398649

noncomputable def ep1210 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 5390762398649 7812500 0 1 5390762398649 5625000000 0

noncomputable def ep1211 := @ep1210 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1171) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 2197131153 62500 0 1 Bool.true 5390762398649 7812500 0 1 qz241)

noncomputable def ep1212 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 2197131153 62500 0 1 0 1 0

noncomputable def ep1213 := @ep1212 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1171) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 2197131153 62500 0 1 Bool.true 5390762398649 7812500 0 1 qz241)

noncomputable def ep1214 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.false 732377051 15000000 0 1 Bool.false 5390762398649 5625000000 0 1 (@ep1169 732377051 15000000 0 1 (ep1206 rfl) (ep1208 rfl) rfl rfl) (@ep1209 5390762398649 5625000000 0 1 (ep1211 rfl) (ep1213 rfl) rfl rfl)

noncomputable def ep1215 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 732377051 15000000 0 1 Bool.false 5390762398649 5625000000 0 1 ep1214

noncomputable def ep1216 := @Enclosure.Complex.IsNear.re_isNear qz223 Bool.false 7866744070183791 590295810358705651712 319783616472833832839 ep1167 Bool.true 25441405139974797 2361183241434822606848 259243524355629187593 ep1167

noncomputable abbrev qz506 := (@Nat.cast Real Real.instNatCast 3404825447)

noncomputable abbrev qz242 := (@Inv.inv Real Real.instInv (Real.sqrt qz506))

noncomputable def ep1217 := @Enclosure.Complex.IsNear.of_eq qz223 (Complex.mk (@HMul.hMul Real Real Real qz0 qz242 qz137) (@HMul.hMul Real Real Real qz0 qz242 qz418)) Bool.false 7866744070183791 590295810358705651712 319783616472833832839 ep1167 Bool.true 25441405139974797 2361183241434822606848 259243524355629187593

noncomputable def ep1218 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz506) 8019684176059419 137438953472 1 137438953472 1177693 1177694 68719476736 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz506) (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz506 qz15)) Bool.false 8019684176059419 137438953472 1 137438953472 (BSN.sqrt_natCast_div_one 3404825447) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz506 qz15)) Bool.false 8019684176059419 137438953472 1 137438953472 8019684176059419 137438953472 1 137438953472 (BSN.sqrt_enclosure 3404825447 1 4009842088029709 4009842088029710 68719476736 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep1219 := nat_lit 739532312687500000000000000

noncomputable def ep1220 := nat_lit 2958129250750000000000000

noncomputable def ep1221 := nat_lit 7763107665658486196323483648

noncomputable def ep1222 := nat_lit 2475880078570760549798248448

noncomputable def ep1223 := nat_lit 23665034006000000000000000

noncomputable def ep1224 := nat_lit 38173642625234895562091333025

noncomputable def ep1225 := nat_lit 418040252652648286100516895

noncomputable def ep1226 := BSN.log_dyadic_bound 7 39 8 7 ep1224 68719476736 23665034006 ep1225 91651674949449615 24938675630 46 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base7 (BSN.artanhP 7) (BSN.artanhQ 39) 0 7 ep1225 ep1224 91651674949449615 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep1227 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz139 88388 1000 0 1 3530252645604599 1125899906842624 125011832517003 ep1220 78007992709924824103 281474976710656000 2762386463128215291 ep1219 qz18 (BSN.isNear_log_sfrac 23 1 3530252645604599 1125899906842624 125011832517003 ep1220 Bool.false (@Enclosure.Real.IsNear.recentre' qz421 Bool.false ep1221 ep1222 1000094660136024 ep1223 3530252645604599 1125899906842624 125011832517003 ep1220 (BSN.log_rat_reduce_isNear 23 1 4 46 32 24938675630 68719476736 24973259072661432 36028797018963968 23665034006 1000000000000000 rfl rfl rfl rfl (ep1226 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1228 := nat_lit 1683373743569156758210347008

noncomputable def ep1229 := nat_lit 1055023758371737820006808555397075724208797490587020991115177267179222550564023953442579669671675663131950432489681830228619710359269424620601006835718245567942774102699555428499456

noncomputable def ep1230 := nat_lit 118471658034259428782235204372444635462331972429639033257780066369387519461588934825569028614577116538889267969336012369372246813616988720376390556367654990461123310430062324062617600

noncomputable def ep1231 := nat_lit 2413730760889046641095353007285186369521824238713174869028120827033046381334023847663891406853336794006682977028106004662034948464899490313812175555470138873450685924376576

noncomputable def ep1232 := nat_lit 6399934754545590260319163696199364024298328901003064891145304357060812367010548703417093173235298317050893425501686588011615082141189287740129780553861882354638282878896705256816640

noncomputable def ep1233 := nat_lit 10780920881117608019183403597892461827072209491097152026457986039614264271004593069126781603926517605038923385209577125612874460039145973554251540629456604131962221249135671489698201600

noncomputable def ep1234 := BSN.cos_dyadic_bound_f 191377437609976 281474976710656 4 3 137438953472 47376288782 ep1229 ep1230 ep1231 ep1232 ep1233 ep1231 106876623776 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 191377437609976) (BSN.cosEvenQ 281474976710656) 0 3 ep1229 ep1230 ep1231 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 191377437609976) (BSN.cosOddQ 281474976710656) 0 3 ep1232 ep1233 ep1231 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz507 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 4761230023799) (@Nat.cast Real Real.instNatCast 17179869184))

noncomputable def ep1235 := @Enclosure.Real.IsNear.cos_image qz140 qz507 Bool.false 4761230023799 17179869184 515 137438953472 Bool.false 106876623776 137438953472 1 23665034006 (@Enclosure.Real.IsNear.recentre' qz140 Bool.false 78007992709924824103 281474976710656000 2762386463128215291 ep1219 4761230023799 17179869184 515 137438953472 (ep1227 rfl) rfl) (Enclosure.sfrac_false_div 4761230023799 17179869184) (BSN.cos_reduce0 qz507 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep1228) (@Nat.cast Real Real.instNatCast ep1222)) 226375608064910080 72057594037927936 Bool.false 106876623776 137438953472 44 1000000000000000 47330068012 23665034006 (BSN.sin_reduce_arg_pos_rat_q0 4761230023799 17179869184 226375608064910080 72057594037927936 44 ep1228 ep1222 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 106876623776 137438953472 ep1228 ep1222 191377437609976 281474976710656 47376288782 47330068012 (ep1234 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1236 := nat_lit 25464466723487993371802906475870798486202561068014493320511382901428700529570088038776702681606561726005511313455841280

noncomputable def ep1237 := nat_lit 14298200008547628616551818071540114577587335786466501286865076710532687516440907786670008938572638187735909165122537390080

noncomputable def ep1238 := nat_lit 1799392406663595049494920059672388709745750881913104637617049014751729186837649661972967357583064117491516022194176

noncomputable def ep1239 := nat_lit 66689737640476813010356048994803097882143309676705337479545099043432236682571541049724360314200146226205162414062698496

noncomputable def ep1240 := nat_lit 262133666823373191303449997978235433922434489418552523592526406359765937801416642755616830540498366775158334693913185484800

noncomputable def ep1241 := BSN.sin_dyadic_bound_f 191377437609976 281474976710656 3 2 137438953472 47376288782 ep1236 ep1237 ep1238 ep1239 ep1240 ep1238 86410955448 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 191377437609976) (BSN.sinEvenQ 281474976710656) 0 2 ep1236 ep1237 ep1238 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 191377437609976) (BSN.sinOddQ 281474976710656) 0 2 ep1239 ep1240 ep1238 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1242 := @Enclosure.Real.IsNear.sin_image qz140 qz507 Bool.false 4761230023799 17179869184 515 137438953472 Bool.false 86410955448 137438953472 1 23665034006 (@Enclosure.Real.IsNear.recentre' qz140 Bool.false 78007992709924824103 281474976710656000 2762386463128215291 ep1219 4761230023799 17179869184 515 137438953472 (ep1227 rfl) rfl) (Enclosure.sfrac_false_div 4761230023799 17179869184) (BSN.sin_reduce0 qz507 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep1228) (@Nat.cast Real Real.instNatCast ep1222)) 226375608064910080 72057594037927936 Bool.false 86410955448 137438953472 44 1000000000000000 47330068012 23665034006 (BSN.sin_reduce_arg_pos_rat_q0 4761230023799 17179869184 226375608064910080 72057594037927936 44 ep1228 ep1222 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 86410955448 137438953472 ep1228 ep1222 191377437609976 281474976710656 47376288782 47330068012 (ep1241 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz508 := (@Enclosure.Real.IsNear.recentre' qz242 Bool.false 2355387 137438953472 1 137438953472 2355387 137438953472 1 137438953472 (ep1218 rfl rfl) rfl)

noncomputable def ep1243 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz242 qz137) (@HMul.hMul Real Real Real qz0 qz242 qz418) Bool.false 7866744070183791 590295810358705651712 319783616472833832839 ep1167 Bool.true 25441405139974797 2361183241434822606848 259243524355629187593 ep1167 (@Enclosure.Real.IsNear.mulLit_ff qz242 qz137 2355387 137438953472 1 137438953472 3339894493 4294967296 6162465733281 1626248753831965884416 7866744070183791 590295810358705651712 319783616472833832839 ep1167 qz508 (@Enclosure.Real.IsNear.recentre' qz137 Bool.false 106876623776 137438953472 12324931466562 3252497507663931768832 3339894493 4294967296 6162465733281 1626248753831965884416 (ep1235 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz242 qz418 2355387 137438953472 1 137438953472 10801369431 17179869184 6162465733281 1626248753831965884416 25441405139974797 2361183241434822606848 259243524355629187593 ep1167 qz508 (@Enclosure.Real.IsNear.neg qz138 Bool.false 10801369431 17179869184 6162465733281 1626248753831965884416 (@Enclosure.Real.IsNear.recentre' qz138 Bool.false 86410955448 137438953472 12324931466562 3252497507663931768832 10801369431 17179869184 6162465733281 1626248753831965884416 (ep1242 rfl rfl) rfl)) rfl)

noncomputable def ep1244 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz233 5390762398649 5625000000 0 1 25441405139974797 2361183241434822606848 259243524355629187593 ep1167 ep1162

noncomputable def ep1245 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 732377051 15000000 0 1 Bool.false 5390762398649 5625000000 0 1 ep1214

noncomputable def ep1246 := @Enclosure.Complex.IsNear.im_isNear qz223 Bool.false 7866744070183791 590295810358705651712 319783616472833832839 ep1167 Bool.true 25441405139974797 2361183241434822606848 259243524355629187593 ep1167

noncomputable def ep1247 := nat_lit 6210900423236994680394549

noncomputable def ep1248 := nat_lit 11805916207174113034240000000

noncomputable def ep1249 := nat_lit 63288002619474126552962376081

noncomputable def ep1250 := nat_lit 279387408514761926118177442365440000000

noncomputable def ep1251 := nat_lit 14135916044447256791146699453

noncomputable def ep1252 := nat_lit 1106804644422573096960000000000

noncomputable def ep1253 := nat_lit 1723877495385745581661567945434511

noncomputable def ep1254 := @Enclosure.Real.IsNear.addLit_tf_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz233) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz232) ep1247 ep1248 ep1249 ep1250 ep1251 ep1252 ep1253

noncomputable def ep1255 := nat_lit 314310834579107166882949622661120000000000

noncomputable def ep1256 := nat_lit 160013186897907617889928829594658806616090707230720000000

noncomputable def ep1257 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz233 732377051 15000000 0 1 25441405139974797 2361183241434822606848 259243524355629187593 ep1167 ep1247

noncomputable def ep1258 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz232 5390762398649 5625000000 0 1 7866744070183791 590295810358705651712 319783616472833832839 ep1167 ep1251

noncomputable abbrev qz509 := (@ep1217 ep1167 (BSN.cpow_neg_s_sub_mk qz13 88388 1000 23 3 3404825447 qz14 rfl EMRow25.d17) ep1243)

noncomputable def ep1259 := ep1157 (@ep1164 ep1165 ep1166 ep1147 ep1148 ep1149 ep1150 (@ep1168 ep1159 ep1160 ep1161 ep1215 (ep1216 qz509) rfl) (@ep1244 ep1148 ep1163 ep1165 ep1245 (ep1246 qz509) rfl) rfl rfl) (@ep1254 ep1255 ep1256 ep1152 ep1153 ep1154 ep1156 (@ep1257 ep1248 ep1249 ep1250 ep1215 (ep1246 qz509) rfl) (@ep1258 ep1252 ep1253 ep1255 ep1245 (ep1216 qz509) rfl) rfl rfl)

noncomputable def ep1260 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) ep1152 ep1153 ep1154 ep1156 ep1152 ep1153 ep1154

noncomputable def ep1261 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223) Bool.false ep1147 ep1148 ep1149 ep1150 Bool.false ep1152 ep1153 ep1154

noncomputable def ep1262 := @ep1117 104822925067503745 252201579132747776 49518481631 252201579132747776 (@ep1118 1 1835008 (ep1119 (@ep1120 524288 1 524288 (ep1121 (@ep1122 1956172136 244521517 31250 0 1 (ep1126 rfl) (ep1129 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) (Enclosure.Real.IsNear.const Bool.false 2 7) rfl) (@ep1130 1019 137438953472 (BSN.norm_eq_sqrt_mul_add (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (@ep1131 1019 137438953472 2260230997 137438953472 1019 137438953472 (@ep1136 1130114989 1130116008 68719476736 (@ep1142 ep1143 ep1144 ep1145 ep1146 ep1132 ep1133 ep1134 ep1135 (@ep1151 ep1150 ep1137 ep1138 ep1139 ep1140 (@ep1155 ep1156 ep1259) (@ep1155 ep1156 ep1259) rfl) (@ep1260 ep1156 ep1141 ep1143 ep1144 ep1145 (@ep1261 ep1156 ep1259) (@ep1261 ep1156 ep1259) rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl

theorem EMRow25.d18 : Enclosure.Real.IsNear (@HAdd.hAdd Real Real Real qz381 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 23))) (@HMul.hMul Real Real Real qz0 qz220 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)))) Bool.false 964670934647671945 2269814212194729984 813945056774021 6809442636584189952 := ep1115 (ep1116 ep1262) rfl rfl

noncomputable abbrev qz570 := (@HAdd.hAdd Complex Complex Complex qz572 qz578 (@Nat.cast Complex Complex.instNatCast 3))

noncomputable abbrev qz510 := qz570

noncomputable abbrev qz243 := (@HDiv.hDiv Real Real Real qz270 (@Norm.norm Complex Complex.instNorm qz510) (@HAdd.hAdd Real Real Real qz381 (Complex.re qz426) qz296))

noncomputable abbrev qz511 := (@HPow.hPow Complex Complex Complex qz526 qz554 (@HSub.hSub Complex Complex Complex qz546 qz562 qz528))

noncomputable abbrev qz244 := qz511

noncomputable def ep1263 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz149 1 23))) (@HMul.hMul Real Real Real qz0 qz243 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))) 215130065 3221225472 592103 4831838208 116492246911641519 252201579132747776 53633777749

noncomputable def ep1264 := nat_lit 429503935154223667015057408

noncomputable def ep1265 := @Enclosure.Real.IsNear.mulLit_ff (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz149 1 23)) 4427 294912 1 884736 145785 32768 513 65536 215130065 3221225472

noncomputable def ep1266 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (zetaApproximant qz149 1 23)) (Real.sqrt (@HAdd.hAdd Real Real Real qz381 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz149 1 23)) (Complex.re (zetaApproximant qz149 1 23))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz149 1 23)) (Complex.im (zetaApproximant qz149 1 23))))) Bool.false 145785 32768 513 65536

noncomputable def ep1267 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz381 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz149 1 23)) (Complex.re (zetaApproximant qz149 1 23))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz149 1 23)) (Complex.im (zetaApproximant qz149 1 23))))) Bool.false 2332560 524288 4104 524288

noncomputable def ep1268 := nat_lit 469169839778529774788785878894297279505573133

noncomputable def ep1269 := nat_lit 23702982833954641233565507296493043712000000

noncomputable def ep1270 := nat_lit 24309076513591981385901546411956544569912333238427401736210117

noncomputable def ep1271 := nat_lit 349035620985256561640606451929379348456248008407685005312000000

noncomputable def ep1272 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz381 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz149 1 23)) (Complex.re (zetaApproximant qz149 1 23))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz149 1 23)) (Complex.im (zetaApproximant qz149 1 23)))) ep1268 ep1269 ep1270 ep1271 1164228 1168332

noncomputable def ep1273 := nat_lit 858717620590278865194960677136581958198002552704187041

noncomputable def ep1274 := nat_lit 43383606399699776113812816018246915932683239424000000

noncomputable def ep1275 := nat_lit 1076954080893844839719126126433990753884112118542131772852747

noncomputable def ep1276 := nat_lit 15512694266011402739582508974639082153611022595897111347200000

noncomputable def ep1277 := nat_lit 1680449203665993558801689332140503547827310223801

noncomputable def ep1278 := nat_lit 15618098303891919400972613766568889735765966192640000

noncomputable def ep1279 := nat_lit 155219386960944984442417134383505215039621142458873694046619

noncomputable def ep1280 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz149 1 23)) (Complex.re (zetaApproximant qz149 1 23))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz149 1 23)) (Complex.im (zetaApproximant qz149 1 23))) ep1273 ep1274 ep1275 ep1276 ep1277 ep1278 ep1279

noncomputable def ep1281 := nat_lit 698071241970513123281212903858758696912496016815370010624000000

noncomputable def ep1282 := nat_lit 13411609117609965642950320389379773013133306697370369841036595291542646224763709024133137530087528202240000

noncomputable def ep1283 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (zetaApproximant qz149 1 23)) (Complex.re (zetaApproximant qz149 1 23)) ep802 ep803 ep804 ep805 ep802 ep803 ep804 ep805 ep1273

noncomputable def ep1284 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (zetaApproximant qz149 1 23)) (Complex.im (zetaApproximant qz149 1 23)) ep912 ep913 ep914 ep915 ep912 ep913 ep914 ep915 ep1277

noncomputable def ep1285 := @ep1263 252201579132747776 ep1264 400006710695311117 756604737398243328 278630221906685 2269814212194729984 (@ep1265 592103 4831838208 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaStirlingErrorBound 1 2) (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 96 162) qz493) Bool.false 4427 294912 1 884736 (BSN.theta_err_eq 1 2 96 162 EMRow25.d14 EMRow25.d15 rfl) (ep1096 rfl)) (ep1266 (BSN.norm_eq_sqrt_mul_add (zetaApproximant qz149 1 23)) (@ep1267 145785 32768 513 65536 (@ep1272 262144 (@ep1280 ep1281 ep1282 ep1268 ep1269 ep1270 ep1271 (@ep1283 ep1274 ep1275 ep1276 ep1078 ep1078 rfl) (@ep1284 ep1278 ep1279 ep1281 ep1084 ep1084 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl)

noncomputable abbrev qz245 := (@Norm.norm Complex Complex.instNorm qz510)

noncomputable def ep1286 := @Enclosure.Real.IsNear.of_eq (@HMul.hMul Real Real Real qz0 qz243 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))) (@HMul.hMul Real Real Real qz0 (@HMul.hMul Real Real Real qz0 qz245 qz569) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))) Bool.false 116492246911641519 252201579132747776 53633777749 252201579132747776 (BSN.zrb_shape_eq qz245 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) qz152 3)

noncomputable def ep1287 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz0 qz245 qz569) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) 47616081 1835008 1 1835008 2446489599 137438953472 1075 137438953472

noncomputable def ep1288 := @Enclosure.Real.IsNear.mulLit_ff qz245 qz569 47616081 524288 1 524288 2 7 0 1 47616081 1835008

noncomputable abbrev qz512 := (Complex.re qz570)

noncomputable abbrev qz513 := (Complex.im qz570)

noncomputable abbrev qz246 := (@HAdd.hAdd Real Real Real qz381 (@HMul.hMul Real Real Real qz267 qz512 qz512) (@HMul.hMul Real Real Real qz267 qz513 qz513))

noncomputable abbrev qz247 := qz510

noncomputable def ep1289 := @Enclosure.Real.IsNear.of_eq qz245 (Real.sqrt qz246) Bool.false 47616081 524288 1 524288 (BSN.norm_eq_sqrt_mul_add qz247)

noncomputable def ep1290 := @Enclosure.Real.IsNear.recentre' (Real.sqrt qz246) Bool.false 47616081 524288 1 524288 47616081

noncomputable def ep1291 := @Enclosure.Real.IsNear.sqrt_image qz246 8248357009 1000000 0 1 23808040 23808041 262144

noncomputable abbrev qz248 := (@HMul.hMul Real Real Real qz267 qz512 qz512)

noncomputable abbrev qz249 := (@HMul.hMul Real Real Real qz267 qz513 qz513)

noncomputable def ep1292 := @Enclosure.Real.IsNear.addLit_ff qz248 qz249 49 4 0 1 8236107009 1000000 0 1

noncomputable abbrev qz250 := qz512

noncomputable def ep1293 := @Enclosure.Real.IsNear.mulLit_ff qz250 qz250 7 2 0 1 7 2 0 1 49 4

noncomputable def ep1294 := @Enclosure.Complex.IsNear.of_eq qz247 (Complex.mk qz498 qz152) Bool.false 7 2 0 1 Bool.false 90753 1000 0 1 (BSN.s_add_nat_mk qz152 Bool.false 90753 1000 3 qz153)

noncomputable abbrev qz514 := (ep1294 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7 2) qz152 Bool.false 7 2 0 1 Bool.false 90753 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 7 2) qz154))

noncomputable def ep1295 := @ep1293 0 1 (@Enclosure.Complex.IsNear.re_isNear qz247 Bool.false 7 2 0 1 Bool.false 90753 1000 0 1 qz514)

noncomputable def ep1296 := ep1295 (@Enclosure.Complex.IsNear.re_isNear qz247 Bool.false 7 2 0 1 Bool.false 90753 1000 0 1 qz514)

noncomputable abbrev qz251 := qz513

noncomputable def ep1297 := @Enclosure.Real.IsNear.mulLit_ff qz251 qz251 90753 1000 0 1 90753 1000 0 1 8236107009 1000000

noncomputable def ep1298 := @ep1297 0 1 (@Enclosure.Complex.IsNear.im_isNear qz247 Bool.false 7 2 0 1 Bool.false 90753 1000 0 1 qz514)

noncomputable def ep1299 := ep1298 (@Enclosure.Complex.IsNear.im_isNear qz247 Bool.false 7 2 0 1 Bool.false 90753 1000 0 1 qz514)

noncomputable def ep1300 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Real.sqrt (@HAdd.hAdd Real Real Real qz381 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))))) Bool.false 2446489599 137438953472

noncomputable def ep1301 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz381 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))))) Bool.false 2446489599 137438953472

noncomputable def ep1302 := nat_lit 144715948771025171482529375475473796773409768060578646795813257

noncomputable def ep1303 := nat_lit 456719261665907161938651510223838443642478919680000000000000000000

noncomputable def ep1304 := nat_lit 160201934225334909627565502655526323052048393683339045246842551517397061254919

noncomputable def ep1305 := nat_lit 575501038657003670191497475478288639679885471932622468286511138734080000000000000000000

noncomputable def ep1306 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz381 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)))) ep1302 ep1303 ep1304 ep1305

noncomputable def ep1307 := nat_lit 166009277154760326696178986856775779845107422998307389673398249

noncomputable def ep1308 := nat_lit 570899077082383952423314387779798054553098649600000000000000000000

noncomputable def ep1309 := nat_lit 36758598942440618394196475214127081717554585459809831556238308825725622727979

noncomputable def ep1310 := nat_lit 143875259664250917547874368869572159919971367983155617071627784683520000000000000000000

noncomputable def ep1311 := nat_lit 59542635236084550627930929950265864486619148309663675285473289

noncomputable def ep1312 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))) ep1307 ep1308 ep1309 ep1310 ep1311

noncomputable def ep1313 := nat_lit 2283596308329535809693257551119192218212394598400000000000000000000

noncomputable def ep1314 := nat_lit 13167538455572436050779601799017996181830051844099719021889316214494570343003

noncomputable def ep1315 := nat_lit 413091007962399132907948410292610173827673725580146512568881965508016909465496149202561163466807786902388736000000000000000000000

noncomputable def ep1316 := nat_lit 12884458745122370358490523163693

noncomputable def ep1317 := nat_lit 755578637259143234191360000000000

noncomputable def ep1318 := nat_lit 200925145699957295803708954342588771

noncomputable def ep1319 := nat_lit 26821191217417144907345034467082240000000000

noncomputable def ep1320 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) ep1316 ep1317 ep1318 ep1319 ep1316 ep1317 ep1318

noncomputable def ep1321 := nat_lit 7716387447250465184998647796733

noncomputable def ep1322 := nat_lit 1511157274518286468382720000000000

noncomputable def ep1323 := nat_lit 120179969922471753769057097880547271

noncomputable def ep1324 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3))) qz244) Bool.false ep1316 ep1317 ep1318 ep1319 Bool.true ep1321 ep1322 ep1323

noncomputable def ep1325 := nat_lit 53642382434834289814690068934164480000000000

noncomputable def ep1326 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3))) qz244 Bool.false ep1316 ep1317 ep1318 ep1319 Bool.true ep1321 ep1322 ep1323 ep1325

noncomputable def ep1327 := nat_lit 637283609941425035393695949

noncomputable def ep1328 := nat_lit 3022314549036572936765440000000

noncomputable def ep1329 := nat_lit 9971944420156527962164669547063

noncomputable def ep1330 := nat_lit 107284764869668579629380137868328960000000

noncomputable def ep1331 := nat_lit 13043779647607726617338947150943

noncomputable def ep1332 := nat_lit 198432159594918163813167786955823021

noncomputable abbrev qz252 := (Complex.re qz511)

noncomputable abbrev qz253 := (Complex.im qz511)

noncomputable def ep1333 := @Enclosure.Real.IsNear.subLit_tt_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3)))) qz252) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3)))) qz253) ep1327 ep1328 ep1329 ep1330 ep1331 ep1317 ep1332

noncomputable def ep1334 := nat_lit 38940887121844845214774534701406700596932247663065169920000000

noncomputable def ep1335 := nat_lit 223509926811809540894541953892352

noncomputable def ep1336 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3)))) qz252 24707071027 480000000 0 1 77380715331857661 18889465931478580854784 403606903030275890669 ep1335 ep1327

noncomputable def ep1337 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3)))) 24707071027 480000000 0 1 0 1 0 1 24707071027

noncomputable def ep1338 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 74121213081 2000000 0 1 24707071027 480000000 0

noncomputable abbrev qz515 := (@HAdd.hAdd Complex Complex Complex qz525 qz561 qz529)

noncomputable abbrev qz254 := qz515

noncomputable def ep1339 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3)) (@HMul.hMul Complex Complex Complex qz62 (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 2)) qz254) Bool.true 74121213081 2000000 0 1 Bool.true 746929589637777 1000000000 0 1

noncomputable abbrev qz255 := (Complex.re qz515)

noncomputable abbrev qz256 := (Complex.im qz515)

noncomputable def ep1340 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 2))) qz255) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 2))) qz256) 8235357009 400000 0 1 8236107009 500000 0 1

noncomputable def ep1341 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 2))) qz255 8235357009 1000000 0 1 5 2 0 1 8235357009 400000

noncomputable abbrev qz516 := (@HAdd.hAdd Complex Complex Complex qz525 qz561 (@Nat.cast Complex Complex.instNatCast 1))

noncomputable abbrev qz257 := qz516

noncomputable def ep1342 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 2)) (@HMul.hMul Complex Complex Complex qz62 (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 1)) qz257) Bool.true 8235357009 1000000 0 1 Bool.false 90753 500 0 1

noncomputable abbrev qz258 := (Complex.re qz516)

noncomputable abbrev qz259 := (Complex.im qz516)

noncomputable def ep1343 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 1))) qz258) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 1))) qz259) 3 4 0 1 8236107009 1000000 0 1

noncomputable def ep1344 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 1))) qz258 1 2 0 1 3 2 0 1 3 4

noncomputable def ep1345 := @ep1344 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 90753 1000 0 1 ep1040)

noncomputable def ep1346 := @Enclosure.Complex.IsNear.of_eq qz257 (Complex.mk qz502 qz152) Bool.false 3 2 0 1 Bool.false 90753 1000 0 1 (BSN.s_add_nat_mk qz152 Bool.false 90753 1000 1 qz153)

noncomputable abbrev qz517 := (ep1346 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 3 2) qz152 Bool.false 3 2 0 1 Bool.false 90753 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 3 2) qz154))

noncomputable def ep1347 := ep1345 (@Enclosure.Complex.IsNear.re_isNear qz257 Bool.false 3 2 0 1 Bool.false 90753 1000 0 1 qz517)

noncomputable def ep1348 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 1))) qz259 90753 1000 0 1 90753 1000 0 1 8236107009 1000000

noncomputable def ep1349 := @ep1348 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 90753 1000 0 1 ep1040)

noncomputable def ep1350 := ep1349 (@Enclosure.Complex.IsNear.im_isNear qz257 Bool.false 3 2 0 1 Bool.false 90753 1000 0 1 qz517)

noncomputable def ep1351 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 1)) qz257 Bool.true 8235357009 1000000 0 1 Bool.false 90753 500 0 1 (@ep1343 32941428036 8235357009 1000000 0 1 (ep1347 rfl) (ep1350 rfl) rfl rfl)

noncomputable def ep1352 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 1))) qz259) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 1))) qz258) 90753 2000 0 1 272259 2000 0 1

noncomputable def ep1353 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 1))) qz259 1 2 0 1 90753 1000 0 1 90753 2000

noncomputable def ep1354 := @ep1353 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 90753 1000 0 1 ep1040)

noncomputable def ep1355 := ep1354 (@Enclosure.Complex.IsNear.im_isNear qz257 Bool.false 3 2 0 1 Bool.false 90753 1000 0 1 qz517)

noncomputable def ep1356 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 1))) qz258 90753 1000 0 1 3 2 0 1 272259 2000

noncomputable def ep1357 := @ep1356 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 90753 1000 0 1 ep1040)

noncomputable def ep1358 := ep1357 (@Enclosure.Complex.IsNear.re_isNear qz257 Bool.false 3 2 0 1 Bool.false 90753 1000 0 1 qz517)

noncomputable abbrev qz260 := (ep1342 (BSN.ascPochhammer_succ_eval_c 1 2 qz426 rfl) (ep1351 (@ep1352 726024000 90753 500 0 1 (ep1355 rfl) (ep1358 rfl) rfl rfl)))

noncomputable def ep1359 := @ep1341 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 8235357009 1000000 0 1 Bool.false 90753 500 0 1 qz260)

noncomputable def ep1360 := @Enclosure.Complex.IsNear.of_eq qz254 (Complex.mk qz504 qz152) Bool.false 5 2 0 1 Bool.false 90753 1000 0 1 (BSN.s_add_nat_mk qz152 Bool.false 90753 1000 2 qz153)

noncomputable abbrev qz518 := (ep1360 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 5 2) qz152 Bool.false 5 2 0 1 Bool.false 90753 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 5 2) qz154))

noncomputable def ep1361 := ep1359 (@Enclosure.Complex.IsNear.re_isNear qz254 Bool.false 5 2 0 1 Bool.false 90753 1000 0 1 qz518)

noncomputable def ep1362 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 2))) qz256 90753 500 0 1 90753 1000 0 1 8236107009 500000

noncomputable def ep1363 := @ep1362 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 8235357009 1000000 0 1 Bool.false 90753 500 0 1 qz260)

noncomputable def ep1364 := ep1363 (@Enclosure.Complex.IsNear.im_isNear qz254 Bool.false 5 2 0 1 Bool.false 90753 1000 0 1 qz518)

noncomputable def ep1365 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 2)) qz254 Bool.true 74121213081 2000000 0 1 Bool.true 746929589637777 1000000000 0 1 (@ep1340 7412121308100000 74121213081 2000000 0 1 (ep1361 rfl) (ep1364 rfl) rfl rfl)

noncomputable def ep1366 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 2))) qz256) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 2))) qz255) 747383354637777 1000000000 0 1 90753 200 0 1

noncomputable def ep1367 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 2))) qz256 8235357009 1000000 0 1 90753 1000 0 1 747383354637777 1000000000

noncomputable def ep1368 := @ep1367 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 8235357009 1000000 0 1 Bool.false 90753 500 0 1 qz260)

noncomputable def ep1369 := ep1368 (@Enclosure.Complex.IsNear.im_isNear qz254 Bool.false 5 2 0 1 Bool.false 90753 1000 0 1 qz518)

noncomputable def ep1370 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 2))) qz255 90753 500 0 1 5 2 0 1 90753 200

noncomputable def ep1371 := @ep1370 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 8235357009 1000000 0 1 Bool.false 90753 500 0 1 qz260)

noncomputable def ep1372 := ep1371 (@Enclosure.Complex.IsNear.re_isNear qz254 Bool.false 5 2 0 1 Bool.false 90753 1000 0 1 qz518)

noncomputable abbrev qz261 := (ep1339 (BSN.ascPochhammer_succ_eval_c 2 3 qz426 rfl) (ep1365 (@ep1366 149385917927555400 746929589637777 1000000000 0 1 (ep1369 rfl) (ep1372 rfl) rfl rfl)))

noncomputable def ep1373 := @ep1338 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1171) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 74121213081 2000000 0 1 Bool.true 746929589637777 1000000000 0 1 qz261)

noncomputable def ep1374 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 746929589637777 1000000000 0 1 0 1 0

noncomputable def ep1375 := @ep1374 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1171) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 74121213081 2000000 0 1 Bool.true 746929589637777 1000000000 0 1 qz261)

noncomputable def ep1376 := @Enclosure.Real.IsNear.addLit_ft_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3)))) 248976529879259 240000000000 0 1 0 1 0 1 248976529879259

noncomputable def ep1377 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 746929589637777 1000000000 0 1 248976529879259 240000000000 0

noncomputable def ep1378 := @ep1377 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1171) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 74121213081 2000000 0 1 Bool.true 746929589637777 1000000000 0 1 qz261)

noncomputable def ep1379 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 74121213081 2000000 0 1 0 1 0

noncomputable def ep1380 := @ep1379 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1171) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 74121213081 2000000 0 1 Bool.true 746929589637777 1000000000 0 1 qz261)

noncomputable def ep1381 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.false 24707071027 480000000 0 1 Bool.false 248976529879259 240000000000 0 1 (@ep1337 24707071027 480000000 0 1 (ep1373 rfl) (ep1375 rfl) rfl rfl) (@ep1376 248976529879259 240000000000 0 1 (ep1378 rfl) (ep1380 rfl) rfl rfl)

noncomputable def ep1382 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 24707071027 480000000 0 1 Bool.false 248976529879259 240000000000 0 1 ep1381

noncomputable def ep1383 := nat_lit 111754963405904770447270976946176

noncomputable def ep1384 := @Enclosure.Complex.IsNear.re_isNear qz244 Bool.true 77380715331857661 18889465931478580854784 403606903030275890669 ep1335 Bool.true 157168785996816231 9444732965739290427392 796991426023760976919 ep1383

noncomputable def ep1385 := @Enclosure.Complex.IsNear.of_eq qz244 (Complex.mk (@HMul.hMul Real Real Real qz0 qz242 qz216) (@HMul.hMul Real Real Real qz0 qz242 qz488)) Bool.true 77380715331857661 18889465931478580854784 403606903030275890669 ep1335 Bool.true 157168785996816231 9444732965739290427392 796991426023760976919

noncomputable def ep1386 := nat_lit 2958129250750000000000000000

noncomputable def ep1387 := @Enclosure.Real.IsNear.mulLit_ff qz152 qz139 90753 1000 0 1 3530252645604599 1125899906842624 125011832517003 ep1220 320381018346554173047 1125899906842624000 11345198836415573259 ep1386 qz154 (BSN.isNear_log_sfrac 23 1 3530252645604599 1125899906842624 125011832517003 ep1220 Bool.false (@Enclosure.Real.IsNear.recentre' qz421 Bool.false ep1221 ep1222 1000094660136024 ep1223 3530252645604599 1125899906842624 125011832517003 ep1220 (BSN.log_rat_reduce_isNear 23 1 4 46 32 24938675630 68719476736 24973259072661432 36028797018963968 23665034006 1000000000000000 rfl rfl rfl rfl (ep1226 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1388 := nat_lit 597606707849264204053741568

noncomputable def ep1389 := nat_lit 404430631834128331627332711239631706432292501390494924495558926345267004025852242938636964874422430913661948552806400

noncomputable def ep1390 := nat_lit 453947052187476338083769974498103745896969602140957561675752482538344467674085244361233101485569217381653282816

noncomputable def ep1391 := nat_lit 1059222348413203993586085917619076710392796527595749907366602093971679948462379640129844037436561104328476961628225536

noncomputable def ep1392 := BSN.sin_dyadic_bound_f 67940016816608 281474976710656 3 2 137438953472 47376288782 ep1389 ep1237 ep1390 ep1391 ep1240 ep1390 32852654503 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 67940016816608) (BSN.sinEvenQ 281474976710656) 0 2 ep1389 ep1237 ep1390 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 67940016816608) (BSN.sinOddQ 281474976710656) 0 2 ep1391 ep1240 ep1390 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz519 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 4888626378579) (@Nat.cast Real Real.instNatCast 17179869184))

noncomputable def ep1393 := @Enclosure.Real.IsNear.cos_image qz218 qz519 Bool.false 4888626378579 17179869184 33 8589934592 Bool.true 32852654503 137438953472 1 23665034006 (@Enclosure.Real.IsNear.recentre' qz218 Bool.false 320381018346554173047 1125899906842624000 11345198836415573259 ep1386 4888626378579 17179869184 33 8589934592 (ep1387 rfl) rfl) (Enclosure.sfrac_false_div 4888626378579 17179869184) (BSN.cos_reduce1 qz519 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep1388) (@Nat.cast Real Real.instNatCast ep1222)) 226375608064910080 72057594037927936 Bool.false 32852654503 137438953472 45 1000000000000000 47330068012 23665034006 (BSN.sin_reduce_arg_pos_rat_q1 4888626378579 17179869184 226375608064910080 72057594037927936 45 ep1388 ep1222 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 32852654503 137438953472 ep1388 ep1222 67940016816608 281474976710656 47376288782 47330068012 (ep1392 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1394 := nat_lit 224683886106538934226890654586450724952938454981209242923115703859585019278570212337129141033835344093908807708573696

noncomputable def ep1395 := nat_lit 1588688889838625401839090896837790508620815087385166809651675190059187501826767531852223215396959798637323240569170821120

noncomputable def ep1396 := nat_lit 674050750425512427727995796219403178651323571004423446854223760073789981146775288840898700635303061143291659819155456

noncomputable def ep1397 := nat_lit 71491000042738143082759090357700572887936678932332506434325383552663437582204538933350044692863190938679545825612686950400

noncomputable def ep1398 := BSN.cos_dyadic_bound_f 67940016816608 281474976710656 3 2 137438953472 47376288782 ep1394 ep1395 ep1390 ep1396 ep1397 ep1390 133454745226 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 67940016816608) (BSN.cosEvenQ 281474976710656) 0 2 ep1394 ep1395 ep1390 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 67940016816608) (BSN.cosOddQ 281474976710656) 0 2 ep1396 ep1397 ep1390 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1399 := @Enclosure.Real.IsNear.sin_image qz218 qz519 Bool.false 4888626378579 17179869184 33 8589934592 Bool.false 133454745226 137438953472 1 23665034006 (@Enclosure.Real.IsNear.recentre' qz218 Bool.false 320381018346554173047 1125899906842624000 11345198836415573259 ep1386 4888626378579 17179869184 33 8589934592 (ep1387 rfl) rfl) (Enclosure.sfrac_false_div 4888626378579 17179869184) (BSN.sin_reduce1 qz519 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep1388) (@Nat.cast Real Real.instNatCast ep1222)) 226375608064910080 72057594037927936 Bool.false 133454745226 137438953472 45 1000000000000000 47330068012 23665034006 (BSN.sin_reduce_arg_pos_rat_q1 4888626378579 17179869184 226375608064910080 72057594037927936 45 ep1388 ep1222 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 133454745226 137438953472 ep1388 ep1222 67940016816608 281474976710656 47376288782 47330068012 (ep1398 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1400 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz242 qz216) (@HMul.hMul Real Real Real qz0 qz242 qz488) Bool.true 77380715331857661 18889465931478580854784 403606903030275890669 ep1335 Bool.true 157168785996816231 9444732965739290427392 796991426023760976919 ep1383 (@Enclosure.Real.IsNear.mulLit_ft qz242 qz216 2355387 137438953472 1 137438953472 32852654503 137438953472 394768028395 101640547114497867776 77380715331857661 18889465931478580854784 403606903030275890669 ep1335 qz508 (@Enclosure.Real.IsNear.recentre' qz216 Bool.true 32852654503 137438953472 789536056790 203281094228995735552 32852654503 137438953472 394768028395 101640547114497867776 (ep1393 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz242 qz488 2355387 137438953472 1 137438953472 66727372613 68719476736 394768028395 101640547114497867776 157168785996816231 9444732965739290427392 796991426023760976919 ep1383 qz508 (@Enclosure.Real.IsNear.neg qz217 Bool.false 66727372613 68719476736 394768028395 101640547114497867776 (@Enclosure.Real.IsNear.recentre' qz217 Bool.false 133454745226 137438953472 789536056790 203281094228995735552 66727372613 68719476736 394768028395 101640547114497867776 (ep1399 rfl rfl) rfl)) rfl)

noncomputable def ep1401 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3)))) qz253 248976529879259 240000000000 0 1 157168785996816231 9444732965739290427392 796991426023760976919 ep1383 ep1331

noncomputable def ep1402 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 24707071027 480000000 0 1 Bool.false 248976529879259 240000000000 0 1 ep1381

noncomputable def ep1403 := @Enclosure.Complex.IsNear.im_isNear qz244 Bool.true 77380715331857661 18889465931478580854784 403606903030275890669 ep1335 Bool.true 157168785996816231 9444732965739290427392 796991426023760976919 ep1383

noncomputable def ep1404 := nat_lit 1294393452950233871727813079

noncomputable def ep1405 := nat_lit 1511157274518286468382720000000

noncomputable def ep1406 := nat_lit 19691323770679078646408640625813

noncomputable def ep1407 := nat_lit 53642382434834289814690068934164480000000

noncomputable def ep1408 := nat_lit 6421993994300231313270834717733

noncomputable def ep1409 := nat_lit 100488646151792675122648457254734271

noncomputable def ep1410 := @Enclosure.Real.IsNear.addLit_tt (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3)))) qz253) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3)))) qz252) ep1404 ep1405 ep1406 ep1407 ep1408 ep1322 ep1409

noncomputable def ep1411 := nat_lit 11660675023914130962902658014098760172789410993809653760000000

noncomputable def ep1412 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3)))) qz253 24707071027 480000000 0 1 157168785996816231 9444732965739290427392 796991426023760976919 ep1383 ep1404

noncomputable def ep1413 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3)))) qz252 248976529879259 240000000000 0 1 77380715331857661 18889465931478580854784 403606903030275890669 ep1335 ep1408

noncomputable abbrev qz520 := (@ep1385 ep1383 (BSN.cpow_neg_s_sub_mk qz152 90753 1000 23 3 3404825447 qz153 rfl EMRow25.d17) ep1400)

noncomputable def ep1414 := ep1326 (@ep1333 ep1319 ep1334 ep1316 ep1317 ep1318 ep1319 (@ep1336 ep1328 ep1329 ep1330 ep1382 (ep1384 qz520) rfl) (@ep1401 ep1317 ep1332 ep1319 ep1402 (ep1403 qz520) rfl) rfl rfl) (@ep1410 ep1325 ep1411 ep1321 ep1322 ep1323 ep1325 (@ep1412 ep1405 ep1406 ep1407 ep1382 (ep1403 qz520) rfl) (@ep1413 ep1322 ep1409 ep1325 ep1402 (ep1384 qz520) rfl) rfl rfl)

noncomputable def ep1415 := @Enclosure.Real.IsNear.mulLit_tt (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) ep1321 ep1322 ep1323 ep1325 ep1321 ep1322 ep1323

noncomputable def ep1416 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3))) qz244) Bool.false ep1316 ep1317 ep1318 ep1319 Bool.true ep1321 ep1322 ep1323

noncomputable def ep1417 := @ep1287 116492246911641519 252201579132747776 53633777749 252201579132747776 (@ep1288 1 1835008 (ep1289 (@ep1290 524288 1 524288 (ep1291 (@ep1292 32993428036 8248357009 1000000 0 1 (ep1296 rfl) (ep1299 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) (Enclosure.Real.IsNear.const Bool.false 2 7) rfl) (@ep1300 1075 137438953472 (BSN.norm_eq_sqrt_mul_add (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (@ep1301 1075 137438953472 2446489599 137438953472 1075 137438953472 (@ep1306 1223244262 1223245337 68719476736 (@ep1312 ep1313 ep1314 ep1305 ep1315 ep1302 ep1303 ep1304 ep1305 (@ep1320 ep1319 ep1307 ep1308 ep1309 ep1310 (@ep1324 ep1325 ep1414) (@ep1324 ep1325 ep1414) rfl) (@ep1415 ep1325 ep1311 ep1313 ep1314 ep1305 (@ep1416 ep1325 ep1414) (@ep1416 ep1325 ep1414) rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl

theorem EMRow25.d19 : Enclosure.Real.IsNear (@HAdd.hAdd Real Real Real qz381 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz149 1 23))) (@HMul.hMul Real Real Real qz0 qz243 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)))) Bool.false 400006710695311117 756604737398243328 278630221906685 2269814212194729984 := ep1285 (ep1286 ep1417) rfl rfl

noncomputable def EMRow25.d20 := fun (I J : @NonemptyInterval Real Real.instLE) => @LE.le Real Real.instLE (@Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE I)) (@Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE J))

noncomputable abbrev qz521 := (EMRow25.d3 qz531 qz563 (@Enclosure.dec_le_dec qz531 qz563 88388 1000 90753 1000 (@Eq.refl Real qz531) (@Eq.refl Real qz563) rfl rfl rfl) 23 23 1 1)

noncomputable abbrev qz262 := qz521

noncomputable def ep1418 := @Zeta.Certificates.ZIntervalEM.Certificate.mk qz262 (@Enclosure.dec_nonneg qz13 88388 1000 qz14) (@Enclosure.pos_of_ble 1 rfl) (@Enclosure.pos_of_ble 23 rfl)

noncomputable abbrev qz263 := (Zeta.Certificates.ZIntervalEM.fstVal qz521)

noncomputable def ep1419 := @Enclosure.Real.IsNear.neg_val qz263 ep271 ep272

noncomputable def ep1420 := @Enclosure.Real.IsNear.of_eq qz263 (hardyZApproximantEM 1 23 qz13) Bool.true

noncomputable abbrev qz264 := (Zeta.Certificates.ZIntervalEM.sndVal qz521)

noncomputable def ep1421 := BSN.mul_neg_of_neg_pos_r qz263 qz264 (@ep1419 ep273 ep274 (@ep1420 ep271 ep272 ep273 ep274 (@Eq.refl Real (hardyZApproximantEM 1 23 qz13)) EMRow25.d10) rfl rfl rfl)

noncomputable def ep1422 := @Enclosure.Real.IsNear.pos_val qz264 ep785 ep786

noncomputable def ep1423 := @Enclosure.Real.IsNear.of_eq qz264 (hardyZApproximantEM 1 23 qz152) Bool.false

noncomputable def ep1424 := BSN.gt_trans_le (@Norm.norm Real Real.norm qz263) (BSN.hardyZErrorBoundStrong 1 23 qz13)

noncomputable def ep1425 := @Enclosure.norm_gt_of_isNear qz263 (BSN.hardyZErrorBoundStrong 1 23 qz13) Bool.true

noncomputable def ep1426 := @Enclosure.Real.IsNear.of_eq (BSN.hardyZErrorBoundStrong 1 23 qz13) (@HAdd.hAdd Real Real Real qz381 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 23))) (@HMul.hMul Real Real Real qz0 qz220 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)))) Bool.false 964670934647671945 2269814212194729984 813945056774021 6809442636584189952 (@Eq.refl Real (@HAdd.hAdd Real Real Real qz381 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 23))) (@HMul.hMul Real Real Real qz0 qz220 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)))))

noncomputable def ep1427 := BSN.gt_trans_le (@Norm.norm Real Real.norm qz264) (BSN.hardyZErrorBoundStrong 1 23 qz152)

noncomputable def ep1428 := @Enclosure.norm_gt_of_isNear qz264 (BSN.hardyZErrorBoundStrong 1 23 qz152) Bool.false

noncomputable def ep1429 := @Enclosure.Real.IsNear.of_eq (BSN.hardyZErrorBoundStrong 1 23 qz152) (@HAdd.hAdd Real Real Real qz381 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz149 1 23))) (@HMul.hMul Real Real Real qz0 qz243 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)))) Bool.false 400006710695311117 756604737398243328 278630221906685 2269814212194729984 (@Eq.refl Real (@HAdd.hAdd Real Real Real qz381 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz149 1 23))) (@HMul.hMul Real Real Real qz0 qz243 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)))))

noncomputable def ep1430 := @List.cons EMRow25.d0 (@PSigma.mk Zeta.Certificates.ZIntervalEM Zeta.Certificates.ZIntervalEM.Certificate qz262 (ep1418 (@Enclosure.pos_of_ble 1 rfl) (@Enclosure.pos_of_ble 23 rfl) (ep1421 (@ep1422 ep787 ep788 (@ep1423 ep785 ep786 ep787 ep788 (@Eq.refl Real (hardyZApproximantEM 1 23 qz152)) EMRow25.d13) rfl rfl rfl)) (ep1424 (hardyZErrorBoundEM 1 23 qz13) (BSN.hardyZErrorBoundEM_le_strong 1 23 qz13 rfl) (@ep1425 Bool.false ep271 ep272 ep273 ep274 964670934647671945 2269814212194729984 813945056774021 6809442636584189952 (@ep1420 ep271 ep272 ep273 ep274 (@Eq.refl Real (hardyZApproximantEM 1 23 qz13)) EMRow25.d10) (ep1426 EMRow25.d18) rfl rfl rfl rfl rfl)) (ep1427 (hardyZErrorBoundEM 1 23 qz152) (BSN.hardyZErrorBoundEM_le_strong 1 23 qz152 rfl) (@ep1428 Bool.false ep785 ep786 ep787 ep788 400006710695311117 756604737398243328 278630221906685 2269814212194729984 (@ep1423 ep785 ep786 ep787 ep788 (@Eq.refl Real (hardyZApproximantEM 1 23 qz152)) EMRow25.d13) (ep1429 EMRow25.d19) rfl rfl rfl rfl rfl)))) (@List.nil EMRow25.d0)

noncomputable abbrev qz522 := (@Enclosure.dec_le_dec qz531 qz563 88388 1000 90753 1000 (@Eq.refl Real qz531) (@Eq.refl Real qz563) rfl rfl rfl)

noncomputable abbrev qz265 := (Zeta.Certificates.CertifiedZeroIntervals.intervals (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedEM ep1430 (@List.IsChain.singleton EMRow25.d1 EMRow25.d20 (EMRow25.d2 qz284 qz433 qz522))))

noncomputable abbrev qz523 := (@NonemptyInterval Real Real.instLE)

noncomputable def ep1431 := And (@Eq (Option Real) (@Option.map qz523 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz523 qz265)) (@Option.some Real qz13))

noncomputable def ep1432 := ep1431 (@Eq (Option Real) (@Option.map qz523 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz523 qz265)) (@Option.some Real qz152))

noncomputable def ep1433 := @And.intro (@Eq Nat (@List.length qz523 qz265) 1) ep1432

noncomputable def ep1434 := @And.intro (@Eq (Option Real) (@Option.map qz523 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz523 qz265)) (@Option.some Real qz13))

noncomputable def ep1435 := @ep1434 (@Eq (Option Real) (@Option.map qz523 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz523 qz265)) (@Option.some Real qz152))

noncomputable abbrev qz266 := (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedEM ep1430 (@List.IsChain.singleton EMRow25.d1 EMRow25.d20 (EMRow25.d2 qz284 qz433 qz522)))

theorem EMRow25.d21 : Zeta.Certificates.BatchSpec 1 88388 1000 90753 1000 := @Exists.intro Zeta.Certificates.CertifiedZeroIntervals (fun (C : Zeta.Certificates.CertifiedZeroIntervals) => And (@Eq Nat (@List.length qz523 (Zeta.Certificates.CertifiedZeroIntervals.intervals C)) 1) (And (@Eq (Option Real) (@Option.map qz523 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz523 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz13)) (@Eq (Option Real) (@Option.map qz523 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz523 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz152)))) qz266 (ep1433 (@Eq.refl Nat 1) (ep1435 (@Eq.refl (Option Real) (@Option.some Real qz13)) (@Eq.refl (Option Real) (@Option.some Real qz152))))

theorem solution : Zeta.Certificates.BatchSpec 1 88388 1000 90753 1000 := EMRow25.d21
#print axioms solution
#check solution
