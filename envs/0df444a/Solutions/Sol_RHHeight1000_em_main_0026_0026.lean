-- Prove2me | solution 1 for RHHeight1000.em_main_0026_0026
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-20T08:27:09.254872+00:00
-- url     : https://prove2.me/submissions/873248bf-4c1f-47fa-8e44-fae0fd60e5b1

import Definitions.Def_RHT1000_Support_20261118_S005
/- Copyright (c) 2026 Salvatore Mercuri, Bhavik Mehta.
Apache 2.0 license; see the source project LICENSE. -/
set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable def EMRow26.d0 := @PSigma Zeta.Certificates.ZIntervalEM fun (I : Zeta.Certificates.ZIntervalEM) => Zeta.Certificates.ZIntervalEM.Certificate I

noncomputable def EMRow26.d1 := @NonemptyInterval Real Real.instLE

noncomputable def EMRow26.d2 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @NonemptyInterval.mk Real Real.instLE (@Prod.mk Real Real a b) h

noncomputable def EMRow26.d3 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) (fc sc fb sb : Nat) => Zeta.Certificates.ZIntervalEM.mk (EMRow26.d2 a b h) fc sc fb sb

noncomputable def ep0 := nat_lit 26986075409044028275299783

noncomputable def ep1 := nat_lit 4294967296000000000000000

noncomputable def ep2 := nat_lit 26986075409044045455168967

noncomputable abbrev qz267 := (@instHMul Real Real.instMul)

noncomputable abbrev qz0 := qz267

noncomputable abbrev qz268 := (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 2 1) Real.pi)

noncomputable def ep3 := @BSN.isNear_log_image_fff qz268 884279719003555 140737488355328 1 500000000000000 ep0 ep1 ep2 ep1 4138529546116343 2251799813685248 50000000025619 12809500000000000000 4138529546116343 2251799813685248 50000000025619 12809500000000000000 481788 262144

noncomputable abbrev qz269 := (@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 2 1) Real.pi 2 1 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 140737488355328 1 500000000000000 (Enclosure.Real.IsNear.const Bool.false 2 1) BSN.pi_near_15 rfl)

noncomputable def ep4 := @ep3 2 262144 qz269 rfl rfl rfl rfl

noncomputable def ep5 := nat_lit 53972150818088056550599566

noncomputable def ep6 := nat_lit 34359738368000000000000000

noncomputable def ep7 := nat_lit 9806206225044028275299783

noncomputable def ep8 := nat_lit 44165944593044028275299783

noncomputable def ep9 := nat_lit 13681445815609410487519367394620474863599256634174726093703677122907123617368241606644861540940610176751640793056574796245399519365549113997355475306157239709119582688278313060810592403844863400465080549957745

noncomputable def ep10 := nat_lit 231714499556395493334623298703961145503103241611736774613091488581016477543539392410113701224645713379230392133956226737605624599560350113120270717249177907454870984269546186598262646369758174842349131395304

noncomputable def ep11 := nat_lit 8978369550011295664474073352761810093897501552430546263638635096022803738134167562509900960712119243631997923545019968443113540909076206607473711060286601587364321108377403290080403445693385008949995305

noncomputable def ep12 := BSN.log_dyadic_bound ep7 ep8 5 4 ep9 524288 256190 ep10 ep11 236759 ep5 ep6 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP ep7) (BSN.artanhQ ep8) 0 4 ep10 ep9 ep11 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz270 := (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))

noncomputable abbrev qz1 := qz270

noncomputable def ep13 := ep4 rfl rfl rfl rfl (BSN.isNear_log_sfrac ep0 ep1 4138529546116343 2251799813685248 50000000025619 12809500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep0) (@Nat.cast Real Real.instNatCast ep1))) Bool.false 34716502058787923820544 18889465931478580854784 1000000000512380 256190000000000000000 4138529546116343 2251799813685248 50000000025619 12809500000000000000 (BSN.log_rat_reduce_isNear ep0 ep1 2 ep5 ep6 236759 524288 24973259072661432 36028797018963968 256190 1000000000000000 rfl rfl rfl rfl (ep12 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep14 := nat_lit 53972150818088090910337934

noncomputable def ep15 := nat_lit 9806206225044045455168967

noncomputable def ep16 := nat_lit 44165944593044045455168967

noncomputable def ep17 := nat_lit 13681445815609453062485491347592146866046743284321690683909457683007658987562290830600045658905080811372395010565947827677605470036294121079488508864180301737865471494204890974265645509835068840465080549957745

noncomputable def ep18 := nat_lit 231714499556396865510889920206523150079811393376960301632499817942333196803513131357563499488546302200815366867712007119763002650772307103678175657719139104636874731038771518520299266622696414842349131395304

noncomputable def ep19 := nat_lit 8978369550011421500876706511871067098718760264493934208903156435737864998391937547068187824077011975074541700434630537294838404525415248443919841847024664017658842168336182958576672102333385008949995305

noncomputable def ep20 := BSN.log_dyadic_bound ep15 ep16 5 4 ep17 524288 256190 ep18 ep19 236759 ep14 ep6 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP ep15) (BSN.artanhQ ep16) 0 4 ep18 ep17 ep19 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep21 := ep13 (BSN.isNear_log_sfrac ep2 ep1 4138529546116343 2251799813685248 50000000025619 12809500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep2) (@Nat.cast Real Real.instNatCast ep1))) Bool.false 34716502058787923820544 18889465931478580854784 1000000000512380 256190000000000000000 4138529546116343 2251799813685248 50000000025619 12809500000000000000 (BSN.log_rat_reduce_isNear ep2 ep1 2 ep14 ep6 236759 524288 24973259072661432 36028797018963968 256190 1000000000000000 rfl rfl rfl rfl (ep20 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable abbrev qz271 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)

noncomputable abbrev qz2 := (Real.log qz271)

theorem EMRow26.d4 : Enclosure.Real.IsNear qz2 Bool.false 120447 65536 1 131072 := @Enclosure.Real.IsNear.of_eq qz2 (Real.log qz268) Bool.false 120447 65536 1 131072 BSN.log_two_pi_eq (@Enclosure.Real.IsNear.recentre' (Real.log qz268) Bool.false 481788 262144 2 262144 120447 65536 1 131072 (ep21 rfl rfl rfl rfl rfl rfl rfl rfl) rfl)

noncomputable def ep22 := nat_lit 8589934592000000000000000

noncomputable def ep23 := @BSN.isNear_log_image_fff Real.pi 226375608064910080 72057594037927936 1 1000000000000000 ep0 ep22 ep2 ep22 600168 524288 1 256190 600168 524288 1 256190 300084 262144 2 262144 BSN.pi_near_15 rfl rfl rfl

noncomputable def ep24 := nat_lit 17179869184000000000000000

noncomputable def ep25 := nat_lit 18396140817044028275299783

noncomputable def ep26 := nat_lit 35576010001044028275299783

noncomputable def ep27 := nat_lit 145019262663961446558303139663424756232419223153299357158415217874016130572233056993847515999529612750616182853355499335896178729185698845314776375864537073527142908641610750276034469165612529925303649396973267518946591078603565291376312767403717761600170009932259137778521478520425507632472584532570900560707662248426541531715360699177249902784721815296292248142738824858695953661559845440650653128788875447728828657762006237171740033404723254477174341920697506370253193455781322964835857351124092897592956162654178130575

noncomputable def ep28 := nat_lit 15500762873619990602332184736899274490522931101512051618692838888825382235673431503644115344741331161500627469184702974962114537943617674254904297224139410345221262767191485292268260077615645253784097850065864022184521411511133693085443040736512010941548648374196772723338837137976260321103066698629790037694560548409922339907589559883712609967105556007429010014773911317423638534096849366294542840133852248768895750397896505791271178551667935288585787166713880920071720072716082683081155281219708172458141800988558163320

noncomputable def ep29 := nat_lit 12900190794487083783367107939442176642390171280542213571554777169279725287102813254708993369099729304728646904879886535518616983985412662170766446331701281703998252143668221340329975389245922410714088123244705567402747658401492589451585970559635763980329972215329212888079422466283203384882259392047898400615815810081169907384366653346471604103896809335921621947903075223769953790093549808584241881353287841076643853121427928248525828402335494512605306631304432120211393210317325496757155861061354331245840675149075

noncomputable def ep30 := BSN.log_dyadic_bound ep25 ep26 11 10 ep27 524288 256190 ep28 ep29 600168 ep5 ep24 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base10 (BSN.artanhP ep25) (BSN.artanhQ ep26) 0 10 ep28 ep27 ep29 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep31 := nat_lit 18396140817044045455168967

noncomputable def ep32 := nat_lit 35576010001044045455168967

noncomputable def ep33 := nat_lit 145019262663962847171784895425483977818796535899227200426399035286881207006285364467913811844950531107314785650583974625982406238691319033447632878979985852280879486690814033867010958364699188952871572448188560932645032521756218245629809291975913196623825614492380080480004685076434733043183791438169545293975334857826316990371107134320667652578346815517853870648072772035977941843998949310557583393428557296298890786965786350523173236912472938174255438182435383147950274229549088258679583524155427309880956162654178130575

noncomputable def ep34 := nat_lit 15500762873620157189619721156942591192100275120160672416764593300158228469749443299607348495591439275767946573253526107895503597951484257520435868240203420954375895980141891044871083424251900562230440202302413072793440172565998181227591194192658878334739610458454844032013325963992941389843551995646587189684848765634635122388286241104146031552341815777883628509454807838726994150833304950745987647656768534710890974432620160470644835720379148964170536679305861738540146791997074363921127776563807649880221800988558163320

noncomputable def ep35 := nat_lit 12900190794487324729109480814509220959173684627296055849229843377126536688487849343376525559792931631054411655715865486295286288812423905434305314401904993536755333953308594664509631000767632482919425633906965368325056855874260596615770736441041599390097968820060635361729170158825410327022636428624381203910573184452046894301676992229743752846881064485858738985580654099214803581683226335297196686880535448467637789069028262446657986458573827723305156755787640135484017403116612632808333639900906331245840675149075

noncomputable def ep36 := BSN.log_dyadic_bound ep31 ep32 11 10 ep33 524288 256190 ep34 ep35 600168 ep14 ep24 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base10 (BSN.artanhP ep31) (BSN.artanhQ ep32) 0 10 ep34 ep33 ep35 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep37 := @Enclosure.Real.IsNear.recentre' (Real.log Real.pi) Bool.false 300084 262144 2 262144 75021 65536 1 131072 (ep23 rfl rfl rfl rfl rfl (BSN.isNear_log_sfrac ep0 ep22 600168 524288 1 256190 Bool.false (BSN.logfrac_isNear ep5 ep24 1 ep0 ep22 600168 524288 256190 rfl rfl rfl (ep30 rfl))) (BSN.isNear_log_sfrac ep2 ep22 600168 524288 1 256190 Bool.false (BSN.logfrac_isNear ep14 ep24 1 ep2 ep22 600168 524288 256190 rfl rfl rfl (ep36 rfl))) rfl rfl rfl rfl rfl rfl rfl rfl) rfl

theorem EMRow26.d5 : Enclosure.Real.IsNear (Real.log Real.pi) Bool.false 75021 65536 1 131072 := ep37

noncomputable abbrev qz527 := (@HAdd.hAdd Complex Complex Complex (@instHAdd Complex Complex.instAdd) (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (2 : Complex)) (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul) Complex.I ↑(Enclosure.sfrac Bool.false 90753 1000)))

noncomputable abbrev qz503 := qz527

noncomputable abbrev qz272 := qz503

noncomputable abbrev qz3 := (BSN.headSumC qz272 9)

noncomputable abbrev qz528 := (@instHAdd Complex Complex.instAdd)

noncomputable abbrev qz504 := qz528

noncomputable abbrev qz273 := qz504

noncomputable abbrev qz4 := qz273

noncomputable abbrev qz5 := qz272

noncomputable abbrev qz505 := (@instHPow Complex Complex Complex.instPow)

noncomputable abbrev qz274 := qz505

noncomputable abbrev qz506 := (@Neg.neg Complex Complex.instNeg qz527)

noncomputable abbrev qz275 := qz506

noncomputable abbrev qz6 := (@HPow.hPow Complex Complex Complex qz274 (@Nat.cast Complex Complex.instNatCast 8) qz275)

noncomputable def ep38 := @Enclosure.Complex.IsNear.of_eq qz3 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 8) qz6) Bool.false 243218440123 68719476736 3894463965793 1600476613181440 Bool.true 48783384305 274877906944 7773307875901 3200953226362880

noncomputable def ep39 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 8) qz6 Bool.false 878032596179 274877906944 76658896002429 35210485489991680 Bool.true 27575262023 274877906944 76537959463409 35210485489991680 Bool.false

noncomputable abbrev qz7 := (@HPow.hPow Complex Complex Complex qz274 (@Nat.cast Complex Complex.instNatCast 7) qz275)

noncomputable def ep40 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 8) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 7) qz7) Bool.false 878032596179 274877906944 76658896002429 35210485489991680 Bool.true 27575262023 274877906944 76537959463409 35210485489991680

noncomputable def ep41 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 7) qz7 Bool.false 398224147295 137438953472 16764870939913 8802621372497920 Bool.false 18376106437 137438953472 16737425561403 8802621372497920 Bool.false

noncomputable abbrev qz8 := (@HPow.hPow Complex Complex Complex qz274 (@Nat.cast Complex Complex.instNatCast 6) qz275)

noncomputable def ep42 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 7) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 6) qz8) Bool.false 398224147295 137438953472 16764870939913 8802621372497920 Bool.false 18376106437 137438953472 16737425561403 8802621372497920

noncomputable def ep43 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 6) qz8 Bool.false 714750678485 274877906944 56699079121507 35210485489991680 Bool.true 20089270331 137438953472 14148037602803 8802621372497920 Bool.false

noncomputable abbrev qz9 := (@HPow.hPow Complex Complex Complex qz274 (@Nat.cast Complex Complex.instNatCast 5) qz275)

noncomputable def ep44 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 6) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 5) qz9) Bool.false 714750678485 274877906944 56699079121507 35210485489991680 Bool.true 20089270331 137438953472 14148037602803 8802621372497920

noncomputable def ep45 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 5) qz9 Bool.false 711934705795 274877906944 45401801203397 35210485489991680 Bool.false 10339798211 34359738368 22614634959901 17605242744995840 Bool.false

noncomputable abbrev qz10 := (@HPow.hPow Complex Complex Complex qz274 (@Nat.cast Complex Complex.instNatCast 4) qz275)

noncomputable def ep46 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 5) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 4) qz10) Bool.false 711934705795 274877906944 45401801203397 35210485489991680 Bool.false 10339798211 34359738368 22614634959901 17605242744995840

noncomputable def ep47 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 4) qz10 Bool.false 287983318349 137438953472 1635320459523 1760524274499584 Bool.false 25692032725 68719476736 3259052087539 3521048548999168 Bool.false

noncomputable abbrev qz507 := (@Nat.cast Complex Complex.instNatCast 3)

noncomputable abbrev qz276 := qz507

noncomputable abbrev qz11 := (@HPow.hPow Complex Complex Complex qz274 qz276 qz275)

noncomputable def ep48 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 4) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 3) qz11) Bool.false 287983318349 137438953472 1635320459523 1760524274499584 Bool.false 25692032725 68719476736 3259052087539 3521048548999168

noncomputable def ep49 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 3) qz11 Bool.false 58590659471 34359738368 1799410796421 3521048548999168 Bool.true 1776945645 34359738368 1786997417399 3521048548999168 Bool.false

noncomputable abbrev qz508 := (@Nat.cast Complex Complex.instNatCast 2)

noncomputable abbrev qz277 := qz508

noncomputable abbrev qz12 := (@HPow.hPow Complex Complex Complex qz274 qz277 qz275)

noncomputable def ep50 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 3) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 2) qz12) Bool.false 58590659471 34359738368 1799410796421 3521048548999168 Bool.true 1776945645 34359738368 1786997417399 3521048548999168

noncomputable def ep51 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 2) qz12 Bool.false 1 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable abbrev qz278 := (Enclosure.sfrac Bool.false 0 1)

noncomputable abbrev qz13 := qz278

noncomputable def ep52 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 2) (Complex.mk (Enclosure.sfrac Bool.false 1 1) qz13) Bool.false 1 1 0 1 Bool.false 0 1 0 1 (BSN.head_sum_c_two qz5)

noncomputable abbrev qz279 := (@Nat.cast Real Real.instNatCast 2)

noncomputable abbrev qz14 := (@Inv.inv Real Real.instInv (Real.sqrt qz279))

noncomputable abbrev qz529 := (Enclosure.sfrac Bool.false 90753 1000)

noncomputable abbrev qz509 := qz529

noncomputable abbrev qz280 := qz509

noncomputable abbrev qz281 := (Enclosure.sfrac Bool.false 2 1)

noncomputable abbrev qz15 := (@HMul.hMul Real Real Real qz267 qz280 (Real.log qz281))

noncomputable abbrev qz16 := qz280

noncomputable abbrev qz282 := (@Eq.refl Real qz509)

noncomputable abbrev qz17 := qz282

noncomputable def ep53 := @Enclosure.Complex.IsNear.of_eq qz12 (Complex.mk (@HMul.hMul Real Real Real qz0 qz14 (Real.cos qz15)) (@HMul.hMul Real Real Real qz0 qz14 (@Neg.neg Real Real.instNeg (Real.sin qz15)))) Bool.false 24230921103 34359738368 1799410796421 3521048548999168 Bool.true 1776945645 34359738368 1786997417399 3521048548999168 (BSN.cpow_neg_s_mk qz16 90753 1000 2 qz17 rfl)

noncomputable abbrev qz18 := (@Nat.cast Real Real.instNatCast 1)

noncomputable def ep54 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz279) 741455 524288 1 524288 185363 185365 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz279) (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz279 qz18)) Bool.false 741455 524288 1 524288 (BSN.sqrt_natCast_div_one 2) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz279 qz18)) Bool.false 741455 524288 1 524288 741455 524288 1 524288 (BSN.sqrt_enclosure 2 1 370727 370728 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep55 := BSN.log_dyadic_bound 1 3 6 5 613814355 262144 128095 24381081 945 181704 4 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 1) (BSN.artanhQ 3) 0 5 24381081 613814355 945 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep56 := nat_lit 38169219558481359397822218600625

noncomputable def ep57 := nat_lit 31901471898837980949691369446728269824

noncomputable def ep58 := nat_lit 478522078482569714245370541700924047360

noncomputable abbrev qz283 := (BSN.cosEvenQ 1073741824)

noncomputable abbrev qz284 := (BSN.cosOddQ 1073741824)

noncomputable def ep59 := BSN.cos_dyadic_bound_f 78601045 1073741824 2 1 524288 256441 ep56 ep57 ep56 ep56 ep58 ep56 522883 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 78601045) qz283 0 1 ep56 ep57 ep56 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 78601045) qz284 0 1 ep56 ep58 ep56 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz19 := (@Nat.cast Real Real.instNatCast 262144)

noncomputable abbrev qz20 := (Real.log qz281)

noncomputable abbrev qz21 := (Enclosure.Real.IsNear.const Bool.false 90753 1000)

noncomputable abbrev qz285 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 16490183) qz19)

noncomputable abbrev qz286 := (BSN.isNear_log_sfrac 2 1 181704 262144 1 128095 Bool.false (BSN.logfrac_isNear 4 2 1 2 1 181704 262144 128095 rfl rfl rfl (ep55 rfl)))

noncomputable abbrev qz287 := (@Nat.cast Real Real.instNatCast 2765528427569690443776)

noncomputable abbrev qz288 := (@Nat.cast Real Real.instNatCast 37778931862957161709568)

noncomputable def ep60 := @Enclosure.Real.IsNear.cos_image qz15 qz285 Bool.false 16490183 262144 93 131072 Bool.false 522883 524288 1 128095 (@Enclosure.Real.IsNear.recentre' qz15 Bool.false 2061272889 32768000 90753 128095000 16490183 262144 93 131072 (@Enclosure.Real.IsNear.mulLit_ff qz16 qz20 90753 1000 0 1 181704 262144 1 128095 2061272889 32768000 90753 128095000 qz21 qz286 rfl) rfl) (Enclosure.sfrac_false_div 16490183 262144) (BSN.cos_reduce0 qz285 (@HDiv.hDiv Real Real Real qz1 qz287 qz288) 226375608064910080 72057594037927936 Bool.false 522883 524288 10 1000000000000000 256190 128095 (BSN.sin_reduce_arg_pos_rat_q0 16490183 262144 226375608064910080 72057594037927936 10 2765528427569690443776 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 522883 524288 2765528427569690443776 37778931862957161709568 78601045 1073741824 256441 256190 (ep59 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz289 := (BSN.sinEvenQ 1073741824)

noncomputable abbrev qz290 := (BSN.sinOddQ 1073741824)

noncomputable def ep61 := BSN.sin_dyadic_bound_f 78601045 1073741824 1 0 524288 256441 0 1 1 0 1 1 38345 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 78601045) qz289 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 78601045) qz290 0 0 rfl) rfl rfl

noncomputable def ep62 := @Enclosure.Real.IsNear.sin_image qz15 qz285 Bool.false 16490183 262144 93 131072 Bool.false 38345 524288 1 128095 (@Enclosure.Real.IsNear.recentre' qz15 Bool.false 2061272889 32768000 90753 128095000 16490183 262144 93 131072 (@Enclosure.Real.IsNear.mulLit_ff qz16 qz20 90753 1000 0 1 181704 262144 1 128095 2061272889 32768000 90753 128095000 qz21 qz286 rfl) rfl) (Enclosure.sfrac_false_div 16490183 262144) (BSN.sin_reduce0 qz285 (@HDiv.hDiv Real Real Real qz1 qz287 qz288) 226375608064910080 72057594037927936 Bool.false 38345 524288 10 1000000000000000 256190 128095 (BSN.sin_reduce_arg_pos_rat_q0 16490183 262144 226375608064910080 72057594037927936 10 2765528427569690443776 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 38345 524288 2765528427569690443776 37778931862957161709568 78601045 1073741824 256441 256190 (ep61 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz291 := (@Enclosure.Real.IsNear.recentre' qz14 Bool.false 370728 524288 2 524288 46341 65536 1 262144 (ep54 rfl rfl) rfl)

noncomputable def ep63 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz14 (Real.cos qz15)) (@HMul.hMul Real Real Real qz0 qz14 (@Neg.neg Real Real.instNeg (Real.sin qz15))) Bool.false 24230921103 34359738368 1799410796421 3521048548999168 Bool.true 1776945645 34359738368 1786997417399 3521048548999168 (@Enclosure.Real.IsNear.mulLit_ff qz14 (Real.cos qz15) 46341 65536 1 262144 522883 524288 12043907 16789667840 24230921103 34359738368 1799410796421 3521048548999168 qz291 (@Enclosure.Real.IsNear.recentre' (Real.cos qz15) Bool.false 522883 524288 12043907 16789667840 522883 524288 12043907 16789667840 (ep60 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz14 (@Neg.neg Real Real.instNeg (Real.sin qz15)) 46341 65536 1 262144 38345 524288 12043907 16789667840 1776945645 34359738368 1786997417399 3521048548999168 qz291 (@Enclosure.Real.IsNear.neg (Real.sin qz15) Bool.false 38345 524288 12043907 16789667840 (@Enclosure.Real.IsNear.recentre' (Real.sin qz15) Bool.false 38345 524288 12043907 16789667840 38345 524288 12043907 16789667840 (ep62 rfl rfl) rfl)) rfl)

noncomputable abbrev qz292 := (Enclosure.Real.IsNear.const Bool.false 0 1)

noncomputable abbrev qz22 := qz292

noncomputable def ep64 := @ep51 24230921103 34359738368 1799410796421 3521048548999168 Bool.true 1776945645 34359738368 1786997417399 3521048548999168 Bool.false 58590659471 58590659471 34359738368 1799410796421 3521048548999168 Bool.true 1776945645 1776945645 34359738368 1786997417399 3521048548999168 (ep52 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 1) qz13 Bool.false 1 1 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 1) qz22)) (ep53 ep63) rfl rfl

noncomputable abbrev qz293 := (@Nat.cast Real Real.instNatCast 3)

noncomputable abbrev qz23 := (@Inv.inv Real Real.instInv (Real.sqrt qz293))

noncomputable abbrev qz24 := (@HMul.hMul Real Real Real qz267 qz280 (Real.log (Enclosure.sfrac Bool.false 3 1)))

noncomputable def ep65 := @Enclosure.Complex.IsNear.of_eq qz11 (Complex.mk (@HMul.hMul Real Real Real qz0 qz23 (Real.cos qz24)) (@HMul.hMul Real Real Real qz0 qz23 (@Neg.neg Real Real.instNeg (Real.sin qz24)))) Bool.false 53620680465 137438953472 1471230122625 3521048548999168 Bool.false 29245924015 68719476736 368013667535 880262137249792 (BSN.cpow_neg_s_mk qz16 90753 1000 3 qz17 rfl)

noncomputable def ep66 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz293) 908093 524288 1 524288 151348 151350 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz293) (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz293 qz18)) Bool.false 908093 524288 1 524288 (BSN.sqrt_natCast_div_one 3) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz293 qz18)) Bool.false 908093 524288 1 524288 908093 524288 1 524288 (BSN.sqrt_enclosure 3 1 454046 454047 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep67 := BSN.log_dyadic_bound 1 2 10 9 171633298636800 262144 128095 16925142283965 34459425 287994 3 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base9 (BSN.artanhP 1) (BSN.artanhQ 2) 0 9 16925142283965 171633298636800 34459425 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep68 := nat_lit 402864491377854441139192920100000000

noncomputable def ep69 := nat_lit 159507359494189904748456847233641349120

noncomputable def ep70 := nat_lit 1116551516459329333239197930635489443840

noncomputable def ep71 := BSN.sin_dyadic_bound_f 796690700 1073741824 2 1 524288 256441 ep68 ep69 ep68 ep68 ep70 ep68 354285 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 796690700) qz289 0 1 ep68 ep69 ep68 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 796690700) qz290 0 1 ep68 ep70 ep68 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz25 := (Real.log (Enclosure.sfrac Bool.false 3 1))

noncomputable abbrev qz294 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 26136319) qz19)

noncomputable abbrev qz295 := (BSN.isNear_log_sfrac 3 1 287994 262144 1 128095 Bool.false (BSN.logfrac_isNear 3 1 2 3 1 287994 262144 128095 rfl rfl rfl (ep67 rfl)))

noncomputable def ep72 := @Enclosure.Real.IsNear.cos_image qz24 qz294 Bool.false 26136319 262144 373 524288 Bool.false 354285 524288 1 128095 (@Enclosure.Real.IsNear.recentre' qz24 Bool.false 13068159741 131072000 90753 128095000 26136319 262144 373 524288 (@Enclosure.Real.IsNear.mulLit_ff qz16 qz25 90753 1000 0 1 287994 262144 1 128095 13068159741 131072000 90753 128095000 qz21 qz295 rfl) rfl) (Enclosure.sfrac_false_div 26136319 262144) (BSN.cos_reduce3 qz294 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 28031062059794623889408) qz288) 226375608064910080 72057594037927936 Bool.false 354285 524288 15 1000000000000000 256190 128095 (BSN.sin_reduce_arg_pos_rat_q3 26136319 262144 226375608064910080 72057594037927936 15 28031062059794623889408 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 354285 524288 28031062059794623889408 37778931862957161709568 796690700 1073741824 256441 256190 (ep71 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep73 := nat_lit 899800217349532703938620246886056147101759012498396200625639114368000000000

noncomputable def ep74 := nat_lit 71239273651864456168798555229954474558164150722024956391463162036118429368320

noncomputable def ep75 := nat_lit 162299798413137355346034810502392145250460997205964984010000000000000000

noncomputable def ep76 := nat_lit 2699076052451771837105168671037163657014776115500776671908897343104000000000

noncomputable def ep77 := nat_lit 3205767314333900527595934985347951355117386782491123037615842291625329321574400

noncomputable def ep78 := BSN.cos_dyadic_bound_f 796690700 1073741824 3 2 524288 256441 ep73 ep74 ep75 ep76 ep77 ep75 386470 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 796690700) qz283 0 2 ep73 ep74 ep75 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 796690700) qz284 0 2 ep76 ep77 ep75 rfl rfl rfl rfl) rfl rfl

noncomputable def ep79 := @Enclosure.Real.IsNear.sin_image qz24 qz294 Bool.false 26136319 262144 373 524288 Bool.true 386470 524288 1 128095 (@Enclosure.Real.IsNear.recentre' qz24 Bool.false 13068159741 131072000 90753 128095000 26136319 262144 373 524288 (@Enclosure.Real.IsNear.mulLit_ff qz16 qz25 90753 1000 0 1 287994 262144 1 128095 13068159741 131072000 90753 128095000 qz21 qz295 rfl) rfl) (Enclosure.sfrac_false_div 26136319 262144) (BSN.sin_reduce3 qz294 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 28031062059794623889408) qz288) 226375608064910080 72057594037927936 Bool.false 386470 524288 15 1000000000000000 256190 128095 (BSN.sin_reduce_arg_pos_rat_q3 26136319 262144 226375608064910080 72057594037927936 15 28031062059794623889408 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 386470 524288 28031062059794623889408 37778931862957161709568 796690700 1073741824 256441 256190 (ep78 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz296 := (@Enclosure.Real.IsNear.recentre' qz23 Bool.false 302698 524288 2 524288 151349 262144 1 262144 (ep66 rfl rfl) rfl)

noncomputable def ep80 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz23 (Real.cos qz24)) (@HMul.hMul Real Real Real qz0 qz23 (@Neg.neg Real Real.instNeg (Real.sin qz24))) Bool.false 53620680465 137438953472 1471230122625 3521048548999168 Bool.false 29245924015 68719476736 368013667535 880262137249792 (@Enclosure.Real.IsNear.mulLit_ff qz23 (Real.cos qz24) 151349 262144 1 262144 354285 524288 48303723 67158671360 53620680465 137438953472 1471230122625 3521048548999168 qz296 (@Enclosure.Real.IsNear.recentre' (Real.cos qz24) Bool.false 354285 524288 48303723 67158671360 354285 524288 48303723 67158671360 (ep72 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz23 (@Neg.neg Real Real.instNeg (Real.sin qz24)) 151349 262144 1 262144 193235 262144 48303723 67158671360 29245924015 68719476736 368013667535 880262137249792 qz296 (@Enclosure.Real.IsNear.neg (Real.sin qz24) Bool.true 193235 262144 48303723 67158671360 (@Enclosure.Real.IsNear.recentre' (Real.sin qz24) Bool.true 386470 524288 48303723 67158671360 193235 262144 48303723 67158671360 (ep79 rfl rfl) rfl)) rfl)

noncomputable def ep81 := @ep49 53620680465 137438953472 1471230122625 3521048548999168 Bool.false 29245924015 68719476736 368013667535 880262137249792 Bool.false 9895031472820093714432 287983318349 137438953472 1635320459523 1760524274499584 Bool.false 882771522573094092800 25692032725 68719476736 3259052087539 3521048548999168 (ep50 (BSN.head_sum_c_succ qz5 2 3 rfl rfl) (ep64 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep65 ep80) rfl rfl

noncomputable abbrev qz297 := (@Nat.cast Real Real.instNatCast 4)

noncomputable abbrev qz26 := (@Inv.inv Real Real.instInv (Real.sqrt qz297))

noncomputable abbrev qz27 := (@HMul.hMul Real Real Real qz267 qz280 (Real.log (Enclosure.sfrac Bool.false 4 1)))

noncomputable def ep82 := @Enclosure.Complex.IsNear.of_eq qz10 (Complex.mk (@HMul.hMul Real Real Real qz0 qz26 (Real.cos qz27)) (@HMul.hMul Real Real Real qz0 qz26 (@Neg.neg Real Real.instNeg (Real.sin qz27)))) Bool.false 135968069097 274877906944 12695392012937 35210485489991680 Bool.true 5012436303 68719476736 3159687261103 8802621372497920 (BSN.cpow_neg_s_mk qz16 90753 1000 4 qz17 rfl)

noncomputable def ep83 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz297) 1048577 524288 1 524288 131071 131072 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz297) (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz297 qz18)) Bool.false 1048577 524288 1 524288 (BSN.sqrt_natCast_div_one 4) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz297 qz18)) Bool.false 1048577 524288 1 524288 1048577 524288 1 524288 (BSN.sqrt_enclosure 4 1 524288 524289 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep84 := nat_lit 318077276165597140789031982421875

noncomputable def ep85 := nat_lit 49379992292270016474244603430625

noncomputable def ep86 := nat_lit 20095619060363156210525625

noncomputable def ep87 := BSN.log_dyadic_bound 3 5 14 13 ep84 262144 128095 ep85 ep86 363408 8 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base13 (BSN.artanhP 3) (BSN.artanhQ 5) 0 13 ep85 ep84 ep86 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep88 := nat_lit 610707512935701750365155497610000

noncomputable def ep89 := BSN.cos_dyadic_bound_f 157202090 1073741824 2 1 524288 256441 ep88 ep57 ep88 ep88 ep58 ep88 518679 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 157202090) qz283 0 1 ep88 ep57 ep88 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 157202090) qz284 0 1 ep88 ep58 ep88 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz28 := (Real.log (Enclosure.sfrac Bool.false 4 1))

noncomputable abbrev qz298 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 16490183) (@Nat.cast Real Real.instNatCast 131072))

noncomputable abbrev qz299 := (BSN.isNear_log_sfrac 4 1 363408 262144 1 128095 Bool.false (BSN.logfrac_isNear 8 2 1 4 1 363408 262144 128095 rfl rfl rfl (ep87 rfl)))

noncomputable abbrev qz300 := (@Nat.cast Real Real.instNatCast 18889465931478580854784)

noncomputable def ep90 := @Enclosure.Real.IsNear.cos_image qz27 qz298 Bool.false 16490183 131072 93 131072 Bool.false 518679 524288 1 128095 (@Enclosure.Real.IsNear.recentre' qz27 Bool.false 2061272889 16384000 90753 128095000 16490183 131072 93 131072 (@Enclosure.Real.IsNear.mulLit_ff qz16 qz28 90753 1000 0 1 363408 262144 1 128095 2061272889 16384000 90753 128095000 qz21 qz299 rfl) rfl) (Enclosure.sfrac_false_div 16490183 131072) (BSN.cos_reduce0 qz298 (@HDiv.hDiv Real Real Real qz1 qz287 qz300) 226375608064910080 72057594037927936 Bool.false 518679 524288 20 1000000000000000 256190 128095 (BSN.sin_reduce_arg_pos_rat_q0 16490183 131072 226375608064910080 72057594037927936 20 2765528427569690443776 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 518679 524288 2765528427569690443776 18889465931478580854784 157202090 1073741824 256441 256190 (ep89 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep91 := BSN.sin_dyadic_bound_f 157202090 1073741824 1 0 524288 256441 0 1 1 0 1 1 76484 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 157202090) qz289 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 157202090) qz290 0 0 rfl) rfl rfl

noncomputable def ep92 := @Enclosure.Real.IsNear.sin_image qz27 qz298 Bool.false 16490183 131072 93 131072 Bool.false 76484 524288 1 128095 (@Enclosure.Real.IsNear.recentre' qz27 Bool.false 2061272889 16384000 90753 128095000 16490183 131072 93 131072 (@Enclosure.Real.IsNear.mulLit_ff qz16 qz28 90753 1000 0 1 363408 262144 1 128095 2061272889 16384000 90753 128095000 qz21 qz299 rfl) rfl) (Enclosure.sfrac_false_div 16490183 131072) (BSN.sin_reduce0 qz298 (@HDiv.hDiv Real Real Real qz1 qz287 qz300) 226375608064910080 72057594037927936 Bool.false 76484 524288 20 1000000000000000 256190 128095 (BSN.sin_reduce_arg_pos_rat_q0 16490183 131072 226375608064910080 72057594037927936 20 2765528427569690443776 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 76484 524288 2765528427569690443776 18889465931478580854784 157202090 1073741824 256441 256190 (ep91 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz301 := (@Enclosure.Real.IsNear.recentre' qz26 Bool.false 262143 524288 1 524288 262143 524288 1 524288 (ep83 rfl rfl) rfl)

noncomputable def ep93 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz26 (Real.cos qz27)) (@HMul.hMul Real Real Real qz0 qz26 (@Neg.neg Real Real.instNeg (Real.sin qz27))) Bool.false 135968069097 274877906944 12695392012937 35210485489991680 Bool.true 5012436303 68719476736 3159687261103 8802621372497920 (@Enclosure.Real.IsNear.mulLit_ff qz26 (Real.cos qz27) 262143 524288 1 524288 518679 524288 12043907 16789667840 135968069097 274877906944 12695392012937 35210485489991680 qz301 (@Enclosure.Real.IsNear.recentre' (Real.cos qz27) Bool.false 518679 524288 12043907 16789667840 518679 524288 12043907 16789667840 (ep90 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz26 (@Neg.neg Real Real.instNeg (Real.sin qz27)) 262143 524288 1 524288 19121 131072 12043907 16789667840 5012436303 68719476736 3159687261103 8802621372497920 qz301 (@Enclosure.Real.IsNear.neg (Real.sin qz27) Bool.false 19121 131072 12043907 16789667840 (@Enclosure.Real.IsNear.recentre' (Real.sin qz27) Bool.false 76484 524288 12043907 16789667840 19121 131072 12043907 16789667840 (ep92 rfl rfl) rfl)) rfl)

noncomputable def ep94 := @ep47 135968069097 274877906944 12695392012937 35210485489991680 Bool.true 5012436303 68719476736 3159687261103 8802621372497920 Bool.false 97847560904861013770240 711934705795 274877906944 45401801203397 35210485489991680 Bool.false 1421091045231497838592 10339798211 34359738368 22614634959901 17605242744995840 (ep48 (BSN.head_sum_c_succ qz5 3 4 rfl rfl) (ep81 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep82 ep93) rfl rfl

noncomputable abbrev qz302 := (@Nat.cast Real Real.instNatCast 5)

noncomputable abbrev qz29 := (@Inv.inv Real Real.instInv (Real.sqrt qz302))

noncomputable abbrev qz30 := (@HMul.hMul Real Real Real qz267 qz280 (Real.log (Enclosure.sfrac Bool.false 5 1)))

noncomputable def ep95 := @Enclosure.Complex.IsNear.of_eq qz9 (Complex.mk (@HMul.hMul Real Real Real qz0 qz29 (Real.cos qz30)) (@HMul.hMul Real Real Real qz0 qz29 (@Neg.neg Real Real.instNeg (Real.sin qz30)))) Bool.false 1407986345 137438953472 1129727791811 3521048548999168 Bool.true 61448463175 137438953472 1136288049141 3521048548999168 (BSN.cpow_neg_s_mk qz16 90753 1000 5 qz17 rfl)

noncomputable def ep96 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz302) 1172343 524288 1 524288 117234 117235 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz302) (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz302 qz18)) Bool.false 1172343 524288 1 524288 (BSN.sqrt_natCast_div_one 5) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz302 qz18)) Bool.false 1172343 524288 1 524288 1172343 524288 1 524288 (BSN.sqrt_enclosure 5 1 586171 586172 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep97 := nat_lit 11734546589655452485523914939250625

noncomputable def ep98 := nat_lit 2429970938528035899633153341031900

noncomputable def ep99 := nat_lit 824199001261152424427520000

noncomputable def ep100 := BSN.log_dyadic_bound 2 3 17 16 ep97 262144 128095 ep98 ep99 421904 5 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base16 (BSN.artanhP 2) (BSN.artanhQ 3) 0 16 ep98 ep97 ep99 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep101 := nat_lit 17097994243407839456135547488003606775124251122594040885994261988400209423521

noncomputable def ep102 := nat_lit 58225053035468334353592355190318974722378021184944023586694491841766190241

noncomputable def ep103 := nat_lit 51177532624152581699699457753630182375927997325412234610809396981517095890081

noncomputable def ep104 := BSN.cos_dyadic_bound_f 1662029533 1073741824 3 2 524288 256441 ep101 ep74 ep102 ep103 ep77 ep102 12010 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1662029533) qz283 0 2 ep101 ep74 ep102 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1662029533) qz284 0 2 ep103 ep77 ep102 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz31 := (@Nat.cast Real Real.instNatCast 524288)

noncomputable abbrev qz32 := (Real.log (Enclosure.sfrac Bool.false 5 1))

noncomputable abbrev qz33 := (@Nat.cast Real Real.instNatCast 75557863725914323419136)

noncomputable abbrev qz303 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 76578107) qz31)

noncomputable abbrev qz304 := (BSN.isNear_log_sfrac 5 1 421904 262144 1 128095 Bool.false (BSN.logfrac_isNear 5 1 2 5 1 421904 262144 128095 rfl rfl rfl (ep100 rfl)))

noncomputable def ep105 := @Enclosure.Real.IsNear.cos_image qz30 qz303 Bool.false 76578107 524288 93 131072 Bool.false 12010 524288 1 128095 (@Enclosure.Real.IsNear.recentre' qz30 Bool.false 2393065857 16384000 90753 128095000 76578107 524288 93 131072 (@Enclosure.Real.IsNear.mulLit_ff qz16 qz32 90753 1000 0 1 421904 262144 1 128095 2393065857 16384000 90753 128095000 qz21 qz304 rfl) rfl) (Enclosure.sfrac_false_div 76578107 524288) (BSN.cos_reduce0 qz303 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 116954931093542088474624) qz33) 226375608064910080 72057594037927936 Bool.false 12010 524288 23 1000000000000000 256190 128095 (BSN.sin_reduce_arg_pos_rat_q0 76578107 524288 226375608064910080 72057594037927936 23 116954931093542088474624 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 12010 524288 116954931093542088474624 75557863725914323419136 1662029533 1073741824 256441 256190 (ep104 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep106 := nat_lit 30729809595705736353561111594254237015445749603721318375920315985646964010145

noncomputable def ep107 := nat_lit 641153462866780105519186997069590271023477356498224607523168458325065864314880

noncomputable def ep108 := nat_lit 80388565521933789337039952267024390033759779784970686374936655547045855718561

noncomputable def ep109 := nat_lit 11754480152557635267851761612942488302097084869134117804591421735959540845772800

noncomputable def ep110 := BSN.sin_dyadic_bound_f 1662029533 1073741824 3 2 524288 256441 ep106 ep107 ep102 ep108 ep109 ep102 524150 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1662029533) qz289 0 2 ep106 ep107 ep102 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1662029533) qz290 0 2 ep108 ep109 ep102 rfl rfl rfl rfl) rfl rfl

noncomputable def ep111 := @Enclosure.Real.IsNear.sin_image qz30 qz303 Bool.false 76578107 524288 93 131072 Bool.false 524150 524288 1 128095 (@Enclosure.Real.IsNear.recentre' qz30 Bool.false 2393065857 16384000 90753 128095000 76578107 524288 93 131072 (@Enclosure.Real.IsNear.mulLit_ff qz16 qz32 90753 1000 0 1 421904 262144 1 128095 2393065857 16384000 90753 128095000 qz21 qz304 rfl) rfl) (Enclosure.sfrac_false_div 76578107 524288) (BSN.sin_reduce0 qz303 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 116954931093542088474624) qz33) 226375608064910080 72057594037927936 Bool.false 524150 524288 23 1000000000000000 256190 128095 (BSN.sin_reduce_arg_pos_rat_q0 76578107 524288 226375608064910080 72057594037927936 23 116954931093542088474624 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 524150 524288 116954931093542088474624 75557863725914323419136 1662029533 1073741824 256441 256190 (ep110 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz305 := (@Enclosure.Real.IsNear.recentre' qz29 Bool.false 234469 524288 1 524288 234469 524288 1 524288 (ep96 rfl rfl) rfl)

noncomputable def ep112 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz29 (Real.cos qz30)) (@HMul.hMul Real Real Real qz0 qz29 (@Neg.neg Real Real.instNeg (Real.sin qz30))) Bool.false 1407986345 137438953472 1129727791811 3521048548999168 Bool.true 61448463175 137438953472 1136288049141 3521048548999168 (@Enclosure.Real.IsNear.mulLit_ff qz29 (Real.cos qz30) 234469 524288 1 524288 6005 262144 12043907 16789667840 1407986345 137438953472 1129727791811 3521048548999168 qz305 (@Enclosure.Real.IsNear.recentre' (Real.cos qz30) Bool.false 12010 524288 12043907 16789667840 6005 262144 12043907 16789667840 (ep105 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz29 (@Neg.neg Real Real.instNeg (Real.sin qz30)) 234469 524288 1 524288 262075 262144 12043907 16789667840 61448463175 137438953472 1136288049141 3521048548999168 qz305 (@Enclosure.Real.IsNear.neg (Real.sin qz30) Bool.false 262075 262144 12043907 16789667840 (@Enclosure.Real.IsNear.recentre' (Real.sin qz30) Bool.false 524150 524288 12043907 16789667840 262075 262144 12043907 16789667840 (ep111 rfl rfl) rfl)) rfl)

noncomputable def ep113 := @ep45 1407986345 137438953472 1129727791811 3521048548999168 Bool.true 61448463175 137438953472 1136288049141 3521048548999168 Bool.false 98234585244380346449920 714750678485 274877906944 56699079121507 35210485489991680 Bool.true 690262072577184759808 20089270331 137438953472 14148037602803 8802621372497920 (ep46 (BSN.head_sum_c_succ qz5 4 5 rfl rfl) (ep94 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep95 ep112) rfl rfl

noncomputable abbrev qz306 := (@Nat.cast Real Real.instNatCast 6)

noncomputable abbrev qz34 := (@Inv.inv Real Real.instInv (Real.sqrt qz306))

noncomputable abbrev qz307 := (Real.log (Enclosure.sfrac Bool.false 6 1))

noncomputable abbrev qz35 := (@HMul.hMul Real Real Real qz267 qz280 qz307)

noncomputable def ep114 := @Enclosure.Complex.IsNear.of_eq qz8 (Complex.mk (@HMul.hMul Real Real Real qz0 qz34 (Real.cos qz35)) (@HMul.hMul Real Real Real qz0 qz34 (@Neg.neg Real Real.instNeg (Real.sin qz35)))) Bool.false 81697616105 274877906944 2072080927629 7042097097998336 Bool.false 75127689 268435456 64734698965 220065534312448 (BSN.cpow_neg_s_mk qz16 90753 1000 6 qz17 rfl)

noncomputable abbrev qz308 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 6) qz18)

noncomputable def ep115 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz306) 1284239 524288 1 524288 107019 107020 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz306) (Real.sqrt qz308) Bool.false 1284239 524288 1 524288 (BSN.sqrt_natCast_div_one 6) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz308) Bool.false 1284239 524288 1 524288 1284239 524288 1 524288 (BSN.sqrt_enclosure 6 1 642119 642120 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep116 := BSN.log_dyadic_bound 2 10 4 3 105000000 262144 128095 1434560 960 106290 12 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 2) (BSN.artanhQ 10) 0 3 1434560 105000000 960 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep117 := @Enclosure.Real.IsNear.mulLit_ff qz16 qz307 90753 1000 0 1 4034681531866359 2251799813685248 100000000025619 12809500000000000000 366159453061467678327 2251799813685248000 9075300002325001107 12809500000000000000000 qz21 (BSN.isNear_log_sfrac 6 1 4034681531866359 2251799813685248 100000000025619 12809500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz308) Bool.false 16922680887833197019136 9444732965739290427392 1000000000256190 128095000000000000000 4034681531866359 2251799813685248 100000000025619 12809500000000000000 (BSN.log_rat_reduce_isNear 6 1 2 12 8 106290 262144 24973259072661432 36028797018963968 128095 1000000000000000 rfl rfl rfl rfl (ep116 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep118 := nat_lit 587716790084778288943662165621795856

noncomputable def ep119 := BSN.sin_dyadic_bound_f 875572322 1073741824 2 1 524288 256441 ep118 ep69 ep118 ep118 ep70 ep118 381695 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 875572322) qz289 0 1 ep118 ep69 ep118 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 875572322) qz290 0 1 ep118 ep70 ep118 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz309 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 85253141) qz31)

noncomputable def ep120 := @Enclosure.Real.IsNear.cos_image qz35 qz309 Bool.false 85253141 524288 93 131072 Bool.false 381695 524288 1 128095 (@Enclosure.Real.IsNear.recentre' qz35 Bool.false 366159453061467678327 2251799813685248000 9075300002325001107 12809500000000000000000 85253141 524288 93 131072 (ep117 rfl) rfl) (Enclosure.sfrac_false_div 85253141 524288) (BSN.cos_reduce3 qz309 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 61612924755495020920832) qz33) 226375608064910080 72057594037927936 Bool.false 381695 524288 25 1000000000000000 256190 128095 (BSN.sin_reduce_arg_pos_rat_q3 85253141 524288 226375608064910080 72057594037927936 25 61612924755495020920832 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 381695 524288 61612924755495020920832 75557863725914323419136 875572322 1073741824 256441 256190 (ep119 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep121 := nat_lit 1312777557460884612081796299632411935624410068829559307451954799189452226816

noncomputable def ep122 := nat_lit 345411025347555347686510595923595499641319379140366728708606566538772736

noncomputable def ep123 := nat_lit 3937641850331958725550015877705388615873947567730397188898447184435279134976

noncomputable def ep124 := BSN.cos_dyadic_bound_f 875572322 1073741824 3 2 524288 256441 ep121 ep74 ep122 ep123 ep77 ep122 359424 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 875572322) qz283 0 2 ep121 ep74 ep122 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 875572322) qz284 0 2 ep123 ep77 ep122 rfl rfl rfl rfl) rfl rfl

noncomputable def ep125 := @Enclosure.Real.IsNear.sin_image qz35 qz309 Bool.false 85253141 524288 93 131072 Bool.true 359424 524288 1 128095 (@Enclosure.Real.IsNear.recentre' qz35 Bool.false 366159453061467678327 2251799813685248000 9075300002325001107 12809500000000000000000 85253141 524288 93 131072 (ep117 rfl) rfl) (Enclosure.sfrac_false_div 85253141 524288) (BSN.sin_reduce3 qz309 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 61612924755495020920832) qz33) 226375608064910080 72057594037927936 Bool.false 359424 524288 25 1000000000000000 256190 128095 (BSN.sin_reduce_arg_pos_rat_q3 85253141 524288 226375608064910080 72057594037927936 25 61612924755495020920832 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 359424 524288 61612924755495020920832 75557863725914323419136 875572322 1073741824 256441 256190 (ep124 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz310 := (@Enclosure.Real.IsNear.recentre' qz34 Bool.false 214039 524288 1 524288 214039 524288 1 524288 (ep115 rfl rfl) rfl)

noncomputable def ep126 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz34 (Real.cos qz35)) (@HMul.hMul Real Real Real qz0 qz34 (@Neg.neg Real Real.instNeg (Real.sin qz35))) Bool.false 81697616105 274877906944 2072080927629 7042097097998336 Bool.false 75127689 268435456 64734698965 220065534312448 (@Enclosure.Real.IsNear.mulLit_ff qz34 (Real.cos qz35) 214039 524288 1 524288 381695 524288 12043907 16789667840 81697616105 274877906944 2072080927629 7042097097998336 qz310 (@Enclosure.Real.IsNear.recentre' (Real.cos qz35) Bool.false 381695 524288 12043907 16789667840 381695 524288 12043907 16789667840 (ep120 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz34 (@Neg.neg Real Real.instNeg (Real.sin qz35)) 214039 524288 1 524288 351 512 12043907 16789667840 75127689 268435456 64734698965 220065534312448 qz310 (@Enclosure.Real.IsNear.neg (Real.sin qz35) Bool.true 351 512 12043907 16789667840 (@Enclosure.Real.IsNear.recentre' (Real.sin qz35) Bool.true 359424 524288 12043907 16789667840 351 512 12043907 16789667840 (ep125 rfl rfl) rfl)) rfl)

noncomputable def ep127 := @ep43 81697616105 274877906944 2072080927629 7042097097998336 Bool.false 75127689 268435456 64734698965 220065534312448 Bool.false 218926040206017518632960 398224147295 137438953472 16764870939913 8802621372497920 Bool.false 4932798510920630272 18376106437 137438953472 16737425561403 8802621372497920 (ep44 (BSN.head_sum_c_succ qz5 5 6 rfl rfl) (ep113 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep114 ep126) rfl rfl

noncomputable abbrev qz311 := (@Nat.cast Real Real.instNatCast 7)

noncomputable abbrev qz36 := (@Inv.inv Real Real.instInv (Real.sqrt qz311))

noncomputable abbrev qz312 := (Real.log (Enclosure.sfrac Bool.false 7 1))

noncomputable abbrev qz37 := (@HMul.hMul Real Real Real qz267 qz280 qz312)

noncomputable def ep128 := @Enclosure.Complex.IsNear.of_eq qz7 (Complex.mk (@HMul.hMul Real Real Real qz0 qz36 (Real.cos qz37)) (@HMul.hMul Real Real Real qz0 qz36 (@Neg.neg Real Real.instNeg (Real.sin qz37)))) Bool.false 81584301589 274877906944 9599412242777 35210485489991680 Bool.true 64327474897 274877906944 9588257217797 35210485489991680 (BSN.cpow_neg_s_mk qz16 90753 1000 7 qz17 rfl)

noncomputable abbrev qz313 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 7) qz18)

noncomputable def ep129 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz311) 1387135 524288 1 524288 99081 99082 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz311) (Real.sqrt qz313) Bool.false 1387135 524288 1 524288 (BSN.sqrt_natCast_div_one 7) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz313) Bool.false 1387135 524288 1 524288 1387135 524288 1 524288 (BSN.sqrt_enclosure 7 1 693567 693568 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep130 := BSN.log_dyadic_bound 3 11 5 4 202569142545 262144 128095 5259111624 688905 146699 14 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 3) (BSN.artanhQ 11) 0 4 5259111624 202569142545 688905 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep131 := @Enclosure.Real.IsNear.mulLit_ff qz16 qz312 90753 1000 0 1 4381792198794487 2251799813685248 100000000025619 12809500000000000000 397660787417196078711 2251799813685248000 9075300002325001107 12809500000000000000000 qz21 (BSN.isNear_log_sfrac 7 1 4381792198794487 2251799813685248 100000000025619 12809500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz313) Bool.false 18378568546572512002048 9444732965739290427392 1000000000256190 128095000000000000000 4381792198794487 2251799813685248 100000000025619 12809500000000000000 (BSN.log_rat_reduce_isNear 7 1 2 14 8 146699 262144 24973259072661432 36028797018963968 128095 1000000000000000 rfl rfl rfl rfl (ep130 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep132 := nat_lit 589960493579786813557846291437469538630522493547230605001186845208279515136

noncomputable def ep133 := nat_lit 69779137495284851307650278875152678127631031715905999027234025825632256

noncomputable def ep134 := nat_lit 1769741922464369870970923573754658310535312218578260003005506067573187280896

noncomputable def ep135 := BSN.cos_dyadic_bound_f 716911752 1073741824 3 2 524288 256441 ep132 ep74 ep133 ep134 ep77 ep133 411703 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 716911752) qz283 0 2 ep132 ep74 ep133 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 716911752) qz284 0 2 ep134 ep77 ep133 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz314 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 92587617) qz31)

noncomputable def ep136 := @Enclosure.Real.IsNear.cos_image qz37 qz314 Bool.false 92587617 524288 93 131072 Bool.false 411703 524288 1 128095 (@Enclosure.Real.IsNear.recentre' qz37 Bool.false 397660787417196078711 2251799813685248000 9075300002325001107 12809500000000000000000 92587617 524288 93 131072 (ep131 rfl) rfl) (Enclosure.sfrac_false_div 92587617 524288) (BSN.cos_reduce0 qz314 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 50448179723125909356544) qz33) 226375608064910080 72057594037927936 Bool.false 411703 524288 28 1000000000000000 256190 128095 (BSN.sin_reduce_arg_pos_rat_q0 92587617 524288 226375608064910080 72057594037927936 28 50448179723125909356544 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 411703 524288 50448179723125909356544 75557863725914323419136 716911752 1073741824 256441 256190 (ep135 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep137 := nat_lit 264157410449309279466685129635926016

noncomputable def ep138 := BSN.sin_dyadic_bound_f 716911752 1073741824 2 1 524288 256441 ep137 ep69 ep137 ep137 ep70 ep137 324619 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 716911752) qz289 0 1 ep137 ep69 ep137 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 716911752) qz290 0 1 ep137 ep70 ep137 rfl rfl rfl rfl) rfl rfl

noncomputable def ep139 := @Enclosure.Real.IsNear.sin_image qz37 qz314 Bool.false 92587617 524288 93 131072 Bool.false 324619 524288 1 128095 (@Enclosure.Real.IsNear.recentre' qz37 Bool.false 397660787417196078711 2251799813685248000 9075300002325001107 12809500000000000000000 92587617 524288 93 131072 (ep131 rfl) rfl) (Enclosure.sfrac_false_div 92587617 524288) (BSN.sin_reduce0 qz314 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 50448179723125909356544) qz33) 226375608064910080 72057594037927936 Bool.false 324619 524288 28 1000000000000000 256190 128095 (BSN.sin_reduce_arg_pos_rat_q0 92587617 524288 226375608064910080 72057594037927936 28 50448179723125909356544 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 324619 524288 50448179723125909356544 75557863725914323419136 716911752 1073741824 256441 256190 (ep138 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz315 := (@Enclosure.Real.IsNear.recentre' qz36 Bool.false 198163 524288 1 524288 198163 524288 1 524288 (ep129 rfl rfl) rfl)

noncomputable def ep140 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz36 (Real.cos qz37)) (@HMul.hMul Real Real Real qz0 qz36 (@Neg.neg Real Real.instNeg (Real.sin qz37))) Bool.false 81584301589 274877906944 9599412242777 35210485489991680 Bool.true 64327474897 274877906944 9588257217797 35210485489991680 (@Enclosure.Real.IsNear.mulLit_ff qz36 (Real.cos qz37) 198163 524288 1 524288 411703 524288 12043907 16789667840 81584301589 274877906944 9599412242777 35210485489991680 qz315 (@Enclosure.Real.IsNear.recentre' (Real.cos qz37) Bool.false 411703 524288 12043907 16789667840 411703 524288 12043907 16789667840 (ep136 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz36 (@Neg.neg Real Real.instNeg (Real.sin qz37)) 198163 524288 1 524288 324619 524288 12043907 16789667840 64327474897 274877906944 9588257217797 35210485489991680 qz315 (@Enclosure.Real.IsNear.neg (Real.sin qz37) Bool.false 324619 524288 12043907 16789667840 (@Enclosure.Real.IsNear.recentre' (Real.sin qz37) Bool.false 324619 524288 12043907 16789667840 324619 524288 12043907 16789667840 (ep139 rfl rfl) rfl)) rfl)

noncomputable def ep141 := @ep41 81584301589 274877906944 9599412242777 35210485489991680 Bool.true 64327474897 274877906944 9588257217797 35210485489991680 Bool.false 120675881133144945983488 878032596179 274877906944 76658896002429 35210485489991680 Bool.true 3789915154157305593856 27575262023 274877906944 76537959463409 35210485489991680 (ep42 (BSN.head_sum_c_succ qz5 6 7 rfl rfl) (ep127 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep128 ep140) rfl rfl

noncomputable abbrev qz316 := (@Nat.cast Real Real.instNatCast 8)

noncomputable abbrev qz38 := (@Inv.inv Real Real.instInv (Real.sqrt qz316))

noncomputable abbrev qz317 := (Real.log (Enclosure.sfrac Bool.false 8 1))

noncomputable abbrev qz39 := (@HMul.hMul Real Real Real qz267 qz280 qz317)

noncomputable def ep142 := @Enclosure.Complex.IsNear.of_eq qz6 (Complex.mk (@HMul.hMul Real Real Real qz0 qz38 (Real.cos qz39)) (@HMul.hMul Real Real Real qz0 qz38 (@Neg.neg Real Real.instNeg (Real.sin qz39)))) Bool.false 94841164313 274877906944 9019311245017 35210485489991680 Bool.true 10604061141 137438953472 4484213585751 17605242744995840 (BSN.cpow_neg_s_mk qz16 90753 1000 8 qz17 rfl)

noncomputable abbrev qz318 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 8) qz18)

noncomputable def ep143 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz316) 1482911 524288 1 524288 92681 92682 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz316) (Real.sqrt qz318) Bool.false 1482911 524288 1 524288 (BSN.sqrt_natCast_div_one 8) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz318) Bool.false 1482911 524288 1 524288 1482911 524288 1 524288 (BSN.sqrt_enclosure 8 1 741455 741456 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep144 := BSN.log_dyadic_bound 0 16 1 0 1 262144 128095 0 1 0 16 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 0) (BSN.artanhQ 16) 0 0 rfl) rfl rfl rfl

noncomputable def ep145 := @Enclosure.Real.IsNear.mulLit_ff qz16 qz317 90753 1000 0 1 9364972152248037 4503599627370496 200000000076857 25619000000000000000 849899317732966101861 4503599627370496000 18150600006975003321 25619000000000000000000 qz21 (BSN.isNear_log_sfrac 8 1 9364972152248037 4503599627370496 200000000076857 25619000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz318) Bool.false 19639770079031275290624 9444732965739290427392 1000000000384285 128095000000000000000 9364972152248037 4503599627370496 200000000076857 25619000000000000000 (BSN.log_rat_reduce_isNear 8 1 3 16 16 0 262144 24973259072661432 36028797018963968 128095 1000000000000000 rfl rfl rfl rfl (ep144 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep146 := nat_lit 3113676473797034833455954427641856

noncomputable def ep147 := BSN.cos_dyadic_bound_f 236220928 1073741824 2 1 524288 256441 ep146 ep57 ep146 ep146 ep58 ep146 511651 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 236220928) qz283 0 1 ep146 ep57 ep146 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 236220928) qz284 0 1 ep146 ep58 ep146 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz319 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 49470651) qz19)

noncomputable def ep148 := @Enclosure.Real.IsNear.cos_image qz39 qz319 Bool.false 49470651 262144 373 524288 Bool.false 511651 524288 1 128095 (@Enclosure.Real.IsNear.recentre' qz39 Bool.false 849899317732966101861 4503599627370496000 18150600006975003321 25619000000000000000000 49470651 262144 373 524288 (ep145 rfl) rfl) (Enclosure.sfrac_false_div 49470651 262144) (BSN.cos_reduce0 qz319 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 8311285031892808630272) qz288) 226375608064910080 72057594037927936 Bool.false 511651 524288 30 1000000000000000 256190 128095 (BSN.sin_reduce_arg_pos_rat_q0 49470651 262144 226375608064910080 72057594037927936 30 8311285031892808630272 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 511651 524288 8311285031892808630272 37778931862957161709568 236220928 1073741824 256441 256190 (ep147 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep149 := BSN.sin_dyadic_bound_f 236220928 1073741824 2 1 524288 256441 ep146 ep69 ep146 ep146 ep70 ep146 114414 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 236220928) qz289 0 1 ep146 ep69 ep146 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 236220928) qz290 0 1 ep146 ep70 ep146 rfl rfl rfl rfl) rfl rfl

noncomputable def ep150 := @Enclosure.Real.IsNear.sin_image qz39 qz319 Bool.false 49470651 262144 373 524288 Bool.false 114414 524288 1 128095 (@Enclosure.Real.IsNear.recentre' qz39 Bool.false 849899317732966101861 4503599627370496000 18150600006975003321 25619000000000000000000 49470651 262144 373 524288 (ep145 rfl) rfl) (Enclosure.sfrac_false_div 49470651 262144) (BSN.sin_reduce0 qz319 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 8311285031892808630272) qz288) 226375608064910080 72057594037927936 Bool.false 114414 524288 30 1000000000000000 256190 128095 (BSN.sin_reduce_arg_pos_rat_q0 49470651 262144 226375608064910080 72057594037927936 30 8311285031892808630272 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 114414 524288 8311285031892808630272 37778931862957161709568 236220928 1073741824 256441 256190 (ep149 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz320 := (@Enclosure.Real.IsNear.recentre' qz38 Bool.false 185363 524288 1 524288 185363 524288 1 524288 (ep143 rfl rfl) rfl)

noncomputable def ep151 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz38 (Real.cos qz39)) (@HMul.hMul Real Real Real qz0 qz38 (@Neg.neg Real Real.instNeg (Real.sin qz39))) Bool.false 94841164313 274877906944 9019311245017 35210485489991680 Bool.true 10604061141 137438953472 4484213585751 17605242744995840 (@Enclosure.Real.IsNear.mulLit_ff qz38 (Real.cos qz39) 185363 524288 1 524288 511651 524288 48303723 67158671360 94841164313 274877906944 9019311245017 35210485489991680 qz320 (@Enclosure.Real.IsNear.recentre' (Real.cos qz39) Bool.false 511651 524288 48303723 67158671360 511651 524288 48303723 67158671360 (ep148 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz38 (@Neg.neg Real Real.instNeg (Real.sin qz39)) 185363 524288 1 524288 57207 262144 48303723 67158671360 10604061141 137438953472 4484213585751 17605242744995840 qz320 (@Enclosure.Real.IsNear.neg (Real.sin qz39) Bool.false 57207 262144 48303723 67158671360 (@Enclosure.Real.IsNear.recentre' (Real.sin qz39) Bool.false 114414 524288 48303723 67158671360 57207 262144 48303723 67158671360 (ep150 rfl rfl) rfl)) rfl)

noncomputable def ep152 := @ep39 94841164313 274877906944 9019311245017 35210485489991680 Bool.true 10604061141 137438953472 4484213585751 17605242744995840 Bool.false 267421503004779319656448 243218440123 68719476736 3894463965793 1600476613181440 Bool.true 6704737285701590056960 48783384305 274877906944 7773307875901 3200953226362880 (ep40 (BSN.head_sum_c_succ qz5 7 8 rfl rfl) (ep141 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep142 ep151) rfl rfl

theorem EMRow26.d6 : Enclosure.Complex.IsNear qz3 Bool.false 243218440123 68719476736 3894463965793 1600476613181440 Bool.true 48783384305 274877906944 7773307875901 3200953226362880 := ep38 (BSN.head_sum_c_succ qz5 8 9 rfl rfl) (ep152 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable abbrev qz40 := (BSN.headSumC qz272 17)

noncomputable abbrev qz41 := (@HPow.hPow Complex Complex Complex qz274 (@Nat.cast Complex Complex.instNatCast 16) qz275)

noncomputable def ep153 := @Enclosure.Complex.IsNear.of_eq qz40 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 16) qz41) Bool.false 151686259201 34359738368 7198733835695 1760524274499584 Bool.true 70888791985 274877906944 28764762539911 7042097097998336

noncomputable def ep154 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 16) qz41 Bool.false 1147706456205 274877906944 137579121149009 35210485489991680 Bool.true 25509672941 137438953472 34368282203291 8802621372497920 Bool.false

noncomputable abbrev qz42 := (@HPow.hPow Complex Complex Complex qz274 (@Nat.cast Complex Complex.instNatCast 15) qz275)

noncomputable def ep155 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 16) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 15) qz42) Bool.false 1147706456205 274877906944 137579121149009 35210485489991680 Bool.true 25509672941 137438953472 34368282203291 8802621372497920

noncomputable def ep156 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 15) qz42 Bool.false 1094306657835 274877906944 7705271760259 2071205028823040 Bool.true 2134079403 137438953472 1924851747741 517801257205760 Bool.false

noncomputable abbrev qz43 := (@HPow.hPow Complex Complex Complex qz274 (@Nat.cast Complex Complex.instNatCast 14) qz275)

noncomputable def ep157 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 15) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 14) qz43) Bool.false 1094306657835 274877906944 7705271760259 2071205028823040 Bool.true 2134079403 137438953472 1924851747741 517801257205760

noncomputable def ep158 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 14) qz43 Bool.false 520053016731 137438953472 15523700720819 4401310686248960 Bool.false 45322204425 274877906944 124094119270227 35210485489991680 Bool.false

noncomputable abbrev qz44 := (@HPow.hPow Complex Complex Complex qz274 (@Nat.cast Complex Complex.instNatCast 13) qz275)

noncomputable def ep159 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 14) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 13) qz44) Bool.false 520053016731 137438953472 15523700720819 4401310686248960 Bool.false 45322204425 274877906944 124094119270227 35210485489991680

noncomputable def ep160 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 13) qz44 Bool.false 241810945101 68719476736 5323641170973 1600476613181440 Bool.false 67754177751 274877906944 10642640377111 3200953226362880 Bool.false

noncomputable abbrev qz45 := (@HPow.hPow Complex Complex Complex qz274 (@Nat.cast Complex Complex.instNatCast 12) qz275)

noncomputable def ep161 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 13) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 12) qz45) Bool.false 241810945101 68719476736 5323641170973 1600476613181440 Bool.false 67754177751 274877906944 10642640377111 3200953226362880

noncomputable def ep162 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 12) qz45 Bool.false 905644283357 274877906944 109776589414321 35210485489991680 Bool.false 17734544043 274877906944 109735328477681 35210485489991680 Bool.false

noncomputable abbrev qz46 := (@HPow.hPow Complex Complex Complex qz274 (@Nat.cast Complex Complex.instNatCast 11) qz275)

noncomputable def ep163 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 12) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 11) qz46) Bool.false 905644283357 274877906944 109776589414321 35210485489991680 Bool.false 17734544043 274877906944 109735328477681 35210485489991680

noncomputable def ep164 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 11) qz46 Bool.false 240147226985 68719476736 4641657421103 1600476613181440 Bool.true 44313676563 274877906944 9279040556601 3200953226362880 Bool.true

noncomputable abbrev qz47 := (@HPow.hPow Complex Complex Complex qz274 (@Nat.cast Complex Complex.instNatCast 10) qz275)

noncomputable def ep165 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 11) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 10) qz47) Bool.false 240147226985 68719476736 4641657421103 1600476613181440 Bool.true 44313676563 274877906944 9279040556601 3200953226362880

noncomputable def ep166 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 10) qz47 Bool.false 964962414245 274877906944 94125757826373 35210485489991680 Bool.false 21250199361 137438953472 47007523107269 17605242744995840 Bool.true

noncomputable abbrev qz48 := (@HPow.hPow Complex Complex Complex qz274 (@Nat.cast Complex Complex.instNatCast 9) qz275)

noncomputable def ep167 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 10) (@HAdd.hAdd Complex Complex Complex qz4 qz3 qz48) Bool.false 964962414245 274877906944 94125757826373 35210485489991680 Bool.false 21250199361 137438953472 47007523107269 17605242744995840

noncomputable def ep168 := @Enclosure.Complex.IsNear.addLitP qz3 qz48 Bool.false 243218440123 68719476736 3894463965793 1600476613181440 Bool.true 48783384305 274877906944 7773307875901 3200953226362880 Bool.true

noncomputable abbrev qz321 := (@Nat.cast Real Real.instNatCast 9)

noncomputable abbrev qz49 := (@Inv.inv Real Real.instInv (Real.sqrt qz321))

noncomputable abbrev qz322 := (Real.log (Enclosure.sfrac Bool.false 9 1))

noncomputable abbrev qz50 := (@HMul.hMul Real Real Real qz267 qz280 qz322)

noncomputable def ep169 := @Enclosure.Complex.IsNear.of_eq qz48 (Complex.mk (@HMul.hMul Real Real Real qz0 qz49 (Real.cos qz50)) (@HMul.hMul Real Real Real qz0 qz49 (@Neg.neg Real Real.instNeg (Real.sin qz50)))) Bool.true 7911346247 274877906944 8447550578927 35210485489991680 Bool.false 91283783027 274877906944 8508659579627 35210485489991680 (BSN.cpow_neg_s_mk qz16 90753 1000 9 qz17 rfl)

noncomputable abbrev qz323 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 9) qz18)

noncomputable def ep170 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz321) 1572865 524288 1 524288 87381 87382 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz321) (Real.sqrt qz323) Bool.false 1572865 524288 1 524288 (BSN.sqrt_natCast_div_one 9) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz323) Bool.false 1572865 524288 1 524288 1572865 524288 1 524288 (BSN.sqrt_enclosure 9 1 786432 786433 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep171 := BSN.log_dyadic_bound 1 17 2 1 867 262144 128095 1 1 30876 18 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 1) (BSN.artanhQ 17) 0 1 1 867 1 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep172 := @Enclosure.Real.IsNear.mulLit_ff qz16 qz322 90753 1000 0 1 9895417793173221 4503599627370496 200000000076857 25619000000000000000 898038850983849325413 4503599627370496000 18150600006975003321 25619000000000000000000 qz21 (BSN.isNear_log_sfrac 9 1 9895417793173221 4503599627370496 200000000076857 25619000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz323) Bool.false 20752195215788806766592 9444732965739290427392 1000000000384285 128095000000000000000 9895417793173221 4503599627370496 200000000076857 25619000000000000000 (BSN.log_rat_reduce_isNear 9 1 3 18 16 30876 262144 24973259072661432 36028797018963968 128095 1000000000000000 rfl rfl rfl rfl (ep171 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep173 := nat_lit 14451020040670555905798029387975205586048662664797559500830555228912526475201

noncomputable def ep174 := nat_lit 41636410838359849338411928890151365737616435151257715052327691137382006721

noncomputable def ep175 := nat_lit 43269787300334948018717264306145314026670755124090163072387010304462815412161

noncomputable def ep176 := BSN.cos_dyadic_bound_f 1593801241 1073741824 3 2 524288 256441 ep173 ep74 ep174 ep175 ep77 ep174 45269 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1593801241) qz283 0 2 ep173 ep74 ep174 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1593801241) qz284 0 2 ep175 ep77 ep174 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz324 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 104545481) qz31)

noncomputable def ep177 := @Enclosure.Real.IsNear.cos_image qz50 qz324 Bool.false 104545481 524288 373 524288 Bool.true 45269 524288 1 128095 (@Enclosure.Real.IsNear.recentre' qz50 Bool.false 898038850983849325413 4503599627370496000 18150600006975003321 25619000000000000000000 104545481 524288 373 524288 (ep172 rfl) rfl) (Enclosure.sfrac_false_div 104545481 524288) (BSN.cos_reduce2 qz324 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 112153791852734046011392) qz33) 226375608064910080 72057594037927936 Bool.false 45269 524288 31 1000000000000000 256190 128095 (BSN.sin_reduce_arg_pos_rat_q2 104545481 524288 226375608064910080 72057594037927936 31 112153791852734046011392 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 45269 524288 112153791852734046011392 75557863725914323419136 1593801241 1073741824 256441 256190 (ep176 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep178 := nat_lit 25978526944536312750965723355243248962297499648514600929453137259132642049985

noncomputable def ep179 := nat_lit 67971587808618712686933751378862549832918262946340966133721114654934491643841

noncomputable def ep180 := BSN.sin_dyadic_bound_f 1593801241 1073741824 3 2 524288 256441 ep178 ep107 ep174 ep179 ep109 ep174 522329 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1593801241) qz289 0 2 ep178 ep107 ep174 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1593801241) qz290 0 2 ep179 ep109 ep174 rfl rfl rfl rfl) rfl rfl

noncomputable def ep181 := @Enclosure.Real.IsNear.sin_image qz50 qz324 Bool.false 104545481 524288 373 524288 Bool.true 522329 524288 1 128095 (@Enclosure.Real.IsNear.recentre' qz50 Bool.false 898038850983849325413 4503599627370496000 18150600006975003321 25619000000000000000000 104545481 524288 373 524288 (ep172 rfl) rfl) (Enclosure.sfrac_false_div 104545481 524288) (BSN.sin_reduce2 qz324 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 112153791852734046011392) qz33) 226375608064910080 72057594037927936 Bool.false 522329 524288 31 1000000000000000 256190 128095 (BSN.sin_reduce_arg_pos_rat_q2 104545481 524288 226375608064910080 72057594037927936 31 112153791852734046011392 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 522329 524288 112153791852734046011392 75557863725914323419136 1593801241 1073741824 256441 256190 (ep180 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz325 := (@Enclosure.Real.IsNear.recentre' qz49 Bool.false 174763 524288 1 524288 174763 524288 1 524288 (ep170 rfl rfl) rfl)

noncomputable def ep182 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz49 (Real.cos qz50)) (@HMul.hMul Real Real Real qz0 qz49 (@Neg.neg Real Real.instNeg (Real.sin qz50))) Bool.true 7911346247 274877906944 8447550578927 35210485489991680 Bool.false 91283783027 274877906944 8508659579627 35210485489991680 (@Enclosure.Real.IsNear.mulLit_ft qz49 (Real.cos qz50) 174763 524288 1 524288 45269 524288 48303723 67158671360 7911346247 274877906944 8447550578927 35210485489991680 qz325 (@Enclosure.Real.IsNear.recentre' (Real.cos qz50) Bool.true 45269 524288 48303723 67158671360 45269 524288 48303723 67158671360 (ep177 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz49 (@Neg.neg Real Real.instNeg (Real.sin qz50)) 174763 524288 1 524288 522329 524288 48303723 67158671360 91283783027 274877906944 8508659579627 35210485489991680 qz325 (@Enclosure.Real.IsNear.neg (Real.sin qz50) Bool.true 522329 524288 48303723 67158671360 (@Enclosure.Real.IsNear.recentre' (Real.sin qz50) Bool.true 522329 524288 48303723 67158671360 522329 524288 48303723 67158671360 (ep181 rfl rfl) rfl)) rfl)

noncomputable def ep183 := @ep168 7911346247 274877906944 8447550578927 35210485489991680 Bool.false 91283783027 274877906944 8508659579627 35210485489991680 Bool.false 66311712176823672504320 964962414245 274877906944 94125757826373 35210485489991680 Bool.false 11682420644988812525568 21250199361 137438953472 47007523107269 17605242744995840 EMRow26.d6 (ep169 ep182) rfl rfl

noncomputable abbrev qz326 := (@Nat.cast Real Real.instNatCast 10)

noncomputable abbrev qz51 := (@Inv.inv Real Real.instInv (Real.sqrt qz326))

noncomputable abbrev qz52 := (@HMul.hMul Real Real Real qz267 qz280 (Real.log (Enclosure.sfrac Bool.false 10 1)))

noncomputable def ep184 := @Enclosure.Complex.IsNear.of_eq qz47 (Complex.mk (@HMul.hMul Real Real Real qz0 qz51 (Real.cos qz52)) (@HMul.hMul Real Real Real qz0 qz51 (@Neg.neg Real Real.instNeg (Real.sin qz52)))) Bool.true 4373506305 274877906944 7990705437893 35210485489991680 Bool.true 86814075285 274877906944 8054399908073 35210485489991680 (BSN.cpow_neg_s_mk qz16 90753 1000 10 qz17 rfl)

noncomputable abbrev qz327 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 10) qz18)

noncomputable def ep185 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz326) 1657945 524288 1 524288 82897 82898 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz326) (Real.sqrt qz327) Bool.false 1657945 524288 1 524288 (BSN.sqrt_natCast_div_one 10) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz327) Bool.false 1657945 524288 1 524288 1657945 524288 1 524288 (BSN.sqrt_enclosure 10 1 828972 828973 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep186 := BSN.log_dyadic_bound 2 18 3 2 1574640 262144 128095 6528 48 58495 20 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 2) (BSN.artanhQ 18) 0 2 6528 1574640 48 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz53 := (Real.log (Enclosure.sfrac Bool.false 10 1))

noncomputable def ep187 := @Enclosure.Real.IsNear.mulLit_ff qz16 qz53 90753 1000 0 1 10369908600166117 4503599627370496 200000000076857 25619000000000000000 941100315190875616101 4503599627370496000 18150600006975003321 25619000000000000000000 qz21 (BSN.isNear_log_sfrac 10 1 10369908600166117 4503599627370496 200000000076857 25619000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz327) Bool.false 21747274560655572598784 9444732965739290427392 1000000000384285 128095000000000000000 10369908600166117 4503599627370496 200000000076857 25619000000000000000 (BSN.log_rat_reduce_isNear 10 1 3 20 16 58495 262144 24973259072661432 36028797018963968 128095 1000000000000000 rfl rfl rfl rfl (ep186 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep188 := BSN.sin_dyadic_bound_f 54047970 1073741824 1 0 524288 256441 0 1 1 0 1 1 26379 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 54047970) qz289 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 54047970) qz290 0 0 rfl) rfl rfl

noncomputable abbrev qz328 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 3423703) (@Nat.cast Real Real.instNatCast 16384))

noncomputable abbrev qz329 := (@Nat.cast Real Real.instNatCast 2361183241434822606848)

noncomputable def ep189 := @Enclosure.Real.IsNear.cos_image qz52 qz328 Bool.false 3423703 16384 93 131072 Bool.true 26379 524288 1 128095 (@Enclosure.Real.IsNear.recentre' qz52 Bool.false 941100315190875616101 4503599627370496000 18150600006975003321 25619000000000000000000 3423703 16384 93 131072 (ep187 rfl) rfl) (Enclosure.sfrac_false_div 3423703 16384) (BSN.cos_reduce1 qz328 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 118852743652238688256) qz329) 226375608064910080 72057594037927936 Bool.false 26379 524288 33 1000000000000000 256190 128095 (BSN.sin_reduce_arg_pos_rat_q1 3423703 16384 226375608064910080 72057594037927936 33 118852743652238688256 2361183241434822606848 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 26379 524288 118852743652238688256 2361183241434822606848 54047970 1073741824 256441 256190 (ep188 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep190 := BSN.cos_dyadic_bound_f 54047970 1073741824 1 0 524288 256441 0 1 1 0 1 1 523623 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 54047970) qz283 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 54047970) qz284 0 0 rfl) rfl rfl

noncomputable def ep191 := @Enclosure.Real.IsNear.sin_image qz52 qz328 Bool.false 3423703 16384 93 131072 Bool.false 523623 524288 1 128095 (@Enclosure.Real.IsNear.recentre' qz52 Bool.false 941100315190875616101 4503599627370496000 18150600006975003321 25619000000000000000000 3423703 16384 93 131072 (ep187 rfl) rfl) (Enclosure.sfrac_false_div 3423703 16384) (BSN.sin_reduce1 qz328 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 118852743652238688256) qz329) 226375608064910080 72057594037927936 Bool.false 523623 524288 33 1000000000000000 256190 128095 (BSN.sin_reduce_arg_pos_rat_q1 3423703 16384 226375608064910080 72057594037927936 33 118852743652238688256 2361183241434822606848 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 523623 524288 118852743652238688256 2361183241434822606848 54047970 1073741824 256441 256190 (ep190 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz330 := (@Enclosure.Real.IsNear.recentre' qz51 Bool.false 165795 524288 1 524288 165795 524288 1 524288 (ep185 rfl rfl) rfl)

noncomputable def ep192 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz51 (Real.cos qz52)) (@HMul.hMul Real Real Real qz0 qz51 (@Neg.neg Real Real.instNeg (Real.sin qz52))) Bool.true 4373506305 274877906944 7990705437893 35210485489991680 Bool.true 86814075285 274877906944 8054399908073 35210485489991680 (@Enclosure.Real.IsNear.mulLit_ft qz51 (Real.cos qz52) 165795 524288 1 524288 26379 524288 12043907 16789667840 4373506305 274877906944 7990705437893 35210485489991680 qz330 (@Enclosure.Real.IsNear.recentre' (Real.cos qz52) Bool.true 26379 524288 12043907 16789667840 26379 524288 12043907 16789667840 (ep189 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz51 (@Neg.neg Real Real.instNeg (Real.sin qz52)) 165795 524288 1 524288 523623 524288 12043907 16789667840 86814075285 274877906944 8054399908073 35210485489991680 qz330 (@Enclosure.Real.IsNear.neg (Real.sin qz52) Bool.false 523623 524288 12043907 16789667840 (@Enclosure.Real.IsNear.recentre' (Real.sin qz52) Bool.false 523623 524288 12043907 16789667840 523623 524288 12043907 16789667840 (ep191 rfl rfl) rfl)) rfl)

noncomputable def ep193 := @ep166 4373506305 274877906944 7990705437893 35210485489991680 Bool.true 86814075285 274877906944 8054399908073 35210485489991680 Bool.false 264044668448169902735360 240147226985 68719476736 4641657421103 1600476613181440 Bool.true 6090425331315413876736 44313676563 274877906944 9279040556601 3200953226362880 (ep167 (BSN.head_sum_c_succ qz5 9 10 rfl rfl) (ep183 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep184 ep192) rfl rfl

noncomputable abbrev qz331 := (@Nat.cast Real Real.instNatCast 11)

noncomputable abbrev qz54 := (@Inv.inv Real Real.instInv (Real.sqrt qz331))

noncomputable abbrev qz55 := (@HMul.hMul Real Real Real qz267 qz280 (Real.log (Enclosure.sfrac Bool.false 11 1)))

noncomputable def ep194 := @Enclosure.Complex.IsNear.of_eq qz46 (Complex.mk (@HMul.hMul Real Real Real qz0 qz54 (Real.cos qz55)) (@HMul.hMul Real Real Real qz0 qz54 (@Neg.neg Real Real.instNeg (Real.sin qz55)))) Bool.true 54944624583 274877906944 1532025230011 7042097097998336 Bool.false 31024110303 137438953472 766588235507 3521048548999168 (BSN.cpow_neg_s_mk qz16 90753 1000 11 qz17 rfl)

noncomputable abbrev qz332 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 11) qz18)

noncomputable def ep195 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz331) 1738867 524288 1 524288 79039 79040 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz331) (Real.sqrt qz332) Bool.false 1738867 524288 1 524288 (BSN.sqrt_natCast_div_one 11) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz332) Bool.false 1738867 524288 1 524288 1738867 524288 1 524288 (BSN.sqrt_enclosure 11 1 869433 869434 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep196 := BSN.log_dyadic_bound 3 19 4 3 4939817505 262144 128095 41676111 10935 83480 22 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 3) (BSN.artanhQ 19) 0 3 41676111 4939817505 10935 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz56 := (Real.log (Enclosure.sfrac Bool.false 11 1))

noncomputable def ep197 := @Enclosure.Real.IsNear.mulLit_ff qz16 qz56 90753 1000 0 1 10799147631728357 4503599627370496 200000000076857 25619000000000000000 980055045022243582821 4503599627370496000 18150600006975003321 25619000000000000000000 qz21 (BSN.isNear_log_sfrac 11 1 10799147631728357 4503599627370496 200000000076857 25619000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz332) Bool.false 22647454054174387339264 9444732965739290427392 1000000000384285 128095000000000000000 10799147631728357 4503599627370496 200000000076857 25619000000000000000 (BSN.log_rat_reduce_isNear 11 1 3 22 16 83480 262144 24973259072661432 36028797018963968 128095 1000000000000000 rfl rfl rfl rfl (ep196 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep198 := nat_lit 1521271987942145618305668805844212827187514682374842321404089239168000000000

noncomputable def ep199 := nat_lit 463800658570788080222865640298580012718230018151170456010000000000000000

noncomputable def ep200 := nat_lit 4562888362509295278756560686252041321537107587088224623300247717504000000000

noncomputable def ep201 := BSN.cos_dyadic_bound_f 908429900 1073741824 3 2 524288 256441 ep198 ep74 ep199 ep200 ep77 ep199 347577 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 908429900) qz283 0 2 ep198 ep74 ep199 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 908429900) qz284 0 2 ep200 ep77 ep199 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz333 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 114093423) qz31)

noncomputable def ep202 := @Enclosure.Real.IsNear.cos_image qz55 qz333 Bool.false 114093423 524288 93 131072 Bool.true 347577 524288 1 128095 (@Enclosure.Real.IsNear.recentre' qz55 Bool.false 980055045022243582821 4503599627370496000 18150600006975003321 25619000000000000000000 114093423 524288 93 131072 (ep197 rfl) rfl) (Enclosure.sfrac_false_div 114093423 524288) (BSN.cos_reduce2 qz333 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 63925071306470599950336) qz33) 226375608064910080 72057594037927936 Bool.false 347577 524288 34 1000000000000000 256190 128095 (BSN.sin_reduce_arg_pos_rat_q2 114093423 524288 226375608064910080 72057594037927936 34 63925071306470599950336 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 347577 524288 63925071306470599950336 75557863725914323419136 908429900 1073741824 256441 256190 (ep201 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep203 := nat_lit 681029117270905003867460280100000000

noncomputable def ep204 := BSN.sin_dyadic_bound_f 908429900 1073741824 2 1 524288 256441 ep203 ep69 ep203 ep203 ep70 ep203 392514 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 908429900) qz289 0 1 ep203 ep69 ep203 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 908429900) qz290 0 1 ep203 ep70 ep203 rfl rfl rfl rfl) rfl rfl

noncomputable def ep205 := @Enclosure.Real.IsNear.sin_image qz55 qz333 Bool.false 114093423 524288 93 131072 Bool.true 392514 524288 1 128095 (@Enclosure.Real.IsNear.recentre' qz55 Bool.false 980055045022243582821 4503599627370496000 18150600006975003321 25619000000000000000000 114093423 524288 93 131072 (ep197 rfl) rfl) (Enclosure.sfrac_false_div 114093423 524288) (BSN.sin_reduce2 qz333 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 63925071306470599950336) qz33) 226375608064910080 72057594037927936 Bool.false 392514 524288 34 1000000000000000 256190 128095 (BSN.sin_reduce_arg_pos_rat_q2 114093423 524288 226375608064910080 72057594037927936 34 63925071306470599950336 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 392514 524288 63925071306470599950336 75557863725914323419136 908429900 1073741824 256441 256190 (ep204 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz334 := (@Enclosure.Real.IsNear.recentre' qz54 Bool.false 158079 524288 1 524288 158079 524288 1 524288 (ep195 rfl rfl) rfl)

noncomputable def ep206 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz54 (Real.cos qz55)) (@HMul.hMul Real Real Real qz0 qz54 (@Neg.neg Real Real.instNeg (Real.sin qz55))) Bool.true 54944624583 274877906944 1532025230011 7042097097998336 Bool.false 31024110303 137438953472 766588235507 3521048548999168 (@Enclosure.Real.IsNear.mulLit_ft qz54 (Real.cos qz55) 158079 524288 1 524288 347577 524288 12043907 16789667840 54944624583 274877906944 1532025230011 7042097097998336 qz334 (@Enclosure.Real.IsNear.recentre' (Real.cos qz55) Bool.true 347577 524288 12043907 16789667840 347577 524288 12043907 16789667840 (ep202 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz54 (@Neg.neg Real Real.instNeg (Real.sin qz55)) 158079 524288 1 524288 196257 262144 12043907 16789667840 31024110303 137438953472 766588235507 3521048548999168 qz334 (@Enclosure.Real.IsNear.neg (Real.sin qz55) Bool.true 196257 262144 12043907 16789667840 (@Enclosure.Real.IsNear.recentre' (Real.sin qz55) Bool.true 392514 524288 12043907 16789667840 196257 262144 12043907 16789667840 (ep205 rfl rfl) rfl)) rfl)

noncomputable def ep207 := @ep164 54944624583 274877906944 1532025230011 7042097097998336 Bool.false 31024110303 137438953472 766588235507 3521048548999168 Bool.false 62235401261242753482752 905644283357 274877906944 109776589414321 35210485489991680 Bool.false 2437417173573011767296 17734544043 274877906944 109735328477681 35210485489991680 (ep165 (BSN.head_sum_c_succ qz5 10 11 rfl rfl) (ep193 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep194 ep206) rfl rfl

noncomputable abbrev qz335 := (@Nat.cast Real Real.instNatCast 12)

noncomputable abbrev qz57 := (@Inv.inv Real Real.instInv (Real.sqrt qz335))

noncomputable abbrev qz58 := (@HMul.hMul Real Real Real qz267 qz280 (Real.log (Enclosure.sfrac Bool.false 12 1)))

noncomputable def ep208 := @Enclosure.Complex.IsNear.of_eq qz45 (Complex.mk (@HMul.hMul Real Real Real qz0 qz57 (Real.cos qz58)) (@HMul.hMul Real Real Real qz0 qz57 (@Neg.neg Real Real.instNeg (Real.sin qz58)))) Bool.false 61599497047 274877906944 1468703269417 7042097097998336 Bool.false 12504908427 68719476736 366685783527 1760524274499584 (BSN.cpow_neg_s_mk qz16 90753 1000 12 qz17 rfl)

noncomputable abbrev qz336 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 12) qz18)

noncomputable def ep209 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz335) 1816187 524288 1 524288 75674 75675 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz335) (Real.sqrt qz336) Bool.false 1816187 524288 1 524288 (BSN.sqrt_natCast_div_one 12) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz336) Bool.false 1816187 524288 1 524288 1816187 524288 1 524288 (BSN.sqrt_enclosure 12 1 908093 908094 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep210 := BSN.log_dyadic_bound 4 20 4 3 6720000000 262144 128095 91811840 61440 106290 24 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 4) (BSN.artanhQ 20) 0 3 91811840 6720000000 61440 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz59 := (Real.log (Enclosure.sfrac Bool.false 12 1))

noncomputable def ep211 := @Enclosure.Real.IsNear.mulLit_ff qz16 qz59 90753 1000 0 1 11191020447815397 4503599627370496 200000000076857 25619000000000000000 1015618678700590723941 4503599627370496000 18150600006975003321 25619000000000000000000 qz21 (BSN.isNear_log_sfrac 12 1 11191020447815397 4503599627370496 200000000076857 25619000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz336) Bool.false 23469270914176955449344 9444732965739290427392 1000000000384285 128095000000000000000 11191020447815397 4503599627370496 200000000076857 25619000000000000000 (BSN.log_rat_reduce_isNear 12 1 3 24 16 106290 262144 24973259072661432 36028797018963968 128095 1000000000000000 rfl rfl rfl rfl (ep210 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep212 := nat_lit 829397435584241028181795299101749921

noncomputable def ep213 := BSN.sin_dyadic_bound_f 954312631 1073741824 2 1 524288 256441 ep212 ep69 ep212 ep212 ep70 ep212 407003 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 954312631) qz289 0 1 ep212 ep69 ep212 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 954312631) qz290 0 1 ep212 ep70 ep212 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz337 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 118233575) qz31)

noncomputable def ep214 := @Enclosure.Real.IsNear.cos_image qz58 qz337 Bool.false 118233575 524288 93 131072 Bool.false 407003 524288 1 128095 (@Enclosure.Real.IsNear.recentre' qz58 Bool.false 1015618678700590723941 4503599627370496000 18150600006975003321 25619000000000000000000 118233575 524288 93 131072 (ep211 rfl) rfl) (Enclosure.sfrac_false_div 118233575 524288) (BSN.cos_reduce3 qz337 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 67153781443423560007680) qz33) 226375608064910080 72057594037927936 Bool.false 407003 524288 35 1000000000000000 256190 128095 (BSN.sin_reduce_arg_pos_rat_q3 118233575 524288 226375608064910080 72057594037927936 35 67153781443423560007680 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 407003 524288 67153781443423560007680 75557863725914323419136 954312631 1073741824 256441 256190 (ep213 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep215 := nat_lit 1852817829004280188851717448780236339002438666586385401331155273538531379521

noncomputable def ep216 := nat_lit 687900106153715245732825048551019705876302501663412291633195804423506241

noncomputable def ep217 := nat_lit 5557077686800533136063686696243606977595563394755829379410199429006747126081

noncomputable def ep218 := BSN.cos_dyadic_bound_f 954312631 1073741824 3 2 524288 256441 ep215 ep74 ep216 ep217 ep77 ep216 330492 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 954312631) qz283 0 2 ep215 ep74 ep216 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 954312631) qz284 0 2 ep217 ep77 ep216 rfl rfl rfl rfl) rfl rfl

noncomputable def ep219 := @Enclosure.Real.IsNear.sin_image qz58 qz337 Bool.false 118233575 524288 93 131072 Bool.true 330492 524288 1 128095 (@Enclosure.Real.IsNear.recentre' qz58 Bool.false 1015618678700590723941 4503599627370496000 18150600006975003321 25619000000000000000000 118233575 524288 93 131072 (ep211 rfl) rfl) (Enclosure.sfrac_false_div 118233575 524288) (BSN.sin_reduce3 qz337 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 67153781443423560007680) qz33) 226375608064910080 72057594037927936 Bool.false 330492 524288 35 1000000000000000 256190 128095 (BSN.sin_reduce_arg_pos_rat_q3 118233575 524288 226375608064910080 72057594037927936 35 67153781443423560007680 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 330492 524288 67153781443423560007680 75557863725914323419136 954312631 1073741824 256441 256190 (ep218 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz338 := (@Enclosure.Real.IsNear.recentre' qz57 Bool.false 151349 524288 1 524288 151349 524288 1 524288 (ep209 rfl rfl) rfl)

noncomputable def ep220 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz57 (Real.cos qz58)) (@HMul.hMul Real Real Real qz0 qz57 (@Neg.neg Real Real.instNeg (Real.sin qz58))) Bool.false 61599497047 274877906944 1468703269417 7042097097998336 Bool.false 12504908427 68719476736 366685783527 1760524274499584 (@Enclosure.Real.IsNear.mulLit_ff qz57 (Real.cos qz58) 151349 524288 1 524288 407003 524288 12043907 16789667840 61599497047 274877906944 1468703269417 7042097097998336 qz338 (@Enclosure.Real.IsNear.recentre' (Real.cos qz58) Bool.false 407003 524288 12043907 16789667840 407003 524288 12043907 16789667840 (ep214 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz57 (@Neg.neg Real Real.instNeg (Real.sin qz58)) 151349 524288 1 524288 82623 131072 12043907 16789667840 12504908427 68719476736 366685783527 1760524274499584 qz338 (@Enclosure.Real.IsNear.neg (Real.sin qz58) Bool.true 82623 131072 12043907 16789667840 (@Enclosure.Real.IsNear.recentre' (Real.sin qz58) Bool.true 330492 524288 12043907 16789667840 82623 131072 12043907 16789667840 (ep219 rfl rfl) rfl)) rfl)

noncomputable def ep221 := @ep162 61599497047 274877906944 1468703269417 7042097097998336 Bool.false 12504908427 68719476736 366685783527 1760524274499584 Bool.false 265873945862053482725376 241810945101 68719476736 5323641170973 1600476613181440 Bool.false 4656031641726653300736 67754177751 274877906944 10642640377111 3200953226362880 (ep163 (BSN.head_sum_c_succ qz5 11 12 rfl rfl) (ep207 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep208 ep220) rfl rfl

noncomputable abbrev qz339 := (@Nat.cast Real Real.instNatCast 13)

noncomputable abbrev qz60 := (@Inv.inv Real Real.instInv (Real.sqrt qz339))

noncomputable abbrev qz61 := (@HMul.hMul Real Real Real qz267 qz280 (Real.log (Enclosure.sfrac Bool.false 13 1)))

noncomputable def ep222 := @Enclosure.Complex.IsNear.of_eq qz44 (Complex.mk (@HMul.hMul Real Real Real qz0 qz60 (Real.cos qz61)) (@HMul.hMul Real Real Real qz0 qz60 (@Neg.neg Real Real.instNeg (Real.sin qz61)))) Bool.false 36431126529 137438953472 3534750002573 17605242744995840 Bool.true 11215986663 137438953472 3512537561003 17605242744995840 (BSN.cpow_neg_s_mk qz16 90753 1000 13 qz17 rfl)

noncomputable abbrev qz340 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 13) qz18)

noncomputable def ep223 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz339) 1890347 524288 1 524288 72705 72706 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz339) (Real.sqrt qz340) Bool.false 1890347 524288 1 524288 (BSN.sqrt_natCast_div_one 13) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz340) Bool.false 1890347 524288 1 524288 1890347 524288 1 524288 (BSN.sqrt_enclosure 13 1 945173 945174 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep224 := BSN.log_dyadic_bound 5 21 5 4 35742602096145 262144 128095 699352521000 41015625 127272 26 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 5) (BSN.artanhQ 21) 0 4 699352521000 35742602096145 41015625 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz62 := (Real.log (Enclosure.sfrac Bool.false 13 1))

noncomputable def ep225 := @Enclosure.Real.IsNear.mulLit_ff qz16 qz62 90753 1000 0 1 11551488463034085 4503599627370496 200000000076857 25619000000000000000 209666446497146463201 900719925474099200 18150600006975003321 25619000000000000000000 qz21 (BSN.isNear_log_sfrac 13 1 11551488463034085 4503599627370496 200000000076857 25619000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz340) Bool.false 24225227133228857425920 9444732965739290427392 1000000000384285 128095000000000000000 11551488463034085 4503599627370496 200000000076857 25619000000000000000 (BSN.log_rat_reduce_isNear 13 1 3 26 16 127272 262144 24973259072661432 36028797018963968 128095 1000000000000000 rfl rfl rfl rfl (ep224 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep226 := nat_lit 10575608505030121393218623115494416

noncomputable def ep227 := BSN.cos_dyadic_bound_f 320683298 1073741824 2 1 524288 256441 ep226 ep57 ep226 ep226 ep58 ep226 501078 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 320683298) qz283 0 1 ep226 ep57 ep226 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 320683298) qz284 0 1 ep226 ep58 ep226 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz341 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 61020967) qz19)

noncomputable def ep228 := @Enclosure.Real.IsNear.cos_image qz61 qz341 Bool.false 61020967 262144 93 131072 Bool.false 501078 524288 1 128095 (@Enclosure.Real.IsNear.recentre' qz61 Bool.false 209666446497146463201 900719925474099200 18150600006975003321 25619000000000000000000 61020967 262144 93 131072 (ep225 rfl) rfl) (Enclosure.sfrac_false_div 61020967 262144) (BSN.cos_reduce0 qz341 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 11283040491562036363264) qz288) 226375608064910080 72057594037927936 Bool.false 501078 524288 37 1000000000000000 256190 128095 (BSN.sin_reduce_arg_pos_rat_q0 61020967 262144 226375608064910080 72057594037927936 37 11283040491562036363264 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 501078 524288 11283040491562036363264 37778931862957161709568 320683298 1073741824 256441 256190 (ep227 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep229 := BSN.sin_dyadic_bound_f 320683298 1073741824 2 1 524288 256441 ep226 ep69 ep226 ep226 ep70 ep226 154266 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 320683298) qz289 0 1 ep226 ep69 ep226 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 320683298) qz290 0 1 ep226 ep70 ep226 rfl rfl rfl rfl) rfl rfl

noncomputable def ep230 := @Enclosure.Real.IsNear.sin_image qz61 qz341 Bool.false 61020967 262144 93 131072 Bool.false 154266 524288 1 128095 (@Enclosure.Real.IsNear.recentre' qz61 Bool.false 209666446497146463201 900719925474099200 18150600006975003321 25619000000000000000000 61020967 262144 93 131072 (ep225 rfl) rfl) (Enclosure.sfrac_false_div 61020967 262144) (BSN.sin_reduce0 qz341 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 11283040491562036363264) qz288) 226375608064910080 72057594037927936 Bool.false 154266 524288 37 1000000000000000 256190 128095 (BSN.sin_reduce_arg_pos_rat_q0 61020967 262144 226375608064910080 72057594037927936 37 11283040491562036363264 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 154266 524288 11283040491562036363264 37778931862957161709568 320683298 1073741824 256441 256190 (ep229 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz342 := (@Enclosure.Real.IsNear.recentre' qz60 Bool.false 145411 524288 1 524288 145411 524288 1 524288 (ep223 rfl rfl) rfl)

noncomputable def ep231 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz60 (Real.cos qz61)) (@HMul.hMul Real Real Real qz0 qz60 (@Neg.neg Real Real.instNeg (Real.sin qz61))) Bool.false 36431126529 137438953472 3534750002573 17605242744995840 Bool.true 11215986663 137438953472 3512537561003 17605242744995840 (@Enclosure.Real.IsNear.mulLit_ff qz60 (Real.cos qz61) 145411 524288 1 524288 250539 262144 12043907 16789667840 36431126529 137438953472 3534750002573 17605242744995840 qz342 (@Enclosure.Real.IsNear.recentre' (Real.cos qz61) Bool.false 501078 524288 12043907 16789667840 250539 262144 12043907 16789667840 (ep228 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz60 (@Neg.neg Real Real.instNeg (Real.sin qz61)) 145411 524288 1 524288 77133 262144 12043907 16789667840 11215986663 137438953472 3512537561003 17605242744995840 qz342 (@Enclosure.Real.IsNear.neg (Real.sin qz61) Bool.false 77133 262144 12043907 16789667840 (@Enclosure.Real.IsNear.recentre' (Real.sin qz61) Bool.false 154266 524288 12043907 16789667840 77133 262144 12043907 16789667840 (ep230 rfl rfl) rfl)) rfl)

noncomputable def ep232 := @ep160 36431126529 137438953472 3534750002573 17605242744995840 Bool.true 11215986663 137438953472 3512537561003 17605242744995840 Bool.false 35737771184732573270016 520053016731 137438953472 15523700720819 4401310686248960 Bool.false 6229036345216047513600 45322204425 274877906944 124094119270227 35210485489991680 (ep161 (BSN.head_sum_c_succ qz5 12 13 rfl rfl) (ep221 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep222 ep231) rfl rfl

noncomputable abbrev qz343 := (@Nat.cast Real Real.instNatCast 14)

noncomputable abbrev qz63 := (@Inv.inv Real Real.instInv (Real.sqrt qz343))

noncomputable abbrev qz64 := (@HMul.hMul Real Real Real qz267 qz280 (Real.log (Enclosure.sfrac Bool.false 14 1)))

noncomputable def ep233 := @Enclosure.Complex.IsNear.of_eq qz43 (Complex.mk (@HMul.hMul Real Real Real qz0 qz63 (Real.cos qz64)) (@HMul.hMul Real Real Real qz0 qz63 (@Neg.neg Real Real.instNeg (Real.sin qz64)))) Bool.false 54200624373 274877906944 6800014157851 35210485489991680 Bool.true 49590363231 274877906944 6795799576161 35210485489991680 (BSN.cpow_neg_s_mk qz16 90753 1000 14 qz17 rfl)

noncomputable abbrev qz344 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 14) qz18)

noncomputable def ep234 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz343) 1961707 524288 1 524288 70060 70061 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz343) (Real.sqrt qz344) Bool.false 1961707 524288 1 524288 (BSN.sqrt_natCast_div_one 14) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz344) Bool.false 1961707 524288 1 524288 1961707 524288 1 524288 (BSN.sqrt_enclosure 14 1 980853 980854 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep235 := BSN.log_dyadic_bound 6 22 5 4 51857700491520 262144 128095 1346332575744 176359680 146699 28 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 6) (BSN.artanhQ 22) 0 4 1346332575744 51857700491520 176359680 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz65 := (Real.log (Enclosure.sfrac Bool.false 14 1))

noncomputable def ep236 := @Enclosure.Real.IsNear.mulLit_ff qz16 qz65 90753 1000 0 1 11885241781671653 4503599627370496 200000000076857 25619000000000000000 1078621347412047524709 4503599627370496000 18150600006975003321 25619000000000000000000 qz21 (BSN.isNear_log_sfrac 14 1 11885241781671653 4503599627370496 200000000076857 25619000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz344) Bool.false 24925158572916270432256 9444732965739290427392 1000000000384285 128095000000000000000 11885241781671653 4503599627370496 200000000076857 25619000000000000000 (BSN.log_rat_reduce_isNear 14 1 3 28 16 146699 262144 24973259072661432 36028797018963968 128095 1000000000000000 rfl rfl rfl rfl (ep235 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep237 := nat_lit 895116301378815309710484970732928239233888211160472656023120965185616773376

noncomputable def ep238 := nat_lit 160614792514440732087550626974227690933279534296647752377828925574512896

noncomputable def ep239 := nat_lit 2685027674551417047667279810944836262319798074412824672564607237705701294336

noncomputable def ep240 := BSN.cos_dyadic_bound_f 795652062 1073741824 3 2 524288 256441 ep237 ep74 ep238 ep239 ep77 ep238 386813 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 795652062) qz283 0 2 ep237 ep74 ep238 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 795652062) qz284 0 2 ep239 ep77 ep238 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz345 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 125568051) qz31)

noncomputable def ep241 := @Enclosure.Real.IsNear.cos_image qz64 qz345 Bool.false 125568051 524288 93 131072 Bool.false 386813 524288 1 128095 (@Enclosure.Real.IsNear.recentre' qz64 Bool.false 1078621347412047524709 4503599627370496000 18150600006975003321 25619000000000000000000 125568051 524288 93 131072 (ep236 rfl) rfl) (Enclosure.sfrac_false_div 125568051 524288) (BSN.cos_reduce0 qz345 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 55989036411054448443392) qz33) 226375608064910080 72057594037927936 Bool.false 386813 524288 38 1000000000000000 256190 128095 (BSN.sin_reduce_arg_pos_rat_q0 125568051 524288 226375608064910080 72057594037927936 38 55989036411054448443392 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 386813 524288 55989036411054448443392 75557863725914323419136 795652062 1073741824 256441 256190 (ep240 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep242 := nat_lit 400767753835610796247503007270200336

noncomputable def ep243 := BSN.sin_dyadic_bound_f 795652062 1073741824 2 1 524288 256441 ep242 ep69 ep242 ep242 ep70 ep242 353911 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 795652062) qz289 0 1 ep242 ep69 ep242 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 795652062) qz290 0 1 ep242 ep70 ep242 rfl rfl rfl rfl) rfl rfl

noncomputable def ep244 := @Enclosure.Real.IsNear.sin_image qz64 qz345 Bool.false 125568051 524288 93 131072 Bool.false 353911 524288 1 128095 (@Enclosure.Real.IsNear.recentre' qz64 Bool.false 1078621347412047524709 4503599627370496000 18150600006975003321 25619000000000000000000 125568051 524288 93 131072 (ep236 rfl) rfl) (Enclosure.sfrac_false_div 125568051 524288) (BSN.sin_reduce0 qz345 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 55989036411054448443392) qz33) 226375608064910080 72057594037927936 Bool.false 353911 524288 38 1000000000000000 256190 128095 (BSN.sin_reduce_arg_pos_rat_q0 125568051 524288 226375608064910080 72057594037927936 38 55989036411054448443392 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 353911 524288 55989036411054448443392 75557863725914323419136 795652062 1073741824 256441 256190 (ep243 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz346 := (@Enclosure.Real.IsNear.recentre' qz63 Bool.false 140121 524288 1 524288 140121 524288 1 524288 (ep234 rfl rfl) rfl)

noncomputable def ep245 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz63 (Real.cos qz64)) (@HMul.hMul Real Real Real qz0 qz63 (@Neg.neg Real Real.instNeg (Real.sin qz64))) Bool.false 54200624373 274877906944 6800014157851 35210485489991680 Bool.true 49590363231 274877906944 6795799576161 35210485489991680 (@Enclosure.Real.IsNear.mulLit_ff qz63 (Real.cos qz64) 140121 524288 1 524288 386813 524288 12043907 16789667840 54200624373 274877906944 6800014157851 35210485489991680 qz346 (@Enclosure.Real.IsNear.recentre' (Real.cos qz64) Bool.false 386813 524288 12043907 16789667840 386813 524288 12043907 16789667840 (ep241 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz63 (@Neg.neg Real Real.instNeg (Real.sin qz64)) 140121 524288 1 524288 353911 524288 12043907 16789667840 49590363231 274877906944 6795799576161 35210485489991680 qz346 (@Enclosure.Real.IsNear.neg (Real.sin qz64) Bool.false 353911 524288 12043907 16789667840 (@Enclosure.Real.IsNear.recentre' (Real.sin qz64) Bool.false 353911 524288 12043907 16789667840 353911 524288 12043907 16789667840 (ep244 rfl rfl) rfl)) rfl)

noncomputable def ep246 := @ep158 54200624373 274877906944 6800014157851 35210485489991680 Bool.true 49590363231 274877906944 6795799576161 35210485489991680 Bool.false 150400361830284389253120 1094306657835 274877906944 7705271760259 2071205028823040 Bool.true 1173222559097882148864 2134079403 137438953472 1924851747741 517801257205760 (ep159 (BSN.head_sum_c_succ qz5 13 14 rfl rfl) (ep232 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep233 ep245) rfl rfl

noncomputable abbrev qz347 := (@Nat.cast Real Real.instNatCast 15)

noncomputable abbrev qz66 := (@Inv.inv Real Real.instInv (Real.sqrt qz347))

noncomputable abbrev qz67 := (@HMul.hMul Real Real Real qz267 qz280 (Real.log (Enclosure.sfrac Bool.false 15 1)))

noncomputable def ep247 := @Enclosure.Complex.IsNear.of_eq qz42 (Complex.mk (@HMul.hMul Real Real Real qz0 qz66 (Real.cos qz67)) (@HMul.hMul Real Real Real qz0 qz66 (@Neg.neg Real Real.instNeg (Real.sin qz67)))) Bool.false 26699899185 137438953472 3294750612303 17605242744995840 Bool.true 11687796769 68719476736 822901245847 4401310686248960 (BSN.cpow_neg_s_mk qz16 90753 1000 15 qz17 rfl)

noncomputable abbrev qz348 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 15) qz18)

noncomputable def ep248 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz347) 2030559 524288 1 524288 67685 67686 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz347) (Real.sqrt qz348) Bool.false 2030559 524288 1 524288 (BSN.sqrt_natCast_div_one 15) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz348) Bool.false 2030559 524288 1 524288 2030559 524288 1 524288 (BSN.sqrt_enclosure 15 1 1015279 1015280 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep249 := BSN.log_dyadic_bound 7 23 6 5 430628584065881355 262144 128095 14087658153505881 266939110305 164785 30 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 7) (BSN.artanhQ 23) 0 5 14087658153505881 430628584065881355 266939110305 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz68 := (Real.log (Enclosure.sfrac Bool.false 15 1))

noncomputable def ep250 := @Enclosure.Real.IsNear.mulLit_ff qz16 qz68 90753 1000 0 1 12195956895733477 4503599627370496 200000000076857 25619000000000000000 1106819676158500238181 4503599627370496000 18150600006975003321 25619000000000000000000 qz21 (BSN.isNear_log_sfrac 15 1 12195956895733477 4503599627370496 200000000076857 25619000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz348) Bool.false 25576775395801252757504 9444732965739290427392 1000000000384285 128095000000000000000 12195956895733477 4503599627370496 200000000076857 25619000000000000000 (BSN.log_rat_reduce_isNear 15 1 3 30 16 164785 262144 24973259072661432 36028797018963968 128095 1000000000000000 rfl rfl rfl rfl (ep249 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep251 := nat_lit 793883445120496832887300407759732456215553809404039131667754111402587890625

noncomputable def ep252 := nat_lit 126344902156476416557244795894636716077443555800252962172031402587890625

noncomputable def ep253 := nat_lit 2381397645557177545828786733687408095214506541100516889078918271402587890625

noncomputable def ep254 := BSN.cos_dyadic_bound_f 772137625 1073741824 3 2 524288 256441 ep251 ep74 ep252 ep253 ep77 ep252 394470 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 772137625) qz283 0 2 ep251 ep74 ep252 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 772137625) qz284 0 2 ep253 ep77 ep252 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz349 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 8053173) (@Nat.cast Real Real.instNatCast 32768))

noncomputable def ep255 := @Enclosure.Real.IsNear.cos_image qz67 qz349 Bool.false 8053173 32768 373 524288 Bool.false 394470 524288 1 128095 (@Enclosure.Real.IsNear.recentre' qz67 Bool.false 1106819676158500238181 4503599627370496000 18150600006975003321 25619000000000000000000 8053173 32768 373 524288 (ep250 rfl) rfl) (Enclosure.sfrac_false_div 8053173 32768) (BSN.cos_reduce0 qz349 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 3395897191332594057216) (@Nat.cast Real Real.instNatCast 4722366482869645213696)) 226375608064910080 72057594037927936 Bool.false 394470 524288 39 1000000000000000 256190 128095 (BSN.sin_reduce_arg_pos_rat_q0 8053173 32768 226375608064910080 72057594037927936 39 3395897191332594057216 4722366482869645213696 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 394470 524288 3395897191332594057216 4722366482869645213696 772137625 1073741824 256441 256190 (ep254 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep256 := nat_lit 355450280850186439344523535400390625

noncomputable def ep257 := BSN.sin_dyadic_bound_f 772137625 1073741824 2 1 524288 256441 ep256 ep69 ep256 ep256 ep70 ep256 345356 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 772137625) qz289 0 1 ep256 ep69 ep256 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 772137625) qz290 0 1 ep256 ep70 ep256 rfl rfl rfl rfl) rfl rfl

noncomputable def ep258 := @Enclosure.Real.IsNear.sin_image qz67 qz349 Bool.false 8053173 32768 373 524288 Bool.false 345356 524288 1 128095 (@Enclosure.Real.IsNear.recentre' qz67 Bool.false 1106819676158500238181 4503599627370496000 18150600006975003321 25619000000000000000000 8053173 32768 373 524288 (ep250 rfl) rfl) (Enclosure.sfrac_false_div 8053173 32768) (BSN.sin_reduce0 qz349 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 3395897191332594057216) (@Nat.cast Real Real.instNatCast 4722366482869645213696)) 226375608064910080 72057594037927936 Bool.false 345356 524288 39 1000000000000000 256190 128095 (BSN.sin_reduce_arg_pos_rat_q0 8053173 32768 226375608064910080 72057594037927936 39 3395897191332594057216 4722366482869645213696 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 345356 524288 3395897191332594057216 4722366482869645213696 772137625 1073741824 256441 256190 (ep257 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz350 := (@Enclosure.Real.IsNear.recentre' qz66 Bool.false 135371 524288 1 524288 135371 524288 1 524288 (ep248 rfl rfl) rfl)

noncomputable def ep259 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz66 (Real.cos qz67)) (@HMul.hMul Real Real Real qz0 qz66 (@Neg.neg Real Real.instNeg (Real.sin qz67))) Bool.false 26699899185 137438953472 3294750612303 17605242744995840 Bool.true 11687796769 68719476736 822901245847 4401310686248960 (@Enclosure.Real.IsNear.mulLit_ff qz66 (Real.cos qz67) 135371 524288 1 524288 197235 262144 48303723 67158671360 26699899185 137438953472 3294750612303 17605242744995840 qz350 (@Enclosure.Real.IsNear.recentre' (Real.cos qz67) Bool.false 394470 524288 48303723 67158671360 197235 262144 48303723 67158671360 (ep255 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz66 (@Neg.neg Real Real.instNeg (Real.sin qz67)) 135371 524288 1 524288 86339 131072 48303723 67158671360 11687796769 68719476736 822901245847 4401310686248960 qz350 (@Enclosure.Real.IsNear.neg (Real.sin qz67) Bool.false 86339 131072 48303723 67158671360 (@Enclosure.Real.IsNear.recentre' (Real.sin qz67) Bool.false 345356 524288 48303723 67158671360 86339 131072 48303723 67158671360 (ep258 rfl rfl) rfl)) rfl)

noncomputable def ep260 := @ep156 26699899185 137438953472 3294750612303 17605242744995840 Bool.true 11687796769 68719476736 822901245847 4401310686248960 Bool.false 157739574233873000693760 1147706456205 274877906944 137579121149009 35210485489991680 Bool.true 1753011376212018200576 25509672941 137438953472 34368282203291 8802621372497920 (ep157 (BSN.head_sum_c_succ qz5 14 15 rfl rfl) (ep246 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep247 ep259) rfl rfl

noncomputable abbrev qz351 := (@Nat.cast Real Real.instNatCast 16)

noncomputable abbrev qz69 := (@Inv.inv Real Real.instInv (Real.sqrt qz351))

noncomputable abbrev qz352 := (Real.log (Enclosure.sfrac Bool.false 16 1))

noncomputable abbrev qz70 := (@HMul.hMul Real Real Real qz267 qz280 qz352)

noncomputable def ep261 := @Enclosure.Complex.IsNear.of_eq qz41 (Complex.mk (@HMul.hMul Real Real Real qz0 qz69 (Real.cos qz70)) (@HMul.hMul Real Real Real qz0 qz69 (@Neg.neg Real Real.instNeg (Real.sin qz70)))) Bool.false 65783617403 274877906944 6395555564891 35210485489991680 Bool.true 19869446103 274877906944 6350683886391 35210485489991680 (BSN.cpow_neg_s_mk qz16 90753 1000 16 qz17 rfl)

noncomputable abbrev qz353 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 16) qz18)

noncomputable def ep262 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz351) 2097153 524288 1 524288 65535 65536 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz351) (Real.sqrt qz353) Bool.false 2097153 524288 1 524288 (BSN.sqrt_natCast_div_one 16) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz353) Bool.false 2097153 524288 1 524288 2097153 524288 1 524288 (BSN.sqrt_enclosure 16 1 1048576 1048577 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep263 := BSN.log_dyadic_bound 0 32 1 0 1 262144 128095 0 1 0 32 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 0) (BSN.artanhQ 32) 0 0 rfl) rfl rfl rfl

noncomputable def ep264 := @Enclosure.Real.IsNear.mulLit_ff qz16 qz352 90753 1000 0 1 3121657384082679 1125899906842624 50000000025619 6404750000000000000 283299772577655367287 1125899906842624000 4537650002325001107 6404750000000000000000 qz21 (BSN.isNear_log_sfrac 16 1 3121657384082679 1125899906842624 50000000025619 6404750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz353) Bool.false 26186360105375033720832 9444732965739290427392 1000000000512380 128095000000000000000 3121657384082679 1125899906842624 50000000025619 6404750000000000000 (BSN.log_rat_reduce_isNear 16 1 4 32 32 0 262144 24973259072661432 36028797018963968 128095 1000000000000000 rfl rfl rfl rfl (ep263 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep265 := nat_lit 9840755233551264771266319548688561

noncomputable def ep266 := BSN.cos_dyadic_bound_f 314961237 1073741824 2 1 524288 256441 ep265 ep57 ep265 ep265 ep58 ep265 501893 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 314961237) qz283 0 1 ep265 ep57 ep265 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 314961237) qz284 0 1 ep265 ep58 ep265 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz354 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 16490217) (@Nat.cast Real Real.instNatCast 65536))

noncomputable abbrev qz355 := (@Nat.cast Real Real.instNatCast 9444732965739290427392)

noncomputable def ep267 := @Enclosure.Real.IsNear.cos_image qz70 qz354 Bool.false 16490217 65536 373 524288 Bool.false 501893 524288 1 128095 (@Enclosure.Real.IsNear.recentre' qz70 Bool.false 283299772577655367287 1125899906842624000 4537650002325001107 6404750000000000000000 16490217 65536 373 524288 (ep264 rfl) rfl) (Enclosure.sfrac_false_div 16490217 65536) (BSN.cos_reduce0 qz354 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 2770428343964269543424) qz355) 226375608064910080 72057594037927936 Bool.false 501893 524288 40 1000000000000000 256190 128095 (BSN.sin_reduce_arg_pos_rat_q0 16490217 65536 226375608064910080 72057594037927936 40 2770428343964269543424 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 501893 524288 2770428343964269543424 9444732965739290427392 314961237 1073741824 256441 256190 (ep266 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep268 := BSN.sin_dyadic_bound_f 314961237 1073741824 2 1 524288 256441 ep265 ep69 ep265 ep265 ep70 ep265 151593 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 314961237) qz289 0 1 ep265 ep69 ep265 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 314961237) qz290 0 1 ep265 ep70 ep265 rfl rfl rfl rfl) rfl rfl

noncomputable def ep269 := @Enclosure.Real.IsNear.sin_image qz70 qz354 Bool.false 16490217 65536 373 524288 Bool.false 151593 524288 1 128095 (@Enclosure.Real.IsNear.recentre' qz70 Bool.false 283299772577655367287 1125899906842624000 4537650002325001107 6404750000000000000000 16490217 65536 373 524288 (ep264 rfl) rfl) (Enclosure.sfrac_false_div 16490217 65536) (BSN.sin_reduce0 qz354 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 2770428343964269543424) qz355) 226375608064910080 72057594037927936 Bool.false 151593 524288 40 1000000000000000 256190 128095 (BSN.sin_reduce_arg_pos_rat_q0 16490217 65536 226375608064910080 72057594037927936 40 2770428343964269543424 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 151593 524288 2770428343964269543424 9444732965739290427392 314961237 1073741824 256441 256190 (ep268 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz356 := (@Enclosure.Real.IsNear.recentre' qz69 Bool.false 131071 524288 1 524288 131071 524288 1 524288 (ep262 rfl rfl) rfl)

noncomputable def ep270 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz69 (Real.cos qz70)) (@HMul.hMul Real Real Real qz0 qz69 (@Neg.neg Real Real.instNeg (Real.sin qz70))) Bool.false 65783617403 274877906944 6395555564891 35210485489991680 Bool.true 19869446103 274877906944 6350683886391 35210485489991680 (@Enclosure.Real.IsNear.mulLit_ff qz69 (Real.cos qz70) 131071 524288 1 524288 501893 524288 48303723 67158671360 65783617403 274877906944 6395555564891 35210485489991680 qz356 (@Enclosure.Real.IsNear.recentre' (Real.cos qz70) Bool.false 501893 524288 48303723 67158671360 501893 524288 48303723 67158671360 (ep267 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz69 (@Neg.neg Real Real.instNeg (Real.sin qz70)) 131071 524288 1 524288 151593 524288 48303723 67158671360 19869446103 274877906944 6350683886391 35210485489991680 qz356 (@Enclosure.Real.IsNear.neg (Real.sin qz70) Bool.false 151593 524288 48303723 67158671360 (@Enclosure.Real.IsNear.recentre' (Real.sin qz70) Bool.false 151593 524288 48303723 67158671360 151593 524288 48303723 67158671360 (ep269 rfl rfl) rfl)) rfl)

noncomputable def ep271 := @ep154 65783617403 274877906944 6395555564891 35210485489991680 Bool.true 19869446103 274877906944 6350683886391 35210485489991680 Bool.false 333561611530687534333952 151686259201 34359738368 7198733835695 1760524274499584 Bool.true 9742881383312701521920 70888791985 274877906944 28764762539911 7042097097998336 (ep155 (BSN.head_sum_c_succ qz5 15 16 rfl rfl) (ep260 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep261 ep270) rfl rfl

theorem EMRow26.d7 : Enclosure.Complex.IsNear qz40 Bool.false 151686259201 34359738368 7198733835695 1760524274499584 Bool.true 70888791985 274877906944 28764762539911 7042097097998336 := ep153 (BSN.head_sum_c_succ qz5 16 17 rfl rfl) (ep271 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

theorem EMRow26.d8 : @Eq Nat (BSN.factNat (Nat.mul 2 1)) 2 := @Eq.refl Nat 2

theorem EMRow26.d9 : @Eq Nat (Nat.pow 19 1) 19 := @Eq.refl Nat 19

noncomputable def ep272 := nat_lit 203195189978266860593619984565519

noncomputable def ep273 := nat_lit 45105397297653291930798260224000

noncomputable def ep274 := nat_lit 985304586986296622222452053056239260081

noncomputable def ep275 := nat_lit 148020839932648214874983076930592440320000

noncomputable abbrev qz530 := (@instHMul Complex Complex.instMul)

noncomputable abbrev qz510 := qz530

noncomputable abbrev qz357 := qz510

noncomputable abbrev qz71 := qz357

noncomputable abbrev qz511 := (@instHSub Complex Complex.instSub)

noncomputable abbrev qz358 := qz511

noncomputable abbrev qz72 := qz358

noncomputable abbrev qz531 := (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (4 : Complex))

noncomputable abbrev qz532 := (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid))

noncomputable abbrev qz512 := (@HAdd.hAdd Complex Complex Complex qz528 (@HAdd.hAdd Complex Complex Complex qz528 qz531 (@HMul.hMul Complex Complex Complex qz530 Complex.I (@HDiv.hDiv Complex Complex Complex qz532 (↑qz529) (2 : Complex)))) (@Nat.cast Complex Complex.instNatCast 2))

noncomputable abbrev qz359 := qz512

noncomputable abbrev qz73 := (Complex.Stirling.logGammaStirling 1 qz359)

noncomputable abbrev qz513 := (@HAdd.hAdd Complex Complex Complex qz528 qz531 (@HMul.hMul Complex Complex Complex qz530 Complex.I (@HDiv.hDiv Complex Complex Complex qz532 (↑qz529) (2 : Complex))))

noncomputable abbrev qz360 := qz513

noncomputable abbrev qz74 := qz360

noncomputable abbrev qz75 := (@HMul.hMul Real Real Real qz267 (@HDiv.hDiv Real Real Real qz270 qz280 (2 : Real)) (Real.log Real.pi))

noncomputable abbrev qz361 := (@instHSub Real Real.instSub)

noncomputable def ep276 := Complex.re (@HMul.hMul Complex Complex Complex qz71 (Complex.exp (@HMul.hMul Complex Complex Complex qz71 Complex.I ↑(@HSub.hSub Real Real Real qz361 (Complex.im (@HSub.hSub Complex Complex Complex qz72 qz73 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz74 (@Nat.cast Complex Complex.instNatCast j))))) qz75))) (zetaApproximant qz5 1 19))

noncomputable def ep277 := @Enclosure.Real.IsNear.of_eq ep276 (@HSub.hSub Real Real Real qz361 (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz361 (Complex.im (@HSub.hSub Complex Complex Complex qz72 qz73 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz74 (@Nat.cast Complex Complex.instNatCast j))))) qz75)) (Complex.re (zetaApproximant qz5 1 19))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz361 (Complex.im (@HSub.hSub Complex Complex Complex qz72 qz73 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz74 (@Nat.cast Complex Complex.instNatCast j))))) qz75)) (Complex.im (zetaApproximant qz5 1 19))))

noncomputable def ep278 := nat_lit 203195321812791632808759200249367

noncomputable def ep279 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz361 (Complex.im (@HSub.hSub Complex Complex Complex qz72 qz73 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz74 (@Nat.cast Complex Complex.instNatCast j))))) qz75)) (Complex.re (zetaApproximant qz5 1 19))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz361 (Complex.im (@HSub.hSub Complex Complex Complex qz72 qz73 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz74 (@Nat.cast Complex Complex.instNatCast j))))) qz75)) (Complex.im (zetaApproximant qz5 1 19))) ep278

noncomputable def ep280 := nat_lit 980225832225623363253431525997079543197

noncomputable def ep281 := nat_lit 16479315596526892401960481

noncomputable def ep282 := nat_lit 5638174662206661491349782528000

noncomputable def ep283 := nat_lit 1269688690168314742255131764789929221

noncomputable def ep284 := nat_lit 37005209983162053718745769232648110080000

noncomputable def ep285 := nat_lit 1145649971617733165069245490068345403334345122601477217452032000

noncomputable def ep286 := @Enclosure.Real.IsNear.mulLit_ff (Real.cos (@HSub.hSub Real Real Real qz361 (Complex.im (@HSub.hSub Complex Complex Complex qz72 qz73 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz74 (@Nat.cast Complex Complex.instNatCast j))))) qz75)) (Complex.re (zetaApproximant qz5 1 19)) 524287 524288 30882803

noncomputable def ep287 := nat_lit 387565058475208488497252841

noncomputable def ep288 := nat_lit 86031717868143638478848000

noncomputable def ep289 := nat_lit 2005046382618506339939162739

noncomputable def ep290 := nat_lit 440809316012794374837921382400

noncomputable def ep291 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HSub.hSub Real Real Real qz361 (Complex.im (@HSub.hSub Complex Complex Complex qz72 qz73 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz74 (@Nat.cast Complex Complex.instNatCast j))))) qz75)) Bool.false 524287 524288 30882803

noncomputable abbrev qz362 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 19765203) qz19)

noncomputable def ep292 := @Enclosure.Real.IsNear.cos_image (@HSub.hSub Real Real Real qz361 (Complex.im (@HSub.hSub Complex Complex Complex qz72 qz73 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz74 (@Nat.cast Complex Complex.instNatCast j))))) qz75) qz362 Bool.false 19765203 262144 237

noncomputable def ep293 := nat_lit 3018087620622984110239997

noncomputable def ep294 := nat_lit 6715867136000000000000000000

noncomputable def ep295 := @Enclosure.Real.IsNear.recentre' (@HSub.hSub Real Real Real qz361 (Complex.im (@HSub.hSub Complex Complex Complex qz72 qz73 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz74 (@Nat.cast Complex Complex.instNatCast j))))) qz75) Bool.false 271650884367938335609 3602879701896396800 ep293 ep294

noncomputable def ep296 := @Enclosure.Real.IsNear.subLit_ff_p (Complex.im (@HSub.hSub Complex Complex Complex qz72 qz73 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz74 (@Nat.cast Complex Complex.instNatCast j))))) qz75 2293991155617256210781 18014398509481984000 693086513622984110239997 ep294 6808380813 131072000

noncomputable def ep297 := nat_lit 178029123579372067624714240000

noncomputable def ep298 := nat_lit 98762752000000000000000000

noncomputable def ep299 := @Enclosure.Complex.IsNear.im_isNear (@HSub.hSub Complex Complex Complex qz72 qz73 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz74 (@Nat.cast Complex Complex.instNatCast j)))) Bool.true 64232229632228426097 900719925474099200 18592498450524073658689 ep298 Bool.false 2293991155617256210781 18014398509481984000

noncomputable def ep300 := nat_lit 1678966784000000000000000000

noncomputable def ep301 := @Enclosure.Complex.IsNear.subLitP qz73 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz74 (@Nat.cast Complex Complex.instNatCast j))) Bool.true 57359392489772586697 900719925474099200 309518873640440617573713 ep300 Bool.false 2349989706446781394781 18014398509481984000 640657713616268243103997

noncomputable def ep302 := nat_lit 289276245436880071099068368774234112

noncomputable def ep303 := nat_lit 645701107101818035801769745984782336

noncomputable abbrev qz533 := (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (2 : Complex))

noncomputable abbrev qz514 := qz533

noncomputable abbrev qz363 := (@HSub.hSub Complex Complex Complex qz511 qz512 qz514)

noncomputable abbrev qz364 := (Complex.log qz512)

noncomputable abbrev qz76 := (@HSub.hSub Complex Complex Complex qz358 (@HMul.hMul Complex Complex Complex qz357 qz363 qz364) qz359)

noncomputable abbrev qz365 := qz514

noncomputable abbrev qz77 := (@HMul.hMul Complex Complex Complex qz357 qz365 ↑(Real.log qz271))

noncomputable abbrev qz515 := qz532

noncomputable abbrev qz366 := qz515

noncomputable abbrev qz78 := qz366

noncomputable abbrev qz79 := (@instHMul Nat instMulNat)

noncomputable abbrev qz516 := (@instHPow Complex Int (@ZPow.toPow Complex (@DivInvMonoid.toZPow Complex Complex.instDivInvMonoid)))

noncomputable abbrev qz367 := qz516

noncomputable abbrev qz80 := qz367

noncomputable abbrev qz81 := qz359

noncomputable abbrev qz368 := (@OfNat.ofNat Int 1 (@instOfNat 1))

noncomputable abbrev qz82 := qz368

noncomputable abbrev qz369 := (@OfNat.ofNat Int 2 (@instOfNat 2))

noncomputable abbrev qz83 := qz369

noncomputable abbrev qz370 := (@instHSub Int Int.instSub)

noncomputable abbrev qz371 := (@instHMul Int Int.instMul)

noncomputable def ep304 := @Enclosure.Complex.IsNear.of_eq qz73 (@HAdd.hAdd Complex Complex Complex qz4 (@HAdd.hAdd Complex Complex Complex qz4 qz76 qz77) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz79 2 k))) (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz71 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz80 qz81 (@HSub.hSub Int Int Int qz370 qz82 (@HMul.hMul Int Int Int qz371 qz83 (@Nat.cast Int instNatCastInt k)))))) Bool.true 57359392489772586697

noncomputable def ep305 := @Enclosure.Complex.IsNear.addLitP (@HAdd.hAdd Complex Complex Complex qz4 qz76 qz77) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz79 2 k))) (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz71 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz80 qz81 (@HSub.hSub Int Int Int qz370 qz82 (@HMul.hMul Int Int Int qz371 qz83 (@Nat.cast Int instNatCastInt k))))) Bool.true 57359474310315153097 900719925474099200

noncomputable def ep306 := nat_lit 985426859448005097363758645248

noncomputable def ep307 := nat_lit 20186257870251132910091320164352000

noncomputable def ep308 := @ep305 18891514920303520107 102476000000000000000000 Bool.false 2350022708489890410333 18014398509481984000 9775300025664678677 102476000000000000000000 Bool.false 1560603 17179869184 3 17179869184 Bool.true 15736600451 8589934592000 30251 8589934592000 Bool.true ep306 57359392489772586697 900719925474099200 309518873640440617573713 ep300 Bool.false ep307

noncomputable def ep309 := @Enclosure.Complex.IsNear.addLitP qz76 qz77 Bool.true 58187179791757252297 900719925474099200 18500600003311332607 102476000000000000000000

noncomputable def ep310 := nat_lit 7518221016801627746729984

noncomputable def ep311 := @ep309 Bool.false 2350022708489890410333 18014398509481984000 9775300025664678677 102476000000000000000000 Bool.false 120447 131072 1 262144 Bool.false 0 1 0 1 Bool.true ep310 57359474310315153097 900719925474099200 18891514920303520107 102476000000000000000000 Bool.false 2350022708489890410333 2350022708489890410333 18014398509481984000

noncomputable abbrev qz84 := (@HMul.hMul Complex Complex Complex qz357 qz363 qz364)

noncomputable def ep312 := @Enclosure.Complex.IsNear.subLitP qz84 qz81 Bool.true 56160559959440529097 900719925474099200 18500600003311332607 102476000000000000000000 Bool.false 3167453062455399657309

noncomputable def ep313 := nat_lit 9400090833959561641332000

noncomputable def ep314 := @ep312 18014398509481984000 9775300025664678677 102476000000000000000000 Bool.false 9000 4000 0 1 Bool.false 181506 4000 0 1 Bool.true 232748719167029009188000 58187179791757252297 900719925474099200 18500600003311332607 102476000000000000000000 Bool.false ep313 2350022708489890410333 18014398509481984000 9775300025664678677 102476000000000000000000

noncomputable abbrev qz85 := qz363

noncomputable abbrev qz86 := qz364

noncomputable def ep315 := @Enclosure.Complex.IsNear.mul qz85 qz86 Bool.true 56160559959440529097 900719925474099200 18500600003311332607 102476000000000000000000 Bool.false 3167453062455399657309 18014398509481984000 9775300025664678677

noncomputable abbrev qz87 := (Complex.re qz363)

noncomputable abbrev qz88 := (Complex.re qz364)

noncomputable abbrev qz89 := (Complex.im qz363)

noncomputable abbrev qz90 := (Complex.im qz364)

noncomputable def ep316 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 qz87 qz88) (@HMul.hMul Real Real Real qz0 qz89 qz90) 240614269956240971 36028797018963968 700000001972663 204952000000000000000 15543979177086638343 225179981368524800

noncomputable def ep317 := nat_lit 505849353812509529585329450174644224

noncomputable def ep318 := @Enclosure.Real.IsNear.mulLit_ff qz87 qz88 7000 4000 0 1 34373467136605853 9007199254740992 100000000281809 51238000000000000000

noncomputable def ep319 := @Enclosure.Complex.IsNear.re_isNear qz85 Bool.false 7000 4000 0 1 Bool.false 181506 4000 0 1

noncomputable abbrev qz372 := (Enclosure.sfrac Bool.false 181506 4000)

noncomputable abbrev qz91 := qz372

noncomputable def ep320 := @Enclosure.Complex.IsNear.of_eq qz85 (Complex.mk (Enclosure.sfrac Bool.false 7000 4000) qz91) Bool.false 7000 4000 0 1 Bool.false 181506 4000 0

noncomputable abbrev qz373 := (Enclosure.sfrac Bool.false 9000 4000)

noncomputable abbrev qz92 := qz373

noncomputable abbrev qz374 := (Complex.log (Complex.mk qz92 qz91))

noncomputable def ep321 := @Enclosure.Complex.IsNear.of_eq qz86 qz374 Bool.false 34373467136605853 9007199254740992 100000000281809 51238000000000000000 Bool.false 856389275125155 562949953421312 200000000025619 51238000000000000000

noncomputable def ep322 := BSN.log_dyadic_bound 257428036 65793428036 1 0 1 524288 256190 0 1 4102 66050856072 65536000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 257428036) (BSN.artanhQ 65793428036) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz93 := (Enclosure.sfrac Bool.false 1 2)

noncomputable abbrev qz375 := (Real.log (Enclosure.sfrac Bool.false 33025428036 16000000))

noncomputable abbrev qz376 := (Enclosure.Real.IsNear.const Bool.false 1 2)

noncomputable abbrev qz377 := (@Nat.cast Real Real.instNatCast 16000000)

noncomputable def ep323 := @Enclosure.Real.IsNear.mulLit_ff qz93 qz375 1 2 0 1 34373467136605853 4503599627370496 100000000281809 25619000000000000000 34373467136605853 9007199254740992 100000000281809 51238000000000000000 qz376 (BSN.isNear_log_sfrac 33025428036 16000000 34373467136605853 4503599627370496 100000000281809 25619000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 33025428036) qz377)) Bool.false 144172770704934475661312 18889465931478580854784 1000000002818090 256190000000000000000 34373467136605853 4503599627370496 100000000281809 25619000000000000000 (BSN.log_rat_reduce_isNear 33025428036 16000000 11 66050856072 65536000000 4102 524288 24973259072661432 36028797018963968 256190 1000000000000000 rfl rfl rfl rfl (ep322 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep324 := BSN.arctan_dyadic_bound_f 9000 181506 1 0 524288 256190 0 1 1 0 1 1 25975 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 9000) (BSN.arctanEvenQ 181506) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 9000) (BSN.arctanOddQ 181506) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz94 := (@HMul.hMul Real Real Real qz267 (Enclosure.sfrac Bool.false 1 2) Real.pi)

noncomputable abbrev qz95 := (@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 2) Real.pi 1 2 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 qz376 BSN.pi_near_15 rfl)

noncomputable abbrev qz378 := (Real.arctan (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 9000) (@Nat.cast Real Real.instNatCast 181506)))

noncomputable def ep325 := @Enclosure.Real.IsNear.subLit_ff_p qz94 qz378 884279719003555 562949953421312 1 2000000000000000 25975 524288 1 256190 448994620276817264640 856389275125155 562949953421312 200000000025619 51238000000000000000 qz95 (ep324 rfl) rfl rfl

noncomputable abbrev qz379 := (Real.arctan (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 181506) (@Nat.cast Real Real.instNatCast 9000)))

noncomputable def ep326 := @Enclosure.Complex.IsNear.re_isNear qz86 Bool.false 34373467136605853 9007199254740992 100000000281809 51238000000000000000 Bool.false 856389275125155 562949953421312 200000000025619 51238000000000000000 (ep321 (@congrArg Complex Complex qz81 (Complex.mk qz92 qz91) Complex.log (BSN.w_shift_mk qz16 Bool.false 90753 1000 2 qz17 rfl)) (@Enclosure.Complex.IsNear.of_parts qz374 Bool.false 34373467136605853 9007199254740992 100000000281809 51238000000000000000 Bool.false 856389275125155 562949953421312 200000000025619 51238000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz374) (@HMul.hMul Real Real Real qz0 qz93 qz375) Bool.false 34373467136605853 9007199254740992 100000000281809 51238000000000000000 (Enclosure.clog_re_eq 9000 181506 4000 33025428036 16000000 rfl rfl rfl) (ep323 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz374) qz379 Bool.false 856389275125155 562949953421312 200000000025619 51238000000000000000 (Enclosure.clog_im_eq 9000 181506 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz379 (@HSub.hSub Real Real Real qz361 qz94 qz378) Bool.false 856389275125155 562949953421312 200000000025619 51238000000000000000 (BSN.arctan_recip 181506 9000 rfl rfl) ep325))))

noncomputable def ep327 := @Enclosure.Real.IsNear.mulLit_ff qz89 qz90 181506 4000 0 1 856389275125155 562949953421312 200000000025619 51238000000000000000

noncomputable def ep328 := @Enclosure.Complex.IsNear.im_isNear qz85 Bool.false 7000 4000 0 1 Bool.false 181506 4000 0 1

noncomputable def ep329 := @Enclosure.Complex.IsNear.im_isNear qz86 Bool.false 34373467136605853 9007199254740992 100000000281809 51238000000000000000 Bool.false 856389275125155 562949953421312 200000000025619 51238000000000000000 (ep321 (@congrArg Complex Complex qz81 (Complex.mk qz92 qz91) Complex.log (BSN.w_shift_mk qz16 Bool.false 90753 1000 2 qz17 rfl)) (@Enclosure.Complex.IsNear.of_parts qz374 Bool.false 34373467136605853 9007199254740992 100000000281809 51238000000000000000 Bool.false 856389275125155 562949953421312 200000000025619 51238000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz374) (@HMul.hMul Real Real Real qz0 qz93 qz375) Bool.false 34373467136605853 9007199254740992 100000000281809 51238000000000000000 (Enclosure.clog_re_eq 9000 181506 4000 33025428036 16000000 rfl rfl rfl) (ep323 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz374) qz379 Bool.false 856389275125155 562949953421312 200000000025619 51238000000000000000 (Enclosure.clog_im_eq 9000 181506 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz379 (@HSub.hSub Real Real Real qz361 qz94 qz378) Bool.false 856389275125155 562949953421312 200000000025619 51238000000000000000 (BSN.arctan_recip 181506 9000 rfl rfl) ep325))))

noncomputable abbrev qz380 := (Enclosure.Real.IsNear.const Bool.false 181506 4000)

noncomputable abbrev qz96 := (@ep320 1 (BSN.w_sub_half_mk qz280 Bool.false 90753 1000 2 qz282 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7000 4000) qz372 Bool.false 7000 4000 0 1 Bool.false 181506 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 7000 4000) qz380))

noncomputable def ep330 := @ep316 18150600002325001107 102476000000000000000000 ep317 56160559959440529097 900719925474099200 18500600003311332607 102476000000000000000000 (@ep318 240614269956240971 36028797018963968 700000001972663 204952000000000000000 (ep319 qz96) ep326 rfl) (@ep327 15543979177086638343 225179981368524800 18150600002325001107 102476000000000000000000 (ep328 qz96) ep329 rfl) rfl

noncomputable def ep331 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz87 qz90) (@HMul.hMul Real Real Real qz0 qz89 qz88) 5994724925876085 2251799813685248 1400000000179333 204952000000000000000 3119495263048390977309 18014398509481984000

noncomputable def ep332 := nat_lit 7132470215893837145310107987588677632

noncomputable def ep333 := @Enclosure.Real.IsNear.mulLit_ff qz87 qz90 7000 4000 0 1 856389275125155 562949953421312 200000000025619 51238000000000000000

noncomputable def ep334 := @Enclosure.Real.IsNear.mulLit_ff qz89 qz88 181506 4000 0 1 34373467136605853 9007199254740992 100000000281809 51238000000000000000

noncomputable def ep335 := @ep331 9075300025575012177 102476000000000000000000 ep332 3167453062455399657309 18014398509481984000 9775300025664678677 102476000000000000000000 (@ep333 5994724925876085 2251799813685248 1400000000179333 204952000000000000000 (ep319 qz96) ep329 rfl) (@ep334 3119495263048390977309 18014398509481984000 9075300025575012177 102476000000000000000000 (ep328 qz96) ep326 rfl) rfl

noncomputable def ep336 := @Enclosure.Complex.IsNear.of_eq qz81 (Complex.mk qz92 qz91) Bool.false 9000 4000 0 1 Bool.false 181506 4000 0 1 (BSN.w_shift_mk qz16 Bool.false 90753 1000 2 qz17 rfl)

noncomputable abbrev qz381 := (ep336 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 9000 4000) (Enclosure.sfrac Bool.false 181506 4000) Bool.false 9000 4000 0 1 Bool.false 181506 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 9000 4000) (Enclosure.Real.IsNear.const Bool.false 181506 4000)))

noncomputable abbrev qz97 := qz381

noncomputable def ep337 := ep314 (@ep315 102476000000000000000000 (ep330 rfl) (ep335 rfl)) qz97 rfl rfl rfl rfl rfl rfl

noncomputable abbrev qz98 := qz365

noncomputable def ep338 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re qz98) (Complex.re ↑qz2)) (@HMul.hMul Real Real Real qz0 (Complex.im qz98) (Complex.im ↑qz2)) 120447 131072 1 262144 0 1 0 1 120447 120447

noncomputable def ep339 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re qz98) (Complex.re ↑qz2) 1 2 0 1 120447 65536 1 131072 120447 131072 1 262144

noncomputable abbrev qz99 := (@Enclosure.Complex.IsNear.of_eq qz365 (Complex.mk (Enclosure.sfrac Bool.false 1 2) qz278) Bool.false 1 2 0 1 Bool.false 0 1 0 1 BSN.half_c_mk (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 2) qz278 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz376 qz292))

noncomputable def ep340 := ep339 (@Enclosure.Complex.IsNear.re_isNear qz98 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz99) (@Enclosure.Real.IsNear.of_eq (Complex.re ↑qz2) qz2 Bool.false 120447 65536 1 131072 (Complex.ofReal_re qz2) EMRow26.d4)

noncomputable def ep341 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz98) (Complex.im ↑qz2) 0 1 0 1 0 1 0 1 0 1 0 1

noncomputable def ep342 := ep341 (@Enclosure.Complex.IsNear.im_isNear qz98 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz99) (@Enclosure.Real.IsNear.of_eq (Complex.im ↑qz2) qz13 Bool.false 0 1 0 1 (@Eq.trans Real (Complex.im ↑qz2) (0 : Real) qz13 (Complex.ofReal_im qz2) Enclosure.sfrac_zero_eq) qz22)

noncomputable def ep343 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re qz98) (Complex.im ↑qz2)) (@HMul.hMul Real Real Real qz0 (Complex.im qz98) (Complex.re ↑qz2)) 0 1 0 1 0 1 0 1 0 0

noncomputable def ep344 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re qz98) (Complex.im ↑qz2) 1 2 0 1 0 1 0 1 0 1 0 1

noncomputable def ep345 := ep344 (@Enclosure.Complex.IsNear.re_isNear qz98 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz99) (@Enclosure.Real.IsNear.of_eq (Complex.im ↑qz2) qz13 Bool.false 0 1 0 1 (@Eq.trans Real (Complex.im ↑qz2) (0 : Real) qz13 (Complex.ofReal_im qz2) Enclosure.sfrac_zero_eq) qz22)

noncomputable def ep346 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz98) (Complex.re ↑qz2) 0 1 0 1 120447 65536 1 131072 0 1 0 1

noncomputable def ep347 := ep346 (@Enclosure.Complex.IsNear.im_isNear qz98 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz99) (@Enclosure.Real.IsNear.of_eq (Complex.re ↑qz2) qz2 Bool.false 120447 65536 1 131072 (Complex.ofReal_re qz2) EMRow26.d4)

noncomputable def ep348 := @ep311 9775300025664678677 102476000000000000000000 (ep337 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@Enclosure.Complex.IsNear.mul qz98 (↑qz2) Bool.false 120447 131072 1 262144 Bool.false 0 1 0 1 (@ep338 131072 1 262144 (ep340 rfl) (ep342 rfl) rfl rfl) (@ep343 1 0 1 (ep345 rfl) (ep347 rfl) rfl rfl))

noncomputable abbrev qz100 := (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 1)

noncomputable abbrev qz382 := (@Nat.cast Complex Complex.instNatCast 1)

noncomputable abbrev qz101 := (@HMul.hMul Complex Complex Complex qz357 (@HMul.hMul Complex Complex Complex qz357 (2 : Complex) qz382) (@HSub.hSub Complex Complex Complex qz358 (@HMul.hMul Complex Complex Complex qz357 (2 : Complex) qz382) (1 : Complex)))

noncomputable abbrev qz383 := (@HPow.hPow Complex Int Complex qz516 qz512 (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) (@OfNat.ofNat Int 1 (@instOfNat 1)) (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (@OfNat.ofNat Int 2 (@instOfNat 2)) (@Nat.cast Int instNatCastInt 1))))

noncomputable abbrev qz102 := qz383

noncomputable def ep349 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz79 2 k))) (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz71 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz80 qz81 (@HSub.hSub Int Int Int qz370 qz82 (@HMul.hMul Int Int Int qz371 qz83 (@Nat.cast Int instNatCastInt k))))) (@HAdd.hAdd Complex Complex Complex qz4 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz79 2 k))) (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz71 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz80 qz81 (@HSub.hSub Int Int Int qz370 qz82 (@HMul.hMul Int Int Int qz371 qz83 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 (@Rat.cast Complex Complex.instRatCast (bernoulli qz100)) qz101) qz102)) Bool.false 1560603 17179869184 3 17179869184

noncomputable def ep350 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz79 2 k))) (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz71 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz80 qz81 (@HSub.hSub Int Int Int qz370 qz82 (@HMul.hMul Int Int Int qz371 qz83 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 (@Rat.cast Complex Complex.instRatCast (bernoulli qz100)) qz101) qz102) Bool.false 0 1 0 1 Bool.false

noncomputable def ep351 := @ep350 0 1 0 1 Bool.false 1560603 17179869184 3 17179869184 Bool.true 15736600451 8589934592000 30251 8589934592000 Bool.false 1560603 1560603 17179869184 3 17179869184 Bool.true 15736600451 15736600451 8589934592000 30251

noncomputable def ep352 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz79 2 k))) (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz71 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz80 qz81 (@HSub.hSub Int Int Int qz370 qz82 (@HMul.hMul Int Int Int qz371 qz83 (@Nat.cast Int instNatCastInt k))))) (Complex.mk qz13 qz13) Bool.false 0 1 0 1 Bool.false

noncomputable def ep353 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz78 (@Rat.cast Complex Complex.instRatCast (bernoulli qz100)) qz101) qz102 Bool.false 1560603 17179869184 3 17179869184 Bool.true 15736600451 8589934592000 30251 8589934592000

noncomputable abbrev qz103 := (Complex.re qz383)

noncomputable abbrev qz104 := (Complex.im qz383)

noncomputable def ep354 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz78 (@Rat.cast Complex Complex.instRatCast (bernoulli qz100)) qz101)) qz103) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz78 (@Rat.cast Complex Complex.instRatCast (bernoulli qz100)) qz101)) qz104) 1560603 17179869184 3 17179869184 0 1 0

noncomputable def ep355 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz78 (@Rat.cast Complex Complex.instRatCast (bernoulli qz100)) qz101)) qz103 1 12 0 1 4681809 4294967296 9 4294967296 1560603

noncomputable def ep356 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz78 (@Rat.cast Complex Complex.instRatCast (bernoulli qz100)) qz101) (Complex.mk (Enclosure.sfrac Bool.false 1 12) qz13) Bool.false 1 12 0 1 Bool.false 0 1 0 1

noncomputable abbrev qz384 := (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 12) qz13 Bool.false 1 12 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 12) qz22)

noncomputable def ep357 := @Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz78 (@Rat.cast Complex Complex.instRatCast (bernoulli qz100)) qz101) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (ep356 (BSN.stirling_coeff_mk 1 1 6 Bool.false BSN.bern_real_1 rfl rfl) qz384)

noncomputable def ep358 := @Enclosure.Complex.IsNear.re_isNear qz102 Bool.false 4681809 4294967296 9 4294967296 Bool.true 47209801353 2147483648000 90753 2147483648000

noncomputable abbrev qz517 := (@instHPow Complex Nat (@NPow.toPow Complex (@Monoid.toNPow Complex (@Semiring.toMonoid Complex Complex.instSemiring))))

noncomputable abbrev qz385 := (@HPow.hPow Complex Nat Complex qz517 qz512 1)

noncomputable abbrev qz105 := (@Inv.inv Complex Complex.instInv qz385)

noncomputable def ep359 := @Enclosure.Complex.IsNear.of_eq qz102 qz105 Bool.false 4681809 4294967296 9 4294967296 Bool.true 47209801353 2147483648000 90753

noncomputable def ep360 := @Enclosure.Complex.IsNear.of_parts qz105 Bool.false 4681809 4294967296 9 4294967296 Bool.true 47209801353 2147483648000 90753

noncomputable abbrev qz106 := (Complex.re qz385)

noncomputable abbrev qz107 := (@MonoidWithZeroHom Complex Real (@instMulZeroOneClassOfSemiring Complex Complex.instSemiring) (@instMulZeroOneClassOfSemiring Real Real.semiring))

noncomputable abbrev qz108 := (@MonoidWithZeroHom.funLike Complex Real (@instMulZeroOneClassOfSemiring Complex Complex.instSemiring) (@instMulZeroOneClassOfSemiring Real Real.semiring))

noncomputable abbrev qz109 := qz385

noncomputable def ep361 := @Enclosure.Real.IsNear.mulLit_ff qz106 (@Inv.inv Real Real.instInv (@DFunLike.coe qz107 Complex (fun (x : Complex) => Real) qz108 Complex.normSq qz109)) 9000 4000 0 1 520201 1073741824 1 1073741824

noncomputable def ep362 := @Enclosure.Complex.IsNear.re_isNear qz109 Bool.false 9000 4000 0 1 Bool.false 181506 4000 0 1

noncomputable def ep363 := @Enclosure.Complex.IsNear.of_eq qz109 qz81 Bool.false 9000 4000 0 1 Bool.false 181506 4000 0

noncomputable def ep364 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (@DFunLike.coe qz107 Complex (fun (x : Complex) => Real) qz108 Complex.normSq qz109)) Bool.false 520201 1073741824 1 1073741824 520201 1073741824 1

noncomputable abbrev qz110 := (Complex.im qz385)

noncomputable abbrev qz386 := (@instHAdd Real Real.instAdd)

noncomputable def ep365 := @Enclosure.Real.IsNear.of_eq (@DFunLike.coe qz107 Complex (fun (x : Complex) => Real) qz108 Complex.normSq qz109) (@HAdd.hAdd Real Real Real qz386 (@HMul.hMul Real Real Real qz0 qz106 qz106) (@HMul.hMul Real Real Real qz0 qz110 qz110)) Bool.false 8256357009 4000000 0 1

noncomputable def ep366 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz106 qz106) (@HMul.hMul Real Real Real qz0 qz110 qz110) 81 16 0 1 8236107009 4000000

noncomputable def ep367 := @Enclosure.Real.IsNear.mulLit_ff qz106 qz106 9000 4000 0 1 9000 4000 0 1

noncomputable def ep368 := @Enclosure.Real.IsNear.mulLit_ff qz110 qz110 181506 4000 0 1 181506 4000 0 1

noncomputable def ep369 := @Enclosure.Complex.IsNear.im_isNear qz109 Bool.false 9000 4000 0 1 Bool.false 181506 4000 0 1

noncomputable abbrev qz111 := (ep362 (@ep363 1 (BSN.pow_one_c qz359) qz381))

noncomputable abbrev qz112 := (ep369 (@ep363 1 (BSN.pow_one_c qz359) qz381))

noncomputable def ep370 := @ep366 0 1 132101712144 8256357009 4000000 0 1 (@ep367 81 16 0 1 qz111 qz111 rfl) (@ep368 8236107009 4000000 0 1 qz112 qz112 rfl)

noncomputable def ep371 := @Enclosure.Real.IsNear.inv_image (@DFunLike.coe qz107 Complex (fun (x : Complex) => Real) qz108 Complex.normSq qz109) 8256357009 4000000 0 1 260100 260101 536870912 (ep365 (Enclosure.Complex.normSq_eq_mul_add_mul qz109) (ep370 rfl rfl)) rfl

noncomputable def ep372 := @Enclosure.Real.IsNear.of_eq (Complex.re qz105) (@HMul.hMul Real Real Real qz0 qz106 (@Inv.inv Real Real.instInv (@DFunLike.coe qz107 Complex (fun (x : Complex) => Real) qz108 Complex.normSq qz109))) Bool.false 4681809 4294967296 9 4294967296 (Enclosure.Complex.inv_re_eq_mul qz109) (@ep361 4681809 4294967296 9 4294967296 qz111 (@ep364 1073741824 (ep371 rfl rfl rfl rfl rfl) rfl) rfl)

noncomputable def ep373 := @Enclosure.Real.IsNear.of_eq (Complex.im qz105) (@HMul.hMul Real Real Real qz0 (@Neg.neg Real Real.instNeg qz110) (@Inv.inv Real Real.instInv (@DFunLike.coe qz107 Complex (fun (x : Complex) => Real) qz108 Complex.normSq qz109))) Bool.true 47209801353 2147483648000 90753 2147483648000 (Enclosure.Complex.inv_im_eq_mul qz109)

noncomputable def ep374 := @Enclosure.Real.IsNear.mulLit_tf (@Neg.neg Real Real.instNeg qz110) (@Inv.inv Real Real.instInv (@DFunLike.coe qz107 Complex (fun (x : Complex) => Real) qz108 Complex.normSq qz109)) 181506 4000 0 1 520201 1073741824 1

noncomputable def ep375 := @ep374 1073741824 47209801353 2147483648000 90753 2147483648000 (@Enclosure.Real.IsNear.neg qz110 Bool.false 181506 4000 0 1 qz112) (@ep364 1073741824 (ep371 rfl rfl rfl rfl rfl) rfl) rfl

noncomputable def ep376 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz78 (@Rat.cast Complex Complex.instRatCast (bernoulli qz100)) qz101)) qz104 0 1 0 1 47209801353 2147483648000 90753 2147483648000 0

noncomputable def ep377 := @Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz78 (@Rat.cast Complex Complex.instRatCast (bernoulli qz100)) qz101) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (ep356 (BSN.stirling_coeff_mk 1 1 6 Bool.false BSN.bern_real_1 rfl rfl) qz384)

noncomputable def ep378 := @Enclosure.Complex.IsNear.im_isNear qz102 Bool.false 4681809 4294967296 9 4294967296 Bool.true 47209801353 2147483648000 90753 2147483648000

noncomputable abbrev qz113 := (@ep359 2147483648000 (BSN.zpow_one_sub_two_mul qz359 1 1 rfl rfl) (@ep360 2147483648000 ep372 (ep373 ep375)))

noncomputable def ep379 := @ep354 1 1560603 1560603 17179869184 3 17179869184 (@ep355 17179869184 3 17179869184 ep357 (ep358 qz113) rfl) (@ep376 1 0 1 ep377 (ep378 qz113) rfl) rfl

noncomputable def ep380 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz78 (@Rat.cast Complex Complex.instRatCast (bernoulli qz100)) qz101)) qz104) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz78 (@Rat.cast Complex Complex.instRatCast (bernoulli qz100)) qz101)) qz103) 15736600451 8589934592000 30251 8589934592000 0 1 0

noncomputable def ep381 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HDiv.hDiv Complex Complex Complex qz78 (@Rat.cast Complex Complex.instRatCast (bernoulli qz100)) qz101)) qz104 1 12 0 1 47209801353 2147483648000 90753 2147483648000 15736600451

noncomputable def ep382 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz78 (@Rat.cast Complex Complex.instRatCast (bernoulli qz100)) qz101)) qz103 0 1 0 1 4681809 4294967296 9 4294967296 0

noncomputable def ep383 := @ep380 1 15736600451 15736600451 8589934592000 30251 8589934592000 (@ep381 8589934592000 30251 8589934592000 ep357 (ep378 qz113) rfl) (@ep382 1 0 1 ep377 (ep358 qz113) rfl) rfl

noncomputable abbrev qz114 := (@Enclosure.Complex.IsNear.mk qz278 qz278 Bool.false 0 1 0 1 Bool.false 0 1 0 1 qz292 qz292)

noncomputable def ep384 := @ep351 8589934592000 (@ep352 0 1 0 1 (BSN.stirling_sum_base qz81) qz114) (ep353 (ep379 rfl) (ep383 rfl)) rfl rfl rfl rfl rfl

noncomputable def ep385 := @ep308 2349989706446781394781 18014398509481984000 640657713616268243103997 ep294 (ep348 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep349 Bool.true 15736600451 8589934592000 30251 8589934592000 (BSN.stirling_sum_succ qz81 0 1 rfl) (ep384 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl

noncomputable def ep386 := @Enclosure.Complex.IsNear.of_eq (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz74 (@Nat.cast Complex Complex.instNatCast j))) (BSN.logSumC qz16 2) Bool.false 34364185712279197 4503599627370496 100000000281809 25619000000000000000 Bool.false 874977356711331 281474976710656

noncomputable abbrev qz115 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz273 qz360 qz382))

noncomputable def ep387 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz16 2) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.logSumC qz16 1) qz115) Bool.false 34364185712279197 4503599627370496 100000000281809 25619000000000000000 Bool.false 874977356711331 281474976710656 200000000025619 25619000000000000000

noncomputable def ep388 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz16 1) qz115 Bool.false 34362549329739421 9007199254740992 100000000281809 51238000000000000000 Bool.false 881178752615843 562949953421312 200000000025619 51238000000000000000 Bool.false

noncomputable def ep389 := nat_lit 619050135874844457114864449486848

noncomputable def ep390 := nat_lit 985136924410692962256414572544

noncomputable abbrev qz116 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz273 qz360 (@Nat.cast Complex Complex.instNatCast 0)))

noncomputable def ep391 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz16 1) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.logSumC qz16 0) qz116) Bool.false 34362549329739421 9007199254740992 100000000281809 51238000000000000000 Bool.false 881178752615843 562949953421312 200000000025619 51238000000000000000

noncomputable def ep392 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz16 0) qz116 Bool.false 0 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable abbrev qz387 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz91))

noncomputable def ep393 := @Enclosure.Complex.IsNear.of_eq qz116 qz387 Bool.false 34362549329739421 9007199254740992 100000000281809 51238000000000000000 Bool.false 881178752615843 562949953421312 200000000025619 51238000000000000000

noncomputable def ep394 := BSN.log_dyadic_bound 177428036 65713428036 1 0 1 524288 256190 0 1 2831 65890856072 65536000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 177428036) (BSN.artanhQ 65713428036) 0 0 rfl) rfl rfl rfl

noncomputable def ep395 := @Enclosure.Real.IsNear.mulLit_ff qz93 (Real.log (Enclosure.sfrac Bool.false 32945428036 16000000)) 1 2 0 1 34362549329739421 4503599627370496 100000000281809 25619000000000000000 34362549329739421 9007199254740992 100000000281809 51238000000000000000 qz376 (BSN.isNear_log_sfrac 32945428036 16000000 34362549329739421 4503599627370496 100000000281809 25619000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 32945428036) qz377)) Bool.false 144126978103923372457984 18889465931478580854784 1000000002818090 256190000000000000000 34362549329739421 4503599627370496 100000000281809 25619000000000000000 (BSN.log_rat_reduce_isNear 32945428036 16000000 11 65890856072 65536000000 2831 524288 24973259072661432 36028797018963968 256190 1000000000000000 rfl rfl rfl rfl (ep394 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep396 := BSN.arctan_dyadic_bound_f 1000 181506 1 0 524288 256190 0 1 1 0 1 1 2888 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 181506) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 181506) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz388 := (@Nat.cast Real Real.instNatCast 1000)

noncomputable abbrev qz389 := (@Nat.cast Real Real.instNatCast 181506)

noncomputable def ep397 := @Enclosure.Real.IsNear.subLit_ff_p qz94 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz388 qz389)) 884279719003555 562949953421312 1 2000000000000000 2888 524288 1 256190 461991445851455094784 881178752615843 562949953421312 200000000025619 51238000000000000000 qz95 (ep396 rfl) rfl rfl

noncomputable abbrev qz117 := (@HAdd.hAdd Complex Complex Complex qz273 qz360 (@Nat.cast Complex Complex.instNatCast 0))

noncomputable abbrev qz390 := (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz91)

noncomputable def ep398 := @ep392 34362549329739421 9007199254740992 100000000281809 51238000000000000000 Bool.false 881178752615843 562949953421312 200000000025619 51238000000000000000 Bool.false 34362549329739421 34362549329739421 9007199254740992 100000000281809 51238000000000000000 Bool.false 881178752615843 881178752615843 562949953421312 200000000025619 51238000000000000000 (@Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz16 0) (Complex.mk qz13 qz13) Bool.false 0 1 0 1 Bool.false 0 1 0 1 (BSN.log_sum_c_base qz16) qz114) (ep393 (@congrArg Complex Complex qz117 qz390 Complex.log (BSN.w_shift_mk qz16 Bool.false 90753 1000 0 qz17 rfl)) (@Enclosure.Complex.IsNear.of_parts qz387 Bool.false 34362549329739421 9007199254740992 100000000281809 51238000000000000000 Bool.false 881178752615843 562949953421312 200000000025619 51238000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz387) (@HMul.hMul Real Real Real qz0 qz93 (Real.log (Enclosure.sfrac Bool.false 32945428036 16000000))) Bool.false 34362549329739421 9007199254740992 100000000281809 51238000000000000000 (Enclosure.clog_re_eq 1000 181506 4000 32945428036 16000000 rfl rfl rfl) (ep395 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz387) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz389 qz388)) Bool.false 881178752615843 562949953421312 200000000025619 51238000000000000000 (Enclosure.clog_im_eq 1000 181506 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz389 qz388)) (@HSub.hSub Real Real Real qz361 qz94 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz388 qz389))) Bool.false 881178752615843 562949953421312 200000000025619 51238000000000000000 (BSN.arctan_recip 181506 1000 rfl rfl) ep397)))) rfl rfl

noncomputable abbrev qz391 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz91))

noncomputable def ep399 := @Enclosure.Complex.IsNear.of_eq qz115 qz391 Bool.false 34365822094818973 9007199254740992 100000000281809 51238000000000000000 Bool.false 868775960806819 562949953421312 200000000025619 51238000000000000000

noncomputable def ep400 := BSN.log_dyadic_bound 201428036 65737428036 1 0 1 524288 256190 0 1 3212 65938856072 65536000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 201428036) (BSN.artanhQ 65737428036) 0 0 rfl) rfl rfl rfl

noncomputable def ep401 := @Enclosure.Real.IsNear.mulLit_ff qz93 (Real.log (Enclosure.sfrac Bool.false 32969428036 16000000)) 1 2 0 1 34365822094818973 4503599627370496 100000000281809 25619000000000000000 34365822094818973 9007199254740992 100000000281809 51238000000000000000 qz376 (BSN.isNear_log_sfrac 32969428036 16000000 34365822094818973 4503599627370496 100000000281809 25619000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 32969428036) qz377)) Bool.false 144140705075587597729792 18889465931478580854784 1000000002818090 256190000000000000000 34365822094818973 4503599627370496 100000000281809 25619000000000000000 (BSN.log_rat_reduce_isNear 32969428036 16000000 11 65938856072 65536000000 3212 524288 24973259072661432 36028797018963968 256190 1000000000000000 rfl rfl rfl rfl (ep400 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep402 := BSN.arctan_dyadic_bound_f 5000 181506 1 0 524288 256190 0 1 1 0 1 1 14439 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 5000) (BSN.arctanEvenQ 181506) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 5000) (BSN.arctanOddQ 181506) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz392 := (@Nat.cast Real Real.instNatCast 5000)

noncomputable def ep403 := @Enclosure.Real.IsNear.subLit_ff_p qz94 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz392 qz389)) 884279719003555 562949953421312 1 2000000000000000 14439 524288 1 256190 455488810939485519872 868775960806819 562949953421312 200000000025619 51238000000000000000 qz95 (ep402 rfl) rfl rfl

noncomputable abbrev qz118 := (@HAdd.hAdd Complex Complex Complex qz273 qz360 qz382)

noncomputable abbrev qz393 := (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz91)

noncomputable def ep404 := @ep388 34365822094818973 9007199254740992 100000000281809 51238000000000000000 Bool.false 868775960806819 562949953421312 200000000025619 51238000000000000000 Bool.false ep389 34364185712279197 4503599627370496 100000000281809 25619000000000000000 Bool.false ep390 874977356711331 281474976710656 200000000025619 25619000000000000000 (ep391 (BSN.log_sum_c_succ qz16 0 1 rfl) (ep398 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep399 (@congrArg Complex Complex qz118 qz393 Complex.log (BSN.w_shift_mk qz16 Bool.false 90753 1000 1 qz17 rfl)) (@Enclosure.Complex.IsNear.of_parts qz391 Bool.false 34365822094818973 9007199254740992 100000000281809 51238000000000000000 Bool.false 868775960806819 562949953421312 200000000025619 51238000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz391) (@HMul.hMul Real Real Real qz0 qz93 (Real.log (Enclosure.sfrac Bool.false 32969428036 16000000))) Bool.false 34365822094818973 9007199254740992 100000000281809 51238000000000000000 (Enclosure.clog_re_eq 5000 181506 4000 32969428036 16000000 rfl rfl rfl) (ep401 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz391) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz389 qz392)) Bool.false 868775960806819 562949953421312 200000000025619 51238000000000000000 (Enclosure.clog_im_eq 5000 181506 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz389 qz392)) (@HSub.hSub Real Real Real qz361 qz94 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz392 qz389))) Bool.false 868775960806819 562949953421312 200000000025619 51238000000000000000 (BSN.arctan_recip 181506 5000 rfl rfl) ep403)))) rfl rfl

noncomputable def ep405 := @ep301 ep294 Bool.false 34364185712279197 4503599627370496 100000000281809 25619000000000000000 Bool.false 874977356711331 281474976710656 200000000025619 25619000000000000000 Bool.true ep302 64232229632228426097 900719925474099200 18592498450524073658689 ep298 Bool.false ep303 2293991155617256210781 18014398509481984000 693086513622984110239997 ep294 (@ep304 900719925474099200 309518873640440617573713 ep300 Bool.false 2349989706446781394781 18014398509481984000 640657713616268243103997 ep294 (BSN.logGammaStirling_unfold 1 qz81) (ep385 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (@ep386 200000000025619 25619000000000000000 (BSN.log_sum_c_eq qz16 2) (ep387 (BSN.log_sum_c_succ qz16 1 2 rfl) (ep404 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)))

noncomputable abbrev qz119 := (@HDiv.hDiv Real Real Real qz270 qz280 (2 : Real))

noncomputable def ep406 := @Enclosure.Real.IsNear.mulLit_ff qz119 (Real.log Real.pi) 90753 2000 0 1 75021 65536 1 131072 6808380813 131072000 90753 262144000 (@Enclosure.Real.IsNear.of_eq qz119 (Enclosure.sfrac Bool.false 90753 2000) Bool.false 90753 2000 0 1 (BSN.t_half_eq qz16 Bool.false 90753 1000 qz17) (Enclosure.Real.IsNear.const Bool.false 90753 2000)) EMRow26.d5 rfl

noncomputable def ep407 := @ep296 90753 262144000 ep297 271650884367938335609 3602879701896396800 ep293 ep294 (@ep299 693086513622984110239997 ep294 (ep405 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) ep406 rfl rfl

noncomputable def ep408 := BSN.cos_dyadic_bound_f 45260 1073741824 1 0 524288 256441 0 1 1 0 1 1 524287 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 45260) qz283 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 45260) qz284 0 0 rfl) rfl rfl

noncomputable def ep409 := @ep292 524288 Bool.false 524287 524288 1 128095 (@ep295 19765203 262144 237 524288 ep407 rfl) (Enclosure.sfrac_false_div 19765203 262144) (BSN.cos_reduce0 qz362 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 1592475216884269056) qz288) 226375608064910080 72057594037927936 Bool.false 524287 524288 12 1000000000000000 256190 128095 (BSN.sin_reduce_arg_pos_rat_q0 19765203 262144 226375608064910080 72057594037927936 12 1592475216884269056 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 524287 524288 1592475216884269056 37778931862957161709568 45260 1073741824 256441 256190 (ep408 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep410 := nat_lit 1498119599684262945632771

noncomputable def ep411 := nat_lit 21507929467035909619712000

noncomputable def ep412 := nat_lit 3756427573762251471067459627

noncomputable def ep413 := nat_lit 826517467523989452821102592000

noncomputable abbrev qz120 := qz274

noncomputable abbrev qz121 := qz275

noncomputable abbrev qz518 := (@Nat.cast Complex Complex.instNatCast 19)

noncomputable abbrev qz394 := (@HPow.hPow Complex Complex Complex qz505 qz518 qz506)

noncomputable abbrev qz122 := qz394

noncomputable abbrev qz395 := qz518

noncomputable abbrev qz123 := (@HAdd.hAdd Complex Complex Complex qz273 (@HDiv.hDiv Complex Complex Complex qz366 qz395 (@HSub.hSub Complex Complex Complex qz358 qz272 (1 : Complex))) qz365)

noncomputable abbrev qz124 := (@instHSub Nat instSubNat)

noncomputable abbrev qz396 := qz517

noncomputable abbrev qz125 := qz396

noncomputable abbrev qz126 := qz395

noncomputable def ep414 := @Enclosure.Complex.IsNear.of_eq (zetaApproximant qz5 1 19) (@HAdd.hAdd Complex Complex Complex qz4 (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 19, @HPow.hPow Complex Complex Complex qz120 (@Nat.cast Complex Complex.instNatCast n) qz121) (@HMul.hMul Complex Complex Complex qz71 qz122 (@HAdd.hAdd Complex Complex Complex qz4 qz123 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz79 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz79 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz125 qz126 (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1))))))) Bool.false ep287 ep288 ep289

noncomputable def ep415 := @Enclosure.Complex.IsNear.addLitP (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 19, @HPow.hPow Complex Complex Complex qz120 (@Nat.cast Complex Complex.instNatCast n) qz121) (@HMul.hMul Complex Complex Complex qz71 qz122 (@HAdd.hAdd Complex Complex Complex qz4 qz123 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz79 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz79 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz125 qz126 (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1)))))) Bool.false 635761183857 137438953472 3548050850637 800238306590720

noncomputable def ep416 := nat_lit 10398003810807721384935159

noncomputable def ep417 := nat_lit 50611240278062942649819699

noncomputable def ep418 := nat_lit 94500414908493152690299177

noncomputable def ep419 := nat_lit 53266536039147138716073380414018813952

noncomputable def ep420 := nat_lit 411799979912993361750872158134861824

noncomputable def ep421 := @ep415 Bool.false 25159250813 274877906944 14181984064963 3200953226362880 Bool.true ep416 ep288 ep417 ep290 Bool.true 470475832176731288378729 ep411 ep418 ep413 Bool.false ep419 ep287 ep288 ep289 ep290 Bool.false ep420 ep410 ep411

noncomputable def ep422 := @Enclosure.Complex.IsNear.of_eq (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 19, @HPow.hPow Complex Complex Complex qz120 (@Nat.cast Complex Complex.instNatCast n) qz121) (BSN.headSumC qz5 19) Bool.false 635761183857 137438953472 3548050850637 800238306590720 Bool.false 25159250813 274877906944 14181984064963

noncomputable abbrev qz127 := (@HPow.hPow Complex Complex Complex qz274 (@Nat.cast Complex Complex.instNatCast 18) qz275)

noncomputable def ep423 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 19) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 18) qz127) Bool.false 635761183857 137438953472 3548050850637 800238306590720 Bool.false 25159250813 274877906944 14181984064963 3200953226362880

noncomputable def ep424 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 18) qz127 Bool.false 1272372192989 274877906944 30032001022597 7042097097998336 Bool.true 39623954337 274877906944 29996264105975 7042097097998336 Bool.true

noncomputable abbrev qz128 := (@HPow.hPow Complex Complex Complex qz274 (@Nat.cast Complex Complex.instNatCast 17) qz275)

noncomputable def ep425 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 18) (@HAdd.hAdd Complex Complex Complex qz4 qz40 qz128) Bool.false 1272372192989 274877906944 30032001022597 7042097097998336 Bool.true 39623954337 274877906944 29996264105975 7042097097998336

noncomputable def ep426 := @Enclosure.Complex.IsNear.addLitP qz40 qz128 Bool.false 151686259201 34359738368 7198733835695 1760524274499584 Bool.true 70888791985 274877906944 28764762539911 7042097097998336 Bool.false

noncomputable abbrev qz397 := (@Nat.cast Real Real.instNatCast 17)

noncomputable abbrev qz129 := (@Inv.inv Real Real.instInv (Real.sqrt qz397))

noncomputable abbrev qz398 := (Real.log (Enclosure.sfrac Bool.false 17 1))

noncomputable abbrev qz130 := (@HMul.hMul Real Real Real qz267 qz280 qz398)

noncomputable def ep427 := @Enclosure.Complex.IsNear.of_eq qz128 (Complex.mk (@HMul.hMul Real Real Real qz0 qz129 (Real.cos qz130)) (@HMul.hMul Real Real Real qz0 qz129 (@Neg.neg Real Real.instNeg (Real.sin qz130)))) Bool.false 58882119381 274877906944 6615324491 37658273251328 Bool.false 1954052353 17179869184 411598117 2353642078208 (BSN.cpow_neg_s_mk qz16 90753 1000 17 qz17 rfl)

noncomputable abbrev qz399 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 17) qz18)

noncomputable def ep428 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz397) 2161695 524288 1 524288 63579 63580 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz397) (Real.sqrt qz399) Bool.false 2161695 524288 1 524288 (BSN.sqrt_natCast_div_one 17) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz399) Bool.false 2161695 524288 1 524288 2161695 524288 1 524288 (BSN.sqrt_enclosure 17 1 1080847 1080848 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep429 := BSN.log_dyadic_bound 1 33 2 1 3267 262144 128095 1 1 15892 34 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 1) (BSN.artanhQ 33) 0 1 1 3267 1 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep430 := @Enclosure.Real.IsNear.mulLit_ff qz16 qz398 90753 1000 0 1 3189913004350711 1125899906842624 50000000025619 6404750000000000000 289494174883840075383 1125899906842624000 4537650002325001107 6404750000000000000000 qz21 (BSN.isNear_log_sfrac 17 1 3189913004350711 1125899906842624 50000000025619 6404750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz399) Bool.false 26758929747600409100288 9444732965739290427392 1000000000512380 128095000000000000000 3189913004350711 1125899906842624 50000000025619 6404750000000000000 (BSN.log_rat_reduce_isNear 17 1 4 34 32 15892 262144 24973259072661432 36028797018963968 128095 1000000000000000 rfl rfl rfl rfl (ep429 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep431 := nat_lit 7344699398926917978106428971269924528887525344619053124996360287010491040000

noncomputable def ep432 := nat_lit 3335730404043302094534458071488530580831350203762774782068138384100000000

noncomputable def ep433 := nat_lit 19230716767011572215459020087876916145193601335577142263438547575262743200000

noncomputable def ep434 := BSN.sin_dyadic_bound_f 1162515810 1073741824 3 2 524288 256441 ep431 ep107 ep432 ep433 ep109 ep432 463059 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1162515810) qz289 0 2 ep431 ep107 ep432 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1162515810) qz290 0 2 ep433 ep109 ep432 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz400 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 67403115) qz19)

noncomputable def ep435 := @Enclosure.Real.IsNear.cos_image qz130 qz400 Bool.false 67403115 262144 93 131072 Bool.false 463059 524288 1 128095 (@Enclosure.Real.IsNear.recentre' qz130 Bool.false 289494174883840075383 1125899906842624000 4537650002325001107 6404750000000000000000 67403115 262144 93 131072 (ep430 rfl) rfl) (Enclosure.sfrac_false_div 67403115 262144) (BSN.cos_reduce3 qz400 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 40902388830992617963520) qz288) 226375608064910080 72057594037927936 Bool.false 463059 524288 40 1000000000000000 256190 128095 (BSN.sin_reduce_arg_pos_rat_q3 67403115 262144 226375608064910080 72057594037927936 40 40902388830992617963520 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 463059 524288 40902388830992617963520 37778931862957161709568 1162515810 1073741824 256441 256190 (ep434 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep436 := nat_lit 4081871101805640344323364743181730751862328013767812969345563776509872800000

noncomputable def ep437 := nat_lit 12238941844608834428781025313402215194425321340895913358472555052761418400000

noncomputable def ep438 := BSN.cos_dyadic_bound_f 1162515810 1073741824 3 2 524288 256441 ep436 ep74 ep432 ep437 ep77 ep432 245872 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1162515810) qz283 0 2 ep436 ep74 ep432 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1162515810) qz284 0 2 ep437 ep77 ep432 rfl rfl rfl rfl) rfl rfl

noncomputable def ep439 := @Enclosure.Real.IsNear.sin_image qz130 qz400 Bool.false 67403115 262144 93 131072 Bool.true 245872 524288 1 128095 (@Enclosure.Real.IsNear.recentre' qz130 Bool.false 289494174883840075383 1125899906842624000 4537650002325001107 6404750000000000000000 67403115 262144 93 131072 (ep430 rfl) rfl) (Enclosure.sfrac_false_div 67403115 262144) (BSN.sin_reduce3 qz400 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 40902388830992617963520) qz288) 226375608064910080 72057594037927936 Bool.false 245872 524288 40 1000000000000000 256190 128095 (BSN.sin_reduce_arg_pos_rat_q3 67403115 262144 226375608064910080 72057594037927936 40 40902388830992617963520 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 245872 524288 40902388830992617963520 37778931862957161709568 1162515810 1073741824 256441 256190 (ep438 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz401 := (@Enclosure.Real.IsNear.recentre' qz129 Bool.false 127159 524288 1 524288 127159 524288 1 524288 (ep428 rfl rfl) rfl)

noncomputable def ep440 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz129 (Real.cos qz130)) (@HMul.hMul Real Real Real qz0 qz129 (@Neg.neg Real Real.instNeg (Real.sin qz130))) Bool.false 58882119381 274877906944 6615324491 37658273251328 Bool.false 1954052353 17179869184 411598117 2353642078208 (@Enclosure.Real.IsNear.mulLit_ff qz129 (Real.cos qz130) 127159 524288 1 524288 463059 524288 12043907 16789667840 58882119381 274877906944 6615324491 37658273251328 qz401 (@Enclosure.Real.IsNear.recentre' (Real.cos qz130) Bool.false 463059 524288 12043907 16789667840 463059 524288 12043907 16789667840 (ep435 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz129 (@Neg.neg Real Real.instNeg (Real.sin qz130)) 127159 524288 1 524288 15367 32768 12043907 16789667840 1954052353 17179869184 411598117 2353642078208 qz401 (@Enclosure.Real.IsNear.neg (Real.sin qz130) Bool.true 15367 32768 12043907 16789667840 (@Enclosure.Real.IsNear.recentre' (Real.sin qz130) Bool.true 245872 524288 12043907 16789667840 15367 32768 12043907 16789667840 (ep439 rfl rfl) rfl)) rfl)

noncomputable def ep441 := @ep426 58882119381 274877906944 6615324491 37658273251328 Bool.false 1954052353 17179869184 411598117 2353642078208 Bool.false 43718375657820443901952 1272372192989 274877906944 30032001022597 7042097097998336 Bool.true 680734352062449451008 39623954337 274877906944 29996264105975 7042097097998336 EMRow26.d7 (ep427 ep440) rfl rfl

noncomputable abbrev qz402 := (@Nat.cast Real Real.instNatCast 18)

noncomputable abbrev qz131 := (@Inv.inv Real Real.instInv (Real.sqrt qz402))

noncomputable abbrev qz403 := (Real.log (Enclosure.sfrac Bool.false 18 1))

noncomputable abbrev qz132 := (@HMul.hMul Real Real Real qz267 qz280 qz403)

noncomputable def ep442 := @Enclosure.Complex.IsNear.of_eq qz127 (Complex.mk (@HMul.hMul Real Real Real qz0 qz131 (Real.cos qz132)) (@HMul.hMul Real Real Real qz0 qz131 (@Neg.neg Real Real.instNeg (Real.sin qz132)))) Bool.true 849825275 274877906944 5954232315043 35210485489991680 Bool.false 32391602575 137438953472 3010252092359 17605242744995840 (BSN.cpow_neg_s_mk qz16 90753 1000 18 qz17 rfl)

noncomputable abbrev qz404 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 18) qz18)

noncomputable def ep443 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz402) 2224365 524288 1 524288 61787 61788 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz402) (Real.sqrt qz404) Bool.false 2224365 524288 1 524288 (BSN.sqrt_natCast_div_one 18) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz404) Bool.false 2224365 524288 1 524288 2224365 524288 1 524288 (BSN.sqrt_enclosure 18 1 1112182 1112183 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep444 := BSN.log_dyadic_bound 2 34 2 1 3468 262144 128095 4 4 30876 36 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 2) (BSN.artanhQ 34) 0 1 4 3468 4 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep445 := @Enclosure.Real.IsNear.mulLit_ff qz16 qz403 90753 1000 0 1 3254268794313975 1125899906842624 50000000025619 6404750000000000000 11813386235615046927 45035996273704960 4537650002325001107 6404750000000000000000 qz21 (BSN.isNear_log_sfrac 18 1 3254268794313975 1125899906842624 50000000025619 6404750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz404) Bool.false 27298785242132565196800 9444732965739290427392 1000000000512380 128095000000000000000 3254268794313975 1125899906842624 50000000025619 6404750000000000000 (BSN.log_rat_reduce_isNear 18 1 4 36 32 30876 262144 24973259072661432 36028797018963968 128095 1000000000000000 rfl rfl rfl rfl (ep444 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep446 := nat_lit 17536292812673165773860908202760344037644570618839561479552287385814394826881

noncomputable def ep447 := nat_lit 61237800050437782317904266851158115435837381986079053573819930383910531201

noncomputable def ep448 := nat_lit 52486402837918621756946916074578715882062037092546526331509222296675363418241

noncomputable def ep449 := BSN.cos_dyadic_bound_f 1672543599 1073741824 3 2 524288 256441 ep446 ep74 ep447 ep448 ep77 ep447 6877 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1672543599) qz283 0 2 ep446 ep74 ep447 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1672543599) qz284 0 2 ep448 ep77 ep447 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz405 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 34381479) (@Nat.cast Real Real.instNatCast 131072))

noncomputable def ep450 := @Enclosure.Real.IsNear.cos_image qz132 qz405 Bool.false 34381479 131072 93 131072 Bool.true 6877 524288 1 128095 (@Enclosure.Real.IsNear.recentre' qz132 Bool.false 11813386235615046927 45035996273704960 4537650002325001107 6404750000000000000000 34381479 131072 93 131072 (ep445 rfl) rfl) (Enclosure.sfrac_false_div 34381479 131072) (BSN.cos_reduce2 qz405 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 29423698163962665238528) qz300) 226375608064910080 72057594037927936 Bool.false 6877 524288 41 1000000000000000 256190 128095 (BSN.sin_reduce_arg_pos_rat_q2 34381479 131072 226375608064910080 72057594037927936 41 29423698163962665238528 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 6877 524288 29423698163962665238528 18889465931478580854784 1672543599 1073741824 256441 256190 (ep449 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep451 := nat_lit 31516336822771348167095311351487692775411557208322347420335061350158782263425

noncomputable def ep452 := nat_lit 82443640002414726885306351393280177462991294070009639061758023648841907925121

noncomputable def ep453 := BSN.sin_dyadic_bound_f 1672543599 1073741824 3 2 524288 256441 ep451 ep107 ep447 ep452 ep109 ep447 524242 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1672543599) qz289 0 2 ep451 ep107 ep447 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1672543599) qz290 0 2 ep452 ep109 ep447 rfl rfl rfl rfl) rfl rfl

noncomputable def ep454 := @Enclosure.Real.IsNear.sin_image qz132 qz405 Bool.false 34381479 131072 93 131072 Bool.true 524242 524288 1 128095 (@Enclosure.Real.IsNear.recentre' qz132 Bool.false 11813386235615046927 45035996273704960 4537650002325001107 6404750000000000000000 34381479 131072 93 131072 (ep445 rfl) rfl) (Enclosure.sfrac_false_div 34381479 131072) (BSN.sin_reduce2 qz405 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 29423698163962665238528) qz300) 226375608064910080 72057594037927936 Bool.false 524242 524288 41 1000000000000000 256190 128095 (BSN.sin_reduce_arg_pos_rat_q2 34381479 131072 226375608064910080 72057594037927936 41 29423698163962665238528 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 524242 524288 29423698163962665238528 18889465931478580854784 1672543599 1073741824 256441 256190 (ep453 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz406 := (@Enclosure.Real.IsNear.recentre' qz131 Bool.false 123575 524288 1 524288 123575 524288 1 524288 (ep443 rfl rfl) rfl)

noncomputable def ep455 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz131 (Real.cos qz132)) (@HMul.hMul Real Real Real qz0 qz131 (@Neg.neg Real Real.instNeg (Real.sin qz132))) Bool.true 849825275 274877906944 5954232315043 35210485489991680 Bool.false 32391602575 137438953472 3010252092359 17605242744995840 (@Enclosure.Real.IsNear.mulLit_ft qz131 (Real.cos qz132) 123575 524288 1 524288 6877 524288 12043907 16789667840 849825275 274877906944 5954232315043 35210485489991680 qz406 (@Enclosure.Real.IsNear.recentre' (Real.cos qz132) Bool.true 6877 524288 12043907 16789667840 6877 524288 12043907 16789667840 (ep450 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz131 (@Neg.neg Real Real.instNeg (Real.sin qz132)) 123575 524288 1 524288 262121 262144 12043907 16789667840 32391602575 137438953472 3010252092359 17605242744995840 qz406 (@Enclosure.Real.IsNear.neg (Real.sin qz132) Bool.true 262121 262144 12043907 16789667840 (@Enclosure.Real.IsNear.recentre' (Real.sin qz132) Bool.true 524242 524288 12043907 16789667840 262121 262144 12043907 16789667840 (ep454 rfl rfl) rfl)) rfl)

noncomputable def ep456 := @ep424 849825275 274877906944 5954232315043 35210485489991680 Bool.false 32391602575 137438953472 3010252092359 17605242744995840 Bool.false 349513407069703442006016 635761183857 137438953472 3548050850637 800238306590720 Bool.false 3457861101878285172736 25159250813 274877906944 14181984064963 3200953226362880 (ep425 (BSN.head_sum_c_succ qz5 17 18 rfl rfl) (ep441 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep442 ep455) rfl rfl

noncomputable def ep457 := @Enclosure.Complex.IsNear.mul qz122 (@HAdd.hAdd Complex Complex Complex qz4 qz123 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz79 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz79 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz125 qz126 (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1))))) Bool.true ep416 ep288 ep417 ep290 Bool.true

noncomputable abbrev qz133 := (Complex.re qz394)

noncomputable abbrev qz134 := (Complex.im qz394)

noncomputable def ep458 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 qz133 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz123 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz79 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz79 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz125 qz126 (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz134 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz123 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz79 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz79 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz125 qz126 (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1))))))) 303974984040270851517 2688491183379488702464 8376878933670736631209

noncomputable def ep459 := nat_lit 100183935457453267008618496

noncomputable def ep460 := nat_lit 13752972969911701472500099

noncomputable def ep461 := nat_lit 27954941570102884026097873526364565565683531776

noncomputable def ep462 := @Enclosure.Real.IsNear.mulLit_tf qz133 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz123 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz79 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz79 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz125 qz126 (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1)))))) 484604091 2147483648 146900798277 880262137249792 1881793755061

noncomputable abbrev qz407 := (@Nat.cast Real Real.instNatCast 19)

noncomputable abbrev qz135 := (@Inv.inv Real Real.instInv (Real.sqrt qz407))

noncomputable abbrev qz408 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) qz509 (Real.log (Enclosure.sfrac Bool.false 19 1)))

noncomputable abbrev qz136 := (Real.cos qz408)

noncomputable abbrev qz137 := (Real.sin qz408)

noncomputable abbrev qz409 := (@Neg.neg Real Real.instNeg qz137)

noncomputable def ep463 := @Enclosure.Complex.IsNear.of_eq qz122 (Complex.mk (@HMul.hMul Real Real Real qz0 qz135 qz136) (@HMul.hMul Real Real Real qz0 qz135 qz409)) Bool.true 484604091 2147483648 146900798277 880262137249792 Bool.false 5679454101 137438953472 582206883805 3521048548999168 (BSN.cpow_neg_s_mk qz16 90753 1000 19 qz17 rfl)

noncomputable abbrev qz410 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 19) qz18)

noncomputable def ep464 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz407) 2285319 524288 1 524288 60139 60140 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz407) (Real.sqrt qz410) Bool.false 2285319 524288 1 524288 (BSN.sqrt_natCast_div_one 19) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz410) Bool.false 2285319 524288 1 524288 2285319 524288 1 524288 (BSN.sqrt_enclosure 19 1 1142659 1142660 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep465 := BSN.log_dyadic_bound 3 35 3 2 22509375 262144 128095 55368 243 45049 38 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 3) (BSN.artanhQ 35) 0 2 55368 22509375 243 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz411 := (Real.log (Enclosure.sfrac Bool.false 19 1))

noncomputable abbrev qz138 := qz411

noncomputable abbrev qz412 := (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 19) qz18))

noncomputable def ep466 := @Enclosure.Real.IsNear.mulLit_ff qz16 qz138 90753 1000 0 1 3315141365800183 1125899906842624 50000000025619 6404750000000000000 300859024370464007799 1125899906842624000 4537650002325001107 6404750000000000000000 qz21 (BSN.isNear_log_sfrac 19 1 3315141365800183 1125899906842624 50000000025619 6404750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' qz412 Bool.false 27809421382282341515264 9444732965739290427392 1000000000512380 128095000000000000000 3315141365800183 1125899906842624 50000000025619 6404750000000000000 (BSN.log_rat_reduce_isNear 19 1 4 38 32 45049 262144 24973259072661432 36028797018963968 128095 1000000000000000 rfl rfl rfl rfl (ep465 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep467 := nat_lit 1430303251610069739165401784810256

noncomputable def ep468 := BSN.cos_dyadic_bound_f 194471978 1073741824 2 1 524288 256441 ep467 ep57 ep467 ep467 ep58 ep467 515712 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 194471978) qz283 0 1 ep467 ep57 ep467 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 194471978) qz284 0 1 ep467 ep58 ep467 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz139 := qz408

noncomputable abbrev qz413 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 4378075) (@Nat.cast Real Real.instNatCast 16384))

noncomputable def ep469 := @Enclosure.Real.IsNear.cos_image qz139 qz413 Bool.false 4378075 16384 373 524288 Bool.true 515712 524288 1 128095 (@Enclosure.Real.IsNear.recentre' qz139 Bool.false 300859024370464007799 1125899906842624000 4537650002325001107 6404750000000000000000 4378075 16384 373 524288 (ep466 rfl) rfl) (Enclosure.sfrac_false_div 4378075 16384) (BSN.cos_reduce2 qz413 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 427648404169949184000) qz329) 226375608064910080 72057594037927936 Bool.false 515712 524288 42 1000000000000000 256190 128095 (BSN.sin_reduce_arg_pos_rat_q2 4378075 16384 226375608064910080 72057594037927936 42 427648404169949184000 2361183241434822606848 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 515712 524288 427648404169949184000 2361183241434822606848 194471978 1073741824 256441 256190 (ep468 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep470 := BSN.sin_dyadic_bound_f 194471978 1073741824 2 1 524288 256441 ep467 ep69 ep467 ep467 ep70 ep467 94438 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 194471978) qz289 0 1 ep467 ep69 ep467 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 194471978) qz290 0 1 ep467 ep70 ep467 rfl rfl rfl rfl) rfl rfl

noncomputable def ep471 := @Enclosure.Real.IsNear.sin_image qz139 qz413 Bool.false 4378075 16384 373 524288 Bool.true 94438 524288 1 128095 (@Enclosure.Real.IsNear.recentre' qz139 Bool.false 300859024370464007799 1125899906842624000 4537650002325001107 6404750000000000000000 4378075 16384 373 524288 (ep466 rfl) rfl) (Enclosure.sfrac_false_div 4378075 16384) (BSN.sin_reduce2 qz413 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 427648404169949184000) qz329) 226375608064910080 72057594037927936 Bool.false 94438 524288 42 1000000000000000 256190 128095 (BSN.sin_reduce_arg_pos_rat_q2 4378075 16384 226375608064910080 72057594037927936 42 427648404169949184000 2361183241434822606848 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 94438 524288 427648404169949184000 2361183241434822606848 194471978 1073741824 256441 256190 (ep470 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz414 := (@Enclosure.Real.IsNear.recentre' qz135 Bool.false 120279 524288 1 524288 120279 524288 1 524288 (ep464 rfl rfl) rfl)

noncomputable def ep472 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz135 qz136) (@HMul.hMul Real Real Real qz0 qz135 qz409) Bool.true 484604091 2147483648 146900798277 880262137249792 Bool.false 5679454101 137438953472 582206883805 3521048548999168 (@Enclosure.Real.IsNear.mulLit_ft qz135 qz136 120279 524288 1 524288 4029 4096 48303723 67158671360 484604091 2147483648 146900798277 880262137249792 qz414 (@Enclosure.Real.IsNear.recentre' qz136 Bool.true 515712 524288 48303723 67158671360 4029 4096 48303723 67158671360 (ep469 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz135 qz409 120279 524288 1 524288 47219 262144 48303723 67158671360 5679454101 137438953472 582206883805 3521048548999168 qz414 (@Enclosure.Real.IsNear.neg qz137 Bool.true 47219 262144 48303723 67158671360 (@Enclosure.Real.IsNear.recentre' qz137 Bool.true 94438 524288 48303723 67158671360 47219 262144 48303723 67158671360 (ep471 rfl rfl) rfl)) rfl)

noncomputable def ep473 := @ep462 3755778796104 0 1 303974984040270851517 2688491183379488702464 8376878933670736631209 ep459 (@Enclosure.Complex.IsNear.re_isNear qz122 Bool.true 484604091 2147483648 146900798277 880262137249792 Bool.false 5679454101 137438953472 582206883805 3521048548999168 (ep463 ep472))

noncomputable def ep474 := @Enclosure.Complex.IsNear.re_isNear (@HAdd.hAdd Complex Complex Complex qz4 qz123 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz79 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz79 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz125 qz126 (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1))))) Bool.false 1881793755061 3755778796104 0 1 Bool.false

noncomputable def ep475 := @Enclosure.Complex.IsNear.addLitP qz123 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz79 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz79 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz125 qz126 (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1)))) Bool.false 8217357009 16472714018 0 1 Bool.true 1724307000

noncomputable def ep476 := @ep475 8236357009 0 1 Bool.false 1 456 0 1 Bool.false 30251 76000 0 1 Bool.false 3763587510122 1881793755061 3755778796104 0 1 Bool.false 118110703879259 118110703879259 625963132684000 0 1

noncomputable abbrev qz140 := (@HDiv.hDiv Complex Complex Complex qz366 qz395 (@HSub.hSub Complex Complex Complex qz358 qz272 (1 : Complex)))

noncomputable def ep477 := @Enclosure.Complex.IsNear.addLitP qz140 qz98 Bool.true 38000000 32945428036 0 1 Bool.true 6897228000 32945428036 0 1

noncomputable def ep478 := @Enclosure.Complex.IsNear.of_eq qz140 (Complex.mk (Enclosure.sfrac Bool.true 38000000 32945428036) (Enclosure.sfrac Bool.true 6897228000 32945428036)) Bool.true 38000000 32945428036 0 1 Bool.true 6897228000 32945428036 0 1

noncomputable def ep479 := @ep477 Bool.false 1 2 0 1 Bool.false 0 1 0 1 Bool.false 32869428036 8217357009 16472714018 0 1 Bool.true 6897228000 1724307000 8236357009 0 1 (ep478 (BSN.N_div_s_sub_one_mk qz16 90753 1000 19 qz17 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 38000000 32945428036) (Enclosure.sfrac Bool.true 6897228000 32945428036) Bool.true 38000000 32945428036 0 1 Bool.true 6897228000 32945428036 0 1 (Enclosure.Real.IsNear.const Bool.true 38000000 32945428036) (Enclosure.Real.IsNear.const Bool.true 6897228000 32945428036))) qz99 rfl

noncomputable abbrev qz141 := (@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 1)))

noncomputable abbrev qz415 := (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz517 qz518 1))

noncomputable abbrev qz142 := qz415

noncomputable def ep480 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz79 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz79 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz125 qz126 (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1)))) (@HAdd.hAdd Complex Complex Complex qz4 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz79 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz79 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz125 qz126 (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz100)) ↑qz141) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz142)) Bool.false 1 456 0 1

noncomputable def ep481 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz79 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz79 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz125 qz126 (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz100)) ↑qz141) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz142) Bool.false 0 1 0 1 Bool.false

noncomputable def ep482 := @ep481 0 1 0 1 Bool.false 1 456 0 1 Bool.false 30251 76000 0 1 Bool.false 1 1 456 0 1 Bool.false 30251 30251 76000 0

noncomputable def ep483 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz79 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz79 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz125 qz126 (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1)))) (Complex.mk qz13 qz13) Bool.false 0 1 0 1 Bool.false

noncomputable def ep484 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz100)) ↑qz141) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz142 Bool.false 1 456 0 1 Bool.false 30251 76000 0 1

noncomputable abbrev qz143 := (Complex.re qz415)

noncomputable abbrev qz144 := (Complex.im qz415)

noncomputable def ep485 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz100)) ↑qz141) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) qz143) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz100)) ↑qz141) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) qz144) 1 456 0 1 0 1 0

noncomputable def ep486 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz100)) ↑qz141) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) qz143 1 24 0 1 1 19 0 1 1

noncomputable def ep487 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz100)) ↑qz141)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz100)) ↑qz141)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) 1 24 0 1 0 1 0 1 1

noncomputable def ep488 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz100)) ↑qz141)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 1 2 0 1 1 24 0

noncomputable def ep489 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz100)) ↑qz141) (Complex.mk (Enclosure.sfrac Bool.false 1 12) qz13) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (BSN.bern_coeff_mk 1 1 6 2 Bool.false BSN.bern_real_1 EMRow26.d8 rfl) qz384

noncomputable def ep490 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) qz5 Bool.false 1 2 0 1 Bool.false 90753 1000 0 1 (BSN.ascPochhammer_one_eval qz5)

noncomputable def ep491 := ep490 (@Enclosure.Complex.IsNear.of_eq qz5 (Complex.mk qz93 qz16) Bool.false 1 2 0 1 Bool.false 90753 1000 0 1 (BSN.s_crit_mk qz16 Bool.false 90753 1000 qz17) (@Enclosure.Complex.IsNear.mk qz93 qz16 Bool.false 1 2 0 1 Bool.false 90753 1000 0 1 qz376 qz21))

noncomputable def ep492 := @ep488 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz100)) ↑qz141) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep489) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 90753 1000 0 1 ep491)

noncomputable def ep493 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz100)) ↑qz141)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 90753 1000 0 1 0 1 0

noncomputable def ep494 := @ep493 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz100)) ↑qz141) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep489) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 90753 1000 0 1 ep491)

noncomputable def ep495 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz100)) ↑qz141)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz100)) ↑qz141)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) 30251 4000 0 1 0 1 0 1 30251

noncomputable def ep496 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz100)) ↑qz141)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 90753 1000 0 1 30251 4000 0

noncomputable def ep497 := @ep496 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz100)) ↑qz141) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep489) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 90753 1000 0 1 ep491)

noncomputable def ep498 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz100)) ↑qz141)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 1 2 0 1 0 1 0

noncomputable def ep499 := @ep498 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz100)) ↑qz141) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep489) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 90753 1000 0 1 ep491)

noncomputable def ep500 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz100)) ↑qz141) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 24 0 1 Bool.false 30251 4000 0 1 (@ep487 1 24 0 1 (ep492 rfl) (ep494 rfl) rfl rfl) (@ep495 30251 4000 0 1 (ep497 rfl) (ep499 rfl) rfl rfl)

noncomputable def ep501 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz100)) ↑qz141) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 30251 4000 0 1 ep500

noncomputable abbrev qz145 := (@Enclosure.Complex.IsNear.re_isNear qz415 Bool.false 1 19 0 1 Bool.false 0 1 0 1 (@Enclosure.Complex.IsNear.of_eq qz415 (Complex.mk (Enclosure.sfrac Bool.false 1 19) qz278) Bool.false 1 19 0 1 Bool.false 0 1 0 1 (BSN.natCast_pow_inv_mk 19 1 19 EMRow26.d9 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 19) qz278 Bool.false 1 19 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 19) qz292)))

noncomputable def ep502 := @ep486 456 0 1 ep501 qz145

noncomputable def ep503 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz100)) ↑qz141) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) qz144 30251 4000 0 1 0 1 0 1 0

noncomputable def ep504 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz100)) ↑qz141) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 30251 4000 0 1 ep500

noncomputable abbrev qz146 := (@Enclosure.Complex.IsNear.im_isNear qz415 Bool.false 1 19 0 1 Bool.false 0 1 0 1 (@Enclosure.Complex.IsNear.of_eq qz415 (Complex.mk (Enclosure.sfrac Bool.false 1 19) qz278) Bool.false 1 19 0 1 Bool.false 0 1 0 1 (BSN.natCast_pow_inv_mk 19 1 19 EMRow26.d9 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 19) qz278 Bool.false 1 19 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 19) qz292)))

noncomputable def ep505 := @ep503 1 0 1 ep504 qz146

noncomputable def ep506 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz100)) ↑qz141) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) qz144) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz100)) ↑qz141) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) qz143) 0 1 0 1 30251 76000 0

noncomputable def ep507 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz100)) ↑qz141) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) qz144 1 24 0 1 0 1 0 1 0

noncomputable def ep508 := @ep507 1 0 1 ep501 qz146

noncomputable def ep509 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz100)) ↑qz141) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) qz143 30251 4000 0 1 1 19 0 1 30251

noncomputable def ep510 := @ep509 76000 0 1 ep504 qz145

noncomputable def ep511 := @ep482 1 (@ep483 0 1 0 1 (BSN.bern_sum_base qz5 19) qz114) (ep484 (@ep485 1 1 1 456 0 1 (ep502 rfl) (ep505 rfl) rfl rfl) (@ep506 1 30251 30251 76000 0 1 (ep508 rfl) (ep510 rfl) rfl rfl)) rfl rfl rfl rfl rfl

noncomputable def ep512 := ep476 (ep479 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep480 Bool.false 30251 76000 0 1 (BSN.bern_sum_succ qz5 19 0 1 1 rfl rfl) (ep511 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl rfl

noncomputable def ep513 := @Enclosure.Real.IsNear.mulLit_ff qz134 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz123 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz79 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz79 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz125 qz126 (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1)))))) 5679454101 137438953472 582206883805 3521048548999168 118110703879259

noncomputable def ep514 := @ep513 625963132684000 0 1 670804321519054136391159 ep288 ep460 ep290 (@Enclosure.Complex.IsNear.im_isNear qz122 Bool.true 484604091 2147483648 146900798277 880262137249792 Bool.false 5679454101 137438953472 582206883805 3521048548999168 (ep463 ep472))

noncomputable def ep515 := @Enclosure.Complex.IsNear.im_isNear (@HAdd.hAdd Complex Complex Complex qz4 qz123 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz79 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz79 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz125 qz126 (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1))))) Bool.false 1881793755061 3755778796104 0 1 Bool.false

noncomputable def ep516 := nat_lit 1344245591689744351232000

noncomputable def ep517 := nat_lit 17350556684921507723236743

noncomputable def ep518 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 qz133 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz123 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz79 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz79 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz125 qz126 (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz134 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz123 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz79 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz79 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz125 qz126 (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1))))))) 57236930290778481448569 ep516 ep517

noncomputable def ep519 := nat_lit 551011645015992968547401728000

noncomputable def ep520 := nat_lit 1202207225489439204103421952

noncomputable def ep521 := nat_lit 5059480507201080118639446634424167481709953024

noncomputable def ep522 := @Enclosure.Real.IsNear.mulLit_tf qz133 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz123 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz79 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz79 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz125 qz126 (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1)))))) 484604091 2147483648 146900798277 880262137249792 118110703879259

noncomputable def ep523 := @ep522 625963132684000 0 1 57236930290778481448569 ep516 ep517 ep519 (@Enclosure.Complex.IsNear.re_isNear qz122 Bool.true 484604091 2147483648 146900798277 880262137249792 Bool.false 5679454101 137438953472 582206883805 3521048548999168 (ep463 ep472))

noncomputable def ep524 := @Enclosure.Real.IsNear.mulLit_ff qz134 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz123 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz79 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz79 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz125 qz126 (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1)))))) 5679454101 137438953472 582206883805 3521048548999168 1881793755061

noncomputable def ep525 := @ep524 3755778796104 0 1 3562520419805795318387 172063435736287276957696 99599388917979477971555 ep520 (@Enclosure.Complex.IsNear.im_isNear qz122 Bool.true 484604091 2147483648 146900798277 880262137249792 Bool.false 5679454101 137438953472 582206883805 3521048548999168 (ep463 ep472))

noncomputable abbrev qz416 := (ep512 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable def ep526 := @ep457 470475832176731288378729 ep411 ep418 ep413 (@ep458 ep459 670804321519054136391159 ep288 ep460 ep290 ep461 ep416 ep288 ep417 ep290 (ep473 (@ep474 118110703879259 625963132684000 0 1 qz416) rfl) (ep514 (@ep515 118110703879259 625963132684000 0 1 qz416) rfl) rfl rfl) (@ep518 ep519 3562520419805795318387 172063435736287276957696 99599388917979477971555 ep520 ep521 470475832176731288378729 ep411 ep418 ep413 (ep523 (@ep515 118110703879259 625963132684000 0 1 qz416) rfl) (ep525 (@ep474 118110703879259 625963132684000 0 1 qz416) rfl) rfl rfl)

noncomputable def ep527 := @ep421 ep412 ep413 (@ep422 3200953226362880 (BSN.head_sum_c_eq qz5 19) (ep423 (BSN.head_sum_c_succ qz5 18 19 rfl rfl) (ep456 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))) ep526 rfl rfl rfl

noncomputable def ep528 := @Enclosure.Complex.IsNear.re_isNear (zetaApproximant qz5 1 19) Bool.false ep287 ep288 ep289 ep290 Bool.false ep410 ep411 ep412 ep413 (@ep414 ep290 Bool.false ep410 ep411 ep412 ep413 (BSN.zetaApproximant_eq_folded' qz5 1 19 rfl) (ep527 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

noncomputable def ep529 := @Enclosure.Real.IsNear.mulLit_ff (Real.sin (@HSub.hSub Real Real Real qz361 (Complex.im (@HSub.hSub Complex Complex Complex qz72 qz73 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz74 (@Nat.cast Complex Complex.instNatCast j))))) qz75)) (Complex.im (zetaApproximant qz5 1 19)) 11 262144 30882803

noncomputable def ep530 := @Enclosure.Real.IsNear.recentre' (Real.sin (@HSub.hSub Real Real Real qz361 (Complex.im (@HSub.hSub Complex Complex Complex qz72 qz73 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz74 (@Nat.cast Complex Complex.instNatCast j))))) qz75)) Bool.false 22 524288 30882803

noncomputable def ep531 := @Enclosure.Real.IsNear.sin_image (@HSub.hSub Real Real Real qz361 (Complex.im (@HSub.hSub Complex Complex Complex qz72 qz73 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz74 (@Nat.cast Complex Complex.instNatCast j))))) qz75) qz362 Bool.false 19765203 262144 237

noncomputable def ep532 := BSN.sin_dyadic_bound_f 45260 1073741824 1 0 524288 256441 0 1 1 0 1 1 22 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 45260) qz289 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 45260) qz290 0 0 rfl) rfl rfl

noncomputable def ep533 := @ep531 524288 Bool.false 22 524288 1 128095 (@ep295 19765203 262144 237 524288 ep407 rfl) (Enclosure.sfrac_false_div 19765203 262144) (BSN.sin_reduce0 qz362 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 1592475216884269056) qz288) 226375608064910080 72057594037927936 Bool.false 22 524288 12 1000000000000000 256190 128095 (BSN.sin_reduce_arg_pos_rat_q0 19765203 262144 226375608064910080 72057594037927936 12 1592475216884269056 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 22 524288 1592475216884269056 37778931862957161709568 45260 1073741824 256441 256190 (ep532 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep534 := @Enclosure.Complex.IsNear.im_isNear (zetaApproximant qz5 1 19) Bool.false ep287 ep288 ep289 ep290 Bool.false ep410 ep411 ep412 ep413 (@ep414 ep290 Bool.false ep410 ep411 ep412 ep413 (BSN.zetaApproximant_eq_folded' qz5 1 19 rfl) (ep527 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

theorem EMRow26.d10 : Enclosure.Real.IsNear (hardyZApproximantEM 1 19 qz16) Bool.false ep272 ep273 ep274 ep275 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantEM 1 19 qz16) ep276 Bool.false ep272 ep273 ep274 ep275 (@Eq.refl Real ep276) (@ep277 Bool.false ep272 ep273 ep274 ep275 (BSN.re_exp_mul (@HSub.hSub Real Real Real qz361 (Complex.im (@HSub.hSub Complex Complex Complex qz72 qz73 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz74 (@Nat.cast Complex Complex.instNatCast j))))) qz75) (zetaApproximant qz5 1 19)) (@ep279 ep273 ep280 ep275 ep281 ep282 ep283 ep284 ep285 ep272 ep273 ep274 ep275 (@ep286 67158671360 ep287 ep288 ep289 ep290 ep278 ep273 ep280 ep275 (@ep291 67158671360 524287 524288 30882803 67158671360 (ep409 rfl rfl) rfl) ep528 rfl) (@ep529 67158671360 ep410 ep411 ep412 ep413 ep281 ep282 ep283 ep284 (@ep530 67158671360 11 262144 30882803 67158671360 (ep533 rfl rfl) rfl) ep534 rfl) rfl rfl))

noncomputable abbrev qz534 := (@HAdd.hAdd Complex Complex Complex (@instHAdd Complex Complex.instAdd) (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (2 : Complex)) (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul) Complex.I ↑(Enclosure.sfrac Bool.false 93095 1000)))

noncomputable abbrev qz519 := qz534

noncomputable abbrev qz417 := qz519

noncomputable abbrev qz147 := (BSN.headSumC qz417 9)

noncomputable abbrev qz148 := qz417

noncomputable abbrev qz520 := (@Neg.neg Complex Complex.instNeg qz534)

noncomputable abbrev qz418 := qz520

noncomputable abbrev qz149 := qz418

noncomputable abbrev qz419 := (@HPow.hPow Complex Complex Complex qz120 (@Nat.cast Complex Complex.instNatCast 8) qz149)

noncomputable def ep535 := @Enclosure.Complex.IsNear.of_eq qz147 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz148 8) qz419) Bool.false 139475645627 274877906944 7971377890511 3200953226362880 Bool.false 140104265 274877906944 7990756265141 3200953226362880

noncomputable def ep536 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz148 8) qz419 Bool.false 12954950275 34359738368 39246461596487 17605242744995840 Bool.true 45097442759 137438953472 19667105961691 8802621372497920 Bool.false

noncomputable abbrev qz420 := (@HPow.hPow Complex Complex Complex qz120 (@Nat.cast Complex Complex.instNatCast 7) qz149)

noncomputable def ep537 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz148 8) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz148 7) qz420) Bool.false 12954950275 34359738368 39246461596487 17605242744995840 Bool.true 45097442759 137438953472 19667105961691 8802621372497920

noncomputable def ep538 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz148 7) qz420 Bool.false 52685355521 274877906944 68659472418547 35210485489991680 Bool.true 2823999321 4294967296 34404691831141 17605242744995840 Bool.false

noncomputable abbrev qz421 := (@HPow.hPow Complex Complex Complex qz120 (@Nat.cast Complex Complex.instNatCast 6) qz149)

noncomputable def ep539 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz148 7) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz148 6) qz421) Bool.false 52685355521 274877906944 68659472418547 35210485489991680 Bool.true 2823999321 4294967296 34404691831141 17605242744995840

noncomputable def ep540 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz148 6) qz421 Bool.false 159912901429 274877906944 58009614455087 35210485489991680 Bool.true 53457238603 68719476736 29101946341511 17605242744995840 Bool.true

noncomputable abbrev qz422 := (@HPow.hPow Complex Complex Complex qz120 (@Nat.cast Complex Complex.instNatCast 5) qz149)

noncomputable def ep541 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz148 6) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz148 5) qz422) Bool.false 159912901429 274877906944 58009614455087 35210485489991680 Bool.true 53457238603 68719476736 29101946341511 17605242744995840

noncomputable def ep542 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz148 5) qz422 Bool.false 90016285715 274877906944 46375344723357 35210485489991680 Bool.true 78738155121 68719476736 23276281501501 17605242744995840 Bool.false

noncomputable abbrev qz423 := (@HPow.hPow Complex Complex Complex qz120 (@Nat.cast Complex Complex.instNatCast 4) qz149)

noncomputable def ep543 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz148 5) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz148 4) qz423) Bool.false 90016285715 274877906944 46375344723357 35210485489991680 Bool.true 78738155121 68719476736 23276281501501 17605242744995840

noncomputable def ep544 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz148 4) qz423 Bool.false 111565333057 137438953472 3334555379579 3521048548999168 Bool.true 43644498819 34359738368 3357110449655 3521048548999168 Bool.true

noncomputable abbrev qz150 := qz276

noncomputable def ep545 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz148 4) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz148 3) (@HPow.hPow Complex Complex Complex qz120 qz150 qz149)) Bool.false 111565333057 137438953472 3334555379579 3521048548999168 Bool.true 43644498819 34359738368 3357110449655 3521048548999168

noncomputable def ep546 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz148 3) (@HPow.hPow Complex Complex Complex qz120 qz150 qz149) Bool.false 7828134893 8589934592 917594159579 1760524274499584 Bool.true 24104132127 34359738368 1846829362187 3521048548999168 Bool.true

noncomputable abbrev qz151 := qz277

noncomputable def ep547 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz148 3) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz148 2) (@HPow.hPow Complex Complex Complex qz120 qz151 qz149)) Bool.false 7828134893 8589934592 917594159579 1760524274499584 Bool.true 24104132127 34359738368 1846829362187 3521048548999168

noncomputable def ep548 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz148 2) (@HPow.hPow Complex Complex Complex qz120 qz151 qz149) Bool.false 1 1 0 1 Bool.false 0 1 0 1 Bool.true

noncomputable def ep549 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz148 2) (Complex.mk (Enclosure.sfrac Bool.false 1 1) qz13) Bool.false 1 1 0 1 Bool.false 0 1 0 1 (BSN.head_sum_c_two qz148)

noncomputable abbrev qz535 := (Enclosure.sfrac Bool.false 93095 1000)

noncomputable abbrev qz521 := qz535

noncomputable abbrev qz424 := qz521

noncomputable abbrev qz152 := (@HMul.hMul Real Real Real qz267 qz424 (Real.log qz281))

noncomputable abbrev qz153 := qz424

noncomputable abbrev qz425 := (@Eq.refl Real qz521)

noncomputable abbrev qz154 := qz425

noncomputable def ep550 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz120 qz151 qz149) (Complex.mk (@HMul.hMul Real Real Real qz0 qz14 (Real.cos qz152)) (@HMul.hMul Real Real Real qz0 qz14 (@Neg.neg Real Real.instNeg (Real.sin qz152)))) Bool.true 761799699 8589934592 917594159579 1760524274499584 Bool.true 24104132127 34359738368 1846829362187 3521048548999168 (BSN.cpow_neg_s_mk qz153 93095 1000 2 qz154 rfl)

noncomputable def ep551 := BSN.sin_dyadic_bound_f 135026180 1073741824 1 0 524288 256441 0 1 1 0 1 1 65756 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 135026180) qz289 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 135026180) qz290 0 0 rfl) rfl rfl

noncomputable abbrev qz155 := (Enclosure.Real.IsNear.const Bool.false 93095 1000)

noncomputable abbrev qz426 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 33831467) qz31)

noncomputable def ep552 := @Enclosure.Real.IsNear.cos_image qz152 qz426 Bool.false 33831467 524288 191 262144 Bool.true 65756 524288 1 128095 (@Enclosure.Real.IsNear.recentre' qz152 Bool.false 422893347 6553600 18619 25619000 33831467 524288 191 262144 (@Enclosure.Real.IsNear.mulLit_ff qz153 qz20 93095 1000 0 1 181704 262144 1 128095 422893347 6553600 18619 25619000 qz155 qz286 rfl) rfl) (Enclosure.sfrac_false_div 33831467 524288) (BSN.cos_reduce1 qz426 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 9501622740552813379584) qz33) 226375608064910080 72057594037927936 Bool.false 65756 524288 10 1000000000000000 256190 128095 (BSN.sin_reduce_arg_pos_rat_q1 33831467 524288 226375608064910080 72057594037927936 10 9501622740552813379584 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 65756 524288 9501622740552813379584 75557863725914323419136 135026180 1073741824 256441 256190 (ep551 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep553 := nat_lit 332408350427348939200021977760000

noncomputable def ep554 := BSN.cos_dyadic_bound_f 135026180 1073741824 2 1 524288 256441 ep553 ep57 ep553 ep553 ep58 ep553 520147 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 135026180) qz283 0 1 ep553 ep57 ep553 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 135026180) qz284 0 1 ep553 ep58 ep553 rfl rfl rfl rfl) rfl rfl

noncomputable def ep555 := @Enclosure.Real.IsNear.sin_image qz152 qz426 Bool.false 33831467 524288 191 262144 Bool.false 520147 524288 1 128095 (@Enclosure.Real.IsNear.recentre' qz152 Bool.false 422893347 6553600 18619 25619000 33831467 524288 191 262144 (@Enclosure.Real.IsNear.mulLit_ff qz153 qz20 93095 1000 0 1 181704 262144 1 128095 422893347 6553600 18619 25619000 qz155 qz286 rfl) rfl) (Enclosure.sfrac_false_div 33831467 524288) (BSN.sin_reduce1 qz426 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 9501622740552813379584) qz33) 226375608064910080 72057594037927936 Bool.false 520147 524288 10 1000000000000000 256190 128095 (BSN.sin_reduce_arg_pos_rat_q1 33831467 524288 226375608064910080 72057594037927936 10 9501622740552813379584 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 520147 524288 9501622740552813379584 75557863725914323419136 135026180 1073741824 256441 256190 (ep554 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep556 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz14 (Real.cos qz152)) (@HMul.hMul Real Real Real qz0 qz14 (@Neg.neg Real Real.instNeg (Real.sin qz152))) Bool.true 761799699 8589934592 917594159579 1760524274499584 Bool.true 24104132127 34359738368 1846829362187 3521048548999168 (@Enclosure.Real.IsNear.mulLit_ft qz14 (Real.cos qz152) 46341 65536 1 262144 16439 131072 24728289 33579335680 761799699 8589934592 917594159579 1760524274499584 qz291 (@Enclosure.Real.IsNear.recentre' (Real.cos qz152) Bool.true 65756 524288 24728289 33579335680 16439 131072 24728289 33579335680 (ep552 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz14 (@Neg.neg Real Real.instNeg (Real.sin qz152)) 46341 65536 1 262144 520147 524288 24728289 33579335680 24104132127 34359738368 1846829362187 3521048548999168 qz291 (@Enclosure.Real.IsNear.neg (Real.sin qz152) Bool.false 520147 524288 24728289 33579335680 (@Enclosure.Real.IsNear.recentre' (Real.sin qz152) Bool.false 520147 524288 24728289 33579335680 520147 524288 24728289 33579335680 (ep555 rfl rfl) rfl)) rfl)

noncomputable def ep557 := @ep548 761799699 8589934592 917594159579 1760524274499584 Bool.true 24104132127 34359738368 1846829362187 3521048548999168 Bool.false 7828134893 7828134893 8589934592 917594159579 1760524274499584 Bool.true 24104132127 24104132127 34359738368 1846829362187 3521048548999168 (ep549 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 1) qz13 Bool.false 1 1 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 1) qz22)) (ep550 ep556) rfl rfl

noncomputable abbrev qz156 := (@HMul.hMul Real Real Real qz267 qz424 (Real.log (Enclosure.sfrac Bool.false 3 1)))

noncomputable def ep558 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz120 qz150 qz149) (Complex.mk (@HMul.hMul Real Real Real qz0 qz23 (Real.cos qz156)) (@HMul.hMul Real Real Real qz0 qz23 (@Neg.neg Real Real.instNeg (Real.sin qz156)))) Bool.true 13684825231 137438953472 1499367060421 3521048548999168 Bool.true 4885091673 8589934592 377570271867 880262137249792 (BSN.cpow_neg_s_mk qz153 93095 1000 3 qz154 rfl)

noncomputable def ep559 := nat_lit 1199705358899395129822172335645456

noncomputable def ep560 := BSN.sin_dyadic_bound_f 186109546 1073741824 2 1 524288 256441 ep559 ep69 ep559 ep559 ep70 ep559 90419 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 186109546) qz289 0 1 ep559 ep69 ep559 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 186109546) qz290 0 1 ep559 ep70 ep559 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz427 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 26810801) qz19)

noncomputable def ep561 := @Enclosure.Real.IsNear.cos_image qz156 qz427 Bool.false 26810801 262144 191 262144 Bool.true 90419 524288 1 128095 (@Enclosure.Real.IsNear.recentre' qz156 Bool.false 2681080143 26214400 18619 25619000 26810801 262144 191 262144 (@Enclosure.Real.IsNear.mulLit_ff qz153 qz25 93095 1000 0 1 287994 262144 1 128095 2681080143 26214400 18619 25619000 qz155 qz295 rfl) rfl) (Enclosure.sfrac_false_div 26810801 262144) (BSN.cos_reduce1 qz427 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 6548147542438468124672) qz288) 226375608064910080 72057594037927936 Bool.false 90419 524288 16 1000000000000000 256190 128095 (BSN.sin_reduce_arg_pos_rat_q1 26810801 262144 226375608064910080 72057594037927936 16 6548147542438468124672 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 90419 524288 6548147542438468124672 37778931862957161709568 186109546 1073741824 256441 256190 (ep560 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep562 := BSN.cos_dyadic_bound_f 186109546 1073741824 2 1 524288 256441 ep559 ep57 ep559 ep559 ep58 ep559 516432 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 186109546) qz283 0 1 ep559 ep57 ep559 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 186109546) qz284 0 1 ep559 ep58 ep559 rfl rfl rfl rfl) rfl rfl

noncomputable def ep563 := @Enclosure.Real.IsNear.sin_image qz156 qz427 Bool.false 26810801 262144 191 262144 Bool.false 516432 524288 1 128095 (@Enclosure.Real.IsNear.recentre' qz156 Bool.false 2681080143 26214400 18619 25619000 26810801 262144 191 262144 (@Enclosure.Real.IsNear.mulLit_ff qz153 qz25 93095 1000 0 1 287994 262144 1 128095 2681080143 26214400 18619 25619000 qz155 qz295 rfl) rfl) (Enclosure.sfrac_false_div 26810801 262144) (BSN.sin_reduce1 qz427 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 6548147542438468124672) qz288) 226375608064910080 72057594037927936 Bool.false 516432 524288 16 1000000000000000 256190 128095 (BSN.sin_reduce_arg_pos_rat_q1 26810801 262144 226375608064910080 72057594037927936 16 6548147542438468124672 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 516432 524288 6548147542438468124672 37778931862957161709568 186109546 1073741824 256441 256190 (ep562 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep564 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz23 (Real.cos qz156)) (@HMul.hMul Real Real Real qz0 qz23 (@Neg.neg Real Real.instNeg (Real.sin qz156))) Bool.true 13684825231 137438953472 1499367060421 3521048548999168 Bool.true 4885091673 8589934592 377570271867 880262137249792 (@Enclosure.Real.IsNear.mulLit_ft qz23 (Real.cos qz156) 151349 262144 1 262144 90419 524288 24728289 33579335680 13684825231 137438953472 1499367060421 3521048548999168 qz296 (@Enclosure.Real.IsNear.recentre' (Real.cos qz156) Bool.true 90419 524288 24728289 33579335680 90419 524288 24728289 33579335680 (ep561 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz23 (@Neg.neg Real Real.instNeg (Real.sin qz156)) 151349 262144 1 262144 32277 32768 24728289 33579335680 4885091673 8589934592 377570271867 880262137249792 qz296 (@Enclosure.Real.IsNear.neg (Real.sin qz156) Bool.false 32277 32768 24728289 33579335680 (@Enclosure.Real.IsNear.recentre' (Real.sin qz156) Bool.false 516432 524288 24728289 33579335680 32277 32768 24728289 33579335680 (ep563 rfl rfl) rfl)) rfl)

noncomputable def ep565 := @ep546 13684825231 137438953472 1499367060421 3521048548999168 Bool.true 4885091673 8589934592 377570271867 880262137249792 Bool.false 958338913694325407744 111565333057 137438953472 3334555379579 3521048548999168 Bool.true 374903390155831246848 43644498819 34359738368 3357110449655 3521048548999168 (ep547 (BSN.head_sum_c_succ qz148 2 3 rfl rfl) (ep557 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep558 ep564) rfl rfl

noncomputable abbrev qz157 := (@HMul.hMul Real Real Real qz267 qz424 (Real.log (Enclosure.sfrac Bool.false 4 1)))

noncomputable def ep566 := @Enclosure.Complex.IsNear.of_eq qz423 (Complex.mk (@HMul.hMul Real Real Real qz0 qz26 (Real.cos qz157)) (@HMul.hMul Real Real Real qz0 qz26 (@Neg.neg Real Real.instNeg (Real.sin qz157)))) Bool.true 133114380399 274877906944 13029790927567 35210485489991680 Bool.false 8550842517 68719476736 3245364626613 8802621372497920 (BSN.cpow_neg_s_mk qz153 93095 1000 4 qz154 rfl)

noncomputable def ep567 := nat_lit 5318694945634758753176536953655296

noncomputable def ep568 := BSN.cos_dyadic_bound_f 270054408 1073741824 2 1 524288 256441 ep567 ep57 ep567 ep567 ep58 ep567 507793 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 270054408) qz283 0 1 ep567 ep57 ep567 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 270054408) qz284 0 1 ep567 ep58 ep567 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz428 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 67662935) qz31)

noncomputable def ep569 := @Enclosure.Real.IsNear.cos_image qz157 qz428 Bool.false 67662935 524288 191 262144 Bool.true 507793 524288 1 128095 (@Enclosure.Real.IsNear.recentre' qz157 Bool.false 422893347 3276800 18619 25619000 67662935 524288 191 262144 (@Enclosure.Real.IsNear.mulLit_ff qz153 qz28 93095 1000 0 1 363408 262144 1 128095 422893347 3276800 18619 25619000 qz155 qz299 rfl) rfl) (Enclosure.sfrac_false_div 67662935 524288) (BSN.cos_reduce2 qz428 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 19003389596293702615040) qz33) 226375608064910080 72057594037927936 Bool.false 507793 524288 20 1000000000000000 256190 128095 (BSN.sin_reduce_arg_pos_rat_q2 67662935 524288 226375608064910080 72057594037927936 20 19003389596293702615040 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 507793 524288 19003389596293702615040 75557863725914323419136 270054408 1073741824 256441 256190 (ep568 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep570 := BSN.sin_dyadic_bound_f 270054408 1073741824 2 1 524288 256441 ep567 ep69 ep567 ep567 ep70 ep567 130476 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 270054408) qz289 0 1 ep567 ep69 ep567 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 270054408) qz290 0 1 ep567 ep70 ep567 rfl rfl rfl rfl) rfl rfl

noncomputable def ep571 := @Enclosure.Real.IsNear.sin_image qz157 qz428 Bool.false 67662935 524288 191 262144 Bool.true 130476 524288 1 128095 (@Enclosure.Real.IsNear.recentre' qz157 Bool.false 422893347 3276800 18619 25619000 67662935 524288 191 262144 (@Enclosure.Real.IsNear.mulLit_ff qz153 qz28 93095 1000 0 1 363408 262144 1 128095 422893347 3276800 18619 25619000 qz155 qz299 rfl) rfl) (Enclosure.sfrac_false_div 67662935 524288) (BSN.sin_reduce2 qz428 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 19003389596293702615040) qz33) 226375608064910080 72057594037927936 Bool.false 130476 524288 20 1000000000000000 256190 128095 (BSN.sin_reduce_arg_pos_rat_q2 67662935 524288 226375608064910080 72057594037927936 20 19003389596293702615040 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 130476 524288 19003389596293702615040 75557863725914323419136 270054408 1073741824 256441 256190 (ep570 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep572 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz26 (Real.cos qz157)) (@HMul.hMul Real Real Real qz0 qz26 (@Neg.neg Real Real.instNeg (Real.sin qz157))) Bool.true 133114380399 274877906944 13029790927567 35210485489991680 Bool.false 8550842517 68719476736 3245364626613 8802621372497920 (@Enclosure.Real.IsNear.mulLit_ft qz26 (Real.cos qz157) 262143 524288 1 524288 507793 524288 24728289 33579335680 133114380399 274877906944 13029790927567 35210485489991680 qz301 (@Enclosure.Real.IsNear.recentre' (Real.cos qz157) Bool.true 507793 524288 24728289 33579335680 507793 524288 24728289 33579335680 (ep569 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz26 (@Neg.neg Real Real.instNeg (Real.sin qz157)) 262143 524288 1 524288 32619 131072 24728289 33579335680 8550842517 68719476736 3245364626613 8802621372497920 qz301 (@Enclosure.Real.IsNear.neg (Real.sin qz157) Bool.true 32619 131072 24728289 33579335680 (@Enclosure.Real.IsNear.recentre' (Real.sin qz157) Bool.true 130476 524288 24728289 33579335680 32619 131072 24728289 33579335680 (ep571 rfl rfl) rfl)) rfl)

noncomputable def ep573 := @ep544 133114380399 274877906944 13029790927567 35210485489991680 Bool.false 8550842517 68719476736 3245364626613 8802621372497920 Bool.false 12371744104106143252480 90016285715 274877906944 46375344723357 35210485489991680 Bool.true 2705422409536559382528 78738155121 68719476736 23276281501501 17605242744995840 (ep545 (BSN.head_sum_c_succ qz148 3 4 rfl rfl) (ep565 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep566 ep572) rfl rfl

noncomputable abbrev qz158 := (@HMul.hMul Real Real Real qz267 qz424 (Real.log (Enclosure.sfrac Bool.false 5 1)))

noncomputable def ep574 := @Enclosure.Complex.IsNear.of_eq qz422 (Complex.mk (@HMul.hMul Real Real Real qz0 qz29 (Real.cos qz158)) (@HMul.hMul Real Real Real qz0 qz29 (@Neg.neg Real Real.instNeg (Real.sin qz158)))) Bool.false 34948307857 137438953472 1163426973173 3521048548999168 Bool.false 12640458259 34359738368 582566484001 1760524274499584 (BSN.cpow_neg_s_mk qz153 93095 1000 5 qz154 rfl)

noncomputable def ep575 := nat_lit 177841377630898903499003099740435216

noncomputable def ep576 := BSN.sin_dyadic_bound_f 649393898 1073741824 2 1 524288 256441 ep575 ep69 ep575 ep575 ep70 ep575 298106 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 649393898) qz289 0 1 ep575 ep69 ep575 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 649393898) qz290 0 1 ep575 ep70 ep575 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz429 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 78554305) qz31)

noncomputable def ep577 := @Enclosure.Real.IsNear.cos_image qz158 qz429 Bool.false 78554305 524288 191 262144 Bool.false 298106 524288 1 128095 (@Enclosure.Real.IsNear.recentre' qz158 Bool.false 490964411 3276800 18619 25619000 78554305 524288 191 262144 (@Enclosure.Real.IsNear.mulLit_ff qz153 qz32 93095 1000 0 1 421904 262144 1 128095 490964411 3276800 18619 25619000 qz155 qz304 rfl) rfl) (Enclosure.sfrac_false_div 78554305 524288) (BSN.cos_reduce3 qz429 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 45697033135265582940160) qz33) 226375608064910080 72057594037927936 Bool.false 298106 524288 23 1000000000000000 256190 128095 (BSN.sin_reduce_arg_pos_rat_q3 78554305 524288 226375608064910080 72057594037927936 23 45697033135265582940160 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 298106 524288 45697033135265582940160 75557863725914323419136 649393898 1073741824 256441 256190 (ep576 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep578 := BSN.cos_dyadic_bound_f 649393898 1073741824 2 1 524288 256441 ep575 ep57 ep575 ep575 ep58 ep575 431288 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 649393898) qz283 0 1 ep575 ep57 ep575 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 649393898) qz284 0 1 ep575 ep58 ep575 rfl rfl rfl rfl) rfl rfl

noncomputable def ep579 := @Enclosure.Real.IsNear.sin_image qz158 qz429 Bool.false 78554305 524288 191 262144 Bool.true 431288 524288 1 128095 (@Enclosure.Real.IsNear.recentre' qz158 Bool.false 490964411 3276800 18619 25619000 78554305 524288 191 262144 (@Enclosure.Real.IsNear.mulLit_ff qz153 qz32 93095 1000 0 1 421904 262144 1 128095 490964411 3276800 18619 25619000 qz155 qz304 rfl) rfl) (Enclosure.sfrac_false_div 78554305 524288) (BSN.sin_reduce3 qz429 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 45697033135265582940160) qz33) 226375608064910080 72057594037927936 Bool.false 431288 524288 23 1000000000000000 256190 128095 (BSN.sin_reduce_arg_pos_rat_q3 78554305 524288 226375608064910080 72057594037927936 23 45697033135265582940160 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 431288 524288 45697033135265582940160 75557863725914323419136 649393898 1073741824 256441 256190 (ep578 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep580 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz29 (Real.cos qz158)) (@HMul.hMul Real Real Real qz0 qz29 (@Neg.neg Real Real.instNeg (Real.sin qz158))) Bool.false 34948307857 137438953472 1163426973173 3521048548999168 Bool.false 12640458259 34359738368 582566484001 1760524274499584 (@Enclosure.Real.IsNear.mulLit_ff qz29 (Real.cos qz158) 234469 524288 1 524288 149053 262144 24728289 33579335680 34948307857 137438953472 1163426973173 3521048548999168 qz305 (@Enclosure.Real.IsNear.recentre' (Real.cos qz158) Bool.false 298106 524288 24728289 33579335680 149053 262144 24728289 33579335680 (ep577 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz29 (@Neg.neg Real Real.instNeg (Real.sin qz158)) 234469 524288 1 524288 53911 65536 24728289 33579335680 12640458259 34359738368 582566484001 1760524274499584 qz305 (@Enclosure.Real.IsNear.neg (Real.sin qz158) Bool.true 53911 65536 24728289 33579335680 (@Enclosure.Real.IsNear.recentre' (Real.sin qz158) Bool.true 431288 524288 24728289 33579335680 53911 65536 24728289 33579335680 (ep579 rfl rfl) rfl)) rfl)

noncomputable def ep581 := @ep542 34948307857 137438953472 1163426973173 3521048548999168 Bool.false 12640458259 34359738368 582566484001 1760524274499584 Bool.false 21978261819072853311488 159912901429 274877906944 58009614455087 35210485489991680 Bool.true 1836776732274829819904 53457238603 68719476736 29101946341511 17605242744995840 (ep543 (BSN.head_sum_c_succ qz148 4 5 rfl rfl) (ep573 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep574 ep580) rfl rfl

noncomputable abbrev qz159 := (@HMul.hMul Real Real Real qz267 qz424 qz307)

noncomputable def ep582 := @Enclosure.Complex.IsNear.of_eq qz421 (Complex.mk (@HMul.hMul Real Real Real qz0 qz34 (Real.cos qz159)) (@HMul.hMul Real Real Real qz0 qz34 (@Neg.neg Real Real.instNeg (Real.sin qz159)))) Bool.true 26806886477 68719476736 532492898173 1760524274499584 Bool.false 8273249467 68719476736 530274548963 1760524274499584 (BSN.cpow_neg_s_mk qz153 93095 1000 6 qz154 rfl)

noncomputable def ep583 := @Enclosure.Real.IsNear.mulLit_ff qz153 qz307 93095 1000 0 1 4034681531866359 2251799813685248 100000000025619 12809500000000000000 75121735441819738221 450359962737049600 1861900000477000161 2561900000000000000000 qz155 (BSN.isNear_log_sfrac 6 1 4034681531866359 2251799813685248 100000000025619 12809500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz308) Bool.false 16922680887833197019136 9444732965739290427392 1000000000256190 128095000000000000000 4034681531866359 2251799813685248 100000000025619 12809500000000000000 (BSN.log_rat_reduce_isNear 6 1 2 12 8 106290 262144 24973259072661432 36028797018963968 128095 1000000000000000 rfl rfl rfl rfl (ep116 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep584 := nat_lit 10673721844562690534941159325250625

noncomputable def ep585 := BSN.cos_dyadic_bound_f 321424495 1073741824 2 1 524288 256441 ep584 ep57 ep584 ep584 ep58 ep584 500972 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 321424495) qz283 0 1 ep584 ep57 ep584 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 321424495) qz284 0 1 ep584 ep58 ep584 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz430 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 43726605) qz19)

noncomputable def ep586 := @Enclosure.Real.IsNear.cos_image qz159 qz430 Bool.false 43726605 262144 191 262144 Bool.true 500972 524288 1 128095 (@Enclosure.Real.IsNear.recentre' qz159 Bool.false 75121735441819738221 450359962737049600 1861900000477000161 2561900000000000000000 43726605 262144 191 262144 (ep583 rfl) rfl) (Enclosure.sfrac_false_div 43726605 262144) (BSN.cos_reduce2 qz430 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 11309119033474222653440) qz288) 226375608064910080 72057594037927936 Bool.false 500972 524288 26 1000000000000000 256190 128095 (BSN.sin_reduce_arg_pos_rat_q2 43726605 262144 226375608064910080 72057594037927936 26 11309119033474222653440 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 500972 524288 11309119033474222653440 37778931862957161709568 321424495 1073741824 256441 256190 (ep585 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep587 := BSN.sin_dyadic_bound_f 321424495 1073741824 2 1 524288 256441 ep584 ep69 ep584 ep584 ep70 ep584 154612 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 321424495) qz289 0 1 ep584 ep69 ep584 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 321424495) qz290 0 1 ep584 ep70 ep584 rfl rfl rfl rfl) rfl rfl

noncomputable def ep588 := @Enclosure.Real.IsNear.sin_image qz159 qz430 Bool.false 43726605 262144 191 262144 Bool.true 154612 524288 1 128095 (@Enclosure.Real.IsNear.recentre' qz159 Bool.false 75121735441819738221 450359962737049600 1861900000477000161 2561900000000000000000 43726605 262144 191 262144 (ep583 rfl) rfl) (Enclosure.sfrac_false_div 43726605 262144) (BSN.sin_reduce2 qz430 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 11309119033474222653440) qz288) 226375608064910080 72057594037927936 Bool.false 154612 524288 26 1000000000000000 256190 128095 (BSN.sin_reduce_arg_pos_rat_q2 43726605 262144 226375608064910080 72057594037927936 26 11309119033474222653440 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 154612 524288 11309119033474222653440 37778931862957161709568 321424495 1073741824 256441 256190 (ep587 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep589 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz34 (Real.cos qz159)) (@HMul.hMul Real Real Real qz0 qz34 (@Neg.neg Real Real.instNeg (Real.sin qz159))) Bool.true 26806886477 68719476736 532492898173 1760524274499584 Bool.false 8273249467 68719476736 530274548963 1760524274499584 (@Enclosure.Real.IsNear.mulLit_ft qz34 (Real.cos qz159) 214039 524288 1 524288 125243 131072 24728289 33579335680 26806886477 68719476736 532492898173 1760524274499584 qz310 (@Enclosure.Real.IsNear.recentre' (Real.cos qz159) Bool.true 500972 524288 24728289 33579335680 125243 131072 24728289 33579335680 (ep586 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz34 (@Neg.neg Real Real.instNeg (Real.sin qz159)) 214039 524288 1 524288 38653 131072 24728289 33579335680 8273249467 68719476736 530274548963 1760524274499584 qz310 (@Enclosure.Real.IsNear.neg (Real.sin qz159) Bool.true 38653 131072 24728289 33579335680 (@Enclosure.Real.IsNear.recentre' (Real.sin qz159) Bool.true 154612 524288 24728289 33579335680 38653 131072 24728289 33579335680 (ep588 rfl rfl) rfl)) rfl)

noncomputable def ep590 := @ep540 26806886477 68719476736 532492898173 1760524274499584 Bool.false 8273249467 68719476736 530274548963 1760524274499584 Bool.false 3620510063053248659456 52685355521 274877906944 68659472418547 35210485489991680 Bool.true 3105020090271028740096 2823999321 4294967296 34404691831141 17605242744995840 (ep541 (BSN.head_sum_c_succ qz148 5 6 rfl rfl) (ep581 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep582 ep589) rfl rfl

noncomputable abbrev qz160 := (@HMul.hMul Real Real Real qz267 qz424 qz312)

noncomputable def ep591 := @Enclosure.Complex.IsNear.of_eq qz420 (Complex.mk (@HMul.hMul Real Real Real qz0 qz36 (Real.cos qz160)) (@HMul.hMul Real Real Real qz0 qz36 (@Neg.neg Real Real.instNeg (Real.sin qz160)))) Bool.false 50954246679 274877906944 9833450774427 35210485489991680 Bool.false 45270535513 137438953472 4929520092241 17605242744995840 (BSN.cpow_neg_s_mk qz153 93095 1000 7 qz154 rfl)

noncomputable def ep592 := @Enclosure.Real.IsNear.mulLit_ff qz153 qz312 93095 1000 0 1 4381792198794487 2251799813685248 100000000025619 12809500000000000000 81584588949354553453 450359962737049600 1861900000477000161 2561900000000000000000 qz155 (BSN.isNear_log_sfrac 7 1 4381792198794487 2251799813685248 100000000025619 12809500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz313) Bool.false 18378568546572512002048 9444732965739290427392 1000000000256190 128095000000000000000 4381792198794487 2251799813685248 100000000025619 12809500000000000000 (BSN.log_rat_reduce_isNear 7 1 2 14 8 146699 262144 24973259072661432 36028797018963968 128095 1000000000000000 rfl rfl rfl rfl (ep130 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep593 := nat_lit 91772156958293005885100586181640625

noncomputable def ep594 := BSN.sin_dyadic_bound_f 550399125 1073741824 2 1 524288 256441 ep593 ep69 ep593 ep593 ep70 ep593 257133 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 550399125) qz289 0 1 ep593 ep69 ep593 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 550399125) qz290 0 1 ep593 ep70 ep593 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz431 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 94976961) qz31)

noncomputable def ep595 := @Enclosure.Real.IsNear.cos_image qz160 qz431 Bool.false 94976961 524288 191 262144 Bool.false 257133 524288 1 128095 (@Enclosure.Real.IsNear.recentre' qz160 Bool.false 81584588949354553453 450359962737049600 1861900000477000161 2561900000000000000000 94976961 524288 191 262144 (ep592 rfl) rfl) (Enclosure.sfrac_false_div 94976961 524288) (BSN.cos_reduce3 qz431 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 38730895257636953915392) qz33) 226375608064910080 72057594037927936 Bool.false 257133 524288 28 1000000000000000 256190 128095 (BSN.sin_reduce_arg_pos_rat_q3 94976961 524288 226375608064910080 72057594037927936 28 38730895257636953915392 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 257133 524288 38730895257636953915392 75557863725914323419136 550399125 1073741824 256441 256190 (ep594 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep596 := BSN.cos_dyadic_bound_f 550399125 1073741824 2 1 524288 256441 ep593 ep57 ep593 ep593 ep58 ep593 456902 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 550399125) qz283 0 1 ep593 ep57 ep593 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 550399125) qz284 0 1 ep593 ep58 ep593 rfl rfl rfl rfl) rfl rfl

noncomputable def ep597 := @Enclosure.Real.IsNear.sin_image qz160 qz431 Bool.false 94976961 524288 191 262144 Bool.true 456902 524288 1 128095 (@Enclosure.Real.IsNear.recentre' qz160 Bool.false 81584588949354553453 450359962737049600 1861900000477000161 2561900000000000000000 94976961 524288 191 262144 (ep592 rfl) rfl) (Enclosure.sfrac_false_div 94976961 524288) (BSN.sin_reduce3 qz431 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 38730895257636953915392) qz33) 226375608064910080 72057594037927936 Bool.false 456902 524288 28 1000000000000000 256190 128095 (BSN.sin_reduce_arg_pos_rat_q3 94976961 524288 226375608064910080 72057594037927936 28 38730895257636953915392 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 456902 524288 38730895257636953915392 75557863725914323419136 550399125 1073741824 256441 256190 (ep596 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep598 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz36 (Real.cos qz160)) (@HMul.hMul Real Real Real qz0 qz36 (@Neg.neg Real Real.instNeg (Real.sin qz160))) Bool.false 50954246679 274877906944 9833450774427 35210485489991680 Bool.false 45270535513 137438953472 4929520092241 17605242744995840 (@Enclosure.Real.IsNear.mulLit_ff qz36 (Real.cos qz160) 198163 524288 1 524288 257133 524288 24728289 33579335680 50954246679 274877906944 9833450774427 35210485489991680 qz315 (@Enclosure.Real.IsNear.recentre' (Real.cos qz160) Bool.false 257133 524288 24728289 33579335680 257133 524288 24728289 33579335680 (ep595 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz36 (@Neg.neg Real Real.instNeg (Real.sin qz160)) 198163 524288 1 524288 228451 262144 24728289 33579335680 45270535513 137438953472 4929520092241 17605242744995840 qz315 (@Enclosure.Real.IsNear.neg (Real.sin qz160) Bool.true 228451 262144 24728289 33579335680 (@Enclosure.Real.IsNear.recentre' (Real.sin qz160) Bool.true 456902 524288 24728289 33579335680 228451 262144 24728289 33579335680 (ep597 rfl rfl) rfl)) rfl)

noncomputable def ep599 := @ep538 50954246679 274877906944 9833450774427 35210485489991680 Bool.false 45270535513 137438953472 4929520092241 17605242744995840 Bool.false 28488236929244777676800 12954950275 34359738368 39246461596487 17605242744995840 Bool.true 193692041783137009664 45097442759 137438953472 19667105961691 8802621372497920 (ep539 (BSN.head_sum_c_succ qz148 6 7 rfl rfl) (ep590 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep591 ep598) rfl rfl

noncomputable abbrev qz161 := (@HMul.hMul Real Real Real qz267 qz424 qz317)

noncomputable def ep600 := @Enclosure.Complex.IsNear.of_eq qz419 (Complex.mk (@HMul.hMul Real Real Real qz0 qz38 (Real.cos qz161)) (@HMul.hMul Real Real Real qz0 qz38 (@Neg.neg Real Real.instNeg (Real.sin qz161)))) Bool.false 35836043427 274877906944 9192233602647 35210485489991680 Bool.false 90334989783 274877906944 9229895069787 35210485489991680 (BSN.cpow_neg_s_mk qz153 93095 1000 8 qz154 rfl)

noncomputable def ep601 := @Enclosure.Real.IsNear.mulLit_ff qz153 qz317 93095 1000 0 1 9364972152248037 4503599627370496 200000000076857 25619000000000000000 174366416502706200903 900719925474099200 3723800001431000483 5123800000000000000000 qz155 (BSN.isNear_log_sfrac 8 1 9364972152248037 4503599627370496 200000000076857 25619000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz318) Bool.false 19639770079031275290624 9444732965739290427392 1000000000384285 128095000000000000000 9364972152248037 4503599627370496 200000000076857 25619000000000000000 (BSN.log_rat_reduce_isNear 8 1 3 16 16 0 262144 24973259072661432 36028797018963968 128095 1000000000000000 rfl rfl rfl rfl (ep144 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep602 := nat_lit 27040152445516738441749615725138176

noncomputable def ep603 := BSN.sin_dyadic_bound_f 405510668 1073741824 2 1 524288 256441 ep602 ep69 ep602 ep602 ep70 ep602 193329 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 405510668) qz289 0 1 ep602 ep69 ep602 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 405510668) qz290 0 1 ep602 ep70 ep602 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz432 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 25373653) (@Nat.cast Real Real.instNatCast 131072))

noncomputable def ep604 := @Enclosure.Real.IsNear.cos_image qz161 qz432 Bool.false 25373653 131072 191 262144 Bool.false 193329 524288 1 128095 (@Enclosure.Real.IsNear.recentre' qz161 Bool.false 174366416502706200903 900719925474099200 3723800001431000483 5123800000000000000000 25373653 131072 191 262144 (ep601 rfl) rfl) (Enclosure.sfrac_false_div 25373653 131072) (BSN.cos_reduce3 qz432 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 7133819131585611431936) qz300) 226375608064910080 72057594037927936 Bool.false 193329 524288 30 1000000000000000 256190 128095 (BSN.sin_reduce_arg_pos_rat_q3 25373653 131072 226375608064910080 72057594037927936 30 7133819131585611431936 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 193329 524288 7133819131585611431936 18889465931478580854784 405510668 1073741824 256441 256190 (ep603 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep605 := BSN.cos_dyadic_bound_f 405510668 1073741824 2 1 524288 256441 ep602 ep57 ep602 ep602 ep58 ep602 487341 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 405510668) qz283 0 1 ep602 ep57 ep602 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 405510668) qz284 0 1 ep602 ep58 ep602 rfl rfl rfl rfl) rfl rfl

noncomputable def ep606 := @Enclosure.Real.IsNear.sin_image qz161 qz432 Bool.false 25373653 131072 191 262144 Bool.true 487341 524288 1 128095 (@Enclosure.Real.IsNear.recentre' qz161 Bool.false 174366416502706200903 900719925474099200 3723800001431000483 5123800000000000000000 25373653 131072 191 262144 (ep601 rfl) rfl) (Enclosure.sfrac_false_div 25373653 131072) (BSN.sin_reduce3 qz432 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 7133819131585611431936) qz300) 226375608064910080 72057594037927936 Bool.false 487341 524288 30 1000000000000000 256190 128095 (BSN.sin_reduce_arg_pos_rat_q3 25373653 131072 226375608064910080 72057594037927936 30 7133819131585611431936 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 487341 524288 7133819131585611431936 18889465931478580854784 405510668 1073741824 256441 256190 (ep605 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep607 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz38 (Real.cos qz161)) (@HMul.hMul Real Real Real qz0 qz38 (@Neg.neg Real Real.instNeg (Real.sin qz161))) Bool.false 35836043427 274877906944 9192233602647 35210485489991680 Bool.false 90334989783 274877906944 9229895069787 35210485489991680 (@Enclosure.Real.IsNear.mulLit_ff qz38 (Real.cos qz161) 185363 524288 1 524288 193329 524288 24728289 33579335680 35836043427 274877906944 9192233602647 35210485489991680 qz320 (@Enclosure.Real.IsNear.recentre' (Real.cos qz161) Bool.false 193329 524288 24728289 33579335680 193329 524288 24728289 33579335680 (ep604 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz38 (@Neg.neg Real Real.instNeg (Real.sin qz161)) 185363 524288 1 524288 487341 524288 24728289 33579335680 90334989783 274877906944 9229895069787 35210485489991680 qz320 (@Enclosure.Real.IsNear.neg (Real.sin qz161) Bool.true 487341 524288 24728289 33579335680 (@Enclosure.Real.IsNear.recentre' (Real.sin qz161) Bool.true 487341 524288 24728289 33579335680 487341 524288 24728289 33579335680 (ep606 rfl rfl) rfl)) rfl)

noncomputable def ep608 := @ep536 35836043427 274877906944 9192233602647 35210485489991680 Bool.false 90334989783 274877906944 9229895069787 35210485489991680 Bool.false 4792346692451603316736 139475645627 274877906944 7971377890511 3200953226362880 Bool.false 19255783558563758080 140104265 274877906944 7990756265141 3200953226362880 (ep537 (BSN.head_sum_c_succ qz148 7 8 rfl rfl) (ep599 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep600 ep607) rfl rfl

theorem EMRow26.d11 : Enclosure.Complex.IsNear qz147 Bool.false 139475645627 274877906944 7971377890511 3200953226362880 Bool.false 140104265 274877906944 7990756265141 3200953226362880 := ep535 (BSN.head_sum_c_succ qz148 8 9 rfl rfl) (ep608 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable abbrev qz162 := (BSN.headSumC qz417 17)

noncomputable abbrev qz163 := (@HPow.hPow Complex Complex Complex qz274 (@Nat.cast Complex Complex.instNatCast 16) qz418)

noncomputable def ep609 := @Enclosure.Complex.IsNear.of_eq qz162 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz148 16) qz163) Bool.false 19698319881 17179869184 1844563380337 440131068624896 Bool.true 68168483723 274877906944 29521081790301 7042097097998336

noncomputable def ep610 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz148 16) qz163 Bool.false 254983873115 274877906944 141023875202299 35210485489991680 Bool.true 17504612323 137438953472 35272657497531 8802621372497920 Bool.false

noncomputable abbrev qz164 := (@HPow.hPow Complex Complex Complex qz274 (@Nat.cast Complex Complex.instNatCast 15) qz418)

noncomputable def ep611 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz148 16) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz148 15) qz164) Bool.false 254983873115 274877906944 141023875202299 35210485489991680 Bool.true 17504612323 137438953472 35272657497531 8802621372497920

noncomputable def ep612 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz148 15) qz164 Bool.false 51109186957 68719476736 987360360563 258900628602880 Bool.false 14812312081 274877906944 7902850024329 2071205028823040 Bool.false

noncomputable abbrev qz165 := (@HPow.hPow Complex Complex Complex qz274 (@Nat.cast Complex Complex.instNatCast 14) qz418)

noncomputable def ep613 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz148 15) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz148 14) qz165) Bool.false 51109186957 68719476736 987360360563 258900628602880 Bool.false 14812312081 274877906944 7902850024329 2071205028823040

noncomputable def ep614 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz148 14) qz165 Bool.false 145445666707 274877906944 127297126290957 35210485489991680 Bool.false 29297610173 137438953472 63689235293451 17605242744995840 Bool.false

noncomputable abbrev qz166 := (@HPow.hPow Complex Complex Complex qz274 (@Nat.cast Complex Complex.instNatCast 13) qz418)

noncomputable def ep615 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz148 14) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz148 13) qz166) Bool.false 145445666707 274877906944 127297126290957 35210485489991680 Bool.false 29297610173 137438953472 63689235293451 17605242744995840

noncomputable def ep616 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz148 13) qz166 Bool.false 69227909413 274877906944 10912582260381 3200953226362880 Bool.false 60316159531 274877906944 10925943151131 3200953226362880 Bool.false

noncomputable abbrev qz167 := (@HPow.hPow Complex Complex Complex qz274 (@Nat.cast Complex Complex.instNatCast 12) qz418)

noncomputable def ep617 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz148 13) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz148 12) qz167) Bool.false 69227909413 274877906944 10912582260381 3200953226362880 Bool.false 60316159531 274877906944 10925943151131 3200953226362880

noncomputable def ep618 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz148 12) qz167 Bool.false 18246544125 137438953472 56262723250313 17605242744995840 Bool.true 2991841531 68719476736 14079868006327 4401310686248960 Bool.false

noncomputable abbrev qz168 := (@HPow.hPow Complex Complex Complex qz274 (@Nat.cast Complex Complex.instNatCast 11) qz418)

noncomputable def ep619 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz148 12) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz148 11) qz168) Bool.false 18246544125 137438953472 56262723250313 17605242744995840 Bool.true 2991841531 68719476736 14079868006327 4401310686248960

noncomputable def ep620 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz148 11) qz168 Bool.false 118051893273 274877906944 9512841972761 3200953226362880 Bool.true 13350322541 137438953472 4764041340463 1600476613181440 Bool.true

noncomputable abbrev qz169 := (@HPow.hPow Complex Complex Complex qz274 (@Nat.cast Complex Complex.instNatCast 10) qz418)

noncomputable def ep621 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz148 11) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz148 10) qz169) Bool.false 118051893273 274877906944 9512841972761 3200953226362880 Bool.true 13350322541 137438953472 4764041340463 1600476613181440

noncomputable def ep622 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz148 10) qz169 Bool.false 53312593263 274877906944 96391540614873 35210485489991680 Bool.false 31304891003 274877906944 96564390983113 35210485489991680 Bool.false

noncomputable abbrev qz433 := (@HPow.hPow Complex Complex Complex qz120 (@Nat.cast Complex Complex.instNatCast 9) qz149)

noncomputable def ep623 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz148 10) (@HAdd.hAdd Complex Complex Complex qz4 qz147 qz433) Bool.false 53312593263 274877906944 96391540614873 35210485489991680 Bool.false 31304891003 274877906944 96564390983113 35210485489991680

noncomputable def ep624 := @Enclosure.Complex.IsNear.addLitP qz147 qz433 Bool.false 139475645627 274877906944 7971377890511 3200953226362880 Bool.false 140104265 274877906944 7990756265141 3200953226362880 Bool.true

noncomputable abbrev qz170 := (@HMul.hMul Real Real Real qz267 qz424 qz322)

noncomputable def ep625 := @Enclosure.Complex.IsNear.of_eq qz433 (Complex.mk (@HMul.hMul Real Real Real qz0 qz49 (Real.cos qz170)) (@HMul.hMul Real Real Real qz0 qz49 (@Neg.neg Real Real.instNeg (Real.sin qz170)))) Bool.true 21540763091 68719476736 2176595954813 8802621372497920 Bool.false 15582393369 137438953472 4333036033281 17605242744995840 (BSN.cpow_neg_s_mk qz153 93095 1000 9 qz154 rfl)

noncomputable def ep626 := @Enclosure.Real.IsNear.mulLit_ff qz153 qz322 93095 1000 0 1 9895417793173221 4503599627370496 200000000076857 25619000000000000000 184242783891092201799 900719925474099200 3723800001431000483 5123800000000000000000 qz155 (BSN.isNear_log_sfrac 9 1 9895417793173221 4503599627370496 200000000076857 25619000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz323) Bool.false 20752195215788806766592 9444732965739290427392 1000000000384285 128095000000000000000 9895417793173221 4503599627370496 200000000076857 25619000000000000000 (BSN.log_rat_reduce_isNear 9 1 3 18 16 30876 262144 24973259072661432 36028797018963968 128095 1000000000000000 rfl rfl rfl rfl (ep171 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep627 := nat_lit 19284156487380682673965685519077041

noncomputable def ep628 := BSN.cos_dyadic_bound_f 372649173 1073741824 2 1 524288 256441 ep627 ep57 ep627 ep627 ep58 ep627 493028 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 372649173) qz283 0 1 ep627 ep57 ep627 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 372649173) qz284 0 1 ep627 ep58 ep627 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz434 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 53621707) qz19)

noncomputable def ep629 := @Enclosure.Real.IsNear.cos_image qz170 qz434 Bool.false 53621707 262144 191 262144 Bool.true 493028 524288 1 128095 (@Enclosure.Real.IsNear.recentre' qz170 Bool.false 184242783891092201799 900719925474099200 3723800001431000483 5123800000000000000000 53621707 262144 191 262144 (ep626 rfl) rfl) (Enclosure.sfrac_false_div 53621707 262144) (BSN.cos_reduce2 qz434 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 13111427179624901115904) qz288) 226375608064910080 72057594037927936 Bool.false 493028 524288 32 1000000000000000 256190 128095 (BSN.sin_reduce_arg_pos_rat_q2 53621707 262144 226375608064910080 72057594037927936 32 13111427179624901115904 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 493028 524288 13111427179624901115904 37778931862957161709568 372649173 1073741824 256441 256190 (ep628 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep630 := BSN.sin_dyadic_bound_f 372649173 1073741824 2 1 524288 256441 ep627 ep69 ep627 ep627 ep70 ep627 178326 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 372649173) qz289 0 1 ep627 ep69 ep627 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 372649173) qz290 0 1 ep627 ep70 ep627 rfl rfl rfl rfl) rfl rfl

noncomputable def ep631 := @Enclosure.Real.IsNear.sin_image qz170 qz434 Bool.false 53621707 262144 191 262144 Bool.true 178326 524288 1 128095 (@Enclosure.Real.IsNear.recentre' qz170 Bool.false 184242783891092201799 900719925474099200 3723800001431000483 5123800000000000000000 53621707 262144 191 262144 (ep626 rfl) rfl) (Enclosure.sfrac_false_div 53621707 262144) (BSN.sin_reduce2 qz434 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 13111427179624901115904) qz288) 226375608064910080 72057594037927936 Bool.false 178326 524288 32 1000000000000000 256190 128095 (BSN.sin_reduce_arg_pos_rat_q2 53621707 262144 226375608064910080 72057594037927936 32 13111427179624901115904 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 178326 524288 13111427179624901115904 37778931862957161709568 372649173 1073741824 256441 256190 (ep630 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep632 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz49 (Real.cos qz170)) (@HMul.hMul Real Real Real qz0 qz49 (@Neg.neg Real Real.instNeg (Real.sin qz170))) Bool.true 21540763091 68719476736 2176595954813 8802621372497920 Bool.false 15582393369 137438953472 4333036033281 17605242744995840 (@Enclosure.Real.IsNear.mulLit_ft qz49 (Real.cos qz170) 174763 524288 1 524288 123257 131072 24728289 33579335680 21540763091 68719476736 2176595954813 8802621372497920 qz325 (@Enclosure.Real.IsNear.recentre' (Real.cos qz170) Bool.true 493028 524288 24728289 33579335680 123257 131072 24728289 33579335680 (ep629 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz49 (@Neg.neg Real Real.instNeg (Real.sin qz170)) 174763 524288 1 524288 89163 262144 24728289 33579335680 15582393369 137438953472 4333036033281 17605242744995840 qz325 (@Enclosure.Real.IsNear.neg (Real.sin qz170) Bool.true 89163 262144 24728289 33579335680 (@Enclosure.Real.IsNear.recentre' (Real.sin qz170) Bool.true 178326 524288 24728289 33579335680 89163 262144 24728289 33579335680 (ep631 rfl rfl) rfl)) rfl)

noncomputable def ep633 := @ep624 21540763091 68719476736 2176595954813 8802621372497920 Bool.false 15582393369 137438953472 4333036033281 17605242744995840 Bool.false 3663613512472558829568 53312593263 274877906944 96391540614873 35210485489991680 Bool.false 4302511458007348412416 31304891003 274877906944 96564390983113 35210485489991680 EMRow26.d11 (ep625 ep632) rfl rfl

noncomputable abbrev qz171 := (@HMul.hMul Real Real Real qz267 qz424 (Real.log (Enclosure.sfrac Bool.false 10 1)))

noncomputable def ep634 := @Enclosure.Complex.IsNear.of_eq qz169 (Complex.mk (@HMul.hMul Real Real Real qz0 qz51 (Real.cos qz171)) (@HMul.hMul Real Real Real qz0 qz51 (@Neg.neg Real Real.instNeg (Real.sin qz171)))) Bool.false 32369650005 137438953472 4124860542749 17605242744995840 Bool.true 58005536085 274877906944 8244518507073 35210485489991680 (BSN.cpow_neg_s_mk qz153 93095 1000 10 qz154 rfl)

noncomputable def ep635 := @Enclosure.Real.IsNear.mulLit_ff qz153 qz53 93095 1000 0 1 10369908600166117 4503599627370496 200000000076857 25619000000000000000 193077328226492932423 900719925474099200 3723800001431000483 5123800000000000000000 qz155 (BSN.isNear_log_sfrac 10 1 10369908600166117 4503599627370496 200000000076857 25619000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz327) Bool.false 21747274560655572598784 9444732965739290427392 1000000000384285 128095000000000000000 10369908600166117 4503599627370496 200000000076857 25619000000000000000 (BSN.log_rat_reduce_isNear 10 1 3 20 16 58495 262144 24973259072661432 36028797018963968 128095 1000000000000000 rfl rfl rfl rfl (ep186 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep636 := nat_lit 845835799537117818095659126551182259090588308171548620141373911754392712321

noncomputable def ep637 := nat_lit 143419205544629949812863948126473578273274837621029184497556595165607041

noncomputable def ep638 := nat_lit 2537220560200264194387351651757293830115218374839403802055126622072846922881

noncomputable def ep639 := BSN.cos_dyadic_bound_f 784469231 1073741824 3 2 524288 256441 ep636 ep74 ep637 ep638 ep77 ep637 390478 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 784469231) qz283 0 2 ep636 ep74 ep637 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 784469231) qz284 0 2 ep638 ep77 ep637 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz435 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 28096449) (@Nat.cast Real Real.instNatCast 131072))

noncomputable def ep640 := @Enclosure.Real.IsNear.cos_image qz171 qz435 Bool.false 28096449 131072 191 262144 Bool.false 390478 524288 1 128095 (@Enclosure.Real.IsNear.recentre' qz171 Bool.false 193077328226492932423 900719925474099200 3723800001431000483 5123800000000000000000 28096449 131072 191 262144 (ep635 rfl) rfl) (Enclosure.sfrac_false_div 28096449 131072) (BSN.cos_reduce0 qz435 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 13800528660083054215168) qz300) 226375608064910080 72057594037927936 Bool.false 390478 524288 34 1000000000000000 256190 128095 (BSN.sin_reduce_arg_pos_rat_q0 28096449 131072 226375608064910080 72057594037927936 34 13800528660083054215168 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 390478 524288 13800528660083054215168 18889465931478580854784 784469231 1073741824 256441 256190 (ep639 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep641 := nat_lit 378707282138368643507781910858912321

noncomputable def ep642 := BSN.sin_dyadic_bound_f 784469231 1073741824 2 1 524288 256441 ep641 ep69 ep641 ep641 ep70 ep641 349863 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 784469231) qz289 0 1 ep641 ep69 ep641 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 784469231) qz290 0 1 ep641 ep70 ep641 rfl rfl rfl rfl) rfl rfl

noncomputable def ep643 := @Enclosure.Real.IsNear.sin_image qz171 qz435 Bool.false 28096449 131072 191 262144 Bool.false 349863 524288 1 128095 (@Enclosure.Real.IsNear.recentre' qz171 Bool.false 193077328226492932423 900719925474099200 3723800001431000483 5123800000000000000000 28096449 131072 191 262144 (ep635 rfl) rfl) (Enclosure.sfrac_false_div 28096449 131072) (BSN.sin_reduce0 qz435 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 13800528660083054215168) qz300) 226375608064910080 72057594037927936 Bool.false 349863 524288 34 1000000000000000 256190 128095 (BSN.sin_reduce_arg_pos_rat_q0 28096449 131072 226375608064910080 72057594037927936 34 13800528660083054215168 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 349863 524288 13800528660083054215168 18889465931478580854784 784469231 1073741824 256441 256190 (ep642 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep644 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz51 (Real.cos qz171)) (@HMul.hMul Real Real Real qz0 qz51 (@Neg.neg Real Real.instNeg (Real.sin qz171))) Bool.false 32369650005 137438953472 4124860542749 17605242744995840 Bool.true 58005536085 274877906944 8244518507073 35210485489991680 (@Enclosure.Real.IsNear.mulLit_ff qz51 (Real.cos qz171) 165795 524288 1 524288 195239 262144 24728289 33579335680 32369650005 137438953472 4124860542749 17605242744995840 qz330 (@Enclosure.Real.IsNear.recentre' (Real.cos qz171) Bool.false 390478 524288 24728289 33579335680 195239 262144 24728289 33579335680 (ep640 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz51 (@Neg.neg Real Real.instNeg (Real.sin qz171)) 165795 524288 1 524288 349863 524288 24728289 33579335680 58005536085 274877906944 8244518507073 35210485489991680 qz330 (@Enclosure.Real.IsNear.neg (Real.sin qz171) Bool.false 349863 524288 24728289 33579335680 (@Enclosure.Real.IsNear.recentre' (Real.sin qz171) Bool.false 349863 524288 24728289 33579335680 349863 524288 24728289 33579335680 (ep643 rfl rfl) rfl)) rfl)

noncomputable def ep645 := @ep622 32369650005 137438953472 4124860542749 17605242744995840 Bool.true 58005536085 274877906944 8244518507073 35210485489991680 Bool.false 16224928666829356793856 118051893273 274877906944 9512841972761 3200953226362880 Bool.true 7339417434194767249408 13350322541 137438953472 4764041340463 1600476613181440 (ep623 (BSN.head_sum_c_succ qz148 9 10 rfl rfl) (ep633 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep634 ep644) rfl rfl

noncomputable abbrev qz172 := (@HMul.hMul Real Real Real qz267 qz424 (Real.log (Enclosure.sfrac Bool.false 11 1)))

noncomputable def ep646 := @Enclosure.Complex.IsNear.of_eq qz168 (Complex.mk (@HMul.hMul Real Real Real qz0 qz54 (Real.cos qz172)) (@HMul.hMul Real Real Real qz0 qz54 (@Neg.neg Real Real.instNeg (Real.sin qz172)))) Bool.true 81558805023 274877906944 1576836960051 7042097097998336 Bool.false 7366639479 137438953472 783003456043 3521048548999168 (BSN.cpow_neg_s_mk qz153 93095 1000 11 qz154 rfl)

noncomputable def ep647 := @Enclosure.Real.IsNear.mulLit_ff qz153 qz56 93095 1000 0 1 10799147631728357 4503599627370496 200000000076857 25619000000000000000 201069329755150278983 900719925474099200 3723800001431000483 5123800000000000000000 qz155 (BSN.isNear_log_sfrac 11 1 10799147631728357 4503599627370496 200000000076857 25619000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz332) Bool.false 22647454054174387339264 9444732965739290427392 1000000000384285 128095000000000000000 10799147631728357 4503599627370496 200000000076857 25619000000000000000 (BSN.log_rat_reduce_isNear 11 1 3 22 16 83480 262144 24973259072661432 36028797018963968 128095 1000000000000000 rfl rfl rfl rfl (ep196 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep648 := nat_lit 1356094118865199435074223108263936

noncomputable def ep649 := BSN.cos_dyadic_bound_f 191898888 1073741824 2 1 524288 256441 ep648 ep57 ep648 ep648 ep58 ep648 515937 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 191898888) qz283 0 1 ep648 ep57 ep648 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 191898888) qz284 0 1 ep648 ep58 ep648 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz436 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 117037753) qz31)

noncomputable def ep650 := @Enclosure.Real.IsNear.cos_image qz172 qz436 Bool.false 117037753 524288 191 262144 Bool.true 515937 524288 1 128095 (@Enclosure.Real.IsNear.recentre' qz172 Bool.false 201069329755150278983 900719925474099200 3723800001431000483 5123800000000000000000 117037753 524288 191 262144 (ep647 rfl) rfl) (Enclosure.sfrac_false_div 117037753 524288) (BSN.cos_reduce2 qz436 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 13503683809313015463936) qz33) 226375608064910080 72057594037927936 Bool.false 515937 524288 35 1000000000000000 256190 128095 (BSN.sin_reduce_arg_pos_rat_q2 117037753 524288 226375608064910080 72057594037927936 35 13503683809313015463936 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 515937 524288 13503683809313015463936 75557863725914323419136 191898888 1073741824 256441 256190 (ep649 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep651 := BSN.sin_dyadic_bound_f 191898888 1073741824 2 1 524288 256441 ep648 ep69 ep648 ep648 ep70 ep648 93202 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 191898888) qz289 0 1 ep648 ep69 ep648 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 191898888) qz290 0 1 ep648 ep70 ep648 rfl rfl rfl rfl) rfl rfl

noncomputable def ep652 := @Enclosure.Real.IsNear.sin_image qz172 qz436 Bool.false 117037753 524288 191 262144 Bool.true 93202 524288 1 128095 (@Enclosure.Real.IsNear.recentre' qz172 Bool.false 201069329755150278983 900719925474099200 3723800001431000483 5123800000000000000000 117037753 524288 191 262144 (ep647 rfl) rfl) (Enclosure.sfrac_false_div 117037753 524288) (BSN.sin_reduce2 qz436 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 13503683809313015463936) qz33) 226375608064910080 72057594037927936 Bool.false 93202 524288 35 1000000000000000 256190 128095 (BSN.sin_reduce_arg_pos_rat_q2 117037753 524288 226375608064910080 72057594037927936 35 13503683809313015463936 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 93202 524288 13503683809313015463936 75557863725914323419136 191898888 1073741824 256441 256190 (ep651 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep653 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz54 (Real.cos qz172)) (@HMul.hMul Real Real Real qz0 qz54 (@Neg.neg Real Real.instNeg (Real.sin qz172))) Bool.true 81558805023 274877906944 1576836960051 7042097097998336 Bool.false 7366639479 137438953472 783003456043 3521048548999168 (@Enclosure.Real.IsNear.mulLit_ft qz54 (Real.cos qz172) 158079 524288 1 524288 515937 524288 24728289 33579335680 81558805023 274877906944 1576836960051 7042097097998336 qz334 (@Enclosure.Real.IsNear.recentre' (Real.cos qz172) Bool.true 515937 524288 24728289 33579335680 515937 524288 24728289 33579335680 (ep650 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz54 (@Neg.neg Real Real.instNeg (Real.sin qz172)) 158079 524288 1 524288 46601 262144 24728289 33579335680 7366639479 137438953472 783003456043 3521048548999168 qz334 (@Enclosure.Real.IsNear.neg (Real.sin qz172) Bool.true 46601 262144 24728289 33579335680 (@Enclosure.Real.IsNear.recentre' (Real.sin qz172) Bool.true 93202 524288 24728289 33579335680 46601 262144 24728289 33579335680 (ep652 rfl rfl) rfl)) rfl)

noncomputable def ep654 := @ep620 81558805023 274877906944 1576836960051 7042097097998336 Bool.false 7366639479 137438953472 783003456043 3521048548999168 Bool.false 10031143716082679808000 18246544125 137438953472 56262723250313 17605242744995840 Bool.true 822391137949412491264 2991841531 68719476736 14079868006327 4401310686248960 (ep621 (BSN.head_sum_c_succ qz148 10 11 rfl rfl) (ep645 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep646 ep653) rfl rfl

noncomputable abbrev qz173 := (@HMul.hMul Real Real Real qz267 qz424 (Real.log (Enclosure.sfrac Bool.false 12 1)))

noncomputable def ep655 := @Enclosure.Complex.IsNear.of_eq qz167 (Complex.mk (@HMul.hMul Real Real Real qz0 qz57 (Real.cos qz173)) (@HMul.hMul Real Real Real qz0 qz57 (@Neg.neg Real Real.instNeg (Real.sin qz173)))) Bool.false 32734821163 274877906944 1502591672713 7042097097998336 Bool.false 72283525655 274877906944 1509286122365 7042097097998336 (BSN.cpow_neg_s_mk qz153 93095 1000 12 qz154 rfl)

noncomputable def ep656 := @Enclosure.Real.IsNear.mulLit_ff qz153 qz59 93095 1000 0 1 11191020447815397 4503599627370496 200000000076857 25619000000000000000 208365609717874876743 900719925474099200 3723800001431000483 5123800000000000000000 qz155 (BSN.isNear_log_sfrac 12 1 11191020447815397 4503599627370496 200000000076857 25619000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz336) Bool.false 23469270914176955449344 9444732965739290427392 1000000000384285 128095000000000000000 11191020447815397 4503599627370496 200000000076857 25619000000000000000 (BSN.log_rat_reduce_isNear 12 1 3 24 16 106290 262144 24973259072661432 36028797018963968 128095 1000000000000000 rfl rfl rfl rfl (ep210 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep657 := nat_lit 43463123515641000545430210472500625

noncomputable def ep658 := BSN.sin_dyadic_bound_f 456594035 1073741824 2 1 524288 256441 ep657 ep69 ep657 ep657 ep70 ep657 216287 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 456594035) qz289 0 1 ep657 ep69 ep657 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 456594035) qz290 0 1 ep657 ep70 ep657 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz437 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 121284747) qz31)

noncomputable def ep659 := @Enclosure.Real.IsNear.cos_image qz173 qz437 Bool.false 121284747 524288 191 262144 Bool.false 216287 524288 1 128095 (@Enclosure.Real.IsNear.recentre' qz173 Bool.false 208365609717874876743 900719925474099200 3723800001431000483 5123800000000000000000 121284747 524288 191 262144 (ep656 rfl) rfl) (Enclosure.sfrac_false_div 121284747 524288) (BSN.cos_reduce3 qz437 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 32129948870666568597504) qz33) 226375608064910080 72057594037927936 Bool.false 216287 524288 36 1000000000000000 256190 128095 (BSN.sin_reduce_arg_pos_rat_q3 121284747 524288 226375608064910080 72057594037927936 36 32129948870666568597504 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 216287 524288 32129948870666568597504 75557863725914323419136 456594035 1073741824 256441 256190 (ep658 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep660 := BSN.cos_dyadic_bound_f 456594035 1073741824 2 1 524288 256441 ep657 ep57 ep657 ep657 ep58 ep657 477595 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 456594035) qz283 0 1 ep657 ep57 ep657 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 456594035) qz284 0 1 ep657 ep58 ep657 rfl rfl rfl rfl) rfl rfl

noncomputable def ep661 := @Enclosure.Real.IsNear.sin_image qz173 qz437 Bool.false 121284747 524288 191 262144 Bool.true 477595 524288 1 128095 (@Enclosure.Real.IsNear.recentre' qz173 Bool.false 208365609717874876743 900719925474099200 3723800001431000483 5123800000000000000000 121284747 524288 191 262144 (ep656 rfl) rfl) (Enclosure.sfrac_false_div 121284747 524288) (BSN.sin_reduce3 qz437 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 32129948870666568597504) qz33) 226375608064910080 72057594037927936 Bool.false 477595 524288 36 1000000000000000 256190 128095 (BSN.sin_reduce_arg_pos_rat_q3 121284747 524288 226375608064910080 72057594037927936 36 32129948870666568597504 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 477595 524288 32129948870666568597504 75557863725914323419136 456594035 1073741824 256441 256190 (ep660 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep662 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz57 (Real.cos qz173)) (@HMul.hMul Real Real Real qz0 qz57 (@Neg.neg Real Real.instNeg (Real.sin qz173))) Bool.false 32734821163 274877906944 1502591672713 7042097097998336 Bool.false 72283525655 274877906944 1509286122365 7042097097998336 (@Enclosure.Real.IsNear.mulLit_ff qz57 (Real.cos qz173) 151349 524288 1 524288 216287 524288 24728289 33579335680 32734821163 274877906944 1502591672713 7042097097998336 qz338 (@Enclosure.Real.IsNear.recentre' (Real.cos qz173) Bool.false 216287 524288 24728289 33579335680 216287 524288 24728289 33579335680 (ep659 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz57 (@Neg.neg Real Real.instNeg (Real.sin qz173)) 151349 524288 1 524288 477595 524288 24728289 33579335680 72283525655 274877906944 1509286122365 7042097097998336 qz338 (@Enclosure.Real.IsNear.neg (Real.sin qz173) Bool.true 477595 524288 24728289 33579335680 (@Enclosure.Real.IsNear.recentre' (Real.sin qz173) Bool.true 477595 524288 24728289 33579335680 477595 524288 24728289 33579335680 (ep661 rfl rfl) rfl)) rfl)

noncomputable def ep663 := @ep618 32734821163 274877906944 1502591672713 7042097097998336 Bool.false 72283525655 274877906944 1509286122365 7042097097998336 Bool.false 9514611420777137831936 69227909413 274877906944 10912582260381 3200953226362880 Bool.false 4144894921695419170816 60316159531 274877906944 10925943151131 3200953226362880 (ep619 (BSN.head_sum_c_succ qz148 11 12 rfl rfl) (ep654 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep655 ep662) rfl rfl

noncomputable abbrev qz174 := (@HMul.hMul Real Real Real qz267 qz424 (Real.log (Enclosure.sfrac Bool.false 13 1)))

noncomputable def ep664 := @Enclosure.Complex.IsNear.of_eq qz166 (Complex.mk (@HMul.hMul Real Real Real qz0 qz60 (Real.cos qz174)) (@HMul.hMul Real Real Real qz0 qz60 (@Neg.neg Real Real.instNeg (Real.sin qz174)))) Bool.false 38108878647 137438953472 3629360713383 17605242744995840 Bool.true 1720939185 274877906944 7193095924461 35210485489991680 (BSN.cpow_neg_s_mk qz153 93095 1000 13 qz154 rfl)

noncomputable def ep665 := @Enclosure.Real.IsNear.mulLit_ff qz153 qz62 93095 1000 0 1 11551488463034085 4503599627370496 200000000076857 25619000000000000000 43015432738646325723 180143985094819840 3723800001431000483 5123800000000000000000 qz155 (BSN.isNear_log_sfrac 13 1 11551488463034085 4503599627370496 200000000076857 25619000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz340) Bool.false 24225227133228857425920 9444732965739290427392 1000000000384285 128095000000000000000 11551488463034085 4503599627370496 200000000076857 25619000000000000000 (BSN.log_rat_reduce_isNear 13 1 3 26 16 127272 262144 24973259072661432 36028797018963968 128095 1000000000000000 rfl rfl rfl rfl (ep224 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep666 := BSN.cos_dyadic_bound_f 24242142 1073741824 1 0 524288 256441 0 1 1 0 1 1 524154 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 24242142) qz283 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 24242142) qz284 0 0 rfl) rfl rfl

noncomputable abbrev qz438 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 62595693) qz19)

noncomputable def ep667 := @Enclosure.Real.IsNear.cos_image qz174 qz438 Bool.false 62595693 262144 191 262144 Bool.false 524154 524288 1 128095 (@Enclosure.Real.IsNear.recentre' qz174 Bool.false 43015432738646325723 180143985094819840 3723800001431000483 5123800000000000000000 62595693 262144 191 262144 (ep665 rfl) rfl) (Enclosure.sfrac_false_div 62595693 262144) (BSN.cos_reduce0 qz438 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 852944547231098208256) qz288) 226375608064910080 72057594037927936 Bool.false 524154 524288 38 1000000000000000 256190 128095 (BSN.sin_reduce_arg_pos_rat_q0 62595693 262144 226375608064910080 72057594037927936 38 852944547231098208256 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 524154 524288 852944547231098208256 37778931862957161709568 24242142 1073741824 256441 256190 (ep666 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep668 := BSN.sin_dyadic_bound_f 24242142 1073741824 1 0 524288 256441 0 1 1 0 1 1 11835 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 24242142) qz289 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 24242142) qz290 0 0 rfl) rfl rfl

noncomputable def ep669 := @Enclosure.Real.IsNear.sin_image qz174 qz438 Bool.false 62595693 262144 191 262144 Bool.false 11835 524288 1 128095 (@Enclosure.Real.IsNear.recentre' qz174 Bool.false 43015432738646325723 180143985094819840 3723800001431000483 5123800000000000000000 62595693 262144 191 262144 (ep665 rfl) rfl) (Enclosure.sfrac_false_div 62595693 262144) (BSN.sin_reduce0 qz438 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 852944547231098208256) qz288) 226375608064910080 72057594037927936 Bool.false 11835 524288 38 1000000000000000 256190 128095 (BSN.sin_reduce_arg_pos_rat_q0 62595693 262144 226375608064910080 72057594037927936 38 852944547231098208256 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 11835 524288 852944547231098208256 37778931862957161709568 24242142 1073741824 256441 256190 (ep668 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep670 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz60 (Real.cos qz174)) (@HMul.hMul Real Real Real qz0 qz60 (@Neg.neg Real Real.instNeg (Real.sin qz174))) Bool.false 38108878647 137438953472 3629360713383 17605242744995840 Bool.true 1720939185 274877906944 7193095924461 35210485489991680 (@Enclosure.Real.IsNear.mulLit_ff qz60 (Real.cos qz174) 145411 524288 1 524288 262077 262144 24728289 33579335680 38108878647 137438953472 3629360713383 17605242744995840 qz342 (@Enclosure.Real.IsNear.recentre' (Real.cos qz174) Bool.false 524154 524288 24728289 33579335680 262077 262144 24728289 33579335680 (ep667 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz60 (@Neg.neg Real Real.instNeg (Real.sin qz174)) 145411 524288 1 524288 11835 524288 24728289 33579335680 1720939185 274877906944 7193095924461 35210485489991680 qz342 (@Enclosure.Real.IsNear.neg (Real.sin qz174) Bool.false 11835 524288 24728289 33579335680 (@Enclosure.Real.IsNear.recentre' (Real.sin qz174) Bool.false 11835 524288 24728289 33579335680 11835 524288 24728289 33579335680 (ep669 rfl rfl) rfl)) rfl)

noncomputable def ep671 := @ep616 38108878647 137438953472 3629360713383 17605242744995840 Bool.true 1720939185 274877906944 7193095924461 35210485489991680 Bool.false 19989900219247392456704 145445666707 274877906944 127297126290957 35210485489991680 Bool.false 16106531525630963482624 29297610173 137438953472 63689235293451 17605242744995840 (ep617 (BSN.head_sum_c_succ qz148 12 13 rfl rfl) (ep663 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep664 ep670) rfl rfl

noncomputable abbrev qz175 := (@HMul.hMul Real Real Real qz267 qz424 (Real.log (Enclosure.sfrac Bool.false 14 1)))

noncomputable def ep672 := @Enclosure.Complex.IsNear.of_eq qz165 (Complex.mk (@HMul.hMul Real Real Real qz0 qz63 (Real.cos qz175)) (@HMul.hMul Real Real Real qz0 qz63 (@Neg.neg Real Real.instNeg (Real.sin qz175)))) Bool.false 58991081121 274877906944 6983882745611 35210485489991680 Bool.true 43782908265 274877906944 6969979826691 35210485489991680 (BSN.cpow_neg_s_mk qz153 93095 1000 14 qz154 rfl)

noncomputable def ep673 := @Enclosure.Real.IsNear.mulLit_ff qz153 qz65 93095 1000 0 1 11885241781671653 4503599627370496 200000000076857 25619000000000000000 221291316732944507207 900719925474099200 3723800001431000483 5123800000000000000000 qz155 (BSN.isNear_log_sfrac 14 1 11885241781671653 4503599627370496 200000000076857 25619000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz344) Bool.false 24925158572916270432256 9444732965739290427392 1000000000384285 128095000000000000000 11885241781671653 4503599627370496 200000000076857 25619000000000000000 (BSN.log_rat_reduce_isNear 14 1 3 28 16 146699 262144 24973259072661432 36028797018963968 128095 1000000000000000 rfl rfl rfl rfl (ep235 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep674 := nat_lit 220906770423805009155699657800200161

noncomputable def ep675 := BSN.cos_dyadic_bound_f 685570713 1073741824 2 1 524288 256441 ep674 ep57 ep674 ep674 ep58 ep674 421001 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 685570713) qz283 0 1 ep674 ep57 ep674 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 685570713) qz284 0 1 ep674 ep58 ep674 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz439 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 128808499) qz31)

noncomputable def ep676 := @Enclosure.Real.IsNear.cos_image qz175 qz439 Bool.false 128808499 524288 191 262144 Bool.false 421001 524288 1 128095 (@Enclosure.Real.IsNear.recentre' qz175 Bool.false 221291316732944507207 900719925474099200 3723800001431000483 5123800000000000000000 128808499 524288 191 262144 (ep673 rfl) rfl) (Enclosure.sfrac_false_div 128808499 524288) (BSN.cos_reduce0 qz439 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 48242750176543153061888) qz33) 226375608064910080 72057594037927936 Bool.false 421001 524288 39 1000000000000000 256190 128095 (BSN.sin_reduce_arg_pos_rat_q0 128808499 524288 226375608064910080 72057594037927936 39 48242750176543153061888 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 421001 524288 48242750176543153061888 75557863725914323419136 685570713 1073741824 256441 256190 (ep675 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep677 := BSN.sin_dyadic_bound_f 685570713 1073741824 2 1 524288 256441 ep674 ep69 ep674 ep674 ep70 ep674 312465 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 685570713) qz289 0 1 ep674 ep69 ep674 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 685570713) qz290 0 1 ep674 ep70 ep674 rfl rfl rfl rfl) rfl rfl

noncomputable def ep678 := @Enclosure.Real.IsNear.sin_image qz175 qz439 Bool.false 128808499 524288 191 262144 Bool.false 312465 524288 1 128095 (@Enclosure.Real.IsNear.recentre' qz175 Bool.false 221291316732944507207 900719925474099200 3723800001431000483 5123800000000000000000 128808499 524288 191 262144 (ep673 rfl) rfl) (Enclosure.sfrac_false_div 128808499 524288) (BSN.sin_reduce0 qz439 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 48242750176543153061888) qz33) 226375608064910080 72057594037927936 Bool.false 312465 524288 39 1000000000000000 256190 128095 (BSN.sin_reduce_arg_pos_rat_q0 128808499 524288 226375608064910080 72057594037927936 39 48242750176543153061888 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 312465 524288 48242750176543153061888 75557863725914323419136 685570713 1073741824 256441 256190 (ep677 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep679 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz63 (Real.cos qz175)) (@HMul.hMul Real Real Real qz0 qz63 (@Neg.neg Real Real.instNeg (Real.sin qz175))) Bool.false 58991081121 274877906944 6983882745611 35210485489991680 Bool.true 43782908265 274877906944 6969979826691 35210485489991680 (@Enclosure.Real.IsNear.mulLit_ff qz63 (Real.cos qz175) 140121 524288 1 524288 421001 524288 24728289 33579335680 58991081121 274877906944 6983882745611 35210485489991680 qz346 (@Enclosure.Real.IsNear.recentre' (Real.cos qz175) Bool.false 421001 524288 24728289 33579335680 421001 524288 24728289 33579335680 (ep676 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz63 (@Neg.neg Real Real.instNeg (Real.sin qz175)) 140121 524288 1 524288 312465 524288 24728289 33579335680 43782908265 274877906944 6969979826691 35210485489991680 qz346 (@Enclosure.Real.IsNear.neg (Real.sin qz175) Bool.false 312465 524288 24728289 33579335680 (@Enclosure.Real.IsNear.recentre' (Real.sin qz175) Bool.false 312465 524288 24728289 33579335680 312465 524288 24728289 33579335680 (ep678 rfl rfl) rfl)) rfl)

noncomputable def ep680 := @ep614 58991081121 274877906944 6983882745611 35210485489991680 Bool.true 43782908265 274877906944 6969979826691 35210485489991680 Bool.false 56195145345398978117632 51109186957 68719476736 987360360563 258900628602880 Bool.false 2035788670913302495232 14812312081 274877906944 7902850024329 2071205028823040 (ep615 (BSN.head_sum_c_succ qz148 13 14 rfl rfl) (ep671 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep672 ep679) rfl rfl

noncomputable abbrev qz176 := (@HMul.hMul Real Real Real qz267 qz424 (Real.log (Enclosure.sfrac Bool.false 15 1)))

noncomputable def ep681 := @Enclosure.Complex.IsNear.of_eq qz164 (Complex.mk (@HMul.hMul Real Real Real qz0 qz66 (Real.cos qz176)) (@HMul.hMul Real Real Real qz0 qz66 (@Neg.neg Real Real.instNeg (Real.sin qz176)))) Bool.false 50547125287 274877906944 6742866165731 35210485489991680 Bool.true 49821536727 274877906944 6742179576531 35210485489991680 (BSN.cpow_neg_s_mk qz153 93095 1000 15 qz154 rfl)

noncomputable def ep682 := @Enclosure.Real.IsNear.mulLit_ff qz153 qz68 93095 1000 0 1 12195956895733477 4503599627370496 200000000076857 25619000000000000000 227076521441661608263 900719925474099200 3723800001431000483 5123800000000000000000 qz155 (BSN.isNear_log_sfrac 15 1 12195956895733477 4503599627370496 200000000076857 25619000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz348) Bool.false 25576775395801252757504 9444732965739290427392 1000000000384285 128095000000000000000 12195956895733477 4503599627370496 200000000076857 25619000000000000000 (BSN.log_rat_reduce_isNear 15 1 3 30 16 164785 262144 24973259072661432 36028797018963968 128095 1000000000000000 rfl rfl rfl rfl (ep249 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep683 := nat_lit 1088676169099775440604467597587400753814154033287577395887075567726053395041

noncomputable def ep684 := nat_lit 237569315906301961849773900934352483256713894657389547514196497268836961

noncomputable def ep685 := nat_lit 3265553368667513717889703244960333556475948672073417408566198310183622511201

noncomputable def ep686 := BSN.cos_dyadic_bound_f 835552597 1073741824 3 2 524288 256441 ep683 ep74 ep684 ep685 ep77 ep684 373397 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 835552597) qz283 0 2 ep683 ep74 ep684 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 835552597) qz284 0 2 ep685 ep77 ep684 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz440 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 132175931) qz31)

noncomputable def ep687 := @Enclosure.Real.IsNear.cos_image qz176 qz440 Bool.false 132175931 524288 191 262144 Bool.false 373397 524288 1 128095 (@Enclosure.Real.IsNear.recentre' qz176 Bool.false 227076521441661608263 900719925474099200 3723800001431000483 5123800000000000000000 132175931 524288 191 262144 (ep682 rfl) rfl) (Enclosure.sfrac_false_div 132175931 524288) (BSN.cos_reduce0 qz440 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 58796786984656339730432) qz33) 226375608064910080 72057594037927936 Bool.false 373397 524288 40 1000000000000000 256190 128095 (BSN.sin_reduce_arg_pos_rat_q0 132175931 524288 226375608064910080 72057594037927936 40 58796786984656339730432 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 373397 524288 58796786984656339730432 75557863725914323419136 835552597 1073741824 256441 256190 (ep686 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep688 := nat_lit 487410828671565279012199106253359281

noncomputable def ep689 := BSN.sin_dyadic_bound_f 835552597 1073741824 2 1 524288 256441 ep688 ep69 ep688 ep688 ep70 ep688 368037 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 835552597) qz289 0 1 ep688 ep69 ep688 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 835552597) qz290 0 1 ep688 ep70 ep688 rfl rfl rfl rfl) rfl rfl

noncomputable def ep690 := @Enclosure.Real.IsNear.sin_image qz176 qz440 Bool.false 132175931 524288 191 262144 Bool.false 368037 524288 1 128095 (@Enclosure.Real.IsNear.recentre' qz176 Bool.false 227076521441661608263 900719925474099200 3723800001431000483 5123800000000000000000 132175931 524288 191 262144 (ep682 rfl) rfl) (Enclosure.sfrac_false_div 132175931 524288) (BSN.sin_reduce0 qz440 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 58796786984656339730432) qz33) 226375608064910080 72057594037927936 Bool.false 368037 524288 40 1000000000000000 256190 128095 (BSN.sin_reduce_arg_pos_rat_q0 132175931 524288 226375608064910080 72057594037927936 40 58796786984656339730432 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 368037 524288 58796786984656339730432 75557863725914323419136 835552597 1073741824 256441 256190 (ep689 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep691 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz66 (Real.cos qz176)) (@HMul.hMul Real Real Real qz0 qz66 (@Neg.neg Real Real.instNeg (Real.sin qz176))) Bool.false 50547125287 274877906944 6742866165731 35210485489991680 Bool.true 49821536727 274877906944 6742179576531 35210485489991680 (@Enclosure.Real.IsNear.mulLit_ff qz66 (Real.cos qz176) 135371 524288 1 524288 373397 524288 24728289 33579335680 50547125287 274877906944 6742866165731 35210485489991680 qz350 (@Enclosure.Real.IsNear.recentre' (Real.cos qz176) Bool.false 373397 524288 24728289 33579335680 373397 524288 24728289 33579335680 (ep687 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz66 (@Neg.neg Real Real.instNeg (Real.sin qz176)) 135371 524288 1 524288 368037 524288 24728289 33579335680 49821536727 274877906944 6742179576531 35210485489991680 qz350 (@Enclosure.Real.IsNear.neg (Real.sin qz176) Bool.false 368037 524288 24728289 33579335680 (@Enclosure.Real.IsNear.recentre' (Real.sin qz176) Bool.false 368037 524288 24728289 33579335680 368037 524288 24728289 33579335680 (ep690 rfl rfl) rfl)) rfl)

noncomputable def ep692 := @ep612 50547125287 274877906944 6742866165731 35210485489991680 Bool.true 49821536727 274877906944 6742179576531 35210485489991680 Bool.false 17522358336581418352640 254983873115 274877906944 141023875202299 35210485489991680 Bool.true 9623262394424779341824 17504612323 137438953472 35272657497531 8802621372497920 (ep613 (BSN.head_sum_c_succ qz148 14 15 rfl rfl) (ep680 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep681 ep691) rfl rfl

noncomputable abbrev qz177 := (@HMul.hMul Real Real Real qz267 qz424 qz352)

noncomputable def ep693 := @Enclosure.Complex.IsNear.of_eq qz163 (Complex.mk (@HMul.hMul Real Real Real qz0 qz69 (Real.cos qz177)) (@HMul.hMul Real Real Real qz0 qz69 (@Neg.neg Real Real.instNeg (Real.sin qz177)))) Bool.false 60189244981 274877906944 6541195224661 35210485489991680 Bool.true 33159259077 274877906944 6514778961381 35210485489991680 (BSN.cpow_neg_s_mk qz153 93095 1000 16 qz154 rfl)

noncomputable def ep694 := @Enclosure.Real.IsNear.mulLit_ff qz153 qz352 93095 1000 0 1 3121657384082679 1125899906842624 50000000025619 6404750000000000000 58122138834235400301 225179981368524800 930950000477000161 1280950000000000000000 qz155 (BSN.isNear_log_sfrac 16 1 3121657384082679 1125899906842624 50000000025619 6404750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz353) Bool.false 26186360105375033720832 9444732965739290427392 1000000000512380 128095000000000000000 3121657384082679 1125899906842624 50000000025619 6404750000000000000 (BSN.log_rat_reduce_isNear 16 1 4 32 32 0 262144 24973259072661432 36028797018963968 128095 1000000000000000 rfl rfl rfl rfl (ep263 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep695 := nat_lit 85459803912340355087643150722909761

noncomputable def ep696 := BSN.cos_dyadic_bound_f 540680209 1073741824 2 1 524288 256441 ep695 ep57 ep695 ep695 ep58 ep695 459211 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 540680209) qz283 0 1 ep695 ep57 ep695 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 540680209) qz284 0 1 ep695 ep58 ep695 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz441 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 135326149) qz31)

noncomputable def ep697 := @Enclosure.Real.IsNear.cos_image qz177 qz441 Bool.false 135326149 524288 191 262144 Bool.false 459211 524288 1 128095 (@Enclosure.Real.IsNear.recentre' qz177 Bool.false 58122138834235400301 225179981368524800 930950000477000161 1280950000000000000000 135326149 524288 191 262144 (ep694 rfl) rfl) (Enclosure.sfrac_false_div 135326149 524288) (BSN.cos_reduce0 qz441 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 38046987330060569018368) qz33) 226375608064910080 72057594037927936 Bool.false 459211 524288 41 1000000000000000 256190 128095 (BSN.sin_reduce_arg_pos_rat_q0 135326149 524288 226375608064910080 72057594037927936 41 38046987330060569018368 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 459211 524288 38046987330060569018368 75557863725914323419136 540680209 1073741824 256441 256190 (ep696 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep698 := BSN.sin_dyadic_bound_f 540680209 1073741824 2 1 524288 256441 ep695 ep69 ep695 ep695 ep70 ep695 252987 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 540680209) qz289 0 1 ep695 ep69 ep695 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 540680209) qz290 0 1 ep695 ep70 ep695 rfl rfl rfl rfl) rfl rfl

noncomputable def ep699 := @Enclosure.Real.IsNear.sin_image qz177 qz441 Bool.false 135326149 524288 191 262144 Bool.false 252987 524288 1 128095 (@Enclosure.Real.IsNear.recentre' qz177 Bool.false 58122138834235400301 225179981368524800 930950000477000161 1280950000000000000000 135326149 524288 191 262144 (ep694 rfl) rfl) (Enclosure.sfrac_false_div 135326149 524288) (BSN.sin_reduce0 qz441 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 38046987330060569018368) qz33) 226375608064910080 72057594037927936 Bool.false 252987 524288 41 1000000000000000 256190 128095 (BSN.sin_reduce_arg_pos_rat_q0 135326149 524288 226375608064910080 72057594037927936 41 38046987330060569018368 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 252987 524288 38046987330060569018368 75557863725914323419136 540680209 1073741824 256441 256190 (ep698 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep700 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz69 (Real.cos qz177)) (@HMul.hMul Real Real Real qz0 qz69 (@Neg.neg Real Real.instNeg (Real.sin qz177))) Bool.false 60189244981 274877906944 6541195224661 35210485489991680 Bool.true 33159259077 274877906944 6514778961381 35210485489991680 (@Enclosure.Real.IsNear.mulLit_ff qz69 (Real.cos qz177) 131071 524288 1 524288 459211 524288 24728289 33579335680 60189244981 274877906944 6541195224661 35210485489991680 qz356 (@Enclosure.Real.IsNear.recentre' (Real.cos qz177) Bool.false 459211 524288 24728289 33579335680 459211 524288 24728289 33579335680 (ep697 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz69 (@Neg.neg Real Real.instNeg (Real.sin qz177)) 131071 524288 1 524288 252987 524288 24728289 33579335680 33159259077 274877906944 6514778961381 35210485489991680 qz356 (@Enclosure.Real.IsNear.neg (Real.sin qz177) Bool.false 252987 524288 24728289 33579335680 (@Enclosure.Real.IsNear.recentre' (Real.sin qz177) Bool.false 252987 524288 24728289 33579335680 252987 524288 24728289 33579335680 (ep699 rfl rfl) rfl)) rfl)

noncomputable def ep701 := @ep610 60189244981 274877906944 6541195224661 35210485489991680 Bool.true 33159259077 274877906944 6514778961381 35210485489991680 Bool.false 86634127027242610458624 19698319881 17179869184 1844563380337 440131068624896 Bool.true 9369005062662186336256 68168483723 274877906944 29521081790301 7042097097998336 (ep611 (BSN.head_sum_c_succ qz148 15 16 rfl rfl) (ep692 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep693 ep700) rfl rfl

theorem EMRow26.d12 : Enclosure.Complex.IsNear qz162 Bool.false 19698319881 17179869184 1844563380337 440131068624896 Bool.true 68168483723 274877906944 29521081790301 7042097097998336 := ep609 (BSN.head_sum_c_succ qz148 16 17 rfl rfl) (ep701 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable def ep702 := nat_lit 16377612022746145453399739137

noncomputable def ep703 := nat_lit 11865843011540707008158105600

noncomputable def ep704 := nat_lit 39163157723087870637786782309360191

noncomputable def ep705 := nat_lit 7329831766300491021966364457618636800

noncomputable abbrev qz522 := (@HAdd.hAdd Complex Complex Complex qz528 (@HAdd.hAdd Complex Complex Complex qz528 qz531 (@HMul.hMul Complex Complex Complex qz530 Complex.I (@HDiv.hDiv Complex Complex Complex qz532 (↑qz535) (2 : Complex)))) (@Nat.cast Complex Complex.instNatCast 2))

noncomputable abbrev qz442 := qz522

noncomputable abbrev qz178 := (Complex.Stirling.logGammaStirling 1 qz442)

noncomputable abbrev qz523 := (@HAdd.hAdd Complex Complex Complex qz528 qz531 (@HMul.hMul Complex Complex Complex qz530 Complex.I (@HDiv.hDiv Complex Complex Complex qz532 (↑qz535) (2 : Complex))))

noncomputable abbrev qz443 := qz523

noncomputable abbrev qz179 := qz443

noncomputable abbrev qz180 := (@HMul.hMul Real Real Real qz267 (@HDiv.hDiv Real Real Real qz270 qz424 (2 : Real)) (Real.log Real.pi))

noncomputable def ep706 := Complex.re (@HMul.hMul Complex Complex Complex qz71 (Complex.exp (@HMul.hMul Complex Complex Complex qz71 Complex.I ↑(@HSub.hSub Real Real Real qz361 (Complex.im (@HSub.hSub Complex Complex Complex qz72 qz178 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz179 (@Nat.cast Complex Complex.instNatCast j))))) qz180))) (zetaApproximant qz148 1 19))

noncomputable def ep707 := @Enclosure.Real.IsNear.of_eq ep706 (@HSub.hSub Real Real Real qz361 (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz361 (Complex.im (@HSub.hSub Complex Complex Complex qz72 qz178 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz179 (@Nat.cast Complex Complex.instNatCast j))))) qz180)) (Complex.re (zetaApproximant qz148 1 19))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz361 (Complex.im (@HSub.hSub Complex Complex Complex qz72 qz178 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz179 (@Nat.cast Complex Complex.instNatCast j))))) qz180)) (Complex.im (zetaApproximant qz148 1 19))))

noncomputable def ep708 := nat_lit 104817751429950410275759537213

noncomputable def ep709 := @Enclosure.Real.IsNear.subLit_tt_n (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz361 (Complex.im (@HSub.hSub Complex Complex Complex qz72 qz178 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz179 (@Nat.cast Complex Complex.instNatCast j))))) qz180)) (Complex.re (zetaApproximant qz148 1 19))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz361 (Complex.im (@HSub.hSub Complex Complex Complex qz72 qz178 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz179 (@Nat.cast Complex Complex.instNatCast j))))) qz180)) (Complex.im (zetaApproximant qz148 1 19))) ep708

noncomputable def ep710 := nat_lit 75941395273860524852211875840

noncomputable def ep711 := nat_lit 389850437231371313448432046164221983

noncomputable def ep712 := nat_lit 73298317663004910219663644576186368000

noncomputable def ep713 := nat_lit 5172421875396870006033681

noncomputable def ep714 := nat_lit 379706976369302624261059379200

noncomputable def ep715 := nat_lit 1781139999507392929435776929379927

noncomputable def ep716 := nat_lit 39799638664361454111335630695436019887789017065901848002560

noncomputable def ep717 := @Enclosure.Real.IsNear.mulLit_tf (Real.cos (@HSub.hSub Real Real Real qz361 (Complex.im (@HSub.hSub Complex Complex Complex qz72 qz178 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz179 (@Nat.cast Complex Complex.instNatCast j))))) qz180)) (Complex.re (zetaApproximant qz148 1 19)) 524287 524288 31651373

noncomputable def ep718 := nat_lit 15277669117451418064754903

noncomputable def ep719 := nat_lit 3274260025340303734367846400

noncomputable def ep720 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HSub.hSub Real Real Real qz361 (Complex.im (@HSub.hSub Complex Complex Complex qz72 qz178 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz179 (@Nat.cast Complex Complex.instNatCast j))))) qz180)) Bool.true 524287 524288 31651373

noncomputable abbrev qz444 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 41177647) qz31)

noncomputable def ep721 := @Enclosure.Real.IsNear.cos_image (@HSub.hSub Real Real Real qz361 (Complex.im (@HSub.hSub Complex Complex Complex qz72 qz178 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz179 (@Nat.cast Complex Complex.instNatCast j))))) qz180) qz444 Bool.false 41177647 524288 243

noncomputable def ep722 := nat_lit 3712109195367994704519661

noncomputable def ep723 := nat_lit 8059040563200000000000000000

noncomputable def ep724 := @Enclosure.Real.IsNear.recentre' (@HSub.hSub Real Real Real qz361 (Complex.im (@HSub.hSub Complex Complex Complex qz72 qz178 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz179 (@Nat.cast Complex Complex.instNatCast j))))) qz180) Bool.false 169782383406241126697 2161727821137838080 ep722 ep723

noncomputable def ep725 := @Enclosure.Real.IsNear.subLit_ff_p (Complex.im (@HSub.hSub Complex Complex Complex qz72 qz178 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz179 (@Nat.cast Complex Complex.instNatCast j))))) qz180 1424842704317724229069 10808639105689190400 850108229367994704519661 ep723 1396815999 26214400

noncomputable def ep726 := nat_lit 22253716557822836958429184000

noncomputable def ep727 := nat_lit 671586713600000000000000000

noncomputable def ep728 := @Enclosure.Complex.IsNear.im_isNear (@HSub.hSub Complex Complex Complex qz72 qz178 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz179 (@Nat.cast Complex Complex.instNatCast j)))) Bool.true 65894719367410873753 900719925474099200 129498637066719366071773 ep727 Bool.false 1424842704317724229069 10808639105689190400

noncomputable def ep729 := @Enclosure.Complex.IsNear.subLitP qz178 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz179 (@Nat.cast Complex Complex.instNatCast j))) Bool.true 58976000807318784753 900719925474099200 126877197059331912222173 ep727 Bool.false 1458450843938839429069 10808639105689190400 787193669359935663956461

noncomputable def ep730 := nat_lit 296763433588755016936503149212991488

noncomputable def ep731 := nat_lit 401057567014179540631431907077259264

noncomputable abbrev qz445 := (@HSub.hSub Complex Complex Complex qz511 qz522 qz514)

noncomputable abbrev qz446 := (Complex.log qz522)

noncomputable abbrev qz181 := (@HSub.hSub Complex Complex Complex qz358 (@HMul.hMul Complex Complex Complex qz357 qz445 qz446) qz442)

noncomputable abbrev qz182 := qz442

noncomputable def ep732 := @Enclosure.Complex.IsNear.of_eq qz178 (@HAdd.hAdd Complex Complex Complex qz4 (@HAdd.hAdd Complex Complex Complex qz4 qz181 qz77) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz79 2 k))) (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz71 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz80 qz182 (@HSub.hSub Int Int Int qz370 qz82 (@HMul.hMul Int Int Int qz371 qz83 (@Nat.cast Int instNatCastInt k)))))) Bool.true 58976000807318784753

noncomputable def ep733 := @Enclosure.Complex.IsNear.addLitP (@HAdd.hAdd Complex Complex Complex qz4 qz181 qz77) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz79 2 k))) (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz71 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz80 qz182 (@HSub.hSub Int Int Int qz370 qz82 (@HMul.hMul Int Int Int qz371 qz83 (@Nat.cast Int instNatCastInt k))))) Bool.true 58976078572467456753 900719925474099200

noncomputable def ep734 := nat_lit 2026399957730430223684787503104

noncomputable def ep735 := nat_lit 1002239788406546427527466676387840

noncomputable def ep736 := @ep733 3871982984072703961 20495200000000000000000 Bool.false 486156716465404805103 3602879701896396800 2001900005264935071 20495200000000000000000 Bool.false 2966505 34359738368 3 34359738368 Bool.true 3682223773 2061584302080 18619 10307921510400 Bool.true ep734 58976000807318784753 900719925474099200 126877197059331912222173 ep727 Bool.false ep735

noncomputable def ep737 := @Enclosure.Complex.IsNear.addLitP qz181 qz77 Bool.true 59803784053909555953 900719925474099200 3793800000674266461 20495200000000000000000

noncomputable def ep738 := nat_lit 7730112570650454491529216

noncomputable def ep739 := @ep737 Bool.false 486156716465404805103 3602879701896396800 2001900005264935071 20495200000000000000000 Bool.false 120447 131072 1 262144 Bool.false 0 1 0 1 Bool.true ep738 58976078572467456753 900719925474099200 3871982984072703961 20495200000000000000000 Bool.false 486156716465404805103 486156716465404805103 3602879701896396800

noncomputable abbrev qz183 := (@HMul.hMul Complex Complex Complex qz357 qz445 qz446)

noncomputable def ep740 := @Enclosure.Complex.IsNear.subLitP qz183 qz182 Bool.true 57777164221592832753 900719925474099200 3793800000674266461 20495200000000000000000 Bool.false 653861759389427335151

noncomputable def ep741 := nat_lit 1944626865861619220412000

noncomputable def ep742 := @ep740 3602879701896396800 2001900005264935071 20495200000000000000000 Bool.false 9000 4000 0 1 Bool.false 186190 4000 0 1 Bool.true 239215136215638223812000 59803784053909555953 900719925474099200 3793800000674266461 20495200000000000000000 Bool.false ep741 486156716465404805103 3602879701896396800 2001900005264935071 20495200000000000000000

noncomputable abbrev qz184 := qz445

noncomputable abbrev qz185 := qz446

noncomputable def ep743 := @Enclosure.Complex.IsNear.mul qz184 qz185 Bool.true 57777164221592832753 900719925474099200 3793800000674266461 20495200000000000000000 Bool.false 653861759389427335151 3602879701896396800 2001900005264935071

noncomputable abbrev qz186 := (Complex.re qz445)

noncomputable abbrev qz187 := (Complex.re qz446)

noncomputable abbrev qz188 := (Complex.im qz445)

noncomputable abbrev qz189 := (Complex.im qz446)

noncomputable def ep744 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 qz186 qz187) (@HMul.hMul Real Real Real qz0 qz188 qz189) 242216902643005003 36028797018963968 700000001972663 204952000000000000000 15958146696916989457 225179981368524800

noncomputable def ep745 := nat_lit 520410430517778870335454882589310976

noncomputable def ep746 := @Enclosure.Real.IsNear.mulLit_ff qz186 qz187 7000 4000 0 1 34602414663286429 9007199254740992 100000000281809 51238000000000000000

noncomputable def ep747 := @Enclosure.Complex.IsNear.re_isNear qz184 Bool.false 7000 4000 0 1 Bool.false 186190 4000 0 1

noncomputable abbrev qz447 := (Enclosure.sfrac Bool.false 186190 4000)

noncomputable abbrev qz190 := qz447

noncomputable def ep748 := @Enclosure.Complex.IsNear.of_eq qz184 (Complex.mk (Enclosure.sfrac Bool.false 7000 4000) qz190) Bool.false 7000 4000 0 1 Bool.false 186190 4000 0

noncomputable abbrev qz448 := (Complex.log (Complex.mk qz92 qz190))

noncomputable def ep749 := @Enclosure.Complex.IsNear.of_eq qz185 qz448 Bool.false 34602414663286429 9007199254740992 100000000281809 51238000000000000000 Bool.false 857089354794403 562949953421312 200000000025619 51238000000000000000

noncomputable def ep750 := BSN.log_dyadic_bound 1979716100 67515716100 2 1 13675115761487397630000 524288 256190 3919275836599210000 3919275836599210000 30755 69495432200 65536000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 1979716100) (BSN.artanhQ 67515716100) 0 1 3919275836599210000 13675115761487397630000 3919275836599210000 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz449 := (Real.log (Enclosure.sfrac Bool.false 34747716100 16000000))

noncomputable def ep751 := @Enclosure.Real.IsNear.mulLit_ff qz93 qz449 1 2 0 1 34602414663286429 4503599627370496 100000000281809 25619000000000000000 34602414663286429 9007199254740992 100000000281809 51238000000000000000 qz376 (BSN.isNear_log_sfrac 34747716100 16000000 34602414663286429 4503599627370496 100000000281809 25619000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 34747716100) qz377)) Bool.false 145133046231880922300416 18889465931478580854784 1000000002818090 256190000000000000000 34602414663286429 4503599627370496 100000000281809 25619000000000000000 (BSN.log_rat_reduce_isNear 34747716100 16000000 11 69495432200 65536000000 30755 524288 24973259072661432 36028797018963968 256190 1000000000000000 rfl rfl rfl rfl (ep750 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep752 := BSN.arctan_dyadic_bound_f 9000 186190 1 0 524288 256190 0 1 1 0 1 1 25323 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 9000) (BSN.arctanEvenQ 186190) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 9000) (BSN.arctanOddQ 186190) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz450 := (Real.arctan (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 9000) (@Nat.cast Real Real.instNatCast 186190)))

noncomputable def ep753 := @Enclosure.Real.IsNear.subLit_ff_p qz94 qz450 884279719003555 562949953421312 1 2000000000000000 25323 524288 1 256190 449361663646447960064 857089354794403 562949953421312 200000000025619 51238000000000000000 qz95 (ep752 rfl) rfl rfl

noncomputable abbrev qz451 := (Complex.mk qz92 qz190)

noncomputable abbrev qz452 := (Real.arctan (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 186190) (@Nat.cast Real Real.instNatCast 9000)))

noncomputable def ep754 := @Enclosure.Complex.IsNear.re_isNear qz185 Bool.false 34602414663286429 9007199254740992 100000000281809 51238000000000000000 Bool.false 857089354794403 562949953421312 200000000025619 51238000000000000000 (ep749 (@congrArg Complex Complex qz182 qz451 Complex.log (BSN.w_shift_mk qz153 Bool.false 93095 1000 2 qz154 rfl)) (@Enclosure.Complex.IsNear.of_parts qz448 Bool.false 34602414663286429 9007199254740992 100000000281809 51238000000000000000 Bool.false 857089354794403 562949953421312 200000000025619 51238000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz448) (@HMul.hMul Real Real Real qz0 qz93 qz449) Bool.false 34602414663286429 9007199254740992 100000000281809 51238000000000000000 (Enclosure.clog_re_eq 9000 186190 4000 34747716100 16000000 rfl rfl rfl) (ep751 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz448) qz452 Bool.false 857089354794403 562949953421312 200000000025619 51238000000000000000 (Enclosure.clog_im_eq 9000 186190 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz452 (@HSub.hSub Real Real Real qz361 qz94 qz450) Bool.false 857089354794403 562949953421312 200000000025619 51238000000000000000 (BSN.arctan_recip 186190 9000 rfl rfl) ep753))))

noncomputable def ep755 := @Enclosure.Real.IsNear.mulLit_ff qz188 qz189 186190 4000 0 1 857089354794403 562949953421312 200000000025619 51238000000000000000

noncomputable def ep756 := @Enclosure.Complex.IsNear.im_isNear qz184 Bool.false 7000 4000 0 1 Bool.false 186190 4000 0 1

noncomputable def ep757 := @Enclosure.Complex.IsNear.im_isNear qz185 Bool.false 34602414663286429 9007199254740992 100000000281809 51238000000000000000 Bool.false 857089354794403 562949953421312 200000000025619 51238000000000000000 (ep749 (@congrArg Complex Complex qz182 qz451 Complex.log (BSN.w_shift_mk qz153 Bool.false 93095 1000 2 qz154 rfl)) (@Enclosure.Complex.IsNear.of_parts qz448 Bool.false 34602414663286429 9007199254740992 100000000281809 51238000000000000000 Bool.false 857089354794403 562949953421312 200000000025619 51238000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz448) (@HMul.hMul Real Real Real qz0 qz93 qz449) Bool.false 34602414663286429 9007199254740992 100000000281809 51238000000000000000 (Enclosure.clog_re_eq 9000 186190 4000 34747716100 16000000 rfl rfl rfl) (ep751 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz448) qz452 Bool.false 857089354794403 562949953421312 200000000025619 51238000000000000000 (Enclosure.clog_im_eq 9000 186190 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz452 (@HSub.hSub Real Real Real qz361 qz94 qz450) Bool.false 857089354794403 562949953421312 200000000025619 51238000000000000000 (BSN.arctan_recip 186190 9000 rfl rfl) ep753))))

noncomputable abbrev qz453 := (Enclosure.Real.IsNear.const Bool.false 186190 4000)

noncomputable abbrev qz191 := (@ep748 1 (BSN.w_sub_half_mk qz424 Bool.false 93095 1000 2 qz425 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7000 4000) qz447 Bool.false 7000 4000 0 1 Bool.false 186190 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 7000 4000) qz453))

noncomputable def ep758 := @ep744 3723800000477000161 20495200000000000000000 ep745 57777164221592832753 900719925474099200 3793800000674266461 20495200000000000000000 (@ep746 242216902643005003 36028797018963968 700000001972663 204952000000000000000 (ep747 qz191) ep754 rfl) (@ep755 15958146696916989457 225179981368524800 3723800000477000161 20495200000000000000000 (ep756 qz191) ep757 rfl) rfl

noncomputable def ep759 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz186 qz189) (@HMul.hMul Real Real Real qz0 qz188 qz187) 5999625483560821 2251799813685248 1400000000179333 204952000000000000000 644262358615730021551 3602879701896396800

noncomputable def ep760 := nat_lit 1472365787969020930368196429320552448

noncomputable def ep761 := @Enclosure.Real.IsNear.mulLit_ff qz186 qz189 7000 4000 0 1 857089354794403 562949953421312 200000000025619 51238000000000000000

noncomputable def ep762 := @Enclosure.Real.IsNear.mulLit_ff qz188 qz187 186190 4000 0 1 34602414663286429 9007199254740992 100000000281809 51238000000000000000

noncomputable def ep763 := @ep759 1861900005247001771 20495200000000000000000 ep760 653861759389427335151 3602879701896396800 2001900005264935071 20495200000000000000000 (@ep761 5999625483560821 2251799813685248 1400000000179333 204952000000000000000 (ep747 qz191) ep757 rfl) (@ep762 644262358615730021551 3602879701896396800 1861900005247001771 20495200000000000000000 (ep756 qz191) ep754 rfl) rfl

noncomputable def ep764 := @Enclosure.Complex.IsNear.of_eq qz182 qz451 Bool.false 9000 4000 0 1 Bool.false 186190 4000 0 1 (BSN.w_shift_mk qz153 Bool.false 93095 1000 2 qz154 rfl)

noncomputable abbrev qz454 := (ep764 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 9000 4000) (Enclosure.sfrac Bool.false 186190 4000) Bool.false 9000 4000 0 1 Bool.false 186190 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 9000 4000) (Enclosure.Real.IsNear.const Bool.false 186190 4000)))

noncomputable abbrev qz192 := qz454

noncomputable def ep765 := ep742 (@ep743 20495200000000000000000 (ep758 rfl) (ep763 rfl)) qz192 rfl rfl rfl rfl rfl rfl

noncomputable def ep766 := @ep739 2001900005264935071 20495200000000000000000 (ep765 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@Enclosure.Complex.IsNear.mul qz98 (↑qz2) Bool.false 120447 131072 1 262144 Bool.false 0 1 0 1 (@ep338 131072 1 262144 (ep340 rfl) (ep342 rfl) rfl rfl) (@ep343 1 0 1 (ep345 rfl) (ep347 rfl) rfl rfl))

noncomputable abbrev qz455 := (@HPow.hPow Complex Int Complex qz516 qz522 (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) (@OfNat.ofNat Int 1 (@instOfNat 1)) (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (@OfNat.ofNat Int 2 (@instOfNat 2)) (@Nat.cast Int instNatCastInt 1))))

noncomputable abbrev qz193 := qz455

noncomputable def ep767 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz79 2 k))) (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz71 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz80 qz182 (@HSub.hSub Int Int Int qz370 qz82 (@HMul.hMul Int Int Int qz371 qz83 (@Nat.cast Int instNatCastInt k))))) (@HAdd.hAdd Complex Complex Complex qz4 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz79 2 k))) (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz71 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz80 qz182 (@HSub.hSub Int Int Int qz370 qz82 (@HMul.hMul Int Int Int qz371 qz83 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 (@Rat.cast Complex Complex.instRatCast (bernoulli qz100)) qz101) qz193)) Bool.false 2966505 34359738368 3 34359738368

noncomputable def ep768 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz79 2 k))) (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz71 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz80 qz182 (@HSub.hSub Int Int Int qz370 qz82 (@HMul.hMul Int Int Int qz371 qz83 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 (@Rat.cast Complex Complex.instRatCast (bernoulli qz100)) qz101) qz193) Bool.false 0 1 0 1 Bool.false

noncomputable def ep769 := @ep768 0 1 0 1 Bool.false 2966505 34359738368 3 34359738368 Bool.true 3682223773 2061584302080 18619 10307921510400 Bool.false 2966505 2966505 34359738368 3 34359738368 Bool.true 3682223773 3682223773 2061584302080 18619

noncomputable def ep770 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz79 2 k))) (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz71 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz80 qz182 (@HSub.hSub Int Int Int qz370 qz82 (@HMul.hMul Int Int Int qz371 qz83 (@Nat.cast Int instNatCastInt k))))) (Complex.mk qz13 qz13) Bool.false 0 1 0 1 Bool.false

noncomputable def ep771 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz78 (@Rat.cast Complex Complex.instRatCast (bernoulli qz100)) qz101) qz193 Bool.false 2966505 34359738368 3 34359738368 Bool.true 3682223773 2061584302080 18619 10307921510400

noncomputable abbrev qz194 := (Complex.re qz455)

noncomputable abbrev qz195 := (Complex.im qz455)

noncomputable def ep772 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz78 (@Rat.cast Complex Complex.instRatCast (bernoulli qz100)) qz101)) qz194) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz78 (@Rat.cast Complex Complex.instRatCast (bernoulli qz100)) qz101)) qz195) 2966505 34359738368 3 34359738368 0 1 0

noncomputable def ep773 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz78 (@Rat.cast Complex Complex.instRatCast (bernoulli qz100)) qz101)) qz194 1 12 0 1 8899515 8589934592 9 8589934592 2966505

noncomputable def ep774 := @Enclosure.Complex.IsNear.re_isNear qz193 Bool.false 8899515 8589934592 9 8589934592 Bool.true 3682223773 171798691840 18619 858993459200

noncomputable abbrev qz456 := (@HPow.hPow Complex Nat Complex qz517 qz522 1)

noncomputable abbrev qz196 := (@Inv.inv Complex Complex.instInv qz456)

noncomputable def ep775 := @Enclosure.Complex.IsNear.of_eq qz193 qz196 Bool.false 8899515 8589934592 9 8589934592 Bool.true 3682223773 171798691840 18619

noncomputable def ep776 := @Enclosure.Complex.IsNear.of_parts qz196 Bool.false 8899515 8589934592 9 8589934592 Bool.true 3682223773 171798691840 18619

noncomputable abbrev qz197 := (Complex.re qz456)

noncomputable abbrev qz198 := qz456

noncomputable def ep777 := @Enclosure.Real.IsNear.mulLit_ff qz197 (@Inv.inv Real Real.instInv (@DFunLike.coe qz107 Complex (fun (x : Complex) => Real) qz108 Complex.normSq qz198)) 9000 4000 0 1 988835 2147483648 1 2147483648

noncomputable def ep778 := @Enclosure.Complex.IsNear.re_isNear qz198 Bool.false 9000 4000 0 1 Bool.false 186190 4000 0 1

noncomputable def ep779 := @Enclosure.Complex.IsNear.of_eq qz198 qz182 Bool.false 9000 4000 0 1 Bool.false 186190 4000 0

noncomputable def ep780 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (@DFunLike.coe qz107 Complex (fun (x : Complex) => Real) qz108 Complex.normSq qz198)) Bool.false 988835 2147483648 1 2147483648 988835 2147483648 1

noncomputable abbrev qz199 := (Complex.im qz456)

noncomputable def ep781 := @Enclosure.Real.IsNear.of_eq (@DFunLike.coe qz107 Complex (fun (x : Complex) => Real) qz108 Complex.normSq qz198) (@HAdd.hAdd Real Real Real qz386 (@HMul.hMul Real Real Real qz0 qz197 qz197) (@HMul.hMul Real Real Real qz0 qz199 qz199)) Bool.false 347477161 160000 0 1

noncomputable def ep782 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz197 qz197) (@HMul.hMul Real Real Real qz0 qz199 qz199) 81 16 0 1 346667161 160000

noncomputable def ep783 := @Enclosure.Real.IsNear.mulLit_ff qz197 qz197 9000 4000 0 1 9000 4000 0 1

noncomputable def ep784 := @Enclosure.Real.IsNear.mulLit_ff qz199 qz199 186190 4000 0 1 186190 4000 0 1

noncomputable def ep785 := @Enclosure.Complex.IsNear.im_isNear qz198 Bool.false 9000 4000 0 1 Bool.false 186190 4000 0 1

noncomputable abbrev qz200 := (ep778 (@ep779 1 (BSN.pow_one_c qz442) qz454))

noncomputable abbrev qz201 := (ep785 (@ep779 1 (BSN.pow_one_c qz442) qz454))

noncomputable def ep786 := @ep782 0 1 5559634576 347477161 160000 0 1 (@ep783 81 16 0 1 qz200 qz200 rfl) (@ep784 346667161 160000 0 1 qz201 qz201 rfl)

noncomputable def ep787 := @Enclosure.Real.IsNear.inv_image (@DFunLike.coe qz107 Complex (fun (x : Complex) => Real) qz108 Complex.normSq qz198) 347477161 160000 0 1 494417 494418 1073741824 (ep781 (Enclosure.Complex.normSq_eq_mul_add_mul qz198) (ep786 rfl rfl)) rfl

noncomputable def ep788 := @Enclosure.Real.IsNear.of_eq (Complex.re qz196) (@HMul.hMul Real Real Real qz0 qz197 (@Inv.inv Real Real.instInv (@DFunLike.coe qz107 Complex (fun (x : Complex) => Real) qz108 Complex.normSq qz198))) Bool.false 8899515 8589934592 9 8589934592 (Enclosure.Complex.inv_re_eq_mul qz198) (@ep777 8899515 8589934592 9 8589934592 qz200 (@ep780 2147483648 (ep787 rfl rfl rfl rfl rfl) rfl) rfl)

noncomputable def ep789 := @Enclosure.Real.IsNear.of_eq (Complex.im qz196) (@HMul.hMul Real Real Real qz0 (@Neg.neg Real Real.instNeg qz199) (@Inv.inv Real Real.instInv (@DFunLike.coe qz107 Complex (fun (x : Complex) => Real) qz108 Complex.normSq qz198))) Bool.true 3682223773 171798691840 18619 858993459200 (Enclosure.Complex.inv_im_eq_mul qz198)

noncomputable def ep790 := @Enclosure.Real.IsNear.mulLit_tf (@Neg.neg Real Real.instNeg qz199) (@Inv.inv Real Real.instInv (@DFunLike.coe qz107 Complex (fun (x : Complex) => Real) qz108 Complex.normSq qz198)) 186190 4000 0 1 988835 2147483648 1

noncomputable def ep791 := @ep790 2147483648 3682223773 171798691840 18619 858993459200 (@Enclosure.Real.IsNear.neg qz199 Bool.false 186190 4000 0 1 qz201) (@ep780 2147483648 (ep787 rfl rfl rfl rfl rfl) rfl) rfl

noncomputable def ep792 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz78 (@Rat.cast Complex Complex.instRatCast (bernoulli qz100)) qz101)) qz195 0 1 0 1 3682223773 171798691840 18619 858993459200 0

noncomputable def ep793 := @Enclosure.Complex.IsNear.im_isNear qz193 Bool.false 8899515 8589934592 9 8589934592 Bool.true 3682223773 171798691840 18619 858993459200

noncomputable abbrev qz202 := (@ep775 858993459200 (BSN.zpow_one_sub_two_mul qz442 1 1 rfl rfl) (@ep776 858993459200 ep788 (ep789 ep791)))

noncomputable def ep794 := @ep772 1 2966505 2966505 34359738368 3 34359738368 (@ep773 34359738368 3 34359738368 ep357 (ep774 qz202) rfl) (@ep792 1 0 1 ep377 (ep793 qz202) rfl) rfl

noncomputable def ep795 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz78 (@Rat.cast Complex Complex.instRatCast (bernoulli qz100)) qz101)) qz195) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz78 (@Rat.cast Complex Complex.instRatCast (bernoulli qz100)) qz101)) qz194) 3682223773 2061584302080 18619 10307921510400 0 1 0

noncomputable def ep796 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HDiv.hDiv Complex Complex Complex qz78 (@Rat.cast Complex Complex.instRatCast (bernoulli qz100)) qz101)) qz195 1 12 0 1 3682223773 171798691840 18619 858993459200 3682223773

noncomputable def ep797 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz78 (@Rat.cast Complex Complex.instRatCast (bernoulli qz100)) qz101)) qz194 0 1 0 1 8899515 8589934592 9 8589934592 0

noncomputable def ep798 := @ep795 1 3682223773 3682223773 2061584302080 18619 10307921510400 (@ep796 2061584302080 18619 10307921510400 ep357 (ep793 qz202) rfl) (@ep797 1 0 1 ep377 (ep774 qz202) rfl) rfl

noncomputable def ep799 := @ep769 10307921510400 (@ep770 0 1 0 1 (BSN.stirling_sum_base qz182) qz114) (ep771 (ep794 rfl) (ep798 rfl)) rfl rfl rfl rfl rfl

noncomputable def ep800 := @ep736 1458450843938839429069 10808639105689190400 787193669359935663956461 ep723 (ep766 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep767 Bool.true 3682223773 2061584302080 18619 10307921510400 (BSN.stirling_sum_succ qz182 0 1 rfl) (ep799 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl

noncomputable def ep801 := @Enclosure.Complex.IsNear.of_eq (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz179 (@Nat.cast Complex Complex.instNatCast j))) (BSN.logSumC qz153 2) Bool.false 34593592800460445 4503599627370496 100000000281809 25619000000000000000 Bool.false 875211969299875 281474976710656

noncomputable abbrev qz203 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz273 qz443 qz382))

noncomputable def ep802 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz153 2) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.logSumC qz153 1) qz203) Bool.false 34593592800460445 4503599627370496 100000000281809 25619000000000000000 Bool.false 875211969299875 281474976710656 200000000025619 25619000000000000000

noncomputable def ep803 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz153 1) qz203 Bool.false 34592038022299293 9007199254740992 100000000281809 51238000000000000000 Bool.false 881257135768995 562949953421312 200000000025619 51238000000000000000 Bool.false

noncomputable def ep804 := nat_lit 623182766582241333153813632122880

noncomputable def ep805 := nat_lit 985401074702278758731087872000

noncomputable abbrev qz204 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz273 qz443 (@Nat.cast Complex Complex.instNatCast 0)))

noncomputable def ep806 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz153 1) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.logSumC qz153 0) qz204) Bool.false 34592038022299293 9007199254740992 100000000281809 51238000000000000000 Bool.false 881257135768995 562949953421312 200000000025619 51238000000000000000

noncomputable def ep807 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz153 0) qz204 Bool.false 0 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable abbrev qz457 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz190))

noncomputable def ep808 := @Enclosure.Complex.IsNear.of_eq qz204 qz457 Bool.false 34592038022299293 9007199254740992 100000000281809 51238000000000000000 Bool.false 881257135768995 562949953421312 200000000025619 51238000000000000000

noncomputable def ep809 := BSN.log_dyadic_bound 1899716100 67435716100 2 1 13642727417759397630000 524288 256190 3608921260599210000 3608921260599210000 29547 69335432200 65536000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 1899716100) (BSN.artanhQ 67435716100) 0 1 3608921260599210000 13642727417759397630000 3608921260599210000 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep810 := @Enclosure.Real.IsNear.mulLit_ff qz93 (Real.log (Enclosure.sfrac Bool.false 34667716100 16000000)) 1 2 0 1 34592038022299293 4503599627370496 100000000281809 25619000000000000000 34592038022299293 9007199254740992 100000000281809 51238000000000000000 qz376 (BSN.isNear_log_sfrac 34667716100 16000000 34592038022299293 4503599627370496 100000000281809 25619000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 34667716100) qz377)) Bool.false 145089523445082013827072 18889465931478580854784 1000000002818090 256190000000000000000 34592038022299293 4503599627370496 100000000281809 25619000000000000000 (BSN.log_rat_reduce_isNear 34667716100 16000000 11 69335432200 65536000000 29547 524288 24973259072661432 36028797018963968 256190 1000000000000000 rfl rfl rfl rfl (ep809 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep811 := BSN.arctan_dyadic_bound_f 1000 186190 1 0 524288 256190 0 1 1 0 1 1 2815 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 186190) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 186190) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz458 := (@Nat.cast Real Real.instNatCast 186190)

noncomputable def ep812 := @Enclosure.Real.IsNear.subLit_ff_p qz94 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz388 qz458)) 884279719003555 562949953421312 1 2000000000000000 2815 524288 1 256190 462032541198054850560 881257135768995 562949953421312 200000000025619 51238000000000000000 qz95 (ep811 rfl) rfl rfl

noncomputable abbrev qz205 := (@HAdd.hAdd Complex Complex Complex qz273 qz443 (@Nat.cast Complex Complex.instNatCast 0))

noncomputable abbrev qz459 := (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz190)

noncomputable def ep813 := @ep807 34592038022299293 9007199254740992 100000000281809 51238000000000000000 Bool.false 881257135768995 562949953421312 200000000025619 51238000000000000000 Bool.false 34592038022299293 34592038022299293 9007199254740992 100000000281809 51238000000000000000 Bool.false 881257135768995 881257135768995 562949953421312 200000000025619 51238000000000000000 (@Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz153 0) (Complex.mk qz13 qz13) Bool.false 0 1 0 1 Bool.false 0 1 0 1 (BSN.log_sum_c_base qz153) qz114) (ep808 (@congrArg Complex Complex qz205 qz459 Complex.log (BSN.w_shift_mk qz153 Bool.false 93095 1000 0 qz154 rfl)) (@Enclosure.Complex.IsNear.of_parts qz457 Bool.false 34592038022299293 9007199254740992 100000000281809 51238000000000000000 Bool.false 881257135768995 562949953421312 200000000025619 51238000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz457) (@HMul.hMul Real Real Real qz0 qz93 (Real.log (Enclosure.sfrac Bool.false 34667716100 16000000))) Bool.false 34592038022299293 9007199254740992 100000000281809 51238000000000000000 (Enclosure.clog_re_eq 1000 186190 4000 34667716100 16000000 rfl rfl rfl) (ep810 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz457) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz458 qz388)) Bool.false 881257135768995 562949953421312 200000000025619 51238000000000000000 (Enclosure.clog_im_eq 1000 186190 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz458 qz388)) (@HSub.hSub Real Real Real qz361 qz94 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz388 qz458))) Bool.false 881257135768995 562949953421312 200000000025619 51238000000000000000 (BSN.arctan_recip 186190 1000 rfl rfl) ep812)))) rfl rfl

noncomputable abbrev qz460 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz190))

noncomputable def ep814 := @Enclosure.Complex.IsNear.of_eq qz203 qz460 Bool.false 34595147578621597 9007199254740992 100000000281809 51238000000000000000 Bool.false 869166802830755 562949953421312 200000000025619 51238000000000000000

noncomputable def ep815 := BSN.log_dyadic_bound 1923716100 67459716100 2 1 13652439888877797630000 524288 256190 3700683633399210000 3700683633399210000 29909 69383432200 65536000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 1923716100) (BSN.artanhQ 67459716100) 0 1 3700683633399210000 13652439888877797630000 3700683633399210000 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep816 := @Enclosure.Real.IsNear.mulLit_ff qz93 (Real.log (Enclosure.sfrac Bool.false 34691716100 16000000)) 1 2 0 1 34595147578621597 4503599627370496 100000000281809 25619000000000000000 34595147578621597 9007199254740992 100000000281809 51238000000000000000 qz376 (BSN.isNear_log_sfrac 34691716100 16000000 34595147578621597 4503599627370496 100000000281809 25619000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 34691716100) qz377)) Bool.false 145102565869602878783488 18889465931478580854784 1000000002818090 256190000000000000000 34595147578621597 4503599627370496 100000000281809 25619000000000000000 (BSN.log_rat_reduce_isNear 34691716100 16000000 11 69383432200 65536000000 29909 524288 24973259072661432 36028797018963968 256190 1000000000000000 rfl rfl rfl rfl (ep815 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep817 := BSN.arctan_dyadic_bound_f 5000 186190 1 0 524288 256190 0 1 1 0 1 1 14075 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 5000) (BSN.arctanEvenQ 186190) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 5000) (BSN.arctanOddQ 186190) 0 0 rfl) rfl rfl rfl

noncomputable def ep818 := @Enclosure.Real.IsNear.subLit_ff_p qz94 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz392 qz458)) 884279719003555 562949953421312 1 2000000000000000 14075 524288 1 256190 455693724722530877440 869166802830755 562949953421312 200000000025619 51238000000000000000 qz95 (ep817 rfl) rfl rfl

noncomputable abbrev qz206 := (@HAdd.hAdd Complex Complex Complex qz273 qz443 qz382)

noncomputable abbrev qz461 := (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz190)

noncomputable def ep819 := @ep803 34595147578621597 9007199254740992 100000000281809 51238000000000000000 Bool.false 869166802830755 562949953421312 200000000025619 51238000000000000000 Bool.false ep804 34593592800460445 4503599627370496 100000000281809 25619000000000000000 Bool.false ep805 875211969299875 281474976710656 200000000025619 25619000000000000000 (ep806 (BSN.log_sum_c_succ qz153 0 1 rfl) (ep813 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep814 (@congrArg Complex Complex qz206 qz461 Complex.log (BSN.w_shift_mk qz153 Bool.false 93095 1000 1 qz154 rfl)) (@Enclosure.Complex.IsNear.of_parts qz460 Bool.false 34595147578621597 9007199254740992 100000000281809 51238000000000000000 Bool.false 869166802830755 562949953421312 200000000025619 51238000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz460) (@HMul.hMul Real Real Real qz0 qz93 (Real.log (Enclosure.sfrac Bool.false 34691716100 16000000))) Bool.false 34595147578621597 9007199254740992 100000000281809 51238000000000000000 (Enclosure.clog_re_eq 5000 186190 4000 34691716100 16000000 rfl rfl rfl) (ep816 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz460) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz458 qz392)) Bool.false 869166802830755 562949953421312 200000000025619 51238000000000000000 (Enclosure.clog_im_eq 5000 186190 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz458 qz392)) (@HSub.hSub Real Real Real qz361 qz94 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz392 qz458))) Bool.false 869166802830755 562949953421312 200000000025619 51238000000000000000 (BSN.arctan_recip 186190 5000 rfl rfl) ep818)))) rfl rfl

noncomputable def ep820 := @ep729 ep723 Bool.false 34593592800460445 4503599627370496 100000000281809 25619000000000000000 Bool.false 875211969299875 281474976710656 200000000025619 25619000000000000000 Bool.true ep730 65894719367410873753 900719925474099200 129498637066719366071773 ep727 Bool.false ep731 1424842704317724229069 10808639105689190400 850108229367994704519661 ep723 (@ep732 900719925474099200 126877197059331912222173 ep727 Bool.false 1458450843938839429069 10808639105689190400 787193669359935663956461 ep723 (BSN.logGammaStirling_unfold 1 qz182) (ep800 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (@ep801 200000000025619 25619000000000000000 (BSN.log_sum_c_eq qz153 2) (ep802 (BSN.log_sum_c_succ qz153 1 2 rfl) (ep819 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)))

noncomputable abbrev qz207 := (@HDiv.hDiv Real Real Real qz270 qz424 (2 : Real))

noncomputable def ep821 := @Enclosure.Real.IsNear.mulLit_ff qz207 (Real.log Real.pi) 93095 2000 0 1 75021 65536 1 131072 1396815999 26214400 18619 52428800 (@Enclosure.Real.IsNear.of_eq qz207 (Enclosure.sfrac Bool.false 93095 2000) Bool.false 93095 2000 0 1 (BSN.t_half_eq qz153 Bool.false 93095 1000 qz154) (Enclosure.Real.IsNear.const Bool.false 93095 2000)) EMRow26.d5 rfl

noncomputable def ep822 := @ep725 18619 52428800 ep726 169782383406241126697 2161727821137838080 ep722 ep723 (@ep728 850108229367994704519661 ep723 (ep820 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) ep821 rfl rfl

noncomputable def ep823 := BSN.cos_dyadic_bound_f 335402 1073741824 1 0 524288 256441 0 1 1 0 1 1 524287 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 335402) qz283 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 335402) qz284 0 0 rfl) rfl rfl

noncomputable def ep824 := @ep721 524288 Bool.true 524287 524288 1 128095 (@ep724 41177647 524288 243 524288 ep822 rfl) (Enclosure.sfrac_false_div 41177647 524288) (BSN.cos_reduce2 qz444 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 23601869423518941184) qz33) 226375608064910080 72057594037927936 Bool.false 524287 524288 12 1000000000000000 256190 128095 (BSN.sin_reduce_arg_pos_rat_q2 41177647 524288 226375608064910080 72057594037927936 12 23601869423518941184 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 524287 524288 23601869423518941184 75557863725914323419136 335402 1073741824 256441 256190 (ep823 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep825 := nat_lit 3055763173780259951569039

noncomputable def ep826 := nat_lit 654852005068060746873569280

noncomputable abbrev qz462 := (@HPow.hPow Complex Complex Complex qz505 qz518 qz520)

noncomputable abbrev qz208 := qz462

noncomputable abbrev qz209 := (@HAdd.hAdd Complex Complex Complex qz273 (@HDiv.hDiv Complex Complex Complex qz366 qz395 (@HSub.hSub Complex Complex Complex qz358 qz417 (1 : Complex))) qz365)

noncomputable def ep827 := @Enclosure.Complex.IsNear.of_eq (zetaApproximant qz148 1 19) (@HAdd.hAdd Complex Complex Complex qz4 (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 19, @HPow.hPow Complex Complex Complex qz120 (@Nat.cast Complex Complex.instNatCast n) qz149) (@HMul.hMul Complex Complex Complex qz71 qz208 (@HAdd.hAdd Complex Complex Complex qz4 qz209 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz79 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz79 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz125 qz126 (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1))))))) Bool.false 199924376209882011714499 144846716449471521095680 ep718

noncomputable def ep828 := @Enclosure.Complex.IsNear.addLitP (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 19, @HPow.hPow Complex Complex Complex qz120 (@Nat.cast Complex Complex.instNatCast n) qz149) (@HMul.hMul Complex Complex Complex qz71 qz208 (@HAdd.hAdd Complex Complex Complex qz4 qz209 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz79 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz79 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz125 qz126 (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1)))))) Bool.false 205369024657 137438953472 7275579343819 1600476613181440

noncomputable def ep829 := nat_lit 6685527140838192893218471

noncomputable def ep830 := nat_lit 55662420430785163484253388800

noncomputable def ep831 := nat_lit 1337180357035683201148847

noncomputable def ep832 := nat_lit 11132484086157032696850677760

noncomputable def ep833 := nat_lit 27477397039828597514638787008790528

noncomputable def ep834 := nat_lit 8722604287978225745934913401520128

noncomputable def ep835 := @ep828 Bool.true 1457702111 274877906944 14552258220183 3200953226362880 Bool.true 16513745083418374967581 144846716449471521095680 ep829 ep830 Bool.false 35573324965943506146187 724233582247357605478400 ep831 ep832 Bool.false ep833 199924376209882011714499 144846716449471521095680 ep718 ep719 Bool.false ep834 31732649542312085926587 724233582247357605478400

noncomputable def ep836 := @Enclosure.Complex.IsNear.of_eq (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 19, @HPow.hPow Complex Complex Complex qz120 (@Nat.cast Complex Complex.instNatCast n) qz149) (BSN.headSumC qz148 19) Bool.false 205369024657 137438953472 7275579343819 1600476613181440 Bool.true 1457702111 274877906944 14552258220183

noncomputable abbrev qz210 := (@HPow.hPow Complex Complex Complex qz274 (@Nat.cast Complex Complex.instNatCast 18) qz418)

noncomputable def ep837 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz148 19) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz148 18) qz210) Bool.false 205369024657 137438953472 7275579343819 1600476613181440 Bool.true 1457702111 274877906944 14552258220183 3200953226362880

noncomputable def ep838 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz148 18) qz210 Bool.false 95306528741 68719476736 7696025404469 1760524274499584 Bool.true 29567363443 137438953472 15390340766307 3521048548999168 Bool.false

noncomputable abbrev qz211 := (@HPow.hPow Complex Complex Complex qz274 (@Nat.cast Complex Complex.instNatCast 17) qz418)

noncomputable def ep839 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz148 18) (@HAdd.hAdd Complex Complex Complex qz4 qz162 qz211) Bool.false 95306528741 68719476736 7696025404469 1760524274499584 Bool.true 29567363443 137438953472 15390340766307 3521048548999168

noncomputable def ep840 := @Enclosure.Complex.IsNear.addLitP qz162 qz211 Bool.false 19698319881 17179869184 1844563380337 440131068624896 Bool.true 68168483723 274877906944 29521081790301 7042097097998336 Bool.false

noncomputable abbrev qz212 := (@HMul.hMul Real Real Real qz267 qz424 qz398)

noncomputable def ep841 := @Enclosure.Complex.IsNear.of_eq qz211 (Complex.mk (@HMul.hMul Real Real Real qz0 qz129 (Real.cos qz212)) (@HMul.hMul Real Real Real qz0 qz129 (@Neg.neg Real Real.instNeg (Real.sin qz212)))) Bool.false 16513249217 68719476736 1699314883 9414568312832 Bool.false 9033756837 274877906944 6735827499 37658273251328 (BSN.cpow_neg_s_mk qz153 93095 1000 17 qz154 rfl)

noncomputable def ep842 := @Enclosure.Real.IsNear.mulLit_ff qz153 qz398 93095 1000 0 1 3189913004350711 1125899906842624 50000000025619 6404750000000000000 59392990228005888109 225179981368524800 930950000477000161 1280950000000000000000 qz155 (BSN.isNear_log_sfrac 17 1 3189913004350711 1125899906842624 50000000025619 6404750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz399) Bool.false 26758929747600409100288 9444732965739290427392 1000000000512380 128095000000000000000 3189913004350711 1125899906842624 50000000025619 6404750000000000000 (BSN.log_rat_reduce_isNear 17 1 4 34 32 15892 262144 24973259072661432 36028797018963968 128095 1000000000000000 rfl rfl rfl rfl (ep429 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep843 := nat_lit 22680033238119678363418799600821375437701640779383589870863773012961447870720

noncomputable def ep844 := nat_lit 31747398403958113083982522315166492362620558935070465367526099191093494016

noncomputable def ep845 := nat_lit 59348686502421320673484693918402856587298149707728811765476744206684878766336

noncomputable def ep846 := BSN.sin_dyadic_bound_f 1540683806 1073741824 3 2 524288 256441 ep843 ep107 ep844 ep845 ep109 ep844 519452 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1540683806) qz289 0 2 ep843 ep107 ep844 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1540683806) qz290 0 2 ep845 ep109 ep844 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz463 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 138285081) qz31)

noncomputable def ep847 := @Enclosure.Real.IsNear.cos_image qz212 qz463 Bool.false 138285081 524288 191 262144 Bool.false 519452 524288 1 128095 (@Enclosure.Real.IsNear.recentre' qz212 Bool.false 59392990228005888109 225179981368524800 930950000477000161 1280950000000000000000 138285081 524288 191 262144 (ep842 rfl) rfl) (Enclosure.sfrac_false_div 138285081 524288) (BSN.cos_reduce3 qz463 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 108415984610322207997952) qz33) 226375608064910080 72057594037927936 Bool.false 519452 524288 41 1000000000000000 256190 128095 (BSN.sin_reduce_arg_pos_rat_q3 138285081 524288 226375608064910080 72057594037927936 41 108415984610322207997952 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 519452 524288 108415984610322207997952 75557863725914323419136 1540683806 1073741824 256441 256190 (ep846 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep848 := nat_lit 12614128420468247141047769788151949239773187348073136801754329940174623703296

noncomputable def ep849 := nat_lit 37778890464596825196975344319825514734594320926349269474527937622141684121856

noncomputable def ep850 := BSN.cos_dyadic_bound_f 1540683806 1073741824 3 2 524288 256441 ep848 ep74 ep844 ep849 ep77 ep844 71043 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1540683806) qz283 0 2 ep848 ep74 ep844 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1540683806) qz284 0 2 ep849 ep77 ep844 rfl rfl rfl rfl) rfl rfl

noncomputable def ep851 := @Enclosure.Real.IsNear.sin_image qz212 qz463 Bool.false 138285081 524288 191 262144 Bool.true 71043 524288 1 128095 (@Enclosure.Real.IsNear.recentre' qz212 Bool.false 59392990228005888109 225179981368524800 930950000477000161 1280950000000000000000 138285081 524288 191 262144 (ep842 rfl) rfl) (Enclosure.sfrac_false_div 138285081 524288) (BSN.sin_reduce3 qz463 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 108415984610322207997952) qz33) 226375608064910080 72057594037927936 Bool.false 71043 524288 41 1000000000000000 256190 128095 (BSN.sin_reduce_arg_pos_rat_q3 138285081 524288 226375608064910080 72057594037927936 41 108415984610322207997952 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 71043 524288 108415984610322207997952 75557863725914323419136 1540683806 1073741824 256441 256190 (ep850 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep852 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz129 (Real.cos qz212)) (@HMul.hMul Real Real Real qz0 qz129 (@Neg.neg Real Real.instNeg (Real.sin qz212))) Bool.false 16513249217 68719476736 1699314883 9414568312832 Bool.false 9033756837 274877906944 6735827499 37658273251328 (@Enclosure.Real.IsNear.mulLit_ff qz129 (Real.cos qz212) 127159 524288 1 524288 129863 131072 24728289 33579335680 16513249217 68719476736 1699314883 9414568312832 qz401 (@Enclosure.Real.IsNear.recentre' (Real.cos qz212) Bool.false 519452 524288 24728289 33579335680 129863 131072 24728289 33579335680 (ep847 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz129 (@Neg.neg Real Real.instNeg (Real.sin qz212)) 127159 524288 1 524288 71043 524288 24728289 33579335680 9033756837 274877906944 6735827499 37658273251328 qz401 (@Enclosure.Real.IsNear.neg (Real.sin qz212) Bool.true 71043 524288 24728289 33579335680 (@Enclosure.Real.IsNear.recentre' (Real.sin qz212) Bool.true 71043 524288 24728289 33579335680 71043 524288 24728289 33579335680 (ep851 rfl rfl) rfl)) rfl)

noncomputable def ep853 := @ep840 16513249217 68719476736 1699314883 9414568312832 Bool.false 9033756837 274877906944 6735827499 37658273251328 Bool.false 1637353696151516217344 95306528741 68719476736 7696025404469 1760524274499584 Bool.true 16254829954128762896384 29567363443 137438953472 15390340766307 3521048548999168 EMRow26.d12 (ep841 ep852) rfl rfl

noncomputable abbrev qz213 := (@HMul.hMul Real Real Real qz267 qz424 qz403)

noncomputable def ep854 := @Enclosure.Complex.IsNear.of_eq qz210 (Complex.mk (@HMul.hMul Real Real Real qz0 qz131 (Real.cos qz213)) (@HMul.hMul Real Real Real qz0 qz131 (@Neg.neg Real Real.instNeg (Real.sin qz213)))) Bool.false 14755967175 137438953472 3071118737319 17605242744995840 Bool.false 57677024775 274877906944 6171432758943 35210485489991680 (BSN.cpow_neg_s_mk qz153 93095 1000 18 qz154 rfl)

noncomputable def ep855 := @Enclosure.Real.IsNear.mulLit_ff qz153 qz403 93095 1000 0 1 3254268794313975 1125899906842624 50000000025619 6404750000000000000 2423649227253276021 9007199254740992 930950000477000161 1280950000000000000000 qz155 (BSN.isNear_log_sfrac 18 1 3254268794313975 1125899906842624 50000000025619 6404750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz404) Bool.false 27298785242132565196800 9444732965739290427392 1000000000512380 128095000000000000000 3254268794313975 1125899906842624 50000000025619 6404750000000000000 (BSN.log_rat_reduce_isNear 18 1 4 36 32 30876 262144 24973259072661432 36028797018963968 128095 1000000000000000 rfl rfl rfl rfl (ep444 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep856 := nat_lit 66503087397785628022154182394812641

noncomputable def ep857 := BSN.sin_dyadic_bound_f 507820761 1073741824 2 1 524288 256441 ep856 ep69 ep856 ep856 ep70 ep856 238818 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 507820761) qz289 0 1 ep856 ep69 ep856 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 507820761) qz290 0 1 ep856 ep70 ep856 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz464 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 17634369) (@Nat.cast Real Real.instNatCast 65536))

noncomputable def ep858 := @Enclosure.Real.IsNear.cos_image qz213 qz464 Bool.false 17634369 65536 191 262144 Bool.false 238818 524288 1 128095 (@Enclosure.Real.IsNear.recentre' qz213 Bool.false 2423649227253276021 9007199254740992 930950000477000161 1280950000000000000000 17634369 65536 191 262144 (ep855 rfl) rfl) (Enclosure.sfrac_false_div 17634369 65536) (BSN.cos_reduce3 qz464 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 4466838659769500172288) qz355) 226375608064910080 72057594037927936 Bool.false 238818 524288 42 1000000000000000 256190 128095 (BSN.sin_reduce_arg_pos_rat_q3 17634369 65536 226375608064910080 72057594037927936 42 4466838659769500172288 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 238818 524288 4466838659769500172288 9444732965739290427392 507820761 1073741824 256441 256190 (ep857 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep859 := BSN.cos_dyadic_bound_f 507820761 1073741824 2 1 524288 256441 ep856 ep57 ep856 ep856 ep58 ep856 466737 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 507820761) qz283 0 1 ep856 ep57 ep856 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 507820761) qz284 0 1 ep856 ep58 ep856 rfl rfl rfl rfl) rfl rfl

noncomputable def ep860 := @Enclosure.Real.IsNear.sin_image qz213 qz464 Bool.false 17634369 65536 191 262144 Bool.true 466737 524288 1 128095 (@Enclosure.Real.IsNear.recentre' qz213 Bool.false 2423649227253276021 9007199254740992 930950000477000161 1280950000000000000000 17634369 65536 191 262144 (ep855 rfl) rfl) (Enclosure.sfrac_false_div 17634369 65536) (BSN.sin_reduce3 qz464 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 4466838659769500172288) qz355) 226375608064910080 72057594037927936 Bool.false 466737 524288 42 1000000000000000 256190 128095 (BSN.sin_reduce_arg_pos_rat_q3 17634369 65536 226375608064910080 72057594037927936 42 4466838659769500172288 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 466737 524288 4466838659769500172288 9444732965739290427392 507820761 1073741824 256441 256190 (ep859 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep861 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz131 (Real.cos qz213)) (@HMul.hMul Real Real Real qz0 qz131 (@Neg.neg Real Real.instNeg (Real.sin qz213))) Bool.false 14755967175 137438953472 3071118737319 17605242744995840 Bool.false 57677024775 274877906944 6171432758943 35210485489991680 (@Enclosure.Real.IsNear.mulLit_ff qz131 (Real.cos qz213) 123575 524288 1 524288 119409 262144 24728289 33579335680 14755967175 137438953472 3071118737319 17605242744995840 qz406 (@Enclosure.Real.IsNear.recentre' (Real.cos qz213) Bool.false 238818 524288 24728289 33579335680 119409 262144 24728289 33579335680 (ep858 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz131 (@Neg.neg Real Real.instNeg (Real.sin qz213)) 123575 524288 1 524288 466737 524288 24728289 33579335680 57677024775 274877906944 6171432758943 35210485489991680 qz406 (@Enclosure.Real.IsNear.neg (Real.sin qz213) Bool.true 466737 524288 24728289 33579335680 (@Enclosure.Real.IsNear.recentre' (Real.sin qz213) Bool.true 466737 524288 24728289 33579335680 466737 524288 24728289 33579335680 (ep860 rfl rfl) rfl)) rfl)

noncomputable def ep862 := @ep838 14755967175 137438953472 3071118737319 17605242744995840 Bool.false 57677024775 274877906944 6171432758943 35210485489991680 Bool.false 14112851912211721879552 205369024657 137438953472 7275579343819 1600476613181440 Bool.true 200345052609765179392 1457702111 274877906944 14552258220183 3200953226362880 (ep839 (BSN.head_sum_c_succ qz148 17 18 rfl rfl) (ep853 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep854 ep861) rfl rfl

noncomputable def ep863 := @Enclosure.Complex.IsNear.mul qz208 (@HAdd.hAdd Complex Complex Complex qz4 qz209 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz79 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz79 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz125 qz126 (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1))))) Bool.true 16513745083418374967581 144846716449471521095680 ep829 ep830 Bool.false

noncomputable abbrev qz214 := (Complex.re qz462)

noncomputable abbrev qz215 := (Complex.im qz462)

noncomputable def ep864 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 qz214 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz209 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz79 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz79 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz125 qz126 (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz215 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz209 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz79 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz79 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz125 qz126 (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1))))))) 583745378300771546783 7242335822473576054784 47495606538494226203785

noncomputable def ep865 := nat_lit 556624204307851634842533888

noncomputable def ep866 := nat_lit 1091420008446767911455948800

noncomputable def ep867 := nat_lit 119598087580837789487053915980221393879957504

noncomputable def ep868 := @Enclosure.Real.IsNear.mulLit_tf qz214 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz209 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz79 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz79 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz125 qz126 (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1)))))) 22107159921 137438953472 599572466765 3521048548999168 79215789869

noncomputable abbrev qz465 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) qz521 (Real.log (Enclosure.sfrac Bool.false 19 1)))

noncomputable abbrev qz216 := (Real.cos qz465)

noncomputable abbrev qz217 := (Real.sin qz465)

noncomputable abbrev qz466 := (@Neg.neg Real Real.instNeg qz217)

noncomputable def ep869 := @Enclosure.Complex.IsNear.of_eq qz208 (Complex.mk (@HMul.hMul Real Real Real qz0 qz135 qz216) (@HMul.hMul Real Real Real qz0 qz135 qz466)) Bool.true 22107159921 137438953472 599572466765 3521048548999168 Bool.false 22481949285 137438953472 599652295569 3521048548999168 (BSN.cpow_neg_s_mk qz153 93095 1000 19 qz154 rfl)

noncomputable def ep870 := @Enclosure.Real.IsNear.mulLit_ff qz153 qz138 93095 1000 0 1 3315141365800183 1125899906842624 50000000025619 6404750000000000000 61724617089833607277 225179981368524800 930950000477000161 1280950000000000000000 qz155 (BSN.isNear_log_sfrac 19 1 3315141365800183 1125899906842624 50000000025619 6404750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' qz412 Bool.false 27809421382282341515264 9444732965739290427392 1000000000512380 128095000000000000000 3315141365800183 1125899906842624 50000000025619 6404750000000000000 (BSN.log_rat_reduce_isNear 19 1 4 38 32 45049 262144 24973259072661432 36028797018963968 128095 1000000000000000 rfl rfl rfl rfl (ep465 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep871 := nat_lit 1178858584853733442606212529038343208255252963408804085486361589923376800000

noncomputable def ep872 := nat_lit 278548380723011226153895572013805273724963694786537239749181600100000000

noncomputable def ep873 := nat_lit 3536018657799754305366329795971002014218308962836839181979586406569930400000

noncomputable def ep874 := BSN.cos_dyadic_bound_f 852339430 1073741824 3 2 524288 256441 ep871 ep74 ep872 ep873 ep77 ep872 367598 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 852339430) qz283 0 2 ep871 ep74 ep872 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 852339430) qz284 0 2 ep873 ep77 ep872 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz218 := qz465

noncomputable abbrev qz467 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 143713823) qz31)

noncomputable def ep875 := @Enclosure.Real.IsNear.cos_image qz218 qz467 Bool.false 143713823 524288 191 262144 Bool.true 367598 524288 1 128095 (@Enclosure.Real.IsNear.recentre' qz218 Bool.false 61724617089833607277 225179981368524800 930950000477000161 1280950000000000000000 143713823 524288 191 262144 (ep870 rfl) rfl) (Enclosure.sfrac_false_div 143713823 524288) (BSN.cos_reduce2 qz467 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 59978055347671134109696) qz33) 226375608064910080 72057594037927936 Bool.false 367598 524288 43 1000000000000000 256190 128095 (BSN.sin_reduce_arg_pos_rat_q2 143713823 524288 226375608064910080 72057594037927936 43 59978055347671134109696 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 367598 524288 59978055347671134109696 75557863725914323419136 852339430 1073741824 256441 256190 (ep874 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep876 := nat_lit 527776828520361649794825139080010000

noncomputable def ep877 := BSN.sin_dyadic_bound_f 852339430 1073741824 2 1 524288 256441 ep876 ep69 ep876 ep876 ep70 ep876 373830 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 852339430) qz289 0 1 ep876 ep69 ep876 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 852339430) qz290 0 1 ep876 ep70 ep876 rfl rfl rfl rfl) rfl rfl

noncomputable def ep878 := @Enclosure.Real.IsNear.sin_image qz218 qz467 Bool.false 143713823 524288 191 262144 Bool.true 373830 524288 1 128095 (@Enclosure.Real.IsNear.recentre' qz218 Bool.false 61724617089833607277 225179981368524800 930950000477000161 1280950000000000000000 143713823 524288 191 262144 (ep870 rfl) rfl) (Enclosure.sfrac_false_div 143713823 524288) (BSN.sin_reduce2 qz467 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 59978055347671134109696) qz33) 226375608064910080 72057594037927936 Bool.false 373830 524288 43 1000000000000000 256190 128095 (BSN.sin_reduce_arg_pos_rat_q2 143713823 524288 226375608064910080 72057594037927936 43 59978055347671134109696 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 373830 524288 59978055347671134109696 75557863725914323419136 852339430 1073741824 256441 256190 (ep877 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep879 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz135 qz216) (@HMul.hMul Real Real Real qz0 qz135 qz466) Bool.true 22107159921 137438953472 599572466765 3521048548999168 Bool.false 22481949285 137438953472 599652295569 3521048548999168 (@Enclosure.Real.IsNear.mulLit_ft qz135 qz216 120279 524288 1 524288 183799 262144 24728289 33579335680 22107159921 137438953472 599572466765 3521048548999168 qz414 (@Enclosure.Real.IsNear.recentre' qz216 Bool.true 367598 524288 24728289 33579335680 183799 262144 24728289 33579335680 (ep875 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz135 qz466 120279 524288 1 524288 186915 262144 24728289 33579335680 22481949285 137438953472 599652295569 3521048548999168 qz414 (@Enclosure.Real.IsNear.neg qz217 Bool.true 186915 262144 24728289 33579335680 (@Enclosure.Real.IsNear.recentre' qz217 Bool.true 373830 524288 24728289 33579335680 186915 262144 24728289 33579335680 (ep878 rfl rfl) rfl)) rfl)

noncomputable def ep880 := @ep868 158084785416 0 1 583745378300771546783 7242335822473576054784 47495606538494226203785 ep865 (@Enclosure.Complex.IsNear.re_isNear qz208 Bool.true 22107159921 137438953472 599572466765 3521048548999168 Bool.false 22481949285 137438953472 599652295569 3521048548999168 (ep869 ep879))

noncomputable def ep881 := @Enclosure.Complex.IsNear.re_isNear (@HAdd.hAdd Complex Complex Complex qz4 qz209 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz79 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz79 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz125 qz126 (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1))))) Bool.false 79215789869 158084785416 0 1 Bool.false

noncomputable def ep882 := @Enclosure.Complex.IsNear.addLitP qz209 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz79 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz79 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz125 qz126 (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1)))) Bool.false 345917161 693354322 0 1 Bool.true 70752200

noncomputable def ep883 := @ep882 346677161 0 1 Bool.false 1 456 0 1 Bool.false 18619 45600 0 1 Bool.false 158431579738 79215789869 158084785416 0 1 Bool.false 3228481740659 3228481740659 15808478541600 0 1

noncomputable abbrev qz219 := (@HDiv.hDiv Complex Complex Complex qz366 qz395 (@HSub.hSub Complex Complex Complex qz358 qz417 (1 : Complex)))

noncomputable def ep884 := @Enclosure.Complex.IsNear.addLitP qz219 qz98 Bool.true 38000000 34667716100 0 1 Bool.true 7075220000 34667716100 0 1

noncomputable def ep885 := @Enclosure.Complex.IsNear.of_eq qz219 (Complex.mk (Enclosure.sfrac Bool.true 38000000 34667716100) (Enclosure.sfrac Bool.true 7075220000 34667716100)) Bool.true 38000000 34667716100 0 1 Bool.true 7075220000 34667716100 0 1

noncomputable def ep886 := @ep884 Bool.false 1 2 0 1 Bool.false 0 1 0 1 Bool.false 34591716100 345917161 693354322 0 1 Bool.true 7075220000 70752200 346677161 0 1 (ep885 (BSN.N_div_s_sub_one_mk qz153 93095 1000 19 qz154 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 38000000 34667716100) (Enclosure.sfrac Bool.true 7075220000 34667716100) Bool.true 38000000 34667716100 0 1 Bool.true 7075220000 34667716100 0 1 (Enclosure.Real.IsNear.const Bool.true 38000000 34667716100) (Enclosure.Real.IsNear.const Bool.true 7075220000 34667716100))) qz99 rfl

noncomputable def ep887 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz79 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz79 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz125 qz126 (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1)))) (@HAdd.hAdd Complex Complex Complex qz4 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz79 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz79 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz125 qz126 (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz100)) ↑qz141) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 1))) qz142)) Bool.false 1 456 0 1

noncomputable def ep888 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz79 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz79 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz125 qz126 (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz100)) ↑qz141) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 1))) qz142) Bool.false 0 1 0 1 Bool.false

noncomputable def ep889 := @ep888 0 1 0 1 Bool.false 1 456 0 1 Bool.false 18619 45600 0 1 Bool.false 1 1 456 0 1 Bool.false 18619 18619 45600 0

noncomputable def ep890 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz79 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz79 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz125 qz126 (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1)))) (Complex.mk qz13 qz13) Bool.false 0 1 0 1 Bool.false

noncomputable def ep891 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz100)) ↑qz141) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 1))) qz142 Bool.false 1 456 0 1 Bool.false 18619 45600 0 1

noncomputable def ep892 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz100)) ↑qz141) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 1)))) qz143) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz100)) ↑qz141) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 1)))) qz144) 1 456 0 1 0 1 0

noncomputable def ep893 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz100)) ↑qz141) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 1)))) qz143 1 24 0 1 1 19 0 1 1

noncomputable def ep894 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz100)) ↑qz141)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz100)) ↑qz141)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 1)))) 1 24 0 1 0 1 0 1 1

noncomputable def ep895 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz100)) ↑qz141)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 1 2 0 1 1 24 0

noncomputable def ep896 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 1)) qz148 Bool.false 1 2 0 1 Bool.false 93095 1000 0 1 (BSN.ascPochhammer_one_eval qz148)

noncomputable def ep897 := ep896 (@Enclosure.Complex.IsNear.of_eq qz148 (Complex.mk qz93 qz153) Bool.false 1 2 0 1 Bool.false 93095 1000 0 1 (BSN.s_crit_mk qz153 Bool.false 93095 1000 qz154) (@Enclosure.Complex.IsNear.mk qz93 qz153 Bool.false 1 2 0 1 Bool.false 93095 1000 0 1 qz376 qz155))

noncomputable def ep898 := @ep895 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz100)) ↑qz141) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep489) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 93095 1000 0 1 ep897)

noncomputable def ep899 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz100)) ↑qz141)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 93095 1000 0 1 0 1 0

noncomputable def ep900 := @ep899 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz100)) ↑qz141) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep489) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 93095 1000 0 1 ep897)

noncomputable def ep901 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz100)) ↑qz141)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz100)) ↑qz141)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 1)))) 18619 2400 0 1 0 1 0 1 18619

noncomputable def ep902 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz100)) ↑qz141)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 93095 1000 0 1 18619 2400 0

noncomputable def ep903 := @ep902 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz100)) ↑qz141) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep489) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 93095 1000 0 1 ep897)

noncomputable def ep904 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz100)) ↑qz141)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 1 2 0 1 0 1 0

noncomputable def ep905 := @ep904 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz100)) ↑qz141) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep489) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 93095 1000 0 1 ep897)

noncomputable def ep906 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz100)) ↑qz141) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 24 0 1 Bool.false 18619 2400 0 1 (@ep894 1 24 0 1 (ep898 rfl) (ep900 rfl) rfl rfl) (@ep901 18619 2400 0 1 (ep903 rfl) (ep905 rfl) rfl rfl)

noncomputable def ep907 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz100)) ↑qz141) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 18619 2400 0 1 ep906

noncomputable def ep908 := @ep893 456 0 1 ep907 qz145

noncomputable def ep909 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz100)) ↑qz141) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 1)))) qz144 18619 2400 0 1 0 1 0 1 0

noncomputable def ep910 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz100)) ↑qz141) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 18619 2400 0 1 ep906

noncomputable def ep911 := @ep909 1 0 1 ep910 qz146

noncomputable def ep912 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz100)) ↑qz141) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 1)))) qz144) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz100)) ↑qz141) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 1)))) qz143) 0 1 0 1 18619 45600 0

noncomputable def ep913 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz100)) ↑qz141) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 1)))) qz144 1 24 0 1 0 1 0 1 0

noncomputable def ep914 := @ep913 1 0 1 ep907 qz146

noncomputable def ep915 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz100)) ↑qz141) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 1)))) qz143 18619 2400 0 1 1 19 0 1 18619

noncomputable def ep916 := @ep915 45600 0 1 ep910 qz145

noncomputable def ep917 := @ep889 1 (@ep890 0 1 0 1 (BSN.bern_sum_base qz148 19) qz114) (ep891 (@ep892 1 1 1 456 0 1 (ep908 rfl) (ep911 rfl) rfl rfl) (@ep912 1 18619 18619 45600 0 1 (ep914 rfl) (ep916 rfl) rfl rfl)) rfl rfl rfl rfl rfl

noncomputable def ep918 := ep883 (ep886 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep887 Bool.false 18619 45600 0 1 (BSN.bern_sum_succ qz148 19 0 1 1 rfl rfl) (ep917 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl rfl

noncomputable def ep919 := @Enclosure.Real.IsNear.mulLit_ff qz215 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz209 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz79 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz79 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz125 qz126 (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1)))))) 22481949285 137438953472 599652295569 3521048548999168 3228481740659

noncomputable def ep920 := @ep919 15808478541600 0 1 4838837517402944031921 144846716449471521095680 37960127195858240643921 ep866 (@Enclosure.Complex.IsNear.im_isNear qz208 Bool.true 22107159921 137438953472 599572466765 3521048548999168 Bool.false 22481949285 137438953472 599652295569 3521048548999168 (ep869 ep879))

noncomputable def ep921 := @Enclosure.Complex.IsNear.im_isNear (@HAdd.hAdd Complex Complex Complex qz4 qz209 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz79 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz79 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz125 qz126 (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1))))) Bool.false 79215789869 158084785416 0 1 Bool.false

noncomputable def ep922 := @Enclosure.Real.IsNear.addLit_tf_p (@HMul.hMul Real Real Real qz0 qz214 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz209 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz79 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz79 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz125 qz126 (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz215 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz209 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz79 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz79 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz125 qz126 (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1))))))) 23790854047592320309313 724233582247357605478400 22773044248855030902331

noncomputable def ep923 := nat_lit 185541401435950544947511296

noncomputable def ep924 := nat_lit 257633965725346259483727975611649695424708608

noncomputable def ep925 := @Enclosure.Real.IsNear.mulLit_tf qz214 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz209 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz79 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz79 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz125 qz126 (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1)))))) 22107159921 137438953472 599572466765 3521048548999168 3228481740659

noncomputable def ep926 := @ep925 15808478541600 0 1 23790854047592320309313 724233582247357605478400 22773044248855030902331 ep826 (@Enclosure.Complex.IsNear.re_isNear qz208 Bool.true 22107159921 137438953472 599572466765 3521048548999168 Bool.false 22481949285 137438953472 599652295569 3521048548999168 (ep869 ep879))

noncomputable def ep927 := @Enclosure.Real.IsNear.mulLit_ff qz215 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz209 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz79 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz79 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz125 qz126 (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1)))))) 22481949285 137438953472 599652295569 3521048548999168 79215789869

noncomputable def ep928 := @ep927 158084785416 0 1 593641790135358264555 7242335822473576054784 15833976746752461263487 ep923 (@Enclosure.Complex.IsNear.im_isNear qz208 Bool.true 22107159921 137438953472 599572466765 3521048548999168 Bool.false 22481949285 137438953472 599652295569 3521048548999168 (ep869 ep879))

noncomputable abbrev qz468 := (ep918 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable def ep929 := @ep863 35573324965943506146187 724233582247357605478400 ep831 ep832 (@ep864 ep865 4838837517402944031921 144846716449471521095680 37960127195858240643921 ep866 ep867 16513745083418374967581 144846716449471521095680 ep829 ep830 (ep880 (@ep881 3228481740659 15808478541600 0 1 qz468) rfl) (ep920 (@ep921 3228481740659 15808478541600 0 1 qz468) rfl) rfl rfl) (@ep922 ep826 593641790135358264555 7242335822473576054784 15833976746752461263487 ep923 ep924 35573324965943506146187 724233582247357605478400 ep831 ep832 (ep926 (@ep921 3228481740659 15808478541600 0 1 qz468) rfl) (ep928 (@ep881 3228481740659 15808478541600 0 1 qz468) rfl) rfl rfl)

noncomputable def ep930 := @ep835 ep825 ep826 (@ep836 3200953226362880 (BSN.head_sum_c_eq qz148 19) (ep837 (BSN.head_sum_c_succ qz148 18 19 rfl rfl) (ep862 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))) ep929 rfl rfl rfl

noncomputable def ep931 := @Enclosure.Complex.IsNear.re_isNear (zetaApproximant qz148 1 19) Bool.false 199924376209882011714499 144846716449471521095680 ep718 ep719 Bool.false 31732649542312085926587 724233582247357605478400 ep825 ep826 (@ep827 ep719 Bool.false 31732649542312085926587 724233582247357605478400 ep825 ep826 (BSN.zetaApproximant_eq_folded' qz148 1 19 rfl) (ep930 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

noncomputable def ep932 := @Enclosure.Real.IsNear.mulLit_tf (Real.sin (@HSub.hSub Real Real Real qz361 (Complex.im (@HSub.hSub Complex Complex Complex qz72 qz178 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz179 (@Nat.cast Complex Complex.instNatCast j))))) qz180)) (Complex.im (zetaApproximant qz148 1 19)) 163 524288 31651373

noncomputable def ep933 := @Enclosure.Real.IsNear.recentre' (Real.sin (@HSub.hSub Real Real Real qz361 (Complex.im (@HSub.hSub Complex Complex Complex qz72 qz178 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz179 (@Nat.cast Complex Complex.instNatCast j))))) qz180)) Bool.true 163 524288 31651373

noncomputable def ep934 := @Enclosure.Real.IsNear.sin_image (@HSub.hSub Real Real Real qz361 (Complex.im (@HSub.hSub Complex Complex Complex qz72 qz178 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz179 (@Nat.cast Complex Complex.instNatCast j))))) qz180) qz444 Bool.false 41177647 524288 243

noncomputable def ep935 := BSN.sin_dyadic_bound_f 335402 1073741824 1 0 524288 256441 0 1 1 0 1 1 163 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 335402) qz289 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 335402) qz290 0 0 rfl) rfl rfl

noncomputable def ep936 := @ep934 524288 Bool.true 163 524288 1 128095 (@ep724 41177647 524288 243 524288 ep822 rfl) (Enclosure.sfrac_false_div 41177647 524288) (BSN.sin_reduce2 qz444 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 23601869423518941184) qz33) 226375608064910080 72057594037927936 Bool.false 163 524288 12 1000000000000000 256190 128095 (BSN.sin_reduce_arg_pos_rat_q2 41177647 524288 226375608064910080 72057594037927936 12 23601869423518941184 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 163 524288 23601869423518941184 75557863725914323419136 335402 1073741824 256441 256190 (ep935 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep937 := @Enclosure.Complex.IsNear.im_isNear (zetaApproximant qz148 1 19) Bool.false 199924376209882011714499 144846716449471521095680 ep718 ep719 Bool.false 31732649542312085926587 724233582247357605478400 ep825 ep826 (@ep827 ep719 Bool.false 31732649542312085926587 724233582247357605478400 ep825 ep826 (BSN.zetaApproximant_eq_folded' qz148 1 19 rfl) (ep930 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

theorem EMRow26.d13 : Enclosure.Real.IsNear (hardyZApproximantEM 1 19 qz153) Bool.true ep702 ep703 ep704 ep705 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantEM 1 19 qz153) ep706 Bool.true ep702 ep703 ep704 ep705 (@Eq.refl Real ep706) (@ep707 Bool.true ep702 ep703 ep704 ep705 (BSN.re_exp_mul (@HSub.hSub Real Real Real qz361 (Complex.im (@HSub.hSub Complex Complex Complex qz72 qz178 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz179 (@Nat.cast Complex Complex.instNatCast j))))) qz180) (zetaApproximant qz148 1 19)) (@ep709 ep710 ep711 ep712 ep713 ep714 ep715 ep712 ep716 ep702 ep703 ep704 ep705 (@ep717 67158671360 199924376209882011714499 144846716449471521095680 ep718 ep719 ep708 ep710 ep711 ep712 (@ep720 67158671360 524287 524288 31651373 67158671360 (ep824 rfl rfl) rfl) ep931 rfl) (@ep932 67158671360 31732649542312085926587 724233582247357605478400 ep825 ep826 ep713 ep714 ep715 ep712 (@ep933 67158671360 163 524288 31651373 67158671360 (ep936 rfl rfl) rfl) ep937 rfl) rfl rfl))

theorem EMRow26.d14 : @Eq Nat (Nat.mul (BSN.factNat (Nat.succ (Nat.mul 2 1))) (Nat.pow 4 (Nat.mul 2 1))) 96 := @Eq.refl Nat 96

theorem EMRow26.d15 : @Eq Nat (Nat.mul (Nat.mul 2 1) (Nat.pow (Nat.succ (Nat.mul 4 2)) (Nat.mul 2 1))) 162 := @Eq.refl Nat 162

theorem EMRow26.d16 : @Eq Nat (BSN.factNat (Nat.mul 2 2)) 24 := @Eq.refl Nat 24

theorem EMRow26.d17 : @Eq Nat (Nat.pow 19 (Nat.succ (Nat.mul 2 3))) 893871739 := @Eq.refl Nat 893871739

noncomputable abbrev qz524 := (@HAdd.hAdd Complex Complex Complex qz528 qz527 (@Nat.cast Complex Complex.instNatCast 3))

noncomputable abbrev qz469 := qz524

noncomputable abbrev qz220 := (@HDiv.hDiv Real Real Real qz270 (@Norm.norm Complex Complex.instNorm qz469) (@HAdd.hAdd Real Real Real qz386 (Complex.re qz272) qz293))

noncomputable abbrev qz221 := (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 2)

noncomputable abbrev qz222 := (@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 2)))

noncomputable abbrev qz470 := (@HPow.hPow Complex Complex Complex qz505 qz518 (@HSub.hSub Complex Complex Complex qz511 qz506 qz507))

noncomputable abbrev qz223 := qz470

noncomputable def ep938 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 19))) (@HMul.hMul Real Real Real qz0 qz220 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))) 10457242477 154618822656 11523667 154618822656 56839049192030319 63050394783186944 26763530433

noncomputable def ep939 := nat_lit 9447720133476557698264727552

noncomputable def ep940 := @Enclosure.Real.IsNear.mulLit_ff (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 19)) 4427 294912 1 884736 2362151 524288 2425 524288 10457242477 154618822656

noncomputable abbrev qz224 := qz271

noncomputable abbrev qz525 := (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid)))

noncomputable abbrev qz471 := (@Inv.inv Real Real.instInv (@HPow.hPow Real Nat Real qz525 qz224 2))

noncomputable def ep941 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 96 162) qz471 96 162 0 1 13281 524288 1 524288 4427 294912 1 884736

noncomputable def ep942 := nat_lit 781950621441006189802102638025

noncomputable def ep943 := nat_lit 19807040628566084398385987584

noncomputable def ep944 := nat_lit 26986075409044041160201671

noncomputable def ep945 := nat_lit 1073741824000000000000000000000000000000

noncomputable abbrev qz472 := (@HPow.hPow Real Nat Real qz525 qz224 1)

noncomputable def ep946 := @Enclosure.Real.IsNear.mulLit_ff qz472 qz224 884279719003555 140737488355328 1 500000000000000 884279719003555 140737488355328 1 500000000000000 ep942 ep943 ep944 ep945

noncomputable def ep947 := ep946 (@Enclosure.Real.IsNear.of_eq qz472 qz224 Bool.false 884279719003555 140737488355328 1 500000000000000 (BSN.pow_one_r qz224) (@Enclosure.Real.IsNear.of_eq qz224 qz268 Bool.false 884279719003555 140737488355328 1 500000000000000 BSN.two_pi_eq qz269)) (@Enclosure.Real.IsNear.of_eq qz224 qz268 Bool.false 884279719003555 140737488355328 1 500000000000000 BSN.two_pi_eq qz269) rfl

noncomputable abbrev qz473 := (@HPow.hPow Real Nat Real qz525 qz224 2)

noncomputable def ep948 := @Enclosure.Real.IsNear.inv_image qz473 ep942 ep943 ep944 ep945 6640 6641 262144 (@Enclosure.Real.IsNear.of_eq qz473 (@HMul.hMul Real Real Real qz0 qz472 qz224) Bool.false ep942 ep943 ep944 ep945 (BSN.pow_succ_r qz224 1 2 rfl) ep947) rfl rfl rfl

noncomputable def ep949 := ep941 (Enclosure.Real.IsNear.const Bool.false 96 162) (@Enclosure.Real.IsNear.recentre' qz471 Bool.false 13281 524288 1 524288 13281 524288 1 524288 (ep948 rfl rfl rfl) rfl)

noncomputable def ep950 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 19)) (Real.sqrt (@HAdd.hAdd Real Real Real qz386 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz5 1 19)) (Complex.re (zetaApproximant qz5 1 19))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz5 1 19)) (Complex.im (zetaApproximant qz5 1 19))))) Bool.false 2362151 524288 2425 524288

noncomputable def ep951 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz386 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz5 1 19)) (Complex.re (zetaApproximant qz5 1 19))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz5 1 19)) (Complex.im (zetaApproximant qz5 1 19))))) Bool.false 2362151 524288 2425 524288

noncomputable def ep952 := nat_lit 18241388053489985042859130020028059812120593

noncomputable def ep953 := nat_lit 898632304458897866552945613740179456000000

noncomputable def ep954 := nat_lit 1821223608229869702182912899053359928558675724462759423288387

noncomputable def ep955 := nat_lit 43720391943825213429465112553069275335035432613703581696000000

noncomputable def ep956 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz386 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz5 1 19)) (Complex.re (zetaApproximant qz5 1 19))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz5 1 19)) (Complex.im (zetaApproximant qz5 1 19)))) ep952 ep953 ep954 ep955 1179863 1182288

noncomputable def ep957 := nat_lit 150206674550891775038883367865503241697889203882571281

noncomputable def ep958 := nat_lit 7401456479343865395598500275324733767343407104000000

noncomputable def ep959 := nat_lit 39836429348368598674764301954910129031054072384974020136367

noncomputable def ep960 := nat_lit 971564265418338076210335834512650563000787391415635148800000

noncomputable def ep961 := nat_lit 2244362334958136260912067162323694521341589138441

noncomputable def ep962 := nat_lit 462591029958991587224906267207795860458962944000000

noncomputable def ep963 := nat_lit 223314746510021576707182117831282204384706774522879040249

noncomputable def ep964 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz5 1 19)) (Complex.re (zetaApproximant qz5 1 19))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz5 1 19)) (Complex.im (zetaApproximant qz5 1 19))) ep957 ep958 ep959 ep960 ep961 ep962 ep963

noncomputable def ep965 := nat_lit 341565562061134479917696191820853713554964317294559232000000

noncomputable def ep966 := nat_lit 69500871837358147546572479451868808778534233518337207906021252695026699873371174758215842296496128000000

noncomputable def ep967 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (zetaApproximant qz5 1 19)) (Complex.re (zetaApproximant qz5 1 19)) ep287 ep288 ep289 ep290 ep287 ep288 ep289 ep290 ep957

noncomputable def ep968 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (zetaApproximant qz5 1 19)) (Complex.im (zetaApproximant qz5 1 19)) ep410 ep411 ep412 ep413 ep410 ep411 ep412 ep413 ep961

noncomputable def ep969 := @ep938 63050394783186944 ep939 549929689934742503 567453553048682496 42532914042569 567453553048682496 (@ep940 11523667 154618822656 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaStirlingErrorBound 1 2) (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 96 162) qz471) Bool.false 4427 294912 1 884736 (BSN.theta_err_eq 1 2 96 162 EMRow26.d14 EMRow26.d15 rfl) (ep949 rfl)) (ep950 (BSN.norm_eq_sqrt_mul_add (zetaApproximant qz5 1 19)) (@ep951 2362151 524288 2425 524288 (@ep956 262144 (@ep964 ep965 ep966 ep952 ep953 ep954 ep955 (@ep967 ep958 ep959 ep960 ep528 ep528 rfl) (@ep968 ep962 ep963 ep965 ep534 ep534 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl)

noncomputable abbrev qz225 := (@Norm.norm Complex Complex.instNorm qz469)

noncomputable abbrev qz474 := (Enclosure.sfrac Bool.false 2 7)

noncomputable def ep970 := @Enclosure.Real.IsNear.of_eq (@HMul.hMul Real Real Real qz0 qz220 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))) (@HMul.hMul Real Real Real qz0 (@HMul.hMul Real Real Real qz0 qz225 qz474) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))) Bool.false 56839049192030319 63050394783186944 26763530433 63050394783186944 (BSN.zrb_shape_eq qz225 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) qz16 3)

noncomputable def ep971 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz0 qz225 qz474) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) 47616081 1835008 1 1835008 1193694399 34359738368 537 34359738368

noncomputable def ep972 := @Enclosure.Real.IsNear.mulLit_ff qz225 qz474 47616081 524288 1 524288 2 7 0 1 47616081 1835008

noncomputable abbrev qz475 := (Complex.re qz524)

noncomputable abbrev qz476 := (Complex.im qz524)

noncomputable abbrev qz226 := (@HAdd.hAdd Real Real Real qz386 (@HMul.hMul Real Real Real qz267 qz475 qz475) (@HMul.hMul Real Real Real qz267 qz476 qz476))

noncomputable abbrev qz227 := qz469

noncomputable def ep973 := @Enclosure.Real.IsNear.of_eq qz225 (Real.sqrt qz226) Bool.false 47616081 524288 1 524288 (BSN.norm_eq_sqrt_mul_add qz227)

noncomputable def ep974 := @Enclosure.Real.IsNear.recentre' (Real.sqrt qz226) Bool.false 47616081 524288 1 524288 47616081

noncomputable def ep975 := @Enclosure.Real.IsNear.sqrt_image qz226 8248357009 1000000 0 1 23808040 23808041 262144

noncomputable abbrev qz228 := (@HMul.hMul Real Real Real qz267 qz475 qz475)

noncomputable abbrev qz229 := (@HMul.hMul Real Real Real qz267 qz476 qz476)

noncomputable def ep976 := @Enclosure.Real.IsNear.addLit_ff qz228 qz229 49 4 0 1 8236107009 1000000 0 1

noncomputable abbrev qz230 := qz475

noncomputable def ep977 := @Enclosure.Real.IsNear.mulLit_ff qz230 qz230 7 2 0 1 7 2 0 1 49 4

noncomputable abbrev qz477 := (Enclosure.sfrac Bool.false 7 2)

noncomputable def ep978 := @Enclosure.Complex.IsNear.of_eq qz227 (Complex.mk qz477 qz16) Bool.false 7 2 0 1 Bool.false 90753 1000 0 1 (BSN.s_add_nat_mk qz16 Bool.false 90753 1000 3 qz17)

noncomputable abbrev qz478 := (ep978 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7 2) qz16 Bool.false 7 2 0 1 Bool.false 90753 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 7 2) qz21))

noncomputable def ep979 := @ep977 0 1 (@Enclosure.Complex.IsNear.re_isNear qz227 Bool.false 7 2 0 1 Bool.false 90753 1000 0 1 qz478)

noncomputable def ep980 := ep979 (@Enclosure.Complex.IsNear.re_isNear qz227 Bool.false 7 2 0 1 Bool.false 90753 1000 0 1 qz478)

noncomputable abbrev qz231 := qz476

noncomputable def ep981 := @Enclosure.Real.IsNear.mulLit_ff qz231 qz231 90753 1000 0 1 90753 1000 0 1 8236107009 1000000

noncomputable def ep982 := @ep981 0 1 (@Enclosure.Complex.IsNear.im_isNear qz227 Bool.false 7 2 0 1 Bool.false 90753 1000 0 1 qz478)

noncomputable def ep983 := ep982 (@Enclosure.Complex.IsNear.im_isNear qz227 Bool.false 7 2 0 1 Bool.false 90753 1000 0 1 qz478)

noncomputable def ep984 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Real.sqrt (@HAdd.hAdd Real Real Real qz386 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.re (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.im (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))))) Bool.false 1193694399 34359738368

noncomputable def ep985 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz386 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.re (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.im (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))))) Bool.false 2387388798 68719476736

noncomputable def ep986 := nat_lit 43065150964920697059646542880436955466749161780860007841789133

noncomputable def ep987 := nat_lit 35681192317648997026457149236237378409568665600000000000000000000

noncomputable def ep988 := nat_lit 802645542260656863183648691151942314495492938339034627056161640380411571107

noncomputable def ep989 := nat_lit 739587668032214592671147309556714140277742457897553857410498560000000000000000000000

noncomputable def ep990 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz386 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.re (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.im (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)))) ep986 ep987 ep988 ep989

noncomputable def ep991 := nat_lit 2254953134904074439058125499960029419829996632065906327969129

noncomputable def ep992 := nat_lit 43032824342637170692302739159430045045418582028614908731512664158926820151

noncomputable def ep993 := nat_lit 10202549457504155655147104345119231511729791287198525378455001

noncomputable def ep994 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.re (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.im (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))) ep991 ep987 ep992 ep989 ep993

noncomputable def ep995 := nat_lit 8920298079412249256614287309059344602392166400000000000000000000

noncomputable def ep996 := nat_lit 189903179479504923122836487998128067362518589077604929581162244055371187739

noncomputable def ep997 := nat_lit 184896917008053648167786827389178535069435614474388464352624640000000000000000000000

noncomputable def ep998 := nat_lit 384153983441980666839776620037669148112229655319851718118929528566409929203060679117718410245096279847731200000000000000000000

noncomputable def ep999 := nat_lit 1501650137316969860855696644627

noncomputable def ep1000 := nat_lit 188894659314785808547840000000000

noncomputable def ep1001 := nat_lit 3147210877386406749481846927567631

noncomputable def ep1002 := nat_lit 859992830221400504363582383718400000000000

noncomputable def ep1003 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.re (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) ep999 ep1000 ep1001 ep1002 ep999 ep1000 ep1001

noncomputable def ep1004 := nat_lit 3194142992651417860932563897499

noncomputable def ep1005 := nat_lit 94447329657392904273920000000000

noncomputable def ep1006 := nat_lit 6529390411188194683072921933385293

noncomputable def ep1007 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223) Bool.true ep999 ep1000 ep1001 ep1002 Bool.true ep1004 ep1005 ep1006

noncomputable def ep1008 := nat_lit 429996415110700252181791191859200000000000

noncomputable def ep1009 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223 Bool.true ep999 ep1000 ep1001 ep1002 Bool.true ep1004 ep1005 ep1006 ep1008

noncomputable def ep1010 := nat_lit 319878677341684575693756497

noncomputable def ep1011 := nat_lit 188894659314785808547840000000

noncomputable def ep1012 := nat_lit 7059502701422692950320080547669

noncomputable def ep1013 := nat_lit 9459921132435405547999406220902400000000

noncomputable def ep1014 := nat_lit 1181771459975285285161940147627

noncomputable def ep1015 := nat_lit 27559816949827781293980235655574941

noncomputable abbrev qz232 := (Complex.re qz470)

noncomputable abbrev qz233 := (Complex.im qz470)

noncomputable def ep1016 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz232) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz233) ep1010 ep1011 ep1012 ep1013 ep1014 ep1000 ep1015

noncomputable def ep1017 := nat_lit 9459921132435405547999406220902400000000000

noncomputable def ep1018 := nat_lit 283653691098490349410911586883098155445983903408455680000000

noncomputable def ep1019 := nat_lit 19708169025907094891665429626880

noncomputable def ep1020 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz232 24707071027 480000000 0 1 38840542085152833 1180591620717411303424 285728028777997852247 ep1019 ep1010

noncomputable def ep1021 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) 24707071027 480000000 0 1 0 1 0 1 24707071027

noncomputable def ep1022 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 74121213081 2000000 0 1 24707071027 480000000 0

noncomputable def ep1023 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (Complex.mk (Enclosure.sfrac Bool.true 1 720) qz13) Bool.true 1 720 0 1 Bool.false 0 1 0 1 (BSN.bern_coeff_mk 2 1 30 24 Bool.true BSN.bern_real_2 EMRow26.d16 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 1 720) qz13 Bool.true 1 720 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.true 1 720) qz22)

noncomputable abbrev qz479 := (@HAdd.hAdd Complex Complex Complex qz504 qz503 qz508)

noncomputable abbrev qz234 := qz479

noncomputable def ep1024 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) (@HMul.hMul Complex Complex Complex qz71 (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) qz234) Bool.true 74121213081 2000000 0 1 Bool.true 746929589637777 1000000000 0 1

noncomputable abbrev qz235 := (Complex.re qz479)

noncomputable abbrev qz236 := (Complex.im qz479)

noncomputable def ep1025 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz235) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz236) 8235357009 400000 0 1 8236107009 500000 0 1

noncomputable def ep1026 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz235 8235357009 1000000 0 1 5 2 0 1 8235357009 400000

noncomputable abbrev qz480 := (@HAdd.hAdd Complex Complex Complex qz504 qz503 (@Nat.cast Complex Complex.instNatCast 1))

noncomputable abbrev qz237 := qz480

noncomputable def ep1027 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) (@HMul.hMul Complex Complex Complex qz71 (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) qz237) Bool.true 8235357009 1000000 0 1 Bool.false 90753 500 0 1

noncomputable abbrev qz238 := (Complex.re qz480)

noncomputable abbrev qz239 := (Complex.im qz480)

noncomputable def ep1028 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz238) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz239) 3 4 0 1 8236107009 1000000 0 1

noncomputable def ep1029 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz238 1 2 0 1 3 2 0 1 3 4

noncomputable def ep1030 := @ep1029 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 90753 1000 0 1 ep491)

noncomputable abbrev qz481 := (Enclosure.sfrac Bool.false 3 2)

noncomputable def ep1031 := @Enclosure.Complex.IsNear.of_eq qz237 (Complex.mk qz481 qz16) Bool.false 3 2 0 1 Bool.false 90753 1000 0 1 (BSN.s_add_nat_mk qz16 Bool.false 90753 1000 1 qz17)

noncomputable abbrev qz482 := (ep1031 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 3 2) qz16 Bool.false 3 2 0 1 Bool.false 90753 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 3 2) qz21))

noncomputable def ep1032 := ep1030 (@Enclosure.Complex.IsNear.re_isNear qz237 Bool.false 3 2 0 1 Bool.false 90753 1000 0 1 qz482)

noncomputable def ep1033 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz239 90753 1000 0 1 90753 1000 0 1 8236107009 1000000

noncomputable def ep1034 := @ep1033 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 90753 1000 0 1 ep491)

noncomputable def ep1035 := ep1034 (@Enclosure.Complex.IsNear.im_isNear qz237 Bool.false 3 2 0 1 Bool.false 90753 1000 0 1 qz482)

noncomputable def ep1036 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) qz237 Bool.true 8235357009 1000000 0 1 Bool.false 90753 500 0 1 (@ep1028 32941428036 8235357009 1000000 0 1 (ep1032 rfl) (ep1035 rfl) rfl rfl)

noncomputable def ep1037 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz239) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz238) 90753 2000 0 1 272259 2000 0 1

noncomputable def ep1038 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz239 1 2 0 1 90753 1000 0 1 90753 2000

noncomputable def ep1039 := @ep1038 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 90753 1000 0 1 ep491)

noncomputable def ep1040 := ep1039 (@Enclosure.Complex.IsNear.im_isNear qz237 Bool.false 3 2 0 1 Bool.false 90753 1000 0 1 qz482)

noncomputable def ep1041 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz238 90753 1000 0 1 3 2 0 1 272259 2000

noncomputable def ep1042 := @ep1041 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 90753 1000 0 1 ep491)

noncomputable def ep1043 := ep1042 (@Enclosure.Complex.IsNear.re_isNear qz237 Bool.false 3 2 0 1 Bool.false 90753 1000 0 1 qz482)

noncomputable abbrev qz240 := (ep1027 (BSN.ascPochhammer_succ_eval_c 1 2 qz272 rfl) (ep1036 (@ep1037 726024000 90753 500 0 1 (ep1040 rfl) (ep1043 rfl) rfl rfl)))

noncomputable def ep1044 := @ep1026 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 8235357009 1000000 0 1 Bool.false 90753 500 0 1 qz240)

noncomputable abbrev qz483 := (Enclosure.sfrac Bool.false 5 2)

noncomputable def ep1045 := @Enclosure.Complex.IsNear.of_eq qz234 (Complex.mk qz483 qz16) Bool.false 5 2 0 1 Bool.false 90753 1000 0 1 (BSN.s_add_nat_mk qz16 Bool.false 90753 1000 2 qz17)

noncomputable abbrev qz484 := (ep1045 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 5 2) qz16 Bool.false 5 2 0 1 Bool.false 90753 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 5 2) qz21))

noncomputable def ep1046 := ep1044 (@Enclosure.Complex.IsNear.re_isNear qz234 Bool.false 5 2 0 1 Bool.false 90753 1000 0 1 qz484)

noncomputable def ep1047 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz236 90753 500 0 1 90753 1000 0 1 8236107009 500000

noncomputable def ep1048 := @ep1047 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 8235357009 1000000 0 1 Bool.false 90753 500 0 1 qz240)

noncomputable def ep1049 := ep1048 (@Enclosure.Complex.IsNear.im_isNear qz234 Bool.false 5 2 0 1 Bool.false 90753 1000 0 1 qz484)

noncomputable def ep1050 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) qz234 Bool.true 74121213081 2000000 0 1 Bool.true 746929589637777 1000000000 0 1 (@ep1025 7412121308100000 74121213081 2000000 0 1 (ep1046 rfl) (ep1049 rfl) rfl rfl)

noncomputable def ep1051 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz236) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz235) 747383354637777 1000000000 0 1 90753 200 0 1

noncomputable def ep1052 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz236 8235357009 1000000 0 1 90753 1000 0 1 747383354637777 1000000000

noncomputable def ep1053 := @ep1052 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 8235357009 1000000 0 1 Bool.false 90753 500 0 1 qz240)

noncomputable def ep1054 := ep1053 (@Enclosure.Complex.IsNear.im_isNear qz234 Bool.false 5 2 0 1 Bool.false 90753 1000 0 1 qz484)

noncomputable def ep1055 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz235 90753 500 0 1 5 2 0 1 90753 200

noncomputable def ep1056 := @ep1055 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 8235357009 1000000 0 1 Bool.false 90753 500 0 1 qz240)

noncomputable def ep1057 := ep1056 (@Enclosure.Complex.IsNear.re_isNear qz234 Bool.false 5 2 0 1 Bool.false 90753 1000 0 1 qz484)

noncomputable abbrev qz241 := (ep1024 (BSN.ascPochhammer_succ_eval_c 2 3 qz272 rfl) (ep1050 (@ep1051 149385917927555400 746929589637777 1000000000 0 1 (ep1054 rfl) (ep1057 rfl) rfl rfl)))

noncomputable def ep1058 := @ep1022 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1023) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 74121213081 2000000 0 1 Bool.true 746929589637777 1000000000 0 1 qz241)

noncomputable def ep1059 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 746929589637777 1000000000 0 1 0 1 0

noncomputable def ep1060 := @ep1059 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1023) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 74121213081 2000000 0 1 Bool.true 746929589637777 1000000000 0 1 qz241)

noncomputable def ep1061 := @Enclosure.Real.IsNear.addLit_ft_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) 248976529879259 240000000000 0 1 0 1 0 1 248976529879259

noncomputable def ep1062 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 746929589637777 1000000000 0 1 248976529879259 240000000000 0

noncomputable def ep1063 := @ep1062 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1023) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 74121213081 2000000 0 1 Bool.true 746929589637777 1000000000 0 1 qz241)

noncomputable def ep1064 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 74121213081 2000000 0 1 0 1 0

noncomputable def ep1065 := @ep1064 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1023) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 74121213081 2000000 0 1 Bool.true 746929589637777 1000000000 0 1 qz241)

noncomputable def ep1066 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.false 24707071027 480000000 0 1 Bool.false 248976529879259 240000000000 0 1 (@ep1021 24707071027 480000000 0 1 (ep1058 rfl) (ep1060 rfl) rfl rfl) (@ep1061 248976529879259 240000000000 0 1 (ep1063 rfl) (ep1065 rfl) rfl rfl)

noncomputable def ep1067 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 24707071027 480000000 0 1 Bool.false 248976529879259 240000000000 0 1 ep1066

noncomputable def ep1068 := nat_lit 39416338051814189783330859253760

noncomputable def ep1069 := @Enclosure.Complex.IsNear.re_isNear qz223 Bool.true 38840542085152833 1180591620717411303424 285728028777997852247 ep1019 Bool.false 14239552545957459 2361183241434822606848 110692429375543533799 ep1068

noncomputable abbrev qz485 := (@Nat.cast Real Real.instNatCast 893871739)

noncomputable abbrev qz242 := (@Inv.inv Real Real.instInv (Real.sqrt qz485))

noncomputable def ep1070 := @Enclosure.Complex.IsNear.of_eq qz223 (Complex.mk (@HMul.hMul Real Real Real qz0 qz242 qz136) (@HMul.hMul Real Real Real qz0 qz242 qz409)) Bool.true 38840542085152833 1180591620717411303424 285728028777997852247 ep1019 Bool.false 14239552545957459 2361183241434822606848 110692429375543533799

noncomputable def ep1071 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz485) 2054553464925653 68719476736 1 68719476736 1149243 1149244 34359738368 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz485) (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz485 qz18)) Bool.false 2054553464925653 68719476736 1 68719476736 (BSN.sqrt_natCast_div_one 893871739) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz485 qz18)) Bool.false 2054553464925653 68719476736 1 68719476736 2054553464925653 68719476736 1 68719476736 (BSN.sqrt_enclosure 893871739 1 1027276732462826 1027276732462827 34359738368 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep1072 := nat_lit 834673424750000000000000000

noncomputable def ep1073 := nat_lit 3645038905525644730084360192

noncomputable def ep1074 := nat_lit 1237940039285380274899124224

noncomputable def ep1075 := nat_lit 16693468495000000000000000

noncomputable def ep1076 := BSN.log_dyadic_bound 3 35 5 4 2128022244140625 34359738368 16693468495 5234577362280 688905 5904729866 38 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 3) (BSN.artanhQ 35) 0 4 5234577362280 2128022244140625 688905 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep1077 := @Enclosure.Real.IsNear.mulLit_ff qz16 qz138 90753 1000 0 1 3315143572331767 1125899906842624 50003338693699 834673424750000000000000 300859224619824850551 1125899906842624000 4537952996469265347 ep1072 qz21 (BSN.isNear_log_sfrac 19 1 3315143572331767 1125899906842624 50003338693699 834673424750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' qz412 Bool.false ep1073 ep1074 1000066773873980 ep1075 3315143572331767 1125899906842624 50003338693699 834673424750000000000000 (BSN.log_rat_reduce_isNear 19 1 4 38 32 5904729866 34359738368 24973259072661432 36028797018963968 16693468495 1000000000000000 rfl rfl rfl rfl (ep1076 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1078 := nat_lit 448864975693015703755948032

noncomputable def ep1079 := nat_lit 2475880078570760549798248448

noncomputable def ep1080 := nat_lit 279339522407157649705102164204838625723607112192515501606262772969165278449138156288437841771242250229748215054336

noncomputable def ep1081 := nat_lit 6205815975932130475933948815772619174300058935098307850201856211168701179010810671297746935144374213427043908473323520

noncomputable def ep1082 := nat_lit 179625206715018866279300818362455895404367130708615849188824084325077761857527315205667524567038471025197056

noncomputable def ep1083 := nat_lit 838018207971059519077573934012879152259030527843285087587089941259327185191890753810683113978677616612302594768896

noncomputable def ep1084 := nat_lit 279261718916945871417027696709767862843502652079423853259083529502591553055486480208398612081496839604216975881299558400

noncomputable def ep1085 := BSN.cos_dyadic_bound_f 25515019825264 140737488355328 3 2 68719476736 33419541421 ep1080 ep1081 ep1082 ep1083 ep1084 ep1082 67593233436 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 25515019825264) (BSN.cosEvenQ 140737488355328) 0 2 ep1080 ep1081 ep1082 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 25515019825264) (BSN.cosOddQ 140737488355328) 0 2 ep1083 ep1084 ep1082 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz486 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 4590747445981) (@Nat.cast Real Real.instNatCast 17179869184))

noncomputable def ep1086 := @Enclosure.Real.IsNear.cos_image qz139 qz486 Bool.false 4590747445981 17179869184 375 68719476736 Bool.true 67593233436 68719476736 1 16693468495 (@Enclosure.Real.IsNear.recentre' qz139 Bool.false 300859224619824850551 1125899906842624000 4537952996469265347 ep1072 4590747445981 17179869184 375 68719476736 (ep1077 rfl) rfl) (Enclosure.sfrac_false_div 4590747445981 17179869184) (BSN.cos_reduce2 qz486 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep1078) (@Nat.cast Real Real.instNatCast ep1079)) 226375608064910080 72057594037927936 Bool.false 67593233436 68719476736 42 1000000000000000 33386936990 16693468495 (BSN.sin_reduce_arg_pos_rat_q2 4590747445981 17179869184 226375608064910080 72057594037927936 42 ep1078 ep1079 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 67593233436 68719476736 ep1078 ep1079 25515019825264 140737488355328 33419541421 33386936990 (ep1085 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1087 := nat_lit 423822140425696574155001960392100814242431384556732416

noncomputable def ep1088 := nat_lit 47078263015400105728768420674057498120767665833480258846720

noncomputable def ep1089 := nat_lit 329547841107800740101378944718402486845373660834361811927040

noncomputable def ep1090 := BSN.sin_dyadic_bound_f 25515019825264 140737488355328 2 1 68719476736 33419541421 ep1087 ep1088 ep1087 ep1087 ep1089 ep1087 12390370314 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 25515019825264) (BSN.sinEvenQ 140737488355328) 0 1 ep1087 ep1088 ep1087 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 25515019825264) (BSN.sinOddQ 140737488355328) 0 1 ep1087 ep1089 ep1087 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1091 := @Enclosure.Real.IsNear.sin_image qz139 qz486 Bool.false 4590747445981 17179869184 375 68719476736 Bool.true 12390370314 68719476736 1 16693468495 (@Enclosure.Real.IsNear.recentre' qz139 Bool.false 300859224619824850551 1125899906842624000 4537952996469265347 ep1072 4590747445981 17179869184 375 68719476736 (ep1077 rfl) rfl) (Enclosure.sfrac_false_div 4590747445981 17179869184) (BSN.sin_reduce2 qz486 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep1078) (@Nat.cast Real Real.instNatCast ep1079)) 226375608064910080 72057594037927936 Bool.false 12390370314 68719476736 42 1000000000000000 33386936990 16693468495 (BSN.sin_reduce_arg_pos_rat_q2 4590747445981 17179869184 226375608064910080 72057594037927936 42 ep1078 ep1079 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 12390370314 68719476736 ep1078 ep1079 25515019825264 140737488355328 33419541421 33386936990 (ep1090 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz487 := (@Enclosure.Real.IsNear.recentre' qz242 Bool.false 2298487 68719476736 1 68719476736 2298487 68719476736 1 68719476736 (ep1071 rfl rfl) rfl)

noncomputable def ep1092 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz242 qz136) (@HMul.hMul Real Real Real qz0 qz242 qz409) Bool.true 38840542085152833 1180591620717411303424 285728028777997852247 ep1019 Bool.false 14239552545957459 2361183241434822606848 110692429375543533799 ep1068 (@Enclosure.Real.IsNear.mulLit_ft qz242 qz136 2298487 68719476736 1 68719476736 16898308359 17179869184 6328770162361 1147166419885301432320 38840542085152833 1180591620717411303424 285728028777997852247 ep1019 qz487 (@Enclosure.Real.IsNear.recentre' qz136 Bool.true 67593233436 68719476736 6328770162361 1147166419885301432320 16898308359 17179869184 6328770162361 1147166419885301432320 (ep1086 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz242 qz409 2298487 68719476736 1 68719476736 6195185157 34359738368 6328770162361 1147166419885301432320 14239552545957459 2361183241434822606848 110692429375543533799 ep1068 qz487 (@Enclosure.Real.IsNear.neg qz137 Bool.true 6195185157 34359738368 6328770162361 1147166419885301432320 (@Enclosure.Real.IsNear.recentre' qz137 Bool.true 12390370314 68719476736 6328770162361 1147166419885301432320 6195185157 34359738368 6328770162361 1147166419885301432320 (ep1091 rfl rfl) rfl)) rfl)

noncomputable def ep1093 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz233 248976529879259 240000000000 0 1 14239552545957459 2361183241434822606848 110692429375543533799 ep1068 ep1014

noncomputable def ep1094 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 24707071027 480000000 0 1 Bool.false 248976529879259 240000000000 0 1 ep1066

noncomputable def ep1095 := @Enclosure.Complex.IsNear.im_isNear qz223 Bool.true 38840542085152833 1180591620717411303424 285728028777997852247 ep1019 Bool.false 14239552545957459 2361183241434822606848 110692429375543533799 ep1068

noncomputable def ep1096 := nat_lit 117272545381889873744480131

noncomputable def ep1097 := nat_lit 377789318629571617095680000000

noncomputable def ep1098 := nat_lit 2734885714732735346302468141573

noncomputable def ep1099 := nat_lit 18919842264870811095998812441804800000000

noncomputable def ep1100 := nat_lit 3223461128996890329368683930249

noncomputable def ep1101 := nat_lit 71139573094386957677226524231844973

noncomputable def ep1102 := @Enclosure.Real.IsNear.addLit_ft_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz233) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz232) ep1096 ep1097 ep1098 ep1099 ep1100 ep1005 ep1101

noncomputable def ep1103 := nat_lit 4729960566217702773999703110451200000000000

noncomputable def ep1104 := nat_lit 1206713104799199934533120020414452157520295399595704320000000

noncomputable def ep1105 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz233 24707071027 480000000 0 1 14239552545957459 2361183241434822606848 110692429375543533799 ep1068 ep1096

noncomputable def ep1106 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz232 248976529879259 240000000000 0 1 38840542085152833 1180591620717411303424 285728028777997852247 ep1019 ep1100

noncomputable abbrev qz488 := (@ep1070 ep1068 (BSN.cpow_neg_s_sub_mk qz16 90753 1000 19 3 893871739 qz17 rfl EMRow26.d17) ep1092)

noncomputable def ep1107 := ep1009 (@ep1016 ep1017 ep1018 ep999 ep1000 ep1001 ep1002 (@ep1020 ep1011 ep1012 ep1013 ep1067 (ep1069 qz488) rfl) (@ep1093 ep1000 ep1015 ep1017 ep1094 (ep1095 qz488) rfl) rfl rfl) (@ep1102 ep1103 ep1104 ep1004 ep1005 ep1006 ep1008 (@ep1105 ep1097 ep1098 ep1099 ep1067 (ep1095 qz488) rfl) (@ep1106 ep1005 ep1101 ep1103 ep1094 (ep1069 qz488) rfl) rfl rfl)

noncomputable def ep1108 := @Enclosure.Real.IsNear.mulLit_tt (Complex.im (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.im (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) ep1004 ep1005 ep1006 ep1008 ep1004 ep1005 ep1006

noncomputable def ep1109 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223) Bool.true ep999 ep1000 ep1001 ep1002 Bool.true ep1004 ep1005 ep1006

noncomputable def ep1110 := @ep971 56839049192030319 63050394783186944 26763530433 63050394783186944 (@ep972 1 1835008 (ep973 (@ep974 524288 1 524288 (ep975 (@ep976 32993428036 8248357009 1000000 0 1 (ep980 rfl) (ep983 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) (Enclosure.Real.IsNear.const Bool.false 2 7) rfl) (@ep984 537 34359738368 (BSN.norm_eq_sqrt_mul_add (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (@ep985 1074 68719476736 1193694399 34359738368 537 34359738368 (@ep990 1193693862 1193694936 34359738368 (@ep994 ep995 ep996 ep997 ep998 ep986 ep987 ep988 ep989 (@ep1003 ep1002 ep991 ep987 ep992 ep989 (@ep1007 ep1008 ep1107) (@ep1007 ep1008 ep1107) rfl) (@ep1108 ep1008 ep993 ep995 ep996 ep997 (@ep1109 ep1008 ep1107) (@ep1109 ep1008 ep1107) rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl

theorem EMRow26.d18 : Enclosure.Real.IsNear (@HAdd.hAdd Real Real Real qz386 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 19))) (@HMul.hMul Real Real Real qz0 qz220 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)))) Bool.false 549929689934742503 567453553048682496 42532914042569 567453553048682496 := ep969 (ep970 ep1110) rfl rfl

noncomputable abbrev qz526 := (@HAdd.hAdd Complex Complex Complex qz528 qz534 (@Nat.cast Complex Complex.instNatCast 3))

noncomputable abbrev qz489 := qz526

noncomputable abbrev qz243 := (@HDiv.hDiv Real Real Real qz270 (@Norm.norm Complex Complex.instNorm qz489) (@HAdd.hAdd Real Real Real qz386 (Complex.re qz417) qz293))

noncomputable abbrev qz490 := (@HPow.hPow Complex Complex Complex qz505 qz518 (@HSub.hSub Complex Complex Complex qz511 qz520 qz507))

noncomputable abbrev qz244 := qz490

noncomputable def ep1111 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz148 1 19))) (@HMul.hMul Real Real Real qz0 qz243 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))) 133549309 6442450944 715709 9663676416 125866679539388027 126100789566373888 60944434129

noncomputable def ep1112 := nat_lit 827730581727619522106490880

noncomputable def ep1113 := @Enclosure.Real.IsNear.mulLit_ff (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz148 1 19)) 4427 294912 1 884736 90501 65536 633 131072 133549309 6442450944

noncomputable def ep1114 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (zetaApproximant qz148 1 19)) (Real.sqrt (@HAdd.hAdd Real Real Real qz386 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz148 1 19)) (Complex.re (zetaApproximant qz148 1 19))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz148 1 19)) (Complex.im (zetaApproximant qz148 1 19))))) Bool.false 90501 65536 633 131072

noncomputable def ep1115 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz386 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz148 1 19)) (Complex.re (zetaApproximant qz148 1 19))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz148 1 19)) (Complex.im (zetaApproximant qz148 1 19))))) Bool.false 724008 524288 2532 524288

noncomputable def ep1116 := nat_lit 1442625847105826668258644612637605031477

noncomputable def ep1117 := nat_lit 756488082661493950220612739247636480000

noncomputable def ep1118 := nat_lit 71469599444492046676969018086322887832705842110330167

noncomputable def ep1119 := nat_lit 5360389356770743226356761428672510881526113086996480000

noncomputable def ep1120 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz386 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz148 1 19)) (Complex.re (zetaApproximant qz148 1 19))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz148 1 19)) (Complex.im (zetaApproximant qz148 1 19)))) ep1116 ep1117 ep1118 ep1119 360738 363270

noncomputable def ep1121 := nat_lit 39969756202910436495342264296573095465486821001

noncomputable def ep1122 := nat_lit 20980571266193603734492587849824311267714662400

noncomputable def ep1123 := nat_lit 138321857723129696805986054299692735809880036951509779

noncomputable def ep1124 := nat_lit 10720778713541486452713522857345021763052226173992960000

noncomputable def ep1125 := nat_lit 1006961046975199436434848619971881666353468569

noncomputable def ep1126 := nat_lit 524514281654840093362314696245607781692866560000

noncomputable def ep1127 := nat_lit 923468233170879309590396374590607971106329453830111

noncomputable def ep1128 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz148 1 19)) (Complex.re (zetaApproximant qz148 1 19))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz148 1 19)) (Complex.im (zetaApproximant qz148 1 19))) ep1121 ep1122 ep1123 ep1124 ep1125 ep1126 ep1127

noncomputable def ep1129 := nat_lit 2144155742708297290542704571469004352610445234798592000

noncomputable def ep1130 := nat_lit 20985834580697000686263302132608539268002959036106388237411048730381775840434410409317472665600

noncomputable def ep1131 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (zetaApproximant qz148 1 19)) (Complex.re (zetaApproximant qz148 1 19)) 199924376209882011714499 144846716449471521095680 ep718 ep719 199924376209882011714499 144846716449471521095680 ep718 ep719 ep1121

noncomputable def ep1132 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (zetaApproximant qz148 1 19)) (Complex.im (zetaApproximant qz148 1 19)) 31732649542312085926587 724233582247357605478400 ep825 ep826 31732649542312085926587 724233582247357605478400 ep825 ep826 ep1125

noncomputable def ep1133 := @ep1111 126100789566373888 ep1112 385442088231267185 378302368699121664 84601731310169 1134907106097364992 (@ep1113 715709 9663676416 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaStirlingErrorBound 1 2) (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 96 162) qz471) Bool.false 4427 294912 1 884736 (BSN.theta_err_eq 1 2 96 162 EMRow26.d14 EMRow26.d15 rfl) (ep949 rfl)) (ep1114 (BSN.norm_eq_sqrt_mul_add (zetaApproximant qz148 1 19)) (@ep1115 90501 65536 633 131072 (@ep1120 262144 (@ep1128 ep1129 ep1130 ep1116 ep1117 ep1118 ep1119 (@ep1131 ep1122 ep1123 ep1124 ep931 ep931 rfl) (@ep1132 ep1126 ep1127 ep1129 ep937 ep937 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl)

noncomputable abbrev qz245 := (@Norm.norm Complex Complex.instNorm qz489)

noncomputable def ep1134 := @Enclosure.Real.IsNear.of_eq (@HMul.hMul Real Real Real qz0 qz243 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))) (@HMul.hMul Real Real Real qz0 (@HMul.hMul Real Real Real qz0 qz245 qz474) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))) Bool.false 125866679539388027 126100789566373888 60944434129 126100789566373888 (BSN.zrb_shape_eq qz245 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) qz153 3)

noncomputable def ep1135 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz0 qz245 qz474) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) 48843073 1835008 1 1835008 2576960699 68719476736 1195 68719476736

noncomputable def ep1136 := @Enclosure.Real.IsNear.mulLit_ff qz245 qz474 48843073 524288 1 524288 2 7 0 1 48843073 1835008

noncomputable abbrev qz491 := (Complex.re qz526)

noncomputable abbrev qz492 := (Complex.im qz526)

noncomputable abbrev qz246 := (@HAdd.hAdd Real Real Real qz386 (@HMul.hMul Real Real Real qz267 qz491 qz491) (@HMul.hMul Real Real Real qz267 qz492 qz492))

noncomputable abbrev qz247 := qz489

noncomputable def ep1137 := @Enclosure.Real.IsNear.of_eq qz245 (Real.sqrt qz246) Bool.false 48843073 524288 1 524288 (BSN.norm_eq_sqrt_mul_add qz247)

noncomputable def ep1138 := @Enclosure.Real.IsNear.recentre' (Real.sqrt qz246) Bool.false 48843073 524288 1 524288 48843073

noncomputable def ep1139 := @Enclosure.Real.IsNear.sqrt_image qz246 347157161 40000 0 1 24421536 24421537 262144

noncomputable abbrev qz248 := (@HMul.hMul Real Real Real qz267 qz491 qz491)

noncomputable abbrev qz249 := (@HMul.hMul Real Real Real qz267 qz492 qz492)

noncomputable def ep1140 := @Enclosure.Real.IsNear.addLit_ff qz248 qz249 49 4 0 1 346667161 40000 0 1

noncomputable abbrev qz250 := qz491

noncomputable def ep1141 := @Enclosure.Real.IsNear.mulLit_ff qz250 qz250 7 2 0 1 7 2 0 1 49 4

noncomputable def ep1142 := @Enclosure.Complex.IsNear.of_eq qz247 (Complex.mk qz477 qz153) Bool.false 7 2 0 1 Bool.false 93095 1000 0 1 (BSN.s_add_nat_mk qz153 Bool.false 93095 1000 3 qz154)

noncomputable abbrev qz493 := (ep1142 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7 2) qz153 Bool.false 7 2 0 1 Bool.false 93095 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 7 2) qz155))

noncomputable def ep1143 := @ep1141 0 1 (@Enclosure.Complex.IsNear.re_isNear qz247 Bool.false 7 2 0 1 Bool.false 93095 1000 0 1 qz493)

noncomputable def ep1144 := ep1143 (@Enclosure.Complex.IsNear.re_isNear qz247 Bool.false 7 2 0 1 Bool.false 93095 1000 0 1 qz493)

noncomputable abbrev qz251 := qz492

noncomputable def ep1145 := @Enclosure.Real.IsNear.mulLit_ff qz251 qz251 93095 1000 0 1 93095 1000 0 1 346667161 40000

noncomputable def ep1146 := @ep1145 0 1 (@Enclosure.Complex.IsNear.im_isNear qz247 Bool.false 7 2 0 1 Bool.false 93095 1000 0 1 qz493)

noncomputable def ep1147 := ep1146 (@Enclosure.Complex.IsNear.im_isNear qz247 Bool.false 7 2 0 1 Bool.false 93095 1000 0 1 qz493)

noncomputable def ep1148 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Real.sqrt (@HAdd.hAdd Real Real Real qz386 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.re (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.im (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))))) Bool.false 2576960699 68719476736

noncomputable def ep1149 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz386 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.re (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.im (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))))) Bool.false 2576960699 68719476736

noncomputable def ep1150 := nat_lit 104044767728284538967924770321031330623931292282804519624921

noncomputable def ep1151 := nat_lit 73988520389876960234061544656261827870081584988160000000000000

noncomputable def ep1152 := nat_lit 134353238950203815129206602302879392159600577397664933264506687760581806339

noncomputable def ep1153 := nat_lit 103092604222346456501616565773729497441595076691255827292164215275520000000000000000

noncomputable def ep1154 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz386 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.re (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.im (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)))) ep1150 ep1151 ep1152 ep1153

noncomputable def ep1155 := nat_lit 64368418342447061985949281165272629276509474006051659123209

noncomputable def ep1156 := nat_lit 82209467099863289148957271840290919855646205542400000000000000

noncomputable def ep1157 := nat_lit 143033250127655010782918037547184948801055782207624462289038621084437780879

noncomputable def ep1158 := nat_lit 206185208444692913003233131547458994883190153382511654584328430551040000000000000000

noncomputable def ep1159 := nat_lit 461131912200821831805704172722859642750727656773580264140329

noncomputable def ep1160 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.re (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.im (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))) ep1155 ep1156 ep1157 ep1158 ep1159

noncomputable def ep1161 := nat_lit 739885203898769602340615446562618278700815849881600000000000000

noncomputable def ep1162 := nat_lit 41891075924250873158498389019524611839381790862568468079991584812241943933

noncomputable def ep1163 := nat_lit 68728402814897637667744377182486331627730051127503884861442810183680000000000000000

noncomputable def ep1164 := nat_lit 85534649094713254969796026034370456664444421077612304160008276155321330367330795965172093005038485193621504000000000000000

noncomputable def ep1165 := nat_lit 253709318596000848559161452797

noncomputable def ep1166 := nat_lit 9066943647109718810296320000000

noncomputable def ep1167 := nat_lit 5628629465519163958644482902969807

noncomputable def ep1168 := nat_lit 454076214356899466303971498603315200000000

noncomputable def ep1169 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.re (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) ep1165 ep1166 ep1167 ep1168 ep1165 ep1166 ep1167

noncomputable def ep1170 := nat_lit 679066942356069805323345033677

noncomputable def ep1171 := nat_lit 27200830941329156430888960000000

noncomputable def ep1172 := nat_lit 1847703332389676718996680142436639

noncomputable def ep1173 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 3))) qz244) Bool.true ep1165 ep1166 ep1167 ep1168 Bool.true ep1170 ep1171 ep1172

noncomputable def ep1174 := nat_lit 151358738118966488767990499534438400000000

noncomputable def ep1175 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 3))) qz244 Bool.true ep1165 ep1166 ep1167 ep1168 Bool.true ep1170 ep1171 ep1172 ep1174

noncomputable def ep1176 := nat_lit 115148465579084965248531049

noncomputable def ep1177 := nat_lit 90669436471097188102963200000

noncomputable def ep1178 := nat_lit 283929339212262981146631476443

noncomputable def ep1179 := nat_lit 504529127063221629226634998448128000000

noncomputable def ep1180 := nat_lit 80731490679364117344769449299

noncomputable def ep1181 := nat_lit 3022314549036572936765440000000

noncomputable def ep1182 := nat_lit 5373093060228127275612514574171107

noncomputable abbrev qz252 := (Complex.re qz490)

noncomputable abbrev qz253 := (Complex.im qz490)

noncomputable def ep1183 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 3)))) qz252) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 3)))) qz253) ep1176 ep1177 ep1178 ep1179 ep1180 ep1181 ep1182

noncomputable def ep1184 := nat_lit 7667893648188485126825137557447726371009362444209356800000

noncomputable def ep1185 := nat_lit 78832676103628379566661718507520

noncomputable def ep1186 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 3)))) qz252 1039951483 19200000 0 1 110724843861860203 4722366482869645213696 819065150212194027363 ep1185 ep1176

noncomputable def ep1187 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 3)))) 1039951483 19200000 0 1 0 1 0 1 1039951483

noncomputable def ep1188 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 3119854449 80000 0 1 1039951483 19200000 0

noncomputable abbrev qz494 := (@HAdd.hAdd Complex Complex Complex qz504 qz519 qz508)

noncomputable abbrev qz254 := qz494

noncomputable def ep1189 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 3)) (@HMul.hMul Complex Complex Complex qz71 (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 2)) qz254) Bool.true 3119854449 80000 0 1 Bool.true 6450313500659 8000000 0 1

noncomputable abbrev qz255 := (Complex.re qz494)

noncomputable abbrev qz256 := (Complex.im qz494)

noncomputable def ep1190 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 2))) qz255) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 2))) qz256) 346637161 16000 0 1 346667161 20000 0 1

noncomputable def ep1191 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 2))) qz255 346637161 40000 0 1 5 2 0 1 346637161 16000

noncomputable abbrev qz495 := (@HAdd.hAdd Complex Complex Complex qz504 qz519 (@Nat.cast Complex Complex.instNatCast 1))

noncomputable abbrev qz257 := qz495

noncomputable def ep1192 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 2)) (@HMul.hMul Complex Complex Complex qz71 (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 1)) qz257) Bool.true 346637161 40000 0 1 Bool.false 18619 100 0 1

noncomputable abbrev qz258 := (Complex.re qz495)

noncomputable abbrev qz259 := (Complex.im qz495)

noncomputable def ep1193 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 1))) qz258) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 1))) qz259) 3 4 0 1 346667161 40000 0 1

noncomputable def ep1194 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 1))) qz258 1 2 0 1 3 2 0 1 3 4

noncomputable def ep1195 := @ep1194 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 93095 1000 0 1 ep897)

noncomputable def ep1196 := @Enclosure.Complex.IsNear.of_eq qz257 (Complex.mk qz481 qz153) Bool.false 3 2 0 1 Bool.false 93095 1000 0 1 (BSN.s_add_nat_mk qz153 Bool.false 93095 1000 1 qz154)

noncomputable abbrev qz496 := (ep1196 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 3 2) qz153 Bool.false 3 2 0 1 Bool.false 93095 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 3 2) qz155))

noncomputable def ep1197 := ep1195 (@Enclosure.Complex.IsNear.re_isNear qz257 Bool.false 3 2 0 1 Bool.false 93095 1000 0 1 qz496)

noncomputable def ep1198 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 1))) qz259 93095 1000 0 1 93095 1000 0 1 346667161 40000

noncomputable def ep1199 := @ep1198 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 93095 1000 0 1 ep897)

noncomputable def ep1200 := ep1199 (@Enclosure.Complex.IsNear.im_isNear qz257 Bool.false 3 2 0 1 Bool.false 93095 1000 0 1 qz496)

noncomputable def ep1201 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 1)) qz257 Bool.true 346637161 40000 0 1 Bool.false 18619 100 0 1 (@ep1193 1386548644 346637161 40000 0 1 (ep1197 rfl) (ep1200 rfl) rfl rfl)

noncomputable def ep1202 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 1))) qz259) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 1))) qz258) 18619 400 0 1 55857 400 0 1

noncomputable def ep1203 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 1))) qz259 1 2 0 1 93095 1000 0 1 18619 400

noncomputable def ep1204 := @ep1203 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 93095 1000 0 1 ep897)

noncomputable def ep1205 := ep1204 (@Enclosure.Complex.IsNear.im_isNear qz257 Bool.false 3 2 0 1 Bool.false 93095 1000 0 1 qz496)

noncomputable def ep1206 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 1))) qz258 93095 1000 0 1 3 2 0 1 55857 400

noncomputable def ep1207 := @ep1206 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 93095 1000 0 1 ep897)

noncomputable def ep1208 := ep1207 (@Enclosure.Complex.IsNear.re_isNear qz257 Bool.false 3 2 0 1 Bool.false 93095 1000 0 1 qz496)

noncomputable abbrev qz260 := (ep1192 (BSN.ascPochhammer_succ_eval_c 1 2 qz417 rfl) (ep1201 (@ep1202 29790400 18619 100 0 1 (ep1205 rfl) (ep1208 rfl) rfl rfl)))

noncomputable def ep1209 := @ep1191 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 346637161 40000 0 1 Bool.false 18619 100 0 1 qz260)

noncomputable def ep1210 := @Enclosure.Complex.IsNear.of_eq qz254 (Complex.mk qz483 qz153) Bool.false 5 2 0 1 Bool.false 93095 1000 0 1 (BSN.s_add_nat_mk qz153 Bool.false 93095 1000 2 qz154)

noncomputable abbrev qz497 := (ep1210 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 5 2) qz153 Bool.false 5 2 0 1 Bool.false 93095 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 5 2) qz155))

noncomputable def ep1211 := ep1209 (@Enclosure.Complex.IsNear.re_isNear qz254 Bool.false 5 2 0 1 Bool.false 93095 1000 0 1 qz497)

noncomputable def ep1212 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 2))) qz256 18619 100 0 1 93095 1000 0 1 346667161 20000

noncomputable def ep1213 := @ep1212 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 346637161 40000 0 1 Bool.false 18619 100 0 1 qz260)

noncomputable def ep1214 := ep1213 (@Enclosure.Complex.IsNear.im_isNear qz254 Bool.false 5 2 0 1 Bool.false 93095 1000 0 1 qz497)

noncomputable def ep1215 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 2)) qz254 Bool.true 3119854449 80000 0 1 Bool.true 6450313500659 8000000 0 1 (@ep1190 12479417796000 3119854449 80000 0 1 (ep1211 rfl) (ep1214 rfl) rfl rfl)

noncomputable def ep1216 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 2))) qz256) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 2))) qz255) 6454037300659 8000000 0 1 18619 40 0 1

noncomputable def ep1217 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 2))) qz256 346637161 40000 0 1 93095 1000 0 1 6454037300659 8000000

noncomputable def ep1218 := @ep1217 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 346637161 40000 0 1 Bool.false 18619 100 0 1 qz260)

noncomputable def ep1219 := ep1218 (@Enclosure.Complex.IsNear.im_isNear qz254 Bool.false 5 2 0 1 Bool.false 93095 1000 0 1 qz497)

noncomputable def ep1220 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 2))) qz255 18619 100 0 1 5 2 0 1 18619 40

noncomputable def ep1221 := @ep1220 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 346637161 40000 0 1 Bool.false 18619 100 0 1 qz260)

noncomputable def ep1222 := ep1221 (@Enclosure.Complex.IsNear.re_isNear qz254 Bool.false 5 2 0 1 Bool.false 93095 1000 0 1 qz497)

noncomputable abbrev qz261 := (ep1189 (BSN.ascPochhammer_succ_eval_c 2 3 qz417 rfl) (ep1215 (@ep1216 258012540026360 6450313500659 8000000 0 1 (ep1219 rfl) (ep1222 rfl) rfl rfl)))

noncomputable def ep1223 := @ep1188 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1023) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 3119854449 80000 0 1 Bool.true 6450313500659 8000000 0 1 qz261)

noncomputable def ep1224 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 6450313500659 8000000 0 1 0 1 0

noncomputable def ep1225 := @ep1224 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1023) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 3119854449 80000 0 1 Bool.true 6450313500659 8000000 0 1 qz261)

noncomputable def ep1226 := @Enclosure.Real.IsNear.addLit_ft_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 3)))) 6450313500659 5760000000 0 1 0 1 0 1 6450313500659

noncomputable def ep1227 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 6450313500659 8000000 0 1 6450313500659 5760000000 0

noncomputable def ep1228 := @ep1227 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1023) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 3119854449 80000 0 1 Bool.true 6450313500659 8000000 0 1 qz261)

noncomputable def ep1229 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 3119854449 80000 0 1 0 1 0

noncomputable def ep1230 := @ep1229 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1023) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 3119854449 80000 0 1 Bool.true 6450313500659 8000000 0 1 qz261)

noncomputable def ep1231 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.false 1039951483 19200000 0 1 Bool.false 6450313500659 5760000000 0 1 (@ep1187 1039951483 19200000 0 1 (ep1223 rfl) (ep1225 rfl) rfl rfl) (@ep1226 6450313500659 5760000000 0 1 (ep1228 rfl) (ep1230 rfl) rfl rfl)

noncomputable def ep1232 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 1039951483 19200000 0 1 Bool.false 6450313500659 5760000000 0 1 ep1231

noncomputable def ep1233 := @Enclosure.Complex.IsNear.re_isNear qz244 Bool.true 110724843861860203 4722366482869645213696 819065150212194027363 ep1185 Bool.false 112643116654724649 4722366482869645213696 832997196133053397073 ep1185

noncomputable def ep1234 := @Enclosure.Complex.IsNear.of_eq qz244 (Complex.mk (@HMul.hMul Real Real Real qz0 qz242 qz216) (@HMul.hMul Real Real Real qz0 qz242 qz466)) Bool.true 110724843861860203 4722366482869645213696 819065150212194027363 ep1185 Bool.false 112643116654724649 4722366482869645213696 832997196133053397073

noncomputable def ep1235 := nat_lit 166934684950000000000000000

noncomputable def ep1236 := @Enclosure.Real.IsNear.mulLit_ff qz153 qz138 93095 1000 0 1 3315143572331767 1125899906842624 50003338693699 834673424750000000000000 61724658173245169773 225179981368524800 931012163137981681 ep1235 qz155 (BSN.isNear_log_sfrac 19 1 3315143572331767 1125899906842624 50003338693699 834673424750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' qz412 Bool.false ep1073 ep1074 1000066773873980 ep1075 3315143572331767 1125899906842624 50003338693699 834673424750000000000000 (BSN.log_rat_reduce_isNear 19 1 4 38 32 5904729866 34359738368 24973259072661432 36028797018963968 16693468495 1000000000000000 rfl rfl rfl rfl (ep1076 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1237 := nat_lit 7863255508724064325654806528

noncomputable def ep1238 := nat_lit 9903520314283042199192993792

noncomputable def ep1239 := nat_lit 479068007620228267260852039122375785728748119195376265057467592400768337616515719012073376471611586288945507126886743730613759254621180759380185275141467904685373670633186010801

noncomputable def ep1240 := nat_lit 28923744637270368355037891692491366079670891706454842103950211515963749868551986041398688626605741342502262687826174894866271194730710136810642225675697019155547683210464434585600

noncomputable def ep1241 := nat_lit 3790277853139181137724973932781009638596334516706093751669659891822815058312069080249930996939190499558033571188847440393199416750510439386497799670428079951749962540721

noncomputable def ep1242 := nat_lit 2905887651368587750070791308450183674513253793104922774436775316775932873844743346930724503552120571813873090145413690221352074762919703348059041906408052830826011728711610541745

noncomputable def ep1243 := nat_lit 2632060761991603520308448144016714313250051145287390631459469247952701238038230729767280665021122462167705904592181915432830678720494622449768442536488428743154839172152263547289600

noncomputable def ep1244 := BSN.cos_dyadic_bound_f 111743581622989 140737488355328 4 3 68719476736 33419541421 ep1239 ep1240 ep1241 ep1242 ep1243 ep1241 48172925869 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 111743581622989) (BSN.cosEvenQ 140737488355328) 0 3 ep1239 ep1240 ep1241 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 111743581622989) (BSN.cosOddQ 140737488355328) 0 3 ep1242 ep1243 ep1241 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz498 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 18836870780409) (@Nat.cast Real Real.instNatCast 68719476736))

noncomputable def ep1245 := @Enclosure.Real.IsNear.cos_image qz218 qz498 Bool.false 18836870780409 68719476736 3 536870912 Bool.true 48172925869 68719476736 1 16693468495 (@Enclosure.Real.IsNear.recentre' qz218 Bool.false 61724658173245169773 225179981368524800 931012163137981681 ep1235 18836870780409 68719476736 3 536870912 (ep1236 rfl) rfl) (Enclosure.sfrac_false_div 18836870780409 68719476736) (BSN.cos_reduce2 qz498 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep1237) (@Nat.cast Real Real.instNatCast ep1238)) 226375608064910080 72057594037927936 Bool.false 48172925869 68719476736 43 1000000000000000 33386936990 16693468495 (BSN.sin_reduce_arg_pos_rat_q2 18836870780409 68719476736 226375608064910080 72057594037927936 43 ep1237 ep1238 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 48172925869 68719476736 ep1237 ep1238 111743581622989 140737488355328 33419541421 33386936990 (ep1244 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1246 := nat_lit 1245445887370037706406041682000401179163976556403672105581288670333650920659811332428831496014108338625554151047433973781951002750161217919401915114725241614517143587247322310321

noncomputable def ep1247 := nat_lit 376008680284514788615492592002387759035721592183912947351352749707528748291175818538182952145874637452529414941740273633261525531499231778538348933784061249022119881736037649612800

noncomputable def ep1248 := nat_lit 6226723569773647392509569179765087730200479854961907400570156948847081896495834487315147335205529696145783925363330270003612812721987661385675163278047822367087420726695088367281

noncomputable def ep1249 := nat_lit 13160303809958017601542240720083571566250255726436953157297346239763506190191153648836403325105612310838529522960909577164153393602473112248842212682442143715774195860761317736448000

noncomputable def ep1250 := BSN.sin_dyadic_bound_f 111743581622989 140737488355328 4 3 68719476736 33419541421 ep1246 ep1247 ep1241 ep1248 ep1249 ep1241 49007506527 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 111743581622989) (BSN.sinEvenQ 140737488355328) 0 3 ep1246 ep1247 ep1241 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 111743581622989) (BSN.sinOddQ 140737488355328) 0 3 ep1248 ep1249 ep1241 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1251 := @Enclosure.Real.IsNear.sin_image qz218 qz498 Bool.false 18836870780409 68719476736 3 536870912 Bool.true 49007506527 68719476736 1 16693468495 (@Enclosure.Real.IsNear.recentre' qz218 Bool.false 61724658173245169773 225179981368524800 931012163137981681 ep1235 18836870780409 68719476736 3 536870912 (ep1236 rfl) rfl) (Enclosure.sfrac_false_div 18836870780409 68719476736) (BSN.sin_reduce2 qz498 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep1237) (@Nat.cast Real Real.instNatCast ep1238)) 226375608064910080 72057594037927936 Bool.false 49007506527 68719476736 43 1000000000000000 33386936990 16693468495 (BSN.sin_reduce_arg_pos_rat_q2 18836870780409 68719476736 226375608064910080 72057594037927936 43 ep1237 ep1238 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 49007506527 68719476736 ep1237 ep1238 111743581622989 140737488355328 33419541421 33386936990 (ep1250 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1252 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz242 qz216) (@HMul.hMul Real Real Real qz0 qz242 qz466) Bool.true 110724843861860203 4722366482869645213696 819065150212194027363 ep1185 Bool.false 112643116654724649 4722366482869645213696 832997196133053397073 ep1185 (@Enclosure.Real.IsNear.mulLit_ft qz242 qz216 2298487 68719476736 1 68719476736 48172925869 68719476736 50617276397 8962237655353917440 110724843861860203 4722366482869645213696 819065150212194027363 ep1185 qz487 (@Enclosure.Real.IsNear.recentre' qz216 Bool.true 48172925869 68719476736 50617276397 8962237655353917440 48172925869 68719476736 50617276397 8962237655353917440 (ep1245 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz242 qz466 2298487 68719476736 1 68719476736 49007506527 68719476736 50617276397 8962237655353917440 112643116654724649 4722366482869645213696 832997196133053397073 ep1185 qz487 (@Enclosure.Real.IsNear.neg qz217 Bool.true 49007506527 68719476736 50617276397 8962237655353917440 (@Enclosure.Real.IsNear.recentre' qz217 Bool.true 49007506527 68719476736 50617276397 8962237655353917440 49007506527 68719476736 50617276397 8962237655353917440 (ep1251 rfl rfl) rfl)) rfl)

noncomputable def ep1253 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 3)))) qz253 6450313500659 5760000000 0 1 112643116654724649 4722366482869645213696 832997196133053397073 ep1185 ep1180

noncomputable def ep1254 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 1039951483 19200000 0 1 Bool.false 6450313500659 5760000000 0 1 ep1231

noncomputable def ep1255 := @Enclosure.Complex.IsNear.im_isNear qz244 Bool.true 110724843861860203 4722366482869645213696 819065150212194027363 ep1185 Bool.false 112643116654724649 4722366482869645213696 832997196133053397073 ep1185

noncomputable def ep1256 := nat_lit 39047792071607632561401489

noncomputable def ep1257 := nat_lit 30223145490365729367654400000

noncomputable def ep1258 := nat_lit 866276669453410745604254209259

noncomputable def ep1259 := nat_lit 1513587381189664887679904995344384000000

noncomputable def ep1260 := nat_lit 714209955220516674628606373777

noncomputable def ep1261 := nat_lit 1761075665444335644436254721510739

noncomputable def ep1262 := @Enclosure.Real.IsNear.addLit_ft_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 3)))) qz253) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 3)))) qz252) ep1256 ep1257 ep1258 ep1259 ep1260 ep1171 ep1261

noncomputable def ep1263 := nat_lit 20523538996525295834306325751875452956822879882497228800000

noncomputable def ep1264 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 3)))) qz253 1039951483 19200000 0 1 112643116654724649 4722366482869645213696 832997196133053397073 ep1185 ep1256

noncomputable def ep1265 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 3)))) qz252 6450313500659 5760000000 0 1 110724843861860203 4722366482869645213696 819065150212194027363 ep1185 ep1260

noncomputable abbrev qz499 := (@ep1234 ep1185 (BSN.cpow_neg_s_sub_mk qz153 93095 1000 19 3 893871739 qz154 rfl EMRow26.d17) ep1252)

noncomputable def ep1266 := ep1175 (@ep1183 ep1168 ep1184 ep1165 ep1166 ep1167 ep1168 (@ep1186 ep1177 ep1178 ep1179 ep1232 (ep1233 qz499) rfl) (@ep1253 ep1181 ep1182 ep1168 ep1254 (ep1255 qz499) rfl) rfl rfl) (@ep1262 ep1174 ep1263 ep1170 ep1171 ep1172 ep1174 (@ep1264 ep1257 ep1258 ep1259 ep1232 (ep1255 qz499) rfl) (@ep1265 ep1171 ep1261 ep1174 ep1254 (ep1233 qz499) rfl) rfl rfl)

noncomputable def ep1267 := @Enclosure.Real.IsNear.mulLit_tt (Complex.im (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.im (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) ep1170 ep1171 ep1172 ep1174 ep1170 ep1171 ep1172

noncomputable def ep1268 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 3))) qz244) Bool.true ep1165 ep1166 ep1167 ep1168 Bool.true ep1170 ep1171 ep1172

noncomputable def ep1269 := @ep1135 125866679539388027 126100789566373888 60944434129 126100789566373888 (@ep1136 1 1835008 (ep1137 (@ep1138 524288 1 524288 (ep1139 (@ep1140 1388628644 347157161 40000 0 1 (ep1144 rfl) (ep1147 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) (Enclosure.Real.IsNear.const Bool.false 2 7) rfl) (@ep1148 1195 68719476736 (BSN.norm_eq_sqrt_mul_add (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (@ep1149 1195 68719476736 2576960699 68719476736 1195 68719476736 (@ep1154 1288479752 1288480947 34359738368 (@ep1160 ep1161 ep1162 ep1163 ep1164 ep1150 ep1151 ep1152 ep1153 (@ep1169 ep1168 ep1155 ep1156 ep1157 ep1158 (@ep1173 ep1174 ep1266) (@ep1173 ep1174 ep1266) rfl) (@ep1267 ep1174 ep1159 ep1161 ep1162 ep1163 (@ep1268 ep1174 ep1266) (@ep1268 ep1174 ep1266) rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl

theorem EMRow26.d19 : Enclosure.Real.IsNear (@HAdd.hAdd Real Real Real qz386 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz148 1 19))) (@HMul.hMul Real Real Real qz0 qz243 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)))) Bool.false 385442088231267185 378302368699121664 84601731310169 1134907106097364992 := ep1133 (ep1134 ep1269) rfl rfl

noncomputable def EMRow26.d20 := fun (I J : @NonemptyInterval Real Real.instLE) => @LE.le Real Real.instLE (@Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE I)) (@Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE J))

noncomputable abbrev qz500 := (EMRow26.d3 qz509 qz521 (@Enclosure.dec_le_dec qz509 qz521 90753 1000 93095 1000 (@Eq.refl Real qz509) (@Eq.refl Real qz521) rfl rfl rfl) 19 19 1 1)

noncomputable abbrev qz262 := qz500

noncomputable def ep1270 := @Zeta.Certificates.ZIntervalEM.Certificate.mk qz262 (@Enclosure.dec_nonneg qz16 90753 1000 qz17) (@Enclosure.pos_of_ble 1 rfl) (@Enclosure.pos_of_ble 19 rfl)

noncomputable abbrev qz263 := (Zeta.Certificates.ZIntervalEM.fstVal qz500)

noncomputable def ep1271 := @Enclosure.Real.IsNear.pos_val qz263 ep272 ep273

noncomputable def ep1272 := @Enclosure.Real.IsNear.of_eq qz263 (hardyZApproximantEM 1 19 qz16) Bool.false

noncomputable abbrev qz264 := (Zeta.Certificates.ZIntervalEM.sndVal qz500)

noncomputable def ep1273 := BSN.mul_neg_of_pos_neg_r qz263 qz264 (@ep1271 ep274 ep275 (@ep1272 ep272 ep273 ep274 ep275 (@Eq.refl Real (hardyZApproximantEM 1 19 qz16)) EMRow26.d10) rfl rfl rfl)

noncomputable def ep1274 := @Enclosure.Real.IsNear.neg_val qz264 ep702 ep703

noncomputable def ep1275 := @Enclosure.Real.IsNear.of_eq qz264 (hardyZApproximantEM 1 19 qz153) Bool.true

noncomputable def ep1276 := BSN.gt_trans_le (@Norm.norm Real Real.norm qz263) (BSN.hardyZErrorBoundStrong 1 19 qz16)

noncomputable def ep1277 := @Enclosure.norm_gt_of_isNear qz263 (BSN.hardyZErrorBoundStrong 1 19 qz16) Bool.false

noncomputable def ep1278 := @Enclosure.Real.IsNear.of_eq (BSN.hardyZErrorBoundStrong 1 19 qz16) (@HAdd.hAdd Real Real Real qz386 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 19))) (@HMul.hMul Real Real Real qz0 qz220 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)))) Bool.false 549929689934742503 567453553048682496 42532914042569 567453553048682496 (@Eq.refl Real (@HAdd.hAdd Real Real Real qz386 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 19))) (@HMul.hMul Real Real Real qz0 qz220 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)))))

noncomputable def ep1279 := BSN.gt_trans_le (@Norm.norm Real Real.norm qz264) (BSN.hardyZErrorBoundStrong 1 19 qz153)

noncomputable def ep1280 := @Enclosure.norm_gt_of_isNear qz264 (BSN.hardyZErrorBoundStrong 1 19 qz153) Bool.true

noncomputable def ep1281 := @Enclosure.Real.IsNear.of_eq (BSN.hardyZErrorBoundStrong 1 19 qz153) (@HAdd.hAdd Real Real Real qz386 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz148 1 19))) (@HMul.hMul Real Real Real qz0 qz243 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)))) Bool.false 385442088231267185 378302368699121664 84601731310169 1134907106097364992 (@Eq.refl Real (@HAdd.hAdd Real Real Real qz386 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz148 1 19))) (@HMul.hMul Real Real Real qz0 qz243 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)))))

noncomputable def ep1282 := @List.cons EMRow26.d0 (@PSigma.mk Zeta.Certificates.ZIntervalEM Zeta.Certificates.ZIntervalEM.Certificate qz262 (ep1270 (@Enclosure.pos_of_ble 1 rfl) (@Enclosure.pos_of_ble 19 rfl) (ep1273 (@ep1274 ep704 ep705 (@ep1275 ep702 ep703 ep704 ep705 (@Eq.refl Real (hardyZApproximantEM 1 19 qz153)) EMRow26.d13) rfl rfl rfl)) (ep1276 (hardyZErrorBoundEM 1 19 qz16) (BSN.hardyZErrorBoundEM_le_strong 1 19 qz16 rfl) (@ep1277 Bool.false ep272 ep273 ep274 ep275 549929689934742503 567453553048682496 42532914042569 567453553048682496 (@ep1272 ep272 ep273 ep274 ep275 (@Eq.refl Real (hardyZApproximantEM 1 19 qz16)) EMRow26.d10) (ep1278 EMRow26.d18) rfl rfl rfl rfl rfl)) (ep1279 (hardyZErrorBoundEM 1 19 qz153) (BSN.hardyZErrorBoundEM_le_strong 1 19 qz153 rfl) (@ep1280 Bool.false ep702 ep703 ep704 ep705 385442088231267185 378302368699121664 84601731310169 1134907106097364992 (@ep1275 ep702 ep703 ep704 ep705 (@Eq.refl Real (hardyZApproximantEM 1 19 qz153)) EMRow26.d13) (ep1281 EMRow26.d19) rfl rfl rfl rfl rfl)))) (@List.nil EMRow26.d0)

noncomputable abbrev qz501 := (@Enclosure.dec_le_dec qz509 qz521 90753 1000 93095 1000 (@Eq.refl Real qz509) (@Eq.refl Real qz521) rfl rfl rfl)

noncomputable abbrev qz265 := (Zeta.Certificates.CertifiedZeroIntervals.intervals (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedEM ep1282 (@List.IsChain.singleton EMRow26.d1 EMRow26.d20 (EMRow26.d2 qz280 qz424 qz501))))

noncomputable abbrev qz502 := (@NonemptyInterval Real Real.instLE)

noncomputable def ep1283 := And (@Eq (Option Real) (@Option.map qz502 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz502 qz265)) (@Option.some Real qz16))

noncomputable def ep1284 := ep1283 (@Eq (Option Real) (@Option.map qz502 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz502 qz265)) (@Option.some Real qz153))

noncomputable def ep1285 := @And.intro (@Eq Nat (@List.length qz502 qz265) 1) ep1284

noncomputable def ep1286 := @And.intro (@Eq (Option Real) (@Option.map qz502 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz502 qz265)) (@Option.some Real qz16))

noncomputable def ep1287 := @ep1286 (@Eq (Option Real) (@Option.map qz502 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz502 qz265)) (@Option.some Real qz153))

noncomputable abbrev qz266 := (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedEM ep1282 (@List.IsChain.singleton EMRow26.d1 EMRow26.d20 (EMRow26.d2 qz280 qz424 qz501)))

theorem EMRow26.d21 : Zeta.Certificates.BatchSpec 1 90753 1000 93095 1000 := @Exists.intro Zeta.Certificates.CertifiedZeroIntervals (fun (C : Zeta.Certificates.CertifiedZeroIntervals) => And (@Eq Nat (@List.length qz502 (Zeta.Certificates.CertifiedZeroIntervals.intervals C)) 1) (And (@Eq (Option Real) (@Option.map qz502 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz502 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz16)) (@Eq (Option Real) (@Option.map qz502 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz502 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz153)))) qz266 (ep1285 (@Eq.refl Nat 1) (ep1287 (@Eq.refl (Option Real) (@Option.some Real qz16)) (@Eq.refl (Option Real) (@Option.some Real qz153))))

theorem solution : Zeta.Certificates.BatchSpec 1 90753 1000 93095 1000 := EMRow26.d21
#print axioms solution
#check solution
