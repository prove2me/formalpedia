-- Prove2me | solution 1 for RHHeight1000.em_main_0018_0018
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-20T08:14:32.393182+00:00
-- url     : https://prove2.me/submissions/cc61c84b-296f-4e5b-80ad-ec897d74a69c

import Definitions.Def_RHT1000_Support_20261118_S005
/- Copyright (c) 2026 Salvatore Mercuri, Bhavik Mehta.
Apache 2.0 license; see the source project LICENSE. -/
set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable def EMRow18.d0 := @PSigma Zeta.Certificates.ZIntervalEM fun (I : Zeta.Certificates.ZIntervalEM) => Zeta.Certificates.ZIntervalEM.Certificate I

noncomputable def EMRow18.d1 := @NonemptyInterval Real Real.instLE

noncomputable def EMRow18.d2 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @NonemptyInterval.mk Real Real.instLE (@Prod.mk Real Real a b) h

noncomputable def EMRow18.d3 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) (fc sc fb sb : Nat) => Zeta.Certificates.ZIntervalEM.mk (EMRow18.d2 a b h) fc sc fb sb

noncomputable def ep0 := nat_lit 26986075409044028275299783

noncomputable def ep1 := nat_lit 4294967296000000000000000

noncomputable def ep2 := nat_lit 26986075409044045455168967

noncomputable abbrev qz262 := (@instHMul Real Real.instMul)

noncomputable abbrev qz0 := qz262

noncomputable abbrev qz1 := (Enclosure.sfrac Bool.false 2 1)

noncomputable abbrev qz263 := (@HMul.hMul Real Real Real qz0 qz1 Real.pi)

noncomputable def ep3 := @BSN.isNear_log_image_fff qz263 884279719003555 140737488355328 1 500000000000000 ep0 ep1 ep2 ep1 4138529546116343 2251799813685248 25000000007779 3889500000000000000 4138529546116343 2251799813685248 25000000007779 3889500000000000000 481788 262144

noncomputable abbrev qz264 := (@Enclosure.Real.IsNear.mulLit_ff qz1 Real.pi 2 1 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 140737488355328 1 500000000000000 (Enclosure.Real.IsNear.const Bool.false 2 1) BSN.pi_near_15 rfl)

noncomputable def ep4 := @ep3 2 262144 qz264 rfl rfl rfl rfl

noncomputable def ep5 := nat_lit 53972150818088056550599566

noncomputable def ep6 := nat_lit 34359738368000000000000000

noncomputable def ep7 := nat_lit 9806206225044028275299783

noncomputable def ep8 := nat_lit 44165944593044028275299783

noncomputable def ep9 := nat_lit 13681445815609410487519367394620474863599256634174726093703677122907123617368241606644861540940610176751640793056574796245399519365549113997355475306157239709119582688278313060810592403844863400465080549957745

noncomputable def ep10 := nat_lit 231714499556395493334623298703961145503103241611736774613091488581016477543539392410113701224645713379230392133956226737605624599560350113120270717249177907454870984269546186598262646369758174842349131395304

noncomputable def ep11 := nat_lit 8978369550011295664474073352761810093897501552430546263638635096022803738134167562509900960712119243631997923545019968443113540909076206607473711060286601587364321108377403290080403445693385008949995305

noncomputable def ep12 := BSN.log_dyadic_bound ep7 ep8 5 4 ep9 524288 155580 ep10 ep11 236759 ep5 ep6 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP ep7) (BSN.artanhQ ep8) 0 4 ep10 ep9 ep11 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz265 := (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))

noncomputable abbrev qz2 := qz265

noncomputable def ep13 := ep4 rfl rfl rfl rfl (BSN.isNear_log_sfrac ep0 ep1 4138529546116343 2251799813685248 25000000007779 3889500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast ep0) (@Nat.cast Real Real.instNatCast ep1))) Bool.false 34716502058787923820544 18889465931478580854784 1000000000311160 155580000000000000000 4138529546116343 2251799813685248 25000000007779 3889500000000000000 (BSN.log_rat_reduce_isNear ep0 ep1 2 ep5 ep6 236759 524288 24973259072661432 36028797018963968 155580 1000000000000000 rfl rfl rfl rfl (ep12 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep14 := nat_lit 53972150818088090910337934

noncomputable def ep15 := nat_lit 9806206225044045455168967

noncomputable def ep16 := nat_lit 44165944593044045455168967

noncomputable def ep17 := nat_lit 13681445815609453062485491347592146866046743284321690683909457683007658987562290830600045658905080811372395010565947827677605470036294121079488508864180301737865471494204890974265645509835068840465080549957745

noncomputable def ep18 := nat_lit 231714499556396865510889920206523150079811393376960301632499817942333196803513131357563499488546302200815366867712007119763002650772307103678175657719139104636874731038771518520299266622696414842349131395304

noncomputable def ep19 := nat_lit 8978369550011421500876706511871067098718760264493934208903156435737864998391937547068187824077011975074541700434630537294838404525415248443919841847024664017658842168336182958576672102333385008949995305

noncomputable def ep20 := BSN.log_dyadic_bound ep15 ep16 5 4 ep17 524288 155580 ep18 ep19 236759 ep14 ep6 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP ep15) (BSN.artanhQ ep16) 0 4 ep18 ep17 ep19 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep21 := ep13 (BSN.isNear_log_sfrac ep2 ep1 4138529546116343 2251799813685248 25000000007779 3889500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast ep2) (@Nat.cast Real Real.instNatCast ep1))) Bool.false 34716502058787923820544 18889465931478580854784 1000000000311160 155580000000000000000 4138529546116343 2251799813685248 25000000007779 3889500000000000000 (BSN.log_rat_reduce_isNear ep2 ep1 2 ep14 ep6 236759 524288 24973259072661432 36028797018963968 155580 1000000000000000 rfl rfl rfl rfl (ep20 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable abbrev qz266 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)

noncomputable abbrev qz3 := (Real.log qz266)

theorem EMRow18.d4 : Enclosure.Real.IsNear qz3 Bool.false 120447 65536 1 131072 := @Enclosure.Real.IsNear.of_eq qz3 (Real.log qz263) Bool.false 120447 65536 1 131072 BSN.log_two_pi_eq (@Enclosure.Real.IsNear.recentre' (Real.log qz263) Bool.false 481788 262144 2 262144 120447 65536 1 131072 (ep21 rfl rfl rfl rfl rfl rfl rfl rfl) rfl)

noncomputable def ep22 := nat_lit 8589934592000000000000000

noncomputable def ep23 := @BSN.isNear_log_image_fff Real.pi 226375608064910080 72057594037927936 1 1000000000000000 ep0 ep22 ep2 ep22 600168 524288 1 155580 600168 524288 1 155580 300084 262144 2 262144 BSN.pi_near_15 rfl rfl rfl

noncomputable def ep24 := nat_lit 17179869184000000000000000

noncomputable def ep25 := nat_lit 18396140817044028275299783

noncomputable def ep26 := nat_lit 35576010001044028275299783

noncomputable def ep27 := nat_lit 145019262663961446558303139663424756232419223153299357158415217874016130572233056993847515999529612750616182853355499335896178729185698845314776375864537073527142908641610750276034469165612529925303649396973267518946591078603565291376312767403717761600170009932259137778521478520425507632472584532570900560707662248426541531715360699177249902784721815296292248142738824858695953661559845440650653128788875447728828657762006237171740033404723254477174341920697506370253193455781322964835857351124092897592956162654178130575

noncomputable def ep28 := nat_lit 15500762873619990602332184736899274490522931101512051618692838888825382235673431503644115344741331161500627469184702974962114537943617674254904297224139410345221262767191485292268260077615645253784097850065864022184521411511133693085443040736512010941548648374196772723338837137976260321103066698629790037694560548409922339907589559883712609967105556007429010014773911317423638534096849366294542840133852248768895750397896505791271178551667935288585787166713880920071720072716082683081155281219708172458141800988558163320

noncomputable def ep29 := nat_lit 12900190794487083783367107939442176642390171280542213571554777169279725287102813254708993369099729304728646904879886535518616983985412662170766446331701281703998252143668221340329975389245922410714088123244705567402747658401492589451585970559635763980329972215329212888079422466283203384882259392047898400615815810081169907384366653346471604103896809335921621947903075223769953790093549808584241881353287841076643853121427928248525828402335494512605306631304432120211393210317325496757155861061354331245840675149075

noncomputable def ep30 := BSN.log_dyadic_bound ep25 ep26 11 10 ep27 524288 155580 ep28 ep29 600168 ep5 ep24 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base10 (BSN.artanhP ep25) (BSN.artanhQ ep26) 0 10 ep28 ep27 ep29 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep31 := nat_lit 18396140817044045455168967

noncomputable def ep32 := nat_lit 35576010001044045455168967

noncomputable def ep33 := nat_lit 145019262663962847171784895425483977818796535899227200426399035286881207006285364467913811844950531107314785650583974625982406238691319033447632878979985852280879486690814033867010958364699188952871572448188560932645032521756218245629809291975913196623825614492380080480004685076434733043183791438169545293975334857826316990371107134320667652578346815517853870648072772035977941843998949310557583393428557296298890786965786350523173236912472938174255438182435383147950274229549088258679583524155427309880956162654178130575

noncomputable def ep34 := nat_lit 15500762873620157189619721156942591192100275120160672416764593300158228469749443299607348495591439275767946573253526107895503597951484257520435868240203420954375895980141891044871083424251900562230440202302413072793440172565998181227591194192658878334739610458454844032013325963992941389843551995646587189684848765634635122388286241104146031552341815777883628509454807838726994150833304950745987647656768534710890974432620160470644835720379148964170536679305861738540146791997074363921127776563807649880221800988558163320

noncomputable def ep35 := nat_lit 12900190794487324729109480814509220959173684627296055849229843377126536688487849343376525559792931631054411655715865486295286288812423905434305314401904993536755333953308594664509631000767632482919425633906965368325056855874260596615770736441041599390097968820060635361729170158825410327022636428624381203910573184452046894301676992229743752846881064485858738985580654099214803581683226335297196686880535448467637789069028262446657986458573827723305156755787640135484017403116612632808333639900906331245840675149075

noncomputable def ep36 := BSN.log_dyadic_bound ep31 ep32 11 10 ep33 524288 155580 ep34 ep35 600168 ep14 ep24 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base10 (BSN.artanhP ep31) (BSN.artanhQ ep32) 0 10 ep34 ep33 ep35 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep37 := @Enclosure.Real.IsNear.recentre' (Real.log Real.pi) Bool.false 300084 262144 2 262144 75021 65536 1 131072 (ep23 rfl rfl rfl rfl rfl (BSN.isNear_log_sfrac ep0 ep22 600168 524288 1 155580 Bool.false (BSN.logfrac_isNear ep5 ep24 1 ep0 ep22 600168 524288 155580 rfl rfl rfl (ep30 rfl))) (BSN.isNear_log_sfrac ep2 ep22 600168 524288 1 155580 Bool.false (BSN.logfrac_isNear ep14 ep24 1 ep2 ep22 600168 524288 155580 rfl rfl rfl (ep36 rfl))) rfl rfl rfl rfl rfl rfl rfl rfl) rfl

theorem EMRow18.d5 : Enclosure.Real.IsNear (Real.log Real.pi) Bool.false 75021 65536 1 131072 := ep37

noncomputable abbrev qz478 := (@HAdd.hAdd Complex Complex Complex (@instHAdd Complex Complex.instAdd) (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (2 : Complex)) (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul) Complex.I ↑(Enclosure.sfrac Bool.false 71064 1000)))

noncomputable abbrev qz455 := qz478

noncomputable abbrev qz267 := qz455

noncomputable abbrev qz4 := (BSN.headSumC qz267 9)

noncomputable abbrev qz479 := (@instHAdd Complex Complex.instAdd)

noncomputable abbrev qz456 := qz479

noncomputable abbrev qz268 := qz456

noncomputable abbrev qz5 := qz268

noncomputable abbrev qz6 := qz267

noncomputable abbrev qz457 := (@instHPow Complex Complex Complex.instPow)

noncomputable abbrev qz269 := qz457

noncomputable abbrev qz458 := (@Neg.neg Complex Complex.instNeg qz478)

noncomputable abbrev qz270 := qz458

noncomputable abbrev qz7 := (@HPow.hPow Complex Complex Complex qz269 (@Nat.cast Complex Complex.instNatCast 8) qz270)

noncomputable def ep38 := @Enclosure.Complex.IsNear.of_eq qz4 (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz6 8) qz7) Bool.false 210225092189 274877906944 11190727882881 3563792063528960 Bool.true 6601797251 274877906944 11190463578391 3563792063528960

noncomputable def ep39 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz6 8) qz7 Bool.false 306726182167 274877906944 10016626872079 3563792063528960 Bool.true 2262320825 34359738368 1252788512023 445474007941120 Bool.true

noncomputable abbrev qz8 := (@HPow.hPow Complex Complex Complex qz269 (@Nat.cast Complex Complex.instNatCast 7) qz270)

noncomputable def ep40 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz6 8) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz6 7) qz8) Bool.false 306726182167 274877906944 10016626872079 3563792063528960 Bool.true 2262320825 34359738368 1252788512023 445474007941120

noncomputable def ep41 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz6 7) qz8 Bool.false 202982303103 274877906944 26277927876661 10691376190586880 Bool.true 12508586533 274877906944 26314236981481 10691376190586880 Bool.false

noncomputable abbrev qz9 := (@HPow.hPow Complex Complex Complex qz269 (@Nat.cast Complex Complex.instNatCast 6) qz270)

noncomputable def ep42 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz6 7) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz6 6) qz9) Bool.false 202982303103 274877906944 26277927876661 10691376190586880 Bool.true 12508586533 274877906944 26314236981481 10691376190586880

noncomputable def ep43 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz6 6) qz9 Bool.false 106814836579 137438953472 11111921279563 5345688095293440 Bool.false 99203076425 274877906944 22241786339531 10691376190586880 Bool.true

noncomputable abbrev qz10 := (@HPow.hPow Complex Complex Complex qz269 (@Nat.cast Complex Complex.instNatCast 5) qz270)

noncomputable def ep44 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz6 6) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz6 5) qz10) Bool.false 106814836579 137438953472 11111921279563 5345688095293440 Bool.false 99203076425 274877906944 22241786339531 10691376190586880

noncomputable def ep45 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz6 5) qz10 Bool.false 177869164685 274877906944 5926328131577 3563792063528960 Bool.false 108407887461 137438953472 740972920259 445474007941120 Bool.false

noncomputable abbrev qz11 := (@HPow.hPow Complex Complex Complex qz269 (@Nat.cast Complex Complex.instNatCast 4) qz270)

noncomputable def ep46 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz6 5) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz6 4) qz11) Bool.false 177869164685 274877906944 5926328131577 3563792063528960 Bool.false 108407887461 137438953472 740972920259 445474007941120

noncomputable def ep47 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz6 4) qz11 Bool.false 14812465655 17179869184 320184198623 267284404764672 Bool.false 46373843655 137438953472 640104930295 534568809529344 Bool.true

noncomputable abbrev qz459 := (@Nat.cast Complex Complex.instNatCast 3)

noncomputable abbrev qz271 := qz459

noncomputable abbrev qz12 := (@HPow.hPow Complex Complex Complex qz269 qz271 qz270)

noncomputable def ep48 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz6 4) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz6 3) qz12) Bool.false 14812465655 17179869184 320184198623 267284404764672 Bool.false 46373843655 137438953472 640104930295 534568809529344

noncomputable def ep49 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz6 3) qz12 Bool.false 11831904611 8589934592 176008347389 267284404764672 Bool.false 20545792101 34359738368 705305450531 1069137619058688 Bool.true

noncomputable abbrev qz460 := (@Nat.cast Complex Complex.instNatCast 2)

noncomputable abbrev qz272 := qz460

noncomputable abbrev qz13 := (@HPow.hPow Complex Complex Complex qz269 qz272 qz270)

noncomputable def ep50 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz6 3) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz6 2) qz13) Bool.false 11831904611 8589934592 176008347389 267284404764672 Bool.false 20545792101 34359738368 705305450531 1069137619058688

noncomputable def ep51 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz6 2) qz13 Bool.false 1 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable abbrev qz273 := (Enclosure.sfrac Bool.false 0 1)

noncomputable abbrev qz14 := qz273

noncomputable def ep52 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz6 2) (Complex.mk (Enclosure.sfrac Bool.false 1 1) qz14) Bool.false 1 1 0 1 Bool.false 0 1 0 1 (BSN.head_sum_c_two qz6)

noncomputable abbrev qz274 := (@Nat.cast Real Real.instNatCast 2)

noncomputable abbrev qz15 := (@Inv.inv Real Real.instInv (Real.sqrt qz274))

noncomputable abbrev qz480 := (Enclosure.sfrac Bool.false 71064 1000)

noncomputable abbrev qz461 := qz480

noncomputable abbrev qz275 := qz461

noncomputable abbrev qz16 := (@HMul.hMul Real Real Real qz262 qz275 (Real.log (Enclosure.sfrac Bool.false 2 1)))

noncomputable abbrev qz17 := qz275

noncomputable abbrev qz276 := (@Eq.refl Real qz461)

noncomputable abbrev qz18 := qz276

noncomputable def ep53 := @Enclosure.Complex.IsNear.of_eq qz13 (Complex.mk (@HMul.hMul Real Real Real qz0 qz15 (Real.cos qz16)) (@HMul.hMul Real Real Real qz0 qz15 (@Neg.neg Real Real.instNeg (Real.sin qz16)))) Bool.false 3241970019 8589934592 176008347389 267284404764672 Bool.false 20545792101 34359738368 705305450531 1069137619058688 (BSN.cpow_neg_s_mk qz17 71064 1000 2 qz18 rfl)

noncomputable abbrev qz19 := (@Nat.cast Real Real.instNatCast 1)

noncomputable def ep54 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz274) 741455 524288 1 524288 185363 185365 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz274) (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz274 qz19)) Bool.false 741455 524288 1 524288 (BSN.sqrt_natCast_div_one 2) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz274 qz19)) Bool.false 741455 524288 1 524288 741455 524288 1 524288 (BSN.sqrt_enclosure 2 1 370727 370728 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep55 := BSN.log_dyadic_bound 1 3 6 5 613814355 262144 77790 24381081 945 181704 4 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 1) (BSN.artanhQ 3) 0 5 24381081 613814355 945 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep56 := nat_lit 133568845584154468729012016640750096

noncomputable def ep57 := nat_lit 159507359494189904748456847233641349120

noncomputable def ep58 := nat_lit 1116551516459329333239197930635489443840

noncomputable abbrev qz277 := (BSN.sinEvenQ 1073741824)

noncomputable abbrev qz278 := (BSN.sinOddQ 1073741824)

noncomputable def ep59 := BSN.sin_dyadic_bound_f 604541742 1073741824 2 1 524288 155732 ep56 ep57 ep56 ep56 ep58 ep56 279836 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 604541742) qz277 0 1 ep56 ep57 ep56 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 604541742) qz278 0 1 ep56 ep58 ep56 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz20 := (@Nat.cast Real Real.instNatCast 262144)

noncomputable abbrev qz21 := (Real.log (Enclosure.sfrac Bool.false 2 1))

noncomputable abbrev qz22 := (Enclosure.Real.IsNear.const Bool.false 71064 1000)

noncomputable abbrev qz279 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 12912613) qz20)

noncomputable abbrev qz280 := (BSN.isNear_log_sfrac 2 1 181704 262144 1 77790 Bool.false (BSN.logfrac_isNear 4 2 1 2 1 181704 262144 77790 rfl rfl rfl (ep55 rfl)))

noncomputable abbrev qz281 := (@Nat.cast Real Real.instNatCast 21270421628140090556416)

noncomputable abbrev qz282 := (@Nat.cast Real Real.instNatCast 37778931862957161709568)

noncomputable def ep60 := @Enclosure.Real.IsNear.cos_image qz16 qz279 Bool.false 12912613 262144 15 16384 Bool.false 279836 524288 1 77790 (@Enclosure.Real.IsNear.recentre' qz16 Bool.false 201759579 4096000 2961 3241250 12912613 262144 15 16384 (@Enclosure.Real.IsNear.mulLit_ff qz17 qz21 71064 1000 0 1 181704 262144 1 77790 201759579 4096000 2961 3241250 qz22 qz280 rfl) rfl) (Enclosure.sfrac_false_div 12912613 262144) (BSN.cos_reduce3 qz279 (@HDiv.hDiv Real Real Real qz2 qz281 qz282) 226375608064910080 72057594037927936 Bool.false 279836 524288 7 1000000000000000 155580 77790 (BSN.sin_reduce_arg_pos_rat_q3 12912613 262144 226375608064910080 72057594037927936 7 21270421628140090556416 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 279836 524288 21270421628140090556416 37778931862957161709568 604541742 1073741824 155732 155580 (ep59 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep61 := nat_lit 31901471898837980949691369446728269824

noncomputable def ep62 := nat_lit 478522078482569714245370541700924047360

noncomputable abbrev qz283 := (BSN.cosEvenQ 1073741824)

noncomputable abbrev qz284 := (BSN.cosOddQ 1073741824)

noncomputable def ep63 := BSN.cos_dyadic_bound_f 604541742 1073741824 2 1 524288 155732 ep56 ep61 ep56 ep56 ep62 ep56 443361 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 604541742) qz283 0 1 ep56 ep61 ep56 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 604541742) qz284 0 1 ep56 ep62 ep56 rfl rfl rfl rfl) rfl rfl

noncomputable def ep64 := @Enclosure.Real.IsNear.sin_image qz16 qz279 Bool.false 12912613 262144 15 16384 Bool.true 443361 524288 1 77790 (@Enclosure.Real.IsNear.recentre' qz16 Bool.false 201759579 4096000 2961 3241250 12912613 262144 15 16384 (@Enclosure.Real.IsNear.mulLit_ff qz17 qz21 71064 1000 0 1 181704 262144 1 77790 201759579 4096000 2961 3241250 qz22 qz280 rfl) rfl) (Enclosure.sfrac_false_div 12912613 262144) (BSN.sin_reduce3 qz279 (@HDiv.hDiv Real Real Real qz2 qz281 qz282) 226375608064910080 72057594037927936 Bool.false 443361 524288 7 1000000000000000 155580 77790 (BSN.sin_reduce_arg_pos_rat_q3 12912613 262144 226375608064910080 72057594037927936 7 21270421628140090556416 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 443361 524288 21270421628140090556416 37778931862957161709568 604541742 1073741824 155732 155580 (ep63 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz285 := (@Enclosure.Real.IsNear.recentre' qz15 Bool.false 370728 524288 2 524288 46341 65536 1 262144 (ep54 rfl rfl) rfl)

noncomputable def ep65 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz15 (Real.cos qz16)) (@HMul.hMul Real Real Real qz0 qz15 (@Neg.neg Real Real.instNeg (Real.sin qz16))) Bool.false 3241970019 8589934592 176008347389 267284404764672 Bool.false 20545792101 34359738368 705305450531 1069137619058688 (@Enclosure.Real.IsNear.mulLit_ff qz15 (Real.cos qz16) 46341 65536 1 262144 69959 131072 591617 637255680 3241970019 8589934592 176008347389 267284404764672 qz285 (@Enclosure.Real.IsNear.recentre' (Real.cos qz16) Bool.false 279836 524288 1183234 1274511360 69959 131072 591617 637255680 (ep60 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz15 (@Neg.neg Real Real.instNeg (Real.sin qz16)) 46341 65536 1 262144 443361 524288 591617 637255680 20545792101 34359738368 705305450531 1069137619058688 qz285 (@Enclosure.Real.IsNear.neg (Real.sin qz16) Bool.true 443361 524288 591617 637255680 (@Enclosure.Real.IsNear.recentre' (Real.sin qz16) Bool.true 443361 524288 1183234 1274511360 443361 524288 591617 637255680 (ep64 rfl rfl) rfl)) rfl)

noncomputable abbrev qz286 := (Enclosure.Real.IsNear.const Bool.false 0 1)

noncomputable abbrev qz23 := qz286

noncomputable def ep66 := @ep51 3241970019 8589934592 176008347389 267284404764672 Bool.false 20545792101 34359738368 705305450531 1069137619058688 Bool.false 11831904611 11831904611 8589934592 176008347389 267284404764672 Bool.false 20545792101 20545792101 34359738368 705305450531 1069137619058688 (ep52 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 1) qz14 Bool.false 1 1 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 1) qz23)) (ep53 ep65) rfl rfl

noncomputable abbrev qz24 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 3)))

noncomputable abbrev qz25 := (@HMul.hMul Real Real Real qz262 qz275 (Real.log (Enclosure.sfrac Bool.false 3 1)))

noncomputable def ep67 := @Enclosure.Complex.IsNear.of_eq qz12 (Complex.mk (@HMul.hMul Real Real Real qz0 qz24 (Real.cos qz25)) (@HMul.hMul Real Real Real qz0 qz24 (@Neg.neg Real Real.instNeg (Real.sin qz25)))) Bool.true 8851343567 17179869184 24029308539 44547400794112 Bool.true 35809324749 137438953472 191634803353 356379206352896 (BSN.cpow_neg_s_mk qz17 71064 1000 3 qz18 rfl)

noncomputable abbrev qz26 := (@Nat.cast Real Real.instNatCast 3)

noncomputable def ep68 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz26) 908093 524288 1 524288 151348 151350 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz26) (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz26 qz19)) Bool.false 908093 524288 1 524288 (BSN.sqrt_natCast_div_one 3) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz26 qz19)) Bool.false 908093 524288 1 524288 908093 524288 1 524288 (BSN.sqrt_enclosure 3 1 454046 454047 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep69 := BSN.log_dyadic_bound 1 2 10 9 171633298636800 262144 77790 16925142283965 34459425 287994 3 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base9 (BSN.artanhP 1) (BSN.artanhQ 2) 0 9 16925142283965 171633298636800 34459425 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep70 := nat_lit 7900550479409141443230074992027926253539191119598084825800574712188593097185

noncomputable def ep71 := nat_lit 641153462866780105519186997069590271023477356498224607523168458325065864314880

noncomputable def ep72 := nat_lit 3859470773131980357187930741725545806456025892542497496663665707395697121

noncomputable def ep73 := nat_lit 20685669255296013906929034996015108351773143176073724785911668787443865078241

noncomputable def ep74 := nat_lit 11754480152557635267851761612942488302097084869134117804591421735959540845772800

noncomputable def ep75 := BSN.sin_dyadic_bound_f 1183902587 1073741824 3 2 524288 155732 ep70 ep71 ep72 ep73 ep74 ep72 467864 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1183902587) qz277 0 2 ep70 ep71 ep72 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1183902587) qz278 0 2 ep73 ep74 ep72 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz27 := (@Nat.cast Real Real.instNatCast 524288)

noncomputable abbrev qz28 := (Real.log (Enclosure.sfrac Bool.false 3 1))

noncomputable abbrev qz29 := (@Nat.cast Real Real.instNatCast 75557863725914323419136)

noncomputable abbrev qz287 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 40932011) qz27)

noncomputable abbrev qz288 := (BSN.isNear_log_sfrac 3 1 287994 262144 1 77790 Bool.false (BSN.logfrac_isNear 3 1 2 3 1 287994 262144 77790 rfl rfl rfl (ep69 rfl)))

noncomputable def ep76 := @Enclosure.Real.IsNear.cos_image qz25 qz287 Bool.false 40932011 524288 15 16384 Bool.true 467864 524288 1 77790 (@Enclosure.Real.IsNear.recentre' qz25 Bool.false 1279125351 16384000 2961 3241250 40932011 524288 15 16384 (@Enclosure.Real.IsNear.mulLit_ff qz17 qz28 71064 1000 0 1 287994 262144 1 77790 1279125351 16384000 2961 3241250 qz22 qz288 rfl) rfl) (Enclosure.sfrac_false_div 40932011 524288) (BSN.cos_reduce1 qz287 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 83309738332358161989632) qz29) 226375608064910080 72057594037927936 Bool.false 467864 524288 12 1000000000000000 155580 77790 (BSN.sin_reduce_arg_pos_rat_q1 40932011 524288 226375608064910080 72057594037927936 12 83309738332358161989632 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 467864 524288 83309738332358161989632 75557863725914323419136 1183902587 1073741824 155732 155580 (ep75 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep77 := nat_lit 4390910031126470570842125187011837050102419966840066013221058691530283141601

noncomputable def ep78 := nat_lit 71239273651864456168798555229954474558164150722024956391463162036118429368320

noncomputable def ep79 := nat_lit 13165011151833147751811999699552060058694347848735113044669848743176058030561

noncomputable def ep80 := nat_lit 3205767314333900527595934985347951355117386782491123037615842291625329321574400

noncomputable def ep81 := BSN.cos_dyadic_bound_f 1183902587 1073741824 3 2 524288 155732 ep77 ep78 ep72 ep79 ep80 ep72 236601 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1183902587) qz283 0 2 ep77 ep78 ep72 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1183902587) qz284 0 2 ep79 ep80 ep72 rfl rfl rfl rfl) rfl rfl

noncomputable def ep82 := @Enclosure.Real.IsNear.sin_image qz25 qz287 Bool.false 40932011 524288 15 16384 Bool.false 236601 524288 1 77790 (@Enclosure.Real.IsNear.recentre' qz25 Bool.false 1279125351 16384000 2961 3241250 40932011 524288 15 16384 (@Enclosure.Real.IsNear.mulLit_ff qz17 qz28 71064 1000 0 1 287994 262144 1 77790 1279125351 16384000 2961 3241250 qz22 qz288 rfl) rfl) (Enclosure.sfrac_false_div 40932011 524288) (BSN.sin_reduce1 qz287 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 83309738332358161989632) qz29) 226375608064910080 72057594037927936 Bool.false 236601 524288 12 1000000000000000 155580 77790 (BSN.sin_reduce_arg_pos_rat_q1 40932011 524288 226375608064910080 72057594037927936 12 83309738332358161989632 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 236601 524288 83309738332358161989632 75557863725914323419136 1183902587 1073741824 155732 155580 (ep81 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz289 := (@Enclosure.Real.IsNear.recentre' qz24 Bool.false 302698 524288 2 524288 151349 262144 1 262144 (ep68 rfl rfl) rfl)

noncomputable def ep83 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz24 (Real.cos qz25)) (@HMul.hMul Real Real Real qz0 qz24 (@Neg.neg Real Real.instNeg (Real.sin qz25))) Bool.true 8851343567 17179869184 24029308539 44547400794112 Bool.true 35809324749 137438953472 191634803353 356379206352896 (@Enclosure.Real.IsNear.mulLit_ft qz24 (Real.cos qz25) 151349 262144 1 262144 58483 65536 591617 637255680 8851343567 17179869184 24029308539 44547400794112 qz289 (@Enclosure.Real.IsNear.recentre' (Real.cos qz25) Bool.true 467864 524288 1183234 1274511360 58483 65536 591617 637255680 (ep76 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz24 (@Neg.neg Real Real.instNeg (Real.sin qz25)) 151349 262144 1 262144 236601 524288 591617 637255680 35809324749 137438953472 191634803353 356379206352896 qz289 (@Enclosure.Real.IsNear.neg (Real.sin qz25) Bool.false 236601 524288 591617 637255680 (@Enclosure.Real.IsNear.recentre' (Real.sin qz25) Bool.false 236601 524288 1183234 1274511360 236601 524288 591617 637255680 (ep82 rfl rfl) rfl)) rfl)

noncomputable def ep84 := @ep49 8851343567 17179869184 24029308539 44547400794112 Bool.true 35809324749 137438953472 191634803353 356379206352896 Bool.false 127238111122696437760 14812465655 17179869184 320184198623 267284404764672 Bool.false 1593393135104336855040 46373843655 137438953472 640104930295 534568809529344 (ep50 (BSN.head_sum_c_succ qz6 2 3 rfl rfl) (ep66 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep67 ep83) rfl rfl

noncomputable abbrev qz290 := (@Nat.cast Real Real.instNatCast 4)

noncomputable abbrev qz30 := (@Inv.inv Real Real.instInv (Real.sqrt qz290))

noncomputable abbrev qz31 := (@HMul.hMul Real Real Real qz262 qz275 (Real.log (Enclosure.sfrac Bool.false 4 1)))

noncomputable def ep85 := @Enclosure.Complex.IsNear.of_eq qz11 (Complex.mk (@HMul.hMul Real Real Real qz0 qz30 (Real.cos qz31)) (@HMul.hMul Real Real Real qz0 qz30 (@Neg.neg Real Real.instNeg (Real.sin qz31)))) Bool.true 59130285795 274877906944 4971616449811 10691376190586880 Bool.false 31017021903 68719476736 1245312870079 2672844047646720 (BSN.cpow_neg_s_mk qz17 71064 1000 4 qz18 rfl)

noncomputable def ep86 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz290) 1048577 524288 1 524288 131071 131072 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz290) (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz290 qz19)) Bool.false 1048577 524288 1 524288 (BSN.sqrt_natCast_div_one 4) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz290 qz19)) Bool.false 1048577 524288 1 524288 1048577 524288 1 524288 (BSN.sqrt_enclosure 4 1 524288 524289 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep87 := nat_lit 471225594319403171539306640625

noncomputable def ep88 := nat_lit 73155514365408823868279100600

noncomputable def ep89 := BSN.log_dyadic_bound 3 5 13 12 ep87 262144 77790 ep88 89313862490502916491225 363408 8 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base12 (BSN.artanhP 3) (BSN.artanhQ 5) 0 12 ep88 ep87 89313862490502916491225 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep90 := nat_lit 4776935125604045407146314344810303075037629524492001184934511568014784190625

noncomputable def ep91 := nat_lit 4567202976954300216483469128894856568274804766483030391978833477875390625

noncomputable def ep92 := nat_lit 14321670970858227621005976096173119511976338963943037494019577037088601790625

noncomputable def ep93 := BSN.cos_dyadic_bound_f 1209083485 1073741824 3 2 524288 155732 ep90 ep78 ep91 ep92 ep80 ep91 225565 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1209083485) qz283 0 2 ep90 ep78 ep91 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1209083485) qz284 0 2 ep92 ep80 ep91 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz32 := (Real.log (Enclosure.sfrac Bool.false 4 1))

noncomputable abbrev qz291 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 12912613) (@Nat.cast Real Real.instNatCast 131072))

noncomputable abbrev qz292 := (BSN.isNear_log_sfrac 4 1 363408 262144 1 77790 Bool.false (BSN.logfrac_isNear 8 2 1 4 1 363408 262144 77790 rfl rfl rfl (ep89 rfl)))

noncomputable abbrev qz293 := (@Nat.cast Real Real.instNatCast 18889465931478580854784)

noncomputable def ep94 := @Enclosure.Real.IsNear.cos_image qz31 qz291 Bool.false 12912613 131072 15 16384 Bool.true 225565 524288 1 77790 (@Enclosure.Real.IsNear.recentre' qz31 Bool.false 201759579 2048000 2961 3241250 12912613 131072 15 16384 (@Enclosure.Real.IsNear.mulLit_ff qz17 qz32 71064 1000 0 1 363408 262144 1 77790 201759579 2048000 2961 3241250 qz22 qz292 rfl) rfl) (Enclosure.sfrac_false_div 12912613 131072) (BSN.cos_reduce2 qz291 (@HDiv.hDiv Real Real Real qz2 qz281 qz293) 226375608064910080 72057594037927936 Bool.false 225565 524288 15 1000000000000000 155580 77790 (BSN.sin_reduce_arg_pos_rat_q2 12912613 131072 226375608064910080 72057594037927936 15 21270421628140090556416 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 225565 524288 21270421628140090556416 18889465931478580854784 1209083485 1073741824 155732 155580 (ep93 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep95 := nat_lit 8594829463705718292690179045355429649813113300272415708568537755644311230625

noncomputable def ep96 := nat_lit 22502873123933240947171400454484105029352375626329640044663918867723302590625

noncomputable def ep97 := BSN.sin_dyadic_bound_f 1209083485 1073741824 3 2 524288 155732 ep95 ep71 ep91 ep96 ep74 ep91 473284 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1209083485) qz277 0 2 ep95 ep71 ep91 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1209083485) qz278 0 2 ep96 ep74 ep91 rfl rfl rfl rfl) rfl rfl

noncomputable def ep98 := @Enclosure.Real.IsNear.sin_image qz31 qz291 Bool.false 12912613 131072 15 16384 Bool.true 473284 524288 1 77790 (@Enclosure.Real.IsNear.recentre' qz31 Bool.false 201759579 2048000 2961 3241250 12912613 131072 15 16384 (@Enclosure.Real.IsNear.mulLit_ff qz17 qz32 71064 1000 0 1 363408 262144 1 77790 201759579 2048000 2961 3241250 qz22 qz292 rfl) rfl) (Enclosure.sfrac_false_div 12912613 131072) (BSN.sin_reduce2 qz291 (@HDiv.hDiv Real Real Real qz2 qz281 qz293) 226375608064910080 72057594037927936 Bool.false 473284 524288 15 1000000000000000 155580 77790 (BSN.sin_reduce_arg_pos_rat_q2 12912613 131072 226375608064910080 72057594037927936 15 21270421628140090556416 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 473284 524288 21270421628140090556416 18889465931478580854784 1209083485 1073741824 155732 155580 (ep97 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz294 := (@Enclosure.Real.IsNear.recentre' qz30 Bool.false 262143 524288 1 524288 262143 524288 1 524288 (ep86 rfl rfl) rfl)

noncomputable def ep99 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz30 (Real.cos qz31)) (@HMul.hMul Real Real Real qz0 qz30 (@Neg.neg Real Real.instNeg (Real.sin qz31))) Bool.true 59130285795 274877906944 4971616449811 10691376190586880 Bool.false 31017021903 68719476736 1245312870079 2672844047646720 (@Enclosure.Real.IsNear.mulLit_ft qz30 (Real.cos qz31) 262143 524288 1 524288 225565 524288 591617 637255680 59130285795 274877906944 4971616449811 10691376190586880 qz294 (@Enclosure.Real.IsNear.recentre' (Real.cos qz31) Bool.true 225565 524288 1183234 1274511360 225565 524288 591617 637255680 (ep94 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz30 (@Neg.neg Real Real.instNeg (Real.sin qz31)) 262143 524288 1 524288 118321 131072 591617 637255680 31017021903 68719476736 1245312870079 2672844047646720 qz294 (@Enclosure.Real.IsNear.neg (Real.sin qz31) Bool.true 118321 131072 591617 637255680 (@Enclosure.Real.IsNear.recentre' (Real.sin qz31) Bool.true 473284 524288 1183234 1274511360 118321 131072 591617 637255680 (ep98 rfl rfl) rfl)) rfl)

noncomputable def ep100 := @ep47 59130285795 274877906944 4971616449811 10691376190586880 Bool.false 31017021903 68719476736 1245312870079 2672844047646720 Bool.false 3055768981155652567040 177869164685 274877906944 5926328131577 3563792063528960 Bool.false 7449733300375095607296 108407887461 137438953472 740972920259 445474007941120 (ep48 (BSN.head_sum_c_succ qz6 3 4 rfl rfl) (ep84 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep85 ep99) rfl rfl

noncomputable abbrev qz295 := (@Nat.cast Real Real.instNatCast 5)

noncomputable abbrev qz33 := (@Inv.inv Real Real.instInv (Real.sqrt qz295))

noncomputable abbrev qz34 := (@HMul.hMul Real Real Real qz262 qz275 (Real.log (Enclosure.sfrac Bool.false 5 1)))

noncomputable def ep101 := @Enclosure.Complex.IsNear.of_eq qz10 (Complex.mk (@HMul.hMul Real Real Real qz0 qz33 (Real.cos qz34)) (@HMul.hMul Real Real Real qz0 qz33 (@Neg.neg Real Real.instNeg (Real.sin qz34)))) Bool.false 35760508473 274877906944 888971632879 2138275238117376 Bool.true 117612698497 274877906944 891687250663 2138275238117376 (BSN.cpow_neg_s_mk qz17 71064 1000 5 qz18 rfl)

noncomputable def ep102 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz295) 1172343 524288 1 524288 117234 117235 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz295) (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz295 qz19)) Bool.false 1172343 524288 1 524288 (BSN.sqrt_natCast_div_one 5) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz295 qz19)) Bool.false 1172343 524288 1 524288 1172343 524288 1 524288 (BSN.sqrt_enclosure 5 1 586171 586172 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep103 := nat_lit 39510257877627786146545168145625

noncomputable def ep104 := nat_lit 8181717556663416291180905432700

noncomputable def ep105 := nat_lit 6646766139202842132480000

noncomputable def ep106 := BSN.log_dyadic_bound 2 3 16 15 ep103 262144 77790 ep104 ep105 421904 5 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base15 (BSN.artanhP 2) (BSN.artanhQ 3) 0 15 ep104 ep103 ep105 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep107 := nat_lit 7871998137325546871643621461138565120899551821646363412366355313962120191521

noncomputable def ep108 := nat_lit 12387524828740246826213978445790713069340339636200915644585198173387038241

noncomputable def ep109 := nat_lit 23591219362319160121278436426524113936559974785666688405809895545539586498081

noncomputable def ep110 := BSN.cos_dyadic_bound_f 1369692467 1073741824 3 2 524288 155732 ep107 ep78 ep108 ep109 ep80 ep108 152517 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1369692467) qz283 0 2 ep107 ep78 ep108 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1369692467) qz284 0 2 ep109 ep80 ep108 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz35 := (Real.log (Enclosure.sfrac Bool.false 5 1))

noncomputable abbrev qz296 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 59964371) qz27)

noncomputable abbrev qz297 := (BSN.isNear_log_sfrac 5 1 421904 262144 1 77790 Bool.false (BSN.logfrac_isNear 5 1 2 5 1 421904 262144 77790 rfl rfl rfl (ep106 rfl)))

noncomputable def ep111 := @Enclosure.Real.IsNear.cos_image qz34 qz296 Bool.false 59964371 524288 15 16384 Bool.false 152517 524288 1 77790 (@Enclosure.Real.IsNear.recentre' qz34 Bool.false 234235827 2048000 2961 3241250 59964371 524288 15 16384 (@Enclosure.Real.IsNear.mulLit_ff qz17 qz35 71064 1000 0 1 421904 262144 1 77790 234235827 2048000 2961 3241250 qz22 qz297 rfl) rfl) (Enclosure.sfrac_false_div 59964371 524288) (BSN.cos_reduce0 qz296 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 96383538833636177477632) qz29) 226375608064910080 72057594037927936 Bool.false 152517 524288 18 1000000000000000 155580 77790 (BSN.sin_reduce_arg_pos_rat_q0 59964371 524288 226375608064910080 72057594037927936 18 96383538833636177477632 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 152517 524288 96383538833636177477632 75557863725914323419136 1369692467 1073741824 155732 155580 (ep110 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep112 := nat_lit 14159686627322992171497547447292784647163721007254493409743771406593106714145

noncomputable def ep113 := nat_lit 37064837555170828620965420682568870064268908754826966971618644315463129046561

noncomputable def ep114 := BSN.sin_dyadic_bound_f 1369692467 1073741824 3 2 524288 155732 ep112 ep71 ep108 ep113 ep74 ep108 501613 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1369692467) qz277 0 2 ep112 ep71 ep108 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1369692467) qz278 0 2 ep113 ep74 ep108 rfl rfl rfl rfl) rfl rfl

noncomputable def ep115 := @Enclosure.Real.IsNear.sin_image qz34 qz296 Bool.false 59964371 524288 15 16384 Bool.false 501613 524288 1 77790 (@Enclosure.Real.IsNear.recentre' qz34 Bool.false 234235827 2048000 2961 3241250 59964371 524288 15 16384 (@Enclosure.Real.IsNear.mulLit_ff qz17 qz35 71064 1000 0 1 421904 262144 1 77790 234235827 2048000 2961 3241250 qz22 qz297 rfl) rfl) (Enclosure.sfrac_false_div 59964371 524288) (BSN.sin_reduce0 qz296 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 96383538833636177477632) qz29) 226375608064910080 72057594037927936 Bool.false 501613 524288 18 1000000000000000 155580 77790 (BSN.sin_reduce_arg_pos_rat_q0 59964371 524288 226375608064910080 72057594037927936 18 96383538833636177477632 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 501613 524288 96383538833636177477632 75557863725914323419136 1369692467 1073741824 155732 155580 (ep114 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz298 := (@Enclosure.Real.IsNear.recentre' qz33 Bool.false 234469 524288 1 524288 234469 524288 1 524288 (ep102 rfl rfl) rfl)

noncomputable def ep116 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz33 (Real.cos qz34)) (@HMul.hMul Real Real Real qz0 qz33 (@Neg.neg Real Real.instNeg (Real.sin qz34))) Bool.false 35760508473 274877906944 888971632879 2138275238117376 Bool.true 117612698497 274877906944 891687250663 2138275238117376 (@Enclosure.Real.IsNear.mulLit_ff qz33 (Real.cos qz34) 234469 524288 1 524288 152517 524288 591617 637255680 35760508473 274877906944 888971632879 2138275238117376 qz298 (@Enclosure.Real.IsNear.recentre' (Real.cos qz34) Bool.false 152517 524288 1183234 1274511360 152517 524288 591617 637255680 (ep111 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz33 (@Neg.neg Real Real.instNeg (Real.sin qz34)) 234469 524288 1 524288 501613 524288 591617 637255680 117612698497 274877906944 891687250663 2138275238117376 qz298 (@Enclosure.Real.IsNear.neg (Real.sin qz34) Bool.false 501613 524288 591617 637255680 (@Enclosure.Real.IsNear.recentre' (Real.sin qz34) Bool.false 501613 524288 1183234 1274511360 501613 524288 591617 637255680 (ep115 rfl rfl) rfl)) rfl)

noncomputable def ep117 := @ep45 35760508473 274877906944 888971632879 2138275238117376 Bool.true 117612698497 274877906944 891687250663 2138275238117376 Bool.false 58722077418801858609152 106814836579 137438953472 11111921279563 5345688095293440 Bool.false 13634367005054835097600 99203076425 274877906944 22241786339531 10691376190586880 (ep46 (BSN.head_sum_c_succ qz6 4 5 rfl rfl) (ep100 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep101 ep116) rfl rfl

noncomputable abbrev qz299 := (@Nat.cast Real Real.instNatCast 6)

noncomputable abbrev qz36 := (@Inv.inv Real Real.instInv (Real.sqrt qz299))

noncomputable abbrev qz37 := (@HMul.hMul Real Real Real qz262 qz275 (Real.log (Enclosure.sfrac Bool.false 6 1)))

noncomputable def ep118 := @Enclosure.Complex.IsNear.of_eq qz9 (Complex.mk (@HMul.hMul Real Real Real qz0 qz36 (Real.cos qz37)) (@HMul.hMul Real Real Real qz0 qz36 (@Neg.neg Real Real.instNeg (Real.sin qz37)))) Bool.true 10647370055 274877906944 810817063507 2138275238117376 Bool.true 55855831479 137438953472 407245064195 1069137619058688 (BSN.cpow_neg_s_mk qz17 71064 1000 6 qz18 rfl)

noncomputable abbrev qz300 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 6) qz19)

noncomputable def ep119 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz299) 1284239 524288 1 524288 107019 107020 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz299) (Real.sqrt qz300) Bool.false 1284239 524288 1 524288 (BSN.sqrt_natCast_div_one 6) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz300) Bool.false 1284239 524288 1 524288 1284239 524288 1 524288 (BSN.sqrt_enclosure 6 1 642119 642120 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep120 := BSN.log_dyadic_bound 2 10 4 3 105000000 262144 77790 1434560 960 106290 12 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 2) (BSN.artanhQ 10) 0 3 1434560 105000000 960 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz38 := (Real.log (Enclosure.sfrac Bool.false 6 1))

noncomputable def ep121 := @Enclosure.Real.IsNear.mulLit_ff qz17 qz38 71064 1000 0 1 4034681531866359 2251799813685248 50000000007779 3889500000000000000 35840076047568866997 281474976710656000 148050000023033619 162062500000000000000 qz22 (BSN.isNear_log_sfrac 6 1 4034681531866359 2251799813685248 50000000007779 3889500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz300) Bool.false 16922680887833197019136 9444732965739290427392 1000000000155580 77790000000000000000 4034681531866359 2251799813685248 50000000007779 3889500000000000000 (BSN.log_rat_reduce_isNear 6 1 2 12 8 106290 262144 24973259072661432 36028797018963968 77790 1000000000000000 rfl rfl rfl rfl (ep120 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep122 := BSN.sin_dyadic_bound_f 102031705 1073741824 1 0 524288 155732 0 1 1 0 1 1 49745 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 102031705) qz277 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 102031705) qz278 0 0 rfl) rfl rfl

noncomputable abbrev qz301 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 66757343) qz27)

noncomputable def ep123 := @Enclosure.Real.IsNear.cos_image qz37 qz301 Bool.false 66757343 524288 15 16384 Bool.true 49745 524288 1 77790 (@Enclosure.Real.IsNear.recentre' qz37 Bool.false 35840076047568866997 281474976710656000 148050000023033619 162062500000000000000 66757343 524288 15 16384 (ep121 rfl) rfl) (Enclosure.sfrac_false_div 66757343 524288) (BSN.cos_reduce1 qz301 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 7179842997438807801856) qz29) 226375608064910080 72057594037927936 Bool.false 49745 524288 20 1000000000000000 155580 77790 (BSN.sin_reduce_arg_pos_rat_q1 66757343 524288 226375608064910080 72057594037927936 20 7179842997438807801856 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 49745 524288 7179842997438807801856 75557863725914323419136 102031705 1073741824 155732 155580 (ep122 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep124 := nat_lit 108377861160607335242034109350625

noncomputable def ep125 := BSN.cos_dyadic_bound_f 102031705 1073741824 2 1 524288 155732 ep124 ep61 ep124 ep124 ep62 ep124 521922 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 102031705) qz283 0 1 ep124 ep61 ep124 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 102031705) qz284 0 1 ep124 ep62 ep124 rfl rfl rfl rfl) rfl rfl

noncomputable def ep126 := @Enclosure.Real.IsNear.sin_image qz37 qz301 Bool.false 66757343 524288 15 16384 Bool.false 521922 524288 1 77790 (@Enclosure.Real.IsNear.recentre' qz37 Bool.false 35840076047568866997 281474976710656000 148050000023033619 162062500000000000000 66757343 524288 15 16384 (ep121 rfl) rfl) (Enclosure.sfrac_false_div 66757343 524288) (BSN.sin_reduce1 qz301 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 7179842997438807801856) qz29) 226375608064910080 72057594037927936 Bool.false 521922 524288 20 1000000000000000 155580 77790 (BSN.sin_reduce_arg_pos_rat_q1 66757343 524288 226375608064910080 72057594037927936 20 7179842997438807801856 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 521922 524288 7179842997438807801856 75557863725914323419136 102031705 1073741824 155732 155580 (ep125 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz302 := (@Enclosure.Real.IsNear.recentre' qz36 Bool.false 214039 524288 1 524288 214039 524288 1 524288 (ep119 rfl rfl) rfl)

noncomputable def ep127 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz36 (Real.cos qz37)) (@HMul.hMul Real Real Real qz0 qz36 (@Neg.neg Real Real.instNeg (Real.sin qz37))) Bool.true 10647370055 274877906944 810817063507 2138275238117376 Bool.true 55855831479 137438953472 407245064195 1069137619058688 (@Enclosure.Real.IsNear.mulLit_ft qz36 (Real.cos qz37) 214039 524288 1 524288 49745 524288 591617 637255680 10647370055 274877906944 810817063507 2138275238117376 qz302 (@Enclosure.Real.IsNear.recentre' (Real.cos qz37) Bool.true 49745 524288 1183234 1274511360 49745 524288 591617 637255680 (ep123 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz36 (@Neg.neg Real Real.instNeg (Real.sin qz37)) 214039 524288 1 524288 260961 262144 591617 637255680 55855831479 137438953472 407245064195 1069137619058688 qz302 (@Enclosure.Real.IsNear.neg (Real.sin qz37) Bool.false 260961 262144 591617 637255680 (@Enclosure.Real.IsNear.recentre' (Real.sin qz37) Bool.false 521922 524288 1183234 1274511360 260961 262144 591617 637255680 (ep126 rfl rfl) rfl)) rfl)

noncomputable def ep128 := @ep43 10647370055 274877906944 810817063507 2138275238117376 Bool.true 55855831479 137438953472 407245064195 1069137619058688 Bool.false 27897675311812618223616 202982303103 274877906944 26277927876661 10691376190586880 Bool.true 1719167042509472792576 12508586533 274877906944 26314236981481 10691376190586880 (ep44 (BSN.head_sum_c_succ qz6 5 6 rfl rfl) (ep117 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep118 ep127) rfl rfl

noncomputable abbrev qz303 := (@Nat.cast Real Real.instNatCast 7)

noncomputable abbrev qz39 := (@Inv.inv Real Real.instInv (Real.sqrt qz303))

noncomputable abbrev qz40 := (@HMul.hMul Real Real Real qz262 qz275 (Real.log (Enclosure.sfrac Bool.false 7 1)))

noncomputable def ep129 := @Enclosure.Complex.IsNear.of_eq qz8 (Complex.mk (@HMul.hMul Real Real Real qz0 qz39 (Real.cos qz40)) (@HMul.hMul Real Real Real qz0 qz39 (@Neg.neg Real Real.instNeg (Real.sin qz40)))) Bool.false 12967984883 34359738368 471494092447 1336422023823360 Bool.true 5589980067 274877906944 3752687307071 10691376190586880 (BSN.cpow_neg_s_mk qz17 71064 1000 7 qz18 rfl)

noncomputable abbrev qz304 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 7) qz19)

noncomputable def ep130 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz303) 1387135 524288 1 524288 99081 99082 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz303) (Real.sqrt qz304) Bool.false 1387135 524288 1 524288 (BSN.sqrt_natCast_div_one 7) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz304) Bool.false 1387135 524288 1 524288 1387135 524288 1 524288 (BSN.sqrt_enclosure 7 1 693567 693568 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep131 := BSN.log_dyadic_bound 3 11 5 4 202569142545 262144 77790 5259111624 688905 146699 14 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 3) (BSN.artanhQ 11) 0 4 5259111624 202569142545 688905 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz41 := (Real.log (Enclosure.sfrac Bool.false 7 1))

noncomputable def ep132 := @Enclosure.Real.IsNear.mulLit_ff qz17 qz41 71064 1000 0 1 4381792198794487 2251799813685248 50000000007779 3889500000000000000 38923460101891428021 281474976710656000 148050000023033619 162062500000000000000 qz22 (BSN.isNear_log_sfrac 7 1 4381792198794487 2251799813685248 50000000007779 3889500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz304) Bool.false 18378568546572512002048 9444732965739290427392 1000000000155580 77790000000000000000 4381792198794487 2251799813685248 50000000007779 3889500000000000000 (BSN.log_rat_reduce_isNear 7 1 2 14 8 146699 262144 24973259072661432 36028797018963968 77790 1000000000000000 rfl rfl rfl rfl (ep131 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep133 := BSN.cos_dyadic_bound_f 57801762 1073741824 1 0 524288 155732 0 1 1 0 1 1 523528 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 57801762) qz283 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 57801762) qz284 0 0 rfl) rfl rfl

noncomputable abbrev qz305 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 36250297) qz20)

noncomputable def ep134 := @Enclosure.Real.IsNear.cos_image qz40 qz305 Bool.false 36250297 262144 15 16384 Bool.false 523528 524288 1 77790 (@Enclosure.Real.IsNear.recentre' qz40 Bool.false 38923460101891428021 281474976710656000 148050000023033619 162062500000000000000 36250297 262144 15 16384 (ep132 rfl) rfl) (Enclosure.sfrac_false_div 36250297 262144) (BSN.cos_reduce0 qz305 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 2033718710668544180224) qz282) 226375608064910080 72057594037927936 Bool.false 523528 524288 22 1000000000000000 155580 77790 (BSN.sin_reduce_arg_pos_rat_q0 36250297 262144 226375608064910080 72057594037927936 22 2033718710668544180224 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 523528 524288 2033718710668544180224 37778931862957161709568 57801762 1073741824 155732 155580 (ep133 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep135 := BSN.sin_dyadic_bound_f 57801762 1073741824 1 0 524288 155732 0 1 1 0 1 1 28209 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 57801762) qz277 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 57801762) qz278 0 0 rfl) rfl rfl

noncomputable def ep136 := @Enclosure.Real.IsNear.sin_image qz40 qz305 Bool.false 36250297 262144 15 16384 Bool.false 28209 524288 1 77790 (@Enclosure.Real.IsNear.recentre' qz40 Bool.false 38923460101891428021 281474976710656000 148050000023033619 162062500000000000000 36250297 262144 15 16384 (ep132 rfl) rfl) (Enclosure.sfrac_false_div 36250297 262144) (BSN.sin_reduce0 qz305 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 2033718710668544180224) qz282) 226375608064910080 72057594037927936 Bool.false 28209 524288 22 1000000000000000 155580 77790 (BSN.sin_reduce_arg_pos_rat_q0 36250297 262144 226375608064910080 72057594037927936 22 2033718710668544180224 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 28209 524288 2033718710668544180224 37778931862957161709568 57801762 1073741824 155732 155580 (ep135 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz306 := (@Enclosure.Real.IsNear.recentre' qz39 Bool.false 198163 524288 1 524288 198163 524288 1 524288 (ep130 rfl rfl) rfl)

noncomputable def ep137 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz39 (Real.cos qz40)) (@HMul.hMul Real Real Real qz0 qz39 (@Neg.neg Real Real.instNeg (Real.sin qz40))) Bool.false 12967984883 34359738368 471494092447 1336422023823360 Bool.true 5589980067 274877906944 3752687307071 10691376190586880 (@Enclosure.Real.IsNear.mulLit_ff qz39 (Real.cos qz40) 198163 524288 1 524288 65441 65536 591617 637255680 12967984883 34359738368 471494092447 1336422023823360 qz306 (@Enclosure.Real.IsNear.recentre' (Real.cos qz40) Bool.false 523528 524288 1183234 1274511360 65441 65536 591617 637255680 (ep134 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz39 (@Neg.neg Real Real.instNeg (Real.sin qz40)) 198163 524288 1 524288 28209 524288 591617 637255680 5589980067 274877906944 3752687307071 10691376190586880 qz306 (@Enclosure.Real.IsNear.neg (Real.sin qz40) Bool.false 28209 524288 591617 637255680 (@Enclosure.Real.IsNear.recentre' (Real.sin qz40) Bool.false 28209 524288 1183234 1274511360 28209 524288 591617 637255680 (ep136 rfl rfl) rfl)) rfl)

noncomputable def ep138 := @ep41 12967984883 34359738368 471494092447 1336422023823360 Bool.true 5589980067 274877906944 3752687307071 10691376190586880 Bool.false 10539031369873627283456 306726182167 274877906944 10016626872079 3563792063528960 Bool.true 4974896105694586470400 2262320825 34359738368 1252788512023 445474007941120 (ep42 (BSN.head_sum_c_succ qz6 6 7 rfl rfl) (ep128 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep129 ep137) rfl rfl

noncomputable abbrev qz307 := (@Nat.cast Real Real.instNatCast 8)

noncomputable abbrev qz42 := (@Inv.inv Real Real.instInv (Real.sqrt qz307))

noncomputable abbrev qz43 := (@HMul.hMul Real Real Real qz262 qz275 (Real.log (Enclosure.sfrac Bool.false 8 1)))

noncomputable def ep139 := @Enclosure.Complex.IsNear.of_eq qz7 (Complex.mk (@HMul.hMul Real Real Real qz0 qz42 (Real.cos qz43)) (@HMul.hMul Real Real Real qz0 qz42 (@Neg.neg Real Real.instNeg (Real.sin qz43)))) Bool.true 48250544989 137438953472 587050505401 1781896031764480 Bool.false 11496769349 274877906944 1168155482207 3563792063528960 (BSN.cpow_neg_s_mk qz17 71064 1000 8 qz18 rfl)

noncomputable abbrev qz308 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 8) qz19)

noncomputable def ep140 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz307) 1482911 524288 1 524288 92681 92682 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz307) (Real.sqrt qz308) Bool.false 1482911 524288 1 524288 (BSN.sqrt_natCast_div_one 8) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz308) Bool.false 1482911 524288 1 524288 1482911 524288 1 524288 (BSN.sqrt_enclosure 8 1 741455 741456 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep141 := BSN.log_dyadic_bound 0 16 1 0 1 262144 77790 0 1 0 16 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 0) (BSN.artanhQ 16) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz44 := (Real.log (Enclosure.sfrac Bool.false 8 1))

noncomputable def ep142 := @Enclosure.Real.IsNear.mulLit_ff qz17 qz44 71064 1000 0 1 9364972152248037 4503599627370496 100000000023337 7779000000000000000 83189047628419312671 562949953421312000 296100000069100857 324125000000000000000 qz22 (BSN.isNear_log_sfrac 8 1 9364972152248037 4503599627370496 100000000023337 7779000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz308) Bool.false 19639770079031275290624 9444732965739290427392 1000000000233370 77790000000000000000 9364972152248037 4503599627370496 100000000023337 7779000000000000000 (BSN.log_rat_reduce_isNear 8 1 3 16 16 0 262144 24973259072661432 36028797018963968 77790 1000000000000000 rfl rfl rfl rfl (ep141 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep143 := nat_lit 262802875264340309920559314400625

noncomputable def ep144 := BSN.cos_dyadic_bound_f 127323195 1073741824 2 1 524288 155732 ep143 ep61 ep143 ep143 ep62 ep143 520606 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 127323195) qz283 0 1 ep143 ep61 ep143 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 127323195) qz284 0 1 ep143 ep62 ep143 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz309 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 38737919) qz20)

noncomputable def ep145 := @Enclosure.Real.IsNear.cos_image qz43 qz309 Bool.false 38737919 262144 479 524288 Bool.true 520606 524288 1 77790 (@Enclosure.Real.IsNear.recentre' qz43 Bool.false 83189047628419312671 562949953421312000 296100000069100857 324125000000000000000 38737919 262144 479 524288 (ep142 rfl) rfl) (Enclosure.sfrac_false_div 38737919 262144) (BSN.cos_reduce2 qz309 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 4479786698898552127488) qz282) 226375608064910080 72057594037927936 Bool.false 520606 524288 23 1000000000000000 155580 77790 (BSN.sin_reduce_arg_pos_rat_q2 38737919 262144 226375608064910080 72057594037927936 23 4479786698898552127488 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 520606 524288 4479786698898552127488 37778931862957161709568 127323195 1073741824 155732 155580 (ep144 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep146 := BSN.sin_dyadic_bound_f 127323195 1073741824 1 0 524288 155732 0 1 1 0 1 1 62023 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 127323195) qz277 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 127323195) qz278 0 0 rfl) rfl rfl

noncomputable def ep147 := @Enclosure.Real.IsNear.sin_image qz43 qz309 Bool.false 38737919 262144 479 524288 Bool.true 62023 524288 1 77790 (@Enclosure.Real.IsNear.recentre' qz43 Bool.false 83189047628419312671 562949953421312000 296100000069100857 324125000000000000000 38737919 262144 479 524288 (ep142 rfl) rfl) (Enclosure.sfrac_false_div 38737919 262144) (BSN.sin_reduce2 qz309 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 4479786698898552127488) qz282) 226375608064910080 72057594037927936 Bool.false 62023 524288 23 1000000000000000 155580 77790 (BSN.sin_reduce_arg_pos_rat_q2 38737919 262144 226375608064910080 72057594037927936 23 4479786698898552127488 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 62023 524288 4479786698898552127488 37778931862957161709568 127323195 1073741824 155732 155580 (ep146 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz310 := (@Enclosure.Real.IsNear.recentre' qz42 Bool.false 185363 524288 1 524288 185363 524288 1 524288 (ep140 rfl rfl) rfl)

noncomputable def ep148 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz42 (Real.cos qz43)) (@HMul.hMul Real Real Real qz0 qz42 (@Neg.neg Real Real.instNeg (Real.sin qz43))) Bool.true 48250544989 137438953472 587050505401 1781896031764480 Bool.false 11496769349 274877906944 1168155482207 3563792063528960 (@Enclosure.Real.IsNear.mulLit_ft qz42 (Real.cos qz43) 185363 524288 1 524288 260303 262144 18892849 20392181760 48250544989 137438953472 587050505401 1781896031764480 qz310 (@Enclosure.Real.IsNear.recentre' (Real.cos qz43) Bool.true 520606 524288 37785698 40784363520 260303 262144 18892849 20392181760 (ep145 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz42 (@Neg.neg Real Real.instNeg (Real.sin qz43)) 185363 524288 1 524288 62023 524288 18892849 20392181760 11496769349 274877906944 1168155482207 3563792063528960 qz310 (@Enclosure.Real.IsNear.neg (Real.sin qz43) Bool.true 62023 524288 18892849 20392181760 (@Enclosure.Real.IsNear.recentre' (Real.sin qz43) Bool.true 62023 524288 37785698 40784363520 62023 524288 18892849 20392181760 (ep147 rfl rfl) rfl)) rfl)

noncomputable def ep149 := @ep39 48250544989 137438953472 587050505401 1781896031764480 Bool.false 11496769349 274877906944 1168155482207 3563792063528960 Bool.false 28893116664010881630208 210225092189 274877906944 11190727882881 3563792063528960 Bool.true 226836026302941626368 6601797251 274877906944 11190463578391 3563792063528960 (ep40 (BSN.head_sum_c_succ qz6 7 8 rfl rfl) (ep138 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep139 ep148) rfl rfl

theorem EMRow18.d6 : Enclosure.Complex.IsNear qz4 Bool.false 210225092189 274877906944 11190727882881 3563792063528960 Bool.true 6601797251 274877906944 11190463578391 3563792063528960 := ep38 (BSN.head_sum_c_succ qz6 8 9 rfl rfl) (ep149 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

theorem EMRow18.d7 : @Eq Nat (BSN.factNat (Nat.mul 2 1)) 2 := @Eq.refl Nat 2

theorem EMRow18.d8 : @Eq Nat (Nat.pow 15 1) 15 := @Eq.refl Nat 15

noncomputable def ep150 := nat_lit 1379979700127255169487200353267

noncomputable def ep151 := nat_lit 682341563449173892115988480000

noncomputable def ep152 := nat_lit 6036021272253425049252519290810068973

noncomputable def ep153 := nat_lit 1032260663417281782874149111201792000000

noncomputable abbrev qz481 := (@instHMul Complex Complex.instMul)

noncomputable abbrev qz462 := qz481

noncomputable abbrev qz311 := qz462

noncomputable abbrev qz45 := qz311

noncomputable abbrev qz463 := (@instHSub Complex Complex.instSub)

noncomputable abbrev qz312 := qz463

noncomputable abbrev qz46 := qz312

noncomputable abbrev qz482 := (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (4 : Complex))

noncomputable abbrev qz483 := (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid))

noncomputable abbrev qz464 := (@HAdd.hAdd Complex Complex Complex qz479 (@HAdd.hAdd Complex Complex Complex qz479 qz482 (@HMul.hMul Complex Complex Complex qz481 Complex.I (@HDiv.hDiv Complex Complex Complex qz483 (↑qz480) (2 : Complex)))) (@Nat.cast Complex Complex.instNatCast 2))

noncomputable abbrev qz313 := qz464

noncomputable abbrev qz47 := (Complex.Stirling.logGammaStirling 1 qz313)

noncomputable abbrev qz465 := (@HAdd.hAdd Complex Complex Complex qz479 qz482 (@HMul.hMul Complex Complex Complex qz481 Complex.I (@HDiv.hDiv Complex Complex Complex qz483 (↑qz480) (2 : Complex))))

noncomputable abbrev qz314 := qz465

noncomputable abbrev qz48 := qz314

noncomputable abbrev qz49 := (@HMul.hMul Real Real Real qz262 (@HDiv.hDiv Real Real Real qz265 qz275 (2 : Real)) (Real.log Real.pi))

noncomputable abbrev qz315 := (@instHSub Real Real.instSub)

noncomputable def ep154 := Complex.re (@HMul.hMul Complex Complex Complex qz45 (Complex.exp (@HMul.hMul Complex Complex Complex qz45 Complex.I ↑(@HSub.hSub Real Real Real qz315 (Complex.im (@HSub.hSub Complex Complex Complex qz46 qz47 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz48 (@Nat.cast Complex Complex.instNatCast j))))) qz49))) (zetaApproximant qz6 1 15))

noncomputable def ep155 := @Enclosure.Real.IsNear.of_eq ep154 (@HSub.hSub Real Real Real qz315 (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz315 (Complex.im (@HSub.hSub Complex Complex Complex qz46 qz47 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz48 (@Nat.cast Complex Complex.instNatCast j))))) qz49)) (Complex.re (zetaApproximant qz6 1 15))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz315 (Complex.im (@HSub.hSub Complex Complex Complex qz46 qz47 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz48 (@Nat.cast Complex Complex.instNatCast j))))) qz49)) (Complex.im (zetaApproximant qz6 1 15))))

noncomputable def ep156 := nat_lit 4139954890990585952210015115937

noncomputable def ep157 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz315 (Complex.im (@HSub.hSub Complex Complex Complex qz46 qz47 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz48 (@Nat.cast Complex Complex.instNatCast j))))) qz49)) (Complex.re (zetaApproximant qz6 1 15))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz315 (Complex.im (@HSub.hSub Complex Complex Complex qz46 qz47 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz48 (@Nat.cast Complex Complex.instNatCast j))))) qz49)) (Complex.im (zetaApproximant qz6 1 15))) ep156

noncomputable def ep158 := nat_lit 2047024690347521676347965440000

noncomputable def ep159 := nat_lit 2005386103431014184080919254009800403

noncomputable def ep160 := nat_lit 344086887805760594291383037067264000000

noncomputable def ep161 := nat_lit 1973826102555468551757017

noncomputable def ep162 := nat_lit 255878086293440209543495680000

noncomputable def ep163 := nat_lit 4965740490095624252440382195166941

noncomputable def ep164 := nat_lit 258065165854320445718537277800448000000

noncomputable def ep165 := nat_lit 1059319694377072624719307550789990808970510560294265159680000

noncomputable def ep166 := @Enclosure.Real.IsNear.mulLit_ff (Real.cos (@HSub.hSub Real Real Real qz315 (Complex.im (@HSub.hSub Complex Complex Complex qz46 qz47 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz48 (@Nat.cast Complex Complex.instNatCast j))))) qz49)) (Complex.re (zetaApproximant qz6 1 15)) 524287 524288 8624569

noncomputable def ep167 := nat_lit 7896352362333199091737951

noncomputable def ep168 := nat_lit 3904389744467776634880000

noncomputable def ep169 := nat_lit 251618359642029861967184911

noncomputable def ep170 := nat_lit 50620413037024724071219200000

noncomputable def ep171 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HSub.hSub Real Real Real qz315 (Complex.im (@HSub.hSub Complex Complex Complex qz46 qz47 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz48 (@Nat.cast Complex Complex.instNatCast j))))) qz49)) Bool.false 524287 524288 17249138

noncomputable abbrev qz316 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 823553) (@Nat.cast Real Real.instNatCast 16384))

noncomputable def ep172 := @Enclosure.Real.IsNear.cos_image (@HSub.hSub Real Real Real qz315 (Complex.im (@HSub.hSub Complex Complex Complex qz46 qz47 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz48 (@Nat.cast Complex Complex.instNatCast j))))) qz49) qz316 Bool.false 823553 16384 215

noncomputable def ep173 := nat_lit 8496742400000000000000000

noncomputable def ep174 := @Enclosure.Real.IsNear.recentre' (@HSub.hSub Real Real Real qz315 (Complex.im (@HSub.hSub Complex Complex Complex qz46 qz47 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz48 (@Nat.cast Complex Complex.instNatCast j))))) qz49) Bool.false 56594131717019617069 1125899906842624000 3478469243543284912409 ep173

noncomputable def ep175 := @Enclosure.Real.IsNear.subLit_ff_p (Complex.im (@HSub.hSub Complex Complex Complex qz46 qz47 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz48 (@Nat.cast Complex Complex.instNatCast j))))) qz49 102389584242809980717 1125899906842624000 1175107343543284912409 ep173 666411543 16384000

noncomputable def ep176 := nat_lit 927238254051649406058496000

noncomputable def ep177 := nat_lit 84967424000000000000000000

noncomputable def ep178 := @Enclosure.Complex.IsNear.im_isNear (@HSub.hSub Complex Complex Complex qz46 qz47 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz48 (@Nat.cast Complex Complex.instNatCast j)))) Bool.true 25124331378284182251 450359962737049600 20753364277632699751659 ep177 Bool.false 102389584242809980717 1125899906842624000

noncomputable def ep179 := nat_lit 254902272000000000000000000

noncomputable def ep180 := @Enclosure.Complex.IsNear.subLitP qz47 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz48 (@Nat.cast Complex Complex.instNatCast j))) Bool.true 21908081204977669651 450359962737049600 60621692830349076534977 ep179 Bool.false 105879192190595848717 1125899906842624000 3197642030604364510027

noncomputable def ep181 := nat_lit 25490227200000000000000000

noncomputable def ep182 := nat_lit 56574964716586751681966198382133248

noncomputable def ep183 := nat_lit 28820105840158689874536407448420352

noncomputable abbrev qz484 := (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (2 : Complex))

noncomputable abbrev qz466 := qz484

noncomputable abbrev qz317 := (@HSub.hSub Complex Complex Complex qz463 qz464 qz466)

noncomputable abbrev qz318 := (Complex.log qz464)

noncomputable abbrev qz50 := (@HSub.hSub Complex Complex Complex qz312 (@HMul.hMul Complex Complex Complex qz311 qz317 qz318) qz313)

noncomputable abbrev qz319 := qz466

noncomputable abbrev qz51 := (@HMul.hMul Complex Complex Complex qz311 qz319 ↑(Real.log qz266))

noncomputable abbrev qz467 := qz483

noncomputable abbrev qz320 := qz467

noncomputable abbrev qz52 := qz320

noncomputable abbrev qz53 := (@instHMul Nat instMulNat)

noncomputable abbrev qz468 := (@instHPow Complex Int (@ZPow.toPow Complex (@DivInvMonoid.toZPow Complex Complex.instDivInvMonoid)))

noncomputable abbrev qz321 := qz468

noncomputable abbrev qz54 := qz321

noncomputable abbrev qz55 := qz313

noncomputable abbrev qz322 := (@OfNat.ofNat Int 1 (@instOfNat 1))

noncomputable abbrev qz56 := qz322

noncomputable abbrev qz323 := (@OfNat.ofNat Int 2 (@instOfNat 2))

noncomputable abbrev qz57 := qz323

noncomputable abbrev qz324 := (@instHSub Int Int.instSub)

noncomputable abbrev qz325 := (@instHMul Int Int.instMul)

noncomputable def ep184 := @Enclosure.Complex.IsNear.of_eq qz47 (@HAdd.hAdd Complex Complex Complex qz5 (@HAdd.hAdd Complex Complex Complex qz5 qz50 qz51) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz53 2 k))) (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz45 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz54 qz55 (@HSub.hSub Int Int Int qz324 qz56 (@HMul.hMul Int Int Int qz325 qz57 (@Nat.cast Int instNatCastInt k)))))) Bool.true 21908081204977669651

noncomputable def ep185 := @Enclosure.Complex.IsNear.addLitP (@HAdd.hAdd Complex Complex Complex qz5 qz50 qz51) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz53 2 k))) (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz45 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz54 qz55 (@HSub.hSub Int Int Int qz324 qz56 (@HMul.hMul Int Int Int qz325 qz57 (@Nat.cast Int instNatCastInt k))))) Bool.true 21908147821902239251 450359962737049600

noncomputable def ep186 := nat_lit 188188984586982727122673467392

noncomputable def ep187 := nat_lit 2273738338927538844964392796160

noncomputable def ep188 := @ep185 1850024530235564839 7779000000000000000000 Bool.false 4235272889071114261 45035996273704960 195160000277764753 1555800000000000000000 Bool.false 1270617 8589934592 3 8589934592 Bool.true 1254098979 536870912000 2961 536870912000 Bool.true ep186 21908081204977669651 450359962737049600 60621692830349076534977 ep179 Bool.false ep187

noncomputable def ep189 := @Enclosure.Complex.IsNear.addLitP qz50 qz51 Bool.true 22322000562623288851 450359962737049600 455087500051566991 1944750000000000000000

noncomputable def ep190 := nat_lit 2871544751312370303107072

noncomputable def ep191 := @ep189 Bool.false 4235272889071114261 45035996273704960 195160000277764753 1555800000000000000000 Bool.false 120447 131072 1 262144 Bool.false 0 1 0 1 Bool.true ep190 21908147821902239251 450359962737049600 1850024530235564839 7779000000000000000000 Bool.false 4235272889071114261 4235272889071114261 45035996273704960

noncomputable abbrev qz58 := (@HMul.hMul Complex Complex Complex qz311 qz317 qz318)

noncomputable def ep192 := @Enclosure.Complex.IsNear.subLitP qz58 qz55 Bool.true 21308690646464927251 450359962737049600 455087500051566991 1944750000000000000000 Bool.false 145887297716709972493

noncomputable def ep193 := @ep192 1125899906842624000 195160000277764753 1555800000000000000000 Bool.false 9000 4000 0 1 Bool.false 142128 4000 0 1 Bool.true 89288002250493155404000 22322000562623288851 450359962737049600 455087500051566991 1944750000000000000000 Bool.false 423527288907111426100000 4235272889071114261 45035996273704960 195160000277764753 1555800000000000000000

noncomputable abbrev qz59 := qz317

noncomputable abbrev qz60 := qz318

noncomputable def ep194 := @Enclosure.Complex.IsNear.mul qz59 qz60 Bool.true 21308690646464927251 450359962737049600 455087500051566991 1944750000000000000000 Bool.false 145887297716709972493 1125899906842624000 195160000277764753

noncomputable abbrev qz61 := (Complex.re qz317)

noncomputable abbrev qz62 := (Complex.re qz318)

noncomputable abbrev qz63 := (Complex.im qz317)

noncomputable abbrev qz64 := (Complex.im qz318)

noncomputable def ep195 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 qz61 qz62) (@HMul.hMul Real Real Real qz0 qz63 qz64) 112621685095200197 18014398509481984 35000000054453 6223200000000000000 1507764548365308261 28147497671065600

noncomputable def ep196 := nat_lit 23991452813793154971484601265946624

noncomputable def ep197 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz62 7000 4000 0 1 16088812156457171 4503599627370496 5000000007779 1555800000000000000

noncomputable def ep198 := @Enclosure.Complex.IsNear.re_isNear qz59 Bool.false 7000 4000 0 1 Bool.false 142128 4000 0 1

noncomputable abbrev qz326 := (Enclosure.sfrac Bool.false 142128 4000)

noncomputable abbrev qz65 := qz326

noncomputable def ep199 := @Enclosure.Complex.IsNear.of_eq qz59 (Complex.mk (Enclosure.sfrac Bool.false 7000 4000) qz65) Bool.false 7000 4000 0 1 Bool.false 142128 4000 0

noncomputable abbrev qz327 := (Enclosure.sfrac Bool.false 9000 4000)

noncomputable abbrev qz66 := (Complex.mk qz327 qz326)

noncomputable def ep200 := @Enclosure.Complex.IsNear.of_eq qz60 (Complex.log qz66) Bool.false 16088812156457171 4503599627370496 5000000007779 1555800000000000000 Bool.false 848679808828835 562949953421312 100000000007779 15558000000000000000

noncomputable def ep201 := nat_lit 27109123135287491785300952755309254845399040

noncomputable def ep202 := nat_lit 102791992466099399115793767317184066879488

noncomputable def ep203 := nat_lit 692160937229936618211308475804505079808

noncomputable def ep204 := BSN.log_dyadic_bound 3897368384 36665368384 3 2 ep201 524288 155580 ep202 ep203 111881 40562736768 32768000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 3897368384) (BSN.artanhQ 36665368384) 0 2 ep202 ep201 ep203 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz67 := (Enclosure.sfrac Bool.false 1 2)

noncomputable abbrev qz328 := (Real.log (Enclosure.sfrac Bool.false 20281368384 16000000))

noncomputable abbrev qz329 := (Enclosure.Real.IsNear.const Bool.false 1 2)

noncomputable abbrev qz330 := (@Nat.cast Real Real.instNatCast 16000000)

noncomputable def ep205 := @Enclosure.Real.IsNear.mulLit_ff qz67 qz328 1 2 0 1 16088812156457171 2251799813685248 5000000007779 777900000000000000 16088812156457171 4503599627370496 5000000007779 1555800000000000000 qz329 (BSN.isNear_log_sfrac 20281368384 16000000 16088812156457171 2251799813685248 5000000007779 777900000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 20281368384) qz330)) Bool.false 134962738366153876307968 18889465931478580854784 1000000001555800 155580000000000000000 16088812156457171 2251799813685248 5000000007779 777900000000000000 (BSN.log_rat_reduce_isNear 20281368384 16000000 10 40562736768 32768000000 111881 524288 24973259072661432 36028797018963968 155580 1000000000000000 rfl rfl rfl rfl (ep204 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep206 := BSN.arctan_dyadic_bound_f 9000 142128 1 0 524288 155580 0 1 1 0 1 1 33155 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 9000) (BSN.arctanEvenQ 142128) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 9000) (BSN.arctanOddQ 142128) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz68 := (@HMul.hMul Real Real Real qz262 (Enclosure.sfrac Bool.false 1 2) Real.pi)

noncomputable abbrev qz69 := (@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 2) Real.pi 1 2 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 qz329 BSN.pi_near_15 rfl)

noncomputable abbrev qz331 := (Real.arctan (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 9000) (@Nat.cast Real Real.instNatCast 142128)))

noncomputable def ep207 := @Enclosure.Real.IsNear.subLit_ff_p qz68 qz331 884279719003555 562949953421312 1 2000000000000000 33155 524288 1 155580 444952639611252244480 848679808828835 562949953421312 100000000007779 15558000000000000000 qz69 (ep206 rfl) rfl rfl

noncomputable abbrev qz332 := (Real.arctan (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 142128) (@Nat.cast Real Real.instNatCast 9000)))

noncomputable def ep208 := @Enclosure.Complex.IsNear.re_isNear qz60 Bool.false 16088812156457171 4503599627370496 5000000007779 1555800000000000000 Bool.false 848679808828835 562949953421312 100000000007779 15558000000000000000 (ep200 (@congrArg Complex Complex qz55 qz66 Complex.log (BSN.w_shift_mk qz17 Bool.false 71064 1000 2 qz18 rfl)) (@Enclosure.Complex.IsNear.of_parts (Complex.log qz66) Bool.false 16088812156457171 4503599627370496 5000000007779 1555800000000000000 Bool.false 848679808828835 562949953421312 100000000007779 15558000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re (Complex.log qz66)) (@HMul.hMul Real Real Real qz0 qz67 qz328) Bool.false 16088812156457171 4503599627370496 5000000007779 1555800000000000000 (Enclosure.clog_re_eq 9000 142128 4000 20281368384 16000000 rfl rfl rfl) (ep205 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im (Complex.log qz66)) qz332 Bool.false 848679808828835 562949953421312 100000000007779 15558000000000000000 (Enclosure.clog_im_eq 9000 142128 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz332 (@HSub.hSub Real Real Real qz315 qz68 qz331) Bool.false 848679808828835 562949953421312 100000000007779 15558000000000000000 (BSN.arctan_recip 142128 9000 rfl rfl) ep207))))

noncomputable def ep209 := @Enclosure.Real.IsNear.mulLit_ff qz63 qz64 142128 4000 0 1 848679808828835 562949953421312 100000000007779 15558000000000000000

noncomputable def ep210 := @Enclosure.Complex.IsNear.im_isNear qz59 Bool.false 7000 4000 0 1 Bool.false 142128 4000 0 1

noncomputable def ep211 := @Enclosure.Complex.IsNear.im_isNear qz60 Bool.false 16088812156457171 4503599627370496 5000000007779 1555800000000000000 Bool.false 848679808828835 562949953421312 100000000007779 15558000000000000000 (ep200 (@congrArg Complex Complex qz55 qz66 Complex.log (BSN.w_shift_mk qz17 Bool.false 71064 1000 2 qz18 rfl)) (@Enclosure.Complex.IsNear.of_parts (Complex.log qz66) Bool.false 16088812156457171 4503599627370496 5000000007779 1555800000000000000 Bool.false 848679808828835 562949953421312 100000000007779 15558000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re (Complex.log qz66)) (@HMul.hMul Real Real Real qz0 qz67 qz328) Bool.false 16088812156457171 4503599627370496 5000000007779 1555800000000000000 (Enclosure.clog_re_eq 9000 142128 4000 20281368384 16000000 rfl rfl rfl) (ep205 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im (Complex.log qz66)) qz332 Bool.false 848679808828835 562949953421312 100000000007779 15558000000000000000 (Enclosure.clog_im_eq 9000 142128 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz332 (@HSub.hSub Real Real Real qz315 qz68 qz331) Bool.false 848679808828835 562949953421312 100000000007779 15558000000000000000 (BSN.arctan_recip 142128 9000 rfl rfl) ep207))))

noncomputable abbrev qz333 := (Enclosure.Real.IsNear.const Bool.false 142128 4000)

noncomputable abbrev qz70 := (@ep199 1 (BSN.w_sub_half_mk qz275 Bool.false 71064 1000 2 qz276 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7000 4000) qz326 Bool.false 7000 4000 0 1 Bool.false 142128 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 7000 4000) qz333))

noncomputable def ep212 := @ep195 296100000023033619 1296500000000000000000 ep196 21308690646464927251 450359962737049600 455087500051566991 1944750000000000000000 (@ep197 112621685095200197 18014398509481984 35000000054453 6223200000000000000 (ep198 qz70) ep208 rfl) (@ep209 1507764548365308261 28147497671065600 296100000023033619 1296500000000000000000 (ep210 qz70) ep211 rfl) rfl

noncomputable def ep213 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz61 qz64) (@HMul.hMul Real Real Real qz0 qz63 qz62) 5940758661801845 2251799813685248 700000000054453 62232000000000000000 142916918385809049993 1125899906842624000

noncomputable def ep214 := nat_lit 328508989817531822020752619039883264

noncomputable def ep215 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz64 7000 4000 0 1 848679808828835 562949953421312 100000000007779 15558000000000000000

noncomputable def ep216 := @Enclosure.Real.IsNear.mulLit_ff qz63 qz62 142128 4000 0 1 16088812156457171 4503599627370496 5000000007779 1555800000000000000

noncomputable def ep217 := @ep213 14805000023033619 129650000000000000000 ep214 145887297716709972493 1125899906842624000 195160000277764753 1555800000000000000000 (@ep215 5940758661801845 2251799813685248 700000000054453 62232000000000000000 (ep198 qz70) ep211 rfl) (@ep216 142916918385809049993 1125899906842624000 14805000023033619 129650000000000000000 (ep210 qz70) ep208 rfl) rfl

noncomputable def ep218 := @Enclosure.Complex.IsNear.of_eq qz55 qz66 Bool.false 9000 4000 0 1 Bool.false 142128 4000 0 1 (BSN.w_shift_mk qz17 Bool.false 71064 1000 2 qz18 rfl)

noncomputable abbrev qz334 := (ep218 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 9000 4000) (Enclosure.sfrac Bool.false 142128 4000) Bool.false 9000 4000 0 1 Bool.false 142128 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 9000 4000) (Enclosure.Real.IsNear.const Bool.false 142128 4000)))

noncomputable abbrev qz71 := qz334

noncomputable def ep219 := ep193 (@ep194 1555800000000000000000 (ep212 rfl) (ep217 rfl)) qz71 rfl rfl rfl rfl rfl rfl

noncomputable abbrev qz72 := qz319

noncomputable def ep220 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re qz72) (Complex.re ↑qz3)) (@HMul.hMul Real Real Real qz0 (Complex.im qz72) (Complex.im ↑qz3)) 120447 131072 1 262144 0 1 0 1 120447 120447

noncomputable def ep221 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re qz72) (Complex.re ↑qz3) 1 2 0 1 120447 65536 1 131072 120447 131072 1 262144

noncomputable abbrev qz73 := (@Enclosure.Complex.IsNear.of_eq qz319 (Complex.mk (Enclosure.sfrac Bool.false 1 2) qz273) Bool.false 1 2 0 1 Bool.false 0 1 0 1 BSN.half_c_mk (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 2) qz273 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz329 qz286))

noncomputable def ep222 := ep221 (@Enclosure.Complex.IsNear.re_isNear qz72 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz73) (@Enclosure.Real.IsNear.of_eq (Complex.re ↑qz3) qz3 Bool.false 120447 65536 1 131072 (Complex.ofReal_re qz3) EMRow18.d4)

noncomputable def ep223 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz72) (Complex.im ↑qz3) 0 1 0 1 0 1 0 1 0 1 0 1

noncomputable def ep224 := ep223 (@Enclosure.Complex.IsNear.im_isNear qz72 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz73) (@Enclosure.Real.IsNear.of_eq (Complex.im ↑qz3) qz14 Bool.false 0 1 0 1 (@Eq.trans Real (Complex.im ↑qz3) (0 : Real) qz14 (Complex.ofReal_im qz3) Enclosure.sfrac_zero_eq) qz23)

noncomputable def ep225 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re qz72) (Complex.im ↑qz3)) (@HMul.hMul Real Real Real qz0 (Complex.im qz72) (Complex.re ↑qz3)) 0 1 0 1 0 1 0 1 0 0

noncomputable def ep226 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re qz72) (Complex.im ↑qz3) 1 2 0 1 0 1 0 1 0 1 0 1

noncomputable def ep227 := ep226 (@Enclosure.Complex.IsNear.re_isNear qz72 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz73) (@Enclosure.Real.IsNear.of_eq (Complex.im ↑qz3) qz14 Bool.false 0 1 0 1 (@Eq.trans Real (Complex.im ↑qz3) (0 : Real) qz14 (Complex.ofReal_im qz3) Enclosure.sfrac_zero_eq) qz23)

noncomputable def ep228 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz72) (Complex.re ↑qz3) 0 1 0 1 120447 65536 1 131072 0 1 0 1

noncomputable def ep229 := ep228 (@Enclosure.Complex.IsNear.im_isNear qz72 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz73) (@Enclosure.Real.IsNear.of_eq (Complex.re ↑qz3) qz3 Bool.false 120447 65536 1 131072 (Complex.ofReal_re qz3) EMRow18.d4)

noncomputable def ep230 := @ep191 195160000277764753 1555800000000000000000 (ep219 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@Enclosure.Complex.IsNear.mul qz72 (↑qz3) Bool.false 120447 131072 1 262144 Bool.false 0 1 0 1 (@ep220 131072 1 262144 (ep222 rfl) (ep224 rfl) rfl rfl) (@ep225 1 0 1 (ep227 rfl) (ep229 rfl) rfl rfl))

noncomputable abbrev qz74 := (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 1)

noncomputable abbrev qz335 := (@Nat.cast Complex Complex.instNatCast 1)

noncomputable abbrev qz75 := (@HMul.hMul Complex Complex Complex qz311 (@HMul.hMul Complex Complex Complex qz311 (2 : Complex) qz335) (@HSub.hSub Complex Complex Complex qz312 (@HMul.hMul Complex Complex Complex qz311 (2 : Complex) qz335) (1 : Complex)))

noncomputable abbrev qz336 := (@HPow.hPow Complex Int Complex qz468 qz464 (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) (@OfNat.ofNat Int 1 (@instOfNat 1)) (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (@OfNat.ofNat Int 2 (@instOfNat 2)) (@Nat.cast Int instNatCastInt 1))))

noncomputable abbrev qz76 := qz336

noncomputable def ep231 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz53 2 k))) (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz45 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz54 qz55 (@HSub.hSub Int Int Int qz324 qz56 (@HMul.hMul Int Int Int qz325 qz57 (@Nat.cast Int instNatCastInt k))))) (@HAdd.hAdd Complex Complex Complex qz5 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz53 2 k))) (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz45 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz54 qz55 (@HSub.hSub Int Int Int qz324 qz56 (@HMul.hMul Int Int Int qz325 qz57 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 (@Rat.cast Complex Complex.instRatCast (bernoulli qz74)) qz75) qz76)) Bool.false 1270617 8589934592 3 8589934592

noncomputable def ep232 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz53 2 k))) (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz45 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz54 qz55 (@HSub.hSub Int Int Int qz324 qz56 (@HMul.hMul Int Int Int qz325 qz57 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 (@Rat.cast Complex Complex.instRatCast (bernoulli qz74)) qz75) qz76) Bool.false 0 1 0 1 Bool.false

noncomputable def ep233 := @ep232 0 1 0 1 Bool.false 1270617 8589934592 3 8589934592 Bool.true 1254098979 536870912000 2961 536870912000 Bool.false 1270617 1270617 8589934592 3 8589934592 Bool.true 1254098979 1254098979 536870912000 2961

noncomputable def ep234 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz53 2 k))) (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz45 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz54 qz55 (@HSub.hSub Int Int Int qz324 qz56 (@HMul.hMul Int Int Int qz325 qz57 (@Nat.cast Int instNatCastInt k))))) (Complex.mk qz14 qz14) Bool.false 0 1 0 1 Bool.false

noncomputable def ep235 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz52 (@Rat.cast Complex Complex.instRatCast (bernoulli qz74)) qz75) qz76 Bool.false 1270617 8589934592 3 8589934592 Bool.true 1254098979 536870912000 2961 536870912000

noncomputable abbrev qz77 := (Complex.re qz336)

noncomputable abbrev qz78 := (Complex.im qz336)

noncomputable def ep236 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz52 (@Rat.cast Complex Complex.instRatCast (bernoulli qz74)) qz75)) qz77) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz52 (@Rat.cast Complex Complex.instRatCast (bernoulli qz74)) qz75)) qz78) 1270617 8589934592 3 8589934592 0 1 0

noncomputable def ep237 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz52 (@Rat.cast Complex Complex.instRatCast (bernoulli qz74)) qz75)) qz77 1 12 0 1 3811851 2147483648 9 2147483648 1270617

noncomputable def ep238 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz52 (@Rat.cast Complex Complex.instRatCast (bernoulli qz74)) qz75) (Complex.mk (Enclosure.sfrac Bool.false 1 12) qz14) Bool.false 1 12 0 1 Bool.false 0 1 0 1

noncomputable abbrev qz337 := (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 12) qz14 Bool.false 1 12 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 12) qz23)

noncomputable def ep239 := @Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz52 (@Rat.cast Complex Complex.instRatCast (bernoulli qz74)) qz75) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (ep238 (BSN.stirling_coeff_mk 1 1 6 Bool.false BSN.bern_real_1 rfl rfl) qz337)

noncomputable def ep240 := @Enclosure.Complex.IsNear.re_isNear qz76 Bool.false 3811851 2147483648 9 2147483648 Bool.true 3762296937 134217728000 8883 134217728000

noncomputable abbrev qz469 := (@instHPow Complex Nat (@NPow.toPow Complex (@Monoid.toNPow Complex (@Semiring.toMonoid Complex Complex.instSemiring))))

noncomputable abbrev qz338 := (@HPow.hPow Complex Nat Complex qz469 qz464 1)

noncomputable abbrev qz79 := (@Inv.inv Complex Complex.instInv qz338)

noncomputable def ep241 := @Enclosure.Complex.IsNear.of_eq qz76 qz79 Bool.false 3811851 2147483648 9 2147483648 Bool.true 3762296937 134217728000 8883

noncomputable def ep242 := @Enclosure.Complex.IsNear.of_parts qz79 Bool.false 3811851 2147483648 9 2147483648 Bool.true 3762296937 134217728000 8883

noncomputable abbrev qz80 := (Complex.re qz338)

noncomputable abbrev qz81 := (@MonoidWithZeroHom Complex Real (@instMulZeroOneClassOfSemiring Complex Complex.instSemiring) (@instMulZeroOneClassOfSemiring Real Real.semiring))

noncomputable abbrev qz82 := (@MonoidWithZeroHom.funLike Complex Real (@instMulZeroOneClassOfSemiring Complex Complex.instSemiring) (@instMulZeroOneClassOfSemiring Real Real.semiring))

noncomputable abbrev qz83 := qz338

noncomputable def ep243 := @Enclosure.Real.IsNear.mulLit_ff qz80 (@Inv.inv Real Real.instInv (@DFunLike.coe qz81 Complex (fun (x : Complex) => Real) qz82 Complex.normSq qz83)) 9000 4000 0 1 423539 536870912 1 536870912

noncomputable def ep244 := @Enclosure.Complex.IsNear.re_isNear qz83 Bool.false 9000 4000 0 1 Bool.false 142128 4000 0 1

noncomputable def ep245 := @Enclosure.Complex.IsNear.of_eq qz83 qz55 Bool.false 9000 4000 0 1 Bool.false 142128 4000 0

noncomputable def ep246 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (@DFunLike.coe qz81 Complex (fun (x : Complex) => Real) qz82 Complex.normSq qz83)) Bool.false 423539 536870912 1 536870912 423539 536870912 1

noncomputable abbrev qz84 := (Complex.im qz338)

noncomputable abbrev qz339 := (@instHAdd Real Real.instAdd)

noncomputable def ep247 := @Enclosure.Real.IsNear.of_eq (@DFunLike.coe qz81 Complex (fun (x : Complex) => Real) qz82 Complex.normSq qz83) (@HAdd.hAdd Real Real Real qz339 (@HMul.hMul Real Real Real qz0 qz80 qz80) (@HMul.hMul Real Real Real qz0 qz84 qz84)) Bool.false 316896381 250000 0 1

noncomputable def ep248 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz80 qz80) (@HMul.hMul Real Real Real qz0 qz84 qz84) 81 16 0 1 78907689 62500

noncomputable def ep249 := @Enclosure.Real.IsNear.mulLit_ff qz80 qz80 9000 4000 0 1 9000 4000 0 1

noncomputable def ep250 := @Enclosure.Real.IsNear.mulLit_ff qz84 qz84 142128 4000 0 1 142128 4000 0 1

noncomputable def ep251 := @Enclosure.Complex.IsNear.im_isNear qz83 Bool.false 9000 4000 0 1 Bool.false 142128 4000 0 1

noncomputable abbrev qz85 := (ep244 (@ep245 1 (BSN.pow_one_c qz313) qz334))

noncomputable abbrev qz86 := (ep251 (@ep245 1 (BSN.pow_one_c qz313) qz334))

noncomputable def ep252 := @ep248 0 1 1267585524 316896381 250000 0 1 (@ep249 81 16 0 1 qz85 qz85 rfl) (@ep250 78907689 62500 0 1 qz86 qz86 rfl)

noncomputable def ep253 := @Enclosure.Real.IsNear.inv_image (@DFunLike.coe qz81 Complex (fun (x : Complex) => Real) qz82 Complex.normSq qz83) 316896381 250000 0 1 211769 211770 268435456 (ep247 (Enclosure.Complex.normSq_eq_mul_add_mul qz83) (ep252 rfl rfl)) rfl

noncomputable def ep254 := @Enclosure.Real.IsNear.of_eq (Complex.re qz79) (@HMul.hMul Real Real Real qz0 qz80 (@Inv.inv Real Real.instInv (@DFunLike.coe qz81 Complex (fun (x : Complex) => Real) qz82 Complex.normSq qz83))) Bool.false 3811851 2147483648 9 2147483648 (Enclosure.Complex.inv_re_eq_mul qz83) (@ep243 3811851 2147483648 9 2147483648 qz85 (@ep246 536870912 (ep253 rfl rfl rfl rfl rfl) rfl) rfl)

noncomputable def ep255 := @Enclosure.Real.IsNear.of_eq (Complex.im qz79) (@HMul.hMul Real Real Real qz0 (@Neg.neg Real Real.instNeg qz84) (@Inv.inv Real Real.instInv (@DFunLike.coe qz81 Complex (fun (x : Complex) => Real) qz82 Complex.normSq qz83))) Bool.true 3762296937 134217728000 8883 134217728000 (Enclosure.Complex.inv_im_eq_mul qz83)

noncomputable def ep256 := @Enclosure.Real.IsNear.mulLit_tf (@Neg.neg Real Real.instNeg qz84) (@Inv.inv Real Real.instInv (@DFunLike.coe qz81 Complex (fun (x : Complex) => Real) qz82 Complex.normSq qz83)) 142128 4000 0 1 423539 536870912 1

noncomputable def ep257 := @ep256 536870912 3762296937 134217728000 8883 134217728000 (@Enclosure.Real.IsNear.neg qz84 Bool.false 142128 4000 0 1 qz86) (@ep246 536870912 (ep253 rfl rfl rfl rfl rfl) rfl) rfl

noncomputable def ep258 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz52 (@Rat.cast Complex Complex.instRatCast (bernoulli qz74)) qz75)) qz78 0 1 0 1 3762296937 134217728000 8883 134217728000 0

noncomputable def ep259 := @Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz52 (@Rat.cast Complex Complex.instRatCast (bernoulli qz74)) qz75) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (ep238 (BSN.stirling_coeff_mk 1 1 6 Bool.false BSN.bern_real_1 rfl rfl) qz337)

noncomputable def ep260 := @Enclosure.Complex.IsNear.im_isNear qz76 Bool.false 3811851 2147483648 9 2147483648 Bool.true 3762296937 134217728000 8883 134217728000

noncomputable abbrev qz87 := (@ep241 134217728000 (BSN.zpow_one_sub_two_mul qz313 1 1 rfl rfl) (@ep242 134217728000 ep254 (ep255 ep257)))

noncomputable def ep261 := @ep236 1 1270617 1270617 8589934592 3 8589934592 (@ep237 8589934592 3 8589934592 ep239 (ep240 qz87) rfl) (@ep258 1 0 1 ep259 (ep260 qz87) rfl) rfl

noncomputable def ep262 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz52 (@Rat.cast Complex Complex.instRatCast (bernoulli qz74)) qz75)) qz78) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz52 (@Rat.cast Complex Complex.instRatCast (bernoulli qz74)) qz75)) qz77) 1254098979 536870912000 2961 536870912000 0 1 0

noncomputable def ep263 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HDiv.hDiv Complex Complex Complex qz52 (@Rat.cast Complex Complex.instRatCast (bernoulli qz74)) qz75)) qz78 1 12 0 1 3762296937 134217728000 8883 134217728000 1254098979

noncomputable def ep264 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz52 (@Rat.cast Complex Complex.instRatCast (bernoulli qz74)) qz75)) qz77 0 1 0 1 3811851 2147483648 9 2147483648 0

noncomputable def ep265 := @ep262 1 1254098979 1254098979 536870912000 2961 536870912000 (@ep263 536870912000 2961 536870912000 ep239 (ep260 qz87) rfl) (@ep264 1 0 1 ep259 (ep240 qz87) rfl) rfl

noncomputable abbrev qz88 := (@Enclosure.Complex.IsNear.mk qz273 qz273 Bool.false 0 1 0 1 Bool.false 0 1 0 1 qz286 qz286)

noncomputable def ep266 := @ep233 536870912000 (@ep234 0 1 0 1 (BSN.stirling_sum_base qz55) qz88) (ep235 (ep261 rfl) (ep265 rfl)) rfl rfl rfl rfl rfl

noncomputable def ep267 := @ep188 105879192190595848717 1125899906842624000 3197642030604364510027 ep181 (ep230 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep231 Bool.true 1254098979 536870912000 2961 536870912000 (BSN.stirling_sum_succ qz55 0 1 rfl) (ep266 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl

noncomputable def ep268 := @Enclosure.Complex.IsNear.of_eq (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz48 (@Nat.cast Complex Complex.instNatCast j))) (BSN.logSumC qz17 2) Bool.false 16081250866532563 2251799813685248 5000000007779 777900000000000000 Bool.false 872401986946467 281474976710656

noncomputable abbrev qz89 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz268 qz314 qz335))

noncomputable def ep269 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz17 2) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.logSumC qz17 1) qz89) Bool.false 16081250866532563 2251799813685248 5000000007779 777900000000000000 Bool.false 872401986946467 281474976710656 100000000007779 7779000000000000000

noncomputable def ep270 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz17 1) qz89 Bool.false 16079912984219859 4503599627370496 5000000007779 1555800000000000000 Bool.false 880319759156643 562949953421312 100000000007779 15558000000000000000 Bool.false

noncomputable def ep271 := nat_lit 144847030820335033262401698922496

noncomputable def ep272 := nat_lit 982237315832347274180881809408

noncomputable abbrev qz90 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz268 qz314 (@Nat.cast Complex Complex.instNatCast 0)))

noncomputable def ep273 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz17 1) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.logSumC qz17 0) qz90) Bool.false 16079912984219859 4503599627370496 5000000007779 1555800000000000000 Bool.false 880319759156643 562949953421312 100000000007779 15558000000000000000

noncomputable def ep274 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz17 0) qz90 Bool.false 0 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable abbrev qz340 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz65))

noncomputable def ep275 := @Enclosure.Complex.IsNear.of_eq qz90 qz340 Bool.false 16079912984219859 4503599627370496 5000000007779 1555800000000000000 Bool.false 880319759156643 562949953421312 100000000007779 15558000000000000000

noncomputable def ep276 := nat_lit 26873299266343537004952482534283155645399040

noncomputable def ep277 := nat_lit 98161394505914387117460347676597826879488

noncomputable def ep278 := nat_lit 637055902455447633199463310584665079808

noncomputable def ep279 := BSN.log_dyadic_bound 3817368384 36585368384 3 2 ep276 524288 155580 ep277 ep278 109809 40402736768 32768000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 3817368384) (BSN.artanhQ 36585368384) 0 2 ep277 ep276 ep278 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep280 := @Enclosure.Real.IsNear.mulLit_ff qz67 (Real.log (Enclosure.sfrac Bool.false 20201368384 16000000)) 1 2 0 1 16079912984219859 2251799813685248 5000000007779 777900000000000000 16079912984219859 4503599627370496 5000000007779 1555800000000000000 qz329 (BSN.isNear_log_sfrac 20201368384 16000000 16079912984219859 2251799813685248 5000000007779 777900000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 20201368384) qz330)) Bool.false 134888086698730582966272 18889465931478580854784 1000000001555800 155580000000000000000 16079912984219859 2251799813685248 5000000007779 777900000000000000 (BSN.log_rat_reduce_isNear 20201368384 16000000 10 40402736768 32768000000 109809 524288 24973259072661432 36028797018963968 155580 1000000000000000 rfl rfl rfl rfl (ep279 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep281 := BSN.arctan_dyadic_bound_f 1000 142128 1 0 524288 155580 0 1 1 0 1 1 3688 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 142128) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 142128) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz341 := (@Nat.cast Real Real.instNatCast 1000)

noncomputable abbrev qz342 := (@Nat.cast Real Real.instNatCast 142128)

noncomputable def ep282 := @Enclosure.Real.IsNear.subLit_ff_p qz68 (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz341 qz342)) 884279719003555 562949953421312 1 2000000000000000 3688 524288 1 155580 461541085888718045184 880319759156643 562949953421312 100000000007779 15558000000000000000 qz69 (ep281 rfl) rfl rfl

noncomputable abbrev qz91 := (@HAdd.hAdd Complex Complex Complex qz268 qz314 (@Nat.cast Complex Complex.instNatCast 0))

noncomputable abbrev qz343 := (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz65)

noncomputable def ep283 := @ep274 16079912984219859 4503599627370496 5000000007779 1555800000000000000 Bool.false 880319759156643 562949953421312 100000000007779 15558000000000000000 Bool.false 16079912984219859 16079912984219859 4503599627370496 5000000007779 1555800000000000000 Bool.false 880319759156643 880319759156643 562949953421312 100000000007779 15558000000000000000 (@Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz17 0) (Complex.mk qz14 qz14) Bool.false 0 1 0 1 Bool.false 0 1 0 1 (BSN.log_sum_c_base qz17) qz88) (ep275 (@congrArg Complex Complex qz91 qz343 Complex.log (BSN.w_shift_mk qz17 Bool.false 71064 1000 0 qz18 rfl)) (@Enclosure.Complex.IsNear.of_parts qz340 Bool.false 16079912984219859 4503599627370496 5000000007779 1555800000000000000 Bool.false 880319759156643 562949953421312 100000000007779 15558000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz340) (@HMul.hMul Real Real Real qz0 qz67 (Real.log (Enclosure.sfrac Bool.false 20201368384 16000000))) Bool.false 16079912984219859 4503599627370496 5000000007779 1555800000000000000 (Enclosure.clog_re_eq 1000 142128 4000 20201368384 16000000 rfl rfl rfl) (ep280 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz340) (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz342 qz341)) Bool.false 880319759156643 562949953421312 100000000007779 15558000000000000000 (Enclosure.clog_im_eq 1000 142128 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz342 qz341)) (@HSub.hSub Real Real Real qz315 qz68 (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz341 qz342))) Bool.false 880319759156643 562949953421312 100000000007779 15558000000000000000 (BSN.arctan_recip 142128 1000 rfl rfl) ep282)))) rfl rfl

noncomputable abbrev qz344 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz65))

noncomputable def ep284 := @Enclosure.Complex.IsNear.of_eq qz89 qz344 Bool.false 16082588748845267 4503599627370496 5000000007779 1555800000000000000 Bool.false 864484214736291 562949953421312 100000000007779 15558000000000000000

noncomputable def ep285 := nat_lit 26943884216370805244858108282830985405399040

noncomputable def ep286 := nat_lit 99537311759612119732920204096773698879488

noncomputable def ep287 := nat_lit 653228440986358719127953308150617079808

noncomputable def ep288 := BSN.log_dyadic_bound 3841368384 36609368384 3 2 ep285 524288 155580 ep286 ep287 110432 40450736768 32768000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 3841368384) (BSN.artanhQ 36609368384) 0 2 ep286 ep285 ep287 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep289 := @Enclosure.Real.IsNear.mulLit_ff qz67 (Real.log (Enclosure.sfrac Bool.false 20225368384 16000000)) 1 2 0 1 16082588748845267 2251799813685248 5000000007779 777900000000000000 16082588748845267 4503599627370496 5000000007779 1555800000000000000 qz329 (BSN.isNear_log_sfrac 20225368384 16000000 16082588748845267 2251799813685248 5000000007779 777900000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 20225368384) qz330)) Bool.false 134910532639273397518336 18889465931478580854784 1000000001555800 155580000000000000000 16082588748845267 2251799813685248 5000000007779 777900000000000000 (BSN.log_rat_reduce_isNear 20225368384 16000000 10 40450736768 32768000000 110432 524288 24973259072661432 36028797018963968 155580 1000000000000000 rfl rfl rfl rfl (ep288 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep290 := BSN.arctan_dyadic_bound_f 5000 142128 1 0 524288 155580 0 1 1 0 1 1 18436 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 5000) (BSN.arctanEvenQ 142128) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 5000) (BSN.arctanOddQ 142128) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz345 := (@Nat.cast Real Real.instNatCast 5000)

noncomputable def ep291 := @Enclosure.Real.IsNear.subLit_ff_p qz68 (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz345 qz342)) 884279719003555 562949953421312 1 2000000000000000 18436 524288 1 155580 453238699975660535808 864484214736291 562949953421312 100000000007779 15558000000000000000 qz69 (ep290 rfl) rfl rfl

noncomputable abbrev qz92 := (@HAdd.hAdd Complex Complex Complex qz268 qz314 qz335)

noncomputable abbrev qz346 := (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz65)

noncomputable def ep292 := @ep270 16082588748845267 4503599627370496 5000000007779 1555800000000000000 Bool.false 864484214736291 562949953421312 100000000007779 15558000000000000000 Bool.false ep271 16081250866532563 2251799813685248 5000000007779 777900000000000000 Bool.false ep272 872401986946467 281474976710656 100000000007779 7779000000000000000 (ep273 (BSN.log_sum_c_succ qz17 0 1 rfl) (ep283 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep284 (@congrArg Complex Complex qz92 qz346 Complex.log (BSN.w_shift_mk qz17 Bool.false 71064 1000 1 qz18 rfl)) (@Enclosure.Complex.IsNear.of_parts qz344 Bool.false 16082588748845267 4503599627370496 5000000007779 1555800000000000000 Bool.false 864484214736291 562949953421312 100000000007779 15558000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz344) (@HMul.hMul Real Real Real qz0 qz67 (Real.log (Enclosure.sfrac Bool.false 20225368384 16000000))) Bool.false 16082588748845267 4503599627370496 5000000007779 1555800000000000000 (Enclosure.clog_re_eq 5000 142128 4000 20225368384 16000000 rfl rfl rfl) (ep289 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz344) (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz342 qz345)) Bool.false 864484214736291 562949953421312 100000000007779 15558000000000000000 (Enclosure.clog_im_eq 5000 142128 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz342 qz345)) (@HSub.hSub Real Real Real qz315 qz68 (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz345 qz342))) Bool.false 864484214736291 562949953421312 100000000007779 15558000000000000000 (BSN.arctan_recip 142128 5000 rfl rfl) ep291)))) rfl rfl

noncomputable def ep293 := @ep180 ep181 Bool.false 16081250866532563 2251799813685248 5000000007779 777900000000000000 Bool.false 872401986946467 281474976710656 100000000007779 7779000000000000000 Bool.true ep182 25124331378284182251 450359962737049600 20753364277632699751659 ep177 Bool.false ep183 102389584242809980717 1125899906842624000 1175107343543284912409 ep173 (@ep184 450359962737049600 60621692830349076534977 ep179 Bool.false 105879192190595848717 1125899906842624000 3197642030604364510027 ep181 (BSN.logGammaStirling_unfold 1 qz55) (ep267 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (@ep268 100000000007779 7779000000000000000 (BSN.log_sum_c_eq qz17 2) (ep269 (BSN.log_sum_c_succ qz17 1 2 rfl) (ep292 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)))

noncomputable abbrev qz93 := (@HDiv.hDiv Real Real Real qz265 qz275 (2 : Real))

noncomputable def ep294 := @Enclosure.Real.IsNear.mulLit_ff qz93 (Real.log Real.pi) 71064 2000 0 1 75021 65536 1 131072 666411543 16384000 8883 32768000 (@Enclosure.Real.IsNear.of_eq qz93 (Enclosure.sfrac Bool.false 71064 2000) Bool.false 71064 2000 0 1 (BSN.t_half_eq qz17 Bool.false 71064 1000 qz18) (Enclosure.Real.IsNear.const Bool.false 71064 2000)) EMRow18.d5 rfl

noncomputable def ep295 := @ep175 8883 32768000 ep176 56594131717019617069 1125899906842624000 3478469243543284912409 ep173 (@ep178 1175107343543284912409 ep173 (ep293 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) ep294 rfl rfl

noncomputable def ep296 := BSN.cos_dyadic_bound_f 218589 1073741824 1 0 524288 155732 0 1 1 0 1 1 524287 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 218589) qz283 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 218589) qz284 0 0 rfl) rfl rfl

noncomputable def ep297 := @ep172 524288 Bool.false 524287 524288 1 77790 (@ep174 823553 16384 215 524288 ep295 rfl) (Enclosure.sfrac_false_div 823553 16384) (BSN.cos_reduce0 qz316 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 480684299754930176) (@Nat.cast Real Real.instNatCast 2361183241434822606848)) 226375608064910080 72057594037927936 Bool.false 524287 524288 8 1000000000000000 155580 77790 (BSN.sin_reduce_arg_pos_rat_q0 823553 16384 226375608064910080 72057594037927936 8 480684299754930176 2361183241434822606848 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 524287 524288 480684299754930176 2361183241434822606848 218589 1073741824 155732 155580 (ep296 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep298 := nat_lit 5239167109096262779643507

noncomputable def ep299 := nat_lit 1054591938271348418150400000

noncomputable abbrev qz94 := qz269

noncomputable abbrev qz95 := qz270

noncomputable abbrev qz470 := (@Nat.cast Complex Complex.instNatCast 15)

noncomputable abbrev qz347 := (@HPow.hPow Complex Complex Complex qz457 qz470 qz458)

noncomputable abbrev qz96 := qz347

noncomputable abbrev qz348 := qz470

noncomputable abbrev qz97 := (@HAdd.hAdd Complex Complex Complex qz268 (@HDiv.hDiv Complex Complex Complex qz320 qz348 (@HSub.hSub Complex Complex Complex qz312 qz267 (1 : Complex))) qz319)

noncomputable abbrev qz98 := (@instHSub Nat instSubNat)

noncomputable abbrev qz349 := qz469

noncomputable abbrev qz99 := qz349

noncomputable abbrev qz100 := qz348

noncomputable def ep300 := @Enclosure.Complex.IsNear.of_eq (zetaApproximant qz6 1 15) (@HAdd.hAdd Complex Complex Complex qz5 (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 15, @HPow.hPow Complex Complex Complex qz94 (@Nat.cast Complex Complex.instNatCast n) qz95) (@HMul.hMul Complex Complex Complex qz45 qz96 (@HAdd.hAdd Complex Complex Complex qz5 qz97 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz53 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz53 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz99 qz100 (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1))))))) Bool.false ep167 ep168 ep169

noncomputable def ep301 := @Enclosure.Complex.IsNear.addLitP (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 15, @HPow.hPow Complex Complex Complex qz94 (@Nat.cast Complex Complex.instNatCast n) qz95) (@HMul.hMul Complex Complex Complex qz45 qz96 (@HAdd.hAdd Complex Complex Complex qz5 qz97 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz53 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz53 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz99 qz100 (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1)))))) Bool.false 294969852137 137438953472 25689067265357 5345688095293440

noncomputable def ep302 := nat_lit 8358526234764750276674911

noncomputable def ep303 := nat_lit 87882661522612368179200000

noncomputable def ep304 := nat_lit 1085266404925229835330284907105615872

noncomputable def ep305 := nat_lit 5118501771149814011020601571934208

noncomputable def ep306 := @ep301 Bool.true 3101845747 137438953472 25674357254147 5345688095293440 Bool.true 483202607470225865992049 ep168 ep302 ep170 Bool.false 59271445585376651756689 976097436116944158720000 14512990769865763303261 ep303 Bool.false ep304 ep167 ep168 ep169 ep170 Bool.false ep305 37242001935008840599189 976097436116944158720000

noncomputable def ep307 := @Enclosure.Complex.IsNear.of_eq (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 15, @HPow.hPow Complex Complex Complex qz94 (@Nat.cast Complex Complex.instNatCast n) qz95) (BSN.headSumC qz6 15) Bool.false 294969852137 137438953472 25689067265357 5345688095293440 Bool.true 3101845747 137438953472 25674357254147

noncomputable abbrev qz101 := (@HPow.hPow Complex Complex Complex qz269 (@Nat.cast Complex Complex.instNatCast 14) qz270)

noncomputable def ep308 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz6 15) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz6 14) qz101) Bool.false 294969852137 137438953472 25689067265357 5345688095293440 Bool.true 3101845747 137438953472 25674357254147 5345688095293440

noncomputable def ep309 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz6 14) qz101 Bool.false 547436941465 274877906944 16237860905497 3563792063528960 Bool.true 66123774845 274877906944 16226442655927 3563792063528960 Bool.false

noncomputable abbrev qz102 := (@HPow.hPow Complex Complex Complex qz269 (@Nat.cast Complex Complex.instNatCast 13) qz270)

noncomputable def ep310 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz6 14) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz6 13) qz102) Bool.false 547436941465 274877906944 16237860905497 3563792063528960 Bool.true 66123774845 274877906944 16226442655927 3563792063528960

noncomputable def ep311 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz6 13) qz102 Bool.false 471350635715 274877906944 45940328149213 10691376190586880 Bool.true 30664859793 137438953472 22962571439999 5345688095293440 Bool.false

noncomputable abbrev qz103 := (@HPow.hPow Complex Complex Complex qz269 (@Nat.cast Complex Complex.instNatCast 12) qz270)

noncomputable def ep312 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz6 13) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz6 12) qz103) Bool.false 471350635715 274877906944 45940328149213 10691376190586880 Bool.true 30664859793 137438953472 22962571439999 5345688095293440

noncomputable def ep313 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz6 12) qz103 Bool.false 408574702891 274877906944 43058875982293 10691376190586880 Bool.true 12794668219 274877906944 43047350460313 10691376190586880 Bool.false

noncomputable abbrev qz104 := (@HPow.hPow Complex Complex Complex qz269 (@Nat.cast Complex Complex.instNatCast 11) qz270)

noncomputable def ep314 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz6 12) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz6 11) qz104) Bool.false 408574702891 274877906944 43058875982293 10691376190586880 Bool.true 12794668219 274877906944 43047350460313 10691376190586880

noncomputable def ep315 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz6 11) qz104 Bool.false 174188556569 137438953472 3337611200209 890948015882240 Bool.false 44171628695 274877906944 13346867977741 3563792063528960 Bool.false

noncomputable abbrev qz105 := (@HPow.hPow Complex Complex Complex qz269 (@Nat.cast Complex Complex.instNatCast 10) qz270)

noncomputable def ep316 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz6 11) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz6 10) qz105) Bool.false 174188556569 137438953472 3337611200209 890948015882240 Bool.false 44171628695 274877906944 13346867977741 3563792063528960

noncomputable def ep317 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz6 10) qz105 Bool.false 264553316473 274877906944 36892862167919 10691376190586880 Bool.false 67179995615 274877906944 36896398812479 10691376190586880 Bool.false

noncomputable abbrev qz106 := (@HPow.hPow Complex Complex Complex qz269 (@Nat.cast Complex Complex.instNatCast 9) qz270)

noncomputable def ep318 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz6 10) (@HAdd.hAdd Complex Complex Complex qz5 qz4 qz106) Bool.false 264553316473 274877906944 36892862167919 10691376190586880 Bool.false 67179995615 274877906944 36896398812479 10691376190586880

noncomputable def ep319 := @Enclosure.Complex.IsNear.addLitP qz4 qz106 Bool.false 210225092189 274877906944 11190727882881 3563792063528960 Bool.true 6601797251 274877906944 11190463578391 3563792063528960 Bool.false

noncomputable abbrev qz350 := (@Nat.cast Real Real.instNatCast 9)

noncomputable abbrev qz107 := (@Inv.inv Real Real.instInv (Real.sqrt qz350))

noncomputable abbrev qz108 := (@HMul.hMul Real Real Real qz262 qz275 (Real.log (Enclosure.sfrac Bool.false 9 1)))

noncomputable def ep320 := @Enclosure.Complex.IsNear.of_eq qz106 (Complex.mk (@HMul.hMul Real Real Real qz0 qz107 (Real.cos qz108)) (@HMul.hMul Real Real Real qz0 qz107 (@Neg.neg Real Real.instNeg (Real.sin qz108)))) Bool.false 13582056071 68719476736 830169629819 2672844047646720 Bool.false 36890896433 137438953472 1662504038653 5345688095293440 (BSN.cpow_neg_s_mk qz17 71064 1000 9 qz18 rfl)

noncomputable abbrev qz351 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 9) qz19)

noncomputable def ep321 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz350) 1572865 524288 1 524288 87381 87382 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz350) (Real.sqrt qz351) Bool.false 1572865 524288 1 524288 (BSN.sqrt_natCast_div_one 9) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz351) Bool.false 1572865 524288 1 524288 1572865 524288 1 524288 (BSN.sqrt_enclosure 9 1 786432 786433 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep322 := BSN.log_dyadic_bound 1 17 2 1 867 262144 77790 1 1 30876 18 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 1) (BSN.artanhQ 17) 0 1 1 867 1 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz109 := (Real.log (Enclosure.sfrac Bool.false 9 1))

noncomputable def ep323 := @Enclosure.Real.IsNear.mulLit_ff qz17 qz109 71064 1000 0 1 9895417793173221 4503599627370496 100000000023337 7779000000000000000 87900996256757722143 562949953421312000 296100000069100857 324125000000000000000 qz22 (BSN.isNear_log_sfrac 9 1 9895417793173221 4503599627370496 100000000023337 7779000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz351) Bool.false 20752195215788806766592 9444732965739290427392 1000000000233370 77790000000000000000 9895417793173221 4503599627370496 100000000023337 7779000000000000000 (BSN.log_rat_reduce_isNear 9 1 3 18 16 30876 262144 24973259072661432 36028797018963968 77790 1000000000000000 rfl rfl rfl rfl (ep322 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep324 := nat_lit 215710581603172821919264358710042896

noncomputable def ep325 := BSN.sin_dyadic_bound_f 681503142 1073741824 2 1 524288 155732 ep324 ep57 ep324 ep324 ep58 ep324 310868 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 681503142) qz277 0 1 ep324 ep57 ep324 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 681503142) qz278 0 1 ep324 ep58 ep324 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz352 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 40932091) qz20)

noncomputable def ep326 := @Enclosure.Real.IsNear.cos_image qz108 qz352 Bool.false 40932091 262144 15 16384 Bool.false 310868 524288 1 77790 (@Enclosure.Real.IsNear.recentre' qz108 Bool.false 87900996256757722143 562949953421312000 296100000069100857 324125000000000000000 40932091 262144 15 16384 (ep323 rfl) rfl) (Enclosure.sfrac_false_div 40932091 262144) (BSN.cos_reduce3 qz352 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 23978260146836442447872) qz282) 226375608064910080 72057594037927936 Bool.false 310868 524288 24 1000000000000000 155580 77790 (BSN.sin_reduce_arg_pos_rat_q3 40932091 262144 226375608064910080 72057594037927936 24 23978260146836442447872 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 310868 524288 23978260146836442447872 37778931862957161709568 681503142 1073741824 155732 155580 (ep325 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep327 := BSN.cos_dyadic_bound_f 681503142 1073741824 2 1 524288 155732 ep324 ep61 ep324 ep324 ep62 ep324 422182 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 681503142) qz283 0 1 ep324 ep61 ep324 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 681503142) qz284 0 1 ep324 ep62 ep324 rfl rfl rfl rfl) rfl rfl

noncomputable def ep328 := @Enclosure.Real.IsNear.sin_image qz108 qz352 Bool.false 40932091 262144 15 16384 Bool.true 422182 524288 1 77790 (@Enclosure.Real.IsNear.recentre' qz108 Bool.false 87900996256757722143 562949953421312000 296100000069100857 324125000000000000000 40932091 262144 15 16384 (ep323 rfl) rfl) (Enclosure.sfrac_false_div 40932091 262144) (BSN.sin_reduce3 qz352 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 23978260146836442447872) qz282) 226375608064910080 72057594037927936 Bool.false 422182 524288 24 1000000000000000 155580 77790 (BSN.sin_reduce_arg_pos_rat_q3 40932091 262144 226375608064910080 72057594037927936 24 23978260146836442447872 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 422182 524288 23978260146836442447872 37778931862957161709568 681503142 1073741824 155732 155580 (ep327 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz353 := (@Enclosure.Real.IsNear.recentre' qz107 Bool.false 174763 524288 1 524288 174763 524288 1 524288 (ep321 rfl rfl) rfl)

noncomputable def ep329 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz107 (Real.cos qz108)) (@HMul.hMul Real Real Real qz0 qz107 (@Neg.neg Real Real.instNeg (Real.sin qz108))) Bool.false 13582056071 68719476736 830169629819 2672844047646720 Bool.false 36890896433 137438953472 1662504038653 5345688095293440 (@Enclosure.Real.IsNear.mulLit_ff qz107 (Real.cos qz108) 174763 524288 1 524288 77717 131072 591617 637255680 13582056071 68719476736 830169629819 2672844047646720 qz353 (@Enclosure.Real.IsNear.recentre' (Real.cos qz108) Bool.false 310868 524288 1183234 1274511360 77717 131072 591617 637255680 (ep326 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz107 (@Neg.neg Real Real.instNeg (Real.sin qz108)) 174763 524288 1 524288 211091 262144 591617 637255680 36890896433 137438953472 1662504038653 5345688095293440 qz353 (@Enclosure.Real.IsNear.neg (Real.sin qz108) Bool.true 211091 262144 591617 637255680 (@Enclosure.Real.IsNear.recentre' (Real.sin qz108) Bool.true 422182 524288 1183234 1274511360 211091 262144 591617 637255680 (ep328 rfl rfl) rfl)) rfl)

noncomputable def ep330 := @ep319 13582056071 68719476736 830169629819 2672844047646720 Bool.false 36890896433 137438953472 1662504038653 5345688095293440 Bool.false 18179965476797969072128 264553316473 274877906944 36892862167919 10691376190586880 Bool.false 9233148291579149025280 67179995615 274877906944 36896398812479 10691376190586880 EMRow18.d6 (ep320 ep329) rfl rfl

noncomputable abbrev qz354 := (@Nat.cast Real Real.instNatCast 10)

noncomputable abbrev qz110 := (@Inv.inv Real Real.instInv (Real.sqrt qz354))

noncomputable abbrev qz111 := (@HMul.hMul Real Real Real qz262 qz275 (Real.log (Enclosure.sfrac Bool.false 10 1)))

noncomputable def ep331 := @Enclosure.Complex.IsNear.of_eq qz105 (Complex.mk (@HMul.hMul Real Real Real qz0 qz110 (Real.cos qz111)) (@HMul.hMul Real Real Real qz0 qz110 (@Neg.neg Real Real.instNeg (Real.sin qz111)))) Bool.false 83823796665 274877906944 3158472234589 10691376190586880 Bool.true 2876045865 34359738368 393025640093 1336422023823360 (BSN.cpow_neg_s_mk qz17 71064 1000 10 qz18 rfl)

noncomputable abbrev qz355 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 10) qz19)

noncomputable def ep332 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz354) 1657945 524288 1 524288 82897 82898 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz354) (Real.sqrt qz355) Bool.false 1657945 524288 1 524288 (BSN.sqrt_natCast_div_one 10) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz355) Bool.false 1657945 524288 1 524288 1657945 524288 1 524288 (BSN.sqrt_enclosure 10 1 828972 828973 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep333 := BSN.log_dyadic_bound 2 18 3 2 1574640 262144 77790 6528 48 58495 20 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 2) (BSN.artanhQ 18) 0 2 6528 1574640 48 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz112 := (Real.log (Enclosure.sfrac Bool.false 10 1))

noncomputable def ep334 := @Enclosure.Real.IsNear.mulLit_ff qz17 qz112 71064 1000 0 1 10369908600166117 4503599627370496 100000000023337 7779000000000000000 92115898095275617311 562949953421312000 296100000069100857 324125000000000000000 qz22 (BSN.isNear_log_sfrac 10 1 10369908600166117 4503599627370496 100000000023337 7779000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz355) Bool.false 21747274560655572598784 9444732965739290427392 1000000000233370 77790000000000000000 10369908600166117 4503599627370496 100000000023337 7779000000000000000 (BSN.log_rat_reduce_isNear 10 1 3 20 16 58495 262144 24973259072661432 36028797018963968 77790 1000000000000000 rfl rfl rfl rfl (ep333 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep335 := nat_lit 6845502603276613153724858816447041

noncomputable def ep336 := BSN.cos_dyadic_bound_f 287641361 1073741824 2 1 524288 155732 ep335 ep61 ep335 ep335 ep62 ep335 505587 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 287641361) qz283 0 1 ep335 ep61 ep335 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 287641361) qz284 0 1 ep335 ep62 ep335 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz356 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 85789615) qz27)

noncomputable def ep337 := @Enclosure.Real.IsNear.cos_image qz111 qz356 Bool.false 85789615 524288 15 16384 Bool.false 505587 524288 1 77790 (@Enclosure.Real.IsNear.recentre' qz111 Bool.false 92115898095275617311 562949953421312000 296100000069100857 324125000000000000000 85789615 524288 15 16384 (ep334 rfl) rfl) (Enclosure.sfrac_false_div 85789615 524288) (BSN.cos_reduce0 qz356 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 20240961362166147973120) qz29) 226375608064910080 72057594037927936 Bool.false 505587 524288 26 1000000000000000 155580 77790 (BSN.sin_reduce_arg_pos_rat_q0 85789615 524288 226375608064910080 72057594037927936 26 20240961362166147973120 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 505587 524288 20240961362166147973120 75557863725914323419136 287641361 1073741824 155732 155580 (ep336 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep338 := BSN.sin_dyadic_bound_f 287641361 1073741824 2 1 524288 155732 ep335 ep57 ep335 ep335 ep58 ep335 138776 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 287641361) qz277 0 1 ep335 ep57 ep335 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 287641361) qz278 0 1 ep335 ep58 ep335 rfl rfl rfl rfl) rfl rfl

noncomputable def ep339 := @Enclosure.Real.IsNear.sin_image qz111 qz356 Bool.false 85789615 524288 15 16384 Bool.false 138776 524288 1 77790 (@Enclosure.Real.IsNear.recentre' qz111 Bool.false 92115898095275617311 562949953421312000 296100000069100857 324125000000000000000 85789615 524288 15 16384 (ep334 rfl) rfl) (Enclosure.sfrac_false_div 85789615 524288) (BSN.sin_reduce0 qz356 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 20240961362166147973120) qz29) 226375608064910080 72057594037927936 Bool.false 138776 524288 26 1000000000000000 155580 77790 (BSN.sin_reduce_arg_pos_rat_q0 85789615 524288 226375608064910080 72057594037927936 26 20240961362166147973120 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 138776 524288 20240961362166147973120 75557863725914323419136 287641361 1073741824 155732 155580 (ep338 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz357 := (@Enclosure.Real.IsNear.recentre' qz110 Bool.false 165795 524288 1 524288 165795 524288 1 524288 (ep332 rfl rfl) rfl)

noncomputable def ep340 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz110 (Real.cos qz111)) (@HMul.hMul Real Real Real qz0 qz110 (@Neg.neg Real Real.instNeg (Real.sin qz111))) Bool.false 83823796665 274877906944 3158472234589 10691376190586880 Bool.true 2876045865 34359738368 393025640093 1336422023823360 (@Enclosure.Real.IsNear.mulLit_ff qz110 (Real.cos qz111) 165795 524288 1 524288 505587 524288 591617 637255680 83823796665 274877906944 3158472234589 10691376190586880 qz357 (@Enclosure.Real.IsNear.recentre' (Real.cos qz111) Bool.false 505587 524288 1183234 1274511360 505587 524288 591617 637255680 (ep337 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz110 (@Neg.neg Real Real.instNeg (Real.sin qz111)) 165795 524288 1 524288 17347 65536 591617 637255680 2876045865 34359738368 393025640093 1336422023823360 qz357 (@Enclosure.Real.IsNear.neg (Real.sin qz111) Bool.false 17347 65536 591617 637255680 (@Enclosure.Real.IsNear.recentre' (Real.sin qz111) Bool.false 138776 524288 1183234 1274511360 17347 65536 591617 637255680 (ep339 rfl rfl) rfl)) rfl)

noncomputable def ep341 := @ep317 83823796665 274877906944 3158472234589 10691376190586880 Bool.true 2876045865 34359738368 393025640093 1336422023823360 Bool.false 95761171686566523830272 174188556569 137438953472 3337611200209 890948015882240 Bool.false 1517725605248641269760 44171628695 274877906944 13346867977741 3563792063528960 (ep318 (BSN.head_sum_c_succ qz6 9 10 rfl rfl) (ep330 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep331 ep340) rfl rfl

noncomputable abbrev qz358 := (@Nat.cast Real Real.instNatCast 11)

noncomputable abbrev qz113 := (@Inv.inv Real Real.instInv (Real.sqrt qz358))

noncomputable abbrev qz114 := (@HMul.hMul Real Real Real qz262 qz275 (Real.log (Enclosure.sfrac Bool.false 11 1)))

noncomputable def ep342 := @Enclosure.Complex.IsNear.of_eq qz104 (Complex.mk (@HMul.hMul Real Real Real qz0 qz113 (Real.cos qz114)) (@HMul.hMul Real Real Real qz0 qz113 (@Neg.neg Real Real.instNeg (Real.sin qz114)))) Bool.false 60197589753 274877906944 601508315957 2138275238117376 Bool.true 28483148457 137438953472 300674652709 1069137619058688 (BSN.cpow_neg_s_mk qz17 71064 1000 11 qz18 rfl)

noncomputable abbrev qz359 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 11) qz19)

noncomputable def ep343 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz358) 1738867 524288 1 524288 79039 79040 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz358) (Real.sqrt qz359) Bool.false 1738867 524288 1 524288 (BSN.sqrt_natCast_div_one 11) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz359) Bool.false 1738867 524288 1 524288 1738867 524288 1 524288 (BSN.sqrt_enclosure 11 1 869433 869434 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep344 := BSN.log_dyadic_bound 3 19 4 3 4939817505 262144 77790 41676111 10935 83480 22 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 3) (BSN.artanhQ 19) 0 3 41676111 4939817505 10935 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz115 := (Real.log (Enclosure.sfrac Bool.false 11 1))

noncomputable def ep345 := @Enclosure.Real.IsNear.mulLit_ff qz17 qz115 71064 1000 0 1 10799147631728357 4503599627370496 100000000023337 7779000000000000000 95928828412642995231 562949953421312000 296100000069100857 324125000000000000000 qz22 (BSN.isNear_log_sfrac 11 1 10799147631728357 4503599627370496 100000000023337 7779000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz359) Bool.false 22647454054174387339264 9444732965739290427392 1000000000233370 77790000000000000000 10799147631728357 4503599627370496 100000000023337 7779000000000000000 (BSN.log_rat_reduce_isNear 11 1 3 22 16 83480 262144 24973259072661432 36028797018963968 77790 1000000000000000 rfl rfl rfl rfl (ep344 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep346 := nat_lit 979201659657887017251353838399196238240405082962106544696837670377441263616

noncomputable def ep347 := nat_lit 192201269745291090780237371285482578846147288617791404663673982287937536

noncomputable def ep348 := nat_lit 2937220576434170469572501040455017749563522954309084051281185663167747915776

noncomputable def ep349 := BSN.cos_dyadic_bound_f 813709772 1073741824 3 2 524288 155732 ep346 ep78 ep347 ep348 ep80 ep347 380807 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 813709772) qz283 0 2 ep346 ep78 ep347 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 813709772) qz284 0 2 ep348 ep80 ep347 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz360 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 89340683) qz27)

noncomputable def ep350 := @Enclosure.Real.IsNear.cos_image qz114 qz360 Bool.false 89340683 524288 15 16384 Bool.false 380807 524288 1 77790 (@Enclosure.Real.IsNear.recentre' qz114 Bool.false 95928828412642995231 562949953421312000 296100000069100857 324125000000000000000 89340683 524288 15 16384 (ep345 rfl) rfl) (Enclosure.sfrac_false_div 89340683 524288) (BSN.cos_reduce0 qz360 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 57259734847777203552256) qz29) 226375608064910080 72057594037927936 Bool.false 380807 524288 27 1000000000000000 155580 77790 (BSN.sin_reduce_arg_pos_rat_q0 89340683 524288 226375608064910080 72057594037927936 27 57259734847777203552256 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 380807 524288 57259734847777203552256 75557863725914323419136 813709772 1073741824 155732 155580 (ep349 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep351 := nat_lit 438407652471180172920689139718656256

noncomputable def ep352 := BSN.sin_dyadic_bound_f 813709772 1073741824 2 1 524288 155732 ep351 ep57 ep351 ep351 ep58 ep351 360366 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 813709772) qz277 0 1 ep351 ep57 ep351 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 813709772) qz278 0 1 ep351 ep58 ep351 rfl rfl rfl rfl) rfl rfl

noncomputable def ep353 := @Enclosure.Real.IsNear.sin_image qz114 qz360 Bool.false 89340683 524288 15 16384 Bool.false 360366 524288 1 77790 (@Enclosure.Real.IsNear.recentre' qz114 Bool.false 95928828412642995231 562949953421312000 296100000069100857 324125000000000000000 89340683 524288 15 16384 (ep345 rfl) rfl) (Enclosure.sfrac_false_div 89340683 524288) (BSN.sin_reduce0 qz360 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 57259734847777203552256) qz29) 226375608064910080 72057594037927936 Bool.false 360366 524288 27 1000000000000000 155580 77790 (BSN.sin_reduce_arg_pos_rat_q0 89340683 524288 226375608064910080 72057594037927936 27 57259734847777203552256 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 360366 524288 57259734847777203552256 75557863725914323419136 813709772 1073741824 155732 155580 (ep352 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz361 := (@Enclosure.Real.IsNear.recentre' qz113 Bool.false 158079 524288 1 524288 158079 524288 1 524288 (ep343 rfl rfl) rfl)

noncomputable def ep354 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz113 (Real.cos qz114)) (@HMul.hMul Real Real Real qz0 qz113 (@Neg.neg Real Real.instNeg (Real.sin qz114))) Bool.false 60197589753 274877906944 601508315957 2138275238117376 Bool.true 28483148457 137438953472 300674652709 1069137619058688 (@Enclosure.Real.IsNear.mulLit_ff qz113 (Real.cos qz114) 158079 524288 1 524288 380807 524288 591617 637255680 60197589753 274877906944 601508315957 2138275238117376 qz361 (@Enclosure.Real.IsNear.recentre' (Real.cos qz114) Bool.false 380807 524288 1183234 1274511360 380807 524288 591617 637255680 (ep350 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz113 (@Neg.neg Real Real.instNeg (Real.sin qz114)) 158079 524288 1 524288 180183 262144 591617 637255680 28483148457 137438953472 300674652709 1069137619058688 qz361 (@Enclosure.Real.IsNear.neg (Real.sin qz114) Bool.false 180183 262144 591617 637255680 (@Enclosure.Real.IsNear.recentre' (Real.sin qz114) Bool.false 360366 524288 1183234 1274511360 180183 262144 591617 637255680 (ep353 rfl rfl) rfl)) rfl)

noncomputable def ep355 := @ep315 60197589753 274877906944 601508315957 2138275238117376 Bool.true 28483148457 137438953472 300674652709 1069137619058688 Bool.false 56154079580472372887552 408574702891 274877906944 43058875982293 10691376190586880 Bool.true 1758485810040818106368 12794668219 274877906944 43047350460313 10691376190586880 (ep316 (BSN.head_sum_c_succ qz6 10 11 rfl rfl) (ep341 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep342 ep354) rfl rfl

noncomputable abbrev qz362 := (@Nat.cast Real Real.instNatCast 12)

noncomputable abbrev qz116 := (@Inv.inv Real Real.instInv (Real.sqrt qz362))

noncomputable abbrev qz117 := (@HMul.hMul Real Real Real qz262 qz275 (Real.log (Enclosure.sfrac Bool.false 12 1)))

noncomputable def ep356 := @Enclosure.Complex.IsNear.of_eq qz103 (Complex.mk (@HMul.hMul Real Real Real qz0 qz116 (Real.cos qz117)) (@HMul.hMul Real Real Real qz0 qz116 (@Neg.neg Real Real.instNeg (Real.sin qz117)))) Bool.false 7846991603 34359738368 24012101391 89094801588224 Bool.true 48535051367 274877906944 191852827979 712758412705792 (BSN.cpow_neg_s_mk qz17 71064 1000 12 qz18 rfl)

noncomputable abbrev qz363 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 12) qz19)

noncomputable def ep357 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz362) 1816187 524288 1 524288 75674 75675 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz362) (Real.sqrt qz363) Bool.false 1816187 524288 1 524288 (BSN.sqrt_natCast_div_one 12) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz363) Bool.false 1816187 524288 1 524288 1816187 524288 1 524288 (BSN.sqrt_enclosure 12 1 908093 908094 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep358 := BSN.log_dyadic_bound 4 20 4 3 6720000000 262144 77790 91811840 61440 106290 24 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 4) (BSN.artanhQ 20) 0 3 91811840 6720000000 61440 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz118 := (Real.log (Enclosure.sfrac Bool.false 12 1))

noncomputable def ep359 := @Enclosure.Real.IsNear.mulLit_ff qz17 qz118 71064 1000 0 1 11191020447815397 4503599627370496 100000000023337 7779000000000000000 99409834637944171551 562949953421312000 296100000069100857 324125000000000000000 qz22 (BSN.isNear_log_sfrac 12 1 11191020447815397 4503599627370496 100000000023337 7779000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz363) Bool.false 23469270914176955449344 9444732965739290427392 1000000000233370 77790000000000000000 11191020447815397 4503599627370496 100000000023337 7779000000000000000 (BSN.log_rat_reduce_isNear 12 1 3 24 16 106290 262144 24973259072661432 36028797018963968 77790 1000000000000000 rfl rfl rfl rfl (ep358 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep360 := nat_lit 249402689597292780558205768706560000

noncomputable def ep361 := BSN.cos_dyadic_bound_f 706684040 1073741824 2 1 524288 155732 ep360 ep61 ep360 ep360 ep62 ep360 414776 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 706684040) qz283 0 1 ep360 ep61 ep360 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 706684040) qz284 0 1 ep360 ep62 ep360 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz364 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 92582623) qz27)

noncomputable def ep362 := @Enclosure.Real.IsNear.cos_image qz117 qz364 Bool.false 92582623 524288 15 16384 Bool.false 414776 524288 1 77790 (@Enclosure.Real.IsNear.recentre' qz117 Bool.false 99409834637944171551 562949953421312000 296100000069100857 324125000000000000000 92582623 524288 15 16384 (ep359 rfl) rfl) (Enclosure.sfrac_false_div 92582623 524288) (BSN.cos_reduce0 qz364 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 49728468473875085131776) qz29) 226375608064910080 72057594037927936 Bool.false 414776 524288 28 1000000000000000 155580 77790 (BSN.sin_reduce_arg_pos_rat_q0 92582623 524288 226375608064910080 72057594037927936 28 49728468473875085131776 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 414776 524288 49728468473875085131776 75557863725914323419136 706684040 1073741824 155732 155580 (ep361 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep363 := BSN.sin_dyadic_bound_f 706684040 1073741824 2 1 524288 155732 ep360 ep57 ep360 ep360 ep58 ep360 320683 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 706684040) qz277 0 1 ep360 ep57 ep360 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 706684040) qz278 0 1 ep360 ep58 ep360 rfl rfl rfl rfl) rfl rfl

noncomputable def ep364 := @Enclosure.Real.IsNear.sin_image qz117 qz364 Bool.false 92582623 524288 15 16384 Bool.false 320683 524288 1 77790 (@Enclosure.Real.IsNear.recentre' qz117 Bool.false 99409834637944171551 562949953421312000 296100000069100857 324125000000000000000 92582623 524288 15 16384 (ep359 rfl) rfl) (Enclosure.sfrac_false_div 92582623 524288) (BSN.sin_reduce0 qz364 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 49728468473875085131776) qz29) 226375608064910080 72057594037927936 Bool.false 320683 524288 28 1000000000000000 155580 77790 (BSN.sin_reduce_arg_pos_rat_q0 92582623 524288 226375608064910080 72057594037927936 28 49728468473875085131776 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 320683 524288 49728468473875085131776 75557863725914323419136 706684040 1073741824 155732 155580 (ep363 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz365 := (@Enclosure.Real.IsNear.recentre' qz116 Bool.false 151349 524288 1 524288 151349 524288 1 524288 (ep357 rfl rfl) rfl)

noncomputable def ep365 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz116 (Real.cos qz117)) (@HMul.hMul Real Real Real qz0 qz116 (@Neg.neg Real Real.instNeg (Real.sin qz117))) Bool.false 7846991603 34359738368 24012101391 89094801588224 Bool.true 48535051367 274877906944 191852827979 712758412705792 (@Enclosure.Real.IsNear.mulLit_ff qz116 (Real.cos qz117) 151349 524288 1 524288 51847 65536 591617 637255680 7846991603 34359738368 24012101391 89094801588224 qz365 (@Enclosure.Real.IsNear.recentre' (Real.cos qz117) Bool.false 414776 524288 1183234 1274511360 51847 65536 591617 637255680 (ep362 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz116 (@Neg.neg Real Real.instNeg (Real.sin qz117)) 151349 524288 1 524288 320683 524288 591617 637255680 48535051367 274877906944 191852827979 712758412705792 qz365 (@Enclosure.Real.IsNear.neg (Real.sin qz117) Bool.false 320683 524288 591617 637255680 (@Enclosure.Real.IsNear.recentre' (Real.sin qz117) Bool.false 320683 524288 1183234 1274511360 320683 524288 591617 637255680 (ep364 rfl rfl) rfl)) rfl)

noncomputable def ep366 := @ep313 7846991603 34359738368 24012101391 89094801588224 Bool.true 48535051367 274877906944 191852827979 712758412705792 Bool.false 16195484522757876613120 471350635715 274877906944 45940328149213 10691376190586880 Bool.true 16858184953262122205184 30664859793 137438953472 22962571439999 5345688095293440 (ep314 (BSN.head_sum_c_succ qz6 11 12 rfl rfl) (ep355 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep356 ep365) rfl rfl

noncomputable abbrev qz366 := (@Nat.cast Real Real.instNatCast 13)

noncomputable abbrev qz119 := (@Inv.inv Real Real.instInv (Real.sqrt qz366))

noncomputable abbrev qz120 := (@HMul.hMul Real Real Real qz262 qz275 (Real.log (Enclosure.sfrac Bool.false 13 1)))

noncomputable def ep367 := @Enclosure.Complex.IsNear.of_eq qz102 (Complex.mk (@HMul.hMul Real Real Real qz0 qz119 (Real.cos qz120)) (@HMul.hMul Real Real Real qz0 qz119 (@Neg.neg Real Real.instNeg (Real.sin qz120)))) Bool.false 38043152875 137438953472 1386627283639 5345688095293440 Bool.true 4794055259 274877906944 2754185087783 10691376190586880 (BSN.cpow_neg_s_mk qz17 71064 1000 13 qz18 rfl)

noncomputable abbrev qz367 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 13) qz19)

noncomputable def ep368 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz366) 1890347 524288 1 524288 72705 72706 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz366) (Real.sqrt qz367) Bool.false 1890347 524288 1 524288 (BSN.sqrt_natCast_div_one 13) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz367) Bool.false 1890347 524288 1 524288 1890347 524288 1 524288 (BSN.sqrt_enclosure 13 1 945173 945174 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep369 := BSN.log_dyadic_bound 5 21 5 4 35742602096145 262144 77790 699352521000 41015625 127272 26 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 5) (BSN.artanhQ 21) 0 4 699352521000 35742602096145 41015625 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz121 := (Real.log (Enclosure.sfrac Bool.false 13 1))

noncomputable def ep370 := @Enclosure.Real.IsNear.mulLit_ff qz17 qz121 71064 1000 0 1 11551488463034085 4503599627370496 100000000023337 7779000000000000000 20522374403426355411 112589990684262400 296100000069100857 324125000000000000000 qz22 (BSN.isNear_log_sfrac 13 1 11551488463034085 4503599627370496 100000000023337 7779000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz367) Bool.false 24225227133228857425920 9444732965739290427392 1000000000233370 77790000000000000000 11551488463034085 4503599627370496 100000000023337 7779000000000000000 (BSN.log_rat_reduce_isNear 13 1 3 26 16 127272 262144 24973259072661432 36028797018963968 77790 1000000000000000 rfl rfl rfl rfl (ep369 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep371 := BSN.cos_dyadic_bound_f 67565380 1073741824 1 0 524288 155732 0 1 1 0 1 1 523250 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 67565380) qz283 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 67565380) qz284 0 0 rfl) rfl rfl

noncomputable abbrev qz368 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 5972797) (@Nat.cast Real Real.instNatCast 32768))

noncomputable abbrev qz369 := (@Nat.cast Real Real.instNatCast 4722366482869645213696)

noncomputable def ep372 := @Enclosure.Real.IsNear.cos_image qz120 qz368 Bool.false 5972797 32768 15 16384 Bool.false 523250 524288 1 77790 (@Enclosure.Real.IsNear.recentre' qz120 Bool.false 20522374403426355411 112589990684262400 296100000069100857 324125000000000000000 5972797 32768 15 16384 (ep370 rfl) rfl) (Enclosure.sfrac_false_div 5972797 32768) (BSN.cos_reduce0 qz368 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 297155685674798546944) qz369) 226375608064910080 72057594037927936 Bool.false 523250 524288 29 1000000000000000 155580 77790 (BSN.sin_reduce_arg_pos_rat_q0 5972797 32768 226375608064910080 72057594037927936 29 297155685674798546944 4722366482869645213696 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 523250 524288 297155685674798546944 4722366482869645213696 67565380 1073741824 155732 155580 (ep371 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep373 := BSN.sin_dyadic_bound_f 67565380 1073741824 1 0 524288 155732 0 1 1 0 1 1 32969 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 67565380) qz277 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 67565380) qz278 0 0 rfl) rfl rfl

noncomputable def ep374 := @Enclosure.Real.IsNear.sin_image qz120 qz368 Bool.false 5972797 32768 15 16384 Bool.false 32969 524288 1 77790 (@Enclosure.Real.IsNear.recentre' qz120 Bool.false 20522374403426355411 112589990684262400 296100000069100857 324125000000000000000 5972797 32768 15 16384 (ep370 rfl) rfl) (Enclosure.sfrac_false_div 5972797 32768) (BSN.sin_reduce0 qz368 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 297155685674798546944) qz369) 226375608064910080 72057594037927936 Bool.false 32969 524288 29 1000000000000000 155580 77790 (BSN.sin_reduce_arg_pos_rat_q0 5972797 32768 226375608064910080 72057594037927936 29 297155685674798546944 4722366482869645213696 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 32969 524288 297155685674798546944 4722366482869645213696 67565380 1073741824 155732 155580 (ep373 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz370 := (@Enclosure.Real.IsNear.recentre' qz119 Bool.false 145411 524288 1 524288 145411 524288 1 524288 (ep368 rfl rfl) rfl)

noncomputable def ep375 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz119 (Real.cos qz120)) (@HMul.hMul Real Real Real qz0 qz119 (@Neg.neg Real Real.instNeg (Real.sin qz120))) Bool.false 38043152875 137438953472 1386627283639 5345688095293440 Bool.true 4794055259 274877906944 2754185087783 10691376190586880 (@Enclosure.Real.IsNear.mulLit_ff qz119 (Real.cos qz120) 145411 524288 1 524288 261625 262144 591617 637255680 38043152875 137438953472 1386627283639 5345688095293440 qz370 (@Enclosure.Real.IsNear.recentre' (Real.cos qz120) Bool.false 523250 524288 1183234 1274511360 261625 262144 591617 637255680 (ep372 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz119 (@Neg.neg Real Real.instNeg (Real.sin qz120)) 145411 524288 1 524288 32969 524288 591617 637255680 4794055259 274877906944 2754185087783 10691376190586880 qz370 (@Enclosure.Real.IsNear.neg (Real.sin qz120) Bool.false 32969 524288 591617 637255680 (@Enclosure.Real.IsNear.recentre' (Real.sin qz120) Bool.false 32969 524288 1183234 1274511360 32969 524288 591617 637255680 (ep374 rfl rfl) rfl)) rfl)

noncomputable def ep376 := @ep311 38043152875 137438953472 1386627283639 5345688095293440 Bool.true 4794055259 274877906944 2754185087783 10691376190586880 Bool.false 75239160326862122516480 547436941465 274877906944 16237860905497 3563792063528960 Bool.true 9087982414314959011840 66123774845 274877906944 16226442655927 3563792063528960 (ep312 (BSN.head_sum_c_succ qz6 12 13 rfl rfl) (ep366 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep367 ep375) rfl rfl

noncomputable abbrev qz371 := (@Nat.cast Real Real.instNatCast 14)

noncomputable abbrev qz122 := (@Inv.inv Real Real.instInv (Real.sqrt qz371))

noncomputable abbrev qz123 := (@HMul.hMul Real Real Real qz262 qz275 (Real.log (Enclosure.sfrac Bool.false 14 1)))

noncomputable def ep377 := @Enclosure.Complex.IsNear.of_eq qz101 (Complex.mk (@HMul.hMul Real Real Real qz0 qz122 (Real.cos qz123)) (@HMul.hMul Real Real Real qz0 qz122 (@Neg.neg Real Real.instNeg (Real.sin qz123)))) Bool.false 42502762809 274877906944 2664551814223 10691376190586880 Bool.false 59920083351 274877906944 2669386540513 10691376190586880 (BSN.cpow_neg_s_mk qz17 71064 1000 14 qz18 rfl)

noncomputable abbrev qz372 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 14) qz19)

noncomputable def ep378 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz371) 1961707 524288 1 524288 70060 70061 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz371) (Real.sqrt qz372) Bool.false 1961707 524288 1 524288 (BSN.sqrt_natCast_div_one 14) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz372) Bool.false 1961707 524288 1 524288 1961707 524288 1 524288 (BSN.sqrt_enclosure 14 1 980853 980854 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep379 := BSN.log_dyadic_bound 6 22 5 4 51857700491520 262144 77790 1346332575744 176359680 146699 28 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 6) (BSN.artanhQ 22) 0 4 1346332575744 51857700491520 176359680 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz124 := (Real.log (Enclosure.sfrac Bool.false 14 1))

noncomputable def ep380 := @Enclosure.Real.IsNear.mulLit_ff qz17 qz124 71064 1000 0 1 11885241781671653 4503599627370496 100000000023337 7779000000000000000 105576602746589293599 562949953421312000 296100000069100857 324125000000000000000 qz22 (BSN.isNear_log_sfrac 14 1 11885241781671653 4503599627370496 100000000023337 7779000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz372) Bool.false 24925158572916270432256 9444732965739290427392 1000000000233370 77790000000000000000 11885241781671653 4503599627370496 100000000023337 7779000000000000000 (BSN.log_rat_reduce_isNear 14 1 3 28 16 146699 262144 24973259072661432 36028797018963968 77790 1000000000000000 rfl rfl rfl rfl (ep379 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep381 := nat_lit 192582930460805528477500806691156801

noncomputable def ep382 := BSN.sin_dyadic_bound_f 662452049 1073741824 2 1 524288 155732 ep381 ep57 ep381 ep381 ep58 ep381 303329 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 662452049) qz277 0 1 ep381 ep57 ep381 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 662452049) qz278 0 1 ep381 ep58 ep381 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz373 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 98325873) qz27)

noncomputable def ep383 := @Enclosure.Real.IsNear.cos_image qz123 qz373 Bool.false 98325873 524288 15 16384 Bool.false 303329 524288 1 77790 (@Enclosure.Real.IsNear.recentre' qz123 Bool.false 105576602746589293599 562949953421312000 296100000069100857 324125000000000000000 98325873 524288 15 16384 (ep380 rfl) rfl) (Enclosure.sfrac_false_div 98325873 524288) (BSN.cos_reduce3 qz373 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 46615918782585289834496) qz29) 226375608064910080 72057594037927936 Bool.false 303329 524288 29 1000000000000000 155580 77790 (BSN.sin_reduce_arg_pos_rat_q3 98325873 524288 226375608064910080 72057594037927936 29 46615918782585289834496 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 303329 524288 46615918782585289834496 75557863725914323419136 662452049 1073741824 155732 155580 (ep382 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep384 := BSN.cos_dyadic_bound_f 662452049 1073741824 2 1 524288 155732 ep381 ep61 ep381 ep381 ep62 ep381 427631 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 662452049) qz283 0 1 ep381 ep61 ep381 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 662452049) qz284 0 1 ep381 ep62 ep381 rfl rfl rfl rfl) rfl rfl

noncomputable def ep385 := @Enclosure.Real.IsNear.sin_image qz123 qz373 Bool.false 98325873 524288 15 16384 Bool.true 427631 524288 1 77790 (@Enclosure.Real.IsNear.recentre' qz123 Bool.false 105576602746589293599 562949953421312000 296100000069100857 324125000000000000000 98325873 524288 15 16384 (ep380 rfl) rfl) (Enclosure.sfrac_false_div 98325873 524288) (BSN.sin_reduce3 qz373 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 46615918782585289834496) qz29) 226375608064910080 72057594037927936 Bool.false 427631 524288 29 1000000000000000 155580 77790 (BSN.sin_reduce_arg_pos_rat_q3 98325873 524288 226375608064910080 72057594037927936 29 46615918782585289834496 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 427631 524288 46615918782585289834496 75557863725914323419136 662452049 1073741824 155732 155580 (ep384 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz374 := (@Enclosure.Real.IsNear.recentre' qz122 Bool.false 140121 524288 1 524288 140121 524288 1 524288 (ep378 rfl rfl) rfl)

noncomputable def ep386 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz122 (Real.cos qz123)) (@HMul.hMul Real Real Real qz0 qz122 (@Neg.neg Real Real.instNeg (Real.sin qz123))) Bool.false 42502762809 274877906944 2664551814223 10691376190586880 Bool.false 59920083351 274877906944 2669386540513 10691376190586880 (@Enclosure.Real.IsNear.mulLit_ff qz122 (Real.cos qz123) 140121 524288 1 524288 303329 524288 591617 637255680 42502762809 274877906944 2664551814223 10691376190586880 qz374 (@Enclosure.Real.IsNear.recentre' (Real.cos qz123) Bool.false 303329 524288 1183234 1274511360 303329 524288 591617 637255680 (ep383 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz122 (@Neg.neg Real Real.instNeg (Real.sin qz123)) 140121 524288 1 524288 427631 524288 591617 637255680 59920083351 274877906944 2669386540513 10691376190586880 qz374 (@Enclosure.Real.IsNear.neg (Real.sin qz123) Bool.true 427631 524288 591617 637255680 (@Enclosure.Real.IsNear.recentre' (Real.sin qz123) Bool.true 427631 524288 1183234 1274511360 427631 524288 591617 637255680 (ep385 rfl rfl) rfl)) rfl)

noncomputable def ep387 := @ep309 42502762809 274877906944 2664551814223 10691376190586880 Bool.false 59920083351 274877906944 2669386540513 10691376190586880 Bool.false 162161391133999451078656 294969852137 137438953472 25689067265357 5345688095293440 Bool.true 1705257733197016334336 3101845747 137438953472 25674357254147 5345688095293440 (ep310 (BSN.head_sum_c_succ qz6 13 14 rfl rfl) (ep376 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep377 ep386) rfl rfl

noncomputable def ep388 := @Enclosure.Complex.IsNear.mul qz96 (@HAdd.hAdd Complex Complex Complex qz5 qz97 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz53 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz53 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz99 qz100 (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1))))) Bool.true 483202607470225865992049 ep168 ep302 ep170 Bool.false

noncomputable abbrev qz125 := (Complex.re qz347)

noncomputable abbrev qz126 := (Complex.im qz347)

noncomputable def ep389 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 qz125 (Complex.re (@HAdd.hAdd Complex Complex Complex qz5 qz97 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz53 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz53 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz99 qz100 (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz126 (Complex.im (@HAdd.hAdd Complex Complex Complex qz5 qz97 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz53 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz53 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz99 qz100 (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1))))))) 2794983486656851750729 31235117955742213079040 48930020269338708204551

noncomputable def ep390 := nat_lit 404963304296197792569753600

noncomputable def ep391 := nat_lit 1406122584361797890867200000

noncomputable def ep392 := nat_lit 419246956690408565829008512562833447568015360

noncomputable def ep393 := @Enclosure.Real.IsNear.mulLit_tf qz125 (Complex.re (@HAdd.hAdd Complex Complex Complex qz5 qz97 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz53 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz53 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz99 qz100 (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1)))))) 49066437289 274877906944 858975297191 3563792063528960 56963244961

noncomputable abbrev qz127 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 15)))

noncomputable abbrev qz375 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) qz461 (Real.log (Enclosure.sfrac Bool.false 15 1)))

noncomputable abbrev qz128 := (Real.cos qz375)

noncomputable abbrev qz129 := (@Neg.neg Real Real.instNeg (Real.sin qz375))

noncomputable def ep394 := @Enclosure.Complex.IsNear.of_eq qz96 (Complex.mk (@HMul.hMul Real Real Real qz0 qz127 qz128) (@HMul.hMul Real Real Real qz0 qz127 qz129)) Bool.true 49066437289 274877906944 858975297191 3563792063528960 Bool.false 25640214997 137438953472 429593669883 1781896031764480 (BSN.cpow_neg_s_mk qz17 71064 1000 15 qz18 rfl)

noncomputable abbrev qz130 := (@HDiv.hDiv Real Real Real qz265 (@Nat.cast Real Real.instNatCast 15) (@Nat.cast Real Real.instNatCast 1))

noncomputable def ep395 := @Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 15)) 2030559 524288 1 524288 67685 67686 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 15)) (Real.sqrt qz130) Bool.false 2030559 524288 1 524288 (BSN.sqrt_natCast_div_one 15) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz130) Bool.false 2030559 524288 1 524288 2030559 524288 1 524288 (BSN.sqrt_enclosure 15 1 1015279 1015280 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep396 := BSN.log_dyadic_bound 7 23 6 5 430628584065881355 262144 77790 14087658153505881 266939110305 164785 30 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 7) (BSN.artanhQ 23) 0 5 14087658153505881 430628584065881355 266939110305 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz376 := (Real.log (Enclosure.sfrac Bool.false 15 1))

noncomputable abbrev qz131 := qz376

noncomputable def ep397 := @Enclosure.Real.IsNear.mulLit_ff qz17 qz131 71064 1000 0 1 12195956895733477 4503599627370496 100000000023337 7779000000000000000 108336685104800476191 562949953421312000 296100000069100857 324125000000000000000 qz22 (BSN.isNear_log_sfrac 15 1 12195956895733477 4503599627370496 100000000023337 7779000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz130) Bool.false 25576775395801252757504 9444732965739290427392 1000000000233370 77790000000000000000 12195956895733477 4503599627370496 100000000023337 7779000000000000000 (BSN.log_rat_reduce_isNear 15 1 3 30 16 164785 262144 24973259072661432 36028797018963968 77790 1000000000000000 rfl rfl rfl rfl (ep396 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep398 := nat_lit 1262116507565378375597103152880057189367000035263240630088874905399453450496

noncomputable def ep399 := nat_lit 319272578694353020378410213006689104234198416954565980626189537733673216

noncomputable def ep400 := nat_lit 3785710977538746420750552638214158189892531708955812758305372337122893005056

noncomputable def ep401 := BSN.cos_dyadic_bound_f 867002206 1073741824 3 2 524288 155732 ep398 ep78 ep399 ep400 ep80 ep399 362459 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 867002206) qz283 0 2 ep398 ep78 ep399 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 867002206) qz284 0 2 ep400 ep80 ep399 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz132 := qz375

noncomputable abbrev qz377 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 6306025) (@Nat.cast Real Real.instNatCast 32768))

noncomputable def ep402 := @Enclosure.Real.IsNear.cos_image qz132 qz377 Bool.false 6306025 32768 15 16384 Bool.true 362459 524288 1 77790 (@Enclosure.Real.IsNear.recentre' qz132 Bool.false 108336685104800476191 562949953421312000 296100000069100857 324125000000000000000 6306025 32768 15 16384 (ep397 rfl) rfl) (Enclosure.sfrac_false_div 6306025 32768) (BSN.cos_reduce2 qz377 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 3813116027390258053120) qz369) 226375608064910080 72057594037927936 Bool.false 362459 524288 30 1000000000000000 155580 77790 (BSN.sin_reduce_arg_pos_rat_q2 6306025 32768 226375608064910080 72057594037927936 30 3813116027390258053120 4722366482869645213696 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 362459 524288 3813116027390258053120 4722366482869645213696 867002206 1073741824 155732 155580 (ep401 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep403 := nat_lit 565042103470487427692668588087342096

noncomputable def ep404 := BSN.sin_dyadic_bound_f 867002206 1073741824 2 1 524288 155732 ep403 ep57 ep403 ep403 ep58 ep403 378814 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 867002206) qz277 0 1 ep403 ep57 ep403 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 867002206) qz278 0 1 ep403 ep58 ep403 rfl rfl rfl rfl) rfl rfl

noncomputable def ep405 := @Enclosure.Real.IsNear.sin_image qz132 qz377 Bool.false 6306025 32768 15 16384 Bool.true 378814 524288 1 77790 (@Enclosure.Real.IsNear.recentre' qz132 Bool.false 108336685104800476191 562949953421312000 296100000069100857 324125000000000000000 6306025 32768 15 16384 (ep397 rfl) rfl) (Enclosure.sfrac_false_div 6306025 32768) (BSN.sin_reduce2 qz377 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 3813116027390258053120) qz369) 226375608064910080 72057594037927936 Bool.false 378814 524288 30 1000000000000000 155580 77790 (BSN.sin_reduce_arg_pos_rat_q2 6306025 32768 226375608064910080 72057594037927936 30 3813116027390258053120 4722366482869645213696 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 378814 524288 3813116027390258053120 4722366482869645213696 867002206 1073741824 155732 155580 (ep404 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz133 := (Real.sin qz375)

noncomputable abbrev qz378 := (@Enclosure.Real.IsNear.recentre' qz127 Bool.false 135371 524288 1 524288 135371 524288 1 524288 (ep395 rfl rfl) rfl)

noncomputable def ep406 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz127 qz128) (@HMul.hMul Real Real Real qz0 qz127 qz129) Bool.true 49066437289 274877906944 858975297191 3563792063528960 Bool.false 25640214997 137438953472 429593669883 1781896031764480 (@Enclosure.Real.IsNear.mulLit_ft qz127 qz128 135371 524288 1 524288 362459 524288 591617 637255680 49066437289 274877906944 858975297191 3563792063528960 qz378 (@Enclosure.Real.IsNear.recentre' qz128 Bool.true 362459 524288 1183234 1274511360 362459 524288 591617 637255680 (ep402 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz127 qz129 135371 524288 1 524288 189407 262144 591617 637255680 25640214997 137438953472 429593669883 1781896031764480 qz378 (@Enclosure.Real.IsNear.neg qz133 Bool.true 189407 262144 591617 637255680 (@Enclosure.Real.IsNear.recentre' qz133 Bool.true 378814 524288 1183234 1274511360 189407 262144 591617 637255680 (ep405 rfl rfl) rfl)) rfl)

noncomputable def ep407 := @ep393 113632697160 0 1 2794983486656851750729 31235117955742213079040 48930020269338708204551 ep390 (@Enclosure.Complex.IsNear.re_isNear qz96 Bool.true 49066437289 274877906944 858975297191 3563792063528960 Bool.false 25640214997 137438953472 429593669883 1781896031764480 (ep394 ep406))

noncomputable def ep408 := @Enclosure.Complex.IsNear.re_isNear (@HAdd.hAdd Complex Complex Complex qz5 qz97 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz53 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz53 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz99 qz100 (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1))))) Bool.false 56963244961 113632697160 0 1 Bool.false

noncomputable def ep409 := @Enclosure.Complex.IsNear.addLitP qz97 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz53 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz53 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz99 qz100 (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1)))) Bool.false 314708881 631292762 0 1 Bool.true 66622500

noncomputable def ep410 := @ep409 315646381 0 1 Bool.false 1 360 0 1 Bool.false 987 2500 0 1 Bool.false 113926489922 56963244961 113632697160 0 1 Bool.false 144986728047 144986728047 789115952500 0 1

noncomputable abbrev qz134 := (@HDiv.hDiv Complex Complex Complex qz320 qz348 (@HSub.hSub Complex Complex Complex qz312 qz267 (1 : Complex)))

noncomputable def ep411 := @Enclosure.Complex.IsNear.addLitP qz134 qz72 Bool.true 30000000 20201368384 0 1 Bool.true 4263840000 20201368384 0 1

noncomputable def ep412 := @Enclosure.Complex.IsNear.of_eq qz134 (Complex.mk (Enclosure.sfrac Bool.true 30000000 20201368384) (Enclosure.sfrac Bool.true 4263840000 20201368384)) Bool.true 30000000 20201368384 0 1 Bool.true 4263840000 20201368384 0 1

noncomputable def ep413 := @ep411 Bool.false 1 2 0 1 Bool.false 0 1 0 1 Bool.false 20141368384 314708881 631292762 0 1 Bool.true 4263840000 66622500 315646381 0 1 (ep412 (BSN.N_div_s_sub_one_mk qz17 71064 1000 15 qz18 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 30000000 20201368384) (Enclosure.sfrac Bool.true 4263840000 20201368384) Bool.true 30000000 20201368384 0 1 Bool.true 4263840000 20201368384 0 1 (Enclosure.Real.IsNear.const Bool.true 30000000 20201368384) (Enclosure.Real.IsNear.const Bool.true 4263840000 20201368384))) qz73 rfl

noncomputable abbrev qz135 := (@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 1)))

noncomputable abbrev qz379 := (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz469 qz470 1))

noncomputable abbrev qz136 := qz379

noncomputable def ep414 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz53 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz53 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz99 qz100 (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1)))) (@HAdd.hAdd Complex Complex Complex qz5 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz53 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz53 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz99 qz100 (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz74)) ↑qz135) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1))) qz136)) Bool.false 1 360 0 1

noncomputable def ep415 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz53 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz53 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz99 qz100 (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz74)) ↑qz135) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1))) qz136) Bool.false 0 1 0 1 Bool.false

noncomputable def ep416 := @ep415 0 1 0 1 Bool.false 1 360 0 1 Bool.false 987 2500 0 1 Bool.false 1 1 360 0 1 Bool.false 987 987 2500 0

noncomputable def ep417 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz53 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz53 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz99 qz100 (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1)))) (Complex.mk qz14 qz14) Bool.false 0 1 0 1 Bool.false

noncomputable def ep418 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz74)) ↑qz135) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1))) qz136 Bool.false 1 360 0 1 Bool.false 987 2500 0 1

noncomputable abbrev qz137 := (Complex.re qz379)

noncomputable abbrev qz138 := (Complex.im qz379)

noncomputable def ep419 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz74)) ↑qz135) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)))) qz137) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz74)) ↑qz135) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)))) qz138) 1 360 0 1 0 1 0

noncomputable def ep420 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz74)) ↑qz135) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)))) qz137 1 24 0 1 1 15 0 1 1

noncomputable def ep421 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz74)) ↑qz135)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz74)) ↑qz135)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)))) 1 24 0 1 0 1 0 1 1

noncomputable def ep422 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz74)) ↑qz135)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 1 2 0 1 1 24 0

noncomputable def ep423 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz74)) ↑qz135) (Complex.mk (Enclosure.sfrac Bool.false 1 12) qz14) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (BSN.bern_coeff_mk 1 1 6 2 Bool.false BSN.bern_real_1 EMRow18.d7 rfl) qz337

noncomputable def ep424 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)) qz6 Bool.false 1 2 0 1 Bool.false 71064 1000 0 1 (BSN.ascPochhammer_one_eval qz6)

noncomputable def ep425 := ep424 (@Enclosure.Complex.IsNear.of_eq qz6 (Complex.mk qz67 qz17) Bool.false 1 2 0 1 Bool.false 71064 1000 0 1 (BSN.s_crit_mk qz17 Bool.false 71064 1000 qz18) (@Enclosure.Complex.IsNear.mk qz67 qz17 Bool.false 1 2 0 1 Bool.false 71064 1000 0 1 qz329 qz22))

noncomputable def ep426 := @ep422 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz74)) ↑qz135) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep423) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 71064 1000 0 1 ep425)

noncomputable def ep427 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz74)) ↑qz135)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 71064 1000 0 1 0 1 0

noncomputable def ep428 := @ep427 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz74)) ↑qz135) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep423) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 71064 1000 0 1 ep425)

noncomputable def ep429 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz74)) ↑qz135)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz74)) ↑qz135)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)))) 2961 500 0 1 0 1 0 1 2961

noncomputable def ep430 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz74)) ↑qz135)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 71064 1000 0 1 2961 500 0

noncomputable def ep431 := @ep430 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz74)) ↑qz135) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep423) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 71064 1000 0 1 ep425)

noncomputable def ep432 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz74)) ↑qz135)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 1 2 0 1 0 1 0

noncomputable def ep433 := @ep432 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz74)) ↑qz135) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep423) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 71064 1000 0 1 ep425)

noncomputable def ep434 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz74)) ↑qz135) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 24 0 1 Bool.false 2961 500 0 1 (@ep421 1 24 0 1 (ep426 rfl) (ep428 rfl) rfl rfl) (@ep429 2961 500 0 1 (ep431 rfl) (ep433 rfl) rfl rfl)

noncomputable def ep435 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz74)) ↑qz135) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 2961 500 0 1 ep434

noncomputable abbrev qz139 := (@Enclosure.Complex.IsNear.re_isNear qz379 Bool.false 1 15 0 1 Bool.false 0 1 0 1 (@Enclosure.Complex.IsNear.of_eq qz379 (Complex.mk (Enclosure.sfrac Bool.false 1 15) qz273) Bool.false 1 15 0 1 Bool.false 0 1 0 1 (BSN.natCast_pow_inv_mk 15 1 15 EMRow18.d8 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 15) qz273 Bool.false 1 15 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 15) qz286)))

noncomputable def ep436 := @ep420 360 0 1 ep435 qz139

noncomputable def ep437 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz74)) ↑qz135) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)))) qz138 2961 500 0 1 0 1 0 1 0

noncomputable def ep438 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz74)) ↑qz135) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 2961 500 0 1 ep434

noncomputable abbrev qz140 := (@Enclosure.Complex.IsNear.im_isNear qz379 Bool.false 1 15 0 1 Bool.false 0 1 0 1 (@Enclosure.Complex.IsNear.of_eq qz379 (Complex.mk (Enclosure.sfrac Bool.false 1 15) qz273) Bool.false 1 15 0 1 Bool.false 0 1 0 1 (BSN.natCast_pow_inv_mk 15 1 15 EMRow18.d8 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 15) qz273 Bool.false 1 15 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 15) qz286)))

noncomputable def ep439 := @ep437 1 0 1 ep438 qz140

noncomputable def ep440 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz74)) ↑qz135) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)))) qz138) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz74)) ↑qz135) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)))) qz137) 0 1 0 1 987 2500 0

noncomputable def ep441 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz74)) ↑qz135) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)))) qz138 1 24 0 1 0 1 0 1 0

noncomputable def ep442 := @ep441 1 0 1 ep435 qz140

noncomputable def ep443 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz74)) ↑qz135) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)))) qz137 2961 500 0 1 1 15 0 1 987

noncomputable def ep444 := @ep443 2500 0 1 ep438 qz139

noncomputable def ep445 := @ep416 1 (@ep417 0 1 0 1 (BSN.bern_sum_base qz6 15) qz88) (ep418 (@ep419 1 1 1 360 0 1 (ep436 rfl) (ep439 rfl) rfl rfl) (@ep440 1 987 987 2500 0 1 (ep442 rfl) (ep444 rfl) rfl rfl)) rfl rfl rfl rfl rfl

noncomputable def ep446 := ep410 (ep413 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep414 Bool.false 987 2500 0 1 (BSN.bern_sum_succ qz6 15 0 1 1 rfl rfl) (ep445 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl rfl

noncomputable def ep447 := @Enclosure.Real.IsNear.mulLit_ff qz126 (Complex.im (@HAdd.hAdd Complex Complex Complex qz5 qz97 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz53 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz53 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz99 qz100 (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1)))))) 25640214997 137438953472 429593669883 1781896031764480 144986728047

noncomputable def ep448 := @ep447 789115952500 0 1 3717490878836649920859 108455270679660462080000 62285380586039215308501 ep391 (@Enclosure.Complex.IsNear.im_isNear qz96 Bool.true 49066437289 274877906944 858975297191 3563792063528960 Bool.false 25640214997 137438953472 429593669883 1781896031764480 (ep394 ep406))

noncomputable def ep449 := @Enclosure.Complex.IsNear.im_isNear (@HAdd.hAdd Complex Complex Complex qz5 qz97 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz53 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz53 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz99 qz100 (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1))))) Bool.false 56963244961 113632697160 0 1 Bool.false

noncomputable def ep450 := @Enclosure.Real.IsNear.addLit_tf_p (@HMul.hMul Real Real Real qz0 qz125 (Complex.im (@HAdd.hAdd Complex Complex Complex qz5 qz97 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz53 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz53 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz99 qz100 (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz126 (Complex.re (@HAdd.hAdd Complex Complex Complex qz5 qz97 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz53 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz53 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz99 qz100 (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1))))))) 7113982199455422944583 216910541359320924160000 124540017812922520015977

noncomputable def ep451 := nat_lit 2812245168723595781734400000

noncomputable def ep452 := nat_lit 22497961349788766253875200

noncomputable def ep453 := nat_lit 205705621585177309205579232794383663067299840

noncomputable def ep454 := @Enclosure.Real.IsNear.mulLit_tf qz125 (Complex.im (@HAdd.hAdd Complex Complex Complex qz5 qz97 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz53 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz53 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz99 qz100 (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1)))))) 49066437289 274877906944 858975297191 3563792063528960 144986728047

noncomputable def ep455 := @ep454 789115952500 0 1 7113982199455422944583 216910541359320924160000 124540017812922520015977 ep451 (@Enclosure.Complex.IsNear.re_isNear qz96 Bool.true 49066437289 274877906944 858975297191 3563792063528960 Bool.false 25640214997 137438953472 429593669883 1781896031764480 (ep394 ep406))

noncomputable def ep456 := @Enclosure.Real.IsNear.mulLit_ff qz126 (Complex.re (@HAdd.hAdd Complex Complex Complex qz5 qz97 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz53 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz53 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz99 qz100 (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1)))))) 25640214997 137438953472 429593669883 1781896031764480 56963244961

noncomputable def ep457 := @ep456 113632697160 0 1 1460549847726816880117 15617558977871106539520 2719005494582255245507 ep452 (@Enclosure.Complex.IsNear.im_isNear qz96 Bool.true 49066437289 274877906944 858975297191 3563792063528960 Bool.false 25640214997 137438953472 429593669883 1781896031764480 (ep394 ep406))

noncomputable abbrev qz380 := (ep446 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable def ep458 := @ep388 59271445585376651756689 976097436116944158720000 14512990769865763303261 ep303 (@ep389 ep390 3717490878836649920859 108455270679660462080000 62285380586039215308501 ep391 ep392 483202607470225865992049 ep168 ep302 ep170 (ep407 (@ep408 144986728047 789115952500 0 1 qz380) rfl) (ep448 (@ep449 144986728047 789115952500 0 1 qz380) rfl) rfl rfl) (@ep450 ep451 1460549847726816880117 15617558977871106539520 2719005494582255245507 ep452 ep453 59271445585376651756689 976097436116944158720000 14512990769865763303261 ep303 (ep455 (@ep449 144986728047 789115952500 0 1 qz380) rfl) (ep457 (@ep408 144986728047 789115952500 0 1 qz380) rfl) rfl rfl)

noncomputable def ep459 := @ep306 ep298 ep299 (@ep307 5345688095293440 (BSN.head_sum_c_eq qz6 15) (ep308 (BSN.head_sum_c_succ qz6 14 15 rfl rfl) (ep387 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))) ep458 rfl rfl rfl

noncomputable def ep460 := @Enclosure.Complex.IsNear.re_isNear (zetaApproximant qz6 1 15) Bool.false ep167 ep168 ep169 ep170 Bool.false 37242001935008840599189 976097436116944158720000 ep298 ep299 (@ep300 ep170 Bool.false 37242001935008840599189 976097436116944158720000 ep298 ep299 (BSN.zetaApproximant_eq_folded' qz6 1 15 rfl) (ep459 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

noncomputable def ep461 := @Enclosure.Real.IsNear.mulLit_ff (Real.sin (@HSub.hSub Real Real Real qz315 (Complex.im (@HSub.hSub Complex Complex Complex qz46 qz47 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz48 (@Nat.cast Complex Complex.instNatCast j))))) qz49)) (Complex.im (zetaApproximant qz6 1 15)) 53 262144 8624569

noncomputable def ep462 := @Enclosure.Real.IsNear.recentre' (Real.sin (@HSub.hSub Real Real Real qz315 (Complex.im (@HSub.hSub Complex Complex Complex qz46 qz47 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz48 (@Nat.cast Complex Complex.instNatCast j))))) qz49)) Bool.false 106 524288 17249138

noncomputable def ep463 := @Enclosure.Real.IsNear.sin_image (@HSub.hSub Real Real Real qz315 (Complex.im (@HSub.hSub Complex Complex Complex qz46 qz47 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz48 (@Nat.cast Complex Complex.instNatCast j))))) qz49) qz316 Bool.false 823553 16384 215

noncomputable def ep464 := BSN.sin_dyadic_bound_f 218589 1073741824 1 0 524288 155732 0 1 1 0 1 1 106 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 218589) qz277 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 218589) qz278 0 0 rfl) rfl rfl

noncomputable def ep465 := @ep463 524288 Bool.false 106 524288 1 77790 (@ep174 823553 16384 215 524288 ep295 rfl) (Enclosure.sfrac_false_div 823553 16384) (BSN.sin_reduce0 qz316 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 480684299754930176) (@Nat.cast Real Real.instNatCast 2361183241434822606848)) 226375608064910080 72057594037927936 Bool.false 106 524288 8 1000000000000000 155580 77790 (BSN.sin_reduce_arg_pos_rat_q0 823553 16384 226375608064910080 72057594037927936 8 480684299754930176 2361183241434822606848 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 106 524288 480684299754930176 2361183241434822606848 218589 1073741824 155732 155580 (ep464 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep466 := @Enclosure.Complex.IsNear.im_isNear (zetaApproximant qz6 1 15) Bool.false ep167 ep168 ep169 ep170 Bool.false 37242001935008840599189 976097436116944158720000 ep298 ep299 (@ep300 ep170 Bool.false 37242001935008840599189 976097436116944158720000 ep298 ep299 (BSN.zetaApproximant_eq_folded' qz6 1 15 rfl) (ep459 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

theorem EMRow18.d9 : Enclosure.Real.IsNear (hardyZApproximantEM 1 15 qz17) Bool.false ep150 ep151 ep152 ep153 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantEM 1 15 qz17) ep154 Bool.false ep150 ep151 ep152 ep153 (@Eq.refl Real ep154) (@ep155 Bool.false ep150 ep151 ep152 ep153 (BSN.re_exp_mul (@HSub.hSub Real Real Real qz315 (Complex.im (@HSub.hSub Complex Complex Complex qz46 qz47 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz48 (@Nat.cast Complex Complex.instNatCast j))))) qz49) (zetaApproximant qz6 1 15)) (@ep157 ep158 ep159 ep160 ep161 ep162 ep163 ep164 ep165 ep150 ep151 ep152 ep153 (@ep166 20392181760 ep167 ep168 ep169 ep170 ep156 ep158 ep159 ep160 (@ep171 40784363520 524287 524288 8624569 20392181760 (ep297 rfl rfl) rfl) ep460 rfl) (@ep461 20392181760 37242001935008840599189 976097436116944158720000 ep298 ep299 ep161 ep162 ep163 ep164 (@ep462 40784363520 53 262144 8624569 20392181760 (ep465 rfl rfl) rfl) ep466 rfl) rfl rfl))

noncomputable abbrev qz485 := (@HAdd.hAdd Complex Complex Complex (@instHAdd Complex Complex.instAdd) (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (2 : Complex)) (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul) Complex.I ↑(Enclosure.sfrac Bool.false 73635 1000)))

noncomputable abbrev qz471 := qz485

noncomputable abbrev qz381 := qz471

noncomputable abbrev qz141 := (BSN.headSumC qz381 9)

noncomputable abbrev qz142 := qz381

noncomputable abbrev qz472 := (@Neg.neg Complex Complex.instNeg qz485)

noncomputable abbrev qz382 := qz472

noncomputable abbrev qz143 := (@HPow.hPow Complex Complex Complex qz269 (@Nat.cast Complex Complex.instNatCast 8) qz382)

noncomputable def ep467 := @Enclosure.Complex.IsNear.of_eq qz141 (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz142 8) qz143) Bool.false 689280776103 274877906944 11584630798111 3563792063528960 Bool.true 39117928617 274877906944 11589565769781 3563792063528960

noncomputable def ep468 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz142 8) qz143 Bool.false 11807775571 4294967296 2592343899291 890948015882240 Bool.false 15914416409 137438953472 2593498432541 890948015882240 Bool.true

noncomputable abbrev qz144 := (@HPow.hPow Complex Complex Complex qz269 (@Nat.cast Complex Complex.instNatCast 7) qz382)

noncomputable def ep469 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz142 8) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz142 7) qz144) Bool.false 11807775571 4294967296 2592343899291 890948015882240 Bool.false 15914416409 137438953472 2593498432541 890948015882240

noncomputable def ep470 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz142 7) qz144 Bool.false 720622587381 274877906944 27218623210321 10691376190586880 Bool.true 16491449165 68719476736 13610083573673 5345688095293440 Bool.false

noncomputable abbrev qz145 := (@HPow.hPow Complex Complex Complex qz269 (@Nat.cast Complex Complex.instNatCast 6) qz382)

noncomputable def ep471 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz142 7) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz142 6) qz145) Bool.false 720622587381 274877906944 27218623210321 10691376190586880 Bool.true 16491449165 68719476736 13610083573673 5345688095293440

noncomputable def ep472 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz142 6) qz145 Bool.false 304205571679 137438953472 11498115102073 5345688095293440 Bool.true 67172334503 274877906944 23017945866071 10691376190586880 Bool.false

noncomputable abbrev qz146 := (@HPow.hPow Complex Complex Complex qz269 (@Nat.cast Complex Complex.instNatCast 5) qz382)

noncomputable def ep473 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz142 6) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz142 5) qz146) Bool.false 304205571679 137438953472 11498115102073 5345688095293440 Bool.true 67172334503 274877906944 23017945866071 10691376190586880

noncomputable def ep474 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz142 5) qz146 Bool.false 529114899903 274877906944 6129705004297 3563792063528960 Bool.true 40276619407 68719476736 3068067076661 1781896031764480 Bool.false

noncomputable abbrev qz147 := (@HPow.hPow Complex Complex Complex qz269 (@Nat.cast Complex Complex.instNatCast 4) qz382)

noncomputable def ep475 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz142 5) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz142 4) qz147) Bool.false 529114899903 274877906944 6129705004297 3563792063528960 Bool.true 40276619407 68719476736 3068067076661 1781896031764480

noncomputable def ep476 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz142 4) qz147 Bool.false 263032957335 137438953472 1325248598105 1069137619058688 Bool.true 11851063517 137438953472 662591934523 534568809529344 Bool.false

noncomputable abbrev qz148 := (@HPow.hPow Complex Complex Complex qz269 qz271 qz382)

noncomputable def ep477 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz142 4) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz142 3) qz148) Bool.false 263032957335 137438953472 1325248598105 1069137619058688 Bool.true 11851063517 137438953472 662591934523 534568809529344

noncomputable def ep478 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz142 3) qz148 Bool.false 51729132965 34359738368 364642735225 534568809529344 Bool.true 8295039 16777216 729221488175 1069137619058688 Bool.false

noncomputable abbrev qz149 := (@HPow.hPow Complex Complex Complex qz269 qz272 qz382)

noncomputable def ep479 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz142 3) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz142 2) qz149) Bool.false 51729132965 34359738368 364642735225 534568809529344 Bool.true 8295039 16777216 729221488175 1069137619058688

noncomputable def ep480 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz142 2) qz149 Bool.false 1 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable def ep481 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz142 2) (Complex.mk (Enclosure.sfrac Bool.false 1 1) qz14) Bool.false 1 1 0 1 Bool.false 0 1 0 1 (BSN.head_sum_c_two qz142)

noncomputable abbrev qz486 := (Enclosure.sfrac Bool.false 73635 1000)

noncomputable abbrev qz473 := qz486

noncomputable abbrev qz383 := qz473

noncomputable abbrev qz150 := (@HMul.hMul Real Real Real qz262 qz383 (Real.log (Enclosure.sfrac Bool.false 2 1)))

noncomputable abbrev qz151 := qz383

noncomputable abbrev qz384 := (@Eq.refl Real qz473)

noncomputable abbrev qz152 := qz384

noncomputable def ep482 := @Enclosure.Complex.IsNear.of_eq qz149 (Complex.mk (@HMul.hMul Real Real Real qz0 qz15 (Real.cos qz150)) (@HMul.hMul Real Real Real qz0 qz15 (@Neg.neg Real Real.instNeg (Real.sin qz150)))) Bool.false 17369394597 34359738368 364642735225 534568809529344 Bool.true 8295039 16777216 729221488175 1069137619058688 (BSN.cpow_neg_s_mk qz151 73635 1000 2 qz152 rfl)

noncomputable def ep483 := nat_lit 1067207913240925353784183105829957325812498926939272335215205313747184190625

noncomputable def ep484 := nat_lit 228294119493679091766200992030762875655850443960827804843169827875390625

noncomputable def ep485 := nat_lit 3201167151483788703169016915505810451686185079929895350035929601585801790625

noncomputable def ep486 := BSN.cos_dyadic_bound_f 831403485 1073741824 3 2 524288 155732 ep483 ep78 ep484 ep485 ep80 ep484 374817 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 831403485) qz283 0 2 ep483 ep78 ep484 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 831403485) qz284 0 2 ep485 ep80 ep484 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz153 := (Enclosure.Real.IsNear.const Bool.false 73635 1000)

noncomputable abbrev qz385 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 6689887) (@Nat.cast Real Real.instNatCast 131072))

noncomputable abbrev qz386 := (@Nat.cast Real Real.instNatCast 14626204802138603782144)

noncomputable def ep487 := @Enclosure.Real.IsNear.cos_image qz150 qz385 Bool.false 6689887 131072 497 524288 Bool.false 374817 524288 1 77790 (@Enclosure.Real.IsNear.recentre' qz150 Bool.false 334494351 6553600 4909 5186000 6689887 131072 497 524288 (@Enclosure.Real.IsNear.mulLit_ff qz151 qz21 73635 1000 0 1 181704 262144 1 77790 334494351 6553600 4909 5186000 qz153 qz280 rfl) rfl) (Enclosure.sfrac_false_div 6689887 131072) (BSN.cos_reduce0 qz385 (@HDiv.hDiv Real Real Real qz2 qz386 qz293) 226375608064910080 72057594037927936 Bool.false 374817 524288 8 1000000000000000 155580 77790 (BSN.sin_reduce_arg_pos_rat_q0 6689887 131072 226375608064910080 72057594037927936 8 14626204802138603782144 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 374817 524288 14626204802138603782144 18889465931478580854784 831403485 1073741824 155732 155580 (ep486 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep488 := nat_lit 477801338940860536980102012590300625

noncomputable def ep489 := BSN.sin_dyadic_bound_f 831403485 1073741824 2 1 524288 155732 ep488 ep57 ep488 ep488 ep58 ep488 366592 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 831403485) qz277 0 1 ep488 ep57 ep488 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 831403485) qz278 0 1 ep488 ep58 ep488 rfl rfl rfl rfl) rfl rfl

noncomputable def ep490 := @Enclosure.Real.IsNear.sin_image qz150 qz385 Bool.false 6689887 131072 497 524288 Bool.false 366592 524288 1 77790 (@Enclosure.Real.IsNear.recentre' qz150 Bool.false 334494351 6553600 4909 5186000 6689887 131072 497 524288 (@Enclosure.Real.IsNear.mulLit_ff qz151 qz21 73635 1000 0 1 181704 262144 1 77790 334494351 6553600 4909 5186000 qz153 qz280 rfl) rfl) (Enclosure.sfrac_false_div 6689887 131072) (BSN.sin_reduce0 qz385 (@HDiv.hDiv Real Real Real qz2 qz386 qz293) 226375608064910080 72057594037927936 Bool.false 366592 524288 8 1000000000000000 155580 77790 (BSN.sin_reduce_arg_pos_rat_q0 6689887 131072 226375608064910080 72057594037927936 8 14626204802138603782144 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 366592 524288 14626204802138603782144 18889465931478580854784 831403485 1073741824 155732 155580 (ep489 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep491 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz15 (Real.cos qz150)) (@HMul.hMul Real Real Real qz0 qz15 (@Neg.neg Real Real.instNeg (Real.sin qz150))) Bool.false 17369394597 34359738368 364642735225 534568809529344 Bool.true 8295039 16777216 729221488175 1069137619058688 (@Enclosure.Real.IsNear.mulLit_ff qz15 (Real.cos qz150) 46341 65536 1 262144 374817 524288 19592959 20392181760 17369394597 34359738368 364642735225 534568809529344 qz285 (@Enclosure.Real.IsNear.recentre' (Real.cos qz150) Bool.false 374817 524288 39185918 40784363520 374817 524288 19592959 20392181760 (ep487 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz15 (@Neg.neg Real Real.instNeg (Real.sin qz150)) 46341 65536 1 262144 179 256 19592959 20392181760 8295039 16777216 729221488175 1069137619058688 qz285 (@Enclosure.Real.IsNear.neg (Real.sin qz150) Bool.false 179 256 19592959 20392181760 (@Enclosure.Real.IsNear.recentre' (Real.sin qz150) Bool.false 366592 524288 39185918 40784363520 179 256 19592959 20392181760 (ep490 rfl rfl) rfl)) rfl)

noncomputable def ep492 := @ep480 17369394597 34359738368 364642735225 534568809529344 Bool.true 8295039 16777216 729221488175 1069137619058688 Bool.false 51729132965 51729132965 34359738368 364642735225 534568809529344 Bool.true 8295039 8295039 16777216 729221488175 1069137619058688 (ep481 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 1) qz14 Bool.false 1 1 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 1) qz23)) (ep482 ep491) rfl rfl

noncomputable abbrev qz154 := (@HMul.hMul Real Real Real qz262 qz383 (Real.log (Enclosure.sfrac Bool.false 3 1)))

noncomputable def ep493 := @Enclosure.Complex.IsNear.of_eq qz148 (Complex.mk (@HMul.hMul Real Real Real qz0 qz24 (Real.cos qz154)) (@HMul.hMul Real Real Real qz0 qz24 (@Neg.neg Real Real.instNeg (Real.sin qz154)))) Bool.false 56116425475 137438953472 198654375885 356379206352896 Bool.false 56101895971 137438953472 198654126957 356379206352896 (BSN.cpow_neg_s_mk qz151 73635 1000 3 qz152 rfl)

noncomputable def ep494 := nat_lit 506112438925680240410662384755921121

noncomputable def ep495 := BSN.sin_dyadic_bound_f 843454681 1073741824 2 1 524288 155732 ep494 ep57 ep494 ep494 ep58 ep494 370775 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 843454681) qz277 0 1 ep494 ep57 ep494 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 843454681) qz278 0 1 ep494 ep58 ep494 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz387 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 10603219) (@Nat.cast Real Real.instNatCast 131072))

noncomputable def ep496 := @Enclosure.Real.IsNear.cos_image qz154 qz387 Bool.false 10603219 131072 497 524288 Bool.false 370775 524288 1 77790 (@Enclosure.Real.IsNear.recentre' qz154 Bool.false 2120643819 26214400 4909 5186000 10603219 131072 497 524288 (@Enclosure.Real.IsNear.mulLit_ff qz151 qz28 73635 1000 0 1 287994 262144 1 77790 2120643819 26214400 4909 5186000 qz153 qz288 rfl) rfl) (Enclosure.sfrac_false_div 10603219 131072) (BSN.cos_reduce3 qz387 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 14838211680009828958208) qz293) 226375608064910080 72057594037927936 Bool.false 370775 524288 12 1000000000000000 155580 77790 (BSN.sin_reduce_arg_pos_rat_q3 10603219 131072 226375608064910080 72057594037927936 12 14838211680009828958208 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 370775 524288 14838211680009828958208 18889465931478580854784 843454681 1073741824 155732 155580 (ep495 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep497 := nat_lit 1130457372163631246166555292273797101434129011888213143237958916331572585921

noncomputable def ep498 := nat_lit 256149800835300411422216828974168256898316399670118275903041669173896641

noncomputable def ep499 := nat_lit 3390859816889223137676821443163442967788590402865299193162070665656369964481

noncomputable def ep500 := BSN.cos_dyadic_bound_f 843454681 1073741824 3 2 524288 155732 ep497 ep78 ep498 ep499 ep80 ep498 370679 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 843454681) qz283 0 2 ep497 ep78 ep498 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 843454681) qz284 0 2 ep499 ep80 ep498 rfl rfl rfl rfl) rfl rfl

noncomputable def ep501 := @Enclosure.Real.IsNear.sin_image qz154 qz387 Bool.false 10603219 131072 497 524288 Bool.true 370679 524288 1 77790 (@Enclosure.Real.IsNear.recentre' qz154 Bool.false 2120643819 26214400 4909 5186000 10603219 131072 497 524288 (@Enclosure.Real.IsNear.mulLit_ff qz151 qz28 73635 1000 0 1 287994 262144 1 77790 2120643819 26214400 4909 5186000 qz153 qz288 rfl) rfl) (Enclosure.sfrac_false_div 10603219 131072) (BSN.sin_reduce3 qz387 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 14838211680009828958208) qz293) 226375608064910080 72057594037927936 Bool.false 370679 524288 12 1000000000000000 155580 77790 (BSN.sin_reduce_arg_pos_rat_q3 10603219 131072 226375608064910080 72057594037927936 12 14838211680009828958208 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 370679 524288 14838211680009828958208 18889465931478580854784 843454681 1073741824 155732 155580 (ep500 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep502 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz24 (Real.cos qz154)) (@HMul.hMul Real Real Real qz0 qz24 (@Neg.neg Real Real.instNeg (Real.sin qz154))) Bool.false 56116425475 137438953472 198654375885 356379206352896 Bool.false 56101895971 137438953472 198654126957 356379206352896 (@Enclosure.Real.IsNear.mulLit_ff qz24 (Real.cos qz154) 151349 262144 1 262144 370775 524288 19592959 20392181760 56116425475 137438953472 198654375885 356379206352896 qz289 (@Enclosure.Real.IsNear.recentre' (Real.cos qz154) Bool.false 370775 524288 39185918 40784363520 370775 524288 19592959 20392181760 (ep496 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz24 (@Neg.neg Real Real.instNeg (Real.sin qz154)) 151349 262144 1 262144 370679 524288 19592959 20392181760 56101895971 137438953472 198654126957 356379206352896 qz289 (@Enclosure.Real.IsNear.neg (Real.sin qz154) Bool.true 370679 524288 19592959 20392181760 (@Enclosure.Real.IsNear.recentre' (Real.sin qz154) Bool.true 370679 524288 39185918 40784363520 370679 524288 19592959 20392181760 (ep501 rfl rfl) rfl)) rfl)

noncomputable def ep503 := @ep478 56116425475 137438953472 198654375885 356379206352896 Bool.false 56101895971 137438953472 198654126957 356379206352896 Bool.false 9037743596191906529280 263032957335 137438953472 1325248598105 1069137619058688 Bool.true 198827852454428672 11851063517 137438953472 662591934523 534568809529344 (ep479 (BSN.head_sum_c_succ qz142 2 3 rfl rfl) (ep492 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep493 ep502) rfl rfl

noncomputable abbrev qz155 := (@HMul.hMul Real Real Real qz262 qz383 (Real.log (Enclosure.sfrac Bool.false 4 1)))

noncomputable def ep504 := @Enclosure.Complex.IsNear.of_eq qz147 (Complex.mk (@HMul.hMul Real Real Real qz0 qz30 (Real.cos qz155)) (@HMul.hMul Real Real Real qz0 qz30 (@Neg.neg Real Real.instNeg (Real.sin qz155)))) Bool.false 3048985233 274877906944 5136629031841 10691376190586880 Bool.true 68702175297 137438953472 2578281884753 5345688095293440 (BSN.cpow_neg_s_mk qz151 73635 1000 4 qz152 rfl)

noncomputable def ep505 := nat_lit 17130117241881589006671102176957459857268784551539517552193945432527126147041

noncomputable def ep506 := nat_lit 58443294871560821445559008330705478148424697579131070391317059268343508961

noncomputable def ep507 := nat_lit 51273465135901645377122188514210968615509504259460290515799202179044691423201

noncomputable def ep508 := BSN.cos_dyadic_bound_f 1662806971 1073741824 3 2 524288 155732 ep505 ep78 ep506 ep507 ep80 ep506 11631 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1662806971) qz283 0 2 ep505 ep78 ep506 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1662806971) qz284 0 2 ep507 ep80 ep506 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz388 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 6689887) (@Nat.cast Real Real.instNatCast 65536))

noncomputable abbrev qz389 := (@Nat.cast Real Real.instNatCast 9444732965739290427392)

noncomputable def ep509 := @Enclosure.Real.IsNear.cos_image qz155 qz388 Bool.false 6689887 65536 497 524288 Bool.false 11631 524288 1 77790 (@Enclosure.Real.IsNear.recentre' qz155 Bool.false 334494351 3276800 4909 5186000 6689887 65536 497 524288 (@Enclosure.Real.IsNear.mulLit_ff qz151 qz32 73635 1000 0 1 363408 262144 1 77790 334494351 3276800 4909 5186000 qz153 qz292 rfl) rfl) (Enclosure.sfrac_false_div 6689887 65536) (BSN.cos_reduce0 qz388 (@HDiv.hDiv Real Real Real qz2 qz386 qz389) 226375608064910080 72057594037927936 Bool.false 11631 524288 16 1000000000000000 155580 77790 (BSN.sin_reduce_arg_pos_rat_q0 6689887 65536 226375608064910080 72057594037927936 16 14626204802138603782144 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 11631 524288 14626204802138603782144 9444732965739290427392 1662806971 1073741824 155732 155580 (ep508 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep510 := nat_lit 30787456399489611554851536711858863360565072434707826737636048131134152257505

noncomputable def ep511 := nat_lit 80539191902204550837508833946142547551144406866249524484603707961774033088481

noncomputable def ep512 := BSN.sin_dyadic_bound_f 1662806971 1073741824 3 2 524288 155732 ep510 ep71 ep506 ep511 ep74 ep506 524158 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1662806971) qz277 0 2 ep510 ep71 ep506 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1662806971) qz278 0 2 ep511 ep74 ep506 rfl rfl rfl rfl) rfl rfl

noncomputable def ep513 := @Enclosure.Real.IsNear.sin_image qz155 qz388 Bool.false 6689887 65536 497 524288 Bool.false 524158 524288 1 77790 (@Enclosure.Real.IsNear.recentre' qz155 Bool.false 334494351 3276800 4909 5186000 6689887 65536 497 524288 (@Enclosure.Real.IsNear.mulLit_ff qz151 qz32 73635 1000 0 1 363408 262144 1 77790 334494351 3276800 4909 5186000 qz153 qz292 rfl) rfl) (Enclosure.sfrac_false_div 6689887 65536) (BSN.sin_reduce0 qz388 (@HDiv.hDiv Real Real Real qz2 qz386 qz389) 226375608064910080 72057594037927936 Bool.false 524158 524288 16 1000000000000000 155580 77790 (BSN.sin_reduce_arg_pos_rat_q0 6689887 65536 226375608064910080 72057594037927936 16 14626204802138603782144 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 524158 524288 14626204802138603782144 9444732965739290427392 1662806971 1073741824 155732 155580 (ep512 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep514 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz30 (Real.cos qz155)) (@HMul.hMul Real Real Real qz0 qz30 (@Neg.neg Real Real.instNeg (Real.sin qz155))) Bool.false 3048985233 274877906944 5136629031841 10691376190586880 Bool.true 68702175297 137438953472 2578281884753 5345688095293440 (@Enclosure.Real.IsNear.mulLit_ff qz30 (Real.cos qz155) 262143 524288 1 524288 11631 524288 19592959 20392181760 3048985233 274877906944 5136629031841 10691376190586880 qz294 (@Enclosure.Real.IsNear.recentre' (Real.cos qz155) Bool.false 11631 524288 39185918 40784363520 11631 524288 19592959 20392181760 (ep509 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz30 (@Neg.neg Real Real.instNeg (Real.sin qz155)) 262143 524288 1 524288 262079 262144 19592959 20392181760 68702175297 137438953472 2578281884753 5345688095293440 qz294 (@Enclosure.Real.IsNear.neg (Real.sin qz155) Bool.false 262079 262144 19592959 20392181760 (@Enclosure.Real.IsNear.recentre' (Real.sin qz155) Bool.false 524158 524288 39185918 40784363520 262079 262144 19592959 20392181760 (ep513 rfl rfl) rfl)) rfl)

noncomputable def ep515 := @ep476 3048985233 274877906944 5136629031841 10691376190586880 Bool.true 68702175297 137438953472 2578281884753 5345688095293440 Bool.false 72720998109110354313216 529114899903 274877906944 6129705004297 3563792063528960 Bool.true 11071152841376250462208 40276619407 68719476736 3068067076661 1781896031764480 (ep477 (BSN.head_sum_c_succ qz142 3 4 rfl rfl) (ep503 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep504 ep514) rfl rfl

noncomputable abbrev qz156 := (@HMul.hMul Real Real Real qz262 qz383 (Real.log (Enclosure.sfrac Bool.false 5 1)))

noncomputable def ep516 := @Enclosure.Complex.IsNear.of_eq qz146 (Complex.mk (@HMul.hMul Real Real Real qz0 qz33 (Real.cos qz156)) (@HMul.hMul Real Real Real qz0 qz33 (@Neg.neg Real Real.instNeg (Real.sin qz156)))) Bool.false 79296243455 274877906944 921423038251 2138275238117376 Bool.false 93934143125 274877906944 921908681221 2138275238117376 (BSN.cpow_neg_s_mk qz151 73635 1000 5 qz152 rfl)

noncomputable def ep517 := nat_lit 321154390293084568224635264786497536

noncomputable def ep518 := BSN.sin_dyadic_bound_f 752798016 1073741824 2 1 524288 155732 ep517 ep57 ep517 ep517 ep58 ep517 338195 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 752798016) qz277 0 1 ep517 ep57 ep517 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 752798016) qz278 0 1 ep517 ep58 ep517 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz390 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 31066901) qz20)

noncomputable def ep519 := @Enclosure.Real.IsNear.cos_image qz156 qz390 Bool.false 31066901 262144 497 524288 Bool.false 338195 524288 1 77790 (@Enclosure.Real.IsNear.recentre' qz156 Bool.false 388336263 3276800 4909 5186000 31066901 262144 497 524288 (@Enclosure.Real.IsNear.mulLit_ff qz151 qz35 73635 1000 0 1 421904 262144 1 77790 388336263 3276800 4909 5186000 qz153 qz297 rfl) rfl) (Enclosure.sfrac_false_div 31066901 262144) (BSN.cos_reduce3 qz390 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 26486725506410764828672) qz282) 226375608064910080 72057594037927936 Bool.false 338195 524288 18 1000000000000000 155580 77790 (BSN.sin_reduce_arg_pos_rat_q3 31066901 262144 226375608064910080 72057594037927936 18 26486725506410764828672 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 338195 524288 26486725506410764828672 37778931862957161709568 752798016 1073741824 155732 155580 (ep518 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep520 := BSN.cos_dyadic_bound_f 752798016 1073741824 2 1 524288 155732 ep517 ep61 ep517 ep517 ep62 ep517 400625 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 752798016) qz283 0 1 ep517 ep61 ep517 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 752798016) qz284 0 1 ep517 ep62 ep517 rfl rfl rfl rfl) rfl rfl

noncomputable def ep521 := @Enclosure.Real.IsNear.sin_image qz156 qz390 Bool.false 31066901 262144 497 524288 Bool.true 400625 524288 1 77790 (@Enclosure.Real.IsNear.recentre' qz156 Bool.false 388336263 3276800 4909 5186000 31066901 262144 497 524288 (@Enclosure.Real.IsNear.mulLit_ff qz151 qz35 73635 1000 0 1 421904 262144 1 77790 388336263 3276800 4909 5186000 qz153 qz297 rfl) rfl) (Enclosure.sfrac_false_div 31066901 262144) (BSN.sin_reduce3 qz390 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 26486725506410764828672) qz282) 226375608064910080 72057594037927936 Bool.false 400625 524288 18 1000000000000000 155580 77790 (BSN.sin_reduce_arg_pos_rat_q3 31066901 262144 226375608064910080 72057594037927936 18 26486725506410764828672 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 400625 524288 26486725506410764828672 37778931862957161709568 752798016 1073741824 155732 155580 (ep520 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep522 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz33 (Real.cos qz156)) (@HMul.hMul Real Real Real qz0 qz33 (@Neg.neg Real Real.instNeg (Real.sin qz156))) Bool.false 79296243455 274877906944 921423038251 2138275238117376 Bool.false 93934143125 274877906944 921908681221 2138275238117376 (@Enclosure.Real.IsNear.mulLit_ff qz33 (Real.cos qz156) 234469 524288 1 524288 338195 524288 19592959 20392181760 79296243455 274877906944 921423038251 2138275238117376 qz298 (@Enclosure.Real.IsNear.recentre' (Real.cos qz156) Bool.false 338195 524288 39185918 40784363520 338195 524288 19592959 20392181760 (ep519 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz33 (@Neg.neg Real Real.instNeg (Real.sin qz156)) 234469 524288 1 524288 400625 524288 19592959 20392181760 93934143125 274877906944 921908681221 2138275238117376 qz298 (@Enclosure.Real.IsNear.neg (Real.sin qz156) Bool.true 400625 524288 19592959 20392181760 (@Enclosure.Real.IsNear.recentre' (Real.sin qz156) Bool.true 400625 524288 39185918 40784363520 400625 524288 19592959 20392181760 (ep521 rfl rfl) rfl)) rfl)

noncomputable def ep523 := @ep474 79296243455 274877906944 921423038251 2138275238117376 Bool.false 93934143125 274877906944 921908681221 2138275238117376 Bool.false 167238781647652967677952 304205571679 137438953472 11498115102073 5345688095293440 Bool.true 4616047678181718622208 67172334503 274877906944 23017945866071 10691376190586880 (ep475 (BSN.head_sum_c_succ qz142 4 5 rfl rfl) (ep515 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep516 ep522) rfl rfl

noncomputable abbrev qz157 := (@HMul.hMul Real Real Real qz262 qz383 (Real.log (Enclosure.sfrac Bool.false 6 1)))

noncomputable def ep524 := @Enclosure.Complex.IsNear.of_eq qz145 (Complex.mk (@HMul.hMul Real Real Real qz0 qz36 (Real.cos qz157)) (@HMul.hMul Real Real Real qz0 qz36 (@Neg.neg Real Real.instNeg (Real.sin qz157)))) Bool.false 112211444023 274877906944 844478601235 2138275238117376 Bool.false 1206537843 274877906944 840444256255 2138275238117376 (BSN.cpow_neg_s_mk qz151 73635 1000 6 qz152 rfl)

noncomputable def ep525 := @Enclosure.Real.IsNear.mulLit_ff qz151 qz38 73635 1000 0 1 4034681531866359 2251799813685248 50000000007779 3889500000000000000 59418754919795868993 450359962737049600 245450000038187111 259300000000000000000 qz153 (BSN.isNear_log_sfrac 6 1 4034681531866359 2251799813685248 50000000007779 3889500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz300) Bool.false 16922680887833197019136 9444732965739290427392 1000000000155580 77790000000000000000 4034681531866359 2251799813685248 50000000007779 3889500000000000000 (BSN.log_rat_reduce_isNear 6 1 2 12 8 106290 262144 24973259072661432 36028797018963968 77790 1000000000000000 rfl rfl rfl rfl (ep120 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep526 := nat_lit 31708585469789823312195426373539653331657060553103638699806107512787356176705

noncomputable def ep527 := nat_lit 61985709412126387378916539720751332128423561389955703463403475351246295361

noncomputable def ep528 := nat_lit 82945937462782284999993585152103589902322472825401982598646675954350581698881

noncomputable def ep529 := BSN.sin_dyadic_bound_f 1675083447 1073741824 3 2 524288 155732 ep526 ep71 ep527 ep528 ep74 ep527 524257 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1675083447) qz277 0 2 ep526 ep71 ep527 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1675083447) qz278 0 2 ep528 ep74 ep527 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz391 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 34586267) qz20)

noncomputable def ep530 := @Enclosure.Real.IsNear.cos_image qz157 qz391 Bool.false 34586267 262144 249 262144 Bool.false 524257 524288 1 77790 (@Enclosure.Real.IsNear.recentre' qz157 Bool.false 59418754919795868993 450359962737049600 245450000038187111 259300000000000000000 34586267 262144 249 262144 (ep525 rfl) rfl) (Enclosure.sfrac_false_div 34586267 262144) (BSN.cos_reduce3 qz391 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 58936759299641037553664) qz282) 226375608064910080 72057594037927936 Bool.false 524257 524288 20 1000000000000000 155580 77790 (BSN.sin_reduce_arg_pos_rat_q3 34586267 262144 226375608064910080 72057594037927936 20 58936759299641037553664 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 524257 524288 58936759299641037553664 37778931862957161709568 1675083447 1073741824 155732 155580 (ep529 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep531 := nat_lit 17643430020733069123388088669620141331866555223453112923653794607260196229441

noncomputable def ep532 := nat_lit 52806318643374954595406432929418921331342818547579427364034576871078096097601

noncomputable def ep533 := BSN.cos_dyadic_bound_f 1675083447 1073741824 3 2 524288 155732 ep531 ep78 ep527 ep532 ep80 ep527 5637 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1675083447) qz283 0 2 ep531 ep78 ep527 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1675083447) qz284 0 2 ep532 ep80 ep527 rfl rfl rfl rfl) rfl rfl

noncomputable def ep534 := @Enclosure.Real.IsNear.sin_image qz157 qz391 Bool.false 34586267 262144 249 262144 Bool.true 5637 524288 1 77790 (@Enclosure.Real.IsNear.recentre' qz157 Bool.false 59418754919795868993 450359962737049600 245450000038187111 259300000000000000000 34586267 262144 249 262144 (ep525 rfl) rfl) (Enclosure.sfrac_false_div 34586267 262144) (BSN.sin_reduce3 qz391 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 58936759299641037553664) qz282) 226375608064910080 72057594037927936 Bool.false 5637 524288 20 1000000000000000 155580 77790 (BSN.sin_reduce_arg_pos_rat_q3 34586267 262144 226375608064910080 72057594037927936 20 58936759299641037553664 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 5637 524288 58936759299641037553664 37778931862957161709568 1675083447 1073741824 155732 155580 (ep533 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep535 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz36 (Real.cos qz157)) (@HMul.hMul Real Real Real qz0 qz36 (@Neg.neg Real Real.instNeg (Real.sin qz157))) Bool.false 112211444023 274877906944 844478601235 2138275238117376 Bool.false 1206537843 274877906944 840444256255 2138275238117376 (@Enclosure.Real.IsNear.mulLit_ff qz36 (Real.cos qz157) 214039 524288 1 524288 524257 524288 9815927 10196090880 112211444023 274877906944 844478601235 2138275238117376 qz302 (@Enclosure.Real.IsNear.recentre' (Real.cos qz157) Bool.false 524257 524288 19631854 20392181760 524257 524288 9815927 10196090880 (ep530 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz36 (@Neg.neg Real Real.instNeg (Real.sin qz157)) 214039 524288 1 524288 5637 524288 9815927 10196090880 1206537843 274877906944 840444256255 2138275238117376 qz302 (@Enclosure.Real.IsNear.neg (Real.sin qz157) Bool.true 5637 524288 9815927 10196090880 (@Enclosure.Real.IsNear.recentre' (Real.sin qz157) Bool.true 5637 524288 19631854 20392181760 5637 524288 9815927 10196090880 (ep534 rfl rfl) rfl)) rfl)

noncomputable def ep536 := @ep472 112211444023 274877906944 844478601235 2138275238117376 Bool.false 1206537843 274877906944 840444256255 2138275238117376 Bool.false 99041614257929513336832 720622587381 274877906944 27218623210321 10691376190586880 Bool.true 18132540115794306007040 16491449165 68719476736 13610083573673 5345688095293440 (ep473 (BSN.head_sum_c_succ qz142 5 6 rfl rfl) (ep523 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep524 ep535) rfl rfl

noncomputable abbrev qz158 := (@HMul.hMul Real Real Real qz262 qz383 (Real.log (Enclosure.sfrac Bool.false 7 1)))

noncomputable def ep537 := @Enclosure.Complex.IsNear.of_eq qz144 (Complex.mk (@HMul.hMul Real Real Real qz0 qz39 (Real.cos qz158)) (@HMul.hMul Real Real Real qz0 qz39 (@Neg.neg Real Real.instNeg (Real.sin qz158)))) Bool.false 35075049163 274877906944 3889503581171 10691376190586880 Bool.false 48897314739 137438953472 1950907021573 5345688095293440 (BSN.cpow_neg_s_mk qz151 73635 1000 7 qz152 rfl)

noncomputable def ep538 := @Enclosure.Real.IsNear.mulLit_ff qz151 qz41 73635 1000 0 1 4381792198794487 2251799813685248 50000000007779 3889500000000000000 64530653711646410049 450359962737049600 245450000038187111 259300000000000000000 qz153 (BSN.isNear_log_sfrac 7 1 4381792198794487 2251799813685248 50000000007779 3889500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz304) Bool.false 18378568546572512002048 9444732965739290427392 1000000000155580 77790000000000000000 4381792198794487 2251799813685248 50000000007779 3889500000000000000 (BSN.log_rat_reduce_isNear 7 1 2 14 8 146699 262144 24973259072661432 36028797018963968 77790 1000000000000000 rfl rfl rfl rfl (ep131 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep539 := nat_lit 18693712907222929456995996337890625

noncomputable def ep540 := BSN.sin_dyadic_bound_f 369763375 1073741824 2 1 524288 155732 ep539 ep57 ep539 ep539 ep58 ep539 177001 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 369763375) qz277 0 1 ep539 ep57 ep539 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 369763375) qz278 0 1 ep539 ep58 ep539 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz392 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 4695223) (@Nat.cast Real Real.instNatCast 32768))

noncomputable def ep541 := @Enclosure.Real.IsNear.cos_image qz158 qz392 Bool.false 4695223 32768 497 524288 Bool.false 177001 524288 1 77790 (@Enclosure.Real.IsNear.recentre' qz158 Bool.false 64530653711646410049 450359962737049600 245450000038187111 259300000000000000000 4695223 32768 497 524288 (ep538 rfl) rfl) (Enclosure.sfrac_false_div 4695223 32768) (BSN.cos_reduce3 qz392 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 1626236521625646268416) qz369) 226375608064910080 72057594037927936 Bool.false 177001 524288 22 1000000000000000 155580 77790 (BSN.sin_reduce_arg_pos_rat_q3 4695223 32768 226375608064910080 72057594037927936 22 1626236521625646268416 4722366482869645213696 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 177001 524288 1626236521625646268416 4722366482869645213696 369763375 1073741824 155732 155580 (ep540 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep542 := BSN.cos_dyadic_bound_f 369763375 1073741824 2 1 524288 155732 ep539 ep61 ep539 ep539 ep62 ep539 493506 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 369763375) qz283 0 1 ep539 ep61 ep539 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 369763375) qz284 0 1 ep539 ep62 ep539 rfl rfl rfl rfl) rfl rfl

noncomputable def ep543 := @Enclosure.Real.IsNear.sin_image qz158 qz392 Bool.false 4695223 32768 497 524288 Bool.true 493506 524288 1 77790 (@Enclosure.Real.IsNear.recentre' qz158 Bool.false 64530653711646410049 450359962737049600 245450000038187111 259300000000000000000 4695223 32768 497 524288 (ep538 rfl) rfl) (Enclosure.sfrac_false_div 4695223 32768) (BSN.sin_reduce3 qz392 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 1626236521625646268416) qz369) 226375608064910080 72057594037927936 Bool.false 493506 524288 22 1000000000000000 155580 77790 (BSN.sin_reduce_arg_pos_rat_q3 4695223 32768 226375608064910080 72057594037927936 22 1626236521625646268416 4722366482869645213696 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 493506 524288 1626236521625646268416 4722366482869645213696 369763375 1073741824 155732 155580 (ep542 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep544 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz39 (Real.cos qz158)) (@HMul.hMul Real Real Real qz0 qz39 (@Neg.neg Real Real.instNeg (Real.sin qz158))) Bool.false 35075049163 274877906944 3889503581171 10691376190586880 Bool.false 48897314739 137438953472 1950907021573 5345688095293440 (@Enclosure.Real.IsNear.mulLit_ff qz39 (Real.cos qz158) 198163 524288 1 524288 177001 524288 19592959 20392181760 35075049163 274877906944 3889503581171 10691376190586880 qz306 (@Enclosure.Real.IsNear.recentre' (Real.cos qz158) Bool.false 177001 524288 39185918 40784363520 177001 524288 19592959 20392181760 (ep541 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz39 (@Neg.neg Real Real.instNeg (Real.sin qz158)) 198163 524288 1 524288 246753 262144 19592959 20392181760 48897314739 137438953472 1950907021573 5345688095293440 qz306 (@Enclosure.Real.IsNear.neg (Real.sin qz158) Bool.true 246753 262144 19592959 20392181760 (@Enclosure.Real.IsNear.recentre' (Real.sin qz158) Bool.true 493506 524288 39185918 40784363520 246753 262144 19592959 20392181760 (ep543 rfl rfl) rfl)) rfl)

noncomputable def ep545 := @ep470 35075049163 274877906944 3889503581171 10691376190586880 Bool.false 48897314739 137438953472 1950907021573 5345688095293440 Bool.false 207724584615742365761536 11807775571 4294967296 2592343899291 890948015882240 Bool.false 1093630368185292161024 15914416409 137438953472 2593498432541 890948015882240 (ep471 (BSN.head_sum_c_succ qz142 6 7 rfl rfl) (ep536 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep537 ep544) rfl rfl

noncomputable abbrev qz159 := (@HMul.hMul Real Real Real qz262 qz383 (Real.log (Enclosure.sfrac Bool.false 8 1)))

noncomputable def ep546 := @Enclosure.Complex.IsNear.of_eq qz143 (Complex.mk (@HMul.hMul Real Real Real qz0 qz42 (Real.cos qz159)) (@HMul.hMul Real Real Real qz0 qz42 (@Neg.neg Real Real.instNeg (Real.sin qz159)))) Bool.true 66416860441 274877906944 1215255200947 3563792063528960 Bool.true 70946761435 274877906944 1215572039617 3563792063528960 (BSN.cpow_neg_s_mk qz151 73635 1000 8 qz152 rfl)

noncomputable def ep547 := @Enclosure.Real.IsNear.mulLit_ff qz151 qz44 73635 1000 0 1 9364972152248037 4503599627370496 100000000023337 7779000000000000000 137917944886156840899 900719925474099200 490900000114561333 518600000000000000000 qz153 (BSN.isNear_log_sfrac 8 1 9364972152248037 4503599627370496 100000000023337 7779000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz308) Bool.false 19639770079031275290624 9444732965739290427392 1000000000233370 77790000000000000000 9364972152248037 4503599627370496 100000000023337 7779000000000000000 (BSN.log_rat_reduce_isNear 8 1 3 16 16 0 262144 24973259072661432 36028797018963968 77790 1000000000000000 rfl rfl rfl rfl (ep141 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep548 := nat_lit 426059804857313052764673737999650816

noncomputable def ep549 := BSN.sin_dyadic_bound_f 807918664 1073741824 2 1 524288 155732 ep548 ep57 ep548 ep548 ep58 ep548 358307 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 807918664) qz277 0 1 ep548 ep57 ep548 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 807918664) qz278 0 1 ep548 ep58 ep548 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz393 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 80278809) qz27)

noncomputable def ep550 := @Enclosure.Real.IsNear.cos_image qz159 qz393 Bool.false 80278809 524288 497 524288 Bool.true 358307 524288 1 77790 (@Enclosure.Real.IsNear.recentre' qz159 Bool.false 137917944886156840899 900719925474099200 490900000114561333 518600000000000000000 80278809 524288 497 524288 (ep547 rfl) rfl) (Enclosure.sfrac_false_div 80278809 524288) (BSN.cos_reduce1 qz393 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 56852221830560185581568) qz29) 226375608064910080 72057594037927936 Bool.false 358307 524288 24 1000000000000000 155580 77790 (BSN.sin_reduce_arg_pos_rat_q1 80278809 524288 226375608064910080 72057594037927936 24 56852221830560185581568 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 358307 524288 56852221830560185581568 75557863725914323419136 807918664 1073741824 155732 155580 (ep549 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep551 := nat_lit 951616969388912689351423786284948953670422898604104123625256642886013812736

noncomputable def ep552 := nat_lit 181526957315051679190102772312841414268984085584859484330940537929465856

noncomputable def ep553 := nat_lit 2854487854252107964695891153310221178182730727641142651907108047582182506496

noncomputable def ep554 := BSN.cos_dyadic_bound_f 807918664 1073741824 3 2 524288 155732 ep551 ep78 ep552 ep553 ep80 ep552 382745 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 807918664) qz283 0 2 ep551 ep78 ep552 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 807918664) qz284 0 2 ep553 ep80 ep552 rfl rfl rfl rfl) rfl rfl

noncomputable def ep555 := @Enclosure.Real.IsNear.sin_image qz159 qz393 Bool.false 80278809 524288 497 524288 Bool.false 382745 524288 1 77790 (@Enclosure.Real.IsNear.recentre' qz159 Bool.false 137917944886156840899 900719925474099200 490900000114561333 518600000000000000000 80278809 524288 497 524288 (ep547 rfl) rfl) (Enclosure.sfrac_false_div 80278809 524288) (BSN.sin_reduce1 qz393 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 56852221830560185581568) qz29) 226375608064910080 72057594037927936 Bool.false 382745 524288 24 1000000000000000 155580 77790 (BSN.sin_reduce_arg_pos_rat_q1 80278809 524288 226375608064910080 72057594037927936 24 56852221830560185581568 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 382745 524288 56852221830560185581568 75557863725914323419136 807918664 1073741824 155732 155580 (ep554 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep556 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz42 (Real.cos qz159)) (@HMul.hMul Real Real Real qz0 qz42 (@Neg.neg Real Real.instNeg (Real.sin qz159))) Bool.true 66416860441 274877906944 1215255200947 3563792063528960 Bool.true 70946761435 274877906944 1215572039617 3563792063528960 (@Enclosure.Real.IsNear.mulLit_ft qz42 (Real.cos qz159) 185363 524288 1 524288 358307 524288 19592959 20392181760 66416860441 274877906944 1215255200947 3563792063528960 qz310 (@Enclosure.Real.IsNear.recentre' (Real.cos qz159) Bool.true 358307 524288 39185918 40784363520 358307 524288 19592959 20392181760 (ep550 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz42 (@Neg.neg Real Real.instNeg (Real.sin qz159)) 185363 524288 1 524288 382745 524288 19592959 20392181760 70946761435 274877906944 1215572039617 3563792063528960 qz310 (@Enclosure.Real.IsNear.neg (Real.sin qz159) Bool.false 382745 524288 19592959 20392181760 (@Enclosure.Real.IsNear.recentre' (Real.sin qz159) Bool.false 382745 524288 39185918 40784363520 382745 524288 19592959 20392181760 (ep555 rfl rfl) rfl)) rfl)

noncomputable def ep557 := @ep468 66416860441 274877906944 1215255200947 3563792063528960 Bool.true 70946761435 274877906944 1215572039617 3563792063528960 Bool.false 2960438391123883327488 689280776103 274877906944 11584630798111 3563792063528960 Bool.true 5376327171112880308224 39117928617 274877906944 11589565769781 3563792063528960 (ep469 (BSN.head_sum_c_succ qz142 7 8 rfl rfl) (ep545 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep546 ep556) rfl rfl

theorem EMRow18.d10 : Enclosure.Complex.IsNear qz141 Bool.false 689280776103 274877906944 11584630798111 3563792063528960 Bool.true 39117928617 274877906944 11589565769781 3563792063528960 := ep467 (BSN.head_sum_c_succ qz142 8 9 rfl rfl) (ep557 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable def ep558 := nat_lit 4172355234354856482540687453371

noncomputable def ep559 := nat_lit 1125280650220530322655674368000

noncomputable def ep560 := nat_lit 3851906537556055145597419987616635639

noncomputable def ep561 := nat_lit 567449408893096386254512673154662400000

noncomputable abbrev qz474 := (@HAdd.hAdd Complex Complex Complex qz479 (@HAdd.hAdd Complex Complex Complex qz479 qz482 (@HMul.hMul Complex Complex Complex qz481 Complex.I (@HDiv.hDiv Complex Complex Complex qz483 (↑qz486) (2 : Complex)))) (@Nat.cast Complex Complex.instNatCast 2))

noncomputable abbrev qz394 := qz474

noncomputable abbrev qz160 := (Complex.Stirling.logGammaStirling 1 qz394)

noncomputable abbrev qz475 := (@HAdd.hAdd Complex Complex Complex qz479 qz482 (@HMul.hMul Complex Complex Complex qz481 Complex.I (@HDiv.hDiv Complex Complex Complex qz483 (↑qz486) (2 : Complex))))

noncomputable abbrev qz395 := qz475

noncomputable abbrev qz161 := qz395

noncomputable abbrev qz162 := (@HMul.hMul Real Real Real qz262 (@HDiv.hDiv Real Real Real qz265 qz383 (2 : Real)) (Real.log Real.pi))

noncomputable def ep562 := Complex.re (@HMul.hMul Complex Complex Complex qz45 (Complex.exp (@HMul.hMul Complex Complex Complex qz45 Complex.I ↑(@HSub.hSub Real Real Real qz315 (Complex.im (@HSub.hSub Complex Complex Complex qz46 qz160 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz161 (@Nat.cast Complex Complex.instNatCast j))))) qz162))) (zetaApproximant qz142 1 15))

noncomputable def ep563 := @Enclosure.Real.IsNear.of_eq ep562 (@HSub.hSub Real Real Real qz315 (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz315 (Complex.im (@HSub.hSub Complex Complex Complex qz46 qz160 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz161 (@Nat.cast Complex Complex.instNatCast j))))) qz162)) (Complex.re (zetaApproximant qz142 1 15))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz315 (Complex.im (@HSub.hSub Complex Complex Complex qz46 qz160 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz161 (@Nat.cast Complex Complex.instNatCast j))))) qz162)) (Complex.im (zetaApproximant qz142 1 15))))

noncomputable def ep564 := nat_lit 4172359142356291737228751180897

noncomputable def ep565 := @Enclosure.Real.IsNear.subLit_tt_n (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz315 (Complex.im (@HSub.hSub Complex Complex Complex qz46 qz160 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz161 (@Nat.cast Complex Complex.instNatCast j))))) qz162)) (Complex.re (zetaApproximant qz142 1 15))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz315 (Complex.im (@HSub.hSub Complex Complex Complex qz46 qz160 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz161 (@Nat.cast Complex Complex.instNatCast j))))) qz162)) (Complex.im (zetaApproximant qz142 1 15))) ep564

noncomputable def ep566 := nat_lit 3845460047102981799507327028302661457

noncomputable def ep567 := nat_lit 1954000717627344031863763

noncomputable def ep568 := nat_lit 562640325110265161327837184000

noncomputable def ep569 := nat_lit 3223245226536673045046479656987091

noncomputable def ep570 := nat_lit 283724704446548193127256336577331200000

noncomputable def ep571 := nat_lit 2347535305532933039698233386345880582631917447868279947264000

noncomputable def ep572 := @Enclosure.Real.IsNear.mulLit_tf (Real.cos (@HSub.hSub Real Real Real qz315 (Complex.im (@HSub.hSub Complex Complex Complex qz46 qz160 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz161 (@Nat.cast Complex Complex.instNatCast j))))) qz162)) (Complex.re (zetaApproximant qz142 1 15)) 524287 524288 8935729

noncomputable def ep573 := nat_lit 7958158684759095184944031

noncomputable def ep574 := nat_lit 2146302509728489537536000

noncomputable def ep575 := nat_lit 47766978109543831863819521

noncomputable def ep576 := nat_lit 9275604012876622284718080000

noncomputable def ep577 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HSub.hSub Real Real Real qz315 (Complex.im (@HSub.hSub Complex Complex Complex qz46 qz160 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz161 (@Nat.cast Complex Complex.instNatCast j))))) qz162)) Bool.true 524287 524288 17871458

noncomputable abbrev qz396 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 14000295) qz20)

noncomputable def ep578 := @Enclosure.Real.IsNear.cos_image (@HSub.hSub Real Real Real qz315 (Complex.im (@HSub.hSub Complex Complex Complex qz46 qz160 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz161 (@Nat.cast Complex Complex.instNatCast j))))) qz162) qz396 Bool.false 14000295 262144 223

noncomputable def ep579 := nat_lit 13594787840000000000000000

noncomputable def ep580 := @Enclosure.Real.IsNear.recentre' (@HSub.hSub Real Real Real qz315 (Complex.im (@HSub.hSub Complex Complex Complex qz46 qz160 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz161 (@Nat.cast Complex Complex.instNatCast j))))) qz162) Bool.false 96209296696241339621 1801439850948198400 5755049914404341436821 ep579

noncomputable def ep581 := @Enclosure.Real.IsNear.subLit_ff_p (Complex.im (@HSub.hSub Complex Complex Complex qz46 qz160 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz161 (@Nat.cast Complex Complex.instNatCast j))))) qz162 172132929404483452133 1801439850948198400 1936338814404341436821 ep579 1104834267 26214400

noncomputable def ep582 := nat_lit 2522068987313948973360742400

noncomputable def ep583 := nat_lit 16993484800000000000000000

noncomputable def ep584 := @Enclosure.Complex.IsNear.im_isNear (@HSub.hSub Complex Complex Complex qz46 qz160 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz161 (@Nat.cast Complex Complex.instNatCast j)))) Bool.true 5207547144189125249 90071992547409920 4291083735537462512687 ep583 Bool.false 172132929404483452133 1801439850948198400

noncomputable def ep585 := nat_lit 50980454400000000000000000

noncomputable def ep586 := @Enclosure.Complex.IsNear.subLitP qz160 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz161 (@Nat.cast Complex Complex.instNatCast j))) Bool.true 4557898896746971529 90071992547409920 12545571206102582994061 ep585 Bool.false 177718954692742850533 1801439850948198400 5284728443172239946943

noncomputable def ep587 := nat_lit 40784363520000000000000000

noncomputable def ep588 := nat_lit 11726353689042217537793088135626752

noncomputable def ep589 := nat_lit 48451112295263973060405915967029248

noncomputable abbrev qz397 := (@HSub.hSub Complex Complex Complex qz463 qz474 qz466)

noncomputable abbrev qz398 := (Complex.log qz474)

noncomputable abbrev qz163 := (@HSub.hSub Complex Complex Complex qz312 (@HMul.hMul Complex Complex Complex qz311 qz397 qz398) qz394)

noncomputable abbrev qz164 := qz394

noncomputable def ep590 := @Enclosure.Complex.IsNear.of_eq qz160 (@HAdd.hAdd Complex Complex Complex qz5 (@HAdd.hAdd Complex Complex Complex qz5 qz163 qz51) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz53 2 k))) (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz45 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz54 qz164 (@HSub.hSub Int Int Int qz324 qz56 (@HMul.hMul Int Int Int qz325 qz57 (@Nat.cast Int instNatCastInt k)))))) Bool.true 4557898896746971529

noncomputable def ep591 := @Enclosure.Complex.IsNear.addLitP (@HAdd.hAdd Complex Complex Complex qz5 qz163 qz51) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz53 2 k))) (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz45 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz54 qz164 (@HSub.hSub Int Int Int qz324 qz56 (@HMul.hMul Int Int Int qz325 qz57 (@Nat.cast Int instNatCastInt k))))) Bool.true 4557911309380714889 90071992547409920

noncomputable def ep592 := nat_lit 39152053400005447008196231168

noncomputable def ep593 := nat_lit 152659419656927254315410233753600

noncomputable def ep594 := @ep591 1531439624192451833 6223200000000000000000 Bool.false 177723016934012594149 1801439850948198400 80635000115105863 622320000000000000000 Bool.false 1183761 8589934592 3 8589934592 Bool.true 1937027583 858993459200 4909 858993459200 Bool.true ep592 4557898896746971529 90071992547409920 12545571206102582994061 ep585 Bool.false ep593

noncomputable def ep595 := @Enclosure.Complex.IsNear.addLitP qz163 qz51 Bool.true 4640681857524924809 90071992547409920 1507700000169014333 6223200000000000000000

noncomputable def ep596 := @ep595 Bool.false 177723016934012594149 1801439850948198400 80635000115105863 622320000000000000000 Bool.false 120447 131072 1 262144 Bool.false 0 1 0 1 Bool.true 597414551143149061931008 4557911309380714889 90071992547409920 1531439624192451833 6223200000000000000000 Bool.false 177723016934012594149 177723016934012594149 1801439850948198400

noncomputable abbrev qz165 := (@HMul.hMul Complex Complex Complex qz311 qz397 qz398)

noncomputable def ep597 := @Enclosure.Complex.IsNear.subLitP qz165 qz164 Bool.true 4438019874293252489 90071992547409920 1507700000169014333 6223200000000000000000 Bool.false 244047528646297888741

noncomputable def ep598 := @ep597 1801439850948198400 80635000115105863 622320000000000000000 Bool.false 9000 4000 0 1 Bool.false 147270 4000 0 1 Bool.true 18562727430099699236000 4640681857524924809 90071992547409920 1507700000169014333 6223200000000000000000 Bool.false 710892067736050376596000 177723016934012594149 1801439850948198400 80635000115105863 622320000000000000000

noncomputable abbrev qz166 := qz397

noncomputable abbrev qz167 := qz398

noncomputable def ep599 := @Enclosure.Complex.IsNear.mul qz166 qz167 Bool.true 4438019874293252489 90071992547409920 1507700000169014333 6223200000000000000000 Bool.false 244047528646297888741 1801439850948198400 80635000115105863

noncomputable abbrev qz168 := (Complex.re qz397)

noncomputable abbrev qz169 := (Complex.re qz398)

noncomputable abbrev qz170 := (Complex.im qz397)

noncomputable abbrev qz171 := (Complex.im qz398)

noncomputable def ep600 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 qz168 qz169) (@HMul.hMul Real Real Real qz0 qz170 qz171) 113737749526934981 18014398509481984 35000000054453 6223200000000000000 2503354310963963697 45035996273704960

noncomputable def ep601 := nat_lit 39974129304259894818846748954329088

noncomputable def ep602 := @Enclosure.Real.IsNear.mulLit_ff qz168 qz169 7000 4000 0 1 16248249932419283 4503599627370496 5000000007779 1555800000000000000

noncomputable def ep603 := @Enclosure.Complex.IsNear.re_isNear qz166 Bool.false 7000 4000 0 1 Bool.false 147270 4000 0 1

noncomputable abbrev qz399 := (Enclosure.sfrac Bool.false 147270 4000)

noncomputable abbrev qz172 := qz399

noncomputable def ep604 := @Enclosure.Complex.IsNear.of_eq qz166 (Complex.mk (Enclosure.sfrac Bool.false 7000 4000) qz172) Bool.false 7000 4000 0 1 Bool.false 147270 4000 0

noncomputable abbrev qz173 := (Complex.mk qz327 qz399)

noncomputable def ep605 := @Enclosure.Complex.IsNear.of_eq qz167 (Complex.log qz173) Bool.false 16248249932419283 4503599627370496 5000000007779 1555800000000000000 Bool.false 849919980635555 562949953421312 100000000007779 15558000000000000000

noncomputable def ep606 := nat_lit 323886156795824618099505280117597211929663347328713705000000000000

noncomputable def ep607 := nat_lit 2177117418528250907644929032709179128219670282478791000000000000

noncomputable def ep608 := nat_lit 365952443258372944763663647842192863557372444815000000000000

noncomputable def ep609 := BSN.log_dyadic_bound 5385452900 38153452900 4 3 ep606 524288 155580 ep607 ep608 149003 43538905800 32768000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 5385452900) (BSN.artanhQ 38153452900) 0 3 ep607 ep606 ep608 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz400 := (Real.log (Enclosure.sfrac Bool.false 21769452900 16000000))

noncomputable def ep610 := @Enclosure.Real.IsNear.mulLit_ff qz67 qz400 1 2 0 1 16248249932419283 2251799813685248 5000000007779 777900000000000000 16248249932419283 4503599627370496 5000000007779 1555800000000000000 qz329 (BSN.isNear_log_sfrac 21769452900 16000000 16248249932419283 2251799813685248 5000000007779 777900000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 21769452900) qz330)) Bool.false 136300199369091856728064 18889465931478580854784 1000000001555800 155580000000000000000 16248249932419283 2251799813685248 5000000007779 777900000000000000 (BSN.log_rat_reduce_isNear 21769452900 16000000 10 43538905800 32768000000 149003 524288 24973259072661432 36028797018963968 155580 1000000000000000 rfl rfl rfl rfl (ep609 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep611 := BSN.arctan_dyadic_bound_f 9000 147270 1 0 524288 155580 0 1 1 0 1 1 32000 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 9000) (BSN.arctanEvenQ 147270) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 9000) (BSN.arctanOddQ 147270) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz401 := (Real.arctan (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 9000) (@Nat.cast Real Real.instNatCast 147270)))

noncomputable def ep612 := @Enclosure.Real.IsNear.subLit_ff_p qz68 qz401 884279719003555 562949953421312 1 2000000000000000 32000 524288 1 155580 445602846807453859840 849919980635555 562949953421312 100000000007779 15558000000000000000 qz69 (ep611 rfl) rfl rfl

noncomputable abbrev qz402 := (Real.arctan (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 147270) (@Nat.cast Real Real.instNatCast 9000)))

noncomputable def ep613 := @Enclosure.Complex.IsNear.re_isNear qz167 Bool.false 16248249932419283 4503599627370496 5000000007779 1555800000000000000 Bool.false 849919980635555 562949953421312 100000000007779 15558000000000000000 (ep605 (@congrArg Complex Complex qz164 qz173 Complex.log (BSN.w_shift_mk qz151 Bool.false 73635 1000 2 qz152 rfl)) (@Enclosure.Complex.IsNear.of_parts (Complex.log qz173) Bool.false 16248249932419283 4503599627370496 5000000007779 1555800000000000000 Bool.false 849919980635555 562949953421312 100000000007779 15558000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re (Complex.log qz173)) (@HMul.hMul Real Real Real qz0 qz67 qz400) Bool.false 16248249932419283 4503599627370496 5000000007779 1555800000000000000 (Enclosure.clog_re_eq 9000 147270 4000 21769452900 16000000 rfl rfl rfl) (ep610 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im (Complex.log qz173)) qz402 Bool.false 849919980635555 562949953421312 100000000007779 15558000000000000000 (Enclosure.clog_im_eq 9000 147270 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz402 (@HSub.hSub Real Real Real qz315 qz68 qz401) Bool.false 849919980635555 562949953421312 100000000007779 15558000000000000000 (BSN.arctan_recip 147270 9000 rfl rfl) ep612))))

noncomputable def ep614 := @Enclosure.Real.IsNear.mulLit_ff qz170 qz171 147270 4000 0 1 849919980635555 562949953421312 100000000007779 15558000000000000000

noncomputable def ep615 := @Enclosure.Complex.IsNear.im_isNear qz166 Bool.false 7000 4000 0 1 Bool.false 147270 4000 0 1

noncomputable def ep616 := @Enclosure.Complex.IsNear.im_isNear qz167 Bool.false 16248249932419283 4503599627370496 5000000007779 1555800000000000000 Bool.false 849919980635555 562949953421312 100000000007779 15558000000000000000 (ep605 (@congrArg Complex Complex qz164 qz173 Complex.log (BSN.w_shift_mk qz151 Bool.false 73635 1000 2 qz152 rfl)) (@Enclosure.Complex.IsNear.of_parts (Complex.log qz173) Bool.false 16248249932419283 4503599627370496 5000000007779 1555800000000000000 Bool.false 849919980635555 562949953421312 100000000007779 15558000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re (Complex.log qz173)) (@HMul.hMul Real Real Real qz0 qz67 qz400) Bool.false 16248249932419283 4503599627370496 5000000007779 1555800000000000000 (Enclosure.clog_re_eq 9000 147270 4000 21769452900 16000000 rfl rfl rfl) (ep610 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im (Complex.log qz173)) qz402 Bool.false 849919980635555 562949953421312 100000000007779 15558000000000000000 (Enclosure.clog_im_eq 9000 147270 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz402 (@HSub.hSub Real Real Real qz315 qz68 qz401) Bool.false 849919980635555 562949953421312 100000000007779 15558000000000000000 (BSN.arctan_recip 147270 9000 rfl rfl) ep612))))

noncomputable abbrev qz403 := (Enclosure.Real.IsNear.const Bool.false 147270 4000)

noncomputable abbrev qz174 := (@ep604 1 (BSN.w_sub_half_mk qz383 Bool.false 73635 1000 2 qz384 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7000 4000) qz399 Bool.false 7000 4000 0 1 Bool.false 147270 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 7000 4000) qz403))

noncomputable def ep617 := @ep600 490900000038187111 2074400000000000000000 ep601 4438019874293252489 90071992547409920 1507700000169014333 6223200000000000000000 (@ep602 113737749526934981 18014398509481984 35000000054453 6223200000000000000 (ep603 qz174) ep613 rfl) (@ep614 2503354310963963697 45035996273704960 490900000038187111 2074400000000000000000 (ep615 qz174) ep616 rfl) rfl

noncomputable def ep618 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz168 qz171) (@HMul.hMul Real Real Real qz0 qz170 qz169) 5949439864448885 2251799813685248 700000000054453 62232000000000000000 239287976754738780741 1801439850948198400

noncomputable def ep619 := nat_lit 549546179536078809919096941096992768

noncomputable def ep620 := @Enclosure.Real.IsNear.mulLit_ff qz168 qz171 7000 4000 0 1 849919980635555 562949953421312 100000000007779 15558000000000000000

noncomputable def ep621 := @Enclosure.Real.IsNear.mulLit_ff qz170 qz169 147270 4000 0 1 16248249932419283 4503599627370496 5000000007779 1555800000000000000

noncomputable def ep622 := @ep618 24545000038187111 207440000000000000000 ep619 244047528646297888741 1801439850948198400 80635000115105863 622320000000000000000 (@ep620 5949439864448885 2251799813685248 700000000054453 62232000000000000000 (ep603 qz174) ep616 rfl) (@ep621 239287976754738780741 1801439850948198400 24545000038187111 207440000000000000000 (ep615 qz174) ep613 rfl) rfl

noncomputable def ep623 := @Enclosure.Complex.IsNear.of_eq qz164 qz173 Bool.false 9000 4000 0 1 Bool.false 147270 4000 0 1 (BSN.w_shift_mk qz151 Bool.false 73635 1000 2 qz152 rfl)

noncomputable abbrev qz404 := (ep623 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 9000 4000) (Enclosure.sfrac Bool.false 147270 4000) Bool.false 9000 4000 0 1 Bool.false 147270 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 9000 4000) (Enclosure.Real.IsNear.const Bool.false 147270 4000)))

noncomputable abbrev qz175 := qz404

noncomputable def ep624 := ep598 (@ep599 622320000000000000000 (ep617 rfl) (ep622 rfl)) qz175 rfl rfl rfl rfl rfl rfl

noncomputable def ep625 := @ep596 80635000115105863 622320000000000000000 (ep624 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@Enclosure.Complex.IsNear.mul qz72 (↑qz3) Bool.false 120447 131072 1 262144 Bool.false 0 1 0 1 (@ep220 131072 1 262144 (ep222 rfl) (ep224 rfl) rfl rfl) (@ep225 1 0 1 (ep227 rfl) (ep229 rfl) rfl rfl))

noncomputable abbrev qz405 := (@HPow.hPow Complex Int Complex qz468 qz474 (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) (@OfNat.ofNat Int 1 (@instOfNat 1)) (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (@OfNat.ofNat Int 2 (@instOfNat 2)) (@Nat.cast Int instNatCastInt 1))))

noncomputable abbrev qz176 := qz405

noncomputable def ep626 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz53 2 k))) (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz45 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz54 qz164 (@HSub.hSub Int Int Int qz324 qz56 (@HMul.hMul Int Int Int qz325 qz57 (@Nat.cast Int instNatCastInt k))))) (@HAdd.hAdd Complex Complex Complex qz5 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz53 2 k))) (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz45 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz54 qz164 (@HSub.hSub Int Int Int qz324 qz56 (@HMul.hMul Int Int Int qz325 qz57 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 (@Rat.cast Complex Complex.instRatCast (bernoulli qz74)) qz75) qz176)) Bool.false 1183761 8589934592 3 8589934592

noncomputable def ep627 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz53 2 k))) (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz45 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz54 qz164 (@HSub.hSub Int Int Int qz324 qz56 (@HMul.hMul Int Int Int qz325 qz57 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 (@Rat.cast Complex Complex.instRatCast (bernoulli qz74)) qz75) qz176) Bool.false 0 1 0 1 Bool.false

noncomputable def ep628 := @ep627 0 1 0 1 Bool.false 1183761 8589934592 3 8589934592 Bool.true 1937027583 858993459200 4909 858993459200 Bool.false 1183761 1183761 8589934592 3 8589934592 Bool.true 1937027583 1937027583 858993459200 4909

noncomputable def ep629 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz53 2 k))) (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz45 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz54 qz164 (@HSub.hSub Int Int Int qz324 qz56 (@HMul.hMul Int Int Int qz325 qz57 (@Nat.cast Int instNatCastInt k))))) (Complex.mk qz14 qz14) Bool.false 0 1 0 1 Bool.false

noncomputable def ep630 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz52 (@Rat.cast Complex Complex.instRatCast (bernoulli qz74)) qz75) qz176 Bool.false 1183761 8589934592 3 8589934592 Bool.true 1937027583 858993459200 4909 858993459200

noncomputable abbrev qz177 := (Complex.re qz405)

noncomputable abbrev qz178 := (Complex.im qz405)

noncomputable def ep631 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz52 (@Rat.cast Complex Complex.instRatCast (bernoulli qz74)) qz75)) qz177) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz52 (@Rat.cast Complex Complex.instRatCast (bernoulli qz74)) qz75)) qz178) 1183761 8589934592 3 8589934592 0 1 0

noncomputable def ep632 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz52 (@Rat.cast Complex Complex.instRatCast (bernoulli qz74)) qz75)) qz177 1 12 0 1 3551283 2147483648 9 2147483648 1183761

noncomputable def ep633 := @Enclosure.Complex.IsNear.re_isNear qz176 Bool.false 3551283 2147483648 9 2147483648 Bool.true 5811082749 214748364800 14727 214748364800

noncomputable abbrev qz406 := (@HPow.hPow Complex Nat Complex qz469 qz474 1)

noncomputable abbrev qz179 := (@Inv.inv Complex Complex.instInv qz406)

noncomputable def ep634 := @Enclosure.Complex.IsNear.of_eq qz176 qz179 Bool.false 3551283 2147483648 9 2147483648 Bool.true 5811082749 214748364800 14727

noncomputable def ep635 := @Enclosure.Complex.IsNear.of_parts qz179 Bool.false 3551283 2147483648 9 2147483648 Bool.true 5811082749 214748364800 14727

noncomputable abbrev qz180 := (Complex.re qz406)

noncomputable abbrev qz181 := qz406

noncomputable def ep636 := @Enclosure.Real.IsNear.mulLit_ff qz180 (@Inv.inv Real Real.instInv (@DFunLike.coe qz81 Complex (fun (x : Complex) => Real) qz82 Complex.normSq qz181)) 9000 4000 0 1 394587 536870912 1 536870912

noncomputable def ep637 := @Enclosure.Complex.IsNear.re_isNear qz181 Bool.false 9000 4000 0 1 Bool.false 147270 4000 0 1

noncomputable def ep638 := @Enclosure.Complex.IsNear.of_eq qz181 qz164 Bool.false 9000 4000 0 1 Bool.false 147270 4000 0

noncomputable def ep639 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (@DFunLike.coe qz81 Complex (fun (x : Complex) => Real) qz82 Complex.normSq qz181)) Bool.false 394587 536870912 1 536870912 394587 536870912 1

noncomputable abbrev qz182 := (Complex.im qz406)

noncomputable def ep640 := @Enclosure.Real.IsNear.of_eq (@DFunLike.coe qz81 Complex (fun (x : Complex) => Real) qz82 Complex.normSq qz181) (@HAdd.hAdd Real Real Real qz339 (@HMul.hMul Real Real Real qz0 qz180 qz180) (@HMul.hMul Real Real Real qz0 qz182 qz182)) Bool.false 217694529 160000 0 1

noncomputable def ep641 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz180 qz180) (@HMul.hMul Real Real Real qz0 qz182 qz182) 81 16 0 1 216884529 160000

noncomputable def ep642 := @Enclosure.Real.IsNear.mulLit_ff qz180 qz180 9000 4000 0 1 9000 4000 0 1

noncomputable def ep643 := @Enclosure.Real.IsNear.mulLit_ff qz182 qz182 147270 4000 0 1 147270 4000 0 1

noncomputable def ep644 := @Enclosure.Complex.IsNear.im_isNear qz181 Bool.false 9000 4000 0 1 Bool.false 147270 4000 0 1

noncomputable abbrev qz183 := (ep637 (@ep638 1 (BSN.pow_one_c qz394) qz404))

noncomputable abbrev qz184 := (ep644 (@ep638 1 (BSN.pow_one_c qz394) qz404))

noncomputable def ep645 := @ep641 0 1 3483112464 217694529 160000 0 1 (@ep642 81 16 0 1 qz183 qz183 rfl) (@ep643 216884529 160000 0 1 qz184 qz184 rfl)

noncomputable def ep646 := @Enclosure.Real.IsNear.inv_image (@DFunLike.coe qz81 Complex (fun (x : Complex) => Real) qz82 Complex.normSq qz181) 217694529 160000 0 1 197293 197294 268435456 (ep640 (Enclosure.Complex.normSq_eq_mul_add_mul qz181) (ep645 rfl rfl)) rfl

noncomputable def ep647 := @Enclosure.Real.IsNear.of_eq (Complex.re qz179) (@HMul.hMul Real Real Real qz0 qz180 (@Inv.inv Real Real.instInv (@DFunLike.coe qz81 Complex (fun (x : Complex) => Real) qz82 Complex.normSq qz181))) Bool.false 3551283 2147483648 9 2147483648 (Enclosure.Complex.inv_re_eq_mul qz181) (@ep636 3551283 2147483648 9 2147483648 qz183 (@ep639 536870912 (ep646 rfl rfl rfl rfl rfl) rfl) rfl)

noncomputable def ep648 := @Enclosure.Real.IsNear.of_eq (Complex.im qz179) (@HMul.hMul Real Real Real qz0 (@Neg.neg Real Real.instNeg qz182) (@Inv.inv Real Real.instInv (@DFunLike.coe qz81 Complex (fun (x : Complex) => Real) qz82 Complex.normSq qz181))) Bool.true 5811082749 214748364800 14727 214748364800 (Enclosure.Complex.inv_im_eq_mul qz181)

noncomputable def ep649 := @Enclosure.Real.IsNear.mulLit_tf (@Neg.neg Real Real.instNeg qz182) (@Inv.inv Real Real.instInv (@DFunLike.coe qz81 Complex (fun (x : Complex) => Real) qz82 Complex.normSq qz181)) 147270 4000 0 1 394587 536870912 1

noncomputable def ep650 := @ep649 536870912 5811082749 214748364800 14727 214748364800 (@Enclosure.Real.IsNear.neg qz182 Bool.false 147270 4000 0 1 qz184) (@ep639 536870912 (ep646 rfl rfl rfl rfl rfl) rfl) rfl

noncomputable def ep651 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz52 (@Rat.cast Complex Complex.instRatCast (bernoulli qz74)) qz75)) qz178 0 1 0 1 5811082749 214748364800 14727 214748364800 0

noncomputable def ep652 := @Enclosure.Complex.IsNear.im_isNear qz176 Bool.false 3551283 2147483648 9 2147483648 Bool.true 5811082749 214748364800 14727 214748364800

noncomputable abbrev qz185 := (@ep634 214748364800 (BSN.zpow_one_sub_two_mul qz394 1 1 rfl rfl) (@ep635 214748364800 ep647 (ep648 ep650)))

noncomputable def ep653 := @ep631 1 1183761 1183761 8589934592 3 8589934592 (@ep632 8589934592 3 8589934592 ep239 (ep633 qz185) rfl) (@ep651 1 0 1 ep259 (ep652 qz185) rfl) rfl

noncomputable def ep654 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz52 (@Rat.cast Complex Complex.instRatCast (bernoulli qz74)) qz75)) qz178) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz52 (@Rat.cast Complex Complex.instRatCast (bernoulli qz74)) qz75)) qz177) 1937027583 858993459200 4909 858993459200 0 1 0

noncomputable def ep655 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HDiv.hDiv Complex Complex Complex qz52 (@Rat.cast Complex Complex.instRatCast (bernoulli qz74)) qz75)) qz178 1 12 0 1 5811082749 214748364800 14727 214748364800 1937027583

noncomputable def ep656 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz52 (@Rat.cast Complex Complex.instRatCast (bernoulli qz74)) qz75)) qz177 0 1 0 1 3551283 2147483648 9 2147483648 0

noncomputable def ep657 := @ep654 1 1937027583 1937027583 858993459200 4909 858993459200 (@ep655 858993459200 4909 858993459200 ep239 (ep652 qz185) rfl) (@ep656 1 0 1 ep259 (ep633 qz185) rfl) rfl

noncomputable def ep658 := @ep628 858993459200 (@ep629 0 1 0 1 (BSN.stirling_sum_base qz164) qz88) (ep630 (ep653 rfl) (ep657 rfl)) rfl rfl rfl rfl rfl

noncomputable def ep659 := @ep594 177718954692742850533 1801439850948198400 5284728443172239946943 ep587 (ep625 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep626 Bool.true 1937027583 858993459200 4909 858993459200 (BSN.stirling_sum_succ qz164 0 1 rfl) (ep658 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl

noncomputable def ep660 := @Enclosure.Complex.IsNear.of_eq (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz161 (@Nat.cast Complex Complex.instNatCast j))) (BSN.logSumC qz151 2) Bool.false 16241206186053843 2251799813685248 5000000007779 777900000000000000 Bool.false 872816451290531 281474976710656

noncomputable abbrev qz186 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz268 qz395 qz335))

noncomputable def ep661 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz151 2) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.logSumC qz151 1) qz186) Bool.false 16241206186053843 2251799813685248 5000000007779 777900000000000000 Bool.false 872816451290531 281474976710656 100000000007779 7779000000000000000

noncomputable def ep662 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz151 1) qz186 Bool.false 16239960645538003 4503599627370496 5000000007779 1555800000000000000 Bool.false 880458271851939 562949953421312 100000000007779 15558000000000000000 Bool.false

noncomputable def ep663 := nat_lit 146287780255118963727649531232256

noncomputable def ep664 := nat_lit 982703961198718521042318393344

noncomputable abbrev qz187 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz268 qz395 (@Nat.cast Complex Complex.instNatCast 0)))

noncomputable def ep665 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz151 1) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.logSumC qz151 0) qz187) Bool.false 16239960645538003 4503599627370496 5000000007779 1555800000000000000 Bool.false 880458271851939 562949953421312 100000000007779 15558000000000000000

noncomputable def ep666 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz151 0) qz187 Bool.false 0 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable abbrev qz407 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz172))

noncomputable def ep667 := @Enclosure.Complex.IsNear.of_eq qz187 qz407 Bool.false 16239960645538003 4503599627370496 5000000007779 1555800000000000000 Bool.false 880458271851939 562949953421312 100000000007779 15558000000000000000

noncomputable def ep668 := nat_lit 319832718101888446484774846217285437889243588232713705000000000000

noncomputable def ep669 := nat_lit 2094604240920848505696167342766028298465722703278791000000000000

noncomputable def ep670 := nat_lit 334523043436708935757576056006158969534644444815000000000000

noncomputable def ep671 := BSN.log_dyadic_bound 5305452900 38073452900 4 3 ep668 524288 155580 ep669 ep670 147073 43378905800 32768000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 5305452900) (BSN.artanhQ 38073452900) 0 3 ep669 ep668 ep670 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep672 := @Enclosure.Real.IsNear.mulLit_ff qz67 (Real.log (Enclosure.sfrac Bool.false 21689452900 16000000)) 1 2 0 1 16239960645538003 2251799813685248 5000000007779 777900000000000000 16239960645538003 4503599627370496 5000000007779 1555800000000000000 qz329 (BSN.isNear_log_sfrac 21689452900 16000000 16239960645538003 2251799813685248 5000000007779 777900000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 21689452900) qz330)) Bool.false 136230663790845256269824 18889465931478580854784 1000000001555800 155580000000000000000 16239960645538003 2251799813685248 5000000007779 777900000000000000 (BSN.log_rat_reduce_isNear 21689452900 16000000 10 43378905800 32768000000 147073 524288 24973259072661432 36028797018963968 155580 1000000000000000 rfl rfl rfl rfl (ep671 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep673 := BSN.arctan_dyadic_bound_f 1000 147270 1 0 524288 155580 0 1 1 0 1 1 3559 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 147270) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 147270) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz408 := (@Nat.cast Real Real.instNatCast 147270)

noncomputable def ep674 := @Enclosure.Real.IsNear.subLit_ff_p qz68 (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz341 qz408)) 884279719003555 562949953421312 1 2000000000000000 3559 524288 1 155580 461613706432709394432 880458271851939 562949953421312 100000000007779 15558000000000000000 qz69 (ep673 rfl) rfl rfl

noncomputable abbrev qz188 := (@HAdd.hAdd Complex Complex Complex qz268 qz395 (@Nat.cast Complex Complex.instNatCast 0))

noncomputable abbrev qz409 := (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz172)

noncomputable def ep675 := @ep666 16239960645538003 4503599627370496 5000000007779 1555800000000000000 Bool.false 880458271851939 562949953421312 100000000007779 15558000000000000000 Bool.false 16239960645538003 16239960645538003 4503599627370496 5000000007779 1555800000000000000 Bool.false 880458271851939 880458271851939 562949953421312 100000000007779 15558000000000000000 (@Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz151 0) (Complex.mk qz14 qz14) Bool.false 0 1 0 1 Bool.false 0 1 0 1 (BSN.log_sum_c_base qz151) qz88) (ep667 (@congrArg Complex Complex qz188 qz409 Complex.log (BSN.w_shift_mk qz151 Bool.false 73635 1000 0 qz152 rfl)) (@Enclosure.Complex.IsNear.of_parts qz407 Bool.false 16239960645538003 4503599627370496 5000000007779 1555800000000000000 Bool.false 880458271851939 562949953421312 100000000007779 15558000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz407) (@HMul.hMul Real Real Real qz0 qz67 (Real.log (Enclosure.sfrac Bool.false 21689452900 16000000))) Bool.false 16239960645538003 4503599627370496 5000000007779 1555800000000000000 (Enclosure.clog_re_eq 1000 147270 4000 21689452900 16000000 rfl rfl rfl) (ep672 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz407) (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz408 qz341)) Bool.false 880458271851939 562949953421312 100000000007779 15558000000000000000 (Enclosure.clog_im_eq 1000 147270 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz408 qz341)) (@HSub.hSub Real Real Real qz315 qz68 (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz341 qz408))) Bool.false 880458271851939 562949953421312 100000000007779 15558000000000000000 (BSN.arctan_recip 147270 1000 rfl rfl) ep674)))) rfl rfl

noncomputable abbrev qz410 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz172))

noncomputable def ep676 := @Enclosure.Complex.IsNear.of_eq qz186 qz410 Bool.false 16242451726569683 4503599627370496 5000000007779 1555800000000000000 Bool.false 865174630729123 562949953421312 100000000007779 15558000000000000000

noncomputable def ep677 := nat_lit 321044285440535443234292068227742264027967435961513705000000000000

noncomputable def ep678 := nat_lit 2119127492330418211217470301553999747906690977038791000000000000

noncomputable def ep679 := nat_lit 343705933447473946118780052338749280301462844815000000000000

noncomputable def ep680 := BSN.log_dyadic_bound 5329452900 38097452900 4 3 ep677 524288 155580 ep678 ep679 147653 43426905800 32768000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 5329452900) (BSN.artanhQ 38097452900) 0 3 ep678 ep677 ep679 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep681 := @Enclosure.Real.IsNear.mulLit_ff qz67 (Real.log (Enclosure.sfrac Bool.false 21713452900 16000000)) 1 2 0 1 16242451726569683 2251799813685248 5000000007779 777900000000000000 16242451726569683 4503599627370496 5000000007779 1555800000000000000 qz329 (BSN.isNear_log_sfrac 21713452900 16000000 16242451726569683 2251799813685248 5000000007779 777900000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 21713452900) qz330)) Bool.false 136251560493116255371264 18889465931478580854784 1000000001555800 155580000000000000000 16242451726569683 2251799813685248 5000000007779 777900000000000000 (BSN.log_rat_reduce_isNear 21713452900 16000000 10 43426905800 32768000000 147653 524288 24973259072661432 36028797018963968 155580 1000000000000000 rfl rfl rfl rfl (ep680 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep682 := BSN.arctan_dyadic_bound_f 5000 147270 1 0 524288 155580 0 1 1 0 1 1 17793 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 5000) (BSN.arctanEvenQ 147270) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 5000) (BSN.arctanOddQ 147270) 0 0 rfl) rfl rfl rfl

noncomputable def ep683 := @Enclosure.Real.IsNear.subLit_ff_p qz68 (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz345 qz408)) 884279719003555 562949953421312 1 2000000000000000 17793 524288 1 155580 453600676795710439424 865174630729123 562949953421312 100000000007779 15558000000000000000 qz69 (ep682 rfl) rfl rfl

noncomputable abbrev qz189 := (@HAdd.hAdd Complex Complex Complex qz268 qz395 qz335)

noncomputable abbrev qz411 := (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz172)

noncomputable def ep684 := @ep662 16242451726569683 4503599627370496 5000000007779 1555800000000000000 Bool.false 865174630729123 562949953421312 100000000007779 15558000000000000000 Bool.false ep663 16241206186053843 2251799813685248 5000000007779 777900000000000000 Bool.false ep664 872816451290531 281474976710656 100000000007779 7779000000000000000 (ep665 (BSN.log_sum_c_succ qz151 0 1 rfl) (ep675 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep676 (@congrArg Complex Complex qz189 qz411 Complex.log (BSN.w_shift_mk qz151 Bool.false 73635 1000 1 qz152 rfl)) (@Enclosure.Complex.IsNear.of_parts qz410 Bool.false 16242451726569683 4503599627370496 5000000007779 1555800000000000000 Bool.false 865174630729123 562949953421312 100000000007779 15558000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz410) (@HMul.hMul Real Real Real qz0 qz67 (Real.log (Enclosure.sfrac Bool.false 21713452900 16000000))) Bool.false 16242451726569683 4503599627370496 5000000007779 1555800000000000000 (Enclosure.clog_re_eq 5000 147270 4000 21713452900 16000000 rfl rfl rfl) (ep681 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz410) (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz408 qz345)) Bool.false 865174630729123 562949953421312 100000000007779 15558000000000000000 (Enclosure.clog_im_eq 5000 147270 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz408 qz345)) (@HSub.hSub Real Real Real qz315 qz68 (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz345 qz408))) Bool.false 865174630729123 562949953421312 100000000007779 15558000000000000000 (BSN.arctan_recip 147270 5000 rfl rfl) ep683)))) rfl rfl

noncomputable def ep685 := @ep586 ep587 Bool.false 16241206186053843 2251799813685248 5000000007779 777900000000000000 Bool.false 872816451290531 281474976710656 100000000007779 7779000000000000000 Bool.true ep588 5207547144189125249 90071992547409920 4291083735537462512687 ep583 Bool.false ep589 172132929404483452133 1801439850948198400 1936338814404341436821 ep579 (@ep590 90071992547409920 12545571206102582994061 ep585 Bool.false 177718954692742850533 1801439850948198400 5284728443172239946943 ep587 (BSN.logGammaStirling_unfold 1 qz164) (ep659 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (@ep660 100000000007779 7779000000000000000 (BSN.log_sum_c_eq qz151 2) (ep661 (BSN.log_sum_c_succ qz151 1 2 rfl) (ep684 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)))

noncomputable abbrev qz190 := (@HDiv.hDiv Real Real Real qz265 qz383 (2 : Real))

noncomputable def ep686 := @Enclosure.Real.IsNear.mulLit_ff qz190 (Real.log Real.pi) 73635 2000 0 1 75021 65536 1 131072 1104834267 26214400 14727 52428800 (@Enclosure.Real.IsNear.of_eq qz190 (Enclosure.sfrac Bool.false 73635 2000) Bool.false 73635 2000 0 1 (BSN.t_half_eq qz151 Bool.false 73635 1000 qz152) (Enclosure.Real.IsNear.const Bool.false 73635 2000)) EMRow18.d5 rfl

noncomputable def ep687 := @ep581 14727 52428800 ep582 96209296696241339621 1801439850948198400 5755049914404341436821 ep579 (@ep584 1936338814404341436821 ep579 (ep685 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) ep686 rfl rfl

noncomputable def ep688 := nat_lit 32578066970948947632339534617769715436017289585412280655197802667677554114560

noncomputable def ep689 := nat_lit 65424738761693949058486934158863832821490808879394011999221017079929962496

noncomputable def ep690 := nat_lit 85217582965918786929080278486472998984048582842656001887043125340073707503616

noncomputable def ep691 := BSN.sin_dyadic_bound_f 1686427788 1073741824 3 2 524288 155732 ep688 ep71 ep689 ep690 ep74 ep689 524287 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1686427788) qz277 0 2 ep688 ep71 ep689 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1686427788) qz278 0 2 ep690 ep74 ep689 rfl rfl rfl rfl) rfl rfl

noncomputable def ep692 := @ep578 524288 Bool.true 524287 524288 1 77790 (@ep580 14000295 262144 223 524288 ep687 rfl) (Enclosure.sfrac_false_div 14000295 262144) (BSN.cos_reduce1 qz396 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 59335902823727581102080) qz282) 226375608064910080 72057594037927936 Bool.false 524287 524288 8 1000000000000000 155580 77790 (BSN.sin_reduce_arg_pos_rat_q1 14000295 262144 226375608064910080 72057594037927936 8 59335902823727581102080 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 524287 524288 59335902823727581102080 37778931862957161709568 1686427788 1073741824 155732 155580 (ep691 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep693 := nat_lit 15921329789928994722270337

noncomputable def ep694 := nat_lit 3091868004292207428239360000

noncomputable abbrev qz191 := qz382

noncomputable abbrev qz412 := (@HPow.hPow Complex Complex Complex qz457 qz470 qz472)

noncomputable abbrev qz192 := qz412

noncomputable abbrev qz193 := (@HAdd.hAdd Complex Complex Complex qz268 (@HDiv.hDiv Complex Complex Complex qz320 qz348 (@HSub.hSub Complex Complex Complex qz312 qz381 (1 : Complex))) qz319)

noncomputable def ep695 := @Enclosure.Complex.IsNear.of_eq (zetaApproximant qz142 1 15) (@HAdd.hAdd Complex Complex Complex qz5 (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 15, @HPow.hPow Complex Complex Complex qz94 (@Nat.cast Complex Complex.instNatCast n) qz191) (@HMul.hMul Complex Complex Complex qz45 qz192 (@HAdd.hAdd Complex Complex Complex qz5 qz193 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz53 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz53 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz99 qz100 (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1))))))) Bool.false ep573 ep574 ep575

noncomputable def ep696 := @Enclosure.Complex.IsNear.addLitP (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 15, @HPow.hPow Complex Complex Complex qz94 (@Nat.cast Complex Complex.instNatCast n) qz191) (@HMul.hMul Complex Complex Complex qz45 qz192 (@HAdd.hAdd Complex Complex Complex qz5 qz193 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz53 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz53 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz99 qz100 (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1)))))) Bool.false 259180167725 68719476736 26589094687127 5345688095293440

noncomputable def ep697 := nat_lit 1630744759937327638355521

noncomputable def ep698 := nat_lit 1635523081659490716207011

noncomputable def ep699 := nat_lit 546880500598698999326170955766562816

noncomputable def ep700 := nat_lit 10961461784254659046133086057136128

noncomputable def ep701 := @ep696 Bool.true 39341925219 274877906944 53169236795419 10691376190586880 Bool.true 136766813540007034655969 ep574 ep697 ep576 Bool.false 267312174585952002720413 ep574 ep698 ep576 Bool.false ep699 ep573 ep574 ep575 ep576 Bool.true ep700 39877565665864163915587 ep574

noncomputable def ep702 := @Enclosure.Complex.IsNear.of_eq (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 15, @HPow.hPow Complex Complex Complex qz94 (@Nat.cast Complex Complex.instNatCast n) qz191) (BSN.headSumC qz142 15) Bool.false 259180167725 68719476736 26589094687127 5345688095293440 Bool.true 39341925219 274877906944 53169236795419

noncomputable abbrev qz194 := (@HPow.hPow Complex Complex Complex qz269 (@Nat.cast Complex Complex.instNatCast 14) qz382)

noncomputable def ep703 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz142 15) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz142 14) qz194) Bool.false 259180167725 68719476736 26589094687127 5345688095293440 Bool.true 39341925219 274877906944 53169236795419 10691376190586880

noncomputable def ep704 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz142 14) qz194 Bool.false 242658780857 68719476736 2100601693609 445474007941120 Bool.true 35714747049 137438953472 4201243773193 890948015882240 Bool.false

noncomputable abbrev qz195 := (@HPow.hPow Complex Complex Complex qz269 (@Nat.cast Complex Complex.instNatCast 13) qz382)

noncomputable def ep705 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz142 14) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz142 13) qz195) Bool.false 242658780857 68719476736 2100601693609 445474007941120 Bool.true 35714747049 137438953472 4201243773193 890948015882240

noncomputable def ep706 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz142 13) qz195 Bool.false 112459246723 34359738368 1485825261779 334105505955840 Bool.true 10890368987 68719476736 23779209848729 5345688095293440 Bool.false

noncomputable abbrev qz196 := (@HPow.hPow Complex Complex Complex qz269 (@Nat.cast Complex Complex.instNatCast 12) qz382)

noncomputable def ep707 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz142 13) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz142 12) qz196) Bool.false 112459246723 34359738368 1485825261779 334105505955840 Bool.true 10890368987 68719476736 23779209848729 5345688095293440

noncomputable def ep708 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz142 12) qz196 Bool.false 842358258833 274877906944 44560397776423 10691376190586880 Bool.false 1414330559 34359738368 22286518022729 5345688095293440 Bool.false

noncomputable abbrev qz197 := (@HPow.hPow Complex Complex Complex qz269 (@Nat.cast Complex Complex.instNatCast 11) qz382)

noncomputable def ep709 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz142 12) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz142 11) qz197) Bool.false 842358258833 274877906944 44560397776423 10691376190586880 Bool.false 1414330559 34359738368 22286518022729 5345688095293440

noncomputable def ep710 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz142 11) qz197 Bool.false 775862959799 274877906944 13815593930511 3563792063528960 Bool.false 60784360969 274877906944 13821203056251 3563792063528960 Bool.false

noncomputable abbrev qz198 := (@HPow.hPow Complex Complex Complex qz269 (@Nat.cast Complex Complex.instNatCast 10) qz382)

noncomputable def ep711 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz142 11) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz142 10) qz198) Bool.false 775862959799 274877906944 13815593930511 3563792063528960 Bool.false 60784360969 274877906944 13821203056251 3563792063528960

noncomputable def ep712 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz142 10) qz198 Bool.false 689333554529 274877906944 38178048027299 10691376190586880 Bool.false 13127010091 68719476736 9553308334721 2672844047646720 Bool.false

noncomputable abbrev qz199 := (@HPow.hPow Complex Complex Complex qz269 (@Nat.cast Complex Complex.instNatCast 9) qz382)

noncomputable def ep713 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz142 10) (@HAdd.hAdd Complex Complex Complex qz5 qz141 qz199) Bool.false 689333554529 274877906944 38178048027299 10691376190586880 Bool.false 13127010091 68719476736 9553308334721 2672844047646720

noncomputable def ep714 := @Enclosure.Complex.IsNear.addLitP qz141 qz199 Bool.false 689280776103 274877906944 11584630798111 3563792063528960 Bool.true 39117928617 274877906944 11589565769781 3563792063528960 Bool.false

noncomputable abbrev qz200 := (@HMul.hMul Real Real Real qz262 qz383 (Real.log (Enclosure.sfrac Bool.false 9 1)))

noncomputable def ep715 := @Enclosure.Complex.IsNear.of_eq qz199 (Complex.mk (@HMul.hMul Real Real Real qz0 qz107 (Real.cos qz200)) (@HMul.hMul Real Real Real qz0 qz107 (@Neg.neg Real Real.instNeg (Real.sin qz200)))) Bool.false 26389213 137438953472 1712077816483 5345688095293440 Bool.false 91625968981 274877906944 3444536029541 10691376190586880 (BSN.cpow_neg_s_mk qz151 73635 1000 9 qz152 rfl)

noncomputable def ep716 := @Enclosure.Real.IsNear.mulLit_ff qz151 qz109 73635 1000 0 1 9895417793173221 4503599627370496 100000000023337 7779000000000000000 145729817840062025667 900719925474099200 490900000114561333 518600000000000000000 qz153 (BSN.isNear_log_sfrac 9 1 9895417793173221 4503599627370496 100000000023337 7779000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz351) Bool.false 20752195215788806766592 9444732965739290427392 1000000000233370 77790000000000000000 9895417793173221 4503599627370496 100000000023337 7779000000000000000 (BSN.log_rat_reduce_isNear 9 1 3 18 16 30876 262144 24973259072661432 36028797018963968 77790 1000000000000000 rfl rfl rfl rfl (ep322 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep717 := BSN.sin_dyadic_bound_f 619618 1073741824 1 0 524288 155732 0 1 1 0 1 1 302 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 619618) qz277 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 619618) qz278 0 0 rfl) rfl rfl

noncomputable abbrev qz413 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 42412959) qz20)

noncomputable def ep718 := @Enclosure.Real.IsNear.cos_image qz200 qz413 Bool.false 42412959 262144 497 524288 Bool.false 302 524288 1 77790 (@Enclosure.Real.IsNear.recentre' qz200 Bool.false 145729817840062025667 900719925474099200 490900000114561333 518600000000000000000 42412959 262144 497 524288 (ep716 rfl) rfl) (Enclosure.sfrac_false_div 42412959 262144) (BSN.cos_reduce3 qz413 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 21800880081823858688) qz282) 226375608064910080 72057594037927936 Bool.false 302 524288 25 1000000000000000 155580 77790 (BSN.sin_reduce_arg_pos_rat_q3 42412959 262144 226375608064910080 72057594037927936 25 21800880081823858688 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 302 524288 21800880081823858688 37778931862957161709568 619618 1073741824 155732 155580 (ep717 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep719 := BSN.cos_dyadic_bound_f 619618 1073741824 1 0 524288 155732 0 1 1 0 1 1 524287 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 619618) qz283 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 619618) qz284 0 0 rfl) rfl rfl

noncomputable def ep720 := @Enclosure.Real.IsNear.sin_image qz200 qz413 Bool.false 42412959 262144 497 524288 Bool.true 524287 524288 1 77790 (@Enclosure.Real.IsNear.recentre' qz200 Bool.false 145729817840062025667 900719925474099200 490900000114561333 518600000000000000000 42412959 262144 497 524288 (ep716 rfl) rfl) (Enclosure.sfrac_false_div 42412959 262144) (BSN.sin_reduce3 qz413 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 21800880081823858688) qz282) 226375608064910080 72057594037927936 Bool.false 524287 524288 25 1000000000000000 155580 77790 (BSN.sin_reduce_arg_pos_rat_q3 42412959 262144 226375608064910080 72057594037927936 25 21800880081823858688 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 524287 524288 21800880081823858688 37778931862957161709568 619618 1073741824 155732 155580 (ep719 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep721 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz107 (Real.cos qz200)) (@HMul.hMul Real Real Real qz0 qz107 (@Neg.neg Real Real.instNeg (Real.sin qz200))) Bool.false 26389213 137438953472 1712077816483 5345688095293440 Bool.false 91625968981 274877906944 3444536029541 10691376190586880 (@Enclosure.Real.IsNear.mulLit_ff qz107 (Real.cos qz200) 174763 524288 1 524288 151 262144 19592959 20392181760 26389213 137438953472 1712077816483 5345688095293440 qz353 (@Enclosure.Real.IsNear.recentre' (Real.cos qz200) Bool.false 302 524288 39185918 40784363520 151 262144 19592959 20392181760 (ep718 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz107 (@Neg.neg Real Real.instNeg (Real.sin qz200)) 174763 524288 1 524288 524287 524288 19592959 20392181760 91625968981 274877906944 3444536029541 10691376190586880 qz353 (@Enclosure.Real.IsNear.neg (Real.sin qz200) Bool.true 524287 524288 19592959 20392181760 (@Enclosure.Real.IsNear.recentre' (Real.sin qz200) Bool.true 524287 524288 39185918 40784363520 524287 524288 19592959 20392181760 (ep720 rfl rfl) rfl)) rfl)

noncomputable def ep722 := @ep714 26389213 137438953472 1712077816483 5345688095293440 Bool.false 91625968981 274877906944 3444536029541 10691376190586880 Bool.false 94741282327599605874688 689333554529 274877906944 38178048027299 10691376190586880 Bool.false 14433300232987387887616 13127010091 68719476736 9553308334721 2672844047646720 EMRow18.d10 (ep715 ep721) rfl rfl

noncomputable abbrev qz201 := (@HMul.hMul Real Real Real qz262 qz383 (Real.log (Enclosure.sfrac Bool.false 10 1)))

noncomputable def ep723 := @Enclosure.Complex.IsNear.of_eq qz198 (Complex.mk (@HMul.hMul Real Real Real qz0 qz110 (Real.cos qz201)) (@HMul.hMul Real Real Real qz0 qz110 (@Neg.neg Real Real.instNeg (Real.sin qz201)))) Bool.false 43264702635 137438953472 1634366882117 5345688095293440 Bool.false 8276320605 274877906944 3250375829869 10691376190586880 (BSN.cpow_neg_s_mk qz151 73635 1000 10 qz152 rfl)

noncomputable def ep724 := @Enclosure.Real.IsNear.mulLit_ff qz151 qz112 73635 1000 0 1 10369908600166117 4503599627370496 100000000023337 7779000000000000000 152717643954646405059 900719925474099200 490900000114561333 518600000000000000000 qz153 (BSN.isNear_log_sfrac 10 1 10369908600166117 4503599627370496 100000000023337 7779000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz355) Bool.false 21747274560655572598784 9444732965739290427392 1000000000233370 77790000000000000000 10369908600166117 4503599627370496 100000000023337 7779000000000000000 (BSN.log_rat_reduce_isNear 10 1 3 20 16 58495 262144 24973259072661432 36028797018963968 77790 1000000000000000 rfl rfl rfl rfl (ep333 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep725 := nat_lit 25359660153885909021438382823132731813676264453294263309797293172585106735360

noncomputable def ep726 := nat_lit 39679319209569435386124298866858069089254847592827738904800198575530148096

noncomputable def ep727 := nat_lit 66353914838599982636951563290991765495388565719668016138861329416219659305216

noncomputable def ep728 := BSN.sin_dyadic_bound_f 1584238366 1073741824 3 2 524288 155732 ep725 ep71 ep726 ep727 ep74 ep726 521906 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1584238366) qz277 0 2 ep725 ep71 ep726 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1584238366) qz278 0 2 ep727 ep74 ep726 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz414 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 11111671) (@Nat.cast Real Real.instNatCast 65536))

noncomputable def ep729 := @Enclosure.Real.IsNear.cos_image qz201 qz414 Bool.false 11111671 65536 497 524288 Bool.false 521906 524288 1 77790 (@Enclosure.Real.IsNear.recentre' qz201 Bool.false 152717643954646405059 900719925474099200 490900000114561333 518600000000000000000 11111671 65536 497 524288 (ep724 rfl) rfl) (Enclosure.sfrac_false_div 11111671 65536) (BSN.cos_reduce3 qz414 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 13935108036845163773952) qz389) 226375608064910080 72057594037927936 Bool.false 521906 524288 26 1000000000000000 155580 77790 (BSN.sin_reduce_arg_pos_rat_q3 11111671 65536 226375608064910080 72057594037927936 26 13935108036845163773952 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 521906 524288 13935108036845163773952 9444732965739290427392 1584238366 1073741824 155732 155580 (ep728 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep730 := nat_lit 14106335338474202538748490145681232371637593517426958611622851850803072696576

noncomputable def ep731 := nat_lit 42239647377003468745473221839309980976734270857095220357058955155258157793536

noncomputable def ep732 := BSN.cos_dyadic_bound_f 1584238366 1073741824 3 2 524288 155732 ep730 ep78 ep726 ep731 ep80 ep726 49919 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1584238366) qz283 0 2 ep730 ep78 ep726 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1584238366) qz284 0 2 ep731 ep80 ep726 rfl rfl rfl rfl) rfl rfl

noncomputable def ep733 := @Enclosure.Real.IsNear.sin_image qz201 qz414 Bool.false 11111671 65536 497 524288 Bool.true 49919 524288 1 77790 (@Enclosure.Real.IsNear.recentre' qz201 Bool.false 152717643954646405059 900719925474099200 490900000114561333 518600000000000000000 11111671 65536 497 524288 (ep724 rfl) rfl) (Enclosure.sfrac_false_div 11111671 65536) (BSN.sin_reduce3 qz414 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 13935108036845163773952) qz389) 226375608064910080 72057594037927936 Bool.false 49919 524288 26 1000000000000000 155580 77790 (BSN.sin_reduce_arg_pos_rat_q3 11111671 65536 226375608064910080 72057594037927936 26 13935108036845163773952 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 49919 524288 13935108036845163773952 9444732965739290427392 1584238366 1073741824 155732 155580 (ep732 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep734 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz110 (Real.cos qz201)) (@HMul.hMul Real Real Real qz0 qz110 (@Neg.neg Real Real.instNeg (Real.sin qz201))) Bool.false 43264702635 137438953472 1634366882117 5345688095293440 Bool.false 8276320605 274877906944 3250375829869 10691376190586880 (@Enclosure.Real.IsNear.mulLit_ff qz110 (Real.cos qz201) 165795 524288 1 524288 260953 262144 19592959 20392181760 43264702635 137438953472 1634366882117 5345688095293440 qz357 (@Enclosure.Real.IsNear.recentre' (Real.cos qz201) Bool.false 521906 524288 39185918 40784363520 260953 262144 19592959 20392181760 (ep729 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz110 (@Neg.neg Real Real.instNeg (Real.sin qz201)) 165795 524288 1 524288 49919 524288 19592959 20392181760 8276320605 274877906944 3250375829869 10691376190586880 qz357 (@Enclosure.Real.IsNear.neg (Real.sin qz201) Bool.true 49919 524288 19592959 20392181760 (@Enclosure.Real.IsNear.recentre' (Real.sin qz201) Bool.true 49919 524288 39185918 40784363520 49919 524288 19592959 20392181760 (ep733 rfl rfl) rfl)) rfl)

noncomputable def ep735 := @ep712 43264702635 137438953472 1634366882117 5345688095293440 Bool.false 8276320605 274877906944 3250375829869 10691376190586880 Bool.false 106633793232462967472128 775862959799 274877906944 13815593930511 3563792063528960 Bool.false 4177069479521821917184 60784360969 274877906944 13821203056251 3563792063528960 (ep713 (BSN.head_sum_c_succ qz142 9 10 rfl rfl) (ep722 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep723 ep734) rfl rfl

noncomputable abbrev qz202 := (@HMul.hMul Real Real Real qz262 qz383 (Real.log (Enclosure.sfrac Bool.false 11 1)))

noncomputable def ep736 := @Enclosure.Complex.IsNear.of_eq qz197 (Complex.mk (@HMul.hMul Real Real Real qz0 qz113 (Real.cos qz202)) (@HMul.hMul Real Real Real qz0 qz113 (@Neg.neg Real Real.instNeg (Real.sin qz202)))) Bool.false 33247649517 137438953472 311361598489 1069137619058688 Bool.true 49469716497 274877906944 621885375341 2138275238117376 (BSN.cpow_neg_s_mk qz151 73635 1000 11 qz152 rfl)

noncomputable def ep737 := @Enclosure.Real.IsNear.mulLit_ff qz151 qz115 73635 1000 0 1 10799147631728357 4503599627370496 100000000023337 7779000000000000000 159039047172463513539 900719925474099200 490900000114561333 518600000000000000000 qz153 (BSN.isNear_log_sfrac 11 1 10799147631728357 4503599627370496 100000000023337 7779000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz359) Bool.false 22647454054174387339264 9444732965739290427392 1000000000233370 77790000000000000000 10799147631728357 4503599627370496 100000000023337 7779000000000000000 (BSN.log_rat_reduce_isNear 11 1 3 22 16 83480 262144 24973259072661432 36028797018963968 77790 1000000000000000 rfl rfl rfl rfl (ep344 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep738 := nat_lit 222482197326801677905819824854142976

noncomputable def ep739 := BSN.cos_dyadic_bound_f 686789768 1073741824 2 1 524288 155732 ep738 ep61 ep738 ep738 ep62 ep738 420646 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 686789768) qz283 0 1 ep738 ep61 ep738 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 686789768) qz284 0 1 ep738 ep62 ep738 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz415 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 92572909) qz27)

noncomputable def ep740 := @Enclosure.Real.IsNear.cos_image qz202 qz415 Bool.false 92572909 524288 497 524288 Bool.false 420646 524288 1 77790 (@Enclosure.Real.IsNear.recentre' qz202 Bool.false 159039047172463513539 900719925474099200 490900000114561333 518600000000000000000 92572909 524288 497 524288 (ep737 rfl) rfl) (Enclosure.sfrac_false_div 92572909 524288) (BSN.cos_reduce0 qz415 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 48328533536906221191168) qz29) 226375608064910080 72057594037927936 Bool.false 420646 524288 28 1000000000000000 155580 77790 (BSN.sin_reduce_arg_pos_rat_q0 92572909 524288 226375608064910080 72057594037927936 28 48328533536906221191168 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 420646 524288 48328533536906221191168 75557863725914323419136 686789768 1073741824 155732 155580 (ep739 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep741 := BSN.sin_dyadic_bound_f 686789768 1073741824 2 1 524288 155732 ep738 ep57 ep738 ep738 ep58 ep738 312943 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 686789768) qz277 0 1 ep738 ep57 ep738 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 686789768) qz278 0 1 ep738 ep58 ep738 rfl rfl rfl rfl) rfl rfl

noncomputable def ep742 := @Enclosure.Real.IsNear.sin_image qz202 qz415 Bool.false 92572909 524288 497 524288 Bool.false 312943 524288 1 77790 (@Enclosure.Real.IsNear.recentre' qz202 Bool.false 159039047172463513539 900719925474099200 490900000114561333 518600000000000000000 92572909 524288 497 524288 (ep737 rfl) rfl) (Enclosure.sfrac_false_div 92572909 524288) (BSN.sin_reduce0 qz415 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 48328533536906221191168) qz29) 226375608064910080 72057594037927936 Bool.false 312943 524288 28 1000000000000000 155580 77790 (BSN.sin_reduce_arg_pos_rat_q0 92572909 524288 226375608064910080 72057594037927936 28 48328533536906221191168 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 312943 524288 48328533536906221191168 75557863725914323419136 686789768 1073741824 155732 155580 (ep741 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep743 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz113 (Real.cos qz202)) (@HMul.hMul Real Real Real qz0 qz113 (@Neg.neg Real Real.instNeg (Real.sin qz202))) Bool.false 33247649517 137438953472 311361598489 1069137619058688 Bool.true 49469716497 274877906944 621885375341 2138275238117376 (@Enclosure.Real.IsNear.mulLit_ff qz113 (Real.cos qz202) 158079 524288 1 524288 210323 262144 19592959 20392181760 33247649517 137438953472 311361598489 1069137619058688 qz361 (@Enclosure.Real.IsNear.recentre' (Real.cos qz202) Bool.false 420646 524288 39185918 40784363520 210323 262144 19592959 20392181760 (ep740 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz113 (@Neg.neg Real Real.instNeg (Real.sin qz202)) 158079 524288 1 524288 312943 524288 19592959 20392181760 49469716497 274877906944 621885375341 2138275238117376 qz361 (@Enclosure.Real.IsNear.neg (Real.sin qz202) Bool.false 312943 524288 19592959 20392181760 (@Enclosure.Real.IsNear.recentre' (Real.sin qz202) Bool.false 312943 524288 39185918 40784363520 312943 524288 19592959 20392181760 (ep742 rfl rfl) rfl)) rfl)

noncomputable def ep744 := @ep710 33247649517 137438953472 311361598489 1069137619058688 Bool.true 49469716497 274877906944 621885375341 2138275238117376 Bool.false 115772837542503620018176 842358258833 274877906944 44560397776423 10691376190586880 Bool.false 3110145790278860013568 1414330559 34359738368 22286518022729 5345688095293440 (ep711 (BSN.head_sum_c_succ qz142 10 11 rfl rfl) (ep735 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep736 ep743) rfl rfl

noncomputable abbrev qz203 := (@HMul.hMul Real Real Real qz262 qz383 (Real.log (Enclosure.sfrac Bool.false 12 1)))

noncomputable def ep745 := @Enclosure.Complex.IsNear.of_eq qz196 (Complex.mk (@HMul.hMul Real Real Real qz0 qz116 (Real.cos qz203)) (@HMul.hMul Real Real Real qz0 qz116 (@Neg.neg Real Real.instNeg (Real.sin qz203)))) Bool.false 57315714951 274877906944 199067373367 712758412705792 Bool.true 13719030105 68719476736 6219549275 22273700397056 (BSN.cpow_neg_s_mk qz151 73635 1000 12 qz152 rfl)

noncomputable def ep746 := @Enclosure.Real.IsNear.mulLit_ff qz151 qz118 73635 1000 0 1 11191020447815397 4503599627370496 100000000023337 7779000000000000000 164810158134977351619 900719925474099200 490900000114561333 518600000000000000000 qz153 (BSN.isNear_log_sfrac 12 1 11191020447815397 4503599627370496 100000000023337 7779000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz363) Bool.false 23469270914176955449344 9444732965739290427392 1000000000233370 77790000000000000000 11191020447815397 4503599627370496 100000000023337 7779000000000000000 (BSN.log_rat_reduce_isNear 12 1 3 24 16 106290 262144 24973259072661432 36028797018963968 77790 1000000000000000 rfl rfl rfl rfl (ep358 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep747 := nat_lit 1009690394781531935852174565885277855569838623826453377932736166867148800000

noncomputable def ep748 := nat_lit 204353985884903231835770612868256918850433297000474666784788505600000000

noncomputable def ep749 := nat_lit 3028662476372826001092852156430097052871815004885359184464638923590246400000

noncomputable def ep750 := BSN.cos_dyadic_bound_f 819969860 1073741824 3 2 524288 155732 ep747 ep78 ep748 ep749 ep80 ep748 378699 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 819969860) qz283 0 2 ep747 ep78 ep748 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 819969860) qz284 0 2 ep749 ep80 ep748 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz416 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 95932137) qz27)

noncomputable def ep751 := @Enclosure.Real.IsNear.cos_image qz203 qz416 Bool.false 95932137 524288 249 262144 Bool.false 378699 524288 1 77790 (@Enclosure.Real.IsNear.recentre' qz203 Bool.false 164810158134977351619 900719925474099200 490900000114561333 518600000000000000000 95932137 524288 249 262144 (ep746 rfl) rfl) (Enclosure.sfrac_false_div 95932137 524288) (BSN.cos_reduce0 qz416 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 57700249342045086285824) qz29) 226375608064910080 72057594037927936 Bool.false 378699 524288 29 1000000000000000 155580 77790 (BSN.sin_reduce_arg_pos_rat_q0 95932137 524288 226375608064910080 72057594037927936 29 57700249342045086285824 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 378699 524288 57700249342045086285824 75557863725914323419136 819969860 1073741824 155732 155580 (ep750 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep752 := nat_lit 452055290738758229430305849664160000

noncomputable def ep753 := BSN.sin_dyadic_bound_f 819969860 1073741824 2 1 524288 155732 ep752 ep57 ep752 ep752 ep58 ep752 362580 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 819969860) qz277 0 1 ep752 ep57 ep752 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 819969860) qz278 0 1 ep752 ep58 ep752 rfl rfl rfl rfl) rfl rfl

noncomputable def ep754 := @Enclosure.Real.IsNear.sin_image qz203 qz416 Bool.false 95932137 524288 249 262144 Bool.false 362580 524288 1 77790 (@Enclosure.Real.IsNear.recentre' qz203 Bool.false 164810158134977351619 900719925474099200 490900000114561333 518600000000000000000 95932137 524288 249 262144 (ep746 rfl) rfl) (Enclosure.sfrac_false_div 95932137 524288) (BSN.sin_reduce0 qz416 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 57700249342045086285824) qz29) 226375608064910080 72057594037927936 Bool.false 362580 524288 29 1000000000000000 155580 77790 (BSN.sin_reduce_arg_pos_rat_q0 95932137 524288 226375608064910080 72057594037927936 29 57700249342045086285824 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 362580 524288 57700249342045086285824 75557863725914323419136 819969860 1073741824 155732 155580 (ep753 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep755 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz116 (Real.cos qz203)) (@HMul.hMul Real Real Real qz0 qz116 (@Neg.neg Real Real.instNeg (Real.sin qz203))) Bool.false 57315714951 274877906944 199067373367 712758412705792 Bool.true 13719030105 68719476736 6219549275 22273700397056 (@Enclosure.Real.IsNear.mulLit_ff qz116 (Real.cos qz203) 151349 524288 1 524288 378699 524288 9815927 10196090880 57315714951 274877906944 199067373367 712758412705792 qz365 (@Enclosure.Real.IsNear.recentre' (Real.cos qz203) Bool.false 378699 524288 19631854 20392181760 378699 524288 9815927 10196090880 (ep751 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz116 (@Neg.neg Real Real.instNeg (Real.sin qz203)) 151349 524288 1 524288 90645 131072 9815927 10196090880 13719030105 68719476736 6219549275 22273700397056 qz365 (@Enclosure.Real.IsNear.neg (Real.sin qz203) Bool.false 90645 131072 9815927 10196090880 (@Enclosure.Real.IsNear.recentre' (Real.sin qz203) Bool.false 362580 524288 19631854 20392181760 90645 131072 9815927 10196090880 (ep754 rfl rfl) rfl)) rfl)

noncomputable def ep756 := @ep708 57315714951 274877906944 199067373367 712758412705792 Bool.true 13719030105 68719476736 6219549275 22273700397056 Bool.false 247300498845737047556096 112459246723 34359738368 1485825261779 334105505955840 Bool.true 374190229124301193216 10890368987 68719476736 23779209848729 5345688095293440 (ep709 (BSN.head_sum_c_succ qz142 11 12 rfl rfl) (ep744 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep745 ep755) rfl rfl

noncomputable abbrev qz204 := (@HMul.hMul Real Real Real qz262 qz383 (Real.log (Enclosure.sfrac Bool.false 13 1)))

noncomputable def ep757 := @Enclosure.Complex.IsNear.of_eq qz195 (Complex.mk (@HMul.hMul Real Real Real qz0 qz119 (Real.cos qz204)) (@HMul.hMul Real Real Real qz0 qz119 (@Neg.neg Real Real.instNeg (Real.sin qz204)))) Bool.false 17740287411 68719476736 358504033711 1336422023823360 Bool.true 13934009075 137438953472 1428252790429 5345688095293440 (BSN.cpow_neg_s_mk qz151 73635 1000 13 qz152 rfl)

noncomputable def ep758 := @Enclosure.Real.IsNear.mulLit_ff qz151 qz121 73635 1000 0 1 11551488463034085 4503599627370496 100000000023337 7779000000000000000 34023754119020593959 180143985094819840 490900000114561333 518600000000000000000 qz153 (BSN.isNear_log_sfrac 13 1 11551488463034085 4503599627370496 100000000023337 7779000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz367) Bool.false 24225227133228857425920 9444732965739290427392 1000000000233370 77790000000000000000 11551488463034085 4503599627370496 100000000023337 7779000000000000000 (BSN.log_rat_reduce_isNear 13 1 3 26 16 127272 262144 24973259072661432 36028797018963968 77790 1000000000000000 rfl rfl rfl rfl (ep369 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep759 := nat_lit 26067025236257901424724615234584576

noncomputable def ep760 := BSN.cos_dyadic_bound_f 401811968 1073741824 2 1 524288 155732 ep759 ep61 ep759 ep759 ep62 ep759 488004 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 401811968) qz283 0 1 ep759 ep61 ep759 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 401811968) qz284 0 1 ep759 ep62 ep759 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz417 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 99022157) qz27)

noncomputable def ep761 := @Enclosure.Real.IsNear.cos_image qz204 qz417 Bool.false 99022157 524288 497 524288 Bool.false 488004 524288 1 77790 (@Enclosure.Real.IsNear.recentre' qz204 Bool.false 34023754119020593959 180143985094819840 490900000114561333 518600000000000000000 99022157 524288 497 524288 (ep758 rfl) rfl) (Enclosure.sfrac_false_div 99022157 524288) (BSN.cos_reduce0 qz417 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 28275003595658943791104) qz29) 226375608064910080 72057594037927936 Bool.false 488004 524288 30 1000000000000000 155580 77790 (BSN.sin_reduce_arg_pos_rat_q0 99022157 524288 226375608064910080 72057594037927936 30 28275003595658943791104 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 488004 524288 28275003595658943791104 75557863725914323419136 401811968 1073741824 155732 155580 (ep760 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep762 := BSN.sin_dyadic_bound_f 401811968 1073741824 2 1 524288 155732 ep759 ep57 ep759 ep759 ep58 ep759 191650 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 401811968) qz277 0 1 ep759 ep57 ep759 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 401811968) qz278 0 1 ep759 ep58 ep759 rfl rfl rfl rfl) rfl rfl

noncomputable def ep763 := @Enclosure.Real.IsNear.sin_image qz204 qz417 Bool.false 99022157 524288 497 524288 Bool.false 191650 524288 1 77790 (@Enclosure.Real.IsNear.recentre' qz204 Bool.false 34023754119020593959 180143985094819840 490900000114561333 518600000000000000000 99022157 524288 497 524288 (ep758 rfl) rfl) (Enclosure.sfrac_false_div 99022157 524288) (BSN.sin_reduce0 qz417 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 28275003595658943791104) qz29) 226375608064910080 72057594037927936 Bool.false 191650 524288 30 1000000000000000 155580 77790 (BSN.sin_reduce_arg_pos_rat_q0 99022157 524288 226375608064910080 72057594037927936 30 28275003595658943791104 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 191650 524288 28275003595658943791104 75557863725914323419136 401811968 1073741824 155732 155580 (ep762 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep764 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz119 (Real.cos qz204)) (@HMul.hMul Real Real Real qz0 qz119 (@Neg.neg Real Real.instNeg (Real.sin qz204))) Bool.false 17740287411 68719476736 358504033711 1336422023823360 Bool.true 13934009075 137438953472 1428252790429 5345688095293440 (@Enclosure.Real.IsNear.mulLit_ff qz119 (Real.cos qz204) 145411 524288 1 524288 122001 131072 19592959 20392181760 17740287411 68719476736 358504033711 1336422023823360 qz370 (@Enclosure.Real.IsNear.recentre' (Real.cos qz204) Bool.false 488004 524288 39185918 40784363520 122001 131072 19592959 20392181760 (ep761 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz119 (@Neg.neg Real Real.instNeg (Real.sin qz204)) 145411 524288 1 524288 95825 262144 19592959 20392181760 13934009075 137438953472 1428252790429 5345688095293440 qz370 (@Enclosure.Real.IsNear.neg (Real.sin qz204) Bool.false 95825 262144 19592959 20392181760 (@Enclosure.Real.IsNear.recentre' (Real.sin qz204) Bool.false 191650 524288 39185918 40784363520 95825 262144 19592959 20392181760 (ep763 rfl rfl) rfl)) rfl)

noncomputable def ep765 := @ep706 17740287411 68719476736 358504033711 1336422023823360 Bool.true 13934009075 137438953472 1428252790429 5345688095293440 Bool.false 8337692222944366821376 242658780857 68719476736 2100601693609 445474007941120 Bool.true 2454298728965880152064 35714747049 137438953472 4201243773193 890948015882240 (ep707 (BSN.head_sum_c_succ qz142 12 13 rfl rfl) (ep756 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep757 ep764) rfl rfl

noncomputable abbrev qz205 := (@HMul.hMul Real Real Real qz262 qz383 (Real.log (Enclosure.sfrac Bool.false 14 1)))

noncomputable def ep766 := @Enclosure.Complex.IsNear.of_eq qz194 (Complex.mk (@HMul.hMul Real Real Real qz0 qz122 (Real.cos qz205)) (@HMul.hMul Real Real Real qz0 qz122 (@Neg.neg Real Real.instNeg (Real.sin qz205)))) Bool.false 4130346717 17179869184 1381874363819 5345688095293440 Bool.false 32087568879 274877906944 2754311517103 10691376190586880 (BSN.cpow_neg_s_mk qz151 73635 1000 14 qz152 rfl)

noncomputable def ep767 := @Enclosure.Real.IsNear.mulLit_ff qz151 qz124 73635 1000 0 1 11885241781671653 4503599627370496 100000000023337 7779000000000000000 175033955718678433731 900719925474099200 490900000114561333 518600000000000000000 qz153 (BSN.isNear_log_sfrac 14 1 11885241781671653 4503599627370496 100000000023337 7779000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz372) Bool.false 24925158572916270432256 9444732965739290427392 1000000000233370 77790000000000000000 11885241781671653 4503599627370496 100000000023337 7779000000000000000 (BSN.log_rat_reduce_isNear 14 1 3 28 16 146699 262144 24973259072661432 36028797018963968 77790 1000000000000000 rfl rfl rfl rfl (ep379 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep768 := nat_lit 8374954764128735205467244366514274301732404314810976903525573904000000000000

noncomputable def ep769 := nat_lit 4336631566561847168016796541870823555943796225720003906250000000000000000

noncomputable def ep770 := nat_lit 21927384121610349214142184241707689456875245154425202360052098320000000000000

noncomputable def ep771 := BSN.sin_dyadic_bound_f 1201279500 1073741824 3 2 524288 155732 ep768 ep71 ep769 ep770 ep74 ep769 471632 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1201279500) qz277 0 2 ep768 ep71 ep769 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1201279500) qz278 0 2 ep770 ep74 ep769 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz418 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 101883171) qz27)

noncomputable def ep772 := @Enclosure.Real.IsNear.cos_image qz205 qz418 Bool.false 101883171 524288 497 524288 Bool.false 471632 524288 1 77790 (@Enclosure.Real.IsNear.recentre' qz205 Bool.false 175033955718678433731 900719925474099200 490900000114561333 518600000000000000000 101883171 524288 497 524288 (ep767 rfl) rfl) (Enclosure.sfrac_false_div 101883171 524288) (BSN.cos_reduce3 qz418 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 84532529889908927496192) qz29) 226375608064910080 72057594037927936 Bool.false 471632 524288 30 1000000000000000 155580 77790 (BSN.sin_reduce_arg_pos_rat_q3 101883171 524288 226375608064910080 72057594037927936 30 84532529889908927496192 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 471632 524288 84532529889908927496192 75557863725914323419136 1201279500 1073741824 155732 155580 (ep771 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep773 := nat_lit 4654680038545547046223143224304317200320644084328640503694763280000000000000

noncomputable def ep774 := nat_lit 13955366852503517444333396079829209953850044660534481503271789840000000000000

noncomputable def ep775 := BSN.cos_dyadic_bound_f 1201279500 1073741824 3 2 524288 155732 ep773 ep78 ep769 ep774 ep80 ep769 228999 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1201279500) qz283 0 2 ep773 ep78 ep769 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1201279500) qz284 0 2 ep774 ep80 ep769 rfl rfl rfl rfl) rfl rfl

noncomputable def ep776 := @Enclosure.Real.IsNear.sin_image qz205 qz418 Bool.false 101883171 524288 497 524288 Bool.true 228999 524288 1 77790 (@Enclosure.Real.IsNear.recentre' qz205 Bool.false 175033955718678433731 900719925474099200 490900000114561333 518600000000000000000 101883171 524288 497 524288 (ep767 rfl) rfl) (Enclosure.sfrac_false_div 101883171 524288) (BSN.sin_reduce3 qz418 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 84532529889908927496192) qz29) 226375608064910080 72057594037927936 Bool.false 228999 524288 30 1000000000000000 155580 77790 (BSN.sin_reduce_arg_pos_rat_q3 101883171 524288 226375608064910080 72057594037927936 30 84532529889908927496192 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 228999 524288 84532529889908927496192 75557863725914323419136 1201279500 1073741824 155732 155580 (ep775 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep777 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz122 (Real.cos qz205)) (@HMul.hMul Real Real Real qz0 qz122 (@Neg.neg Real Real.instNeg (Real.sin qz205))) Bool.false 4130346717 17179869184 1381874363819 5345688095293440 Bool.false 32087568879 274877906944 2754311517103 10691376190586880 (@Enclosure.Real.IsNear.mulLit_ff qz122 (Real.cos qz205) 140121 524288 1 524288 29477 32768 19592959 20392181760 4130346717 17179869184 1381874363819 5345688095293440 qz374 (@Enclosure.Real.IsNear.recentre' (Real.cos qz205) Bool.false 471632 524288 39185918 40784363520 29477 32768 19592959 20392181760 (ep772 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz122 (@Neg.neg Real Real.instNeg (Real.sin qz205)) 140121 524288 1 524288 228999 524288 19592959 20392181760 32087568879 274877906944 2754311517103 10691376190586880 qz374 (@Enclosure.Real.IsNear.neg (Real.sin qz205) Bool.true 228999 524288 19592959 20392181760 (@Enclosure.Real.IsNear.recentre' (Real.sin qz205) Bool.true 228999 524288 39185918 40784363520 228999 524288 19592959 20392181760 (ep776 rfl rfl) rfl)) rfl)

noncomputable def ep778 := @ep704 4130346717 17179869184 1381874363819 5345688095293440 Bool.false 32087568879 274877906944 2754311517103 10691376190586880 Bool.false 4452681376602678886400 259180167725 68719476736 26589094687127 5345688095293440 Bool.true 5407113029673044410368 39341925219 274877906944 53169236795419 10691376190586880 (ep705 (BSN.head_sum_c_succ qz142 13 14 rfl rfl) (ep765 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep766 ep777) rfl rfl

noncomputable def ep779 := @Enclosure.Complex.IsNear.mul qz192 (@HAdd.hAdd Complex Complex Complex qz5 qz193 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz53 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz53 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz99 qz100 (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1))))) Bool.true 136766813540007034655969 ep574 ep697 ep576 Bool.false

noncomputable abbrev qz206 := (Complex.re qz412)

noncomputable abbrev qz207 := (Complex.im qz412)

noncomputable def ep780 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 qz206 (Complex.re (@HAdd.hAdd Complex Complex Complex qz5 qz193 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz53 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz53 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz99 qz100 (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz207 (Complex.im (@HAdd.hAdd Complex Complex Complex qz5 qz193 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz53 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz53 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz99 qz100 (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1))))))) 233502233019327956861 21463025097284895375360 11545098369869790930133

noncomputable def ep781 := nat_lit 92756040128766222847180800

noncomputable def ep782 := nat_lit 978476517161618210352627614123115272239841280

noncomputable def ep783 := @Enclosure.Real.IsNear.mulLit_tf qz206 (Complex.re (@HAdd.hAdd Complex Complex Complex qz5 qz193 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz53 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz53 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz99 qz100 (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1)))))) 5964310889 274877906944 884683906851 3563792063528960 39149909749

noncomputable abbrev qz419 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) qz473 (Real.log (Enclosure.sfrac Bool.false 15 1)))

noncomputable abbrev qz208 := (Real.cos qz419)

noncomputable abbrev qz209 := (@Neg.neg Real Real.instNeg (Real.sin qz419))

noncomputable def ep784 := @Enclosure.Complex.IsNear.of_eq qz192 (Complex.mk (@HMul.hMul Real Real Real qz0 qz127 qz208) (@HMul.hMul Real Real Real qz0 qz127 qz209)) Bool.true 5964310889 274877906944 884683906851 3563792063528960 Bool.false 70722277643 274877906944 890886025761 3563792063528960 (BSN.cpow_neg_s_mk qz151 73635 1000 15 qz152 rfl)

noncomputable def ep785 := @Enclosure.Real.IsNear.mulLit_ff qz151 qz131 73635 1000 0 1 12195956895733477 4503599627370496 100000000023337 7779000000000000000 179609857203466915779 900719925474099200 490900000114561333 518600000000000000000 qz153 (BSN.isNear_log_sfrac 15 1 12195956895733477 4503599627370496 100000000023337 7779000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz130) Bool.false 25576775395801252757504 9444732965739290427392 1000000000233370 77790000000000000000 12195956895733477 4503599627370496 100000000023337 7779000000000000000 (BSN.log_rat_reduce_isNear 15 1 3 30 16 164785 262144 24973259072661432 36028797018963968 77790 1000000000000000 rfl rfl rfl rfl (ep396 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep786 := nat_lit 14541740407644864016904208886657157111797367958494460246748265640734431412161

noncomputable def ep787 := nat_lit 42159299724906137116954773752200821125676192181065387071720617643672633281

noncomputable def ep788 := nat_lit 43540902623484779776478717112467069693140751491121249966101355686915948969921

noncomputable def ep789 := BSN.cos_dyadic_bound_f 1596289561 1073741824 3 2 524288 155732 ep786 ep78 ep787 ep788 ep80 ep787 44059 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1596289561) qz283 0 2 ep786 ep78 ep787 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1596289561) qz284 0 2 ep788 ep80 ep787 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz210 := qz419

noncomputable abbrev qz420 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 13068337) (@Nat.cast Real Real.instNatCast 65536))

noncomputable def ep790 := @Enclosure.Real.IsNear.cos_image qz210 qz420 Bool.false 13068337 65536 497 524288 Bool.true 44059 524288 1 77790 (@Enclosure.Real.IsNear.recentre' qz210 Bool.false 179609857203466915779 900719925474099200 490900000114561333 518600000000000000000 13068337 65536 497 524288 (ep785 rfl) rfl) (Enclosure.sfrac_false_div 13068337 65536) (BSN.cos_reduce2 qz420 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 14041111475780776361984) qz389) 226375608064910080 72057594037927936 Bool.false 44059 524288 31 1000000000000000 155580 77790 (BSN.sin_reduce_arg_pos_rat_q2 13068337 65536 226375608064910080 72057594037927936 31 14041111475780776361984 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 44059 524288 14041111475780776361984 9444732965739290427392 1596289561 1073741824 155732 155580 (ep789 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep791 := nat_lit 26141405293980830320734012176981122144334721371545176134489501659207038435265

noncomputable def ep792 := nat_lit 68397327379918993284685438448875566191435080233372784011261147155071535448001

noncomputable def ep793 := BSN.sin_dyadic_bound_f 1596289561 1073741824 3 2 524288 155732 ep791 ep71 ep787 ep792 ep74 ep787 522433 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1596289561) qz277 0 2 ep791 ep71 ep787 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1596289561) qz278 0 2 ep792 ep74 ep787 rfl rfl rfl rfl) rfl rfl

noncomputable def ep794 := @Enclosure.Real.IsNear.sin_image qz210 qz420 Bool.false 13068337 65536 497 524288 Bool.true 522433 524288 1 77790 (@Enclosure.Real.IsNear.recentre' qz210 Bool.false 179609857203466915779 900719925474099200 490900000114561333 518600000000000000000 13068337 65536 497 524288 (ep785 rfl) rfl) (Enclosure.sfrac_false_div 13068337 65536) (BSN.sin_reduce2 qz420 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 14041111475780776361984) qz389) 226375608064910080 72057594037927936 Bool.false 522433 524288 31 1000000000000000 155580 77790 (BSN.sin_reduce_arg_pos_rat_q2 13068337 65536 226375608064910080 72057594037927936 31 14041111475780776361984 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 522433 524288 14041111475780776361984 9444732965739290427392 1596289561 1073741824 155732 155580 (ep793 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz211 := (Real.sin qz419)

noncomputable def ep795 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz127 qz208) (@HMul.hMul Real Real Real qz0 qz127 qz209) Bool.true 5964310889 274877906944 884683906851 3563792063528960 Bool.false 70722277643 274877906944 890886025761 3563792063528960 (@Enclosure.Real.IsNear.mulLit_ft qz127 qz208 135371 524288 1 524288 44059 524288 19592959 20392181760 5964310889 274877906944 884683906851 3563792063528960 qz378 (@Enclosure.Real.IsNear.recentre' qz208 Bool.true 44059 524288 39185918 40784363520 44059 524288 19592959 20392181760 (ep790 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz127 qz209 135371 524288 1 524288 522433 524288 19592959 20392181760 70722277643 274877906944 890886025761 3563792063528960 qz378 (@Enclosure.Real.IsNear.neg qz211 Bool.true 522433 524288 19592959 20392181760 (@Enclosure.Real.IsNear.recentre' qz211 Bool.true 522433 524288 39185918 40784363520 522433 524288 19592959 20392181760 (ep794 rfl rfl) rfl)) rfl)

noncomputable def ep796 := @ep783 78082030440 0 1 233502233019327956861 21463025097284895375360 11545098369869790930133 ep781 (@Enclosure.Complex.IsNear.re_isNear qz192 Bool.true 5964310889 274877906944 884683906851 3563792063528960 Bool.false 70722277643 274877906944 890886025761 3563792063528960 (ep784 ep795))

noncomputable def ep797 := @Enclosure.Complex.IsNear.re_isNear (@HAdd.hAdd Complex Complex Complex qz5 qz193 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz53 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz53 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz99 qz100 (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1))))) Bool.false 39149909749 78082030440 0 1 Bool.false

noncomputable def ep798 := @Enclosure.Complex.IsNear.addLitP qz193 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz53 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz53 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz99 qz100 (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1)))) Bool.false 216294529 433789058 0 1 Bool.true 44181000

noncomputable def ep799 := @ep798 216894529 0 1 Bool.false 1 360 0 1 Bool.false 4909 12000 0 1 Bool.false 78299819498 39149909749 78082030440 0 1 Bool.false 534563242861 534563242861 2602734348000 0 1

noncomputable abbrev qz212 := (@HDiv.hDiv Complex Complex Complex qz320 qz348 (@HSub.hSub Complex Complex Complex qz312 qz381 (1 : Complex)))

noncomputable def ep800 := @Enclosure.Complex.IsNear.addLitP qz212 qz72 Bool.true 30000000 21689452900 0 1 Bool.true 4418100000 21689452900 0 1

noncomputable def ep801 := @Enclosure.Complex.IsNear.of_eq qz212 (Complex.mk (Enclosure.sfrac Bool.true 30000000 21689452900) (Enclosure.sfrac Bool.true 4418100000 21689452900)) Bool.true 30000000 21689452900 0 1 Bool.true 4418100000 21689452900 0 1

noncomputable def ep802 := @ep800 Bool.false 1 2 0 1 Bool.false 0 1 0 1 Bool.false 21629452900 216294529 433789058 0 1 Bool.true 4418100000 44181000 216894529 0 1 (ep801 (BSN.N_div_s_sub_one_mk qz151 73635 1000 15 qz152 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 30000000 21689452900) (Enclosure.sfrac Bool.true 4418100000 21689452900) Bool.true 30000000 21689452900 0 1 Bool.true 4418100000 21689452900 0 1 (Enclosure.Real.IsNear.const Bool.true 30000000 21689452900) (Enclosure.Real.IsNear.const Bool.true 4418100000 21689452900))) qz73 rfl

noncomputable def ep803 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz53 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz53 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz99 qz100 (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1)))) (@HAdd.hAdd Complex Complex Complex qz5 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz53 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz53 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz99 qz100 (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz74)) ↑qz135) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1))) qz136)) Bool.false 1 360 0 1

noncomputable def ep804 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz53 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz53 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz99 qz100 (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz74)) ↑qz135) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1))) qz136) Bool.false 0 1 0 1 Bool.false

noncomputable def ep805 := @ep804 0 1 0 1 Bool.false 1 360 0 1 Bool.false 4909 12000 0 1 Bool.false 1 1 360 0 1 Bool.false 4909 4909 12000 0

noncomputable def ep806 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz53 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz53 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz99 qz100 (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1)))) (Complex.mk qz14 qz14) Bool.false 0 1 0 1 Bool.false

noncomputable def ep807 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz74)) ↑qz135) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1))) qz136 Bool.false 1 360 0 1 Bool.false 4909 12000 0 1

noncomputable def ep808 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz74)) ↑qz135) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1)))) qz137) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz74)) ↑qz135) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1)))) qz138) 1 360 0 1 0 1 0

noncomputable def ep809 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz74)) ↑qz135) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1)))) qz137 1 24 0 1 1 15 0 1 1

noncomputable def ep810 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz74)) ↑qz135)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz74)) ↑qz135)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1)))) 1 24 0 1 0 1 0 1 1

noncomputable def ep811 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz74)) ↑qz135)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 1 2 0 1 1 24 0

noncomputable def ep812 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1)) qz142 Bool.false 1 2 0 1 Bool.false 73635 1000 0 1 (BSN.ascPochhammer_one_eval qz142)

noncomputable def ep813 := ep812 (@Enclosure.Complex.IsNear.of_eq qz142 (Complex.mk qz67 qz151) Bool.false 1 2 0 1 Bool.false 73635 1000 0 1 (BSN.s_crit_mk qz151 Bool.false 73635 1000 qz152) (@Enclosure.Complex.IsNear.mk qz67 qz151 Bool.false 1 2 0 1 Bool.false 73635 1000 0 1 qz329 qz153))

noncomputable def ep814 := @ep811 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz74)) ↑qz135) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep423) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 73635 1000 0 1 ep813)

noncomputable def ep815 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz74)) ↑qz135)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 73635 1000 0 1 0 1 0

noncomputable def ep816 := @ep815 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz74)) ↑qz135) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep423) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 73635 1000 0 1 ep813)

noncomputable def ep817 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz74)) ↑qz135)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz74)) ↑qz135)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1)))) 4909 800 0 1 0 1 0 1 4909

noncomputable def ep818 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz74)) ↑qz135)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 73635 1000 0 1 4909 800 0

noncomputable def ep819 := @ep818 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz74)) ↑qz135) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep423) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 73635 1000 0 1 ep813)

noncomputable def ep820 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz74)) ↑qz135)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 1 2 0 1 0 1 0

noncomputable def ep821 := @ep820 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz74)) ↑qz135) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep423) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 73635 1000 0 1 ep813)

noncomputable def ep822 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz74)) ↑qz135) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 24 0 1 Bool.false 4909 800 0 1 (@ep810 1 24 0 1 (ep814 rfl) (ep816 rfl) rfl rfl) (@ep817 4909 800 0 1 (ep819 rfl) (ep821 rfl) rfl rfl)

noncomputable def ep823 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz74)) ↑qz135) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 4909 800 0 1 ep822

noncomputable def ep824 := @ep809 360 0 1 ep823 qz139

noncomputable def ep825 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz74)) ↑qz135) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1)))) qz138 4909 800 0 1 0 1 0 1 0

noncomputable def ep826 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz74)) ↑qz135) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 4909 800 0 1 ep822

noncomputable def ep827 := @ep825 1 0 1 ep826 qz140

noncomputable def ep828 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz74)) ↑qz135) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1)))) qz138) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz74)) ↑qz135) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1)))) qz137) 0 1 0 1 4909 12000 0

noncomputable def ep829 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz74)) ↑qz135) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1)))) qz138 1 24 0 1 0 1 0 1 0

noncomputable def ep830 := @ep829 1 0 1 ep823 qz140

noncomputable def ep831 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz74)) ↑qz135) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1)))) qz137 4909 800 0 1 1 15 0 1 4909

noncomputable def ep832 := @ep831 12000 0 1 ep826 qz139

noncomputable def ep833 := @ep805 1 (@ep806 0 1 0 1 (BSN.bern_sum_base qz142 15) qz88) (ep807 (@ep808 1 1 1 360 0 1 (ep824 rfl) (ep827 rfl) rfl rfl) (@ep828 1 4909 4909 12000 0 1 (ep830 rfl) (ep832 rfl) rfl rfl)) rfl rfl rfl rfl rfl

noncomputable def ep834 := ep799 (ep802 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep803 Bool.false 4909 12000 0 1 (BSN.bern_sum_succ qz142 15 0 1 1 rfl rfl) (ep833 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl rfl

noncomputable def ep835 := @Enclosure.Real.IsNear.mulLit_ff qz207 (Complex.im (@HAdd.hAdd Complex Complex Complex qz5 qz193 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz53 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz53 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz99 qz100 (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1)))))) 70722277643 274877906944 890886025761 3563792063528960 534563242861

noncomputable def ep836 := @ep835 2602734348000 0 1 37805530079358079656623 715434169909496512512000 158744974316782848447407 ep694 (@Enclosure.Complex.IsNear.im_isNear qz192 Bool.true 5964310889 274877906944 884683906851 3563792063528960 Bool.false 70722277643 274877906944 890886025761 3563792063528960 (ep784 ep795))

noncomputable def ep837 := @Enclosure.Complex.IsNear.im_isNear (@HAdd.hAdd Complex Complex Complex qz5 qz193 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz53 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz53 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz99 qz100 (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1))))) Bool.false 39149909749 78082030440 0 1 Bool.false

noncomputable def ep838 := @Enclosure.Real.IsNear.addLit_tf_p (@HMul.hMul Real Real Real qz0 qz206 (Complex.im (@HAdd.hAdd Complex Complex Complex qz5 qz193 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz53 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz53 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz99 qz100 (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz207 (Complex.re (@HAdd.hAdd Complex Complex Complex qz5 qz193 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz53 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz53 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz99 qz100 (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1))))))) 3188301370255013813429 715434169909496512512000 157639832717736471580237

noncomputable def ep839 := nat_lit 1912442637316029806780866380534345600923074560

noncomputable def ep840 := @Enclosure.Real.IsNear.mulLit_tf qz206 (Complex.im (@HAdd.hAdd Complex Complex Complex qz5 qz193 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz53 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz53 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz99 qz100 (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1)))))) 5964310889 274877906944 884683906851 3563792063528960 534563242861

noncomputable def ep841 := @ep840 2602734348000 0 1 3188301370255013813429 715434169909496512512000 157639832717736471580237 ep694 (@Enclosure.Complex.IsNear.re_isNear qz192 Bool.true 5964310889 274877906944 884683906851 3563792063528960 Bool.false 70722277643 274877906944 890886025761 3563792063528960 (ep784 ep795))

noncomputable def ep842 := @Enclosure.Real.IsNear.mulLit_ff qz207 (Complex.re (@HAdd.hAdd Complex Complex Complex qz5 qz193 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz53 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz53 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz99 qz100 (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1)))))) 70722277643 274877906944 890886025761 3563792063528960 39149909749

noncomputable def ep843 := @ep842 78082030440 0 1 2768770786967170441607 21463025097284895375360 11626035835062813014663 ep781 (@Enclosure.Complex.IsNear.im_isNear qz192 Bool.true 5964310889 274877906944 884683906851 3563792063528960 Bool.false 70722277643 274877906944 890886025761 3563792063528960 (ep784 ep795))

noncomputable abbrev qz421 := (ep834 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable def ep844 := @ep779 267312174585952002720413 ep574 ep698 ep576 (@ep780 ep781 37805530079358079656623 715434169909496512512000 158744974316782848447407 ep694 ep782 136766813540007034655969 ep574 ep697 ep576 (ep796 (@ep797 534563242861 2602734348000 0 1 qz421) rfl) (ep836 (@ep837 534563242861 2602734348000 0 1 qz421) rfl) rfl rfl) (@ep838 ep694 2768770786967170441607 21463025097284895375360 11626035835062813014663 ep781 ep839 267312174585952002720413 ep574 ep698 ep576 (ep841 (@ep837 534563242861 2602734348000 0 1 qz421) rfl) (ep843 (@ep797 534563242861 2602734348000 0 1 qz421) rfl) rfl rfl)

noncomputable def ep845 := @ep701 ep693 ep694 (@ep702 10691376190586880 (BSN.head_sum_c_eq qz142 15) (ep703 (BSN.head_sum_c_succ qz142 14 15 rfl rfl) (ep778 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))) ep844 rfl rfl rfl

noncomputable def ep846 := @Enclosure.Complex.IsNear.re_isNear (zetaApproximant qz142 1 15) Bool.false ep573 ep574 ep575 ep576 Bool.true 39877565665864163915587 ep574 ep693 ep694 (@ep695 ep576 Bool.true 39877565665864163915587 ep574 ep693 ep694 (BSN.zetaApproximant_eq_folded' qz142 1 15 rfl) (ep845 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

noncomputable def ep847 := @Enclosure.Real.IsNear.mulLit_ft (Real.sin (@HSub.hSub Real Real Real qz315 (Complex.im (@HSub.hSub Complex Complex Complex qz46 qz160 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz161 (@Nat.cast Complex Complex.instNatCast j))))) qz162)) (Complex.im (zetaApproximant qz142 1 15)) 49 262144 8935729

noncomputable def ep848 := @Enclosure.Real.IsNear.recentre' (Real.sin (@HSub.hSub Real Real Real qz315 (Complex.im (@HSub.hSub Complex Complex Complex qz46 qz160 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz161 (@Nat.cast Complex Complex.instNatCast j))))) qz162)) Bool.false 98 524288 17871458

noncomputable def ep849 := @Enclosure.Real.IsNear.sin_image (@HSub.hSub Real Real Real qz315 (Complex.im (@HSub.hSub Complex Complex Complex qz46 qz160 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz161 (@Nat.cast Complex Complex.instNatCast j))))) qz162) qz396 Bool.false 14000295 262144 223

noncomputable def ep850 := nat_lit 18128003756643501550881291202831559167930267906953219924887321934078610046976

noncomputable def ep851 := nat_lit 54253161792407116754526899740176949838147822103100871750663523768075970215936

noncomputable def ep852 := BSN.cos_dyadic_bound_f 1686427788 1073741824 3 2 524288 155732 ep850 ep78 ep689 ep851 ep80 ep689 98 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1686427788) qz283 0 2 ep850 ep78 ep689 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1686427788) qz284 0 2 ep851 ep80 ep689 rfl rfl rfl rfl) rfl rfl

noncomputable def ep853 := @ep849 524288 Bool.false 98 524288 1 77790 (@ep580 14000295 262144 223 524288 ep687 rfl) (Enclosure.sfrac_false_div 14000295 262144) (BSN.sin_reduce1 qz396 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 59335902823727581102080) qz282) 226375608064910080 72057594037927936 Bool.false 98 524288 8 1000000000000000 155580 77790 (BSN.sin_reduce_arg_pos_rat_q1 14000295 262144 226375608064910080 72057594037927936 8 59335902823727581102080 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 98 524288 59335902823727581102080 37778931862957161709568 1686427788 1073741824 155732 155580 (ep852 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep854 := @Enclosure.Complex.IsNear.im_isNear (zetaApproximant qz142 1 15) Bool.false ep573 ep574 ep575 ep576 Bool.true 39877565665864163915587 ep574 ep693 ep694 (@ep695 ep576 Bool.true 39877565665864163915587 ep574 ep693 ep694 (BSN.zetaApproximant_eq_folded' qz142 1 15 rfl) (ep845 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

theorem EMRow18.d11 : Enclosure.Real.IsNear (hardyZApproximantEM 1 15 qz151) Bool.true ep558 ep559 ep560 ep561 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantEM 1 15 qz151) ep562 Bool.true ep558 ep559 ep560 ep561 (@Eq.refl Real ep562) (@ep563 Bool.true ep558 ep559 ep560 ep561 (BSN.re_exp_mul (@HSub.hSub Real Real Real qz315 (Complex.im (@HSub.hSub Complex Complex Complex qz46 qz160 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz161 (@Nat.cast Complex Complex.instNatCast j))))) qz162) (zetaApproximant qz142 1 15)) (@ep565 ep559 ep566 ep561 ep567 ep568 ep569 ep570 ep571 ep558 ep559 ep560 ep561 (@ep572 20392181760 ep573 ep574 ep575 ep576 ep564 ep559 ep566 ep561 (@ep577 40784363520 524287 524288 8935729 20392181760 (ep692 rfl rfl) rfl) ep846 rfl) (@ep847 20392181760 39877565665864163915587 ep574 ep693 ep694 ep567 ep568 ep569 ep570 (@ep848 40784363520 49 262144 8935729 20392181760 (ep853 rfl rfl) rfl) ep854 rfl) rfl rfl))

theorem EMRow18.d12 : @Eq Nat (Nat.mul (BSN.factNat (Nat.succ (Nat.mul 2 1))) (Nat.pow 4 (Nat.mul 2 1))) 96 := @Eq.refl Nat 96

theorem EMRow18.d13 : @Eq Nat (Nat.mul (Nat.mul 2 1) (Nat.pow (Nat.succ (Nat.mul 4 2)) (Nat.mul 2 1))) 162 := @Eq.refl Nat 162

theorem EMRow18.d14 : @Eq Nat (BSN.factNat (Nat.mul 2 2)) 24 := @Eq.refl Nat 24

theorem EMRow18.d15 : @Eq Nat (Nat.pow 15 (Nat.succ (Nat.mul 2 3))) 170859375 := @Eq.refl Nat 170859375

noncomputable abbrev qz476 := (@HAdd.hAdd Complex Complex Complex qz479 qz478 (@Nat.cast Complex Complex.instNatCast 3))

noncomputable abbrev qz422 := qz476

noncomputable abbrev qz213 := (@HDiv.hDiv Real Real Real qz265 (@Norm.norm Complex Complex.instNorm qz422) (@HAdd.hAdd Real Real Real qz339 (Complex.re qz267) (@Nat.cast Real Real.instNatCast 3)))

noncomputable abbrev qz214 := (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 2)

noncomputable abbrev qz215 := (@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 2)))

noncomputable abbrev qz423 := (@HPow.hPow Complex Complex Complex qz457 qz470 (@HSub.hSub Complex Complex Complex qz463 qz458 qz459))

noncomputable abbrev qz216 := qz423

noncomputable def ep855 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz6 1 15))) (@HMul.hMul Real Real Real qz0 qz213 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz216))) 586865255 19327352832 1011589 12884901888 24458976748432683 31525197391593472 21060511749

noncomputable def ep856 := nat_lit 491228316532785405143023616

noncomputable def ep857 := @Enclosure.Real.IsNear.mulLit_ff (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz6 1 15)) 4427 294912 1 884736 132565 65536 1331 262144 586865255 19327352832

noncomputable abbrev qz424 := (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid)))

noncomputable abbrev qz217 := (@HPow.hPow Real Nat Real qz424 qz266 2)

noncomputable def ep858 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 96 162) (@Inv.inv Real Real.instInv qz217) 96 162 0 1 13281 524288 1 524288 4427 294912 1 884736

noncomputable def ep859 := nat_lit 781950621441006189802102638025

noncomputable def ep860 := nat_lit 19807040628566084398385987584

noncomputable def ep861 := nat_lit 26986075409044041160201671

noncomputable def ep862 := nat_lit 1073741824000000000000000000000000000000

noncomputable abbrev qz218 := qz266

noncomputable abbrev qz425 := (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) qz218 1)

noncomputable def ep863 := @Enclosure.Real.IsNear.mulLit_ff qz425 qz218 884279719003555 140737488355328 1 500000000000000 884279719003555 140737488355328 1 500000000000000 ep859 ep860 ep861 ep862

noncomputable def ep864 := ep863 (@Enclosure.Real.IsNear.of_eq qz425 qz218 Bool.false 884279719003555 140737488355328 1 500000000000000 (BSN.pow_one_r qz218) (@Enclosure.Real.IsNear.of_eq qz218 qz263 Bool.false 884279719003555 140737488355328 1 500000000000000 BSN.two_pi_eq qz264)) (@Enclosure.Real.IsNear.of_eq qz218 qz263 Bool.false 884279719003555 140737488355328 1 500000000000000 BSN.two_pi_eq qz264) rfl

noncomputable def ep865 := @Enclosure.Real.IsNear.inv_image qz217 ep859 ep860 ep861 ep862 6640 6641 262144 (@Enclosure.Real.IsNear.of_eq qz217 (@HMul.hMul Real Real Real qz0 qz425 qz218) Bool.false ep859 ep860 ep861 ep862 (BSN.pow_succ_r qz218 1 2 rfl) ep864) rfl rfl rfl

noncomputable def ep866 := ep858 (Enclosure.Real.IsNear.const Bool.false 96 162) (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz217) Bool.false 13281 524288 1 524288 13281 524288 1 524288 (ep865 rfl rfl rfl) rfl)

noncomputable def ep867 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (zetaApproximant qz6 1 15)) (Real.sqrt (@HAdd.hAdd Real Real Real qz339 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz6 1 15)) (Complex.re (zetaApproximant qz6 1 15))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz6 1 15)) (Complex.im (zetaApproximant qz6 1 15))))) Bool.false 132565 65536 1331 262144

noncomputable def ep868 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz339 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz6 1 15)) (Complex.re (zetaApproximant qz6 1 15))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz6 1 15)) (Complex.im (zetaApproximant qz6 1 15))))) Bool.false 1060520 524288 2662 524288

noncomputable def ep869 := nat_lit 197609020258195607666012356622849420442677

noncomputable def ep870 := nat_lit 48295371638381465009210494707302400000000

noncomputable def ep871 := nat_lit 52617423284758503526752406702685865266221619435778052427

noncomputable def ep872 := nat_lit 2562426216038982648763144827609118452073774448640000000000

noncomputable def ep873 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz339 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz6 1 15)) (Complex.re (zetaApproximant qz6 1 15))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz6 1 15)) (Complex.im (zetaApproximant qz6 1 15)))) ep869 ep870 ep871 ep872 528929 531591

noncomputable def ep874 := nat_lit 62352380630125093914233469762515519486349653678401

noncomputable def ep875 := nat_lit 15244259276705150127635424321579656832614400000000

noncomputable def ep876 := nat_lit 51582779035618765174959643105976773694646926360629448651

noncomputable def ep877 := nat_lit 1386966708127202227449206673017624020547457721

noncomputable def ep878 := nat_lit 952766204794071882977214020098728552038400000000

noncomputable def ep879 := nat_lit 2694386065468068624460321866429925967642429883199489

noncomputable def ep880 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz6 1 15)) (Complex.re (zetaApproximant qz6 1 15))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz6 1 15)) (Complex.im (zetaApproximant qz6 1 15))) ep874 ep875 ep876 ep872 ep877 ep878 ep879

noncomputable def ep881 := nat_lit 6672984937601517314487356321898745968942120960000000000

noncomputable def ep882 := nat_lit 59428384332946535375778106725179843098617454543774172898611010759993171706553264264498380800000000

noncomputable def ep883 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (zetaApproximant qz6 1 15)) (Complex.re (zetaApproximant qz6 1 15)) ep167 ep168 ep169 ep170 ep167 ep168 ep169 ep170 ep874

noncomputable def ep884 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (zetaApproximant qz6 1 15)) (Complex.im (zetaApproximant qz6 1 15)) 37242001935008840599189 976097436116944158720000 ep298 ep299 37242001935008840599189 976097436116944158720000 ep298 ep299 ep877

noncomputable def ep885 := @ep855 31525197391593472 ep856 228746010238670467 283726776524341248 7488277166095 94575592174780416 (@ep857 1011589 12884901888 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaStirlingErrorBound 1 2) (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 96 162) (@Inv.inv Real Real.instInv qz217)) Bool.false 4427 294912 1 884736 (BSN.theta_err_eq 1 2 96 162 EMRow18.d12 EMRow18.d13 rfl) (ep866 rfl)) (ep867 (BSN.norm_eq_sqrt_mul_add (zetaApproximant qz6 1 15)) (@ep868 132565 65536 1331 262144 (@ep873 262144 (@ep880 ep881 ep882 ep869 ep870 ep871 ep872 (@ep883 ep875 ep876 ep872 ep460 ep460 rfl) (@ep884 ep878 ep879 ep881 ep466 ep466 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl)

noncomputable abbrev qz219 := (@Norm.norm Complex Complex.instNorm qz422)

noncomputable abbrev qz426 := (Enclosure.sfrac Bool.false 2 7)

noncomputable def ep886 := @Enclosure.Real.IsNear.of_eq (@HMul.hMul Real Real Real qz0 qz213 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz216))) (@HMul.hMul Real Real Real qz0 (@HMul.hMul Real Real Real qz0 qz219 qz426) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz216))) Bool.false 24458976748432683 31525197391593472 21060511749 31525197391593472 (BSN.zrb_shape_eq qz219 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz216)) qz17 3)

noncomputable def ep887 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz0 qz219 qz426) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz216)) 37303163 1835008 1 1835008 655681041 17179869184 547 17179869184

noncomputable def ep888 := @Enclosure.Real.IsNear.mulLit_ff qz219 qz426 37303163 524288 1 524288 2 7 0 1 37303163 1835008

noncomputable abbrev qz427 := (Complex.re qz476)

noncomputable abbrev qz428 := (Complex.im qz476)

noncomputable abbrev qz220 := (@HAdd.hAdd Real Real Real qz339 (@HMul.hMul Real Real Real qz262 qz427 qz427) (@HMul.hMul Real Real Real qz262 qz428 qz428))

noncomputable abbrev qz221 := qz422

noncomputable def ep889 := @Enclosure.Real.IsNear.of_eq qz219 (Real.sqrt qz220) Bool.false 37303163 524288 1 524288 (BSN.norm_eq_sqrt_mul_add qz221)

noncomputable def ep890 := @Enclosure.Real.IsNear.recentre' (Real.sqrt qz220) Bool.false 37303163 524288 1 524288 37303163

noncomputable def ep891 := @Enclosure.Real.IsNear.sqrt_image qz220 316396381 62500 0 1 18651581 18651582 262144

noncomputable abbrev qz222 := (@HMul.hMul Real Real Real qz262 qz427 qz427)

noncomputable abbrev qz223 := (@HMul.hMul Real Real Real qz262 qz428 qz428)

noncomputable def ep892 := @Enclosure.Real.IsNear.addLit_ff qz222 qz223 49 4 0 1 78907689 15625 0 1

noncomputable abbrev qz224 := qz427

noncomputable def ep893 := @Enclosure.Real.IsNear.mulLit_ff qz224 qz224 7 2 0 1 7 2 0 1 49 4

noncomputable abbrev qz429 := (Enclosure.sfrac Bool.false 7 2)

noncomputable def ep894 := @Enclosure.Complex.IsNear.of_eq qz221 (Complex.mk qz429 qz17) Bool.false 7 2 0 1 Bool.false 71064 1000 0 1 (BSN.s_add_nat_mk qz17 Bool.false 71064 1000 3 qz18)

noncomputable abbrev qz430 := (ep894 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7 2) qz17 Bool.false 7 2 0 1 Bool.false 71064 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 7 2) qz22))

noncomputable def ep895 := @ep893 0 1 (@Enclosure.Complex.IsNear.re_isNear qz221 Bool.false 7 2 0 1 Bool.false 71064 1000 0 1 qz430)

noncomputable def ep896 := ep895 (@Enclosure.Complex.IsNear.re_isNear qz221 Bool.false 7 2 0 1 Bool.false 71064 1000 0 1 qz430)

noncomputable abbrev qz225 := qz428

noncomputable def ep897 := @Enclosure.Real.IsNear.mulLit_ff qz225 qz225 71064 1000 0 1 71064 1000 0 1 78907689 15625

noncomputable def ep898 := @ep897 0 1 (@Enclosure.Complex.IsNear.im_isNear qz221 Bool.false 7 2 0 1 Bool.false 71064 1000 0 1 qz430)

noncomputable def ep899 := ep898 (@Enclosure.Complex.IsNear.im_isNear qz221 Bool.false 7 2 0 1 Bool.false 71064 1000 0 1 qz430)

noncomputable def ep900 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz216)) (Real.sqrt (@HAdd.hAdd Real Real Real qz339 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz216)) (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz216))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz216)) (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz216))))) Bool.false 655681041 17179869184

noncomputable def ep901 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz339 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz216)) (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz216))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz216)) (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz216))))) Bool.false 655681041 17179869184

noncomputable def ep902 := nat_lit 1784380603284203452521384051763253144913985873264320015893

noncomputable def ep903 := nat_lit 1225016520915378468468148586754365561241600000000000000000000

noncomputable def ep904 := nat_lit 1280839779689709834869617756142326818690039539179416227610204932186567

noncomputable def ep905 := nat_lit 527736412454990907049467513448181130204467429376000000000000000000000000000000

noncomputable def ep906 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz339 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz216)) (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz216))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz216)) (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz216)))) ep902 ep903 ep904 ep905

noncomputable def ep907 := nat_lit 1044249611684475799300102848398553632958964476512450954449

noncomputable def ep908 := nat_lit 707468808157455103429287363580259698194162068353725433643610289210471

noncomputable def ep909 := nat_lit 185032747899931913305320300841174877988755349187967265361

noncomputable def ep910 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz216)) (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz216))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz216)) (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz216))) ep907 ep903 ep908 ep905 ep909

noncomputable def ep911 := nat_lit 306254130228844617117037146688591390310400000000000000000000

noncomputable def ep912 := nat_lit 17917842860382960357510324767564597515496170963302837311456082593003

noncomputable def ep913 := nat_lit 16491762889218465845295859795255660318889607168000000000000000000000000000000

noncomputable def ep914 := nat_lit 546473929656024767044574074825814394925895762132944197965866107629147955364534533587827894203187200000000000000000000

noncomputable def ep915 := nat_lit 32314851255799952997872199607

noncomputable def ep916 := nat_lit 1106804644422573096960000000000

noncomputable def ep917 := nat_lit 16677748173422764968147402914689

noncomputable def ep918 := nat_lit 726454687131269672730624000000000000000

noncomputable def ep919 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz216)) (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz216)) ep915 ep916 ep917 ep918 ep915 ep916 ep917

noncomputable def ep920 := nat_lit 13602674292209304873403657481

noncomputable def ep921 := nat_lit 553402322211286548480000000000

noncomputable def ep922 := nat_lit 4013780949347512320729653771641

noncomputable def ep923 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz216) Bool.true ep915 ep916 ep917 ep918 Bool.true ep920 ep921 ep922

noncomputable def ep924 := nat_lit 181613671782817418182656000000000000000

noncomputable def ep925 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz216 Bool.true ep915 ep916 ep917 ep918 Bool.true ep920 ep921 ep922 ep924

noncomputable def ep926 := nat_lit 14775844738913167791140963

noncomputable def ep927 := nat_lit 8854437155380584775680000000

noncomputable def ep928 := nat_lit 7636448519853398940637092161

noncomputable def ep929 := nat_lit 5811637497050157381844992000000000000

noncomputable def ep930 := nat_lit 317373652744122989833120617

noncomputable def ep931 := nat_lit 11529215046068469760000000000

noncomputable def ep932 := nat_lit 436755336345585836126882399849

noncomputable abbrev qz226 := (Complex.re qz423)

noncomputable abbrev qz227 := (Complex.im qz423)

noncomputable def ep933 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)))) qz226) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)))) qz227) ep926 ep927 ep928 ep929 ep930 ep931 ep932

noncomputable def ep934 := nat_lit 20179296864757490909184000000000000000

noncomputable def ep935 := nat_lit 2980518954478667223832650328671322215518107074560000000

noncomputable def ep936 := nat_lit 193721249901671912728166400000

noncomputable def ep937 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)))) qz226 946814143 30000000 0 1 15605855540027741 295147905179352825856 8065414502213872127 ep936 ep926

noncomputable def ep938 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)))) 946814143 30000000 0 1 0 1 0 1 946814143

noncomputable def ep939 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 2840442429 125000 0 1 946814143 30000000 0

noncomputable def ep940 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (Complex.mk (Enclosure.sfrac Bool.true 1 720) qz14) Bool.true 1 720 0 1 Bool.false 0 1 0 1 (BSN.bern_coeff_mk 2 1 30 24 Bool.true BSN.bern_real_2 EMRow18.d14 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 1 720) qz14 Bool.true 1 720 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.true 1 720) qz23)

noncomputable abbrev qz431 := (@HAdd.hAdd Complex Complex Complex qz456 qz455 qz460)

noncomputable abbrev qz228 := qz431

noncomputable def ep941 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)) (@HMul.hMul Complex Complex Complex qz45 (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 2)) qz228) Bool.true 2840442429 125000 0 1 Bool.true 2800555677423 7812500 0 1

noncomputable abbrev qz229 := (Complex.re qz431)

noncomputable abbrev qz230 := (Complex.im qz431)

noncomputable def ep942 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 2))) qz229) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 2))) qz230) 315583881 25000 0 1 157815378 15625 0 1

noncomputable def ep943 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 2))) qz229 315583881 62500 0 1 5 2 0 1 315583881 25000

noncomputable abbrev qz432 := (@HAdd.hAdd Complex Complex Complex qz456 qz455 (@Nat.cast Complex Complex.instNatCast 1))

noncomputable abbrev qz231 := qz432

noncomputable def ep944 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 2)) (@HMul.hMul Complex Complex Complex qz45 (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)) qz231) Bool.true 315583881 62500 0 1 Bool.false 17766 125 0 1

noncomputable abbrev qz232 := (Complex.re qz432)

noncomputable abbrev qz233 := (Complex.im qz432)

noncomputable def ep945 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1))) qz232) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1))) qz233) 3 4 0 1 78907689 15625 0 1

noncomputable def ep946 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1))) qz232 1 2 0 1 3 2 0 1 3 4

noncomputable def ep947 := @ep946 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 71064 1000 0 1 ep425)

noncomputable abbrev qz433 := (Enclosure.sfrac Bool.false 3 2)

noncomputable def ep948 := @Enclosure.Complex.IsNear.of_eq qz231 (Complex.mk qz433 qz17) Bool.false 3 2 0 1 Bool.false 71064 1000 0 1 (BSN.s_add_nat_mk qz17 Bool.false 71064 1000 1 qz18)

noncomputable abbrev qz434 := (ep948 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 3 2) qz17 Bool.false 3 2 0 1 Bool.false 71064 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 3 2) qz22))

noncomputable def ep949 := ep947 (@Enclosure.Complex.IsNear.re_isNear qz231 Bool.false 3 2 0 1 Bool.false 71064 1000 0 1 qz434)

noncomputable def ep950 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1))) qz233 71064 1000 0 1 71064 1000 0 1 78907689 15625

noncomputable def ep951 := @ep950 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 71064 1000 0 1 ep425)

noncomputable def ep952 := ep951 (@Enclosure.Complex.IsNear.im_isNear qz231 Bool.false 3 2 0 1 Bool.false 71064 1000 0 1 qz434)

noncomputable def ep953 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)) qz231 Bool.true 315583881 62500 0 1 Bool.false 17766 125 0 1 (@ep945 315583881 315583881 62500 0 1 (ep949 rfl) (ep952 rfl) rfl rfl)

noncomputable def ep954 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1))) qz233) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1))) qz232) 8883 250 0 1 26649 250 0 1

noncomputable def ep955 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1))) qz233 1 2 0 1 71064 1000 0 1 8883 250

noncomputable def ep956 := @ep955 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 71064 1000 0 1 ep425)

noncomputable def ep957 := ep956 (@Enclosure.Complex.IsNear.im_isNear qz231 Bool.false 3 2 0 1 Bool.false 71064 1000 0 1 qz434)

noncomputable def ep958 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1))) qz232 71064 1000 0 1 3 2 0 1 26649 250

noncomputable def ep959 := @ep958 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 71064 1000 0 1 ep425)

noncomputable def ep960 := ep959 (@Enclosure.Complex.IsNear.re_isNear qz231 Bool.false 3 2 0 1 Bool.false 71064 1000 0 1 qz434)

noncomputable abbrev qz234 := (ep944 (BSN.ascPochhammer_succ_eval_c 1 2 qz267 rfl) (ep953 (@ep954 8883000 17766 125 0 1 (ep957 rfl) (ep960 rfl) rfl rfl)))

noncomputable def ep961 := @ep943 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 315583881 62500 0 1 Bool.false 17766 125 0 1 qz234)

noncomputable abbrev qz435 := (Enclosure.sfrac Bool.false 5 2)

noncomputable def ep962 := @Enclosure.Complex.IsNear.of_eq qz228 (Complex.mk qz435 qz17) Bool.false 5 2 0 1 Bool.false 71064 1000 0 1 (BSN.s_add_nat_mk qz17 Bool.false 71064 1000 2 qz18)

noncomputable abbrev qz436 := (ep962 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 5 2) qz17 Bool.false 5 2 0 1 Bool.false 71064 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 5 2) qz22))

noncomputable def ep963 := ep961 (@Enclosure.Complex.IsNear.re_isNear qz228 Bool.false 5 2 0 1 Bool.false 71064 1000 0 1 qz436)

noncomputable def ep964 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 2))) qz230 17766 125 0 1 71064 1000 0 1 157815378 15625

noncomputable def ep965 := @ep964 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 315583881 62500 0 1 Bool.false 17766 125 0 1 qz234)

noncomputable def ep966 := ep965 (@Enclosure.Complex.IsNear.im_isNear qz228 Bool.false 5 2 0 1 Bool.false 71064 1000 0 1 qz436)

noncomputable def ep967 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 2)) qz228 Bool.true 2840442429 125000 0 1 Bool.true 2800555677423 7812500 0 1 (@ep942 8876382590625 2840442429 125000 0 1 (ep963 rfl) (ep966 rfl) rfl rfl)

noncomputable def ep968 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 2))) qz230) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 2))) qz229) 2803331614923 7812500 0 1 8883 25 0 1

noncomputable def ep969 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 2))) qz230 315583881 62500 0 1 71064 1000 0 1 2803331614923 7812500

noncomputable def ep970 := @ep969 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 315583881 62500 0 1 Bool.false 17766 125 0 1 qz234)

noncomputable def ep971 := ep970 (@Enclosure.Complex.IsNear.im_isNear qz228 Bool.false 5 2 0 1 Bool.false 71064 1000 0 1 qz436)

noncomputable def ep972 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 2))) qz229 17766 125 0 1 5 2 0 1 8883 25

noncomputable def ep973 := @ep972 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 315583881 62500 0 1 Bool.false 17766 125 0 1 qz234)

noncomputable def ep974 := ep973 (@Enclosure.Complex.IsNear.re_isNear qz228 Bool.false 5 2 0 1 Bool.false 71064 1000 0 1 qz436)

noncomputable abbrev qz235 := (ep941 (BSN.ascPochhammer_succ_eval_c 2 3 qz267 rfl) (ep967 (@ep968 70013891935575 2800555677423 7812500 0 1 (ep971 rfl) (ep974 rfl) rfl rfl)))

noncomputable def ep975 := @ep939 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep940) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 2840442429 125000 0 1 Bool.true 2800555677423 7812500 0 1 qz235)

noncomputable def ep976 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 2800555677423 7812500 0 1 0 1 0

noncomputable def ep977 := @ep976 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep940) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 2840442429 125000 0 1 Bool.true 2800555677423 7812500 0 1 qz235)

noncomputable def ep978 := @Enclosure.Real.IsNear.addLit_ft_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)))) 311172853047 625000000 0 1 0 1 0 1 311172853047

noncomputable def ep979 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 2800555677423 7812500 0 1 311172853047 625000000 0

noncomputable def ep980 := @ep979 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep940) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 2840442429 125000 0 1 Bool.true 2800555677423 7812500 0 1 qz235)

noncomputable def ep981 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 2840442429 125000 0 1 0 1 0

noncomputable def ep982 := @ep981 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep940) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 2840442429 125000 0 1 Bool.true 2800555677423 7812500 0 1 qz235)

noncomputable def ep983 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.false 946814143 30000000 0 1 Bool.false 311172853047 625000000 0 1 (@ep938 946814143 30000000 0 1 (ep975 rfl) (ep977 rfl) rfl rfl) (@ep978 311172853047 625000000 0 1 (ep980 rfl) (ep982 rfl) rfl rfl)

noncomputable def ep984 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 946814143 30000000 0 1 Bool.false 311172853047 625000000 0 1 ep983

noncomputable def ep985 := nat_lit 96860624950835956364083200000

noncomputable def ep986 := @Enclosure.Complex.IsNear.re_isNear qz216 Bool.true 15605855540027741 295147905179352825856 8065414502213872127 ep936 Bool.false 1019927187209311 18446744073709551616 4210733668463209501 ep985

noncomputable abbrev qz437 := (@Nat.cast Real Real.instNatCast 170859375)

noncomputable abbrev qz236 := (@Inv.inv Real Real.instInv (Real.sqrt qz437))

noncomputable def ep987 := @Enclosure.Complex.IsNear.of_eq qz216 (Complex.mk (@HMul.hMul Real Real Real qz0 qz236 qz128) (@HMul.hMul Real Real Real qz0 qz236 qz129)) Bool.true 15605855540027741 295147905179352825856 8065414502213872127 ep936 Bool.false 1019927187209311 18446744073709551616 4210733668463209501

noncomputable abbrev qz237 := (Real.sqrt qz437)

noncomputable def ep988 := @Enclosure.Real.IsNear.inv_image qz237 224563546933833 17179869184 1 17179869184 657158 657159 8589934592 (@Enclosure.Real.IsNear.of_eq qz237 (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz437 qz19)) Bool.false 224563546933833 17179869184 1 17179869184 (BSN.sqrt_natCast_div_one 170859375) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz437 qz19)) Bool.false 224563546933833 17179869184 1 17179869184 224563546933833 17179869184 1 17179869184 (BSN.sqrt_enclosure 170859375 1 112281773466916 112281773466917 8589934592 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep989 := nat_lit 838100943070293300562886656

noncomputable def ep990 := nat_lit 309485009821345068724781056

noncomputable def ep991 := nat_lit 3938118750000000000000000

noncomputable def ep992 := nat_lit 2124039924396124256730046692528675

noncomputable def ep993 := nat_lit 69486322526432349988248161643105

noncomputable def ep994 := BSN.log_dyadic_bound 7 23 10 9 ep992 8589934592 3938118750 ep993 56114196246175274031825 5399707268 30 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base9 (BSN.artanhP 7) (BSN.artanhQ 23) 0 9 ep993 ep992 56114196246175274031825 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep995 := @Enclosure.Real.IsNear.mulLit_ff qz17 qz131 71064 1000 0 1 12195973876373221 4503599627370496 160001890297 630099000000000000000 108336835943823322143 562949953421312000 52640621907713 2917125000000000000000 qz22 (BSN.isNear_log_sfrac 15 1 12195973876373221 4503599627370496 160001890297 630099000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz130) Bool.false ep989 ep990 1000011814356250 ep991 12195973876373221 4503599627370496 160001890297 630099000000000000000 (BSN.log_rat_reduce_isNear 15 1 3 30 16 5399707268 8589934592 24973259072661432 36028797018963968 3938118750 1000000000000000 rfl rfl rfl rfl (ep994 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep996 := nat_lit 999918360101577836315279360

noncomputable def ep997 := nat_lit 1237940039285380274899124224

noncomputable def ep998 := nat_lit 30583919299955063987071613672124025137865418357298586612574287928795645878972444825716806654299079870025196764484329834015561416515536004177930906189094203359614238185041

noncomputable def ep999 := nat_lit 1723989524678609869184368353634558086375647288945605880257499904391989104065417411410730399287089189440146844853530817917959165259045966673531664948206962296697359276441600

noncomputable def ep1000 := nat_lit 277572767177085169950502982608971158667290451521151977783476412771480742370908265156855851628142762289730055222392076357433570264557686395470670580282063638484561

noncomputable def ep1001 := nat_lit 185511110035038125896357582516145117156526203522474762963205857346234093359416545872502656903429195191801510713124291906916457445077920788615271809604177916204229323380305

noncomputable def ep1002 := nat_lit 156883046745753498095777520180744785860183903294050135103432491299671008469952984438376466335125116239053362881671304430534284038573182967291381510286833568999459694156185600

noncomputable def ep1003 := BSN.cos_dyadic_bound_f 28419389084933 35184372088832 4 3 17179869184 7883929139 ep998 ep999 ep1000 ep1001 ep1002 ep1000 11873737873 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 28419389084933) (BSN.cosEvenQ 35184372088832) 0 3 ep998 ep999 ep1000 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 28419389084933) (BSN.cosOddQ 35184372088832) 0 3 ep1001 ep1002 ep1000 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz438 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 1653088927365) (@Nat.cast Real Real.instNatCast 8589934592))

noncomputable def ep1004 := @Enclosure.Real.IsNear.cos_image qz132 qz438 Bool.false 1653088927365 8589934592 311 17179869184 Bool.true 11873737873 17179869184 1 3938118750 (@Enclosure.Real.IsNear.recentre' qz132 Bool.false 108336835943823322143 562949953421312000 52640621907713 2917125000000000000000 1653088927365 8589934592 311 17179869184 (ep995 rfl) rfl) (Enclosure.sfrac_false_div 1653088927365 8589934592) (BSN.cos_reduce2 qz438 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast ep996) (@Nat.cast Real Real.instNatCast ep997)) 226375608064910080 72057594037927936 Bool.false 11873737873 17179869184 30 1000000000000000 7876237500 3938118750 (BSN.sin_reduce_arg_pos_rat_q2 1653088927365 8589934592 226375608064910080 72057594037927936 30 ep996 ep997 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 11873737873 17179869184 ep996 ep997 28419389084933 35184372088832 7883929139 7876237500 (ep1003 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1005 := nat_lit 3023438122681059046577101654558980630489421211222949184931057831311345203658405302683004822639598604693664267745

noncomputable def ep1006 := nat_lit 852239132436968601736534718962914620494087683347851114682261747749608011033589111964107092533864866956228564090880

noncomputable def ep1007 := nat_lit 425517967923684632687993519045676235295446691804449615270102729027387475565327844442316131724176663581916641

noncomputable def ep1008 := nat_lit 7917839482692802013534723772433161032615148639511469232585190344254145477478241452421629833176157202456654740961

noncomputable def ep1009 := nat_lit 15624384094677757698503136514320101375724940861377270435841465375409480202282467052675296696454189227530857008332800

noncomputable def ep1010 := BSN.sin_dyadic_bound_f 28419389084933 35184372088832 3 2 17179869184 7883929139 ep1005 ep1006 ep1007 ep1008 ep1009 ep1007 12416209328 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 28419389084933) (BSN.sinEvenQ 35184372088832) 0 2 ep1005 ep1006 ep1007 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 28419389084933) (BSN.sinOddQ 35184372088832) 0 2 ep1008 ep1009 ep1007 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1011 := @Enclosure.Real.IsNear.sin_image qz132 qz438 Bool.false 1653088927365 8589934592 311 17179869184 Bool.true 12416209328 17179869184 1 3938118750 (@Enclosure.Real.IsNear.recentre' qz132 Bool.false 108336835943823322143 562949953421312000 52640621907713 2917125000000000000000 1653088927365 8589934592 311 17179869184 (ep995 rfl) rfl) (Enclosure.sfrac_false_div 1653088927365 8589934592) (BSN.sin_reduce2 qz438 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast ep996) (@Nat.cast Real Real.instNatCast ep997)) 226375608064910080 72057594037927936 Bool.false 12416209328 17179869184 30 1000000000000000 7876237500 3938118750 (BSN.sin_reduce_arg_pos_rat_q2 1653088927365 8589934592 226375608064910080 72057594037927936 30 ep996 ep997 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 12416209328 17179869184 ep996 ep997 28419389084933 35184372088832 7883929139 7876237500 (ep1010 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz439 := (@Enclosure.Real.IsNear.recentre' qz236 Bool.false 1314317 17179869184 1 17179869184 1314317 17179869184 1 17179869184 (ep988 rfl rfl) rfl)

noncomputable def ep1012 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz236 qz128) (@HMul.hMul Real Real Real qz0 qz236 qz129) Bool.true 15605855540027741 295147905179352825856 8065414502213872127 ep936 Bool.false 1019927187209311 18446744073709551616 4210733668463209501 ep985 (@Enclosure.Real.IsNear.mulLit_ft qz236 qz128 1314317 17179869184 1 17179869184 11873737873 17179869184 620967400217 33828182478028800000 15605855540027741 295147905179352825856 8065414502213872127 ep936 qz439 (@Enclosure.Real.IsNear.recentre' qz128 Bool.true 11873737873 17179869184 1241934800434 67656364956057600000 11873737873 17179869184 620967400217 33828182478028800000 (ep1004 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz236 qz129 1314317 17179869184 1 17179869184 776013083 1073741824 620967400217 33828182478028800000 1019927187209311 18446744073709551616 4210733668463209501 ep985 qz439 (@Enclosure.Real.IsNear.neg qz133 Bool.true 776013083 1073741824 620967400217 33828182478028800000 (@Enclosure.Real.IsNear.recentre' qz133 Bool.true 12416209328 17179869184 1241934800434 67656364956057600000 776013083 1073741824 620967400217 33828182478028800000 (ep1011 rfl rfl) rfl)) rfl)

noncomputable def ep1013 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)))) qz227 311172853047 625000000 0 1 1019927187209311 18446744073709551616 4210733668463209501 ep985 ep930

noncomputable def ep1014 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 946814143 30000000 0 1 Bool.false 311172853047 625000000 0 1 ep983

noncomputable def ep1015 := @Enclosure.Complex.IsNear.im_isNear qz216 Bool.true 15605855540027741 295147905179352825856 8065414502213872127 ep936 Bool.false 1019927187209311 18446744073709551616 4210733668463209501 ep985

noncomputable def ep1016 := nat_lit 553402322211286548480000000

noncomputable def ep1017 := nat_lit 3986782189707239830718772643

noncomputable def ep1018 := nat_lit 2905818748525078690922496000000000000

noncomputable def ep1019 := nat_lit 4856118592629763076496376827

noncomputable def ep1020 := nat_lit 184467440737095516160000000000

noncomputable def ep1021 := nat_lit 836579347220179962513273440323

noncomputable def ep1022 := @Enclosure.Real.IsNear.addLit_ft_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)))) qz227) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)))) qz226) 965681485679984356085473 ep1016 ep1017 ep1018 ep1019 ep1020 ep1021

noncomputable def ep1023 := nat_lit 40358593729514981818368000000000000000

noncomputable def ep1024 := nat_lit 2509250513864132642748677024573191006989540392960000000

noncomputable def ep1025 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)))) qz227 946814143 30000000 0 1 1019927187209311 18446744073709551616 4210733668463209501 ep985 965681485679984356085473

noncomputable def ep1026 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)))) qz226 311172853047 625000000 0 1 15605855540027741 295147905179352825856 8065414502213872127 ep936 ep1019

noncomputable abbrev qz440 := (@ep987 ep985 (BSN.cpow_neg_s_sub_mk qz17 71064 1000 15 3 170859375 qz18 rfl EMRow18.d15) ep1012)

noncomputable def ep1027 := ep925 (@ep933 ep934 ep935 ep915 ep916 ep917 ep918 (@ep937 ep927 ep928 ep929 ep984 (ep986 qz440) rfl) (@ep1013 ep931 ep932 ep934 ep1014 (ep1015 qz440) rfl) rfl rfl) (@ep1022 ep1023 ep1024 ep920 ep921 ep922 ep924 (@ep1025 ep1016 ep1017 ep1018 ep984 (ep1015 qz440) rfl) (@ep1026 ep1020 ep1021 ep1023 ep1014 (ep986 qz440) rfl) rfl rfl)

noncomputable def ep1028 := @Enclosure.Real.IsNear.mulLit_tt (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz216)) (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz216)) ep920 ep921 ep922 ep924 ep920 ep921 ep922

noncomputable def ep1029 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz216) Bool.true ep915 ep916 ep917 ep918 Bool.true ep920 ep921 ep922

noncomputable def ep1030 := @ep887 24458976748432683 31525197391593472 21060511749 31525197391593472 (@ep888 1 1835008 (ep889 (@ep890 524288 1 524288 (ep891 (@ep892 316396381 316396381 62500 0 1 (ep896 rfl) (ep899 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) (Enclosure.Real.IsNear.const Bool.false 2 7) rfl) (@ep900 547 17179869184 (BSN.norm_eq_sqrt_mul_add (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz216)) (@ep901 547 17179869184 655681041 17179869184 547 17179869184 (@ep906 327840247 327840794 8589934592 (@ep910 ep911 ep912 ep913 ep914 ep902 ep903 ep904 ep905 (@ep919 ep918 ep907 ep903 ep908 ep905 (@ep923 ep924 ep1027) (@ep923 ep924 ep1027) rfl) (@ep1028 ep924 ep909 ep911 ep912 ep913 (@ep1029 ep924 ep1027) (@ep1029 ep924 ep1027) rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl

theorem EMRow18.d16 : Enclosure.Real.IsNear (@HAdd.hAdd Real Real Real qz339 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz6 1 15))) (@HMul.hMul Real Real Real qz0 qz213 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz216)))) Bool.false 228746010238670467 283726776524341248 7488277166095 94575592174780416 := ep885 (ep886 ep1030) rfl rfl

noncomputable abbrev qz477 := (@HAdd.hAdd Complex Complex Complex qz479 qz485 (@Nat.cast Complex Complex.instNatCast 3))

noncomputable abbrev qz441 := qz477

noncomputable abbrev qz238 := (@HDiv.hDiv Real Real Real qz265 (@Norm.norm Complex Complex.instNorm qz441) (@HAdd.hAdd Real Real Real qz339 (Complex.re qz381) (@Nat.cast Real Real.instNatCast 3)))

noncomputable abbrev qz442 := (@HPow.hPow Complex Complex Complex qz457 qz470 (@HSub.hSub Complex Complex Complex qz463 qz472 qz459))

noncomputable abbrev qz239 := qz442

noncomputable def ep1031 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz142 1 15))) (@HMul.hMul Real Real Real qz0 qz238 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) qz239))) 4303048427 77309411328 19022239 231928233984 28191294219524865 31525197391593472 22875591387

noncomputable def ep1032 := nat_lit 2315106811732677309721739264

noncomputable def ep1033 := @Enclosure.Real.IsNear.mulLit_ff (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz142 1 15)) 4427 294912 1 884736 972001 262144 1359 262144 4303048427 77309411328

noncomputable def ep1034 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (zetaApproximant qz142 1 15)) (Real.sqrt (@HAdd.hAdd Real Real Real qz339 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz142 1 15)) (Complex.re (zetaApproximant qz142 1 15))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz142 1 15)) (Complex.im (zetaApproximant qz142 1 15))))) Bool.false 972001 262144 1359 262144

noncomputable def ep1035 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz339 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz142 1 15)) (Complex.re (zetaApproximant qz142 1 15))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz142 1 15)) (Complex.im (zetaApproximant qz142 1 15))))) Bool.false 1944002 524288 2718 524288

noncomputable def ep1036 := nat_lit 29200312319565260699159858591008505493857

noncomputable def ep1037 := nat_lit 2123896109554157046496193530979942400000

noncomputable def ep1038 := nat_lit 4960017900727886858495495728124108584286779678053655063

noncomputable def ep1039 := nat_lit 129055244705539347760571587355907399773857618329600000000

noncomputable def ep1040 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz339 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz142 1 15)) (Complex.re (zetaApproximant qz142 1 15))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz142 1 15)) (Complex.im (zetaApproximant qz142 1 15)))) ep1036 ep1037 ep1038 ep1039 970642 973360

noncomputable def ep1041 := nat_lit 63332289651806611732666078213035620628184602528961

noncomputable def ep1042 := nat_lit 4606614463266812925918229961947415152951296000000

noncomputable def ep1043 := nat_lit 9863802433041311080249784973962337515157412807623893753

noncomputable def ep1044 := nat_lit 258110489411078695521143174711814799547715236659200000000

noncomputable def ep1045 := nat_lit 1590220243435308398804034998313712655661554569

noncomputable def ep1046 := nat_lit 18744456138154212247068827428626551138715516161138791

noncomputable def ep1047 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz142 1 15)) (Complex.re (zetaApproximant qz142 1 15))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz142 1 15)) (Complex.im (zetaApproximant qz142 1 15))) ep1041 ep1042 ep1043 ep1044 ep1045 ep1042 ep1046

noncomputable def ep1048 := nat_lit 86036829803692898507047724903938266515905078886400000000

noncomputable def ep1049 := nat_lit 291754767033388633957615206387493868767228116301527424975615429849610340849451695508165754880000000

noncomputable def ep1050 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (zetaApproximant qz142 1 15)) (Complex.re (zetaApproximant qz142 1 15)) ep573 ep574 ep575 ep576 ep573 ep574 ep575 ep576 ep1041

noncomputable def ep1051 := @Enclosure.Real.IsNear.mulLit_tt (Complex.im (zetaApproximant qz142 1 15)) (Complex.im (zetaApproximant qz142 1 15)) 39877565665864163915587 ep574 ep693 ep694 39877565665864163915587 ep574 ep693 ep694 ep1045

noncomputable def ep1052 := @ep1031 31525197391593472 ep1032 269513904551588617 283726776524341248 70429562453273 851180329573023744 (@ep1033 19022239 231928233984 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaStirlingErrorBound 1 2) (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 96 162) (@Inv.inv Real Real.instInv qz217)) Bool.false 4427 294912 1 884736 (BSN.theta_err_eq 1 2 96 162 EMRow18.d12 EMRow18.d13 rfl) (ep866 rfl)) (ep1034 (BSN.norm_eq_sqrt_mul_add (zetaApproximant qz142 1 15)) (@ep1035 972001 262144 1359 262144 (@ep1040 262144 (@ep1047 ep1048 ep1049 ep1036 ep1037 ep1038 ep1039 (@ep1050 ep1042 ep1043 ep1044 ep846 ep846 rfl) (@ep1051 ep1042 ep1046 ep1048 ep854 ep854 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl)

noncomputable abbrev qz240 := (@Norm.norm Complex Complex.instNorm qz441)

noncomputable def ep1053 := @Enclosure.Real.IsNear.of_eq (@HMul.hMul Real Real Real qz0 qz238 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) qz239))) (@HMul.hMul Real Real Real qz0 (@HMul.hMul Real Real Real qz0 qz240 qz426) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) qz239))) Bool.false 28191294219524865 31525197391593472 22875591387 31525197391593472 (BSN.zrb_shape_eq qz240 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) qz239)) qz151 3)

noncomputable def ep1054 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz0 qz240 qz426) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) qz239)) 38649533 1835008 1 1835008 729408405 17179869184 573 17179869184

noncomputable def ep1055 := @Enclosure.Real.IsNear.mulLit_ff qz240 qz426 38649533 524288 1 524288 2 7 0 1 38649533 1835008

noncomputable abbrev qz443 := (Complex.re qz477)

noncomputable abbrev qz444 := (Complex.im qz477)

noncomputable abbrev qz241 := (@HAdd.hAdd Real Real Real qz339 (@HMul.hMul Real Real Real qz262 qz443 qz443) (@HMul.hMul Real Real Real qz262 qz444 qz444))

noncomputable abbrev qz242 := qz441

noncomputable def ep1056 := @Enclosure.Real.IsNear.of_eq qz240 (Real.sqrt qz241) Bool.false 38649533 524288 1 524288 (BSN.norm_eq_sqrt_mul_add qz242)

noncomputable def ep1057 := @Enclosure.Real.IsNear.recentre' (Real.sqrt qz241) Bool.false 38649533 524288 1 524288 38649533

noncomputable def ep1058 := @Enclosure.Real.IsNear.sqrt_image qz241 217374529 40000 0 1 19324766 19324767 262144

noncomputable abbrev qz243 := (@HMul.hMul Real Real Real qz262 qz443 qz443)

noncomputable abbrev qz244 := (@HMul.hMul Real Real Real qz262 qz444 qz444)

noncomputable def ep1059 := @Enclosure.Real.IsNear.addLit_ff qz243 qz244 49 4 0 1 216884529 40000 0 1

noncomputable abbrev qz245 := qz443

noncomputable def ep1060 := @Enclosure.Real.IsNear.mulLit_ff qz245 qz245 7 2 0 1 7 2 0 1 49 4

noncomputable def ep1061 := @Enclosure.Complex.IsNear.of_eq qz242 (Complex.mk qz429 qz151) Bool.false 7 2 0 1 Bool.false 73635 1000 0 1 (BSN.s_add_nat_mk qz151 Bool.false 73635 1000 3 qz152)

noncomputable abbrev qz445 := (ep1061 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7 2) qz151 Bool.false 7 2 0 1 Bool.false 73635 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 7 2) qz153))

noncomputable def ep1062 := @ep1060 0 1 (@Enclosure.Complex.IsNear.re_isNear qz242 Bool.false 7 2 0 1 Bool.false 73635 1000 0 1 qz445)

noncomputable def ep1063 := ep1062 (@Enclosure.Complex.IsNear.re_isNear qz242 Bool.false 7 2 0 1 Bool.false 73635 1000 0 1 qz445)

noncomputable abbrev qz246 := qz444

noncomputable def ep1064 := @Enclosure.Real.IsNear.mulLit_ff qz246 qz246 73635 1000 0 1 73635 1000 0 1 216884529 40000

noncomputable def ep1065 := @ep1064 0 1 (@Enclosure.Complex.IsNear.im_isNear qz242 Bool.false 7 2 0 1 Bool.false 73635 1000 0 1 qz445)

noncomputable def ep1066 := ep1065 (@Enclosure.Complex.IsNear.im_isNear qz242 Bool.false 7 2 0 1 Bool.false 73635 1000 0 1 qz445)

noncomputable def ep1067 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) qz239)) (Real.sqrt (@HAdd.hAdd Real Real Real qz339 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) qz239)) (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) qz239))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) qz239)) (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) qz239))))) Bool.false 729408405 17179869184

noncomputable def ep1068 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz339 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) qz239)) (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) qz239))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) qz239)) (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) qz239))))) Bool.false 729408405 17179869184

noncomputable def ep1069 := nat_lit 115774705420422872602659185765795940677813844854446086817

noncomputable def ep1070 := nat_lit 64226146171768194647622868625227281137223598080000000000000

noncomputable def ep1071 := nat_lit 390792337324320148816075407050194790858735522938206933510299281635143

noncomputable def ep1072 := nat_lit 138342934106601136337575611845359994196319909806342144000000000000000000000000

noncomputable def ep1073 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz339 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) qz239)) (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) qz239))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) qz239)) (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) qz239)))) ep1069 ep1070 ep1071 ep1072

noncomputable def ep1074 := nat_lit 578573694741468045650648624347401277442341150031841593281

noncomputable def ep1075 := nat_lit 321130730858840973238114343126136405686117990400000000000000

noncomputable def ep1076 := nat_lit 389316431048817821899695556741863194854911823802454882494315569197259

noncomputable def ep1077 := nat_lit 74958090161579340661826120394606486682018560097210201

noncomputable def ep1078 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) qz239)) (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) qz239))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) qz239)) (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) qz239))) ep1074 ep1075 ep1076 ep1072 ep1077

noncomputable def ep1079 := nat_lit 80282682714710243309528585781534101421529497600000000000000

noncomputable def ep1080 := nat_lit 368976568875581729094962577082899000955924783938012753995928109471

noncomputable def ep1081 := nat_lit 34585733526650284084393902961339998549079977451585536000000000000000000000000

noncomputable def ep1082 := nat_lit 46473519708284268334026145219380566568053932046276676900588919357745013819822178731555253096279965696000000000000000

noncomputable def ep1083 := nat_lit 24053558878915777723148157409

noncomputable def ep1084 := nat_lit 566683977944357425643520000000

noncomputable def ep1085 := nat_lit 12329789686246718446935949788997

noncomputable def ep1086 := nat_lit 371944799811210072438079488000000000000

noncomputable def ep1087 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) qz239)) (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) qz239)) ep1083 ep1084 ep1085 ep1086 ep1083 ep1084 ep1085

noncomputable def ep1088 := nat_lit 273784751513993818811399899

noncomputable def ep1089 := nat_lit 283341988972178712821760000000

noncomputable def ep1090 := nat_lit 1026646044144909535417960771061

noncomputable def ep1091 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) qz239) Bool.true ep1083 ep1084 ep1085 ep1086 Bool.true ep1088 ep1089 ep1090

noncomputable def ep1092 := nat_lit 185972399905605036219039744000000000000

noncomputable def ep1093 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) qz239 Bool.true ep1083 ep1084 ep1085 ep1086 Bool.true ep1088 ep1089 ep1090 ep1092

noncomputable def ep1094 := nat_lit 944473296573929042739200000

noncomputable def ep1095 := nat_lit 398822273751168912729336337

noncomputable def ep1096 := nat_lit 1859723999056050362190397440000000000

noncomputable def ep1097 := nat_lit 23930513198276019830949080809

noncomputable def ep1098 := nat_lit 12250025231496484664390082521597

noncomputable abbrev qz247 := (Complex.re qz442)

noncomputable abbrev qz248 := (Complex.im qz442)

noncomputable def ep1099 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3)))) qz247) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3)))) qz248) 205076134399596486998461 ep1094 ep1095 ep1096 ep1097 ep1084 ep1098

noncomputable def ep1100 := nat_lit 22717944048704685514432232755030956162763690134732800000

noncomputable def ep1101 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3)))) qz247 650603587 19200000 0 1 945627130701309 147573952589676412928 613003496630228251 ep985 205076134399596486998461

noncomputable def ep1102 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3)))) 650603587 19200000 0 1 0 1 0 1 650603587

noncomputable def ep1103 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 1951810761 80000 0 1 650603587 19200000 0

noncomputable abbrev qz446 := (@HAdd.hAdd Complex Complex Complex qz456 qz471 qz460)

noncomputable abbrev qz249 := qz446

noncomputable def ep1104 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3)) (@HMul.hMul Complex Complex Complex qz45 (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 2)) qz249) Bool.true 1951810761 80000 0 1 Bool.true 3190671248583 8000000 0 1

noncomputable abbrev qz250 := (Complex.re qz446)

noncomputable abbrev qz251 := (Complex.im qz446)

noncomputable def ep1105 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 2))) qz250) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 2))) qz251) 216854529 16000 0 1 216884529 20000 0 1

noncomputable def ep1106 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 2))) qz250 216854529 40000 0 1 5 2 0 1 216854529 16000

noncomputable abbrev qz447 := (@HAdd.hAdd Complex Complex Complex qz456 qz471 (@Nat.cast Complex Complex.instNatCast 1))

noncomputable abbrev qz252 := qz447

noncomputable def ep1107 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 2)) (@HMul.hMul Complex Complex Complex qz45 (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1)) qz252) Bool.true 216854529 40000 0 1 Bool.false 14727 100 0 1

noncomputable abbrev qz253 := (Complex.re qz447)

noncomputable abbrev qz254 := (Complex.im qz447)

noncomputable def ep1108 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1))) qz253) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1))) qz254) 3 4 0 1 216884529 40000 0 1

noncomputable def ep1109 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1))) qz253 1 2 0 1 3 2 0 1 3 4

noncomputable def ep1110 := @ep1109 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 73635 1000 0 1 ep813)

noncomputable def ep1111 := @Enclosure.Complex.IsNear.of_eq qz252 (Complex.mk qz433 qz151) Bool.false 3 2 0 1 Bool.false 73635 1000 0 1 (BSN.s_add_nat_mk qz151 Bool.false 73635 1000 1 qz152)

noncomputable abbrev qz448 := (ep1111 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 3 2) qz151 Bool.false 3 2 0 1 Bool.false 73635 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 3 2) qz153))

noncomputable def ep1112 := ep1110 (@Enclosure.Complex.IsNear.re_isNear qz252 Bool.false 3 2 0 1 Bool.false 73635 1000 0 1 qz448)

noncomputable def ep1113 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1))) qz254 73635 1000 0 1 73635 1000 0 1 216884529 40000

noncomputable def ep1114 := @ep1113 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 73635 1000 0 1 ep813)

noncomputable def ep1115 := ep1114 (@Enclosure.Complex.IsNear.im_isNear qz252 Bool.false 3 2 0 1 Bool.false 73635 1000 0 1 qz448)

noncomputable def ep1116 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1)) qz252 Bool.true 216854529 40000 0 1 Bool.false 14727 100 0 1 (@ep1108 867418116 216854529 40000 0 1 (ep1112 rfl) (ep1115 rfl) rfl rfl)

noncomputable def ep1117 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1))) qz254) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1))) qz253) 14727 400 0 1 44181 400 0 1

noncomputable def ep1118 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1))) qz254 1 2 0 1 73635 1000 0 1 14727 400

noncomputable def ep1119 := @ep1118 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 73635 1000 0 1 ep813)

noncomputable def ep1120 := ep1119 (@Enclosure.Complex.IsNear.im_isNear qz252 Bool.false 3 2 0 1 Bool.false 73635 1000 0 1 qz448)

noncomputable def ep1121 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1))) qz253 73635 1000 0 1 3 2 0 1 44181 400

noncomputable def ep1122 := @ep1121 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 73635 1000 0 1 ep813)

noncomputable def ep1123 := ep1122 (@Enclosure.Complex.IsNear.re_isNear qz252 Bool.false 3 2 0 1 Bool.false 73635 1000 0 1 qz448)

noncomputable abbrev qz255 := (ep1107 (BSN.ascPochhammer_succ_eval_c 1 2 qz381 rfl) (ep1116 (@ep1117 23563200 14727 100 0 1 (ep1120 rfl) (ep1123 rfl) rfl rfl)))

noncomputable def ep1124 := @ep1106 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 216854529 40000 0 1 Bool.false 14727 100 0 1 qz255)

noncomputable def ep1125 := @Enclosure.Complex.IsNear.of_eq qz249 (Complex.mk qz435 qz151) Bool.false 5 2 0 1 Bool.false 73635 1000 0 1 (BSN.s_add_nat_mk qz151 Bool.false 73635 1000 2 qz152)

noncomputable abbrev qz449 := (ep1125 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 5 2) qz151 Bool.false 5 2 0 1 Bool.false 73635 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 5 2) qz153))

noncomputable def ep1126 := ep1124 (@Enclosure.Complex.IsNear.re_isNear qz249 Bool.false 5 2 0 1 Bool.false 73635 1000 0 1 qz449)

noncomputable def ep1127 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 2))) qz251 14727 100 0 1 73635 1000 0 1 216884529 20000

noncomputable def ep1128 := @ep1127 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 216854529 40000 0 1 Bool.false 14727 100 0 1 qz255)

noncomputable def ep1129 := ep1128 (@Enclosure.Complex.IsNear.im_isNear qz249 Bool.false 5 2 0 1 Bool.false 73635 1000 0 1 qz449)

noncomputable def ep1130 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 2)) qz249 Bool.true 1951810761 80000 0 1 Bool.true 3190671248583 8000000 0 1 (@ep1105 7807243044000 1951810761 80000 0 1 (ep1126 rfl) (ep1129 rfl) rfl rfl)

noncomputable def ep1131 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 2))) qz251) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 2))) qz250) 3193616648583 8000000 0 1 14727 40 0 1

noncomputable def ep1132 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 2))) qz251 216854529 40000 0 1 73635 1000 0 1 3193616648583 8000000

noncomputable def ep1133 := @ep1132 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 216854529 40000 0 1 Bool.false 14727 100 0 1 qz255)

noncomputable def ep1134 := ep1133 (@Enclosure.Complex.IsNear.im_isNear qz249 Bool.false 5 2 0 1 Bool.false 73635 1000 0 1 qz449)

noncomputable def ep1135 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 2))) qz250 14727 100 0 1 5 2 0 1 14727 40

noncomputable def ep1136 := @ep1135 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 216854529 40000 0 1 Bool.false 14727 100 0 1 qz255)

noncomputable def ep1137 := ep1136 (@Enclosure.Complex.IsNear.re_isNear qz249 Bool.false 5 2 0 1 Bool.false 73635 1000 0 1 qz449)

noncomputable abbrev qz256 := (ep1104 (BSN.ascPochhammer_succ_eval_c 2 3 qz381 rfl) (ep1130 (@ep1131 127626849943320 3190671248583 8000000 0 1 (ep1134 rfl) (ep1137 rfl) rfl rfl)))

noncomputable def ep1138 := @ep1103 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep940) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 1951810761 80000 0 1 Bool.true 3190671248583 8000000 0 1 qz256)

noncomputable def ep1139 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 3190671248583 8000000 0 1 0 1 0

noncomputable def ep1140 := @ep1139 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep940) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 1951810761 80000 0 1 Bool.true 3190671248583 8000000 0 1 qz256)

noncomputable def ep1141 := @Enclosure.Real.IsNear.addLit_ft_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3)))) 1063557082861 1920000000 0 1 0 1 0 1 1063557082861

noncomputable def ep1142 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 3190671248583 8000000 0 1 1063557082861 1920000000 0

noncomputable def ep1143 := @ep1142 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep940) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 1951810761 80000 0 1 Bool.true 3190671248583 8000000 0 1 qz256)

noncomputable def ep1144 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 1951810761 80000 0 1 0 1 0

noncomputable def ep1145 := @ep1144 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep940) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 1951810761 80000 0 1 Bool.true 3190671248583 8000000 0 1 qz256)

noncomputable def ep1146 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.false 650603587 19200000 0 1 Bool.false 1063557082861 1920000000 0 1 (@ep1102 650603587 19200000 0 1 (ep1138 rfl) (ep1140 rfl) rfl rfl) (@ep1141 1063557082861 1920000000 0 1 (ep1143 rfl) (ep1145 rfl) rfl rfl)

noncomputable def ep1147 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 650603587 19200000 0 1 Bool.false 1063557082861 1920000000 0 1 ep1146

noncomputable def ep1148 := @Enclosure.Complex.IsNear.re_isNear qz239 Bool.true 945627130701309 147573952589676412928 613003496630228251 ep985 Bool.false 22500450219279469 295147905179352825856 11517976259951703377 ep936

noncomputable def ep1149 := @Enclosure.Complex.IsNear.of_eq qz239 (Complex.mk (@HMul.hMul Real Real Real qz0 qz236 qz208) (@HMul.hMul Real Real Real qz0 qz236 qz209)) Bool.true 945627130701309 147573952589676412928 613003496630228251 ep985 Bool.false 22500450219279469 295147905179352825856 11517976259951703377

noncomputable def ep1150 := @Enclosure.Real.IsNear.mulLit_ff qz151 qz131 73635 1000 0 1 12195973876373221 4503599627370496 160001890297 630099000000000000000 179610107277348425667 900719925474099200 785449279467973 42006600000000000000000 qz153 (BSN.isNear_log_sfrac 15 1 12195973876373221 4503599627370496 160001890297 630099000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz130) Bool.false ep989 ep990 1000011814356250 ep991 12195973876373221 4503599627370496 160001890297 630099000000000000000 (BSN.log_rat_reduce_isNear 15 1 3 30 16 5399707268 8589934592 24973259072661432 36028797018963968 3938118750 1000000000000000 rfl rfl rfl rfl (ep994 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1151 := nat_lit 3681483585311335837559947264

noncomputable def ep1152 := nat_lit 2475880078570760549798248448

noncomputable def ep1153 := nat_lit 352175247357984868437230583132708825414668600929328262528263303695283126446784690147021186482577158882869909606202209318553726480216466487110451662270419394825027584000000

noncomputable def ep1154 := nat_lit 420452379382509455139436900009052269198240561339772954001192682965491022531274017291473283164725218285470097097518760112199699258250697209358555074072576000000000000

noncomputable def ep1155 := nat_lit 2132395144539413154929912347882995538434348221302897930875926936023507924047501168641440345020182139085679996886975787868073742308156723765499203368534110113151949209600000

noncomputable def ep1156 := BSN.cos_dyadic_bound_f 52317028367260 35184372088832 4 3 17179869184 7883929139 ep1153 ep999 ep1154 ep1155 ep1002 ep1154 1438963554 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 52317028367260) (BSN.cosEvenQ 35184372088832) 0 3 ep1153 ep999 ep1154 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 52317028367260) (BSN.cosOddQ 35184372088832) 0 3 ep1155 ep1002 ep1154 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz450 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 3425790925547) (@Nat.cast Real Real.instNatCast 17179869184))

noncomputable def ep1157 := @Enclosure.Real.IsNear.cos_image qz210 qz450 Bool.false 3425790925547 17179869184 161 8589934592 Bool.true 1438963554 17179869184 1 3938118750 (@Enclosure.Real.IsNear.recentre' qz210 Bool.false 179610107277348425667 900719925474099200 785449279467973 42006600000000000000000 3425790925547 17179869184 161 8589934592 (ep1150 rfl) rfl) (Enclosure.sfrac_false_div 3425790925547 17179869184) (BSN.cos_reduce2 qz450 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast ep1151) (@Nat.cast Real Real.instNatCast ep1152)) 226375608064910080 72057594037927936 Bool.false 1438963554 17179869184 31 1000000000000000 7876237500 3938118750 (BSN.sin_reduce_arg_pos_rat_q2 3425790925547 17179869184 226375608064910080 72057594037927936 31 ep1151 ep1152 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1438963554 17179869184 ep1151 ep1152 52317028367260 35184372088832 7883929139 7876237500 (ep1156 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1158 := nat_lit 914474239224009024338419726386437801151704591921969794095071473313267378859296012973693920542356714241029229650020201178385138892849638393151160500816669363451618918400000

noncomputable def ep1159 := nat_lit 22411863820821928299396788597249255122883414756292876443347498757095858352850426348339495190732159462721908983095900632933469148367597566755911644326690509857065670593740800

noncomputable def ep1160 := nat_lit 4567807598376423371900806112090814601929525278861341279040660874394470467108744886751430103810345412304405793697632347785691541707427490411206024068551427050017390592000000

noncomputable def ep1161 := nat_lit 784415233728767490478887600903723929300919516470250675517162456498355042349764922191882331675625581195266814408356522152671420192865914836456907551434167844997298470780928000

noncomputable def ep1162 := BSN.sin_dyadic_bound_f 52317028367260 35184372088832 4 3 17179869184 7883929139 ep1158 ep1159 ep1154 ep1160 ep1161 ep1154 17119500257 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 52317028367260) (BSN.sinEvenQ 35184372088832) 0 3 ep1158 ep1159 ep1154 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 52317028367260) (BSN.sinOddQ 35184372088832) 0 3 ep1160 ep1161 ep1154 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1163 := @Enclosure.Real.IsNear.sin_image qz210 qz450 Bool.false 3425790925547 17179869184 161 8589934592 Bool.true 17119500257 17179869184 1 3938118750 (@Enclosure.Real.IsNear.recentre' qz210 Bool.false 179610107277348425667 900719925474099200 785449279467973 42006600000000000000000 3425790925547 17179869184 161 8589934592 (ep1150 rfl) rfl) (Enclosure.sfrac_false_div 3425790925547 17179869184) (BSN.sin_reduce2 qz450 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast ep1151) (@Nat.cast Real Real.instNatCast ep1152)) 226375608064910080 72057594037927936 Bool.false 17119500257 17179869184 31 1000000000000000 7876237500 3938118750 (BSN.sin_reduce_arg_pos_rat_q2 3425790925547 17179869184 226375608064910080 72057594037927936 31 ep1151 ep1152 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 17119500257 17179869184 ep1151 ep1152 52317028367260 35184372088832 7883929139 7876237500 (ep1162 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1164 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz236 qz208) (@HMul.hMul Real Real Real qz0 qz236 qz209) Bool.true 945627130701309 147573952589676412928 613003496630228251 ep985 Bool.false 22500450219279469 295147905179352825856 11517976259951703377 ep936 (@Enclosure.Real.IsNear.mulLit_ft qz236 qz208 1314317 17179869184 1 17179869184 719481777 8589934592 321313526671 16914091239014400000 945627130701309 147573952589676412928 613003496630228251 ep985 qz439 (@Enclosure.Real.IsNear.recentre' qz208 Bool.true 1438963554 17179869184 642627053342 33828182478028800000 719481777 8589934592 321313526671 16914091239014400000 (ep1157 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz236 qz209 1314317 17179869184 1 17179869184 17119500257 17179869184 321313526671 16914091239014400000 22500450219279469 295147905179352825856 11517976259951703377 ep936 qz439 (@Enclosure.Real.IsNear.neg qz211 Bool.true 17119500257 17179869184 321313526671 16914091239014400000 (@Enclosure.Real.IsNear.recentre' qz211 Bool.true 17119500257 17179869184 642627053342 33828182478028800000 17119500257 17179869184 321313526671 16914091239014400000 (ep1163 rfl rfl) rfl)) rfl)

noncomputable def ep1165 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3)))) qz248 1063557082861 1920000000 0 1 22500450219279469 295147905179352825856 11517976259951703377 ep936 ep1097

noncomputable def ep1166 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 650603587 19200000 0 1 Bool.false 1063557082861 1920000000 0 1 ep1146

noncomputable def ep1167 := @Enclosure.Complex.IsNear.im_isNear qz239 Bool.true 945627130701309 147573952589676412928 613003496630228251 ep985 Bool.false 22500450219279469 295147905179352825856 11517976259951703377 ep936

noncomputable def ep1168 := nat_lit 14638873621778159086855303

noncomputable def ep1169 := nat_lit 5666839779443574256435200000

noncomputable def ep1170 := nat_lit 7493636669705422663836213299

noncomputable def ep1171 := nat_lit 3719447998112100724380794880000000000

noncomputable def ep1172 := nat_lit 335242810867633924384721683

noncomputable def ep1173 := nat_lit 94447329657392904273920000000

noncomputable def ep1174 := nat_lit 651964210659638402226150106111

noncomputable def ep1175 := @Enclosure.Real.IsNear.addLit_ft_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3)))) qz248) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3)))) qz247) ep1168 ep1169 ep1170 ep1171 ep1172 ep1173 ep1174

noncomputable def ep1176 := nat_lit 517164773628191505058891750652179315154707126681600000

noncomputable def ep1177 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3)))) qz248 650603587 19200000 0 1 22500450219279469 295147905179352825856 11517976259951703377 ep936 ep1168

noncomputable def ep1178 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3)))) qz247 1063557082861 1920000000 0 1 945627130701309 147573952589676412928 613003496630228251 ep985 ep1172

noncomputable abbrev qz451 := (@ep1149 ep936 (BSN.cpow_neg_s_sub_mk qz151 73635 1000 15 3 170859375 qz152 rfl EMRow18.d15) ep1164)

noncomputable def ep1179 := ep1093 (@ep1099 ep1086 ep1100 ep1083 ep1084 ep1085 ep1086 (@ep1101 ep1094 ep1095 ep1096 ep1147 (ep1148 qz451) rfl) (@ep1165 ep1084 ep1098 ep1086 ep1166 (ep1167 qz451) rfl) rfl rfl) (@ep1175 ep1092 ep1176 ep1088 ep1089 ep1090 ep1092 (@ep1177 ep1169 ep1170 ep1171 ep1147 (ep1167 qz451) rfl) (@ep1178 ep1173 ep1174 ep1092 ep1166 (ep1148 qz451) rfl) rfl rfl)

noncomputable def ep1180 := @Enclosure.Real.IsNear.mulLit_tt (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) qz239)) (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) qz239)) ep1088 ep1089 ep1090 ep1092 ep1088 ep1089 ep1090

noncomputable def ep1181 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) qz239) Bool.true ep1083 ep1084 ep1085 ep1086 Bool.true ep1088 ep1089 ep1090

noncomputable def ep1182 := @ep1054 28191294219524865 31525197391593472 22875591387 31525197391593472 (@ep1055 1 1835008 (ep1056 (@ep1057 524288 1 524288 (ep1058 (@ep1059 869498116 217374529 40000 0 1 (ep1063 rfl) (ep1066 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) (Enclosure.Real.IsNear.const Bool.false 2 7) rfl) (@ep1067 573 17179869184 (BSN.norm_eq_sqrt_mul_add (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) qz239)) (@ep1068 573 17179869184 729408405 17179869184 573 17179869184 (@ep1073 364703916 364704489 8589934592 (@ep1078 ep1079 ep1080 ep1081 ep1082 ep1069 ep1070 ep1071 ep1072 (@ep1087 ep1086 ep1074 ep1075 ep1076 ep1072 (@ep1091 ep1092 ep1179) (@ep1091 ep1092 ep1179) rfl) (@ep1180 ep1092 ep1077 ep1079 ep1080 ep1081 (@ep1181 ep1092 ep1179) (@ep1181 ep1092 ep1179) rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl

theorem EMRow18.d17 : Enclosure.Real.IsNear (@HAdd.hAdd Real Real Real qz339 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz142 1 15))) (@HMul.hMul Real Real Real qz0 qz238 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) qz239)))) Bool.false 269513904551588617 283726776524341248 70429562453273 851180329573023744 := ep1052 (ep1053 ep1182) rfl rfl

noncomputable def EMRow18.d18 := fun (I J : @NonemptyInterval Real Real.instLE) => @LE.le Real Real.instLE (@Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE I)) (@Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE J))

noncomputable abbrev qz452 := (EMRow18.d3 qz461 qz473 (@Enclosure.dec_le_dec qz461 qz473 71064 1000 73635 1000 (@Eq.refl Real qz461) (@Eq.refl Real qz473) rfl rfl rfl) 15 15 1 1)

noncomputable abbrev qz257 := qz452

noncomputable def ep1183 := @Zeta.Certificates.ZIntervalEM.Certificate.mk qz257 (@Enclosure.dec_nonneg qz17 71064 1000 qz18) (@Enclosure.pos_of_ble 1 rfl) (@Enclosure.pos_of_ble 15 rfl)

noncomputable abbrev qz258 := (Zeta.Certificates.ZIntervalEM.fstVal qz452)

noncomputable def ep1184 := @Enclosure.Real.IsNear.pos_val qz258 ep150 ep151

noncomputable def ep1185 := @Enclosure.Real.IsNear.of_eq qz258 (hardyZApproximantEM 1 15 qz17) Bool.false

noncomputable abbrev qz259 := (Zeta.Certificates.ZIntervalEM.sndVal qz452)

noncomputable def ep1186 := BSN.mul_neg_of_pos_neg_r qz258 qz259 (@ep1184 ep152 ep153 (@ep1185 ep150 ep151 ep152 ep153 (@Eq.refl Real (hardyZApproximantEM 1 15 qz17)) EMRow18.d9) rfl rfl rfl)

noncomputable def ep1187 := @Enclosure.Real.IsNear.neg_val qz259 ep558 ep559

noncomputable def ep1188 := @Enclosure.Real.IsNear.of_eq qz259 (hardyZApproximantEM 1 15 qz151) Bool.true

noncomputable def ep1189 := BSN.gt_trans_le (@Norm.norm Real Real.norm qz258) (BSN.hardyZErrorBoundStrong 1 15 qz17)

noncomputable def ep1190 := @Enclosure.norm_gt_of_isNear qz258 (BSN.hardyZErrorBoundStrong 1 15 qz17) Bool.false

noncomputable def ep1191 := @Enclosure.Real.IsNear.of_eq (BSN.hardyZErrorBoundStrong 1 15 qz17) (@HAdd.hAdd Real Real Real qz339 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz6 1 15))) (@HMul.hMul Real Real Real qz0 qz213 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz216)))) Bool.false 228746010238670467 283726776524341248 7488277166095 94575592174780416 (@Eq.refl Real (@HAdd.hAdd Real Real Real qz339 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz6 1 15))) (@HMul.hMul Real Real Real qz0 qz213 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz216)))))

noncomputable def ep1192 := BSN.gt_trans_le (@Norm.norm Real Real.norm qz259) (BSN.hardyZErrorBoundStrong 1 15 qz151)

noncomputable def ep1193 := @Enclosure.norm_gt_of_isNear qz259 (BSN.hardyZErrorBoundStrong 1 15 qz151) Bool.true

noncomputable def ep1194 := @Enclosure.Real.IsNear.of_eq (BSN.hardyZErrorBoundStrong 1 15 qz151) (@HAdd.hAdd Real Real Real qz339 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz142 1 15))) (@HMul.hMul Real Real Real qz0 qz238 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) qz239)))) Bool.false 269513904551588617 283726776524341248 70429562453273 851180329573023744 (@Eq.refl Real (@HAdd.hAdd Real Real Real qz339 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz142 1 15))) (@HMul.hMul Real Real Real qz0 qz238 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) qz239)))))

noncomputable def ep1195 := @List.cons EMRow18.d0 (@PSigma.mk Zeta.Certificates.ZIntervalEM Zeta.Certificates.ZIntervalEM.Certificate qz257 (ep1183 (@Enclosure.pos_of_ble 1 rfl) (@Enclosure.pos_of_ble 15 rfl) (ep1186 (@ep1187 ep560 ep561 (@ep1188 ep558 ep559 ep560 ep561 (@Eq.refl Real (hardyZApproximantEM 1 15 qz151)) EMRow18.d11) rfl rfl rfl)) (ep1189 (hardyZErrorBoundEM 1 15 qz17) (BSN.hardyZErrorBoundEM_le_strong 1 15 qz17 rfl) (@ep1190 Bool.false ep150 ep151 ep152 ep153 228746010238670467 283726776524341248 7488277166095 94575592174780416 (@ep1185 ep150 ep151 ep152 ep153 (@Eq.refl Real (hardyZApproximantEM 1 15 qz17)) EMRow18.d9) (ep1191 EMRow18.d16) rfl rfl rfl rfl rfl)) (ep1192 (hardyZErrorBoundEM 1 15 qz151) (BSN.hardyZErrorBoundEM_le_strong 1 15 qz151 rfl) (@ep1193 Bool.false ep558 ep559 ep560 ep561 269513904551588617 283726776524341248 70429562453273 851180329573023744 (@ep1188 ep558 ep559 ep560 ep561 (@Eq.refl Real (hardyZApproximantEM 1 15 qz151)) EMRow18.d11) (ep1194 EMRow18.d17) rfl rfl rfl rfl rfl)))) (@List.nil EMRow18.d0)

noncomputable abbrev qz453 := (@Enclosure.dec_le_dec qz461 qz473 71064 1000 73635 1000 (@Eq.refl Real qz461) (@Eq.refl Real qz473) rfl rfl rfl)

noncomputable abbrev qz260 := (Zeta.Certificates.CertifiedZeroIntervals.intervals (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedEM ep1195 (@List.IsChain.singleton EMRow18.d1 EMRow18.d18 (EMRow18.d2 qz275 qz383 qz453))))

noncomputable abbrev qz454 := (@NonemptyInterval Real Real.instLE)

noncomputable def ep1196 := And (@Eq (Option Real) (@Option.map qz454 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz454 qz260)) (@Option.some Real qz17))

noncomputable def ep1197 := ep1196 (@Eq (Option Real) (@Option.map qz454 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz454 qz260)) (@Option.some Real qz151))

noncomputable def ep1198 := @And.intro (@Eq Nat (@List.length qz454 qz260) 1) ep1197

noncomputable def ep1199 := @And.intro (@Eq (Option Real) (@Option.map qz454 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz454 qz260)) (@Option.some Real qz17))

noncomputable def ep1200 := @ep1199 (@Eq (Option Real) (@Option.map qz454 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz454 qz260)) (@Option.some Real qz151))

noncomputable abbrev qz261 := (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedEM ep1195 (@List.IsChain.singleton EMRow18.d1 EMRow18.d18 (EMRow18.d2 qz275 qz383 qz453)))

theorem EMRow18.d19 : Zeta.Certificates.BatchSpec 1 71064 1000 73635 1000 := @Exists.intro Zeta.Certificates.CertifiedZeroIntervals (fun (C : Zeta.Certificates.CertifiedZeroIntervals) => And (@Eq Nat (@List.length qz454 (Zeta.Certificates.CertifiedZeroIntervals.intervals C)) 1) (And (@Eq (Option Real) (@Option.map qz454 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz454 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz17)) (@Eq (Option Real) (@Option.map qz454 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz454 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz151)))) qz261 (ep1198 (@Eq.refl Nat 1) (ep1200 (@Eq.refl (Option Real) (@Option.some Real qz17)) (@Eq.refl (Option Real) (@Option.some Real qz151))))

theorem solution : Zeta.Certificates.BatchSpec 1 71064 1000 73635 1000 := EMRow18.d19
#print axioms solution
#check solution
