-- Prove2me | solution 1 for RHHeight1000.em_main_0021_0021
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-20T08:19:20.448174+00:00
-- url     : https://prove2.me/submissions/9d4c3bbb-a7b5-4a4a-997b-8f1a544580b6

import Definitions.Def_RHT1000_Support_20261118_S005
/- Copyright (c) 2026 Salvatore Mercuri, Bhavik Mehta.
Apache 2.0 license; see the source project LICENSE. -/
set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable def EMRow21.d0 := @PSigma Zeta.Certificates.ZIntervalEM fun (I : Zeta.Certificates.ZIntervalEM) => Zeta.Certificates.ZIntervalEM.Certificate I

noncomputable def EMRow21.d1 := @NonemptyInterval Real Real.instLE

noncomputable def EMRow21.d2 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @NonemptyInterval.mk Real Real.instLE (@Prod.mk Real Real a b) h

noncomputable def EMRow21.d3 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) (fc sc fb sb : Nat) => Zeta.Certificates.ZIntervalEM.mk (EMRow21.d2 a b h) fc sc fb sb

noncomputable def ep0 := nat_lit 26986075409044028275299783

noncomputable def ep1 := nat_lit 4294967296000000000000000

noncomputable def ep2 := nat_lit 26986075409044045455168967

noncomputable abbrev qz266 := (@instHMul Real Real.instMul)

noncomputable abbrev qz0 := qz266

noncomputable abbrev qz1 := (Enclosure.sfrac Bool.false 2 1)

noncomputable abbrev qz267 := (@HMul.hMul Real Real Real qz0 qz1 Real.pi)

noncomputable def ep3 := @BSN.isNear_log_image_fff qz267 884279719003555 140737488355328 1 500000000000000 ep0 ep1 ep2 ep1 4138529546116343 2251799813685248 125000000040469 20234500000000000000 4138529546116343 2251799813685248 125000000040469 20234500000000000000 481788 262144

noncomputable abbrev qz268 := (@Enclosure.Real.IsNear.mulLit_ff qz1 Real.pi 2 1 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 140737488355328 1 500000000000000 (Enclosure.Real.IsNear.const Bool.false 2 1) BSN.pi_near_15 rfl)

noncomputable def ep4 := @ep3 2 262144 qz268 rfl rfl rfl rfl

noncomputable def ep5 := nat_lit 53972150818088056550599566

noncomputable def ep6 := nat_lit 34359738368000000000000000

noncomputable def ep7 := nat_lit 9806206225044028275299783

noncomputable def ep8 := nat_lit 44165944593044028275299783

noncomputable def ep9 := nat_lit 13681445815609410487519367394620474863599256634174726093703677122907123617368241606644861540940610176751640793056574796245399519365549113997355475306157239709119582688278313060810592403844863400465080549957745

noncomputable def ep10 := nat_lit 231714499556395493334623298703961145503103241611736774613091488581016477543539392410113701224645713379230392133956226737605624599560350113120270717249177907454870984269546186598262646369758174842349131395304

noncomputable def ep11 := nat_lit 8978369550011295664474073352761810093897501552430546263638635096022803738134167562509900960712119243631997923545019968443113540909076206607473711060286601587364321108377403290080403445693385008949995305

noncomputable def ep12 := BSN.log_dyadic_bound ep7 ep8 5 4 ep9 524288 161876 ep10 ep11 236759 ep5 ep6 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP ep7) (BSN.artanhQ ep8) 0 4 ep10 ep9 ep11 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz269 := (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))

noncomputable abbrev qz2 := qz269

noncomputable def ep13 := ep4 rfl rfl rfl rfl (BSN.isNear_log_sfrac ep0 ep1 4138529546116343 2251799813685248 125000000040469 20234500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast ep0) (@Nat.cast Real Real.instNatCast ep1))) Bool.false 34716502058787923820544 18889465931478580854784 1000000000323752 161876000000000000000 4138529546116343 2251799813685248 125000000040469 20234500000000000000 (BSN.log_rat_reduce_isNear ep0 ep1 2 ep5 ep6 236759 524288 24973259072661432 36028797018963968 161876 1000000000000000 rfl rfl rfl rfl (ep12 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep14 := nat_lit 53972150818088090910337934

noncomputable def ep15 := nat_lit 9806206225044045455168967

noncomputable def ep16 := nat_lit 44165944593044045455168967

noncomputable def ep17 := nat_lit 13681445815609453062485491347592146866046743284321690683909457683007658987562290830600045658905080811372395010565947827677605470036294121079488508864180301737865471494204890974265645509835068840465080549957745

noncomputable def ep18 := nat_lit 231714499556396865510889920206523150079811393376960301632499817942333196803513131357563499488546302200815366867712007119763002650772307103678175657719139104636874731038771518520299266622696414842349131395304

noncomputable def ep19 := nat_lit 8978369550011421500876706511871067098718760264493934208903156435737864998391937547068187824077011975074541700434630537294838404525415248443919841847024664017658842168336182958576672102333385008949995305

noncomputable def ep20 := BSN.log_dyadic_bound ep15 ep16 5 4 ep17 524288 161876 ep18 ep19 236759 ep14 ep6 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP ep15) (BSN.artanhQ ep16) 0 4 ep18 ep17 ep19 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep21 := ep13 (BSN.isNear_log_sfrac ep2 ep1 4138529546116343 2251799813685248 125000000040469 20234500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast ep2) (@Nat.cast Real Real.instNatCast ep1))) Bool.false 34716502058787923820544 18889465931478580854784 1000000000323752 161876000000000000000 4138529546116343 2251799813685248 125000000040469 20234500000000000000 (BSN.log_rat_reduce_isNear ep2 ep1 2 ep14 ep6 236759 524288 24973259072661432 36028797018963968 161876 1000000000000000 rfl rfl rfl rfl (ep20 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable abbrev qz270 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)

noncomputable abbrev qz3 := (Real.log qz270)

theorem EMRow21.d4 : Enclosure.Real.IsNear qz3 Bool.false 120447 65536 1 131072 := @Enclosure.Real.IsNear.of_eq qz3 (Real.log qz267) Bool.false 120447 65536 1 131072 BSN.log_two_pi_eq (@Enclosure.Real.IsNear.recentre' (Real.log qz267) Bool.false 481788 262144 2 262144 120447 65536 1 131072 (ep21 rfl rfl rfl rfl rfl rfl rfl rfl) rfl)

noncomputable def ep22 := nat_lit 8589934592000000000000000

noncomputable def ep23 := @BSN.isNear_log_image_fff Real.pi 226375608064910080 72057594037927936 1 1000000000000000 ep0 ep22 ep2 ep22 600168 524288 1 161876 600168 524288 1 161876 300084 262144 2 262144 BSN.pi_near_15 rfl rfl rfl

noncomputable def ep24 := nat_lit 17179869184000000000000000

noncomputable def ep25 := nat_lit 18396140817044028275299783

noncomputable def ep26 := nat_lit 35576010001044028275299783

noncomputable def ep27 := nat_lit 145019262663961446558303139663424756232419223153299357158415217874016130572233056993847515999529612750616182853355499335896178729185698845314776375864537073527142908641610750276034469165612529925303649396973267518946591078603565291376312767403717761600170009932259137778521478520425507632472584532570900560707662248426541531715360699177249902784721815296292248142738824858695953661559845440650653128788875447728828657762006237171740033404723254477174341920697506370253193455781322964835857351124092897592956162654178130575

noncomputable def ep28 := nat_lit 15500762873619990602332184736899274490522931101512051618692838888825382235673431503644115344741331161500627469184702974962114537943617674254904297224139410345221262767191485292268260077615645253784097850065864022184521411511133693085443040736512010941548648374196772723338837137976260321103066698629790037694560548409922339907589559883712609967105556007429010014773911317423638534096849366294542840133852248768895750397896505791271178551667935288585787166713880920071720072716082683081155281219708172458141800988558163320

noncomputable def ep29 := nat_lit 12900190794487083783367107939442176642390171280542213571554777169279725287102813254708993369099729304728646904879886535518616983985412662170766446331701281703998252143668221340329975389245922410714088123244705567402747658401492589451585970559635763980329972215329212888079422466283203384882259392047898400615815810081169907384366653346471604103896809335921621947903075223769953790093549808584241881353287841076643853121427928248525828402335494512605306631304432120211393210317325496757155861061354331245840675149075

noncomputable def ep30 := BSN.log_dyadic_bound ep25 ep26 11 10 ep27 524288 161876 ep28 ep29 600168 ep5 ep24 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base10 (BSN.artanhP ep25) (BSN.artanhQ ep26) 0 10 ep28 ep27 ep29 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep31 := nat_lit 18396140817044045455168967

noncomputable def ep32 := nat_lit 35576010001044045455168967

noncomputable def ep33 := nat_lit 145019262663962847171784895425483977818796535899227200426399035286881207006285364467913811844950531107314785650583974625982406238691319033447632878979985852280879486690814033867010958364699188952871572448188560932645032521756218245629809291975913196623825614492380080480004685076434733043183791438169545293975334857826316990371107134320667652578346815517853870648072772035977941843998949310557583393428557296298890786965786350523173236912472938174255438182435383147950274229549088258679583524155427309880956162654178130575

noncomputable def ep34 := nat_lit 15500762873620157189619721156942591192100275120160672416764593300158228469749443299607348495591439275767946573253526107895503597951484257520435868240203420954375895980141891044871083424251900562230440202302413072793440172565998181227591194192658878334739610458454844032013325963992941389843551995646587189684848765634635122388286241104146031552341815777883628509454807838726994150833304950745987647656768534710890974432620160470644835720379148964170536679305861738540146791997074363921127776563807649880221800988558163320

noncomputable def ep35 := nat_lit 12900190794487324729109480814509220959173684627296055849229843377126536688487849343376525559792931631054411655715865486295286288812423905434305314401904993536755333953308594664509631000767632482919425633906965368325056855874260596615770736441041599390097968820060635361729170158825410327022636428624381203910573184452046894301676992229743752846881064485858738985580654099214803581683226335297196686880535448467637789069028262446657986458573827723305156755787640135484017403116612632808333639900906331245840675149075

noncomputable def ep36 := BSN.log_dyadic_bound ep31 ep32 11 10 ep33 524288 161876 ep34 ep35 600168 ep14 ep24 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base10 (BSN.artanhP ep31) (BSN.artanhQ ep32) 0 10 ep34 ep33 ep35 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep37 := @Enclosure.Real.IsNear.recentre' (Real.log Real.pi) Bool.false 300084 262144 2 262144 75021 65536 1 131072 (ep23 rfl rfl rfl rfl rfl (BSN.isNear_log_sfrac ep0 ep22 600168 524288 1 161876 Bool.false (BSN.logfrac_isNear ep5 ep24 1 ep0 ep22 600168 524288 161876 rfl rfl rfl (ep30 rfl))) (BSN.isNear_log_sfrac ep2 ep22 600168 524288 1 161876 Bool.false (BSN.logfrac_isNear ep14 ep24 1 ep2 ep22 600168 524288 161876 rfl rfl rfl (ep36 rfl))) rfl rfl rfl rfl rfl rfl rfl rfl) rfl

theorem EMRow21.d5 : Enclosure.Real.IsNear (Real.log Real.pi) Bool.false 75021 65536 1 131072 := ep37

noncomputable abbrev qz501 := (@HAdd.hAdd Complex Complex Complex (@instHAdd Complex Complex.instAdd) (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (2 : Complex)) (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul) Complex.I ↑(Enclosure.sfrac Bool.false 78672 1000)))

noncomputable abbrev qz478 := qz501

noncomputable abbrev qz271 := qz478

noncomputable abbrev qz4 := (BSN.headSumC qz271 9)

noncomputable abbrev qz502 := (@instHAdd Complex Complex.instAdd)

noncomputable abbrev qz479 := qz502

noncomputable abbrev qz272 := qz479

noncomputable abbrev qz5 := qz272

noncomputable abbrev qz6 := qz271

noncomputable abbrev qz480 := (@instHPow Complex Complex Complex.instPow)

noncomputable abbrev qz273 := qz480

noncomputable abbrev qz481 := (@Neg.neg Complex Complex.instNeg qz501)

noncomputable abbrev qz274 := qz481

noncomputable abbrev qz7 := (@HPow.hPow Complex Complex Complex qz273 (@Nat.cast Complex Complex.instNatCast 8) qz274)

noncomputable def ep38 := @Enclosure.Complex.IsNear.of_eq qz4 (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz6 8) qz7) Bool.false 104720946353 274877906944 3371220040371 1011275819646976 Bool.true 18526874065 274877906944 3375240495719 1011275819646976

noncomputable def ep39 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz6 8) qz7 Bool.false 5059450155 137438953472 8297102942299 2781008504029184 Bool.false 930978773 68719476736 16624216359521 5562017008058368 Bool.false

noncomputable abbrev qz8 := (@HPow.hPow Complex Complex Complex qz273 (@Nat.cast Complex Complex.instNatCast 7) qz274)

noncomputable def ep40 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz6 8) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz6 7) qz8) Bool.false 5059450155 137438953472 8297102942299 2781008504029184 Bool.false 930978773 68719476736 16624216359521 5562017008058368

noncomputable def ep41 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz6 7) qz8 Bool.false 78712824597 274877906944 2232653231971 855694924316672 Bool.false 40877676127 137438953472 69910061609 26740466384896 Bool.true

noncomputable abbrev qz9 := (@HPow.hPow Complex Complex Complex qz273 (@Nat.cast Complex Complex.instNatCast 6) qz274)

noncomputable def ep42 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz6 7) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz6 6) qz9) Bool.false 78712824597 274877906944 2232653231971 855694924316672 Bool.false 40877676127 137438953472 69910061609 26740466384896

noncomputable def ep43 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz6 6) qz9 Bool.false 181610361535 274877906944 24522653353505 11124034016116736 Bool.false 126532097015 274877906944 24591736040893 11124034016116736 Bool.true

noncomputable abbrev qz10 := (@HPow.hPow Complex Complex Complex qz273 (@Nat.cast Complex Complex.instNatCast 5) qz274)

noncomputable def ep44 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz6 6) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz6 5) qz10) Bool.false 181610361535 274877906944 24522653353505 11124034016116736 Bool.false 126532097015 274877906944 24591736040893 11124034016116736

noncomputable def ep45 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz6 5) qz10 Bool.false 27622395793 68719476736 4900038365933 2781008504029184 Bool.false 56699694723 68719476736 9832102805803 5562017008058368 Bool.false

noncomputable abbrev qz11 := (@HPow.hPow Complex Complex Complex qz273 (@Nat.cast Complex Complex.instNatCast 4) qz274)

noncomputable def ep46 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz6 5) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz6 4) qz11) Bool.false 27622395793 68719476736 4900038365933 2781008504029184 Bool.false 56699694723 68719476736 9832102805803 5562017008058368

noncomputable def ep47 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz6 4) qz11 Bool.false 98314624343 137438953472 7053848065587 5562017008058368 Bool.false 166946553627 137438953472 1771064168633 1390504252014592 Bool.true

noncomputable abbrev qz482 := (@Nat.cast Complex Complex.instNatCast 3)

noncomputable abbrev qz275 := qz482

noncomputable abbrev qz12 := (@HPow.hPow Complex Complex Complex qz273 qz275 qz274)

noncomputable def ep48 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz6 4) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz6 3) qz12) Bool.false 98314624343 137438953472 7053848065587 5562017008058368 Bool.false 166946553627 137438953472 1771064168633 1390504252014592

noncomputable def ep49 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz6 3) qz12 Bool.false 5965968149 8589934592 6861381063 9826885173248 Bool.false 21911924781 34359738368 13757990033 19653770346496 Bool.false

noncomputable abbrev qz483 := (@Nat.cast Complex Complex.instNatCast 2)

noncomputable abbrev qz276 := qz483

noncomputable abbrev qz13 := (@HPow.hPow Complex Complex Complex qz273 qz276 qz274)

noncomputable def ep50 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz6 3) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz6 2) qz13) Bool.false 5965968149 8589934592 6861381063 9826885173248 Bool.false 21911924781 34359738368 13757990033 19653770346496

noncomputable def ep51 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz6 2) qz13 Bool.false 1 1 0 1 Bool.false 0 1 0 1 Bool.true

noncomputable abbrev qz277 := (Enclosure.sfrac Bool.false 0 1)

noncomputable abbrev qz14 := qz277

noncomputable def ep52 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz6 2) (Complex.mk (Enclosure.sfrac Bool.false 1 1) qz14) Bool.false 1 1 0 1 Bool.false 0 1 0 1 (BSN.head_sum_c_two qz6)

noncomputable abbrev qz278 := (@Nat.cast Real Real.instNatCast 2)

noncomputable abbrev qz15 := (@Inv.inv Real Real.instInv (Real.sqrt qz278))

noncomputable abbrev qz503 := (Enclosure.sfrac Bool.false 78672 1000)

noncomputable abbrev qz484 := qz503

noncomputable abbrev qz279 := qz484

noncomputable abbrev qz16 := (@HMul.hMul Real Real Real qz266 qz279 (Real.log (Enclosure.sfrac Bool.false 2 1)))

noncomputable abbrev qz17 := qz279

noncomputable abbrev qz280 := (@Eq.refl Real qz484)

noncomputable abbrev qz18 := qz280

noncomputable def ep53 := @Enclosure.Complex.IsNear.of_eq qz13 (Complex.mk (@HMul.hMul Real Real Real qz0 qz15 (Real.cos qz16)) (@HMul.hMul Real Real Real qz0 qz15 (@Neg.neg Real Real.instNeg (Real.sin qz16)))) Bool.true 2623966443 8589934592 6861381063 9826885173248 Bool.false 21911924781 34359738368 13757990033 19653770346496 (BSN.cpow_neg_s_mk qz17 78672 1000 2 qz18 rfl)

noncomputable abbrev qz19 := (@Nat.cast Real Real.instNatCast 1)

noncomputable def ep54 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz278) 741455 524288 1 524288 185363 185365 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz278) (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz278 qz19)) Bool.false 741455 524288 1 524288 (BSN.sqrt_natCast_div_one 2) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz278 qz19)) Bool.false 741455 524288 1 524288 741455 524288 1 524288 (BSN.sqrt_enclosure 2 1 370727 370728 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep55 := BSN.log_dyadic_bound 1 3 6 5 613814355 262144 80938 24381081 945 181704 4 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 1) (BSN.artanhQ 3) 0 5 24381081 613814355 945 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep56 := nat_lit 4743738241151225826305256340073738455365987625474498758200694143620104184801

noncomputable def ep57 := nat_lit 71239273651864456168798555229954474558164150722024956391463162036118429368320

noncomputable def ep58 := nat_lit 4504004602580614743898884737188217070343889835905979875236420040430052321

noncomputable def ep59 := nat_lit 14222206714248516249427971250746838931957275096751684314851609590779452449761

noncomputable def ep60 := nat_lit 3205767314333900527595934985347951355117386782491123037615842291625329321574400

noncomputable abbrev qz281 := (BSN.cosEvenQ 1073741824)

noncomputable abbrev qz282 := (BSN.cosOddQ 1073741824)

noncomputable def ep61 := BSN.cos_dyadic_bound_f 1206979387 1073741824 3 2 524288 162035 ep56 ep57 ep58 ep59 ep60 ep58 226492 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1206979387) qz281 0 2 ep56 ep57 ep58 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1206979387) qz282 0 2 ep59 ep60 ep58 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz20 := (@Nat.cast Real Real.instNatCast 262144)

noncomputable abbrev qz21 := (Real.log (Enclosure.sfrac Bool.false 2 1))

noncomputable abbrev qz22 := (Enclosure.Real.IsNear.const Bool.false 78672 1000)

noncomputable abbrev qz23 := (@Nat.cast Real Real.instNatCast 37778931862957161709568)

noncomputable abbrev qz283 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 14295017) qz20)

noncomputable abbrev qz284 := (BSN.isNear_log_sfrac 2 1 181704 262144 1 80938 Bool.false (BSN.logfrac_isNear 4 2 1 2 1 181704 262144 80938 rfl rfl rfl (ep55 rfl)))

noncomputable def ep62 := @Enclosure.Real.IsNear.cos_image qz16 qz283 Bool.false 14295017 262144 255 262144 Bool.true 226492 524288 1 80938 (@Enclosure.Real.IsNear.recentre' qz16 Bool.false 111679821 2048000 447 459875 14295017 262144 255 262144 (@Enclosure.Real.IsNear.mulLit_ff qz17 qz21 78672 1000 0 1 181704 262144 1 80938 111679821 2048000 447 459875 qz22 qz284 rfl) rfl) (Enclosure.sfrac_false_div 14295017 262144) (BSN.cos_reduce2 qz283 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 42466811883252187398144) qz23) 226375608064910080 72057594037927936 Bool.false 226492 524288 8 1000000000000000 161876 80938 (BSN.sin_reduce_arg_pos_rat_q2 14295017 262144 226375608064910080 72057594037927936 8 42466811883252187398144 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 226492 524288 42466811883252187398144 37778931862957161709568 1206979387 1073741824 162035 161876 (ep61 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep63 := nat_lit 8535125630390141995554342304342978646002502613985372980861060322483843490785

noncomputable def ep64 := nat_lit 641153462866780105519186997069590271023477356498224607523168458325065864314880

noncomputable def ep65 := nat_lit 22346608262617622326390298317038067911892664357846414791980965688344608105441

noncomputable def ep66 := nat_lit 11754480152557635267851761612942488302097084869134117804591421735959540845772800

noncomputable abbrev qz285 := (BSN.sinEvenQ 1073741824)

noncomputable abbrev qz286 := (BSN.sinOddQ 1073741824)

noncomputable def ep67 := BSN.sin_dyadic_bound_f 1206979387 1073741824 3 2 524288 162035 ep63 ep64 ep58 ep65 ep66 ep58 472841 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1206979387) qz285 0 2 ep63 ep64 ep58 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1206979387) qz286 0 2 ep65 ep66 ep58 rfl rfl rfl rfl) rfl rfl

noncomputable def ep68 := @Enclosure.Real.IsNear.sin_image qz16 qz283 Bool.false 14295017 262144 255 262144 Bool.true 472841 524288 1 80938 (@Enclosure.Real.IsNear.recentre' qz16 Bool.false 111679821 2048000 447 459875 14295017 262144 255 262144 (@Enclosure.Real.IsNear.mulLit_ff qz17 qz21 78672 1000 0 1 181704 262144 1 80938 111679821 2048000 447 459875 qz22 qz284 rfl) rfl) (Enclosure.sfrac_false_div 14295017 262144) (BSN.sin_reduce2 qz283 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 42466811883252187398144) qz23) 226375608064910080 72057594037927936 Bool.false 472841 524288 8 1000000000000000 161876 80938 (BSN.sin_reduce_arg_pos_rat_q2 14295017 262144 226375608064910080 72057594037927936 8 42466811883252187398144 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 472841 524288 42466811883252187398144 37778931862957161709568 1206979387 1073741824 162035 161876 (ep67 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz287 := (@Enclosure.Real.IsNear.recentre' qz15 Bool.false 370728 524288 2 524288 46341 65536 1 262144 (ep54 rfl rfl) rfl)

noncomputable def ep69 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz15 (Real.cos qz16)) (@HMul.hMul Real Real Real qz0 qz15 (@Neg.neg Real Real.instNeg (Real.sin qz16))) Bool.true 2623966443 8589934592 6861381063 9826885173248 Bool.false 21911924781 34359738368 13757990033 19653770346496 (@Enclosure.Real.IsNear.mulLit_ft qz15 (Real.cos qz16) 46341 65536 1 262144 56623 131072 10450667 10608705536 2623966443 8589934592 6861381063 9826885173248 qz287 (@Enclosure.Real.IsNear.recentre' (Real.cos qz16) Bool.true 226492 524288 20901334 21217411072 56623 131072 10450667 10608705536 (ep62 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz15 (@Neg.neg Real Real.instNeg (Real.sin qz16)) 46341 65536 1 262144 472841 524288 10450667 10608705536 21911924781 34359738368 13757990033 19653770346496 qz287 (@Enclosure.Real.IsNear.neg (Real.sin qz16) Bool.true 472841 524288 10450667 10608705536 (@Enclosure.Real.IsNear.recentre' (Real.sin qz16) Bool.true 472841 524288 20901334 21217411072 472841 524288 10450667 10608705536 (ep68 rfl rfl) rfl)) rfl)

noncomputable abbrev qz288 := (Enclosure.Real.IsNear.const Bool.false 0 1)

noncomputable abbrev qz24 := qz288

noncomputable def ep70 := @ep51 2623966443 8589934592 6861381063 9826885173248 Bool.false 21911924781 34359738368 13757990033 19653770346496 Bool.false 5965968149 5965968149 8589934592 6861381063 9826885173248 Bool.false 21911924781 21911924781 34359738368 13757990033 19653770346496 (ep52 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 1) qz14 Bool.false 1 1 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 1) qz24)) (ep53 ep69) rfl rfl

noncomputable abbrev qz289 := (@Nat.cast Real Real.instNatCast 3)

noncomputable abbrev qz25 := (@Inv.inv Real Real.instInv (Real.sqrt qz289))

noncomputable abbrev qz26 := (@HMul.hMul Real Real Real qz266 qz279 (Real.log (Enclosure.sfrac Bool.false 3 1)))

noncomputable def ep71 := @Enclosure.Complex.IsNear.of_eq qz12 (Complex.mk (@HMul.hMul Real Real Real qz0 qz25 (Real.cos qz26)) (@HMul.hMul Real Real Real qz0 qz25 (@Neg.neg Real Real.instNeg (Real.sin qz26)))) Bool.false 2859133959 137438953472 3170306383929 5562017008058368 Bool.false 79298854503 137438953472 3190745495193 5562017008058368 (BSN.cpow_neg_s_mk qz17 78672 1000 3 qz18 rfl)

noncomputable def ep72 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz289) 908093 524288 1 524288 151348 151350 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz289) (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz289 qz19)) Bool.false 908093 524288 1 524288 (BSN.sqrt_natCast_div_one 3) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz289 qz19)) Bool.false 908093 524288 1 524288 908093 524288 1 524288 (BSN.sqrt_enclosure 3 1 454046 454047 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep73 := BSN.log_dyadic_bound 1 2 10 9 171633298636800 262144 80938 16925142283965 34459425 287994 3 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base9 (BSN.artanhP 1) (BSN.artanhQ 2) 0 9 16925142283965 171633298636800 34459425 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep74 := BSN.sin_dyadic_bound_f 38697877 1073741824 1 0 524288 162035 0 1 1 0 1 1 18891 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 38697877) qz285 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 38697877) qz286 0 0 rfl) rfl rfl

noncomputable abbrev qz27 := (@Nat.cast Real Real.instNatCast 524288)

noncomputable abbrev qz28 := (Real.log (Enclosure.sfrac Bool.false 3 1))

noncomputable abbrev qz29 := (@Nat.cast Real Real.instNatCast 75557863725914323419136)

noncomputable abbrev qz290 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 45314127) qz27)

noncomputable abbrev qz291 := (BSN.isNear_log_sfrac 3 1 287994 262144 1 80938 Bool.false (BSN.logfrac_isNear 3 1 2 3 1 287994 262144 80938 rfl rfl rfl (ep73 rfl)))

noncomputable def ep75 := @Enclosure.Real.IsNear.cos_image qz26 qz290 Bool.false 45314127 524288 511 524288 Bool.false 18891 524288 1 80938 (@Enclosure.Real.IsNear.recentre' qz26 Bool.false 708033249 8192000 447 459875 45314127 524288 511 524288 (@Enclosure.Real.IsNear.mulLit_ff qz17 qz28 78672 1000 0 1 287994 262144 1 80938 708033249 8192000 447 459875 qz22 qz291 rfl) rfl) (Enclosure.sfrac_false_div 45314127 524288) (BSN.cos_reduce3 qz290 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 2723121035761936236544) qz29) 226375608064910080 72057594037927936 Bool.false 18891 524288 13 1000000000000000 161876 80938 (BSN.sin_reduce_arg_pos_rat_q3 45314127 524288 226375608064910080 72057594037927936 13 2723121035761936236544 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 18891 524288 2723121035761936236544 75557863725914323419136 38697877 1073741824 162035 161876 (ep74 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep76 := BSN.cos_dyadic_bound_f 38697877 1073741824 1 0 524288 162035 0 1 1 0 1 1 523947 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 38697877) qz281 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 38697877) qz282 0 0 rfl) rfl rfl

noncomputable def ep77 := @Enclosure.Real.IsNear.sin_image qz26 qz290 Bool.false 45314127 524288 511 524288 Bool.true 523947 524288 1 80938 (@Enclosure.Real.IsNear.recentre' qz26 Bool.false 708033249 8192000 447 459875 45314127 524288 511 524288 (@Enclosure.Real.IsNear.mulLit_ff qz17 qz28 78672 1000 0 1 287994 262144 1 80938 708033249 8192000 447 459875 qz22 qz291 rfl) rfl) (Enclosure.sfrac_false_div 45314127 524288) (BSN.sin_reduce3 qz290 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 2723121035761936236544) qz29) 226375608064910080 72057594037927936 Bool.false 523947 524288 13 1000000000000000 161876 80938 (BSN.sin_reduce_arg_pos_rat_q3 45314127 524288 226375608064910080 72057594037927936 13 2723121035761936236544 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 523947 524288 2723121035761936236544 75557863725914323419136 38697877 1073741824 162035 161876 (ep76 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz292 := (@Enclosure.Real.IsNear.recentre' qz25 Bool.false 302698 524288 2 524288 151349 262144 1 262144 (ep72 rfl rfl) rfl)

noncomputable def ep78 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz25 (Real.cos qz26)) (@HMul.hMul Real Real Real qz0 qz25 (@Neg.neg Real Real.instNeg (Real.sin qz26))) Bool.false 2859133959 137438953472 3170306383929 5562017008058368 Bool.false 79298854503 137438953472 3190745495193 5562017008058368 (@Enclosure.Real.IsNear.mulLit_ff qz25 (Real.cos qz26) 151349 262144 1 262144 18891 524288 20941803 21217411072 2859133959 137438953472 3170306383929 5562017008058368 qz292 (@Enclosure.Real.IsNear.recentre' (Real.cos qz26) Bool.false 18891 524288 41883606 42434822144 18891 524288 20941803 21217411072 (ep75 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz25 (@Neg.neg Real Real.instNeg (Real.sin qz26)) 151349 262144 1 262144 523947 524288 20941803 21217411072 79298854503 137438953472 3190745495193 5562017008058368 qz292 (@Enclosure.Real.IsNear.neg (Real.sin qz26) Bool.true 523947 524288 20941803 21217411072 (@Enclosure.Real.IsNear.recentre' (Real.sin qz26) Bool.true 523947 524288 41883606 42434822144 523947 524288 20941803 21217411072 (ep77 rfl rfl) rfl)) rfl)

noncomputable def ep79 := @ep49 2859133959 137438953472 3170306383929 5562017008058368 Bool.false 79298854503 137438953472 3190745495193 5562017008058368 Bool.false 844516192543420973056 98314624343 137438953472 7053848065587 5562017008058368 Bool.false 5736239904063001460736 166946553627 137438953472 1771064168633 1390504252014592 (ep50 (BSN.head_sum_c_succ qz6 2 3 rfl rfl) (ep70 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep71 ep78) rfl rfl

noncomputable abbrev qz293 := (@Nat.cast Real Real.instNatCast 4)

noncomputable abbrev qz30 := (@Inv.inv Real Real.instInv (Real.sqrt qz293))

noncomputable abbrev qz31 := (@HMul.hMul Real Real Real qz266 qz279 (Real.log (Enclosure.sfrac Bool.false 4 1)))

noncomputable def ep80 := @Enclosure.Complex.IsNear.of_eq qz11 (Complex.mk (@HMul.hMul Real Real Real qz0 qz30 (Real.cos qz31)) (@HMul.hMul Real Real Real qz0 qz30 (@Neg.neg Real Real.instNeg (Real.sin qz31)))) Bool.true 43069832757 137438953472 2746228666279 5562017008058368 Bool.true 53547164181 137438953472 2747846131271 5562017008058368 (BSN.cpow_neg_s_mk qz17 78672 1000 4 qz18 rfl)

noncomputable def ep81 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz293) 1048577 524288 1 524288 131071 131072 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz293) (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz293 qz19)) Bool.false 1048577 524288 1 524288 (BSN.sqrt_natCast_div_one 4) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz293 qz19)) Bool.false 1048577 524288 1 524288 1048577 524288 1 524288 (BSN.sqrt_enclosure 4 1 524288 524289 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep82 := nat_lit 471225594319403171539306640625

noncomputable def ep83 := nat_lit 73155514365408823868279100600

noncomputable def ep84 := BSN.log_dyadic_bound 3 5 13 12 ep82 262144 80938 ep83 89313862490502916491225 363408 8 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base12 (BSN.artanhP 3) (BSN.artanhQ 5) 0 12 ep83 ep82 89313862490502916491225 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep85 := nat_lit 279849003223948833148767937902424336

noncomputable def ep86 := nat_lit 159507359494189904748456847233641349120

noncomputable def ep87 := nat_lit 1116551516459329333239197930635489443840

noncomputable def ep88 := BSN.sin_dyadic_bound_f 727329062 1073741824 2 1 524288 162035 ep85 ep86 ep85 ep85 ep87 ep85 328598 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 727329062) qz285 0 1 ep85 ep86 ep85 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 727329062) qz286 0 1 ep85 ep87 ep85 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz32 := (Real.log (Enclosure.sfrac Bool.false 4 1))

noncomputable abbrev qz485 := (@Nat.cast Real Real.instNatCast 131072)

noncomputable abbrev qz294 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 14295017) qz485)

noncomputable abbrev qz295 := (BSN.isNear_log_sfrac 4 1 363408 262144 1 80938 Bool.false (BSN.logfrac_isNear 8 2 1 4 1 363408 262144 80938 rfl rfl rfl (ep84 rfl)))

noncomputable abbrev qz296 := (@Nat.cast Real Real.instNatCast 18889465931478580854784)

noncomputable def ep89 := @Enclosure.Real.IsNear.cos_image qz31 qz294 Bool.false 14295017 131072 255 262144 Bool.true 328598 524288 1 80938 (@Enclosure.Real.IsNear.recentre' qz31 Bool.false 111679821 1024000 447 459875 14295017 131072 255 262144 (@Enclosure.Real.IsNear.mulLit_ff qz17 qz32 78672 1000 0 1 363408 262144 1 80938 111679821 1024000 447 459875 qz22 qz295 rfl) rfl) (Enclosure.sfrac_false_div 14295017 131072) (BSN.cos_reduce1 qz294 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 12795308182968293392384) qz296) 226375608064910080 72057594037927936 Bool.false 328598 524288 17 1000000000000000 161876 80938 (BSN.sin_reduce_arg_pos_rat_q1 14295017 131072 226375608064910080 72057594037927936 17 12795308182968293392384 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 328598 524288 12795308182968293392384 18889465931478580854784 727329062 1073741824 162035 161876 (ep88 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep90 := nat_lit 31901471898837980949691369446728269824

noncomputable def ep91 := nat_lit 478522078482569714245370541700924047360

noncomputable def ep92 := BSN.cos_dyadic_bound_f 727329062 1073741824 2 1 524288 162035 ep85 ep90 ep85 ep85 ep91 ep85 408534 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 727329062) qz281 0 1 ep85 ep90 ep85 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 727329062) qz282 0 1 ep85 ep91 ep85 rfl rfl rfl rfl) rfl rfl

noncomputable def ep93 := @Enclosure.Real.IsNear.sin_image qz31 qz294 Bool.false 14295017 131072 255 262144 Bool.false 408534 524288 1 80938 (@Enclosure.Real.IsNear.recentre' qz31 Bool.false 111679821 1024000 447 459875 14295017 131072 255 262144 (@Enclosure.Real.IsNear.mulLit_ff qz17 qz32 78672 1000 0 1 363408 262144 1 80938 111679821 1024000 447 459875 qz22 qz295 rfl) rfl) (Enclosure.sfrac_false_div 14295017 131072) (BSN.sin_reduce1 qz294 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 12795308182968293392384) qz296) 226375608064910080 72057594037927936 Bool.false 408534 524288 17 1000000000000000 161876 80938 (BSN.sin_reduce_arg_pos_rat_q1 14295017 131072 226375608064910080 72057594037927936 17 12795308182968293392384 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 408534 524288 12795308182968293392384 18889465931478580854784 727329062 1073741824 162035 161876 (ep92 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz297 := (@Enclosure.Real.IsNear.recentre' qz30 Bool.false 262143 524288 1 524288 262143 524288 1 524288 (ep81 rfl rfl) rfl)

noncomputable def ep94 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz30 (Real.cos qz31)) (@HMul.hMul Real Real Real qz0 qz30 (@Neg.neg Real Real.instNeg (Real.sin qz31))) Bool.true 43069832757 137438953472 2746228666279 5562017008058368 Bool.true 53547164181 137438953472 2747846131271 5562017008058368 (@Enclosure.Real.IsNear.mulLit_ft qz30 (Real.cos qz31) 262143 524288 1 524288 164299 262144 10450667 10608705536 43069832757 137438953472 2746228666279 5562017008058368 qz297 (@Enclosure.Real.IsNear.recentre' (Real.cos qz31) Bool.true 328598 524288 20901334 21217411072 164299 262144 10450667 10608705536 (ep89 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz30 (@Neg.neg Real Real.instNeg (Real.sin qz31)) 262143 524288 1 524288 204267 262144 10450667 10608705536 53547164181 137438953472 2747846131271 5562017008058368 qz297 (@Enclosure.Real.IsNear.neg (Real.sin qz31) Bool.false 204267 262144 10450667 10608705536 (@Enclosure.Real.IsNear.recentre' (Real.sin qz31) Bool.false 408534 524288 20901334 21217411072 204267 262144 10450667 10608705536 (ep93 rfl rfl) rfl)) rfl)

noncomputable def ep95 := @ep47 43069832757 137438953472 2746228666279 5562017008058368 Bool.true 53547164181 137438953472 2747846131271 5562017008058368 Bool.false 7592786340358591086592 27622395793 68719476736 4900038365933 2781008504029184 Bool.false 15585493409822001856512 56699694723 68719476736 9832102805803 5562017008058368 (ep48 (BSN.head_sum_c_succ qz6 3 4 rfl rfl) (ep79 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep80 ep94) rfl rfl

noncomputable abbrev qz298 := (@Nat.cast Real Real.instNatCast 5)

noncomputable abbrev qz33 := (@Inv.inv Real Real.instInv (Real.sqrt qz298))

noncomputable abbrev qz34 := (@HMul.hMul Real Real Real qz266 qz279 (Real.log (Enclosure.sfrac Bool.false 5 1)))

noncomputable def ep96 := @Enclosure.Complex.IsNear.of_eq qz10 (Complex.mk (@HMul.hMul Real Real Real qz0 qz33 (Real.cos qz34)) (@HMul.hMul Real Real Real qz0 qz33 (@Neg.neg Real Real.instNeg (Real.sin qz34)))) Bool.false 71120778363 274877906944 4922499889773 11124034016116736 Bool.true 100266681877 274877906944 4927530429287 11124034016116736 (BSN.cpow_neg_s_mk qz17 78672 1000 5 qz18 rfl)

noncomputable def ep97 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz298) 1172343 524288 1 524288 117234 117235 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz298) (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz298 qz19)) Bool.false 1172343 524288 1 524288 (BSN.sqrt_natCast_div_one 5) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz298 qz19)) Bool.false 1172343 524288 1 524288 1172343 524288 1 524288 (BSN.sqrt_enclosure 5 1 586171 586172 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep98 := nat_lit 11734546589655452485523914939250625

noncomputable def ep99 := nat_lit 2429970938528035899633153341031900

noncomputable def ep100 := nat_lit 824199001261152424427520000

noncomputable def ep101 := BSN.log_dyadic_bound 2 3 17 16 ep98 262144 80938 ep99 ep100 421904 5 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base16 (BSN.artanhP 2) (BSN.artanhQ 3) 0 16 ep99 ep98 ep100 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep102 := nat_lit 2458278770597228361681318958483370216657897243881129290521200132214576800000

noncomputable def ep103 := nat_lit 1210645168742867216076516685334952313310954446234599978406958400100000000

noncomputable def ep104 := nat_lit 7372415021454199350611803842079440745347069822750918671606786479843530400000

noncomputable def ep105 := BSN.cos_dyadic_bound_f 1024181930 1073741824 3 2 524288 162035 ep102 ep57 ep103 ep104 ep60 ep103 303327 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1024181930) qz281 0 2 ep102 ep57 ep103 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1024181930) qz282 0 2 ep104 ep60 ep103 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz35 := (Real.log (Enclosure.sfrac Bool.false 5 1))

noncomputable abbrev qz299 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 33192031) qz20)

noncomputable abbrev qz300 := (BSN.isNear_log_sfrac 5 1 421904 262144 1 80938 Bool.false (BSN.logfrac_isNear 5 1 2 5 1 421904 262144 80938 rfl rfl rfl (ep101 rfl)))

noncomputable def ep106 := @Enclosure.Real.IsNear.cos_image qz34 qz299 Bool.false 33192031 262144 511 524288 Bool.false 303327 524288 1 80938 (@Enclosure.Real.IsNear.recentre' qz34 Bool.false 129656373 1024000 447 459875 33192031 262144 511 524288 (@Enclosure.Real.IsNear.mulLit_ff qz17 qz35 78672 1000 0 1 421904 262144 1 80938 129656373 1024000 447 459875 qz22 qz300 rfl) rfl) (Enclosure.sfrac_false_div 33192031 262144) (BSN.cos_reduce0 qz299 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 36035198139215414034432) qz23) 226375608064910080 72057594037927936 Bool.false 303327 524288 20 1000000000000000 161876 80938 (BSN.sin_reduce_arg_pos_rat_q0 33192031 262144 226375608064910080 72057594037927936 20 36035198139215414034432 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 303327 524288 36035198139215414034432 37778931862957161709568 1024181930 1073741824 162035 161876 (ep105 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep107 := nat_lit 4423933270940016757253512911921798428133566275429045042955434671266158240000

noncomputable def ep108 := nat_lit 11584531807903031626837933742304644055652074890353595283965860492096919200000

noncomputable def ep109 := BSN.sin_dyadic_bound_f 1024181930 1073741824 3 2 524288 162035 ep107 ep64 ep103 ep108 ep66 ep103 427633 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1024181930) qz285 0 2 ep107 ep64 ep103 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1024181930) qz286 0 2 ep108 ep66 ep103 rfl rfl rfl rfl) rfl rfl

noncomputable def ep110 := @Enclosure.Real.IsNear.sin_image qz34 qz299 Bool.false 33192031 262144 511 524288 Bool.false 427633 524288 1 80938 (@Enclosure.Real.IsNear.recentre' qz34 Bool.false 129656373 1024000 447 459875 33192031 262144 511 524288 (@Enclosure.Real.IsNear.mulLit_ff qz17 qz35 78672 1000 0 1 421904 262144 1 80938 129656373 1024000 447 459875 qz22 qz300 rfl) rfl) (Enclosure.sfrac_false_div 33192031 262144) (BSN.sin_reduce0 qz299 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 36035198139215414034432) qz23) 226375608064910080 72057594037927936 Bool.false 427633 524288 20 1000000000000000 161876 80938 (BSN.sin_reduce_arg_pos_rat_q0 33192031 262144 226375608064910080 72057594037927936 20 36035198139215414034432 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 427633 524288 36035198139215414034432 37778931862957161709568 1024181930 1073741824 162035 161876 (ep109 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz301 := (@Enclosure.Real.IsNear.recentre' qz33 Bool.false 234469 524288 1 524288 234469 524288 1 524288 (ep97 rfl rfl) rfl)

noncomputable def ep111 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz33 (Real.cos qz34)) (@HMul.hMul Real Real Real qz0 qz33 (@Neg.neg Real Real.instNeg (Real.sin qz34))) Bool.false 71120778363 274877906944 4922499889773 11124034016116736 Bool.true 100266681877 274877906944 4927530429287 11124034016116736 (@Enclosure.Real.IsNear.mulLit_ff qz33 (Real.cos qz34) 234469 524288 1 524288 303327 524288 20941803 21217411072 71120778363 274877906944 4922499889773 11124034016116736 qz301 (@Enclosure.Real.IsNear.recentre' (Real.cos qz34) Bool.false 303327 524288 41883606 42434822144 303327 524288 20941803 21217411072 (ep106 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz33 (@Neg.neg Real Real.instNeg (Real.sin qz34)) 234469 524288 1 524288 427633 524288 20941803 21217411072 100266681877 274877906944 4927530429287 11124034016116736 qz301 (@Enclosure.Real.IsNear.neg (Real.sin qz34) Bool.false 427633 524288 20941803 21217411072 (@Enclosure.Real.IsNear.recentre' (Real.sin qz34) Bool.false 427633 524288 41883606 42434822144 427633 524288 20941803 21217411072 (ep110 rfl rfl) rfl)) rfl)

noncomputable def ep112 := @ep45 71120778363 274877906944 4922499889773 11124034016116736 Bool.true 100266681877 274877906944 4927530429287 11124034016116736 Bool.false 12480169014520981749760 181610361535 274877906944 24522653353505 11124034016116736 Bool.false 8695219497179587543040 126532097015 274877906944 24591736040893 11124034016116736 (ep46 (BSN.head_sum_c_succ qz6 4 5 rfl rfl) (ep95 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep96 ep111) rfl rfl

noncomputable abbrev qz302 := (@Nat.cast Real Real.instNatCast 6)

noncomputable abbrev qz36 := (@Inv.inv Real Real.instInv (Real.sqrt qz302))

noncomputable abbrev qz37 := (@HMul.hMul Real Real Real qz266 qz279 (Real.log (Enclosure.sfrac Bool.false 6 1)))

noncomputable def ep113 := @Enclosure.Complex.IsNear.of_eq qz9 (Complex.mk (@HMul.hMul Real Real Real qz0 qz36 (Real.cos qz37)) (@HMul.hMul Real Real Real qz0 qz36 (@Neg.neg Real Real.instNeg (Real.sin qz37)))) Bool.true 51448768469 137438953472 2250919331059 5562017008058368 Bool.true 44776744761 274877906944 4490849588451 11124034016116736 (BSN.cpow_neg_s_mk qz17 78672 1000 6 qz18 rfl)

noncomputable abbrev qz303 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 6) qz19)

noncomputable def ep114 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz302) 1284239 524288 1 524288 107019 107020 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz302) (Real.sqrt qz303) Bool.false 1284239 524288 1 524288 (BSN.sqrt_natCast_div_one 6) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz303) Bool.false 1284239 524288 1 524288 1284239 524288 1 524288 (BSN.sqrt_enclosure 6 1 642119 642120 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep115 := BSN.log_dyadic_bound 2 10 4 3 105000000 262144 80938 1434560 960 106290 12 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 2) (BSN.artanhQ 10) 0 3 1434560 105000000 960 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz38 := (Real.log (Enclosure.sfrac Bool.false 6 1))

noncomputable def ep116 := @Enclosure.Real.IsNear.mulLit_ff qz17 qz38 78672 1000 0 1 4034681531866359 2251799813685248 250000000040469 20234500000000000000 19838529092186887203 140737488355328000 111750000018089643 114968750000000000000 qz22 (BSN.isNear_log_sfrac 6 1 4034681531866359 2251799813685248 250000000040469 20234500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz303) Bool.false 16922680887833197019136 9444732965739290427392 1000000000161876 80938000000000000000 4034681531866359 2251799813685248 250000000040469 20234500000000000000 (BSN.log_rat_reduce_isNear 6 1 2 12 8 106290 262144 24973259072661432 36028797018963968 80938 1000000000000000 rfl rfl rfl rfl (ep115 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep117 := nat_lit 9691715955780961250171675529378391028183666427175427889340272420720097931905

noncomputable def ep118 := nat_lit 5806551365801621078697756515820503359574729423342702448037154253748613761

noncomputable def ep119 := nat_lit 25373664515310267316322210971155886163613148223535946763356272375951330161281

noncomputable def ep120 := BSN.sin_dyadic_bound_f 1245918929 1073741824 3 2 524288 162035 ep117 ep64 ep118 ep119 ep66 ep118 480742 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1245918929) qz285 0 2 ep117 ep64 ep118 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1245918929) qz286 0 2 ep119 ep66 ep118 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz304 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 73904279) qz27)

noncomputable def ep121 := @Enclosure.Real.IsNear.cos_image qz37 qz304 Bool.false 73904279 524288 511 524288 Bool.true 480742 524288 1 80938 (@Enclosure.Real.IsNear.recentre' qz37 Bool.false 19838529092186887203 140737488355328000 111750000018089643 114968750000000000000 73904279 524288 511 524288 (ep116 rfl) rfl) (Enclosure.sfrac_false_div 73904279 524288) (BSN.cos_reduce1 qz304 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 87673750394459262025728) qz29) 226375608064910080 72057594037927936 Bool.false 480742 524288 22 1000000000000000 161876 80938 (BSN.sin_reduce_arg_pos_rat_q1 73904279 524288 226375608064910080 72057594037927936 22 87673750394459262025728 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 480742 524288 87673750394459262025728 75557863725914323419136 1245918929 1073741824 162035 161876 (ep120 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep122 := nat_lit 5386867331596445859463685408106137461595181228174501139610390080068387123841

noncomputable def ep123 := nat_lit 16148988892057734336233660711286771378066394225676818013935095931697664144001

noncomputable def ep124 := BSN.cos_dyadic_bound_f 1245918929 1073741824 3 2 524288 162035 ep122 ep57 ep118 ep123 ep60 ep118 209199 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1245918929) qz281 0 2 ep122 ep57 ep118 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1245918929) qz282 0 2 ep123 ep60 ep118 rfl rfl rfl rfl) rfl rfl

noncomputable def ep125 := @Enclosure.Real.IsNear.sin_image qz37 qz304 Bool.false 73904279 524288 511 524288 Bool.false 209199 524288 1 80938 (@Enclosure.Real.IsNear.recentre' qz37 Bool.false 19838529092186887203 140737488355328000 111750000018089643 114968750000000000000 73904279 524288 511 524288 (ep116 rfl) rfl) (Enclosure.sfrac_false_div 73904279 524288) (BSN.sin_reduce1 qz304 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 87673750394459262025728) qz29) 226375608064910080 72057594037927936 Bool.false 209199 524288 22 1000000000000000 161876 80938 (BSN.sin_reduce_arg_pos_rat_q1 73904279 524288 226375608064910080 72057594037927936 22 87673750394459262025728 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 209199 524288 87673750394459262025728 75557863725914323419136 1245918929 1073741824 162035 161876 (ep124 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz305 := (@Enclosure.Real.IsNear.recentre' qz36 Bool.false 214039 524288 1 524288 214039 524288 1 524288 (ep114 rfl rfl) rfl)

noncomputable def ep126 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz36 (Real.cos qz37)) (@HMul.hMul Real Real Real qz0 qz36 (@Neg.neg Real Real.instNeg (Real.sin qz37))) Bool.true 51448768469 137438953472 2250919331059 5562017008058368 Bool.true 44776744761 274877906944 4490849588451 11124034016116736 (@Enclosure.Real.IsNear.mulLit_ft qz36 (Real.cos qz37) 214039 524288 1 524288 240371 262144 20941803 21217411072 51448768469 137438953472 2250919331059 5562017008058368 qz305 (@Enclosure.Real.IsNear.recentre' (Real.cos qz37) Bool.true 480742 524288 41883606 42434822144 240371 262144 20941803 21217411072 (ep121 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz36 (@Neg.neg Real Real.instNeg (Real.sin qz37)) 214039 524288 1 524288 209199 524288 20941803 21217411072 44776744761 274877906944 4490849588451 11124034016116736 qz305 (@Enclosure.Real.IsNear.neg (Real.sin qz37) Bool.false 209199 524288 20941803 21217411072 (@Enclosure.Real.IsNear.recentre' (Real.sin qz37) Bool.false 209199 524288 41883606 42434822144 209199 524288 20941803 21217411072 (ep125 rfl rfl) rfl)) rfl)

noncomputable def ep127 := @ep43 51448768469 137438953472 2250919331059 5562017008058368 Bool.true 44776744761 274877906944 4490849588451 11124034016116736 Bool.false 10818208237436780150784 78712824597 274877906944 2232653231971 855694924316672 Bool.false 22472740109048952651776 40877676127 137438953472 69910061609 26740466384896 (ep44 (BSN.head_sum_c_succ qz6 5 6 rfl rfl) (ep112 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep113 ep126) rfl rfl

noncomputable abbrev qz306 := (@Nat.cast Real Real.instNatCast 7)

noncomputable abbrev qz39 := (@Inv.inv Real Real.instInv (Real.sqrt qz306))

noncomputable abbrev qz40 := (@HMul.hMul Real Real Real qz266 qz279 (Real.log (Enclosure.sfrac Bool.false 7 1)))

noncomputable def ep128 := @Enclosure.Complex.IsNear.of_eq qz8 (Complex.mk (@HMul.hMul Real Real Real qz0 qz39 (Real.cos qz40)) (@HMul.hMul Real Real Real qz0 qz39 (@Neg.neg Real Real.instNeg (Real.sin qz40)))) Bool.true 68593924287 274877906944 4163919753573 11124034016116736 Bool.true 39015718581 137438953472 2082923544849 5562017008058368 (BSN.cpow_neg_s_mk qz17 78672 1000 7 qz18 rfl)

noncomputable abbrev qz307 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 7) qz19)

noncomputable def ep129 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz306) 1387135 524288 1 524288 99081 99082 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz306) (Real.sqrt qz307) Bool.false 1387135 524288 1 524288 (BSN.sqrt_natCast_div_one 7) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz307) Bool.false 1387135 524288 1 524288 1387135 524288 1 524288 (BSN.sqrt_enclosure 7 1 693567 693568 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep130 := BSN.log_dyadic_bound 3 11 5 4 202569142545 262144 80938 5259111624 688905 146699 14 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 3) (BSN.artanhQ 11) 0 4 5259111624 202569142545 688905 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz41 := (Real.log (Enclosure.sfrac Bool.false 7 1))

noncomputable def ep131 := @Enclosure.Real.IsNear.mulLit_ff qz17 qz41 78672 1000 0 1 4381792198794487 2251799813685248 250000000040469 20234500000000000000 21545272241472492579 140737488355328000 111750000018089643 114968750000000000000 qz22 (BSN.isNear_log_sfrac 7 1 4381792198794487 2251799813685248 250000000040469 20234500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz307) Bool.false 18378568546572512002048 9444732965739290427392 1000000000161876 80938000000000000000 4381792198794487 2251799813685248 250000000040469 20234500000000000000 (BSN.log_rat_reduce_isNear 7 1 2 14 8 146699 262144 24973259072661432 36028797018963968 80938 1000000000000000 rfl rfl rfl rfl (ep130 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep132 := nat_lit 359446377762122363671512851913773056

noncomputable def ep133 := BSN.sin_dyadic_bound_f 774298696 1073741824 2 1 524288 162035 ep132 ep86 ep132 ep132 ep87 ep132 346149 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 774298696) qz285 0 1 ep132 ep86 ep132 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 774298696) qz286 0 1 ep132 ep87 ep132 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz308 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 80262393) qz27)

noncomputable def ep134 := @Enclosure.Real.IsNear.cos_image qz40 qz308 Bool.false 80262393 524288 511 524288 Bool.true 346149 524288 1 80938 (@Enclosure.Real.IsNear.recentre' qz40 Bool.false 21545272241472492579 140737488355328000 111750000018089643 114968750000000000000 80262393 524288 511 524288 (ep131 rfl) rfl) (Enclosure.sfrac_false_div 80262393 524288) (BSN.cos_reduce1 qz308 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 54486426903106935586816) qz29) 226375608064910080 72057594037927936 Bool.false 346149 524288 24 1000000000000000 161876 80938 (BSN.sin_reduce_arg_pos_rat_q1 80262393 524288 226375608064910080 72057594037927936 24 54486426903106935586816 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 346149 524288 54486426903106935586816 75557863725914323419136 774298696 1073741824 162035 161876 (ep133 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep135 := nat_lit 802809998050707665509788690967763573812222165680971519955978064496705929216

noncomputable def ep136 := nat_lit 129201698486310374485633922666940175180553321654271557838066509871579136

noncomputable def ep137 := nat_lit 2408171590755150375780394805057956841086305390399606016752258060470374629376

noncomputable def ep138 := BSN.cos_dyadic_bound_f 774298696 1073741824 3 2 524288 162035 ep135 ep57 ep136 ep137 ep60 ep136 393774 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 774298696) qz281 0 2 ep135 ep57 ep136 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 774298696) qz282 0 2 ep137 ep60 ep136 rfl rfl rfl rfl) rfl rfl

noncomputable def ep139 := @Enclosure.Real.IsNear.sin_image qz40 qz308 Bool.false 80262393 524288 511 524288 Bool.false 393774 524288 1 80938 (@Enclosure.Real.IsNear.recentre' qz40 Bool.false 21545272241472492579 140737488355328000 111750000018089643 114968750000000000000 80262393 524288 511 524288 (ep131 rfl) rfl) (Enclosure.sfrac_false_div 80262393 524288) (BSN.sin_reduce1 qz308 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 54486426903106935586816) qz29) 226375608064910080 72057594037927936 Bool.false 393774 524288 24 1000000000000000 161876 80938 (BSN.sin_reduce_arg_pos_rat_q1 80262393 524288 226375608064910080 72057594037927936 24 54486426903106935586816 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 393774 524288 54486426903106935586816 75557863725914323419136 774298696 1073741824 162035 161876 (ep138 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz309 := (@Enclosure.Real.IsNear.recentre' qz39 Bool.false 198163 524288 1 524288 198163 524288 1 524288 (ep129 rfl rfl) rfl)

noncomputable def ep140 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz39 (Real.cos qz40)) (@HMul.hMul Real Real Real qz0 qz39 (@Neg.neg Real Real.instNeg (Real.sin qz40))) Bool.true 68593924287 274877906944 4163919753573 11124034016116736 Bool.true 39015718581 137438953472 2082923544849 5562017008058368 (@Enclosure.Real.IsNear.mulLit_ft qz39 (Real.cos qz40) 198163 524288 1 524288 346149 524288 20941803 21217411072 68593924287 274877906944 4163919753573 11124034016116736 qz309 (@Enclosure.Real.IsNear.recentre' (Real.cos qz40) Bool.true 346149 524288 41883606 42434822144 346149 524288 20941803 21217411072 (ep134 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz39 (@Neg.neg Real Real.instNeg (Real.sin qz40)) 198163 524288 1 524288 196887 262144 20941803 21217411072 39015718581 137438953472 2082923544849 5562017008058368 qz309 (@Enclosure.Real.IsNear.neg (Real.sin qz40) Bool.false 196887 262144 20941803 21217411072 (@Enclosure.Real.IsNear.recentre' (Real.sin qz40) Bool.false 393774 524288 41883606 42434822144 196887 262144 20941803 21217411072 (ep139 rfl rfl) rfl)) rfl)

noncomputable def ep141 := @ep41 68593924287 274877906944 4163919753573 11124034016116736 Bool.true 39015718581 137438953472 2082923544849 5562017008058368 Bool.false 2781462137787792752640 5059450155 137438953472 8297102942299 2781008504029184 Bool.false 255905496531533299712 930978773 68719476736 16624216359521 5562017008058368 (ep42 (BSN.head_sum_c_succ qz6 6 7 rfl rfl) (ep127 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep128 ep140) rfl rfl

noncomputable abbrev qz310 := (@Nat.cast Real Real.instNatCast 8)

noncomputable abbrev qz42 := (@Inv.inv Real Real.instInv (Real.sqrt qz310))

noncomputable abbrev qz43 := (@HMul.hMul Real Real Real qz266 qz279 (Real.log (Enclosure.sfrac Bool.false 8 1)))

noncomputable def ep142 := @Enclosure.Complex.IsNear.of_eq qz7 (Complex.mk (@HMul.hMul Real Real Real qz0 qz42 (Real.cos qz43)) (@HMul.hMul Real Real Real qz0 qz42 (@Neg.neg Real Real.instNeg (Real.sin qz43)))) Bool.false 94602046043 274877906944 3895008674885 11124034016116736 Bool.true 22250789157 274877906944 3879212733867 11124034016116736 (BSN.cpow_neg_s_mk qz17 78672 1000 8 qz18 rfl)

noncomputable abbrev qz311 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 8) qz19)

noncomputable def ep143 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz310) 1482911 524288 1 524288 92681 92682 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz310) (Real.sqrt qz311) Bool.false 1482911 524288 1 524288 (BSN.sqrt_natCast_div_one 8) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz311) Bool.false 1482911 524288 1 524288 1482911 524288 1 524288 (BSN.sqrt_enclosure 8 1 741455 741456 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep144 := BSN.log_dyadic_bound 0 16 1 0 1 262144 80938 0 1 0 16 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 0) (BSN.artanhQ 16) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz44 := (Real.log (Enclosure.sfrac Bool.false 8 1))

noncomputable def ep145 := @Enclosure.Real.IsNear.mulLit_ff qz17 qz44 78672 1000 0 1 9364972152248037 4503599627370496 500000000121407 40469000000000000000 46047568072603597929 281474976710656000 223500000054268929 229937500000000000000 qz22 (BSN.isNear_log_sfrac 8 1 9364972152248037 4503599627370496 500000000121407 40469000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz311) Bool.false 19639770079031275290624 9444732965739290427392 1000000000242814 80938000000000000000 9364972152248037 4503599627370496 500000000121407 40469000000000000000 (BSN.log_rat_reduce_isNear 8 1 3 16 16 0 262144 24973259072661432 36028797018963968 80938 1000000000000000 rfl rfl rfl rfl (ep144 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep146 := nat_lit 3785258349946039266003774596563521

noncomputable def ep147 := BSN.cos_dyadic_bound_f 248041233 1073741824 2 1 524288 162035 ep146 ep90 ep146 ep146 ep91 ep146 510361 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 248041233) qz281 0 1 ep146 ep90 ep146 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 248041233) qz282 0 1 ep146 ep91 ep146 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz312 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 85770279) qz27)

noncomputable def ep148 := @Enclosure.Real.IsNear.cos_image qz43 qz312 Bool.false 85770279 524288 255 262144 Bool.false 510361 524288 1 80938 (@Enclosure.Real.IsNear.recentre' qz43 Bool.false 46047568072603597929 281474976710656000 223500000054268929 229937500000000000000 85770279 524288 255 262144 (ep145 rfl) rfl) (Enclosure.sfrac_false_div 85770279 524288) (BSN.cos_reduce0 qz312 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 17454350085531398832128) qz29) 226375608064910080 72057594037927936 Bool.false 510361 524288 26 1000000000000000 161876 80938 (BSN.sin_reduce_arg_pos_rat_q0 85770279 524288 226375608064910080 72057594037927936 26 17454350085531398832128 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 510361 524288 17454350085531398832128 75557863725914323419136 248041233 1073741824 162035 161876 (ep147 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep149 := BSN.sin_dyadic_bound_f 248041233 1073741824 2 1 524288 162035 ep146 ep86 ep146 ep146 ep87 ep146 120039 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 248041233) qz285 0 1 ep146 ep86 ep146 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 248041233) qz286 0 1 ep146 ep87 ep146 rfl rfl rfl rfl) rfl rfl

noncomputable def ep150 := @Enclosure.Real.IsNear.sin_image qz43 qz312 Bool.false 85770279 524288 255 262144 Bool.false 120039 524288 1 80938 (@Enclosure.Real.IsNear.recentre' qz43 Bool.false 46047568072603597929 281474976710656000 223500000054268929 229937500000000000000 85770279 524288 255 262144 (ep145 rfl) rfl) (Enclosure.sfrac_false_div 85770279 524288) (BSN.sin_reduce0 qz312 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 17454350085531398832128) qz29) 226375608064910080 72057594037927936 Bool.false 120039 524288 26 1000000000000000 161876 80938 (BSN.sin_reduce_arg_pos_rat_q0 85770279 524288 226375608064910080 72057594037927936 26 17454350085531398832128 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 120039 524288 17454350085531398832128 75557863725914323419136 248041233 1073741824 162035 161876 (ep149 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz313 := (@Enclosure.Real.IsNear.recentre' qz42 Bool.false 185363 524288 1 524288 185363 524288 1 524288 (ep143 rfl rfl) rfl)

noncomputable def ep151 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz42 (Real.cos qz43)) (@HMul.hMul Real Real Real qz0 qz42 (@Neg.neg Real Real.instNeg (Real.sin qz43))) Bool.false 94602046043 274877906944 3895008674885 11124034016116736 Bool.true 22250789157 274877906944 3879212733867 11124034016116736 (@Enclosure.Real.IsNear.mulLit_ff qz42 (Real.cos qz43) 185363 524288 1 524288 510361 524288 10450667 10608705536 94602046043 274877906944 3895008674885 11124034016116736 qz313 (@Enclosure.Real.IsNear.recentre' (Real.cos qz43) Bool.false 510361 524288 20901334 21217411072 510361 524288 10450667 10608705536 (ep148 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz42 (@Neg.neg Real Real.instNeg (Real.sin qz43)) 185363 524288 1 524288 120039 524288 10450667 10608705536 22250789157 274877906944 3879212733867 11124034016116736 qz313 (@Enclosure.Real.IsNear.neg (Real.sin qz43) Bool.false 120039 524288 10450667 10608705536 (@Enclosure.Real.IsNear.recentre' (Real.sin qz43) Bool.false 120039 524288 20901334 21217411072 120039 524288 10450667 10608705536 (ep150 rfl rfl) rfl)) rfl)

noncomputable def ep152 := @ep39 94602046043 274877906944 3895008674885 11124034016116736 Bool.true 22250789157 274877906944 3879212733867 11124034016116736 Bool.false 14392737273353775087616 104720946353 274877906944 3371220040371 1011275819646976 Bool.true 1273157091300569251840 18526874065 274877906944 3375240495719 1011275819646976 (ep40 (BSN.head_sum_c_succ qz6 7 8 rfl rfl) (ep141 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep142 ep151) rfl rfl

theorem EMRow21.d6 : Enclosure.Complex.IsNear qz4 Bool.false 104720946353 274877906944 3371220040371 1011275819646976 Bool.true 18526874065 274877906944 3375240495719 1011275819646976 := ep38 (BSN.head_sum_c_succ qz6 8 9 rfl rfl) (ep152 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

theorem EMRow21.d7 : @Eq Nat (BSN.factNat (Nat.mul 2 1)) 2 := @Eq.refl Nat 2

theorem EMRow21.d8 : @Eq Nat (Nat.pow 16 1) 16 := @Eq.refl Nat 16

noncomputable def ep153 := nat_lit 1178701273534134566660855496347

noncomputable def ep154 := nat_lit 892005796559986259287605248000

noncomputable def ep155 := nat_lit 2451792462471119981735528242195050277

noncomputable def ep156 := nat_lit 398420055946343408303514138175340544000

noncomputable abbrev qz504 := (@instHMul Complex Complex.instMul)

noncomputable abbrev qz486 := qz504

noncomputable abbrev qz314 := qz486

noncomputable abbrev qz45 := qz314

noncomputable abbrev qz487 := (@instHSub Complex Complex.instSub)

noncomputable abbrev qz315 := qz487

noncomputable abbrev qz46 := qz315

noncomputable abbrev qz505 := (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (4 : Complex))

noncomputable abbrev qz506 := (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid))

noncomputable abbrev qz488 := (@HAdd.hAdd Complex Complex Complex qz502 (@HAdd.hAdd Complex Complex Complex qz502 qz505 (@HMul.hMul Complex Complex Complex qz504 Complex.I (@HDiv.hDiv Complex Complex Complex qz506 (↑qz503) (2 : Complex)))) (@Nat.cast Complex Complex.instNatCast 2))

noncomputable abbrev qz316 := qz488

noncomputable abbrev qz47 := (Complex.Stirling.logGammaStirling 1 qz316)

noncomputable abbrev qz489 := (@HAdd.hAdd Complex Complex Complex qz502 qz505 (@HMul.hMul Complex Complex Complex qz504 Complex.I (@HDiv.hDiv Complex Complex Complex qz506 (↑qz503) (2 : Complex))))

noncomputable abbrev qz317 := qz489

noncomputable abbrev qz48 := qz317

noncomputable abbrev qz49 := (@HMul.hMul Real Real Real qz266 (@HDiv.hDiv Real Real Real qz269 qz279 (2 : Real)) (Real.log Real.pi))

noncomputable abbrev qz318 := (@instHSub Real Real.instSub)

noncomputable def ep157 := Complex.re (@HMul.hMul Complex Complex Complex qz45 (Complex.exp (@HMul.hMul Complex Complex Complex qz45 Complex.I ↑(@HSub.hSub Real Real Real qz318 (Complex.im (@HSub.hSub Complex Complex Complex qz46 qz47 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz48 (@Nat.cast Complex Complex.instNatCast j))))) qz49))) (zetaApproximant qz6 1 16))

noncomputable def ep158 := @Enclosure.Real.IsNear.of_eq ep157 (@HSub.hSub Real Real Real qz318 (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz318 (Complex.im (@HSub.hSub Complex Complex Complex qz46 qz47 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz48 (@Nat.cast Complex Complex.instNatCast j))))) qz49)) (Complex.re (zetaApproximant qz6 1 16))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz318 (Complex.im (@HSub.hSub Complex Complex Complex qz46 qz47 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz48 (@Nat.cast Complex Complex.instNatCast j))))) qz49)) (Complex.im (zetaApproximant qz6 1 16))))

noncomputable def ep159 := nat_lit 141444437383234768522578982751

noncomputable def ep160 := @Enclosure.Real.IsNear.subLit_tt_n (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz318 (Complex.im (@HSub.hSub Complex Complex Complex qz46 qz47 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz48 (@Nat.cast Complex Complex.instNatCast j))))) qz49)) (Complex.re (zetaApproximant qz6 1 16))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz318 (Complex.im (@HSub.hSub Complex Complex Complex qz46 qz47 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz48 (@Nat.cast Complex Complex.instNatCast j))))) qz49)) (Complex.im (zetaApproximant qz6 1 16))) ep159

noncomputable def ep161 := nat_lit 107040695587198351114512629760

noncomputable def ep162 := nat_lit 2448693326231673856941863433429584879

noncomputable def ep163 := nat_lit 3556989232756540954039867

noncomputable def ep164 := nat_lit 1338008694839979388931407872000

noncomputable def ep165 := nat_lit 1549568119723062396832404382732699

noncomputable def ep166 := nat_lit 199210027973171704151757069087670272000

noncomputable def ep167 := nat_lit 189253506312915471772082615869142404834946263102567565230080

noncomputable def ep168 := @Enclosure.Real.IsNear.mulLit_tf (Real.cos (@HSub.hSub Real Real Real qz318 (Complex.im (@HSub.hSub Complex Complex Complex qz46 qz47 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz48 (@Nat.cast Complex Complex.instNatCast j))))) qz49)) (Complex.re (zetaApproximant qz6 1 16)) 524287 524288 9772359

noncomputable def ep169 := nat_lit 103933332341445406163187367

noncomputable def ep170 := nat_lit 18777976945176254928125952000

noncomputable def ep171 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HSub.hSub Real Real Real qz318 (Complex.im (@HSub.hSub Complex Complex Complex qz46 qz47 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz48 (@Nat.cast Complex Complex.instNatCast j))))) qz49)) Bool.true 524287 524288 19544718

noncomputable abbrev qz319 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 3911827) (@Nat.cast Real Real.instNatCast 65536))

noncomputable def ep172 := @Enclosure.Real.IsNear.cos_image (@HSub.hSub Real Real Real qz318 (Complex.im (@HSub.hSub Complex Complex Complex qz46 qz47 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz48 (@Nat.cast Complex Complex.instNatCast j))))) qz49) qz319 Bool.false 3911827 65536 235

noncomputable def ep173 := nat_lit 66304409600000000000000000

noncomputable def ep174 := @Enclosure.Real.IsNear.recentre' (@HSub.hSub Real Real Real qz318 (Complex.im (@HSub.hSub Complex Complex Complex qz46 qz47 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz48 (@Nat.cast Complex Complex.instNatCast j))))) qz49) Bool.false 33602339024902562689 562949953421312000 29491024951366976345003 ep173

noncomputable def ep175 := @Enclosure.Real.IsNear.subLit_ff_p (Complex.im (@HSub.hSub Complex Complex Complex qz46 qz47 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz48 (@Nat.cast Complex Complex.instNatCast j))))) qz49 58951459825230291841 562949953421312000 9592417651366976345003 ep173 368878257 8192000

noncomputable def ep176 := nat_lit 275270361292001793548288000

noncomputable def ep177 := nat_lit 1326088192000000000000000000

noncomputable def ep178 := @Enclosure.Complex.IsNear.im_isNear (@HSub.hSub Complex Complex Complex qz46 qz47 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz48 (@Nat.cast Complex Complex.instNatCast j)))) Bool.true 139134128752343920359 2251799813685248000 342659600181896583894631 ep177 Bool.false 58951459825230291841 562949953421312000

noncomputable def ep179 := @Enclosure.Complex.IsNear.subLitP qz47 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz48 (@Nat.cast Complex Complex.instNatCast j))) Bool.true 122595100944050845359 2251799813685248000 334467600168635701974631 ep177 Bool.false 60698559459142937841 562949953421312000 8773217651300671935403

noncomputable def ep180 := nat_lit 313302205201787346635369259605164032

noncomputable def ep181 := nat_lit 16593360781365869223977329094557696

noncomputable abbrev qz507 := (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (2 : Complex))

noncomputable abbrev qz490 := qz507

noncomputable abbrev qz320 := (@HSub.hSub Complex Complex Complex qz487 qz488 qz490)

noncomputable abbrev qz321 := (Complex.log qz488)

noncomputable abbrev qz50 := (@HSub.hSub Complex Complex Complex qz315 (@HMul.hMul Complex Complex Complex qz314 qz320 qz321) qz316)

noncomputable abbrev qz322 := qz490

noncomputable abbrev qz51 := (@HMul.hMul Complex Complex Complex qz314 qz322 ↑(Real.log qz270))

noncomputable abbrev qz491 := qz506

noncomputable abbrev qz323 := qz491

noncomputable abbrev qz52 := qz323

noncomputable abbrev qz53 := (@instHMul Nat instMulNat)

noncomputable abbrev qz492 := (@instHPow Complex Int (@ZPow.toPow Complex (@DivInvMonoid.toZPow Complex Complex.instDivInvMonoid)))

noncomputable abbrev qz324 := qz492

noncomputable abbrev qz54 := qz324

noncomputable abbrev qz55 := qz316

noncomputable abbrev qz325 := (@OfNat.ofNat Int 1 (@instOfNat 1))

noncomputable abbrev qz56 := qz325

noncomputable abbrev qz326 := (@OfNat.ofNat Int 2 (@instOfNat 2))

noncomputable abbrev qz57 := qz326

noncomputable abbrev qz327 := (@instHSub Int Int.instSub)

noncomputable abbrev qz328 := (@instHMul Int Int.instMul)

noncomputable def ep182 := @Enclosure.Complex.IsNear.of_eq qz47 (@HAdd.hAdd Complex Complex Complex qz5 (@HAdd.hAdd Complex Complex Complex qz5 qz50 qz51) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz53 2 k))) (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz45 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz54 qz55 (@HSub.hSub Int Int Int qz327 qz56 (@HMul.hMul Int Int Int qz328 qz57 (@Nat.cast Int instNatCastInt k)))))) Bool.true 122595100944050845359

noncomputable def ep183 := @Enclosure.Complex.IsNear.addLitP (@HAdd.hAdd Complex Complex Complex qz5 qz50 qz51) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz53 2 k))) (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz45 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz54 qz55 (@HSub.hSub Int Int Int qz327 qz56 (@HMul.hMul Int Int Int qz328 qz57 (@Nat.cast Int instNatCastInt k))))) Bool.true 122595372921334429359 2251799813685248000

noncomputable def ep184 := nat_lit 1053083898409034213156116758528

noncomputable def ep185 := nat_lit 16293645486958147888528490496000

noncomputable def ep186 := @ep183 10207126984792626167 40469000000000000000000 Bool.false 60699748181190388977 562949953421312000 1070900001598970659 8093800000000000000000 Bool.false 1037511 8589934592 3 8589934592 Bool.true 566826843 268435456000 1639 268435456000 Bool.true ep184 122595100944050845359 2251799813685248000 334467600168635701974631 ep177 Bool.false ep185

noncomputable def ep187 := @Enclosure.Complex.IsNear.addLitP qz50 qz51 Bool.true 124664636624939677359 2251799813685248000 5026375000575024021 20234500000000000000000

noncomputable def ep188 := nat_lit 16068820719545146324942848

noncomputable def ep189 := @ep187 Bool.false 60699748181190388977 562949953421312000 1070900001598970659 8093800000000000000000 Bool.false 120447 131072 1 262144 Bool.false 0 1 0 1 Bool.true ep188 122595372921334429359 2251799813685248000 10207126984792626167 40469000000000000000000 Bool.false 60699748181190388977 60699748181190388977 562949953421312000

noncomputable abbrev qz58 := (@HMul.hMul Complex Complex Complex qz314 qz320 qz321)

noncomputable def ep190 := @Enclosure.Complex.IsNear.subLitP qz58 qz55 Bool.true 119598087044147869359 2251799813685248000 5026375000575024021 20234500000000000000000 Bool.false 82843947548971117809

noncomputable def ep191 := @ep190 562949953421312000 1070900001598970659 8093800000000000000000 Bool.false 9000 4000 0 1 Bool.false 157344 4000 0 1 Bool.true 498658546499758709436000 124664636624939677359 2251799813685248000 5026375000575024021 20234500000000000000000 Bool.false 242798992724761555908000 60699748181190388977 562949953421312000 1070900001598970659 8093800000000000000000

noncomputable abbrev qz59 := qz320

noncomputable abbrev qz60 := qz321

noncomputable def ep192 := @Enclosure.Complex.IsNear.mul qz59 qz60 Bool.true 119598087044147869359 2251799813685248000 5026375000575024021 20234500000000000000000 Bool.false 82843947548971117809 562949953421312000 1070900001598970659

noncomputable abbrev qz61 := (Complex.re qz320)

noncomputable abbrev qz62 := (Complex.re qz321)

noncomputable abbrev qz63 := (Complex.im qz320)

noncomputable abbrev qz64 := (Complex.im qz321)

noncomputable def ep193 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 qz61 qz62) (@HMul.hMul Real Real Real qz0 qz63 qz64) 115816397734081989 18014398509481984 175000000283283 32375200000000000000 4189848023778378687 70368744177664000

noncomputable def ep194 := nat_lit 67327737530781061229443217262379008

noncomputable def ep195 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz62 7000 4000 0 1 16545199676297427 4503599627370496 25000000040469 8093800000000000000

noncomputable def ep196 := @Enclosure.Complex.IsNear.re_isNear qz59 Bool.false 7000 4000 0 1 Bool.false 157344 4000 0 1

noncomputable abbrev qz329 := (Enclosure.sfrac Bool.false 157344 4000)

noncomputable abbrev qz65 := qz329

noncomputable def ep197 := @Enclosure.Complex.IsNear.of_eq qz59 (Complex.mk (Enclosure.sfrac Bool.false 7000 4000) qz65) Bool.false 7000 4000 0 1 Bool.false 157344 4000 0

noncomputable abbrev qz330 := (Enclosure.sfrac Bool.false 9000 4000)

noncomputable abbrev qz66 := qz330

noncomputable abbrev qz331 := (Complex.log (Complex.mk qz66 qz65))

noncomputable def ep198 := @Enclosure.Complex.IsNear.of_eq qz60 qz331 Bool.false 16545199676297427 4503599627370496 25000000040469 8093800000000000000 Bool.false 852114708923811 562949953421312 500000000040469 80938000000000000000

noncomputable def ep199 := nat_lit 515195599164907312686954817741596432600235171191174447500655329280

noncomputable def ep200 := nat_lit 7410940563828121579666243652431663793006729267897581486689222656

noncomputable def ep201 := nat_lit 5476538258104101385965370783545498029091634184213683545047040

noncomputable def ep202 := BSN.log_dyadic_bound 8454134336 41222134336 4 3 ep199 524288 161876 ep200 ep201 218142 49676268672 32768000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 8454134336) (BSN.artanhQ 41222134336) 0 3 ep200 ep199 ep201 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz67 := (Enclosure.sfrac Bool.false 1 2)

noncomputable abbrev qz332 := (Real.log (Enclosure.sfrac Bool.false 24838134336 16000000))

noncomputable abbrev qz333 := (Enclosure.Real.IsNear.const Bool.false 1 2)

noncomputable abbrev qz334 := (@Nat.cast Real Real.instNatCast 16000000)

noncomputable def ep203 := @Enclosure.Real.IsNear.mulLit_ff qz67 qz332 1 2 0 1 16545199676297427 2251799813685248 25000000040469 4046900000000000000 16545199676297427 4503599627370496 25000000040469 8093800000000000000 qz333 (BSN.isNear_log_sfrac 24838134336 16000000 16545199676297427 2251799813685248 25000000040469 4046900000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 24838134336) qz334)) Bool.false 138791194366186006511616 18889465931478580854784 1000000001618760 161876000000000000000 16545199676297427 2251799813685248 25000000040469 4046900000000000000 (BSN.log_rat_reduce_isNear 24838134336 16000000 10 49676268672 32768000000 218142 524288 24973259072661432 36028797018963968 161876 1000000000000000 rfl rfl rfl rfl (ep202 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep204 := BSN.arctan_dyadic_bound_f 9000 157344 1 0 524288 161876 0 1 1 0 1 1 29956 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 9000) (BSN.arctanEvenQ 157344) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 9000) (BSN.arctanOddQ 157344) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz68 := (@HMul.hMul Real Real Real qz266 (Enclosure.sfrac Bool.false 1 2) Real.pi)

noncomputable abbrev qz69 := (@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 2) Real.pi 1 2 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 qz333 BSN.pi_near_15 rfl)

noncomputable abbrev qz335 := (Real.arctan (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 9000) (@Nat.cast Real Real.instNatCast 157344)))

noncomputable def ep205 := @Enclosure.Real.IsNear.subLit_ff_p qz68 qz335 884279719003555 562949953421312 1 2000000000000000 29956 524288 1 161876 446753516512247021568 852114708923811 562949953421312 500000000040469 80938000000000000000 qz69 (ep204 rfl) rfl rfl

noncomputable abbrev qz336 := (Real.arctan (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 157344) (@Nat.cast Real Real.instNatCast 9000)))

noncomputable def ep206 := @Enclosure.Complex.IsNear.re_isNear qz60 Bool.false 16545199676297427 4503599627370496 25000000040469 8093800000000000000 Bool.false 852114708923811 562949953421312 500000000040469 80938000000000000000 (ep198 (@congrArg Complex Complex qz55 (Complex.mk qz66 qz65) Complex.log (BSN.w_shift_mk qz17 Bool.false 78672 1000 2 qz18 rfl)) (@Enclosure.Complex.IsNear.of_parts qz331 Bool.false 16545199676297427 4503599627370496 25000000040469 8093800000000000000 Bool.false 852114708923811 562949953421312 500000000040469 80938000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz331) (@HMul.hMul Real Real Real qz0 qz67 qz332) Bool.false 16545199676297427 4503599627370496 25000000040469 8093800000000000000 (Enclosure.clog_re_eq 9000 157344 4000 24838134336 16000000 rfl rfl rfl) (ep203 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz331) qz336 Bool.false 852114708923811 562949953421312 500000000040469 80938000000000000000 (Enclosure.clog_im_eq 9000 157344 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz336 (@HSub.hSub Real Real Real qz318 qz68 qz335) Bool.false 852114708923811 562949953421312 500000000040469 80938000000000000000 (BSN.arctan_recip 157344 9000 rfl rfl) ep205))))

noncomputable def ep207 := @Enclosure.Real.IsNear.mulLit_ff qz63 qz64 157344 4000 0 1 852114708923811 562949953421312 500000000040469 80938000000000000000

noncomputable def ep208 := @Enclosure.Complex.IsNear.im_isNear qz59 Bool.false 7000 4000 0 1 Bool.false 157344 4000 0 1

noncomputable def ep209 := @Enclosure.Complex.IsNear.im_isNear qz60 Bool.false 16545199676297427 4503599627370496 25000000040469 8093800000000000000 Bool.false 852114708923811 562949953421312 500000000040469 80938000000000000000 (ep198 (@congrArg Complex Complex qz55 (Complex.mk qz66 qz65) Complex.log (BSN.w_shift_mk qz17 Bool.false 78672 1000 2 qz18 rfl)) (@Enclosure.Complex.IsNear.of_parts qz331 Bool.false 16545199676297427 4503599627370496 25000000040469 8093800000000000000 Bool.false 852114708923811 562949953421312 500000000040469 80938000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz331) (@HMul.hMul Real Real Real qz0 qz67 qz332) Bool.false 16545199676297427 4503599627370496 25000000040469 8093800000000000000 (Enclosure.clog_re_eq 9000 157344 4000 24838134336 16000000 rfl rfl rfl) (ep203 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz331) qz336 Bool.false 852114708923811 562949953421312 500000000040469 80938000000000000000 (Enclosure.clog_im_eq 9000 157344 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz336 (@HSub.hSub Real Real Real qz318 qz68 qz335) Bool.false 852114708923811 562949953421312 500000000040469 80938000000000000000 (BSN.arctan_recip 157344 9000 rfl rfl) ep205))))

noncomputable abbrev qz337 := (Enclosure.Real.IsNear.const Bool.false 157344 4000)

noncomputable abbrev qz70 := (@ep197 1 (BSN.w_sub_half_mk qz279 Bool.false 78672 1000 2 qz280 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7000 4000) qz329 Bool.false 7000 4000 0 1 Bool.false 157344 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 7000 4000) qz337))

noncomputable def ep210 := @ep193 223500000018089643 919750000000000000000 ep194 119598087044147869359 2251799813685248000 5026375000575024021 20234500000000000000000 (@ep195 115816397734081989 18014398509481984 175000000283283 32375200000000000000 (ep196 qz70) ep206 rfl) (@ep207 4189848023778378687 70368744177664000 223500000018089643 919750000000000000000 (ep208 qz70) ep209 rfl) rfl

noncomputable def ep211 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz61 qz64) (@HMul.hMul Real Real Real qz0 qz63 qz62) 5964802962466677 2251799813685248 3500000000283283 323752000000000000000 81352746808354448559 562949953421312000

noncomputable def ep212 := nat_lit 186547985655723620794744530253381632

noncomputable def ep213 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz64 7000 4000 0 1 852114708923811 562949953421312 500000000040469 80938000000000000000

noncomputable def ep214 := @Enclosure.Real.IsNear.mulLit_ff qz63 qz62 157344 4000 0 1 16545199676297427 4503599627370496 25000000040469 8093800000000000000

noncomputable def ep215 := @ep211 11175000018089643 91975000000000000000 ep212 82843947548971117809 562949953421312000 1070900001598970659 8093800000000000000000 (@ep213 5964802962466677 2251799813685248 3500000000283283 323752000000000000000 (ep196 qz70) ep209 rfl) (@ep214 81352746808354448559 562949953421312000 11175000018089643 91975000000000000000 (ep208 qz70) ep206 rfl) rfl

noncomputable def ep216 := @Enclosure.Complex.IsNear.of_eq qz55 (Complex.mk qz66 qz65) Bool.false 9000 4000 0 1 Bool.false 157344 4000 0 1 (BSN.w_shift_mk qz17 Bool.false 78672 1000 2 qz18 rfl)

noncomputable abbrev qz338 := (ep216 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 9000 4000) (Enclosure.sfrac Bool.false 157344 4000) Bool.false 9000 4000 0 1 Bool.false 157344 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 9000 4000) (Enclosure.Real.IsNear.const Bool.false 157344 4000)))

noncomputable abbrev qz71 := qz338

noncomputable def ep217 := ep191 (@ep192 8093800000000000000000 (ep210 rfl) (ep215 rfl)) qz71 rfl rfl rfl rfl rfl rfl

noncomputable abbrev qz72 := qz322

noncomputable def ep218 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re qz72) (Complex.re ↑qz3)) (@HMul.hMul Real Real Real qz0 (Complex.im qz72) (Complex.im ↑qz3)) 120447 131072 1 262144 0 1 0 1 120447 120447

noncomputable def ep219 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re qz72) (Complex.re ↑qz3) 1 2 0 1 120447 65536 1 131072 120447 131072 1 262144

noncomputable abbrev qz73 := (@Enclosure.Complex.IsNear.of_eq qz322 (Complex.mk (Enclosure.sfrac Bool.false 1 2) qz277) Bool.false 1 2 0 1 Bool.false 0 1 0 1 BSN.half_c_mk (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 2) qz277 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz333 qz288))

noncomputable def ep220 := ep219 (@Enclosure.Complex.IsNear.re_isNear qz72 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz73) (@Enclosure.Real.IsNear.of_eq (Complex.re ↑qz3) qz3 Bool.false 120447 65536 1 131072 (Complex.ofReal_re qz3) EMRow21.d4)

noncomputable def ep221 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz72) (Complex.im ↑qz3) 0 1 0 1 0 1 0 1 0 1 0 1

noncomputable def ep222 := ep221 (@Enclosure.Complex.IsNear.im_isNear qz72 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz73) (@Enclosure.Real.IsNear.of_eq (Complex.im ↑qz3) qz14 Bool.false 0 1 0 1 (@Eq.trans Real (Complex.im ↑qz3) (0 : Real) qz14 (Complex.ofReal_im qz3) Enclosure.sfrac_zero_eq) qz24)

noncomputable def ep223 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re qz72) (Complex.im ↑qz3)) (@HMul.hMul Real Real Real qz0 (Complex.im qz72) (Complex.re ↑qz3)) 0 1 0 1 0 1 0 1 0 0

noncomputable def ep224 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re qz72) (Complex.im ↑qz3) 1 2 0 1 0 1 0 1 0 1 0 1

noncomputable def ep225 := ep224 (@Enclosure.Complex.IsNear.re_isNear qz72 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz73) (@Enclosure.Real.IsNear.of_eq (Complex.im ↑qz3) qz14 Bool.false 0 1 0 1 (@Eq.trans Real (Complex.im ↑qz3) (0 : Real) qz14 (Complex.ofReal_im qz3) Enclosure.sfrac_zero_eq) qz24)

noncomputable def ep226 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz72) (Complex.re ↑qz3) 0 1 0 1 120447 65536 1 131072 0 1 0 1

noncomputable def ep227 := ep226 (@Enclosure.Complex.IsNear.im_isNear qz72 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz73) (@Enclosure.Real.IsNear.of_eq (Complex.re ↑qz3) qz3 Bool.false 120447 65536 1 131072 (Complex.ofReal_re qz3) EMRow21.d4)

noncomputable def ep228 := @ep189 1070900001598970659 8093800000000000000000 (ep217 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@Enclosure.Complex.IsNear.mul qz72 (↑qz3) Bool.false 120447 131072 1 262144 Bool.false 0 1 0 1 (@ep218 131072 1 262144 (ep220 rfl) (ep222 rfl) rfl rfl) (@ep223 1 0 1 (ep225 rfl) (ep227 rfl) rfl rfl))

noncomputable abbrev qz74 := (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 1)

noncomputable abbrev qz339 := (@Nat.cast Complex Complex.instNatCast 1)

noncomputable abbrev qz75 := (@HMul.hMul Complex Complex Complex qz314 (@HMul.hMul Complex Complex Complex qz314 (2 : Complex) qz339) (@HSub.hSub Complex Complex Complex qz315 (@HMul.hMul Complex Complex Complex qz314 (2 : Complex) qz339) (1 : Complex)))

noncomputable abbrev qz340 := (@HPow.hPow Complex Int Complex qz492 qz488 (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) (@OfNat.ofNat Int 1 (@instOfNat 1)) (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (@OfNat.ofNat Int 2 (@instOfNat 2)) (@Nat.cast Int instNatCastInt 1))))

noncomputable abbrev qz76 := qz340

noncomputable def ep229 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz53 2 k))) (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz45 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz54 qz55 (@HSub.hSub Int Int Int qz327 qz56 (@HMul.hMul Int Int Int qz328 qz57 (@Nat.cast Int instNatCastInt k))))) (@HAdd.hAdd Complex Complex Complex qz5 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz53 2 k))) (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz45 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz54 qz55 (@HSub.hSub Int Int Int qz327 qz56 (@HMul.hMul Int Int Int qz328 qz57 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 (@Rat.cast Complex Complex.instRatCast (bernoulli qz74)) qz75) qz76)) Bool.false 1037511 8589934592 3 8589934592

noncomputable def ep230 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz53 2 k))) (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz45 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz54 qz55 (@HSub.hSub Int Int Int qz327 qz56 (@HMul.hMul Int Int Int qz328 qz57 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 (@Rat.cast Complex Complex.instRatCast (bernoulli qz74)) qz75) qz76) Bool.false 0 1 0 1 Bool.false

noncomputable def ep231 := @ep230 0 1 0 1 Bool.false 1037511 8589934592 3 8589934592 Bool.true 566826843 268435456000 1639 268435456000 Bool.false 1037511 1037511 8589934592 3 8589934592 Bool.true 566826843 566826843 268435456000 1639

noncomputable def ep232 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz53 2 k))) (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz45 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz54 qz55 (@HSub.hSub Int Int Int qz327 qz56 (@HMul.hMul Int Int Int qz328 qz57 (@Nat.cast Int instNatCastInt k))))) (Complex.mk qz14 qz14) Bool.false 0 1 0 1 Bool.false

noncomputable def ep233 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz52 (@Rat.cast Complex Complex.instRatCast (bernoulli qz74)) qz75) qz76 Bool.false 1037511 8589934592 3 8589934592 Bool.true 566826843 268435456000 1639 268435456000

noncomputable abbrev qz77 := (Complex.re qz340)

noncomputable abbrev qz78 := (Complex.im qz340)

noncomputable def ep234 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz52 (@Rat.cast Complex Complex.instRatCast (bernoulli qz74)) qz75)) qz77) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz52 (@Rat.cast Complex Complex.instRatCast (bernoulli qz74)) qz75)) qz78) 1037511 8589934592 3 8589934592 0 1 0

noncomputable def ep235 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz52 (@Rat.cast Complex Complex.instRatCast (bernoulli qz74)) qz75)) qz77 1 12 0 1 3112533 2147483648 9 2147483648 1037511

noncomputable def ep236 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz52 (@Rat.cast Complex Complex.instRatCast (bernoulli qz74)) qz75) (Complex.mk (Enclosure.sfrac Bool.false 1 12) qz14) Bool.false 1 12 0 1 Bool.false 0 1 0 1

noncomputable abbrev qz341 := (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 12) qz14 Bool.false 1 12 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 12) qz24)

noncomputable def ep237 := @Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz52 (@Rat.cast Complex Complex.instRatCast (bernoulli qz74)) qz75) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (ep236 (BSN.stirling_coeff_mk 1 1 6 Bool.false BSN.bern_real_1 rfl rfl) qz341)

noncomputable def ep238 := @Enclosure.Complex.IsNear.re_isNear qz76 Bool.false 3112533 2147483648 9 2147483648 Bool.true 1700480529 67108864000 4917 67108864000

noncomputable abbrev qz493 := (@instHPow Complex Nat (@NPow.toPow Complex (@Monoid.toNPow Complex (@Semiring.toMonoid Complex Complex.instSemiring))))

noncomputable abbrev qz342 := (@HPow.hPow Complex Nat Complex qz493 qz488 1)

noncomputable abbrev qz79 := (@Inv.inv Complex Complex.instInv qz342)

noncomputable def ep239 := @Enclosure.Complex.IsNear.of_eq qz76 qz79 Bool.false 3112533 2147483648 9 2147483648 Bool.true 1700480529 67108864000 4917

noncomputable def ep240 := @Enclosure.Complex.IsNear.of_parts qz79 Bool.false 3112533 2147483648 9 2147483648 Bool.true 1700480529 67108864000 4917

noncomputable abbrev qz80 := (Complex.re qz342)

noncomputable abbrev qz81 := (@MonoidWithZeroHom Complex Real (@instMulZeroOneClassOfSemiring Complex Complex.instSemiring) (@instMulZeroOneClassOfSemiring Real Real.semiring))

noncomputable abbrev qz82 := (@MonoidWithZeroHom.funLike Complex Real (@instMulZeroOneClassOfSemiring Complex Complex.instSemiring) (@instMulZeroOneClassOfSemiring Real Real.semiring))

noncomputable abbrev qz83 := qz342

noncomputable def ep241 := @Enclosure.Real.IsNear.mulLit_ff qz80 (@Inv.inv Real Real.instInv (@DFunLike.coe qz81 Complex (fun (x : Complex) => Real) qz82 Complex.normSq qz83)) 9000 4000 0 1 345837 536870912 1 536870912

noncomputable def ep242 := @Enclosure.Complex.IsNear.re_isNear qz83 Bool.false 9000 4000 0 1 Bool.false 157344 4000 0 1

noncomputable def ep243 := @Enclosure.Complex.IsNear.of_eq qz83 qz55 Bool.false 9000 4000 0 1 Bool.false 157344 4000 0

noncomputable def ep244 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (@DFunLike.coe qz81 Complex (fun (x : Complex) => Real) qz82 Complex.normSq qz83)) Bool.false 345837 536870912 1 536870912 345837 536870912 1

noncomputable abbrev qz84 := (Complex.im qz342)

noncomputable abbrev qz343 := (@instHAdd Real Real.instAdd)

noncomputable def ep245 := @Enclosure.Real.IsNear.of_eq (@DFunLike.coe qz81 Complex (fun (x : Complex) => Real) qz82 Complex.normSq qz83) (@HAdd.hAdd Real Real Real qz343 (@HMul.hMul Real Real Real qz0 qz80 qz80) (@HMul.hMul Real Real Real qz0 qz84 qz84)) Bool.false 388095849 250000 0 1

noncomputable def ep246 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz80 qz80) (@HMul.hMul Real Real Real qz0 qz84 qz84) 81 16 0 1 24176889 15625

noncomputable def ep247 := @Enclosure.Real.IsNear.mulLit_ff qz80 qz80 9000 4000 0 1 9000 4000 0 1

noncomputable def ep248 := @Enclosure.Real.IsNear.mulLit_ff qz84 qz84 157344 4000 0 1 157344 4000 0 1

noncomputable def ep249 := @Enclosure.Complex.IsNear.im_isNear qz83 Bool.false 9000 4000 0 1 Bool.false 157344 4000 0 1

noncomputable abbrev qz85 := (ep242 (@ep243 1 (BSN.pow_one_c qz316) qz338))

noncomputable abbrev qz86 := (ep249 (@ep243 1 (BSN.pow_one_c qz316) qz338))

noncomputable def ep250 := @ep246 0 1 388095849 388095849 250000 0 1 (@ep247 81 16 0 1 qz85 qz85 rfl) (@ep248 24176889 15625 0 1 qz86 qz86 rfl)

noncomputable def ep251 := @Enclosure.Real.IsNear.inv_image (@DFunLike.coe qz81 Complex (fun (x : Complex) => Real) qz82 Complex.normSq qz83) 388095849 250000 0 1 172918 172919 268435456 (ep245 (Enclosure.Complex.normSq_eq_mul_add_mul qz83) (ep250 rfl rfl)) rfl

noncomputable def ep252 := @Enclosure.Real.IsNear.of_eq (Complex.re qz79) (@HMul.hMul Real Real Real qz0 qz80 (@Inv.inv Real Real.instInv (@DFunLike.coe qz81 Complex (fun (x : Complex) => Real) qz82 Complex.normSq qz83))) Bool.false 3112533 2147483648 9 2147483648 (Enclosure.Complex.inv_re_eq_mul qz83) (@ep241 3112533 2147483648 9 2147483648 qz85 (@ep244 536870912 (ep251 rfl rfl rfl rfl rfl) rfl) rfl)

noncomputable def ep253 := @Enclosure.Real.IsNear.of_eq (Complex.im qz79) (@HMul.hMul Real Real Real qz0 (@Neg.neg Real Real.instNeg qz84) (@Inv.inv Real Real.instInv (@DFunLike.coe qz81 Complex (fun (x : Complex) => Real) qz82 Complex.normSq qz83))) Bool.true 1700480529 67108864000 4917 67108864000 (Enclosure.Complex.inv_im_eq_mul qz83)

noncomputable def ep254 := @Enclosure.Real.IsNear.mulLit_tf (@Neg.neg Real Real.instNeg qz84) (@Inv.inv Real Real.instInv (@DFunLike.coe qz81 Complex (fun (x : Complex) => Real) qz82 Complex.normSq qz83)) 157344 4000 0 1 345837 536870912 1

noncomputable def ep255 := @ep254 536870912 1700480529 67108864000 4917 67108864000 (@Enclosure.Real.IsNear.neg qz84 Bool.false 157344 4000 0 1 qz86) (@ep244 536870912 (ep251 rfl rfl rfl rfl rfl) rfl) rfl

noncomputable def ep256 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz52 (@Rat.cast Complex Complex.instRatCast (bernoulli qz74)) qz75)) qz78 0 1 0 1 1700480529 67108864000 4917 67108864000 0

noncomputable def ep257 := @Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz52 (@Rat.cast Complex Complex.instRatCast (bernoulli qz74)) qz75) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (ep236 (BSN.stirling_coeff_mk 1 1 6 Bool.false BSN.bern_real_1 rfl rfl) qz341)

noncomputable def ep258 := @Enclosure.Complex.IsNear.im_isNear qz76 Bool.false 3112533 2147483648 9 2147483648 Bool.true 1700480529 67108864000 4917 67108864000

noncomputable abbrev qz87 := (@ep239 67108864000 (BSN.zpow_one_sub_two_mul qz316 1 1 rfl rfl) (@ep240 67108864000 ep252 (ep253 ep255)))

noncomputable def ep259 := @ep234 1 1037511 1037511 8589934592 3 8589934592 (@ep235 8589934592 3 8589934592 ep237 (ep238 qz87) rfl) (@ep256 1 0 1 ep257 (ep258 qz87) rfl) rfl

noncomputable def ep260 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz52 (@Rat.cast Complex Complex.instRatCast (bernoulli qz74)) qz75)) qz78) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz52 (@Rat.cast Complex Complex.instRatCast (bernoulli qz74)) qz75)) qz77) 566826843 268435456000 1639 268435456000 0 1 0

noncomputable def ep261 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HDiv.hDiv Complex Complex Complex qz52 (@Rat.cast Complex Complex.instRatCast (bernoulli qz74)) qz75)) qz78 1 12 0 1 1700480529 67108864000 4917 67108864000 566826843

noncomputable def ep262 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz52 (@Rat.cast Complex Complex.instRatCast (bernoulli qz74)) qz75)) qz77 0 1 0 1 3112533 2147483648 9 2147483648 0

noncomputable def ep263 := @ep260 1 566826843 566826843 268435456000 1639 268435456000 (@ep261 268435456000 1639 268435456000 ep237 (ep258 qz87) rfl) (@ep262 1 0 1 ep257 (ep238 qz87) rfl) rfl

noncomputable abbrev qz88 := (@Enclosure.Complex.IsNear.mk qz277 qz277 Bool.false 0 1 0 1 Bool.false 0 1 0 1 qz288 qz288)

noncomputable def ep264 := @ep231 268435456000 (@ep232 0 1 0 1 (BSN.stirling_sum_base qz55) qz88) (ep233 (ep259 rfl) (ep263 rfl)) rfl rfl rfl rfl rfl

noncomputable def ep265 := @ep186 60698559459142937841 562949953421312000 8773217651300671935403 ep173 (ep228 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep229 Bool.true 566826843 268435456000 1639 268435456000 (BSN.stirling_sum_succ qz55 0 1 rfl) (ep264 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl

noncomputable def ep266 := @Enclosure.Complex.IsNear.of_eq (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz48 (@Nat.cast Complex Complex.instNatCast j))) (BSN.logSumC qz17 2) Bool.false 16539027808293075 2251799813685248 25000000040469 4046900000000000000 Bool.false 873549816956323 281474976710656

noncomputable abbrev qz89 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz272 qz317 qz339))

noncomputable def ep267 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz17 2) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.logSumC qz17 1) qz89) Bool.false 16539027808293075 2251799813685248 25000000040469 4046900000000000000 Bool.false 873549816956323 281474976710656 500000000040469 40469000000000000000

noncomputable def ep268 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz17 1) qz89 Bool.false 16537936886599891 4503599627370496 25000000040469 8093800000000000000 Bool.false 880702011245987 562949953421312 500000000040469 80938000000000000000 Bool.false

noncomputable def ep269 := nat_lit 148970318948997927447088752230400

noncomputable def ep270 := nat_lit 983529657533515312768642711552

noncomputable abbrev qz90 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz272 qz317 (@Nat.cast Complex Complex.instNatCast 0)))

noncomputable def ep271 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz17 1) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.logSumC qz17 0) qz90) Bool.false 16537936886599891 4503599627370496 25000000040469 8093800000000000000 Bool.false 880702011245987 562949953421312 500000000040469 80938000000000000000

noncomputable def ep272 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz17 0) qz90 Bool.false 0 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable abbrev qz344 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz65))

noncomputable def ep273 := @Enclosure.Complex.IsNear.of_eq qz90 qz344 Bool.false 16537936886599891 4503599627370496 25000000040469 8093800000000000000 Bool.false 880702011245987 562949953421312 500000000040469 80938000000000000000

noncomputable def ep274 := nat_lit 509225574067709119253138159435368783924692926416333134630255329280

noncomputable def ep275 := nat_lit 7212241311210533700336651561118682449475426019029874688609222656

noncomputable def ep276 := nat_lit 5172860895428033378821720347418384966803515117740416345047040

noncomputable def ep277 := BSN.log_dyadic_bound 8374134336 41142134336 4 3 ep274 524288 161876 ep275 ep276 216451 49516268672 32768000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 8374134336) (BSN.artanhQ 41142134336) 0 3 ep275 ep274 ep276 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep278 := @Enclosure.Real.IsNear.mulLit_ff qz67 (Real.log (Enclosure.sfrac Bool.false 24758134336 16000000)) 1 2 0 1 16537936886599891 2251799813685248 25000000040469 4046900000000000000 16537936886599891 4503599627370496 25000000040469 8093800000000000000 qz333 (BSN.isNear_log_sfrac 24758134336 16000000 16537936886599891 2251799813685248 25000000040469 4046900000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 24758134336) qz334)) Bool.false 138730269670426938441728 18889465931478580854784 1000000001618760 161876000000000000000 16537936886599891 2251799813685248 25000000040469 4046900000000000000 (BSN.log_rat_reduce_isNear 24758134336 16000000 10 49516268672 32768000000 216451 524288 24973259072661432 36028797018963968 161876 1000000000000000 rfl rfl rfl rfl (ep277 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep279 := BSN.arctan_dyadic_bound_f 1000 157344 1 0 524288 161876 0 1 1 0 1 1 3332 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 157344) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 157344) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz345 := (@Nat.cast Real Real.instNatCast 1000)

noncomputable abbrev qz346 := (@Nat.cast Real Real.instNatCast 157344)

noncomputable def ep280 := @Enclosure.Real.IsNear.subLit_ff_p qz68 (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz345 qz346)) 884279719003555 562949953421312 1 2000000000000000 3332 524288 1 161876 461741496072136032256 880702011245987 562949953421312 500000000040469 80938000000000000000 qz69 (ep279 rfl) rfl rfl

noncomputable abbrev qz91 := (@HAdd.hAdd Complex Complex Complex qz272 qz317 (@Nat.cast Complex Complex.instNatCast 0))

noncomputable abbrev qz347 := (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz65)

noncomputable def ep281 := @ep272 16537936886599891 4503599627370496 25000000040469 8093800000000000000 Bool.false 880702011245987 562949953421312 500000000040469 80938000000000000000 Bool.false 16537936886599891 16537936886599891 4503599627370496 25000000040469 8093800000000000000 Bool.false 880702011245987 880702011245987 562949953421312 500000000040469 80938000000000000000 (@Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz17 0) (Complex.mk qz14 qz14) Bool.false 0 1 0 1 Bool.false 0 1 0 1 (BSN.log_sum_c_base qz17) qz88) (ep273 (@congrArg Complex Complex qz91 qz347 Complex.log (BSN.w_shift_mk qz17 Bool.false 78672 1000 0 qz18 rfl)) (@Enclosure.Complex.IsNear.of_parts qz344 Bool.false 16537936886599891 4503599627370496 25000000040469 8093800000000000000 Bool.false 880702011245987 562949953421312 500000000040469 80938000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz344) (@HMul.hMul Real Real Real qz0 qz67 (Real.log (Enclosure.sfrac Bool.false 24758134336 16000000))) Bool.false 16537936886599891 4503599627370496 25000000040469 8093800000000000000 (Enclosure.clog_re_eq 1000 157344 4000 24758134336 16000000 rfl rfl rfl) (ep278 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz344) (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz346 qz345)) Bool.false 880702011245987 562949953421312 500000000040469 80938000000000000000 (Enclosure.clog_im_eq 1000 157344 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz346 qz345)) (@HSub.hSub Real Real Real qz318 qz68 (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz345 qz346))) Bool.false 880702011245987 562949953421312 500000000040469 80938000000000000000 (BSN.arctan_recip 157344 1000 rfl rfl) ep280)))) rfl rfl

noncomputable abbrev qz348 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz65))

noncomputable def ep282 := @Enclosure.Complex.IsNear.of_eq qz89 qz348 Bool.false 16540118729986259 4503599627370496 25000000040469 8093800000000000000 Bool.false 866397622666659 562949953421312 500000000040469 80938000000000000000

noncomputable def ep283 := nat_lit 511010496175253048548903849671054810328408001951876728491375329280

noncomputable def ep284 := nat_lit 7271433606898626709663952503323994164585133295780426728033222656

noncomputable def ep285 := nat_lit 5262452185517083339184648712131299804367051279282396505047040

noncomputable def ep286 := BSN.log_dyadic_bound 8398134336 41166134336 4 3 ep283 524288 161876 ep284 ep285 216959 49564268672 32768000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 8398134336) (BSN.artanhQ 41166134336) 0 3 ep284 ep283 ep285 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep287 := @Enclosure.Real.IsNear.mulLit_ff qz67 (Real.log (Enclosure.sfrac Bool.false 24782134336 16000000)) 1 2 0 1 16540118729986259 2251799813685248 25000000040469 4046900000000000000 16540118729986259 4503599627370496 25000000040469 8093800000000000000 qz333 (BSN.isNear_log_sfrac 24782134336 16000000 16540118729986259 2251799813685248 25000000040469 4046900000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 24782134336) qz334)) Bool.false 138748572299312572137472 18889465931478580854784 1000000001618760 161876000000000000000 16540118729986259 2251799813685248 25000000040469 4046900000000000000 (BSN.log_rat_reduce_isNear 24782134336 16000000 10 49564268672 32768000000 216959 524288 24973259072661432 36028797018963968 161876 1000000000000000 rfl rfl rfl rfl (ep286 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep288 := BSN.arctan_dyadic_bound_f 5000 157344 1 0 524288 161876 0 1 1 0 1 1 16654 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 5000) (BSN.arctanEvenQ 157344) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 5000) (BSN.arctanOddQ 157344) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz349 := (@Nat.cast Real Real.instNatCast 5000)

noncomputable def ep289 := @Enclosure.Real.IsNear.subLit_ff_p qz68 (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz349 qz346)) 884279719003555 562949953421312 1 2000000000000000 16654 524288 1 161876 454241876792657313792 866397622666659 562949953421312 500000000040469 80938000000000000000 qz69 (ep288 rfl) rfl rfl

noncomputable abbrev qz92 := (@HAdd.hAdd Complex Complex Complex qz272 qz317 qz339)

noncomputable abbrev qz350 := (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz65)

noncomputable def ep290 := @ep268 16540118729986259 4503599627370496 25000000040469 8093800000000000000 Bool.false 866397622666659 562949953421312 500000000040469 80938000000000000000 Bool.false ep269 16539027808293075 2251799813685248 25000000040469 4046900000000000000 Bool.false ep270 873549816956323 281474976710656 500000000040469 40469000000000000000 (ep271 (BSN.log_sum_c_succ qz17 0 1 rfl) (ep281 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep282 (@congrArg Complex Complex qz92 qz350 Complex.log (BSN.w_shift_mk qz17 Bool.false 78672 1000 1 qz18 rfl)) (@Enclosure.Complex.IsNear.of_parts qz348 Bool.false 16540118729986259 4503599627370496 25000000040469 8093800000000000000 Bool.false 866397622666659 562949953421312 500000000040469 80938000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz348) (@HMul.hMul Real Real Real qz0 qz67 (Real.log (Enclosure.sfrac Bool.false 24782134336 16000000))) Bool.false 16540118729986259 4503599627370496 25000000040469 8093800000000000000 (Enclosure.clog_re_eq 5000 157344 4000 24782134336 16000000 rfl rfl rfl) (ep287 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz348) (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz346 qz349)) Bool.false 866397622666659 562949953421312 500000000040469 80938000000000000000 (Enclosure.clog_im_eq 5000 157344 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz346 qz349)) (@HSub.hSub Real Real Real qz318 qz68 (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz349 qz346))) Bool.false 866397622666659 562949953421312 500000000040469 80938000000000000000 (BSN.arctan_recip 157344 5000 rfl rfl) ep289)))) rfl rfl

noncomputable def ep291 := @ep179 ep173 Bool.false 16539027808293075 2251799813685248 25000000040469 4046900000000000000 Bool.false 873549816956323 281474976710656 500000000040469 40469000000000000000 Bool.true ep180 139134128752343920359 2251799813685248000 342659600181896583894631 ep177 Bool.false ep181 58951459825230291841 562949953421312000 9592417651366976345003 ep173 (@ep182 2251799813685248000 334467600168635701974631 ep177 Bool.false 60698559459142937841 562949953421312000 8773217651300671935403 ep173 (BSN.logGammaStirling_unfold 1 qz55) (ep265 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (@ep266 500000000040469 40469000000000000000 (BSN.log_sum_c_eq qz17 2) (ep267 (BSN.log_sum_c_succ qz17 1 2 rfl) (ep290 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)))

noncomputable abbrev qz93 := (@HDiv.hDiv Real Real Real qz269 qz279 (2 : Real))

noncomputable def ep292 := @Enclosure.Real.IsNear.mulLit_ff qz93 (Real.log Real.pi) 78672 2000 0 1 75021 65536 1 131072 368878257 8192000 4917 16384000 (@Enclosure.Real.IsNear.of_eq qz93 (Enclosure.sfrac Bool.false 78672 2000) Bool.false 78672 2000 0 1 (BSN.t_half_eq qz17 Bool.false 78672 1000 qz18) (Enclosure.Real.IsNear.const Bool.false 78672 2000)) EMRow21.d5 rfl

noncomputable def ep293 := @ep175 4917 16384000 ep176 33602339024902562689 562949953421312000 29491024951366976345003 ep173 (@ep178 9592417651366976345003 ep173 (ep291 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) ep292 rfl rfl

noncomputable def ep294 := nat_lit 32550697355620047140042237762604488541043605199518538049266878872677420892160

noncomputable def ep295 := nat_lit 65315075109354681604733012467389478406872153365733984620088367526703005696

noncomputable def ep296 := nat_lit 85146078190732596834655340691397887023407839655194506534885492071492868898816

noncomputable def ep297 := BSN.sin_dyadic_bound_f 1686074184 1073741824 3 2 524288 162035 ep294 ep64 ep295 ep296 ep66 ep295 524287 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1686074184) qz285 0 2 ep294 ep64 ep295 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1686074184) qz286 0 2 ep296 ep66 ep295 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz351 := (@Nat.cast Real Real.instNatCast 9444732965739290427392)

noncomputable def ep298 := @ep172 524288 Bool.true 524287 524288 1 80938 (@ep174 3911827 65536 235 524288 ep293 rfl) (Enclosure.sfrac_false_div 3911827 65536) (BSN.cos_reduce1 qz319 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 14830865369959009091584) qz351) 226375608064910080 72057594037927936 Bool.false 524287 524288 9 1000000000000000 161876 80938 (BSN.sin_reduce_arg_pos_rat_q1 3911827 65536 226375608064910080 72057594037927936 9 14830865369959009091584 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 524287 524288 14830865369959009091584 9444732965739290427392 1686074184 1073741824 162035 161876 (ep297 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep299 := nat_lit 2552049054794272210944000

noncomputable def ep300 := nat_lit 51962606130905824426249319

noncomputable def ep301 := nat_lit 9388988472588127464062976000

noncomputable abbrev qz94 := qz273

noncomputable abbrev qz95 := qz274

noncomputable abbrev qz352 := (@HPow.hPow Complex Complex Complex qz480 (@Nat.cast Complex Complex.instNatCast 16) qz481)

noncomputable abbrev qz96 := qz352

noncomputable abbrev qz353 := (@Nat.cast Complex Complex.instNatCast 16)

noncomputable abbrev qz97 := (@HAdd.hAdd Complex Complex Complex qz272 (@HDiv.hDiv Complex Complex Complex qz323 qz353 (@HSub.hSub Complex Complex Complex qz315 qz271 (1 : Complex))) qz322)

noncomputable abbrev qz98 := (@instHSub Nat instSubNat)

noncomputable abbrev qz354 := qz493

noncomputable abbrev qz99 := qz354

noncomputable abbrev qz100 := qz353

noncomputable def ep302 := @Enclosure.Complex.IsNear.of_eq (zetaApproximant qz6 1 16) (@HAdd.hAdd Complex Complex Complex qz5 (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 16, @HPow.hPow Complex Complex Complex qz94 (@Nat.cast Complex Complex.instNatCast n) qz95) (@HMul.hMul Complex Complex Complex qz45 qz96 (@HAdd.hAdd Complex Complex Complex qz5 qz97 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz53 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz53 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz99 qz100 (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1))))))) Bool.false 269784368834693151885473 204163924383541776875520 ep169

noncomputable def ep303 := @Enclosure.Complex.IsNear.addLitP (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 16, @HPow.hPow Complex Complex Complex qz94 (@Nat.cast Complex Complex.instNatCast n) qz95) (@HMul.hMul Complex Complex Complex qz45 qz96 (@HAdd.hAdd Complex Complex Complex qz5 qz97 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz53 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz53 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz99 qz100 (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1)))))) Bool.false 192225072751 137438953472 14905199227585 2781008504029184

noncomputable def ep304 := nat_lit 36191881411720867219381037

noncomputable def ep305 := nat_lit 206557746396938804209385472000

noncomputable def ep306 := nat_lit 18140265042704523815798509

noncomputable def ep307 := nat_lit 103278873198469402104692736000

noncomputable def ep308 := nat_lit 37078881315744278961384552719712256

noncomputable def ep309 := nat_lit 901972099005961642963003267612672

noncomputable def ep310 := @ep303 Bool.true 8007962613 68719476736 29805606237597 5562017008058368 Bool.true 15763681600304712814687 204163924383541776875520 ep304 ep305 Bool.false 284267899672392502962923 ep299 ep306 ep307 Bool.false ep308 269784368834693151885473 204163924383541776875520 ep169 ep170 Bool.true ep309 13125421523086866989077 ep299

noncomputable def ep311 := @Enclosure.Complex.IsNear.of_eq (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 16, @HPow.hPow Complex Complex Complex qz94 (@Nat.cast Complex Complex.instNatCast n) qz95) (BSN.headSumC qz6 16) Bool.false 192225072751 137438953472 14905199227585 2781008504029184 Bool.true 8007962613 68719476736 29805606237597

noncomputable abbrev qz101 := (@HPow.hPow Complex Complex Complex qz273 (@Nat.cast Complex Complex.instNatCast 15) qz274)

noncomputable def ep312 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz6 16) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz6 15) qz101) Bool.false 192225072751 137438953472 14905199227585 2781008504029184 Bool.true 8007962613 68719476736 29805606237597 5562017008058368

noncomputable def ep313 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz6 15) qz101 Bool.false 162558788843 137438953472 14193401030817 2781008504029184 Bool.true 17744657159 68719476736 28385056997885 5562017008058368 Bool.false

noncomputable abbrev qz102 := (@HPow.hPow Complex Complex Complex qz273 (@Nat.cast Complex Complex.instNatCast 14) qz274)

noncomputable def ep314 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz6 15) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz6 14) qz102) Bool.false 162558788843 137438953472 14193401030817 2781008504029184 Bool.true 17744657159 68719476736 28385056997885 5562017008058368

noncomputable def ep315 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz6 14) qz102 Bool.false 254404814431 274877906944 53818773920107 11124034016116736 Bool.true 51063371027 274877906944 53829954857303 11124034016116736 Bool.false

noncomputable abbrev qz103 := (@HPow.hPow Complex Complex Complex qz273 (@Nat.cast Complex Complex.instNatCast 13) qz274)

noncomputable def ep316 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz6 14) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz6 13) qz103) Bool.false 254404814431 274877906944 53818773920107 11124034016116736 Bool.true 51063371027 274877906944 53829954857303 11124034016116736

noncomputable def ep317 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz6 13) qz103 Bool.false 98733332697 137438953472 1153584957667 252818954911744 Bool.true 366698343 274877906944 4615514193221 1011275819646976 Bool.false

noncomputable abbrev qz104 := (@HPow.hPow Complex Complex Complex qz273 (@Nat.cast Complex Complex.instNatCast 12) qz274)

noncomputable def ep318 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz6 13) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz6 12) qz104) Bool.false 98733332697 137438953472 1153584957667 252818954911744 Bool.true 366698343 274877906944 4615514193221 1011275819646976

noncomputable def ep319 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz6 12) qz104 Bool.false 137485089157 274877906944 47578282845651 11124034016116736 Bool.false 51582332417 274877906944 47593348644971 11124034016116736 Bool.false

noncomputable abbrev qz105 := (@HPow.hPow Complex Complex Complex qz273 (@Nat.cast Complex Complex.instNatCast 11) qz274)

noncomputable def ep320 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz6 12) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz6 11) qz105) Bool.false 137485089157 274877906944 47578282845651 11124034016116736 Bool.false 51582332417 274877906944 47593348644971 11124034016116736

noncomputable def ep321 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz6 11) qz105 Bool.false 13888699621 68719476736 502804864441 126409477455872 Bool.false 64085116685 274877906944 4025424332053 1011275819646976 Bool.false

noncomputable abbrev qz106 := (@HPow.hPow Complex Complex Complex qz273 (@Nat.cast Complex Complex.instNatCast 10) qz274)

noncomputable def ep322 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz6 11) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz6 10) qz106) Bool.false 13888699621 68719476736 502804864441 126409477455872 Bool.false 64085116685 274877906944 4025424332053 1011275819646976

noncomputable def ep323 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz6 10) qz106 Bool.false 6667550867 137438953472 20382227734885 5562017008058368 Bool.true 2974309915 68719476736 10197263475979 2781008504029184 Bool.false

noncomputable abbrev qz107 := (@HPow.hPow Complex Complex Complex qz273 (@Nat.cast Complex Complex.instNatCast 9) qz274)

noncomputable def ep324 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz6 10) (@HAdd.hAdd Complex Complex Complex qz5 qz4 qz107) Bool.false 6667550867 137438953472 20382227734885 5562017008058368 Bool.true 2974309915 68719476736 10197263475979 2781008504029184

noncomputable def ep325 := @Enclosure.Complex.IsNear.addLitP qz4 qz107 Bool.false 104720946353 274877906944 3371220040371 1011275819646976 Bool.true 18526874065 274877906944 3375240495719 1011275819646976 Bool.true

noncomputable abbrev qz355 := (@Nat.cast Real Real.instNatCast 9)

noncomputable abbrev qz108 := (@Inv.inv Real Real.instInv (Real.sqrt qz355))

noncomputable abbrev qz109 := (@HMul.hMul Real Real Real qz266 qz279 (Real.log (Enclosure.sfrac Bool.false 9 1)))

noncomputable def ep326 := @Enclosure.Complex.IsNear.of_eq qz107 (Complex.mk (@HMul.hMul Real Real Real qz0 qz108 (Real.cos qz109)) (@HMul.hMul Real Real Real qz0 qz108 (@Neg.neg Real Real.instNeg (Real.sin qz109)))) Bool.true 91385844619 274877906944 3681035025689 11124034016116736 Bool.false 6629634405 274877906944 3661408451007 11124034016116736 (BSN.cpow_neg_s_mk qz17 78672 1000 9 qz18 rfl)

noncomputable abbrev qz356 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 9) qz19)

noncomputable def ep327 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz355) 1572865 524288 1 524288 87381 87382 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz355) (Real.sqrt qz356) Bool.false 1572865 524288 1 524288 (BSN.sqrt_natCast_div_one 9) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz356) Bool.false 1572865 524288 1 524288 1572865 524288 1 524288 (BSN.sqrt_enclosure 9 1 786432 786433 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep328 := BSN.log_dyadic_bound 1 17 2 1 867 262144 80938 1 1 30876 18 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 1) (BSN.artanhQ 17) 0 1 1 867 1 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz110 := (Real.log (Enclosure.sfrac Bool.false 9 1))

noncomputable def ep329 := @Enclosure.Real.IsNear.mulLit_ff qz17 qz110 78672 1000 0 1 9895417793173221 4503599627370496 500000000121407 40469000000000000000 48655769289032727657 281474976710656000 223500000054268929 229937500000000000000 qz22 (BSN.isNear_log_sfrac 9 1 9895417793173221 4503599627370496 500000000121407 40469000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz356) Bool.false 20752195215788806766592 9444732965739290427392 1000000000242814 80938000000000000000 9895417793173221 4503599627370496 500000000121407 40469000000000000000 (BSN.log_rat_reduce_isNear 9 1 3 18 16 30876 262144 24973259072661432 36028797018963968 80938 1000000000000000 rfl rfl rfl rfl (ep328 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep330 := BSN.cos_dyadic_bound_f 77760298 1073741824 1 0 524288 162035 0 1 1 0 1 1 522913 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 77760298) qz281 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 77760298) qz282 0 0 rfl) rfl rfl

noncomputable abbrev qz357 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 5664277) (@Nat.cast Real Real.instNatCast 32768))

noncomputable abbrev qz358 := (@Nat.cast Real Real.instNatCast 4722366482869645213696)

noncomputable def ep331 := @Enclosure.Real.IsNear.cos_image qz109 qz357 Bool.false 5664277 32768 511 524288 Bool.true 522913 524288 1 80938 (@Enclosure.Real.IsNear.recentre' qz109 Bool.false 48655769289032727657 281474976710656000 223500000054268929 229937500000000000000 5664277 32768 511 524288 (ep329 rfl) rfl) (Enclosure.sfrac_false_div 5664277 32768) (BSN.cos_reduce2 qz357 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 341993410937585926144) qz358) 226375608064910080 72057594037927936 Bool.false 522913 524288 27 1000000000000000 161876 80938 (BSN.sin_reduce_arg_pos_rat_q2 5664277 32768 226375608064910080 72057594037927936 27 341993410937585926144 4722366482869645213696 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 522913 524288 341993410937585926144 4722366482869645213696 77760298 1073741824 162035 161876 (ep330 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep332 := BSN.sin_dyadic_bound_f 77760298 1073741824 1 0 524288 162035 0 1 1 0 1 1 37935 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 77760298) qz285 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 77760298) qz286 0 0 rfl) rfl rfl

noncomputable def ep333 := @Enclosure.Real.IsNear.sin_image qz109 qz357 Bool.false 5664277 32768 511 524288 Bool.true 37935 524288 1 80938 (@Enclosure.Real.IsNear.recentre' qz109 Bool.false 48655769289032727657 281474976710656000 223500000054268929 229937500000000000000 5664277 32768 511 524288 (ep329 rfl) rfl) (Enclosure.sfrac_false_div 5664277 32768) (BSN.sin_reduce2 qz357 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 341993410937585926144) qz358) 226375608064910080 72057594037927936 Bool.false 37935 524288 27 1000000000000000 161876 80938 (BSN.sin_reduce_arg_pos_rat_q2 5664277 32768 226375608064910080 72057594037927936 27 341993410937585926144 4722366482869645213696 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 37935 524288 341993410937585926144 4722366482869645213696 77760298 1073741824 162035 161876 (ep332 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz359 := (@Enclosure.Real.IsNear.recentre' qz108 Bool.false 174763 524288 1 524288 174763 524288 1 524288 (ep327 rfl rfl) rfl)

noncomputable def ep334 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz108 (Real.cos qz109)) (@HMul.hMul Real Real Real qz0 qz108 (@Neg.neg Real Real.instNeg (Real.sin qz109))) Bool.true 91385844619 274877906944 3681035025689 11124034016116736 Bool.false 6629634405 274877906944 3661408451007 11124034016116736 (@Enclosure.Real.IsNear.mulLit_ft qz108 (Real.cos qz109) 174763 524288 1 524288 522913 524288 20941803 21217411072 91385844619 274877906944 3681035025689 11124034016116736 qz359 (@Enclosure.Real.IsNear.recentre' (Real.cos qz109) Bool.true 522913 524288 41883606 42434822144 522913 524288 20941803 21217411072 (ep331 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz108 (@Neg.neg Real Real.instNeg (Real.sin qz109)) 174763 524288 1 524288 37935 524288 20941803 21217411072 6629634405 274877906944 3661408451007 11124034016116736 qz359 (@Enclosure.Real.IsNear.neg (Real.sin qz109) Bool.true 37935 524288 20941803 21217411072 (@Enclosure.Real.IsNear.recentre' (Real.sin qz109) Bool.true 37935 524288 41883606 42434822144 37935 524288 20941803 21217411072 (ep333 rfl rfl) rfl)) rfl)

noncomputable def ep335 := @ep325 91385844619 274877906944 3681035025689 11124034016116736 Bool.false 6629634405 274877906944 3661408451007 11124034016116736 Bool.false 3665524853527225040896 6667550867 137438953472 20382227734885 5562017008058368 Bool.true 3270288336151946199040 2974309915 68719476736 10197263475979 2781008504029184 EMRow21.d6 (ep326 ep334) rfl rfl

noncomputable abbrev qz360 := (@Nat.cast Real Real.instNatCast 10)

noncomputable abbrev qz111 := (@Inv.inv Real Real.instInv (Real.sqrt qz360))

noncomputable abbrev qz112 := (@HMul.hMul Real Real Real qz266 qz279 (Real.log (Enclosure.sfrac Bool.false 10 1)))

noncomputable def ep336 := @Enclosure.Complex.IsNear.of_eq qz106 (Complex.mk (@HMul.hMul Real Real Real qz0 qz111 (Real.cos qz112)) (@HMul.hMul Real Real Real qz0 qz111 (@Neg.neg Real Real.instNeg (Real.sin qz112)))) Bool.false 21109848375 137438953472 1741186300519 5562017008058368 Bool.false 75982356345 274877906944 3490613748667 11124034016116736 (BSN.cpow_neg_s_mk qz17 78672 1000 10 qz18 rfl)

noncomputable abbrev qz361 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 10) qz19)

noncomputable def ep337 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz360) 1657945 524288 1 524288 82897 82898 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz360) (Real.sqrt qz361) Bool.false 1657945 524288 1 524288 (BSN.sqrt_natCast_div_one 10) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz361) Bool.false 1657945 524288 1 524288 1657945 524288 1 524288 (BSN.sqrt_enclosure 10 1 828972 828973 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep338 := BSN.log_dyadic_bound 2 18 3 2 1574640 262144 80938 6528 48 58495 20 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 2) (BSN.artanhQ 18) 0 2 6528 1574640 48 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz113 := (Real.log (Enclosure.sfrac Bool.false 10 1))

noncomputable def ep339 := @Enclosure.Real.IsNear.mulLit_ff qz17 qz113 78672 1000 0 1 10369908600166117 4503599627370496 500000000121407 40469000000000000000 50988840587016797289 281474976710656000 223500000054268929 229937500000000000000 qz22 (BSN.isNear_log_sfrac 10 1 10369908600166117 4503599627370496 500000000121407 40469000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz361) Bool.false 21747274560655572598784 9444732965739290427392 1000000000242814 80938000000000000000 10369908600166117 4503599627370496 500000000121407 40469000000000000000 (BSN.log_rat_reduce_isNear 10 1 3 20 16 58495 262144 24973259072661432 36028797018963968 80938 1000000000000000 rfl rfl rfl rfl (ep338 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep340 := nat_lit 87947405694499351054446708846600625

noncomputable def ep341 := BSN.sin_dyadic_bound_f 544572565 1073741824 2 1 524288 162035 ep340 ep86 ep340 ep340 ep87 ep340 254650 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 544572565) qz285 0 1 ep340 ep86 ep340 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 544572565) qz286 0 1 ep340 ep87 ep340 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz362 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 23743529) qz485)

noncomputable def ep342 := @Enclosure.Real.IsNear.cos_image qz112 qz362 Bool.false 23743529 131072 511 524288 Bool.false 254650 524288 1 80938 (@Enclosure.Real.IsNear.recentre' qz112 Bool.false 50988840587016797289 281474976710656000 223500000054268929 229937500000000000000 23743529 131072 511 524288 (ep339 rfl) rfl) (Enclosure.sfrac_false_div 23743529 131072) (BSN.cos_reduce3 qz362 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 9580221886890285989888) qz296) 226375608064910080 72057594037927936 Bool.false 254650 524288 28 1000000000000000 161876 80938 (BSN.sin_reduce_arg_pos_rat_q3 23743529 131072 226375608064910080 72057594037927936 28 9580221886890285989888 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 254650 524288 9580221886890285989888 18889465931478580854784 544572565 1073741824 162035 161876 (ep341 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep343 := BSN.cos_dyadic_bound_f 544572565 1073741824 2 1 524288 162035 ep340 ep90 ep340 ep340 ep91 ep340 458291 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 544572565) qz281 0 1 ep340 ep90 ep340 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 544572565) qz282 0 1 ep340 ep91 ep340 rfl rfl rfl rfl) rfl rfl

noncomputable def ep344 := @Enclosure.Real.IsNear.sin_image qz112 qz362 Bool.false 23743529 131072 511 524288 Bool.true 458291 524288 1 80938 (@Enclosure.Real.IsNear.recentre' qz112 Bool.false 50988840587016797289 281474976710656000 223500000054268929 229937500000000000000 23743529 131072 511 524288 (ep339 rfl) rfl) (Enclosure.sfrac_false_div 23743529 131072) (BSN.sin_reduce3 qz362 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 9580221886890285989888) qz296) 226375608064910080 72057594037927936 Bool.false 458291 524288 28 1000000000000000 161876 80938 (BSN.sin_reduce_arg_pos_rat_q3 23743529 131072 226375608064910080 72057594037927936 28 9580221886890285989888 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 458291 524288 9580221886890285989888 18889465931478580854784 544572565 1073741824 162035 161876 (ep343 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz363 := (@Enclosure.Real.IsNear.recentre' qz111 Bool.false 165795 524288 1 524288 165795 524288 1 524288 (ep337 rfl rfl) rfl)

noncomputable def ep345 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz111 (Real.cos qz112)) (@HMul.hMul Real Real Real qz0 qz111 (@Neg.neg Real Real.instNeg (Real.sin qz112))) Bool.false 21109848375 137438953472 1741186300519 5562017008058368 Bool.false 75982356345 274877906944 3490613748667 11124034016116736 (@Enclosure.Real.IsNear.mulLit_ff qz111 (Real.cos qz112) 165795 524288 1 524288 127325 262144 20941803 21217411072 21109848375 137438953472 1741186300519 5562017008058368 qz363 (@Enclosure.Real.IsNear.recentre' (Real.cos qz112) Bool.false 254650 524288 41883606 42434822144 127325 262144 20941803 21217411072 (ep342 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz111 (@Neg.neg Real Real.instNeg (Real.sin qz112)) 165795 524288 1 524288 458291 524288 20941803 21217411072 75982356345 274877906944 3490613748667 11124034016116736 qz363 (@Enclosure.Real.IsNear.neg (Real.sin qz112) Bool.true 458291 524288 20941803 21217411072 (@Enclosure.Real.IsNear.recentre' (Real.sin qz112) Bool.true 458291 524288 41883606 42434822144 458291 524288 20941803 21217411072 (ep344 rfl rfl) rfl)) rfl)

noncomputable def ep346 := @ep323 21109848375 137438953472 1741186300519 5562017008058368 Bool.false 75982356345 274877906944 3490613748667 11124034016116736 Bool.false 3817696681994406068224 13888699621 68719476736 502804864441 126409477455872 Bool.false 4403895685158702940160 64085116685 274877906944 4025424332053 1011275819646976 (ep324 (BSN.head_sum_c_succ qz6 9 10 rfl rfl) (ep335 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep336 ep345) rfl rfl

noncomputable abbrev qz364 := (@Nat.cast Real Real.instNatCast 11)

noncomputable abbrev qz114 := (@Inv.inv Real Real.instInv (Real.sqrt qz364))

noncomputable abbrev qz115 := (@HMul.hMul Real Real Real qz266 qz279 (Real.log (Enclosure.sfrac Bool.false 11 1)))

noncomputable def ep347 := @Enclosure.Complex.IsNear.of_eq qz105 (Complex.mk (@HMul.hMul Real Real Real qz0 qz114 (Real.cos qz115)) (@HMul.hMul Real Real Real qz0 qz114 (@Neg.neg Real Real.instNeg (Real.sin qz115)))) Bool.false 81930290673 274877906944 256265751911 855694924316672 Bool.true 3125696067 68719476736 63724634469 213923731079168 (BSN.cpow_neg_s_mk qz17 78672 1000 11 qz18 rfl)

noncomputable abbrev qz365 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 11) qz19)

noncomputable def ep348 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz364) 1738867 524288 1 524288 79039 79040 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz364) (Real.sqrt qz365) Bool.false 1738867 524288 1 524288 (BSN.sqrt_natCast_div_one 11) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz365) Bool.false 1738867 524288 1 524288 1738867 524288 1 524288 (BSN.sqrt_enclosure 11 1 869433 869434 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep349 := BSN.log_dyadic_bound 3 19 4 3 4939817505 262144 80938 41676111 10935 83480 22 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 3) (BSN.artanhQ 19) 0 3 41676111 4939817505 10935 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz116 := (Real.log (Enclosure.sfrac Bool.false 11 1))

noncomputable def ep350 := @Enclosure.Real.IsNear.mulLit_ff qz17 qz116 78672 1000 0 1 10799147631728357 4503599627370496 500000000121407 40469000000000000000 53099408905208331369 281474976710656000 223500000054268929 229937500000000000000 qz22 (BSN.isNear_log_sfrac 11 1 10799147631728357 4503599627370496 500000000121407 40469000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz365) Bool.false 22647454054174387339264 9444732965739290427392 1000000000242814 80938000000000000000 10799147631728357 4503599627370496 500000000121407 40469000000000000000 (BSN.log_rat_reduce_isNear 11 1 3 22 16 83480 262144 24973259072661432 36028797018963968 80938 1000000000000000 rfl rfl rfl rfl (ep349 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep351 := nat_lit 699068561411803318258405212160000

noncomputable def ep352 := BSN.cos_dyadic_bound_f 162603520 1073741824 2 1 524288 162035 ep351 ep90 ep351 ep351 ep91 ep351 518287 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 162603520) qz281 0 1 ep351 ep90 ep351 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 162603520) qz282 0 1 ep351 ep91 ep351 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz366 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 24726339) qz485)

noncomputable def ep353 := @Enclosure.Real.IsNear.cos_image qz115 qz366 Bool.false 24726339 131072 511 524288 Bool.false 518287 524288 1 80938 (@Enclosure.Real.IsNear.recentre' qz115 Bool.false 53099408905208331369 281474976710656000 223500000054268929 229937500000000000000 24726339 131072 511 524288 (ep350 rfl) rfl) (Enclosure.sfrac_false_div 24726339 131072) (BSN.cos_reduce0 qz366 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 2860551378302725521408) qz296) 226375608064910080 72057594037927936 Bool.false 518287 524288 30 1000000000000000 161876 80938 (BSN.sin_reduce_arg_pos_rat_q0 24726339 131072 226375608064910080 72057594037927936 30 2860551378302725521408 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 518287 524288 2860551378302725521408 18889465931478580854784 162603520 1073741824 162035 161876 (ep352 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep354 := BSN.sin_dyadic_bound_f 162603520 1073741824 1 0 524288 162035 0 1 1 0 1 1 79092 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 162603520) qz285 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 162603520) qz286 0 0 rfl) rfl rfl

noncomputable def ep355 := @Enclosure.Real.IsNear.sin_image qz115 qz366 Bool.false 24726339 131072 511 524288 Bool.false 79092 524288 1 80938 (@Enclosure.Real.IsNear.recentre' qz115 Bool.false 53099408905208331369 281474976710656000 223500000054268929 229937500000000000000 24726339 131072 511 524288 (ep350 rfl) rfl) (Enclosure.sfrac_false_div 24726339 131072) (BSN.sin_reduce0 qz366 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 2860551378302725521408) qz296) 226375608064910080 72057594037927936 Bool.false 79092 524288 30 1000000000000000 161876 80938 (BSN.sin_reduce_arg_pos_rat_q0 24726339 131072 226375608064910080 72057594037927936 30 2860551378302725521408 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 79092 524288 2860551378302725521408 18889465931478580854784 162603520 1073741824 162035 161876 (ep354 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz367 := (@Enclosure.Real.IsNear.recentre' qz114 Bool.false 158079 524288 1 524288 158079 524288 1 524288 (ep348 rfl rfl) rfl)

noncomputable def ep356 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz114 (Real.cos qz115)) (@HMul.hMul Real Real Real qz0 qz114 (@Neg.neg Real Real.instNeg (Real.sin qz115))) Bool.false 81930290673 274877906944 256265751911 855694924316672 Bool.true 3125696067 68719476736 63724634469 213923731079168 (@Enclosure.Real.IsNear.mulLit_ff qz114 (Real.cos qz115) 158079 524288 1 524288 518287 524288 20941803 21217411072 81930290673 274877906944 256265751911 855694924316672 qz367 (@Enclosure.Real.IsNear.recentre' (Real.cos qz115) Bool.false 518287 524288 41883606 42434822144 518287 524288 20941803 21217411072 (ep353 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz114 (@Neg.neg Real Real.instNeg (Real.sin qz115)) 158079 524288 1 524288 19773 131072 20941803 21217411072 3125696067 68719476736 63724634469 213923731079168 qz367 (@Enclosure.Real.IsNear.neg (Real.sin qz115) Bool.false 19773 131072 20941803 21217411072 (@Enclosure.Real.IsNear.recentre' (Real.sin qz115) Bool.false 79092 524288 41883606 42434822144 19773 131072 20941803 21217411072 (ep355 rfl rfl) rfl)) rfl)

noncomputable def ep357 := @ep321 81930290673 274877906944 256265751911 855694924316672 Bool.true 3125696067 68719476736 63724634469 213923731079168 Bool.false 9447903385871347351552 137485089157 274877906944 47578282845651 11124034016116736 Bool.false 3544710892518650150912 51582332417 274877906944 47593348644971 11124034016116736 (ep322 (BSN.head_sum_c_succ qz6 10 11 rfl rfl) (ep346 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep347 ep356) rfl rfl

noncomputable abbrev qz368 := (@Nat.cast Real Real.instNatCast 12)

noncomputable abbrev qz117 := (@Inv.inv Real Real.instInv (Real.sqrt qz368))

noncomputable abbrev qz118 := (@HMul.hMul Real Real Real qz266 qz279 (Real.log (Enclosure.sfrac Bool.false 12 1)))

noncomputable def ep358 := @Enclosure.Complex.IsNear.of_eq qz104 (Complex.mk (@HMul.hMul Real Real Real qz0 qz117 (Real.cos qz118)) (@HMul.hMul Real Real Real qz0 qz117 (@Neg.neg Real Real.instNeg (Real.sin qz118)))) Bool.false 59981576237 274877906944 3179455291697 11124034016116736 Bool.true 6493628845 34359738368 794326870115 2781008504029184 (BSN.cpow_neg_s_mk qz17 78672 1000 12 qz18 rfl)

noncomputable abbrev qz369 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 12) qz19)

noncomputable def ep359 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz368) 1816187 524288 1 524288 75674 75675 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz368) (Real.sqrt qz369) Bool.false 1816187 524288 1 524288 (BSN.sqrt_natCast_div_one 12) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz369) Bool.false 1816187 524288 1 524288 1816187 524288 1 524288 (BSN.sqrt_enclosure 12 1 908093 908094 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep360 := BSN.log_dyadic_bound 4 20 4 3 6720000000 262144 80938 91811840 61440 106290 24 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 4) (BSN.artanhQ 20) 0 3 91811840 6720000000 61440 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz119 := (Real.log (Enclosure.sfrac Bool.false 12 1))

noncomputable def ep361 := @Enclosure.Real.IsNear.mulLit_ff qz17 qz119 78672 1000 0 1 11191020447815397 4503599627370496 500000000121407 40469000000000000000 55026247541908307049 281474976710656000 223500000054268929 229937500000000000000 qz22 (BSN.isNear_log_sfrac 12 1 11191020447815397 4503599627370496 500000000121407 40469000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz369) Bool.false 23469270914176955449344 9444732965739290427392 1000000000242814 80938000000000000000 11191020447815397 4503599627370496 500000000121407 40469000000000000000 (BSN.log_rat_reduce_isNear 12 1 3 24 16 106290 262144 24973259072661432 36028797018963968 80938 1000000000000000 rfl rfl rfl rfl (ep360 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep362 := nat_lit 770510441335267017047833376038771811492369449827224282467126160537331402721

noncomputable def ep363 := nat_lit 119016002149751401647364345675458314858112547928115954099222880594921441

noncomputable def ep364 := nat_lit 2311293292001501548340205399424964517847392124385816615493180035850804365281

noncomputable def ep365 := BSN.cos_dyadic_bound_f 766391483 1073741824 3 2 524288 162035 ep362 ep57 ep363 ep364 ep60 ep363 396313 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 766391483) qz281 0 2 ep362 ep57 ep363 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 766391483) qz282 0 2 ep364 ep60 ep363 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz370 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 102494373) qz27)

noncomputable def ep366 := @Enclosure.Real.IsNear.cos_image qz118 qz370 Bool.false 102494373 524288 255 262144 Bool.false 396313 524288 1 80938 (@Enclosure.Real.IsNear.recentre' qz118 Bool.false 55026247541908307049 281474976710656000 223500000054268929 229937500000000000000 102494373 524288 255 262144 (ep361 rfl) rfl) (Enclosure.sfrac_false_div 102494373 524288) (BSN.cos_reduce0 qz370 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 53930006271112612151296) qz29) 226375608064910080 72057594037927936 Bool.false 396313 524288 31 1000000000000000 161876 80938 (BSN.sin_reduce_arg_pos_rat_q0 102494373 524288 226375608064910080 72057594037927936 31 53930006271112612151296 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 396313 524288 53930006271112612151296 75557863725914323419136 766391483 1073741824 162035 161876 (ep365 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep367 := nat_lit 344986959390860746267501987955825521

noncomputable def ep368 := BSN.sin_dyadic_bound_f 766391483 1073741824 2 1 524288 162035 ep367 ep86 ep367 ep367 ep87 ep367 343240 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 766391483) qz285 0 1 ep367 ep86 ep367 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 766391483) qz286 0 1 ep367 ep87 ep367 rfl rfl rfl rfl) rfl rfl

noncomputable def ep369 := @Enclosure.Real.IsNear.sin_image qz118 qz370 Bool.false 102494373 524288 255 262144 Bool.false 343240 524288 1 80938 (@Enclosure.Real.IsNear.recentre' qz118 Bool.false 55026247541908307049 281474976710656000 223500000054268929 229937500000000000000 102494373 524288 255 262144 (ep361 rfl) rfl) (Enclosure.sfrac_false_div 102494373 524288) (BSN.sin_reduce0 qz370 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 53930006271112612151296) qz29) 226375608064910080 72057594037927936 Bool.false 343240 524288 31 1000000000000000 161876 80938 (BSN.sin_reduce_arg_pos_rat_q0 102494373 524288 226375608064910080 72057594037927936 31 53930006271112612151296 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 343240 524288 53930006271112612151296 75557863725914323419136 766391483 1073741824 162035 161876 (ep368 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz371 := (@Enclosure.Real.IsNear.recentre' qz117 Bool.false 151349 524288 1 524288 151349 524288 1 524288 (ep359 rfl rfl) rfl)

noncomputable def ep370 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz117 (Real.cos qz118)) (@HMul.hMul Real Real Real qz0 qz117 (@Neg.neg Real Real.instNeg (Real.sin qz118))) Bool.false 59981576237 274877906944 3179455291697 11124034016116736 Bool.true 6493628845 34359738368 794326870115 2781008504029184 (@Enclosure.Real.IsNear.mulLit_ff qz117 (Real.cos qz118) 151349 524288 1 524288 396313 524288 10450667 10608705536 59981576237 274877906944 3179455291697 11124034016116736 qz371 (@Enclosure.Real.IsNear.recentre' (Real.cos qz118) Bool.false 396313 524288 20901334 21217411072 396313 524288 10450667 10608705536 (ep366 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz117 (@Neg.neg Real Real.instNeg (Real.sin qz118)) 151349 524288 1 524288 42905 65536 10450667 10608705536 6493628845 34359738368 794326870115 2781008504029184 qz371 (@Enclosure.Real.IsNear.neg (Real.sin qz118) Bool.false 42905 65536 10450667 10608705536 (@Enclosure.Real.IsNear.recentre' (Real.sin qz118) Bool.false 343240 524288 20901334 21217411072 42905 65536 10450667 10608705536 (ep369 rfl rfl) rfl)) rfl)

noncomputable def ep371 := @ep319 59981576237 274877906944 3179455291697 11124034016116736 Bool.true 6493628845 34359738368 794326870115 2781008504029184 Bool.false 54279223674713917095936 98733332697 137438953472 1153584957667 252818954911744 Bool.true 12599659125459124224 366698343 274877906944 4615514193221 1011275819646976 (ep320 (BSN.head_sum_c_succ qz6 11 12 rfl rfl) (ep357 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep358 ep370) rfl rfl

noncomputable abbrev qz372 := (@Nat.cast Real Real.instNatCast 13)

noncomputable abbrev qz120 := (@Inv.inv Real Real.instInv (Real.sqrt qz372))

noncomputable abbrev qz121 := (@HMul.hMul Real Real Real qz266 qz279 (Real.log (Enclosure.sfrac Bool.false 13 1)))

noncomputable def ep372 := @Enclosure.Complex.IsNear.of_eq qz103 (Complex.mk (@HMul.hMul Real Real Real qz0 qz120 (Real.cos qz121)) (@HMul.hMul Real Real Real qz0 qz120 (@Neg.neg Real Real.instNeg (Real.sin qz121)))) Bool.false 56938149037 274877906944 3061035782759 11124034016116736 Bool.true 12674168171 68719476736 95603085371 347626063003648 (BSN.cpow_neg_s_mk qz17 78672 1000 13 qz18 rfl)

noncomputable abbrev qz373 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 13) qz19)

noncomputable def ep373 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz372) 1890347 524288 1 524288 72705 72706 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz372) (Real.sqrt qz373) Bool.false 1890347 524288 1 524288 (BSN.sqrt_natCast_div_one 13) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz373) Bool.false 1890347 524288 1 524288 1890347 524288 1 524288 (BSN.sqrt_enclosure 13 1 945173 945174 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep374 := BSN.log_dyadic_bound 5 21 5 4 35742602096145 262144 80938 699352521000 41015625 127272 26 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 5) (BSN.artanhQ 21) 0 4 699352521000 35742602096145 41015625 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz122 := (Real.log (Enclosure.sfrac Bool.false 13 1))

noncomputable def ep375 := @Enclosure.Real.IsNear.mulLit_ff qz17 qz122 78672 1000 0 1 11551488463034085 4503599627370496 500000000121407 40469000000000000000 11359733754547719189 56294995342131200 223500000054268929 229937500000000000000 qz22 (BSN.isNear_log_sfrac 13 1 11551488463034085 4503599627370496 500000000121407 40469000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz373) Bool.false 24225227133228857425920 9444732965739290427392 1000000000242814 80938000000000000000 11551488463034085 4503599627370496 500000000121407 40469000000000000000 (BSN.log_rat_reduce_isNear 13 1 3 26 16 127272 262144 24973259072661432 36028797018963968 80938 1000000000000000 rfl rfl rfl rfl (ep374 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep376 := nat_lit 831486685849542473425417034231617719829283182723587284623164188870668188481

noncomputable def ep377 := nat_lit 138595230320711772727267235488610951853276160405711269666301601549908801

noncomputable def ep378 := nat_lit 2494182867087985996730796568223875937584142995849950431330159963408904747841

noncomputable def ep379 := BSN.cos_dyadic_bound_f 781121399 1073741824 3 2 524288 162035 ep376 ep57 ep377 ep378 ep60 ep377 391567 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 781121399) qz281 0 2 ep376 ep57 ep377 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 781121399) qz282 0 2 ep378 ep60 ep377 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz374 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 26448941) qz485)

noncomputable def ep380 := @Enclosure.Real.IsNear.cos_image qz121 qz374 Bool.false 26448941 131072 511 524288 Bool.false 391567 524288 1 80938 (@Enclosure.Real.IsNear.recentre' qz121 Bool.false 11359733754547719189 56294995342131200 223500000054268929 229937500000000000000 26448941 131072 511 524288 (ep375 rfl) rfl) (Enclosure.sfrac_false_div 26448941 131072) (BSN.cos_reduce0 qz374 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 13741632985877050294272) qz296) 226375608064910080 72057594037927936 Bool.false 391567 524288 32 1000000000000000 161876 80938 (BSN.sin_reduce_arg_pos_rat_q0 26448941 131072 226375608064910080 72057594037927936 32 13741632985877050294272 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 391567 524288 13741632985877050294272 18889465931478580854784 781121399 1073741824 162035 161876 (ep379 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep381 := nat_lit 372283803462777269298906934327274401

noncomputable def ep382 := BSN.sin_dyadic_bound_f 781121399 1073741824 2 1 524288 162035 ep381 ep86 ep381 ep381 ep87 ep381 348644 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 781121399) qz285 0 1 ep381 ep86 ep381 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 781121399) qz286 0 1 ep381 ep87 ep381 rfl rfl rfl rfl) rfl rfl

noncomputable def ep383 := @Enclosure.Real.IsNear.sin_image qz121 qz374 Bool.false 26448941 131072 511 524288 Bool.false 348644 524288 1 80938 (@Enclosure.Real.IsNear.recentre' qz121 Bool.false 11359733754547719189 56294995342131200 223500000054268929 229937500000000000000 26448941 131072 511 524288 (ep375 rfl) rfl) (Enclosure.sfrac_false_div 26448941 131072) (BSN.sin_reduce0 qz374 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 13741632985877050294272) qz296) 226375608064910080 72057594037927936 Bool.false 348644 524288 32 1000000000000000 161876 80938 (BSN.sin_reduce_arg_pos_rat_q0 26448941 131072 226375608064910080 72057594037927936 32 13741632985877050294272 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 348644 524288 13741632985877050294272 18889465931478580854784 781121399 1073741824 162035 161876 (ep382 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz375 := (@Enclosure.Real.IsNear.recentre' qz120 Bool.false 145411 524288 1 524288 145411 524288 1 524288 (ep373 rfl rfl) rfl)

noncomputable def ep384 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz120 (Real.cos qz121)) (@HMul.hMul Real Real Real qz0 qz120 (@Neg.neg Real Real.instNeg (Real.sin qz121))) Bool.false 56938149037 274877906944 3061035782759 11124034016116736 Bool.true 12674168171 68719476736 95603085371 347626063003648 (@Enclosure.Real.IsNear.mulLit_ff qz120 (Real.cos qz121) 145411 524288 1 524288 391567 524288 20941803 21217411072 56938149037 274877906944 3061035782759 11124034016116736 qz375 (@Enclosure.Real.IsNear.recentre' (Real.cos qz121) Bool.false 391567 524288 41883606 42434822144 391567 524288 20941803 21217411072 (ep380 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz120 (@Neg.neg Real Real.instNeg (Real.sin qz121)) 145411 524288 1 524288 87161 131072 20941803 21217411072 12674168171 68719476736 95603085371 347626063003648 qz375 (@Enclosure.Real.IsNear.neg (Real.sin qz121) Bool.false 87161 131072 20941803 21217411072 (@Enclosure.Real.IsNear.recentre' (Real.sin qz121) Bool.false 348644 524288 41883606 42434822144 87161 131072 20941803 21217411072 (ep383 rfl rfl) rfl)) rfl)

noncomputable def ep385 := @ep317 56938149037 274877906944 3061035782759 11124034016116736 Bool.true 12674168171 68719476736 95603085371 347626063003648 Bool.false 34965131453635003154432 254404814431 274877906944 53818773920107 11124034016116736 Bool.true 3509048137351662927872 51063371027 274877906944 53829954857303 11124034016116736 (ep318 (BSN.head_sum_c_succ qz6 12 13 rfl rfl) (ep371 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep372 ep384) rfl rfl

noncomputable abbrev qz376 := (@Nat.cast Real Real.instNatCast 14)

noncomputable abbrev qz123 := (@Inv.inv Real Real.instInv (Real.sqrt qz376))

noncomputable abbrev qz124 := (@HMul.hMul Real Real Real qz266 qz279 (Real.log (Enclosure.sfrac Bool.false 14 1)))

noncomputable def ep386 := @Enclosure.Complex.IsNear.of_eq qz102 (Complex.mk (@HMul.hMul Real Real Real qz0 qz123 (Real.cos qz124)) (@HMul.hMul Real Real Real qz0 qz123 (@Neg.neg Real Real.instNeg (Real.sin qz124)))) Bool.false 70712763255 274877906944 2954830203161 11124034016116736 Bool.true 19915257609 274877906944 2940159138467 11124034016116736 (BSN.cpow_neg_s_mk qz17 78672 1000 14 qz18 rfl)

noncomputable abbrev qz377 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 14) qz19)

noncomputable def ep387 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz376) 1961707 524288 1 524288 70060 70061 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz376) (Real.sqrt qz377) Bool.false 1961707 524288 1 524288 (BSN.sqrt_natCast_div_one 14) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz377) Bool.false 1961707 524288 1 524288 1961707 524288 1 524288 (BSN.sqrt_enclosure 14 1 980853 980854 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep388 := BSN.log_dyadic_bound 6 22 5 4 51857700491520 262144 80938 1346332575744 176359680 146699 28 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 6) (BSN.artanhQ 22) 0 4 1346332575744 51857700491520 176359680 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz125 := (Real.log (Enclosure.sfrac Bool.false 14 1))

noncomputable def ep389 := @Enclosure.Real.IsNear.mulLit_ff qz17 qz125 78672 1000 0 1 11885241781671653 4503599627370496 500000000121407 40469000000000000000 58439733840479517801 281474976710656000 223500000054268929 229937500000000000000 qz22 (BSN.isNear_log_sfrac 14 1 11885241781671653 4503599627370496 500000000121407 40469000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz377) Bool.false 24925158572916270432256 9444732965739290427392 1000000000242814 80938000000000000000 11885241781671653 4503599627370496 500000000121407 40469000000000000000 (BSN.log_rat_reduce_isNear 14 1 3 28 16 146699 262144 24973259072661432 36028797018963968 80938 1000000000000000 rfl rfl rfl rfl (ep388 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep390 := nat_lit 7549677995461815993271044597633681

noncomputable def ep391 := BSN.cos_dyadic_bound_f 294769203 1073741824 2 1 524288 162035 ep390 ep90 ep390 ep390 ep91 ep390 504655 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 294769203) qz281 0 1 ep390 ep90 ep390 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 294769203) qz282 0 1 ep390 ep91 ep390 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz378 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 54426243) qz20)

noncomputable def ep392 := @Enclosure.Real.IsNear.cos_image qz124 qz378 Bool.false 54426243 262144 511 524288 Bool.false 504655 524288 1 80938 (@Enclosure.Real.IsNear.recentre' qz124 Bool.false 58439733840479517801 281474976710656000 223500000054268929 229937500000000000000 54426243 262144 511 524288 (ep389 rfl) rfl) (Enclosure.sfrac_false_div 54426243 262144) (BSN.cos_reduce0 qz378 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 10371269332286104928256) qz23) 226375608064910080 72057594037927936 Bool.false 504655 524288 33 1000000000000000 161876 80938 (BSN.sin_reduce_arg_pos_rat_q0 54426243 262144 226375608064910080 72057594037927936 33 10371269332286104928256 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 504655 524288 10371269332286104928256 37778931862957161709568 294769203 1073741824 162035 161876 (ep391 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep393 := BSN.sin_dyadic_bound_f 294769203 1073741824 2 1 524288 162035 ep390 ep86 ep390 ep390 ep87 ep390 142129 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 294769203) qz285 0 1 ep390 ep86 ep390 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 294769203) qz286 0 1 ep390 ep87 ep390 rfl rfl rfl rfl) rfl rfl

noncomputable def ep394 := @Enclosure.Real.IsNear.sin_image qz124 qz378 Bool.false 54426243 262144 511 524288 Bool.false 142129 524288 1 80938 (@Enclosure.Real.IsNear.recentre' qz124 Bool.false 58439733840479517801 281474976710656000 223500000054268929 229937500000000000000 54426243 262144 511 524288 (ep389 rfl) rfl) (Enclosure.sfrac_false_div 54426243 262144) (BSN.sin_reduce0 qz378 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 10371269332286104928256) qz23) 226375608064910080 72057594037927936 Bool.false 142129 524288 33 1000000000000000 161876 80938 (BSN.sin_reduce_arg_pos_rat_q0 54426243 262144 226375608064910080 72057594037927936 33 10371269332286104928256 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 142129 524288 10371269332286104928256 37778931862957161709568 294769203 1073741824 162035 161876 (ep393 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz379 := (@Enclosure.Real.IsNear.recentre' qz123 Bool.false 140121 524288 1 524288 140121 524288 1 524288 (ep387 rfl rfl) rfl)

noncomputable def ep395 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz123 (Real.cos qz124)) (@HMul.hMul Real Real Real qz0 qz123 (@Neg.neg Real Real.instNeg (Real.sin qz124))) Bool.false 70712763255 274877906944 2954830203161 11124034016116736 Bool.true 19915257609 274877906944 2940159138467 11124034016116736 (@Enclosure.Real.IsNear.mulLit_ff qz123 (Real.cos qz124) 140121 524288 1 524288 504655 524288 20941803 21217411072 70712763255 274877906944 2954830203161 11124034016116736 qz379 (@Enclosure.Real.IsNear.recentre' (Real.cos qz124) Bool.false 504655 524288 41883606 42434822144 504655 524288 20941803 21217411072 (ep392 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz123 (@Neg.neg Real Real.instNeg (Real.sin qz124)) 140121 524288 1 524288 142129 524288 20941803 21217411072 19915257609 274877906944 2940159138467 11124034016116736 qz379 (@Enclosure.Real.IsNear.neg (Real.sin qz124) Bool.false 142129 524288 20941803 21217411072 (@Enclosure.Real.IsNear.recentre' (Real.sin qz124) Bool.false 142129 524288 41883606 42434822144 142129 524288 20941803 21217411072 (ep394 rfl rfl) rfl)) rfl)

noncomputable def ep396 := @ep315 70712763255 274877906944 2954830203161 11124034016116736 Bool.true 19915257609 274877906944 2940159138467 11124034016116736 Bool.false 89367639265030998851584 162558788843 137438953472 14193401030817 2781008504029184 Bool.true 19510456877219141648384 17744657159 68719476736 28385056997885 5562017008058368 (ep316 (BSN.head_sum_c_succ qz6 13 14 rfl rfl) (ep385 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep386 ep395) rfl rfl

noncomputable abbrev qz380 := (@Nat.cast Real Real.instNatCast 15)

noncomputable abbrev qz126 := (@Inv.inv Real Real.instInv (Real.sqrt qz380))

noncomputable abbrev qz127 := (@HMul.hMul Real Real Real qz266 qz279 (Real.log (Enclosure.sfrac Bool.false 15 1)))

noncomputable def ep397 := @Enclosure.Complex.IsNear.of_eq qz101 (Complex.mk (@HMul.hMul Real Real Real qz0 qz126 (Real.cos qz127)) (@HMul.hMul Real Real Real qz0 qz126 (@Neg.neg Real Real.instNeg (Real.sin qz127)))) Bool.false 7416570977 34359738368 22243693649 86906515750912 Bool.false 4868347273 34359738368 44392163741 173813031501824 (BSN.cpow_neg_s_mk qz17 78672 1000 15 qz18 rfl)

noncomputable abbrev qz381 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 15) qz19)

noncomputable def ep398 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz380) 2030559 524288 1 524288 67685 67686 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz380) (Real.sqrt qz381) Bool.false 2030559 524288 1 524288 (BSN.sqrt_natCast_div_one 15) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz381) Bool.false 2030559 524288 1 524288 2030559 524288 1 524288 (BSN.sqrt_enclosure 15 1 1015279 1015280 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep399 := BSN.log_dyadic_bound 7 23 6 5 430628584065881355 262144 80938 14087658153505881 266939110305 164785 30 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 7) (BSN.artanhQ 23) 0 5 14087658153505881 430628584065881355 266939110305 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz128 := (Real.log (Enclosure.sfrac Bool.false 15 1))

noncomputable def ep400 := @Enclosure.Real.IsNear.mulLit_ff qz17 qz128 78672 1000 0 1 12195956895733477 4503599627370496 500000000121407 40469000000000000000 59967520056321506409 281474976710656000 223500000054268929 229937500000000000000 qz22 (BSN.isNear_log_sfrac 15 1 12195956895733477 4503599627370496 500000000121407 40469000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz381) Bool.false 25576775395801252757504 9444732965739290427392 1000000000242814 80938000000000000000 12195956895733477 4503599627370496 500000000121407 40469000000000000000 (BSN.log_rat_reduce_isNear 15 1 3 30 16 164785 262144 24973259072661432 36028797018963968 80938 1000000000000000 rfl rfl rfl rfl (ep399 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep401 := nat_lit 5132465950139312706470786397372228118283953311276805382763384577173131100160

noncomputable def ep402 := nat_lit 1629347938455691150390894926621219574992902703489695434285238157045661696

noncomputable def ep403 := nat_lit 13439534734654985969370474353712734525717508258490745067010497792722983714816

noncomputable def ep404 := BSN.sin_dyadic_bound_f 1062922816 1073741824 3 2 524288 162035 ep401 ep64 ep402 ep403 ep66 ep402 438296 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1062922816) qz285 0 2 ep401 ep64 ep402 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1062922816) qz286 0 2 ep403 ep66 ep402 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz382 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 55849105) qz20)

noncomputable def ep405 := @Enclosure.Real.IsNear.cos_image qz127 qz382 Bool.false 55849105 262144 255 262144 Bool.false 438296 524288 1 80938 (@Enclosure.Real.IsNear.recentre' qz127 Bool.false 59967520056321506409 281474976710656000 223500000054268929 229937500000000000000 55849105 262144 255 262144 (ep400 rfl) rfl) (Enclosure.sfrac_false_div 55849105 262144) (BSN.cos_reduce3 qz382 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 37398271866571178639360) qz23) 226375608064910080 72057594037927936 Bool.false 438296 524288 33 1000000000000000 161876 80938 (BSN.sin_reduce_arg_pos_rat_q3 55849105 262144 226375608064910080 72057594037927936 33 37398271866571178639360 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 438296 524288 37398271866571178639360 37778931862957161709568 1062922816 1073741824 162035 161876 (ep404 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep406 := nat_lit 2852094126938931810772832840729736163302193129688665077283784870943759794176

noncomputable def ep407 := nat_lit 8553023684939884050017716732335966050756593583659015840982784136517188059136

noncomputable def ep408 := BSN.cos_dyadic_bound_f 1062922816 1073741824 3 2 524288 162035 ep406 ep57 ep402 ep407 ep60 ep402 287704 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1062922816) qz281 0 2 ep406 ep57 ep402 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1062922816) qz282 0 2 ep407 ep60 ep402 rfl rfl rfl rfl) rfl rfl

noncomputable def ep409 := @Enclosure.Real.IsNear.sin_image qz127 qz382 Bool.false 55849105 262144 255 262144 Bool.true 287704 524288 1 80938 (@Enclosure.Real.IsNear.recentre' qz127 Bool.false 59967520056321506409 281474976710656000 223500000054268929 229937500000000000000 55849105 262144 255 262144 (ep400 rfl) rfl) (Enclosure.sfrac_false_div 55849105 262144) (BSN.sin_reduce3 qz382 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 37398271866571178639360) qz23) 226375608064910080 72057594037927936 Bool.false 287704 524288 33 1000000000000000 161876 80938 (BSN.sin_reduce_arg_pos_rat_q3 55849105 262144 226375608064910080 72057594037927936 33 37398271866571178639360 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 287704 524288 37398271866571178639360 37778931862957161709568 1062922816 1073741824 162035 161876 (ep408 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz383 := (@Enclosure.Real.IsNear.recentre' qz126 Bool.false 135371 524288 1 524288 135371 524288 1 524288 (ep398 rfl rfl) rfl)

noncomputable def ep410 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz126 (Real.cos qz127)) (@HMul.hMul Real Real Real qz0 qz126 (@Neg.neg Real Real.instNeg (Real.sin qz127))) Bool.false 7416570977 34359738368 22243693649 86906515750912 Bool.false 4868347273 34359738368 44392163741 173813031501824 (@Enclosure.Real.IsNear.mulLit_ff qz126 (Real.cos qz127) 135371 524288 1 524288 54787 65536 10450667 10608705536 7416570977 34359738368 22243693649 86906515750912 qz383 (@Enclosure.Real.IsNear.recentre' (Real.cos qz127) Bool.false 438296 524288 20901334 21217411072 54787 65536 10450667 10608705536 (ep405 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz126 (@Neg.neg Real Real.instNeg (Real.sin qz127)) 135371 524288 1 524288 35963 65536 10450667 10608705536 4868347273 34359738368 44392163741 173813031501824 qz383 (@Enclosure.Real.IsNear.neg (Real.sin qz127) Bool.true 35963 65536 10450667 10608705536 (@Enclosure.Real.IsNear.recentre' (Real.sin qz127) Bool.true 287704 524288 20901334 21217411072 35963 65536 10450667 10608705536 (ep409 rfl rfl) rfl)) rfl)

noncomputable def ep411 := @ep313 7416570977 34359738368 22243693649 86906515750912 Bool.false 4868347273 34359738368 44392163741 173813031501824 Bool.false 6604803207494126010368 192225072751 137438953472 14905199227585 2781008504029184 Bool.true 275151500243405635584 8007962613 68719476736 29805606237597 5562017008058368 (ep314 (BSN.head_sum_c_succ qz6 14 15 rfl rfl) (ep396 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep397 ep410) rfl rfl

noncomputable def ep412 := @Enclosure.Complex.IsNear.mul qz96 (@HAdd.hAdd Complex Complex Complex qz5 qz97 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz53 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz53 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz99 qz100 (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1))))) Bool.true 15763681600304712814687 204163924383541776875520 ep304 ep305 Bool.false

noncomputable abbrev qz129 := (Complex.re qz352)

noncomputable abbrev qz130 := (Complex.im qz352)

noncomputable def ep413 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 qz129 (Complex.re (@HAdd.hAdd Complex Complex Complex qz5 qz97 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz53 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz53 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz99 qz100 (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz130 (Complex.im (@HAdd.hAdd Complex Complex Complex qz5 qz97 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz53 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz53 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz99 qz100 (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1))))))) 1094737437846773791979 40832784876708355375104 204747456995163336324793

noncomputable def ep414 := nat_lit 1652461971175510433675083776

noncomputable def ep415 := nat_lit 782415706049010622005248000

noncomputable def ep416 := nat_lit 26819792485423668458503274671681608563556352

noncomputable def ep417 := @Enclosure.Real.IsNear.mulLit_tf qz129 (Complex.re (@HAdd.hAdd Complex Complex Complex qz5 qz97 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz53 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz53 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz99 qz100 (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1)))))) 14700530147 274877906944 2749422884449 11124034016116736 74469248857

noncomputable abbrev qz384 := (@Nat.cast Real Real.instNatCast 16)

noncomputable abbrev qz131 := (@Inv.inv Real Real.instInv (Real.sqrt qz384))

noncomputable abbrev qz385 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) qz484 (Real.log (Enclosure.sfrac Bool.false 16 1)))

noncomputable abbrev qz132 := (Real.cos qz385)

noncomputable abbrev qz133 := (@Neg.neg Real Real.instNeg (Real.sin qz385))

noncomputable def ep418 := @Enclosure.Complex.IsNear.of_eq qz96 (Complex.mk (@HMul.hMul Real Real Real qz0 qz131 qz132) (@HMul.hMul Real Real Real qz0 qz131 qz133)) Bool.true 14700530147 274877906944 2749422884449 11124034016116736 Bool.false 33564006325 137438953472 1382805100583 5562017008058368 (BSN.cpow_neg_s_mk qz17 78672 1000 16 qz18 rfl)

noncomputable abbrev qz386 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 16) qz19)

noncomputable def ep419 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz384) 2097153 524288 1 524288 65535 65536 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz384) (Real.sqrt qz386) Bool.false 2097153 524288 1 524288 (BSN.sqrt_natCast_div_one 16) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz386) Bool.false 2097153 524288 1 524288 2097153 524288 1 524288 (BSN.sqrt_enclosure 16 1 1048576 1048577 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep420 := BSN.log_dyadic_bound 0 32 1 0 1 262144 80938 0 1 0 32 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 0) (BSN.artanhQ 32) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz387 := (Real.log (Enclosure.sfrac Bool.false 16 1))

noncomputable abbrev qz134 := qz387

noncomputable abbrev qz388 := (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 16) qz19))

noncomputable def ep421 := @Enclosure.Real.IsNear.mulLit_ff qz17 qz134 78672 1000 0 1 3121657384082679 1125899906842624 125000000040469 10117250000000000000 15349189357534532643 70368744177664000 55875000018089643 57484375000000000000 qz22 (BSN.isNear_log_sfrac 16 1 3121657384082679 1125899906842624 125000000040469 10117250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' qz388 Bool.false 26186360105375033720832 9444732965739290427392 1000000000323752 80938000000000000000 3121657384082679 1125899906842624 125000000040469 10117250000000000000 (BSN.log_rat_reduce_isNear 16 1 4 32 32 0 262144 24973259072661432 36028797018963968 80938 1000000000000000 rfl rfl rfl rfl (ep420 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep422 := nat_lit 10032304300130568577478545766300818943538578059038873090994535264436250279936

noncomputable def ep423 := nat_lit 20102112522016131255651158754561533745319480419242148544147097236820525056

noncomputable def ep424 := nat_lit 30056708675347673469924334981393333763125095216278134975895311598835109789696

noncomputable def ep425 := BSN.cos_dyadic_bound_f 1455141452 1073741824 3 2 524288 162035 ep422 ep57 ep423 ep424 ep60 ep423 112157 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1455141452) qz281 0 2 ep422 ep57 ep423 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1455141452) qz282 0 2 ep424 ep60 ep423 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz135 := qz385

noncomputable abbrev qz389 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 28590093) qz485)

noncomputable def ep426 := @Enclosure.Real.IsNear.cos_image qz135 qz389 Bool.false 28590093 131072 511 524288 Bool.true 112157 524288 1 80938 (@Enclosure.Real.IsNear.recentre' qz135 Bool.false 15349189357534532643 70368744177664000 55875000018089643 57484375000000000000 28590093 131072 511 524288 (ep421 rfl) rfl) (Enclosure.sfrac_false_div 28590093 131072) (BSN.cos_reduce2 qz389 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 25599119162033062281216) qz296) 226375608064910080 72057594037927936 Bool.false 112157 524288 34 1000000000000000 161876 80938 (BSN.sin_reduce_arg_pos_rat_q2 28590093 131072 226375608064910080 72057594037927936 34 25599119162033062281216 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 112157 524288 25599119162033062281216 18889465931478580854784 1455141452 1073741824 162035 161876 (ep425 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep427 := nat_lit 18042066050217410534456861452337824871373184921934577844954845798195794083840

noncomputable def ep428 := nat_lit 47220483854105191949163582880044060751342109922483216591524548456891275083776

noncomputable def ep429 := BSN.sin_dyadic_bound_f 1455141452 1073741824 3 2 524288 162035 ep427 ep64 ep423 ep428 ep66 ep423 512150 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1455141452) qz285 0 2 ep427 ep64 ep423 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1455141452) qz286 0 2 ep428 ep66 ep423 rfl rfl rfl rfl) rfl rfl

noncomputable def ep430 := @Enclosure.Real.IsNear.sin_image qz135 qz389 Bool.false 28590093 131072 511 524288 Bool.true 512150 524288 1 80938 (@Enclosure.Real.IsNear.recentre' qz135 Bool.false 15349189357534532643 70368744177664000 55875000018089643 57484375000000000000 28590093 131072 511 524288 (ep421 rfl) rfl) (Enclosure.sfrac_false_div 28590093 131072) (BSN.sin_reduce2 qz389 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 25599119162033062281216) qz296) 226375608064910080 72057594037927936 Bool.false 512150 524288 34 1000000000000000 161876 80938 (BSN.sin_reduce_arg_pos_rat_q2 28590093 131072 226375608064910080 72057594037927936 34 25599119162033062281216 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 512150 524288 25599119162033062281216 18889465931478580854784 1455141452 1073741824 162035 161876 (ep429 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz136 := (Real.sin qz385)

noncomputable abbrev qz390 := (@Enclosure.Real.IsNear.recentre' qz131 Bool.false 131071 524288 1 524288 131071 524288 1 524288 (ep419 rfl rfl) rfl)

noncomputable def ep431 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz131 qz132) (@HMul.hMul Real Real Real qz0 qz131 qz133) Bool.true 14700530147 274877906944 2749422884449 11124034016116736 Bool.false 33564006325 137438953472 1382805100583 5562017008058368 (@Enclosure.Real.IsNear.mulLit_ft qz131 qz132 131071 524288 1 524288 112157 524288 20941803 21217411072 14700530147 274877906944 2749422884449 11124034016116736 qz390 (@Enclosure.Real.IsNear.recentre' qz132 Bool.true 112157 524288 41883606 42434822144 112157 524288 20941803 21217411072 (ep426 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz131 qz133 131071 524288 1 524288 256075 262144 20941803 21217411072 33564006325 137438953472 1382805100583 5562017008058368 qz390 (@Enclosure.Real.IsNear.neg qz136 Bool.true 256075 262144 20941803 21217411072 (@Enclosure.Real.IsNear.recentre' qz136 Bool.true 512150 524288 41883606 42434822144 256075 262144 20941803 21217411072 (ep430 rfl rfl) rfl)) rfl)

noncomputable def ep432 := @ep417 148548806016 0 1 1094737437846773791979 40832784876708355375104 204747456995163336324793 ep414 (@Enclosure.Complex.IsNear.re_isNear qz96 Bool.true 14700530147 274877906944 2749422884449 11124034016116736 Bool.false 33564006325 137438953472 1382805100583 5562017008058368 (ep418 ep431))

noncomputable def ep433 := @Enclosure.Complex.IsNear.re_isNear (@HAdd.hAdd Complex Complex Complex qz5 qz97 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz53 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz53 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz99 qz100 (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1))))) Bool.false 74469248857 148548806016 0 1 Bool.false

noncomputable def ep434 := @Enclosure.Complex.IsNear.addLitP qz97 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz53 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz53 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz99 qz100 (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1)))) Bool.false 385845849 773691698 0 1 Bool.true 78672000

noncomputable def ep435 := @ep434 386845849 0 1 Bool.false 1 384 0 1 Bool.false 1639 4000 0 1 Bool.false 148938497714 74469248857 148548806016 0 1 Bool.false 319352346511 319352346511 1547383396000 0 1

noncomputable abbrev qz137 := (@HDiv.hDiv Complex Complex Complex qz323 qz353 (@HSub.hSub Complex Complex Complex qz315 qz271 (1 : Complex)))

noncomputable def ep436 := @Enclosure.Complex.IsNear.addLitP qz137 qz72 Bool.true 32000000 24758134336 0 1 Bool.true 5035008000 24758134336 0 1

noncomputable def ep437 := @Enclosure.Complex.IsNear.of_eq qz137 (Complex.mk (Enclosure.sfrac Bool.true 32000000 24758134336) (Enclosure.sfrac Bool.true 5035008000 24758134336)) Bool.true 32000000 24758134336 0 1 Bool.true 5035008000 24758134336 0 1

noncomputable def ep438 := @ep436 Bool.false 1 2 0 1 Bool.false 0 1 0 1 Bool.false 24694134336 385845849 773691698 0 1 Bool.true 5035008000 78672000 386845849 0 1 (ep437 (BSN.N_div_s_sub_one_mk qz17 78672 1000 16 qz18 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 32000000 24758134336) (Enclosure.sfrac Bool.true 5035008000 24758134336) Bool.true 32000000 24758134336 0 1 Bool.true 5035008000 24758134336 0 1 (Enclosure.Real.IsNear.const Bool.true 32000000 24758134336) (Enclosure.Real.IsNear.const Bool.true 5035008000 24758134336))) qz73 rfl

noncomputable abbrev qz138 := (@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 1)))

noncomputable abbrev qz139 := (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz354 qz353 1))

noncomputable def ep439 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz53 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz53 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz99 qz100 (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1)))) (@HAdd.hAdd Complex Complex Complex qz5 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz53 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz53 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz99 qz100 (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz74)) ↑qz138) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1))) qz139)) Bool.false 1 384 0 1

noncomputable def ep440 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz53 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz53 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz99 qz100 (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz74)) ↑qz138) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1))) qz139) Bool.false 0 1 0 1 Bool.false

noncomputable def ep441 := @ep440 0 1 0 1 Bool.false 1 384 0 1 Bool.false 1639 4000 0 1 Bool.false 1 1 384 0 1 Bool.false 1639 1639 4000 0

noncomputable def ep442 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz53 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz53 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz99 qz100 (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1)))) (Complex.mk qz14 qz14) Bool.false 0 1 0 1 Bool.false

noncomputable def ep443 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz74)) ↑qz138) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1))) qz139 Bool.false 1 384 0 1 Bool.false 1639 4000 0 1

noncomputable def ep444 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz74)) ↑qz138) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz139)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz74)) ↑qz138) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz139)) 1 384 0 1 0 1 0

noncomputable def ep445 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz74)) ↑qz138) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz139) 1 24 0 1 1 16 0 1 1

noncomputable def ep446 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz74)) ↑qz138)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz74)) ↑qz138)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)))) 1 24 0 1 0 1 0 1 1

noncomputable def ep447 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz74)) ↑qz138)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 1 2 0 1 1 24 0

noncomputable def ep448 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz74)) ↑qz138) (Complex.mk (Enclosure.sfrac Bool.false 1 12) qz14) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (BSN.bern_coeff_mk 1 1 6 2 Bool.false BSN.bern_real_1 EMRow21.d7 rfl) qz341

noncomputable def ep449 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)) qz6 Bool.false 1 2 0 1 Bool.false 78672 1000 0 1 (BSN.ascPochhammer_one_eval qz6)

noncomputable def ep450 := ep449 (@Enclosure.Complex.IsNear.of_eq qz6 (Complex.mk qz67 qz17) Bool.false 1 2 0 1 Bool.false 78672 1000 0 1 (BSN.s_crit_mk qz17 Bool.false 78672 1000 qz18) (@Enclosure.Complex.IsNear.mk qz67 qz17 Bool.false 1 2 0 1 Bool.false 78672 1000 0 1 qz333 qz22))

noncomputable def ep451 := @ep447 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz74)) ↑qz138) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep448) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 78672 1000 0 1 ep450)

noncomputable def ep452 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz74)) ↑qz138)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 78672 1000 0 1 0 1 0

noncomputable def ep453 := @ep452 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz74)) ↑qz138) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep448) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 78672 1000 0 1 ep450)

noncomputable def ep454 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz74)) ↑qz138)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz74)) ↑qz138)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)))) 1639 250 0 1 0 1 0 1 1639

noncomputable def ep455 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz74)) ↑qz138)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 78672 1000 0 1 1639 250 0

noncomputable def ep456 := @ep455 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz74)) ↑qz138) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep448) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 78672 1000 0 1 ep450)

noncomputable def ep457 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz74)) ↑qz138)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 1 2 0 1 0 1 0

noncomputable def ep458 := @ep457 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz74)) ↑qz138) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep448) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 78672 1000 0 1 ep450)

noncomputable def ep459 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz74)) ↑qz138) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 24 0 1 Bool.false 1639 250 0 1 (@ep446 1 24 0 1 (ep451 rfl) (ep453 rfl) rfl rfl) (@ep454 1639 250 0 1 (ep456 rfl) (ep458 rfl) rfl rfl)

noncomputable def ep460 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz74)) ↑qz138) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 1639 250 0 1 ep459

noncomputable abbrev qz140 := (@Enclosure.Complex.IsNear.of_eq (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz354 qz353 1)) (Complex.mk (Enclosure.sfrac Bool.false 1 16) qz277) Bool.false 1 16 0 1 Bool.false 0 1 0 1 (BSN.natCast_pow_inv_mk 16 1 16 EMRow21.d8 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 16) qz277 Bool.false 1 16 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 16) qz288))

noncomputable def ep461 := @ep445 384 0 1 ep460 (@Enclosure.Complex.IsNear.re_isNear qz139 Bool.false 1 16 0 1 Bool.false 0 1 0 1 qz140)

noncomputable def ep462 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz74)) ↑qz138) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz139) 1639 250 0 1 0 1 0 1 0

noncomputable def ep463 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz74)) ↑qz138) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 1639 250 0 1 ep459

noncomputable def ep464 := @ep462 1 0 1 ep463 (@Enclosure.Complex.IsNear.im_isNear qz139 Bool.false 1 16 0 1 Bool.false 0 1 0 1 qz140)

noncomputable def ep465 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz74)) ↑qz138) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz139)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz74)) ↑qz138) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz139)) 0 1 0 1 1639 4000 0

noncomputable def ep466 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz74)) ↑qz138) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz139) 1 24 0 1 0 1 0 1 0

noncomputable def ep467 := @ep466 1 0 1 ep460 (@Enclosure.Complex.IsNear.im_isNear qz139 Bool.false 1 16 0 1 Bool.false 0 1 0 1 qz140)

noncomputable def ep468 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz74)) ↑qz138) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz139) 1639 250 0 1 1 16 0 1 1639

noncomputable def ep469 := @ep468 4000 0 1 ep463 (@Enclosure.Complex.IsNear.re_isNear qz139 Bool.false 1 16 0 1 Bool.false 0 1 0 1 qz140)

noncomputable def ep470 := @ep441 1 (@ep442 0 1 0 1 (BSN.bern_sum_base qz6 16) qz88) (ep443 (@ep444 1 1 1 384 0 1 (ep461 rfl) (ep464 rfl) rfl rfl) (@ep465 1 1639 1639 4000 0 1 (ep467 rfl) (ep469 rfl) rfl rfl)) rfl rfl rfl rfl rfl

noncomputable def ep471 := ep435 (ep438 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep439 Bool.false 1639 4000 0 1 (BSN.bern_sum_succ qz6 16 0 1 1 rfl rfl) (ep470 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl rfl

noncomputable def ep472 := @Enclosure.Real.IsNear.mulLit_ff qz130 (Complex.im (@HAdd.hAdd Complex Complex Complex qz5 qz97 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz53 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz53 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz99 qz100 (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1)))))) 33564006325 137438953472 1382805100583 5562017008058368 319352346511

noncomputable def ep473 := @ep472 1547383396000 0 1 428749767127951827283 8506830182647574036480 40145641239869129465083 ep415 (@Enclosure.Complex.IsNear.im_isNear qz96 Bool.true 14700530147 274877906944 2749422884449 11124034016116736 Bool.false 33564006325 137438953472 1382805100583 5562017008058368 (ep418 ep431))

noncomputable def ep474 := @Enclosure.Complex.IsNear.im_isNear (@HAdd.hAdd Complex Complex Complex qz5 qz97 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz53 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz53 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz99 qz100 (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1))))) Bool.false 74469248857 148548806016 0 1 Bool.false

noncomputable def ep475 := @Enclosure.Real.IsNear.addLit_tf_p (@HMul.hMul Real Real Real qz0 qz129 (Complex.im (@HAdd.hAdd Complex Complex Complex qz5 qz97 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz53 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz53 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz99 qz100 (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz130 (Complex.re (@HAdd.hAdd Complex Complex Complex qz5 qz97 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz53 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz53 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz99 qz100 (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1))))))) 4694648797400145767117 425341509132378701824000 79821331790893651027949

noncomputable def ep476 := nat_lit 1564831412098021244010496000

noncomputable def ep477 := nat_lit 826230985587755216837541888

noncomputable def ep478 := nat_lit 967287499556376387035224274441830562755772416

noncomputable def ep479 := @Enclosure.Real.IsNear.mulLit_tf qz129 (Complex.im (@HAdd.hAdd Complex Complex Complex qz5 qz97 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz53 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz53 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz99 qz100 (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1)))))) 14700530147 274877906944 2749422884449 11124034016116736 319352346511

noncomputable def ep480 := @ep479 1547383396000 0 1 4694648797400145767117 425341509132378701824000 79821331790893651027949 ep476 (@Enclosure.Complex.IsNear.re_isNear qz96 Bool.true 14700530147 274877906944 2749422884449 11124034016116736 Bool.false 33564006325 137438953472 1382805100583 5562017008058368 (ep418 ep431))

noncomputable def ep481 := @Enclosure.Real.IsNear.mulLit_ff qz130 (Complex.re (@HAdd.hAdd Complex Complex Complex qz5 qz97 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz53 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz53 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz99 qz100 (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1)))))) 33564006325 137438953472 1382805100583 5562017008058368 74469248857

noncomputable def ep482 := @ep481 148548806016 0 1 2499486339654347020525 20416392438354177687552 102976457156044342783631 ep477 (@Enclosure.Complex.IsNear.im_isNear qz96 Bool.true 14700530147 274877906944 2749422884449 11124034016116736 Bool.false 33564006325 137438953472 1382805100583 5562017008058368 (ep418 ep431))

noncomputable abbrev qz391 := (ep471 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable def ep483 := @ep412 284267899672392502962923 ep299 ep306 ep307 (@ep413 ep414 428749767127951827283 8506830182647574036480 40145641239869129465083 ep415 ep416 15763681600304712814687 204163924383541776875520 ep304 ep305 (ep432 (@ep433 319352346511 1547383396000 0 1 qz391) rfl) (ep473 (@ep474 319352346511 1547383396000 0 1 qz391) rfl) rfl rfl) (@ep475 ep476 2499486339654347020525 20416392438354177687552 102976457156044342783631 ep477 ep478 284267899672392502962923 ep299 ep306 ep307 (ep480 (@ep474 319352346511 1547383396000 0 1 qz391) rfl) (ep482 (@ep433 319352346511 1547383396000 0 1 qz391) rfl) rfl rfl)

noncomputable def ep484 := @ep310 ep300 ep301 (@ep311 5562017008058368 (BSN.head_sum_c_eq qz6 16) (ep312 (BSN.head_sum_c_succ qz6 15 16 rfl rfl) (ep411 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))) ep483 rfl rfl rfl

noncomputable def ep485 := @Enclosure.Complex.IsNear.re_isNear (zetaApproximant qz6 1 16) Bool.false 269784368834693151885473 204163924383541776875520 ep169 ep170 Bool.true 13125421523086866989077 ep299 ep300 ep301 (@ep302 ep170 Bool.true 13125421523086866989077 ep299 ep300 ep301 (BSN.zetaApproximant_eq_folded' qz6 1 16 rfl) (ep484 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

noncomputable def ep486 := @Enclosure.Real.IsNear.mulLit_ft (Real.sin (@HSub.hSub Real Real Real qz318 (Complex.im (@HSub.hSub Complex Complex Complex qz46 qz47 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz48 (@Nat.cast Complex Complex.instNatCast j))))) qz49)) (Complex.im (zetaApproximant qz6 1 16)) 271 524288 9772359

noncomputable def ep487 := @Enclosure.Real.IsNear.recentre' (Real.sin (@HSub.hSub Real Real Real qz318 (Complex.im (@HSub.hSub Complex Complex Complex qz46 qz47 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz48 (@Nat.cast Complex Complex.instNatCast j))))) qz49)) Bool.false 271 524288 19544718

noncomputable def ep488 := @Enclosure.Real.IsNear.sin_image (@HSub.hSub Real Real Real qz318 (Complex.im (@HSub.hSub Complex Complex Complex qz46 qz47 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz48 (@Nat.cast Complex Complex.instNatCast j))))) qz49) qz319 Bool.false 3911827 65536 235

noncomputable def ep489 := nat_lit 18112749675393072714070013429210222290982834956783958464979416425943768498176

noncomputable def ep490 := nat_lit 54207618875960508779000574262695887916134760563620407425698072542777899483136

noncomputable def ep491 := BSN.cos_dyadic_bound_f 1686074184 1073741824 3 2 524288 162035 ep489 ep57 ep295 ep490 ep60 ep295 271 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1686074184) qz281 0 2 ep489 ep57 ep295 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1686074184) qz282 0 2 ep490 ep60 ep295 rfl rfl rfl rfl) rfl rfl

noncomputable def ep492 := @ep488 524288 Bool.false 271 524288 1 80938 (@ep174 3911827 65536 235 524288 ep293 rfl) (Enclosure.sfrac_false_div 3911827 65536) (BSN.sin_reduce1 qz319 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 14830865369959009091584) qz351) 226375608064910080 72057594037927936 Bool.false 271 524288 9 1000000000000000 161876 80938 (BSN.sin_reduce_arg_pos_rat_q1 3911827 65536 226375608064910080 72057594037927936 9 14830865369959009091584 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 271 524288 14830865369959009091584 9444732965739290427392 1686074184 1073741824 162035 161876 (ep491 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep493 := @Enclosure.Complex.IsNear.im_isNear (zetaApproximant qz6 1 16) Bool.false 269784368834693151885473 204163924383541776875520 ep169 ep170 Bool.true 13125421523086866989077 ep299 ep300 ep301 (@ep302 ep170 Bool.true 13125421523086866989077 ep299 ep300 ep301 (BSN.zetaApproximant_eq_folded' qz6 1 16 rfl) (ep484 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

theorem EMRow21.d9 : Enclosure.Real.IsNear (hardyZApproximantEM 1 16 qz17) Bool.true ep153 ep154 ep155 ep156 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantEM 1 16 qz17) ep157 Bool.true ep153 ep154 ep155 ep156 (@Eq.refl Real ep157) (@ep158 Bool.true ep153 ep154 ep155 ep156 (BSN.re_exp_mul (@HSub.hSub Real Real Real qz318 (Complex.im (@HSub.hSub Complex Complex Complex qz46 qz47 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz48 (@Nat.cast Complex Complex.instNatCast j))))) qz49) (zetaApproximant qz6 1 16)) (@ep160 ep161 ep162 ep156 ep163 ep164 ep165 ep166 ep167 ep153 ep154 ep155 ep156 (@ep168 21217411072 269784368834693151885473 204163924383541776875520 ep169 ep170 ep159 ep161 ep162 ep156 (@ep171 42434822144 524287 524288 9772359 21217411072 (ep298 rfl rfl) rfl) ep485 rfl) (@ep486 21217411072 13125421523086866989077 ep299 ep300 ep301 ep163 ep164 ep165 ep166 (@ep487 42434822144 271 524288 9772359 21217411072 (ep492 rfl rfl) rfl) ep493 rfl) rfl rfl))

noncomputable abbrev qz508 := (@HAdd.hAdd Complex Complex Complex (@instHAdd Complex Complex.instAdd) (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (2 : Complex)) (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul) Complex.I ↑(Enclosure.sfrac Bool.false 81143 1000)))

noncomputable abbrev qz494 := qz508

noncomputable abbrev qz392 := qz494

noncomputable abbrev qz141 := (BSN.headSumC qz392 9)

noncomputable abbrev qz142 := qz392

noncomputable abbrev qz495 := (@Neg.neg Complex Complex.instNeg qz508)

noncomputable abbrev qz393 := qz495

noncomputable abbrev qz143 := (@HPow.hPow Complex Complex Complex qz273 (@Nat.cast Complex Complex.instNatCast 8) qz393)

noncomputable def ep494 := @Enclosure.Complex.IsNear.of_eq qz141 (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz142 8) qz143) Bool.false 13475398257 4294967296 434429481205 126409477455872 Bool.false 197796089 2147483648 1738339569129 505637909823488

noncomputable def ep495 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz142 8) qz143 Bool.false 803077631375 274877906944 34222458538809 11124034016116736 Bool.true 51639442681 274877906944 34232290158607 11124034016116736 Bool.false

noncomputable abbrev qz144 := (@HPow.hPow Complex Complex Complex qz273 (@Nat.cast Complex Complex.instNatCast 7) qz393)

noncomputable def ep496 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz142 8) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz142 7) qz144) Bool.false 803077631375 274877906944 34222458538809 11124034016116736 Bool.true 51639442681 274877906944 34232290158607 11124034016116736

noncomputable def ep497 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz142 7) qz144 Bool.false 731976350649 274877906944 2302902634403 855694924316672 Bool.false 24114308959 274877906944 2303585825835 855694924316672 Bool.false

noncomputable abbrev qz145 := (@HPow.hPow Complex Complex Complex qz273 (@Nat.cast Complex Complex.instNatCast 6) qz393)

noncomputable def ep498 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz142 7) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz142 6) qz145) Bool.false 731976350649 274877906944 2302902634403 855694924316672 Bool.false 24114308959 274877906944 2303585825835 855694924316672

noncomputable def ep499 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz142 6) qz145 Bool.false 330039790177 137438953472 12655913611137 5562017008058368 Bool.false 27568766573 68719476736 1582375735987 695252126007296 Bool.false

noncomputable abbrev qz146 := (@HPow.hPow Complex Complex Complex qz273 (@Nat.cast Complex Complex.instNatCast 5) qz393)

noncomputable def ep500 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz142 6) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz142 5) qz146) Bool.false 330039790177 137438953472 12655913611137 5562017008058368 Bool.false 27568766573 68719476736 1582375735987 695252126007296

noncomputable def ep501 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz142 5) qz146 Bool.false 158362030599 68719476736 10122592930013 5562017008058368 Bool.true 1216826099 34359738368 10117626736209 5562017008058368 Bool.false

noncomputable abbrev qz147 := (@HPow.hPow Complex Complex Complex qz273 (@Nat.cast Complex Complex.instNatCast 4) qz393)

noncomputable def ep502 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz142 5) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz142 4) qz147) Bool.false 158362030599 68719476736 10122592930013 5562017008058368 Bool.true 1216826099 34359738368 10117626736209 5562017008058368

noncomputable def ep503 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz142 4) qz147 Bool.false 260378258349 137438953472 3642070377321 2781008504029184 Bool.true 44205269405 137438953472 3640900094779 2781008504029184 Bool.false

noncomputable abbrev qz148 := (@HPow.hPow Complex Complex Complex qz273 qz275 qz393)

noncomputable def ep504 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz142 4) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz142 3) qz148) Bool.false 260378258349 137438953472 3642070377321 2781008504029184 Bool.true 44205269405 137438953472 3640900094779 2781008504029184

noncomputable def ep505 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz142 3) qz148 Bool.false 57536309039 34359738368 14186007623 19653770346496 Bool.false 7289949051 34359738368 14136984363 19653770346496 Bool.false

noncomputable abbrev qz149 := (@HPow.hPow Complex Complex Complex qz273 qz276 qz393)

noncomputable def ep506 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz142 3) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz142 2) qz149) Bool.false 57536309039 34359738368 14186007623 19653770346496 Bool.false 7289949051 34359738368 14136984363 19653770346496

noncomputable def ep507 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz142 2) qz149 Bool.false 1 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable def ep508 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz142 2) (Complex.mk (Enclosure.sfrac Bool.false 1 1) qz14) Bool.false 1 1 0 1 Bool.false 0 1 0 1 (BSN.head_sum_c_two qz142)

noncomputable abbrev qz509 := (Enclosure.sfrac Bool.false 81143 1000)

noncomputable abbrev qz496 := qz509

noncomputable abbrev qz394 := qz496

noncomputable abbrev qz150 := (@HMul.hMul Real Real Real qz266 qz394 (Real.log (Enclosure.sfrac Bool.false 2 1)))

noncomputable abbrev qz151 := qz394

noncomputable abbrev qz395 := (@Eq.refl Real qz496)

noncomputable abbrev qz152 := qz395

noncomputable def ep509 := @Enclosure.Complex.IsNear.of_eq qz149 (Complex.mk (@HMul.hMul Real Real Real qz0 qz15 (Real.cos qz150)) (@HMul.hMul Real Real Real qz0 qz15 (@Neg.neg Real Real.instNeg (Real.sin qz150)))) Bool.false 23176570671 34359738368 14186007623 19653770346496 Bool.false 7289949051 34359738368 14136984363 19653770346496 (BSN.cpow_neg_s_mk qz151 81143 1000 2 qz152 rfl)

noncomputable def ep510 := nat_lit 13739091737463338076642898879200177197588466338739395322291356684855379452160

noncomputable def ep511 := nat_lit 11663149787510043615569031428700026548431852213144148096920137839076925696

noncomputable def ep512 := nat_lit 35964452307986107272972861489877806903081855507400944842415682522881774018816

noncomputable def ep513 := BSN.sin_dyadic_bound_f 1359414762 1073741824 3 2 524288 162035 ep510 ep64 ep511 ep512 ep66 ep511 500131 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1359414762) qz285 0 2 ep510 ep64 ep511 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1359414762) qz286 0 2 ep512 ep66 ep511 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz153 := (Enclosure.Real.IsNear.const Bool.false 81143 1000)

noncomputable abbrev qz396 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 29488015) qz27)

noncomputable def ep514 := @Enclosure.Real.IsNear.cos_image qz150 qz396 Bool.false 29488015 524288 263 262144 Bool.false 500131 524288 1 80938 (@Enclosure.Real.IsNear.recentre' qz150 Bool.false 1843000959 32768000 81143 80938000 29488015 524288 263 262144 (@Enclosure.Real.IsNear.mulLit_ff qz151 qz21 81143 1000 0 1 181704 262144 1 80938 1843000959 32768000 81143 80938000 qz153 qz284 rfl) rfl) (Enclosure.sfrac_false_div 29488015 524288) (BSN.cos_reduce3 qz396 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 95660309668913930567680) qz29) 226375608064910080 72057594037927936 Bool.false 500131 524288 8 1000000000000000 161876 80938 (BSN.sin_reduce_arg_pos_rat_q3 29488015 524288 226375608064910080 72057594037927936 8 95660309668913930567680 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 500131 524288 95660309668913930567680 75557863725914323419136 1359414762 1073741824 162035 161876 (ep513 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep515 := nat_lit 7638012365162970061964085613523965121570673233616617022649384886181467218176

noncomputable def ep516 := nat_lit 22890710795913890098661118777714495311615155996423562771754314382866247803136

noncomputable def ep517 := BSN.cos_dyadic_bound_f 1359414762 1073741824 3 2 524288 162035 ep515 ep57 ep511 ep516 ep60 ep511 157311 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1359414762) qz281 0 2 ep515 ep57 ep511 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1359414762) qz282 0 2 ep516 ep60 ep511 rfl rfl rfl rfl) rfl rfl

noncomputable def ep518 := @Enclosure.Real.IsNear.sin_image qz150 qz396 Bool.false 29488015 524288 263 262144 Bool.true 157311 524288 1 80938 (@Enclosure.Real.IsNear.recentre' qz150 Bool.false 1843000959 32768000 81143 80938000 29488015 524288 263 262144 (@Enclosure.Real.IsNear.mulLit_ff qz151 qz21 81143 1000 0 1 181704 262144 1 80938 1843000959 32768000 81143 80938000 qz153 qz284 rfl) rfl) (Enclosure.sfrac_false_div 29488015 524288) (BSN.sin_reduce3 qz396 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 95660309668913930567680) qz29) 226375608064910080 72057594037927936 Bool.false 157311 524288 8 1000000000000000 161876 80938 (BSN.sin_reduce_arg_pos_rat_q3 29488015 524288 226375608064910080 72057594037927936 8 95660309668913930567680 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 157311 524288 95660309668913930567680 75557863725914323419136 1359414762 1073741824 162035 161876 (ep517 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep519 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz15 (Real.cos qz150)) (@HMul.hMul Real Real Real qz0 qz15 (@Neg.neg Real Real.instNeg (Real.sin qz150))) Bool.false 23176570671 34359738368 14186007623 19653770346496 Bool.false 7289949051 34359738368 14136984363 19653770346496 (@Enclosure.Real.IsNear.mulLit_ff qz15 (Real.cos qz150) 46341 65536 1 262144 500131 524288 10774419 10608705536 23176570671 34359738368 14186007623 19653770346496 qz287 (@Enclosure.Real.IsNear.recentre' (Real.cos qz150) Bool.false 500131 524288 21548838 21217411072 500131 524288 10774419 10608705536 (ep514 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz15 (@Neg.neg Real Real.instNeg (Real.sin qz150)) 46341 65536 1 262144 157311 524288 10774419 10608705536 7289949051 34359738368 14136984363 19653770346496 qz287 (@Enclosure.Real.IsNear.neg (Real.sin qz150) Bool.true 157311 524288 10774419 10608705536 (@Enclosure.Real.IsNear.recentre' (Real.sin qz150) Bool.true 157311 524288 21548838 21217411072 157311 524288 10774419 10608705536 (ep518 rfl rfl) rfl)) rfl)

noncomputable def ep520 := @ep507 23176570671 34359738368 14186007623 19653770346496 Bool.false 7289949051 34359738368 14136984363 19653770346496 Bool.false 57536309039 57536309039 34359738368 14186007623 19653770346496 Bool.false 7289949051 7289949051 34359738368 14136984363 19653770346496 (ep508 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 1) qz14 Bool.false 1 1 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 1) qz24)) (ep509 ep519) rfl rfl

noncomputable abbrev qz154 := (@HMul.hMul Real Real Real qz266 qz394 (Real.log (Enclosure.sfrac Bool.false 3 1)))

noncomputable def ep521 := @Enclosure.Complex.IsNear.of_eq qz148 (Complex.mk (@HMul.hMul Real Real Real qz0 qz25 (Real.cos qz154)) (@HMul.hMul Real Real Real qz0 qz25 (@Neg.neg Real Real.instNeg (Real.sin qz154)))) Bool.false 30233022193 137438953472 3269500597333 5562017008058368 Bool.true 73365065609 137438953472 3281033614829 5562017008058368 (BSN.cpow_neg_s_mk qz151 81143 1000 3 qz152 rfl)

noncomputable def ep522 := nat_lit 5759766542127135822752118380814047292549792073628635271402979663786188800000

noncomputable def ep523 := nat_lit 6637289177414205011119071022683139775870909774944665937843261465600000000

noncomputable def ep524 := nat_lit 17266025048026579058234117000396775598097634401336016482333252468427366400000

noncomputable def ep525 := BSN.cos_dyadic_bound_f 1266918980 1073741824 3 2 524288 162035 ep522 ep57 ep523 ep524 ep60 ep523 199757 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1266918980) qz281 0 2 ep522 ep57 ep523 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1266918980) qz282 0 2 ep524 ep60 ep523 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz397 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 23368697) qz20)

noncomputable def ep526 := @Enclosure.Real.IsNear.cos_image qz154 qz397 Bool.false 23368697 262144 263 262144 Bool.false 199757 524288 1 80938 (@Enclosure.Real.IsNear.recentre' qz154 Bool.false 11684348571 131072000 81143 80938000 23368697 262144 263 262144 (@Enclosure.Real.IsNear.mulLit_ff qz151 qz28 81143 1000 0 1 287994 262144 1 80938 11684348571 131072000 81143 80938000 qz153 qz291 rfl) rfl) (Enclosure.sfrac_false_div 23368697 262144) (BSN.cos_reduce0 qz397 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 44575748810892759793664) qz23) 226375608064910080 72057594037927936 Bool.false 199757 524288 14 1000000000000000 161876 80938 (BSN.sin_reduce_arg_pos_rat_q0 23368697 262144 226375608064910080 72057594037927936 14 44575748810892759793664 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 199757 524288 44575748810892759793664 37778931862957161709568 1266918980 1073741824 162035 161876 (ep525 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep527 := nat_lit 10362269944486913116944917828647138614768929004711587755775088785642659840000

noncomputable def ep528 := nat_lit 27128532338797530402932972960039114145710070682228057520273486300976947200000

noncomputable def ep529 := BSN.sin_dyadic_bound_f 1266918980 1073741824 3 2 524288 162035 ep527 ep64 ep523 ep528 ep66 ep523 484741 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1266918980) qz285 0 2 ep527 ep64 ep523 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1266918980) qz286 0 2 ep528 ep66 ep523 rfl rfl rfl rfl) rfl rfl

noncomputable def ep530 := @Enclosure.Real.IsNear.sin_image qz154 qz397 Bool.false 23368697 262144 263 262144 Bool.false 484741 524288 1 80938 (@Enclosure.Real.IsNear.recentre' qz154 Bool.false 11684348571 131072000 81143 80938000 23368697 262144 263 262144 (@Enclosure.Real.IsNear.mulLit_ff qz151 qz28 81143 1000 0 1 287994 262144 1 80938 11684348571 131072000 81143 80938000 qz153 qz291 rfl) rfl) (Enclosure.sfrac_false_div 23368697 262144) (BSN.sin_reduce0 qz397 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 44575748810892759793664) qz23) 226375608064910080 72057594037927936 Bool.false 484741 524288 14 1000000000000000 161876 80938 (BSN.sin_reduce_arg_pos_rat_q0 23368697 262144 226375608064910080 72057594037927936 14 44575748810892759793664 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 484741 524288 44575748810892759793664 37778931862957161709568 1266918980 1073741824 162035 161876 (ep529 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep531 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz25 (Real.cos qz154)) (@HMul.hMul Real Real Real qz0 qz25 (@Neg.neg Real Real.instNeg (Real.sin qz154))) Bool.false 30233022193 137438953472 3269500597333 5562017008058368 Bool.true 73365065609 137438953472 3281033614829 5562017008058368 (@Enclosure.Real.IsNear.mulLit_ff qz25 (Real.cos qz154) 151349 262144 1 262144 199757 524288 10774419 10608705536 30233022193 137438953472 3269500597333 5562017008058368 qz292 (@Enclosure.Real.IsNear.recentre' (Real.cos qz154) Bool.false 199757 524288 21548838 21217411072 199757 524288 10774419 10608705536 (ep526 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz25 (@Neg.neg Real Real.instNeg (Real.sin qz154)) 151349 262144 1 262144 484741 524288 10774419 10608705536 73365065609 137438953472 3281033614829 5562017008058368 qz292 (@Enclosure.Real.IsNear.neg (Real.sin qz154) Bool.false 484741 524288 10774419 10608705536 (@Enclosure.Real.IsNear.recentre' (Real.sin qz154) Bool.false 484741 524288 21548838 21217411072 484741 524288 10774419 10608705536 (ep530 rfl rfl) rfl)) rfl)

noncomputable def ep532 := @ep505 30233022193 137438953472 3269500597333 5562017008058368 Bool.true 73365065609 137438953472 3281033614829 5562017008058368 Bool.false 8946528833587151634432 260378258349 137438953472 3642070377321 2781008504029184 Bool.true 1518881491242755031040 44205269405 137438953472 3640900094779 2781008504029184 (ep506 (BSN.head_sum_c_succ qz142 2 3 rfl rfl) (ep520 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep521 ep531) rfl rfl

noncomputable abbrev qz155 := (@HMul.hMul Real Real Real qz266 qz394 (Real.log (Enclosure.sfrac Bool.false 4 1)))

noncomputable def ep533 := @Enclosure.Complex.IsNear.of_eq qz147 (Complex.mk (@HMul.hMul Real Real Real qz0 qz30 (Real.cos qz155)) (@HMul.hMul Real Real Real qz0 qz30 (@Neg.neg Real Real.instNeg (Real.sin qz155)))) Bool.false 56345802849 137438953472 2838452175371 5562017008058368 Bool.false 39337965009 137438953472 2835826546651 5562017008058368 (BSN.cpow_neg_s_mk qz151 81143 1000 4 qz152 rfl)

noncomputable def ep534 := nat_lit 4564140437311572389727489840584924607729092193948700040264775357540255989760

noncomputable def ep535 := nat_lit 1288576494933191175770928098837346901115327212375705161862838318645968896

noncomputable def ep536 := nat_lit 11951614878633750139763606175086208744307721406759891820907586102946672214016

noncomputable def ep537 := BSN.sin_dyadic_bound_f 1032199812 1073741824 3 2 524288 162035 ep534 ep64 ep535 ep536 ep66 ep535 429886 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1032199812) qz285 0 2 ep534 ep64 ep535 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1032199812) qz286 0 2 ep536 ep66 ep535 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz398 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 29488015) qz20)

noncomputable def ep538 := @Enclosure.Real.IsNear.cos_image qz155 qz398 Bool.false 29488015 262144 527 524288 Bool.false 429886 524288 1 80938 (@Enclosure.Real.IsNear.recentre' qz155 Bool.false 1843000959 16384000 81143 80938000 29488015 262144 527 524288 (@Enclosure.Real.IsNear.mulLit_ff qz151 qz32 81143 1000 0 1 363408 262144 1 80938 1843000959 16384000 81143 80938000 qz153 qz295 rfl) rfl) (Enclosure.sfrac_false_div 29488015 262144) (BSN.cos_reduce3 qz398 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 36317302268346142556160) qz23) 226375608064910080 72057594037927936 Bool.false 429886 524288 17 1000000000000000 161876 80938 (BSN.sin_reduce_arg_pos_rat_q3 29488015 262144 226375608064910080 72057594037927936 17 36317302268346142556160 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 429886 524288 36317302268346142556160 37778931862957161709568 1032199812 1073741824 162035 161876 (ep537 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep539 := nat_lit 2536206276948621634815614768368885825138880253177000335774592015663984869376

noncomputable def ep540 := nat_lit 7606041677855998522095302448908982781614410105106249597000050370354662670336

noncomputable def ep541 := BSN.cos_dyadic_bound_f 1032199812 1073741824 3 2 524288 162035 ep539 ep57 ep535 ep540 ep60 ep535 300126 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1032199812) qz281 0 2 ep539 ep57 ep535 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1032199812) qz282 0 2 ep540 ep60 ep535 rfl rfl rfl rfl) rfl rfl

noncomputable def ep542 := @Enclosure.Real.IsNear.sin_image qz155 qz398 Bool.false 29488015 262144 527 524288 Bool.true 300126 524288 1 80938 (@Enclosure.Real.IsNear.recentre' qz155 Bool.false 1843000959 16384000 81143 80938000 29488015 262144 527 524288 (@Enclosure.Real.IsNear.mulLit_ff qz151 qz32 81143 1000 0 1 363408 262144 1 80938 1843000959 16384000 81143 80938000 qz153 qz295 rfl) rfl) (Enclosure.sfrac_false_div 29488015 262144) (BSN.sin_reduce3 qz398 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 36317302268346142556160) qz23) 226375608064910080 72057594037927936 Bool.false 300126 524288 17 1000000000000000 161876 80938 (BSN.sin_reduce_arg_pos_rat_q3 29488015 262144 226375608064910080 72057594037927936 17 36317302268346142556160 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 300126 524288 36317302268346142556160 37778931862957161709568 1032199812 1073741824 162035 161876 (ep541 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep543 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz30 (Real.cos qz155)) (@HMul.hMul Real Real Real qz0 qz30 (@Neg.neg Real Real.instNeg (Real.sin qz155))) Bool.false 56345802849 137438953472 2838452175371 5562017008058368 Bool.false 39337965009 137438953472 2835826546651 5562017008058368 (@Enclosure.Real.IsNear.mulLit_ff qz30 (Real.cos qz155) 262143 524288 1 524288 214943 262144 21589307 21217411072 56345802849 137438953472 2838452175371 5562017008058368 qz297 (@Enclosure.Real.IsNear.recentre' (Real.cos qz155) Bool.false 429886 524288 43178614 42434822144 214943 262144 21589307 21217411072 (ep538 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz30 (@Neg.neg Real Real.instNeg (Real.sin qz155)) 262143 524288 1 524288 150063 262144 21589307 21217411072 39337965009 137438953472 2835826546651 5562017008058368 qz297 (@Enclosure.Real.IsNear.neg (Real.sin qz155) Bool.true 150063 262144 21589307 21217411072 (@Enclosure.Real.IsNear.recentre' (Real.sin qz155) Bool.true 300126 524288 43178614 42434822144 150063 262144 21589307 21217411072 (ep542 rfl rfl) rfl)) rfl)

noncomputable def ep544 := @ep503 56345802849 137438953472 2838452175371 5562017008058368 Bool.false 39337965009 137438953472 2835826546651 5562017008058368 Bool.false 43530223510454802579456 158362030599 68719476736 10122592930013 5562017008058368 Bool.true 668957222415905062912 1216826099 34359738368 10117626736209 5562017008058368 (ep504 (BSN.head_sum_c_succ qz142 3 4 rfl rfl) (ep532 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep533 ep543) rfl rfl

noncomputable abbrev qz156 := (@HMul.hMul Real Real Real qz266 qz394 (Real.log (Enclosure.sfrac Bool.false 5 1)))

noncomputable def ep545 := @Enclosure.Complex.IsNear.of_eq qz146 (Complex.mk (@HMul.hMul Real Real Real qz0 qz33 (Real.cos qz156)) (@HMul.hMul Real Real Real qz0 qz33 (@Neg.neg Real Real.instNeg (Real.sin qz156)))) Bool.false 13315728979 137438953472 633330170281 1390504252014592 Bool.false 30002418771 68719476736 2541379151687 5562017008058368 (BSN.cpow_neg_s_mk qz151 81143 1000 5 qz152 rfl)

noncomputable def ep546 := nat_lit 3022648128703419761032621291763361

noncomputable def ep547 := BSN.sin_dyadic_bound_f 234475191 1073741824 2 1 524288 162035 ep546 ep86 ep546 ep546 ep87 ep546 113582 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 234475191) qz285 0 1 ep546 ep86 ep546 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 234475191) qz286 0 1 ep546 ep87 ep546 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz399 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 8558639) (@Nat.cast Real Real.instNatCast 65536))

noncomputable def ep548 := @Enclosure.Real.IsNear.cos_image qz156 qz399 Bool.false 8558639 65536 527 524288 Bool.false 113582 524288 1 80938 (@Enclosure.Real.IsNear.recentre' qz156 Bool.false 2139659767 16384000 81143 80938000 8558639 65536 527 524288 (@Enclosure.Real.IsNear.mulLit_ff qz151 qz35 81143 1000 0 1 421904 262144 1 80938 2139659767 16384000 81143 80938000 qz153 qz300 rfl) rfl) (Enclosure.sfrac_false_div 8558639 65536) (BSN.cos_reduce3 qz399 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 2062465596573423239168) qz351) 226375608064910080 72057594037927936 Bool.false 113582 524288 20 1000000000000000 161876 80938 (BSN.sin_reduce_arg_pos_rat_q3 8558639 65536 226375608064910080 72057594037927936 20 2062465596573423239168 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 113582 524288 2062465596573423239168 9444732965739290427392 234475191 1073741824 162035 161876 (ep547 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep549 := BSN.cos_dyadic_bound_f 234475191 1073741824 2 1 524288 162035 ep546 ep90 ep546 ep546 ep91 ep546 511836 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 234475191) qz281 0 1 ep546 ep90 ep546 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 234475191) qz282 0 1 ep546 ep91 ep546 rfl rfl rfl rfl) rfl rfl

noncomputable def ep550 := @Enclosure.Real.IsNear.sin_image qz156 qz399 Bool.false 8558639 65536 527 524288 Bool.true 511836 524288 1 80938 (@Enclosure.Real.IsNear.recentre' qz156 Bool.false 2139659767 16384000 81143 80938000 8558639 65536 527 524288 (@Enclosure.Real.IsNear.mulLit_ff qz151 qz35 81143 1000 0 1 421904 262144 1 80938 2139659767 16384000 81143 80938000 qz153 qz300 rfl) rfl) (Enclosure.sfrac_false_div 8558639 65536) (BSN.sin_reduce3 qz399 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 2062465596573423239168) qz351) 226375608064910080 72057594037927936 Bool.false 511836 524288 20 1000000000000000 161876 80938 (BSN.sin_reduce_arg_pos_rat_q3 8558639 65536 226375608064910080 72057594037927936 20 2062465596573423239168 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 511836 524288 2062465596573423239168 9444732965739290427392 234475191 1073741824 162035 161876 (ep549 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep551 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz33 (Real.cos qz156)) (@HMul.hMul Real Real Real qz0 qz33 (@Neg.neg Real Real.instNeg (Real.sin qz156))) Bool.false 13315728979 137438953472 633330170281 1390504252014592 Bool.false 30002418771 68719476736 2541379151687 5562017008058368 (@Enclosure.Real.IsNear.mulLit_ff qz33 (Real.cos qz156) 234469 524288 1 524288 56791 262144 21589307 21217411072 13315728979 137438953472 633330170281 1390504252014592 qz301 (@Enclosure.Real.IsNear.recentre' (Real.cos qz156) Bool.false 113582 524288 43178614 42434822144 56791 262144 21589307 21217411072 (ep548 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz33 (@Neg.neg Real Real.instNeg (Real.sin qz156)) 234469 524288 1 524288 127959 131072 21589307 21217411072 30002418771 68719476736 2541379151687 5562017008058368 qz301 (@Enclosure.Real.IsNear.neg (Real.sin qz156) Bool.true 127959 131072 21589307 21217411072 (@Enclosure.Real.IsNear.recentre' (Real.sin qz156) Bool.true 511836 524288 43178614 42434822144 127959 131072 21589307 21217411072 (ep550 rfl rfl) rfl)) rfl)

noncomputable def ep552 := @ep501 13315728979 137438953472 633330170281 1390504252014592 Bool.false 30002418771 68719476736 2541379151687 5562017008058368 Bool.false 22680161683022672822272 330039790177 137438953472 12655913611137 5562017008058368 Bool.false 947255606576743972864 27568766573 68719476736 1582375735987 695252126007296 (ep502 (BSN.head_sum_c_succ qz142 4 5 rfl rfl) (ep544 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep545 ep551) rfl rfl

noncomputable abbrev qz157 := (@HMul.hMul Real Real Real qz266 qz394 (Real.log (Enclosure.sfrac Bool.false 6 1)))

noncomputable def ep553 := @Enclosure.Complex.IsNear.of_eq qz145 (Complex.mk (@HMul.hMul Real Real Real qz0 qz36 (Real.cos qz157)) (@HMul.hMul Real Real Real qz0 qz36 (@Neg.neg Real Real.instNeg (Real.sin qz157)))) Bool.false 71896770295 274877906944 4625907024965 11124034016116736 Bool.true 86160757333 274877906944 4628603960063 11124034016116736 (BSN.cpow_neg_s_mk qz151 81143 1000 6 qz152 rfl)

noncomputable def ep554 := @Enclosure.Real.IsNear.mulLit_ff qz151 qz38 81143 1000 0 1 4034681531866359 2251799813685248 250000000040469 20234500000000000000 327386163540231968337 2251799813685248000 20285750003283776067 20234500000000000000000 qz153 (BSN.isNear_log_sfrac 6 1 4034681531866359 2251799813685248 250000000040469 20234500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz303) Bool.false 16922680887833197019136 9444732965739290427392 1000000000161876 80938000000000000000 4034681531866359 2251799813685248 250000000040469 20234500000000000000 (BSN.log_rat_reduce_isNear 6 1 2 12 8 106290 262144 24973259072661432 36028797018963968 80938 1000000000000000 rfl rfl rfl rfl (ep115 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep555 := nat_lit 1743760092789158203886499987961410558073063452764476878788741073083792190625

noncomputable def ep556 := nat_lit 609329743261029115451688242647286728015506675084261563971851079875390625

noncomputable def ep557 := nat_lit 5230061618880952553428596587398937100763159344943262113238279517091625790625

noncomputable def ep558 := BSN.cos_dyadic_bound_f 939953885 1073741824 3 2 524288 162035 ep555 ep57 ep556 ep557 ep60 ep556 335905 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 939953885) qz281 0 2 ep555 ep57 ep556 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 939953885) qz282 0 2 ep557 ep60 ep556 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz400 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 76225531) qz27)

noncomputable def ep559 := @Enclosure.Real.IsNear.cos_image qz157 qz400 Bool.false 76225531 524288 263 262144 Bool.false 335905 524288 1 80938 (@Enclosure.Real.IsNear.recentre' qz157 Bool.false 327386163540231968337 2251799813685248000 20285750003283776067 20234500000000000000000 76225531 524288 263 262144 (ep554 rfl) rfl) (Enclosure.sfrac_false_div 76225531 524288) (BSN.cos_reduce0 qz400 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 66143374542509128548352) qz29) 226375608064910080 72057594037927936 Bool.false 335905 524288 23 1000000000000000 161876 80938 (BSN.sin_reduce_arg_pos_rat_q0 76225531 524288 226375608064910080 72057594037927936 23 66143374542509128548352 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 335905 524288 66143374542509128548352 75557863725914323419136 939953885 1073741824 162035 161876 (ep558 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep560 := nat_lit 780595761749337911079292254615900625

noncomputable def ep561 := BSN.sin_dyadic_bound_f 939953885 1073741824 2 1 524288 162035 ep560 ep86 ep560 ep560 ep87 ep560 402547 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 939953885) qz285 0 1 ep560 ep86 ep560 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 939953885) qz286 0 1 ep560 ep87 ep560 rfl rfl rfl rfl) rfl rfl

noncomputable def ep562 := @Enclosure.Real.IsNear.sin_image qz157 qz400 Bool.false 76225531 524288 263 262144 Bool.false 402547 524288 1 80938 (@Enclosure.Real.IsNear.recentre' qz157 Bool.false 327386163540231968337 2251799813685248000 20285750003283776067 20234500000000000000000 76225531 524288 263 262144 (ep554 rfl) rfl) (Enclosure.sfrac_false_div 76225531 524288) (BSN.sin_reduce0 qz400 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 66143374542509128548352) qz29) 226375608064910080 72057594037927936 Bool.false 402547 524288 23 1000000000000000 161876 80938 (BSN.sin_reduce_arg_pos_rat_q0 76225531 524288 226375608064910080 72057594037927936 23 66143374542509128548352 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 402547 524288 66143374542509128548352 75557863725914323419136 939953885 1073741824 162035 161876 (ep561 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep563 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz36 (Real.cos qz157)) (@HMul.hMul Real Real Real qz0 qz36 (@Neg.neg Real Real.instNeg (Real.sin qz157))) Bool.false 71896770295 274877906944 4625907024965 11124034016116736 Bool.true 86160757333 274877906944 4628603960063 11124034016116736 (@Enclosure.Real.IsNear.mulLit_ff qz36 (Real.cos qz157) 214039 524288 1 524288 335905 524288 10774419 10608705536 71896770295 274877906944 4625907024965 11124034016116736 qz305 (@Enclosure.Real.IsNear.recentre' (Real.cos qz157) Bool.false 335905 524288 21548838 21217411072 335905 524288 10774419 10608705536 (ep559 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz36 (@Neg.neg Real Real.instNeg (Real.sin qz157)) 214039 524288 1 524288 402547 524288 10774419 10608705536 86160757333 274877906944 4628603960063 11124034016116736 qz305 (@Enclosure.Real.IsNear.neg (Real.sin qz157) Bool.false 402547 524288 10774419 10608705536 (@Enclosure.Real.IsNear.recentre' (Real.sin qz157) Bool.false 402547 524288 21548838 21217411072 402547 524288 10774419 10608705536 (ep562 rfl rfl) rfl)) rfl)

noncomputable def ep564 := @ep499 71896770295 274877906944 4625907024965 11124034016116736 Bool.true 86160757333 274877906944 4628603960063 11124034016116736 Bool.false 100602063599452268003328 731976350649 274877906944 2302902634403 855694924316672 Bool.false 1657122693512716877824 24114308959 274877906944 2303585825835 855694924316672 (ep500 (BSN.head_sum_c_succ qz142 5 6 rfl rfl) (ep552 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep553 ep563) rfl rfl

noncomputable abbrev qz158 := (@HMul.hMul Real Real Real qz266 qz394 (Real.log (Enclosure.sfrac Bool.false 7 1)))

noncomputable def ep565 := @Enclosure.Complex.IsNear.of_eq qz144 (Complex.mk (@HMul.hMul Real Real Real qz0 qz39 (Real.cos qz158)) (@HMul.hMul Real Real Real qz0 qz39 (@Neg.neg Real Real.instNeg (Real.sin qz158)))) Bool.false 35550640363 137438953472 2142362145785 5562017008058368 Bool.true 9469218955 34359738368 133927325711 347626063003648 (BSN.cpow_neg_s_mk qz151 81143 1000 7 qz152 rfl)

noncomputable def ep566 := @Enclosure.Real.IsNear.mulLit_ff qz151 qz41 81143 1000 0 1 4381792198794487 2251799813685248 250000000040469 20234500000000000000 355551764386781058641 2251799813685248000 20285750003283776067 20234500000000000000000 qz153 (BSN.isNear_log_sfrac 7 1 4381792198794487 2251799813685248 250000000040469 20234500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz307) Bool.false 18378568546572512002048 9444732965739290427392 1000000000161876 80938000000000000000 4381792198794487 2251799813685248 250000000040469 20234500000000000000 (BSN.log_rat_reduce_isNear 7 1 2 14 8 146699 262144 24973259072661432 36028797018963968 80938 1000000000000000 rfl rfl rfl rfl (ep130 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep567 := nat_lit 1323301050794422768859026055461137603502765498920406706564853694621934314081

noncomputable def ep568 := nat_lit 350969511989400756309754856832454448770829188373037654182834767593890401

noncomputable def ep569 := nat_lit 3969201213359289505064458656669747901610754838384474044386195414330615161441

noncomputable def ep570 := BSN.cos_dyadic_bound_f 877321301 1073741824 3 2 524288 162035 ep567 ep57 ep568 ep569 ep60 ep568 358802 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 877321301) qz281 0 2 ep567 ep57 ep568 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 877321301) qz282 0 2 ep569 ep60 ep568 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz401 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 41391673) qz20)

noncomputable def ep571 := @Enclosure.Real.IsNear.cos_image qz158 qz401 Bool.false 41391673 262144 263 262144 Bool.false 358802 524288 1 80938 (@Enclosure.Real.IsNear.recentre' qz158 Bool.false 355551764386781058641 2251799813685248000 20285750003283776067 20234500000000000000000 41391673 262144 263 262144 (ep566 rfl) rfl) (Enclosure.sfrac_false_div 41391673 262144) (BSN.cos_reduce0 qz401 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 30867999112546647801856) qz23) 226375608064910080 72057594037927936 Bool.false 358802 524288 25 1000000000000000 161876 80938 (BSN.sin_reduce_arg_pos_rat_q0 41391673 262144 226375608064910080 72057594037927936 25 30867999112546647801856 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 358802 524288 30867999112546647801856 37778931862957161709568 877321301 1073741824 162035 161876 (ep570 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep572 := nat_lit 592426798844718668175612498599425201

noncomputable def ep573 := BSN.sin_dyadic_bound_f 877321301 1073741824 2 1 524288 162035 ep572 ep86 ep572 ep572 ep87 ep572 382280 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 877321301) qz285 0 1 ep572 ep86 ep572 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 877321301) qz286 0 1 ep572 ep87 ep572 rfl rfl rfl rfl) rfl rfl

noncomputable def ep574 := @Enclosure.Real.IsNear.sin_image qz158 qz401 Bool.false 41391673 262144 263 262144 Bool.false 382280 524288 1 80938 (@Enclosure.Real.IsNear.recentre' qz158 Bool.false 355551764386781058641 2251799813685248000 20285750003283776067 20234500000000000000000 41391673 262144 263 262144 (ep566 rfl) rfl) (Enclosure.sfrac_false_div 41391673 262144) (BSN.sin_reduce0 qz401 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 30867999112546647801856) qz23) 226375608064910080 72057594037927936 Bool.false 382280 524288 25 1000000000000000 161876 80938 (BSN.sin_reduce_arg_pos_rat_q0 41391673 262144 226375608064910080 72057594037927936 25 30867999112546647801856 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 382280 524288 30867999112546647801856 37778931862957161709568 877321301 1073741824 162035 161876 (ep573 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep575 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz39 (Real.cos qz158)) (@HMul.hMul Real Real Real qz0 qz39 (@Neg.neg Real Real.instNeg (Real.sin qz158))) Bool.false 35550640363 137438953472 2142362145785 5562017008058368 Bool.true 9469218955 34359738368 133927325711 347626063003648 (@Enclosure.Real.IsNear.mulLit_ff qz39 (Real.cos qz158) 198163 524288 1 524288 179401 262144 10774419 10608705536 35550640363 137438953472 2142362145785 5562017008058368 qz309 (@Enclosure.Real.IsNear.recentre' (Real.cos qz158) Bool.false 358802 524288 21548838 21217411072 179401 262144 10774419 10608705536 (ep571 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz39 (@Neg.neg Real Real.instNeg (Real.sin qz158)) 198163 524288 1 524288 47785 65536 10774419 10608705536 9469218955 34359738368 133927325711 347626063003648 qz309 (@Enclosure.Real.IsNear.neg (Real.sin qz158) Bool.false 47785 65536 10774419 10608705536 (@Enclosure.Real.IsNear.recentre' (Real.sin qz158) Bool.false 382280 524288 21548838 21217411072 47785 65536 10774419 10608705536 (ep574 rfl rfl) rfl)) rfl)

noncomputable def ep576 := @ep497 35550640363 137438953472 2142362145785 5562017008058368 Bool.true 9469218955 34359738368 133927325711 347626063003648 Bool.false 110374149212952592384000 803077631375 274877906944 34222458538809 11124034016116736 Bool.true 1774317739988492484608 51639442681 274877906944 34232290158607 11124034016116736 (ep498 (BSN.head_sum_c_succ qz142 6 7 rfl rfl) (ep564 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep565 ep575) rfl rfl

noncomputable abbrev qz159 := (@HMul.hMul Real Real Real qz266 qz394 (Real.log (Enclosure.sfrac Bool.false 8 1)))

noncomputable def ep577 := @Enclosure.Complex.IsNear.of_eq qz143 (Complex.mk (@HMul.hMul Real Real Real qz0 qz42 (Real.cos qz159)) (@HMul.hMul Real Real Real qz0 qz42 (@Neg.neg Real Real.instNeg (Real.sin qz159)))) Bool.false 59347857073 274877906944 4007335807231 11124034016116736 Bool.false 76957342073 274877906944 4011180362231 11124034016116736 (BSN.cpow_neg_s_mk qz151 81143 1000 8 qz152 rfl)

noncomputable def ep578 := @Enclosure.Real.IsNear.mulLit_ff qz151 qz44 81143 1000 0 1 9364972152248037 4503599627370496 500000000121407 40469000000000000000 759901935349862466291 4503599627370496000 40571500009851328201 40469000000000000000000 qz153 (BSN.isNear_log_sfrac 8 1 9364972152248037 4503599627370496 500000000121407 40469000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz311) Bool.false 19639770079031275290624 9444732965739290427392 1000000000242814 80938000000000000000 9364972152248037 4503599627370496 500000000121407 40469000000000000000 (BSN.log_rat_reduce_isNear 8 1 3 16 16 0 262144 24973259072661432 36028797018963968 80938 1000000000000000 rfl rfl rfl rfl (ep144 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep579 := nat_lit 247538320093005219575194999739939856

noncomputable def ep580 := BSN.sin_dyadic_bound_f 705359646 1073741824 2 1 524288 162035 ep579 ep86 ep579 ep579 ep87 ep579 320171 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 705359646) qz285 0 1 ep579 ep86 ep579 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 705359646) qz286 0 1 ep579 ep87 ep579 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz402 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 22116057) qz485)

noncomputable def ep581 := @Enclosure.Real.IsNear.cos_image qz159 qz402 Bool.false 22116057 131072 263 262144 Bool.false 320171 524288 1 80938 (@Enclosure.Real.IsNear.recentre' qz159 Bool.false 759901935349862466291 4503599627370496000 40571500009851328201 40469000000000000000000 22116057 131072 263 262144 (ep578 rfl) rfl) (Enclosure.sfrac_false_div 22116057 131072) (BSN.cos_reduce3 qz402 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 12408818120972130320384) qz296) 226375608064910080 72057594037927936 Bool.false 320171 524288 26 1000000000000000 161876 80938 (BSN.sin_reduce_arg_pos_rat_q3 22116057 131072 226375608064910080 72057594037927936 26 12408818120972130320384 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 320171 524288 12408818120972130320384 18889465931478580854784 705359646 1073741824 162035 161876 (ep580 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep582 := BSN.cos_dyadic_bound_f 705359646 1073741824 2 1 524288 162035 ep579 ep90 ep579 ep579 ep91 ep579 415171 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 705359646) qz281 0 1 ep579 ep90 ep579 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 705359646) qz282 0 1 ep579 ep91 ep579 rfl rfl rfl rfl) rfl rfl

noncomputable def ep583 := @Enclosure.Real.IsNear.sin_image qz159 qz402 Bool.false 22116057 131072 263 262144 Bool.true 415171 524288 1 80938 (@Enclosure.Real.IsNear.recentre' qz159 Bool.false 759901935349862466291 4503599627370496000 40571500009851328201 40469000000000000000000 22116057 131072 263 262144 (ep578 rfl) rfl) (Enclosure.sfrac_false_div 22116057 131072) (BSN.sin_reduce3 qz402 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 12408818120972130320384) qz296) 226375608064910080 72057594037927936 Bool.false 415171 524288 26 1000000000000000 161876 80938 (BSN.sin_reduce_arg_pos_rat_q3 22116057 131072 226375608064910080 72057594037927936 26 12408818120972130320384 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 415171 524288 12408818120972130320384 18889465931478580854784 705359646 1073741824 162035 161876 (ep582 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep584 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz42 (Real.cos qz159)) (@HMul.hMul Real Real Real qz0 qz42 (@Neg.neg Real Real.instNeg (Real.sin qz159))) Bool.false 59347857073 274877906944 4007335807231 11124034016116736 Bool.false 76957342073 274877906944 4011180362231 11124034016116736 (@Enclosure.Real.IsNear.mulLit_ff qz42 (Real.cos qz159) 185363 524288 1 524288 320171 524288 10774419 10608705536 59347857073 274877906944 4007335807231 11124034016116736 qz313 (@Enclosure.Real.IsNear.recentre' (Real.cos qz159) Bool.false 320171 524288 21548838 21217411072 320171 524288 10774419 10608705536 (ep581 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz42 (@Neg.neg Real Real.instNeg (Real.sin qz159)) 185363 524288 1 524288 415171 524288 10774419 10608705536 76957342073 274877906944 4011180362231 11124034016116736 qz313 (@Enclosure.Real.IsNear.neg (Real.sin qz159) Bool.true 415171 524288 10774419 10608705536 (@Enclosure.Real.IsNear.recentre' (Real.sin qz159) Bool.true 415171 524288 21548838 21217411072 415171 524288 10774419 10608705536 (ep583 rfl rfl) rfl)) rfl)

noncomputable def ep585 := @ep495 59347857073 274877906944 4007335807231 11124034016116736 Bool.false 76957342073 274877906944 4011180362231 11124034016116736 Bool.false 237061713159743090982912 13475398257 4294967296 434429481205 126409477455872 Bool.false 6959331193091730178048 197796089 2147483648 1738339569129 505637909823488 (ep496 (BSN.head_sum_c_succ qz142 7 8 rfl rfl) (ep576 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep577 ep584) rfl rfl

theorem EMRow21.d10 : Enclosure.Complex.IsNear qz141 Bool.false 13475398257 4294967296 434429481205 126409477455872 Bool.false 197796089 2147483648 1738339569129 505637909823488 := ep494 (BSN.head_sum_c_succ qz142 8 9 rfl rfl) (ep585 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable abbrev qz160 := (@HPow.hPow Complex Complex Complex qz273 qz353 qz393)

noncomputable def ep586 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz142 17) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz142 16) qz160) Bool.false 1149508361535 274877906944 64279047989205 11124034016116736 Bool.false 8433164951 274877906944 64276257570717 11124034016116736

noncomputable def ep587 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz142 16) qz160 Bool.false 140724620285 34359738368 7680246662207 1390504252014592 Bool.true 56065301297 274877906944 61426589614341 11124034016116736 Bool.false

noncomputable abbrev qz161 := (@HPow.hPow Complex Complex Complex qz273 (@Nat.cast Complex Complex.instNatCast 15) qz393)

noncomputable def ep588 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz142 16) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz142 15) qz161) Bool.false 140724620285 34359738368 7680246662207 1390504252014592 Bool.true 56065301297 274877906944 61426589614341 11124034016116736

noncomputable def ep589 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz142 15) qz161 Bool.false 1055876622441 274877906944 58498483027731 11124034016116736 Bool.true 34122924253 137438953472 29250180293493 5562017008058368 Bool.false

noncomputable abbrev qz162 := (@HPow.hPow Complex Complex Complex qz273 (@Nat.cast Complex Complex.instNatCast 14) qz393)

noncomputable def ep590 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz142 15) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz142 14) qz162) Bool.false 1055876622441 274877906944 58498483027731 11124034016116736 Bool.true 34122924253 137438953472 29250180293493 5562017008058368

noncomputable def ep591 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz142 14) qz162 Bool.false 991849452459 274877906944 55460524763697 11124034016116736 Bool.true 8056516001 68719476736 3466905704167 695252126007296 Bool.false

noncomputable abbrev qz163 := (@HPow.hPow Complex Complex Complex qz273 (@Nat.cast Complex Complex.instNatCast 13) qz393)

noncomputable def ep592 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz142 14) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz142 13) qz163) Bool.false 991849452459 274877906944 55460524763697 11124034016116736 Bool.true 8056516001 68719476736 3466905704167 695252126007296

noncomputable def ep593 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz142 13) qz163 Bool.false 937773428135 274877906944 4755637759895 1011275819646976 Bool.false 10756448811 137438953472 2378276166771 505637909823488 Bool.false

noncomputable abbrev qz164 := (@HPow.hPow Complex Complex Complex qz273 (@Nat.cast Complex Complex.instNatCast 12) qz393)

noncomputable def ep594 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz142 13) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz142 12) qz164) Bool.false 937773428135 274877906944 4755637759895 1011275819646976 Bool.false 10756448811 137438953472 2378276166771 505637909823488

noncomputable def ep595 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz142 12) qz164 Bool.false 54437589229 17179869184 24516372327297 5562017008058368 Bool.false 32192310379 137438953472 24524597813423 5562017008058368 Bool.false

noncomputable abbrev qz165 := (@HPow.hPow Complex Complex Complex qz273 (@Nat.cast Complex Complex.instNatCast 11) qz393)

noncomputable def ep596 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz142 12) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz142 11) qz165) Bool.false 54437589229 17179869184 24516372327297 5562017008058368 Bool.false 32192310379 137438953472 24524597813423 5562017008058368

noncomputable def ep597 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz142 11) qz165 Bool.false 789884295367 274877906944 4145376419997 1011275819646976 Bool.false 11846754551 68719476736 129636382121 31602369363968 Bool.false

noncomputable abbrev qz166 := (@HPow.hPow Complex Complex Complex qz273 (@Nat.cast Complex Complex.instNatCast 10) qz393)

noncomputable def ep598 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz142 11) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz142 10) qz166) Bool.false 789884295367 274877906944 4145376419997 1011275819646976 Bool.false 11846754551 68719476736 129636382121 31602369363968

noncomputable def ep599 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz142 10) qz166 Bool.false 797379224137 274877906944 42017890434981 11124034016116736 Bool.true 39213513121 274877906944 42031447388105 11124034016116736 Bool.true

noncomputable abbrev qz167 := (@HPow.hPow Complex Complex Complex qz273 (@Nat.cast Complex Complex.instNatCast 9) qz393)

noncomputable def ep600 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz142 10) (@HAdd.hAdd Complex Complex Complex qz5 qz141 qz167) Bool.false 797379224137 274877906944 42017890434981 11124034016116736 Bool.true 39213513121 274877906944 42031447388105 11124034016116736

noncomputable def ep601 := @Enclosure.Complex.IsNear.addLitP qz141 qz167 Bool.false 13475398257 4294967296 434429481205 126409477455872 Bool.false 197796089 2147483648 1738339569129 505637909823488 Bool.true

noncomputable abbrev qz168 := (@HMul.hMul Real Real Real qz266 qz394 (Real.log (Enclosure.sfrac Bool.false 9 1)))

noncomputable def ep602 := @Enclosure.Complex.IsNear.of_eq qz167 (Complex.mk (@HMul.hMul Real Real Real qz0 qz108 (Real.cos qz168)) (@HMul.hMul Real Real Real qz0 qz108 (@Neg.neg Real Real.instNeg (Real.sin qz168)))) Bool.true 65046264311 274877906944 3788096088941 11124034016116736 Bool.true 64531412513 274877906944 3787976867267 11124034016116736 (BSN.cpow_neg_s_mk qz151 81143 1000 9 qz152 rfl)

noncomputable def ep603 := @Enclosure.Real.IsNear.mulLit_ff qz151 qz110 81143 1000 0 1 9895417793173221 4503599627370496 500000000121407 40469000000000000000 802943885991454671603 4503599627370496000 40571500009851328201 40469000000000000000000 qz153 (BSN.isNear_log_sfrac 9 1 9895417793173221 4503599627370496 500000000121407 40469000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz356) Bool.false 20752195215788806766592 9444732965739290427392 1000000000242814 80938000000000000000 9895417793173221 4503599627370496 500000000121407 40469000000000000000 (BSN.log_rat_reduce_isNear 9 1 3 18 16 30876 262144 24973259072661432 36028797018963968 80938 1000000000000000 rfl rfl rfl rfl (ep328 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep604 := nat_lit 516089253519451123088694762112271521

noncomputable def ep605 := BSN.sin_dyadic_bound_f 847580983 1073741824 2 1 524288 162035 ep604 ep86 ep604 ep604 ep87 ep604 372197 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 847580983) qz285 0 1 ep604 ep86 ep604 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 847580983) qz286 0 1 ep604 ep87 ep604 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz403 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 46737485) qz20)

noncomputable def ep606 := @Enclosure.Real.IsNear.cos_image qz168 qz403 Bool.false 46737485 262144 527 524288 Bool.true 372197 524288 1 80938 (@Enclosure.Real.IsNear.recentre' qz168 Bool.false 802943885991454671603 4503599627370496000 40571500009851328201 40469000000000000000000 46737485 262144 527 524288 (ep603 rfl) rfl) (Enclosure.sfrac_false_div 46737485 262144) (BSN.cos_reduce1 qz403 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 29821604703332634460160) qz23) 226375608064910080 72057594037927936 Bool.false 372197 524288 28 1000000000000000 161876 80938 (BSN.sin_reduce_arg_pos_rat_q1 46737485 262144 226375608064910080 72057594037927936 28 29821604703332634460160 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 372197 524288 29821604703332634460160 37778931862957161709568 847580983 1073741824 162035 161876 (ep605 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep607 := nat_lit 1152746825408611103660618755448753956074720739351397460176481675937149414721

noncomputable def ep608 := nat_lit 266348117598264293439540534325176139386868974154888601681550898427653441

noncomputable def ep609 := nat_lit 3457707779990636782394977185277611515945388480105882603326081926014592937281

noncomputable def ep610 := BSN.cos_dyadic_bound_f 847580983 1073741824 3 2 524288 162035 ep607 ep57 ep608 ep609 ep60 ep608 369251 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 847580983) qz281 0 2 ep607 ep57 ep608 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 847580983) qz282 0 2 ep609 ep60 ep608 rfl rfl rfl rfl) rfl rfl

noncomputable def ep611 := @Enclosure.Real.IsNear.sin_image qz168 qz403 Bool.false 46737485 262144 527 524288 Bool.false 369251 524288 1 80938 (@Enclosure.Real.IsNear.recentre' qz168 Bool.false 802943885991454671603 4503599627370496000 40571500009851328201 40469000000000000000000 46737485 262144 527 524288 (ep603 rfl) rfl) (Enclosure.sfrac_false_div 46737485 262144) (BSN.sin_reduce1 qz403 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 29821604703332634460160) qz23) 226375608064910080 72057594037927936 Bool.false 369251 524288 28 1000000000000000 161876 80938 (BSN.sin_reduce_arg_pos_rat_q1 46737485 262144 226375608064910080 72057594037927936 28 29821604703332634460160 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 369251 524288 29821604703332634460160 37778931862957161709568 847580983 1073741824 162035 161876 (ep610 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep612 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz108 (Real.cos qz168)) (@HMul.hMul Real Real Real qz0 qz108 (@Neg.neg Real Real.instNeg (Real.sin qz168))) Bool.true 65046264311 274877906944 3788096088941 11124034016116736 Bool.true 64531412513 274877906944 3787976867267 11124034016116736 (@Enclosure.Real.IsNear.mulLit_ft qz108 (Real.cos qz168) 174763 524288 1 524288 372197 524288 21589307 21217411072 65046264311 274877906944 3788096088941 11124034016116736 qz359 (@Enclosure.Real.IsNear.recentre' (Real.cos qz168) Bool.true 372197 524288 43178614 42434822144 372197 524288 21589307 21217411072 (ep606 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz108 (@Neg.neg Real Real.instNeg (Real.sin qz168)) 174763 524288 1 524288 369251 524288 21589307 21217411072 64531412513 274877906944 3787976867267 11124034016116736 qz359 (@Enclosure.Real.IsNear.neg (Real.sin qz168) Bool.false 369251 524288 21589307 21217411072 (@Enclosure.Real.IsNear.recentre' (Real.sin qz168) Bool.false 369251 524288 43178614 42434822144 369251 524288 21589307 21217411072 (ep611 rfl rfl) rfl)) rfl)

noncomputable def ep613 := @ep601 65046264311 274877906944 3788096088941 11124034016116736 Bool.true 64531412513 274877906944 3787976867267 11124034016116736 Bool.false 3424717690178268823552 797379224137 274877906944 42017890434981 11124034016116736 Bool.true 84210378207980945408 39213513121 274877906944 42031447388105 11124034016116736 EMRow21.d10 (ep602 ep612) rfl rfl

noncomputable abbrev qz169 := (@HMul.hMul Real Real Real qz266 qz394 (Real.log (Enclosure.sfrac Bool.false 10 1)))

noncomputable def ep614 := @Enclosure.Complex.IsNear.of_eq qz166 (Complex.mk (@HMul.hMul Real Real Real qz0 qz111 (Real.cos qz169)) (@HMul.hMul Real Real Real qz0 qz111 (@Neg.neg Real Real.instNeg (Real.sin qz169)))) Bool.true 3747464385 137438953472 1790625092493 5562017008058368 Bool.false 86600531325 274877906944 3600559118487 11124034016116736 (BSN.cpow_neg_s_mk qz151 81143 1000 10 qz152 rfl)

noncomputable def ep615 := @Enclosure.Real.IsNear.mulLit_ff qz151 qz113 81143 1000 0 1 10369908600166117 4503599627370496 500000000121407 40469000000000000000 841445493543279231731 4503599627370496000 40571500009851328201 40469000000000000000000 qz153 (BSN.isNear_log_sfrac 10 1 10369908600166117 4503599627370496 500000000121407 40469000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz361) Bool.false 21747274560655572598784 9444732965739290427392 1000000000242814 80938000000000000000 10369908600166117 4503599627370496 500000000121407 40469000000000000000 (BSN.log_rat_reduce_isNear 10 1 3 20 16 58495 262144 24973259072661432 36028797018963968 80938 1000000000000000 rfl rfl rfl rfl (ep338 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep616 := nat_lit 14455737159253601996406053334433272437021809687703597441669799006909873684736

noncomputable def ep617 := nat_lit 41663519142118821304644478842829479390774155208021820100516845736143257856

noncomputable def ep618 := nat_lit 43283884439476568346608871045614158352283880752694748684808363329257334538496

noncomputable def ep619 := BSN.cos_dyadic_bound_f 1593930914 1073741824 3 2 524288 162035 ep616 ep57 ep617 ep618 ep60 ep617 45206 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1593930914) qz281 0 2 ep616 ep57 ep617 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1593930914) qz282 0 2 ep618 ep60 ep617 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz404 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 97957147) qz27)

noncomputable def ep620 := @Enclosure.Real.IsNear.cos_image qz169 qz404 Bool.false 97957147 524288 527 524288 Bool.true 45206 524288 1 80938 (@Enclosure.Real.IsNear.recentre' qz169 Bool.false 841445493543279231731 4503599627370496000 40571500009851328201 40469000000000000000000 97957147 524288 527 524288 (ep615 rfl) rfl) (Enclosure.sfrac_false_div 97957147 524288) (BSN.cos_reduce2 qz404 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 112162916745262833598464) qz29) 226375608064910080 72057594037927936 Bool.false 45206 524288 29 1000000000000000 161876 80938 (BSN.sin_reduce_arg_pos_rat_q2 97957147 524288 226375608064910080 72057594037927936 29 112162916745262833598464 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 45206 524288 112162916745262833598464 75557863725914323419136 1593930914 1073741824 162035 161876 (ep619 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep621 := nat_lit 25986996071342788536487180418905626803126638113700057938925224735848858026240

noncomputable def ep622 := nat_lit 67993724965381968075354143369483489136794227379830021178927132748412300984576

noncomputable def ep623 := BSN.sin_dyadic_bound_f 1593930914 1073741824 3 2 524288 162035 ep621 ep64 ep617 ep622 ep66 ep617 522335 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1593930914) qz285 0 2 ep621 ep64 ep617 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1593930914) qz286 0 2 ep622 ep66 ep617 rfl rfl rfl rfl) rfl rfl

noncomputable def ep624 := @Enclosure.Real.IsNear.sin_image qz169 qz404 Bool.false 97957147 524288 527 524288 Bool.true 522335 524288 1 80938 (@Enclosure.Real.IsNear.recentre' qz169 Bool.false 841445493543279231731 4503599627370496000 40571500009851328201 40469000000000000000000 97957147 524288 527 524288 (ep615 rfl) rfl) (Enclosure.sfrac_false_div 97957147 524288) (BSN.sin_reduce2 qz404 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 112162916745262833598464) qz29) 226375608064910080 72057594037927936 Bool.false 522335 524288 29 1000000000000000 161876 80938 (BSN.sin_reduce_arg_pos_rat_q2 97957147 524288 226375608064910080 72057594037927936 29 112162916745262833598464 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 522335 524288 112162916745262833598464 75557863725914323419136 1593930914 1073741824 162035 161876 (ep623 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep625 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz111 (Real.cos qz169)) (@HMul.hMul Real Real Real qz0 qz111 (@Neg.neg Real Real.instNeg (Real.sin qz169))) Bool.true 3747464385 137438953472 1790625092493 5562017008058368 Bool.false 86600531325 274877906944 3600559118487 11124034016116736 (@Enclosure.Real.IsNear.mulLit_ft qz111 (Real.cos qz169) 165795 524288 1 524288 22603 262144 21589307 21217411072 3747464385 137438953472 1790625092493 5562017008058368 qz363 (@Enclosure.Real.IsNear.recentre' (Real.cos qz169) Bool.true 45206 524288 43178614 42434822144 22603 262144 21589307 21217411072 (ep620 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz111 (@Neg.neg Real Real.instNeg (Real.sin qz169)) 165795 524288 1 524288 522335 524288 21589307 21217411072 86600531325 274877906944 3600559118487 11124034016116736 qz363 (@Enclosure.Real.IsNear.neg (Real.sin qz169) Bool.true 522335 524288 21589307 21217411072 (@Enclosure.Real.IsNear.recentre' (Real.sin qz169) Bool.true 522335 524288 43178614 42434822144 522335 524288 21589307 21217411072 (ep624 rfl rfl) rfl)) rfl)

noncomputable def ep626 := @ep599 3747464385 137438953472 1790625092493 5562017008058368 Bool.false 86600531325 274877906944 3600559118487 11124034016116736 Bool.false 108560870919208618164224 789884295367 274877906944 4145376419997 1011275819646976 Bool.false 13025644380232746008576 11846754551 68719476736 129636382121 31602369363968 (ep600 (BSN.head_sum_c_succ qz142 9 10 rfl rfl) (ep613 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep614 ep625) rfl rfl

noncomputable abbrev qz170 := (@HMul.hMul Real Real Real qz266 qz394 (Real.log (Enclosure.sfrac Bool.false 11 1)))

noncomputable def ep627 := @Enclosure.Complex.IsNear.of_eq qz165 (Complex.mk (@HMul.hMul Real Real Real qz0 qz114 (Real.cos qz170)) (@HMul.hMul Real Real Real qz0 qz114 (@Neg.neg Real Real.instNeg (Real.sin qz170)))) Bool.false 81117132297 274877906944 264123387279 855694924316672 Bool.false 8498801277 137438953472 131430350779 427847462158336 (BSN.cpow_neg_s_mk qz151 81143 1000 11 qz152 rfl)

noncomputable def ep628 := @Enclosure.Real.IsNear.mulLit_ff qz151 qz116 81143 1000 0 1 10799147631728357 4503599627370496 500000000121407 40469000000000000000 876275236281334072051 4503599627370496000 40571500009851328201 40469000000000000000000 qz153 (BSN.isNear_log_sfrac 11 1 10799147631728357 4503599627370496 500000000121407 40469000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz365) Bool.false 22647454054174387339264 9444732965739290427392 1000000000242814 80938000000000000000 10799147631728357 4503599627370496 500000000121407 40469000000000000000 (BSN.log_rat_reduce_isNear 11 1 3 22 16 83480 262144 24973259072661432 36028797018963968 80938 1000000000000000 rfl rfl rfl rfl (ep349 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep629 := nat_lit 18528491424784214395446662626401197843239300116803079407515838972444723445760

noncomputable def ep630 := nat_lit 21199383100557892993464989487256270923174458926306497060647173084529360896

noncomputable def ep631 := nat_lit 48492678539891086827989934990928531817465408324794045072062339980932656726016

noncomputable def ep632 := BSN.sin_dyadic_bound_f 1464840716 1073741824 3 2 524288 162035 ep629 ep64 ep630 ep631 ep66 ep630 513143 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1464840716) qz285 0 2 ep629 ep64 ep630 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1464840716) qz286 0 2 ep631 ep66 ep630 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz405 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 102011863) qz27)

noncomputable def ep633 := @Enclosure.Real.IsNear.cos_image qz170 qz405 Bool.false 102011863 524288 527 524288 Bool.false 513143 524288 1 80938 (@Enclosure.Real.IsNear.recentre' qz170 Bool.false 876275236281334072051 4503599627370496000 40571500009851328201 40469000000000000000000 102011863 524288 527 524288 (ep628 rfl) rfl) (Enclosure.sfrac_false_div 102011863 524288) (BSN.cos_reduce3 qz405 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 103079001673766971375616) qz29) 226375608064910080 72057594037927936 Bool.false 513143 524288 30 1000000000000000 161876 80938 (BSN.sin_reduce_arg_pos_rat_q3 102011863 524288 226375608064910080 72057594037927936 30 103079001673766971375616 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 513143 524288 103079001673766971375616 75557863725914323419136 1464840716 1073741824 162035 161876 (ep632 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep634 := nat_lit 10303028295147033727689685898883890477765466491080069225091309283840192741376

noncomputable def ep635 := nat_lit 30866686119239985397082127717677158891450050555387594681152633505351519502336

noncomputable def ep636 := BSN.cos_dyadic_bound_f 1464840716 1073741824 3 2 524288 162035 ep634 ep57 ep630 ep635 ep60 ep630 107526 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1464840716) qz281 0 2 ep634 ep57 ep630 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1464840716) qz282 0 2 ep635 ep60 ep630 rfl rfl rfl rfl) rfl rfl

noncomputable def ep637 := @Enclosure.Real.IsNear.sin_image qz170 qz405 Bool.false 102011863 524288 527 524288 Bool.true 107526 524288 1 80938 (@Enclosure.Real.IsNear.recentre' qz170 Bool.false 876275236281334072051 4503599627370496000 40571500009851328201 40469000000000000000000 102011863 524288 527 524288 (ep628 rfl) rfl) (Enclosure.sfrac_false_div 102011863 524288) (BSN.sin_reduce3 qz405 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 103079001673766971375616) qz29) 226375608064910080 72057594037927936 Bool.false 107526 524288 30 1000000000000000 161876 80938 (BSN.sin_reduce_arg_pos_rat_q3 102011863 524288 226375608064910080 72057594037927936 30 103079001673766971375616 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 107526 524288 103079001673766971375616 75557863725914323419136 1464840716 1073741824 162035 161876 (ep636 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep638 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz114 (Real.cos qz170)) (@HMul.hMul Real Real Real qz0 qz114 (@Neg.neg Real Real.instNeg (Real.sin qz170))) Bool.false 81117132297 274877906944 264123387279 855694924316672 Bool.false 8498801277 137438953472 131430350779 427847462158336 (@Enclosure.Real.IsNear.mulLit_ff qz114 (Real.cos qz170) 158079 524288 1 524288 513143 524288 21589307 21217411072 81117132297 274877906944 264123387279 855694924316672 qz367 (@Enclosure.Real.IsNear.recentre' (Real.cos qz170) Bool.false 513143 524288 43178614 42434822144 513143 524288 21589307 21217411072 (ep633 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz114 (@Neg.neg Real Real.instNeg (Real.sin qz170)) 158079 524288 1 524288 53763 262144 21589307 21217411072 8498801277 137438953472 131430350779 427847462158336 qz367 (@Enclosure.Real.IsNear.neg (Real.sin qz170) Bool.true 53763 262144 21589307 21217411072 (@Enclosure.Real.IsNear.recentre' (Real.sin qz170) Bool.true 107526 524288 43178614 42434822144 53763 262144 21589307 21217411072 (ep637 rfl rfl) rfl)) rfl)

noncomputable def ep639 := @ep597 81117132297 274877906944 264123387279 855694924316672 Bool.false 8498801277 137438953472 131430350779 427847462158336 Bool.false 239419049381516139298816 54437589229 17179869184 24516372327297 5562017008058368 Bool.false 2212238724167781842944 32192310379 137438953472 24524597813423 5562017008058368 (ep598 (BSN.head_sum_c_succ qz142 10 11 rfl rfl) (ep626 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep627 ep638) rfl rfl

noncomputable abbrev qz171 := (@HMul.hMul Real Real Real qz266 qz394 (Real.log (Enclosure.sfrac Bool.false 12 1)))

noncomputable def ep640 := @Enclosure.Complex.IsNear.of_eq qz164 (Complex.mk (@HMul.hMul Real Real Real qz0 qz117 (Real.cos qz171)) (@HMul.hMul Real Real Real qz0 qz117 (@Neg.neg Real Real.instNeg (Real.sin qz171)))) Bool.false 66772000471 274877906944 3279270704251 11124034016116736 Bool.true 334935337 2147483648 818220010529 2781008504029184 (BSN.cpow_neg_s_mk qz151 81143 1000 12 qz152 rfl)

noncomputable def ep641 := @Enclosure.Real.IsNear.mulLit_ff qz151 qz119 81143 1000 0 1 11191020447815397 4503599627370496 500000000121407 40469000000000000000 908072972197084758771 4503599627370496000 40571500009851328201 40469000000000000000000 qz153 (BSN.isNear_log_sfrac 12 1 11191020447815397 4503599627370496 500000000121407 40469000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz369) Bool.false 23469270914176955449344 9444732965739290427392 1000000000242814 80938000000000000000 11191020447815397 4503599627370496 500000000121407 40469000000000000000 (BSN.log_rat_reduce_isNear 12 1 3 24 16 106290 262144 24973259072661432 36028797018963968 80938 1000000000000000 rfl rfl rfl rfl (ep360 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep642 := nat_lit 141076948470419027782711334156307361

noncomputable def ep643 := BSN.cos_dyadic_bound_f 612863863 1073741824 2 1 524288 162035 ep642 ep90 ep642 ep642 ep91 ep642 441179 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 612863863) qz281 0 1 ep642 ep90 ep642 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 612863863) qz282 0 1 ep642 ep91 ep642 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz406 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 105713607) qz27)

noncomputable def ep644 := @Enclosure.Real.IsNear.cos_image qz171 qz406 Bool.false 105713607 524288 263 262144 Bool.false 441179 524288 1 80938 (@Enclosure.Real.IsNear.recentre' qz171 Bool.false 908072972197084758771 4503599627370496000 40571500009851328201 40469000000000000000000 105713607 524288 263 262144 (ep641 rfl) rfl) (Enclosure.sfrac_false_div 105713607 524288) (BSN.cos_reduce0 qz406 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 43126460436760110301184) qz29) 226375608064910080 72057594037927936 Bool.false 441179 524288 32 1000000000000000 161876 80938 (BSN.sin_reduce_arg_pos_rat_q0 105713607 524288 226375608064910080 72057594037927936 32 43126460436760110301184 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 441179 524288 43126460436760110301184 75557863725914323419136 612863863 1073741824 162035 161876 (ep643 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep645 := BSN.sin_dyadic_bound_f 612863863 1073741824 2 1 524288 162035 ep642 ep86 ep642 ep642 ep87 ep642 283264 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 612863863) qz285 0 1 ep642 ep86 ep642 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 612863863) qz286 0 1 ep642 ep87 ep642 rfl rfl rfl rfl) rfl rfl

noncomputable def ep646 := @Enclosure.Real.IsNear.sin_image qz171 qz406 Bool.false 105713607 524288 263 262144 Bool.false 283264 524288 1 80938 (@Enclosure.Real.IsNear.recentre' qz171 Bool.false 908072972197084758771 4503599627370496000 40571500009851328201 40469000000000000000000 105713607 524288 263 262144 (ep641 rfl) rfl) (Enclosure.sfrac_false_div 105713607 524288) (BSN.sin_reduce0 qz406 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 43126460436760110301184) qz29) 226375608064910080 72057594037927936 Bool.false 283264 524288 32 1000000000000000 161876 80938 (BSN.sin_reduce_arg_pos_rat_q0 105713607 524288 226375608064910080 72057594037927936 32 43126460436760110301184 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 283264 524288 43126460436760110301184 75557863725914323419136 612863863 1073741824 162035 161876 (ep645 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep647 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz117 (Real.cos qz171)) (@HMul.hMul Real Real Real qz0 qz117 (@Neg.neg Real Real.instNeg (Real.sin qz171))) Bool.false 66772000471 274877906944 3279270704251 11124034016116736 Bool.true 334935337 2147483648 818220010529 2781008504029184 (@Enclosure.Real.IsNear.mulLit_ff qz117 (Real.cos qz171) 151349 524288 1 524288 441179 524288 10774419 10608705536 66772000471 274877906944 3279270704251 11124034016116736 qz371 (@Enclosure.Real.IsNear.recentre' (Real.cos qz171) Bool.false 441179 524288 21548838 21217411072 441179 524288 10774419 10608705536 (ep644 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz117 (@Neg.neg Real Real.instNeg (Real.sin qz171)) 151349 524288 1 524288 2213 4096 10774419 10608705536 334935337 2147483648 818220010529 2781008504029184 qz371 (@Enclosure.Real.IsNear.neg (Real.sin qz171) Bool.false 2213 4096 10774419 10608705536 (@Enclosure.Real.IsNear.recentre' (Real.sin qz171) Bool.false 283264 524288 21548838 21217411072 2213 4096 10774419 10608705536 (ep646 rfl rfl) rfl)) rfl)

noncomputable def ep648 := @ep595 66772000471 274877906944 3279270704251 11124034016116736 Bool.true 334935337 2147483648 818220010529 2781008504029184 Bool.false 16110824819590525091840 937773428135 274877906944 4755637759895 1011275819646976 Bool.false 23099297932171542528 10756448811 137438953472 2378276166771 505637909823488 (ep596 (BSN.head_sum_c_succ qz142 11 12 rfl rfl) (ep639 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep640 ep647) rfl rfl

noncomputable abbrev qz172 := (@HMul.hMul Real Real Real qz266 qz394 (Real.log (Enclosure.sfrac Bool.false 13 1)))

noncomputable def ep649 := @Enclosure.Complex.IsNear.of_eq qz163 (Complex.mk (@HMul.hMul Real Real Real qz0 qz120 (Real.cos qz172)) (@HMul.hMul Real Real Real qz0 qz120 (@Neg.neg Real Real.instNeg (Real.sin qz172)))) Bool.false 13519006081 68719476736 787127351213 2781008504029184 Bool.true 26869480813 137438953472 1574207798855 5562017008058368 (BSN.cpow_neg_s_mk qz151 81143 1000 13 qz152 rfl)

noncomputable def ep650 := @Enclosure.Real.IsNear.mulLit_ff qz151 qz122 81143 1000 0 1 11551488463034085 4503599627370496 500000000121407 40469000000000000000 187464485671194951831 900719925474099200 40571500009851328201 40469000000000000000000 qz153 (BSN.isNear_log_sfrac 13 1 11551488463034085 4503599627370496 500000000121407 40469000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz373) Bool.false 24225227133228857425920 9444732965739290427392 1000000000242814 80938000000000000000 11551488463034085 4503599627370496 500000000121407 40469000000000000000 (BSN.log_rat_reduce_isNear 13 1 3 26 16 127272 262144 24973259072661432 36028797018963968 80938 1000000000000000 rfl rfl rfl rfl (ep374 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep651 := nat_lit 1111829255620147952251887878974272984249832023687296334993166108306157844001

noncomputable def ep652 := nat_lit 247779332760326155511328641240355901620435122282753708710975252464383521

noncomputable def ep653 := nat_lit 3334992208194923204444640979640338240946255200817323497562076374413544764961

noncomputable def ep654 := BSN.cos_dyadic_bound_f 839959091 1073741824 3 2 524288 162035 ep651 ep57 ep652 ep653 ep60 ep652 371884 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 839959091) qz281 0 2 ep651 ep57 ep652 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 839959091) qz282 0 2 ep653 ep60 ep652 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz407 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 27279673) qz485)

noncomputable def ep655 := @Enclosure.Real.IsNear.cos_image qz172 qz407 Bool.false 27279673 131072 263 262144 Bool.false 371884 524288 1 80938 (@Enclosure.Real.IsNear.recentre' qz172 Bool.false 187464485671194951831 900719925474099200 40571500009851328201 40469000000000000000000 27279673 131072 263 262144 (ep650 rfl) rfl) (Enclosure.sfrac_false_div 27279673 131072) (BSN.cos_reduce0 qz407 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 14776716605373374529536) qz296) 226375608064910080 72057594037927936 Bool.false 371884 524288 33 1000000000000000 161876 80938 (BSN.sin_reduce_arg_pos_rat_q0 27279673 131072 226375608064910080 72057594037927936 33 14776716605373374529536 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 371884 524288 14776716605373374529536 18889465931478580854784 839959091 1073741824 162035 161876 (ep654 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep656 := nat_lit 497774379373151502010197473208930961

noncomputable def ep657 := BSN.sin_dyadic_bound_f 839959091 1073741824 2 1 524288 162035 ep656 ep86 ep656 ep656 ep87 ep656 369566 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 839959091) qz285 0 1 ep656 ep86 ep656 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 839959091) qz286 0 1 ep656 ep87 ep656 rfl rfl rfl rfl) rfl rfl

noncomputable def ep658 := @Enclosure.Real.IsNear.sin_image qz172 qz407 Bool.false 27279673 131072 263 262144 Bool.false 369566 524288 1 80938 (@Enclosure.Real.IsNear.recentre' qz172 Bool.false 187464485671194951831 900719925474099200 40571500009851328201 40469000000000000000000 27279673 131072 263 262144 (ep650 rfl) rfl) (Enclosure.sfrac_false_div 27279673 131072) (BSN.sin_reduce0 qz407 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 14776716605373374529536) qz296) 226375608064910080 72057594037927936 Bool.false 369566 524288 33 1000000000000000 161876 80938 (BSN.sin_reduce_arg_pos_rat_q0 27279673 131072 226375608064910080 72057594037927936 33 14776716605373374529536 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 369566 524288 14776716605373374529536 18889465931478580854784 839959091 1073741824 162035 161876 (ep657 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep659 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz120 (Real.cos qz172)) (@HMul.hMul Real Real Real qz0 qz120 (@Neg.neg Real Real.instNeg (Real.sin qz172))) Bool.false 13519006081 68719476736 787127351213 2781008504029184 Bool.true 26869480813 137438953472 1574207798855 5562017008058368 (@Enclosure.Real.IsNear.mulLit_ff qz120 (Real.cos qz172) 145411 524288 1 524288 92971 131072 10774419 10608705536 13519006081 68719476736 787127351213 2781008504029184 qz375 (@Enclosure.Real.IsNear.recentre' (Real.cos qz172) Bool.false 371884 524288 21548838 21217411072 92971 131072 10774419 10608705536 (ep655 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz120 (@Neg.neg Real Real.instNeg (Real.sin qz172)) 145411 524288 1 524288 184783 262144 10774419 10608705536 26869480813 137438953472 1574207798855 5562017008058368 qz375 (@Enclosure.Real.IsNear.neg (Real.sin qz172) Bool.false 184783 262144 10774419 10608705536 (@Enclosure.Real.IsNear.recentre' (Real.sin qz172) Bool.false 369566 524288 21548838 21217411072 184783 262144 10774419 10608705536 (ep658 rfl rfl) rfl)) rfl)

noncomputable def ep660 := @ep593 13519006081 68719476736 787127351213 2781008504029184 Bool.true 26869480813 137438953472 1574207798855 5562017008058368 Bool.false 68159375373870588493824 991849452459 274877906944 55460524763697 11124034016116736 Bool.true 2214558255615725010944 8056516001 68719476736 3466905704167 695252126007296 (ep594 (BSN.head_sum_c_succ qz142 12 13 rfl rfl) (ep648 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep649 ep659) rfl rfl

noncomputable abbrev qz173 := (@HMul.hMul Real Real Real qz266 qz394 (Real.log (Enclosure.sfrac Bool.false 14 1)))

noncomputable def ep661 := @Enclosure.Complex.IsNear.of_eq qz162 (Complex.mk (@HMul.hMul Real Real Real qz0 qz123 (Real.cos qz173)) (@HMul.hMul Real Real Real qz0 qz123 (@Neg.neg Real Real.instNeg (Real.sin qz173)))) Bool.false 32013584991 137438953472 1518979132017 5562017008058368 Bool.true 18009892251 137438953472 1514934660157 5562017008058368 (BSN.cpow_neg_s_mk qz151 81143 1000 14 qz152 rfl)

noncomputable def ep662 := @Enclosure.Real.IsNear.mulLit_ff qz151 qz125 81143 1000 0 1 11885241781671653 4503599627370496 500000000121407 40469000000000000000 964404173890182939379 4503599627370496000 40571500009851328201 40469000000000000000000 qz153 (BSN.isNear_log_sfrac 14 1 11885241781671653 4503599627370496 500000000121407 40469000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz377) Bool.false 24925158572916270432256 9444732965739290427392 1000000000242814 80938000000000000000 11885241781671653 4503599627370496 500000000121407 40469000000000000000 (BSN.log_rat_reduce_isNear 14 1 3 28 16 146699 262144 24973259072661432 36028797018963968 80938 1000000000000000 rfl rfl rfl rfl (ep388 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep663 := nat_lit 91660263286025450462082876563657281

noncomputable def ep664 := BSN.cos_dyadic_bound_f 550231279 1073741824 2 1 524288 162035 ep663 ep90 ep663 ep663 ep91 ep663 456942 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 550231279) qz281 0 1 ep663 ep90 ep663 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 550231279) qz282 0 1 ep663 ep91 ep663 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz408 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 56135711) qz20)

noncomputable def ep665 := @Enclosure.Real.IsNear.cos_image qz173 qz408 Bool.false 56135711 262144 263 262144 Bool.false 456942 524288 1 80938 (@Enclosure.Real.IsNear.recentre' qz173 Bool.false 964404173890182939379 4503599627370496000 40571500009851328201 40469000000000000000000 56135711 262144 263 262144 (ep662 rfl) rfl) (Enclosure.sfrac_false_div 56135711 262144) (BSN.cos_reduce0 qz408 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 19359542059672138678272) qz23) 226375608064910080 72057594037927936 Bool.false 456942 524288 34 1000000000000000 161876 80938 (BSN.sin_reduce_arg_pos_rat_q0 56135711 262144 226375608064910080 72057594037927936 34 19359542059672138678272 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 456942 524288 19359542059672138678272 37778931862957161709568 550231279 1073741824 162035 161876 (ep664 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep666 := BSN.sin_dyadic_bound_f 550231279 1073741824 2 1 524288 162035 ep663 ep86 ep663 ep663 ep87 ep663 257062 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 550231279) qz285 0 1 ep663 ep86 ep663 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 550231279) qz286 0 1 ep663 ep87 ep663 rfl rfl rfl rfl) rfl rfl

noncomputable def ep667 := @Enclosure.Real.IsNear.sin_image qz173 qz408 Bool.false 56135711 262144 263 262144 Bool.false 257062 524288 1 80938 (@Enclosure.Real.IsNear.recentre' qz173 Bool.false 964404173890182939379 4503599627370496000 40571500009851328201 40469000000000000000000 56135711 262144 263 262144 (ep662 rfl) rfl) (Enclosure.sfrac_false_div 56135711 262144) (BSN.sin_reduce0 qz408 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 19359542059672138678272) qz23) 226375608064910080 72057594037927936 Bool.false 257062 524288 34 1000000000000000 161876 80938 (BSN.sin_reduce_arg_pos_rat_q0 56135711 262144 226375608064910080 72057594037927936 34 19359542059672138678272 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 257062 524288 19359542059672138678272 37778931862957161709568 550231279 1073741824 162035 161876 (ep666 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep668 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz123 (Real.cos qz173)) (@HMul.hMul Real Real Real qz0 qz123 (@Neg.neg Real Real.instNeg (Real.sin qz173))) Bool.false 32013584991 137438953472 1518979132017 5562017008058368 Bool.true 18009892251 137438953472 1514934660157 5562017008058368 (@Enclosure.Real.IsNear.mulLit_ff qz123 (Real.cos qz173) 140121 524288 1 524288 228471 262144 10774419 10608705536 32013584991 137438953472 1518979132017 5562017008058368 qz379 (@Enclosure.Real.IsNear.recentre' (Real.cos qz173) Bool.false 456942 524288 21548838 21217411072 228471 262144 10774419 10608705536 (ep665 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz123 (@Neg.neg Real Real.instNeg (Real.sin qz173)) 140121 524288 1 524288 128531 262144 10774419 10608705536 18009892251 137438953472 1514934660157 5562017008058368 qz379 (@Enclosure.Real.IsNear.neg (Real.sin qz173) Bool.false 128531 262144 10774419 10608705536 (@Enclosure.Real.IsNear.recentre' (Real.sin qz173) Bool.false 257062 524288 21548838 21217411072 128531 262144 10774419 10608705536 (ep667 rfl rfl) rfl)) rfl)

noncomputable def ep669 := @ep591 32013584991 137438953472 1518979132017 5562017008058368 Bool.true 18009892251 137438953472 1514934660157 5562017008058368 Bool.false 145118577983841110065152 1055876622441 274877906944 58498483027731 11124034016116736 Bool.true 2344909499368323678208 34122924253 137438953472 29250180293493 5562017008058368 (ep592 (BSN.head_sum_c_succ qz142 13 14 rfl rfl) (ep660 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep661 ep668) rfl rfl

noncomputable abbrev qz174 := (@HMul.hMul Real Real Real qz266 qz394 (Real.log (Enclosure.sfrac Bool.false 15 1)))

noncomputable def ep670 := @Enclosure.Complex.IsNear.of_eq qz161 (Complex.mk (@HMul.hMul Real Real Real qz0 qz126 (Real.cos qz174)) (@HMul.hMul Real Real Real qz0 qz126 (@Neg.neg Real Real.instNeg (Real.sin qz174)))) Bool.false 69920339839 274877906944 2943490269925 11124034016116736 Bool.false 12180547209 274877906944 2926229027355 11124034016116736 (BSN.cpow_neg_s_mk qz151 81143 1000 15 qz152 rfl)

noncomputable def ep671 := @Enclosure.Real.IsNear.mulLit_ff qz151 qz128 81143 1000 0 1 12195956895733477 4503599627370496 500000000121407 40469000000000000000 989616530390501524211 4503599627370496000 40571500009851328201 40469000000000000000000 qz153 (BSN.isNear_log_sfrac 15 1 12195956895733477 4503599627370496 500000000121407 40469000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz381) Bool.false 25576775395801252757504 9444732965739290427392 1000000000242814 80938000000000000000 12195956895733477 4503599627370496 500000000121407 40469000000000000000 (BSN.log_rat_reduce_isNear 15 1 3 30 16 164785 262144 24973259072661432 36028797018963968 80938 1000000000000000 rfl rfl rfl rfl (ep399 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep672 := nat_lit 20452965478601517612705195052622523188906124753248121785463344325855317618145

noncomputable def ep673 := nat_lit 25825728861009506672738564185051474196665864496574634579157797539079286241

noncomputable def ep674 := nat_lit 53525477454371864070091076986283191679388105811226817172609170133605417774561

noncomputable def ep675 := BSN.sin_dyadic_bound_f 1501435131 1073741824 3 2 524288 162035 ep672 ep64 ep673 ep674 ep66 ep673 516509 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1501435131) qz285 0 2 ep672 ep64 ep673 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1501435131) qz286 0 2 ep674 ep66 ep673 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz409 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 57603263) qz20)

noncomputable def ep676 := @Enclosure.Real.IsNear.cos_image qz174 qz409 Bool.false 57603263 262144 527 524288 Bool.false 516509 524288 1 80938 (@Enclosure.Real.IsNear.recentre' qz174 Bool.false 989616530390501524211 4503599627370496000 40571500009851328201 40469000000000000000000 57603263 262144 527 524288 (ep671 rfl) rfl) (Enclosure.sfrac_false_div 57603263 262144) (BSN.cos_reduce3 qz409 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 52827052349067211309056) qz23) 226375608064910080 72057594037927936 Bool.false 516509 524288 34 1000000000000000 161876 80938 (BSN.sin_reduce_arg_pos_rat_q3 57603263 262144 226375608064910080 72057594037927936 34 52827052349067211309056 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 516509 524288 52827052349067211309056 37778931862957161709568 1501435131 1073741824 162035 161876 (ep675 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep677 := nat_lit 11374236700939069565579658835539202426813031913802989718403705868825878359521

noncomputable def ep678 := nat_lit 34071058645095189683393499378247504332045764012415819886052802011399476506081

noncomputable def ep679 := BSN.cos_dyadic_bound_f 1501435131 1073741824 3 2 524288 162035 ep677 ep57 ep673 ep678 ep60 ep673 89979 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1501435131) qz281 0 2 ep677 ep57 ep673 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1501435131) qz282 0 2 ep678 ep60 ep673 rfl rfl rfl rfl) rfl rfl

noncomputable def ep680 := @Enclosure.Real.IsNear.sin_image qz174 qz409 Bool.false 57603263 262144 527 524288 Bool.true 89979 524288 1 80938 (@Enclosure.Real.IsNear.recentre' qz174 Bool.false 989616530390501524211 4503599627370496000 40571500009851328201 40469000000000000000000 57603263 262144 527 524288 (ep671 rfl) rfl) (Enclosure.sfrac_false_div 57603263 262144) (BSN.sin_reduce3 qz409 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 52827052349067211309056) qz23) 226375608064910080 72057594037927936 Bool.false 89979 524288 34 1000000000000000 161876 80938 (BSN.sin_reduce_arg_pos_rat_q3 57603263 262144 226375608064910080 72057594037927936 34 52827052349067211309056 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 89979 524288 52827052349067211309056 37778931862957161709568 1501435131 1073741824 162035 161876 (ep679 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep681 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz126 (Real.cos qz174)) (@HMul.hMul Real Real Real qz0 qz126 (@Neg.neg Real Real.instNeg (Real.sin qz174))) Bool.false 69920339839 274877906944 2943490269925 11124034016116736 Bool.false 12180547209 274877906944 2926229027355 11124034016116736 (@Enclosure.Real.IsNear.mulLit_ff qz126 (Real.cos qz174) 135371 524288 1 524288 516509 524288 21589307 21217411072 69920339839 274877906944 2943490269925 11124034016116736 qz383 (@Enclosure.Real.IsNear.recentre' (Real.cos qz174) Bool.false 516509 524288 43178614 42434822144 516509 524288 21589307 21217411072 (ep676 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz126 (@Neg.neg Real Real.instNeg (Real.sin qz174)) 135371 524288 1 524288 89979 524288 21589307 21217411072 12180547209 274877906944 2926229027355 11124034016116736 qz383 (@Enclosure.Real.IsNear.neg (Real.sin qz174) Bool.true 89979 524288 21589307 21217411072 (@Enclosure.Real.IsNear.recentre' (Real.sin qz174) Bool.true 89979 524288 43178614 42434822144 89979 524288 21589307 21217411072 (ep680 rfl rfl) rfl)) rfl)

noncomputable def ep682 := @ep589 69920339839 274877906944 2943490269925 11124034016116736 Bool.false 12180547209 274877906944 2926229027355 11124034016116736 Bool.false 309456712635439718072320 140724620285 34359738368 7680246662207 1390504252014592 Bool.true 7705556336352044253184 56065301297 274877906944 61426589614341 11124034016116736 (ep590 (BSN.head_sum_c_succ qz142 14 15 rfl rfl) (ep669 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep670 ep681) rfl rfl

noncomputable abbrev qz175 := (@HMul.hMul Real Real Real qz266 qz394 qz387)

noncomputable def ep683 := @Enclosure.Complex.IsNear.of_eq qz160 (Complex.mk (@HMul.hMul Real Real Real qz0 qz131 (Real.cos qz175)) (@HMul.hMul Real Real Real qz0 qz131 (@Neg.neg Real Real.instNeg (Real.sin qz175)))) Bool.false 23711399255 274877906944 2837074691549 11124034016116736 Bool.false 8062308281 34359738368 356208494547 1390504252014592 (BSN.cpow_neg_s_mk qz151 81143 1000 16 qz152 rfl)

noncomputable def ep684 := @Enclosure.Real.IsNear.mulLit_ff qz151 qz134 81143 1000 0 1 3121657384082679 1125899906842624 125000000040469 10117250000000000000 253300645116620822097 1125899906842624000 10142875003283776067 10117250000000000000000 qz153 (BSN.isNear_log_sfrac 16 1 3121657384082679 1125899906842624 125000000040469 10117250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' qz388 Bool.false 26186360105375033720832 9444732965739290427392 1000000000323752 80938000000000000000 3121657384082679 1125899906842624 125000000040469 10117250000000000000 (BSN.log_rat_reduce_isNear 16 1 4 32 32 0 262144 24973259072661432 36028797018963968 80938 1000000000000000 rfl rfl rfl rfl (ep420 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep685 := nat_lit 20474149325545773968773314461012641

noncomputable def ep686 := BSN.sin_dyadic_bound_f 378269623 1073741824 2 1 524288 162035 ep685 ep86 ep685 ep685 ep87 ep685 180905 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 378269623) qz285 0 1 ep685 ep86 ep685 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 378269623) qz286 0 1 ep685 ep87 ep685 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz410 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 7372019) (@Nat.cast Real Real.instNatCast 32768))

noncomputable def ep687 := @Enclosure.Real.IsNear.cos_image qz175 qz410 Bool.false 7372019 32768 527 524288 Bool.false 180905 524288 1 80938 (@Enclosure.Real.IsNear.recentre' qz175 Bool.false 253300645116620822097 1125899906842624000 10142875003283776067 10117250000000000000000 7372019 32768 527 524288 (ep684 rfl) rfl) (Enclosure.sfrac_false_div 7372019 32768) (BSN.cos_reduce3 qz410 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 1663647398633718939648) qz358) 226375608064910080 72057594037927936 Bool.false 180905 524288 35 1000000000000000 161876 80938 (BSN.sin_reduce_arg_pos_rat_q3 7372019 32768 226375608064910080 72057594037927936 35 1663647398633718939648 4722366482869645213696 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 180905 524288 1663647398633718939648 4722366482869645213696 378269623 1073741824 162035 161876 (ep686 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep688 := BSN.cos_dyadic_bound_f 378269623 1073741824 2 1 524288 162035 ep685 ep90 ep685 ep685 ep91 ep685 492088 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 378269623) qz281 0 1 ep685 ep90 ep685 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 378269623) qz282 0 1 ep685 ep91 ep685 rfl rfl rfl rfl) rfl rfl

noncomputable def ep689 := @Enclosure.Real.IsNear.sin_image qz175 qz410 Bool.false 7372019 32768 527 524288 Bool.true 492088 524288 1 80938 (@Enclosure.Real.IsNear.recentre' qz175 Bool.false 253300645116620822097 1125899906842624000 10142875003283776067 10117250000000000000000 7372019 32768 527 524288 (ep684 rfl) rfl) (Enclosure.sfrac_false_div 7372019 32768) (BSN.sin_reduce3 qz410 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 1663647398633718939648) qz358) 226375608064910080 72057594037927936 Bool.false 492088 524288 35 1000000000000000 161876 80938 (BSN.sin_reduce_arg_pos_rat_q3 7372019 32768 226375608064910080 72057594037927936 35 1663647398633718939648 4722366482869645213696 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 492088 524288 1663647398633718939648 4722366482869645213696 378269623 1073741824 162035 161876 (ep688 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep690 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz131 (Real.cos qz175)) (@HMul.hMul Real Real Real qz0 qz131 (@Neg.neg Real Real.instNeg (Real.sin qz175))) Bool.false 23711399255 274877906944 2837074691549 11124034016116736 Bool.false 8062308281 34359738368 356208494547 1390504252014592 (@Enclosure.Real.IsNear.mulLit_ff qz131 (Real.cos qz175) 131071 524288 1 524288 180905 524288 21589307 21217411072 23711399255 274877906944 2837074691549 11124034016116736 qz390 (@Enclosure.Real.IsNear.recentre' (Real.cos qz175) Bool.false 180905 524288 43178614 42434822144 180905 524288 21589307 21217411072 (ep687 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz131 (@Neg.neg Real Real.instNeg (Real.sin qz175)) 131071 524288 1 524288 61511 65536 21589307 21217411072 8062308281 34359738368 356208494547 1390504252014592 qz390 (@Enclosure.Real.IsNear.neg (Real.sin qz175) Bool.true 61511 65536 21589307 21217411072 (@Enclosure.Real.IsNear.recentre' (Real.sin qz175) Bool.true 492088 524288 43178614 42434822144 61511 65536 21589307 21217411072 (ep689 rfl rfl) rfl)) rfl)

noncomputable def ep691 := @ep587 23711399255 274877906944 2837074691549 11124034016116736 Bool.false 8062308281 34359738368 356208494547 1390504252014592 Bool.false 39496806554170954874880 1149508361535 274877906944 64279047989205 11124034016116736 Bool.false 289761341330547539968 8433164951 274877906944 64276257570717 11124034016116736 (ep588 (BSN.head_sum_c_succ qz142 15 16 rfl rfl) (ep682 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep683 ep690) rfl rfl

theorem EMRow21.d11 : Enclosure.Complex.IsNear (BSN.headSumC qz142 17) Bool.false 1149508361535 274877906944 64279047989205 11124034016116736 Bool.false 8433164951 274877906944 64276257570717 11124034016116736 := ep586 (BSN.head_sum_c_succ qz142 16 17 rfl rfl) (ep691 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

theorem EMRow21.d12 : @Eq Nat (Nat.pow 17 1) 17 := @Eq.refl Nat 17

noncomputable def ep692 := nat_lit 784892268592994999809145176997569

noncomputable def ep693 := nat_lit 193579128633115738415365619712000

noncomputable def ep694 := nat_lit 834565649044558915457948014548550394829

noncomputable def ep695 := nat_lit 105677424859337650913622363942623903744000

noncomputable abbrev qz497 := (@HAdd.hAdd Complex Complex Complex qz502 (@HAdd.hAdd Complex Complex Complex qz502 qz505 (@HMul.hMul Complex Complex Complex qz504 Complex.I (@HDiv.hDiv Complex Complex Complex qz506 (↑qz509) (2 : Complex)))) (@Nat.cast Complex Complex.instNatCast 2))

noncomputable abbrev qz411 := qz497

noncomputable abbrev qz176 := (Complex.Stirling.logGammaStirling 1 qz411)

noncomputable abbrev qz498 := (@HAdd.hAdd Complex Complex Complex qz502 qz505 (@HMul.hMul Complex Complex Complex qz504 Complex.I (@HDiv.hDiv Complex Complex Complex qz506 (↑qz509) (2 : Complex))))

noncomputable abbrev qz412 := qz498

noncomputable abbrev qz177 := qz412

noncomputable abbrev qz178 := (@HMul.hMul Real Real Real qz266 (@HDiv.hDiv Real Real Real qz269 qz394 (2 : Real)) (Real.log Real.pi))

noncomputable def ep696 := Complex.re (@HMul.hMul Complex Complex Complex qz45 (Complex.exp (@HMul.hMul Complex Complex Complex qz45 Complex.I ↑(@HSub.hSub Real Real Real qz318 (Complex.im (@HSub.hSub Complex Complex Complex qz46 qz176 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz177 (@Nat.cast Complex Complex.instNatCast j))))) qz178))) (zetaApproximant qz142 1 17))

noncomputable def ep697 := @Enclosure.Real.IsNear.of_eq ep696 (@HSub.hSub Real Real Real qz318 (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz318 (Complex.im (@HSub.hSub Complex Complex Complex qz46 qz176 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz177 (@Nat.cast Complex Complex.instNatCast j))))) qz178)) (Complex.re (zetaApproximant qz142 1 17))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz318 (Complex.im (@HSub.hSub Complex Complex Complex qz46 qz176 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz177 (@Nat.cast Complex Complex.instNatCast j))))) qz178)) (Complex.im (zetaApproximant qz142 1 17))))

noncomputable def ep698 := nat_lit 261629762908048308199756011956933

noncomputable def ep699 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz318 (Complex.im (@HSub.hSub Complex Complex Complex qz46 qz176 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz177 (@Nat.cast Complex Complex.instNatCast j))))) qz178)) (Complex.re (zetaApproximant qz142 1 17))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz318 (Complex.im (@HSub.hSub Complex Complex Complex qz46 qz176 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz177 (@Nat.cast Complex Complex.instNatCast j))))) qz178)) (Complex.im (zetaApproximant qz142 1 17))) ep698

noncomputable def ep700 := nat_lit 64526376211038579471788539904000

noncomputable def ep701 := nat_lit 2493846432067834207761587829377903578057

noncomputable def ep702 := nat_lit 317032274578012952740867091827871711232000

noncomputable def ep703 := nat_lit 297986885007520987714112677

noncomputable def ep704 := nat_lit 19357912863311573841536561971200

noncomputable def ep705 := nat_lit 985051506584253861225621426774760643

noncomputable def ep706 := nat_lit 31703227457801295274086709182787171123200

noncomputable def ep707 := nat_lit 5064625380836713572606000142478626514054380993649772506749337600

noncomputable def ep708 := @Enclosure.Real.IsNear.mulLit_ff (Real.cos (@HSub.hSub Real Real Real qz318 (Complex.im (@HSub.hSub Complex Complex Complex qz46 qz176 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz177 (@Nat.cast Complex Complex.instNatCast j))))) qz178)) (Complex.re (zetaApproximant qz142 1 17)) 524287 524288 10015173

noncomputable def ep709 := nat_lit 499020122391072653336352059

noncomputable def ep710 := nat_lit 123074295446469458526208000

noncomputable def ep711 := nat_lit 88898456118197688478260211733

noncomputable def ep712 := nat_lit 14942080987269517551291334656000

noncomputable def ep713 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HSub.hSub Real Real Real qz318 (Complex.im (@HSub.hSub Complex Complex Complex qz46 qz176 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz177 (@Nat.cast Complex Complex.instNatCast j))))) qz178)) Bool.false 524287 524288 20030346

noncomputable abbrev qz413 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 32941843) qz27)

noncomputable def ep714 := @Enclosure.Real.IsNear.cos_image (@HSub.hSub Real Real Real qz318 (Complex.im (@HSub.hSub Complex Complex Complex qz46 qz176 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz177 (@Nat.cast Complex Complex.instNatCast j))))) qz178) qz413 Bool.false 32941843 524288 241

noncomputable def ep715 := nat_lit 1457714936930117977391611

noncomputable def ep716 := nat_lit 3182611660800000000000000000

noncomputable def ep717 := @Enclosure.Real.IsNear.recentre' (@HSub.hSub Real Real Real qz318 (Complex.im (@HSub.hSub Complex Complex Complex qz46 qz176 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz177 (@Nat.cast Complex Complex.instNatCast j))))) qz178) Bool.false 1697809669793086527007 27021597764222976000 ep715 ep716

noncomputable def ep718 := @Enclosure.Real.IsNear.subLit_ff_p (Complex.im (@HSub.hSub Complex Complex Complex qz46 qz176 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz177 (@Nat.cast Complex Complex.instNatCast j))))) qz178 2952784477054217049631 27021597764222976000 472582116830117977391611 ep716 6087429003 131072000

noncomputable def ep719 := nat_lit 222535309039119437267861504000

noncomputable def ep720 := @Enclosure.Complex.IsNear.im_isNear (@HSub.hSub Complex Complex Complex qz46 qz176 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz177 (@Nat.cast Complex Complex.instNatCast j)))) Bool.true 5740870509642844729 90071992547409920 352780816182715774875239 ep177 Bool.false 2952784477054217049631 27021597764222976000

noncomputable def ep721 := @Enclosure.Complex.IsNear.subLitP qz176 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz177 (@Nat.cast Complex Complex.instNatCast j))) Bool.true 5073741144010549569 90071992547409920 344588816169454892955239 ep177 Bool.false 3036676595563415673631 27021597764222976000 39387319711539578702801

noncomputable def ep722 := nat_lit 289328332800000000000000000

noncomputable def ep723 := nat_lit 12927291144004892492541975741857792

noncomputable def ep724 := nat_lit 831134941910422300069118205478567936

noncomputable abbrev qz414 := (@HSub.hSub Complex Complex Complex qz487 qz497 qz490)

noncomputable abbrev qz415 := (Complex.log qz497)

noncomputable abbrev qz179 := (@HSub.hSub Complex Complex Complex qz315 (@HMul.hMul Complex Complex Complex qz314 qz414 qz415) qz411)

noncomputable abbrev qz180 := qz411

noncomputable def ep725 := @Enclosure.Complex.IsNear.of_eq qz176 (@HAdd.hAdd Complex Complex Complex qz5 (@HAdd.hAdd Complex Complex Complex qz5 qz179 qz51) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz53 2 k))) (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz45 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz54 qz180 (@HSub.hSub Int Int Int qz327 qz56 (@HMul.hMul Int Int Int qz328 qz57 (@Nat.cast Int instNatCastInt k)))))) Bool.true 5073741144010549569

noncomputable def ep726 := @Enclosure.Complex.IsNear.addLitP (@HAdd.hAdd Complex Complex Complex qz5 qz179 qz51) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz53 2 k))) (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz45 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz54 qz180 (@HSub.hSub Int Int Int qz327 qz56 (@HMul.hMul Int Int Int qz328 qz57 (@Nat.cast Int instNatCastInt k))))) Bool.true 5073751372565342529 90071992547409920

noncomputable def ep727 := nat_lit 43583104563789873355683790848

noncomputable def ep728 := nat_lit 13042426666473489012298954571776000

noncomputable def ep729 := @ep726 42064007939270503567 161876000000000000000000 Bool.false 1012243975757173339061 9007199254740992000 200325000299812747 1471600000000000000000 Bool.false 975471 8589934592 3 8589934592 Bool.true 26384214451 12884901888000 81143 12884901888000 Bool.true ep727 5073741144010549569 90071992547409920 344588816169454892955239 ep177 Bool.false ep728

noncomputable def ep730 := @Enclosure.Complex.IsNear.addLitP qz179 qz51 Bool.true 5156521920709552449 90071992547409920 41446500004700191067 161876000000000000000000

noncomputable def ep731 := @ep730 Bool.false 1012243975757173339061 9007199254740992000 200325000299812747 1471600000000000000000 Bool.false 120447 131072 1 262144 Bool.false 0 1 0 1 Bool.true 665026739904884575961088 5073751372565342529 90071992547409920 42064007939270503567 161876000000000000000000 Bool.false 1012243975757173339061 1012243975757173339061 9007199254740992000

noncomputable abbrev qz181 := (@HMul.hMul Complex Complex Complex qz314 qz414 qz415)

noncomputable def ep732 := @Enclosure.Complex.IsNear.subLitP qz181 qz180 Bool.true 4953859937477880129 90071992547409920 41446500004700191067 161876000000000000000000 Bool.false 1377679560320897495989

noncomputable def ep733 := nat_lit 4048975903028693356244000

noncomputable def ep734 := @ep732 9007199254740992000 200325000299812747 1471600000000000000000 Bool.false 9000 4000 0 1 Bool.false 162286 4000 0 1 Bool.true 20626087682838209796000 5156521920709552449 90071992547409920 41446500004700191067 161876000000000000000000 Bool.false ep733 1012243975757173339061 9007199254740992000 200325000299812747 1471600000000000000000

noncomputable abbrev qz182 := qz414

noncomputable abbrev qz183 := qz415

noncomputable def ep735 := @Enclosure.Complex.IsNear.mul qz182 qz183 Bool.true 4953859937477880129 90071992547409920 41446500004700191067 161876000000000000000000 Bool.false 1377679560320897495989 9007199254740992000 200325000299812747

noncomputable abbrev qz184 := (Complex.re qz414)

noncomputable abbrev qz185 := (Complex.re qz415)

noncomputable abbrev qz186 := (Complex.im qz414)

noncomputable abbrev qz187 := (Complex.im qz415)

noncomputable def ep736 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 qz184 qz185) (@HMul.hMul Real Real Real qz0 qz186 qz187) 116788271523755461 18014398509481984 175000000283283 32375200000000000000 2768900647548328717 45035996273704960

noncomputable def ep737 := nat_lit 44620403536942019122221833118547968

noncomputable def ep738 := @Enclosure.Real.IsNear.mulLit_ff qz184 qz185 7000 4000 0 1 16684038789107923 4503599627370496 25000000040469 8093800000000000000

noncomputable def ep739 := @Enclosure.Complex.IsNear.re_isNear qz182 Bool.false 7000 4000 0 1 Bool.false 162286 4000 0 1

noncomputable abbrev qz416 := (Enclosure.sfrac Bool.false 162286 4000)

noncomputable abbrev qz188 := qz416

noncomputable def ep740 := @Enclosure.Complex.IsNear.of_eq qz182 (Complex.mk (Enclosure.sfrac Bool.false 7000 4000) qz188) Bool.false 7000 4000 0 1 Bool.false 162286 4000 0

noncomputable abbrev qz417 := (Complex.log (Complex.mk qz66 qz188))

noncomputable def ep741 := @Enclosure.Complex.IsNear.of_eq qz183 qz417 Bool.false 16684038789107923 4503599627370496 25000000040469 8093800000000000000 Bool.false 853092887725475 562949953421312 500000000040469 80938000000000000000

noncomputable def ep742 := nat_lit 10644461007200359776476815662006353494654860666540417578013140365882457510007609029099520

noncomputable def ep743 := nat_lit 201679395538054756796562662924995051695693206741753386523738019770533864437811140624384

noncomputable def ep744 := nat_lit 10786835387741209646833977340059129098775944950904280080314519750983445855083233280

noncomputable def ep745 := BSN.log_dyadic_bound 10033745796 42801745796 5 4 ep742 524288 161876 ep743 ep744 250468 52835491592 32768000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 10033745796) (BSN.artanhQ 42801745796) 0 4 ep743 ep742 ep744 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz418 := (Real.log (Enclosure.sfrac Bool.false 26417745796 16000000))

noncomputable def ep746 := @Enclosure.Real.IsNear.mulLit_ff qz67 qz418 1 2 0 1 16684038789107923 2251799813685248 25000000040469 4046900000000000000 16684038789107923 4503599627370496 25000000040469 8093800000000000000 qz333 (BSN.isNear_log_sfrac 26417745796 16000000 16684038789107923 2251799813685248 25000000040469 4046900000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 26417745796) qz334)) Bool.false 139955861258621035741184 18889465931478580854784 1000000001618760 161876000000000000000 16684038789107923 2251799813685248 25000000040469 4046900000000000000 (BSN.log_rat_reduce_isNear 26417745796 16000000 10 52835491592 32768000000 250468 524288 24973259072661432 36028797018963968 161876 1000000000000000 rfl rfl rfl rfl (ep745 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep747 := BSN.arctan_dyadic_bound_f 9000 162286 1 0 524288 161876 0 1 1 0 1 1 29045 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 9000) (BSN.arctanEvenQ 162286) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 9000) (BSN.arctanOddQ 162286) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz419 := (Real.arctan (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 9000) (@Nat.cast Real Real.instNatCast 162286)))

noncomputable def ep748 := @Enclosure.Real.IsNear.subLit_ff_p qz68 qz419 884279719003555 562949953421312 1 2000000000000000 29045 524288 1 161876 447266363919813836800 853092887725475 562949953421312 500000000040469 80938000000000000000 qz69 (ep747 rfl) rfl rfl

noncomputable abbrev qz420 := (Complex.mk qz66 qz188)

noncomputable abbrev qz421 := (Real.arctan (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 162286) (@Nat.cast Real Real.instNatCast 9000)))

noncomputable def ep749 := @Enclosure.Complex.IsNear.re_isNear qz183 Bool.false 16684038789107923 4503599627370496 25000000040469 8093800000000000000 Bool.false 853092887725475 562949953421312 500000000040469 80938000000000000000 (ep741 (@congrArg Complex Complex qz180 qz420 Complex.log (BSN.w_shift_mk qz151 Bool.false 81143 1000 2 qz152 rfl)) (@Enclosure.Complex.IsNear.of_parts qz417 Bool.false 16684038789107923 4503599627370496 25000000040469 8093800000000000000 Bool.false 853092887725475 562949953421312 500000000040469 80938000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz417) (@HMul.hMul Real Real Real qz0 qz67 qz418) Bool.false 16684038789107923 4503599627370496 25000000040469 8093800000000000000 (Enclosure.clog_re_eq 9000 162286 4000 26417745796 16000000 rfl rfl rfl) (ep746 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz417) qz421 Bool.false 853092887725475 562949953421312 500000000040469 80938000000000000000 (Enclosure.clog_im_eq 9000 162286 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz421 (@HSub.hSub Real Real Real qz318 qz68 qz419) Bool.false 853092887725475 562949953421312 500000000040469 80938000000000000000 (BSN.arctan_recip 162286 9000 rfl rfl) ep748))))

noncomputable def ep750 := @Enclosure.Real.IsNear.mulLit_ff qz186 qz187 162286 4000 0 1 853092887725475 562949953421312 500000000040469 80938000000000000000

noncomputable def ep751 := @Enclosure.Complex.IsNear.im_isNear qz182 Bool.false 7000 4000 0 1 Bool.false 162286 4000 0 1

noncomputable def ep752 := @Enclosure.Complex.IsNear.im_isNear qz183 Bool.false 16684038789107923 4503599627370496 25000000040469 8093800000000000000 Bool.false 853092887725475 562949953421312 500000000040469 80938000000000000000 (ep741 (@congrArg Complex Complex qz180 qz420 Complex.log (BSN.w_shift_mk qz151 Bool.false 81143 1000 2 qz152 rfl)) (@Enclosure.Complex.IsNear.of_parts qz417 Bool.false 16684038789107923 4503599627370496 25000000040469 8093800000000000000 Bool.false 853092887725475 562949953421312 500000000040469 80938000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz417) (@HMul.hMul Real Real Real qz0 qz67 qz418) Bool.false 16684038789107923 4503599627370496 25000000040469 8093800000000000000 (Enclosure.clog_re_eq 9000 162286 4000 26417745796 16000000 rfl rfl rfl) (ep746 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz417) qz421 Bool.false 853092887725475 562949953421312 500000000040469 80938000000000000000 (Enclosure.clog_im_eq 9000 162286 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz421 (@HSub.hSub Real Real Real qz318 qz68 qz419) Bool.false 853092887725475 562949953421312 500000000040469 80938000000000000000 (BSN.arctan_recip 162286 9000 rfl rfl) ep748))))

noncomputable abbrev qz422 := (Enclosure.Real.IsNear.const Bool.false 162286 4000)

noncomputable abbrev qz189 := (@ep740 1 (BSN.w_sub_half_mk qz394 Bool.false 81143 1000 2 qz395 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7000 4000) qz416 Bool.false 7000 4000 0 1 Bool.false 162286 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 7000 4000) qz422))

noncomputable def ep753 := @ep736 40571500003283776067 161876000000000000000000 ep737 4953859937477880129 90071992547409920 41446500004700191067 161876000000000000000000 (@ep738 116788271523755461 18014398509481984 175000000283283 32375200000000000000 (ep739 qz189) ep749 rfl) (@ep750 2768900647548328717 45035996273704960 40571500003283776067 161876000000000000000000 (ep751 qz189) ep752 rfl) rfl

noncomputable def ep754 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz184 qz187) (@HMul.hMul Real Real Real qz0 qz186 qz185) 5971650214078325 2251799813685248 3500000000283283 323752000000000000000 1353792959464584195989 9007199254740992000

noncomputable def ep755 := nat_lit 3102258577248571364810972817388470272

noncomputable def ep756 := @Enclosure.Real.IsNear.mulLit_ff qz184 qz187 7000 4000 0 1 853092887725475 562949953421312 500000000040469 80938000000000000000

noncomputable def ep757 := @Enclosure.Real.IsNear.mulLit_ff qz186 qz185 162286 4000 0 1 16684038789107923 4503599627370496 25000000040469 8093800000000000000

noncomputable def ep758 := @ep754 2028575003283776067 16187600000000000000000 ep755 1377679560320897495989 9007199254740992000 200325000299812747 1471600000000000000000 (@ep756 5971650214078325 2251799813685248 3500000000283283 323752000000000000000 (ep739 qz189) ep752 rfl) (@ep757 1353792959464584195989 9007199254740992000 2028575003283776067 16187600000000000000000 (ep751 qz189) ep749 rfl) rfl

noncomputable def ep759 := @Enclosure.Complex.IsNear.of_eq qz180 qz420 Bool.false 9000 4000 0 1 Bool.false 162286 4000 0 1 (BSN.w_shift_mk qz151 Bool.false 81143 1000 2 qz152 rfl)

noncomputable abbrev qz423 := (ep759 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 9000 4000) (Enclosure.sfrac Bool.false 162286 4000) Bool.false 9000 4000 0 1 Bool.false 162286 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 9000 4000) (Enclosure.Real.IsNear.const Bool.false 162286 4000)))

noncomputable abbrev qz190 := qz423

noncomputable def ep760 := ep734 (@ep735 1471600000000000000000 (ep753 rfl) (ep758 rfl)) qz190 rfl rfl rfl rfl rfl rfl

noncomputable def ep761 := @ep731 200325000299812747 1471600000000000000000 (ep760 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@Enclosure.Complex.IsNear.mul qz72 (↑qz3) Bool.false 120447 131072 1 262144 Bool.false 0 1 0 1 (@ep218 131072 1 262144 (ep220 rfl) (ep222 rfl) rfl rfl) (@ep223 1 0 1 (ep225 rfl) (ep227 rfl) rfl rfl))

noncomputable abbrev qz424 := (@HPow.hPow Complex Int Complex qz492 qz497 (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) (@OfNat.ofNat Int 1 (@instOfNat 1)) (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (@OfNat.ofNat Int 2 (@instOfNat 2)) (@Nat.cast Int instNatCastInt 1))))

noncomputable abbrev qz191 := qz424

noncomputable def ep762 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz53 2 k))) (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz45 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz54 qz180 (@HSub.hSub Int Int Int qz327 qz56 (@HMul.hMul Int Int Int qz328 qz57 (@Nat.cast Int instNatCastInt k))))) (@HAdd.hAdd Complex Complex Complex qz5 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz53 2 k))) (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz45 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz54 qz180 (@HSub.hSub Int Int Int qz327 qz56 (@HMul.hMul Int Int Int qz328 qz57 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 (@Rat.cast Complex Complex.instRatCast (bernoulli qz74)) qz75) qz191)) Bool.false 975471 8589934592 3 8589934592

noncomputable def ep763 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz53 2 k))) (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz45 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz54 qz180 (@HSub.hSub Int Int Int qz327 qz56 (@HMul.hMul Int Int Int qz328 qz57 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 (@Rat.cast Complex Complex.instRatCast (bernoulli qz74)) qz75) qz191) Bool.false 0 1 0 1 Bool.false

noncomputable def ep764 := @ep763 0 1 0 1 Bool.false 975471 8589934592 3 8589934592 Bool.true 26384214451 12884901888000 81143 12884901888000 Bool.false 975471 975471 8589934592 3 8589934592 Bool.true 26384214451 26384214451 12884901888000 81143

noncomputable def ep765 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz53 2 k))) (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz45 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz54 qz180 (@HSub.hSub Int Int Int qz327 qz56 (@HMul.hMul Int Int Int qz328 qz57 (@Nat.cast Int instNatCastInt k))))) (Complex.mk qz14 qz14) Bool.false 0 1 0 1 Bool.false

noncomputable def ep766 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz52 (@Rat.cast Complex Complex.instRatCast (bernoulli qz74)) qz75) qz191 Bool.false 975471 8589934592 3 8589934592 Bool.true 26384214451 12884901888000 81143 12884901888000

noncomputable abbrev qz192 := (Complex.re qz424)

noncomputable abbrev qz193 := (Complex.im qz424)

noncomputable def ep767 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz52 (@Rat.cast Complex Complex.instRatCast (bernoulli qz74)) qz75)) qz192) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz52 (@Rat.cast Complex Complex.instRatCast (bernoulli qz74)) qz75)) qz193) 975471 8589934592 3 8589934592 0 1 0

noncomputable def ep768 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz52 (@Rat.cast Complex Complex.instRatCast (bernoulli qz74)) qz75)) qz192 1 12 0 1 2926413 2147483648 9 2147483648 975471

noncomputable def ep769 := @Enclosure.Complex.IsNear.re_isNear qz191 Bool.false 2926413 2147483648 9 2147483648 Bool.true 26384214451 1073741824000 81143 1073741824000

noncomputable abbrev qz425 := (@HPow.hPow Complex Nat Complex qz493 qz497 1)

noncomputable abbrev qz194 := (@Inv.inv Complex Complex.instInv qz425)

noncomputable def ep770 := @Enclosure.Complex.IsNear.of_eq qz191 qz194 Bool.false 2926413 2147483648 9 2147483648 Bool.true 26384214451 1073741824000 81143

noncomputable def ep771 := @Enclosure.Complex.IsNear.of_parts qz194 Bool.false 2926413 2147483648 9 2147483648 Bool.true 26384214451 1073741824000 81143

noncomputable abbrev qz195 := (Complex.re qz425)

noncomputable abbrev qz196 := qz425

noncomputable def ep772 := @Enclosure.Real.IsNear.mulLit_ff qz195 (@Inv.inv Real Real.instInv (@DFunLike.coe qz81 Complex (fun (x : Complex) => Real) qz82 Complex.normSq qz196)) 9000 4000 0 1 325157 536870912 1 536870912

noncomputable def ep773 := @Enclosure.Complex.IsNear.re_isNear qz196 Bool.false 9000 4000 0 1 Bool.false 162286 4000 0 1

noncomputable def ep774 := @Enclosure.Complex.IsNear.of_eq qz196 qz180 Bool.false 9000 4000 0 1 Bool.false 162286 4000 0

noncomputable def ep775 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (@DFunLike.coe qz81 Complex (fun (x : Complex) => Real) qz82 Complex.normSq qz196)) Bool.false 325157 536870912 1 536870912 325157 536870912 1

noncomputable abbrev qz197 := (Complex.im qz425)

noncomputable def ep776 := @Enclosure.Real.IsNear.of_eq (@DFunLike.coe qz81 Complex (fun (x : Complex) => Real) qz82 Complex.normSq qz196) (@HAdd.hAdd Real Real Real qz343 (@HMul.hMul Real Real Real qz0 qz195 qz195) (@HMul.hMul Real Real Real qz0 qz197 qz197)) Bool.false 6604436449 4000000 0 1

noncomputable def ep777 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz195 qz195) (@HMul.hMul Real Real Real qz0 qz197 qz197) 81 16 0 1 6584186449 4000000

noncomputable def ep778 := @Enclosure.Real.IsNear.mulLit_ff qz195 qz195 9000 4000 0 1 9000 4000 0 1

noncomputable def ep779 := @Enclosure.Real.IsNear.mulLit_ff qz197 qz197 162286 4000 0 1 162286 4000 0 1

noncomputable def ep780 := @Enclosure.Complex.IsNear.im_isNear qz196 Bool.false 9000 4000 0 1 Bool.false 162286 4000 0 1

noncomputable abbrev qz198 := (ep773 (@ep774 1 (BSN.pow_one_c qz411) qz423))

noncomputable abbrev qz199 := (ep780 (@ep774 1 (BSN.pow_one_c qz411) qz423))

noncomputable def ep781 := @ep777 0 1 105670983184 6604436449 4000000 0 1 (@ep778 81 16 0 1 qz198 qz198 rfl) (@ep779 6584186449 4000000 0 1 qz199 qz199 rfl)

noncomputable def ep782 := @Enclosure.Real.IsNear.inv_image (@DFunLike.coe qz81 Complex (fun (x : Complex) => Real) qz82 Complex.normSq qz196) 6604436449 4000000 0 1 162578 162579 268435456 (ep776 (Enclosure.Complex.normSq_eq_mul_add_mul qz196) (ep781 rfl rfl)) rfl

noncomputable def ep783 := @Enclosure.Real.IsNear.of_eq (Complex.re qz194) (@HMul.hMul Real Real Real qz0 qz195 (@Inv.inv Real Real.instInv (@DFunLike.coe qz81 Complex (fun (x : Complex) => Real) qz82 Complex.normSq qz196))) Bool.false 2926413 2147483648 9 2147483648 (Enclosure.Complex.inv_re_eq_mul qz196) (@ep772 2926413 2147483648 9 2147483648 qz198 (@ep775 536870912 (ep782 rfl rfl rfl rfl rfl) rfl) rfl)

noncomputable def ep784 := @Enclosure.Real.IsNear.of_eq (Complex.im qz194) (@HMul.hMul Real Real Real qz0 (@Neg.neg Real Real.instNeg qz197) (@Inv.inv Real Real.instInv (@DFunLike.coe qz81 Complex (fun (x : Complex) => Real) qz82 Complex.normSq qz196))) Bool.true 26384214451 1073741824000 81143 1073741824000 (Enclosure.Complex.inv_im_eq_mul qz196)

noncomputable def ep785 := @Enclosure.Real.IsNear.mulLit_tf (@Neg.neg Real Real.instNeg qz197) (@Inv.inv Real Real.instInv (@DFunLike.coe qz81 Complex (fun (x : Complex) => Real) qz82 Complex.normSq qz196)) 162286 4000 0 1 325157 536870912 1

noncomputable def ep786 := @ep785 536870912 26384214451 1073741824000 81143 1073741824000 (@Enclosure.Real.IsNear.neg qz197 Bool.false 162286 4000 0 1 qz199) (@ep775 536870912 (ep782 rfl rfl rfl rfl rfl) rfl) rfl

noncomputable def ep787 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz52 (@Rat.cast Complex Complex.instRatCast (bernoulli qz74)) qz75)) qz193 0 1 0 1 26384214451 1073741824000 81143 1073741824000 0

noncomputable def ep788 := @Enclosure.Complex.IsNear.im_isNear qz191 Bool.false 2926413 2147483648 9 2147483648 Bool.true 26384214451 1073741824000 81143 1073741824000

noncomputable abbrev qz200 := (@ep770 1073741824000 (BSN.zpow_one_sub_two_mul qz411 1 1 rfl rfl) (@ep771 1073741824000 ep783 (ep784 ep786)))

noncomputable def ep789 := @ep767 1 975471 975471 8589934592 3 8589934592 (@ep768 8589934592 3 8589934592 ep237 (ep769 qz200) rfl) (@ep787 1 0 1 ep257 (ep788 qz200) rfl) rfl

noncomputable def ep790 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz52 (@Rat.cast Complex Complex.instRatCast (bernoulli qz74)) qz75)) qz193) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz52 (@Rat.cast Complex Complex.instRatCast (bernoulli qz74)) qz75)) qz192) 26384214451 12884901888000 81143 12884901888000 0 1 0

noncomputable def ep791 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HDiv.hDiv Complex Complex Complex qz52 (@Rat.cast Complex Complex.instRatCast (bernoulli qz74)) qz75)) qz193 1 12 0 1 26384214451 1073741824000 81143 1073741824000 26384214451

noncomputable def ep792 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz52 (@Rat.cast Complex Complex.instRatCast (bernoulli qz74)) qz75)) qz192 0 1 0 1 2926413 2147483648 9 2147483648 0

noncomputable def ep793 := @ep790 1 26384214451 26384214451 12884901888000 81143 12884901888000 (@ep791 12884901888000 81143 12884901888000 ep237 (ep788 qz200) rfl) (@ep792 1 0 1 ep257 (ep769 qz200) rfl) rfl

noncomputable def ep794 := @ep764 12884901888000 (@ep765 0 1 0 1 (BSN.stirling_sum_base qz180) qz88) (ep766 (ep789 rfl) (ep793 rfl)) rfl rfl rfl rfl rfl

noncomputable def ep795 := @ep729 3036676595563415673631 27021597764222976000 39387319711539578702801 ep722 (ep761 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep762 Bool.true 26384214451 12884901888000 81143 12884901888000 (BSN.stirling_sum_succ qz180 0 1 rfl) (ep794 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl

noncomputable def ep796 := @Enclosure.Complex.IsNear.of_eq (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz177 (@Nat.cast Complex Complex.instNatCast j))) (BSN.logSumC qz151 2) Bool.false 16678234140807379 2251799813685248 25000000040469 4046900000000000000 Bool.false 873876234470819 281474976710656

noncomputable abbrev qz201 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz272 qz412 qz339))

noncomputable def ep797 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz151 2) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.logSumC qz151 1) qz201) Bool.false 16678234140807379 2251799813685248 25000000040469 4046900000000000000 Bool.false 873876234470819 281474976710656 500000000040469 40469000000000000000

noncomputable def ep798 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz151 1) qz201 Bool.false 16677209791107283 4503599627370496 25000000040469 8093800000000000000 Bool.false 880811532912035 562949953421312 500000000040469 80938000000000000000 Bool.false

noncomputable def ep799 := nat_lit 150224178123475993158960407379968

noncomputable def ep800 := nat_lit 983897170982678160037753389056

noncomputable abbrev qz202 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz272 qz412 (@Nat.cast Complex Complex.instNatCast 0)))

noncomputable def ep801 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz151 1) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.logSumC qz151 0) qz202) Bool.false 16677209791107283 4503599627370496 25000000040469 8093800000000000000 Bool.false 880811532912035 562949953421312 500000000040469 80938000000000000000

noncomputable def ep802 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz151 0) qz202 Bool.false 0 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable abbrev qz426 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz188))

noncomputable def ep803 := @Enclosure.Complex.IsNear.of_eq qz202 qz426 Bool.false 16677209791107283 4503599627370496 25000000040469 8093800000000000000 Bool.false 880811532912035 562949953421312 500000000040469 80938000000000000000

noncomputable def ep804 := nat_lit 10486335316793245914097050723863926414981574779110999265788906093799585237272172229099520

noncomputable def ep805 := nat_lit 196178142290997758861839388358903395025634438356514888093531348029387541938800580624384

noncomputable def ep806 := nat_lit 10117696820996669555341893898666500411027301619841363382491553586986564139883233280

noncomputable def ep807 := BSN.log_dyadic_bound 9953745796 42721745796 5 4 ep804 524288 161876 ep805 ep806 248878 52675491592 32768000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 9953745796) (BSN.artanhQ 42721745796) 0 4 ep805 ep804 ep806 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep808 := @Enclosure.Real.IsNear.mulLit_ff qz67 (Real.log (Enclosure.sfrac Bool.false 26337745796 16000000)) 1 2 0 1 16677209791107283 2251799813685248 25000000040469 4046900000000000000 16677209791107283 4503599627370496 25000000040469 8093800000000000000 qz333 (BSN.isNear_log_sfrac 26337745796 16000000 16677209791107283 2251799813685248 25000000040469 4046900000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 26337745796) qz334)) Bool.false 139898575471360883032064 18889465931478580854784 1000000001618760 161876000000000000000 16677209791107283 2251799813685248 25000000040469 4046900000000000000 (BSN.log_rat_reduce_isNear 26337745796 16000000 10 52675491592 32768000000 248878 524288 24973259072661432 36028797018963968 161876 1000000000000000 rfl rfl rfl rfl (ep807 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep809 := BSN.arctan_dyadic_bound_f 1000 162286 1 0 524288 161876 0 1 1 0 1 1 3230 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 162286) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 162286) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz427 := (@Nat.cast Real Real.instNatCast 162286)

noncomputable def ep810 := @Enclosure.Real.IsNear.subLit_ff_p qz68 (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz345 qz427)) 884279719003555 562949953421312 1 2000000000000000 3230 524288 1 161876 461798916967385006080 880811532912035 562949953421312 500000000040469 80938000000000000000 qz69 (ep809 rfl) rfl rfl

noncomputable abbrev qz203 := (@HAdd.hAdd Complex Complex Complex qz272 qz412 (@Nat.cast Complex Complex.instNatCast 0))

noncomputable abbrev qz428 := (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz188)

noncomputable def ep811 := @ep802 16677209791107283 4503599627370496 25000000040469 8093800000000000000 Bool.false 880811532912035 562949953421312 500000000040469 80938000000000000000 Bool.false 16677209791107283 16677209791107283 4503599627370496 25000000040469 8093800000000000000 Bool.false 880811532912035 880811532912035 562949953421312 500000000040469 80938000000000000000 (@Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz151 0) (Complex.mk qz14 qz14) Bool.false 0 1 0 1 Bool.false 0 1 0 1 (BSN.log_sum_c_base qz151) qz88) (ep803 (@congrArg Complex Complex qz203 qz428 Complex.log (BSN.w_shift_mk qz151 Bool.false 81143 1000 0 qz152 rfl)) (@Enclosure.Complex.IsNear.of_parts qz426 Bool.false 16677209791107283 4503599627370496 25000000040469 8093800000000000000 Bool.false 880811532912035 562949953421312 500000000040469 80938000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz426) (@HMul.hMul Real Real Real qz0 qz67 (Real.log (Enclosure.sfrac Bool.false 26337745796 16000000))) Bool.false 16677209791107283 4503599627370496 25000000040469 8093800000000000000 (Enclosure.clog_re_eq 1000 162286 4000 26337745796 16000000 rfl rfl rfl) (ep808 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz426) (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz427 qz345)) Bool.false 880811532912035 562949953421312 500000000040469 80938000000000000000 (Enclosure.clog_im_eq 1000 162286 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz427 qz345)) (@HSub.hSub Real Real Real qz318 qz68 (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz345 qz427))) Bool.false 880811532912035 562949953421312 500000000040469 80938000000000000000 (BSN.arctan_recip 162286 1000 rfl rfl) ep810)))) rfl rfl

noncomputable abbrev qz429 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz188))

noncomputable def ep812 := @Enclosure.Complex.IsNear.of_eq qz201 qz429 Bool.false 16679258490507475 4503599627370496 25000000040469 8093800000000000000 Bool.false 866940936029603 562949953421312 500000000040469 80938000000000000000

noncomputable def ep813 := nat_lit 10533555754969390581020972745811139691054093932536557687028788718570229232052803269099520

noncomputable def ep814 := nat_lit 197815647990192585678276564630908457711261307609882090941851244310096180320503748624384

noncomputable def ep815 := nat_lit 10314514257632031582479648338801402616917940968782379594074681180887068654443233280

noncomputable def ep816 := BSN.log_dyadic_bound 9977745796 42745745796 5 4 ep813 524288 161876 ep814 ep815 249355 52723491592 32768000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 9977745796) (BSN.artanhQ 42745745796) 0 4 ep814 ep813 ep815 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep817 := @Enclosure.Real.IsNear.mulLit_ff qz67 (Real.log (Enclosure.sfrac Bool.false 26361745796 16000000)) 1 2 0 1 16679258490507475 2251799813685248 25000000040469 4046900000000000000 16679258490507475 4503599627370496 25000000040469 8093800000000000000 qz333 (BSN.isNear_log_sfrac 26361745796 16000000 16679258490507475 2251799813685248 25000000040469 4046900000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 26361745796) qz334)) Bool.false 139915761207538928844800 18889465931478580854784 1000000001618760 161876000000000000000 16679258490507475 2251799813685248 25000000040469 4046900000000000000 (BSN.log_rat_reduce_isNear 26361745796 16000000 10 52723491592 32768000000 249355 524288 24973259072661432 36028797018963968 161876 1000000000000000 rfl rfl rfl rfl (ep816 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep818 := BSN.arctan_dyadic_bound_f 5000 162286 1 0 524288 161876 0 1 1 0 1 1 16148 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 5000) (BSN.arctanEvenQ 162286) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 5000) (BSN.arctanOddQ 162286) 0 0 rfl) rfl rfl rfl

noncomputable def ep819 := @Enclosure.Real.IsNear.subLit_ff_p qz68 (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz349 qz427)) 884279719003555 562949953421312 1 2000000000000000 16148 524288 1 161876 454526729469088497664 866940936029603 562949953421312 500000000040469 80938000000000000000 qz69 (ep818 rfl) rfl rfl

noncomputable abbrev qz204 := (@HAdd.hAdd Complex Complex Complex qz272 qz412 qz339)

noncomputable abbrev qz430 := (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz188)

noncomputable def ep820 := @ep798 16679258490507475 4503599627370496 25000000040469 8093800000000000000 Bool.false 866940936029603 562949953421312 500000000040469 80938000000000000000 Bool.false ep799 16678234140807379 2251799813685248 25000000040469 4046900000000000000 Bool.false ep800 873876234470819 281474976710656 500000000040469 40469000000000000000 (ep801 (BSN.log_sum_c_succ qz151 0 1 rfl) (ep811 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep812 (@congrArg Complex Complex qz204 qz430 Complex.log (BSN.w_shift_mk qz151 Bool.false 81143 1000 1 qz152 rfl)) (@Enclosure.Complex.IsNear.of_parts qz429 Bool.false 16679258490507475 4503599627370496 25000000040469 8093800000000000000 Bool.false 866940936029603 562949953421312 500000000040469 80938000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz429) (@HMul.hMul Real Real Real qz0 qz67 (Real.log (Enclosure.sfrac Bool.false 26361745796 16000000))) Bool.false 16679258490507475 4503599627370496 25000000040469 8093800000000000000 (Enclosure.clog_re_eq 5000 162286 4000 26361745796 16000000 rfl rfl rfl) (ep817 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz429) (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz427 qz349)) Bool.false 866940936029603 562949953421312 500000000040469 80938000000000000000 (Enclosure.clog_im_eq 5000 162286 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz427 qz349)) (@HSub.hSub Real Real Real qz318 qz68 (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz349 qz427))) Bool.false 866940936029603 562949953421312 500000000040469 80938000000000000000 (BSN.arctan_recip 162286 5000 rfl rfl) ep819)))) rfl rfl

noncomputable def ep821 := @ep721 ep722 Bool.false 16678234140807379 2251799813685248 25000000040469 4046900000000000000 Bool.false 873876234470819 281474976710656 500000000040469 40469000000000000000 Bool.true ep723 5740870509642844729 90071992547409920 352780816182715774875239 ep177 Bool.false ep724 2952784477054217049631 27021597764222976000 472582116830117977391611 ep716 (@ep725 90071992547409920 344588816169454892955239 ep177 Bool.false 3036676595563415673631 27021597764222976000 39387319711539578702801 ep722 (BSN.logGammaStirling_unfold 1 qz180) (ep795 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (@ep796 500000000040469 40469000000000000000 (BSN.log_sum_c_eq qz151 2) (ep797 (BSN.log_sum_c_succ qz151 1 2 rfl) (ep820 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)))

noncomputable abbrev qz205 := (@HDiv.hDiv Real Real Real qz269 qz394 (2 : Real))

noncomputable def ep822 := @Enclosure.Real.IsNear.mulLit_ff qz205 (Real.log Real.pi) 81143 2000 0 1 75021 65536 1 131072 6087429003 131072000 81143 262144000 (@Enclosure.Real.IsNear.of_eq qz205 (Enclosure.sfrac Bool.false 81143 2000) Bool.false 81143 2000 0 1 (BSN.t_half_eq qz151 Bool.false 81143 1000 qz152) (Enclosure.Real.IsNear.const Bool.false 81143 2000)) EMRow21.d5 rfl

noncomputable def ep823 := @ep718 81143 262144000 ep719 1697809669793086527007 27021597764222976000 ep715 ep716 (@ep720 472582116830117977391611 ep716 (ep821 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) ep822 rfl rfl

noncomputable def ep824 := nat_lit 32570933958291469665003798979548013624342703411442556413423256881759331098880

noncomputable def ep825 := nat_lit 65396149619885362971555534090782993659426337675054528579484519587462062336

noncomputable def ep826 := nat_lit 85198947553283558534960764557907339407353723435637559465075078801466166681856

noncomputable def ep827 := BSN.sin_dyadic_bound_f 1686335654 1073741824 3 2 524288 162035 ep824 ep64 ep825 ep826 ep66 ep825 524287 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1686335654) qz285 0 2 ep824 ep64 ep825 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1686335654) qz286 0 2 ep826 ep66 ep825 rfl rfl rfl rfl) rfl rfl

noncomputable def ep828 := @ep714 524288 Bool.false 524287 524288 1 80938 (@ep717 32941843 524288 241 524288 ep823 rfl) (Enclosure.sfrac_false_div 32941843 524288) (BSN.cos_reduce3 qz413 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 118665322266028761153536) qz29) 226375608064910080 72057594037927936 Bool.false 524287 524288 9 1000000000000000 161876 80938 (BSN.sin_reduce_arg_pos_rat_q3 32941843 524288 226375608064910080 72057594037927936 9 118665322266028761153536 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 524287 524288 118665322266028761153536 75557863725914323419136 1686335654 1073741824 162035 161876 (ep827 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep829 := nat_lit 2083824370681964949049739

noncomputable def ep830 := nat_lit 36922288633940837557862400

noncomputable def ep831 := nat_lit 1777837553994996357248069227

noncomputable def ep832 := nat_lit 298841619745390351025826693120

noncomputable abbrev qz206 := qz393

noncomputable abbrev qz431 := (@HPow.hPow Complex Complex Complex qz480 (@Nat.cast Complex Complex.instNatCast 17) qz495)

noncomputable abbrev qz207 := qz431

noncomputable abbrev qz432 := (@Nat.cast Complex Complex.instNatCast 17)

noncomputable abbrev qz208 := (@HAdd.hAdd Complex Complex Complex qz272 (@HDiv.hDiv Complex Complex Complex qz323 qz432 (@HSub.hSub Complex Complex Complex qz315 qz392 (1 : Complex))) qz322)

noncomputable abbrev qz209 := qz432

noncomputable def ep833 := @Enclosure.Complex.IsNear.of_eq (zetaApproximant qz142 1 17) (@HAdd.hAdd Complex Complex Complex qz5 (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 17, @HPow.hPow Complex Complex Complex qz94 (@Nat.cast Complex Complex.instNatCast n) qz206) (@HMul.hMul Complex Complex Complex qz45 qz207 (@HAdd.hAdd Complex Complex Complex qz5 qz208 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz53 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz53 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz99 qz209 (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1))))))) Bool.false ep709 ep710 ep711

noncomputable def ep834 := @Enclosure.Complex.IsNear.addLitP (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 17, @HPow.hPow Complex Complex Complex qz94 (@Nat.cast Complex Complex.instNatCast n) qz206) (@HMul.hMul Complex Complex Complex qz45 qz207 (@HAdd.hAdd Complex Complex Complex qz5 qz208 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz53 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz53 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz99 qz209 (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1)))))) Bool.false 1149508361535 274877906944 64279047989205 11124034016116736

noncomputable def ep835 := nat_lit 15662680889177350730267941

noncomputable def ep836 := nat_lit 17882724439306364542091131

noncomputable def ep837 := nat_lit 104490076834052570288750592000

noncomputable def ep838 := nat_lit 2089801536681051405775011840

noncomputable def ep839 := nat_lit 137169606765796759580132952406224797696

noncomputable def ep840 := nat_lit 572797281451956523083963858069487616

noncomputable def ep841 := @ep834 Bool.false 8433164951 274877906944 64276257570717 11124034016116736 Bool.true ep835 ep710 ep836 ep837 Bool.false 951060541532573489470139 ep830 357258648439973573449109 ep838 Bool.false ep839 ep709 ep710 ep711 ep712 Bool.false ep840 ep829 ep830

noncomputable def ep842 := @Enclosure.Complex.IsNear.of_eq (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 17, @HPow.hPow Complex Complex Complex qz94 (@Nat.cast Complex Complex.instNatCast n) qz206) (BSN.headSumC qz142 17) Bool.false 1149508361535 274877906944 64279047989205 11124034016116736 Bool.false 8433164951 274877906944 64276257570717

noncomputable def ep843 := @Enclosure.Complex.IsNear.mul qz207 (@HAdd.hAdd Complex Complex Complex qz5 qz208 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz53 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz53 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz99 qz209 (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1))))) Bool.true ep835 ep710 ep836 ep837 Bool.false

noncomputable abbrev qz210 := (Complex.re qz431)

noncomputable abbrev qz211 := (Complex.im qz431)

noncomputable def ep844 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 qz210 (Complex.re (@HAdd.hAdd Complex Complex Complex qz5 qz208 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz53 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz53 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz99 qz209 (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz211 (Complex.im (@HAdd.hAdd Complex Complex Complex qz5 qz208 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz53 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz53 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz99 qz209 (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1))))))) 38046506491399260396425 369222886339408375578624 169105600981079891666125

noncomputable def ep845 := nat_lit 1358370998842683413753757696

noncomputable def ep846 := nat_lit 8941536176132791794378823

noncomputable def ep847 := nat_lit 369222886339408375578624000

noncomputable def ep848 := nat_lit 21123272243300949127019901

noncomputable def ep849 := nat_lit 452790332947561137917919232000

noncomputable def ep850 := nat_lit 17349060737145458040797338482847159675069296279552

noncomputable def ep851 := @Enclosure.Real.IsNear.mulLit_tf qz210 (Complex.re (@HAdd.hAdd Complex Complex Complex qz5 qz208 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz53 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz53 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz99 qz209 (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1)))))) 28259180365 137438953472 125603797025 505637909823488 1346341472045

noncomputable abbrev qz433 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) qz496 (Real.log (Enclosure.sfrac Bool.false 17 1)))

noncomputable abbrev qz212 := (Real.cos qz433)

noncomputable abbrev qz213 := (Real.sin qz433)

noncomputable abbrev qz434 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 17)))

noncomputable abbrev qz435 := (@Neg.neg Real Real.instNeg qz213)

noncomputable def ep852 := @Enclosure.Complex.IsNear.of_eq qz207 (Complex.mk (@HMul.hMul Real Real Real qz0 qz434 qz212) (@HMul.hMul Real Real Real qz0 qz434 qz435)) Bool.true 28259180365 137438953472 125603797025 505637909823488 Bool.false 35359230289 274877906944 250595412129 1011275819646976 (BSN.cpow_neg_s_mk qz151 81143 1000 17 qz152 rfl)

noncomputable abbrev qz436 := (Real.sqrt (@Nat.cast Real Real.instNatCast 17))

noncomputable abbrev qz437 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 17) qz19)

noncomputable def ep853 := @Enclosure.Real.IsNear.inv_image qz436 2161695 524288 1 524288 63579 63580 262144 (@Enclosure.Real.IsNear.of_eq qz436 (Real.sqrt qz437) Bool.false 2161695 524288 1 524288 (BSN.sqrt_natCast_div_one 17) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz437) Bool.false 2161695 524288 1 524288 2161695 524288 1 524288 (BSN.sqrt_enclosure 17 1 1080847 1080848 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep854 := BSN.log_dyadic_bound 1 33 2 1 3267 262144 80938 1 1 15892 34 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 1) (BSN.artanhQ 33) 0 1 1 3267 1 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz438 := (Real.log (Enclosure.sfrac Bool.false 17 1))

noncomputable abbrev qz214 := qz438

noncomputable def ep855 := @Enclosure.Real.IsNear.mulLit_ff qz151 qz214 81143 1000 0 1 3189913004350711 1125899906842624 125000000040469 10117250000000000000 258839110912029742673 1125899906842624000 10142875003283776067 10117250000000000000000 qz153 (BSN.isNear_log_sfrac 17 1 3189913004350711 1125899906842624 125000000040469 10117250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz437) Bool.false 26758929747600409100288 9444732965739290427392 1000000000323752 80938000000000000000 3189913004350711 1125899906842624 125000000040469 10117250000000000000 (BSN.log_rat_reduce_isNear 17 1 4 34 32 15892 262144 24973259072661432 36028797018963968 80938 1000000000000000 rfl rfl rfl rfl (ep854 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep856 := nat_lit 129835891142032046409605158276546816

noncomputable def ep857 := BSN.cos_dyadic_bound_f 600272836 1073741824 2 1 524288 162035 ep856 ep90 ep856 ep856 ep91 ep856 444470 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 600272836) qz281 0 1 ep856 ep90 ep856 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 600272836) qz282 0 1 ep856 ep91 ep856 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz215 := qz433

noncomputable abbrev qz439 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 120531353) qz27)

noncomputable def ep858 := @Enclosure.Real.IsNear.cos_image qz215 qz439 Bool.false 120531353 524288 527 524288 Bool.true 444470 524288 1 80938 (@Enclosure.Real.IsNear.recentre' qz215 Bool.false 258839110912029742673 1125899906842624000 10142875003283776067 10117250000000000000000 120531353 524288 527 524288 (ep855 rfl) rfl) (Enclosure.sfrac_false_div 120531353 524288) (BSN.cos_reduce2 qz439 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 42240445666580785790976) qz29) 226375608064910080 72057594037927936 Bool.false 444470 524288 36 1000000000000000 161876 80938 (BSN.sin_reduce_arg_pos_rat_q2 120531353 524288 226375608064910080 72057594037927936 36 42240445666580785790976 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 444470 524288 42240445666580785790976 75557863725914323419136 600272836 1073741824 162035 161876 (ep857 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep859 := BSN.sin_dyadic_bound_f 600272836 1073741824 2 1 524288 162035 ep856 ep86 ep856 ep856 ep87 ep856 278071 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 600272836) qz285 0 1 ep856 ep86 ep856 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 600272836) qz286 0 1 ep856 ep87 ep856 rfl rfl rfl rfl) rfl rfl

noncomputable def ep860 := @Enclosure.Real.IsNear.sin_image qz215 qz439 Bool.false 120531353 524288 527 524288 Bool.true 278071 524288 1 80938 (@Enclosure.Real.IsNear.recentre' qz215 Bool.false 258839110912029742673 1125899906842624000 10142875003283776067 10117250000000000000000 120531353 524288 527 524288 (ep855 rfl) rfl) (Enclosure.sfrac_false_div 120531353 524288) (BSN.sin_reduce2 qz439 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 42240445666580785790976) qz29) 226375608064910080 72057594037927936 Bool.false 278071 524288 36 1000000000000000 161876 80938 (BSN.sin_reduce_arg_pos_rat_q2 120531353 524288 226375608064910080 72057594037927936 36 42240445666580785790976 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 278071 524288 42240445666580785790976 75557863725914323419136 600272836 1073741824 162035 161876 (ep859 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep861 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz434 qz212) (@HMul.hMul Real Real Real qz0 qz434 qz435) Bool.true 28259180365 137438953472 125603797025 505637909823488 Bool.false 35359230289 274877906944 250595412129 1011275819646976 (@Enclosure.Real.IsNear.mulLit_ft qz434 qz212 127159 524288 1 524288 222235 262144 21589307 21217411072 28259180365 137438953472 125603797025 505637909823488 (@Enclosure.Real.IsNear.recentre' qz434 Bool.false 127159 524288 1 524288 127159 524288 1 524288 (ep853 rfl rfl) rfl) (@Enclosure.Real.IsNear.recentre' qz212 Bool.true 444470 524288 43178614 42434822144 222235 262144 21589307 21217411072 (ep858 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz434 qz435 127159 524288 1 524288 278071 524288 21589307 21217411072 35359230289 274877906944 250595412129 1011275819646976 (@Enclosure.Real.IsNear.recentre' qz434 Bool.false 127159 524288 1 524288 127159 524288 1 524288 (ep853 rfl rfl) rfl) (@Enclosure.Real.IsNear.neg qz213 Bool.true 278071 524288 21589307 21217411072 (@Enclosure.Real.IsNear.recentre' qz213 Bool.true 278071 524288 43178614 42434822144 278071 524288 21589307 21217411072 (ep860 rfl rfl) rfl)) rfl)

noncomputable def ep862 := @ep851 2686450071192 0 1 38046506491399260396425 369222886339408375578624 169105600981079891666125 ep845 (@Enclosure.Complex.IsNear.re_isNear qz207 Bool.true 28259180365 137438953472 125603797025 505637909823488 Bool.false 35359230289 274877906944 250595412129 1011275819646976 (ep852 ep861))

noncomputable def ep863 := @Enclosure.Complex.IsNear.re_isNear (@HAdd.hAdd Complex Complex Complex qz5 qz208 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz53 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz53 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz99 qz209 (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1))))) Bool.false 1346341472045 2686450071192 0 1 Bool.false

noncomputable def ep864 := @Enclosure.Complex.IsNear.addLitP qz208 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz53 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz53 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz99 qz209 (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1)))) Bool.false 6567436449 13168872898 0 1 Bool.true 1379431000

noncomputable def ep865 := @ep864 6584436449 0 1 Bool.false 1 408 0 1 Bool.false 81143 204000 0 1 Bool.false 2692682944090 1346341472045 2686450071192 0 1 Bool.false 252877002781207 252877002781207 1343225035596000 0 1

noncomputable abbrev qz216 := (@HDiv.hDiv Complex Complex Complex qz323 qz432 (@HSub.hSub Complex Complex Complex qz315 qz392 (1 : Complex)))

noncomputable def ep866 := @Enclosure.Complex.IsNear.addLitP qz216 qz72 Bool.true 34000000 26337745796 0 1 Bool.true 5517724000 26337745796 0 1

noncomputable def ep867 := @Enclosure.Complex.IsNear.of_eq qz216 (Complex.mk (Enclosure.sfrac Bool.true 34000000 26337745796) (Enclosure.sfrac Bool.true 5517724000 26337745796)) Bool.true 34000000 26337745796 0 1 Bool.true 5517724000 26337745796 0 1

noncomputable def ep868 := @ep866 Bool.false 1 2 0 1 Bool.false 0 1 0 1 Bool.false 26269745796 6567436449 13168872898 0 1 Bool.true 5517724000 1379431000 6584436449 0 1 (ep867 (BSN.N_div_s_sub_one_mk qz151 81143 1000 17 qz152 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 34000000 26337745796) (Enclosure.sfrac Bool.true 5517724000 26337745796) Bool.true 34000000 26337745796 0 1 Bool.true 5517724000 26337745796 0 1 (Enclosure.Real.IsNear.const Bool.true 34000000 26337745796) (Enclosure.Real.IsNear.const Bool.true 5517724000 26337745796))) qz73 rfl

noncomputable abbrev qz217 := (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz354 qz432 1))

noncomputable def ep869 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz53 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz53 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz99 qz209 (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1)))) (@HAdd.hAdd Complex Complex Complex qz5 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz53 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz53 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz99 qz209 (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz74)) ↑qz138) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1))) qz217)) Bool.false 1 408 0 1

noncomputable def ep870 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz53 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz53 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz99 qz209 (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz74)) ↑qz138) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1))) qz217) Bool.false 0 1 0 1 Bool.false

noncomputable def ep871 := @ep870 0 1 0 1 Bool.false 1 408 0 1 Bool.false 81143 204000 0 1 Bool.false 1 1 408 0 1 Bool.false 81143 81143 204000 0

noncomputable def ep872 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz53 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz53 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz99 qz209 (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1)))) (Complex.mk qz14 qz14) Bool.false 0 1 0 1 Bool.false

noncomputable def ep873 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz74)) ↑qz138) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1))) qz217 Bool.false 1 408 0 1 Bool.false 81143 204000 0 1

noncomputable def ep874 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz74)) ↑qz138) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz217)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz74)) ↑qz138) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz217)) 1 408 0 1 0 1 0

noncomputable def ep875 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz74)) ↑qz138) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz217) 1 24 0 1 1 17 0 1 1

noncomputable def ep876 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz74)) ↑qz138)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz74)) ↑qz138)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1)))) 1 24 0 1 0 1 0 1 1

noncomputable def ep877 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz74)) ↑qz138)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 1 2 0 1 1 24 0

noncomputable def ep878 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1)) qz142 Bool.false 1 2 0 1 Bool.false 81143 1000 0 1 (BSN.ascPochhammer_one_eval qz142)

noncomputable def ep879 := ep878 (@Enclosure.Complex.IsNear.of_eq qz142 (Complex.mk qz67 qz151) Bool.false 1 2 0 1 Bool.false 81143 1000 0 1 (BSN.s_crit_mk qz151 Bool.false 81143 1000 qz152) (@Enclosure.Complex.IsNear.mk qz67 qz151 Bool.false 1 2 0 1 Bool.false 81143 1000 0 1 qz333 qz153))

noncomputable def ep880 := @ep877 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz74)) ↑qz138) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep448) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 81143 1000 0 1 ep879)

noncomputable def ep881 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz74)) ↑qz138)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 81143 1000 0 1 0 1 0

noncomputable def ep882 := @ep881 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz74)) ↑qz138) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep448) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 81143 1000 0 1 ep879)

noncomputable def ep883 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz74)) ↑qz138)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz74)) ↑qz138)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1)))) 81143 12000 0 1 0 1 0 1 81143

noncomputable def ep884 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz74)) ↑qz138)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 81143 1000 0 1 81143 12000 0

noncomputable def ep885 := @ep884 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz74)) ↑qz138) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep448) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 81143 1000 0 1 ep879)

noncomputable def ep886 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz74)) ↑qz138)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 1 2 0 1 0 1 0

noncomputable def ep887 := @ep886 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz74)) ↑qz138) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep448) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 81143 1000 0 1 ep879)

noncomputable def ep888 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz74)) ↑qz138) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 24 0 1 Bool.false 81143 12000 0 1 (@ep876 1 24 0 1 (ep880 rfl) (ep882 rfl) rfl rfl) (@ep883 81143 12000 0 1 (ep885 rfl) (ep887 rfl) rfl rfl)

noncomputable def ep889 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz74)) ↑qz138) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 81143 12000 0 1 ep888

noncomputable abbrev qz218 := (@Enclosure.Complex.IsNear.of_eq (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz354 qz432 1)) (Complex.mk (Enclosure.sfrac Bool.false 1 17) qz277) Bool.false 1 17 0 1 Bool.false 0 1 0 1 (BSN.natCast_pow_inv_mk 17 1 17 EMRow21.d12 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 17) qz277 Bool.false 1 17 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 17) qz288))

noncomputable def ep890 := @ep875 408 0 1 ep889 (@Enclosure.Complex.IsNear.re_isNear qz217 Bool.false 1 17 0 1 Bool.false 0 1 0 1 qz218)

noncomputable def ep891 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz74)) ↑qz138) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz217) 81143 12000 0 1 0 1 0 1 0

noncomputable def ep892 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz74)) ↑qz138) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 81143 12000 0 1 ep888

noncomputable def ep893 := @ep891 1 0 1 ep892 (@Enclosure.Complex.IsNear.im_isNear qz217 Bool.false 1 17 0 1 Bool.false 0 1 0 1 qz218)

noncomputable def ep894 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz74)) ↑qz138) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz217)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz74)) ↑qz138) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz217)) 0 1 0 1 81143 204000 0

noncomputable def ep895 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz74)) ↑qz138) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz217) 1 24 0 1 0 1 0 1 0

noncomputable def ep896 := @ep895 1 0 1 ep889 (@Enclosure.Complex.IsNear.im_isNear qz217 Bool.false 1 17 0 1 Bool.false 0 1 0 1 qz218)

noncomputable def ep897 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz74)) ↑qz138) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz217) 81143 12000 0 1 1 17 0 1 81143

noncomputable def ep898 := @ep897 204000 0 1 ep892 (@Enclosure.Complex.IsNear.re_isNear qz217 Bool.false 1 17 0 1 Bool.false 0 1 0 1 qz218)

noncomputable def ep899 := @ep871 1 (@ep872 0 1 0 1 (BSN.bern_sum_base qz142 17) qz88) (ep873 (@ep874 1 1 1 408 0 1 (ep890 rfl) (ep893 rfl) rfl rfl) (@ep894 1 81143 81143 204000 0 1 (ep896 rfl) (ep898 rfl) rfl rfl)) rfl rfl rfl rfl rfl

noncomputable def ep900 := ep865 (ep868 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep869 Bool.false 81143 204000 0 1 (BSN.bern_sum_succ qz142 17 0 1 1 rfl rfl) (ep899 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl rfl

noncomputable def ep901 := @Enclosure.Real.IsNear.mulLit_ff qz211 (Complex.im (@HAdd.hAdd Complex Complex Complex qz5 qz208 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz53 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz53 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz99 qz209 (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1)))))) 35359230289 274877906944 250595412129 1011275819646976 252877002781207

noncomputable def ep902 := @ep901 1343225035596000 0 1 ep846 ep847 ep848 ep849 (@Enclosure.Complex.IsNear.im_isNear qz207 Bool.true 28259180365 137438953472 125603797025 505637909823488 Bool.false 35359230289 274877906944 250595412129 1011275819646976 (ep852 ep861))

noncomputable def ep903 := @Enclosure.Complex.IsNear.im_isNear (@HAdd.hAdd Complex Complex Complex qz5 qz208 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz53 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz53 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz99 qz209 (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1))))) Bool.false 1346341472045 2686450071192 0 1 Bool.false

noncomputable def ep904 := nat_lit 1429219366350947049080111

noncomputable def ep905 := nat_lit 1270492469184843380500367

noncomputable def ep906 := @Enclosure.Real.IsNear.addLit_tf_p (@HMul.hMul Real Real Real qz0 qz210 (Complex.im (@HAdd.hAdd Complex Complex Complex qz5 qz208 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz53 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz53 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz99 qz209 (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz211 (Complex.re (@HAdd.hAdd Complex Complex Complex qz5 qz208 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz53 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz53 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz99 qz209 (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1))))))) ep904 ep830 ep905

noncomputable def ep907 := nat_lit 27167419976853668275075153920

noncomputable def ep908 := nat_lit 905580665895122275835838464

noncomputable def ep909 := nat_lit 702306636456355120535505129628074583570589417472

noncomputable def ep910 := @Enclosure.Real.IsNear.mulLit_tf qz210 (Complex.im (@HAdd.hAdd Complex Complex Complex qz5 qz208 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz53 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz53 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz99 qz209 (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1)))))) 28259180365 137438953472 125603797025 505637909823488 252877002781207

noncomputable def ep911 := @ep910 1343225035596000 0 1 ep904 ep830 ep905 ep907 (@Enclosure.Complex.IsNear.re_isNear qz207 Bool.true 28259180365 137438953472 125603797025 505637909823488 Bool.false 35359230289 274877906944 250595412129 1011275819646976 (ep852 ep861))

noncomputable def ep912 := @Enclosure.Real.IsNear.mulLit_ff qz211 (Complex.re (@HAdd.hAdd Complex Complex Complex qz5 qz208 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz53 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz53 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz99 qz209 (@HSub.hSub Nat Nat Nat qz98 (@HMul.hMul Nat Nat Nat qz53 2 k) 1)))))) 35359230289 274877906944 250595412129 1011275819646976 1346341472045

noncomputable def ep913 := @ep912 2686450071192 0 1 47605598157670410771005 738445772678816751157248 112462332017827102477935 ep908 (@Enclosure.Complex.IsNear.im_isNear qz207 Bool.true 28259180365 137438953472 125603797025 505637909823488 Bool.false 35359230289 274877906944 250595412129 1011275819646976 (ep852 ep861))

noncomputable abbrev qz440 := (ep900 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable def ep914 := @ep843 951060541532573489470139 ep830 357258648439973573449109 ep838 (@ep844 ep845 ep846 ep847 ep848 ep849 ep850 ep835 ep710 ep836 ep837 (ep862 (@ep863 252877002781207 1343225035596000 0 1 qz440) rfl) (ep902 (@ep903 252877002781207 1343225035596000 0 1 qz440) rfl) rfl rfl) (@ep906 ep907 47605598157670410771005 738445772678816751157248 112462332017827102477935 ep908 ep909 951060541532573489470139 ep830 357258648439973573449109 ep838 (ep911 (@ep903 252877002781207 1343225035596000 0 1 qz440) rfl) (ep913 (@ep863 252877002781207 1343225035596000 0 1 qz440) rfl) rfl rfl)

noncomputable def ep915 := @ep841 ep831 ep832 (@ep842 11124034016116736 (BSN.head_sum_c_eq qz142 17) EMRow21.d11) ep914 rfl rfl rfl rfl rfl rfl rfl rfl rfl

noncomputable def ep916 := @Enclosure.Complex.IsNear.re_isNear (zetaApproximant qz142 1 17) Bool.false ep709 ep710 ep711 ep712 Bool.false ep829 ep830 ep831 ep832 (@ep833 ep712 Bool.false ep829 ep830 ep831 ep832 (BSN.zetaApproximant_eq_folded' qz142 1 17 rfl) (ep915 rfl rfl rfl rfl rfl rfl rfl rfl rfl))

noncomputable def ep917 := @Enclosure.Real.IsNear.mulLit_tf (Real.sin (@HSub.hSub Real Real Real qz318 (Complex.im (@HSub.hSub Complex Complex Complex qz46 qz176 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz177 (@Nat.cast Complex Complex.instNatCast j))))) qz178)) (Complex.im (zetaApproximant qz142 1 17)) 143 524288 10015173

noncomputable def ep918 := @Enclosure.Real.IsNear.recentre' (Real.sin (@HSub.hSub Real Real Real qz318 (Complex.im (@HSub.hSub Complex Complex Complex qz46 qz176 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz177 (@Nat.cast Complex Complex.instNatCast j))))) qz178)) Bool.true 143 524288 20030346

noncomputable def ep919 := @Enclosure.Real.IsNear.sin_image (@HSub.hSub Real Real Real qz318 (Complex.im (@HSub.hSub Complex Complex Complex qz46 qz176 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz177 (@Nat.cast Complex Complex.instNatCast j))))) qz178) qz413 Bool.false 32941843 524288 241

noncomputable def ep920 := nat_lit 18124028265548543308545024114900355566261246934212555575714913609682944860416

noncomputable def ep921 := nat_lit 54241292497405859199691961276519500711464888127287557669985771789873910456576

noncomputable def ep922 := BSN.cos_dyadic_bound_f 1686335654 1073741824 3 2 524288 162035 ep920 ep57 ep825 ep921 ep60 ep825 143 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1686335654) qz281 0 2 ep920 ep57 ep825 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1686335654) qz282 0 2 ep921 ep60 ep825 rfl rfl rfl rfl) rfl rfl

noncomputable def ep923 := @ep919 524288 Bool.true 143 524288 1 80938 (@ep717 32941843 524288 241 524288 ep823 rfl) (Enclosure.sfrac_false_div 32941843 524288) (BSN.sin_reduce3 qz413 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 118665322266028761153536) qz29) 226375608064910080 72057594037927936 Bool.false 143 524288 9 1000000000000000 161876 80938 (BSN.sin_reduce_arg_pos_rat_q3 32941843 524288 226375608064910080 72057594037927936 9 118665322266028761153536 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 143 524288 118665322266028761153536 75557863725914323419136 1686335654 1073741824 162035 161876 (ep922 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep924 := @Enclosure.Complex.IsNear.im_isNear (zetaApproximant qz142 1 17) Bool.false ep709 ep710 ep711 ep712 Bool.false ep829 ep830 ep831 ep832 (@ep833 ep712 Bool.false ep829 ep830 ep831 ep832 (BSN.zetaApproximant_eq_folded' qz142 1 17 rfl) (ep915 rfl rfl rfl rfl rfl rfl rfl rfl rfl))

theorem EMRow21.d13 : Enclosure.Real.IsNear (hardyZApproximantEM 1 17 qz151) Bool.false ep692 ep693 ep694 ep695 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantEM 1 17 qz151) ep696 Bool.false ep692 ep693 ep694 ep695 (@Eq.refl Real ep696) (@ep697 Bool.false ep692 ep693 ep694 ep695 (BSN.re_exp_mul (@HSub.hSub Real Real Real qz318 (Complex.im (@HSub.hSub Complex Complex Complex qz46 qz176 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz177 (@Nat.cast Complex Complex.instNatCast j))))) qz178) (zetaApproximant qz142 1 17)) (@ep699 ep700 ep701 ep702 ep703 ep704 ep705 ep706 ep707 ep692 ep693 ep694 ep695 (@ep708 21217411072 ep709 ep710 ep711 ep712 ep698 ep700 ep701 ep702 (@ep713 42434822144 524287 524288 10015173 21217411072 (ep828 rfl rfl) rfl) ep916 rfl) (@ep917 21217411072 ep829 ep830 ep831 ep832 ep703 ep704 ep705 ep706 (@ep918 42434822144 143 524288 10015173 21217411072 (ep923 rfl rfl) rfl) ep924 rfl) rfl rfl))

theorem EMRow21.d14 : @Eq Nat (Nat.mul (BSN.factNat (Nat.succ (Nat.mul 2 1))) (Nat.pow 4 (Nat.mul 2 1))) 96 := @Eq.refl Nat 96

theorem EMRow21.d15 : @Eq Nat (Nat.mul (Nat.mul 2 1) (Nat.pow (Nat.succ (Nat.mul 4 2)) (Nat.mul 2 1))) 162 := @Eq.refl Nat 162

theorem EMRow21.d16 : @Eq Nat (BSN.factNat (Nat.mul 2 2)) 24 := @Eq.refl Nat 24

theorem EMRow21.d17 : @Eq Nat (Nat.pow 16 (Nat.succ (Nat.mul 2 3))) 268435456 := @Eq.refl Nat 268435456

noncomputable abbrev qz499 := (@HAdd.hAdd Complex Complex Complex qz502 qz501 (@Nat.cast Complex Complex.instNatCast 3))

noncomputable abbrev qz441 := qz499

noncomputable abbrev qz219 := (@HDiv.hDiv Real Real Real qz269 (@Norm.norm Complex Complex.instNorm qz441) (@HAdd.hAdd Real Real Real qz343 (Complex.re qz271) qz289))

noncomputable abbrev qz220 := (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 2)

noncomputable abbrev qz221 := (@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 2)))

noncomputable abbrev qz442 := (@HPow.hPow Complex Complex Complex qz480 (@Nat.cast Complex Complex.instNatCast 16) (@HSub.hSub Complex Complex Complex qz487 qz481 qz482))

noncomputable abbrev qz222 := qz442

noncomputable def ep925 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz6 1 16))) (@HMul.hMul Real Real Real qz0 qz219 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz220)) ↑qz221) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz222))) 1022340391 51539607552 39569213 463856467968 29299088240040791 31525197391593472 15490589449

noncomputable def ep926 := nat_lit 1542292992150794590889181184

noncomputable def ep927 := @Enclosure.Real.IsNear.mulLit_ff (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz6 1 16)) 4427 294912 1 884736 692799 524288 2927 524288 1022340391 51539607552

noncomputable abbrev qz443 := (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid)))

noncomputable abbrev qz223 := (@HPow.hPow Real Nat Real qz443 qz270 2)

noncomputable def ep928 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 96 162) (@Inv.inv Real Real.instInv qz223) 96 162 0 1 13281 524288 1 524288 4427 294912 1 884736

noncomputable def ep929 := nat_lit 781950621441006189802102638025

noncomputable def ep930 := nat_lit 19807040628566084398385987584

noncomputable def ep931 := nat_lit 26986075409044041160201671

noncomputable def ep932 := nat_lit 1073741824000000000000000000000000000000

noncomputable abbrev qz224 := qz270

noncomputable abbrev qz444 := (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) qz224 1)

noncomputable def ep933 := @Enclosure.Real.IsNear.mulLit_ff qz444 qz224 884279719003555 140737488355328 1 500000000000000 884279719003555 140737488355328 1 500000000000000 ep929 ep930 ep931 ep932

noncomputable def ep934 := ep933 (@Enclosure.Real.IsNear.of_eq qz444 qz224 Bool.false 884279719003555 140737488355328 1 500000000000000 (BSN.pow_one_r qz224) (@Enclosure.Real.IsNear.of_eq qz224 qz267 Bool.false 884279719003555 140737488355328 1 500000000000000 BSN.two_pi_eq qz268)) (@Enclosure.Real.IsNear.of_eq qz224 qz267 Bool.false 884279719003555 140737488355328 1 500000000000000 BSN.two_pi_eq qz268) rfl

noncomputable def ep935 := @Enclosure.Real.IsNear.inv_image qz223 ep929 ep930 ep931 ep932 6640 6641 262144 (@Enclosure.Real.IsNear.of_eq qz223 (@HMul.hMul Real Real Real qz0 qz444 qz224) Bool.false ep929 ep930 ep931 ep932 (BSN.pow_succ_r qz224 1 2 rfl) ep934) rfl rfl rfl

noncomputable def ep936 := ep928 (Enclosure.Real.IsNear.const Bool.false 96 162) (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz223) Bool.false 13281 524288 1 524288 13281 524288 1 524288 (ep935 rfl rfl rfl) rfl)

noncomputable def ep937 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (zetaApproximant qz6 1 16)) (Real.sqrt (@HAdd.hAdd Real Real Real qz343 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz6 1 16)) (Complex.re (zetaApproximant qz6 1 16))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz6 1 16)) (Complex.im (zetaApproximant qz6 1 16))))) Bool.false 692799 524288 2927 524288

noncomputable def ep938 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz343 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz6 1 16)) (Complex.re (zetaApproximant qz6 1 16))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz6 1 16)) (Complex.im (zetaApproximant qz6 1 16))))) Bool.false 692799 524288 2927 524288

noncomputable def ep939 := nat_lit 117593203511327404349421463796740755689309

noncomputable def ep940 := nat_lit 67344182649625258930950717157933056000000

noncomputable def ep941 := nat_lit 5199558425347936302504888611239022600860015519021798399

noncomputable def ep942 := nat_lit 352612418153570954978614583224041964505398775906304000000

noncomputable def ep943 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz343 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz6 1 16)) (Complex.re (zetaApproximant qz6 1 16))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz6 1 16)) (Complex.im (zetaApproximant qz6 1 16)))) ep939 ep940 ep941 ep942 344936 347863

noncomputable def ep944 := nat_lit 72783605667533753607413341176633298774908433729

noncomputable def ep945 := nat_lit 41682908019688564516781540089791168213575270400

noncomputable def ep946 := nat_lit 5168684436006944154536102320242116302293928242732157139

noncomputable def ep947 := nat_lit 172276690158711971225146469282333303637311929

noncomputable def ep948 := nat_lit 6512954378076338205747115639029870033371136000000

noncomputable def ep949 := nat_lit 1543699467049607398439314549845314928304363814482063

noncomputable def ep950 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz6 1 16)) (Complex.re (zetaApproximant qz6 1 16))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz6 1 16)) (Complex.im (zetaApproximant qz6 1 16))) ep944 ep945 ep946 ep942 ep947 ep948 ep949

noncomputable def ep951 := nat_lit 17630620907678547748930729161202098225269938795315200000

noncomputable def ep952 := nat_lit 474043484177975564861865141070091718047692879193216379340321323452851801468340466788211464601600

noncomputable def ep953 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (zetaApproximant qz6 1 16)) (Complex.re (zetaApproximant qz6 1 16)) 269784368834693151885473 204163924383541776875520 ep169 ep170 269784368834693151885473 204163924383541776875520 ep169 ep170 ep944

noncomputable def ep954 := @Enclosure.Real.IsNear.mulLit_tt (Complex.im (zetaApproximant qz6 1 16)) (Complex.im (zetaApproximant qz6 1 16)) 13125421523086866989077 ep299 ep300 ep301 13125421523086866989077 ep299 ep300 ep301 ep947

noncomputable def ep955 := @ep925 31525197391593472 ep926 89773267516330501 94575592174780416 73028068323827 851180329573023744 (@ep927 39569213 463856467968 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaStirlingErrorBound 1 2) (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 96 162) (@Inv.inv Real Real.instInv qz223)) Bool.false 4427 294912 1 884736 (BSN.theta_err_eq 1 2 96 162 EMRow21.d14 EMRow21.d15 rfl) (ep936 rfl)) (ep937 (BSN.norm_eq_sqrt_mul_add (zetaApproximant qz6 1 16)) (@ep938 692799 524288 2927 524288 (@ep943 262144 (@ep950 ep951 ep952 ep939 ep940 ep941 ep942 (@ep953 ep945 ep946 ep942 ep485 ep485 rfl) (@ep954 ep948 ep949 ep951 ep493 ep493 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl)

noncomputable abbrev qz225 := (@Norm.norm Complex Complex.instNorm qz441)

noncomputable abbrev qz445 := (Enclosure.sfrac Bool.false 2 7)

noncomputable def ep956 := @Enclosure.Real.IsNear.of_eq (@HMul.hMul Real Real Real qz0 qz219 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz220)) ↑qz221) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz222))) (@HMul.hMul Real Real Real qz0 (@HMul.hMul Real Real Real qz0 qz225 qz445) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz220)) ↑qz221) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz222))) Bool.false 29299088240040791 31525197391593472 15490589449 31525197391593472 (BSN.zrb_shape_eq qz225 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz220)) ↑qz221) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz222)) qz17 3)

noncomputable def ep957 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz0 qz225 qz445) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz220)) ↑qz221) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz222)) 41287583 1835008 1 1835008 709634377 17179869184 179 8589934592

noncomputable def ep958 := @Enclosure.Real.IsNear.mulLit_ff qz225 qz445 41287583 524288 1 524288 2 7 0 1 41287583 1835008

noncomputable abbrev qz446 := (Complex.re qz499)

noncomputable abbrev qz447 := (Complex.im qz499)

noncomputable abbrev qz226 := (@HAdd.hAdd Real Real Real qz343 (@HMul.hMul Real Real Real qz266 qz446 qz446) (@HMul.hMul Real Real Real qz266 qz447 qz447))

noncomputable abbrev qz227 := qz441

noncomputable def ep959 := @Enclosure.Real.IsNear.of_eq qz225 (Real.sqrt qz226) Bool.false 41287583 524288 1 524288 (BSN.norm_eq_sqrt_mul_add qz227)

noncomputable def ep960 := @Enclosure.Real.IsNear.recentre' (Real.sqrt qz226) Bool.false 41287583 524288 1 524288 41287583

noncomputable def ep961 := @Enclosure.Real.IsNear.sqrt_image qz226 387595849 62500 0 1 20643791 20643792 262144

noncomputable abbrev qz228 := (@HMul.hMul Real Real Real qz266 qz446 qz446)

noncomputable abbrev qz229 := (@HMul.hMul Real Real Real qz266 qz447 qz447)

noncomputable def ep962 := @Enclosure.Real.IsNear.addLit_ff qz228 qz229 49 4 0 1 96707556 15625 0 1

noncomputable abbrev qz230 := qz446

noncomputable def ep963 := @Enclosure.Real.IsNear.mulLit_ff qz230 qz230 7 2 0 1 7 2 0 1 49 4

noncomputable abbrev qz448 := (Enclosure.sfrac Bool.false 7 2)

noncomputable def ep964 := @Enclosure.Complex.IsNear.of_eq qz227 (Complex.mk qz448 qz17) Bool.false 7 2 0 1 Bool.false 78672 1000 0 1 (BSN.s_add_nat_mk qz17 Bool.false 78672 1000 3 qz18)

noncomputable abbrev qz449 := (ep964 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7 2) qz17 Bool.false 7 2 0 1 Bool.false 78672 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 7 2) qz22))

noncomputable def ep965 := @ep963 0 1 (@Enclosure.Complex.IsNear.re_isNear qz227 Bool.false 7 2 0 1 Bool.false 78672 1000 0 1 qz449)

noncomputable def ep966 := ep965 (@Enclosure.Complex.IsNear.re_isNear qz227 Bool.false 7 2 0 1 Bool.false 78672 1000 0 1 qz449)

noncomputable abbrev qz231 := qz447

noncomputable def ep967 := @Enclosure.Real.IsNear.mulLit_ff qz231 qz231 78672 1000 0 1 78672 1000 0 1 96707556 15625

noncomputable def ep968 := @ep967 0 1 (@Enclosure.Complex.IsNear.im_isNear qz227 Bool.false 7 2 0 1 Bool.false 78672 1000 0 1 qz449)

noncomputable def ep969 := ep968 (@Enclosure.Complex.IsNear.im_isNear qz227 Bool.false 7 2 0 1 Bool.false 78672 1000 0 1 qz449)

noncomputable def ep970 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz220)) ↑qz221) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz222)) (Real.sqrt (@HAdd.hAdd Real Real Real qz343 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz220)) ↑qz221) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz222)) (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz220)) ↑qz221) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz222))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz220)) ↑qz221) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz222)) (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz220)) ↑qz221) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz222))))) Bool.false 709634377 17179869184

noncomputable def ep971 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz343 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz220)) ↑qz221) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz222)) (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz220)) ↑qz221) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz222))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz220)) ↑qz221) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz222)) (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz220)) ↑qz221) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz222))))) Bool.false 1419268754 34359738368

noncomputable def ep972 := nat_lit 16720971986396638373023591880249274235583800500903802612013

noncomputable def ep973 := nat_lit 9800132167323027747745188694034924489932800000000000000000000

noncomputable def ep974 := nat_lit 9191037836074799849496624759511544444203388707362919137656399

noncomputable def ep975 := nat_lit 5350022691168820312664707723235466055593496254873600000000000000000000

noncomputable def ep976 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz343 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz220)) ↑qz221) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz222)) (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz220)) ↑qz221) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz222))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz220)) ↑qz221) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz222)) (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz220)) ↑qz221) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz222)))) ep972 ep973 ep974 ep975

noncomputable def ep977 := nat_lit 3623314375823622309353348367356424341889600833763827070889

noncomputable def ep978 := nat_lit 2177807148294006166165597487563316553318400000000000000000000

noncomputable def ep979 := nat_lit 5850208300647691275533119540214235281706473876134773996802527

noncomputable def ep980 := nat_lit 3566681794112546875109805148823644037062330836582400000000000000000000

noncomputable def ep981 := nat_lit 33284583615227038474681938171629175766447739917326463441

noncomputable def ep982 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz220)) ↑qz221) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz222)) (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz220)) ↑qz221) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz222))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz220)) ↑qz221) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz222)) (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz220)) ↑qz221) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz222))) ep977 ep978 ep979 ep980 ep981

noncomputable def ep983 := nat_lit 784010573385842219819615095522793959194624000000000000000000

noncomputable def ep984 := nat_lit 831450770206525872393890898380383043287355786321516284905217

noncomputable def ep985 := nat_lit 10700045382337640625329415446470932111186992509747200000000000000000000

noncomputable def ep986 := nat_lit 2913204185471874134417975961867732426852672562623328649313650683869910717669605949024826424228315136000000000000000000

noncomputable def ep987 := nat_lit 60193972919417956535780439667

noncomputable def ep988 := nat_lit 1475739525896764129280000000000

noncomputable def ep989 := nat_lit 1200786358472422168751689361

noncomputable def ep990 := nat_lit 59721702873516147547832320000000000

noncomputable def ep991 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz220)) ↑qz221) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz222)) (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz220)) ↑qz221) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz222)) ep987 ep988 ep989 ep990 ep987 ep988 ep989

noncomputable def ep992 := nat_lit 5769279297730959954524423479

noncomputable def ep993 := nat_lit 885443715538058477568000000000

noncomputable def ep994 := nat_lit 356116670296364605387070573

noncomputable def ep995 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz220)) ↑qz221) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz222) Bool.true ep987 ep988 ep989 ep990 Bool.true ep992 ep993 ep994

noncomputable def ep996 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz220)) ↑qz221) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz222 Bool.true ep987 ep988 ep989 ep990 Bool.true ep992 ep993 ep994 ep990

noncomputable def ep997 := nat_lit 3577503165604962667848677

noncomputable def ep998 := nat_lit 7083549724304467820544000000

noncomputable def ep999 := nat_lit 1433320868964387541147975680000000

noncomputable def ep1000 := nat_lit 44586494819937691984983973969

noncomputable def ep1001 := nat_lit 1106804644422573096960000000000

noncomputable def ep1002 := nat_lit 80746396821179111004623857

noncomputable abbrev qz232 := (Complex.re qz442)

noncomputable abbrev qz233 := (Complex.im qz442)

noncomputable def ep1003 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz220)) ↑qz221) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)))) qz232) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz220)) ↑qz221) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)))) qz233) ep997 ep998 396140922283084976412947 ep999 ep1000 ep1001 ep1002

noncomputable def ep1004 := nat_lit 4071934286830646423715840000000000

noncomputable def ep1005 := nat_lit 319790250208600251003248453768432769545638181339136000000

noncomputable def ep1006 := nat_lit 47777362298812918038265856

noncomputable def ep1007 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz220)) ↑qz221) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)))) qz232 1160412547 30000000 0 1 15414790088463955 1180591620717411303424 341379385553201 ep1006 ep997

noncomputable def ep1008 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz220)) ↑qz221)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz220)) ↑qz221)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)))) 1160412547 30000000 0 1 0 1 0 1 1160412547

noncomputable def ep1009 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz220)) ↑qz221)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 3481237641 125000 0 1 1160412547 30000000 0

noncomputable def ep1010 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz220)) ↑qz221) (Complex.mk (Enclosure.sfrac Bool.true 1 720) qz14) Bool.true 1 720 0 1 Bool.false 0 1 0 1 (BSN.bern_coeff_mk 2 1 30 24 Bool.true BSN.bern_real_2 EMRow21.d16 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 1 720) qz14 Bool.true 1 720 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.true 1 720) qz24)

noncomputable abbrev qz450 := (@HAdd.hAdd Complex Complex Complex qz479 qz478 qz483)

noncomputable abbrev qz234 := qz450

noncomputable def ep1011 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)) (@HMul.hMul Complex Complex Complex qz45 (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 2)) qz234) Bool.true 3481237641 125000 0 1 Bool.true 1900277164533 3906250 0 1

noncomputable abbrev qz235 := (Complex.re qz450)

noncomputable abbrev qz236 := (Complex.im qz450)

noncomputable def ep1012 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 2))) qz235) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 2))) qz236) 386783349 25000 0 1 193415112 15625 0 1

noncomputable def ep1013 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 2))) qz235 386783349 62500 0 1 5 2 0 1 386783349 25000

noncomputable abbrev qz451 := (@HAdd.hAdd Complex Complex Complex qz479 qz478 (@Nat.cast Complex Complex.instNatCast 1))

noncomputable abbrev qz237 := qz451

noncomputable def ep1014 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 2)) (@HMul.hMul Complex Complex Complex qz45 (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)) qz237) Bool.true 386783349 62500 0 1 Bool.false 19668 125 0 1

noncomputable abbrev qz238 := (Complex.re qz451)

noncomputable abbrev qz239 := (Complex.im qz451)

noncomputable def ep1015 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1))) qz238) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1))) qz239) 3 4 0 1 96707556 15625 0 1

noncomputable def ep1016 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1))) qz238 1 2 0 1 3 2 0 1 3 4

noncomputable def ep1017 := @ep1016 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 78672 1000 0 1 ep450)

noncomputable abbrev qz452 := (Enclosure.sfrac Bool.false 3 2)

noncomputable def ep1018 := @Enclosure.Complex.IsNear.of_eq qz237 (Complex.mk qz452 qz17) Bool.false 3 2 0 1 Bool.false 78672 1000 0 1 (BSN.s_add_nat_mk qz17 Bool.false 78672 1000 1 qz18)

noncomputable abbrev qz453 := (ep1018 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 3 2) qz17 Bool.false 3 2 0 1 Bool.false 78672 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 3 2) qz22))

noncomputable def ep1019 := ep1017 (@Enclosure.Complex.IsNear.re_isNear qz237 Bool.false 3 2 0 1 Bool.false 78672 1000 0 1 qz453)

noncomputable def ep1020 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1))) qz239 78672 1000 0 1 78672 1000 0 1 96707556 15625

noncomputable def ep1021 := @ep1020 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 78672 1000 0 1 ep450)

noncomputable def ep1022 := ep1021 (@Enclosure.Complex.IsNear.im_isNear qz237 Bool.false 3 2 0 1 Bool.false 78672 1000 0 1 qz453)

noncomputable def ep1023 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)) qz237 Bool.true 386783349 62500 0 1 Bool.false 19668 125 0 1 (@ep1015 386783349 386783349 62500 0 1 (ep1019 rfl) (ep1022 rfl) rfl rfl)

noncomputable def ep1024 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1))) qz239) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1))) qz238) 4917 125 0 1 14751 125 0 1

noncomputable def ep1025 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1))) qz239 1 2 0 1 78672 1000 0 1 4917 125

noncomputable def ep1026 := @ep1025 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 78672 1000 0 1 ep450)

noncomputable def ep1027 := ep1026 (@Enclosure.Complex.IsNear.im_isNear qz237 Bool.false 3 2 0 1 Bool.false 78672 1000 0 1 qz453)

noncomputable def ep1028 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1))) qz238 78672 1000 0 1 3 2 0 1 14751 125

noncomputable def ep1029 := @ep1028 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 78672 1000 0 1 ep450)

noncomputable def ep1030 := ep1029 (@Enclosure.Complex.IsNear.re_isNear qz237 Bool.false 3 2 0 1 Bool.false 78672 1000 0 1 qz453)

noncomputable abbrev qz240 := (ep1014 (BSN.ascPochhammer_succ_eval_c 1 2 qz271 rfl) (ep1023 (@ep1024 2458500 19668 125 0 1 (ep1027 rfl) (ep1030 rfl) rfl rfl)))

noncomputable def ep1031 := @ep1013 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 386783349 62500 0 1 Bool.false 19668 125 0 1 qz240)

noncomputable abbrev qz454 := (Enclosure.sfrac Bool.false 5 2)

noncomputable def ep1032 := @Enclosure.Complex.IsNear.of_eq qz234 (Complex.mk qz454 qz17) Bool.false 5 2 0 1 Bool.false 78672 1000 0 1 (BSN.s_add_nat_mk qz17 Bool.false 78672 1000 2 qz18)

noncomputable abbrev qz455 := (ep1032 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 5 2) qz17 Bool.false 5 2 0 1 Bool.false 78672 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 5 2) qz22))

noncomputable def ep1033 := ep1031 (@Enclosure.Complex.IsNear.re_isNear qz234 Bool.false 5 2 0 1 Bool.false 78672 1000 0 1 qz455)

noncomputable def ep1034 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 2))) qz236 19668 125 0 1 78672 1000 0 1 193415112 15625

noncomputable def ep1035 := @ep1034 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 386783349 62500 0 1 Bool.false 19668 125 0 1 qz240)

noncomputable def ep1036 := ep1035 (@Enclosure.Complex.IsNear.im_isNear qz234 Bool.false 5 2 0 1 Bool.false 78672 1000 0 1 qz455)

noncomputable def ep1037 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 2)) qz234 Bool.true 3481237641 125000 0 1 Bool.true 1900277164533 3906250 0 1 (@ep1012 10878867628125 3481237641 125000 0 1 (ep1033 rfl) (ep1036 rfl) rfl rfl)

noncomputable def ep1038 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 2))) qz236) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 2))) qz235) 1901813727033 3906250 0 1 9834 25 0 1

noncomputable def ep1039 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 2))) qz236 386783349 62500 0 1 78672 1000 0 1 1901813727033 3906250

noncomputable def ep1040 := @ep1039 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 386783349 62500 0 1 Bool.false 19668 125 0 1 qz240)

noncomputable def ep1041 := ep1040 (@Enclosure.Complex.IsNear.im_isNear qz234 Bool.false 5 2 0 1 Bool.false 78672 1000 0 1 qz455)

noncomputable def ep1042 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 2))) qz235 19668 125 0 1 5 2 0 1 9834 25

noncomputable def ep1043 := @ep1042 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 386783349 62500 0 1 Bool.false 19668 125 0 1 qz240)

noncomputable def ep1044 := ep1043 (@Enclosure.Complex.IsNear.re_isNear qz234 Bool.false 5 2 0 1 Bool.false 78672 1000 0 1 qz455)

noncomputable abbrev qz241 := (ep1011 (BSN.ascPochhammer_succ_eval_c 2 3 qz271 rfl) (ep1037 (@ep1038 47506929113325 1900277164533 3906250 0 1 (ep1041 rfl) (ep1044 rfl) rfl rfl)))

noncomputable def ep1045 := @ep1009 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz220)) ↑qz221) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1010) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 3481237641 125000 0 1 Bool.true 1900277164533 3906250 0 1 qz241)

noncomputable def ep1046 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz220)) ↑qz221)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 1900277164533 3906250 0 1 0 1 0

noncomputable def ep1047 := @ep1046 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz220)) ↑qz221) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1010) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 3481237641 125000 0 1 Bool.true 1900277164533 3906250 0 1 qz241)

noncomputable def ep1048 := @Enclosure.Real.IsNear.addLit_ft_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz220)) ↑qz221)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz220)) ↑qz221)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)))) 633425721511 937500000 0 1 0 1 0 1 633425721511

noncomputable def ep1049 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz220)) ↑qz221)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 1900277164533 3906250 0 1 633425721511 937500000 0

noncomputable def ep1050 := @ep1049 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz220)) ↑qz221) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1010) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 3481237641 125000 0 1 Bool.true 1900277164533 3906250 0 1 qz241)

noncomputable def ep1051 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz220)) ↑qz221)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 3481237641 125000 0 1 0 1 0

noncomputable def ep1052 := @ep1051 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz220)) ↑qz221) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1010) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 3481237641 125000 0 1 Bool.true 1900277164533 3906250 0 1 qz241)

noncomputable def ep1053 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz220)) ↑qz221) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.false 1160412547 30000000 0 1 Bool.false 633425721511 937500000 0 1 (@ep1008 1160412547 30000000 0 1 (ep1045 rfl) (ep1047 rfl) rfl rfl) (@ep1048 633425721511 937500000 0 1 (ep1050 rfl) (ep1052 rfl) rfl rfl)

noncomputable def ep1054 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz220)) ↑qz221) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 1160412547 30000000 0 1 Bool.false 633425721511 937500000 0 1 ep1053

noncomputable def ep1055 := @Enclosure.Complex.IsNear.re_isNear qz222 Bool.true 15414790088463955 1180591620717411303424 341379385553201 ep1006 Bool.false 70389460525188679 1180591620717411303424 1402232866253357 ep1006

noncomputable abbrev qz456 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 268435456)))

noncomputable def ep1056 := @Enclosure.Complex.IsNear.of_eq qz222 (Complex.mk (@HMul.hMul Real Real Real qz0 qz456 qz132) (@HMul.hMul Real Real Real qz0 qz456 qz133)) Bool.true 15414790088463955 1180591620717411303424 341379385553201 ep1006 Bool.false 70389460525188679 1180591620717411303424 1402232866253357

noncomputable abbrev qz457 := (Real.sqrt (@Nat.cast Real Real.instNatCast 268435456))

noncomputable abbrev qz458 := (@Nat.cast Real Real.instNatCast 268435456)

noncomputable def ep1057 := @Enclosure.Real.IsNear.inv_image qz457 562949953421313 34359738368 1 34359738368 1048575 1048576 17179869184 (@Enclosure.Real.IsNear.of_eq qz457 (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz458 qz19)) Bool.false 562949953421313 34359738368 1 34359738368 (BSN.sqrt_natCast_div_one 268435456) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz458 qz19)) Bool.false 562949953421313 34359738368 1 34359738368 562949953421313 34359738368 1 34359738368 (BSN.sqrt_enclosure 268435456 1 281474976710656 281474976710657 17179869184 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep1058 := nat_lit 1716149295865858209928445952

noncomputable def ep1059 := nat_lit 618970019642690137449562112

noncomputable def ep1060 := nat_lit 5304352768000000000000000

noncomputable def ep1061 := BSN.log_dyadic_bound 0 32 1 0 1 17179869184 5304352768 0 1 0 32 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 0) (BSN.artanhQ 32) 0 0 rfl) rfl rfl rfl

noncomputable def ep1062 := @Enclosure.Real.IsNear.mulLit_ff qz17 qz134 78672 1000 0 1 3121657384082679 1125899906842624 30518225629 161876000000000000000 15349189357534532643 70368744177664000 13641646856163 919750000000000000000 qz22 (BSN.isNear_log_sfrac 16 1 3121657384082679 1125899906842624 30518225629 161876000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' qz388 Bool.false ep1058 ep1059 1000021217411072 ep1060 3121657384082679 1125899906842624 30518225629 161876000000000000000 (BSN.log_rat_reduce_isNear 16 1 4 32 32 0 17179869184 24973259072661432 36028797018963968 5304352768 1000000000000000 rfl rfl rfl rfl (ep1061 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1063 := nat_lit 6710659325778961203730579456

noncomputable def ep1064 := nat_lit 4951760157141521099596496896

noncomputable def ep1065 := nat_lit 994436432335034586696945915232093952403640194111751808021543734636587715795298986183280854555573127767765642132230491284975237762069452635454068070071982368237677707264000000

noncomputable def ep1066 := nat_lit 7061461093083586024179172776487149921794651295521201685534719608389587370251949717138351715479917319946841476520062230191960740901052279494785699627855717567272383596304793600

noncomputable def ep1067 := nat_lit 565750174496962409088925234545678975533252286363707277025225965193976637586591486171248315006064849439977691135391531903944606181494400166551705707149725696000000000000

noncomputable def ep1068 := nat_lit 6024852554788676067004168425198218796672054408791021806996170683167202682857386613897992851636888148574391444582622123733111325507168399453810771753273527504238582536601600000

noncomputable def ep1069 := nat_lit 642592959470606328200304722660330642883313267892429353383659484363452450692927424259590006108672476115162574363325662947468427421995757434025498666134870298621786907263736217600

noncomputable def ep1070 := BSN.cos_dyadic_bound_f 95364204721860 70368744177664 4 3 34359738368 10619065601 ep1065 ep1066 ep1067 ep1068 ep1069 ep1067 7350348205 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 95364204721860) (BSN.cosEvenQ 70368744177664) 0 3 ep1065 ep1066 ep1067 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 95364204721860) (BSN.cosOddQ 70368744177664) 0 3 ep1068 ep1069 ep1067 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz459 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 7494721365983) (@Nat.cast Real Real.instNatCast 34359738368))

noncomputable def ep1071 := @Enclosure.Real.IsNear.cos_image qz135 qz459 Bool.false 7494721365983 34359738368 511 34359738368 Bool.true 7350348205 34359738368 1 5304352768 (@Enclosure.Real.IsNear.recentre' qz135 Bool.false 15349189357534532643 70368744177664000 13641646856163 919750000000000000000 7494721365983 34359738368 511 34359738368 (ep1062 rfl) rfl) (Enclosure.sfrac_false_div 7494721365983 34359738368) (BSN.cos_reduce2 qz459 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast ep1063) (@Nat.cast Real Real.instNatCast ep1064)) 226375608064910080 72057594037927936 Bool.false 7350348205 34359738368 34 1000000000000000 10608705536 5304352768 (BSN.sin_reduce_arg_pos_rat_q2 7494721365983 34359738368 226375608064910080 72057594037927936 34 ep1063 ep1064 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 7350348205 34359738368 ep1063 ep1064 95364204721860 70368744177664 10619065601 10608705536 (ep1070 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1072 := nat_lit 2583231266039482261410938910659651055600278870436795113528849218507905900185405759753852995939911990352960245065415050025348342270949269233621339829975856249915952490086400000

noncomputable def ep1073 := nat_lit 91798994210086618314329246094332948983330466841775621911951354909064635813275346322798572301238925159308939194760808992495489631713679633432214095162124328374540986751962316800

noncomputable def ep1074 := nat_lit 12907257840348398780422894390034111388792760110572165591968805884781913393466893243722163707791831689693809727066462303625315026670857053629637282629148082206359880466432000000

noncomputable def ep1075 := nat_lit 3212964797353031641001523613301653214416566339462146766918297421817262253464637121297950030543362380575812871816628314737342137109978787170127493330674351493108934536318681088000

noncomputable def ep1076 := BSN.sin_dyadic_bound_f 95364204721860 70368744177664 4 3 34359738368 10619065601 ep1072 ep1073 ep1067 ep1074 ep1075 ep1067 33564326329 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 95364204721860) (BSN.sinEvenQ 70368744177664) 0 3 ep1072 ep1073 ep1067 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 95364204721860) (BSN.sinOddQ 70368744177664) 0 3 ep1074 ep1075 ep1067 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1077 := @Enclosure.Real.IsNear.sin_image qz135 qz459 Bool.false 7494721365983 34359738368 511 34359738368 Bool.true 33564326329 34359738368 1 5304352768 (@Enclosure.Real.IsNear.recentre' qz135 Bool.false 15349189357534532643 70368744177664000 13641646856163 919750000000000000000 7494721365983 34359738368 511 34359738368 (ep1062 rfl) rfl) (Enclosure.sfrac_false_div 7494721365983 34359738368) (BSN.sin_reduce2 qz459 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast ep1063) (@Nat.cast Real Real.instNatCast ep1064)) 226375608064910080 72057594037927936 Bool.false 33564326329 34359738368 34 1000000000000000 10608705536 5304352768 (BSN.sin_reduce_arg_pos_rat_q2 7494721365983 34359738368 226375608064910080 72057594037927936 34 ep1063 ep1064 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 33564326329 34359738368 ep1063 ep1064 95364204721860 70368744177664 10619065601 10608705536 (ep1076 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1078 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz456 qz132) (@HMul.hMul Real Real Real qz0 qz456 qz133) Bool.true 15414790088463955 1180591620717411303424 341379385553201 ep1006 Bool.false 70389460525188679 1180591620717411303424 1402232866253357 ep1006 (@Enclosure.Real.IsNear.mulLit_ft qz456 qz132 2097151 34359738368 1 34359738368 7350348205 34359738368 20941803 1390504252014592 15414790088463955 1180591620717411303424 341379385553201 ep1006 (@Enclosure.Real.IsNear.recentre' qz456 Bool.false 2097151 34359738368 1 34359738368 2097151 34359738368 1 34359738368 (ep1057 rfl rfl) rfl) (@Enclosure.Real.IsNear.recentre' qz132 Bool.true 7350348205 34359738368 2744884002816 182256173320056602624 7350348205 34359738368 20941803 1390504252014592 (ep1071 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz456 qz133 2097151 34359738368 1 34359738368 33564326329 34359738368 20941803 1390504252014592 70389460525188679 1180591620717411303424 1402232866253357 ep1006 (@Enclosure.Real.IsNear.recentre' qz456 Bool.false 2097151 34359738368 1 34359738368 2097151 34359738368 1 34359738368 (ep1057 rfl rfl) rfl) (@Enclosure.Real.IsNear.neg qz136 Bool.true 33564326329 34359738368 20941803 1390504252014592 (@Enclosure.Real.IsNear.recentre' qz136 Bool.true 33564326329 34359738368 2744884002816 182256173320056602624 33564326329 34359738368 20941803 1390504252014592 (ep1077 rfl rfl) rfl)) rfl)

noncomputable def ep1079 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz220)) ↑qz221) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)))) qz233 633425721511 937500000 0 1 70389460525188679 1180591620717411303424 1402232866253357 ep1006 ep1000

noncomputable def ep1080 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz220)) ↑qz221) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 1160412547 30000000 0 1 Bool.false 633425721511 937500000 0 1 ep1053

noncomputable def ep1081 := @Enclosure.Complex.IsNear.im_isNear qz222 Bool.true 15414790088463955 1180591620717411303424 341379385553201 ep1006 Bool.false 70389460525188679 1180591620717411303424 1402232866253357 ep1006

noncomputable def ep1082 := nat_lit 81680813169990152653955413

noncomputable def ep1083 := nat_lit 35417748621522339102720000000

noncomputable def ep1084 := nat_lit 1627168611816168343670279

noncomputable def ep1085 := nat_lit 1952824906745178442718327201

noncomputable def ep1086 := nat_lit 221360928884514619392000000000

noncomputable def ep1087 := nat_lit 19658043963910744845509701

noncomputable def ep1088 := @Enclosure.Real.IsNear.addLit_ft_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz220)) ↑qz221) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)))) qz233) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz220)) ↑qz221) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)))) qz232) ep1082 ep1083 ep1084 ep999 ep1085 ep1086 ep1087

noncomputable def ep1089 := nat_lit 51083720973597018882520370934695702955836540190720000000

noncomputable def ep1090 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz220)) ↑qz221) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)))) qz233 1160412547 30000000 0 1 70389460525188679 1180591620717411303424 1402232866253357 ep1006 ep1082

noncomputable def ep1091 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz220)) ↑qz221) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)))) qz232 633425721511 937500000 0 1 15414790088463955 1180591620717411303424 341379385553201 ep1006 ep1085

noncomputable abbrev qz460 := (@ep1056 ep1006 (BSN.cpow_neg_s_sub_mk qz17 78672 1000 16 3 268435456 qz18 rfl EMRow21.d17) ep1078)

noncomputable def ep1092 := ep996 (@ep1003 ep1004 ep1005 ep987 ep988 ep989 ep990 (@ep1007 ep998 396140922283084976412947 ep999 ep1054 (ep1055 qz460) rfl) (@ep1079 ep1001 ep1002 ep1004 ep1080 (ep1081 qz460) rfl) rfl rfl) (@ep1088 ep1004 ep1089 ep992 ep993 ep994 ep990 (@ep1090 ep1083 ep1084 ep999 ep1054 (ep1081 qz460) rfl) (@ep1091 ep1086 ep1087 ep1004 ep1080 (ep1055 qz460) rfl) rfl rfl)

noncomputable def ep1093 := @Enclosure.Real.IsNear.mulLit_tt (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz220)) ↑qz221) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz222)) (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz220)) ↑qz221) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz222)) ep992 ep993 ep994 ep990 ep992 ep993 ep994

noncomputable def ep1094 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz220)) ↑qz221) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz222) Bool.true ep987 ep988 ep989 ep990 Bool.true ep992 ep993 ep994

noncomputable def ep1095 := @ep957 29299088240040791 31525197391593472 15490589449 31525197391593472 (@ep958 1 1835008 (ep959 (@ep960 524288 1 524288 (ep961 (@ep962 387595849 387595849 62500 0 1 (ep966 rfl) (ep969 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) (Enclosure.Real.IsNear.const Bool.false 2 7) rfl) (@ep970 179 8589934592 (BSN.norm_eq_sqrt_mul_add (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz220)) ↑qz221) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz222)) (@ep971 716 34359738368 709634377 17179869184 179 8589934592 (@ep976 709634019 709634735 17179869184 (@ep982 ep983 ep984 ep985 ep986 ep972 ep973 ep974 ep975 (@ep991 ep990 ep977 ep978 ep979 ep980 (@ep995 ep990 ep1092) (@ep995 ep990 ep1092) rfl) (@ep1093 ep990 ep981 ep983 ep984 ep985 (@ep1094 ep990 ep1092) (@ep1094 ep990 ep1092) rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl

theorem EMRow21.d18 : Enclosure.Real.IsNear (@HAdd.hAdd Real Real Real qz343 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz6 1 16))) (@HMul.hMul Real Real Real qz0 qz219 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz220)) ↑qz221) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz222)))) Bool.false 89773267516330501 94575592174780416 73028068323827 851180329573023744 := ep955 (ep956 ep1095) rfl rfl

theorem EMRow21.d19 : @Eq Nat (Nat.pow 17 (Nat.succ (Nat.mul 2 3))) 410338673 := @Eq.refl Nat 410338673

noncomputable abbrev qz500 := (@HAdd.hAdd Complex Complex Complex qz502 qz508 (@Nat.cast Complex Complex.instNatCast 3))

noncomputable abbrev qz461 := qz500

noncomputable abbrev qz242 := (@HDiv.hDiv Real Real Real qz269 (@Norm.norm Complex Complex.instNorm qz461) (@HAdd.hAdd Real Real Real qz343 (Complex.re qz392) qz289))

noncomputable abbrev qz462 := (@HPow.hPow Complex Complex Complex qz480 (@Nat.cast Complex Complex.instNatCast 17) (@HSub.hSub Complex Complex Complex qz487 qz495 qz482))

noncomputable abbrev qz243 := qz462

noncomputable def ep1096 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz142 1 17))) (@HMul.hMul Real Real Real qz0 qz242 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz220)) ↑qz221) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) qz243))) 4705887719 77309411328 22101685 231928233984 6703824426998367 7881299347898368 2213132639

noncomputable def ep1097 := nat_lit 555357229908548301218643968

noncomputable def ep1098 := @Enclosure.Real.IsNear.mulLit_ff (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz142 1 17)) 4427 294912 1 884736 1062997 262144 99 16384 4705887719 77309411328

noncomputable def ep1099 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (zetaApproximant qz142 1 17)) (Real.sqrt (@HAdd.hAdd Real Real Real qz343 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz142 1 17)) (Complex.re (zetaApproximant qz142 1 17))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz142 1 17)) (Complex.im (zetaApproximant qz142 1 17))))) Bool.false 1062997 262144 99 16384

noncomputable def ep1100 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz343 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz142 1 17)) (Complex.re (zetaApproximant qz142 1 17))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz142 1 17)) (Complex.im (zetaApproximant qz142 1 17))))) Bool.false 2125994 524288 3168 524288

noncomputable def ep1101 := nat_lit 340442799125510245063709631911342034781598021

noncomputable def ep1102 := nat_lit 20704207695330992789512302845623271424000000

noncomputable def ep1103 := nat_lit 214460268335295664064803238106183221595775986028935744829997

noncomputable def ep1104 := nat_lit 4377760475100415692680367400647012708845058250858561536000000

noncomputable def ep1105 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz343 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz142 1 17)) (Complex.re (zetaApproximant qz142 1 17))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz142 1 17)) (Complex.im (zetaApproximant qz142 1 17)))) ep1101 ep1102 ep1103 ep1104 1061413 1064581

noncomputable def ep1106 := nat_lit 249021082551201130510478043221796989223417761593539481

noncomputable def ep1107 := nat_lit 15147282199644852893624554643405365387422859264000000

noncomputable def ep1108 := nat_lit 10779646365420777888185953571414619960243954756097137780350347

noncomputable def ep1109 := nat_lit 223265784230121200326698737432997648151097970793786638336000000

noncomputable def ep1110 := nat_lit 4342324007848087261096385132411273110199095968121

noncomputable def ep1111 := nat_lit 1363255397968036760426209917906482884868057333760000

noncomputable def ep1112 := nat_lit 315654639358601958238023144001448682281241062757170411959

noncomputable def ep1113 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz142 1 17)) (Complex.re (zetaApproximant qz142 1 17))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz142 1 17)) (Complex.im (zetaApproximant qz142 1 17))) ep1106 ep1107 ep1108 ep1109 ep1110 ep1111 ep1112

noncomputable def ep1114 := nat_lit 446531568460242400653397474865995296302195941587573276672000

noncomputable def ep1115 := nat_lit 339545109402918199860270809263081784102524758506855324906480834434208573654857308877700786731677122560000

noncomputable def ep1116 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (zetaApproximant qz142 1 17)) (Complex.re (zetaApproximant qz142 1 17)) ep709 ep710 ep711 ep712 ep709 ep710 ep711 ep712 ep1106

noncomputable def ep1117 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (zetaApproximant qz142 1 17)) (Complex.im (zetaApproximant qz142 1 17)) ep829 ep830 ep831 ep832 ep829 ep830 ep831 ep832 ep1110

noncomputable def ep1118 := @ep1096 3940649673949184 ep1097 64652090648718679 70931694131085312 10198946778373 106397541196627968 (@ep1098 22101685 231928233984 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaStirlingErrorBound 1 2) (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 96 162) (@Inv.inv Real Real.instInv qz223)) Bool.false 4427 294912 1 884736 (BSN.theta_err_eq 1 2 96 162 EMRow21.d14 EMRow21.d15 rfl) (ep936 rfl)) (ep1099 (BSN.norm_eq_sqrt_mul_add (zetaApproximant qz142 1 17)) (@ep1100 1062997 262144 99 16384 (@ep1105 262144 (@ep1113 ep1114 ep1115 ep1101 ep1102 ep1103 ep1104 (@ep1116 ep1107 ep1108 ep1109 ep916 ep916 rfl) (@ep1117 ep1111 ep1112 ep1114 ep924 ep924 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl)

noncomputable abbrev qz244 := (@Norm.norm Complex Complex.instNorm qz461)

noncomputable def ep1119 := @Enclosure.Real.IsNear.of_eq (@HMul.hMul Real Real Real qz0 qz242 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz220)) ↑qz221) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) qz243))) (@HMul.hMul Real Real Real qz0 (@HMul.hMul Real Real Real qz0 qz244 qz445) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz220)) ↑qz221) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) qz243))) Bool.false 6703824426998367 7881299347898368 2213132639 3940649673949184 (BSN.zrb_shape_eq qz244 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz220)) ↑qz221) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) qz243)) qz151 3)

noncomputable def ep1120 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz0 qz244 qz445) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz220)) ↑qz221) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) qz243)) 42581859 1835008 1 1835008 157433813 4294967296 401 17179869184

noncomputable def ep1121 := @Enclosure.Real.IsNear.mulLit_ff qz244 qz445 42581859 524288 1 524288 2 7 0 1 42581859 1835008

noncomputable abbrev qz463 := (Complex.re qz500)

noncomputable abbrev qz464 := (Complex.im qz500)

noncomputable abbrev qz245 := (@HAdd.hAdd Real Real Real qz343 (@HMul.hMul Real Real Real qz266 qz463 qz463) (@HMul.hMul Real Real Real qz266 qz464 qz464))

noncomputable abbrev qz246 := qz461

noncomputable def ep1122 := @Enclosure.Real.IsNear.of_eq qz244 (Real.sqrt qz245) Bool.false 42581859 524288 1 524288 (BSN.norm_eq_sqrt_mul_add qz246)

noncomputable def ep1123 := @Enclosure.Real.IsNear.recentre' (Real.sqrt qz245) Bool.false 42581859 524288 1 524288 42581859

noncomputable def ep1124 := @Enclosure.Real.IsNear.sqrt_image qz245 6596436449 1000000 0 1 21290929 21290930 262144

noncomputable abbrev qz247 := (@HMul.hMul Real Real Real qz266 qz463 qz463)

noncomputable abbrev qz248 := (@HMul.hMul Real Real Real qz266 qz464 qz464)

noncomputable def ep1125 := @Enclosure.Real.IsNear.addLit_ff qz247 qz248 49 4 0 1 6584186449 1000000 0 1

noncomputable abbrev qz249 := qz463

noncomputable def ep1126 := @Enclosure.Real.IsNear.mulLit_ff qz249 qz249 7 2 0 1 7 2 0 1 49 4

noncomputable def ep1127 := @Enclosure.Complex.IsNear.of_eq qz246 (Complex.mk qz448 qz151) Bool.false 7 2 0 1 Bool.false 81143 1000 0 1 (BSN.s_add_nat_mk qz151 Bool.false 81143 1000 3 qz152)

noncomputable abbrev qz465 := (ep1127 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7 2) qz151 Bool.false 7 2 0 1 Bool.false 81143 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 7 2) qz153))

noncomputable def ep1128 := @ep1126 0 1 (@Enclosure.Complex.IsNear.re_isNear qz246 Bool.false 7 2 0 1 Bool.false 81143 1000 0 1 qz465)

noncomputable def ep1129 := ep1128 (@Enclosure.Complex.IsNear.re_isNear qz246 Bool.false 7 2 0 1 Bool.false 81143 1000 0 1 qz465)

noncomputable abbrev qz250 := qz464

noncomputable def ep1130 := @Enclosure.Real.IsNear.mulLit_ff qz250 qz250 81143 1000 0 1 81143 1000 0 1 6584186449 1000000

noncomputable def ep1131 := @ep1130 0 1 (@Enclosure.Complex.IsNear.im_isNear qz246 Bool.false 7 2 0 1 Bool.false 81143 1000 0 1 qz465)

noncomputable def ep1132 := ep1131 (@Enclosure.Complex.IsNear.im_isNear qz246 Bool.false 7 2 0 1 Bool.false 81143 1000 0 1 qz465)

noncomputable def ep1133 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz220)) ↑qz221) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) qz243)) (Real.sqrt (@HAdd.hAdd Real Real Real qz343 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz220)) ↑qz221) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) qz243)) (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz220)) ↑qz221) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) qz243))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz220)) ↑qz221) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) qz243)) (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz220)) ↑qz221) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) qz243))))) Bool.false 157433813 4294967296

noncomputable def ep1134 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz343 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz220)) ↑qz221) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) qz243)) (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz220)) ↑qz221) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) qz243))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz220)) ↑qz221) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) qz243)) (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz220)) ↑qz221) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) qz243))))) Bool.false 1259470504 34359738368

noncomputable def ep1135 := nat_lit 970824418686731714388548529363611370164148919393011024725574401

noncomputable def ep1136 := nat_lit 722544144432392189785757272033806912793765478400000000000000000000

noncomputable def ep1137 := nat_lit 20893591302104705061209059623098482860998981943254924474256060969640306829

noncomputable def ep1138 := nat_lit 12229168528569055079059548221751286475131863423759203603073466368000000000000000000

noncomputable def ep1139 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz343 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz220)) ↑qz221) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) qz243)) (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz220)) ↑qz221) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) qz243))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz220)) ↑qz221) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) qz243)) (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz220)) ↑qz221) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) qz243)))) ep1135 ep1136 ep1137 ep1138

noncomputable def ep1140 := nat_lit 201759076004609596955750699086575631701551879918669287647289

noncomputable def ep1141 := nat_lit 451590090270245118616098295021129320496103424000000000000000000

noncomputable def ep1142 := nat_lit 104466017689904898409663403551463378941993903402402260258450732203690893

noncomputable def ep1143 := nat_lit 191080758258891485610305440964863851173935365996237556298022912000000000000000000

noncomputable def ep1144 := nat_lit 648009897079356359259347410825090359441665911523140164489912001

noncomputable def ep1145 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz220)) ↑qz221) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) qz243)) (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz220)) ↑qz221) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) qz243))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz220)) ↑qz221) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) qz243)) (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz220)) ↑qz221) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) qz243))) ep1140 ep1141 ep1142 ep1143 ep1144

noncomputable def ep1146 := nat_lit 14207766169950791562990601795804826608711372125501179817715214108604089677

noncomputable def ep1147 := nat_lit 438414686871299416889979411651730905189133913744684531408499273968965285654928406013473639738643440702849024000000000000000000

noncomputable def ep1148 := nat_lit 449175996692398509732847570517

noncomputable def ep1149 := nat_lit 21250649172913403461632000000000

noncomputable def ep1150 := nat_lit 103212302599776552483471958506723

noncomputable def ep1151 := nat_lit 7980826153118307454948005117952000000000

noncomputable def ep1152 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz220)) ↑qz221) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) qz243)) (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz220)) ↑qz221) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) qz243)) ep1148 ep1149 ep1150 ep1151 ep1148 ep1149 ep1150

noncomputable def ep1153 := nat_lit 25456038518971414364010976174751

noncomputable def ep1154 := nat_lit 850025966916536138465280000000000

noncomputable def ep1155 := nat_lit 6192242417706367499942891634673053

noncomputable def ep1156 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz220)) ↑qz221) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) qz243) Bool.true ep1148 ep1149 ep1150 ep1151 Bool.true ep1153 ep1154 ep1155

noncomputable def ep1157 := nat_lit 319233046124732298197920204718080000000000

noncomputable def ep1158 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz220)) ↑qz221) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) qz243 Bool.true ep1148 ep1149 ep1150 ep1151 Bool.true ep1153 ep1154 ep1155 ep1157

noncomputable def ep1159 := nat_lit 975810482387128363246811771

noncomputable def ep1160 := nat_lit 566683977944357425643520000000

noncomputable def ep1161 := nat_lit 60361880268688155501720441849

noncomputable def ep1162 := nat_lit 58042372022678599672349128130560000000

noncomputable def ep1163 := nat_lit 825166207205762392222184258209

noncomputable def ep1164 := nat_lit 42501298345826806923264000000000

noncomputable def ep1165 := nat_lit 14601929855820297092613138115767

noncomputable abbrev qz251 := (Complex.re qz462)

noncomputable abbrev qz252 := (Complex.im qz462)

noncomputable def ep1166 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz220)) ↑qz221) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3)))) qz251) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz220)) ↑qz221) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3)))) qz252) ep1159 ep1160 ep1161 ep1162 ep1163 ep1164 ep1165

noncomputable def ep1167 := nat_lit 1227819408172047300761231556608000000000

noncomputable def ep1168 := nat_lit 509081681205539842123157959824006329406444214608199680000000

noncomputable def ep1169 := nat_lit 3990413076559153727474002558976

noncomputable def ep1170 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz220)) ↑qz221) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3)))) qz251 19751309347 480000000 0 1 49404850344027593 1180591620717411303424 100851139226841310611 ep1169 ep1159

noncomputable def ep1171 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz220)) ↑qz221)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz220)) ↑qz221)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3)))) 19751309347 480000000 0 1 0 1 0 1 19751309347

noncomputable def ep1172 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz220)) ↑qz221)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 59253928041 2000000 0 1 19751309347 480000000 0

noncomputable abbrev qz466 := (@HAdd.hAdd Complex Complex Complex qz479 qz494 qz483)

noncomputable abbrev qz253 := qz466

noncomputable def ep1173 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3)) (@HMul.hMul Complex Complex Complex qz45 (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 2)) qz253) Bool.true 59253928041 2000000 0 1 Bool.true 533794068781207 1000000000 0 1

noncomputable abbrev qz254 := (Complex.re qz466)

noncomputable abbrev qz255 := (Complex.im qz466)

noncomputable def ep1174 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 2))) qz254) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 2))) qz255) 6583436449 400000 0 1 6584186449 500000 0 1

noncomputable def ep1175 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 2))) qz254 6583436449 1000000 0 1 5 2 0 1 6583436449 400000

noncomputable abbrev qz467 := (@HAdd.hAdd Complex Complex Complex qz479 qz494 (@Nat.cast Complex Complex.instNatCast 1))

noncomputable abbrev qz256 := qz467

noncomputable def ep1176 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 2)) (@HMul.hMul Complex Complex Complex qz45 (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1)) qz256) Bool.true 6583436449 1000000 0 1 Bool.false 81143 500 0 1

noncomputable abbrev qz257 := (Complex.re qz467)

noncomputable abbrev qz258 := (Complex.im qz467)

noncomputable def ep1177 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1))) qz257) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1))) qz258) 3 4 0 1 6584186449 1000000 0 1

noncomputable def ep1178 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1))) qz257 1 2 0 1 3 2 0 1 3 4

noncomputable def ep1179 := @ep1178 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 81143 1000 0 1 ep879)

noncomputable def ep1180 := @Enclosure.Complex.IsNear.of_eq qz256 (Complex.mk qz452 qz151) Bool.false 3 2 0 1 Bool.false 81143 1000 0 1 (BSN.s_add_nat_mk qz151 Bool.false 81143 1000 1 qz152)

noncomputable abbrev qz468 := (ep1180 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 3 2) qz151 Bool.false 3 2 0 1 Bool.false 81143 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 3 2) qz153))

noncomputable def ep1181 := ep1179 (@Enclosure.Complex.IsNear.re_isNear qz256 Bool.false 3 2 0 1 Bool.false 81143 1000 0 1 qz468)

noncomputable def ep1182 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1))) qz258 81143 1000 0 1 81143 1000 0 1 6584186449 1000000

noncomputable def ep1183 := @ep1182 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 81143 1000 0 1 ep879)

noncomputable def ep1184 := ep1183 (@Enclosure.Complex.IsNear.im_isNear qz256 Bool.false 3 2 0 1 Bool.false 81143 1000 0 1 qz468)

noncomputable def ep1185 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1)) qz256 Bool.true 6583436449 1000000 0 1 Bool.false 81143 500 0 1 (@ep1177 26333745796 6583436449 1000000 0 1 (ep1181 rfl) (ep1184 rfl) rfl rfl)

noncomputable def ep1186 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1))) qz258) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1))) qz257) 81143 2000 0 1 243429 2000 0 1

noncomputable def ep1187 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1))) qz258 1 2 0 1 81143 1000 0 1 81143 2000

noncomputable def ep1188 := @ep1187 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 81143 1000 0 1 ep879)

noncomputable def ep1189 := ep1188 (@Enclosure.Complex.IsNear.im_isNear qz256 Bool.false 3 2 0 1 Bool.false 81143 1000 0 1 qz468)

noncomputable def ep1190 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1))) qz257 81143 1000 0 1 3 2 0 1 243429 2000

noncomputable def ep1191 := @ep1190 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 81143 1000 0 1 ep879)

noncomputable def ep1192 := ep1191 (@Enclosure.Complex.IsNear.re_isNear qz256 Bool.false 3 2 0 1 Bool.false 81143 1000 0 1 qz468)

noncomputable abbrev qz259 := (ep1176 (BSN.ascPochhammer_succ_eval_c 1 2 qz392 rfl) (ep1185 (@ep1186 649144000 81143 500 0 1 (ep1189 rfl) (ep1192 rfl) rfl rfl)))

noncomputable def ep1193 := @ep1175 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 6583436449 1000000 0 1 Bool.false 81143 500 0 1 qz259)

noncomputable def ep1194 := @Enclosure.Complex.IsNear.of_eq qz253 (Complex.mk qz454 qz151) Bool.false 5 2 0 1 Bool.false 81143 1000 0 1 (BSN.s_add_nat_mk qz151 Bool.false 81143 1000 2 qz152)

noncomputable abbrev qz469 := (ep1194 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 5 2) qz151 Bool.false 5 2 0 1 Bool.false 81143 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 5 2) qz153))

noncomputable def ep1195 := ep1193 (@Enclosure.Complex.IsNear.re_isNear qz253 Bool.false 5 2 0 1 Bool.false 81143 1000 0 1 qz469)

noncomputable def ep1196 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 2))) qz255 81143 500 0 1 81143 1000 0 1 6584186449 500000

noncomputable def ep1197 := @ep1196 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 6583436449 1000000 0 1 Bool.false 81143 500 0 1 qz259)

noncomputable def ep1198 := ep1197 (@Enclosure.Complex.IsNear.im_isNear qz253 Bool.false 5 2 0 1 Bool.false 81143 1000 0 1 qz469)

noncomputable def ep1199 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 2)) qz253 Bool.true 59253928041 2000000 0 1 Bool.true 533794068781207 1000000000 0 1 (@ep1174 5925392804100000 59253928041 2000000 0 1 (ep1195 rfl) (ep1198 rfl) rfl rfl)

noncomputable def ep1200 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 2))) qz255) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 2))) qz254) 534199783781207 1000000000 0 1 81143 200 0 1

noncomputable def ep1201 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 2))) qz255 6583436449 1000000 0 1 81143 1000 0 1 534199783781207 1000000000

noncomputable def ep1202 := @ep1201 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 6583436449 1000000 0 1 Bool.false 81143 500 0 1 qz259)

noncomputable def ep1203 := ep1202 (@Enclosure.Complex.IsNear.im_isNear qz253 Bool.false 5 2 0 1 Bool.false 81143 1000 0 1 qz469)

noncomputable def ep1204 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 2))) qz254 81143 500 0 1 5 2 0 1 81143 200

noncomputable def ep1205 := @ep1204 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 6583436449 1000000 0 1 Bool.false 81143 500 0 1 qz259)

noncomputable def ep1206 := ep1205 (@Enclosure.Complex.IsNear.re_isNear qz253 Bool.false 5 2 0 1 Bool.false 81143 1000 0 1 qz469)

noncomputable abbrev qz260 := (ep1173 (BSN.ascPochhammer_succ_eval_c 2 3 qz392 rfl) (ep1199 (@ep1200 106758813756241400 533794068781207 1000000000 0 1 (ep1203 rfl) (ep1206 rfl) rfl rfl)))

noncomputable def ep1207 := @ep1172 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz220)) ↑qz221) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1010) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 59253928041 2000000 0 1 Bool.true 533794068781207 1000000000 0 1 qz260)

noncomputable def ep1208 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz220)) ↑qz221)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 533794068781207 1000000000 0 1 0 1 0

noncomputable def ep1209 := @ep1208 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz220)) ↑qz221) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1010) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 59253928041 2000000 0 1 Bool.true 533794068781207 1000000000 0 1 qz260)

noncomputable def ep1210 := @Enclosure.Real.IsNear.addLit_ft_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz220)) ↑qz221)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz220)) ↑qz221)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3)))) 533794068781207 720000000000 0 1 0 1 0 1 533794068781207

noncomputable def ep1211 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz220)) ↑qz221)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 533794068781207 1000000000 0 1 533794068781207 720000000000 0

noncomputable def ep1212 := @ep1211 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz220)) ↑qz221) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1010) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 59253928041 2000000 0 1 Bool.true 533794068781207 1000000000 0 1 qz260)

noncomputable def ep1213 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz220)) ↑qz221)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 59253928041 2000000 0 1 0 1 0

noncomputable def ep1214 := @ep1213 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz220)) ↑qz221) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1010) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 59253928041 2000000 0 1 Bool.true 533794068781207 1000000000 0 1 qz260)

noncomputable def ep1215 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz220)) ↑qz221) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.false 19751309347 480000000 0 1 Bool.false 533794068781207 720000000000 0 1 (@ep1171 19751309347 480000000 0 1 (ep1207 rfl) (ep1209 rfl) rfl rfl) (@ep1210 533794068781207 720000000000 0 1 (ep1212 rfl) (ep1214 rfl) rfl rfl)

noncomputable def ep1216 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz220)) ↑qz221) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 19751309347 480000000 0 1 Bool.false 533794068781207 720000000000 0 1 ep1215

noncomputable def ep1217 := nat_lit 997603269139788431868500639744

noncomputable def ep1218 := @Enclosure.Complex.IsNear.re_isNear qz243 Bool.true 49404850344027593 1180591620717411303424 100851139226841310611 ep1169 Bool.false 7729256050838435 295147905179352825856 16002667442818937385 ep1217

noncomputable abbrev qz470 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 410338673)))

noncomputable def ep1219 := @Enclosure.Complex.IsNear.of_eq qz243 (Complex.mk (@HMul.hMul Real Real Real qz0 qz470 qz212) (@HMul.hMul Real Real Real qz0 qz470 qz435)) Bool.true 49404850344027593 1180591620717411303424 100851139226841310611 ep1169 Bool.false 7729256050838435 295147905179352825856 16002667442818937385

noncomputable abbrev qz471 := (Real.sqrt (@Nat.cast Real Real.instNatCast 410338673))

noncomputable abbrev qz472 := (@Nat.cast Real Real.instNatCast 410338673)

noncomputable def ep1220 := @Enclosure.Real.IsNear.inv_image qz471 696018964540551 34359738368 1 34359738368 848103 848104 17179869184 (@Enclosure.Real.IsNear.of_eq qz471 (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz472 qz19)) Bool.false 696018964540551 34359738368 1 34359738368 (BSN.sqrt_natCast_div_one 410338673) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz472 qz19)) Bool.false 696018964540551 34359738368 1 34359738368 696018964540551 34359738368 1 34359738368 (BSN.sqrt_enclosure 410338673 1 348009482270275 348009482270276 17179869184 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep1221 := nat_lit 845002837250000000000000000

noncomputable def ep1222 := nat_lit 1753674119217514004137115648

noncomputable def ep1223 := nat_lit 6760022698000000000000000

noncomputable def ep1224 := BSN.log_dyadic_bound 1 33 4 3 135604136745 17179869184 6760022698 41530119 15 1041523072 34 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 1) (BSN.artanhQ 33) 0 3 41530119 135604136745 15 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep1225 := @Enclosure.Real.IsNear.mulLit_ff qz151 qz214 81143 1000 0 1 3189914640129271 1125899906842624 125003380011349 845002837250000000000000 258839243644009436753 1125899906842624000 10143149264260891907 ep1221 qz153 (BSN.isNear_log_sfrac 17 1 3189914640129271 1125899906842624 125003380011349 845002837250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz437) Bool.false ep1222 ep1059 1000027040090792 ep1223 3189914640129271 1125899906842624 125003380011349 845002837250000000000000 (BSN.log_rat_reduce_isNear 17 1 4 34 32 1041523072 17179869184 24973259072661432 36028797018963968 6760022698 1000000000000000 rfl rfl rfl rfl (ep1224 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1226 := nat_lit 2768859208140172035172073472

noncomputable def ep1227 := nat_lit 98750214046310333367217066129620265070217195055930585168402048422089341391038098269721784217540411100505305872641

noncomputable def ep1228 := nat_lit 24241468655984884671616987561611793649609605215227765039851000824877738980510979184756823965407711771199390267473920

noncomputable def ep1229 := nat_lit 5746039153218441830169414726048440169668075321244721440459393219901390783595554912870078577622842187937839361

noncomputable def ep1230 := nat_lit 296239150060624563217990859559408698330312249017149266062325226479828221391547103699339612495465987617140041939201

noncomputable def ep1231 := nat_lit 1090866089519319810222764440272530714232432234685249426793295037119498254122994063314057078443347029703972562036326400

noncomputable def ep1232 := BSN.cos_dyadic_bound_f 39347855933729 70368744177664 3 2 34359738368 13533248566 ep1227 ep1228 ep1229 ep1230 ep1231 ep1229 29126663399 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 39347855933729) (BSN.cosEvenQ 70368744177664) 0 2 ep1227 ep1228 ep1229 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 39347855933729) (BSN.cosOddQ 70368744177664) 0 2 ep1230 ep1231 ep1229 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz473 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 7899146839721) (@Nat.cast Real Real.instNatCast 34359738368))

noncomputable def ep1233 := @Enclosure.Real.IsNear.cos_image qz215 qz473 Bool.false 7899146839721 34359738368 207 17179869184 Bool.true 29126663399 34359738368 1 6760022698 (@Enclosure.Real.IsNear.recentre' qz215 Bool.false 258839243644009436753 1125899906842624000 10143149264260891907 ep1221 7899146839721 34359738368 207 17179869184 (ep1225 rfl) rfl) (Enclosure.sfrac_false_div 7899146839721 34359738368) (BSN.cos_reduce2 qz473 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast ep1226) (@Nat.cast Real Real.instNatCast ep1064)) 226375608064910080 72057594037927936 Bool.false 29126663399 34359738368 36 1000000000000000 13520045396 6760022698 (BSN.sin_reduce_arg_pos_rat_q2 7899146839721 34359738368 226375608064910080 72057594037927936 36 ep1226 ep1064 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 29126663399 34359738368 ep1226 ep1064 39347855933729 70368744177664 13533248566 13520045396 (ep1232 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1234 := nat_lit 177745788452036025307526583501535638374255216640418057525971319645184893391241700441568915528710641707159200299265

noncomputable def ep1235 := nat_lit 218173217903863962044552888054506142846486446937049885358659007423899650824598812662811415688669405940794512407265280

noncomputable def ep1236 := nat_lit 465515380930036760232939825356370212553250866698193849685687950529318689963411965496154893876545053202826958567681

noncomputable def ep1237 := nat_lit 3999842328237505970816802947665945952185584860512581231575415136104826931784311565484875954292272442247899394133196800

noncomputable def ep1238 := BSN.sin_dyadic_bound_f 39347855933729 70368744177664 3 2 34359738368 13533248566 ep1234 ep1235 ep1229 ep1236 ep1237 ep1229 18227152820 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 39347855933729) (BSN.sinEvenQ 70368744177664) 0 2 ep1234 ep1235 ep1229 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 39347855933729) (BSN.sinOddQ 70368744177664) 0 2 ep1236 ep1237 ep1229 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1239 := @Enclosure.Real.IsNear.sin_image qz215 qz473 Bool.false 7899146839721 34359738368 207 17179869184 Bool.true 18227152820 34359738368 1 6760022698 (@Enclosure.Real.IsNear.recentre' qz215 Bool.false 258839243644009436753 1125899906842624000 10143149264260891907 ep1221 7899146839721 34359738368 207 17179869184 (ep1225 rfl) rfl) (Enclosure.sfrac_false_div 7899146839721 34359738368) (BSN.sin_reduce2 qz473 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast ep1226) (@Nat.cast Real Real.instNatCast ep1064)) 226375608064910080 72057594037927936 Bool.false 18227152820 34359738368 36 1000000000000000 13520045396 6760022698 (BSN.sin_reduce_arg_pos_rat_q2 7899146839721 34359738368 226375608064910080 72057594037927936 36 ep1226 ep1064 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 18227152820 34359738368 ep1226 ep1064 39347855933729 70368744177664 13533248566 13520045396 (ep1238 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1240 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz470 qz212) (@HMul.hMul Real Real Real qz0 qz470 qz435) Bool.true 49404850344027593 1180591620717411303424 100851139226841310611 ep1169 Bool.false 7729256050838435 295147905179352825856 16002667442818937385 ep1217 (@Enclosure.Real.IsNear.mulLit_ft qz470 qz212 1696207 34359738368 1 34359738368 29126663399 34359738368 708252283835 58068152816255369216 49404850344027593 1180591620717411303424 100851139226841310611 ep1169 (@Enclosure.Real.IsNear.recentre' qz470 Bool.false 1696207 34359738368 1 34359738368 1696207 34359738368 1 34359738368 (ep1220 rfl rfl) rfl) (@Enclosure.Real.IsNear.recentre' qz212 Bool.true 29126663399 34359738368 1416504567670 116136305632510738432 29126663399 34359738368 708252283835 58068152816255369216 (ep1233 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz470 qz435 1696207 34359738368 1 34359738368 4556788205 8589934592 708252283835 58068152816255369216 7729256050838435 295147905179352825856 16002667442818937385 ep1217 (@Enclosure.Real.IsNear.recentre' qz470 Bool.false 1696207 34359738368 1 34359738368 1696207 34359738368 1 34359738368 (ep1220 rfl rfl) rfl) (@Enclosure.Real.IsNear.neg qz213 Bool.true 4556788205 8589934592 708252283835 58068152816255369216 (@Enclosure.Real.IsNear.recentre' qz213 Bool.true 18227152820 34359738368 1416504567670 116136305632510738432 4556788205 8589934592 708252283835 58068152816255369216 (ep1239 rfl rfl) rfl)) rfl)

noncomputable def ep1241 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz220)) ↑qz221) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3)))) qz252 533794068781207 720000000000 0 1 7729256050838435 295147905179352825856 16002667442818937385 ep1217 ep1163

noncomputable def ep1242 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz220)) ↑qz221) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 19751309347 480000000 0 1 Bool.false 533794068781207 720000000000 0 1 ep1215

noncomputable def ep1243 := @Enclosure.Complex.IsNear.im_isNear qz243 Bool.true 49404850344027593 1180591620717411303424 100851139226841310611 ep1169 Bool.false 7729256050838435 295147905179352825856 16002667442818937385 ep1217

noncomputable def ep1244 := nat_lit 30532585456456297680470389

noncomputable def ep1245 := nat_lit 28334198897217871282176000000

noncomputable def ep1246 := nat_lit 1915597788122922824248231743

noncomputable def ep1247 := nat_lit 2902118601133929983617456406528000000

noncomputable def ep1248 := nat_lit 26372016082665103294425087844751

noncomputable def ep1249 := nat_lit 460117435462526614559660472534081

noncomputable def ep1250 := @Enclosure.Real.IsNear.addLit_ft_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz220)) ↑qz221) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3)))) qz252) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz220)) ↑qz221) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3)))) qz251) ep1244 ep1245 ep1246 ep1247 ep1248 ep1154 ep1249

noncomputable def ep1251 := nat_lit 24556388163440946015224631132160000000000

noncomputable def ep1252 := nat_lit 721276458531775502198539703774702318418977388207538176000000

noncomputable def ep1253 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz220)) ↑qz221) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3)))) qz252 19751309347 480000000 0 1 7729256050838435 295147905179352825856 16002667442818937385 ep1217 ep1244

noncomputable def ep1254 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz220)) ↑qz221) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3)))) qz251 533794068781207 720000000000 0 1 49404850344027593 1180591620717411303424 100851139226841310611 ep1169 ep1248

noncomputable abbrev qz474 := (@ep1219 ep1217 (BSN.cpow_neg_s_sub_mk qz151 81143 1000 17 3 410338673 qz152 rfl EMRow21.d19) ep1240)

noncomputable def ep1255 := ep1158 (@ep1166 ep1167 ep1168 ep1148 ep1149 ep1150 ep1151 (@ep1170 ep1160 ep1161 ep1162 ep1216 (ep1218 qz474) rfl) (@ep1241 ep1164 ep1165 ep1167 ep1242 (ep1243 qz474) rfl) rfl rfl) (@ep1250 ep1251 ep1252 ep1153 ep1154 ep1155 ep1157 (@ep1253 ep1245 ep1246 ep1247 ep1216 (ep1243 qz474) rfl) (@ep1254 ep1154 ep1249 ep1251 ep1242 (ep1218 qz474) rfl) rfl rfl)

noncomputable def ep1256 := @Enclosure.Real.IsNear.mulLit_tt (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz220)) ↑qz221) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) qz243)) (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz220)) ↑qz221) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) qz243)) ep1153 ep1154 ep1155 ep1157 ep1153 ep1154 ep1155

noncomputable def ep1257 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz220)) ↑qz221) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) qz243) Bool.true ep1148 ep1149 ep1150 ep1151 Bool.true ep1153 ep1154 ep1155

noncomputable def ep1258 := @ep1120 6703824426998367 7881299347898368 2213132639 3940649673949184 (@ep1121 1 1835008 (ep1122 (@ep1123 524288 1 524288 (ep1124 (@ep1125 26385745796 6596436449 1000000 0 1 (ep1129 rfl) (ep1132 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) (Enclosure.Real.IsNear.const Bool.false 2 7) rfl) (@ep1133 401 17179869184 (BSN.norm_eq_sqrt_mul_add (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz220)) ↑qz221) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) qz243)) (@ep1134 802 34359738368 157433813 4294967296 401 17179869184 (@ep1139 629734851 629735653 17179869184 (@ep1145 ep1136 ep1146 ep1138 ep1147 ep1135 ep1136 ep1137 ep1138 (@ep1152 ep1151 ep1140 ep1141 ep1142 ep1143 (@ep1156 ep1157 ep1255) (@ep1156 ep1157 ep1255) rfl) (@ep1256 ep1157 ep1144 ep1136 ep1146 ep1138 (@ep1257 ep1157 ep1255) (@ep1257 ep1157 ep1255) rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl

theorem EMRow21.d20 : Enclosure.Real.IsNear (@HAdd.hAdd Real Real Real qz343 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz142 1 17))) (@HMul.hMul Real Real Real qz0 qz242 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz220)) ↑qz221) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) qz243)))) Bool.false 64652090648718679 70931694131085312 10198946778373 106397541196627968 := ep1118 (ep1119 ep1258) rfl rfl

noncomputable def EMRow21.d21 := fun (I J : @NonemptyInterval Real Real.instLE) => @LE.le Real Real.instLE (@Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE I)) (@Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE J))

noncomputable abbrev qz475 := (EMRow21.d3 qz484 qz496 (@Enclosure.dec_le_dec qz484 qz496 78672 1000 81143 1000 (@Eq.refl Real qz484) (@Eq.refl Real qz496) rfl rfl rfl) 16 17 1 1)

noncomputable abbrev qz261 := qz475

noncomputable def ep1259 := @Zeta.Certificates.ZIntervalEM.Certificate.mk qz261 (@Enclosure.dec_nonneg qz17 78672 1000 qz18) (@Enclosure.pos_of_ble 1 rfl) (@Enclosure.pos_of_ble 16 rfl)

noncomputable abbrev qz262 := (Zeta.Certificates.ZIntervalEM.fstVal qz475)

noncomputable def ep1260 := @Enclosure.Real.IsNear.neg_val qz262 ep153 ep154

noncomputable def ep1261 := @Enclosure.Real.IsNear.of_eq qz262 (hardyZApproximantEM 1 16 qz17) Bool.true

noncomputable abbrev qz263 := (Zeta.Certificates.ZIntervalEM.sndVal qz475)

noncomputable def ep1262 := BSN.mul_neg_of_neg_pos_r qz262 qz263 (@ep1260 ep155 ep156 (@ep1261 ep153 ep154 ep155 ep156 (@Eq.refl Real (hardyZApproximantEM 1 16 qz17)) EMRow21.d9) rfl rfl rfl)

noncomputable def ep1263 := @Enclosure.Real.IsNear.pos_val qz263 ep692 ep693

noncomputable def ep1264 := @Enclosure.Real.IsNear.of_eq qz263 (hardyZApproximantEM 1 17 qz151) Bool.false

noncomputable def ep1265 := BSN.gt_trans_le (@Norm.norm Real Real.norm qz262) (BSN.hardyZErrorBoundStrong 1 16 qz17)

noncomputable def ep1266 := @Enclosure.norm_gt_of_isNear qz262 (BSN.hardyZErrorBoundStrong 1 16 qz17) Bool.true

noncomputable def ep1267 := @Enclosure.Real.IsNear.of_eq (BSN.hardyZErrorBoundStrong 1 16 qz17) (@HAdd.hAdd Real Real Real qz343 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz6 1 16))) (@HMul.hMul Real Real Real qz0 qz219 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz220)) ↑qz221) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz222)))) Bool.false 89773267516330501 94575592174780416 73028068323827 851180329573023744 (@Eq.refl Real (@HAdd.hAdd Real Real Real qz343 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz6 1 16))) (@HMul.hMul Real Real Real qz0 qz219 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz220)) ↑qz221) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz222)))))

noncomputable def ep1268 := BSN.gt_trans_le (@Norm.norm Real Real.norm qz263) (BSN.hardyZErrorBoundStrong 1 17 qz151)

noncomputable def ep1269 := @Enclosure.norm_gt_of_isNear qz263 (BSN.hardyZErrorBoundStrong 1 17 qz151) Bool.false

noncomputable def ep1270 := @Enclosure.Real.IsNear.of_eq (BSN.hardyZErrorBoundStrong 1 17 qz151) (@HAdd.hAdd Real Real Real qz343 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz142 1 17))) (@HMul.hMul Real Real Real qz0 qz242 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz220)) ↑qz221) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) qz243)))) Bool.false 64652090648718679 70931694131085312 10198946778373 106397541196627968 (@Eq.refl Real (@HAdd.hAdd Real Real Real qz343 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz142 1 17))) (@HMul.hMul Real Real Real qz0 qz242 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz52 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz220)) ↑qz221) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) qz243)))))

noncomputable def ep1271 := @List.cons EMRow21.d0 (@PSigma.mk Zeta.Certificates.ZIntervalEM Zeta.Certificates.ZIntervalEM.Certificate qz261 (ep1259 (@Enclosure.pos_of_ble 1 rfl) (@Enclosure.pos_of_ble 17 rfl) (ep1262 (@ep1263 ep694 ep695 (@ep1264 ep692 ep693 ep694 ep695 (@Eq.refl Real (hardyZApproximantEM 1 17 qz151)) EMRow21.d13) rfl rfl rfl)) (ep1265 (hardyZErrorBoundEM 1 16 qz17) (BSN.hardyZErrorBoundEM_le_strong 1 16 qz17 rfl) (@ep1266 Bool.false ep153 ep154 ep155 ep156 89773267516330501 94575592174780416 73028068323827 851180329573023744 (@ep1261 ep153 ep154 ep155 ep156 (@Eq.refl Real (hardyZApproximantEM 1 16 qz17)) EMRow21.d9) (ep1267 EMRow21.d18) rfl rfl rfl rfl rfl)) (ep1268 (hardyZErrorBoundEM 1 17 qz151) (BSN.hardyZErrorBoundEM_le_strong 1 17 qz151 rfl) (@ep1269 Bool.false ep692 ep693 ep694 ep695 64652090648718679 70931694131085312 10198946778373 106397541196627968 (@ep1264 ep692 ep693 ep694 ep695 (@Eq.refl Real (hardyZApproximantEM 1 17 qz151)) EMRow21.d13) (ep1270 EMRow21.d20) rfl rfl rfl rfl rfl)))) (@List.nil EMRow21.d0)

noncomputable abbrev qz476 := (@Enclosure.dec_le_dec qz484 qz496 78672 1000 81143 1000 (@Eq.refl Real qz484) (@Eq.refl Real qz496) rfl rfl rfl)

noncomputable abbrev qz264 := (Zeta.Certificates.CertifiedZeroIntervals.intervals (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedEM ep1271 (@List.IsChain.singleton EMRow21.d1 EMRow21.d21 (EMRow21.d2 qz279 qz394 qz476))))

noncomputable abbrev qz477 := (@NonemptyInterval Real Real.instLE)

noncomputable def ep1272 := And (@Eq (Option Real) (@Option.map qz477 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz477 qz264)) (@Option.some Real qz17))

noncomputable def ep1273 := ep1272 (@Eq (Option Real) (@Option.map qz477 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz477 qz264)) (@Option.some Real qz151))

noncomputable def ep1274 := @And.intro (@Eq Nat (@List.length qz477 qz264) 1) ep1273

noncomputable def ep1275 := @And.intro (@Eq (Option Real) (@Option.map qz477 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz477 qz264)) (@Option.some Real qz17))

noncomputable def ep1276 := @ep1275 (@Eq (Option Real) (@Option.map qz477 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz477 qz264)) (@Option.some Real qz151))

noncomputable abbrev qz265 := (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedEM ep1271 (@List.IsChain.singleton EMRow21.d1 EMRow21.d21 (EMRow21.d2 qz279 qz394 qz476)))

theorem EMRow21.d22 : Zeta.Certificates.BatchSpec 1 78672 1000 81143 1000 := @Exists.intro Zeta.Certificates.CertifiedZeroIntervals (fun (C : Zeta.Certificates.CertifiedZeroIntervals) => And (@Eq Nat (@List.length qz477 (Zeta.Certificates.CertifiedZeroIntervals.intervals C)) 1) (And (@Eq (Option Real) (@Option.map qz477 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz477 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz17)) (@Eq (Option Real) (@Option.map qz477 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz477 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz151)))) qz265 (ep1274 (@Eq.refl Nat 1) (ep1276 (@Eq.refl (Option Real) (@Option.some Real qz17)) (@Eq.refl (Option Real) (@Option.some Real qz151))))

theorem solution : Zeta.Certificates.BatchSpec 1 78672 1000 81143 1000 := EMRow21.d22
#print axioms solution
#check solution
