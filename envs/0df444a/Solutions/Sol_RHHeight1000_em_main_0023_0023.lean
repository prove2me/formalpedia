-- Prove2me | solution 1 for RHHeight1000.em_main_0023_0023
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-20T08:22:32.496391+00:00
-- url     : https://prove2.me/submissions/8d97ed2f-ff74-4c80-9aca-fabe70969793

import Definitions.Def_RHT1000_Support_20261118_S005
/- Copyright (c) 2026 Salvatore Mercuri, Bhavik Mehta.
Apache 2.0 license; see the source project LICENSE. -/
set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable def EMRow23.d0 := @PSigma Zeta.Certificates.ZIntervalEM fun (I : Zeta.Certificates.ZIntervalEM) => Zeta.Certificates.ZIntervalEM.Certificate I

noncomputable def EMRow23.d1 := @NonemptyInterval Real Real.instLE

noncomputable def EMRow23.d2 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @NonemptyInterval.mk Real Real.instLE (@Prod.mk Real Real a b) h

noncomputable def EMRow23.d3 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) (fc sc fb sb : Nat) => Zeta.Certificates.ZIntervalEM.mk (EMRow23.d2 a b h) fc sc fb sb

noncomputable def ep0 := nat_lit 26986075409044028275299783

noncomputable def ep1 := nat_lit 4294967296000000000000000

noncomputable def ep2 := nat_lit 26986075409044045455168967

noncomputable abbrev qz266 := (@instHMul Real Real.instMul)

noncomputable abbrev qz0 := qz266

noncomputable abbrev qz267 := (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 2 1) Real.pi)

noncomputable def ep3 := @BSN.isNear_log_image_fff qz267 884279719003555 140737488355328 1 500000000000000 ep0 ep1 ep2 ep1 4138529546116343 2251799813685248 5000000001657 828500000000000000 4138529546116343 2251799813685248 5000000001657 828500000000000000 481788 262144

noncomputable abbrev qz268 := (@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 2 1) Real.pi 2 1 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 140737488355328 1 500000000000000 (Enclosure.Real.IsNear.const Bool.false 2 1) BSN.pi_near_15 rfl)

noncomputable def ep4 := @ep3 2 262144 qz268 rfl rfl rfl rfl

noncomputable def ep5 := nat_lit 53972150818088056550599566

noncomputable def ep6 := nat_lit 34359738368000000000000000

noncomputable def ep7 := nat_lit 9806206225044028275299783

noncomputable def ep8 := nat_lit 44165944593044028275299783

noncomputable def ep9 := nat_lit 13681445815609410487519367394620474863599256634174726093703677122907123617368241606644861540940610176751640793056574796245399519365549113997355475306157239709119582688278313060810592403844863400465080549957745

noncomputable def ep10 := nat_lit 231714499556395493334623298703961145503103241611736774613091488581016477543539392410113701224645713379230392133956226737605624599560350113120270717249177907454870984269546186598262646369758174842349131395304

noncomputable def ep11 := nat_lit 8978369550011295664474073352761810093897501552430546263638635096022803738134167562509900960712119243631997923545019968443113540909076206607473711060286601587364321108377403290080403445693385008949995305

noncomputable def ep12 := BSN.log_dyadic_bound ep7 ep8 5 4 ep9 524288 165700 ep10 ep11 236759 ep5 ep6 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP ep7) (BSN.artanhQ ep8) 0 4 ep10 ep9 ep11 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz269 := (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))

noncomputable abbrev qz1 := qz269

noncomputable def ep13 := ep4 rfl rfl rfl rfl (BSN.isNear_log_sfrac ep0 ep1 4138529546116343 2251799813685248 5000000001657 828500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep0) (@Nat.cast Real Real.instNatCast ep1))) Bool.false 34716502058787923820544 18889465931478580854784 1000000000331400 165700000000000000000 4138529546116343 2251799813685248 5000000001657 828500000000000000 (BSN.log_rat_reduce_isNear ep0 ep1 2 ep5 ep6 236759 524288 24973259072661432 36028797018963968 165700 1000000000000000 rfl rfl rfl rfl (ep12 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep14 := nat_lit 53972150818088090910337934

noncomputable def ep15 := nat_lit 9806206225044045455168967

noncomputable def ep16 := nat_lit 44165944593044045455168967

noncomputable def ep17 := nat_lit 13681445815609453062485491347592146866046743284321690683909457683007658987562290830600045658905080811372395010565947827677605470036294121079488508864180301737865471494204890974265645509835068840465080549957745

noncomputable def ep18 := nat_lit 231714499556396865510889920206523150079811393376960301632499817942333196803513131357563499488546302200815366867712007119763002650772307103678175657719139104636874731038771518520299266622696414842349131395304

noncomputable def ep19 := nat_lit 8978369550011421500876706511871067098718760264493934208903156435737864998391937547068187824077011975074541700434630537294838404525415248443919841847024664017658842168336182958576672102333385008949995305

noncomputable def ep20 := BSN.log_dyadic_bound ep15 ep16 5 4 ep17 524288 165700 ep18 ep19 236759 ep14 ep6 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP ep15) (BSN.artanhQ ep16) 0 4 ep18 ep17 ep19 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep21 := ep13 (BSN.isNear_log_sfrac ep2 ep1 4138529546116343 2251799813685248 5000000001657 828500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep2) (@Nat.cast Real Real.instNatCast ep1))) Bool.false 34716502058787923820544 18889465931478580854784 1000000000331400 165700000000000000000 4138529546116343 2251799813685248 5000000001657 828500000000000000 (BSN.log_rat_reduce_isNear ep2 ep1 2 ep14 ep6 236759 524288 24973259072661432 36028797018963968 165700 1000000000000000 rfl rfl rfl rfl (ep20 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable abbrev qz270 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)

noncomputable abbrev qz2 := (Real.log qz270)

theorem EMRow23.d4 : Enclosure.Real.IsNear qz2 Bool.false 120447 65536 1 131072 := @Enclosure.Real.IsNear.of_eq qz2 (Real.log qz267) Bool.false 120447 65536 1 131072 BSN.log_two_pi_eq (@Enclosure.Real.IsNear.recentre' (Real.log qz267) Bool.false 481788 262144 2 262144 120447 65536 1 131072 (ep21 rfl rfl rfl rfl rfl rfl rfl rfl) rfl)

noncomputable def ep22 := nat_lit 8589934592000000000000000

noncomputable def ep23 := @BSN.isNear_log_image_fff Real.pi 226375608064910080 72057594037927936 1 1000000000000000 ep0 ep22 ep2 ep22 600168 524288 1 165700 600168 524288 1 165700 300084 262144 2 262144 BSN.pi_near_15 rfl rfl rfl

noncomputable def ep24 := nat_lit 17179869184000000000000000

noncomputable def ep25 := nat_lit 18396140817044028275299783

noncomputable def ep26 := nat_lit 35576010001044028275299783

noncomputable def ep27 := nat_lit 145019262663961446558303139663424756232419223153299357158415217874016130572233056993847515999529612750616182853355499335896178729185698845314776375864537073527142908641610750276034469165612529925303649396973267518946591078603565291376312767403717761600170009932259137778521478520425507632472584532570900560707662248426541531715360699177249902784721815296292248142738824858695953661559845440650653128788875447728828657762006237171740033404723254477174341920697506370253193455781322964835857351124092897592956162654178130575

noncomputable def ep28 := nat_lit 15500762873619990602332184736899274490522931101512051618692838888825382235673431503644115344741331161500627469184702974962114537943617674254904297224139410345221262767191485292268260077615645253784097850065864022184521411511133693085443040736512010941548648374196772723338837137976260321103066698629790037694560548409922339907589559883712609967105556007429010014773911317423638534096849366294542840133852248768895750397896505791271178551667935288585787166713880920071720072716082683081155281219708172458141800988558163320

noncomputable def ep29 := nat_lit 12900190794487083783367107939442176642390171280542213571554777169279725287102813254708993369099729304728646904879886535518616983985412662170766446331701281703998252143668221340329975389245922410714088123244705567402747658401492589451585970559635763980329972215329212888079422466283203384882259392047898400615815810081169907384366653346471604103896809335921621947903075223769953790093549808584241881353287841076643853121427928248525828402335494512605306631304432120211393210317325496757155861061354331245840675149075

noncomputable def ep30 := BSN.log_dyadic_bound ep25 ep26 11 10 ep27 524288 165700 ep28 ep29 600168 ep5 ep24 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base10 (BSN.artanhP ep25) (BSN.artanhQ ep26) 0 10 ep28 ep27 ep29 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep31 := nat_lit 18396140817044045455168967

noncomputable def ep32 := nat_lit 35576010001044045455168967

noncomputable def ep33 := nat_lit 145019262663962847171784895425483977818796535899227200426399035286881207006285364467913811844950531107314785650583974625982406238691319033447632878979985852280879486690814033867010958364699188952871572448188560932645032521756218245629809291975913196623825614492380080480004685076434733043183791438169545293975334857826316990371107134320667652578346815517853870648072772035977941843998949310557583393428557296298890786965786350523173236912472938174255438182435383147950274229549088258679583524155427309880956162654178130575

noncomputable def ep34 := nat_lit 15500762873620157189619721156942591192100275120160672416764593300158228469749443299607348495591439275767946573253526107895503597951484257520435868240203420954375895980141891044871083424251900562230440202302413072793440172565998181227591194192658878334739610458454844032013325963992941389843551995646587189684848765634635122388286241104146031552341815777883628509454807838726994150833304950745987647656768534710890974432620160470644835720379148964170536679305861738540146791997074363921127776563807649880221800988558163320

noncomputable def ep35 := nat_lit 12900190794487324729109480814509220959173684627296055849229843377126536688487849343376525559792931631054411655715865486295286288812423905434305314401904993536755333953308594664509631000767632482919425633906965368325056855874260596615770736441041599390097968820060635361729170158825410327022636428624381203910573184452046894301676992229743752846881064485858738985580654099214803581683226335297196686880535448467637789069028262446657986458573827723305156755787640135484017403116612632808333639900906331245840675149075

noncomputable def ep36 := BSN.log_dyadic_bound ep31 ep32 11 10 ep33 524288 165700 ep34 ep35 600168 ep14 ep24 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base10 (BSN.artanhP ep31) (BSN.artanhQ ep32) 0 10 ep34 ep33 ep35 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep37 := @Enclosure.Real.IsNear.recentre' (Real.log Real.pi) Bool.false 300084 262144 2 262144 75021 65536 1 131072 (ep23 rfl rfl rfl rfl rfl (BSN.isNear_log_sfrac ep0 ep22 600168 524288 1 165700 Bool.false (BSN.logfrac_isNear ep5 ep24 1 ep0 ep22 600168 524288 165700 rfl rfl rfl (ep30 rfl))) (BSN.isNear_log_sfrac ep2 ep22 600168 524288 1 165700 Bool.false (BSN.logfrac_isNear ep14 ep24 1 ep2 ep22 600168 524288 165700 rfl rfl rfl (ep36 rfl))) rfl rfl rfl rfl rfl rfl rfl rfl) rfl

theorem EMRow23.d5 : Enclosure.Real.IsNear (Real.log Real.pi) Bool.false 75021 65536 1 131072 := ep37

noncomputable abbrev qz514 := (@HAdd.hAdd Complex Complex Complex (@instHAdd Complex Complex.instAdd) (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (2 : Complex)) (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul) Complex.I ↑(Enclosure.sfrac Bool.false 83585 1000)))

noncomputable abbrev qz488 := qz514

noncomputable abbrev qz271 := qz488

noncomputable abbrev qz3 := (BSN.headSumC qz271 9)

noncomputable abbrev qz515 := (@instHAdd Complex Complex.instAdd)

noncomputable abbrev qz489 := qz515

noncomputable abbrev qz272 := qz489

noncomputable abbrev qz4 := qz272

noncomputable abbrev qz5 := qz271

noncomputable abbrev qz490 := (@instHPow Complex Complex Complex.instPow)

noncomputable abbrev qz273 := qz490

noncomputable abbrev qz491 := (@Neg.neg Complex Complex.instNeg qz514)

noncomputable abbrev qz274 := qz491

noncomputable abbrev qz6 := (@HPow.hPow Complex Complex Complex qz273 (@Nat.cast Complex Complex.instNatCast 8) qz274)

noncomputable def ep38 := @Enclosure.Complex.IsNear.of_eq qz3 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 8) qz6) Bool.false 22088809367 137438953472 19694882123539 5693408647577600 Bool.false 46135290831 274877906944 39413903878753 11386817295155200

noncomputable def ep39 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 8) qz6 Bool.false 23707756073 68719476736 8815034795403 2846704323788800 Bool.true 9200928813 68719476736 4409632951739 1423352161894400 Bool.true

noncomputable abbrev qz7 := (@HPow.hPow Complex Complex Complex qz273 (@Nat.cast Complex Complex.instNatCast 7) qz274)

noncomputable def ep40 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 8) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 7) qz7) Bool.false 23707756073 68719476736 8815034795403 2846704323788800 Bool.true 9200928813 68719476736 4409632951739 1423352161894400

noncomputable def ep41 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 7) qz7 Bool.false 1020472679 17179869184 3855130094337 1423352161894400 Bool.true 13107106589 34359738368 7715037443949 2846704323788800 Bool.false

noncomputable abbrev qz8 := (@HPow.hPow Complex Complex Complex qz273 (@Nat.cast Complex Complex.instNatCast 6) qz274)

noncomputable def ep42 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 7) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 6) qz8) Bool.false 1020472679 17179869184 3855130094337 1423352161894400 Bool.true 13107106589 34359738368 7715037443949 2846704323788800

noncomputable def ep43 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 6) qz8 Bool.true 41221745183 274877906944 26074491678911 11386817295155200 Bool.true 100597261189 137438953472 13043046810043 5693408647577600 Bool.false

noncomputable abbrev qz9 := (@HPow.hPow Complex Complex Complex qz273 (@Nat.cast Complex Complex.instNatCast 5) qz274)

noncomputable def ep44 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 6) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 5) qz9) Bool.true 41221745183 274877906944 26074491678911 11386817295155200 Bool.true 100597261189 137438953472 13043046810043 5693408647577600

noncomputable def ep45 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 5) qz9 Bool.false 15670856659 68719476736 5211705444389 2846704323788800 Bool.true 135503577117 274877906944 20865175248081 11386817295155200 Bool.true

noncomputable abbrev qz10 := (@HPow.hPow Complex Complex Complex qz273 (@Nat.cast Complex Complex.instNatCast 4) qz274)

noncomputable def ep46 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 5) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 4) qz10) Bool.false 15670856659 68719476736 5211705444389 2846704323788800 Bool.true 135503577117 274877906944 20865175248081 11386817295155200

noncomputable def ep47 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 4) qz10 Bool.false 47757684145 68719476736 750119161671 569340864757760 Bool.true 43174178379 137438953472 375831274733 284670432378880 Bool.true

noncomputable abbrev qz492 := (@Nat.cast Complex Complex.instNatCast 3)

noncomputable abbrev qz275 := qz492

noncomputable abbrev qz11 := (@HPow.hPow Complex Complex Complex qz273 qz275 qz274)

noncomputable def ep48 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 4) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 3) qz11) Bool.false 47757684145 68719476736 750119161671 569340864757760 Bool.true 43174178379 137438953472 375831274733 284670432378880

noncomputable def ep49 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 3) qz11 Bool.false 19389083677 17179869184 206113847343 284670432378880 Bool.true 23890870845 34359738368 827936738087 1138681729515520 Bool.true

noncomputable abbrev qz493 := (@Nat.cast Complex Complex.instNatCast 2)

noncomputable abbrev qz276 := qz493

noncomputable abbrev qz12 := (@HPow.hPow Complex Complex Complex qz273 qz276 qz274)

noncomputable def ep50 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 3) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 2) qz12) Bool.false 19389083677 17179869184 206113847343 284670432378880 Bool.true 23890870845 34359738368 827936738087 1138681729515520

noncomputable def ep51 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 2) qz12 Bool.false 1 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable abbrev qz277 := (Enclosure.sfrac Bool.false 0 1)

noncomputable abbrev qz13 := qz277

noncomputable def ep52 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 2) (Complex.mk (Enclosure.sfrac Bool.false 1 1) qz13) Bool.false 1 1 0 1 Bool.false 0 1 0 1 (BSN.head_sum_c_two qz5)

noncomputable abbrev qz278 := (@Nat.cast Real Real.instNatCast 2)

noncomputable abbrev qz14 := (@Inv.inv Real Real.instInv (Real.sqrt qz278))

noncomputable abbrev qz516 := (Enclosure.sfrac Bool.false 83585 1000)

noncomputable abbrev qz494 := qz516

noncomputable abbrev qz279 := qz494

noncomputable abbrev qz280 := (Enclosure.sfrac Bool.false 2 1)

noncomputable abbrev qz15 := (@HMul.hMul Real Real Real qz266 qz279 (Real.log qz280))

noncomputable abbrev qz16 := qz279

noncomputable abbrev qz281 := (@Eq.refl Real qz494)

noncomputable abbrev qz17 := qz281

noncomputable def ep53 := @Enclosure.Complex.IsNear.of_eq qz12 (Complex.mk (@HMul.hMul Real Real Real qz0 qz14 (Real.cos qz15)) (@HMul.hMul Real Real Real qz0 qz14 (@Neg.neg Real Real.instNeg (Real.sin qz15)))) Bool.false 2209214493 17179869184 206113847343 284670432378880 Bool.true 23890870845 34359738368 827936738087 1138681729515520 (BSN.cpow_neg_s_mk qz16 83585 1000 2 qz17 rfl)

noncomputable abbrev qz18 := (@Nat.cast Real Real.instNatCast 1)

noncomputable def ep54 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz278) 741455 524288 1 524288 185363 185365 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz278) (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz278 qz18)) Bool.false 741455 524288 1 524288 (BSN.sqrt_natCast_div_one 2) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz278 qz18)) Bool.false 741455 524288 1 524288 741455 524288 1 524288 (BSN.sqrt_enclosure 2 1 370727 370728 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep55 := BSN.log_dyadic_bound 1 3 6 5 613814355 262144 82850 24381081 945 181704 4 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 1) (BSN.artanhQ 3) 0 5 24381081 613814355 945 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep56 := nat_lit 11038814460521706534344499311296401725225370637240881750011093456179176690625

noncomputable def ep57 := nat_lit 71239273651864456168798555229954474558164150722024956391463162036118429368320

noncomputable def ep58 := nat_lit 24328255258029832382315523983300659941732654989195995817924337468187890625

noncomputable def ep59 := nat_lit 33067786871049059938268866885922603855792646601744253258397431693601154290625

noncomputable def ep60 := nat_lit 3205767314333900527595934985347951355117386782491123037615842291625329321574400

noncomputable abbrev qz282 := (BSN.cosEvenQ 1073741824)

noncomputable abbrev qz283 := (BSN.cosOddQ 1073741824)

noncomputable def ep61 := BSN.cos_dyadic_bound_f 1490266265 1073741824 3 2 524288 165862 ep56 ep57 ep58 ep59 ep60 ep58 95346 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1490266265) qz282 0 2 ep56 ep57 ep58 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1490266265) qz283 0 2 ep59 ep60 ep58 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz19 := (@Nat.cast Real Real.instNatCast 524288)

noncomputable abbrev qz20 := (Real.log qz280)

noncomputable abbrev qz21 := (Enclosure.Real.IsNear.const Bool.false 83585 1000)

noncomputable abbrev qz22 := (@Nat.cast Real Real.instNatCast 75557863725914323419136)

noncomputable abbrev qz284 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 30375457) qz19)

noncomputable abbrev qz285 := (BSN.isNear_log_sfrac 2 1 181704 262144 1 82850 Bool.false (BSN.logfrac_isNear 4 2 1 2 1 181704 262144 82850 rfl rfl rfl (ep55 rfl)))

noncomputable def ep62 := @Enclosure.Real.IsNear.cos_image qz15 qz284 Bool.false 30375457 524288 265 262144 Bool.false 95346 524288 1 82850 (@Enclosure.Real.IsNear.recentre' qz15 Bool.false 379693221 6553600 16717 16570000 30375457 524288 265 262144 (@Enclosure.Real.IsNear.mulLit_ff qz16 qz20 83585 1000 0 1 181704 262144 1 82850 379693221 6553600 16717 16570000 qz21 qz285 rfl) rfl) (Enclosure.sfrac_false_div 30375457 524288) (BSN.cos_reduce0 qz284 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 104868165604192041304064) qz22) 226375608064910080 72057594037927936 Bool.false 95346 524288 9 1000000000000000 165700 82850 (BSN.sin_reduce_arg_pos_rat_q0 30375457 524288 226375608064910080 72057594037927936 9 104868165604192041304064 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 95346 524288 104868165604192041304064 75557863725914323419136 1490266265 1073741824 165862 165700 (ep61 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep63 := nat_lit 19850403424732647895914246341146882577452281023042230353365628751147967730625

noncomputable def ep64 := nat_lit 641153462866780105519186997069590271023477356498224607523168458325065864314880

noncomputable def ep65 := nat_lit 51949763222929648570204039092745062824850311714175714551300007325677135090625

noncomputable def ep66 := nat_lit 11754480152557635267851761612942488302097084869134117804591421735959540845772800

noncomputable abbrev qz286 := (BSN.sinEvenQ 1073741824)

noncomputable abbrev qz287 := (BSN.sinOddQ 1073741824)

noncomputable def ep67 := BSN.sin_dyadic_bound_f 1490266265 1073741824 3 2 524288 165862 ep63 ep64 ep58 ep65 ep66 ep58 515545 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1490266265) qz286 0 2 ep63 ep64 ep58 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1490266265) qz287 0 2 ep65 ep66 ep58 rfl rfl rfl rfl) rfl rfl

noncomputable def ep68 := @Enclosure.Real.IsNear.sin_image qz15 qz284 Bool.false 30375457 524288 265 262144 Bool.false 515545 524288 1 82850 (@Enclosure.Real.IsNear.recentre' qz15 Bool.false 379693221 6553600 16717 16570000 30375457 524288 265 262144 (@Enclosure.Real.IsNear.mulLit_ff qz16 qz20 83585 1000 0 1 181704 262144 1 82850 379693221 6553600 16717 16570000 qz21 qz285 rfl) rfl) (Enclosure.sfrac_false_div 30375457 524288) (BSN.sin_reduce0 qz284 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 104868165604192041304064) qz22) 226375608064910080 72057594037927936 Bool.false 515545 524288 9 1000000000000000 165700 82850 (BSN.sin_reduce_arg_pos_rat_q0 30375457 524288 226375608064910080 72057594037927936 9 104868165604192041304064 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 515545 524288 104868165604192041304064 75557863725914323419136 1490266265 1073741824 165862 165700 (ep67 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz288 := (@Enclosure.Real.IsNear.recentre' qz14 Bool.false 370728 524288 2 524288 46341 65536 1 262144 (ep54 rfl rfl) rfl)

noncomputable def ep69 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz14 (Real.cos qz15)) (@HMul.hMul Real Real Real qz0 qz14 (@Neg.neg Real Real.instNeg (Real.sin qz15))) Bool.false 2209214493 17179869184 206113847343 284670432378880 Bool.true 23890870845 34359738368 827936738087 1138681729515520 (@Enclosure.Real.IsNear.mulLit_ff qz14 (Real.cos qz15) 46341 65536 1 262144 47673 262144 11108697 10859315200 2209214493 17179869184 206113847343 284670432378880 qz288 (@Enclosure.Real.IsNear.recentre' (Real.cos qz15) Bool.false 95346 524288 22217394 21718630400 47673 262144 11108697 10859315200 (ep62 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz14 (@Neg.neg Real Real.instNeg (Real.sin qz15)) 46341 65536 1 262144 515545 524288 11108697 10859315200 23890870845 34359738368 827936738087 1138681729515520 qz288 (@Enclosure.Real.IsNear.neg (Real.sin qz15) Bool.false 515545 524288 11108697 10859315200 (@Enclosure.Real.IsNear.recentre' (Real.sin qz15) Bool.false 515545 524288 22217394 21718630400 515545 524288 11108697 10859315200 (ep68 rfl rfl) rfl)) rfl)

noncomputable abbrev qz289 := (Enclosure.Real.IsNear.const Bool.false 0 1)

noncomputable abbrev qz23 := qz289

noncomputable def ep70 := @ep51 2209214493 17179869184 206113847343 284670432378880 Bool.true 23890870845 34359738368 827936738087 1138681729515520 Bool.false 19389083677 19389083677 17179869184 206113847343 284670432378880 Bool.true 23890870845 23890870845 34359738368 827936738087 1138681729515520 (ep52 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 1) qz13 Bool.false 1 1 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 1) qz23)) (ep53 ep69) rfl rfl

noncomputable abbrev qz290 := (@Nat.cast Real Real.instNatCast 3)

noncomputable abbrev qz24 := (@Inv.inv Real Real.instInv (Real.sqrt qz290))

noncomputable abbrev qz25 := (@HMul.hMul Real Real Real qz266 qz279 (Real.log (Enclosure.sfrac Bool.false 3 1)))

noncomputable def ep71 := @Enclosure.Complex.IsNear.of_eq qz11 (Complex.mk (@HMul.hMul Real Real Real qz0 qz24 (Real.cos qz25)) (@HMul.hMul Real Real Real qz0 qz24 (@Neg.neg Real Real.instNeg (Real.sin qz25)))) Bool.true 29798650563 68719476736 67578293397 113868172951552 Bool.false 52389305001 137438953472 135077672169 227736345903104 (BSN.cpow_neg_s_mk qz16 83585 1000 3 qz17 rfl)

noncomputable def ep72 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz290) 908093 524288 1 524288 151348 151350 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz290) (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz290 qz18)) Bool.false 908093 524288 1 524288 (BSN.sqrt_natCast_div_one 3) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz290 qz18)) Bool.false 908093 524288 1 524288 908093 524288 1 524288 (BSN.sqrt_enclosure 3 1 454046 454047 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep73 := BSN.log_dyadic_bound 1 2 10 9 171633298636800 262144 82850 16925142283965 34459425 287994 3 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base9 (BSN.artanhP 1) (BSN.artanhQ 2) 0 9 16925142283965 171633298636800 34459425 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep74 := nat_lit 802809309490259530242055393997710188250548400114667770149570729814960800000

noncomputable def ep75 := nat_lit 129201476892592433071651407279409590127567812510342434283443216100000000

noncomputable def ep76 := nat_lit 2408169525516993405860022879178571745571390064718982625580145303012682400000

noncomputable def ep77 := BSN.cos_dyadic_bound_f 774298530 1073741824 3 2 524288 165862 ep74 ep57 ep75 ep76 ep60 ep75 393774 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 774298530) qz282 0 2 ep74 ep57 ep75 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 774298530) qz283 0 2 ep76 ep60 ep75 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz26 := (Real.log (Enclosure.sfrac Bool.false 3 1))

noncomputable abbrev qz495 := (@Nat.cast Real Real.instNatCast 131072)

noncomputable abbrev qz291 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 12035989) qz495)

noncomputable abbrev qz292 := (BSN.isNear_log_sfrac 3 1 287994 262144 1 82850 Bool.false (BSN.logfrac_isNear 3 1 2 3 1 287994 262144 82850 rfl rfl rfl (ep73 rfl)))

noncomputable abbrev qz293 := (@Nat.cast Real Real.instNatCast 18889465931478580854784)

noncomputable def ep78 := @Enclosure.Real.IsNear.cos_image qz25 qz291 Bool.false 12035989 131072 265 262144 Bool.true 393774 524288 1 82850 (@Enclosure.Real.IsNear.recentre' qz25 Bool.false 2407197849 26214400 16717 16570000 12035989 131072 265 262144 (@Enclosure.Real.IsNear.mulLit_ff qz16 qz26 83585 1000 0 1 287994 262144 1 82850 2407197849 26214400 16717 16570000 qz21 qz292 rfl) rfl) (Enclosure.sfrac_false_div 12035989 131072) (BSN.cos_reduce2 qz291 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 13621603797466588643328) qz293) 226375608064910080 72057594037927936 Bool.false 393774 524288 14 1000000000000000 165700 82850 (BSN.sin_reduce_arg_pos_rat_q2 12035989 131072 226375608064910080 72057594037927936 14 13621603797466588643328 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 393774 524288 13621603797466588643328 18889465931478580854784 774298530 1073741824 165862 165700 (ep77 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep79 := nat_lit 359446069518909099270723633888810000

noncomputable def ep80 := nat_lit 159507359494189904748456847233641349120

noncomputable def ep81 := nat_lit 1116551516459329333239197930635489443840

noncomputable def ep82 := BSN.sin_dyadic_bound_f 774298530 1073741824 2 1 524288 165862 ep79 ep80 ep79 ep79 ep81 ep79 346149 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 774298530) qz286 0 1 ep79 ep80 ep79 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 774298530) qz287 0 1 ep79 ep81 ep79 rfl rfl rfl rfl) rfl rfl

noncomputable def ep83 := @Enclosure.Real.IsNear.sin_image qz25 qz291 Bool.false 12035989 131072 265 262144 Bool.true 346149 524288 1 82850 (@Enclosure.Real.IsNear.recentre' qz25 Bool.false 2407197849 26214400 16717 16570000 12035989 131072 265 262144 (@Enclosure.Real.IsNear.mulLit_ff qz16 qz26 83585 1000 0 1 287994 262144 1 82850 2407197849 26214400 16717 16570000 qz21 qz292 rfl) rfl) (Enclosure.sfrac_false_div 12035989 131072) (BSN.sin_reduce2 qz291 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 13621603797466588643328) qz293) 226375608064910080 72057594037927936 Bool.false 346149 524288 14 1000000000000000 165700 82850 (BSN.sin_reduce_arg_pos_rat_q2 12035989 131072 226375608064910080 72057594037927936 14 13621603797466588643328 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 346149 524288 13621603797466588643328 18889465931478580854784 774298530 1073741824 165862 165700 (ep82 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz294 := (@Enclosure.Real.IsNear.recentre' qz24 Bool.false 302698 524288 2 524288 151349 262144 1 262144 (ep72 rfl rfl) rfl)

noncomputable def ep84 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz24 (Real.cos qz25)) (@HMul.hMul Real Real Real qz0 qz24 (@Neg.neg Real Real.instNeg (Real.sin qz25))) Bool.true 29798650563 68719476736 67578293397 113868172951552 Bool.false 52389305001 137438953472 135077672169 227736345903104 (@Enclosure.Real.IsNear.mulLit_ft qz24 (Real.cos qz25) 151349 262144 1 262144 196887 262144 11108697 10859315200 29798650563 68719476736 67578293397 113868172951552 qz294 (@Enclosure.Real.IsNear.recentre' (Real.cos qz25) Bool.true 393774 524288 22217394 21718630400 196887 262144 11108697 10859315200 (ep78 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz24 (@Neg.neg Real Real.instNeg (Real.sin qz25)) 151349 262144 1 262144 346149 524288 11108697 10859315200 52389305001 137438953472 135077672169 227736345903104 qz294 (@Enclosure.Real.IsNear.neg (Real.sin qz25) Bool.true 346149 524288 11108697 10859315200 (@Enclosure.Real.IsNear.recentre' (Real.sin qz25) Bool.true 346149 524288 22217394 21718630400 346149 524288 11108697 10859315200 (ep83 rfl rfl) rfl)) rfl)

noncomputable def ep85 := @ep49 29798650563 68719476736 67578293397 113868172951552 Bool.false 52389305001 137438953472 135077672169 227736345903104 Bool.false 820470766141890887680 47757684145 68719476736 750119161671 569340864757760 Bool.true 1483453473355802345472 43174178379 137438953472 375831274733 284670432378880 (ep50 (BSN.head_sum_c_succ qz5 2 3 rfl rfl) (ep70 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep71 ep84) rfl rfl

noncomputable abbrev qz295 := (@Nat.cast Real Real.instNatCast 4)

noncomputable abbrev qz27 := (@Inv.inv Real Real.instInv (Real.sqrt qz295))

noncomputable abbrev qz28 := (@HMul.hMul Real Real Real qz266 qz279 (Real.log (Enclosure.sfrac Bool.false 4 1)))

noncomputable def ep86 := @Enclosure.Complex.IsNear.of_eq qz10 (Complex.mk (@HMul.hMul Real Real Real qz0 qz27 (Real.cos qz28)) (@HMul.hMul Real Real Real qz0 qz27 (@Neg.neg Real Real.instNeg (Real.sin qz28)))) Bool.true 16043413743 34359738368 730554818017 1423352161894400 Bool.true 49155220359 274877906944 5831924258761 11386817295155200 (BSN.cpow_neg_s_mk qz16 83585 1000 4 qz17 rfl)

noncomputable def ep87 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz295) 1048577 524288 1 524288 131071 131072 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz295) (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz295 qz18)) Bool.false 1048577 524288 1 524288 (BSN.sqrt_natCast_div_one 4) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz295 qz18)) Bool.false 1048577 524288 1 524288 1048577 524288 1 524288 (BSN.sqrt_enclosure 4 1 524288 524289 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep88 := nat_lit 471225594319403171539306640625

noncomputable def ep89 := nat_lit 73155514365408823868279100600

noncomputable def ep90 := BSN.log_dyadic_bound 3 5 13 12 ep88 262144 82850 ep89 89313862490502916491225 363408 8 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base12 (BSN.artanhP 3) (BSN.artanhQ 5) 0 12 ep89 ep88 89313862490502916491225 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep91 := nat_lit 11274398597645121544021215113453271411019998480840835312121833580922866991360

noncomputable def ep92 := nat_lit 7856312843120408665572484748252816276219021558332570314017208941387940096

noncomputable def ep93 := nat_lit 29515467058753123382216065083737587231081355700631554036953536278416690217216

noncomputable def ep94 := BSN.sin_dyadic_bound_f 1293904866 1073741824 3 2 524288 165862 ep91 ep64 ep92 ep93 ep66 ep92 489608 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1293904866) qz286 0 2 ep91 ep64 ep92 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1293904866) qz287 0 2 ep93 ep66 ep92 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz29 := (Real.log (Enclosure.sfrac Bool.false 4 1))

noncomputable abbrev qz296 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 60750915) qz19)

noncomputable abbrev qz297 := (BSN.isNear_log_sfrac 4 1 363408 262144 1 82850 Bool.false (BSN.logfrac_isNear 8 2 1 4 1 363408 262144 82850 rfl rfl rfl (ep90 rfl)))

noncomputable def ep95 := @Enclosure.Real.IsNear.cos_image qz28 qz296 Bool.false 60750915 524288 265 262144 Bool.true 489608 524288 1 82850 (@Enclosure.Real.IsNear.recentre' qz28 Bool.false 379693221 3276800 16717 16570000 60750915 524288 265 262144 (@Enclosure.Real.IsNear.mulLit_ff qz16 qz29 83585 1000 0 1 363408 262144 1 82850 379693221 3276800 16717 16570000 qz21 qz297 rfl) rfl) (Enclosure.sfrac_false_div 60750915 524288) (BSN.cos_reduce1 qz296 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 91050460522436582440960) qz22) 226375608064910080 72057594037927936 Bool.false 489608 524288 18 1000000000000000 165700 82850 (BSN.sin_reduce_arg_pos_rat_q1 60750915 524288 226375608064910080 72057594037927936 18 91050460522436582440960 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 489608 524288 91050460522436582440960 75557863725914323419136 1293904866 1073741824 165862 165700 (ep94 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep96 := nat_lit 6267046471066454372752040611806596480022763165604167426873915193375542968576

noncomputable def ep97 := nat_lit 18785426787513122300924976865923283807515851453695837139993711162243853025536

noncomputable def ep98 := BSN.cos_dyadic_bound_f 1293904866 1073741824 3 2 524288 165862 ep96 ep57 ep92 ep97 ep60 ep92 187513 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1293904866) qz282 0 2 ep96 ep57 ep92 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1293904866) qz283 0 2 ep97 ep60 ep92 rfl rfl rfl rfl) rfl rfl

noncomputable def ep99 := @Enclosure.Real.IsNear.sin_image qz28 qz296 Bool.false 60750915 524288 265 262144 Bool.false 187513 524288 1 82850 (@Enclosure.Real.IsNear.recentre' qz28 Bool.false 379693221 3276800 16717 16570000 60750915 524288 265 262144 (@Enclosure.Real.IsNear.mulLit_ff qz16 qz29 83585 1000 0 1 363408 262144 1 82850 379693221 3276800 16717 16570000 qz21 qz297 rfl) rfl) (Enclosure.sfrac_false_div 60750915 524288) (BSN.sin_reduce1 qz296 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 91050460522436582440960) qz22) 226375608064910080 72057594037927936 Bool.false 187513 524288 18 1000000000000000 165700 82850 (BSN.sin_reduce_arg_pos_rat_q1 60750915 524288 226375608064910080 72057594037927936 18 91050460522436582440960 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 187513 524288 91050460522436582440960 75557863725914323419136 1293904866 1073741824 165862 165700 (ep98 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz298 := (@Enclosure.Real.IsNear.recentre' qz27 Bool.false 262143 524288 1 524288 262143 524288 1 524288 (ep87 rfl rfl) rfl)

noncomputable def ep100 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz27 (Real.cos qz28)) (@HMul.hMul Real Real Real qz0 qz27 (@Neg.neg Real Real.instNeg (Real.sin qz28))) Bool.true 16043413743 34359738368 730554818017 1423352161894400 Bool.true 49155220359 274877906944 5831924258761 11386817295155200 (@Enclosure.Real.IsNear.mulLit_ft qz27 (Real.cos qz28) 262143 524288 1 524288 61201 65536 11108697 10859315200 16043413743 34359738368 730554818017 1423352161894400 qz298 (@Enclosure.Real.IsNear.recentre' (Real.cos qz28) Bool.true 489608 524288 22217394 21718630400 61201 65536 11108697 10859315200 (ep95 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz27 (@Neg.neg Real Real.instNeg (Real.sin qz28)) 262143 524288 1 524288 187513 524288 11108697 10859315200 49155220359 274877906944 5831924258761 11386817295155200 qz298 (@Enclosure.Real.IsNear.neg (Real.sin qz28) Bool.false 187513 524288 11108697 10859315200 (@Enclosure.Real.IsNear.recentre' (Real.sin qz28) Bool.false 187513 524288 22217394 21718630400 187513 524288 11108697 10859315200 (ep99 rfl rfl) rfl)) rfl)

noncomputable def ep101 := @ep47 16043413743 34359738368 730554818017 1423352161894400 Bool.true 49155220359 274877906944 5831924258761 11386817295155200 Bool.false 538446534805670592512 15670856659 68719476736 5211705444389 2846704323788800 Bool.true 18623469830672926900224 135503577117 274877906944 20865175248081 11386817295155200 (ep48 (BSN.head_sum_c_succ qz5 3 4 rfl rfl) (ep85 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep86 ep100) rfl rfl

noncomputable abbrev qz299 := (@Nat.cast Real Real.instNatCast 5)

noncomputable abbrev qz30 := (@Inv.inv Real Real.instInv (Real.sqrt qz299))

noncomputable abbrev qz31 := (@HMul.hMul Real Real Real qz266 qz279 (Real.log (Enclosure.sfrac Bool.false 5 1)))

noncomputable def ep102 := @Enclosure.Complex.IsNear.of_eq qz9 (Complex.mk (@HMul.hMul Real Real Real qz0 qz30 (Real.cos qz31)) (@HMul.hMul Real Real Real qz0 qz30 (@Neg.neg Real Real.instNeg (Real.sin qz31)))) Bool.true 103905171819 274877906944 1045533980271 2277363459031040 Bool.true 65690945261 274877906944 1044183674401 2277363459031040 (BSN.cpow_neg_s_mk qz16 83585 1000 5 qz17 rfl)

noncomputable def ep103 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz299) 1172343 524288 1 524288 117234 117235 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz299) (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz299 qz18)) Bool.false 1172343 524288 1 524288 (BSN.sqrt_natCast_div_one 5) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz299 qz18)) Bool.false 1172343 524288 1 524288 1172343 524288 1 524288 (BSN.sqrt_enclosure 5 1 586171 586172 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep104 := nat_lit 11734546589655452485523914939250625

noncomputable def ep105 := nat_lit 2429970938528035899633153341031900

noncomputable def ep106 := nat_lit 824199001261152424427520000

noncomputable def ep107 := BSN.log_dyadic_bound 2 3 17 16 ep104 262144 82850 ep105 ep106 421904 5 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base16 (BSN.artanhP 2) (BSN.artanhQ 3) 0 16 ep105 ep104 ep106 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep108 := nat_lit 5496473211595172830183164224730383938757607467337434598265237335505390921825

noncomputable def ep109 := nat_lit 1868574267024490683206008714655407459101510373312548015833301938858748001

noncomputable def ep110 := nat_lit 14392499767269317760802144193517753941812331397660298870097605770803585869921

noncomputable def ep111 := BSN.sin_dyadic_bound_f 1081281557 1073741824 3 2 524288 165862 ep108 ep64 ep109 ep110 ep66 ep109 443151 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1081281557) qz286 0 2 ep108 ep64 ep109 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1081281557) qz287 0 2 ep110 ep66 ep109 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz32 := (Real.log (Enclosure.sfrac Bool.false 5 1))

noncomputable abbrev qz300 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 70529691) qz19)

noncomputable abbrev qz301 := (BSN.isNear_log_sfrac 5 1 421904 262144 1 82850 Bool.false (BSN.logfrac_isNear 5 1 2 5 1 421904 262144 82850 rfl rfl rfl (ep107 rfl)))

noncomputable def ep112 := @Enclosure.Real.IsNear.cos_image qz31 qz300 Bool.false 70529691 524288 265 262144 Bool.true 443151 524288 1 82850 (@Enclosure.Real.IsNear.recentre' qz31 Bool.false 440810573 3276800 16717 16570000 70529691 524288 265 262144 (@Enclosure.Real.IsNear.mulLit_ff qz16 qz32 83585 1000 0 1 421904 262144 1 82850 440810573 3276800 16717 16570000 qz21 qz301 rfl) rfl) (Enclosure.sfrac_false_div 70529691 524288) (BSN.cos_reduce1 qz300 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 76088425300475250737152) qz22) 226375608064910080 72057594037927936 Bool.false 443151 524288 21 1000000000000000 165700 82850 (BSN.sin_reduce_arg_pos_rat_q1 70529691 524288 226375608064910080 72057594037927936 21 76088425300475250737152 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 443151 524288 76088425300475250737152 75557863725914323419136 1081281557 1073741824 165862 165700 (ep111 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep113 := nat_lit 3054426706115995790405405017612282369291604819797824798154391098364709955681

noncomputable def ep114 := nat_lit 9159542969813938389849803035407536292956611438646849298431506691216412371041

noncomputable def ep115 := BSN.cos_dyadic_bound_f 1081281557 1073741824 3 2 524288 165862 ep113 ep57 ep109 ep114 ep60 ep109 280169 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1081281557) qz282 0 2 ep113 ep57 ep109 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1081281557) qz283 0 2 ep114 ep60 ep109 rfl rfl rfl rfl) rfl rfl

noncomputable def ep116 := @Enclosure.Real.IsNear.sin_image qz31 qz300 Bool.false 70529691 524288 265 262144 Bool.false 280169 524288 1 82850 (@Enclosure.Real.IsNear.recentre' qz31 Bool.false 440810573 3276800 16717 16570000 70529691 524288 265 262144 (@Enclosure.Real.IsNear.mulLit_ff qz16 qz32 83585 1000 0 1 421904 262144 1 82850 440810573 3276800 16717 16570000 qz21 qz301 rfl) rfl) (Enclosure.sfrac_false_div 70529691 524288) (BSN.sin_reduce1 qz300 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 76088425300475250737152) qz22) 226375608064910080 72057594037927936 Bool.false 280169 524288 21 1000000000000000 165700 82850 (BSN.sin_reduce_arg_pos_rat_q1 70529691 524288 226375608064910080 72057594037927936 21 76088425300475250737152 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 280169 524288 76088425300475250737152 75557863725914323419136 1081281557 1073741824 165862 165700 (ep115 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz302 := (@Enclosure.Real.IsNear.recentre' qz30 Bool.false 234469 524288 1 524288 234469 524288 1 524288 (ep103 rfl rfl) rfl)

noncomputable def ep117 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz30 (Real.cos qz31)) (@HMul.hMul Real Real Real qz0 qz30 (@Neg.neg Real Real.instNeg (Real.sin qz31))) Bool.true 103905171819 274877906944 1045533980271 2277363459031040 Bool.true 65690945261 274877906944 1044183674401 2277363459031040 (@Enclosure.Real.IsNear.mulLit_ft qz30 (Real.cos qz31) 234469 524288 1 524288 443151 524288 11108697 10859315200 103905171819 274877906944 1045533980271 2277363459031040 qz302 (@Enclosure.Real.IsNear.recentre' (Real.cos qz31) Bool.true 443151 524288 22217394 21718630400 443151 524288 11108697 10859315200 (ep112 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz30 (@Neg.neg Real Real.instNeg (Real.sin qz31)) 234469 524288 1 524288 280169 524288 11108697 10859315200 65690945261 274877906944 1044183674401 2277363459031040 qz302 (@Enclosure.Real.IsNear.neg (Real.sin qz31) Bool.false 280169 524288 11108697 10859315200 (@Enclosure.Real.IsNear.recentre' (Real.sin qz31) Bool.false 280169 524288 22217394 21718630400 280169 524288 11108697 10859315200 (ep116 rfl rfl) rfl)) rfl)

noncomputable def ep118 := @ep45 103905171819 274877906944 1045533980271 2277363459031040 Bool.true 65690945261 274877906944 1044183674401 2277363459031040 Bool.true 2832736759120488562688 41221745183 274877906944 26074491678911 11386817295155200 Bool.true 55303929199862409592832 100597261189 137438953472 13043046810043 5693408647577600 (ep46 (BSN.head_sum_c_succ qz5 4 5 rfl rfl) (ep101 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep102 ep117) rfl rfl

noncomputable abbrev qz303 := (@Nat.cast Real Real.instNatCast 6)

noncomputable abbrev qz33 := (@Inv.inv Real Real.instInv (Real.sqrt qz303))

noncomputable abbrev qz34 := (@HMul.hMul Real Real Real qz266 qz279 (Real.log (Enclosure.sfrac Bool.false 6 1)))

noncomputable def ep119 := @Enclosure.Complex.IsNear.of_eq qz8 (Complex.mk (@HMul.hMul Real Real Real qz0 qz33 (Real.cos qz34)) (@HMul.hMul Real Real Real qz0 qz33 (@Neg.neg Real Real.instNeg (Real.sin qz34)))) Bool.false 57549308047 274877906944 953309815157 2277363459031040 Bool.false 48168834833 137438953472 477405615571 1138681729515520 (BSN.cpow_neg_s_mk qz16 83585 1000 6 qz17 rfl)

noncomputable abbrev qz304 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 6) qz18)

noncomputable def ep120 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz303) 1284239 524288 1 524288 107019 107020 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz303) (Real.sqrt qz304) Bool.false 1284239 524288 1 524288 (BSN.sqrt_natCast_div_one 6) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz304) Bool.false 1284239 524288 1 524288 1284239 524288 1 524288 (BSN.sqrt_enclosure 6 1 642119 642120 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep121 := BSN.log_dyadic_bound 2 10 4 3 105000000 262144 82850 1434560 960 106290 12 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 2) (BSN.artanhQ 10) 0 3 1434560 105000000 960 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz35 := (Real.log (Enclosure.sfrac Bool.false 6 1))

noncomputable def ep122 := @Enclosure.Real.IsNear.mulLit_ff qz16 qz35 83585 1000 0 1 4034681531866359 2251799813685248 10000000001657 828500000000000000 67447771168209923403 450359962737049600 167170000027700069 165700000000000000000 qz21 (BSN.isNear_log_sfrac 6 1 4034681531866359 2251799813685248 10000000001657 828500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz304) Bool.false 16922680887833197019136 9444732965739290427392 1000000000165700 82850000000000000000 4034681531866359 2251799813685248 10000000001657 828500000000000000 (BSN.log_rat_reduce_isNear 6 1 2 12 8 106290 262144 24973259072661432 36028797018963968 82850 1000000000000000 rfl rfl rfl rfl (ep121 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep123 := nat_lit 111761367877476523158240048969610000

noncomputable def ep124 := BSN.sin_dyadic_bound_f 578193130 1073741824 2 1 524288 165862 ep123 ep80 ep123 ep123 ep81 ep123 268873 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 578193130) qz286 0 1 ep123 ep80 ep123 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 578193130) qz287 0 1 ep123 ep81 ep123 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz305 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 78519539) qz19)

noncomputable def ep125 := @Enclosure.Real.IsNear.cos_image qz34 qz305 Bool.false 78519539 524288 265 262144 Bool.false 268873 524288 1 82850 (@Enclosure.Real.IsNear.recentre' qz34 Bool.false 67447771168209923403 450359962737049600 167170000027700069 165700000000000000000 78519539 524288 265 262144 (ep122 rfl) rfl) (Enclosure.sfrac_false_div 78519539 524288) (BSN.cos_reduce3 qz305 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 40686724506620377694208) qz22) 226375608064910080 72057594037927936 Bool.false 268873 524288 23 1000000000000000 165700 82850 (BSN.sin_reduce_arg_pos_rat_q3 78519539 524288 226375608064910080 72057594037927936 23 40686724506620377694208 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 268873 524288 40686724506620377694208 75557863725914323419136 578193130 1073741824 165862 165700 (ep124 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep126 := nat_lit 31901471898837980949691369446728269824

noncomputable def ep127 := nat_lit 478522078482569714245370541700924047360

noncomputable def ep128 := BSN.cos_dyadic_bound_f 578193130 1073741824 2 1 524288 165862 ep123 ep126 ep123 ep123 ep127 ep123 450094 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 578193130) qz282 0 1 ep123 ep126 ep123 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 578193130) qz283 0 1 ep123 ep127 ep123 rfl rfl rfl rfl) rfl rfl

noncomputable def ep129 := @Enclosure.Real.IsNear.sin_image qz34 qz305 Bool.false 78519539 524288 265 262144 Bool.true 450094 524288 1 82850 (@Enclosure.Real.IsNear.recentre' qz34 Bool.false 67447771168209923403 450359962737049600 167170000027700069 165700000000000000000 78519539 524288 265 262144 (ep122 rfl) rfl) (Enclosure.sfrac_false_div 78519539 524288) (BSN.sin_reduce3 qz305 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 40686724506620377694208) qz22) 226375608064910080 72057594037927936 Bool.false 450094 524288 23 1000000000000000 165700 82850 (BSN.sin_reduce_arg_pos_rat_q3 78519539 524288 226375608064910080 72057594037927936 23 40686724506620377694208 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 450094 524288 40686724506620377694208 75557863725914323419136 578193130 1073741824 165862 165700 (ep128 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz306 := (@Enclosure.Real.IsNear.recentre' qz33 Bool.false 214039 524288 1 524288 214039 524288 1 524288 (ep120 rfl rfl) rfl)

noncomputable def ep130 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz33 (Real.cos qz34)) (@HMul.hMul Real Real Real qz0 qz33 (@Neg.neg Real Real.instNeg (Real.sin qz34))) Bool.false 57549308047 274877906944 953309815157 2277363459031040 Bool.false 48168834833 137438953472 477405615571 1138681729515520 (@Enclosure.Real.IsNear.mulLit_ff qz33 (Real.cos qz34) 214039 524288 1 524288 268873 524288 11108697 10859315200 57549308047 274877906944 953309815157 2277363459031040 qz306 (@Enclosure.Real.IsNear.recentre' (Real.cos qz34) Bool.false 268873 524288 22217394 21718630400 268873 524288 11108697 10859315200 (ep125 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz33 (@Neg.neg Real Real.instNeg (Real.sin qz34)) 214039 524288 1 524288 225047 262144 11108697 10859315200 48168834833 137438953472 477405615571 1138681729515520 qz306 (@Enclosure.Real.IsNear.neg (Real.sin qz34) Bool.true 225047 262144 11108697 10859315200 (@Enclosure.Real.IsNear.recentre' (Real.sin qz34) Bool.true 450094 524288 22217394 21718630400 225047 262144 11108697 10859315200 (ep129 rfl rfl) rfl)) rfl)

noncomputable def ep131 := @ep43 57549308047 274877906944 953309815157 2277363459031040 Bool.false 48168834833 137438953472 477405615571 1138681729515520 Bool.false 4488086305552902127616 1020472679 17179869184 3855130094337 1423352161894400 Bool.true 7205708050552462508032 13107106589 34359738368 7715037443949 2846704323788800 (ep44 (BSN.head_sum_c_succ qz5 5 6 rfl rfl) (ep118 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep119 ep130) rfl rfl

noncomputable abbrev qz307 := (@Nat.cast Real Real.instNatCast 7)

noncomputable abbrev qz36 := (@Inv.inv Real Real.instInv (Real.sqrt qz307))

noncomputable abbrev qz37 := (@HMul.hMul Real Real Real qz266 qz279 (Real.log (Enclosure.sfrac Bool.false 7 1)))

noncomputable def ep132 := @Enclosure.Complex.IsNear.of_eq qz7 (Complex.mk (@HMul.hMul Real Real Real qz0 qz36 (Real.cos qz37)) (@HMul.hMul Real Real Real qz0 qz36 (@Neg.neg Real Real.instNeg (Real.sin qz37)))) Bool.false 19625865357 68719476736 1104774606729 2846704323788800 Bool.false 17013284365 68719476736 1104228459529 2846704323788800 (BSN.cpow_neg_s_mk qz16 83585 1000 7 qz17 rfl)

noncomputable abbrev qz308 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 7) qz18)

noncomputable def ep133 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz307) 1387135 524288 1 524288 99081 99082 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz307) (Real.sqrt qz308) Bool.false 1387135 524288 1 524288 (BSN.sqrt_natCast_div_one 7) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz308) Bool.false 1387135 524288 1 524288 1387135 524288 1 524288 (BSN.sqrt_enclosure 7 1 693567 693568 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep134 := BSN.log_dyadic_bound 3 11 5 4 202569142545 262144 82850 5259111624 688905 146699 14 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 3) (BSN.artanhQ 11) 0 4 5259111624 202569142545 688905 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz38 := (Real.log (Enclosure.sfrac Bool.false 7 1))

noncomputable def ep135 := @Enclosure.Real.IsNear.mulLit_ff qz16 qz38 83585 1000 0 1 4381792198794487 2251799813685248 10000000001657 828500000000000000 73250420187247439179 450359962737049600 167170000027700069 165700000000000000000 qz21 (BSN.isNear_log_sfrac 7 1 4381792198794487 2251799813685248 10000000001657 828500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz308) Bool.false 18378568546572512002048 9444732965739290427392 1000000000165700 82850000000000000000 4381792198794487 2251799813685248 10000000001657 828500000000000000 (BSN.log_rat_reduce_isNear 7 1 2 14 8 146699 262144 24973259072661432 36028797018963968 82850 1000000000000000 rfl rfl rfl rfl (ep134 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep136 := nat_lit 715613749045231637235923748314410000

noncomputable def ep137 := BSN.sin_dyadic_bound_f 919749730 1073741824 2 1 524288 165862 ep136 ep80 ep136 ep136 ep81 ep136 396156 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 919749730) qz286 0 1 ep136 ep80 ep136 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 919749730) qz287 0 1 ep136 ep81 ep136 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz496 := (@Nat.cast Real Real.instNatCast 65536)

noncomputable abbrev qz309 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 10659339) qz496)

noncomputable abbrev qz310 := (@Nat.cast Real Real.instNatCast 9444732965739290427392)

noncomputable def ep138 := @Enclosure.Real.IsNear.cos_image qz37 qz309 Bool.false 10659339 65536 265 262144 Bool.false 396156 524288 1 82850 (@Enclosure.Real.IsNear.recentre' qz37 Bool.false 73250420187247439179 450359962737049600 167170000027700069 165700000000000000000 10659339 65536 265 262144 (ep135 rfl) rfl) (Enclosure.sfrac_false_div 10659339 65536) (BSN.cos_reduce3 qz309 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 8090204184684913491968) qz310) 226375608064910080 72057594037927936 Bool.false 396156 524288 25 1000000000000000 165700 82850 (BSN.sin_reduce_arg_pos_rat_q3 10659339 65536 226375608064910080 72057594037927936 25 8090204184684913491968 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 396156 524288 8090204184684913491968 9444732965739290427392 919749730 1073741824 165862 165700 (ep137 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep139 := nat_lit 1598551336429021218429357007700737089905455285473412418787861310363568800000

noncomputable def ep140 := nat_lit 512103037822571763993660683025856945388713524997061075316213648100000000

noncomputable def ep141 := nat_lit 4794629803211418511760083701736159555825588429370243134212951503794506400000

noncomputable def ep142 := BSN.cos_dyadic_bound_f 919749730 1073741824 3 2 524288 165862 ep139 ep57 ep140 ep141 ep60 ep140 343420 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 919749730) qz282 0 2 ep139 ep57 ep140 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 919749730) qz283 0 2 ep141 ep60 ep140 rfl rfl rfl rfl) rfl rfl

noncomputable def ep143 := @Enclosure.Real.IsNear.sin_image qz37 qz309 Bool.false 10659339 65536 265 262144 Bool.true 343420 524288 1 82850 (@Enclosure.Real.IsNear.recentre' qz37 Bool.false 73250420187247439179 450359962737049600 167170000027700069 165700000000000000000 10659339 65536 265 262144 (ep135 rfl) rfl) (Enclosure.sfrac_false_div 10659339 65536) (BSN.sin_reduce3 qz309 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 8090204184684913491968) qz310) 226375608064910080 72057594037927936 Bool.false 343420 524288 25 1000000000000000 165700 82850 (BSN.sin_reduce_arg_pos_rat_q3 10659339 65536 226375608064910080 72057594037927936 25 8090204184684913491968 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 343420 524288 8090204184684913491968 9444732965739290427392 919749730 1073741824 165862 165700 (ep142 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz311 := (@Enclosure.Real.IsNear.recentre' qz36 Bool.false 198163 524288 1 524288 198163 524288 1 524288 (ep133 rfl rfl) rfl)

noncomputable def ep144 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz36 (Real.cos qz37)) (@HMul.hMul Real Real Real qz0 qz36 (@Neg.neg Real Real.instNeg (Real.sin qz37))) Bool.false 19625865357 68719476736 1104774606729 2846704323788800 Bool.false 17013284365 68719476736 1104228459529 2846704323788800 (@Enclosure.Real.IsNear.mulLit_ff qz36 (Real.cos qz37) 198163 524288 1 524288 99039 131072 11108697 10859315200 19625865357 68719476736 1104774606729 2846704323788800 qz311 (@Enclosure.Real.IsNear.recentre' (Real.cos qz37) Bool.false 396156 524288 22217394 21718630400 99039 131072 11108697 10859315200 (ep138 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz36 (@Neg.neg Real Real.instNeg (Real.sin qz37)) 198163 524288 1 524288 85855 131072 11108697 10859315200 17013284365 68719476736 1104228459529 2846704323788800 qz311 (@Enclosure.Real.IsNear.neg (Real.sin qz37) Bool.true 85855 131072 11108697 10859315200 (@Enclosure.Real.IsNear.recentre' (Real.sin qz37) Bool.true 343420 524288 22217394 21718630400 85855 131072 11108697 10859315200 (ep143 rfl rfl) rfl)) rfl)

noncomputable def ep145 := @ep41 19625865357 68719476736 1104774606729 2846704323788800 Bool.false 17013284365 68719476736 1104228459529 2846704323788800 Bool.false 407296147980321554432 23707756073 68719476736 8815034795403 2846704323788800 Bool.true 316141506757272797184 9200928813 68719476736 4409632951739 1423352161894400 (ep42 (BSN.head_sum_c_succ qz5 6 7 rfl rfl) (ep131 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep132 ep144) rfl rfl

noncomputable abbrev qz312 := (@Nat.cast Real Real.instNatCast 8)

noncomputable abbrev qz39 := (@Inv.inv Real Real.instInv (Real.sqrt qz312))

noncomputable abbrev qz313 := (Real.log (Enclosure.sfrac Bool.false 8 1))

noncomputable abbrev qz40 := (@HMul.hMul Real Real Real qz266 qz279 qz313)

noncomputable def ep146 := @Enclosure.Complex.IsNear.of_eq qz6 (Complex.mk (@HMul.hMul Real Real Real qz0 qz39 (Real.cos qz40)) (@HMul.hMul Real Real Real qz0 qz39 (@Neg.neg Real Real.instNeg (Real.sin qz40)))) Bool.true 25326702779 137438953472 2064812532733 5693408647577600 Bool.false 82939006083 274877906944 4136840264841 11386817295155200 (BSN.cpow_neg_s_mk qz16 83585 1000 8 qz17 rfl)

noncomputable abbrev qz314 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 8) qz18)

noncomputable def ep147 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz312) 1482911 524288 1 524288 92681 92682 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz312) (Real.sqrt qz314) Bool.false 1482911 524288 1 524288 (BSN.sqrt_natCast_div_one 8) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz314) Bool.false 1482911 524288 1 524288 1482911 524288 1 524288 (BSN.sqrt_enclosure 8 1 741455 741456 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep148 := BSN.log_dyadic_bound 0 16 1 0 1 262144 82850 0 1 0 16 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 0) (BSN.artanhQ 16) 0 0 rfl) rfl rfl rfl

noncomputable def ep149 := @Enclosure.Real.IsNear.mulLit_ff qz16 qz313 83585 1000 0 1 9364972152248037 4503599627370496 20000000004971 1657000000000000000 156554239469130434529 900719925474099200 334340000083100207 331400000000000000000 qz21 (BSN.isNear_log_sfrac 8 1 9364972152248037 4503599627370496 20000000004971 1657000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz314) Bool.false 19639770079031275290624 9444732965739290427392 1000000000248550 82850000000000000000 9364972152248037 4503599627370496 20000000004971 1657000000000000000 (BSN.log_rat_reduce_isNear 8 1 3 16 16 0 262144 24973259072661432 36028797018963968 82850 1000000000000000 rfl rfl rfl rfl (ep148 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep150 := nat_lit 3247014630078888572618727803301433241120771499397267849821046198967148503296

noncomputable def ep151 := nat_lit 2111475062575813571459454264001360432351936905080751655516052715906294016

noncomputable def ep152 := nat_lit 9736820940111514090713264501376297002497610624381642046152106491469632921856

noncomputable def ep153 := BSN.cos_dyadic_bound_f 1097926442 1073741824 3 2 524288 165862 ep150 ep57 ep151 ep152 ep60 ep151 273266 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1097926442) qz282 0 2 ep150 ep57 ep151 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1097926442) qz283 0 2 ep152 ep60 ep151 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz315 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 2847705) (@Nat.cast Real Real.instNatCast 16384))

noncomputable def ep154 := @Enclosure.Real.IsNear.cos_image qz40 qz315 Bool.false 2847705 16384 265 262144 Bool.true 273266 524288 1 82850 (@Enclosure.Real.IsNear.recentre' qz40 Bool.false 156554239469130434529 900719925474099200 334340000083100207 331400000000000000000 2847705 16384 265 262144 (ep149 rfl) rfl) (Enclosure.sfrac_false_div 2847705 16384) (BSN.cos_reduce2 qz315 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 2414365780651603394560) (@Nat.cast Real Real.instNatCast 2361183241434822606848)) 226375608064910080 72057594037927936 Bool.false 273266 524288 27 1000000000000000 165700 82850 (BSN.sin_reduce_arg_pos_rat_q2 2847705 16384 226375608064910080 72057594037927936 27 2414365780651603394560 2361183241434822606848 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 273266 524288 2414365780651603394560 2361183241434822606848 1097926442 1073741824 165862 165700 (ep153 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep155 := nat_lit 5842937154091938779856542482531378745671507149391017528353470315968142270720

noncomputable def ep156 := nat_lit 15299512062996621677651438814011894512249187017225391357293015313614619566336

noncomputable def ep157 := BSN.sin_dyadic_bound_f 1097926442 1073741824 3 2 524288 165862 ep155 ep64 ep151 ep156 ep66 ep151 447441 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1097926442) qz286 0 2 ep155 ep64 ep151 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1097926442) qz287 0 2 ep156 ep66 ep151 rfl rfl rfl rfl) rfl rfl

noncomputable def ep158 := @Enclosure.Real.IsNear.sin_image qz40 qz315 Bool.false 2847705 16384 265 262144 Bool.true 447441 524288 1 82850 (@Enclosure.Real.IsNear.recentre' qz40 Bool.false 156554239469130434529 900719925474099200 334340000083100207 331400000000000000000 2847705 16384 265 262144 (ep149 rfl) rfl) (Enclosure.sfrac_false_div 2847705 16384) (BSN.sin_reduce2 qz315 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 2414365780651603394560) (@Nat.cast Real Real.instNatCast 2361183241434822606848)) 226375608064910080 72057594037927936 Bool.false 447441 524288 27 1000000000000000 165700 82850 (BSN.sin_reduce_arg_pos_rat_q2 2847705 16384 226375608064910080 72057594037927936 27 2414365780651603394560 2361183241434822606848 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 447441 524288 2414365780651603394560 2361183241434822606848 1097926442 1073741824 165862 165700 (ep157 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz316 := (@Enclosure.Real.IsNear.recentre' qz39 Bool.false 185363 524288 1 524288 185363 524288 1 524288 (ep147 rfl rfl) rfl)

noncomputable def ep159 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz39 (Real.cos qz40)) (@HMul.hMul Real Real Real qz0 qz39 (@Neg.neg Real Real.instNeg (Real.sin qz40))) Bool.true 25326702779 137438953472 2064812532733 5693408647577600 Bool.false 82939006083 274877906944 4136840264841 11386817295155200 (@Enclosure.Real.IsNear.mulLit_ft qz39 (Real.cos qz40) 185363 524288 1 524288 136633 262144 11108697 10859315200 25326702779 137438953472 2064812532733 5693408647577600 qz316 (@Enclosure.Real.IsNear.recentre' (Real.cos qz40) Bool.true 273266 524288 22217394 21718630400 136633 262144 11108697 10859315200 (ep154 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz39 (@Neg.neg Real Real.instNeg (Real.sin qz40)) 185363 524288 1 524288 447441 524288 11108697 10859315200 82939006083 274877906944 4136840264841 11386817295155200 qz316 (@Enclosure.Real.IsNear.neg (Real.sin qz40) Bool.true 447441 524288 11108697 10859315200 (@Enclosure.Real.IsNear.recentre' (Real.sin qz40) Bool.true 447441 524288 22217394 21718630400 447441 524288 11108697 10859315200 (ep158 rfl rfl) rfl)) rfl)

noncomputable def ep160 := @ep39 25326702779 137438953472 2064812532733 5693408647577600 Bool.false 82939006083 274877906944 4136840264841 11386817295155200 Bool.false 1517931421421495386112 22088809367 137438953472 19694882123539 5693408647577600 Bool.false 3170393044969498607616 46135290831 274877906944 39413903878753 11386817295155200 (ep40 (BSN.head_sum_c_succ qz5 7 8 rfl rfl) (ep145 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep146 ep159) rfl rfl

theorem EMRow23.d6 : Enclosure.Complex.IsNear qz3 Bool.false 22088809367 137438953472 19694882123539 5693408647577600 Bool.false 46135290831 274877906944 39413903878753 11386817295155200 := ep38 (BSN.head_sum_c_succ qz5 8 9 rfl rfl) (ep160 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable abbrev qz41 := (@HPow.hPow Complex Complex Complex qz273 (@Nat.cast Complex Complex.instNatCast 16) qz274)

noncomputable def ep161 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 17) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 16) qz41) Bool.false 92947171639 68719476736 1655329213103 284670432378880 Bool.true 5806503165 68719476736 6621600605377 1138681729515520

noncomputable def ep162 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 16) qz41 Bool.false 320628398481 274877906944 63284921044627 11386817295155200 Bool.true 69105188003 274877906944 63289427670377 11386817295155200 Bool.false

noncomputable abbrev qz42 := (@HPow.hPow Complex Complex Complex qz273 (@Nat.cast Complex Complex.instNatCast 15) qz274)

noncomputable def ep163 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 16) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 15) qz42) Bool.false 320628398481 274877906944 63284921044627 11386817295155200 Bool.true 69105188003 274877906944 63289427670377 11386817295155200

noncomputable def ep164 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 15) qz42 Bool.false 62633086771 68719476736 15063964457271 2846704323788800 Bool.true 57980940707 274877906944 60278410469009 11386817295155200 Bool.false

noncomputable abbrev qz43 := (@HPow.hPow Complex Complex Complex qz273 (@Nat.cast Complex Complex.instNatCast 14) qz274)

noncomputable def ep165 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 15) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 14) qz43) Bool.false 62633086771 68719476736 15063964457271 2846704323788800 Bool.true 57980940707 274877906944 60278410469009 11386817295155200

noncomputable def ep166 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 14) qz43 Bool.false 193124913505 274877906944 57125740365941 11386817295155200 Bool.true 6070528081 137438953472 14287928201329 2846704323788800 Bool.false

noncomputable abbrev qz44 := (@HPow.hPow Complex Complex Complex qz273 (@Nat.cast Complex Complex.instNatCast 13) qz274)

noncomputable def ep167 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 14) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 13) qz44) Bool.false 193124913505 274877906944 57125740365941 11386817295155200 Bool.true 6070528081 137438953472 14287928201329 2846704323788800

noncomputable def ep168 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 13) qz44 Bool.false 4312710267 8589934592 26939681240969 5693408647577600 Bool.false 20264276485 137438953472 6738254059611 1423352161894400 Bool.false

noncomputable abbrev qz45 := (@HPow.hPow Complex Complex Complex qz273 (@Nat.cast Complex Complex.instNatCast 12) qz274)

noncomputable def ep169 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 13) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 12) qz45) Bool.false 4312710267 8589934592 26939681240969 5693408647577600 Bool.false 20264276485 137438953472 6738254059611 1423352161894400

noncomputable def ep170 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 12) qz45 Bool.false 63624294957 274877906944 50496401045263 11386817295155200 Bool.false 68164123625 274877906944 50535865897113 11386817295155200 Bool.false

noncomputable abbrev qz46 := (@HPow.hPow Complex Complex Complex qz273 (@Nat.cast Complex Complex.instNatCast 11) qz274)

noncomputable def ep171 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 12) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 11) qz46) Bool.false 63624294957 274877906944 50496401045263 11386817295155200 Bool.false 68164123625 274877906944 50535865897113 11386817295155200

noncomputable def ep172 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 11) qz46 Bool.true 3143848431 274877906944 46966778641643 11386817295155200 Bool.false 4765761839 68719476736 23505436596459 5693408647577600 Bool.false

noncomputable abbrev qz47 := (@HPow.hPow Complex Complex Complex qz273 (@Nat.cast Complex Complex.instNatCast 10) qz274)

noncomputable def ep173 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 11) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 10) qz47) Bool.true 3143848431 274877906944 46966778641643 11386817295155200 Bool.false 4765761839 68719476736 23505436596459 5693408647577600

noncomputable def ep174 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 10) qz47 Bool.false 55891108809 274877906944 43275341402719 11386817295155200 Bool.true 11184711931 68719476736 21659122451197 5693408647577600 Bool.true

noncomputable abbrev qz48 := (@HPow.hPow Complex Complex Complex qz273 (@Nat.cast Complex Complex.instNatCast 9) qz274)

noncomputable def ep175 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 10) (@HAdd.hAdd Complex Complex Complex qz4 qz3 qz48) Bool.false 55891108809 274877906944 43275341402719 11386817295155200 Bool.true 11184711931 68719476736 21659122451197 5693408647577600

noncomputable def ep176 := @Enclosure.Complex.IsNear.addLitP qz3 qz48 Bool.false 22088809367 137438953472 19694882123539 5693408647577600 Bool.false 46135290831 274877906944 39413903878753 11386817295155200 Bool.false

noncomputable abbrev qz317 := (@Nat.cast Real Real.instNatCast 9)

noncomputable abbrev qz49 := (@Inv.inv Real Real.instInv (Real.sqrt qz317))

noncomputable abbrev qz318 := (Real.log (Enclosure.sfrac Bool.false 9 1))

noncomputable abbrev qz50 := (@HMul.hMul Real Real Real qz266 qz279 qz318)

noncomputable def ep177 := @Enclosure.Complex.IsNear.of_eq qz48 (Complex.mk (@HMul.hMul Real Real Real qz0 qz49 (Real.cos qz50)) (@HMul.hMul Real Real Real qz0 qz49 (@Neg.neg Real Real.instNeg (Real.sin qz50)))) Bool.false 11713490075 274877906944 3885577155641 11386817295155200 Bool.true 90874138555 274877906944 3904341023641 11386817295155200 (BSN.cpow_neg_s_mk qz16 83585 1000 9 qz17 rfl)

noncomputable abbrev qz319 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 9) qz18)

noncomputable def ep178 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz317) 1572865 524288 1 524288 87381 87382 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz317) (Real.sqrt qz319) Bool.false 1572865 524288 1 524288 (BSN.sqrt_natCast_div_one 9) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz319) Bool.false 1572865 524288 1 524288 1572865 524288 1 524288 (BSN.sqrt_enclosure 9 1 786432 786433 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep179 := BSN.log_dyadic_bound 1 17 2 1 867 262144 82850 1 1 30876 18 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 1) (BSN.artanhQ 17) 0 1 1 867 1 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep180 := @Enclosure.Real.IsNear.mulLit_ff qz16 qz318 83585 1000 0 1 9895417793173221 4503599627370496 20000000004971 1657000000000000000 165421699248476735457 900719925474099200 334340000083100207 331400000000000000000 qz21 (BSN.isNear_log_sfrac 9 1 9895417793173221 4503599627370496 20000000004971 1657000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz319) Bool.false 20752195215788806766592 9444732965739290427392 1000000000248550 82850000000000000000 9895417793173221 4503599627370496 20000000004971 1657000000000000000 (BSN.log_rat_reduce_isNear 9 1 3 18 16 30876 262144 24973259072661432 36028797018963968 82850 1000000000000000 rfl rfl rfl rfl (ep179 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep181 := nat_lit 12888868635721860430742792756244935855600992145390609037466814442932346617856

noncomputable def ep182 := nat_lit 33141773926702614104814574366766730931562051698517052091263293282991538176

noncomputable def ep183 := nat_lit 38600322359312176064018749120001274104939852332774793008217916742231056777216

noncomputable def ep184 := BSN.cos_dyadic_bound_f 1548984132 1073741824 3 2 524288 165862 ep181 ep57 ep182 ep183 ep60 ep182 67025 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1548984132) qz282 0 2 ep181 ep57 ep182 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1548984132) qz283 0 2 ep183 ep60 ep182 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz320 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 96288101) qz19)

noncomputable def ep185 := @Enclosure.Real.IsNear.cos_image qz50 qz320 Bool.false 96288101 524288 265 262144 Bool.false 67025 524288 1 82850 (@Enclosure.Real.IsNear.recentre' qz50 Bool.false 165421699248476735457 900719925474099200 334340000083100207 331400000000000000000 96288101 524288 265 262144 (ep180 rfl) rfl) (Enclosure.sfrac_false_div 96288101 524288) (BSN.cos_reduce0 qz320 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 109000068150279045906432) qz22) 226375608064910080 72057594037927936 Bool.false 67025 524288 29 1000000000000000 165700 82850 (BSN.sin_reduce_arg_pos_rat_q0 96288101 524288 226375608064910080 72057594037927936 29 109000068150279045906432 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 67025 524288 109000068150279045906432 75557863725914323419136 1548984132 1073741824 165862 165700 (ep184 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep186 := nat_lit 23173450125157986684053175301747471155336536220344282625767255362651830681600

noncomputable def ep187 := nat_lit 60638711265246732321112426003220992604373161064818379268861718713058522628096

noncomputable def ep188 := BSN.sin_dyadic_bound_f 1548984132 1073741824 3 2 524288 165862 ep186 ep64 ep182 ep187 ep66 ep182 519985 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1548984132) qz286 0 2 ep186 ep64 ep182 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1548984132) qz287 0 2 ep187 ep66 ep182 rfl rfl rfl rfl) rfl rfl

noncomputable def ep189 := @Enclosure.Real.IsNear.sin_image qz50 qz320 Bool.false 96288101 524288 265 262144 Bool.false 519985 524288 1 82850 (@Enclosure.Real.IsNear.recentre' qz50 Bool.false 165421699248476735457 900719925474099200 334340000083100207 331400000000000000000 96288101 524288 265 262144 (ep180 rfl) rfl) (Enclosure.sfrac_false_div 96288101 524288) (BSN.sin_reduce0 qz320 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 109000068150279045906432) qz22) 226375608064910080 72057594037927936 Bool.false 519985 524288 29 1000000000000000 165700 82850 (BSN.sin_reduce_arg_pos_rat_q0 96288101 524288 226375608064910080 72057594037927936 29 109000068150279045906432 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 519985 524288 109000068150279045906432 75557863725914323419136 1548984132 1073741824 165862 165700 (ep188 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz321 := (@Enclosure.Real.IsNear.recentre' qz49 Bool.false 174763 524288 1 524288 174763 524288 1 524288 (ep178 rfl rfl) rfl)

noncomputable def ep190 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz49 (Real.cos qz50)) (@HMul.hMul Real Real Real qz0 qz49 (@Neg.neg Real Real.instNeg (Real.sin qz50))) Bool.false 11713490075 274877906944 3885577155641 11386817295155200 Bool.true 90874138555 274877906944 3904341023641 11386817295155200 (@Enclosure.Real.IsNear.mulLit_ff qz49 (Real.cos qz50) 174763 524288 1 524288 67025 524288 11108697 10859315200 11713490075 274877906944 3885577155641 11386817295155200 qz321 (@Enclosure.Real.IsNear.recentre' (Real.cos qz50) Bool.false 67025 524288 22217394 21718630400 67025 524288 11108697 10859315200 (ep185 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz49 (@Neg.neg Real Real.instNeg (Real.sin qz50)) 174763 524288 1 524288 519985 524288 11108697 10859315200 90874138555 274877906944 3904341023641 11386817295155200 qz321 (@Enclosure.Real.IsNear.neg (Real.sin qz50) Bool.false 519985 524288 11108697 10859315200 (@Enclosure.Real.IsNear.recentre' (Real.sin qz50) Bool.false 519985 524288 22217394 21718630400 519985 524288 11108697 10859315200 (ep189 rfl rfl) rfl)) rfl)

noncomputable def ep191 := @ep176 11713490075 274877906944 3885577155641 11386817295155200 Bool.true 90874138555 274877906944 3904341023641 11386817295155200 Bool.false 7681615503098640334848 55891108809 274877906944 43275341402719 11386817295155200 Bool.true 12297720821459458195456 11184711931 68719476736 21659122451197 5693408647577600 EMRow23.d6 (ep177 ep190) rfl rfl

noncomputable abbrev qz322 := (@Nat.cast Real Real.instNatCast 10)

noncomputable abbrev qz51 := (@Inv.inv Real Real.instInv (Real.sqrt qz322))

noncomputable abbrev qz52 := (@HMul.hMul Real Real Real qz266 qz279 (Real.log (Enclosure.sfrac Bool.false 10 1)))

noncomputable def ep192 := @Enclosure.Complex.IsNear.of_eq qz47 (Complex.mk (@HMul.hMul Real Real Real qz0 qz51 (Real.cos qz52)) (@HMul.hMul Real Real Real qz0 qz51 (@Neg.neg Real Real.instNeg (Real.sin qz52)))) Bool.true 7379369655 34359738368 922859309731 2846704323788800 Bool.false 7975236885 34359738368 923157072631 2846704323788800 (BSN.cpow_neg_s_mk qz16 83585 1000 10 qz17 rfl)

noncomputable abbrev qz323 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 10) qz18)

noncomputable def ep193 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz322) 1657945 524288 1 524288 82897 82898 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz322) (Real.sqrt qz323) Bool.false 1657945 524288 1 524288 (BSN.sqrt_natCast_div_one 10) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz323) Bool.false 1657945 524288 1 524288 1657945 524288 1 524288 (BSN.sqrt_enclosure 10 1 828972 828973 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep194 := BSN.log_dyadic_bound 2 18 3 2 1574640 262144 82850 6528 48 58495 20 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 2) (BSN.artanhQ 18) 0 2 6528 1574640 48 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz53 := (Real.log (Enclosure.sfrac Bool.false 10 1))

noncomputable def ep195 := @Enclosure.Real.IsNear.mulLit_ff qz16 qz53 83585 1000 0 1 10369908600166117 4503599627370496 20000000004971 1657000000000000000 173353762068976977889 900719925474099200 334340000083100207 331400000000000000000 qz21 (BSN.isNear_log_sfrac 10 1 10369908600166117 4503599627370496 20000000004971 1657000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz323) Bool.false 21747274560655572598784 9444732965739290427392 1000000000248550 82850000000000000000 10369908600166117 4503599627370496 20000000004971 1657000000000000000 (BSN.log_rat_reduce_isNear 10 1 3 20 16 58495 262144 24973259072661432 36028797018963968 82850 1000000000000000 rfl rfl rfl rfl (ep194 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep196 := nat_lit 1370025992441640849338191728184065262237289418786652341889872432310752542976

noncomputable def ep197 := nat_lit 376185072936146258374449325940181753312096326930187325584018553431818496

noncomputable def ep198 := nat_lit 4109325607179050255497826285900315423205244063706096651018449259825393991936

noncomputable def ep199 := BSN.cos_dyadic_bound_f 884963166 1073741824 3 2 524288 165862 ep196 ep57 ep197 ep198 ep60 ep197 356072 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 884963166) qz282 0 2 ep196 ep57 ep197 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 884963166) qz283 0 2 ep198 ep60 ep197 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz497 := (@Nat.cast Real Real.instNatCast 262144)

noncomputable abbrev qz324 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 50452585) qz497)

noncomputable abbrev qz325 := (@Nat.cast Real Real.instNatCast 37778931862957161709568)

noncomputable def ep200 := @Enclosure.Real.IsNear.cos_image qz52 qz324 Bool.false 50452585 262144 529 524288 Bool.true 356072 524288 1 82850 (@Enclosure.Real.IsNear.recentre' qz52 Bool.false 173353762068976977889 900719925474099200 334340000083100207 331400000000000000000 50452585 262144 529 524288 (ep195 rfl) rfl) (Enclosure.sfrac_false_div 50452585 262144) (BSN.cos_reduce2 qz324 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 31136873318834692423680) qz325) 226375608064910080 72057594037927936 Bool.false 356072 524288 30 1000000000000000 165700 82850 (BSN.sin_reduce_arg_pos_rat_q2 50452585 262144 226375608064910080 72057594037927936 30 31136873318834692423680 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 356072 524288 31136873318834692423680 37778931862957161709568 884963166 1073741824 165862 165700 (ep199 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep201 := nat_lit 613339280444474922735171444587525136

noncomputable def ep202 := BSN.sin_dyadic_bound_f 884963166 1073741824 2 1 524288 165862 ep201 ep80 ep201 ep201 ep81 ep201 384824 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 884963166) qz286 0 1 ep201 ep80 ep201 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 884963166) qz287 0 1 ep201 ep81 ep201 rfl rfl rfl rfl) rfl rfl

noncomputable def ep203 := @Enclosure.Real.IsNear.sin_image qz52 qz324 Bool.false 50452585 262144 529 524288 Bool.true 384824 524288 1 82850 (@Enclosure.Real.IsNear.recentre' qz52 Bool.false 173353762068976977889 900719925474099200 334340000083100207 331400000000000000000 50452585 262144 529 524288 (ep195 rfl) rfl) (Enclosure.sfrac_false_div 50452585 262144) (BSN.sin_reduce2 qz324 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 31136873318834692423680) qz325) 226375608064910080 72057594037927936 Bool.false 384824 524288 30 1000000000000000 165700 82850 (BSN.sin_reduce_arg_pos_rat_q2 50452585 262144 226375608064910080 72057594037927936 30 31136873318834692423680 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 384824 524288 31136873318834692423680 37778931862957161709568 884963166 1073741824 165862 165700 (ep202 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz326 := (@Enclosure.Real.IsNear.recentre' qz51 Bool.false 165795 524288 1 524288 165795 524288 1 524288 (ep193 rfl rfl) rfl)

noncomputable def ep204 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz51 (Real.cos qz52)) (@HMul.hMul Real Real Real qz0 qz51 (@Neg.neg Real Real.instNeg (Real.sin qz52))) Bool.true 7379369655 34359738368 922859309731 2846704323788800 Bool.false 7975236885 34359738368 923157072631 2846704323788800 (@Enclosure.Real.IsNear.mulLit_ft qz51 (Real.cos qz52) 165795 524288 1 524288 44509 65536 22175969 21718630400 7379369655 34359738368 922859309731 2846704323788800 qz326 (@Enclosure.Real.IsNear.recentre' (Real.cos qz52) Bool.true 356072 524288 44351938 43437260800 44509 65536 22175969 21718630400 (ep200 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz51 (@Neg.neg Real Real.instNeg (Real.sin qz52)) 165795 524288 1 524288 48103 65536 22175969 21718630400 7975236885 34359738368 923157072631 2846704323788800 qz326 (@Enclosure.Real.IsNear.neg (Real.sin qz52) Bool.true 48103 65536 22175969 21718630400 (@Enclosure.Real.IsNear.recentre' (Real.sin qz52) Bool.true 384824 524288 44351938 43437260800 48103 65536 22175969 21718630400 (ep203 rfl rfl) rfl)) rfl)

noncomputable def ep205 := @ep174 7379369655 34359738368 922859309731 2846704323788800 Bool.false 7975236885 34359738368 923157072631 2846704323788800 Bool.true 108021809557807300608 3143848431 274877906944 46966778641643 11386817295155200 Bool.false 163750329912238538752 4765761839 68719476736 23505436596459 5693408647577600 (ep175 (BSN.head_sum_c_succ qz5 9 10 rfl rfl) (ep191 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep192 ep204) rfl rfl

noncomputable abbrev qz327 := (@Nat.cast Real Real.instNatCast 11)

noncomputable abbrev qz54 := (@Inv.inv Real Real.instInv (Real.sqrt qz327))

noncomputable abbrev qz55 := (@HMul.hMul Real Real Real qz266 qz279 (Real.log (Enclosure.sfrac Bool.false 11 1)))

noncomputable def ep206 := @Enclosure.Complex.IsNear.of_eq qz46 (Complex.mk (@HMul.hMul Real Real Real qz0 qz54 (Real.cos qz55)) (@HMul.hMul Real Real Real qz0 qz54 (@Neg.neg Real Real.instNeg (Real.sin qz55)))) Bool.false 16692035847 68719476736 176481120181 569340864757760 Bool.false 49101076269 274877906944 704998540839 2277363459031040 (BSN.cpow_neg_s_mk qz16 83585 1000 11 qz17 rfl)

noncomputable abbrev qz328 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 11) qz18)

noncomputable def ep207 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz327) 1738867 524288 1 524288 79039 79040 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz327) (Real.sqrt qz328) Bool.false 1738867 524288 1 524288 (BSN.sqrt_natCast_div_one 11) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz328) Bool.false 1738867 524288 1 524288 1738867 524288 1 524288 (BSN.sqrt_enclosure 11 1 869433 869434 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep208 := BSN.log_dyadic_bound 3 19 4 3 4939817505 262144 82850 41676111 10935 83480 22 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 3) (BSN.artanhQ 19) 0 3 41676111 4939817505 10935 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz56 := (Real.log (Enclosure.sfrac Bool.false 11 1))

noncomputable def ep209 := @Enclosure.Real.IsNear.mulLit_ff qz16 qz56 83585 1000 0 1 10799147631728357 4503599627370496 20000000004971 1657000000000000000 180529350959602943969 900719925474099200 334340000083100207 331400000000000000000 qz21 (BSN.isNear_log_sfrac 11 1 10799147631728357 4503599627370496 20000000004971 1657000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz328) Bool.false 22647454054174387339264 9444732965739290427392 1000000000248550 82850000000000000000 10799147631728357 4503599627370496 20000000004971 1657000000000000000 (BSN.log_rat_reduce_isNear 11 1 3 22 16 83480 262144 24973259072661432 36028797018963968 82850 1000000000000000 rfl rfl rfl rfl (ep208 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep210 := nat_lit 4114410567713536365472771053684246669617573894075167212353817726743750901760

noncomputable def ep211 := nat_lit 1047204785296980493501326596858834012526757046993554845217105399980752896

noncomputable def ep212 := nat_lit 10774141726740209655439207754682874593930507354025543610224885399395569238016

noncomputable def ep213 := BSN.sin_dyadic_bound_f 1005782216 1073741824 3 2 524288 165862 ep210 ep64 ep211 ep212 ep66 ep211 422372 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1005782216) qz286 0 2 ep210 ep64 ep211 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1005782216) qz287 0 2 ep212 ep66 ep211 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz329 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 13135239) qz496)

noncomputable def ep214 := @Enclosure.Real.IsNear.cos_image qz55 qz329 Bool.false 13135239 65536 265 262144 Bool.false 422372 524288 1 82850 (@Enclosure.Real.IsNear.recentre' qz55 Bool.false 180529350959602943969 900719925474099200 334340000083100207 331400000000000000000 13135239 65536 265 262144 (ep209 rfl) rfl) (Enclosure.sfrac_false_div 13135239 65536) (BSN.cos_reduce3 qz329 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 8846953938289738907648) qz310) 226375608064910080 72057594037927936 Bool.false 422372 524288 31 1000000000000000 165700 82850 (BSN.sin_reduce_arg_pos_rat_q3 13135239 65536 226375608064910080 72057594037927936 31 8846953938289738907648 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 422372 524288 8846953938289738907648 9444732965739290427392 1005782216 1073741824 165862 165700 (ep213 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep215 := nat_lit 2286249073078763305481984508312074298237552944284867809016661895035408613376

noncomputable def ep216 := nat_lit 6856652809665695955458950871742505226687605318760616317359551474306264334336

noncomputable def ep217 := BSN.cos_dyadic_bound_f 1005782216 1073741824 3 2 524288 165862 ep215 ep57 ep211 ep216 ep60 ep211 310611 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1005782216) qz282 0 2 ep215 ep57 ep211 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1005782216) qz283 0 2 ep216 ep60 ep211 rfl rfl rfl rfl) rfl rfl

noncomputable def ep218 := @Enclosure.Real.IsNear.sin_image qz55 qz329 Bool.false 13135239 65536 265 262144 Bool.true 310611 524288 1 82850 (@Enclosure.Real.IsNear.recentre' qz55 Bool.false 180529350959602943969 900719925474099200 334340000083100207 331400000000000000000 13135239 65536 265 262144 (ep209 rfl) rfl) (Enclosure.sfrac_false_div 13135239 65536) (BSN.sin_reduce3 qz329 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 8846953938289738907648) qz310) 226375608064910080 72057594037927936 Bool.false 310611 524288 31 1000000000000000 165700 82850 (BSN.sin_reduce_arg_pos_rat_q3 13135239 65536 226375608064910080 72057594037927936 31 8846953938289738907648 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 310611 524288 8846953938289738907648 9444732965739290427392 1005782216 1073741824 165862 165700 (ep217 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz330 := (@Enclosure.Real.IsNear.recentre' qz54 Bool.false 158079 524288 1 524288 158079 524288 1 524288 (ep207 rfl rfl) rfl)

noncomputable def ep219 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz54 (Real.cos qz55)) (@HMul.hMul Real Real Real qz0 qz54 (@Neg.neg Real Real.instNeg (Real.sin qz55))) Bool.false 16692035847 68719476736 176481120181 569340864757760 Bool.false 49101076269 274877906944 704998540839 2277363459031040 (@Enclosure.Real.IsNear.mulLit_ff qz54 (Real.cos qz55) 158079 524288 1 524288 105593 131072 11108697 10859315200 16692035847 68719476736 176481120181 569340864757760 qz330 (@Enclosure.Real.IsNear.recentre' (Real.cos qz55) Bool.false 422372 524288 22217394 21718630400 105593 131072 11108697 10859315200 (ep214 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz54 (@Neg.neg Real Real.instNeg (Real.sin qz55)) 158079 524288 1 524288 310611 524288 11108697 10859315200 49101076269 274877906944 704998540839 2277363459031040 qz330 (@Enclosure.Real.IsNear.neg (Real.sin qz55) Bool.true 310611 524288 11108697 10859315200 (@Enclosure.Real.IsNear.recentre' (Real.sin qz55) Bool.true 310611 524288 22217394 21718630400 310611 524288 11108697 10859315200 (ep218 rfl rfl) rfl)) rfl)

noncomputable def ep220 := @ep172 16692035847 68719476736 176481120181 569340864757760 Bool.false 49101076269 274877906944 704998540839 2277363459031040 Bool.false 4372228257141963620352 63624294957 274877906944 50496401045263 11386817295155200 Bool.false 4684202907678015488000 68164123625 274877906944 50535865897113 11386817295155200 (ep173 (BSN.head_sum_c_succ qz5 10 11 rfl rfl) (ep205 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep206 ep219) rfl rfl

noncomputable abbrev qz331 := (@Nat.cast Real Real.instNatCast 12)

noncomputable abbrev qz57 := (@Inv.inv Real Real.instInv (Real.sqrt qz331))

noncomputable abbrev qz58 := (@HMul.hMul Real Real Real qz266 qz279 (Real.log (Enclosure.sfrac Bool.false 12 1)))

noncomputable def ep221 := @Enclosure.Complex.IsNear.of_eq qz45 (Complex.mk (@HMul.hMul Real Real Real qz0 qz57 (Real.cos qz58)) (@HMul.hMul Real Real Real qz0 qz57 (@Neg.neg Real Real.instNeg (Real.sin qz58)))) Bool.false 74382433587 274877906944 135318457467 455472691806208 Bool.true 27635570655 274877906944 134806663191 455472691806208 (BSN.cpow_neg_s_mk qz16 83585 1000 12 qz17 rfl)

noncomputable abbrev qz332 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 12) qz18)

noncomputable def ep222 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz331) 1816187 524288 1 524288 75674 75675 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz331) (Real.sqrt qz332) Bool.false 1816187 524288 1 524288 (BSN.sqrt_natCast_div_one 12) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz332) Bool.false 1816187 524288 1 524288 1816187 524288 1 524288 (BSN.sqrt_enclosure 12 1 908093 908094 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep223 := BSN.log_dyadic_bound 4 20 4 3 6720000000 262144 82850 91811840 61440 106290 24 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 4) (BSN.artanhQ 20) 0 3 91811840 6720000000 61440 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz59 := (Real.log (Enclosure.sfrac Bool.false 12 1))

noncomputable def ep224 := @Enclosure.Real.IsNear.mulLit_ff qz16 qz59 83585 1000 0 1 11191020447815397 4503599627370496 20000000004971 1657000000000000000 187080288826129991649 900719925474099200 334340000083100207 331400000000000000000 qz21 (BSN.isNear_log_sfrac 12 1 11191020447815397 4503599627370496 20000000004971 1657000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz332) Bool.false 23469270914176955449344 9444732965739290427392 1000000000248550 82850000000000000000 11191020447815397 4503599627370496 20000000004971 1657000000000000000 (BSN.log_rat_reduce_isNear 12 1 3 24 16 106290 262144 24973259072661432 36028797018963968 82850 1000000000000000 rfl rfl rfl rfl (ep223 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep225 := nat_lit 21285064593277628350543346908500625

noncomputable def ep226 := BSN.cos_dyadic_bound_f 381960755 1073741824 2 1 524288 165862 ep225 ep126 ep225 ep225 ep127 ep225 491463 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 381960755) qz282 0 1 ep225 ep126 ep225 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 381960755) qz283 0 1 ep225 ep127 ep225 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz333 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 27223765) qz495)

noncomputable def ep227 := @Enclosure.Real.IsNear.cos_image qz58 qz333 Bool.false 27223765 131072 265 262144 Bool.false 491463 524288 1 82850 (@Enclosure.Real.IsNear.recentre' qz58 Bool.false 187080288826129991649 900719925474099200 334340000083100207 331400000000000000000 27223765 131072 265 262144 (ep224 rfl) rfl) (Enclosure.sfrac_false_div 27223765 131072) (BSN.cos_reduce0 qz333 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 6719524670428424437760) qz293) 226375608064910080 72057594037927936 Bool.false 491463 524288 33 1000000000000000 165700 82850 (BSN.sin_reduce_arg_pos_rat_q0 27223765 131072 226375608064910080 72057594037927936 33 6719524670428424437760 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 491463 524288 6719524670428424437760 18889465931478580854784 381960755 1073741824 165862 165700 (ep226 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep228 := BSN.sin_dyadic_bound_f 381960755 1073741824 2 1 524288 165862 ep225 ep80 ep225 ep225 ep81 ep225 182595 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 381960755) qz286 0 1 ep225 ep80 ep225 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 381960755) qz287 0 1 ep225 ep81 ep225 rfl rfl rfl rfl) rfl rfl

noncomputable def ep229 := @Enclosure.Real.IsNear.sin_image qz58 qz333 Bool.false 27223765 131072 265 262144 Bool.false 182595 524288 1 82850 (@Enclosure.Real.IsNear.recentre' qz58 Bool.false 187080288826129991649 900719925474099200 334340000083100207 331400000000000000000 27223765 131072 265 262144 (ep224 rfl) rfl) (Enclosure.sfrac_false_div 27223765 131072) (BSN.sin_reduce0 qz333 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 6719524670428424437760) qz293) 226375608064910080 72057594037927936 Bool.false 182595 524288 33 1000000000000000 165700 82850 (BSN.sin_reduce_arg_pos_rat_q0 27223765 131072 226375608064910080 72057594037927936 33 6719524670428424437760 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 182595 524288 6719524670428424437760 18889465931478580854784 381960755 1073741824 165862 165700 (ep228 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz334 := (@Enclosure.Real.IsNear.recentre' qz57 Bool.false 151349 524288 1 524288 151349 524288 1 524288 (ep222 rfl rfl) rfl)

noncomputable def ep230 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz57 (Real.cos qz58)) (@HMul.hMul Real Real Real qz0 qz57 (@Neg.neg Real Real.instNeg (Real.sin qz58))) Bool.false 74382433587 274877906944 135318457467 455472691806208 Bool.true 27635570655 274877906944 134806663191 455472691806208 (@Enclosure.Real.IsNear.mulLit_ff qz57 (Real.cos qz58) 151349 524288 1 524288 491463 524288 11108697 10859315200 74382433587 274877906944 135318457467 455472691806208 qz334 (@Enclosure.Real.IsNear.recentre' (Real.cos qz58) Bool.false 491463 524288 22217394 21718630400 491463 524288 11108697 10859315200 (ep227 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz57 (@Neg.neg Real Real.instNeg (Real.sin qz58)) 151349 524288 1 524288 182595 524288 11108697 10859315200 27635570655 274877906944 134806663191 455472691806208 qz334 (@Enclosure.Real.IsNear.neg (Real.sin qz58) Bool.false 182595 524288 11108697 10859315200 (@Enclosure.Real.IsNear.recentre' (Real.sin qz58) Bool.false 182595 524288 22217394 21718630400 182595 524288 11108697 10859315200 (ep229 rfl rfl) rfl)) rfl)

noncomputable def ep231 := @ep170 74382433587 274877906944 135318457467 455472691806208 Bool.true 27635570655 274877906944 134806663191 455472691806208 Bool.false 37935000686363500609536 4312710267 8589934592 26939681240969 5693408647577600 Bool.false 11140403811862634823680 20264276485 137438953472 6738254059611 1423352161894400 (ep171 (BSN.head_sum_c_succ qz5 11 12 rfl rfl) (ep220 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep221 ep230) rfl rfl

noncomputable abbrev qz335 := (@Nat.cast Real Real.instNatCast 13)

noncomputable abbrev qz60 := (@Inv.inv Real Real.instInv (Real.sqrt qz335))

noncomputable abbrev qz61 := (@HMul.hMul Real Real Real qz266 qz279 (Real.log (Enclosure.sfrac Bool.false 13 1)))

noncomputable def ep232 := @Enclosure.Complex.IsNear.of_eq qz44 (Complex.mk (@HMul.hMul Real Real Real qz0 qz60 (Real.cos qz61)) (@HMul.hMul Real Real Real qz0 qz60 (@Neg.neg Real Real.instNeg (Real.sin qz61)))) Bool.false 55118184961 274877906944 3246377884003 11386817295155200 Bool.true 13167402283 68719476736 811420082107 2846704323788800 (BSN.cpow_neg_s_mk qz16 83585 1000 13 qz17 rfl)

noncomputable abbrev qz336 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 13) qz18)

noncomputable def ep233 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz335) 1890347 524288 1 524288 72705 72706 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz335) (Real.sqrt qz336) Bool.false 1890347 524288 1 524288 (BSN.sqrt_natCast_div_one 13) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz336) Bool.false 1890347 524288 1 524288 1890347 524288 1 524288 (BSN.sqrt_enclosure 13 1 945173 945174 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep234 := BSN.log_dyadic_bound 5 21 5 4 35742602096145 262144 82850 699352521000 41015625 127272 26 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 5) (BSN.artanhQ 21) 0 4 699352521000 35742602096145 41015625 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz62 := (Real.log (Enclosure.sfrac Bool.false 13 1))

noncomputable def ep235 := @Enclosure.Real.IsNear.mulLit_ff qz16 qz62 83585 1000 0 1 11551488463034085 4503599627370496 20000000004971 1657000000000000000 38621246527308159789 180143985094819840 334340000083100207 331400000000000000000 qz21 (BSN.isNear_log_sfrac 13 1 11551488463034085 4503599627370496 20000000004971 1657000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz336) Bool.false 24225227133228857425920 9444732965739290427392 1000000000248550 82850000000000000000 11551488463034085 4503599627370496 20000000004971 1657000000000000000 (BSN.log_rat_reduce_isNear 13 1 3 26 16 127272 262144 24973259072661432 36028797018963968 82850 1000000000000000 rfl rfl rfl rfl (ep234 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep236 := nat_lit 1004561717052675922365480935219751148403079421382059584559443754301827413121

noncomputable def ep237 := nat_lit 202283660148735913840490160679147191336763798899528846192455367011955841

noncomputable def ep238 := nat_lit 3013280583837730295268761825337895150826564736548379695985946352171458327681

noncomputable def ep239 := BSN.cos_dyadic_bound_f 818926831 1073741824 3 2 524288 165862 ep236 ep57 ep237 ep238 ep60 ep237 379051 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 818926831) qz282 0 2 ep236 ep57 ep237 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 818926831) qz283 0 2 ep238 ep60 ep237 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz337 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 112402621) qz19)

noncomputable def ep240 := @Enclosure.Real.IsNear.cos_image qz61 qz337 Bool.false 112402621 524288 265 262144 Bool.false 379051 524288 1 82850 (@Enclosure.Real.IsNear.recentre' qz61 Bool.false 38621246527308159789 180143985094819840 334340000083100207 331400000000000000000 112402621 524288 265 262144 (ep235 rfl) rfl) (Enclosure.sfrac_false_div 112402621 524288) (BSN.cos_reduce0 qz337 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 57626852679708491907072) qz22) 226375608064910080 72057594037927936 Bool.false 379051 524288 34 1000000000000000 165700 82850 (BSN.sin_reduce_arg_pos_rat_q0 112402621 524288 226375608064910080 72057594037927936 34 57626852679708491907072 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 379051 524288 57626852679708491907072 75557863725914323419136 818926831 1073741824 165862 165700 (ep239 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep241 := nat_lit 449759558151614954470298401373958721

noncomputable def ep242 := BSN.sin_dyadic_bound_f 818926831 1073741824 2 1 524288 165862 ep241 ep80 ep241 ep241 ep81 ep241 362212 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 818926831) qz286 0 1 ep241 ep80 ep241 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 818926831) qz287 0 1 ep241 ep81 ep241 rfl rfl rfl rfl) rfl rfl

noncomputable def ep243 := @Enclosure.Real.IsNear.sin_image qz61 qz337 Bool.false 112402621 524288 265 262144 Bool.false 362212 524288 1 82850 (@Enclosure.Real.IsNear.recentre' qz61 Bool.false 38621246527308159789 180143985094819840 334340000083100207 331400000000000000000 112402621 524288 265 262144 (ep235 rfl) rfl) (Enclosure.sfrac_false_div 112402621 524288) (BSN.sin_reduce0 qz337 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 57626852679708491907072) qz22) 226375608064910080 72057594037927936 Bool.false 362212 524288 34 1000000000000000 165700 82850 (BSN.sin_reduce_arg_pos_rat_q0 112402621 524288 226375608064910080 72057594037927936 34 57626852679708491907072 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 362212 524288 57626852679708491907072 75557863725914323419136 818926831 1073741824 165862 165700 (ep242 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz338 := (@Enclosure.Real.IsNear.recentre' qz60 Bool.false 145411 524288 1 524288 145411 524288 1 524288 (ep233 rfl rfl) rfl)

noncomputable def ep244 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz60 (Real.cos qz61)) (@HMul.hMul Real Real Real qz0 qz60 (@Neg.neg Real Real.instNeg (Real.sin qz61))) Bool.false 55118184961 274877906944 3246377884003 11386817295155200 Bool.true 13167402283 68719476736 811420082107 2846704323788800 (@Enclosure.Real.IsNear.mulLit_ff qz60 (Real.cos qz61) 145411 524288 1 524288 379051 524288 11108697 10859315200 55118184961 274877906944 3246377884003 11386817295155200 qz338 (@Enclosure.Real.IsNear.recentre' (Real.cos qz61) Bool.false 379051 524288 22217394 21718630400 379051 524288 11108697 10859315200 (ep240 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz60 (@Neg.neg Real Real.instNeg (Real.sin qz61)) 145411 524288 1 524288 90553 131072 11108697 10859315200 13167402283 68719476736 811420082107 2846704323788800 qz338 (@Enclosure.Real.IsNear.neg (Real.sin qz61) Bool.false 90553 131072 11108697 10859315200 (@Enclosure.Real.IsNear.recentre' (Real.sin qz61) Bool.false 362212 524288 22217394 21718630400 90553 131072 11108697 10859315200 (ep243 rfl rfl) rfl)) rfl)

noncomputable def ep245 := @ep168 55118184961 274877906944 3246377884003 11386817295155200 Bool.true 13167402283 68719476736 811420082107 2846704323788800 Bool.false 1658930375093607464960 193124913505 274877906944 57125740365941 11386817295155200 Bool.true 417163513237514223616 6070528081 137438953472 14287928201329 2846704323788800 (ep169 (BSN.head_sum_c_succ qz5 12 13 rfl rfl) (ep231 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep232 ep244) rfl rfl

noncomputable abbrev qz339 := (@Nat.cast Real Real.instNatCast 14)

noncomputable abbrev qz63 := (@Inv.inv Real Real.instInv (Real.sqrt qz339))

noncomputable abbrev qz64 := (@HMul.hMul Real Real Real qz266 qz279 (Real.log (Enclosure.sfrac Bool.false 14 1)))

noncomputable def ep246 := @Enclosure.Complex.IsNear.of_eq qz43 (Complex.mk (@HMul.hMul Real Real Real qz0 qz63 (Real.cos qz64)) (@HMul.hMul Real Real Real qz0 qz63 (@Neg.neg Real Real.instNeg (Real.sin qz64)))) Bool.false 57407433579 274877906944 3130117463143 11386817295155200 Bool.true 45839884545 274877906944 3126697663693 11386817295155200 (BSN.cpow_neg_s_mk qz16 83585 1000 14 qz17 rfl)

noncomputable abbrev qz340 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 14) qz18)

noncomputable def ep247 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz339) 1961707 524288 1 524288 70060 70061 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz339) (Real.sqrt qz340) Bool.false 1961707 524288 1 524288 (BSN.sqrt_natCast_div_one 14) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz340) Bool.false 1961707 524288 1 524288 1961707 524288 1 524288 (BSN.sqrt_enclosure 14 1 980853 980854 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep248 := BSN.log_dyadic_bound 6 22 5 4 51857700491520 262144 82850 1346332575744 176359680 146699 28 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 6) (BSN.artanhQ 22) 0 4 1346332575744 51857700491520 176359680 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz65 := (Real.log (Enclosure.sfrac Bool.false 14 1))

noncomputable def ep249 := @Enclosure.Real.IsNear.mulLit_ff qz16 qz65 83585 1000 0 1 11885241781671653 4503599627370496 20000000004971 1657000000000000000 198685586864205023201 900719925474099200 334340000083100207 331400000000000000000 qz21 (BSN.isNear_log_sfrac 14 1 11885241781671653 4503599627370496 20000000004971 1657000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz340) Bool.false 24925158572916270432256 9444732965739290427392 1000000000248550 82850000000000000000 11885241781671653 4503599627370496 20000000004971 1657000000000000000 (BSN.log_rat_reduce_isNear 14 1 3 28 16 146699 262144 24973259072661432 36028797018963968 82850 1000000000000000 rfl rfl rfl rfl (ep248 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep250 := nat_lit 274025445378500067617007087228660496

noncomputable def ep251 := BSN.cos_dyadic_bound_f 723515306 1073741824 2 1 524288 165862 ep250 ep126 ep250 ep250 ep127 ep250 409699 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 723515306) qz282 0 1 ep250 ep126 ep250 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 723515306) qz283 0 1 ep250 ep127 ep250 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz341 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 14456279) qz496)

noncomputable def ep252 := @Enclosure.Real.IsNear.cos_image qz64 qz341 Bool.false 14456279 65536 265 262144 Bool.false 409699 524288 1 82850 (@Enclosure.Real.IsNear.recentre' qz64 Bool.false 198685586864205023201 900719925474099200 334340000083100207 331400000000000000000 14456279 65536 265 262144 (ep249 rfl) rfl) (Enclosure.sfrac_false_div 14456279 65536) (BSN.cos_reduce0 qz341 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 6364107942173069017088) qz310) 226375608064910080 72057594037927936 Bool.false 409699 524288 35 1000000000000000 165700 82850 (BSN.sin_reduce_arg_pos_rat_q0 14456279 65536 226375608064910080 72057594037927936 35 6364107942173069017088 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 409699 524288 6364107942173069017088 9444732965739290427392 723515306 1073741824 165862 165700 (ep251 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep253 := BSN.sin_dyadic_bound_f 723515306 1073741824 2 1 524288 165862 ep250 ep80 ep250 ep250 ep81 ep250 327145 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 723515306) qz286 0 1 ep250 ep80 ep250 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 723515306) qz287 0 1 ep250 ep81 ep250 rfl rfl rfl rfl) rfl rfl

noncomputable def ep254 := @Enclosure.Real.IsNear.sin_image qz64 qz341 Bool.false 14456279 65536 265 262144 Bool.false 327145 524288 1 82850 (@Enclosure.Real.IsNear.recentre' qz64 Bool.false 198685586864205023201 900719925474099200 334340000083100207 331400000000000000000 14456279 65536 265 262144 (ep249 rfl) rfl) (Enclosure.sfrac_false_div 14456279 65536) (BSN.sin_reduce0 qz341 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 6364107942173069017088) qz310) 226375608064910080 72057594037927936 Bool.false 327145 524288 35 1000000000000000 165700 82850 (BSN.sin_reduce_arg_pos_rat_q0 14456279 65536 226375608064910080 72057594037927936 35 6364107942173069017088 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 327145 524288 6364107942173069017088 9444732965739290427392 723515306 1073741824 165862 165700 (ep253 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz342 := (@Enclosure.Real.IsNear.recentre' qz63 Bool.false 140121 524288 1 524288 140121 524288 1 524288 (ep247 rfl rfl) rfl)

noncomputable def ep255 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz63 (Real.cos qz64)) (@HMul.hMul Real Real Real qz0 qz63 (@Neg.neg Real Real.instNeg (Real.sin qz64))) Bool.false 57407433579 274877906944 3130117463143 11386817295155200 Bool.true 45839884545 274877906944 3126697663693 11386817295155200 (@Enclosure.Real.IsNear.mulLit_ff qz63 (Real.cos qz64) 140121 524288 1 524288 409699 524288 11108697 10859315200 57407433579 274877906944 3130117463143 11386817295155200 qz342 (@Enclosure.Real.IsNear.recentre' (Real.cos qz64) Bool.false 409699 524288 22217394 21718630400 409699 524288 11108697 10859315200 (ep252 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz63 (@Neg.neg Real Real.instNeg (Real.sin qz64)) 140121 524288 1 524288 327145 524288 11108697 10859315200 45839884545 274877906944 3126697663693 11386817295155200 qz342 (@Enclosure.Real.IsNear.neg (Real.sin qz64) Bool.false 327145 524288 11108697 10859315200 (@Enclosure.Real.IsNear.recentre' (Real.sin qz64) Bool.false 327145 524288 22217394 21718630400 327145 524288 11108697 10859315200 (ep254 rfl rfl) rfl)) rfl)

noncomputable def ep256 := @ep166 57407433579 274877906944 3130117463143 11386817295155200 Bool.true 45839884545 274877906944 3126697663693 11386817295155200 Bool.false 68865807188217661751296 62633086771 68719476736 15063964457271 2846704323788800 Bool.true 7968839812092163784704 57980940707 274877906944 60278410469009 11386817295155200 (ep167 (BSN.head_sum_c_succ qz5 13 14 rfl rfl) (ep245 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep246 ep255) rfl rfl

noncomputable abbrev qz343 := (@Nat.cast Real Real.instNatCast 15)

noncomputable abbrev qz66 := (@Inv.inv Real Real.instInv (Real.sqrt qz343))

noncomputable abbrev qz67 := (@HMul.hMul Real Real Real qz266 qz279 (Real.log (Enclosure.sfrac Bool.false 15 1)))

noncomputable def ep257 := @Enclosure.Complex.IsNear.of_eq qz42 (Complex.mk (@HMul.hMul Real Real Real qz0 qz66 (Real.cos qz67)) (@HMul.hMul Real Real Real qz0 qz66 (@Neg.neg Real Real.instNeg (Real.sin qz67)))) Bool.false 70096051397 274877906944 3029063215543 11386817295155200 Bool.true 43454091 1073741824 376377150171 1423352161894400 (BSN.cpow_neg_s_mk qz16 83585 1000 15 qz17 rfl)

noncomputable abbrev qz344 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 15) qz18)

noncomputable def ep258 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz343) 2030559 524288 1 524288 67685 67686 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz343) (Real.sqrt qz344) Bool.false 2030559 524288 1 524288 (BSN.sqrt_natCast_div_one 15) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz344) Bool.false 2030559 524288 1 524288 2030559 524288 1 524288 (BSN.sqrt_enclosure 15 1 1015279 1015280 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep259 := BSN.log_dyadic_bound 7 23 6 5 430628584065881355 262144 82850 14087658153505881 266939110305 164785 30 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 7) (BSN.artanhQ 23) 0 5 14087658153505881 430628584065881355 266939110305 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz68 := (Real.log (Enclosure.sfrac Bool.false 15 1))

noncomputable def ep260 := @Enclosure.Real.IsNear.mulLit_ff qz16 qz68 83585 1000 0 1 12195956895733477 4503599627370496 20000000004971 1657000000000000000 203879811425976535009 900719925474099200 334340000083100207 331400000000000000000 qz21 (BSN.isNear_log_sfrac 15 1 12195956895733477 4503599627370496 20000000004971 1657000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz344) Bool.false 25576775395801252757504 9444732965739290427392 1000000000248550 82850000000000000000 12195956895733477 4503599627370496 20000000004971 1657000000000000000 (BSN.log_rat_reduce_isNear 15 1 3 30 16 164785 262144 24973259072661432 36028797018963968 82850 1000000000000000 rfl rfl rfl rfl (ep259 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep261 := nat_lit 815642490510377253696911048010000

noncomputable def ep262 := BSN.cos_dyadic_bound_f 168995430 1073741824 2 1 524288 165862 ep261 ep126 ep261 ep261 ep127 ep261 517807 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 168995430) qz282 0 1 ep261 ep126 ep261 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 168995430) qz283 0 1 ep261 ep127 ep261 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz345 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 118673669) qz19)

noncomputable def ep263 := @Enclosure.Real.IsNear.cos_image qz67 qz345 Bool.false 118673669 524288 265 262144 Bool.false 517807 524288 1 82850 (@Enclosure.Real.IsNear.recentre' qz67 Bool.false 203879811425976535009 900719925474099200 334340000083100207 331400000000000000000 118673669 524288 265 262144 (ep260 rfl) rfl) (Enclosure.sfrac_false_div 118673669 524288) (BSN.cos_reduce0 qz345 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 11891996223343698116608) qz22) 226375608064910080 72057594037927936 Bool.false 517807 524288 36 1000000000000000 165700 82850 (BSN.sin_reduce_arg_pos_rat_q0 118673669 524288 226375608064910080 72057594037927936 36 11891996223343698116608 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 517807 524288 11891996223343698116608 75557863725914323419136 168995430 1073741824 165862 165700 (ep262 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep264 := BSN.sin_dyadic_bound_f 168995430 1073741824 1 0 524288 165862 0 1 1 0 1 1 82176 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 168995430) qz286 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 168995430) qz287 0 0 rfl) rfl rfl

noncomputable def ep265 := @Enclosure.Real.IsNear.sin_image qz67 qz345 Bool.false 118673669 524288 265 262144 Bool.false 82176 524288 1 82850 (@Enclosure.Real.IsNear.recentre' qz67 Bool.false 203879811425976535009 900719925474099200 334340000083100207 331400000000000000000 118673669 524288 265 262144 (ep260 rfl) rfl) (Enclosure.sfrac_false_div 118673669 524288) (BSN.sin_reduce0 qz345 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 11891996223343698116608) qz22) 226375608064910080 72057594037927936 Bool.false 82176 524288 36 1000000000000000 165700 82850 (BSN.sin_reduce_arg_pos_rat_q0 118673669 524288 226375608064910080 72057594037927936 36 11891996223343698116608 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 82176 524288 11891996223343698116608 75557863725914323419136 168995430 1073741824 165862 165700 (ep264 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz346 := (@Enclosure.Real.IsNear.recentre' qz66 Bool.false 135371 524288 1 524288 135371 524288 1 524288 (ep258 rfl rfl) rfl)

noncomputable def ep266 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz66 (Real.cos qz67)) (@HMul.hMul Real Real Real qz0 qz66 (@Neg.neg Real Real.instNeg (Real.sin qz67))) Bool.false 70096051397 274877906944 3029063215543 11386817295155200 Bool.true 43454091 1073741824 376377150171 1423352161894400 (@Enclosure.Real.IsNear.mulLit_ff qz66 (Real.cos qz67) 135371 524288 1 524288 517807 524288 11108697 10859315200 70096051397 274877906944 3029063215543 11386817295155200 qz346 (@Enclosure.Real.IsNear.recentre' (Real.cos qz67) Bool.false 517807 524288 22217394 21718630400 517807 524288 11108697 10859315200 (ep263 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz66 (@Neg.neg Real Real.instNeg (Real.sin qz67)) 135371 524288 1 524288 321 2048 11108697 10859315200 43454091 1073741824 376377150171 1423352161894400 qz346 (@Enclosure.Real.IsNear.neg (Real.sin qz67) Bool.false 321 2048 11108697 10859315200 (@Enclosure.Real.IsNear.recentre' (Real.sin qz67) Bool.false 82176 524288 22217394 21718630400 321 2048 11108697 10859315200 (ep265 rfl rfl) rfl)) rfl)

noncomputable def ep267 := @ep164 70096051397 274877906944 3029063215543 11386817295155200 Bool.true 43454091 1073741824 376377150171 1423352161894400 Bool.false 22033415770316017238016 320628398481 274877906944 63284921044627 11386817295155200 Bool.true 74201130614204137472 69105188003 274877906944 63289427670377 11386817295155200 (ep165 (BSN.head_sum_c_succ qz5 14 15 rfl rfl) (ep256 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep257 ep266) rfl rfl

noncomputable abbrev qz347 := (@Nat.cast Real Real.instNatCast 16)

noncomputable abbrev qz69 := (@Inv.inv Real Real.instInv (Real.sqrt qz347))

noncomputable abbrev qz70 := (@HMul.hMul Real Real Real qz266 qz279 (Real.log (Enclosure.sfrac Bool.false 16 1)))

noncomputable def ep268 := @Enclosure.Complex.IsNear.of_eq qz41 (Complex.mk (@HMul.hMul Real Real Real qz0 qz69 (Real.cos qz70)) (@HMul.hMul Real Real Real qz0 qz69 (@Neg.neg Real Real.instNeg (Real.sin qz70)))) Bool.false 51160288075 274877906944 2928247479493 11386817295155200 Bool.false 45879175343 274877906944 2926578383393 11386817295155200 (BSN.cpow_neg_s_mk qz16 83585 1000 16 qz17 rfl)

noncomputable abbrev qz348 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 16) qz18)

noncomputable def ep269 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz347) 2097153 524288 1 524288 65535 65536 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz347) (Real.sqrt qz348) Bool.false 2097153 524288 1 524288 (BSN.sqrt_natCast_div_one 16) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz348) Bool.false 2097153 524288 1 524288 2097153 524288 1 524288 (BSN.sqrt_enclosure 16 1 1048576 1048577 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep270 := BSN.log_dyadic_bound 0 32 1 0 1 262144 82850 0 1 0 32 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 0) (BSN.artanhQ 32) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz71 := (Real.log (Enclosure.sfrac Bool.false 16 1))

noncomputable def ep271 := @Enclosure.Real.IsNear.mulLit_ff qz16 qz71 83585 1000 0 1 3121657384082679 1125899906842624 5000000001657 414250000000000000 52184746489710144843 225179981368524800 83585000027700069 82850000000000000000 qz21 (BSN.isNear_log_sfrac 16 1 3121657384082679 1125899906842624 5000000001657 414250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz348) Bool.false 26186360105375033720832 9444732965739290427392 1000000000331400 82850000000000000000 3121657384082679 1125899906842624 5000000001657 414250000000000000 (BSN.log_rat_reduce_isNear 16 1 4 32 32 0 262144 24973259072661432 36028797018963968 82850 1000000000000000 rfl rfl rfl rfl (ep270 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep272 := nat_lit 661053864416683223319411272814239121

noncomputable def ep273 := BSN.sin_dyadic_bound_f 901694067 1073741824 2 1 524288 165862 ep272 ep80 ep272 ep272 ep81 ep272 390325 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 901694067) qz286 0 1 ep272 ep80 ep272 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 901694067) qz287 0 1 ep272 ep81 ep272 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz349 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 121502081) qz19)

noncomputable def ep274 := @Enclosure.Real.IsNear.cos_image qz70 qz349 Bool.false 121502081 524288 265 262144 Bool.false 390325 524288 1 82850 (@Enclosure.Real.IsNear.recentre' qz70 Bool.false 52184746489710144843 225179981368524800 83585000027700069 82850000000000000000 121502081 524288 265 262144 (ep271 rfl) rfl) (Enclosure.sfrac_false_div 121502081 524288) (BSN.cos_reduce3 qz349 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 63451079155944628682752) qz22) 226375608064910080 72057594037927936 Bool.false 390325 524288 36 1000000000000000 165700 82850 (BSN.sin_reduce_arg_pos_rat_q3 121502081 524288 226375608064910080 72057594037927936 36 63451079155944628682752 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 390325 524288 63451079155944628682752 75557863725914323419136 901694067 1073741824 165862 165700 (ep273 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep275 := nat_lit 1476638381763155309539383097034568956144002823987620253667698250444287781921

noncomputable def ep276 := nat_lit 436992211660230605852168364793876216653589523662746257364529170166852641

noncomputable def ep277 := nat_lit 4429041160866145467406444954374119115998701292915535268488365692992529640481

noncomputable def ep278 := BSN.cos_dyadic_bound_f 901694067 1073741824 3 2 524288 165862 ep275 ep57 ep276 ep277 ep60 ep276 350033 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 901694067) qz282 0 2 ep275 ep57 ep276 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 901694067) qz283 0 2 ep277 ep60 ep276 rfl rfl rfl rfl) rfl rfl

noncomputable def ep279 := @Enclosure.Real.IsNear.sin_image qz70 qz349 Bool.false 121502081 524288 265 262144 Bool.true 350033 524288 1 82850 (@Enclosure.Real.IsNear.recentre' qz70 Bool.false 52184746489710144843 225179981368524800 83585000027700069 82850000000000000000 121502081 524288 265 262144 (ep271 rfl) rfl) (Enclosure.sfrac_false_div 121502081 524288) (BSN.sin_reduce3 qz349 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 63451079155944628682752) qz22) 226375608064910080 72057594037927936 Bool.false 350033 524288 36 1000000000000000 165700 82850 (BSN.sin_reduce_arg_pos_rat_q3 121502081 524288 226375608064910080 72057594037927936 36 63451079155944628682752 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 350033 524288 63451079155944628682752 75557863725914323419136 901694067 1073741824 165862 165700 (ep278 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz350 := (@Enclosure.Real.IsNear.recentre' qz69 Bool.false 131071 524288 1 524288 131071 524288 1 524288 (ep269 rfl rfl) rfl)

noncomputable def ep280 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz69 (Real.cos qz70)) (@HMul.hMul Real Real Real qz0 qz69 (@Neg.neg Real Real.instNeg (Real.sin qz70))) Bool.false 51160288075 274877906944 2928247479493 11386817295155200 Bool.false 45879175343 274877906944 2926578383393 11386817295155200 (@Enclosure.Real.IsNear.mulLit_ff qz69 (Real.cos qz70) 131071 524288 1 524288 390325 524288 11108697 10859315200 51160288075 274877906944 2928247479493 11386817295155200 qz350 (@Enclosure.Real.IsNear.recentre' (Real.cos qz70) Bool.false 390325 524288 22217394 21718630400 390325 524288 11108697 10859315200 (ep274 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz69 (@Neg.neg Real Real.instNeg (Real.sin qz70)) 131071 524288 1 524288 350033 524288 11108697 10859315200 45879175343 274877906944 2926578383393 11386817295155200 qz350 (@Enclosure.Real.IsNear.neg (Real.sin qz70) Bool.true 350033 524288 11108697 10859315200 (@Enclosure.Real.IsNear.recentre' (Real.sin qz70) Bool.true 350033 524288 22217394 21718630400 350033 524288 11108697 10859315200 (ep279 rfl rfl) rfl)) rfl)

noncomputable def ep281 := @ep162 51160288075 274877906944 2928247479493 11386817295155200 Bool.false 45879175343 274877906944 2926578383393 11386817295155200 Bool.false 102196495985972151844864 92947171639 68719476736 1655329213103 284670432378880 Bool.true 6384317746635645911040 5806503165 68719476736 6621600605377 1138681729515520 (ep163 (BSN.head_sum_c_succ qz5 15 16 rfl rfl) (ep267 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep268 ep280) rfl rfl

theorem EMRow23.d7 : Enclosure.Complex.IsNear (BSN.headSumC qz5 17) Bool.false 92947171639 68719476736 1655329213103 284670432378880 Bool.true 5806503165 68719476736 6621600605377 1138681729515520 := ep161 (BSN.head_sum_c_succ qz5 16 17 rfl rfl) (ep281 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

theorem EMRow23.d8 : @Eq Nat (BSN.factNat (Nat.mul 2 1)) 2 := @Eq.refl Nat 2

theorem EMRow23.d9 : @Eq Nat (Nat.pow 17 1) 17 := @Eq.refl Nat 17

noncomputable def ep282 := nat_lit 2072695048567701865094778988651

noncomputable def ep283 := nat_lit 1643244325263349125560559206400

noncomputable def ep284 := nat_lit 1242463571572406483683200687169748129

noncomputable def ep285 := nat_lit 187990505767291219301925992687206400000

noncomputable abbrev qz517 := (@instHMul Complex Complex.instMul)

noncomputable abbrev qz498 := qz517

noncomputable abbrev qz351 := qz498

noncomputable abbrev qz72 := qz351

noncomputable abbrev qz499 := (@instHSub Complex Complex.instSub)

noncomputable abbrev qz352 := qz499

noncomputable abbrev qz73 := qz352

noncomputable abbrev qz518 := (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (4 : Complex))

noncomputable abbrev qz519 := (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid))

noncomputable abbrev qz500 := (@HAdd.hAdd Complex Complex Complex qz515 (@HAdd.hAdd Complex Complex Complex qz515 qz518 (@HMul.hMul Complex Complex Complex qz517 Complex.I (@HDiv.hDiv Complex Complex Complex qz519 (↑qz516) (2 : Complex)))) (@Nat.cast Complex Complex.instNatCast 2))

noncomputable abbrev qz353 := qz500

noncomputable abbrev qz74 := (Complex.Stirling.logGammaStirling 1 qz353)

noncomputable abbrev qz501 := (@HAdd.hAdd Complex Complex Complex qz515 qz518 (@HMul.hMul Complex Complex Complex qz517 Complex.I (@HDiv.hDiv Complex Complex Complex qz519 (↑qz516) (2 : Complex))))

noncomputable abbrev qz354 := qz501

noncomputable abbrev qz75 := qz354

noncomputable abbrev qz76 := (@HMul.hMul Real Real Real qz266 (@HDiv.hDiv Real Real Real qz269 qz279 (2 : Real)) (Real.log Real.pi))

noncomputable abbrev qz355 := (@instHSub Real Real.instSub)

noncomputable def ep286 := Complex.re (@HMul.hMul Complex Complex Complex qz72 (Complex.exp (@HMul.hMul Complex Complex Complex qz72 Complex.I ↑(@HSub.hSub Real Real Real qz355 (Complex.im (@HSub.hSub Complex Complex Complex qz73 qz74 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz75 (@Nat.cast Complex Complex.instNatCast j))))) qz76))) (zetaApproximant qz5 1 17))

noncomputable def ep287 := @Enclosure.Real.IsNear.of_eq ep286 (@HSub.hSub Real Real Real qz355 (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz355 (Complex.im (@HSub.hSub Complex Complex Complex qz73 qz74 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz75 (@Nat.cast Complex Complex.instNatCast j))))) qz76)) (Complex.re (zetaApproximant qz5 1 17))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz355 (Complex.im (@HSub.hSub Complex Complex Complex qz73 qz74 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz75 (@Nat.cast Complex Complex.instNatCast j))))) qz76)) (Complex.im (zetaApproximant qz5 1 17))))

noncomputable def ep288 := nat_lit 2072695878181471927696679332307

noncomputable def ep289 := @Enclosure.Real.IsNear.subLit_tt_n (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz355 (Complex.im (@HSub.hSub Complex Complex Complex qz73 qz74 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz75 (@Nat.cast Complex Complex.instNatCast j))))) qz76)) (Complex.re (zetaApproximant qz5 1 17))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz355 (Complex.im (@HSub.hSub Complex Complex Complex qz73 qz74 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz75 (@Nat.cast Complex Complex.instNatCast j))))) qz76)) (Complex.im (zetaApproximant qz5 1 17))) ep288

noncomputable def ep290 := nat_lit 3722833548741928701190093131492997931

noncomputable def ep291 := nat_lit 563971517301873657905777978061619200000

noncomputable def ep292 := nat_lit 205405540657918640695069900800

noncomputable def ep293 := nat_lit 569645746911343732438616252030807

noncomputable def ep294 := nat_lit 70496439662734207238222247257702400000

noncomputable def ep295 := nat_lit 425743047070039737087864530149736707309244368879574895820800

noncomputable def ep296 := @Enclosure.Real.IsNear.mulLit_tf (Real.cos (@HSub.hSub Real Real Real qz355 (Complex.im (@HSub.hSub Complex Complex Complex qz73 qz74 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz75 (@Nat.cast Complex Complex.instNatCast j))))) qz76)) (Complex.re (zetaApproximant qz5 1 17)) 524287 524288 5226347

noncomputable def ep297 := nat_lit 3953361189923595144828461

noncomputable def ep298 := nat_lit 3134239817167948008652800

noncomputable def ep299 := nat_lit 155573829191540539039069889

noncomputable def ep300 := nat_lit 25967176885236449251688448000

noncomputable def ep301 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HSub.hSub Real Real Real qz355 (Complex.im (@HSub.hSub Complex Complex Complex qz73 qz74 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz75 (@Nat.cast Complex Complex.instNatCast j))))) qz76)) Bool.true 524287 524288 10452694

noncomputable abbrev qz356 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 4323639) qz496)

noncomputable def ep302 := @Enclosure.Real.IsNear.cos_image (@HSub.hSub Real Real Real qz355 (Complex.im (@HSub.hSub Complex Complex Complex qz73 qz74 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz75 (@Nat.cast Complex Complex.instNatCast j))))) qz76) qz356 Bool.false 4323639 65536 123

noncomputable def ep303 := nat_lit 52124712960000000000000000

noncomputable def ep304 := @Enclosure.Real.IsNear.recentre' (@HSub.hSub Real Real Real qz355 (Complex.im (@HSub.hSub Complex Complex Complex qz73 qz74 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz75 (@Nat.cast Complex Complex.instNatCast j))))) qz76) Bool.false 356541852329732050757 5404319552844595200 24373250350793799246829 ep303

noncomputable def ep305 := @Enclosure.Real.IsNear.subLit_ff_p (Complex.im (@HSub.hSub Complex Complex Complex qz73 qz74 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz75 (@Nat.cast Complex Complex.instNatCast j))))) qz76 615090511523800780613 5404319552844595200 7753208950793799246829 ep303 1254126057 26214400

noncomputable def ep306 := nat_lit 9346530733712527871364300800

noncomputable def ep307 := nat_lit 21718630400000000000000000

noncomputable def ep308 := @Enclosure.Complex.IsNear.im_isNear (@HSub.hSub Complex Complex Complex qz73 qz74 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz75 (@Nat.cast Complex Complex.instNatCast j)))) Bool.true 29571422644947144361 450359962737049600 5806440353433083734871 ep307 Bool.false 615090511523800780613 5404319552844595200

noncomputable def ep309 := @Enclosure.Complex.IsNear.subLitP qz74 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz75 (@Nat.cast Complex Complex.instNatCast j))) Bool.true 26209081306550839761 450359962737049600 5675368353215897430871 ep307 Bool.false 631874769509215391813 5404319552844595200 7124063350741674533869

noncomputable def ep310 := nat_lit 66588924002299703291588545272086528

noncomputable def ep311 := nat_lit 173132587406107310709283607835312128

noncomputable abbrev qz520 := (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (2 : Complex))

noncomputable abbrev qz502 := qz520

noncomputable abbrev qz357 := (@HSub.hSub Complex Complex Complex qz499 qz500 qz502)

noncomputable abbrev qz358 := (Complex.log qz500)

noncomputable abbrev qz77 := (@HSub.hSub Complex Complex Complex qz352 (@HMul.hMul Complex Complex Complex qz351 qz357 qz358) qz353)

noncomputable abbrev qz359 := qz502

noncomputable abbrev qz78 := (@HMul.hMul Complex Complex Complex qz351 qz359 ↑(Real.log qz270))

noncomputable abbrev qz503 := qz519

noncomputable abbrev qz360 := qz503

noncomputable abbrev qz79 := qz360

noncomputable abbrev qz80 := (@instHMul Nat instMulNat)

noncomputable abbrev qz504 := (@instHPow Complex Int (@ZPow.toPow Complex (@DivInvMonoid.toZPow Complex Complex.instDivInvMonoid)))

noncomputable abbrev qz361 := qz504

noncomputable abbrev qz81 := qz361

noncomputable abbrev qz82 := qz353

noncomputable abbrev qz362 := (@OfNat.ofNat Int 1 (@instOfNat 1))

noncomputable abbrev qz83 := qz362

noncomputable abbrev qz363 := (@OfNat.ofNat Int 2 (@instOfNat 2))

noncomputable abbrev qz84 := qz363

noncomputable abbrev qz364 := (@instHSub Int Int.instSub)

noncomputable abbrev qz365 := (@instHMul Int Int.instMul)

noncomputable def ep312 := @Enclosure.Complex.IsNear.of_eq qz74 (@HAdd.hAdd Complex Complex Complex qz4 (@HAdd.hAdd Complex Complex Complex qz4 qz77 qz78) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz72 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz81 qz82 (@HSub.hSub Int Int Int qz364 qz83 (@HMul.hMul Int Int Int qz365 qz84 (@Nat.cast Int instNatCastInt k)))))) Bool.true 26209081306550839761

noncomputable def ep313 := @Enclosure.Complex.IsNear.addLitP (@HAdd.hAdd Complex Complex Complex qz4 qz77 qz78) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz72 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz81 qz82 (@HSub.hSub Int Int Int qz364 qz83 (@HMul.hMul Int Int Int qz365 qz84 (@Nat.cast Int instNatCastInt k))))) Bool.true 26209129513180932561 450359962737049600

noncomputable def ep314 := nat_lit 450268588279363229339325825024

noncomputable def ep315 := nat_lit 1085552588083847231382664459059200

noncomputable def ep316 := @ep313 346396762734611569 1325600000000000000000 Bool.false 210628504815228514327 1801439850948198400 18117000027816059 132560000000000000000 Bool.false 1838937 17179869184 3 17179869184 Bool.true 10247169943 5153960755200 16717 5153960755200 Bool.true ep314 26209081306550839761 450359962737049600 5675368353215897430871 ep307 Bool.false ep315

noncomputable def ep317 := @Enclosure.Complex.IsNear.addLitP qz77 qz78 Bool.true 26622982253901982161 450359962737049600 341340000039299069 1325600000000000000000

noncomputable def ep318 := nat_lit 3435283023551651192635392

noncomputable def ep319 := @ep317 Bool.false 210628504815228514327 1801439850948198400 18117000027816059 132560000000000000000 Bool.false 120447 131072 1 262144 Bool.false 0 1 0 1 Bool.true ep318 26209129513180932561 450359962737049600 346396762734611569 1325600000000000000000 Bool.false 210628504815228514327 210628504815228514327 1801439850948198400

noncomputable abbrev qz85 := (@HMul.hMul Complex Complex Complex qz351 qz357 qz358)

noncomputable def ep320 := @Enclosure.Complex.IsNear.subLitP qz85 qz82 Bool.true 25609672337743620561 450359962737049600 341340000039299069 1325600000000000000000 Bool.false 285915179785981095959

noncomputable def ep321 := @ep320 1801439850948198400 18117000027816059 132560000000000000000 Bool.false 9000 4000 0 1 Bool.false 167170 4000 0 1 Bool.true 106491929015607928644000 26622982253901982161 450359962737049600 341340000039299069 1325600000000000000000 Bool.false 842514019260914057308000 210628504815228514327 1801439850948198400 18117000027816059 132560000000000000000

noncomputable abbrev qz86 := qz357

noncomputable abbrev qz87 := qz358

noncomputable def ep322 := @Enclosure.Complex.IsNear.mul qz86 qz87 Bool.true 25609672337743620561 450359962737049600 341340000039299069 1325600000000000000000 Bool.false 285915179785981095959 1801439850948198400 18117000027816059

noncomputable abbrev qz88 := (Complex.re qz357)

noncomputable abbrev qz89 := (Complex.re qz358)

noncomputable abbrev qz90 := (Complex.im qz357)

noncomputable abbrev qz91 := (Complex.im qz358)

noncomputable def ep323 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 qz88 qz89) (@HMul.hMul Real Real Real qz0 qz90 qz91) 117720249362216389 18014398509481984 7000000011599 1325600000000000000 14276339285899515143 225179981368524800

noncomputable def ep324 := nat_lit 230671421594685337485187582380736512

noncomputable def ep325 := @Enclosure.Real.IsNear.mulLit_ff qz88 qz89 7000 4000 0 1 16817178480316627 4503599627370496 1000000001657 331400000000000000

noncomputable def ep326 := @Enclosure.Complex.IsNear.re_isNear qz86 Bool.false 7000 4000 0 1 Bool.false 167170 4000 0 1

noncomputable abbrev qz366 := (Enclosure.sfrac Bool.false 167170 4000)

noncomputable abbrev qz92 := qz366

noncomputable def ep327 := @Enclosure.Complex.IsNear.of_eq qz86 (Complex.mk (Enclosure.sfrac Bool.false 7000 4000) qz92) Bool.false 7000 4000 0 1 Bool.false 167170 4000 0

noncomputable abbrev qz367 := (Enclosure.sfrac Bool.false 9000 4000)

noncomputable abbrev qz93 := qz367

noncomputable abbrev qz368 := (Complex.log (Complex.mk qz93 qz92))

noncomputable def ep328 := @Enclosure.Complex.IsNear.of_eq qz87 qz368 Bool.false 16817178480316627 4503599627370496 1000000001657 331400000000000000 Bool.false 854001273308579 562949953421312 20000000001657 3314000000000000000

noncomputable def ep329 := nat_lit 14300172506964333116179481851263979617484300065875644481575260773063865450000000000000000

noncomputable def ep330 := nat_lit 341819219620439595541521268368476787262525335409117734892563401140922640000000000000000

noncomputable def ep331 := nat_lit 35452874446136267297870075375198346372037327994696135701735047985050000000000000000

noncomputable def ep332 := BSN.log_dyadic_bound 11642808900 44410808900 5 4 ep329 524288 165700 ep330 ep331 281467 56053617800 32768000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 11642808900) (BSN.artanhQ 44410808900) 0 4 ep330 ep329 ep331 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz94 := (Enclosure.sfrac Bool.false 1 2)

noncomputable abbrev qz369 := (Real.log (Enclosure.sfrac Bool.false 28026808900 16000000))

noncomputable abbrev qz370 := (Enclosure.Real.IsNear.const Bool.false 1 2)

noncomputable abbrev qz371 := (@Nat.cast Real Real.instNatCast 16000000)

noncomputable def ep333 := @Enclosure.Real.IsNear.mulLit_ff qz94 qz369 1 2 0 1 16817178480316627 2251799813685248 1000000001657 165700000000000000 16817178480316627 4503599627370496 1000000001657 331400000000000000 qz370 (BSN.isNear_log_sfrac 28026808900 16000000 16817178480316627 2251799813685248 1000000001657 165700000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 28026808900) qz371)) Bool.false 141072717937411899785216 18889465931478580854784 1000000001657000 165700000000000000000 16817178480316627 2251799813685248 1000000001657 165700000000000000 (BSN.log_rat_reduce_isNear 28026808900 16000000 10 56053617800 32768000000 281467 524288 24973259072661432 36028797018963968 165700 1000000000000000 rfl rfl rfl rfl (ep332 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep334 := BSN.arctan_dyadic_bound_f 9000 167170 1 0 524288 165700 0 1 1 0 1 1 28199 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 9000) (BSN.arctanEvenQ 167170) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 9000) (BSN.arctanOddQ 167170) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz95 := (@HMul.hMul Real Real Real qz266 (Enclosure.sfrac Bool.false 1 2) Real.pi)

noncomputable abbrev qz96 := (@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 2) Real.pi 1 2 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 qz370 BSN.pi_near_15 rfl)

noncomputable abbrev qz372 := (Real.arctan (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 9000) (@Nat.cast Real Real.instNatCast 167170)))

noncomputable def ep335 := @Enclosure.Real.IsNear.subLit_ff_p qz95 qz372 884279719003555 562949953421312 1 2000000000000000 28199 524288 1 165700 447742619580408266752 854001273308579 562949953421312 20000000001657 3314000000000000000 qz96 (ep334 rfl) rfl rfl

noncomputable abbrev qz373 := (Real.arctan (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 167170) (@Nat.cast Real Real.instNatCast 9000)))

noncomputable def ep336 := @Enclosure.Complex.IsNear.re_isNear qz87 Bool.false 16817178480316627 4503599627370496 1000000001657 331400000000000000 Bool.false 854001273308579 562949953421312 20000000001657 3314000000000000000 (ep328 (@congrArg Complex Complex qz82 (Complex.mk qz93 qz92) Complex.log (BSN.w_shift_mk qz16 Bool.false 83585 1000 2 qz17 rfl)) (@Enclosure.Complex.IsNear.of_parts qz368 Bool.false 16817178480316627 4503599627370496 1000000001657 331400000000000000 Bool.false 854001273308579 562949953421312 20000000001657 3314000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz368) (@HMul.hMul Real Real Real qz0 qz94 qz369) Bool.false 16817178480316627 4503599627370496 1000000001657 331400000000000000 (Enclosure.clog_re_eq 9000 167170 4000 28026808900 16000000 rfl rfl rfl) (ep333 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz368) qz373 Bool.false 854001273308579 562949953421312 20000000001657 3314000000000000000 (Enclosure.clog_im_eq 9000 167170 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz373 (@HSub.hSub Real Real Real qz355 qz95 qz372) Bool.false 854001273308579 562949953421312 20000000001657 3314000000000000000 (BSN.arctan_recip 167170 9000 rfl rfl) ep335))))

noncomputable def ep337 := @Enclosure.Real.IsNear.mulLit_ff qz90 qz91 167170 4000 0 1 854001273308579 562949953421312 20000000001657 3314000000000000000

noncomputable def ep338 := @Enclosure.Complex.IsNear.im_isNear qz86 Bool.false 7000 4000 0 1 Bool.false 167170 4000 0 1

noncomputable def ep339 := @Enclosure.Complex.IsNear.im_isNear qz87 Bool.false 16817178480316627 4503599627370496 1000000001657 331400000000000000 Bool.false 854001273308579 562949953421312 20000000001657 3314000000000000000 (ep328 (@congrArg Complex Complex qz82 (Complex.mk qz93 qz92) Complex.log (BSN.w_shift_mk qz16 Bool.false 83585 1000 2 qz17 rfl)) (@Enclosure.Complex.IsNear.of_parts qz368 Bool.false 16817178480316627 4503599627370496 1000000001657 331400000000000000 Bool.false 854001273308579 562949953421312 20000000001657 3314000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz368) (@HMul.hMul Real Real Real qz0 qz94 qz369) Bool.false 16817178480316627 4503599627370496 1000000001657 331400000000000000 (Enclosure.clog_re_eq 9000 167170 4000 28026808900 16000000 rfl rfl rfl) (ep333 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz368) qz373 Bool.false 854001273308579 562949953421312 20000000001657 3314000000000000000 (Enclosure.clog_im_eq 9000 167170 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz373 (@HSub.hSub Real Real Real qz355 qz95 qz372) Bool.false 854001273308579 562949953421312 20000000001657 3314000000000000000 (BSN.arctan_recip 167170 9000 rfl rfl) ep335))))

noncomputable abbrev qz374 := (Enclosure.Real.IsNear.const Bool.false 167170 4000)

noncomputable abbrev qz97 := (@ep327 1 (BSN.w_sub_half_mk qz279 Bool.false 83585 1000 2 qz281 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7000 4000) qz366 Bool.false 7000 4000 0 1 Bool.false 167170 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 7000 4000) qz374))

noncomputable def ep340 := @ep323 334340000027700069 1325600000000000000000 ep324 25609672337743620561 450359962737049600 341340000039299069 1325600000000000000000 (@ep325 117720249362216389 18014398509481984 7000000011599 1325600000000000000 (ep326 qz97) ep336 rfl) (@ep337 14276339285899515143 225179981368524800 334340000027700069 1325600000000000000000 (ep338 qz97) ep339 rfl) rfl

noncomputable def ep341 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz88 qz91) (@HMul.hMul Real Real Real qz0 qz90 qz89) 5978008913160053 2251799813685248 140000000011599 13256000000000000000 281132772655453053559 1801439850948198400

noncomputable def ep342 := nat_lit 643823748571856417019995229710712832

noncomputable def ep343 := @Enclosure.Real.IsNear.mulLit_ff qz88 qz91 7000 4000 0 1 854001273308579 562949953421312 20000000001657 3314000000000000000

noncomputable def ep344 := @Enclosure.Real.IsNear.mulLit_ff qz90 qz89 167170 4000 0 1 16817178480316627 4503599627370496 1000000001657 331400000000000000

noncomputable def ep345 := @ep341 16717000027700069 132560000000000000000 ep342 285915179785981095959 1801439850948198400 18117000027816059 132560000000000000000 (@ep343 5978008913160053 2251799813685248 140000000011599 13256000000000000000 (ep326 qz97) ep339 rfl) (@ep344 281132772655453053559 1801439850948198400 16717000027700069 132560000000000000000 (ep338 qz97) ep336 rfl) rfl

noncomputable def ep346 := @Enclosure.Complex.IsNear.of_eq qz82 (Complex.mk qz93 qz92) Bool.false 9000 4000 0 1 Bool.false 167170 4000 0 1 (BSN.w_shift_mk qz16 Bool.false 83585 1000 2 qz17 rfl)

noncomputable abbrev qz375 := (ep346 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 9000 4000) (Enclosure.sfrac Bool.false 167170 4000) Bool.false 9000 4000 0 1 Bool.false 167170 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 9000 4000) (Enclosure.Real.IsNear.const Bool.false 167170 4000)))

noncomputable abbrev qz98 := qz375

noncomputable def ep347 := ep321 (@ep322 132560000000000000000 (ep340 rfl) (ep345 rfl)) qz98 rfl rfl rfl rfl rfl rfl

noncomputable abbrev qz99 := qz359

noncomputable def ep348 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re qz99) (Complex.re ↑qz2)) (@HMul.hMul Real Real Real qz0 (Complex.im qz99) (Complex.im ↑qz2)) 120447 131072 1 262144 0 1 0 1 120447 120447

noncomputable def ep349 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re qz99) (Complex.re ↑qz2) 1 2 0 1 120447 65536 1 131072 120447 131072 1 262144

noncomputable abbrev qz100 := (@Enclosure.Complex.IsNear.of_eq qz359 (Complex.mk (Enclosure.sfrac Bool.false 1 2) qz277) Bool.false 1 2 0 1 Bool.false 0 1 0 1 BSN.half_c_mk (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 2) qz277 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz370 qz289))

noncomputable def ep350 := ep349 (@Enclosure.Complex.IsNear.re_isNear qz99 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz100) (@Enclosure.Real.IsNear.of_eq (Complex.re ↑qz2) qz2 Bool.false 120447 65536 1 131072 (Complex.ofReal_re qz2) EMRow23.d4)

noncomputable def ep351 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz99) (Complex.im ↑qz2) 0 1 0 1 0 1 0 1 0 1 0 1

noncomputable def ep352 := ep351 (@Enclosure.Complex.IsNear.im_isNear qz99 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz100) (@Enclosure.Real.IsNear.of_eq (Complex.im ↑qz2) qz13 Bool.false 0 1 0 1 (@Eq.trans Real (Complex.im ↑qz2) (0 : Real) qz13 (Complex.ofReal_im qz2) Enclosure.sfrac_zero_eq) qz23)

noncomputable def ep353 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re qz99) (Complex.im ↑qz2)) (@HMul.hMul Real Real Real qz0 (Complex.im qz99) (Complex.re ↑qz2)) 0 1 0 1 0 1 0 1 0 0

noncomputable def ep354 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re qz99) (Complex.im ↑qz2) 1 2 0 1 0 1 0 1 0 1 0 1

noncomputable def ep355 := ep354 (@Enclosure.Complex.IsNear.re_isNear qz99 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz100) (@Enclosure.Real.IsNear.of_eq (Complex.im ↑qz2) qz13 Bool.false 0 1 0 1 (@Eq.trans Real (Complex.im ↑qz2) (0 : Real) qz13 (Complex.ofReal_im qz2) Enclosure.sfrac_zero_eq) qz23)

noncomputable def ep356 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz99) (Complex.re ↑qz2) 0 1 0 1 120447 65536 1 131072 0 1 0 1

noncomputable def ep357 := ep356 (@Enclosure.Complex.IsNear.im_isNear qz99 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz100) (@Enclosure.Real.IsNear.of_eq (Complex.re ↑qz2) qz2 Bool.false 120447 65536 1 131072 (Complex.ofReal_re qz2) EMRow23.d4)

noncomputable def ep358 := @ep319 18117000027816059 132560000000000000000 (ep347 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@Enclosure.Complex.IsNear.mul qz99 (↑qz2) Bool.false 120447 131072 1 262144 Bool.false 0 1 0 1 (@ep348 131072 1 262144 (ep350 rfl) (ep352 rfl) rfl rfl) (@ep353 1 0 1 (ep355 rfl) (ep357 rfl) rfl rfl))

noncomputable abbrev qz101 := (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 1)

noncomputable abbrev qz376 := (@Nat.cast Complex Complex.instNatCast 1)

noncomputable abbrev qz102 := (@HMul.hMul Complex Complex Complex qz351 (@HMul.hMul Complex Complex Complex qz351 (2 : Complex) qz376) (@HSub.hSub Complex Complex Complex qz352 (@HMul.hMul Complex Complex Complex qz351 (2 : Complex) qz376) (1 : Complex)))

noncomputable abbrev qz377 := (@HPow.hPow Complex Int Complex qz504 qz500 (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) (@OfNat.ofNat Int 1 (@instOfNat 1)) (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (@OfNat.ofNat Int 2 (@instOfNat 2)) (@Nat.cast Int instNatCastInt 1))))

noncomputable abbrev qz103 := qz377

noncomputable def ep359 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz72 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz81 qz82 (@HSub.hSub Int Int Int qz364 qz83 (@HMul.hMul Int Int Int qz365 qz84 (@Nat.cast Int instNatCastInt k))))) (@HAdd.hAdd Complex Complex Complex qz4 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz72 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz81 qz82 (@HSub.hSub Int Int Int qz364 qz83 (@HMul.hMul Int Int Int qz365 qz84 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 (@Rat.cast Complex Complex.instRatCast (bernoulli qz101)) qz102) qz103)) Bool.false 1838937 17179869184 3 17179869184

noncomputable def ep360 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz72 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz81 qz82 (@HSub.hSub Int Int Int qz364 qz83 (@HMul.hMul Int Int Int qz365 qz84 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 (@Rat.cast Complex Complex.instRatCast (bernoulli qz101)) qz102) qz103) Bool.false 0 1 0 1 Bool.false

noncomputable def ep361 := @ep360 0 1 0 1 Bool.false 1838937 17179869184 3 17179869184 Bool.true 10247169943 5153960755200 16717 5153960755200 Bool.false 1838937 1838937 17179869184 3 17179869184 Bool.true 10247169943 10247169943 5153960755200 16717

noncomputable def ep362 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz72 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz81 qz82 (@HSub.hSub Int Int Int qz364 qz83 (@HMul.hMul Int Int Int qz365 qz84 (@Nat.cast Int instNatCastInt k))))) (Complex.mk qz13 qz13) Bool.false 0 1 0 1 Bool.false

noncomputable def ep363 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz79 (@Rat.cast Complex Complex.instRatCast (bernoulli qz101)) qz102) qz103 Bool.false 1838937 17179869184 3 17179869184 Bool.true 10247169943 5153960755200 16717 5153960755200

noncomputable abbrev qz104 := (Complex.re qz377)

noncomputable abbrev qz105 := (Complex.im qz377)

noncomputable def ep364 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz79 (@Rat.cast Complex Complex.instRatCast (bernoulli qz101)) qz102)) qz104) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz79 (@Rat.cast Complex Complex.instRatCast (bernoulli qz101)) qz102)) qz105) 1838937 17179869184 3 17179869184 0 1 0

noncomputable def ep365 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz79 (@Rat.cast Complex Complex.instRatCast (bernoulli qz101)) qz102)) qz104 1 12 0 1 5516811 4294967296 9 4294967296 1838937

noncomputable def ep366 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz79 (@Rat.cast Complex Complex.instRatCast (bernoulli qz101)) qz102) (Complex.mk (Enclosure.sfrac Bool.false 1 12) qz13) Bool.false 1 12 0 1 Bool.false 0 1 0 1

noncomputable abbrev qz378 := (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 12) qz13 Bool.false 1 12 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 12) qz23)

noncomputable def ep367 := @Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz79 (@Rat.cast Complex Complex.instRatCast (bernoulli qz101)) qz102) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (ep366 (BSN.stirling_coeff_mk 1 1 6 Bool.false BSN.bern_real_1 rfl rfl) qz378)

noncomputable def ep368 := @Enclosure.Complex.IsNear.re_isNear qz103 Bool.false 5516811 4294967296 9 4294967296 Bool.true 10247169943 429496729600 16717 429496729600

noncomputable abbrev qz505 := (@instHPow Complex Nat (@NPow.toPow Complex (@Monoid.toNPow Complex (@Semiring.toMonoid Complex Complex.instSemiring))))

noncomputable abbrev qz379 := (@HPow.hPow Complex Nat Complex qz505 qz500 1)

noncomputable abbrev qz106 := (@Inv.inv Complex Complex.instInv qz379)

noncomputable def ep369 := @Enclosure.Complex.IsNear.of_eq qz103 qz106 Bool.false 5516811 4294967296 9 4294967296 Bool.true 10247169943 429496729600 16717

noncomputable def ep370 := @Enclosure.Complex.IsNear.of_parts qz106 Bool.false 5516811 4294967296 9 4294967296 Bool.true 10247169943 429496729600 16717

noncomputable abbrev qz107 := (Complex.re qz379)

noncomputable abbrev qz108 := (@MonoidWithZeroHom Complex Real (@instMulZeroOneClassOfSemiring Complex Complex.instSemiring) (@instMulZeroOneClassOfSemiring Real Real.semiring))

noncomputable abbrev qz109 := (@MonoidWithZeroHom.funLike Complex Real (@instMulZeroOneClassOfSemiring Complex Complex.instSemiring) (@instMulZeroOneClassOfSemiring Real Real.semiring))

noncomputable abbrev qz110 := qz379

noncomputable def ep371 := @Enclosure.Real.IsNear.mulLit_ff qz107 (@Inv.inv Real Real.instInv (@DFunLike.coe qz108 Complex (fun (x : Complex) => Real) qz109 Complex.normSq qz110)) 9000 4000 0 1 612979 1073741824 1 1073741824

noncomputable def ep372 := @Enclosure.Complex.IsNear.re_isNear qz110 Bool.false 9000 4000 0 1 Bool.false 167170 4000 0 1

noncomputable def ep373 := @Enclosure.Complex.IsNear.of_eq qz110 qz82 Bool.false 9000 4000 0 1 Bool.false 167170 4000 0

noncomputable def ep374 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (@DFunLike.coe qz108 Complex (fun (x : Complex) => Real) qz109 Complex.normSq qz110)) Bool.false 612979 1073741824 1 1073741824 612979 1073741824 1

noncomputable abbrev qz111 := (Complex.im qz379)

noncomputable abbrev qz380 := (@instHAdd Real Real.instAdd)

noncomputable def ep375 := @Enclosure.Real.IsNear.of_eq (@DFunLike.coe qz108 Complex (fun (x : Complex) => Real) qz109 Complex.normSq qz110) (@HAdd.hAdd Real Real Real qz380 (@HMul.hMul Real Real Real qz0 qz107 qz107) (@HMul.hMul Real Real Real qz0 qz111 qz111)) Bool.false 280268089 160000 0 1

noncomputable def ep376 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz107 qz107) (@HMul.hMul Real Real Real qz0 qz111 qz111) 81 16 0 1 279458089 160000

noncomputable def ep377 := @Enclosure.Real.IsNear.mulLit_ff qz107 qz107 9000 4000 0 1 9000 4000 0 1

noncomputable def ep378 := @Enclosure.Real.IsNear.mulLit_ff qz111 qz111 167170 4000 0 1 167170 4000 0 1

noncomputable def ep379 := @Enclosure.Complex.IsNear.im_isNear qz110 Bool.false 9000 4000 0 1 Bool.false 167170 4000 0 1

noncomputable abbrev qz112 := (ep372 (@ep373 1 (BSN.pow_one_c qz353) qz375))

noncomputable abbrev qz113 := (ep379 (@ep373 1 (BSN.pow_one_c qz353) qz375))

noncomputable def ep380 := @ep376 0 1 4484289424 280268089 160000 0 1 (@ep377 81 16 0 1 qz112 qz112 rfl) (@ep378 279458089 160000 0 1 qz113 qz113 rfl)

noncomputable def ep381 := @Enclosure.Real.IsNear.inv_image (@DFunLike.coe qz108 Complex (fun (x : Complex) => Real) qz109 Complex.normSq qz110) 280268089 160000 0 1 306489 306490 536870912 (ep375 (Enclosure.Complex.normSq_eq_mul_add_mul qz110) (ep380 rfl rfl)) rfl

noncomputable def ep382 := @Enclosure.Real.IsNear.of_eq (Complex.re qz106) (@HMul.hMul Real Real Real qz0 qz107 (@Inv.inv Real Real.instInv (@DFunLike.coe qz108 Complex (fun (x : Complex) => Real) qz109 Complex.normSq qz110))) Bool.false 5516811 4294967296 9 4294967296 (Enclosure.Complex.inv_re_eq_mul qz110) (@ep371 5516811 4294967296 9 4294967296 qz112 (@ep374 1073741824 (ep381 rfl rfl rfl rfl rfl) rfl) rfl)

noncomputable def ep383 := @Enclosure.Real.IsNear.of_eq (Complex.im qz106) (@HMul.hMul Real Real Real qz0 (@Neg.neg Real Real.instNeg qz111) (@Inv.inv Real Real.instInv (@DFunLike.coe qz108 Complex (fun (x : Complex) => Real) qz109 Complex.normSq qz110))) Bool.true 10247169943 429496729600 16717 429496729600 (Enclosure.Complex.inv_im_eq_mul qz110)

noncomputable def ep384 := @Enclosure.Real.IsNear.mulLit_tf (@Neg.neg Real Real.instNeg qz111) (@Inv.inv Real Real.instInv (@DFunLike.coe qz108 Complex (fun (x : Complex) => Real) qz109 Complex.normSq qz110)) 167170 4000 0 1 612979 1073741824 1

noncomputable def ep385 := @ep384 1073741824 10247169943 429496729600 16717 429496729600 (@Enclosure.Real.IsNear.neg qz111 Bool.false 167170 4000 0 1 qz113) (@ep374 1073741824 (ep381 rfl rfl rfl rfl rfl) rfl) rfl

noncomputable def ep386 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz79 (@Rat.cast Complex Complex.instRatCast (bernoulli qz101)) qz102)) qz105 0 1 0 1 10247169943 429496729600 16717 429496729600 0

noncomputable def ep387 := @Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz79 (@Rat.cast Complex Complex.instRatCast (bernoulli qz101)) qz102) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (ep366 (BSN.stirling_coeff_mk 1 1 6 Bool.false BSN.bern_real_1 rfl rfl) qz378)

noncomputable def ep388 := @Enclosure.Complex.IsNear.im_isNear qz103 Bool.false 5516811 4294967296 9 4294967296 Bool.true 10247169943 429496729600 16717 429496729600

noncomputable abbrev qz114 := (@ep369 429496729600 (BSN.zpow_one_sub_two_mul qz353 1 1 rfl rfl) (@ep370 429496729600 ep382 (ep383 ep385)))

noncomputable def ep389 := @ep364 1 1838937 1838937 17179869184 3 17179869184 (@ep365 17179869184 3 17179869184 ep367 (ep368 qz114) rfl) (@ep386 1 0 1 ep387 (ep388 qz114) rfl) rfl

noncomputable def ep390 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz79 (@Rat.cast Complex Complex.instRatCast (bernoulli qz101)) qz102)) qz105) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz79 (@Rat.cast Complex Complex.instRatCast (bernoulli qz101)) qz102)) qz104) 10247169943 5153960755200 16717 5153960755200 0 1 0

noncomputable def ep391 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HDiv.hDiv Complex Complex Complex qz79 (@Rat.cast Complex Complex.instRatCast (bernoulli qz101)) qz102)) qz105 1 12 0 1 10247169943 429496729600 16717 429496729600 10247169943

noncomputable def ep392 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz79 (@Rat.cast Complex Complex.instRatCast (bernoulli qz101)) qz102)) qz104 0 1 0 1 5516811 4294967296 9 4294967296 0

noncomputable def ep393 := @ep390 1 10247169943 10247169943 5153960755200 16717 5153960755200 (@ep391 5153960755200 16717 5153960755200 ep367 (ep388 qz114) rfl) (@ep392 1 0 1 ep387 (ep368 qz114) rfl) rfl

noncomputable abbrev qz115 := (@Enclosure.Complex.IsNear.mk qz277 qz277 Bool.false 0 1 0 1 Bool.false 0 1 0 1 qz289 qz289)

noncomputable def ep394 := @ep361 5153960755200 (@ep362 0 1 0 1 (BSN.stirling_sum_base qz82) qz115) (ep363 (ep389 rfl) (ep393 rfl)) rfl rfl rfl rfl rfl

noncomputable def ep395 := @ep316 631874769509215391813 5404319552844595200 7124063350741674533869 ep303 (ep358 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep359 Bool.true 10247169943 5153960755200 16717 5153960755200 (BSN.stirling_sum_succ qz82 0 1 rfl) (ep394 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl

noncomputable def ep396 := @Enclosure.Complex.IsNear.of_eq (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz75 (@Nat.cast Complex Complex.instNatCast j))) (BSN.logSumC qz16 2) Bool.false 16811706691981523 2251799813685248 1000000001657 165700000000000000 Bool.false 874180103407011 281474976710656

noncomputable abbrev qz116 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz272 qz354 qz376))

noncomputable def ep397 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz16 2) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.logSumC qz16 1) qz116) Bool.false 16811706691981523 2251799813685248 1000000001657 165700000000000000 Bool.false 874180103407011 281474976710656 20000000001657 1657000000000000000

noncomputable def ep398 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz16 1) qz116 Bool.false 16810740324339923 4503599627370496 1000000001657 331400000000000000 Bool.false 880912464643491 562949953421312 20000000001657 3314000000000000000 Bool.false

noncomputable def ep399 := nat_lit 151426391986940121912488614690816

noncomputable def ep400 := nat_lit 984239296989629100094195236864

noncomputable abbrev qz117 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz272 qz354 (@Nat.cast Complex Complex.instNatCast 0)))

noncomputable def ep401 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz16 1) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.logSumC qz16 0) qz117) Bool.false 16810740324339923 4503599627370496 1000000001657 331400000000000000 Bool.false 880912464643491 562949953421312 20000000001657 3314000000000000000

noncomputable def ep402 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz16 0) qz117 Bool.false 0 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable abbrev qz381 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz92))

noncomputable def ep403 := @Enclosure.Complex.IsNear.of_eq qz117 qz381 Bool.false 16810740324339923 4503599627370496 1000000001657 331400000000000000 Bool.false 880912464643491 562949953421312 20000000001657 3314000000000000000

noncomputable def ep404 := nat_lit 14095388669823836586138024775299656045517351461527915768384355499143865450000000000000000

noncomputable def ep405 := nat_lit 333362825269698117172899697813223142879002266584832832104348516276922640000000000000000

noncomputable def ep406 := nat_lit 33550274945131829027863768411693378428465945457122485691460167985050000000000000000

noncomputable def ep407 := BSN.log_dyadic_bound 11562808900 44330808900 5 4 ep404 524288 165700 ep405 ep406 279968 55893617800 32768000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 11562808900) (BSN.artanhQ 44330808900) 0 4 ep405 ep404 ep406 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep408 := @Enclosure.Real.IsNear.mulLit_ff qz94 (Real.log (Enclosure.sfrac Bool.false 27946808900 16000000)) 1 2 0 1 16810740324339923 2251799813685248 1000000001657 165700000000000000 16810740324339923 4503599627370496 1000000001657 331400000000000000 qz370 (BSN.isNear_log_sfrac 27946808900 16000000 16810740324339923 2251799813685248 1000000001657 165700000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 27946808900) qz371)) Bool.false 141018710770680472797184 18889465931478580854784 1000000001657000 165700000000000000000 16810740324339923 2251799813685248 1000000001657 165700000000000000 (BSN.log_rat_reduce_isNear 27946808900 16000000 10 55893617800 32768000000 279968 524288 24973259072661432 36028797018963968 165700 1000000000000000 rfl rfl rfl rfl (ep407 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep409 := BSN.arctan_dyadic_bound_f 1000 167170 1 0 524288 165700 0 1 1 0 1 1 3136 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 167170) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 167170) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz382 := (@Nat.cast Real Real.instNatCast 1000)

noncomputable abbrev qz383 := (@Nat.cast Real Real.instNatCast 167170)

noncomputable def ep410 := @Enclosure.Real.IsNear.subLit_ff_p qz95 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz382 qz383)) 884279719003555 562949953421312 1 2000000000000000 3136 524288 1 165700 461851834263006609408 880912464643491 562949953421312 20000000001657 3314000000000000000 qz96 (ep409 rfl) rfl rfl

noncomputable abbrev qz118 := (@HAdd.hAdd Complex Complex Complex qz272 qz354 (@Nat.cast Complex Complex.instNatCast 0))

noncomputable abbrev qz384 := (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz92)

noncomputable def ep411 := @ep402 16810740324339923 4503599627370496 1000000001657 331400000000000000 Bool.false 880912464643491 562949953421312 20000000001657 3314000000000000000 Bool.false 16810740324339923 16810740324339923 4503599627370496 1000000001657 331400000000000000 Bool.false 880912464643491 880912464643491 562949953421312 20000000001657 3314000000000000000 (@Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz16 0) (Complex.mk qz13 qz13) Bool.false 0 1 0 1 Bool.false 0 1 0 1 (BSN.log_sum_c_base qz16) qz115) (ep403 (@congrArg Complex Complex qz118 qz384 Complex.log (BSN.w_shift_mk qz16 Bool.false 83585 1000 0 qz17 rfl)) (@Enclosure.Complex.IsNear.of_parts qz381 Bool.false 16810740324339923 4503599627370496 1000000001657 331400000000000000 Bool.false 880912464643491 562949953421312 20000000001657 3314000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz381) (@HMul.hMul Real Real Real qz0 qz94 (Real.log (Enclosure.sfrac Bool.false 27946808900 16000000))) Bool.false 16810740324339923 4503599627370496 1000000001657 331400000000000000 (Enclosure.clog_re_eq 1000 167170 4000 27946808900 16000000 rfl rfl rfl) (ep408 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz381) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz383 qz382)) Bool.false 880912464643491 562949953421312 20000000001657 3314000000000000000 (Enclosure.clog_im_eq 1000 167170 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz383 qz382)) (@HSub.hSub Real Real Real qz355 qz95 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz382 qz383))) Bool.false 880912464643491 562949953421312 20000000001657 3314000000000000000 (BSN.arctan_recip 167170 1000 rfl rfl) ep410)))) rfl rfl

noncomputable abbrev qz385 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz92))

noncomputable def ep412 := @Enclosure.Complex.IsNear.of_eq qz116 qz385 Bool.false 16812673059623123 4503599627370496 1000000001657 331400000000000000 Bool.false 867447742170531 562949953421312 20000000001657 3314000000000000000

noncomputable def ep413 := nat_lit 14156552638949582707359614872750051365316004364584681501771434441319865450000000000000000

noncomputable def ep414 := nat_lit 335881549761627065314907825512975377213378756030684611026919093736122640000000000000000

noncomputable def ep415 := nat_lit 34111439978709059144563642199638491808555051614854586317582631985050000000000000000

noncomputable def ep416 := BSN.log_dyadic_bound 11586808900 44354808900 5 4 ep413 524288 165700 ep414 ep415 280418 55941617800 32768000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 11586808900) (BSN.artanhQ 44354808900) 0 4 ep414 ep413 ep415 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep417 := @Enclosure.Real.IsNear.mulLit_ff qz94 (Real.log (Enclosure.sfrac Bool.false 27970808900 16000000)) 1 2 0 1 16812673059623123 2251799813685248 1000000001657 165700000000000000 16812673059623123 4503599627370496 1000000001657 331400000000000000 qz370 (BSN.isNear_log_sfrac 27970808900 16000000 16812673059623123 2251799813685248 1000000001657 165700000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 27970808900) qz371)) Bool.false 141034923729339006582784 18889465931478580854784 1000000001657000 165700000000000000000 16812673059623123 2251799813685248 1000000001657 165700000000000000 (BSN.log_rat_reduce_isNear 27970808900 16000000 10 55941617800 32768000000 280418 524288 24973259072661432 36028797018963968 165700 1000000000000000 rfl rfl rfl rfl (ep416 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep418 := BSN.arctan_dyadic_bound_f 5000 167170 1 0 524288 165700 0 1 1 0 1 1 15676 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 5000) (BSN.arctanEvenQ 167170) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 5000) (BSN.arctanOddQ 167170) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz386 := (@Nat.cast Real Real.instNatCast 5000)

noncomputable def ep419 := @Enclosure.Real.IsNear.subLit_ff_p qz95 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz386 qz383)) 884279719003555 562949953421312 1 2000000000000000 15676 524288 1 165700 454792441847103356928 867447742170531 562949953421312 20000000001657 3314000000000000000 qz96 (ep418 rfl) rfl rfl

noncomputable abbrev qz119 := (@HAdd.hAdd Complex Complex Complex qz272 qz354 qz376)

noncomputable abbrev qz387 := (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz92)

noncomputable def ep420 := @ep398 16812673059623123 4503599627370496 1000000001657 331400000000000000 Bool.false 867447742170531 562949953421312 20000000001657 3314000000000000000 Bool.false ep399 16811706691981523 2251799813685248 1000000001657 165700000000000000 Bool.false ep400 874180103407011 281474976710656 20000000001657 1657000000000000000 (ep401 (BSN.log_sum_c_succ qz16 0 1 rfl) (ep411 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep412 (@congrArg Complex Complex qz119 qz387 Complex.log (BSN.w_shift_mk qz16 Bool.false 83585 1000 1 qz17 rfl)) (@Enclosure.Complex.IsNear.of_parts qz385 Bool.false 16812673059623123 4503599627370496 1000000001657 331400000000000000 Bool.false 867447742170531 562949953421312 20000000001657 3314000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz385) (@HMul.hMul Real Real Real qz0 qz94 (Real.log (Enclosure.sfrac Bool.false 27970808900 16000000))) Bool.false 16812673059623123 4503599627370496 1000000001657 331400000000000000 (Enclosure.clog_re_eq 5000 167170 4000 27970808900 16000000 rfl rfl rfl) (ep417 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz385) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz383 qz386)) Bool.false 867447742170531 562949953421312 20000000001657 3314000000000000000 (Enclosure.clog_im_eq 5000 167170 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz383 qz386)) (@HSub.hSub Real Real Real qz355 qz95 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz386 qz383))) Bool.false 867447742170531 562949953421312 20000000001657 3314000000000000000 (BSN.arctan_recip 167170 5000 rfl rfl) ep419)))) rfl rfl

noncomputable def ep421 := @ep309 ep303 Bool.false 16811706691981523 2251799813685248 1000000001657 165700000000000000 Bool.false 874180103407011 281474976710656 20000000001657 1657000000000000000 Bool.true ep310 29571422644947144361 450359962737049600 5806440353433083734871 ep307 Bool.false ep311 615090511523800780613 5404319552844595200 7753208950793799246829 ep303 (@ep312 450359962737049600 5675368353215897430871 ep307 Bool.false 631874769509215391813 5404319552844595200 7124063350741674533869 ep303 (BSN.logGammaStirling_unfold 1 qz82) (ep395 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (@ep396 20000000001657 1657000000000000000 (BSN.log_sum_c_eq qz16 2) (ep397 (BSN.log_sum_c_succ qz16 1 2 rfl) (ep420 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)))

noncomputable abbrev qz120 := (@HDiv.hDiv Real Real Real qz269 qz279 (2 : Real))

noncomputable def ep422 := @Enclosure.Real.IsNear.mulLit_ff qz120 (Real.log Real.pi) 83585 2000 0 1 75021 65536 1 131072 1254126057 26214400 16717 52428800 (@Enclosure.Real.IsNear.of_eq qz120 (Enclosure.sfrac Bool.false 83585 2000) Bool.false 83585 2000 0 1 (BSN.t_half_eq qz16 Bool.false 83585 1000 qz17) (Enclosure.Real.IsNear.const Bool.false 83585 2000)) EMRow23.d5 rfl

noncomputable def ep423 := @ep305 16717 52428800 ep306 356541852329732050757 5404319552844595200 24373250350793799246829 ep303 (@ep308 7753208950793799246829 ep303 (ep421 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) ep422 rfl rfl

noncomputable def ep424 := BSN.cos_dyadic_bound_f 53427 1073741824 1 0 524288 165862 0 1 1 0 1 1 524287 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 53427) qz282 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 53427) qz283 0 0 rfl) rfl rfl

noncomputable def ep425 := @ep302 262144 Bool.true 524287 524288 1 82850 (@ep304 4323639 65536 123 262144 ep423 rfl) (Enclosure.sfrac_false_div 4323639 65536) (BSN.cos_reduce2 qz356 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 469951143632437248) qz310) 226375608064910080 72057594037927936 Bool.false 524287 524288 10 1000000000000000 165700 82850 (BSN.sin_reduce_arg_pos_rat_q2 4323639 65536 226375608064910080 72057594037927936 10 469951143632437248 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 524287 524288 469951143632437248 9444732965739290427392 53427 1073741824 165862 165700 (ep424 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep426 := nat_lit 38897129362933056355683491

noncomputable def ep427 := nat_lit 6491794221309112312922112000

noncomputable abbrev qz121 := qz273

noncomputable abbrev qz122 := qz274

noncomputable abbrev qz388 := (@HPow.hPow Complex Complex Complex qz490 (@Nat.cast Complex Complex.instNatCast 17) qz491)

noncomputable abbrev qz123 := qz388

noncomputable abbrev qz389 := (@Nat.cast Complex Complex.instNatCast 17)

noncomputable abbrev qz124 := (@HAdd.hAdd Complex Complex Complex qz272 (@HDiv.hDiv Complex Complex Complex qz360 qz389 (@HSub.hSub Complex Complex Complex qz352 qz271 (1 : Complex))) qz359)

noncomputable abbrev qz125 := (@instHSub Nat instSubNat)

noncomputable abbrev qz390 := qz505

noncomputable abbrev qz126 := qz390

noncomputable abbrev qz127 := qz389

noncomputable def ep428 := @Enclosure.Complex.IsNear.of_eq (zetaApproximant qz5 1 17) (@HAdd.hAdd Complex Complex Complex qz4 (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 17, @HPow.hPow Complex Complex Complex qz121 (@Nat.cast Complex Complex.instNatCast n) qz122) (@HMul.hMul Complex Complex Complex qz72 qz123 (@HAdd.hAdd Complex Complex Complex qz4 qz124 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz80 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz126 qz127 (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz80 2 k) 1))))))) Bool.false ep297 ep298 ep299

noncomputable def ep429 := @Enclosure.Complex.IsNear.addLitP (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 17, @HPow.hPow Complex Complex Complex qz121 (@Nat.cast Complex Complex.instNatCast n) qz122) (@HMul.hMul Complex Complex Complex qz72 qz123 (@HAdd.hAdd Complex Complex Complex qz4 qz124 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz80 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz126 qz127 (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))))) Bool.false 92947171639 68719476736 1655329213103 284670432378880

noncomputable def ep430 := nat_lit 4577372971123081896561089

noncomputable def ep431 := nat_lit 271672912319959774172521976400183296

noncomputable def ep432 := nat_lit 548179078573867543791300566319104

noncomputable def ep433 := @ep429 Bool.true 5806503165 68719476736 6621600605377 1138681729515520 Bool.true 285884218816317563718739 ep298 ep430 ep300 Bool.false 74184535087807240866689 783559954291987002163200 1146397589891608738802291 ep427 Bool.false ep431 ep297 ep298 ep299 ep300 Bool.false ep432 7977055481371172118689 783559954291987002163200

noncomputable def ep434 := @Enclosure.Complex.IsNear.of_eq (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 17, @HPow.hPow Complex Complex Complex qz121 (@Nat.cast Complex Complex.instNatCast n) qz122) (BSN.headSumC qz5 17) Bool.false 92947171639 68719476736 1655329213103 284670432378880 Bool.true 5806503165 68719476736 6621600605377

noncomputable def ep435 := @Enclosure.Complex.IsNear.mul qz123 (@HAdd.hAdd Complex Complex Complex qz4 qz124 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz80 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz126 qz127 (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz80 2 k) 1))))) Bool.true 285884218816317563718739 ep298 ep430 ep300 Bool.false

noncomputable abbrev qz128 := (Complex.re qz388)

noncomputable abbrev qz129 := (Complex.im qz388)

noncomputable def ep436 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 qz128 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz124 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz80 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz126 qz127 (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz80 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz129 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz124 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz80 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz126 qz127 (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz80 2 k) 1))))))) 174992241407479600445 3917799771459935010816 809602490516133263609

noncomputable def ep437 := nat_lit 6491794221309112312922112

noncomputable def ep438 := nat_lit 8655725628412149750562816000

noncomputable def ep439 := nat_lit 373345709047523667824653430665012663715627008

noncomputable def ep440 := @Enclosure.Real.IsNear.mulLit_tf qz128 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz124 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz80 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz126 qz127 (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))))) 3061861561 34359738368 70828590041 284670432378880 57152238245

noncomputable abbrev qz391 := (@Nat.cast Real Real.instNatCast 17)

noncomputable abbrev qz130 := (@Inv.inv Real Real.instInv (Real.sqrt qz391))

noncomputable abbrev qz392 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) qz494 (Real.log (Enclosure.sfrac Bool.false 17 1)))

noncomputable abbrev qz131 := (Real.cos qz392)

noncomputable abbrev qz132 := (Real.sin qz392)

noncomputable abbrev qz393 := (@Neg.neg Real Real.instNeg qz132)

noncomputable def ep441 := @Enclosure.Complex.IsNear.of_eq qz123 (Complex.mk (@HMul.hMul Real Real Real qz0 qz130 qz131) (@HMul.hMul Real Real Real qz0 qz130 qz393)) Bool.true 3061861561 34359738368 70828590041 284670432378880 Bool.false 62004890103 274877906944 569072671053 2277363459031040 (BSN.cpow_neg_s_mk qz16 83585 1000 17 qz17 rfl)

noncomputable abbrev qz394 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 17) qz18)

noncomputable def ep442 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz391) 2161695 524288 1 524288 63579 63580 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz391) (Real.sqrt qz394) Bool.false 2161695 524288 1 524288 (BSN.sqrt_natCast_div_one 17) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz394) Bool.false 2161695 524288 1 524288 2161695 524288 1 524288 (BSN.sqrt_enclosure 17 1 1080847 1080848 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep443 := BSN.log_dyadic_bound 1 33 2 1 3267 262144 82850 1 1 15892 34 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 1) (BSN.artanhQ 33) 0 1 1 3267 1 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz395 := (Real.log (Enclosure.sfrac Bool.false 17 1))

noncomputable abbrev qz133 := qz395

noncomputable abbrev qz396 := (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 17) qz18))

noncomputable def ep444 := @Enclosure.Real.IsNear.mulLit_ff qz16 qz133 83585 1000 0 1 3189913004350711 1125899906842624 5000000001657 414250000000000000 53325775693730835787 225179981368524800 83585000027700069 82850000000000000000 qz21 (BSN.isNear_log_sfrac 17 1 3189913004350711 1125899906842624 5000000001657 414250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' qz396 Bool.false 26758929747600409100288 9444732965739290427392 1000000000331400 82850000000000000000 3189913004350711 1125899906842624 5000000001657 414250000000000000 (BSN.log_rat_reduce_isNear 17 1 4 34 32 15892 262144 24973259072661432 36028797018963968 82850 1000000000000000 rfl rfl rfl rfl (ep443 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep445 := nat_lit 6051653717260618157408806484462839455960560683079937428296445990020879220736

noncomputable def ep446 := nat_lit 7326194693153218214155623364022310292198309093243902474901979700821753856

noncomputable def ep447 := nat_lit 18140308762395548035798108206660473747297285431053324479939534010660994154496

noncomputable def ep448 := BSN.cos_dyadic_bound_f 1282654848 1073741824 3 2 524288 165862 ep445 ep57 ep446 ep447 ep60 ep446 192632 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1282654848) qz282 0 2 ep445 ep57 ep446 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1282654848) qz283 0 2 ep447 ep60 ep446 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz134 := qz392

noncomputable abbrev qz397 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 62079373) qz497)

noncomputable def ep449 := @Enclosure.Real.IsNear.cos_image qz134 qz397 Bool.false 62079373 262144 265 262144 Bool.true 192632 524288 1 82850 (@Enclosure.Real.IsNear.recentre' qz134 Bool.false 53325775693730835787 225179981368524800 83585000027700069 82850000000000000000 62079373 262144 265 262144 (ep444 rfl) rfl) (Enclosure.sfrac_false_div 62079373 262144) (BSN.cos_reduce2 qz397 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 45129405441040770400256) qz325) 226375608064910080 72057594037927936 Bool.false 192632 524288 37 1000000000000000 165700 82850 (BSN.sin_reduce_arg_pos_rat_q2 62079373 262144 226375608064910080 72057594037927936 37 45129405441040770400256 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 192632 524288 45129405441040770400256 37778931862957161709568 1282654848 1073741824 165862 165700 (ep448 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep450 := nat_lit 10887115735314590108764527173341893172495250582269292248953681198276925194240

noncomputable def ep451 := nat_lit 28502013086796916502988938254258445997014478072173370524205038028352521240576

noncomputable def ep452 := BSN.sin_dyadic_bound_f 1282654848 1073741824 3 2 524288 165862 ep450 ep64 ep446 ep451 ep66 ep446 487617 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1282654848) qz286 0 2 ep450 ep64 ep446 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1282654848) qz287 0 2 ep451 ep66 ep446 rfl rfl rfl rfl) rfl rfl

noncomputable def ep453 := @Enclosure.Real.IsNear.sin_image qz134 qz397 Bool.false 62079373 262144 265 262144 Bool.true 487617 524288 1 82850 (@Enclosure.Real.IsNear.recentre' qz134 Bool.false 53325775693730835787 225179981368524800 83585000027700069 82850000000000000000 62079373 262144 265 262144 (ep444 rfl) rfl) (Enclosure.sfrac_false_div 62079373 262144) (BSN.sin_reduce2 qz397 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 45129405441040770400256) qz325) 226375608064910080 72057594037927936 Bool.false 487617 524288 37 1000000000000000 165700 82850 (BSN.sin_reduce_arg_pos_rat_q2 62079373 262144 226375608064910080 72057594037927936 37 45129405441040770400256 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 487617 524288 45129405441040770400256 37778931862957161709568 1282654848 1073741824 165862 165700 (ep452 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz398 := (@Enclosure.Real.IsNear.recentre' qz130 Bool.false 127159 524288 1 524288 127159 524288 1 524288 (ep442 rfl rfl) rfl)

noncomputable def ep454 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz130 qz131) (@HMul.hMul Real Real Real qz0 qz130 qz393) Bool.true 3061861561 34359738368 70828590041 284670432378880 Bool.false 62004890103 274877906944 569072671053 2277363459031040 (@Enclosure.Real.IsNear.mulLit_ft qz130 qz131 127159 524288 1 524288 24079 65536 11108697 10859315200 3061861561 34359738368 70828590041 284670432378880 qz398 (@Enclosure.Real.IsNear.recentre' qz131 Bool.true 192632 524288 22217394 21718630400 24079 65536 11108697 10859315200 (ep449 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz130 qz393 127159 524288 1 524288 487617 524288 11108697 10859315200 62004890103 274877906944 569072671053 2277363459031040 qz398 (@Enclosure.Real.IsNear.neg qz132 Bool.true 487617 524288 11108697 10859315200 (@Enclosure.Real.IsNear.recentre' qz132 Bool.true 487617 524288 22217394 21718630400 487617 524288 11108697 10859315200 (ep453 rfl rfl) rfl)) rfl)

noncomputable def ep455 := @ep440 114022980312 0 1 174992241407479600445 3917799771459935010816 809602490516133263609 ep437 (@Enclosure.Complex.IsNear.re_isNear qz123 Bool.true 3061861561 34359738368 70828590041 284670432378880 Bool.false 62004890103 274877906944 569072671053 2277363459031040 (ep441 ep454))

noncomputable def ep456 := @Enclosure.Complex.IsNear.re_isNear (@HAdd.hAdd Complex Complex Complex qz4 qz124 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz80 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz126 qz127 (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz80 2 k) 1))))) Bool.false 57152238245 114022980312 0 1 Bool.false

noncomputable def ep457 := @Enclosure.Complex.IsNear.addLitP qz124 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz80 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz126 qz127 (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) Bool.false 278788089 558936178 0 1 Bool.true 56837800

noncomputable def ep458 := @ep457 279468089 0 1 Bool.false 1 408 0 1 Bool.false 16717 40800 0 1 Bool.false 114304476490 57152238245 114022980312 0 1 Bool.false 2352885803813 2352885803813 11402298031200 0 1

noncomputable abbrev qz135 := (@HDiv.hDiv Complex Complex Complex qz360 qz389 (@HSub.hSub Complex Complex Complex qz352 qz271 (1 : Complex)))

noncomputable def ep459 := @Enclosure.Complex.IsNear.addLitP qz135 qz99 Bool.true 34000000 27946808900 0 1 Bool.true 5683780000 27946808900 0 1

noncomputable def ep460 := @Enclosure.Complex.IsNear.of_eq qz135 (Complex.mk (Enclosure.sfrac Bool.true 34000000 27946808900) (Enclosure.sfrac Bool.true 5683780000 27946808900)) Bool.true 34000000 27946808900 0 1 Bool.true 5683780000 27946808900 0 1

noncomputable def ep461 := @ep459 Bool.false 1 2 0 1 Bool.false 0 1 0 1 Bool.false 27878808900 278788089 558936178 0 1 Bool.true 5683780000 56837800 279468089 0 1 (ep460 (BSN.N_div_s_sub_one_mk qz16 83585 1000 17 qz17 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 34000000 27946808900) (Enclosure.sfrac Bool.true 5683780000 27946808900) Bool.true 34000000 27946808900 0 1 Bool.true 5683780000 27946808900 0 1 (Enclosure.Real.IsNear.const Bool.true 34000000 27946808900) (Enclosure.Real.IsNear.const Bool.true 5683780000 27946808900))) qz100 rfl

noncomputable abbrev qz136 := (@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 1)))

noncomputable abbrev qz137 := (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz390 qz389 1))

noncomputable def ep462 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz80 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz126 qz127 (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) (@HAdd.hAdd Complex Complex Complex qz4 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz80 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz126 qz127 (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz136) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz137)) Bool.false 1 408 0 1

noncomputable def ep463 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz80 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz126 qz127 (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz136) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz137) Bool.false 0 1 0 1 Bool.false

noncomputable def ep464 := @ep463 0 1 0 1 Bool.false 1 408 0 1 Bool.false 16717 40800 0 1 Bool.false 1 1 408 0 1 Bool.false 16717 16717 40800 0

noncomputable def ep465 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz80 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz126 qz127 (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) (Complex.mk qz13 qz13) Bool.false 0 1 0 1 Bool.false

noncomputable def ep466 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz136) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz137 Bool.false 1 408 0 1 Bool.false 16717 40800 0 1

noncomputable def ep467 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz136) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz137)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz136) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz137)) 1 408 0 1 0 1 0

noncomputable def ep468 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz136) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz137) 1 24 0 1 1 17 0 1 1

noncomputable def ep469 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz136)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz136)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) 1 24 0 1 0 1 0 1 1

noncomputable def ep470 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz136)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 1 2 0 1 1 24 0

noncomputable def ep471 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz136) (Complex.mk (Enclosure.sfrac Bool.false 1 12) qz13) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (BSN.bern_coeff_mk 1 1 6 2 Bool.false BSN.bern_real_1 EMRow23.d8 rfl) qz378

noncomputable def ep472 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) qz5 Bool.false 1 2 0 1 Bool.false 83585 1000 0 1 (BSN.ascPochhammer_one_eval qz5)

noncomputable def ep473 := ep472 (@Enclosure.Complex.IsNear.of_eq qz5 (Complex.mk qz94 qz16) Bool.false 1 2 0 1 Bool.false 83585 1000 0 1 (BSN.s_crit_mk qz16 Bool.false 83585 1000 qz17) (@Enclosure.Complex.IsNear.mk qz94 qz16 Bool.false 1 2 0 1 Bool.false 83585 1000 0 1 qz370 qz21))

noncomputable def ep474 := @ep470 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz136) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep471) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 83585 1000 0 1 ep473)

noncomputable def ep475 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz136)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 83585 1000 0 1 0 1 0

noncomputable def ep476 := @ep475 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz136) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep471) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 83585 1000 0 1 ep473)

noncomputable def ep477 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz136)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz136)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) 16717 2400 0 1 0 1 0 1 16717

noncomputable def ep478 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz136)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 83585 1000 0 1 16717 2400 0

noncomputable def ep479 := @ep478 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz136) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep471) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 83585 1000 0 1 ep473)

noncomputable def ep480 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz136)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 1 2 0 1 0 1 0

noncomputable def ep481 := @ep480 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz136) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep471) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 83585 1000 0 1 ep473)

noncomputable def ep482 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz136) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 24 0 1 Bool.false 16717 2400 0 1 (@ep469 1 24 0 1 (ep474 rfl) (ep476 rfl) rfl rfl) (@ep477 16717 2400 0 1 (ep479 rfl) (ep481 rfl) rfl rfl)

noncomputable def ep483 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz136) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 16717 2400 0 1 ep482

noncomputable abbrev qz138 := (@Enclosure.Complex.IsNear.of_eq (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz390 qz389 1)) (Complex.mk (Enclosure.sfrac Bool.false 1 17) qz277) Bool.false 1 17 0 1 Bool.false 0 1 0 1 (BSN.natCast_pow_inv_mk 17 1 17 EMRow23.d9 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 17) qz277 Bool.false 1 17 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 17) qz289))

noncomputable def ep484 := @ep468 408 0 1 ep483 (@Enclosure.Complex.IsNear.re_isNear qz137 Bool.false 1 17 0 1 Bool.false 0 1 0 1 qz138)

noncomputable def ep485 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz136) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz137) 16717 2400 0 1 0 1 0 1 0

noncomputable def ep486 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz136) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 16717 2400 0 1 ep482

noncomputable def ep487 := @ep485 1 0 1 ep486 (@Enclosure.Complex.IsNear.im_isNear qz137 Bool.false 1 17 0 1 Bool.false 0 1 0 1 qz138)

noncomputable def ep488 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz136) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz137)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz136) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz137)) 0 1 0 1 16717 40800 0

noncomputable def ep489 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz136) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz137) 1 24 0 1 0 1 0 1 0

noncomputable def ep490 := @ep489 1 0 1 ep483 (@Enclosure.Complex.IsNear.im_isNear qz137 Bool.false 1 17 0 1 Bool.false 0 1 0 1 qz138)

noncomputable def ep491 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz136) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz137) 16717 2400 0 1 1 17 0 1 16717

noncomputable def ep492 := @ep491 40800 0 1 ep486 (@Enclosure.Complex.IsNear.re_isNear qz137 Bool.false 1 17 0 1 Bool.false 0 1 0 1 qz138)

noncomputable def ep493 := @ep464 1 (@ep465 0 1 0 1 (BSN.bern_sum_base qz5 17) qz115) (ep466 (@ep467 1 1 1 408 0 1 (ep484 rfl) (ep487 rfl) rfl rfl) (@ep488 1 16717 16717 40800 0 1 (ep490 rfl) (ep492 rfl) rfl rfl)) rfl rfl rfl rfl rfl

noncomputable def ep494 := ep458 (ep461 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep462 Bool.false 16717 40800 0 1 (BSN.bern_sum_succ qz5 17 0 1 1 rfl rfl) (ep493 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl rfl

noncomputable def ep495 := @Enclosure.Real.IsNear.mulLit_ff qz129 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz124 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz80 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz126 qz127 (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))))) 62004890103 274877906944 569072671053 2277363459031040 2352885803813

noncomputable def ep496 := @ep495 11402298031200 0 1 48630141896777961120913 1044746605722649336217600 446321003019516280708363 ep438 (@Enclosure.Complex.IsNear.im_isNear qz123 Bool.true 3061861561 34359738368 70828590041 284670432378880 Bool.false 62004890103 274877906944 569072671053 2277363459031040 (ep441 ep454))

noncomputable def ep497 := @Enclosure.Complex.IsNear.im_isNear (@HAdd.hAdd Complex Complex Complex qz4 qz124 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz80 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz126 qz127 (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz80 2 k) 1))))) Bool.false 57152238245 114022980312 0 1 Bool.false

noncomputable def ep498 := @Enclosure.Real.IsNear.addLit_tf_p (@HMul.hMul Real Real Real qz0 qz128 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz124 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz80 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz126 qz127 (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz80 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz129 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz124 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz80 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz126 qz127 (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz80 2 k) 1))))))) 7204210600117611932093 391779977145993501081600 166651584011559731626333

noncomputable def ep499 := nat_lit 3245897110654556156461056000

noncomputable def ep500 := nat_lit 17311451256824299501125632

noncomputable def ep501 := nat_lit 387520206150496984143528747421283629905477632

noncomputable def ep502 := @Enclosure.Real.IsNear.mulLit_tf qz128 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz124 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz80 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz126 qz127 (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))))) 3061861561 34359738368 70828590041 284670432378880 2352885803813

noncomputable def ep503 := @ep502 11402298031200 0 1 7204210600117611932093 391779977145993501081600 166651584011559731626333 ep499 (@Enclosure.Complex.IsNear.re_isNear qz123 Bool.true 3061861561 34359738368 70828590041 284670432378880 Bool.false 62004890103 274877906944 569072671053 2277363459031040 (ep441 ep454))

noncomputable def ep504 := @Enclosure.Real.IsNear.mulLit_ff qz129 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz124 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz80 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz126 qz127 (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))))) 62004890103 274877906944 569072671053 2277363459031040 57152238245

noncomputable def ep505 := @ep504 114022980312 0 1 1181239417173899529745 10447466057226493362176 2168251791649304734799 ep500 (@Enclosure.Complex.IsNear.im_isNear qz123 Bool.true 3061861561 34359738368 70828590041 284670432378880 Bool.false 62004890103 274877906944 569072671053 2277363459031040 (ep441 ep454))

noncomputable abbrev qz399 := (ep494 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable def ep506 := @ep435 74184535087807240866689 783559954291987002163200 1146397589891608738802291 ep427 (@ep436 ep437 48630141896777961120913 1044746605722649336217600 446321003019516280708363 ep438 ep439 285884218816317563718739 ep298 ep430 ep300 (ep455 (@ep456 2352885803813 11402298031200 0 1 qz399) rfl) (ep496 (@ep497 2352885803813 11402298031200 0 1 qz399) rfl) rfl rfl) (@ep498 ep499 1181239417173899529745 10447466057226493362176 2168251791649304734799 ep500 ep501 74184535087807240866689 783559954291987002163200 1146397589891608738802291 ep427 (ep503 (@ep497 2352885803813 11402298031200 0 1 qz399) rfl) (ep505 (@ep456 2352885803813 11402298031200 0 1 qz399) rfl) rfl rfl)

noncomputable def ep507 := @ep433 ep426 ep427 (@ep434 1138681729515520 (BSN.head_sum_c_eq qz5 17) EMRow23.d7) ep506 rfl rfl rfl rfl rfl rfl rfl rfl rfl

noncomputable def ep508 := @Enclosure.Complex.IsNear.re_isNear (zetaApproximant qz5 1 17) Bool.false ep297 ep298 ep299 ep300 Bool.false 7977055481371172118689 783559954291987002163200 ep426 ep427 (@ep428 ep300 Bool.false 7977055481371172118689 783559954291987002163200 ep426 ep427 (BSN.zetaApproximant_eq_folded' qz5 1 17 rfl) (ep507 rfl rfl rfl rfl rfl rfl rfl rfl rfl))

noncomputable def ep509 := @Enclosure.Real.IsNear.mulLit_tf (Real.sin (@HSub.hSub Real Real Real qz355 (Complex.im (@HSub.hSub Complex Complex Complex qz73 qz74 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz75 (@Nat.cast Complex Complex.instNatCast j))))) qz76)) (Complex.im (zetaApproximant qz5 1 17)) 13 262144 5226347

noncomputable def ep510 := @Enclosure.Real.IsNear.recentre' (Real.sin (@HSub.hSub Real Real Real qz355 (Complex.im (@HSub.hSub Complex Complex Complex qz73 qz74 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz75 (@Nat.cast Complex Complex.instNatCast j))))) qz76)) Bool.true 26 524288 10452694

noncomputable def ep511 := @Enclosure.Real.IsNear.sin_image (@HSub.hSub Real Real Real qz355 (Complex.im (@HSub.hSub Complex Complex Complex qz73 qz74 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz75 (@Nat.cast Complex Complex.instNatCast j))))) qz76) qz356 Bool.false 4323639 65536 123

noncomputable def ep512 := BSN.sin_dyadic_bound_f 53427 1073741824 1 0 524288 165862 0 1 1 0 1 1 26 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 53427) qz286 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 53427) qz287 0 0 rfl) rfl rfl

noncomputable def ep513 := @ep511 262144 Bool.true 26 524288 1 82850 (@ep304 4323639 65536 123 262144 ep423 rfl) (Enclosure.sfrac_false_div 4323639 65536) (BSN.sin_reduce2 qz356 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 469951143632437248) qz310) 226375608064910080 72057594037927936 Bool.false 26 524288 10 1000000000000000 165700 82850 (BSN.sin_reduce_arg_pos_rat_q2 4323639 65536 226375608064910080 72057594037927936 10 469951143632437248 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 26 524288 469951143632437248 9444732965739290427392 53427 1073741824 165862 165700 (ep512 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep514 := @Enclosure.Complex.IsNear.im_isNear (zetaApproximant qz5 1 17) Bool.false ep297 ep298 ep299 ep300 Bool.false 7977055481371172118689 783559954291987002163200 ep426 ep427 (@ep428 ep300 Bool.false 7977055481371172118689 783559954291987002163200 ep426 ep427 (BSN.zetaApproximant_eq_folded' qz5 1 17 rfl) (ep507 rfl rfl rfl rfl rfl rfl rfl rfl rfl))

theorem EMRow23.d10 : Enclosure.Real.IsNear (hardyZApproximantEM 1 17 qz16) Bool.true ep282 ep283 ep284 ep285 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantEM 1 17 qz16) ep286 Bool.true ep282 ep283 ep284 ep285 (@Eq.refl Real ep286) (@ep287 Bool.true ep282 ep283 ep284 ep285 (BSN.re_exp_mul (@HSub.hSub Real Real Real qz355 (Complex.im (@HSub.hSub Complex Complex Complex qz73 qz74 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz75 (@Nat.cast Complex Complex.instNatCast j))))) qz76) (zetaApproximant qz5 1 17)) (@ep289 ep283 ep290 ep291 103701721257825237542957 ep292 ep293 ep294 ep295 ep282 ep283 ep284 ep285 (@ep296 10859315200 ep297 ep298 ep299 ep300 ep288 ep283 ep290 ep291 (@ep301 21718630400 524287 524288 5226347 10859315200 (ep425 rfl rfl) rfl) ep508 rfl) (@ep509 10859315200 7977055481371172118689 783559954291987002163200 ep426 ep427 103701721257825237542957 ep292 ep293 ep294 (@ep510 21718630400 13 262144 5226347 10859315200 (ep513 rfl rfl) rfl) ep514 rfl) rfl rfl))

noncomputable abbrev qz521 := (@HAdd.hAdd Complex Complex Complex (@instHAdd Complex Complex.instAdd) (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (2 : Complex)) (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul) Complex.I ↑(Enclosure.sfrac Bool.false 85999 1000)))

noncomputable abbrev qz506 := qz521

noncomputable abbrev qz400 := qz506

noncomputable abbrev qz139 := (BSN.headSumC qz400 9)

noncomputable abbrev qz140 := qz400

noncomputable abbrev qz507 := (@Neg.neg Complex Complex.instNeg qz521)

noncomputable abbrev qz401 := qz507

noncomputable abbrev qz141 := (@HPow.hPow Complex Complex Complex qz273 (@Nat.cast Complex Complex.instNatCast 8) qz401)

noncomputable def ep515 := @Enclosure.Complex.IsNear.of_eq qz139 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz140 8) qz141) Bool.false 217681867921 274877906944 40555495354353 11386817295155200 Bool.false 19203975065 274877906944 40415556070553 11386817295155200

noncomputable def ep516 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz140 8) qz141 Bool.false 39007406751 34359738368 2268807392507 711676080947200 Bool.false 42388437653 274877906944 36176889220337 11386817295155200 Bool.true

noncomputable abbrev qz142 := (@HPow.hPow Complex Complex Complex qz273 (@Nat.cast Complex Complex.instNatCast 7) qz401)

noncomputable def ep517 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz140 8) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz140 7) qz142) Bool.false 39007406751 34359738368 2268807392507 711676080947200 Bool.false 42388437653 274877906944 36176889220337 11386817295155200

noncomputable def ep518 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz140 7) qz142 Bool.false 47659995983 34359738368 7940156552599 2846704323788800 Bool.true 8771887155 68719476736 15817435713273 5693408647577600 Bool.true

noncomputable abbrev qz143 := (@HPow.hPow Complex Complex Complex qz273 (@Nat.cast Complex Complex.instNatCast 6) qz401)

noncomputable def ep519 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz140 7) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz140 6) qz143) Bool.false 47659995983 34359738368 7940156552599 2846704323788800 Bool.true 8771887155 68719476736 15817435713273 5693408647577600

noncomputable def ep520 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz140 6) qz143 Bool.false 246107120587 137438953472 13425372965193 5693408647577600 Bool.true 26006234253 137438953472 3342898208667 1423352161894400 Bool.true

noncomputable abbrev qz144 := (@HPow.hPow Complex Complex Complex qz273 (@Nat.cast Complex Complex.instNatCast 5) qz401)

noncomputable def ep521 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz140 6) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz140 5) qz144) Bool.false 246107120587 137438953472 13425372965193 5693408647577600 Bool.true 26006234253 137438953472 3342898208667 1423352161894400

noncomputable def ep522 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz140 5) qz144 Bool.false 371266924559 274877906944 21474371298081 11386817295155200 Bool.true 7506812063 68719476736 5346073811339 2846704323788800 Bool.false

noncomputable abbrev qz145 := (@HPow.hPow Complex Complex Complex qz273 (@Nat.cast Complex Complex.instNatCast 4) qz401)

noncomputable def ep523 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz140 5) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz140 4) qz145) Bool.false 371266924559 274877906944 21474371298081 11386817295155200 Bool.true 7506812063 68719476736 5346073811339 2846704323788800

noncomputable def ep524 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz140 4) qz145 Bool.false 7362575533 8589934592 48330896031 35583804047360 Bool.true 26018649409 137438953472 1539377085877 1138681729515520 Bool.false

noncomputable abbrev qz146 := (@HPow.hPow Complex Complex Complex qz273 qz275 qz401)

noncomputable def ep525 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz140 4) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz140 3) qz146) Bool.false 7362575533 8589934592 48330896031 35583804047360 Bool.true 26018649409 137438953472 1539377085877 1138681729515520

noncomputable def ep526 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz140 3) qz146 Bool.false 10142256155 34359738368 425515683071 569340864757760 Bool.true 1951743897 34359738368 423525311241 569340864757760 Bool.false

noncomputable abbrev qz147 := (@HPow.hPow Complex Complex Complex qz273 qz276 qz401)

noncomputable def ep527 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz140 3) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz140 2) qz147) Bool.false 10142256155 34359738368 425515683071 569340864757760 Bool.true 1951743897 34359738368 423525311241 569340864757760

noncomputable def ep528 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz140 2) qz147 Bool.false 1 1 0 1 Bool.false 0 1 0 1 Bool.true

noncomputable def ep529 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz140 2) (Complex.mk (Enclosure.sfrac Bool.false 1 1) qz13) Bool.false 1 1 0 1 Bool.false 0 1 0 1 (BSN.head_sum_c_two qz140)

noncomputable abbrev qz522 := (Enclosure.sfrac Bool.false 85999 1000)

noncomputable abbrev qz508 := qz522

noncomputable abbrev qz402 := qz508

noncomputable abbrev qz148 := (@HMul.hMul Real Real Real qz266 qz402 (Real.log qz280))

noncomputable abbrev qz149 := qz402

noncomputable abbrev qz403 := (@Eq.refl Real qz508)

noncomputable abbrev qz150 := qz403

noncomputable def ep530 := @Enclosure.Complex.IsNear.of_eq qz147 (Complex.mk (@HMul.hMul Real Real Real qz0 qz14 (Real.cos qz148)) (@HMul.hMul Real Real Real qz0 qz14 (@Neg.neg Real Real.instNeg (Real.sin qz148)))) Bool.true 24217482213 34359738368 425515683071 569340864757760 Bool.true 1951743897 34359738368 423525311241 569340864757760 (BSN.cpow_neg_s_mk qz149 85999 1000 2 qz150 rfl)

noncomputable def ep531 := nat_lit 26404168095569828430315004014774866098558932846805378081663499479904000409600

noncomputable def ep532 := nat_lit 43009703457257436491159616111923498959272352703861542128176192484777394176

noncomputable def ep533 := nat_lit 69084138825656848134601228279276773164577430789636404859958784802392266244096

noncomputable def ep534 := BSN.sin_dyadic_bound_f 1600279368 1073741824 3 2 524288 165862 ep531 ep64 ep532 ep533 ep66 ep532 522593 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1600279368) qz286 0 2 ep531 ep64 ep532 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1600279368) qz287 0 2 ep533 ep66 ep532 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz151 := (Enclosure.Real.IsNear.const Bool.false 85999 1000)

noncomputable abbrev qz404 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 7813181) qz495)

noncomputable def ep535 := @Enclosure.Real.IsNear.cos_image qz148 qz404 Bool.false 7813181 131072 545 524288 Bool.true 522593 524288 1 82850 (@Enclosure.Real.IsNear.recentre' qz148 Bool.false 1953295287 32768000 85999 82850000 7813181 131072 545 524288 (@Enclosure.Real.IsNear.mulLit_ff qz149 qz20 85999 1000 0 1 181704 262144 1 82850 1953295287 32768000 85999 82850000 qz151 qz285 rfl) rfl) (Enclosure.sfrac_false_div 7813181 131072) (BSN.cos_reduce1 qz404 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 28152412375199579635712) qz293) 226375608064910080 72057594037927936 Bool.false 522593 524288 9 1000000000000000 165700 82850 (BSN.sin_reduce_arg_pos_rat_q1 7813181 131072 226375608064910080 72057594037927936 9 28152412375199579635712 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 522593 524288 28152412375199579635712 18889465931478580854784 1600279368 1073741824 165862 165700 (ep534 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep536 := nat_lit 14688097699075352433059962059813558276514639293871370730758911352162123513856

noncomputable def ep537 := nat_lit 43978273690311542426197566947216827831625373176206389108020381671516815753216

noncomputable def ep538 := BSN.cos_dyadic_bound_f 1600279368 1073741824 3 2 524288 165862 ep536 ep57 ep532 ep537 ep60 ep532 42117 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1600279368) qz282 0 2 ep536 ep57 ep532 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1600279368) qz283 0 2 ep537 ep60 ep532 rfl rfl rfl rfl) rfl rfl

noncomputable def ep539 := @Enclosure.Real.IsNear.sin_image qz148 qz404 Bool.false 7813181 131072 545 524288 Bool.false 42117 524288 1 82850 (@Enclosure.Real.IsNear.recentre' qz148 Bool.false 1953295287 32768000 85999 82850000 7813181 131072 545 524288 (@Enclosure.Real.IsNear.mulLit_ff qz149 qz20 85999 1000 0 1 181704 262144 1 82850 1953295287 32768000 85999 82850000 qz151 qz285 rfl) rfl) (Enclosure.sfrac_false_div 7813181 131072) (BSN.sin_reduce1 qz404 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 28152412375199579635712) qz293) 226375608064910080 72057594037927936 Bool.false 42117 524288 9 1000000000000000 165700 82850 (BSN.sin_reduce_arg_pos_rat_q1 7813181 131072 226375608064910080 72057594037927936 9 28152412375199579635712 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 42117 524288 28152412375199579635712 18889465931478580854784 1600279368 1073741824 165862 165700 (ep538 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep540 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz14 (Real.cos qz148)) (@HMul.hMul Real Real Real qz0 qz14 (@Neg.neg Real Real.instNeg (Real.sin qz148))) Bool.true 24217482213 34359738368 425515683071 569340864757760 Bool.true 1951743897 34359738368 423525311241 569340864757760 (@Enclosure.Real.IsNear.mulLit_ft qz14 (Real.cos qz148) 46341 65536 1 262144 522593 524288 22838769 21718630400 24217482213 34359738368 425515683071 569340864757760 qz288 (@Enclosure.Real.IsNear.recentre' (Real.cos qz148) Bool.true 522593 524288 45677538 43437260800 522593 524288 22838769 21718630400 (ep535 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz14 (@Neg.neg Real Real.instNeg (Real.sin qz148)) 46341 65536 1 262144 42117 524288 22838769 21718630400 1951743897 34359738368 423525311241 569340864757760 qz288 (@Enclosure.Real.IsNear.neg (Real.sin qz148) Bool.false 42117 524288 22838769 21718630400 (@Enclosure.Real.IsNear.recentre' (Real.sin qz148) Bool.false 42117 524288 45677538 43437260800 42117 524288 22838769 21718630400 (ep539 rfl rfl) rfl)) rfl)

noncomputable def ep541 := @ep528 24217482213 34359738368 425515683071 569340864757760 Bool.true 1951743897 34359738368 423525311241 569340864757760 Bool.false 10142256155 10142256155 34359738368 425515683071 569340864757760 Bool.true 1951743897 1951743897 34359738368 423525311241 569340864757760 (ep529 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 1) qz13 Bool.false 1 1 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 1) qz23)) (ep530 ep540) rfl rfl

noncomputable abbrev qz152 := (@HMul.hMul Real Real Real qz266 qz402 (Real.log (Enclosure.sfrac Bool.false 3 1)))

noncomputable def ep542 := @Enclosure.Complex.IsNear.of_eq qz146 (Complex.mk (@HMul.hMul Real Real Real qz0 qz24 (Real.cos qz152)) (@HMul.hMul Real Real Real qz0 qz24 (@Neg.neg Real Real.instNeg (Real.sin qz152)))) Bool.false 19308045977 34359738368 69555730685 113868172951552 Bool.true 18211673821 137438953472 138465292679 227736345903104 (BSN.cpow_neg_s_mk qz149 85999 1000 3 qz150 rfl)

noncomputable def ep543 := nat_lit 3822680935668183270564302291992576

noncomputable def ep544 := BSN.cos_dyadic_bound_f 248652032 1073741824 2 1 524288 165862 ep543 ep126 ep543 ep543 ep127 ep543 510292 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 248652032) qz282 0 1 ep543 ep126 ep543 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 248652032) qz283 0 1 ep543 ep127 ep543 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz405 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 6191799) qz496)

noncomputable def ep545 := @Enclosure.Real.IsNear.cos_image qz152 qz405 Bool.false 6191799 65536 545 524288 Bool.false 510292 524288 1 82850 (@Enclosure.Real.IsNear.recentre' qz152 Bool.false 12383598003 131072000 85999 82850000 6191799 65536 545 524288 (@Enclosure.Real.IsNear.mulLit_ff qz149 qz26 85999 1000 0 1 287994 262144 1 82850 12383598003 131072000 85999 82850000 qz151 qz292 rfl) rfl) (Enclosure.sfrac_false_div 6191799 65536) (BSN.cos_reduce0 qz405 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 2187166404379492220928) qz310) 226375608064910080 72057594037927936 Bool.false 510292 524288 15 1000000000000000 165700 82850 (BSN.sin_reduce_arg_pos_rat_q0 6191799 65536 226375608064910080 72057594037927936 15 2187166404379492220928 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 510292 524288 2187166404379492220928 9444732965739290427392 248652032 1073741824 165862 165700 (ep544 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep546 := BSN.sin_dyadic_bound_f 248652032 1073741824 2 1 524288 165862 ep543 ep80 ep543 ep543 ep81 ep543 120329 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 248652032) qz286 0 1 ep543 ep80 ep543 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 248652032) qz287 0 1 ep543 ep81 ep543 rfl rfl rfl rfl) rfl rfl

noncomputable def ep547 := @Enclosure.Real.IsNear.sin_image qz152 qz405 Bool.false 6191799 65536 545 524288 Bool.false 120329 524288 1 82850 (@Enclosure.Real.IsNear.recentre' qz152 Bool.false 12383598003 131072000 85999 82850000 6191799 65536 545 524288 (@Enclosure.Real.IsNear.mulLit_ff qz149 qz26 85999 1000 0 1 287994 262144 1 82850 12383598003 131072000 85999 82850000 qz151 qz292 rfl) rfl) (Enclosure.sfrac_false_div 6191799 65536) (BSN.sin_reduce0 qz405 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 2187166404379492220928) qz310) 226375608064910080 72057594037927936 Bool.false 120329 524288 15 1000000000000000 165700 82850 (BSN.sin_reduce_arg_pos_rat_q0 6191799 65536 226375608064910080 72057594037927936 15 2187166404379492220928 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 120329 524288 2187166404379492220928 9444732965739290427392 248652032 1073741824 165862 165700 (ep546 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep548 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz24 (Real.cos qz152)) (@HMul.hMul Real Real Real qz0 qz24 (@Neg.neg Real Real.instNeg (Real.sin qz152))) Bool.false 19308045977 34359738368 69555730685 113868172951552 Bool.true 18211673821 137438953472 138465292679 227736345903104 (@Enclosure.Real.IsNear.mulLit_ff qz24 (Real.cos qz152) 151349 262144 1 262144 127573 131072 22838769 21718630400 19308045977 34359738368 69555730685 113868172951552 qz294 (@Enclosure.Real.IsNear.recentre' (Real.cos qz152) Bool.false 510292 524288 45677538 43437260800 127573 131072 22838769 21718630400 (ep545 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz24 (@Neg.neg Real Real.instNeg (Real.sin qz152)) 151349 262144 1 262144 120329 524288 22838769 21718630400 18211673821 137438953472 138465292679 227736345903104 qz294 (@Enclosure.Real.IsNear.neg (Real.sin qz152) Bool.false 120329 524288 22838769 21718630400 (@Enclosure.Real.IsNear.recentre' (Real.sin qz152) Bool.false 120329 524288 45677538 43437260800 120329 524288 22838769 21718630400 (ep547 rfl rfl) rfl)) rfl)

noncomputable def ep549 := @ep526 19308045977 34359738368 69555730685 113868172951552 Bool.true 18211673821 137438953472 138465292679 227736345903104 Bool.false 1011904676114072600576 7362575533 8589934592 48330896031 35583804047360 Bool.true 893993986381957824512 26018649409 137438953472 1539377085877 1138681729515520 (ep527 (BSN.head_sum_c_succ qz140 2 3 rfl rfl) (ep541 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep542 ep548) rfl rfl

noncomputable abbrev qz153 := (@HMul.hMul Real Real Real qz266 qz402 (Real.log (Enclosure.sfrac Bool.false 4 1)))

noncomputable def ep550 := @Enclosure.Complex.IsNear.of_eq qz145 (Complex.mk (@HMul.hMul Real Real Real qz0 qz27 (Real.cos qz153)) (@HMul.hMul Real Real Real qz0 qz27 (@Neg.neg Real Real.instNeg (Real.sin qz153)))) Bool.false 135664507503 274877906944 6008484568161 11386817295155200 Bool.false 11005025283 137438953472 2995262193293 5693408647577600 (BSN.cpow_neg_s_mk qz149 85999 1000 4 qz150 rfl)

noncomputable def ep551 := nat_lit 21143305581700548332806911014559436527216759049603639081487493835243210670080

noncomputable def ep552 := nat_lit 27596170557672183523047174567913187689559935086995062307332054289257332736

noncomputable def ep553 := nat_lit 55330644628312824003076023898355236219784605235011538922064898623454373216256

noncomputable def ep554 := BSN.sin_dyadic_bound_f 1513931072 1073741824 3 2 524288 165862 ep551 ep64 ep552 ep553 ep66 ep552 517521 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1513931072) qz286 0 2 ep551 ep64 ep552 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1513931072) qz287 0 2 ep553 ep66 ep552 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz406 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 62505449) qz19)

noncomputable def ep555 := @Enclosure.Real.IsNear.cos_image qz153 qz406 Bool.false 62505449 524288 545 524288 Bool.false 517521 524288 1 82850 (@Enclosure.Real.IsNear.recentre' qz153 Bool.false 1953295287 16384000 85999 82850000 62505449 524288 545 524288 (@Enclosure.Real.IsNear.mulLit_ff qz149 qz29 85999 1000 0 1 363408 262144 1 82850 1953295287 16384000 85999 82850000 qz151 qz297 rfl) rfl) (Enclosure.sfrac_false_div 62505449 524288) (BSN.cos_reduce3 qz406 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 106533428315649136918528) qz22) 226375608064910080 72057594037927936 Bool.false 517521 524288 18 1000000000000000 165700 82850 (BSN.sin_reduce_arg_pos_rat_q3 62505449 524288 226375608064910080 72057594037927936 18 106533428315649136918528 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 517521 524288 106533428315649136918528 75557863725914323419136 1513931072 1073741824 165862 165700 (ep554 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep556 := nat_lit 11758545843414825599791860419007648376315781665374019517407421932597009186816

noncomputable def ep557 := nat_lit 35220445189129132432329486907887118753568225125948068427607601689212512894976

noncomputable def ep558 := BSN.cos_dyadic_bound_f 1513931072 1073741824 3 2 524288 165862 ep556 ep57 ep552 ep557 ep60 ep552 83962 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1513931072) qz282 0 2 ep556 ep57 ep552 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1513931072) qz283 0 2 ep557 ep60 ep552 rfl rfl rfl rfl) rfl rfl

noncomputable def ep559 := @Enclosure.Real.IsNear.sin_image qz153 qz406 Bool.false 62505449 524288 545 524288 Bool.true 83962 524288 1 82850 (@Enclosure.Real.IsNear.recentre' qz153 Bool.false 1953295287 16384000 85999 82850000 62505449 524288 545 524288 (@Enclosure.Real.IsNear.mulLit_ff qz149 qz29 85999 1000 0 1 363408 262144 1 82850 1953295287 16384000 85999 82850000 qz151 qz297 rfl) rfl) (Enclosure.sfrac_false_div 62505449 524288) (BSN.sin_reduce3 qz406 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 106533428315649136918528) qz22) 226375608064910080 72057594037927936 Bool.false 83962 524288 18 1000000000000000 165700 82850 (BSN.sin_reduce_arg_pos_rat_q3 62505449 524288 226375608064910080 72057594037927936 18 106533428315649136918528 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 83962 524288 106533428315649136918528 75557863725914323419136 1513931072 1073741824 165862 165700 (ep558 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep560 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz27 (Real.cos qz153)) (@HMul.hMul Real Real Real qz0 qz27 (@Neg.neg Real Real.instNeg (Real.sin qz153))) Bool.false 135664507503 274877906944 6008484568161 11386817295155200 Bool.false 11005025283 137438953472 2995262193293 5693408647577600 (@Enclosure.Real.IsNear.mulLit_ff qz27 (Real.cos qz153) 262143 524288 1 524288 517521 524288 22838769 21718630400 135664507503 274877906944 6008484568161 11386817295155200 qz298 (@Enclosure.Real.IsNear.recentre' (Real.cos qz153) Bool.false 517521 524288 45677538 43437260800 517521 524288 22838769 21718630400 (ep555 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz27 (@Neg.neg Real Real.instNeg (Real.sin qz153)) 262143 524288 1 524288 41981 262144 22838769 21718630400 11005025283 137438953472 2995262193293 5693408647577600 qz298 (@Enclosure.Real.IsNear.neg (Real.sin qz153) Bool.true 41981 262144 22838769 21718630400 (@Enclosure.Real.IsNear.recentre' (Real.sin qz153) Bool.true 83962 524288 45677538 43437260800 41981 262144 22838769 21718630400 (ep559 rfl rfl) rfl)) rfl)

noncomputable def ep561 := @ep524 135664507503 274877906944 6008484568161 11386817295155200 Bool.false 11005025283 137438953472 2995262193293 5693408647577600 Bool.false 3189158598134808444928 371266924559 274877906944 21474371298081 11386817295155200 Bool.true 2063456787699410665472 7506812063 68719476736 5346073811339 2846704323788800 (ep525 (BSN.head_sum_c_succ qz140 3 4 rfl rfl) (ep549 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep550 ep560) rfl rfl

noncomputable abbrev qz154 := (@HMul.hMul Real Real Real qz266 qz402 (Real.log (Enclosure.sfrac Bool.false 5 1)))

noncomputable def ep562 := @Enclosure.Complex.IsNear.of_eq qz144 (Complex.mk (@HMul.hMul Real Real Real qz0 qz30 (Real.cos qz154)) (@HMul.hMul Real Real Real qz0 qz30 (@Neg.neg Real Real.instNeg (Real.sin qz154)))) Bool.false 120947316615 274877906944 1075274926461 2277363459031040 Bool.true 10992610127 137438953472 267944521199 569340864757760 (BSN.cpow_neg_s_mk qz149 85999 1000 5 qz150 rfl)

noncomputable def ep563 := nat_lit 1389564272027489355923890120811536

noncomputable def ep564 := BSN.cos_dyadic_bound_f 193072162 1073741824 2 1 524288 165862 ep563 ep126 ep563 ep563 ep127 ep563 515835 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 193072162) qz282 0 1 ep563 ep126 ep563 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 193072162) qz283 0 1 ep563 ep127 ep563 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz407 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 18141661) qz495)

noncomputable def ep565 := @Enclosure.Real.IsNear.cos_image qz154 qz407 Bool.false 18141661 131072 545 524288 Bool.false 515835 524288 1 82850 (@Enclosure.Real.IsNear.recentre' qz154 Bool.false 2267707631 16384000 85999 82850000 18141661 131072 545 524288 (@Enclosure.Real.IsNear.mulLit_ff qz149 qz32 85999 1000 0 1 421904 262144 1 82850 2267707631 16384000 85999 82850000 qz151 qz301 rfl) rfl) (Enclosure.sfrac_false_div 18141661 131072) (BSN.cos_reduce0 qz407 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 3396561398436842176512) qz293) 226375608064910080 72057594037927936 Bool.false 515835 524288 22 1000000000000000 165700 82850 (BSN.sin_reduce_arg_pos_rat_q0 18141661 131072 226375608064910080 72057594037927936 22 3396561398436842176512 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 515835 524288 3396561398436842176512 18889465931478580854784 193072162 1073741824 165862 165700 (ep564 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep566 := BSN.sin_dyadic_bound_f 193072162 1073741824 2 1 524288 165862 ep563 ep80 ep563 ep563 ep81 ep563 93766 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 193072162) qz286 0 1 ep563 ep80 ep563 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 193072162) qz287 0 1 ep563 ep81 ep563 rfl rfl rfl rfl) rfl rfl

noncomputable def ep567 := @Enclosure.Real.IsNear.sin_image qz154 qz407 Bool.false 18141661 131072 545 524288 Bool.false 93766 524288 1 82850 (@Enclosure.Real.IsNear.recentre' qz154 Bool.false 2267707631 16384000 85999 82850000 18141661 131072 545 524288 (@Enclosure.Real.IsNear.mulLit_ff qz149 qz32 85999 1000 0 1 421904 262144 1 82850 2267707631 16384000 85999 82850000 qz151 qz301 rfl) rfl) (Enclosure.sfrac_false_div 18141661 131072) (BSN.sin_reduce0 qz407 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 3396561398436842176512) qz293) 226375608064910080 72057594037927936 Bool.false 93766 524288 22 1000000000000000 165700 82850 (BSN.sin_reduce_arg_pos_rat_q0 18141661 131072 226375608064910080 72057594037927936 22 3396561398436842176512 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 93766 524288 3396561398436842176512 18889465931478580854784 193072162 1073741824 165862 165700 (ep566 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep568 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz30 (Real.cos qz154)) (@HMul.hMul Real Real Real qz0 qz30 (@Neg.neg Real Real.instNeg (Real.sin qz154))) Bool.false 120947316615 274877906944 1075274926461 2277363459031040 Bool.true 10992610127 137438953472 267944521199 569340864757760 (@Enclosure.Real.IsNear.mulLit_ff qz30 (Real.cos qz154) 234469 524288 1 524288 515835 524288 22838769 21718630400 120947316615 274877906944 1075274926461 2277363459031040 qz302 (@Enclosure.Real.IsNear.recentre' (Real.cos qz154) Bool.false 515835 524288 45677538 43437260800 515835 524288 22838769 21718630400 (ep565 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz30 (@Neg.neg Real Real.instNeg (Real.sin qz154)) 234469 524288 1 524288 46883 262144 22838769 21718630400 10992610127 137438953472 267944521199 569340864757760 qz302 (@Enclosure.Real.IsNear.neg (Real.sin qz154) Bool.false 46883 262144 22838769 21718630400 (@Enclosure.Real.IsNear.recentre' (Real.sin qz154) Bool.false 93766 524288 45677538 43437260800 46883 262144 22838769 21718630400 (ep567 rfl rfl) rfl)) rfl)

noncomputable def ep569 := @ep522 120947316615 274877906944 1075274926461 2277363459031040 Bool.true 10992610127 137438953472 267944521199 569340864757760 Bool.false 135298820381938345312256 246107120587 137438953472 13425372965193 5693408647577600 Bool.true 1787134809739999838208 26006234253 137438953472 3342898208667 1423352161894400 (ep523 (BSN.head_sum_c_succ qz140 4 5 rfl rfl) (ep561 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep562 ep568) rfl rfl

noncomputable abbrev qz155 := (@HMul.hMul Real Real Real qz266 qz402 (Real.log (Enclosure.sfrac Bool.false 6 1)))

noncomputable def ep570 := @Enclosure.Complex.IsNear.of_eq qz143 (Complex.mk (@HMul.hMul Real Real Real qz0 qz33 (Real.cos qz155)) (@HMul.hMul Real Real Real qz0 qz33 (@Neg.neg Real Real.instNeg (Real.sin qz155)))) Bool.true 55467136655 137438953472 490988028001 1138681729515520 Bool.false 8462459943 137438953472 489168575721 1138681729515520 (BSN.cpow_neg_s_mk qz149 85999 1000 6 qz150 rfl)

noncomputable def ep571 := @Enclosure.Real.IsNear.mulLit_ff qz149 qz35 85999 1000 0 1 4034681531866359 2251799813685248 10000000001657 828500000000000000 346978577058975007641 2251799813685248000 859990000142500343 828500000000000000000 qz151 (BSN.isNear_log_sfrac 6 1 4034681531866359 2251799813685248 10000000001657 828500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz304) Bool.false 16922680887833197019136 9444732965739290427392 1000000000165700 82850000000000000000 4034681531866359 2251799813685248 10000000001657 828500000000000000 (BSN.log_rat_reduce_isNear 6 1 2 12 8 106290 262144 24973259072661432 36028797018963968 82850 1000000000000000 rfl rfl rfl rfl (ep121 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep572 := nat_lit 698421478147308754352811048254881

noncomputable def ep573 := BSN.cos_dyadic_bound_f 162565879 1073741824 2 1 524288 165862 ep572 ep126 ep572 ep572 ep127 ep572 518290 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 162565879) qz282 0 1 ep572 ep126 ep572 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 162565879) qz283 0 1 ep572 ep127 ep572 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz408 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 80787245) qz19)

noncomputable def ep574 := @Enclosure.Real.IsNear.cos_image qz155 qz408 Bool.false 80787245 524288 545 524288 Bool.true 518290 524288 1 82850 (@Enclosure.Real.IsNear.recentre' qz155 Bool.false 346978577058975007641 2251799813685248000 859990000142500343 828500000000000000000 80787245 524288 545 524288 (ep571 rfl) rfl) (Enclosure.sfrac_false_div 80787245 524288) (BSN.cos_reduce2 qz408 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 11439556793960465694720) qz22) 226375608064910080 72057594037927936 Bool.false 518290 524288 24 1000000000000000 165700 82850 (BSN.sin_reduce_arg_pos_rat_q2 80787245 524288 226375608064910080 72057594037927936 24 11439556793960465694720 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 518290 524288 11439556793960465694720 75557863725914323419136 162565879 1073741824 165862 165700 (ep573 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep575 := BSN.sin_dyadic_bound_f 162565879 1073741824 1 0 524288 165862 0 1 1 0 1 1 79074 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 162565879) qz286 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 162565879) qz287 0 0 rfl) rfl rfl

noncomputable def ep576 := @Enclosure.Real.IsNear.sin_image qz155 qz408 Bool.false 80787245 524288 545 524288 Bool.true 79074 524288 1 82850 (@Enclosure.Real.IsNear.recentre' qz155 Bool.false 346978577058975007641 2251799813685248000 859990000142500343 828500000000000000000 80787245 524288 545 524288 (ep571 rfl) rfl) (Enclosure.sfrac_false_div 80787245 524288) (BSN.sin_reduce2 qz408 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 11439556793960465694720) qz22) 226375608064910080 72057594037927936 Bool.false 79074 524288 24 1000000000000000 165700 82850 (BSN.sin_reduce_arg_pos_rat_q2 80787245 524288 226375608064910080 72057594037927936 24 11439556793960465694720 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 79074 524288 11439556793960465694720 75557863725914323419136 162565879 1073741824 165862 165700 (ep575 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep577 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz33 (Real.cos qz155)) (@HMul.hMul Real Real Real qz0 qz33 (@Neg.neg Real Real.instNeg (Real.sin qz155))) Bool.true 55467136655 137438953472 490988028001 1138681729515520 Bool.false 8462459943 137438953472 489168575721 1138681729515520 (@Enclosure.Real.IsNear.mulLit_ft qz33 (Real.cos qz155) 214039 524288 1 524288 259145 262144 22838769 21718630400 55467136655 137438953472 490988028001 1138681729515520 qz306 (@Enclosure.Real.IsNear.recentre' (Real.cos qz155) Bool.true 518290 524288 45677538 43437260800 259145 262144 22838769 21718630400 (ep574 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz33 (@Neg.neg Real Real.instNeg (Real.sin qz155)) 214039 524288 1 524288 39537 262144 22838769 21718630400 8462459943 137438953472 489168575721 1138681729515520 qz306 (@Enclosure.Real.IsNear.neg (Real.sin qz155) Bool.true 39537 262144 22838769 21718630400 (@Enclosure.Real.IsNear.recentre' (Real.sin qz155) Bool.true 79074 524288 45677538 43437260800 39537 262144 22838769 21718630400 (ep576 rfl rfl) rfl)) rfl)

noncomputable def ep578 := @ep520 55467136655 137438953472 490988028001 1138681729515520 Bool.false 8462459943 137438953472 489168575721 1138681729515520 Bool.false 26201359881532975611904 47659995983 34359738368 7940156552599 2846704323788800 Bool.true 2411197981115358904320 8771887155 68719476736 15817435713273 5693408647577600 (ep521 (BSN.head_sum_c_succ qz140 5 6 rfl rfl) (ep569 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep570 ep577) rfl rfl

noncomputable abbrev qz156 := (@HMul.hMul Real Real Real qz266 qz402 (Real.log (Enclosure.sfrac Bool.false 7 1)))

noncomputable def ep579 := @Enclosure.Complex.IsNear.of_eq qz142 (Complex.mk (@HMul.hMul Real Real Real qz0 qz36 (Real.cos qz156)) (@HMul.hMul Real Real Real qz0 qz36 (@Neg.neg Real Real.instNeg (Real.sin qz156)))) Bool.true 540786827 2147483648 1135073017429 2846704323788800 Bool.false 77475986273 274877906944 4542017793791 11386817295155200 (BSN.cpow_neg_s_mk qz149 85999 1000 7 qz150 rfl)

noncomputable def ep580 := @Enclosure.Real.IsNear.mulLit_ff qz149 qz38 85999 1000 0 1 4381792198794487 2251799813685248 10000000001657 828500000000000000 376829747304127087513 2251799813685248000 859990000142500343 828500000000000000000 qz151 (BSN.isNear_log_sfrac 7 1 4381792198794487 2251799813685248 10000000001657 828500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz308) Bool.false 18378568546572512002048 9444732965739290427392 1000000000165700 82850000000000000000 4381792198794487 2251799813685248 10000000001657 828500000000000000 (BSN.log_rat_reduce_isNear 7 1 2 14 8 146699 262144 24973259072661432 36028797018963968 82850 1000000000000000 rfl rfl rfl rfl (ep134 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep581 := nat_lit 1489661148678980283947382194905626263971497614287696809287020759616752515201

noncomputable def ep582 := nat_lit 444731721472633131503985578011236256913995696813278763360966961454446721

noncomputable def ep583 := nat_lit 4468093982593995585579138613560856319400664851469463870334340344927348652161

noncomputable def ep584 := BSN.cos_dyadic_bound_f 903674991 1073741824 3 2 524288 165862 ep581 ep57 ep582 ep583 ep60 ep582 349312 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 903674991) qz282 0 2 ep581 ep57 ep582 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 903674991) qz283 0 2 ep583 ep60 ep582 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz409 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 10967189) qz496)

noncomputable def ep585 := @Enclosure.Real.IsNear.cos_image qz156 qz409 Bool.false 10967189 65536 545 524288 Bool.true 349312 524288 1 82850 (@Enclosure.Real.IsNear.recentre' qz156 Bool.false 376829747304127087513 2251799813685248000 859990000142500343 828500000000000000000 10967189 65536 545 524288 (ep580 rfl) rfl) (Enclosure.sfrac_false_div 10967189 65536) (BSN.cos_reduce2 qz409 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 7948809283411302678528) qz310) 226375608064910080 72057594037927936 Bool.false 349312 524288 26 1000000000000000 165700 82850 (BSN.sin_reduce_arg_pos_rat_q2 10967189 65536 226375608064910080 72057594037927936 26 7948809283411302678528 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 349312 524288 7948809283411302678528 9444732965739290427392 903674991 1073741824 165862 165700 (ep584 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep586 := nat_lit 666882089632517519977888598633706561

noncomputable def ep587 := BSN.sin_dyadic_bound_f 903674991 1073741824 2 1 524288 165862 ep586 ep80 ep586 ep586 ep81 ep586 390971 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 903674991) qz286 0 1 ep586 ep80 ep586 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 903674991) qz287 0 1 ep586 ep81 ep586 rfl rfl rfl rfl) rfl rfl

noncomputable def ep588 := @Enclosure.Real.IsNear.sin_image qz156 qz409 Bool.false 10967189 65536 545 524288 Bool.true 390971 524288 1 82850 (@Enclosure.Real.IsNear.recentre' qz156 Bool.false 376829747304127087513 2251799813685248000 859990000142500343 828500000000000000000 10967189 65536 545 524288 (ep580 rfl) rfl) (Enclosure.sfrac_false_div 10967189 65536) (BSN.sin_reduce2 qz409 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 7948809283411302678528) qz310) 226375608064910080 72057594037927936 Bool.false 390971 524288 26 1000000000000000 165700 82850 (BSN.sin_reduce_arg_pos_rat_q2 10967189 65536 226375608064910080 72057594037927936 26 7948809283411302678528 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 390971 524288 7948809283411302678528 9444732965739290427392 903674991 1073741824 165862 165700 (ep587 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep589 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz36 (Real.cos qz156)) (@HMul.hMul Real Real Real qz0 qz36 (@Neg.neg Real Real.instNeg (Real.sin qz156))) Bool.true 540786827 2147483648 1135073017429 2846704323788800 Bool.false 77475986273 274877906944 4542017793791 11386817295155200 (@Enclosure.Real.IsNear.mulLit_ft qz36 (Real.cos qz156) 198163 524288 1 524288 2729 4096 22838769 21718630400 540786827 2147483648 1135073017429 2846704323788800 qz311 (@Enclosure.Real.IsNear.recentre' (Real.cos qz156) Bool.true 349312 524288 45677538 43437260800 2729 4096 22838769 21718630400 (ep585 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz36 (@Neg.neg Real Real.instNeg (Real.sin qz156)) 198163 524288 1 524288 390971 524288 22838769 21718630400 77475986273 274877906944 4542017793791 11386817295155200 qz311 (@Enclosure.Real.IsNear.neg (Real.sin qz156) Bool.true 390971 524288 22838769 21718630400 (@Enclosure.Real.IsNear.recentre' (Real.sin qz156) Bool.true 390971 524288 45677538 43437260800 390971 524288 22838769 21718630400 (ep588 rfl rfl) rfl)) rfl)

noncomputable def ep590 := @ep518 540786827 2147483648 1135073017429 2846704323788800 Bool.false 77475986273 274877906944 4542017793791 11386817295155200 Bool.false 83767768148657307648 39007406751 34359738368 2268807392507 711676080947200 Bool.false 2912911255170719940608 42388437653 274877906944 36176889220337 11386817295155200 (ep519 (BSN.head_sum_c_succ qz140 6 7 rfl rfl) (ep578 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep579 ep589) rfl rfl

noncomputable abbrev qz157 := (@HMul.hMul Real Real Real qz266 qz402 qz313)

noncomputable def ep591 := @Enclosure.Complex.IsNear.of_eq qz141 (Complex.mk (@HMul.hMul Real Real Real qz0 qz39 (Real.cos qz157)) (@HMul.hMul Real Real Real qz0 qz39 (@Neg.neg Real Real.instNeg (Real.sin qz157)))) Bool.true 94377386087 274877906944 4254577074241 11386817295155200 Bool.true 5796115647 68719476736 529833356277 1423352161894400 (BSN.cpow_neg_s_mk qz149 85999 1000 8 qz150 rfl)

noncomputable def ep592 := @Enclosure.Real.IsNear.mulLit_ff qz149 qz313 85999 1000 0 1 9364972152248037 4503599627370496 20000000004971 1657000000000000000 805378240121178933963 4503599627370496000 1719980000427501029 1657000000000000000000 qz151 (BSN.isNear_log_sfrac 8 1 9364972152248037 4503599627370496 20000000004971 1657000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz314) Bool.false 19639770079031275290624 9444732965739290427392 1000000000248550 82850000000000000000 9364972152248037 4503599627370496 20000000004971 1657000000000000000 (BSN.log_rat_reduce_isNear 8 1 3 16 16 0 262144 24973259072661432 36028797018963968 82850 1000000000000000 rfl rfl rfl rfl (ep148 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep593 := nat_lit 16730788114686179146524336846015467611728282292847142759794985445979974380865

noncomputable def ep594 := nat_lit 17289093679976431302099735954815672379677164017991422022023018876801756481

noncomputable def ep595 := nat_lit 43790738910600983542598435024208904084959357263332435401903591280337491963201

noncomputable def ep596 := BSN.sin_dyadic_bound_f 1427978039 1073741824 3 2 524288 165862 ep593 ep64 ep594 ep595 ep66 ep594 509149 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1427978039) qz286 0 2 ep593 ep64 ep594 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1427978039) qz287 0 2 ep595 ep66 ep594 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz410 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 93758367) qz19)

noncomputable def ep597 := @Enclosure.Real.IsNear.cos_image qz157 qz410 Bool.false 93758367 524288 545 524288 Bool.true 509149 524288 1 82850 (@Enclosure.Real.IsNear.recentre' qz157 Bool.false 805378240121178933963 4503599627370496000 1719980000427501029 1657000000000000000000 93758367 524288 545 524288 (ep592 rfl) rfl) (Enclosure.sfrac_false_div 93758367 524288) (BSN.cos_reduce1 qz410 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 100485021361798595477504) qz22) 226375608064910080 72057594037927936 Bool.false 509149 524288 28 1000000000000000 165700 82850 (BSN.sin_reduce_arg_pos_rat_q1 93758367 524288 226375608064910080 72057594037927936 28 100485021361798595477504 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 509149 524288 100485021361798595477504 75557863725914323419136 1427978039 1073741824 165862 165700 (ep596 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep598 := nat_lit 9302566327572311273092231463766288972017791124478631054118113256156342103361

noncomputable def ep599 := nat_lit 27873120795356980956672494919389235571294019045399910318310293730715422797121

noncomputable def ep600 := BSN.cos_dyadic_bound_f 1427978039 1073741824 3 2 524288 165862 ep598 ep57 ep594 ep599 ep60 ep594 125076 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1427978039) qz282 0 2 ep598 ep57 ep594 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1427978039) qz283 0 2 ep599 ep60 ep594 rfl rfl rfl rfl) rfl rfl

noncomputable def ep601 := @Enclosure.Real.IsNear.sin_image qz157 qz410 Bool.false 93758367 524288 545 524288 Bool.false 125076 524288 1 82850 (@Enclosure.Real.IsNear.recentre' qz157 Bool.false 805378240121178933963 4503599627370496000 1719980000427501029 1657000000000000000000 93758367 524288 545 524288 (ep592 rfl) rfl) (Enclosure.sfrac_false_div 93758367 524288) (BSN.sin_reduce1 qz410 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 100485021361798595477504) qz22) 226375608064910080 72057594037927936 Bool.false 125076 524288 28 1000000000000000 165700 82850 (BSN.sin_reduce_arg_pos_rat_q1 93758367 524288 226375608064910080 72057594037927936 28 100485021361798595477504 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 125076 524288 100485021361798595477504 75557863725914323419136 1427978039 1073741824 165862 165700 (ep600 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep602 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz39 (Real.cos qz157)) (@HMul.hMul Real Real Real qz0 qz39 (@Neg.neg Real Real.instNeg (Real.sin qz157))) Bool.true 94377386087 274877906944 4254577074241 11386817295155200 Bool.true 5796115647 68719476736 529833356277 1423352161894400 (@Enclosure.Real.IsNear.mulLit_ft qz39 (Real.cos qz157) 185363 524288 1 524288 509149 524288 22838769 21718630400 94377386087 274877906944 4254577074241 11386817295155200 qz316 (@Enclosure.Real.IsNear.recentre' (Real.cos qz157) Bool.true 509149 524288 45677538 43437260800 509149 524288 22838769 21718630400 (ep597 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz39 (@Neg.neg Real Real.instNeg (Real.sin qz157)) 185363 524288 1 524288 31269 131072 22838769 21718630400 5796115647 68719476736 529833356277 1423352161894400 qz316 (@Enclosure.Real.IsNear.neg (Real.sin qz157) Bool.false 31269 131072 22838769 21718630400 (@Enclosure.Real.IsNear.recentre' (Real.sin qz157) Bool.false 125076 524288 45677538 43437260800 31269 131072 22838769 21718630400 (ep601 rfl rfl) rfl)) rfl)

noncomputable def ep603 := @ep516 94377386087 274877906944 4254577074241 11386817295155200 Bool.true 5796115647 68719476736 529833356277 1423352161894400 Bool.false 7479492029223092092928 217681867921 274877906944 40555495354353 11386817295155200 Bool.false 1319687117717991587840 19203975065 274877906944 40415556070553 11386817295155200 (ep517 (BSN.head_sum_c_succ qz140 7 8 rfl rfl) (ep590 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep591 ep602) rfl rfl

theorem EMRow23.d11 : Enclosure.Complex.IsNear qz139 Bool.false 217681867921 274877906944 40555495354353 11386817295155200 Bool.false 19203975065 274877906944 40415556070553 11386817295155200 := ep515 (BSN.head_sum_c_succ qz140 8 9 rfl rfl) (ep603 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable abbrev qz158 := (BSN.headSumC qz400 17)

noncomputable abbrev qz159 := (@HPow.hPow Complex Complex Complex qz273 (@Nat.cast Complex Complex.instNatCast 16) qz401)

noncomputable def ep604 := @Enclosure.Complex.IsNear.of_eq qz158 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz140 16) qz159) Bool.false 35680143545 17179869184 6815220077747 1138681729515520 Bool.true 12161664627 68719476736 6794409980447 1138681729515520

noncomputable def ep605 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz140 16) qz159 Bool.false 505677488853 274877906944 65138069662377 11386817295155200 Bool.true 17585120465 68719476736 32471860169751 5693408647577600 Bool.false

noncomputable abbrev qz160 := (@HPow.hPow Complex Complex Complex qz273 (@Nat.cast Complex Complex.instNatCast 15) qz401)

noncomputable def ep606 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz140 16) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz140 15) qz160) Bool.false 505677488853 274877906944 65138069662377 11386817295155200 Bool.true 17585120465 68719476736 32471860169751 5693408647577600

noncomputable def ep607 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz140 15) qz160 Bool.false 440626849997 274877906944 62026433621509 11386817295155200 Bool.true 10489243387 68719476736 30921652419917 5693408647577600 Bool.false

noncomputable abbrev qz161 := (@HPow.hPow Complex Complex Complex qz273 (@Nat.cast Complex Complex.instNatCast 14) qz401)

noncomputable def ep608 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz140 15) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz140 14) qz161) Bool.false 440626849997 274877906944 62026433621509 11386817295155200 Bool.true 10489243387 68719476736 30921652419917 5693408647577600

noncomputable def ep609 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz140 14) qz161 Bool.false 387444484931 274877906944 58810496938641 11386817295155200 Bool.false 8723811305 274877906944 58628107717491 11386817295155200 Bool.false

noncomputable abbrev qz162 := (@HPow.hPow Complex Complex Complex qz273 (@Nat.cast Complex Complex.instNatCast 13) qz401)

noncomputable def ep610 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz140 14) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz140 13) qz162) Bool.false 387444484931 274877906944 58810496938641 11386817295155200 Bool.false 8723811305 274877906944 58628107717491 11386817295155200

noncomputable def ep611 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz140 13) qz162 Bool.false 163874380845 137438953472 27736229807069 5693408647577600 Bool.false 56142338405 274877906944 55293567947163 11386817295155200 Bool.false

noncomputable abbrev qz163 := (@HPow.hPow Complex Complex Complex qz273 (@Nat.cast Complex Complex.instNatCast 12) qz401)

noncomputable def ep612 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz140 13) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz140 12) qz163) Bool.false 163874380845 137438953472 27736229807069 5693408647577600 Bool.false 56142338405 274877906944 55293567947163 11386817295155200

noncomputable def ep613 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz140 12) qz163 Bool.false 7768718311 8589934592 25997074112569 5693408647577600 Bool.false 61779785957 274877906944 51835377260613 11386817295155200 Bool.false

noncomputable abbrev qz164 := (@HPow.hPow Complex Complex Complex qz273 (@Nat.cast Complex Complex.instNatCast 11) qz401)

noncomputable def ep614 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz140 12) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz140 11) qz164) Bool.false 7768718311 8589934592 25997074112569 5693408647577600 Bool.false 61779785957 274877906944 51835377260613 11386817295155200

noncomputable def ep615 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz140 11) qz164 Bool.false 26643128479 34359738368 24187252411309 5693408647577600 Bool.true 13132903669 274877906944 48205393598143 11386817295155200 Bool.false

noncomputable abbrev qz165 := (@HPow.hPow Complex Complex Complex qz273 (@Nat.cast Complex Complex.instNatCast 10) qz401)

noncomputable def ep616 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz140 11) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz140 10) qz165) Bool.false 26643128479 34359738368 24187252411309 5693408647577600 Bool.true 13132903669 274877906944 48205393598143 11386817295155200

noncomputable def ep617 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz140 10) qz165 Bool.false 149819973871 137438953472 11141579234461 2846704323788800 Bool.true 21761870239 274877906944 44416661047469 11386817295155200 Bool.true

noncomputable abbrev qz166 := (@HPow.hPow Complex Complex Complex qz273 (@Nat.cast Complex Complex.instNatCast 9) qz401)

noncomputable def ep618 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz140 10) (@HAdd.hAdd Complex Complex Complex qz4 qz139 qz166) Bool.false 149819973871 137438953472 11141579234461 2846704323788800 Bool.true 21761870239 274877906944 44416661047469 11386817295155200

noncomputable def ep619 := @Enclosure.Complex.IsNear.addLitP qz139 qz166 Bool.false 217681867921 274877906944 40555495354353 11386817295155200 Bool.false 19203975065 274877906944 40415556070553 11386817295155200 Bool.false

noncomputable abbrev qz167 := (@HMul.hMul Real Real Real qz266 qz402 qz318)

noncomputable def ep620 := @Enclosure.Complex.IsNear.of_eq qz166 (Complex.mk (@HMul.hMul Real Real Real qz0 qz49 (Real.cos qz167)) (@HMul.hMul Real Real Real qz0 qz49 (@Neg.neg Real Real.instNeg (Real.sin qz167)))) Bool.false 81958079821 274877906944 4010821583491 11386817295155200 Bool.true 5120730663 34359738368 1000276244229 2846704323788800 (BSN.cpow_neg_s_mk qz149 85999 1000 9 qz150 rfl)

noncomputable def ep621 := @Enclosure.Real.IsNear.mulLit_ff qz149 qz318 85999 1000 0 1 9895417793173221 4503599627370496 20000000004971 1657000000000000000 850996034795103832779 4503599627370496000 1719980000427501029 1657000000000000000000 qz151 (BSN.isNear_log_sfrac 9 1 9895417793173221 4503599627370496 20000000004971 1657000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz319) Bool.false 20752195215788806766592 9444732965739290427392 1000000000248550 82850000000000000000 9895417793173221 4503599627370496 20000000004971 1657000000000000000 (BSN.log_rat_reduce_isNear 9 1 3 18 16 30876 262144 24973259072661432 36028797018963968 82850 1000000000000000 rfl rfl rfl rfl (ep179 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep622 := nat_lit 61357579310158682765939340849709056

noncomputable def ep623 := BSN.cos_dyadic_bound_f 497699328 1073741824 2 1 524288 165862 ep622 ep126 ep622 ep622 ep127 ep622 468967 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 497699328) qz282 0 1 ep622 ep126 ep622 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 497699328) qz283 0 1 ep622 ep127 ep622 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz411 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 99068977) qz19)

noncomputable def ep624 := @Enclosure.Real.IsNear.cos_image qz167 qz411 Bool.false 99068977 524288 545 524288 Bool.false 468967 524288 1 82850 (@Enclosure.Real.IsNear.recentre' qz167 Bool.false 850996034795103832779 4503599627370496000 1719980000427501029 1657000000000000000000 99068977 524288 545 524288 (ep621 rfl) rfl) (Enclosure.sfrac_false_div 99068977 524288) (BSN.cos_reduce0 qz411 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 35022476701370515718144) qz22) 226375608064910080 72057594037927936 Bool.false 468967 524288 30 1000000000000000 165700 82850 (BSN.sin_reduce_arg_pos_rat_q0 99068977 524288 226375608064910080 72057594037927936 30 35022476701370515718144 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 468967 524288 35022476701370515718144 75557863725914323419136 497699328 1073741824 165862 165700 (ep623 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep625 := BSN.sin_dyadic_bound_f 497699328 1073741824 2 1 524288 165862 ep622 ep80 ep622 ep622 ep81 ep622 234408 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 497699328) qz286 0 1 ep622 ep80 ep622 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 497699328) qz287 0 1 ep622 ep81 ep622 rfl rfl rfl rfl) rfl rfl

noncomputable def ep626 := @Enclosure.Real.IsNear.sin_image qz167 qz411 Bool.false 99068977 524288 545 524288 Bool.false 234408 524288 1 82850 (@Enclosure.Real.IsNear.recentre' qz167 Bool.false 850996034795103832779 4503599627370496000 1719980000427501029 1657000000000000000000 99068977 524288 545 524288 (ep621 rfl) rfl) (Enclosure.sfrac_false_div 99068977 524288) (BSN.sin_reduce0 qz411 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 35022476701370515718144) qz22) 226375608064910080 72057594037927936 Bool.false 234408 524288 30 1000000000000000 165700 82850 (BSN.sin_reduce_arg_pos_rat_q0 99068977 524288 226375608064910080 72057594037927936 30 35022476701370515718144 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 234408 524288 35022476701370515718144 75557863725914323419136 497699328 1073741824 165862 165700 (ep625 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep627 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz49 (Real.cos qz167)) (@HMul.hMul Real Real Real qz0 qz49 (@Neg.neg Real Real.instNeg (Real.sin qz167))) Bool.false 81958079821 274877906944 4010821583491 11386817295155200 Bool.true 5120730663 34359738368 1000276244229 2846704323788800 (@Enclosure.Real.IsNear.mulLit_ff qz49 (Real.cos qz167) 174763 524288 1 524288 468967 524288 22838769 21718630400 81958079821 274877906944 4010821583491 11386817295155200 qz321 (@Enclosure.Real.IsNear.recentre' (Real.cos qz167) Bool.false 468967 524288 45677538 43437260800 468967 524288 22838769 21718630400 (ep624 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz49 (@Neg.neg Real Real.instNeg (Real.sin qz167)) 174763 524288 1 524288 29301 65536 22838769 21718630400 5120730663 34359738368 1000276244229 2846704323788800 qz321 (@Enclosure.Real.IsNear.neg (Real.sin qz167) Bool.false 29301 65536 22838769 21718630400 (@Enclosure.Real.IsNear.recentre' (Real.sin qz167) Bool.false 234408 524288 45677538 43437260800 29301 65536 22838769 21718630400 (ep626 rfl rfl) rfl)) rfl)

noncomputable def ep628 := @ep619 81958079821 274877906944 4010821583491 11386817295155200 Bool.true 5120730663 34359738368 1000276244229 2846704323788800 Bool.false 82364401672130498920448 149819973871 137438953472 11141579234461 2846704323788800 Bool.true 747732167810405629952 21761870239 274877906944 44416661047469 11386817295155200 EMRow23.d11 (ep620 ep627) rfl rfl

noncomputable abbrev qz168 := (@HMul.hMul Real Real Real qz266 qz402 (Real.log (Enclosure.sfrac Bool.false 10 1)))

noncomputable def ep629 := @Enclosure.Complex.IsNear.of_eq qz165 (Complex.mk (@HMul.hMul Real Real Real qz0 qz51 (Real.cos qz168)) (@HMul.hMul Real Real Real qz0 qz51 (@Neg.neg Real Real.instNeg (Real.sin qz168)))) Bool.true 43247459955 137438953472 1904093942387 5693408647577600 Bool.false 4314483285 137438953472 1894366275337 5693408647577600 (BSN.cpow_neg_s_mk qz149 85999 1000 10 qz150 rfl)

noncomputable def ep630 := @Enclosure.Real.IsNear.mulLit_ff qz149 qz53 85999 1000 0 1 10369908600166117 4503599627370496 20000000004971 1657000000000000000 891801769705685895883 4503599627370496000 1719980000427501029 1657000000000000000000 qz151 (BSN.isNear_log_sfrac 10 1 10369908600166117 4503599627370496 20000000004971 1657000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz323) Bool.false 21747274560655572598784 9444732965739290427392 1000000000248550 82850000000000000000 10369908600166117 4503599627370496 20000000004971 1657000000000000000 (BSN.log_rat_reduce_isNear 10 1 3 20 16 58495 262144 24973259072661432 36028797018963968 82850 1000000000000000 rfl rfl rfl rfl (ep194 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep631 := nat_lit 129940966577458139291973115100641

noncomputable def ep632 := BSN.cos_dyadic_bound_f 106766873 1073741824 2 1 524288 165862 ep631 ep126 ep631 ep631 ep127 ep631 521698 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 106766873) qz282 0 1 ep631 ep126 ep631 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 106766873) qz283 0 1 ep631 ep127 ep631 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz412 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 51909695) qz497)

noncomputable def ep633 := @Enclosure.Real.IsNear.cos_image qz168 qz412 Bool.false 51909695 262144 545 524288 Bool.true 521698 524288 1 82850 (@Enclosure.Real.IsNear.recentre' qz168 Bool.false 891801769705685895883 4503599627370496000 1719980000427501029 1657000000000000000000 51909695 262144 545 524288 (ep630 rfl) rfl) (Enclosure.sfrac_false_div 51909695 262144) (BSN.cos_reduce2 qz412 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 3756525413773890027520) qz325) 226375608064910080 72057594037927936 Bool.false 521698 524288 31 1000000000000000 165700 82850 (BSN.sin_reduce_arg_pos_rat_q2 51909695 262144 226375608064910080 72057594037927936 31 3756525413773890027520 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 521698 524288 3756525413773890027520 37778931862957161709568 106766873 1073741824 165862 165700 (ep632 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep634 := BSN.sin_dyadic_bound_f 106766873 1073741824 1 0 524288 165862 0 1 1 0 1 1 52046 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 106766873) qz286 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 106766873) qz287 0 0 rfl) rfl rfl

noncomputable def ep635 := @Enclosure.Real.IsNear.sin_image qz168 qz412 Bool.false 51909695 262144 545 524288 Bool.true 52046 524288 1 82850 (@Enclosure.Real.IsNear.recentre' qz168 Bool.false 891801769705685895883 4503599627370496000 1719980000427501029 1657000000000000000000 51909695 262144 545 524288 (ep630 rfl) rfl) (Enclosure.sfrac_false_div 51909695 262144) (BSN.sin_reduce2 qz412 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 3756525413773890027520) qz325) 226375608064910080 72057594037927936 Bool.false 52046 524288 31 1000000000000000 165700 82850 (BSN.sin_reduce_arg_pos_rat_q2 51909695 262144 226375608064910080 72057594037927936 31 3756525413773890027520 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 52046 524288 3756525413773890027520 37778931862957161709568 106766873 1073741824 165862 165700 (ep634 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep636 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz51 (Real.cos qz168)) (@HMul.hMul Real Real Real qz0 qz51 (@Neg.neg Real Real.instNeg (Real.sin qz168))) Bool.true 43247459955 137438953472 1904093942387 5693408647577600 Bool.false 4314483285 137438953472 1894366275337 5693408647577600 (@Enclosure.Real.IsNear.mulLit_ft qz51 (Real.cos qz168) 165795 524288 1 524288 260849 262144 22838769 21718630400 43247459955 137438953472 1904093942387 5693408647577600 qz326 (@Enclosure.Real.IsNear.recentre' (Real.cos qz168) Bool.true 521698 524288 45677538 43437260800 260849 262144 22838769 21718630400 (ep633 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz51 (@Neg.neg Real Real.instNeg (Real.sin qz168)) 165795 524288 1 524288 26023 262144 22838769 21718630400 4314483285 137438953472 1894366275337 5693408647577600 qz326 (@Enclosure.Real.IsNear.neg (Real.sin qz168) Bool.true 26023 262144 22838769 21718630400 (@Enclosure.Real.IsNear.recentre' (Real.sin qz168) Bool.true 52046 524288 45677538 43437260800 26023 262144 22838769 21718630400 (ep635 rfl rfl) rfl)) rfl)

noncomputable def ep637 := @ep617 43247459955 137438953472 1904093942387 5693408647577600 Bool.false 4314483285 137438953472 1894366275337 5693408647577600 Bool.false 14647214781495196516352 26643128479 34359738368 24187252411309 5693408647577600 Bool.true 1804972536315949088768 13132903669 274877906944 48205393598143 11386817295155200 (ep618 (BSN.head_sum_c_succ qz140 9 10 rfl rfl) (ep628 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep629 ep636) rfl rfl

noncomputable abbrev qz169 := (@HMul.hMul Real Real Real qz266 qz402 (Real.log (Enclosure.sfrac Bool.false 11 1)))

noncomputable def ep638 := @Enclosure.Complex.IsNear.of_eq qz164 (Complex.mk (@HMul.hMul Real Real Real qz0 qz54 (Real.cos qz169)) (@HMul.hMul Real Real Real qz0 qz54 (@Neg.neg Real Real.instNeg (Real.sin qz169)))) Bool.false 4431744765 34359738368 90491085063 284670432378880 Bool.false 37456344813 137438953472 362998366247 1138681729515520 (BSN.cpow_neg_s_mk qz149 85999 1000 11 qz150 rfl)

noncomputable def ep639 := @Enclosure.Real.IsNear.mulLit_ff qz149 qz56 85999 1000 0 1 10799147631728357 4503599627370496 20000000004971 1657000000000000000 928715897181006973643 4503599627370496000 1719980000427501029 1657000000000000000000 qz151 (BSN.isNear_log_sfrac 11 1 10799147631728357 4503599627370496 20000000004971 1657000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz328) Bool.false 22647454054174387339264 9444732965739290427392 1000000000248550 82850000000000000000 10799147631728357 4503599627370496 20000000004971 1657000000000000000 (BSN.log_rat_reduce_isNear 11 1 3 22 16 83480 262144 24973259072661432 36028797018963968 82850 1000000000000000 rfl rfl rfl rfl (ep208 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep640 := nat_lit 50749095943626125691827057433477376

noncomputable def ep641 := BSN.sin_dyadic_bound_f 474632068 1073741824 2 1 524288 165862 ep640 ep80 ep640 ep640 ep81 ep640 224280 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 474632068) qz286 0 1 ep640 ep80 ep640 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 474632068) qz287 0 1 ep640 ep81 ep640 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz413 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 13514595) qz496)

noncomputable def ep642 := @Enclosure.Real.IsNear.cos_image qz169 qz413 Bool.false 13514595 65536 545 524288 Bool.false 224280 524288 1 82850 (@Enclosure.Real.IsNear.recentre' qz169 Bool.false 928715897181006973643 4503599627370496000 1719980000427501029 1657000000000000000000 13514595 65536 545 524288 (ep639 rfl) rfl) (Enclosure.sfrac_false_div 13514595 65536) (BSN.cos_reduce3 qz413 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 4174907825426331074560) qz310) 226375608064910080 72057594037927936 Bool.false 224280 524288 32 1000000000000000 165700 82850 (BSN.sin_reduce_arg_pos_rat_q3 13514595 65536 226375608064910080 72057594037927936 32 4174907825426331074560 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 224280 524288 4174907825426331074560 9444732965739290427392 474632068 1073741824 165862 165700 (ep641 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep643 := BSN.cos_dyadic_bound_f 474632068 1073741824 2 1 524288 165862 ep640 ep126 ep640 ep640 ep127 ep640 473894 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 474632068) qz282 0 1 ep640 ep126 ep640 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 474632068) qz283 0 1 ep640 ep127 ep640 rfl rfl rfl rfl) rfl rfl

noncomputable def ep644 := @Enclosure.Real.IsNear.sin_image qz169 qz413 Bool.false 13514595 65536 545 524288 Bool.true 473894 524288 1 82850 (@Enclosure.Real.IsNear.recentre' qz169 Bool.false 928715897181006973643 4503599627370496000 1719980000427501029 1657000000000000000000 13514595 65536 545 524288 (ep639 rfl) rfl) (Enclosure.sfrac_false_div 13514595 65536) (BSN.sin_reduce3 qz413 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 4174907825426331074560) qz310) 226375608064910080 72057594037927936 Bool.false 473894 524288 32 1000000000000000 165700 82850 (BSN.sin_reduce_arg_pos_rat_q3 13514595 65536 226375608064910080 72057594037927936 32 4174907825426331074560 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 473894 524288 4174907825426331074560 9444732965739290427392 474632068 1073741824 165862 165700 (ep643 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep645 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz54 (Real.cos qz169)) (@HMul.hMul Real Real Real qz0 qz54 (@Neg.neg Real Real.instNeg (Real.sin qz169))) Bool.false 4431744765 34359738368 90491085063 284670432378880 Bool.false 37456344813 137438953472 362998366247 1138681729515520 (@Enclosure.Real.IsNear.mulLit_ff qz54 (Real.cos qz169) 158079 524288 1 524288 28035 65536 22838769 21718630400 4431744765 34359738368 90491085063 284670432378880 qz330 (@Enclosure.Real.IsNear.recentre' (Real.cos qz169) Bool.false 224280 524288 45677538 43437260800 28035 65536 22838769 21718630400 (ep642 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz54 (@Neg.neg Real Real.instNeg (Real.sin qz169)) 158079 524288 1 524288 236947 262144 22838769 21718630400 37456344813 137438953472 362998366247 1138681729515520 qz330 (@Enclosure.Real.IsNear.neg (Real.sin qz169) Bool.true 236947 262144 22838769 21718630400 (@Enclosure.Real.IsNear.recentre' (Real.sin qz169) Bool.true 473894 524288 45677538 43437260800 236947 262144 22838769 21718630400 (ep644 rfl rfl) rfl)) rfl)

noncomputable def ep646 := @ep615 4431744765 34359738368 90491085063 284670432378880 Bool.false 37456344813 137438953472 362998366247 1138681729515520 Bool.false 1067724514482603425792 7768718311 8589934592 25997074112569 5693408647577600 Bool.false 8490949127654241992704 61779785957 274877906944 51835377260613 11386817295155200 (ep616 (BSN.head_sum_c_succ qz140 10 11 rfl rfl) (ep637 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep638 ep645) rfl rfl

noncomputable abbrev qz170 := (@HMul.hMul Real Real Real qz266 qz402 (Real.log (Enclosure.sfrac Bool.false 12 1)))

noncomputable def ep647 := @Enclosure.Complex.IsNear.of_eq qz163 (Complex.mk (@HMul.hMul Real Real Real qz0 qz57 (Real.cos qz170)) (@HMul.hMul Real Real Real qz0 qz57 (@Neg.neg Real Real.instNeg (Real.sin qz170)))) Bool.false 39574887869 137438953472 17391556945 56934086475776 Bool.true 44042559 2147483648 69163813731 227736345903104 (BSN.cpow_neg_s_mk qz149 85999 1000 12 qz150 rfl)

noncomputable def ep648 := @Enclosure.Real.IsNear.mulLit_ff qz149 qz59 85999 1000 0 1 11191020447815397 4503599627370496 20000000004971 1657000000000000000 962416567491676326603 4503599627370496000 1719980000427501029 1657000000000000000000 qz151 (BSN.isNear_log_sfrac 12 1 11191020447815397 4503599627370496 20000000004971 1657000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz332) Bool.false 23469270914176955449344 9444732965739290427392 1000000000248550 82850000000000000000 11191020447815397 4503599627370496 20000000004971 1657000000000000000 (BSN.log_rat_reduce_isNear 12 1 3 24 16 106290 262144 24973259072661432 36028797018963968 82850 1000000000000000 rfl rfl rfl rfl (ep223 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep649 := BSN.cos_dyadic_bound_f 76348655 1073741824 1 0 524288 165862 0 1 1 0 1 1 522962 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 76348655) qz282 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 76348655) qz283 0 0 rfl) rfl rfl

noncomputable abbrev qz414 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 56020017) qz497)

noncomputable def ep650 := @Enclosure.Real.IsNear.cos_image qz170 qz414 Bool.false 56020017 262144 545 524288 Bool.false 522962 524288 1 82850 (@Enclosure.Real.IsNear.recentre' qz170 Bool.false 962416567491676326603 4503599627370496000 1719980000427501029 1657000000000000000000 56020017 262144 545 524288 (ep648 rfl) rfl) (Enclosure.sfrac_false_div 56020017 262144) (BSN.cos_reduce0 qz414 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 2686279490424069423104) qz325) 226375608064910080 72057594037927936 Bool.false 522962 524288 34 1000000000000000 165700 82850 (BSN.sin_reduce_arg_pos_rat_q0 56020017 262144 226375608064910080 72057594037927936 34 2686279490424069423104 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 522962 524288 2686279490424069423104 37778931862957161709568 76348655 1073741824 165862 165700 (ep649 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep651 := BSN.sin_dyadic_bound_f 76348655 1073741824 1 0 524288 165862 0 1 1 0 1 1 37248 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 76348655) qz286 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 76348655) qz287 0 0 rfl) rfl rfl

noncomputable def ep652 := @Enclosure.Real.IsNear.sin_image qz170 qz414 Bool.false 56020017 262144 545 524288 Bool.false 37248 524288 1 82850 (@Enclosure.Real.IsNear.recentre' qz170 Bool.false 962416567491676326603 4503599627370496000 1719980000427501029 1657000000000000000000 56020017 262144 545 524288 (ep648 rfl) rfl) (Enclosure.sfrac_false_div 56020017 262144) (BSN.sin_reduce0 qz414 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 2686279490424069423104) qz325) 226375608064910080 72057594037927936 Bool.false 37248 524288 34 1000000000000000 165700 82850 (BSN.sin_reduce_arg_pos_rat_q0 56020017 262144 226375608064910080 72057594037927936 34 2686279490424069423104 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 37248 524288 2686279490424069423104 37778931862957161709568 76348655 1073741824 165862 165700 (ep651 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep653 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz57 (Real.cos qz170)) (@HMul.hMul Real Real Real qz0 qz57 (@Neg.neg Real Real.instNeg (Real.sin qz170))) Bool.false 39574887869 137438953472 17391556945 56934086475776 Bool.true 44042559 2147483648 69163813731 227736345903104 (@Enclosure.Real.IsNear.mulLit_ff qz57 (Real.cos qz170) 151349 524288 1 524288 261481 262144 22838769 21718630400 39574887869 137438953472 17391556945 56934086475776 qz334 (@Enclosure.Real.IsNear.recentre' (Real.cos qz170) Bool.false 522962 524288 45677538 43437260800 261481 262144 22838769 21718630400 (ep650 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz57 (@Neg.neg Real Real.instNeg (Real.sin qz170)) 151349 524288 1 524288 291 4096 22838769 21718630400 44042559 2147483648 69163813731 227736345903104 qz334 (@Enclosure.Real.IsNear.neg (Real.sin qz170) Bool.false 291 4096 22838769 21718630400 (@Enclosure.Real.IsNear.recentre' (Real.sin qz170) Bool.false 37248 524288 45677538 43437260800 291 4096 22838769 21718630400 (ep652 rfl rfl) rfl)) rfl)

noncomputable def ep654 := @ep613 39574887869 137438953472 17391556945 56934086475776 Bool.true 44042559 2147483648 69163813731 227736345903104 Bool.false 1407670212763047690240 163874380845 137438953472 27736229807069 5693408647577600 Bool.false 120564753685219901440 56142338405 274877906944 55293567947163 11386817295155200 (ep614 (BSN.head_sum_c_succ qz140 11 12 rfl rfl) (ep646 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep647 ep653) rfl rfl

noncomputable abbrev qz171 := (@HMul.hMul Real Real Real qz266 qz402 (Real.log (Enclosure.sfrac Bool.false 13 1)))

noncomputable def ep655 := @Enclosure.Complex.IsNear.of_eq qz162 (Complex.mk (@HMul.hMul Real Real Real qz0 qz60 (Real.cos qz171)) (@HMul.hMul Real Real Real qz0 qz60 (@Neg.neg Real Real.instNeg (Real.sin qz171)))) Bool.false 59695723241 274877906944 3338037324503 11386817295155200 Bool.true 11854631775 68719476736 416817471291 1423352161894400 (BSN.cpow_neg_s_mk qz149 85999 1000 13 qz150 rfl)

noncomputable def ep656 := @Enclosure.Real.IsNear.mulLit_ff qz149 qz62 85999 1000 0 1 11551488463034085 4503599627370496 20000000004971 1657000000000000000 198683291266493655183 900719925474099200 1719980000427501029 1657000000000000000000 qz151 (BSN.isNear_log_sfrac 13 1 11551488463034085 4503599627370496 20000000004971 1657000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz336) Bool.false 24225227133228857425920 9444732965739290427392 1000000000248550 82850000000000000000 11551488463034085 4503599627370496 20000000004971 1657000000000000000 (BSN.log_rat_reduce_isNear 13 1 3 26 16 127272 262144 24973259072661432 36028797018963968 82850 1000000000000000 rfl rfl rfl rfl (ep234 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep657 := nat_lit 269903756264271518709433969695107856

noncomputable def ep658 := BSN.cos_dyadic_bound_f 720779178 1073741824 2 1 524288 165862 ep657 ep126 ep657 ep657 ep127 ep657 410531 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 720779178) qz282 0 1 ep657 ep126 ep657 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 720779178) qz283 0 1 ep657 ep127 ep657 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz415 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 903507) (@Nat.cast Real Real.instNatCast 4096))

noncomputable def ep659 := @Enclosure.Real.IsNear.cos_image qz171 qz415 Bool.false 903507 4096 545 524288 Bool.false 410531 524288 1 82850 (@Enclosure.Real.IsNear.recentre' qz171 Bool.false 198683291266493655183 900719925474099200 1719980000427501029 1657000000000000000000 903507 4096 545 524288 (ep656 rfl) rfl) (Enclosure.sfrac_false_div 903507 4096) (BSN.cos_reduce0 qz415 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 396252544110275067904) (@Nat.cast Real Real.instNatCast 590295810358705651712)) 226375608064910080 72057594037927936 Bool.false 410531 524288 35 1000000000000000 165700 82850 (BSN.sin_reduce_arg_pos_rat_q0 903507 4096 226375608064910080 72057594037927936 35 396252544110275067904 590295810358705651712 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 410531 524288 396252544110275067904 590295810358705651712 720779178 1073741824 165862 165700 (ep658 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep660 := BSN.sin_dyadic_bound_f 720779178 1073741824 2 1 524288 165862 ep657 ep80 ep657 ep657 ep81 ep657 326100 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 720779178) qz286 0 1 ep657 ep80 ep657 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 720779178) qz287 0 1 ep657 ep81 ep657 rfl rfl rfl rfl) rfl rfl

noncomputable def ep661 := @Enclosure.Real.IsNear.sin_image qz171 qz415 Bool.false 903507 4096 545 524288 Bool.false 326100 524288 1 82850 (@Enclosure.Real.IsNear.recentre' qz171 Bool.false 198683291266493655183 900719925474099200 1719980000427501029 1657000000000000000000 903507 4096 545 524288 (ep656 rfl) rfl) (Enclosure.sfrac_false_div 903507 4096) (BSN.sin_reduce0 qz415 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 396252544110275067904) (@Nat.cast Real Real.instNatCast 590295810358705651712)) 226375608064910080 72057594037927936 Bool.false 326100 524288 35 1000000000000000 165700 82850 (BSN.sin_reduce_arg_pos_rat_q0 903507 4096 226375608064910080 72057594037927936 35 396252544110275067904 590295810358705651712 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 326100 524288 396252544110275067904 590295810358705651712 720779178 1073741824 165862 165700 (ep660 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep662 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz60 (Real.cos qz171)) (@HMul.hMul Real Real Real qz0 qz60 (@Neg.neg Real Real.instNeg (Real.sin qz171))) Bool.false 59695723241 274877906944 3338037324503 11386817295155200 Bool.true 11854631775 68719476736 416817471291 1423352161894400 (@Enclosure.Real.IsNear.mulLit_ff qz60 (Real.cos qz171) 145411 524288 1 524288 410531 524288 22838769 21718630400 59695723241 274877906944 3338037324503 11386817295155200 qz338 (@Enclosure.Real.IsNear.recentre' (Real.cos qz171) Bool.false 410531 524288 45677538 43437260800 410531 524288 22838769 21718630400 (ep659 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz60 (@Neg.neg Real Real.instNeg (Real.sin qz171)) 145411 524288 1 524288 81525 131072 22838769 21718630400 11854631775 68719476736 416817471291 1423352161894400 qz338 (@Enclosure.Real.IsNear.neg (Real.sin qz171) Bool.false 81525 131072 22838769 21718630400 (@Enclosure.Real.IsNear.recentre' (Real.sin qz171) Bool.false 326100 524288 45677538 43437260800 81525 131072 22838769 21718630400 (ep661 rfl rfl) rfl)) rfl)

noncomputable def ep663 := @ep611 59695723241 274877906944 3338037324503 11386817295155200 Bool.true 11854631775 68719476736 416817471291 1423352161894400 Bool.false 53249964537414714130432 387444484931 274877906944 58810496938641 11386817295155200 Bool.false 599495748023201300480 8723811305 274877906944 58628107717491 11386817295155200 (ep612 (BSN.head_sum_c_succ qz140 12 13 rfl rfl) (ep654 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep655 ep662) rfl rfl

noncomputable abbrev qz172 := (@HMul.hMul Real Real Real qz266 qz402 (Real.log (Enclosure.sfrac Bool.false 14 1)))

noncomputable def ep664 := @Enclosure.Complex.IsNear.of_eq qz161 (Complex.mk (@HMul.hMul Real Real Real qz0 qz63 (Real.cos qz172)) (@HMul.hMul Real Real Real qz0 qz63 (@Neg.neg Real Real.instNeg (Real.sin qz172)))) Bool.false 26591182533 137438953472 803984170717 2846704323788800 Bool.true 50680784853 274877906944 3215197122343 11386817295155200 (BSN.cpow_neg_s_mk qz149 85999 1000 14 qz150 rfl)

noncomputable def ep665 := @Enclosure.Real.IsNear.mulLit_ff qz149 qz65 85999 1000 0 1 11885241781671653 4503599627370496 20000000004971 1657000000000000000 1022118907981980486347 4503599627370496000 1719980000427501029 1657000000000000000000 qz151 (BSN.isNear_log_sfrac 14 1 11885241781671653 4503599627370496 20000000004971 1657000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz340) Bool.false 24925158572916270432256 9444732965739290427392 1000000000248550 82850000000000000000 11885241781671653 4503599627370496 20000000004971 1657000000000000000 (BSN.log_rat_reduce_isNear 14 1 3 28 16 146699 262144 24973259072661432 36028797018963968 82850 1000000000000000 rfl rfl rfl rfl (ep248 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep666 := nat_lit 997371358386282794564795144775698878309053260230774742885373815864321515776

noncomputable def ep667 := nat_lit 199398823944187528403757435009189778592534569285734798630342817658839296

noncomputable def ep668 := nat_lit 2991715277510960008637577919457078255369974711553752759058860761957646868736

noncomputable def ep669 := BSN.cos_dyadic_bound_f 817457766 1073741824 3 2 524288 165862 ep666 ep57 ep667 ep668 ep60 ep667 379546 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 817457766) qz282 0 2 ep666 ep57 ep667 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 817457766) qz283 0 2 ep668 ep60 ep667 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz416 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 118990301) qz19)

noncomputable def ep670 := @Enclosure.Real.IsNear.cos_image qz172 qz416 Bool.false 118990301 524288 545 524288 Bool.false 379546 524288 1 82850 (@Enclosure.Real.IsNear.recentre' qz172 Bool.false 1022118907981980486347 4503599627370496000 1719980000427501029 1657000000000000000000 118990301 524288 545 524288 (ep665 rfl) rfl) (Enclosure.sfrac_false_div 118990301 524288) (BSN.cos_reduce0 qz416 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 57523476454178094579712) qz22) 226375608064910080 72057594037927936 Bool.false 379546 524288 36 1000000000000000 165700 82850 (BSN.sin_reduce_arg_pos_rat_q0 118990301 524288 226375608064910080 72057594037927936 36 57523476454178094579712 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 379546 524288 57523476454178094579712 75557863725914323419136 817457766 1073741824 165862 165700 (ep669 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep671 := nat_lit 446540954386255067048748744990091536

noncomputable def ep672 := BSN.sin_dyadic_bound_f 817457766 1073741824 2 1 524288 165862 ep671 ep80 ep671 ep671 ep81 ep671 361693 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 817457766) qz286 0 1 ep671 ep80 ep671 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 817457766) qz287 0 1 ep671 ep81 ep671 rfl rfl rfl rfl) rfl rfl

noncomputable def ep673 := @Enclosure.Real.IsNear.sin_image qz172 qz416 Bool.false 118990301 524288 545 524288 Bool.false 361693 524288 1 82850 (@Enclosure.Real.IsNear.recentre' qz172 Bool.false 1022118907981980486347 4503599627370496000 1719980000427501029 1657000000000000000000 118990301 524288 545 524288 (ep665 rfl) rfl) (Enclosure.sfrac_false_div 118990301 524288) (BSN.sin_reduce0 qz416 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 57523476454178094579712) qz22) 226375608064910080 72057594037927936 Bool.false 361693 524288 36 1000000000000000 165700 82850 (BSN.sin_reduce_arg_pos_rat_q0 118990301 524288 226375608064910080 72057594037927936 36 57523476454178094579712 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 361693 524288 57523476454178094579712 75557863725914323419136 817457766 1073741824 165862 165700 (ep672 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep674 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz63 (Real.cos qz172)) (@HMul.hMul Real Real Real qz0 qz63 (@Neg.neg Real Real.instNeg (Real.sin qz172))) Bool.false 26591182533 137438953472 803984170717 2846704323788800 Bool.true 50680784853 274877906944 3215197122343 11386817295155200 (@Enclosure.Real.IsNear.mulLit_ff qz63 (Real.cos qz172) 140121 524288 1 524288 189773 262144 22838769 21718630400 26591182533 137438953472 803984170717 2846704323788800 qz342 (@Enclosure.Real.IsNear.recentre' (Real.cos qz172) Bool.false 379546 524288 45677538 43437260800 189773 262144 22838769 21718630400 (ep670 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz63 (@Neg.neg Real Real.instNeg (Real.sin qz172)) 140121 524288 1 524288 361693 524288 22838769 21718630400 50680784853 274877906944 3215197122343 11386817295155200 qz342 (@Enclosure.Real.IsNear.neg (Real.sin qz172) Bool.false 361693 524288 22838769 21718630400 (@Enclosure.Real.IsNear.recentre' (Real.sin qz172) Bool.false 361693 524288 45677538 43437260800 361693 524288 22838769 21718630400 (ep673 rfl rfl) rfl)) rfl)

noncomputable def ep675 := @ep609 26591182533 137438953472 803984170717 2846704323788800 Bool.true 50680784853 274877906944 3215197122343 11386817295155200 Bool.false 60559293135251606339584 440626849997 274877906944 62026433621509 11386817295155200 Bool.true 11533045070579013517312 10489243387 68719476736 30921652419917 5693408647577600 (ep610 (BSN.head_sum_c_succ qz140 13 14 rfl rfl) (ep663 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep664 ep674) rfl rfl

noncomputable abbrev qz173 := (@HMul.hMul Real Real Real qz266 qz402 (Real.log (Enclosure.sfrac Bool.false 15 1)))

noncomputable def ep676 := @Enclosure.Complex.IsNear.of_eq qz160 (Complex.mk (@HMul.hMul Real Real Real qz0 qz66 (Real.cos qz173)) (@HMul.hMul Real Real Real qz0 qz66 (@Neg.neg Real Real.instNeg (Real.sin qz173)))) Bool.false 8131329857 34359738368 777909010217 2846704323788800 Bool.true 3547938539 34359738368 775103874917 2846704323788800 (BSN.cpow_neg_s_mk qz149 85999 1000 15 qz150 rfl)

noncomputable def ep677 := @Enclosure.Real.IsNear.mulLit_ff qz149 qz68 85999 1000 0 1 12195956895733477 4503599627370496 20000000004971 1657000000000000000 1048840097076183288523 4503599627370496000 1719980000427501029 1657000000000000000000 qz151 (BSN.isNear_log_sfrac 15 1 12195956895733477 4503599627370496 20000000004971 1657000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz344) Bool.false 25576775395801252757504 9444732965739290427392 1000000000248550 82850000000000000000 12195956895733477 4503599627370496 20000000004971 1657000000000000000 (BSN.log_rat_reduce_isNear 15 1 3 30 16 164785 262144 24973259072661432 36028797018963968 82850 1000000000000000 rfl rfl rfl rfl (ep259 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep678 := nat_lit 38086746744003510036671923220710416

noncomputable def ep679 := BSN.cos_dyadic_bound_f 441767202 1073741824 2 1 524288 165862 ep678 ep126 ep678 ep678 ep127 ep678 480536 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 441767202) qz282 0 1 ep678 ep126 ep678 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 441767202) qz283 0 1 ep678 ep127 ep678 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz417 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 122101057) qz19)

noncomputable def ep680 := @Enclosure.Real.IsNear.cos_image qz173 qz417 Bool.false 122101057 524288 545 524288 Bool.false 480536 524288 1 82850 (@Enclosure.Real.IsNear.recentre' qz173 Bool.false 1048840097076183288523 4503599627370496000 1719980000427501029 1657000000000000000000 122101057 524288 545 524288 (ep677 rfl) rfl) (Enclosure.sfrac_false_div 122101057 524288) (BSN.cos_reduce0 qz417 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 31086603247732899446784) qz22) 226375608064910080 72057594037927936 Bool.false 480536 524288 37 1000000000000000 165700 82850 (BSN.sin_reduce_arg_pos_rat_q0 122101057 524288 226375608064910080 72057594037927936 37 31086603247732899446784 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 480536 524288 31086603247732899446784 75557863725914323419136 441767202 1073741824 165862 165700 (ep679 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep681 := BSN.sin_dyadic_bound_f 441767202 1073741824 2 1 524288 165862 ep678 ep80 ep678 ep678 ep81 ep678 209672 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 441767202) qz286 0 1 ep678 ep80 ep678 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 441767202) qz287 0 1 ep678 ep81 ep678 rfl rfl rfl rfl) rfl rfl

noncomputable def ep682 := @Enclosure.Real.IsNear.sin_image qz173 qz417 Bool.false 122101057 524288 545 524288 Bool.false 209672 524288 1 82850 (@Enclosure.Real.IsNear.recentre' qz173 Bool.false 1048840097076183288523 4503599627370496000 1719980000427501029 1657000000000000000000 122101057 524288 545 524288 (ep677 rfl) rfl) (Enclosure.sfrac_false_div 122101057 524288) (BSN.sin_reduce0 qz417 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 31086603247732899446784) qz22) 226375608064910080 72057594037927936 Bool.false 209672 524288 37 1000000000000000 165700 82850 (BSN.sin_reduce_arg_pos_rat_q0 122101057 524288 226375608064910080 72057594037927936 37 31086603247732899446784 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 209672 524288 31086603247732899446784 75557863725914323419136 441767202 1073741824 165862 165700 (ep681 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep683 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz66 (Real.cos qz173)) (@HMul.hMul Real Real Real qz0 qz66 (@Neg.neg Real Real.instNeg (Real.sin qz173))) Bool.false 8131329857 34359738368 777909010217 2846704323788800 Bool.true 3547938539 34359738368 775103874917 2846704323788800 (@Enclosure.Real.IsNear.mulLit_ff qz66 (Real.cos qz173) 135371 524288 1 524288 60067 65536 22838769 21718630400 8131329857 34359738368 777909010217 2846704323788800 qz346 (@Enclosure.Real.IsNear.recentre' (Real.cos qz173) Bool.false 480536 524288 45677538 43437260800 60067 65536 22838769 21718630400 (ep680 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz66 (@Neg.neg Real Real.instNeg (Real.sin qz173)) 135371 524288 1 524288 26209 65536 22838769 21718630400 3547938539 34359738368 775103874917 2846704323788800 qz346 (@Enclosure.Real.IsNear.neg (Real.sin qz173) Bool.false 26209 65536 22838769 21718630400 (@Enclosure.Real.IsNear.recentre' (Real.sin qz173) Bool.false 209672 524288 45677538 43437260800 26209 65536 22838769 21718630400 (ep682 rfl rfl) rfl)) rfl)

noncomputable def ep684 := @ep607 8131329857 34359738368 777909010217 2846704323788800 Bool.true 3547938539 34359738368 775103874917 2846704323788800 Bool.false 17374946215576316411904 505677488853 274877906944 65138069662377 11386817295155200 Bool.true 604220138347162501120 17585120465 68719476736 32471860169751 5693408647577600 (ep608 (BSN.head_sum_c_succ qz140 14 15 rfl rfl) (ep675 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep676 ep683) rfl rfl

noncomputable abbrev qz174 := (@HMul.hMul Real Real Real qz266 qz402 (Real.log (Enclosure.sfrac Bool.false 16 1)))

noncomputable def ep685 := @Enclosure.Complex.IsNear.of_eq qz159 (Complex.mk (@HMul.hMul Real Real Real qz0 qz69 (Real.cos qz174)) (@HMul.hMul Real Real Real qz0 qz69 (@Neg.neg Real Real.instNeg (Real.sin qz174)))) Bool.false 65204807867 274877906944 3014131115093 11386817295155200 Bool.false 2711727919 34359738368 375047433121 1423352161894400 (BSN.cpow_neg_s_mk qz149 85999 1000 16 qz150 rfl)

noncomputable def ep686 := @Enclosure.Real.IsNear.mulLit_ff qz149 qz71 85999 1000 0 1 3121657384082679 1125899906842624 5000000001657 414250000000000000 268459413373726311321 1125899906842624000 429995000142500343 414250000000000000000 qz151 (BSN.isNear_log_sfrac 16 1 3121657384082679 1125899906842624 5000000001657 414250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz348) Bool.false 26186360105375033720832 9444732965739290427392 1000000000331400 82850000000000000000 3121657384082679 1125899906842624 5000000001657 414250000000000000 (BSN.log_rat_reduce_isNear 16 1 4 32 32 0 262144 24973259072661432 36028797018963968 82850 1000000000000000 rfl rfl rfl rfl (ep270 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep687 := nat_lit 13038623149250105170975638869390631750629878716458227280590207324511957930625

noncomputable def ep688 := nat_lit 10505115608086949728922832098686035660263769913897832615783644216062890625

noncomputable def ep689 := nat_lit 34131766632289563243470321977387115289152112439434760672548798044991026090625

noncomputable def ep690 := BSN.sin_dyadic_bound_f 1341760815 1073741824 3 2 524288 165862 ep687 ep64 ep688 ep689 ep66 ep688 497477 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1341760815) qz286 0 2 ep687 ep64 ep688 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1341760815) qz287 0 2 ep689 ep66 ep688 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz418 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 31252789) qz495)

noncomputable def ep691 := @Enclosure.Real.IsNear.cos_image qz174 qz418 Bool.false 31252789 131072 545 524288 Bool.false 497477 524288 1 82850 (@Enclosure.Real.IsNear.recentre' qz174 Bool.false 268459413373726311321 1125899906842624000 429995000142500343 414250000000000000000 31252789 131072 545 524288 (ep686 rfl) rfl) (Enclosure.sfrac_false_div 31252789 131072) (BSN.cos_reduce3 qz418 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 23604505887171567157248) qz293) 226375608064910080 72057594037927936 Bool.false 497477 524288 37 1000000000000000 165700 82850 (BSN.sin_reduce_arg_pos_rat_q3 31252789 131072 226375608064910080 72057594037927936 37 23604505887171567157248 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 497477 524288 23604505887171567157248 18889465931478580854784 1341760815 1073741824 165862 165700 (ep690 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep692 := nat_lit 7248348467631430405977098408371989210643383184660747525934907911047115690625

noncomputable def ep693 := nat_lit 21724035171678117318473449560918595560609622014154446912573156444709221290625

noncomputable def ep694 := BSN.cos_dyadic_bound_f 1341760815 1073741824 3 2 524288 165862 ep692 ep57 ep688 ep693 ep60 ep688 165512 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1341760815) qz282 0 2 ep692 ep57 ep688 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1341760815) qz283 0 2 ep693 ep60 ep688 rfl rfl rfl rfl) rfl rfl

noncomputable def ep695 := @Enclosure.Real.IsNear.sin_image qz174 qz418 Bool.false 31252789 131072 545 524288 Bool.true 165512 524288 1 82850 (@Enclosure.Real.IsNear.recentre' qz174 Bool.false 268459413373726311321 1125899906842624000 429995000142500343 414250000000000000000 31252789 131072 545 524288 (ep686 rfl) rfl) (Enclosure.sfrac_false_div 31252789 131072) (BSN.sin_reduce3 qz418 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 23604505887171567157248) qz293) 226375608064910080 72057594037927936 Bool.false 165512 524288 37 1000000000000000 165700 82850 (BSN.sin_reduce_arg_pos_rat_q3 31252789 131072 226375608064910080 72057594037927936 37 23604505887171567157248 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 165512 524288 23604505887171567157248 18889465931478580854784 1341760815 1073741824 165862 165700 (ep694 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep696 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz69 (Real.cos qz174)) (@HMul.hMul Real Real Real qz0 qz69 (@Neg.neg Real Real.instNeg (Real.sin qz174))) Bool.false 65204807867 274877906944 3014131115093 11386817295155200 Bool.false 2711727919 34359738368 375047433121 1423352161894400 (@Enclosure.Real.IsNear.mulLit_ff qz69 (Real.cos qz174) 131071 524288 1 524288 497477 524288 22838769 21718630400 65204807867 274877906944 3014131115093 11386817295155200 qz350 (@Enclosure.Real.IsNear.recentre' (Real.cos qz174) Bool.false 497477 524288 45677538 43437260800 497477 524288 22838769 21718630400 (ep691 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz69 (@Neg.neg Real Real.instNeg (Real.sin qz174)) 131071 524288 1 524288 20689 65536 22838769 21718630400 2711727919 34359738368 375047433121 1423352161894400 qz350 (@Enclosure.Real.IsNear.neg (Real.sin qz174) Bool.true 20689 65536 22838769 21718630400 (@Enclosure.Real.IsNear.recentre' (Real.sin qz174) Bool.true 165512 524288 45677538 43437260800 20689 65536 22838769 21718630400 (ep695 rfl rfl) rfl)) rfl)

noncomputable def ep697 := @ep605 65204807867 274877906944 3014131115093 11386817295155200 Bool.false 2711727919 34359738368 375047433121 1423352161894400 Bool.false 156922930833777156423680 35680143545 17179869184 6815220077747 1138681729515520 Bool.true 417871614703080308736 12161664627 68719476736 6794409980447 1138681729515520 (ep606 (BSN.head_sum_c_succ qz140 15 16 rfl rfl) (ep684 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep685 ep696) rfl rfl

theorem EMRow23.d12 : Enclosure.Complex.IsNear qz158 Bool.false 35680143545 17179869184 6815220077747 1138681729515520 Bool.true 12161664627 68719476736 6794409980447 1138681729515520 := ep604 (BSN.head_sum_c_succ qz140 16 17 rfl rfl) (ep697 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

theorem EMRow23.d13 : @Eq Nat (Nat.pow 18 1) 18 := @Eq.refl Nat 18

noncomputable def ep698 := nat_lit 6121449664911191234209643002601

noncomputable def ep699 := nat_lit 3069755055756907586340110991360

noncomputable def ep700 := nat_lit 979917727117444440193456455464504264951

noncomputable def ep701 := nat_lit 131694842173185899336361553176821760000000

noncomputable abbrev qz509 := (@HAdd.hAdd Complex Complex Complex qz515 (@HAdd.hAdd Complex Complex Complex qz515 qz518 (@HMul.hMul Complex Complex Complex qz517 Complex.I (@HDiv.hDiv Complex Complex Complex qz519 (↑qz522) (2 : Complex)))) (@Nat.cast Complex Complex.instNatCast 2))

noncomputable abbrev qz419 := qz509

noncomputable abbrev qz175 := (Complex.Stirling.logGammaStirling 1 qz419)

noncomputable abbrev qz510 := (@HAdd.hAdd Complex Complex Complex qz515 qz518 (@HMul.hMul Complex Complex Complex qz517 Complex.I (@HDiv.hDiv Complex Complex Complex qz519 (↑qz522) (2 : Complex))))

noncomputable abbrev qz420 := qz510

noncomputable abbrev qz176 := qz420

noncomputable abbrev qz177 := (@HMul.hMul Real Real Real qz266 (@HDiv.hDiv Real Real Real qz269 qz402 (2 : Real)) (Real.log Real.pi))

noncomputable def ep702 := Complex.re (@HMul.hMul Complex Complex Complex qz72 (Complex.exp (@HMul.hMul Complex Complex Complex qz72 Complex.I ↑(@HSub.hSub Real Real Real qz355 (Complex.im (@HSub.hSub Complex Complex Complex qz73 qz175 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz176 (@Nat.cast Complex Complex.instNatCast j))))) qz177))) (zetaApproximant qz140 1 18))

noncomputable def ep703 := @Enclosure.Real.IsNear.of_eq ep702 (@HSub.hSub Real Real Real qz355 (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz355 (Complex.im (@HSub.hSub Complex Complex Complex qz73 qz175 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz176 (@Nat.cast Complex Complex.instNatCast j))))) qz177)) (Complex.re (zetaApproximant qz140 1 18))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz355 (Complex.im (@HSub.hSub Complex Complex Complex qz73 qz175 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz176 (@Nat.cast Complex Complex.instNatCast j))))) qz177)) (Complex.im (zetaApproximant qz140 1 18))))

noncomputable def ep704 := nat_lit 18364010113180316273614811260237

noncomputable def ep705 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz355 (Complex.im (@HSub.hSub Complex Complex Complex qz73 qz175 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz176 (@Nat.cast Complex Complex.instNatCast j))))) qz177)) (Complex.re (zetaApproximant qz140 1 18))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz355 (Complex.im (@HSub.hSub Complex Complex Complex qz73 qz175 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz176 (@Nat.cast Complex Complex.instNatCast j))))) qz177)) (Complex.im (zetaApproximant qz140 1 18))) ep704

noncomputable def ep706 := nat_lit 9209265167270722759020332974080

noncomputable def ep707 := nat_lit 2924453036662394482903389487140363753539

noncomputable def ep708 := nat_lit 395084526519557698009084659530465280000000

noncomputable def ep709 := nat_lit 13033905894516500542990291

noncomputable def ep710 := nat_lit 354202506433489336885397422080

noncomputable def ep711 := nat_lit 7650072344969418838489939626574520657

noncomputable def ep712 := nat_lit 197542263259778849004542329765232640000000

noncomputable def ep713 := nat_lit 6504698442953962075865937062034137697034995551148108404490240

noncomputable def ep714 := @Enclosure.Real.IsNear.mulLit_ff (Real.cos (@HSub.hSub Real Real Real qz355 (Complex.im (@HSub.hSub Complex Complex Complex qz73 qz175 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz176 (@Nat.cast Complex Complex.instNatCast j))))) qz177)) (Complex.re (zetaApproximant qz140 1 18)) 524287 524288 10742669

noncomputable def ep715 := nat_lit 35026636390336430759516851

noncomputable def ep716 := nat_lit 17565279326001592176476160

noncomputable def ep717 := nat_lit 116651931955745319521842710331

noncomputable def ep718 := nat_lit 18191042401990398897763123200000

noncomputable def ep719 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HSub.hSub Real Real Real qz355 (Complex.im (@HSub.hSub Complex Complex Complex qz73 qz175 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz176 (@Nat.cast Complex Complex.instNatCast j))))) qz177)) Bool.false 524287 524288 21485338

noncomputable abbrev qz421 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 36235885) qz19)

noncomputable def ep720 := @Enclosure.Real.IsNear.cos_image (@HSub.hSub Real Real Real qz355 (Complex.im (@HSub.hSub Complex Complex Complex qz73 qz175 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz176 (@Nat.cast Complex Complex.instNatCast j))))) qz177) qz421 Bool.false 36235885 524288 253

noncomputable def ep721 := nat_lit 260623564800000000000000000

noncomputable def ep722 := @Enclosure.Real.IsNear.recentre' (@HSub.hSub Real Real Real qz355 (Complex.im (@HSub.hSub Complex Complex Complex qz73 qz175 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz176 (@Nat.cast Complex Complex.instNatCast j))))) qz177) Bool.false 373516660664756269739 5404319552844595200 125215498393592152416463 ep721

noncomputable def ep723 := @Enclosure.Real.IsNear.subLit_ff_p (Complex.im (@HSub.hSub Complex Complex Complex qz73 qz175 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz176 (@Nat.cast Complex Complex.instNatCast j))))) qz177 3197662034078744362327 27021597764222976000 39715292593592152416463 ep721 6451730979 131072000

noncomputable def ep724 := nat_lit 244787878733254668936151040000

noncomputable def ep725 := nat_lit 108593152000000000000000000

noncomputable def ep726 := @Enclosure.Complex.IsNear.im_isNear (@HSub.hSub Complex Complex Complex qz73 qz175 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz176 (@Nat.cast Complex Complex.instNatCast j)))) Bool.true 152142613680220919649 2251799813685248000 29823221287230954641587 ep725 Bool.false 3197662034078744362327 27021597764222976000

noncomputable def ep727 := @Enclosure.Complex.IsNear.subLitP qz175 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz176 (@Nat.cast Complex Complex.instNatCast j))) Bool.true 135202738721675812649 2251799813685248000 29167861286145023121587 ep725 Bool.false 3281610536918604874327 27021597764222976000 36569564593331528851663

noncomputable def ep728 := nat_lit 342594709138708130403450250384637952

noncomputable def ep729 := nat_lit 900061846570863461986391782705856512

noncomputable abbrev qz422 := (@HSub.hSub Complex Complex Complex qz499 qz509 qz502)

noncomputable abbrev qz423 := (Complex.log qz509)

noncomputable abbrev qz178 := (@HSub.hSub Complex Complex Complex qz352 (@HMul.hMul Complex Complex Complex qz351 qz422 qz423) qz419)

noncomputable abbrev qz179 := qz419

noncomputable def ep730 := @Enclosure.Complex.IsNear.of_eq qz175 (@HAdd.hAdd Complex Complex Complex qz4 (@HAdd.hAdd Complex Complex Complex qz4 qz178 qz78) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz72 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz81 qz179 (@HSub.hSub Int Int Int qz364 qz83 (@HMul.hMul Int Int Int qz365 qz84 (@Nat.cast Int instNatCastInt k)))))) Bool.true 135202738721675812649

noncomputable def ep731 := @Enclosure.Complex.IsNear.addLitP (@HAdd.hAdd Complex Complex Complex qz4 qz178 qz78) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz72 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz81 qz179 (@HSub.hSub Int Int Int qz364 qz83 (@HMul.hMul Int Int Int qz365 qz84 (@Nat.cast Int instNatCastInt k))))) Bool.true 135202966449969700649 2251799813685248000

noncomputable def ep732 := nat_lit 2322765364556921846566712508416

noncomputable def ep733 := nat_lit 28188819868548817098361310019584000

noncomputable def ep734 := @ep731 1780263813677057843 6628000000000000000000 Bool.false 1093887587333353690653 9007199254740992000 92999000143080293 662800000000000000000 Bool.false 1737429 17179869184 3 17179869184 Bool.true 49805718857 25769803776000 85999 25769803776000 Bool.true ep732 135202738721675812649 2251799813685248000 29167861286145023121587 ep725 Bool.false ep733

noncomputable def ep735 := @Enclosure.Complex.IsNear.addLitP qz178 qz78 Bool.true 137272230153574948649 2251799813685248000 1754980000200495343 6628000000000000000000

noncomputable def ep736 := nat_lit 17721323218530428603465728

noncomputable def ep737 := @ep735 Bool.false 1093887587333353690653 9007199254740992000 92999000143080293 662800000000000000000 Bool.false 120447 131072 1 262144 Bool.false 0 1 0 1 Bool.true ep736 135202966449969700649 2251799813685248000 1780263813677057843 6628000000000000000000 Bool.false 1093887587333353690653 1093887587333353690653 9007199254740992000

noncomputable abbrev qz180 := (@HMul.hMul Complex Complex Complex qz351 qz422 qz423)

noncomputable def ep738 := @Enclosure.Complex.IsNear.subLitP qz180 qz179 Bool.true 132205680572783140649 2251799813685248000 1754980000200495343 6628000000000000000000 Bool.false 1481192651687588976157

noncomputable def ep739 := nat_lit 4375550349333414762612000

noncomputable def ep740 := @ep738 9007199254740992000 92999000143080293 662800000000000000000 Bool.false 9000 4000 0 1 Bool.false 171998 4000 0 1 Bool.true 549088920614299794596000 137272230153574948649 2251799813685248000 1754980000200495343 6628000000000000000000 Bool.false ep739 1093887587333353690653 9007199254740992000 92999000143080293 662800000000000000000

noncomputable abbrev qz181 := qz422

noncomputable abbrev qz182 := qz423

noncomputable def ep741 := @Enclosure.Complex.IsNear.mul qz181 qz182 Bool.true 132205680572783140649 2251799813685248000 1754980000200495343 6628000000000000000000 Bool.false 1481192651687588976157 9007199254740992000 92999000143080293

noncomputable abbrev qz183 := (Complex.re qz422)

noncomputable abbrev qz184 := (Complex.re qz423)

noncomputable abbrev qz185 := (Complex.im qz422)

noncomputable abbrev qz186 := (Complex.im qz423)

noncomputable def ep742 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 qz183 qz184) (@HMul.hMul Real Real Real qz0 qz185 qz186) 118615307661800901 18014398509481984 7000000011599 1325600000000000000 73516297015254126637 1125899906842624000

noncomputable def ep743 := nat_lit 1190802907527697948816437600801783808

noncomputable def ep744 := @Enclosure.Real.IsNear.mulLit_ff qz183 qz184 7000 4000 0 1 16945043951685843 4503599627370496 1000000001657 331400000000000000

noncomputable def ep745 := @Enclosure.Complex.IsNear.re_isNear qz181 Bool.false 7000 4000 0 1 Bool.false 171998 4000 0 1

noncomputable abbrev qz424 := (Enclosure.sfrac Bool.false 171998 4000)

noncomputable abbrev qz187 := qz424

noncomputable def ep746 := @Enclosure.Complex.IsNear.of_eq qz181 (Complex.mk (Enclosure.sfrac Bool.false 7000 4000) qz187) Bool.false 7000 4000 0 1 Bool.false 171998 4000 0

noncomputable abbrev qz425 := (Complex.log (Complex.mk qz93 qz187))

noncomputable def ep747 := @Enclosure.Complex.IsNear.of_eq qz182 qz425 Bool.false 16945043951685843 4503599627370496 1000000001657 331400000000000000 Bool.false 854850603091363 562949953421312 20000000001657 3314000000000000000

noncomputable def ep748 := nat_lit 445616888943529036657176791305688570501508129321349191266965067921496266923593660813148775128470502097965547520

noncomputable def ep749 := nat_lit 13010336100413247216204808284129475365091826987721132490745956272956550341988565801347265584889110073577570304

noncomputable def ep750 := nat_lit 161255520711329383584810236646246970805982625278426077204576503715434627118235876336058915185859960504320

noncomputable def ep751 := BSN.log_dyadic_bound 13280312004 46048312004 6 5 ep748 524288 165700 ep749 ep750 311238 59328624008 32768000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 13280312004) (BSN.artanhQ 46048312004) 0 5 ep749 ep748 ep750 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz426 := (Real.log (Enclosure.sfrac Bool.false 29664312004 16000000))

noncomputable def ep752 := @Enclosure.Real.IsNear.mulLit_ff qz94 qz426 1 2 0 1 16945043951685843 2251799813685248 1000000001657 165700000000000000 16945043951685843 4503599627370496 1000000001657 331400000000000000 qz370 (BSN.isNear_log_sfrac 29664312004 16000000 16945043951685843 2251799813685248 1000000001657 165700000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 29664312004) qz371)) Bool.false 142145331253463476076544 18889465931478580854784 1000000001657000 165700000000000000000 16945043951685843 2251799813685248 1000000001657 165700000000000000 (BSN.log_rat_reduce_isNear 29664312004 16000000 10 59328624008 32768000000 311238 524288 24973259072661432 36028797018963968 165700 1000000000000000 rfl rfl rfl rfl (ep751 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep753 := BSN.arctan_dyadic_bound_f 9000 171998 1 0 524288 165700 0 1 1 0 1 1 27408 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 9000) (BSN.arctanEvenQ 171998) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 9000) (BSN.arctanOddQ 171998) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz427 := (Real.arctan (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 9000) (@Nat.cast Real Real.instNatCast 171998)))

noncomputable def ep754 := @Enclosure.Real.IsNear.subLit_ff_p qz95 qz427 884279719003555 562949953421312 1 2000000000000000 27408 524288 1 165700 448187912993564524544 854850603091363 562949953421312 20000000001657 3314000000000000000 qz96 (ep753 rfl) rfl rfl

noncomputable abbrev qz428 := (Complex.mk qz93 qz187)

noncomputable abbrev qz429 := (Real.arctan (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 171998) (@Nat.cast Real Real.instNatCast 9000)))

noncomputable def ep755 := @Enclosure.Complex.IsNear.re_isNear qz182 Bool.false 16945043951685843 4503599627370496 1000000001657 331400000000000000 Bool.false 854850603091363 562949953421312 20000000001657 3314000000000000000 (ep747 (@congrArg Complex Complex qz179 qz428 Complex.log (BSN.w_shift_mk qz149 Bool.false 85999 1000 2 qz150 rfl)) (@Enclosure.Complex.IsNear.of_parts qz425 Bool.false 16945043951685843 4503599627370496 1000000001657 331400000000000000 Bool.false 854850603091363 562949953421312 20000000001657 3314000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz425) (@HMul.hMul Real Real Real qz0 qz94 qz426) Bool.false 16945043951685843 4503599627370496 1000000001657 331400000000000000 (Enclosure.clog_re_eq 9000 171998 4000 29664312004 16000000 rfl rfl rfl) (ep752 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz425) qz429 Bool.false 854850603091363 562949953421312 20000000001657 3314000000000000000 (Enclosure.clog_im_eq 9000 171998 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz429 (@HSub.hSub Real Real Real qz355 qz95 qz427) Bool.false 854850603091363 562949953421312 20000000001657 3314000000000000000 (BSN.arctan_recip 171998 9000 rfl rfl) ep754))))

noncomputable def ep756 := @Enclosure.Real.IsNear.mulLit_ff qz185 qz186 171998 4000 0 1 854850603091363 562949953421312 20000000001657 3314000000000000000

noncomputable def ep757 := @Enclosure.Complex.IsNear.im_isNear qz181 Bool.false 7000 4000 0 1 Bool.false 171998 4000 0 1

noncomputable def ep758 := @Enclosure.Complex.IsNear.im_isNear qz182 Bool.false 16945043951685843 4503599627370496 1000000001657 331400000000000000 Bool.false 854850603091363 562949953421312 20000000001657 3314000000000000000 (ep747 (@congrArg Complex Complex qz179 qz428 Complex.log (BSN.w_shift_mk qz149 Bool.false 85999 1000 2 qz150 rfl)) (@Enclosure.Complex.IsNear.of_parts qz425 Bool.false 16945043951685843 4503599627370496 1000000001657 331400000000000000 Bool.false 854850603091363 562949953421312 20000000001657 3314000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz425) (@HMul.hMul Real Real Real qz0 qz94 qz426) Bool.false 16945043951685843 4503599627370496 1000000001657 331400000000000000 (Enclosure.clog_re_eq 9000 171998 4000 29664312004 16000000 rfl rfl rfl) (ep752 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz425) qz429 Bool.false 854850603091363 562949953421312 20000000001657 3314000000000000000 (Enclosure.clog_im_eq 9000 171998 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz429 (@HSub.hSub Real Real Real qz355 qz95 qz427) Bool.false 854850603091363 562949953421312 20000000001657 3314000000000000000 (BSN.arctan_recip 171998 9000 rfl rfl) ep754))))

noncomputable abbrev qz430 := (Enclosure.Real.IsNear.const Bool.false 171998 4000)

noncomputable abbrev qz188 := (@ep746 1 (BSN.w_sub_half_mk qz402 Bool.false 85999 1000 2 qz403 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7000 4000) qz424 Bool.false 7000 4000 0 1 Bool.false 171998 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 7000 4000) qz430))

noncomputable def ep759 := @ep742 1719980000142500343 6628000000000000000000 ep743 132205680572783140649 2251799813685248000 1754980000200495343 6628000000000000000000 (@ep744 118615307661800901 18014398509481984 7000000011599 1325600000000000000 (ep745 qz188) ep755 rfl) (@ep756 73516297015254126637 1125899906842624000 1719980000142500343 6628000000000000000000 (ep757 qz188) ep758 rfl) rfl

noncomputable def ep760 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz183 qz186) (@HMul.hMul Real Real Real qz0 qz185 qz184) 5983954221639541 2251799813685248 140000000011599 13256000000000000000 1457256834801030812157 9007199254740992000

noncomputable def ep761 := nat_lit 3335349337102071293114811029374631936

noncomputable def ep762 := @Enclosure.Real.IsNear.mulLit_ff qz183 qz186 7000 4000 0 1 854850603091363 562949953421312 20000000001657 3314000000000000000

noncomputable def ep763 := @Enclosure.Real.IsNear.mulLit_ff qz185 qz184 171998 4000 0 1 16945043951685843 4503599627370496 1000000001657 331400000000000000

noncomputable def ep764 := @ep760 85999000142500343 662800000000000000000 ep761 1481192651687588976157 9007199254740992000 92999000143080293 662800000000000000000 (@ep762 5983954221639541 2251799813685248 140000000011599 13256000000000000000 (ep745 qz188) ep758 rfl) (@ep763 1457256834801030812157 9007199254740992000 85999000142500343 662800000000000000000 (ep757 qz188) ep755 rfl) rfl

noncomputable def ep765 := @Enclosure.Complex.IsNear.of_eq qz179 qz428 Bool.false 9000 4000 0 1 Bool.false 171998 4000 0 1 (BSN.w_shift_mk qz149 Bool.false 85999 1000 2 qz150 rfl)

noncomputable abbrev qz431 := (ep765 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 9000 4000) (Enclosure.sfrac Bool.false 171998 4000) Bool.false 9000 4000 0 1 Bool.false 171998 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 9000 4000) (Enclosure.Real.IsNear.const Bool.false 171998 4000)))

noncomputable abbrev qz189 := qz431

noncomputable def ep766 := ep740 (@ep741 662800000000000000000 (ep759 rfl) (ep764 rfl)) qz189 rfl rfl rfl rfl rfl rfl

noncomputable def ep767 := @ep737 92999000143080293 662800000000000000000 (ep766 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@Enclosure.Complex.IsNear.mul qz99 (↑qz2) Bool.false 120447 131072 1 262144 Bool.false 0 1 0 1 (@ep348 131072 1 262144 (ep350 rfl) (ep352 rfl) rfl rfl) (@ep353 1 0 1 (ep355 rfl) (ep357 rfl) rfl rfl))

noncomputable abbrev qz432 := (@HPow.hPow Complex Int Complex qz504 qz509 (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) (@OfNat.ofNat Int 1 (@instOfNat 1)) (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (@OfNat.ofNat Int 2 (@instOfNat 2)) (@Nat.cast Int instNatCastInt 1))))

noncomputable abbrev qz190 := qz432

noncomputable def ep768 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz72 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz81 qz179 (@HSub.hSub Int Int Int qz364 qz83 (@HMul.hMul Int Int Int qz365 qz84 (@Nat.cast Int instNatCastInt k))))) (@HAdd.hAdd Complex Complex Complex qz4 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz72 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz81 qz179 (@HSub.hSub Int Int Int qz364 qz83 (@HMul.hMul Int Int Int qz365 qz84 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 (@Rat.cast Complex Complex.instRatCast (bernoulli qz101)) qz102) qz190)) Bool.false 1737429 17179869184 3 17179869184

noncomputable def ep769 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz72 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz81 qz179 (@HSub.hSub Int Int Int qz364 qz83 (@HMul.hMul Int Int Int qz365 qz84 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 (@Rat.cast Complex Complex.instRatCast (bernoulli qz101)) qz102) qz190) Bool.false 0 1 0 1 Bool.false

noncomputable def ep770 := @ep769 0 1 0 1 Bool.false 1737429 17179869184 3 17179869184 Bool.true 49805718857 25769803776000 85999 25769803776000 Bool.false 1737429 1737429 17179869184 3 17179869184 Bool.true 49805718857 49805718857 25769803776000 85999

noncomputable def ep771 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz72 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz81 qz179 (@HSub.hSub Int Int Int qz364 qz83 (@HMul.hMul Int Int Int qz365 qz84 (@Nat.cast Int instNatCastInt k))))) (Complex.mk qz13 qz13) Bool.false 0 1 0 1 Bool.false

noncomputable def ep772 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz79 (@Rat.cast Complex Complex.instRatCast (bernoulli qz101)) qz102) qz190 Bool.false 1737429 17179869184 3 17179869184 Bool.true 49805718857 25769803776000 85999 25769803776000

noncomputable abbrev qz191 := (Complex.re qz432)

noncomputable abbrev qz192 := (Complex.im qz432)

noncomputable def ep773 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz79 (@Rat.cast Complex Complex.instRatCast (bernoulli qz101)) qz102)) qz191) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz79 (@Rat.cast Complex Complex.instRatCast (bernoulli qz101)) qz102)) qz192) 1737429 17179869184 3 17179869184 0 1 0

noncomputable def ep774 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz79 (@Rat.cast Complex Complex.instRatCast (bernoulli qz101)) qz102)) qz191 1 12 0 1 5212287 4294967296 9 4294967296 1737429

noncomputable def ep775 := @Enclosure.Complex.IsNear.re_isNear qz190 Bool.false 5212287 4294967296 9 4294967296 Bool.true 49805718857 2147483648000 85999 2147483648000

noncomputable abbrev qz433 := (@HPow.hPow Complex Nat Complex qz505 qz509 1)

noncomputable abbrev qz193 := (@Inv.inv Complex Complex.instInv qz433)

noncomputable def ep776 := @Enclosure.Complex.IsNear.of_eq qz190 qz193 Bool.false 5212287 4294967296 9 4294967296 Bool.true 49805718857 2147483648000 85999

noncomputable def ep777 := @Enclosure.Complex.IsNear.of_parts qz193 Bool.false 5212287 4294967296 9 4294967296 Bool.true 49805718857 2147483648000 85999

noncomputable abbrev qz194 := (Complex.re qz433)

noncomputable abbrev qz195 := qz433

noncomputable def ep778 := @Enclosure.Real.IsNear.mulLit_ff qz194 (@Inv.inv Real Real.instInv (@DFunLike.coe qz108 Complex (fun (x : Complex) => Real) qz109 Complex.normSq qz195)) 9000 4000 0 1 579143 1073741824 1 1073741824

noncomputable def ep779 := @Enclosure.Complex.IsNear.re_isNear qz195 Bool.false 9000 4000 0 1 Bool.false 171998 4000 0 1

noncomputable def ep780 := @Enclosure.Complex.IsNear.of_eq qz195 qz179 Bool.false 9000 4000 0 1 Bool.false 171998 4000 0

noncomputable def ep781 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (@DFunLike.coe qz108 Complex (fun (x : Complex) => Real) qz109 Complex.normSq qz195)) Bool.false 579143 1073741824 1 1073741824 579143 1073741824 1

noncomputable abbrev qz196 := (Complex.im qz433)

noncomputable def ep782 := @Enclosure.Real.IsNear.of_eq (@DFunLike.coe qz108 Complex (fun (x : Complex) => Real) qz109 Complex.normSq qz195) (@HAdd.hAdd Real Real Real qz380 (@HMul.hMul Real Real Real qz0 qz194 qz194) (@HMul.hMul Real Real Real qz0 qz196 qz196)) Bool.false 7416078001 4000000 0 1

noncomputable def ep783 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz194 qz194) (@HMul.hMul Real Real Real qz0 qz196 qz196) 81 16 0 1 7395828001 4000000

noncomputable def ep784 := @Enclosure.Real.IsNear.mulLit_ff qz194 qz194 9000 4000 0 1 9000 4000 0 1

noncomputable def ep785 := @Enclosure.Real.IsNear.mulLit_ff qz196 qz196 171998 4000 0 1 171998 4000 0 1

noncomputable def ep786 := @Enclosure.Complex.IsNear.im_isNear qz195 Bool.false 9000 4000 0 1 Bool.false 171998 4000 0 1

noncomputable abbrev qz197 := (ep779 (@ep780 1 (BSN.pow_one_c qz419) qz431))

noncomputable abbrev qz198 := (ep786 (@ep780 1 (BSN.pow_one_c qz419) qz431))

noncomputable def ep787 := @ep783 0 1 118657248016 7416078001 4000000 0 1 (@ep784 81 16 0 1 qz197 qz197 rfl) (@ep785 7395828001 4000000 0 1 qz198 qz198 rfl)

noncomputable def ep788 := @Enclosure.Real.IsNear.inv_image (@DFunLike.coe qz108 Complex (fun (x : Complex) => Real) qz109 Complex.normSq qz195) 7416078001 4000000 0 1 289571 289572 536870912 (ep782 (Enclosure.Complex.normSq_eq_mul_add_mul qz195) (ep787 rfl rfl)) rfl

noncomputable def ep789 := @Enclosure.Real.IsNear.of_eq (Complex.re qz193) (@HMul.hMul Real Real Real qz0 qz194 (@Inv.inv Real Real.instInv (@DFunLike.coe qz108 Complex (fun (x : Complex) => Real) qz109 Complex.normSq qz195))) Bool.false 5212287 4294967296 9 4294967296 (Enclosure.Complex.inv_re_eq_mul qz195) (@ep778 5212287 4294967296 9 4294967296 qz197 (@ep781 1073741824 (ep788 rfl rfl rfl rfl rfl) rfl) rfl)

noncomputable def ep790 := @Enclosure.Real.IsNear.of_eq (Complex.im qz193) (@HMul.hMul Real Real Real qz0 (@Neg.neg Real Real.instNeg qz196) (@Inv.inv Real Real.instInv (@DFunLike.coe qz108 Complex (fun (x : Complex) => Real) qz109 Complex.normSq qz195))) Bool.true 49805718857 2147483648000 85999 2147483648000 (Enclosure.Complex.inv_im_eq_mul qz195)

noncomputable def ep791 := @Enclosure.Real.IsNear.mulLit_tf (@Neg.neg Real Real.instNeg qz196) (@Inv.inv Real Real.instInv (@DFunLike.coe qz108 Complex (fun (x : Complex) => Real) qz109 Complex.normSq qz195)) 171998 4000 0 1 579143 1073741824 1

noncomputable def ep792 := @ep791 1073741824 49805718857 2147483648000 85999 2147483648000 (@Enclosure.Real.IsNear.neg qz196 Bool.false 171998 4000 0 1 qz198) (@ep781 1073741824 (ep788 rfl rfl rfl rfl rfl) rfl) rfl

noncomputable def ep793 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz79 (@Rat.cast Complex Complex.instRatCast (bernoulli qz101)) qz102)) qz192 0 1 0 1 49805718857 2147483648000 85999 2147483648000 0

noncomputable def ep794 := @Enclosure.Complex.IsNear.im_isNear qz190 Bool.false 5212287 4294967296 9 4294967296 Bool.true 49805718857 2147483648000 85999 2147483648000

noncomputable abbrev qz199 := (@ep776 2147483648000 (BSN.zpow_one_sub_two_mul qz419 1 1 rfl rfl) (@ep777 2147483648000 ep789 (ep790 ep792)))

noncomputable def ep795 := @ep773 1 1737429 1737429 17179869184 3 17179869184 (@ep774 17179869184 3 17179869184 ep367 (ep775 qz199) rfl) (@ep793 1 0 1 ep387 (ep794 qz199) rfl) rfl

noncomputable def ep796 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz79 (@Rat.cast Complex Complex.instRatCast (bernoulli qz101)) qz102)) qz192) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz79 (@Rat.cast Complex Complex.instRatCast (bernoulli qz101)) qz102)) qz191) 49805718857 25769803776000 85999 25769803776000 0 1 0

noncomputable def ep797 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HDiv.hDiv Complex Complex Complex qz79 (@Rat.cast Complex Complex.instRatCast (bernoulli qz101)) qz102)) qz192 1 12 0 1 49805718857 2147483648000 85999 2147483648000 49805718857

noncomputable def ep798 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz79 (@Rat.cast Complex Complex.instRatCast (bernoulli qz101)) qz102)) qz191 0 1 0 1 5212287 4294967296 9 4294967296 0

noncomputable def ep799 := @ep796 1 49805718857 49805718857 25769803776000 85999 25769803776000 (@ep797 25769803776000 85999 25769803776000 ep367 (ep794 qz199) rfl) (@ep798 1 0 1 ep387 (ep775 qz199) rfl) rfl

noncomputable def ep800 := @ep770 25769803776000 (@ep771 0 1 0 1 (BSN.stirling_sum_base qz179) qz115) (ep772 (ep795 rfl) (ep799 rfl)) rfl rfl rfl rfl rfl

noncomputable def ep801 := @ep734 3281610536918604874327 27021597764222976000 36569564593331528851663 ep721 (ep767 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep768 Bool.true 49805718857 25769803776000 85999 25769803776000 (BSN.stirling_sum_succ qz179 0 1 rfl) (ep800 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl

noncomputable def ep802 := @Enclosure.Complex.IsNear.of_eq (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz176 (@Nat.cast Complex Complex.instNatCast j))) (BSN.logSumC qz149 2) Bool.false 16939874958545107 2251799813685248 1000000001657 165700000000000000 Bool.false 874463571248547 281474976710656

noncomputable abbrev qz200 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz272 qz420 qz376))

noncomputable def ep803 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz149 2) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.logSumC qz149 1) qz200) Bool.false 16939874958545107 2251799813685248 1000000001657 165700000000000000 Bool.false 874463571248547 281474976710656 20000000001657 1657000000000000000

noncomputable def ep804 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz149 1) qz200 Bool.false 16938962277994707 4503599627370496 1000000001657 331400000000000000 Bool.false 881006953924003 562949953421312 20000000001657 3314000000000000000 Bool.false

noncomputable def ep805 := nat_lit 152580829102013080521032433926144

noncomputable def ep806 := nat_lit 984558453406007362196317667328

noncomputable abbrev qz201 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz272 qz420 (@Nat.cast Complex Complex.instNatCast 0)))

noncomputable def ep807 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz149 1) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.logSumC qz149 0) qz201) Bool.false 16938962277994707 4503599627370496 1000000001657 331400000000000000 Bool.false 881006953924003 562949953421312 20000000001657 3314000000000000000

noncomputable def ep808 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz149 0) qz201 Bool.false 0 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable abbrev qz434 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz187))

noncomputable def ep809 := @Enclosure.Complex.IsNear.of_eq qz201 qz434 Bool.false 16938962277994707 4503599627370496 1000000001657 331400000000000000 Bool.false 881006953924003 562949953421312 20000000001657 3314000000000000000

noncomputable def ep810 := nat_lit 437935405166394800019957250910035964188596667621415704592893314689875907902852173933481095774490704593965547520

noncomputable def ep811 := nat_lit 12670670537683241802231207996609486562442984826354745069971463268408909830276434410158395425828098412777570304

noncomputable def ep812 := nat_lit 151800699253155918747652231221233791912582282768251464217912183211248259831789728332048454476995960504320

noncomputable def ep813 := BSN.log_dyadic_bound 13200312004 45968312004 6 5 ep810 524288 165700 ep811 ep812 309822 59168624008 32768000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 13200312004) (BSN.artanhQ 45968312004) 0 5 ep811 ep810 ep812 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep814 := @Enclosure.Real.IsNear.mulLit_ff qz94 (Real.log (Enclosure.sfrac Bool.false 29584312004 16000000)) 1 2 0 1 16938962277994707 2251799813685248 1000000001657 165700000000000000 16938962277994707 4503599627370496 1000000001657 331400000000000000 qz370 (BSN.isNear_log_sfrac 29584312004 16000000 16938962277994707 2251799813685248 1000000001657 165700000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 29584312004) qz371)) Bool.false 142094314476884623097856 18889465931478580854784 1000000001657000 165700000000000000000 16938962277994707 2251799813685248 1000000001657 165700000000000000 (BSN.log_rat_reduce_isNear 29584312004 16000000 10 59168624008 32768000000 309822 524288 24973259072661432 36028797018963968 165700 1000000000000000 rfl rfl rfl rfl (ep813 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep815 := BSN.arctan_dyadic_bound_f 1000 171998 1 0 524288 165700 0 1 1 0 1 1 3048 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 171998) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 171998) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz435 := (@Nat.cast Real Real.instNatCast 171998)

noncomputable def ep816 := @Enclosure.Real.IsNear.subLit_ff_p qz95 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz382 qz435)) 884279719003555 562949953421312 1 2000000000000000 3048 524288 1 165700 461901373858907684864 881006953924003 562949953421312 20000000001657 3314000000000000000 qz96 (ep815 rfl) rfl rfl

noncomputable abbrev qz202 := (@HAdd.hAdd Complex Complex Complex qz272 qz420 (@Nat.cast Complex Complex.instNatCast 0))

noncomputable abbrev qz436 := (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz187)

noncomputable def ep817 := @ep808 16938962277994707 4503599627370496 1000000001657 331400000000000000 Bool.false 881006953924003 562949953421312 20000000001657 3314000000000000000 Bool.false 16938962277994707 16938962277994707 4503599627370496 1000000001657 331400000000000000 Bool.false 881006953924003 881006953924003 562949953421312 20000000001657 3314000000000000000 (@Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz149 0) (Complex.mk qz13 qz13) Bool.false 0 1 0 1 Bool.false 0 1 0 1 (BSN.log_sum_c_base qz149) qz115) (ep809 (@congrArg Complex Complex qz202 qz436 Complex.log (BSN.w_shift_mk qz149 Bool.false 85999 1000 0 qz150 rfl)) (@Enclosure.Complex.IsNear.of_parts qz434 Bool.false 16938962277994707 4503599627370496 1000000001657 331400000000000000 Bool.false 881006953924003 562949953421312 20000000001657 3314000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz434) (@HMul.hMul Real Real Real qz0 qz94 (Real.log (Enclosure.sfrac Bool.false 29584312004 16000000))) Bool.false 16938962277994707 4503599627370496 1000000001657 331400000000000000 (Enclosure.clog_re_eq 1000 171998 4000 29584312004 16000000 rfl rfl rfl) (ep814 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz434) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz435 qz382)) Bool.false 881006953924003 562949953421312 20000000001657 3314000000000000000 (Enclosure.clog_im_eq 1000 171998 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz435 qz382)) (@HSub.hSub Real Real Real qz355 qz95 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz382 qz435))) Bool.false 881006953924003 562949953421312 20000000001657 3314000000000000000 (BSN.arctan_recip 171998 1000 rfl rfl) ep816)))) rfl rfl

noncomputable abbrev qz437 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz187))

noncomputable def ep818 := @Enclosure.Complex.IsNear.of_eq qz200 qz437 Bool.false 16940787639095507 4503599627370496 1000000001657 331400000000000000 Bool.false 867920188573091 562949953421312 20000000001657 3314000000000000000

noncomputable def ep819 := nat_lit 440227239996759517878856072247136054195559733416360599330990016305758465426527783335300169004659043845165547520

noncomputable def ep820 := nat_lit 12771757931540831080620976717445651124220733508713670621844958774951975159012672474351668648517281911017570304

noncomputable def ep821 := nat_lit 154583337415052852780881187735588335469271960184861394269603940538809570871794740705162863089655160504320

noncomputable def ep822 := BSN.log_dyadic_bound 13224312004 45992312004 6 5 ep819 524288 165700 ep820 ep821 310247 59216624008 32768000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 13224312004) (BSN.artanhQ 45992312004) 0 5 ep820 ep819 ep821 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep823 := @Enclosure.Real.IsNear.mulLit_ff qz94 (Real.log (Enclosure.sfrac Bool.false 29608312004 16000000)) 1 2 0 1 16940787639095507 2251799813685248 1000000001657 165700000000000000 16940787639095507 4503599627370496 1000000001657 331400000000000000 qz370 (BSN.isNear_log_sfrac 29608312004 16000000 16940787639095507 2251799813685248 1000000001657 165700000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 29608312004) qz371)) Bool.false 142109626715617682784256 18889465931478580854784 1000000001657000 165700000000000000000 16940787639095507 2251799813685248 1000000001657 165700000000000000 (BSN.log_rat_reduce_isNear 29608312004 16000000 10 59216624008 32768000000 310247 524288 24973259072661432 36028797018963968 165700 1000000000000000 rfl rfl rfl rfl (ep822 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep824 := BSN.arctan_dyadic_bound_f 5000 171998 1 0 524288 165700 0 1 1 0 1 1 15236 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 5000) (BSN.arctanEvenQ 171998) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 5000) (BSN.arctanOddQ 171998) 0 0 rfl) rfl rfl rfl

noncomputable def ep825 := @Enclosure.Real.IsNear.subLit_ff_p qz95 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz386 qz435)) 884279719003555 562949953421312 1 2000000000000000 15236 524288 1 165700 455040139826608734208 867920188573091 562949953421312 20000000001657 3314000000000000000 qz96 (ep824 rfl) rfl rfl

noncomputable abbrev qz203 := (@HAdd.hAdd Complex Complex Complex qz272 qz420 qz376)

noncomputable abbrev qz438 := (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz187)

noncomputable def ep826 := @ep804 16940787639095507 4503599627370496 1000000001657 331400000000000000 Bool.false 867920188573091 562949953421312 20000000001657 3314000000000000000 Bool.false ep805 16939874958545107 2251799813685248 1000000001657 165700000000000000 Bool.false ep806 874463571248547 281474976710656 20000000001657 1657000000000000000 (ep807 (BSN.log_sum_c_succ qz149 0 1 rfl) (ep817 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep818 (@congrArg Complex Complex qz203 qz438 Complex.log (BSN.w_shift_mk qz149 Bool.false 85999 1000 1 qz150 rfl)) (@Enclosure.Complex.IsNear.of_parts qz437 Bool.false 16940787639095507 4503599627370496 1000000001657 331400000000000000 Bool.false 867920188573091 562949953421312 20000000001657 3314000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz437) (@HMul.hMul Real Real Real qz0 qz94 (Real.log (Enclosure.sfrac Bool.false 29608312004 16000000))) Bool.false 16940787639095507 4503599627370496 1000000001657 331400000000000000 (Enclosure.clog_re_eq 5000 171998 4000 29608312004 16000000 rfl rfl rfl) (ep823 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz437) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz435 qz386)) Bool.false 867920188573091 562949953421312 20000000001657 3314000000000000000 (Enclosure.clog_im_eq 5000 171998 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz435 qz386)) (@HSub.hSub Real Real Real qz355 qz95 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz386 qz435))) Bool.false 867920188573091 562949953421312 20000000001657 3314000000000000000 (BSN.arctan_recip 171998 5000 rfl rfl) ep825)))) rfl rfl

noncomputable def ep827 := @ep727 ep721 Bool.false 16939874958545107 2251799813685248 1000000001657 165700000000000000 Bool.false 874463571248547 281474976710656 20000000001657 1657000000000000000 Bool.true ep728 152142613680220919649 2251799813685248000 29823221287230954641587 ep725 Bool.false ep729 3197662034078744362327 27021597764222976000 39715292593592152416463 ep721 (@ep730 2251799813685248000 29167861286145023121587 ep725 Bool.false 3281610536918604874327 27021597764222976000 36569564593331528851663 ep721 (BSN.logGammaStirling_unfold 1 qz179) (ep801 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (@ep802 20000000001657 1657000000000000000 (BSN.log_sum_c_eq qz149 2) (ep803 (BSN.log_sum_c_succ qz149 1 2 rfl) (ep826 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)))

noncomputable abbrev qz204 := (@HDiv.hDiv Real Real Real qz269 qz402 (2 : Real))

noncomputable def ep828 := @Enclosure.Real.IsNear.mulLit_ff qz204 (Real.log Real.pi) 85999 2000 0 1 75021 65536 1 131072 6451730979 131072000 85999 262144000 (@Enclosure.Real.IsNear.of_eq qz204 (Enclosure.sfrac Bool.false 85999 2000) Bool.false 85999 2000 0 1 (BSN.t_half_eq qz149 Bool.false 85999 1000 qz150) (Enclosure.Real.IsNear.const Bool.false 85999 2000)) EMRow23.d5 rfl

noncomputable def ep829 := @ep723 85999 262144000 ep724 373516660664756269739 5404319552844595200 125215498393592152416463 ep721 (@ep726 39715292593592152416463 ep721 (ep827 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) ep828 rfl rfl

noncomputable def ep830 := nat_lit 32546104012325647597857302204971608834503224602072622116671158223340518867200

noncomputable def ep831 := nat_lit 65296679634319364338697652138165925048890389865255766765259971543882629376

noncomputable def ep832 := nat_lit 85134077789063988547363614338130516402191194278979786683185469678630310871296

noncomputable def ep833 := BSN.sin_dyadic_bound_f 1686014818 1073741824 3 2 524288 165862 ep830 ep64 ep831 ep832 ep66 ep831 524287 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1686014818) qz286 0 2 ep830 ep64 ep831 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1686014818) qz287 0 2 ep832 ep66 ep831 rfl rfl rfl rfl) rfl rfl

noncomputable def ep834 := @ep720 524288 Bool.false 524287 524288 1 82850 (@ep722 36235885 524288 253 524288 ep829 rfl) (Enclosure.sfrac_false_div 36235885 524288) (BSN.cos_reduce3 qz421 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 118642745421254885376000) qz22) 226375608064910080 72057594037927936 Bool.false 524287 524288 10 1000000000000000 165700 82850 (BSN.sin_reduce_arg_pos_rat_q3 36235885 524288 226375608064910080 72057594037927936 10 118642745421254885376000 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 524287 524288 118642745421254885376000 75557863725914323419136 1686014818 1073741824 165862 165700 (ep833 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep835 := nat_lit 8782639663000796088238080

noncomputable def ep836 := nat_lit 58170704231454895899163171453

noncomputable def ep837 := nat_lit 9095521200995199448881561600000

noncomputable abbrev qz205 := qz401

noncomputable abbrev qz439 := (@HPow.hPow Complex Complex Complex qz490 (@Nat.cast Complex Complex.instNatCast 18) qz507)

noncomputable abbrev qz206 := qz439

noncomputable abbrev qz440 := (@Nat.cast Complex Complex.instNatCast 18)

noncomputable abbrev qz207 := (@HAdd.hAdd Complex Complex Complex qz272 (@HDiv.hDiv Complex Complex Complex qz360 qz440 (@HSub.hSub Complex Complex Complex qz352 qz400 (1 : Complex))) qz359)

noncomputable abbrev qz208 := qz440

noncomputable def ep838 := @Enclosure.Complex.IsNear.of_eq (zetaApproximant qz140 1 18) (@HAdd.hAdd Complex Complex Complex qz4 (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 18, @HPow.hPow Complex Complex Complex qz121 (@Nat.cast Complex Complex.instNatCast n) qz205) (@HMul.hMul Complex Complex Complex qz72 qz206 (@HAdd.hAdd Complex Complex Complex qz4 qz207 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz80 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz126 qz208 (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz80 2 k) 1))))))) Bool.false ep715 ep716 ep717

noncomputable def ep839 := @Enclosure.Complex.IsNear.addLitP (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 18, @HPow.hPow Complex Complex Complex qz121 (@Nat.cast Complex Complex.instNatCast n) qz205) (@HMul.hMul Complex Complex Complex qz72 qz206 (@HAdd.hAdd Complex Complex Complex qz4 qz207 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz80 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz126 qz208 (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))))) Bool.false 582815024439 274877906944 14212053201387 2277363459031040

noncomputable def ep840 := nat_lit 2216475700687653142516109

noncomputable def ep841 := nat_lit 3129401601379705063464750331

noncomputable def ep842 := nat_lit 1561702176883111114736191453

noncomputable def ep843 := nat_lit 9628048498264221475167572211577913344

noncomputable def ep844 := nat_lit 155770990069119987657765681782325248

noncomputable def ep845 := @ep839 Bool.false 16944624031 274877906944 14173929111087 2277363459031040 Bool.true ep840 ep716 ep841 ep718 Bool.false 25292912977685615947397 ep835 ep842 ep837 Bool.false ep843 ep715 ep716 ep717 ep718 Bool.false ep844 566691560631152197521317 ep835

noncomputable def ep846 := @Enclosure.Complex.IsNear.of_eq (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 18, @HPow.hPow Complex Complex Complex qz121 (@Nat.cast Complex Complex.instNatCast n) qz205) (BSN.headSumC qz140 18) Bool.false 582815024439 274877906944 14212053201387 2277363459031040 Bool.false 16944624031 274877906944 14173929111087

noncomputable abbrev qz209 := (@HPow.hPow Complex Complex Complex qz273 qz389 qz401)

noncomputable def ep847 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz140 18) (@HAdd.hAdd Complex Complex Complex qz4 qz158 qz209) Bool.false 582815024439 274877906944 14212053201387 2277363459031040 Bool.false 16944624031 274877906944 14173929111087 2277363459031040

noncomputable def ep848 := @Enclosure.Complex.IsNear.addLitP qz158 qz209 Bool.false 35680143545 17179869184 6815220077747 1138681729515520 Bool.true 12161664627 68719476736 6794409980447 1138681729515520 Bool.false

noncomputable abbrev qz210 := (@HMul.hMul Real Real Real qz266 qz402 qz395)

noncomputable def ep849 := @Enclosure.Complex.IsNear.of_eq qz209 (Complex.mk (@HMul.hMul Real Real Real qz0 qz130 (Real.cos qz210)) (@HMul.hMul Real Real Real qz0 qz130 (@Neg.neg Real Real.instNeg (Real.sin qz210)))) Bool.false 11932727719 274877906944 581613045893 2277363459031040 Bool.false 65591282539 274877906944 585109150193 2277363459031040 (BSN.cpow_neg_s_mk qz149 85999 1000 17 qz150 rfl)

noncomputable def ep850 := @Enclosure.Real.IsNear.mulLit_ff qz149 qz133 85999 1000 0 1 3189913004350711 1125899906842624 5000000001657 414250000000000000 274329328461156795289 1125899906842624000 429995000142500343 414250000000000000000 qz151 (BSN.isNear_log_sfrac 17 1 3189913004350711 1125899906842624 5000000001657 414250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' qz396 Bool.false 26758929747600409100288 9444732965739290427392 1000000000331400 82850000000000000000 3189913004350711 1125899906842624 5000000001657 414250000000000000 (BSN.log_rat_reduce_isNear 17 1 4 34 32 15892 262144 24973259072661432 36028797018963968 82850 1000000000000000 rfl rfl rfl rfl (ep443 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep851 := nat_lit 1394078500112019137272648836944656

noncomputable def ep852 := BSN.sin_dyadic_bound_f 193228778 1073741824 2 1 524288 165862 ep851 ep80 ep851 ep851 ep81 ep851 93841 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 193228778) qz286 0 1 ep851 ep80 ep851 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 193228778) qz287 0 1 ep851 ep81 ep851 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz441 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 31936137) qz495)

noncomputable def ep853 := @Enclosure.Real.IsNear.cos_image qz210 qz441 Bool.false 31936137 131072 545 524288 Bool.false 93841 524288 1 82850 (@Enclosure.Real.IsNear.recentre' qz210 Bool.false 274329328461156795289 1125899906842624000 429995000142500343 414250000000000000000 31936137 131072 545 524288 (ep850 rfl) rfl) (Enclosure.sfrac_false_div 31936137 131072) (BSN.cos_reduce3 qz441 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 3399316627295949553664) qz293) 226375608064910080 72057594037927936 Bool.false 93841 524288 38 1000000000000000 165700 82850 (BSN.sin_reduce_arg_pos_rat_q3 31936137 131072 226375608064910080 72057594037927936 38 3399316627295949553664 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 93841 524288 3399316627295949553664 18889465931478580854784 193228778 1073741824 165862 165700 (ep852 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep854 := BSN.cos_dyadic_bound_f 193228778 1073741824 2 1 524288 165862 ep851 ep126 ep851 ep851 ep127 ep851 515821 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 193228778) qz282 0 1 ep851 ep126 ep851 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 193228778) qz283 0 1 ep851 ep127 ep851 rfl rfl rfl rfl) rfl rfl

noncomputable def ep855 := @Enclosure.Real.IsNear.sin_image qz210 qz441 Bool.false 31936137 131072 545 524288 Bool.true 515821 524288 1 82850 (@Enclosure.Real.IsNear.recentre' qz210 Bool.false 274329328461156795289 1125899906842624000 429995000142500343 414250000000000000000 31936137 131072 545 524288 (ep850 rfl) rfl) (Enclosure.sfrac_false_div 31936137 131072) (BSN.sin_reduce3 qz441 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 3399316627295949553664) qz293) 226375608064910080 72057594037927936 Bool.false 515821 524288 38 1000000000000000 165700 82850 (BSN.sin_reduce_arg_pos_rat_q3 31936137 131072 226375608064910080 72057594037927936 38 3399316627295949553664 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 515821 524288 3399316627295949553664 18889465931478580854784 193228778 1073741824 165862 165700 (ep854 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep856 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz130 (Real.cos qz210)) (@HMul.hMul Real Real Real qz0 qz130 (@Neg.neg Real Real.instNeg (Real.sin qz210))) Bool.false 11932727719 274877906944 581613045893 2277363459031040 Bool.false 65591282539 274877906944 585109150193 2277363459031040 (@Enclosure.Real.IsNear.mulLit_ff qz130 (Real.cos qz210) 127159 524288 1 524288 93841 524288 22838769 21718630400 11932727719 274877906944 581613045893 2277363459031040 qz398 (@Enclosure.Real.IsNear.recentre' (Real.cos qz210) Bool.false 93841 524288 45677538 43437260800 93841 524288 22838769 21718630400 (ep853 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz130 (@Neg.neg Real Real.instNeg (Real.sin qz210)) 127159 524288 1 524288 515821 524288 22838769 21718630400 65591282539 274877906944 585109150193 2277363459031040 qz398 (@Enclosure.Real.IsNear.neg (Real.sin qz210) Bool.true 515821 524288 22838769 21718630400 (@Enclosure.Real.IsNear.recentre' (Real.sin qz210) Bool.true 515821 524288 45677538 43437260800 515821 524288 22838769 21718630400 (ep855 rfl rfl) rfl)) rfl)

noncomputable def ep857 := @ep848 11932727719 274877906944 581613045893 2277363459031040 Bool.false 65591282539 274877906944 585109150193 2277363459031040 Bool.false 10012685878331782987776 582815024439 274877906944 14212053201387 2277363459031040 Bool.false 1164425696898571042816 16944624031 274877906944 14173929111087 2277363459031040 EMRow23.d12 (ep849 ep856) rfl rfl

noncomputable def ep858 := @Enclosure.Complex.IsNear.mul qz206 (@HAdd.hAdd Complex Complex Complex qz4 qz207 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz80 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz126 qz208 (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz80 2 k) 1))))) Bool.true ep840 ep716 ep841 ep718 Bool.false

noncomputable abbrev qz211 := (Complex.re qz439)

noncomputable abbrev qz212 := (Complex.im qz439)

noncomputable def ep859 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 qz211 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz207 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz80 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz126 qz208 (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz80 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz212 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz207 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz80 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz126 qz208 (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz80 2 k) 1))))))) 16034447018008690203325 146377327716679934803968 758493796110757641567983

noncomputable def ep860 := nat_lit 6063680800663466299254374400

noncomputable def ep861 := nat_lit 853920213047432138760801331

noncomputable def ep862 := nat_lit 324441790015614389568064634784431713739197120512

noncomputable def ep863 := @Enclosure.Real.IsNear.mulLit_tf qz211 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz207 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz80 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz126 qz208 (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))))) 30044666175 137438953472 1421233477797 5693408647577600 1601060926217

noncomputable abbrev qz442 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) qz508 (Real.log (Enclosure.sfrac Bool.false 18 1)))

noncomputable abbrev qz213 := (Real.cos qz442)

noncomputable abbrev qz214 := (Real.sin qz442)

noncomputable abbrev qz443 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 18)))

noncomputable abbrev qz444 := (@Neg.neg Real Real.instNeg qz214)

noncomputable def ep864 := @Enclosure.Complex.IsNear.of_eq qz206 (Complex.mk (@HMul.hMul Real Real Real qz0 qz443 qz213) (@HMul.hMul Real Real Real qz0 qz443 qz444)) Bool.true 30044666175 137438953472 1421233477797 5693408647577600 Bool.false 24225272275 274877906944 2830444550669 11386817295155200 (BSN.cpow_neg_s_mk qz149 85999 1000 18 qz150 rfl)

noncomputable abbrev qz445 := (Real.sqrt (@Nat.cast Real Real.instNatCast 18))

noncomputable abbrev qz446 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 18) qz18)

noncomputable def ep865 := @Enclosure.Real.IsNear.inv_image qz445 2224365 524288 1 524288 61787 61788 262144 (@Enclosure.Real.IsNear.of_eq qz445 (Real.sqrt qz446) Bool.false 2224365 524288 1 524288 (BSN.sqrt_natCast_div_one 18) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz446) Bool.false 2224365 524288 1 524288 2224365 524288 1 524288 (BSN.sqrt_enclosure 18 1 1112182 1112183 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep866 := BSN.log_dyadic_bound 2 34 2 1 3468 262144 82850 4 4 30876 36 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 2) (BSN.artanhQ 34) 0 1 4 3468 4 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz447 := (Real.log (Enclosure.sfrac Bool.false 18 1))

noncomputable abbrev qz215 := qz447

noncomputable def ep867 := @Enclosure.Real.IsNear.mulLit_ff qz149 qz215 85999 1000 0 1 3254268794313975 1125899906842624 5000000001657 414250000000000000 11194554481688301441 45035996273704960 429995000142500343 414250000000000000000 qz151 (BSN.isNear_log_sfrac 18 1 3254268794313975 1125899906842624 5000000001657 414250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz446) Bool.false 27298785242132565196800 9444732965739290427392 1000000000331400 82850000000000000000 3254268794313975 1125899906842624 5000000001657 414250000000000000 (BSN.log_rat_reduce_isNear 18 1 4 36 32 30876 262144 24973259072661432 36028797018963968 82850 1000000000000000 rfl rfl rfl rfl (ep866 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep868 := nat_lit 28668422947826433757399533974206881

noncomputable def ep869 := BSN.cos_dyadic_bound_f 411482103 1073741824 2 1 524288 165862 ep868 ep126 ep868 ep868 ep127 ep868 486258 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 411482103) qz282 0 1 ep868 ep126 ep868 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 411482103) qz283 0 1 ep868 ep127 ep868 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz216 := qz442

noncomputable abbrev qz448 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 65160883) qz497)

noncomputable def ep870 := @Enclosure.Real.IsNear.cos_image qz216 qz448 Bool.false 65160883 262144 545 524288 Bool.true 486258 524288 1 82850 (@Enclosure.Real.IsNear.recentre' qz216 Bool.false 11194554481688301441 45035996273704960 429995000142500343 414250000000000000000 65160883 262144 545 524288 (ep867 rfl) rfl) (Enclosure.sfrac_false_div 65160883 262144) (BSN.cos_reduce2 qz448 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 14477739444129094434816) qz325) 226375608064910080 72057594037927936 Bool.false 486258 524288 39 1000000000000000 165700 82850 (BSN.sin_reduce_arg_pos_rat_q2 65160883 262144 226375608064910080 72057594037927936 39 14477739444129094434816 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 486258 524288 14477739444129094434816 37778931862957161709568 411482103 1073741824 165862 165700 (ep869 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep871 := BSN.sin_dyadic_bound_f 411482103 1073741824 2 1 524288 165862 ep868 ep80 ep868 ep868 ep81 ep868 196037 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 411482103) qz286 0 1 ep868 ep80 ep868 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 411482103) qz287 0 1 ep868 ep81 ep868 rfl rfl rfl rfl) rfl rfl

noncomputable def ep872 := @Enclosure.Real.IsNear.sin_image qz216 qz448 Bool.false 65160883 262144 545 524288 Bool.true 196037 524288 1 82850 (@Enclosure.Real.IsNear.recentre' qz216 Bool.false 11194554481688301441 45035996273704960 429995000142500343 414250000000000000000 65160883 262144 545 524288 (ep867 rfl) rfl) (Enclosure.sfrac_false_div 65160883 262144) (BSN.sin_reduce2 qz448 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 14477739444129094434816) qz325) 226375608064910080 72057594037927936 Bool.false 196037 524288 39 1000000000000000 165700 82850 (BSN.sin_reduce_arg_pos_rat_q2 65160883 262144 226375608064910080 72057594037927936 39 14477739444129094434816 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 196037 524288 14477739444129094434816 37778931862957161709568 411482103 1073741824 165862 165700 (ep871 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep873 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz443 qz213) (@HMul.hMul Real Real Real qz0 qz443 qz444) Bool.true 30044666175 137438953472 1421233477797 5693408647577600 Bool.false 24225272275 274877906944 2830444550669 11386817295155200 (@Enclosure.Real.IsNear.mulLit_ft qz443 qz213 123575 524288 1 524288 243129 262144 22838769 21718630400 30044666175 137438953472 1421233477797 5693408647577600 (@Enclosure.Real.IsNear.recentre' qz443 Bool.false 123575 524288 1 524288 123575 524288 1 524288 (ep865 rfl rfl) rfl) (@Enclosure.Real.IsNear.recentre' qz213 Bool.true 486258 524288 45677538 43437260800 243129 262144 22838769 21718630400 (ep870 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz443 qz444 123575 524288 1 524288 196037 524288 22838769 21718630400 24225272275 274877906944 2830444550669 11386817295155200 (@Enclosure.Real.IsNear.recentre' qz443 Bool.false 123575 524288 1 524288 123575 524288 1 524288 (ep865 rfl rfl) rfl) (@Enclosure.Real.IsNear.neg qz214 Bool.true 196037 524288 22838769 21718630400 (@Enclosure.Real.IsNear.recentre' qz214 Bool.true 196037 524288 45677538 43437260800 196037 524288 22838769 21718630400 (ep872 rfl rfl) rfl)) rfl)

noncomputable def ep874 := @ep863 3195105696432 0 1 16034447018008690203325 146377327716679934803968 758493796110757641567983 ep860 (@Enclosure.Complex.IsNear.re_isNear qz206 Bool.true 30044666175 137438953472 1421233477797 5693408647577600 Bool.false 24225272275 274877906944 2830444550669 11386817295155200 (ep864 ep873))

noncomputable def ep875 := @Enclosure.Complex.IsNear.re_isNear (@HAdd.hAdd Complex Complex Complex qz4 qz207 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz80 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz126 qz208 (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz80 2 k) 1))))) Bool.false 1601060926217 3195105696432 0 1 Bool.false

noncomputable def ep876 := @Enclosure.Complex.IsNear.addLitP qz207 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz80 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz126 qz208 (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) Bool.false 7378078001 14792156002 0 1 Bool.true 1547982000

noncomputable def ep877 := @ep876 7396078001 0 1 Bool.false 1 432 0 1 Bool.false 85999 216000 0 1 Bool.false 3202121852434 1601060926217 3195105696432 0 1 Bool.false 301691200007999 301691200007999 1597552848216000 0 1

noncomputable abbrev qz217 := (@HDiv.hDiv Complex Complex Complex qz360 qz440 (@HSub.hSub Complex Complex Complex qz352 qz400 (1 : Complex)))

noncomputable def ep878 := @Enclosure.Complex.IsNear.addLitP qz217 qz99 Bool.true 36000000 29584312004 0 1 Bool.true 6191928000 29584312004 0 1

noncomputable def ep879 := @Enclosure.Complex.IsNear.of_eq qz217 (Complex.mk (Enclosure.sfrac Bool.true 36000000 29584312004) (Enclosure.sfrac Bool.true 6191928000 29584312004)) Bool.true 36000000 29584312004 0 1 Bool.true 6191928000 29584312004 0 1

noncomputable def ep880 := @ep878 Bool.false 1 2 0 1 Bool.false 0 1 0 1 Bool.false 29512312004 7378078001 14792156002 0 1 Bool.true 6191928000 1547982000 7396078001 0 1 (ep879 (BSN.N_div_s_sub_one_mk qz149 85999 1000 18 qz150 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 36000000 29584312004) (Enclosure.sfrac Bool.true 6191928000 29584312004) Bool.true 36000000 29584312004 0 1 Bool.true 6191928000 29584312004 0 1 (Enclosure.Real.IsNear.const Bool.true 36000000 29584312004) (Enclosure.Real.IsNear.const Bool.true 6191928000 29584312004))) qz100 rfl

noncomputable abbrev qz218 := (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz390 qz440 1))

noncomputable def ep881 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz80 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz126 qz208 (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) (@HAdd.hAdd Complex Complex Complex qz4 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz80 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz126 qz208 (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz136) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 1))) qz218)) Bool.false 1 432 0 1

noncomputable def ep882 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz80 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz126 qz208 (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz136) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 1))) qz218) Bool.false 0 1 0 1 Bool.false

noncomputable def ep883 := @ep882 0 1 0 1 Bool.false 1 432 0 1 Bool.false 85999 216000 0 1 Bool.false 1 1 432 0 1 Bool.false 85999 85999 216000 0

noncomputable def ep884 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz80 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz126 qz208 (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) (Complex.mk qz13 qz13) Bool.false 0 1 0 1 Bool.false

noncomputable def ep885 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz136) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 1))) qz218 Bool.false 1 432 0 1 Bool.false 85999 216000 0 1

noncomputable def ep886 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz136) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz218)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz136) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz218)) 1 432 0 1 0 1 0

noncomputable def ep887 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz136) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz218) 1 24 0 1 1 18 0 1 1

noncomputable def ep888 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz136)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz136)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 1)))) 1 24 0 1 0 1 0 1 1

noncomputable def ep889 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz136)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 1 2 0 1 1 24 0

noncomputable def ep890 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 1)) qz140 Bool.false 1 2 0 1 Bool.false 85999 1000 0 1 (BSN.ascPochhammer_one_eval qz140)

noncomputable def ep891 := ep890 (@Enclosure.Complex.IsNear.of_eq qz140 (Complex.mk qz94 qz149) Bool.false 1 2 0 1 Bool.false 85999 1000 0 1 (BSN.s_crit_mk qz149 Bool.false 85999 1000 qz150) (@Enclosure.Complex.IsNear.mk qz94 qz149 Bool.false 1 2 0 1 Bool.false 85999 1000 0 1 qz370 qz151))

noncomputable def ep892 := @ep889 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz136) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep471) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 85999 1000 0 1 ep891)

noncomputable def ep893 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz136)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 85999 1000 0 1 0 1 0

noncomputable def ep894 := @ep893 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz136) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep471) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 85999 1000 0 1 ep891)

noncomputable def ep895 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz136)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz136)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 1)))) 85999 12000 0 1 0 1 0 1 85999

noncomputable def ep896 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz136)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 85999 1000 0 1 85999 12000 0

noncomputable def ep897 := @ep896 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz136) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep471) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 85999 1000 0 1 ep891)

noncomputable def ep898 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz136)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 1 2 0 1 0 1 0

noncomputable def ep899 := @ep898 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz136) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep471) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 85999 1000 0 1 ep891)

noncomputable def ep900 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz136) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 24 0 1 Bool.false 85999 12000 0 1 (@ep888 1 24 0 1 (ep892 rfl) (ep894 rfl) rfl rfl) (@ep895 85999 12000 0 1 (ep897 rfl) (ep899 rfl) rfl rfl)

noncomputable def ep901 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz136) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 85999 12000 0 1 ep900

noncomputable abbrev qz219 := (@Enclosure.Complex.IsNear.of_eq (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz390 qz440 1)) (Complex.mk (Enclosure.sfrac Bool.false 1 18) qz277) Bool.false 1 18 0 1 Bool.false 0 1 0 1 (BSN.natCast_pow_inv_mk 18 1 18 EMRow23.d13 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 18) qz277 Bool.false 1 18 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 18) qz289))

noncomputable def ep902 := @ep887 432 0 1 ep901 (@Enclosure.Complex.IsNear.re_isNear qz218 Bool.false 1 18 0 1 Bool.false 0 1 0 1 qz219)

noncomputable def ep903 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz136) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz218) 85999 12000 0 1 0 1 0 1 0

noncomputable def ep904 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz136) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 85999 12000 0 1 ep900

noncomputable def ep905 := @ep903 1 0 1 ep904 (@Enclosure.Complex.IsNear.im_isNear qz218 Bool.false 1 18 0 1 Bool.false 0 1 0 1 qz219)

noncomputable def ep906 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz136) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz218)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz136) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz218)) 0 1 0 1 85999 216000 0

noncomputable def ep907 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz136) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz218) 1 24 0 1 0 1 0 1 0

noncomputable def ep908 := @ep907 1 0 1 ep901 (@Enclosure.Complex.IsNear.im_isNear qz218 Bool.false 1 18 0 1 Bool.false 0 1 0 1 qz219)

noncomputable def ep909 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz136) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz218) 85999 12000 0 1 1 18 0 1 85999

noncomputable def ep910 := @ep909 216000 0 1 ep904 (@Enclosure.Complex.IsNear.re_isNear qz218 Bool.false 1 18 0 1 Bool.false 0 1 0 1 qz219)

noncomputable def ep911 := @ep883 1 (@ep884 0 1 0 1 (BSN.bern_sum_base qz140 18) qz115) (ep885 (@ep886 1 1 1 432 0 1 (ep902 rfl) (ep905 rfl) rfl rfl) (@ep906 1 85999 85999 216000 0 1 (ep908 rfl) (ep910 rfl) rfl rfl)) rfl rfl rfl rfl rfl

noncomputable def ep912 := ep877 (ep880 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep881 Bool.false 85999 216000 0 1 (BSN.bern_sum_succ qz140 18 0 1 1 rfl rfl) (ep911 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl rfl

noncomputable def ep913 := @Enclosure.Real.IsNear.mulLit_ff qz212 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz207 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz80 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz126 qz208 (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))))) 24225272275 274877906944 2830444550669 11386817295155200 301691200007999

noncomputable def ep914 := @ep913 1597552848216000 0 1 292342058526610318117109 ep716 ep861 ep718 (@Enclosure.Complex.IsNear.im_isNear qz206 Bool.true 30044666175 137438953472 1421233477797 5693408647577600 Bool.false 24225272275 274877906944 2830444550669 11386817295155200 (ep864 ep873))

noncomputable def ep915 := @Enclosure.Complex.IsNear.im_isNear (@HAdd.hAdd Complex Complex Complex qz4 qz207 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz80 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz126 qz208 (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz80 2 k) 1))))) Bool.false 1601060926217 3195105696432 0 1 Bool.false

noncomputable def ep916 := nat_lit 2927546554333598696079360

noncomputable def ep917 := nat_lit 142924544469372910996299401

noncomputable def ep918 := @Enclosure.Real.IsNear.addLit_tf_p (@HMul.hMul Real Real Real qz0 qz211 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz207 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz80 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz126 qz208 (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz80 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz212 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz207 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz80 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz126 qz208 (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz80 2 k) 1))))))) 120856151895673163796451 ep916 ep917

noncomputable def ep919 := nat_lit 3031840400331733149627187200000

noncomputable def ep920 := nat_lit 4531714173899969526989173

noncomputable def ep921 := nat_lit 36382084803980797795526246400

noncomputable def ep922 := nat_lit 7404618023688308665157417677185557427589742592

noncomputable def ep923 := @Enclosure.Real.IsNear.mulLit_tf qz211 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz207 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz80 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz126 qz208 (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))))) 30044666175 137438953472 1421233477797 5693408647577600 301691200007999

noncomputable def ep924 := @ep923 1597552848216000 0 1 120856151895673163796451 ep916 ep917 ep919 (@Enclosure.Complex.IsNear.re_isNear qz206 Bool.true 30044666175 137438953472 1421233477797 5693408647577600 Bool.false 24225272275 274877906944 2830444550669 11386817295155200 (ep864 ep873))

noncomputable def ep925 := @Enclosure.Real.IsNear.mulLit_ff qz212 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz207 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz80 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz126 qz208 (@HSub.hSub Nat Nat Nat qz125 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))))) 24225272275 274877906944 2830444550669 11386817295155200 1601060926217

noncomputable def ep926 := @ep925 3195105696432 0 1 38786136866470510733675 878263966300079608823808 ep920 ep921 (@Enclosure.Complex.IsNear.im_isNear qz206 Bool.true 30044666175 137438953472 1421233477797 5693408647577600 Bool.false 24225272275 274877906944 2830444550669 11386817295155200 (ep864 ep873))

noncomputable abbrev qz449 := (ep912 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable def ep927 := @ep858 25292912977685615947397 ep835 ep842 ep837 (@ep859 ep860 292342058526610318117109 ep716 ep861 ep718 ep862 ep840 ep716 ep841 ep718 (ep874 (@ep875 301691200007999 1597552848216000 0 1 qz449) rfl) (ep914 (@ep915 301691200007999 1597552848216000 0 1 qz449) rfl) rfl rfl) (@ep918 ep919 38786136866470510733675 878263966300079608823808 ep920 ep921 ep922 25292912977685615947397 ep835 ep842 ep837 (ep924 (@ep915 301691200007999 1597552848216000 0 1 qz449) rfl) (ep926 (@ep875 301691200007999 1597552848216000 0 1 qz449) rfl) rfl rfl)

noncomputable def ep928 := @ep845 ep836 ep837 (@ep846 2277363459031040 (BSN.head_sum_c_eq qz140 18) (ep847 (BSN.head_sum_c_succ qz140 17 18 rfl rfl) (ep857 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))) ep927 rfl rfl rfl

noncomputable def ep929 := @Enclosure.Complex.IsNear.re_isNear (zetaApproximant qz140 1 18) Bool.false ep715 ep716 ep717 ep718 Bool.false 566691560631152197521317 ep835 ep836 ep837 (@ep838 ep718 Bool.false 566691560631152197521317 ep835 ep836 ep837 (BSN.zetaApproximant_eq_folded' qz140 1 18 rfl) (ep928 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

noncomputable def ep930 := @Enclosure.Real.IsNear.mulLit_tf (Real.sin (@HSub.hSub Real Real Real qz355 (Complex.im (@HSub.hSub Complex Complex Complex qz73 qz175 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz176 (@Nat.cast Complex Complex.instNatCast j))))) qz177)) (Complex.im (zetaApproximant qz140 1 18)) 299 524288 10742669

noncomputable def ep931 := @Enclosure.Real.IsNear.recentre' (Real.sin (@HSub.hSub Real Real Real qz355 (Complex.im (@HSub.hSub Complex Complex Complex qz73 qz175 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz176 (@Nat.cast Complex Complex.instNatCast j))))) qz177)) Bool.true 299 524288 21485338

noncomputable def ep932 := @Enclosure.Real.IsNear.sin_image (@HSub.hSub Real Real Real qz355 (Complex.im (@HSub.hSub Complex Complex Complex qz73 qz175 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz176 (@Nat.cast Complex Complex.instNatCast j))))) qz177) qz421 Bool.false 36235885 524288 253

noncomputable def ep933 := nat_lit 18110189642240612827404589070378967541412409396647125961157425666986458317056

noncomputable def ep934 := nat_lit 54199975567453199753536371906860570774139447410210866349941757057871609692416

noncomputable def ep935 := BSN.cos_dyadic_bound_f 1686014818 1073741824 3 2 524288 165862 ep933 ep57 ep831 ep934 ep60 ep831 299 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1686014818) qz282 0 2 ep933 ep57 ep831 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1686014818) qz283 0 2 ep934 ep60 ep831 rfl rfl rfl rfl) rfl rfl

noncomputable def ep936 := @ep932 524288 Bool.true 299 524288 1 82850 (@ep722 36235885 524288 253 524288 ep829 rfl) (Enclosure.sfrac_false_div 36235885 524288) (BSN.sin_reduce3 qz421 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 118642745421254885376000) qz22) 226375608064910080 72057594037927936 Bool.false 299 524288 10 1000000000000000 165700 82850 (BSN.sin_reduce_arg_pos_rat_q3 36235885 524288 226375608064910080 72057594037927936 10 118642745421254885376000 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 299 524288 118642745421254885376000 75557863725914323419136 1686014818 1073741824 165862 165700 (ep935 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep937 := @Enclosure.Complex.IsNear.im_isNear (zetaApproximant qz140 1 18) Bool.false ep715 ep716 ep717 ep718 Bool.false 566691560631152197521317 ep835 ep836 ep837 (@ep838 ep718 Bool.false 566691560631152197521317 ep835 ep836 ep837 (BSN.zetaApproximant_eq_folded' qz140 1 18 rfl) (ep928 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

theorem EMRow23.d14 : Enclosure.Real.IsNear (hardyZApproximantEM 1 18 qz149) Bool.false ep698 ep699 ep700 ep701 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantEM 1 18 qz149) ep702 Bool.false ep698 ep699 ep700 ep701 (@Eq.refl Real ep702) (@ep703 Bool.false ep698 ep699 ep700 ep701 (BSN.re_exp_mul (@HSub.hSub Real Real Real qz355 (Complex.im (@HSub.hSub Complex Complex Complex qz73 qz175 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz176 (@Nat.cast Complex Complex.instNatCast j))))) qz177) (zetaApproximant qz140 1 18)) (@ep705 ep706 ep707 ep708 ep709 ep710 ep711 ep712 ep713 ep698 ep699 ep700 ep701 (@ep714 21718630400 ep715 ep716 ep717 ep718 ep704 ep706 ep707 ep708 (@ep719 43437260800 524287 524288 10742669 21718630400 (ep834 rfl rfl) rfl) ep929 rfl) (@ep930 21718630400 566691560631152197521317 ep835 ep836 ep837 ep709 ep710 ep711 ep712 (@ep931 43437260800 299 524288 10742669 21718630400 (ep936 rfl rfl) rfl) ep937 rfl) rfl rfl))

theorem EMRow23.d15 : @Eq Nat (Nat.mul (BSN.factNat (Nat.succ (Nat.mul 2 1))) (Nat.pow 4 (Nat.mul 2 1))) 96 := @Eq.refl Nat 96

theorem EMRow23.d16 : @Eq Nat (Nat.mul (Nat.mul 2 1) (Nat.pow (Nat.succ (Nat.mul 4 2)) (Nat.mul 2 1))) 162 := @Eq.refl Nat 162

theorem EMRow23.d17 : @Eq Nat (BSN.factNat (Nat.mul 2 2)) 24 := @Eq.refl Nat 24

theorem EMRow23.d18 : @Eq Nat (Nat.pow 17 (Nat.succ (Nat.mul 2 3))) 410338673 := @Eq.refl Nat 410338673

noncomputable abbrev qz511 := (@HAdd.hAdd Complex Complex Complex qz515 qz514 (@Nat.cast Complex Complex.instNatCast 3))

noncomputable abbrev qz450 := qz511

noncomputable abbrev qz220 := (@HDiv.hDiv Real Real Real qz269 (@Norm.norm Complex Complex.instNorm qz450) (@HAdd.hAdd Real Real Real qz380 (Complex.re qz271) qz290))

noncomputable abbrev qz221 := (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 2)

noncomputable abbrev qz222 := (@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 2)))

noncomputable abbrev qz451 := (@HPow.hPow Complex Complex Complex qz490 (@Nat.cast Complex Complex.instNatCast 17) (@HSub.hSub Complex Complex Complex qz499 qz491 qz492))

noncomputable abbrev qz223 := qz451

noncomputable def ep938 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 17))) (@HMul.hMul Real Real Real qz0 qz220 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))) 1463836247 77309411328 21462323 231928233984 60378446518956665 63050394783186944 39140920487

noncomputable def ep939 := nat_lit 4760117610550959318696460288

noncomputable def ep940 := @Enclosure.Real.IsNear.mulLit_ff (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 17)) 4427 294912 1 884736 330661 262144 1591 262144 1463836247 77309411328

noncomputable abbrev qz224 := qz270

noncomputable abbrev qz512 := (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid)))

noncomputable abbrev qz452 := (@Inv.inv Real Real.instInv (@HPow.hPow Real Nat Real qz512 qz224 2))

noncomputable def ep941 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 96 162) qz452 96 162 0 1 13281 524288 1 524288 4427 294912 1 884736

noncomputable def ep942 := nat_lit 781950621441006189802102638025

noncomputable def ep943 := nat_lit 19807040628566084398385987584

noncomputable def ep944 := nat_lit 26986075409044041160201671

noncomputable def ep945 := nat_lit 1073741824000000000000000000000000000000

noncomputable abbrev qz453 := (@HPow.hPow Real Nat Real qz512 qz224 1)

noncomputable def ep946 := @Enclosure.Real.IsNear.mulLit_ff qz453 qz224 884279719003555 140737488355328 1 500000000000000 884279719003555 140737488355328 1 500000000000000 ep942 ep943 ep944 ep945

noncomputable def ep947 := ep946 (@Enclosure.Real.IsNear.of_eq qz453 qz224 Bool.false 884279719003555 140737488355328 1 500000000000000 (BSN.pow_one_r qz224) (@Enclosure.Real.IsNear.of_eq qz224 qz267 Bool.false 884279719003555 140737488355328 1 500000000000000 BSN.two_pi_eq qz268)) (@Enclosure.Real.IsNear.of_eq qz224 qz267 Bool.false 884279719003555 140737488355328 1 500000000000000 BSN.two_pi_eq qz268) rfl

noncomputable abbrev qz454 := (@HPow.hPow Real Nat Real qz512 qz224 2)

noncomputable def ep948 := @Enclosure.Real.IsNear.inv_image qz454 ep942 ep943 ep944 ep945 6640 6641 262144 (@Enclosure.Real.IsNear.of_eq qz454 (@HMul.hMul Real Real Real qz0 qz453 qz224) Bool.false ep942 ep943 ep944 ep945 (BSN.pow_succ_r qz224 1 2 rfl) ep947) rfl rfl rfl

noncomputable def ep949 := ep941 (Enclosure.Real.IsNear.const Bool.false 96 162) (@Enclosure.Real.IsNear.recentre' qz452 Bool.false 13281 524288 1 524288 13281 524288 1 524288 (ep948 rfl rfl rfl) rfl)

noncomputable def ep950 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 17)) (Real.sqrt (@HAdd.hAdd Real Real Real qz380 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz5 1 17)) (Complex.re (zetaApproximant qz5 1 17))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz5 1 17)) (Complex.im (zetaApproximant qz5 1 17))))) Bool.false 330661 262144 1591 262144

noncomputable def ep951 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz380 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz5 1 17)) (Complex.re (zetaApproximant qz5 1 17))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz5 1 17)) (Complex.im (zetaApproximant qz5 1 17))))) Bool.false 661322 524288 3182 524288

noncomputable def ep952 := nat_lit 55927969767670147497522805886042796146113

noncomputable def ep953 := nat_lit 35150557856789768082749294180365762560000

noncomputable def ep954 := nat_lit 10321878798212281626434468564742016603456001042003893027

noncomputable def ep955 := nat_lit 674294275389158142310895536502872987029378856648704000000

noncomputable def ep956 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz380 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz5 1 17)) (Complex.re (zetaApproximant qz5 1 17))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz5 1 17)) (Complex.im (zetaApproximant qz5 1 17)))) ep952 ep953 ep954 ep955 329070 332252

noncomputable def ep957 := nat_lit 15629064697994104121680371551550963849873115628521

noncomputable def ep958 := nat_lit 9823459231520972160839139110685640983670947840000

noncomputable def ep959 := nat_lit 10215408369168914333597490324571332040578664683526908851

noncomputable def ep960 := nat_lit 63633414152873862528702708710510081103078721

noncomputable def ep961 := nat_lit 613966201970060760052446194417852561479434240000

noncomputable def ep962 := nat_lit 391435400894732694253596471215752069401971906165383

noncomputable def ep963 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz5 1 17)) (Complex.re (zetaApproximant qz5 1 17))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz5 1 17)) (Complex.im (zetaApproximant qz5 1 17))) ep957 ep958 ep959 ep955 ep960 ep961 ep962

noncomputable def ep964 := nat_lit 2479023071283669640848880648907621275843304620032000000

noncomputable def ep965 := nat_lit 9596342593221488053858864547470077769710027481105940609226004857492252632984822938301292871680000

noncomputable def ep966 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (zetaApproximant qz5 1 17)) (Complex.re (zetaApproximant qz5 1 17)) ep297 ep298 ep299 ep300 ep297 ep298 ep299 ep300 ep957

noncomputable def ep967 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (zetaApproximant qz5 1 17)) (Complex.im (zetaApproximant qz5 1 17)) 7977055481371172118689 783559954291987002163200 ep426 ep427 7977055481371172118689 783559954291987002163200 ep426 ep427 ep960

noncomputable def ep968 := @ep938 63050394783186944 ep939 554150623566349889 567453553048682496 158590942467485 1702360659146047488 (@ep940 21462323 231928233984 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaStirlingErrorBound 1 2) (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 96 162) qz452) Bool.false 4427 294912 1 884736 (BSN.theta_err_eq 1 2 96 162 EMRow23.d15 EMRow23.d16 rfl) (ep949 rfl)) (ep950 (BSN.norm_eq_sqrt_mul_add (zetaApproximant qz5 1 17)) (@ep951 330661 262144 1591 262144 (@ep956 262144 (@ep963 ep964 ep965 ep952 ep953 ep954 ep955 (@ep966 ep958 ep959 ep955 ep508 ep508 rfl) (@ep967 ep961 ep962 ep964 ep514 ep514 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl)

noncomputable abbrev qz225 := (@Norm.norm Complex Complex.instNorm qz450)

noncomputable abbrev qz455 := (Enclosure.sfrac Bool.false 2 7)

noncomputable def ep969 := @Enclosure.Real.IsNear.of_eq (@HMul.hMul Real Real Real qz0 qz220 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))) (@HMul.hMul Real Real Real qz0 (@HMul.hMul Real Real Real qz0 qz225 qz455) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))) Bool.false 60378446518956665 63050394783186944 39140920487 63050394783186944 (BSN.zrb_shape_eq qz225 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) qz16 3)

noncomputable def ep970 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz0 qz225 qz455) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) 43861015 1835008 1 1835008 1376585711 34359738368 861 34359738368

noncomputable def ep971 := @Enclosure.Real.IsNear.mulLit_ff qz225 qz455 43861015 524288 1 524288 2 7 0 1 43861015 1835008

noncomputable abbrev qz456 := (Complex.re qz511)

noncomputable abbrev qz457 := (Complex.im qz511)

noncomputable abbrev qz226 := (@HAdd.hAdd Real Real Real qz380 (@HMul.hMul Real Real Real qz266 qz456 qz456) (@HMul.hMul Real Real Real qz266 qz457 qz457))

noncomputable abbrev qz227 := qz450

noncomputable def ep972 := @Enclosure.Real.IsNear.of_eq qz225 (Real.sqrt qz226) Bool.false 43861015 524288 1 524288 (BSN.norm_eq_sqrt_mul_add qz227)

noncomputable def ep973 := @Enclosure.Real.IsNear.recentre' (Real.sqrt qz226) Bool.false 43861015 524288 1 524288 43861015

noncomputable def ep974 := @Enclosure.Real.IsNear.sqrt_image qz226 279948089 40000 0 1 21930507 21930508 262144

noncomputable abbrev qz228 := (@HMul.hMul Real Real Real qz266 qz456 qz456)

noncomputable abbrev qz229 := (@HMul.hMul Real Real Real qz266 qz457 qz457)

noncomputable def ep975 := @Enclosure.Real.IsNear.addLit_ff qz228 qz229 49 4 0 1 279458089 40000 0 1

noncomputable abbrev qz230 := qz456

noncomputable def ep976 := @Enclosure.Real.IsNear.mulLit_ff qz230 qz230 7 2 0 1 7 2 0 1 49 4

noncomputable abbrev qz458 := (Enclosure.sfrac Bool.false 7 2)

noncomputable def ep977 := @Enclosure.Complex.IsNear.of_eq qz227 (Complex.mk qz458 qz16) Bool.false 7 2 0 1 Bool.false 83585 1000 0 1 (BSN.s_add_nat_mk qz16 Bool.false 83585 1000 3 qz17)

noncomputable abbrev qz459 := (ep977 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7 2) qz16 Bool.false 7 2 0 1 Bool.false 83585 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 7 2) qz21))

noncomputable def ep978 := @ep976 0 1 (@Enclosure.Complex.IsNear.re_isNear qz227 Bool.false 7 2 0 1 Bool.false 83585 1000 0 1 qz459)

noncomputable def ep979 := ep978 (@Enclosure.Complex.IsNear.re_isNear qz227 Bool.false 7 2 0 1 Bool.false 83585 1000 0 1 qz459)

noncomputable abbrev qz231 := qz457

noncomputable def ep980 := @Enclosure.Real.IsNear.mulLit_ff qz231 qz231 83585 1000 0 1 83585 1000 0 1 279458089 40000

noncomputable def ep981 := @ep980 0 1 (@Enclosure.Complex.IsNear.im_isNear qz227 Bool.false 7 2 0 1 Bool.false 83585 1000 0 1 qz459)

noncomputable def ep982 := ep981 (@Enclosure.Complex.IsNear.im_isNear qz227 Bool.false 7 2 0 1 Bool.false 83585 1000 0 1 qz459)

noncomputable def ep983 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Real.sqrt (@HAdd.hAdd Real Real Real qz380 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.re (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.im (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))))) Bool.false 1376585711 34359738368

noncomputable def ep984 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz380 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.re (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.im (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))))) Bool.false 1376585711 34359738368

noncomputable def ep985 := nat_lit 7422516605298299024845731890484780010147860888959235371693

noncomputable def ep986 := nat_lit 4624282524367310014628846541016364241880099061760000000000000

noncomputable def ep987 := nat_lit 61658571931681693120945365125004366821813751186036039123391987186374119

noncomputable def ep988 := nat_lit 30753054643175826045040342197069218938560777119837005931347968000000000000000000

noncomputable def ep989 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz380 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.re (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.im (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)))) ep985 ep986 ep987 ep988

noncomputable def ep990 := nat_lit 66778987694712717391156660215167750228690087596316642595361

noncomputable def ep991 := nat_lit 46242825243673100146288465410163642418800990617600000000000000

noncomputable def ep992 := nat_lit 321429592217675435839995114931618698768908352634185851497434830406084757

noncomputable def ep993 := nat_lit 184518327859054956270242053182415313631364662719022035588087808000000000000000000

noncomputable def ep994 := nat_lit 7446178358270272857300658689680049872788521293275711121569

noncomputable def ep995 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.re (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.im (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))) ep990 ep991 ep992 ep993 ep994

noncomputable def ep996 := nat_lit 48521839372414722885677075818407502161974154482030383242917092712159957

noncomputable def ep997 := nat_lit 3432381382470709467039533435902888368949157147741006608661161071398325928690853117795513142352701416275968000000000000000

noncomputable def ep998 := nat_lit 258416306944265259521819377519

noncomputable def ep999 := nat_lit 6800207735332289107722240000000

noncomputable def ep1000 := nat_lit 539260819251564763549265573147761

noncomputable def ep1001 := nat_lit 23527749224631855311599416901632000000000

noncomputable def ep1002 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.re (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) ep998 ep999 ep1000 ep1001 ep998 ep999 ep1000

noncomputable def ep1003 := nat_lit 86291241492229516174247407663

noncomputable def ep1004 := nat_lit 243783000240943325881511453298361

noncomputable def ep1005 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223) Bool.true ep998 ep999 ep1000 ep1001 Bool.true ep1003 ep999 ep1004

noncomputable def ep1006 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223 Bool.true ep998 ep999 ep1000 ep1001 Bool.true ep1003 ep999 ep1004 ep1001

noncomputable def ep1007 := nat_lit 17945912970594724445018117

noncomputable def ep1008 := nat_lit 22667359117774297025740800000

noncomputable def ep1009 := nat_lit 38676454134001614218796563099

noncomputable def ep1010 := nat_lit 78425830748772851038664723005440000000

noncomputable def ep1011 := nat_lit 253032533053086842188313942419

noncomputable def ep1012 := nat_lit 527657883011364279283626604218061

noncomputable abbrev qz232 := (Complex.re qz451)

noncomputable abbrev qz233 := (Complex.im qz451)

noncomputable def ep1013 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz232) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz233) ep1007 ep1008 ep1009 ep1010 ep1011 ep999 ep1012

noncomputable def ep1014 := nat_lit 5857615231394652519158149758875478861577077375841075200000

noncomputable def ep1015 := nat_lit 4084678684831919324930454323200

noncomputable def ep1016 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz232 838324267 19200000 0 1 21406887140241551 1180591620717411303424 46135434290132047697 ep1015 ep1007

noncomputable def ep1017 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) 838324267 19200000 0 1 0 1 0 1 838324267

noncomputable def ep1018 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 2514972801 80000 0 1 838324267 19200000 0

noncomputable def ep1019 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (Complex.mk (Enclosure.sfrac Bool.true 1 720) qz13) Bool.true 1 720 0 1 Bool.false 0 1 0 1 (BSN.bern_coeff_mk 2 1 30 24 Bool.true BSN.bern_real_2 EMRow23.d17 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 1 720) qz13 Bool.true 1 720 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.true 1 720) qz23)

noncomputable abbrev qz460 := (@HAdd.hAdd Complex Complex Complex qz489 qz488 qz493)

noncomputable abbrev qz234 := qz460

noncomputable def ep1020 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) (@HMul.hMul Complex Complex Complex qz72 (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) qz234) Bool.true 2514972801 80000 0 1 Bool.true 4667855963813 8000000 0 1

noncomputable abbrev qz235 := (Complex.re qz460)

noncomputable abbrev qz236 := (Complex.im qz460)

noncomputable def ep1021 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz235) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz236) 279428089 16000 0 1 279458089 20000 0 1

noncomputable def ep1022 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz235 279428089 40000 0 1 5 2 0 1 279428089 16000

noncomputable abbrev qz461 := (@HAdd.hAdd Complex Complex Complex qz489 qz488 (@Nat.cast Complex Complex.instNatCast 1))

noncomputable abbrev qz237 := qz461

noncomputable def ep1023 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) (@HMul.hMul Complex Complex Complex qz72 (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) qz237) Bool.true 279428089 40000 0 1 Bool.false 16717 100 0 1

noncomputable abbrev qz238 := (Complex.re qz461)

noncomputable abbrev qz239 := (Complex.im qz461)

noncomputable def ep1024 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz238) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz239) 3 4 0 1 279458089 40000 0 1

noncomputable def ep1025 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz238 1 2 0 1 3 2 0 1 3 4

noncomputable def ep1026 := @ep1025 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 83585 1000 0 1 ep473)

noncomputable abbrev qz462 := (Enclosure.sfrac Bool.false 3 2)

noncomputable def ep1027 := @Enclosure.Complex.IsNear.of_eq qz237 (Complex.mk qz462 qz16) Bool.false 3 2 0 1 Bool.false 83585 1000 0 1 (BSN.s_add_nat_mk qz16 Bool.false 83585 1000 1 qz17)

noncomputable abbrev qz463 := (ep1027 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 3 2) qz16 Bool.false 3 2 0 1 Bool.false 83585 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 3 2) qz21))

noncomputable def ep1028 := ep1026 (@Enclosure.Complex.IsNear.re_isNear qz237 Bool.false 3 2 0 1 Bool.false 83585 1000 0 1 qz463)

noncomputable def ep1029 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz239 83585 1000 0 1 83585 1000 0 1 279458089 40000

noncomputable def ep1030 := @ep1029 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 83585 1000 0 1 ep473)

noncomputable def ep1031 := ep1030 (@Enclosure.Complex.IsNear.im_isNear qz237 Bool.false 3 2 0 1 Bool.false 83585 1000 0 1 qz463)

noncomputable def ep1032 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) qz237 Bool.true 279428089 40000 0 1 Bool.false 16717 100 0 1 (@ep1024 1117712356 279428089 40000 0 1 (ep1028 rfl) (ep1031 rfl) rfl rfl)

noncomputable def ep1033 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz239) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz238) 16717 400 0 1 50151 400 0 1

noncomputable def ep1034 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz239 1 2 0 1 83585 1000 0 1 16717 400

noncomputable def ep1035 := @ep1034 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 83585 1000 0 1 ep473)

noncomputable def ep1036 := ep1035 (@Enclosure.Complex.IsNear.im_isNear qz237 Bool.false 3 2 0 1 Bool.false 83585 1000 0 1 qz463)

noncomputable def ep1037 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz238 83585 1000 0 1 3 2 0 1 50151 400

noncomputable def ep1038 := @ep1037 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 83585 1000 0 1 ep473)

noncomputable def ep1039 := ep1038 (@Enclosure.Complex.IsNear.re_isNear qz237 Bool.false 3 2 0 1 Bool.false 83585 1000 0 1 qz463)

noncomputable abbrev qz240 := (ep1023 (BSN.ascPochhammer_succ_eval_c 1 2 qz271 rfl) (ep1032 (@ep1033 26747200 16717 100 0 1 (ep1036 rfl) (ep1039 rfl) rfl rfl)))

noncomputable def ep1040 := @ep1022 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 279428089 40000 0 1 Bool.false 16717 100 0 1 qz240)

noncomputable abbrev qz464 := (Enclosure.sfrac Bool.false 5 2)

noncomputable def ep1041 := @Enclosure.Complex.IsNear.of_eq qz234 (Complex.mk qz464 qz16) Bool.false 5 2 0 1 Bool.false 83585 1000 0 1 (BSN.s_add_nat_mk qz16 Bool.false 83585 1000 2 qz17)

noncomputable abbrev qz465 := (ep1041 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 5 2) qz16 Bool.false 5 2 0 1 Bool.false 83585 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 5 2) qz21))

noncomputable def ep1042 := ep1040 (@Enclosure.Complex.IsNear.re_isNear qz234 Bool.false 5 2 0 1 Bool.false 83585 1000 0 1 qz465)

noncomputable def ep1043 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz236 16717 100 0 1 83585 1000 0 1 279458089 20000

noncomputable def ep1044 := @ep1043 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 279428089 40000 0 1 Bool.false 16717 100 0 1 qz240)

noncomputable def ep1045 := ep1044 (@Enclosure.Complex.IsNear.im_isNear qz234 Bool.false 5 2 0 1 Bool.false 83585 1000 0 1 qz465)

noncomputable def ep1046 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) qz234 Bool.true 2514972801 80000 0 1 Bool.true 4667855963813 8000000 0 1 (@ep1021 10059891204000 2514972801 80000 0 1 (ep1042 rfl) (ep1045 rfl) rfl rfl)

noncomputable def ep1047 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz236) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz235) 4671199363813 8000000 0 1 16717 40 0 1

noncomputable def ep1048 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz236 279428089 40000 0 1 83585 1000 0 1 4671199363813 8000000

noncomputable def ep1049 := @ep1048 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 279428089 40000 0 1 Bool.false 16717 100 0 1 qz240)

noncomputable def ep1050 := ep1049 (@Enclosure.Complex.IsNear.im_isNear qz234 Bool.false 5 2 0 1 Bool.false 83585 1000 0 1 qz465)

noncomputable def ep1051 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz235 16717 100 0 1 5 2 0 1 16717 40

noncomputable def ep1052 := @ep1051 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 279428089 40000 0 1 Bool.false 16717 100 0 1 qz240)

noncomputable def ep1053 := ep1052 (@Enclosure.Complex.IsNear.re_isNear qz234 Bool.false 5 2 0 1 Bool.false 83585 1000 0 1 qz465)

noncomputable abbrev qz241 := (ep1020 (BSN.ascPochhammer_succ_eval_c 2 3 qz271 rfl) (ep1046 (@ep1047 186714238552520 4667855963813 8000000 0 1 (ep1050 rfl) (ep1053 rfl) rfl rfl)))

noncomputable def ep1054 := @ep1018 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1019) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 2514972801 80000 0 1 Bool.true 4667855963813 8000000 0 1 qz241)

noncomputable def ep1055 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 4667855963813 8000000 0 1 0 1 0

noncomputable def ep1056 := @ep1055 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1019) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 2514972801 80000 0 1 Bool.true 4667855963813 8000000 0 1 qz241)

noncomputable def ep1057 := @Enclosure.Real.IsNear.addLit_ft_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) 4667855963813 5760000000 0 1 0 1 0 1 4667855963813

noncomputable def ep1058 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 4667855963813 8000000 0 1 4667855963813 5760000000 0

noncomputable def ep1059 := @ep1058 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1019) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 2514972801 80000 0 1 Bool.true 4667855963813 8000000 0 1 qz241)

noncomputable def ep1060 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 2514972801 80000 0 1 0 1 0

noncomputable def ep1061 := @ep1060 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1019) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 2514972801 80000 0 1 Bool.true 4667855963813 8000000 0 1 qz241)

noncomputable def ep1062 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.false 838324267 19200000 0 1 Bool.false 4667855963813 5760000000 0 1 (@ep1017 838324267 19200000 0 1 (ep1054 rfl) (ep1056 rfl) rfl rfl) (@ep1057 4667855963813 5760000000 0 1 (ep1059 rfl) (ep1061 rfl) rfl rfl)

noncomputable def ep1063 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 838324267 19200000 0 1 Bool.false 4667855963813 5760000000 0 1 ep1062

noncomputable def ep1064 := @Enclosure.Complex.IsNear.re_isNear qz223 Bool.true 21406887140241551 1180591620717411303424 46135434290132047697 ep1015 Bool.false 54207442349269463 1180591620717411303424 113040737996624031497 ep1015

noncomputable abbrev qz466 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 410338673)))

noncomputable def ep1065 := @Enclosure.Complex.IsNear.of_eq qz223 (Complex.mk (@HMul.hMul Real Real Real qz0 qz466 qz131) (@HMul.hMul Real Real Real qz0 qz466 qz393)) Bool.true 21406887140241551 1180591620717411303424 46135434290132047697 ep1015 Bool.false 54207442349269463 1180591620717411303424 113040737996624031497

noncomputable abbrev qz467 := (Real.sqrt (@Nat.cast Real Real.instNatCast 410338673))

noncomputable abbrev qz468 := (@Nat.cast Real Real.instNatCast 410338673)

noncomputable def ep1066 := @Enclosure.Real.IsNear.inv_image qz467 696018964540551 34359738368 1 34359738368 848103 848104 17179869184 (@Enclosure.Real.IsNear.of_eq qz467 (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz468 qz18)) Bool.false 696018964540551 34359738368 1 34359738368 (BSN.sqrt_natCast_div_one 410338673) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz468 qz18)) Bool.false 696018964540551 34359738368 1 34359738368 696018964540551 34359738368 1 34359738368 (BSN.sqrt_enclosure 410338673 1 348009482270275 348009482270276 17179869184 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep1067 := nat_lit 6919714850000000000000000

noncomputable def ep1068 := nat_lit 1753674119217514004137115648

noncomputable def ep1069 := nat_lit 618970019642690137449562112

noncomputable def ep1070 := BSN.log_dyadic_bound 1 33 4 3 135604136745 17179869184 6919714850 41530119 15 1041523072 34 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 1) (BSN.artanhQ 33) 0 3 41530119 135604136745 15 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep1071 := @Enclosure.Real.IsNear.mulLit_ff qz16 qz133 83585 1000 0 1 3189914640129271 1125899906842624 5000138394297 34598574250000000000000 53325803039041023307 225179981368524800 83587313537462949 ep1067 qz21 (BSN.isNear_log_sfrac 17 1 3189914640129271 1125899906842624 5000138394297 34598574250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' qz396 Bool.false ep1068 ep1069 1000027678859400 ep1067 3189914640129271 1125899906842624 5000138394297 34598574250000000000000 (BSN.log_rat_reduce_isNear 17 1 4 34 32 1041523072 17179869184 24973259072661432 36028797018963968 6919714850 1000000000000000 rfl rfl rfl rfl (ep1070 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1072 := nat_lit 5915810137214307194520993792

noncomputable def ep1073 := nat_lit 4951760157141521099596496896

noncomputable def ep1074 := nat_lit 600106346968889193658901539345761129536743462762797303036035941895878874878034689024358053555488660607219465559527788355142668735887679888899147708377991832659321752968070721

noncomputable def ep1075 := nat_lit 7061461093083586024179172776487149921794651295521201685534719608389587370251949717138351715479917319946841476520062230191960740901052279494785699627855717567272383596304793600

noncomputable def ep1076 := nat_lit 124627281091035274316361109562746257886110489582229347409547529033478669868870292045090597146306232257632264620467820406006044330094742062759162996257387430260793509441

noncomputable def ep1077 := nat_lit 3637705064085204255103633969591430695133325378468345235021388293093703444872063707576420968455416678945245504974818591537606282975475232377807968654476217614855782456526210625

noncomputable def ep1078 := nat_lit 642592959470606328200304722660330642883313267892429353383659484363452450692927424259590006108672476115162574363325662947468427421995757434025498666134870298621786907263736217600

noncomputable def ep1079 := BSN.cos_dyadic_bound_f 84068718382671 70368744177664 4 3 34359738368 13852944769 ep1074 ep1075 ep1076 ep1077 ep1078 ep1076 12620444993 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 84068718382671) (BSN.cosEvenQ 70368744177664) 0 3 ep1074 ep1075 ep1076 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 84068718382671) (BSN.cosOddQ 70368744177664) 0 3 ep1077 ep1078 ep1076 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz469 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 8136871801611) (@Nat.cast Real Real.instNatCast 34359738368))

noncomputable def ep1080 := @Enclosure.Real.IsNear.cos_image qz134 qz469 Bool.false 8136871801611 34359738368 13 1073741824 Bool.true 12620444993 34359738368 1 6919714850 (@Enclosure.Real.IsNear.recentre' qz134 Bool.false 53325803039041023307 225179981368524800 83587313537462949 ep1067 8136871801611 34359738368 13 1073741824 (ep1071 rfl) rfl) (Enclosure.sfrac_false_div 8136871801611 34359738368) (BSN.cos_reduce2 qz469 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep1072) (@Nat.cast Real Real.instNatCast ep1073)) 226375608064910080 72057594037927936 Bool.false 12620444993 34359738368 37 1000000000000000 13839429700 6919714850 (BSN.sin_reduce_arg_pos_rat_q2 8136871801611 34359738368 226375608064910080 72057594037927936 37 ep1072 ep1073 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 12620444993 34359738368 ep1072 ep1073 84068718382671 70368744177664 13852944769 13839429700 (ep1079 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1081 := nat_lit 1559436452406557588757187334346946958456221812263781698202393913834053489756231905015090849578689658502044003743289071990105189029841205330554176161429293762852122562316043841

noncomputable def ep1082 := nat_lit 91798994210086618314329246094332948983330466841775621911951354909064635813275346322798572301238925159308939194760808992495489631713679633432214095162124328374540986751962316800

noncomputable def ep1083 := nat_lit 7793936887330168653578520781253395740143787575189214869341433895315117852790714041333345636201370565291010327619746799729061889021726619479953260016681814049684111125626062401

noncomputable def ep1084 := nat_lit 3212964797353031641001523613301653214416566339462146766918297421817262253464637121297950030543362380575812871816628314737342137109978787170127493330674351493108934536318681088000

noncomputable def ep1085 := BSN.sin_dyadic_bound_f 84068718382671 70368744177664 4 3 34359738368 13852944769 ep1081 ep1082 ep1076 ep1083 ep1084 ep1076 31958034809 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 84068718382671) (BSN.sinEvenQ 70368744177664) 0 3 ep1081 ep1082 ep1076 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 84068718382671) (BSN.sinOddQ 70368744177664) 0 3 ep1083 ep1084 ep1076 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1086 := @Enclosure.Real.IsNear.sin_image qz134 qz469 Bool.false 8136871801611 34359738368 13 1073741824 Bool.true 31958034809 34359738368 1 6919714850 (@Enclosure.Real.IsNear.recentre' qz134 Bool.false 53325803039041023307 225179981368524800 83587313537462949 ep1067 8136871801611 34359738368 13 1073741824 (ep1071 rfl) rfl) (Enclosure.sfrac_false_div 8136871801611 34359738368) (BSN.sin_reduce2 qz469 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep1072) (@Nat.cast Real Real.instNatCast ep1073)) 226375608064910080 72057594037927936 Bool.false 31958034809 34359738368 37 1000000000000000 13839429700 6919714850 (BSN.sin_reduce_arg_pos_rat_q2 8136871801611 34359738368 226375608064910080 72057594037927936 37 ep1072 ep1073 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 31958034809 34359738368 ep1072 ep1073 84068718382671 70368744177664 13852944769 13839429700 (ep1085 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1087 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz466 qz131) (@HMul.hMul Real Real Real qz0 qz466 qz393) Bool.true 21406887140241551 1180591620717411303424 46135434290132047697 ep1015 Bool.false 54207442349269463 1180591620717411303424 113040737996624031497 ep1015 (@Enclosure.Real.IsNear.mulLit_ft qz466 qz131 1696207 34359738368 1 34359738368 12620444993 34359738368 45515017437 3714993622299443200 21406887140241551 1180591620717411303424 46135434290132047697 ep1015 (@Enclosure.Real.IsNear.recentre' qz466 Bool.false 1696207 34359738368 1 34359738368 1696207 34359738368 1 34359738368 (ep1066 rfl rfl) rfl) (@Enclosure.Real.IsNear.recentre' qz131 Bool.true 12620444993 34359738368 91030034874 7429987244598886400 12620444993 34359738368 45515017437 3714993622299443200 (ep1080 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz466 qz393 1696207 34359738368 1 34359738368 31958034809 34359738368 45515017437 3714993622299443200 54207442349269463 1180591620717411303424 113040737996624031497 ep1015 (@Enclosure.Real.IsNear.recentre' qz466 Bool.false 1696207 34359738368 1 34359738368 1696207 34359738368 1 34359738368 (ep1066 rfl rfl) rfl) (@Enclosure.Real.IsNear.neg qz132 Bool.true 31958034809 34359738368 45515017437 3714993622299443200 (@Enclosure.Real.IsNear.recentre' qz132 Bool.true 31958034809 34359738368 91030034874 7429987244598886400 31958034809 34359738368 45515017437 3714993622299443200 (ep1086 rfl rfl) rfl)) rfl)

noncomputable def ep1088 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz233 4667855963813 5760000000 0 1 54207442349269463 1180591620717411303424 113040737996624031497 ep1015 ep1011

noncomputable def ep1089 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 838324267 19200000 0 1 Bool.false 4667855963813 5760000000 0 1 ep1062

noncomputable def ep1090 := @Enclosure.Complex.IsNear.im_isNear qz223 Bool.true 21406887140241551 1180591620717411303424 46135434290132047697 ep1015 Bool.false 54207442349269463 1180591620717411303424 113040737996624031497 ep1015

noncomputable def ep1091 := nat_lit 45443414373396080554958621

noncomputable def ep1092 := nat_lit 94764793822158889679307437699

noncomputable def ep1093 := nat_lit 99924265804248340340734993963

noncomputable def ep1094 := nat_lit 215353562094295658977719221988661

noncomputable def ep1095 := @Enclosure.Real.IsNear.addLit_ft_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz233) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz232) ep1091 ep1008 ep1092 ep1010 ep1093 ep999 ep1094

noncomputable def ep1096 := nat_lit 1955994559622952459743740363391871488520305582171750400000

noncomputable def ep1097 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz233 838324267 19200000 0 1 54207442349269463 1180591620717411303424 113040737996624031497 ep1015 ep1091

noncomputable def ep1098 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz232 4667855963813 5760000000 0 1 21406887140241551 1180591620717411303424 46135434290132047697 ep1015 ep1093

noncomputable abbrev qz470 := (@ep1065 ep1015 (BSN.cpow_neg_s_sub_mk qz16 83585 1000 17 3 410338673 qz17 rfl EMRow23.d18) ep1087)

noncomputable def ep1099 := ep1006 (@ep1013 ep1001 ep1014 ep998 ep999 ep1000 ep1001 (@ep1016 ep1008 ep1009 ep1010 ep1063 (ep1064 qz470) rfl) (@ep1088 ep999 ep1012 ep1001 ep1089 (ep1090 qz470) rfl) rfl rfl) (@ep1095 ep1001 ep1096 ep1003 ep999 ep1004 ep1001 (@ep1097 ep1008 ep1092 ep1010 ep1063 (ep1090 qz470) rfl) (@ep1098 ep999 ep1094 ep1001 ep1089 (ep1064 qz470) rfl) rfl rfl)

noncomputable def ep1100 := @Enclosure.Real.IsNear.mulLit_tt (Complex.im (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.im (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) ep1003 ep999 ep1004 ep1001 ep1003 ep999 ep1004

noncomputable def ep1101 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223) Bool.true ep998 ep999 ep1000 ep1001 Bool.true ep1003 ep999 ep1004

noncomputable def ep1102 := @ep970 60378446518956665 63050394783186944 39140920487 63050394783186944 (@ep971 1 1835008 (ep972 (@ep973 524288 1 524288 (ep974 (@ep975 1119792356 279948089 40000 0 1 (ep979 rfl) (ep982 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) (Enclosure.Real.IsNear.const Bool.false 2 7) rfl) (@ep983 861 34359738368 (BSN.norm_eq_sqrt_mul_add (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (@ep984 861 34359738368 1376585711 34359738368 861 34359738368 (@ep989 688292425 688293286 17179869184 (@ep995 ep991 ep996 ep993 ep997 ep985 ep986 ep987 ep988 (@ep1002 ep1001 ep990 ep991 ep992 ep993 (@ep1005 ep1001 ep1099) (@ep1005 ep1001 ep1099) rfl) (@ep1100 ep1001 ep994 ep991 ep996 ep993 (@ep1101 ep1001 ep1099) (@ep1101 ep1001 ep1099) rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl

theorem EMRow23.d19 : Enclosure.Real.IsNear (@HAdd.hAdd Real Real Real qz380 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 17))) (@HMul.hMul Real Real Real qz0 qz220 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)))) Bool.false 554150623566349889 567453553048682496 158590942467485 1702360659146047488 := ep968 (ep969 ep1102) rfl rfl

theorem EMRow23.d20 : @Eq Nat (Nat.pow 18 (Nat.succ (Nat.mul 2 3))) 612220032 := @Eq.refl Nat 612220032

noncomputable abbrev qz513 := (@HAdd.hAdd Complex Complex Complex qz515 qz521 (@Nat.cast Complex Complex.instNatCast 3))

noncomputable abbrev qz471 := qz513

noncomputable abbrev qz242 := (@HDiv.hDiv Real Real Real qz269 (@Norm.norm Complex Complex.instNorm qz471) (@HAdd.hAdd Real Real Real qz380 (Complex.re qz400) qz290))

noncomputable abbrev qz472 := (@HPow.hPow Complex Complex Complex qz490 (@Nat.cast Complex Complex.instNatCast 18) (@HSub.hSub Complex Complex Complex qz499 qz507 qz492))

noncomputable abbrev qz243 := qz472

noncomputable def ep1103 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz140 1 18))) (@HMul.hMul Real Real Real qz0 qz242 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 3))) qz243))) 4630708405 154618822656 15760219 154618822656 6923621421612711 7881299347898368 11331043351

noncomputable def ep1104 := nat_lit 1107018191858252359407763456

noncomputable def ep1105 := @Enclosure.Real.IsNear.mulLit_ff (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz140 1 18)) 4427 294912 1 884736 1046015 524288 3481 524288 4630708405 154618822656

noncomputable def ep1106 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (zetaApproximant qz140 1 18)) (Real.sqrt (@HAdd.hAdd Real Real Real qz380 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz140 1 18)) (Complex.re (zetaApproximant qz140 1 18))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz140 1 18)) (Complex.im (zetaApproximant qz140 1 18))))) Bool.false 1046015 524288 3481 524288

noncomputable def ep1107 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz380 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz140 1 18)) (Complex.re (zetaApproximant qz140 1 18))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz140 1 18)) (Complex.im (zetaApproximant qz140 1 18))))) Bool.false 1046015 524288 3481 524288

noncomputable def ep1108 := nat_lit 166054199800806372168628161587067742368157

noncomputable def ep1109 := nat_lit 41716574346395802475134020168476891545600

noncomputable def ep1110 := nat_lit 8763228507338816685707652024928314801644914056432188064210647

noncomputable def ep1111 := nat_lit 330914023671012621488206166347464015760692577818378240000000000

noncomputable def ep1112 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz380 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz140 1 18)) (Complex.re (zetaApproximant qz140 1 18))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz140 1 18)) (Complex.im (zetaApproximant qz140 1 18)))) ep1108 ep1109 ep1110 ep1111 521267 524748

noncomputable def ep1113 := nat_lit 1226865256820840307868129729765564865229706952956201

noncomputable def ep1114 := nat_lit 308539037800458948325080076094762251237275048345600

noncomputable def ep1115 := nat_lit 941842158362496717657877040345926936117483885935222481488979

noncomputable def ep1116 := nat_lit 36768224852334735720911796260829335084521397535375360000000000

noncomputable def ep1117 := nat_lit 321139324890570847219919624405027549038669414489

noncomputable def ep1118 := nat_lit 77134759450114737081270019023690562809318762086400

noncomputable def ep1119 := nat_lit 71662270519086556696689665453743094146889770753796432702459

noncomputable def ep1120 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz140 1 18)) (Complex.re (zetaApproximant qz140 1 18))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz140 1 18)) (Complex.im (zetaApproximant qz140 1 18))) ep1113 ep1114 ep1115 ep1116 ep1117 ep1118 ep1119

noncomputable def ep1121 := nat_lit 82728505917753155372051541586866003940173144454594560000000000

noncomputable def ep1122 := nat_lit 94733040480880381538800585222387818048582840007362320357579692323406419785066724034979287798697164800

noncomputable def ep1123 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (zetaApproximant qz140 1 18)) (Complex.re (zetaApproximant qz140 1 18)) ep715 ep716 ep717 ep718 ep715 ep716 ep717 ep718 ep1113

noncomputable def ep1124 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (zetaApproximant qz140 1 18)) (Complex.im (zetaApproximant qz140 1 18)) 566691560631152197521317 ep835 ep836 ep837 566691560631152197521317 ep835 ep836 ep837 ep1117

noncomputable def ep1125 := @ep1103 31525197391593472 ep1104 64436939536724959 70931694131085312 29022107336911 283726776524341248 (@ep1105 15760219 154618822656 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaStirlingErrorBound 1 2) (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 96 162) qz452) Bool.false 4427 294912 1 884736 (BSN.theta_err_eq 1 2 96 162 EMRow23.d15 EMRow23.d16 rfl) (ep949 rfl)) (ep1106 (BSN.norm_eq_sqrt_mul_add (zetaApproximant qz140 1 18)) (@ep1107 1046015 524288 3481 524288 (@ep1112 262144 (@ep1120 ep1121 ep1122 ep1108 ep1109 ep1110 ep1111 (@ep1123 ep1114 ep1115 ep1116 ep929 ep929 rfl) (@ep1124 ep1118 ep1119 ep1121 ep937 ep937 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl)

noncomputable abbrev qz244 := (@Norm.norm Complex Complex.instNorm qz471)

noncomputable def ep1126 := @Enclosure.Real.IsNear.of_eq (@HMul.hMul Real Real Real qz0 qz242 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 3))) qz243))) (@HMul.hMul Real Real Real qz0 (@HMul.hMul Real Real Real qz0 qz244 qz455) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 3))) qz243))) Bool.false 6923621421612711 7881299347898368 11331043351 31525197391593472 (BSN.zrb_shape_eq qz244 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 3))) qz243)) qz149 3)

noncomputable def ep1127 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz0 qz244 qz455) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 3))) qz243)) 45125569 1835008 1 1835008 153430119 4294967296 475 34359738368

noncomputable def ep1128 := @Enclosure.Real.IsNear.mulLit_ff qz244 qz455 45125569 524288 1 524288 2 7 0 1 45125569 1835008

noncomputable abbrev qz473 := (Complex.re qz513)

noncomputable abbrev qz474 := (Complex.im qz513)

noncomputable abbrev qz245 := (@HAdd.hAdd Real Real Real qz380 (@HMul.hMul Real Real Real qz266 qz473 qz473) (@HMul.hMul Real Real Real qz266 qz474 qz474))

noncomputable abbrev qz246 := qz471

noncomputable def ep1129 := @Enclosure.Real.IsNear.of_eq qz244 (Real.sqrt qz245) Bool.false 45125569 524288 1 524288 (BSN.norm_eq_sqrt_mul_add qz246)

noncomputable def ep1130 := @Enclosure.Real.IsNear.recentre' (Real.sqrt qz245) Bool.false 45125569 524288 1 524288 45125569

noncomputable def ep1131 := @Enclosure.Real.IsNear.sqrt_image qz245 7408078001 1000000 0 1 22562784 22562785 262144

noncomputable abbrev qz247 := (@HMul.hMul Real Real Real qz266 qz473 qz473)

noncomputable abbrev qz248 := (@HMul.hMul Real Real Real qz266 qz474 qz474)

noncomputable def ep1132 := @Enclosure.Real.IsNear.addLit_ff qz247 qz248 49 4 0 1 7395828001 1000000 0 1

noncomputable abbrev qz249 := qz473

noncomputable def ep1133 := @Enclosure.Real.IsNear.mulLit_ff qz249 qz249 7 2 0 1 7 2 0 1 49 4

noncomputable def ep1134 := @Enclosure.Complex.IsNear.of_eq qz246 (Complex.mk qz458 qz149) Bool.false 7 2 0 1 Bool.false 85999 1000 0 1 (BSN.s_add_nat_mk qz149 Bool.false 85999 1000 3 qz150)

noncomputable abbrev qz475 := (ep1134 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7 2) qz149 Bool.false 7 2 0 1 Bool.false 85999 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 7 2) qz151))

noncomputable def ep1135 := @ep1133 0 1 (@Enclosure.Complex.IsNear.re_isNear qz246 Bool.false 7 2 0 1 Bool.false 85999 1000 0 1 qz475)

noncomputable def ep1136 := ep1135 (@Enclosure.Complex.IsNear.re_isNear qz246 Bool.false 7 2 0 1 Bool.false 85999 1000 0 1 qz475)

noncomputable abbrev qz250 := qz474

noncomputable def ep1137 := @Enclosure.Real.IsNear.mulLit_ff qz250 qz250 85999 1000 0 1 85999 1000 0 1 7395828001 1000000

noncomputable def ep1138 := @ep1137 0 1 (@Enclosure.Complex.IsNear.im_isNear qz246 Bool.false 7 2 0 1 Bool.false 85999 1000 0 1 qz475)

noncomputable def ep1139 := ep1138 (@Enclosure.Complex.IsNear.im_isNear qz246 Bool.false 7 2 0 1 Bool.false 85999 1000 0 1 qz475)

noncomputable def ep1140 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 3))) qz243)) (Real.sqrt (@HAdd.hAdd Real Real Real qz380 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 3))) qz243)) (Complex.re (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 3))) qz243))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 3))) qz243)) (Complex.im (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 3))) qz243))))) Bool.false 153430119 4294967296

noncomputable def ep1141 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz380 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 3))) qz243)) (Complex.re (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 3))) qz243))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 3))) qz243)) (Complex.im (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 3))) qz243))))) Bool.false 2454881904 68719476736

noncomputable def ep1142 := nat_lit 1475318844091517328634178178072348059212784410969826535344118121

noncomputable def ep1143 := nat_lit 1156070631091827503657211635254091060470024765440000000000000000000

noncomputable def ep1144 := nat_lit 46837943908564069806406220662159970528138517176614217952873360319749166879

noncomputable def ep1145 := nat_lit 47443527613998080301993439263485626884203968489907501924352000000000000000000000000

noncomputable def ep1146 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz380 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 3))) qz243)) (Complex.re (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 3))) qz243))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 3))) qz243)) (Complex.im (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 3))) qz243)))) ep1142 ep1143 ep1144 ep1145

noncomputable def ep1147 := nat_lit 2626483907542908307541381525158414273599842667112462947168342721

noncomputable def ep1148 := nat_lit 11560706310918275036572116352540910604700247654400000000000000000000

noncomputable def ep1149 := nat_lit 16598899206512182150271190674350034371582721488843621940867636416568300779

noncomputable def ep1150 := nat_lit 94887055227996160603986878526971253768407936979815003848704000000000000000000000000

noncomputable def ep1151 := nat_lit 1347411614819140553200044472840562924280889049176200267363648721

noncomputable def ep1152 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 3))) qz243)) (Complex.re (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 3))) qz243))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 3))) qz243)) (Complex.im (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 3))) qz243))) ep1147 ep1148 ep1149 ep1150 ep1151

noncomputable def ep1153 := nat_lit 1284522923435363892952457372504545622744471961600000000000000000000

noncomputable def ep1154 := nat_lit 77076988610615957462541250649969906684694312864384813964879084222930032979

noncomputable def ep1155 := nat_lit 18950808746117176737921286492297758775826082653976220965300677130808096679607801079251483925807836105629761536000000000000000000000

noncomputable def ep1156 := nat_lit 51249233238585221857061484574561

noncomputable def ep1157 := nat_lit 3400103867666144553861120000000000

noncomputable def ep1158 := nat_lit 1787518463053413126348671306135923

noncomputable def ep1159 := nat_lit 308037425044419173420265111552000000000000

noncomputable def ep1160 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 3))) qz243)) (Complex.re (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 3))) qz243)) ep1156 ep1157 ep1158 ep1159 ep1156 ep1157 ep1158

noncomputable def ep1161 := nat_lit 36707105781022024798804499183689

noncomputable def ep1162 := nat_lit 1133367955888714851287040000000000

noncomputable def ep1163 := nat_lit 3862886613170534359598251700035273

noncomputable def ep1164 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 3))) qz243) Bool.true ep1156 ep1157 ep1158 ep1159 Bool.true ep1161 ep1162 ep1163

noncomputable def ep1165 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 3))) qz243 Bool.true ep1156 ep1157 ep1158 ep1159 Bool.true ep1161 ep1162 ep1163 ep1159

noncomputable def ep1166 := nat_lit 1309057706644914789335961433

noncomputable def ep1167 := nat_lit 755578637259143234191360000000

noncomputable def ep1168 := nat_lit 131944902052751975498106749681

noncomputable def ep1169 := nat_lit 205358283362946115613510074368000000000

noncomputable def ep1170 := nat_lit 45358473558683105305049658126061

noncomputable def ep1171 := nat_lit 1589601109974285163101511181614423

noncomputable abbrev qz251 := (Complex.re qz472)

noncomputable abbrev qz252 := (Complex.im qz472)

noncomputable def ep1172 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 3)))) qz251) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 3)))) qz252) ep1166 ep1167 ep1168 ep1169 ep1170 ep1157 ep1171

noncomputable def ep1173 := nat_lit 38722825810986209790375446589225392157417137358461992960000000

noncomputable def ep1174 := nat_lit 427829757006137740861479321600

noncomputable def ep1175 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 3)))) qz251 22186234003 480000000 0 1 177009451870187433 4722366482869645213696 5947151825537877227 ep1174 ep1166

noncomputable def ep1176 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 3)))) 22186234003 480000000 0 1 0 1 0 1 22186234003

noncomputable def ep1177 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 66558702009 2000000 0 1 22186234003 480000000 0

noncomputable abbrev qz476 := (@HAdd.hAdd Complex Complex Complex qz489 qz506 qz493)

noncomputable abbrev qz253 := qz476

noncomputable def ep1178 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 3)) (@HMul.hMul Complex Complex Complex qz72 (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 2)) qz253) Bool.true 66558702009 2000000 0 1 Bool.true 635539318007999 1000000000 0 1

noncomputable abbrev qz254 := (Complex.re qz476)

noncomputable abbrev qz255 := (Complex.im qz476)

noncomputable def ep1179 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 2))) qz254) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 2))) qz255) 7395078001 400000 0 1 7395828001 500000 0 1

noncomputable def ep1180 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 2))) qz254 7395078001 1000000 0 1 5 2 0 1 7395078001 400000

noncomputable abbrev qz477 := (@HAdd.hAdd Complex Complex Complex qz489 qz506 (@Nat.cast Complex Complex.instNatCast 1))

noncomputable abbrev qz256 := qz477

noncomputable def ep1181 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 2)) (@HMul.hMul Complex Complex Complex qz72 (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 1)) qz256) Bool.true 7395078001 1000000 0 1 Bool.false 85999 500 0 1

noncomputable abbrev qz257 := (Complex.re qz477)

noncomputable abbrev qz258 := (Complex.im qz477)

noncomputable def ep1182 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 1))) qz257) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 1))) qz258) 3 4 0 1 7395828001 1000000 0 1

noncomputable def ep1183 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 1))) qz257 1 2 0 1 3 2 0 1 3 4

noncomputable def ep1184 := @ep1183 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 85999 1000 0 1 ep891)

noncomputable def ep1185 := @Enclosure.Complex.IsNear.of_eq qz256 (Complex.mk qz462 qz149) Bool.false 3 2 0 1 Bool.false 85999 1000 0 1 (BSN.s_add_nat_mk qz149 Bool.false 85999 1000 1 qz150)

noncomputable abbrev qz478 := (ep1185 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 3 2) qz149 Bool.false 3 2 0 1 Bool.false 85999 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 3 2) qz151))

noncomputable def ep1186 := ep1184 (@Enclosure.Complex.IsNear.re_isNear qz256 Bool.false 3 2 0 1 Bool.false 85999 1000 0 1 qz478)

noncomputable def ep1187 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 1))) qz258 85999 1000 0 1 85999 1000 0 1 7395828001 1000000

noncomputable def ep1188 := @ep1187 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 85999 1000 0 1 ep891)

noncomputable def ep1189 := ep1188 (@Enclosure.Complex.IsNear.im_isNear qz256 Bool.false 3 2 0 1 Bool.false 85999 1000 0 1 qz478)

noncomputable def ep1190 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 1)) qz256 Bool.true 7395078001 1000000 0 1 Bool.false 85999 500 0 1 (@ep1182 29580312004 7395078001 1000000 0 1 (ep1186 rfl) (ep1189 rfl) rfl rfl)

noncomputable def ep1191 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 1))) qz258) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 1))) qz257) 85999 2000 0 1 257997 2000 0 1

noncomputable def ep1192 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 1))) qz258 1 2 0 1 85999 1000 0 1 85999 2000

noncomputable def ep1193 := @ep1192 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 85999 1000 0 1 ep891)

noncomputable def ep1194 := ep1193 (@Enclosure.Complex.IsNear.im_isNear qz256 Bool.false 3 2 0 1 Bool.false 85999 1000 0 1 qz478)

noncomputable def ep1195 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 1))) qz257 85999 1000 0 1 3 2 0 1 257997 2000

noncomputable def ep1196 := @ep1195 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 85999 1000 0 1 ep891)

noncomputable def ep1197 := ep1196 (@Enclosure.Complex.IsNear.re_isNear qz256 Bool.false 3 2 0 1 Bool.false 85999 1000 0 1 qz478)

noncomputable abbrev qz259 := (ep1181 (BSN.ascPochhammer_succ_eval_c 1 2 qz400 rfl) (ep1190 (@ep1191 687992000 85999 500 0 1 (ep1194 rfl) (ep1197 rfl) rfl rfl)))

noncomputable def ep1198 := @ep1180 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 7395078001 1000000 0 1 Bool.false 85999 500 0 1 qz259)

noncomputable def ep1199 := @Enclosure.Complex.IsNear.of_eq qz253 (Complex.mk qz464 qz149) Bool.false 5 2 0 1 Bool.false 85999 1000 0 1 (BSN.s_add_nat_mk qz149 Bool.false 85999 1000 2 qz150)

noncomputable abbrev qz479 := (ep1199 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 5 2) qz149 Bool.false 5 2 0 1 Bool.false 85999 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 5 2) qz151))

noncomputable def ep1200 := ep1198 (@Enclosure.Complex.IsNear.re_isNear qz253 Bool.false 5 2 0 1 Bool.false 85999 1000 0 1 qz479)

noncomputable def ep1201 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 2))) qz255 85999 500 0 1 85999 1000 0 1 7395828001 500000

noncomputable def ep1202 := @ep1201 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 7395078001 1000000 0 1 Bool.false 85999 500 0 1 qz259)

noncomputable def ep1203 := ep1202 (@Enclosure.Complex.IsNear.im_isNear qz253 Bool.false 5 2 0 1 Bool.false 85999 1000 0 1 qz479)

noncomputable def ep1204 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 2)) qz253 Bool.true 66558702009 2000000 0 1 Bool.true 635539318007999 1000000000 0 1 (@ep1179 6655870200900000 66558702009 2000000 0 1 (ep1200 rfl) (ep1203 rfl) rfl rfl)

noncomputable def ep1205 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 2))) qz255) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 2))) qz254) 635969313007999 1000000000 0 1 85999 200 0 1

noncomputable def ep1206 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 2))) qz255 7395078001 1000000 0 1 85999 1000 0 1 635969313007999 1000000000

noncomputable def ep1207 := @ep1206 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 7395078001 1000000 0 1 Bool.false 85999 500 0 1 qz259)

noncomputable def ep1208 := ep1207 (@Enclosure.Complex.IsNear.im_isNear qz253 Bool.false 5 2 0 1 Bool.false 85999 1000 0 1 qz479)

noncomputable def ep1209 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 2))) qz254 85999 500 0 1 5 2 0 1 85999 200

noncomputable def ep1210 := @ep1209 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 7395078001 1000000 0 1 Bool.false 85999 500 0 1 qz259)

noncomputable def ep1211 := ep1210 (@Enclosure.Complex.IsNear.re_isNear qz253 Bool.false 5 2 0 1 Bool.false 85999 1000 0 1 qz479)

noncomputable abbrev qz260 := (ep1178 (BSN.ascPochhammer_succ_eval_c 2 3 qz400 rfl) (ep1204 (@ep1205 127107863601599800 635539318007999 1000000000 0 1 (ep1208 rfl) (ep1211 rfl) rfl rfl)))

noncomputable def ep1212 := @ep1177 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1019) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 66558702009 2000000 0 1 Bool.true 635539318007999 1000000000 0 1 qz260)

noncomputable def ep1213 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 635539318007999 1000000000 0 1 0 1 0

noncomputable def ep1214 := @ep1213 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1019) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 66558702009 2000000 0 1 Bool.true 635539318007999 1000000000 0 1 qz260)

noncomputable def ep1215 := @Enclosure.Real.IsNear.addLit_ft_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 3)))) 635539318007999 720000000000 0 1 0 1 0 1 635539318007999

noncomputable def ep1216 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 635539318007999 1000000000 0 1 635539318007999 720000000000 0

noncomputable def ep1217 := @ep1216 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1019) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 66558702009 2000000 0 1 Bool.true 635539318007999 1000000000 0 1 qz260)

noncomputable def ep1218 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 66558702009 2000000 0 1 0 1 0

noncomputable def ep1219 := @ep1218 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1019) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 66558702009 2000000 0 1 Bool.true 635539318007999 1000000000 0 1 qz260)

noncomputable def ep1220 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.false 22186234003 480000000 0 1 Bool.false 635539318007999 720000000000 0 1 (@ep1176 22186234003 480000000 0 1 (ep1212 rfl) (ep1214 rfl) rfl rfl) (@ep1215 635539318007999 720000000000 0 1 (ep1217 rfl) (ep1219 rfl) rfl rfl)

noncomputable def ep1221 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 22186234003 480000000 0 1 Bool.false 635539318007999 720000000000 0 1 ep1220

noncomputable def ep1222 := @Enclosure.Complex.IsNear.re_isNear qz243 Bool.true 177009451870187433 4722366482869645213696 5947151825537877227 ep1174 Bool.false 71370051031385939 4722366482869645213696 2501184529317001577 ep1174

noncomputable abbrev qz480 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 612220032)))

noncomputable def ep1223 := @Enclosure.Complex.IsNear.of_eq qz243 (Complex.mk (@HMul.hMul Real Real Real qz0 qz480 qz213) (@HMul.hMul Real Real Real qz0 qz480 qz444)) Bool.true 177009451870187433 4722366482869645213696 5947151825537877227 ep1174 Bool.false 71370051031385939 4722366482869645213696 2501184529317001577

noncomputable abbrev qz481 := (Real.sqrt (@Nat.cast Real Real.instNatCast 612220032))

noncomputable abbrev qz482 := (@Nat.cast Real Real.instNatCast 612220032)

noncomputable def ep1224 := @Enclosure.Real.IsNear.inv_image qz481 1700331543922591 68719476736 1 68719476736 1388660 1388661 34359738368 (@Enclosure.Real.IsNear.of_eq qz481 (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz482 qz18)) Bool.false 1700331543922591 68719476736 1 68719476736 (BSN.sqrt_natCast_div_one 612220032) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz482 qz18)) Bool.false 1700331543922591 68719476736 1 68719476736 1700331543922591 68719476736 1 68719476736 (BSN.sqrt_enclosure 612220032 1 850165771961295 850165771961296 34359738368 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep1225 := nat_lit 2717894250000000000000000

noncomputable def ep1226 := nat_lit 3578106927507003823049670656

noncomputable def ep1227 := nat_lit 1237940039285380274899124224

noncomputable def ep1228 := nat_lit 8697261600000000000000000

noncomputable def ep1229 := BSN.log_dyadic_bound 2 34 4 3 162204463680 34359738368 8697261600 187476416 960 4046994289 36 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 2) (BSN.artanhQ 34) 0 3 187476416 162204463680 960 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep1230 := @Enclosure.Real.IsNear.mulLit_ff qz149 qz215 85999 1000 0 1 3254269292944631 1125899906842624 312510871577 2717894250000000000000 279863904923945321369 1125899906842624000 26875622444750423 ep1225 qz151 (BSN.isNear_log_sfrac 18 1 3254269292944631 1125899906842624 312510871577 2717894250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz446) Bool.false ep1226 ep1227 1000034789046400 ep1228 3254269292944631 1125899906842624 312510871577 2717894250000000000000 (BSN.log_rat_reduce_isNear 18 1 4 36 32 4046994289 34359738368 24973259072661432 36028797018963968 8697261600 1000000000000000 rfl rfl rfl rfl (ep1229 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1231 := nat_lit 474454351386938794502520832

noncomputable def ep1232 := nat_lit 5579207659096530640943621942783067711515110001748613666853928245527115843003071039692176786340588252125779746507201

noncomputable def ep1233 := nat_lit 6205815975932130475933948815772619174300058935098307850201856211168701179010810671297746935144374213427043908473323520

noncomputable def ep1234 := nat_lit 71653426607005711026048701158851855312871744795704642499348296969112718829491522392382750027354089472019024321

noncomputable def ep1235 := nat_lit 16737479670436377911408813730946885430834704261756249591276786039987409303571554136031745593521710048198395201472961

noncomputable def ep1236 := nat_lit 279261718916945871417027696709767862843502652079423853259083529502591553055486480208398612081496839604216975881299558400

noncomputable def ep1237 := BSN.cos_dyadic_bound_f 53939214852441 140737488355328 3 2 68719476736 17411510040 ep1232 ep1233 ep1234 ep1235 ep1236 ep1234 63733883073 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 53939214852441) (BSN.cosEvenQ 140737488355328) 0 2 ep1232 ep1233 ep1234 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 53939214852441) (BSN.cosOddQ 140737488355328) 0 2 ep1235 ep1236 ep1234 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz483 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 2135192145721) (@Nat.cast Real Real.instNatCast 8589934592))

noncomputable def ep1238 := @Enclosure.Real.IsNear.cos_image qz216 qz483 Bool.false 2135192145721 8589934592 85 8589934592 Bool.true 63733883073 68719476736 1 8697261600 (@Enclosure.Real.IsNear.recentre' qz216 Bool.false 279863904923945321369 1125899906842624000 26875622444750423 ep1225 2135192145721 8589934592 85 8589934592 (ep1230 rfl) rfl) (Enclosure.sfrac_false_div 2135192145721 8589934592) (BSN.cos_reduce2 qz483 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep1231) (@Nat.cast Real Real.instNatCast ep1227)) 226375608064910080 72057594037927936 Bool.false 63733883073 68719476736 39 1000000000000000 17394523200 8697261600 (BSN.sin_reduce_arg_pos_rat_q2 2135192145721 8589934592 226375608064910080 72057594037927936 39 ep1231 ep1227 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 63733883073 68719476736 ep1231 ep1227 53939214852441 140737488355328 17411510040 17394523200 (ep1237 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1239 := nat_lit 10042516463632469549129698658048594799242947705751668036623071363311233227230464278228004309213036970554825928493505

noncomputable def ep1240 := nat_lit 55852343783389174283405539341953572568700530415884770651816705900518310611097296041679722416299367920843395176259911680

noncomputable def ep1241 := nat_lit 26301712823013389857521835263658729190251499341762794669353521292381946555487396790037090285391243016260637020015041

noncomputable def ep1242 := nat_lit 1023959636028801528529101554602482163759509724291220795283306274842835694536783760764128244298821745215462244898098380800

noncomputable def ep1243 := BSN.sin_dyadic_bound_f 53939214852441 140737488355328 3 2 68719476736 17411510040 ep1239 ep1240 ep1234 ep1241 ep1242 ep1234 25697444059 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 53939214852441) (BSN.sinEvenQ 140737488355328) 0 2 ep1239 ep1240 ep1234 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 53939214852441) (BSN.sinOddQ 140737488355328) 0 2 ep1241 ep1242 ep1234 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1244 := @Enclosure.Real.IsNear.sin_image qz216 qz483 Bool.false 2135192145721 8589934592 85 8589934592 Bool.true 25697444059 68719476736 1 8697261600 (@Enclosure.Real.IsNear.recentre' qz216 Bool.false 279863904923945321369 1125899906842624000 26875622444750423 ep1225 2135192145721 8589934592 85 8589934592 (ep1230 rfl) rfl) (Enclosure.sfrac_false_div 2135192145721 8589934592) (BSN.sin_reduce2 qz483 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep1231) (@Nat.cast Real Real.instNatCast ep1227)) 226375608064910080 72057594037927936 Bool.false 25697444059 68719476736 39 1000000000000000 17394523200 8697261600 (BSN.sin_reduce_arg_pos_rat_q2 2135192145721 8589934592 226375608064910080 72057594037927936 39 ep1231 ep1227 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 25697444059 68719476736 ep1231 ep1227 53939214852441 140737488355328 17411510040 17394523200 (ep1243 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1245 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz480 qz213) (@HMul.hMul Real Real Real qz0 qz480 qz444) Bool.true 177009451870187433 4722366482869645213696 5947151825537877227 ep1174 Bool.false 71370051031385939 4722366482869645213696 2501184529317001577 ep1174 (@Enclosure.Real.IsNear.mulLit_ft qz480 qz213 2777321 68719476736 1 68719476736 63733883073 68719476736 23370536581 2334653383547289600 177009451870187433 4722366482869645213696 5947151825537877227 ep1174 (@Enclosure.Real.IsNear.recentre' qz480 Bool.false 2777321 68719476736 1 68719476736 2777321 68719476736 1 68719476736 (ep1224 rfl rfl) rfl) (@Enclosure.Real.IsNear.recentre' qz213 Bool.true 63733883073 68719476736 747857170592 74708908273513267200 63733883073 68719476736 23370536581 2334653383547289600 (ep1238 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz480 qz444 2777321 68719476736 1 68719476736 25697444059 68719476736 23370536581 2334653383547289600 71370051031385939 4722366482869645213696 2501184529317001577 ep1174 (@Enclosure.Real.IsNear.recentre' qz480 Bool.false 2777321 68719476736 1 68719476736 2777321 68719476736 1 68719476736 (ep1224 rfl rfl) rfl) (@Enclosure.Real.IsNear.neg qz214 Bool.true 25697444059 68719476736 23370536581 2334653383547289600 (@Enclosure.Real.IsNear.recentre' qz214 Bool.true 25697444059 68719476736 747857170592 74708908273513267200 25697444059 68719476736 23370536581 2334653383547289600 (ep1244 rfl rfl) rfl)) rfl)

noncomputable def ep1246 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 3)))) qz252 635539318007999 720000000000 0 1 71370051031385939 4722366482869645213696 2501184529317001577 ep1174 ep1170

noncomputable def ep1247 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 22186234003 480000000 0 1 Bool.false 635539318007999 720000000000 0 1 ep1220

noncomputable def ep1248 := @Enclosure.Complex.IsNear.im_isNear qz243 Bool.true 177009451870187433 4722366482869645213696 5947151825537877227 ep1174 Bool.false 71370051031385939 4722366482869645213696 2501184529317001577 ep1174

noncomputable def ep1249 := nat_lit 1583432652988379940057883817

noncomputable def ep1250 := nat_lit 2266735911777429702574080000000

noncomputable def ep1251 := nat_lit 55491865252110410753642022731

noncomputable def ep1252 := nat_lit 37498822107516214768833441092189

noncomputable def ep1253 := nat_lit 3779648815292368743467788665938773

noncomputable def ep1254 := @Enclosure.Real.IsNear.addLit_ft_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 3)))) qz252) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 3)))) qz251) ep1249 ep1250 ep1251 ep1169 ep1252 ep1162 ep1253

noncomputable def ep1255 := nat_lit 83205314891255520223077953449578357508811269422050181120000000

noncomputable def ep1256 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 3)))) qz252 22186234003 480000000 0 1 71370051031385939 4722366482869645213696 2501184529317001577 ep1174 ep1249

noncomputable def ep1257 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 3)))) qz251 635539318007999 720000000000 0 1 177009451870187433 4722366482869645213696 5947151825537877227 ep1174 ep1252

noncomputable abbrev qz484 := (@ep1223 ep1174 (BSN.cpow_neg_s_sub_mk qz149 85999 1000 18 3 612220032 qz150 rfl EMRow23.d20) ep1245)

noncomputable def ep1258 := ep1165 (@ep1172 ep1159 ep1173 ep1156 ep1157 ep1158 ep1159 (@ep1175 ep1167 ep1168 ep1169 ep1221 (ep1222 qz484) rfl) (@ep1246 ep1157 ep1171 ep1159 ep1247 (ep1248 qz484) rfl) rfl rfl) (@ep1254 ep1159 ep1255 ep1161 ep1162 ep1163 ep1159 (@ep1256 ep1250 ep1251 ep1169 ep1221 (ep1248 qz484) rfl) (@ep1257 ep1162 ep1253 ep1159 ep1247 (ep1222 qz484) rfl) rfl rfl)

noncomputable def ep1259 := @Enclosure.Real.IsNear.mulLit_tt (Complex.im (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 3))) qz243)) (Complex.im (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 3))) qz243)) ep1161 ep1162 ep1163 ep1159 ep1161 ep1162 ep1163

noncomputable def ep1260 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 3))) qz243) Bool.true ep1156 ep1157 ep1158 ep1159 Bool.true ep1161 ep1162 ep1163

noncomputable def ep1261 := @ep1127 6923621421612711 7881299347898368 11331043351 31525197391593472 (@ep1128 1 1835008 (ep1129 (@ep1130 524288 1 524288 (ep1131 (@ep1132 29632312004 7408078001 1000000 0 1 (ep1136 rfl) (ep1139 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) (Enclosure.Real.IsNear.const Bool.false 2 7) rfl) (@ep1140 475 34359738368 (BSN.norm_eq_sqrt_mul_add (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 3))) qz243)) (@ep1141 950 68719476736 153430119 4294967296 475 34359738368 (@ep1146 1227440477 1227441427 34359738368 (@ep1152 ep1153 ep1154 ep1150 ep1155 ep1142 ep1143 ep1144 ep1145 (@ep1160 ep1159 ep1147 ep1148 ep1149 ep1150 (@ep1164 ep1159 ep1258) (@ep1164 ep1159 ep1258) rfl) (@ep1259 ep1159 ep1151 ep1153 ep1154 ep1150 (@ep1260 ep1159 ep1258) (@ep1260 ep1159 ep1258) rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl

theorem EMRow23.d21 : Enclosure.Real.IsNear (@HAdd.hAdd Real Real Real qz380 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz140 1 18))) (@HMul.hMul Real Real Real qz0 qz242 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 3))) qz243)))) Bool.false 64436939536724959 70931694131085312 29022107336911 283726776524341248 := ep1125 (ep1126 ep1261) rfl rfl

noncomputable def EMRow23.d22 := fun (I J : @NonemptyInterval Real Real.instLE) => @LE.le Real Real.instLE (@Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE I)) (@Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE J))

noncomputable abbrev qz485 := (EMRow23.d3 qz494 qz508 (@Enclosure.dec_le_dec qz494 qz508 83585 1000 85999 1000 (@Eq.refl Real qz494) (@Eq.refl Real qz508) rfl rfl rfl) 17 18 1 1)

noncomputable abbrev qz261 := qz485

noncomputable def ep1262 := @Zeta.Certificates.ZIntervalEM.Certificate.mk qz261 (@Enclosure.dec_nonneg qz16 83585 1000 qz17) (@Enclosure.pos_of_ble 1 rfl) (@Enclosure.pos_of_ble 17 rfl)

noncomputable abbrev qz262 := (Zeta.Certificates.ZIntervalEM.fstVal qz485)

noncomputable def ep1263 := @Enclosure.Real.IsNear.neg_val qz262 ep282 ep283

noncomputable def ep1264 := @Enclosure.Real.IsNear.of_eq qz262 (hardyZApproximantEM 1 17 qz16) Bool.true

noncomputable abbrev qz263 := (Zeta.Certificates.ZIntervalEM.sndVal qz485)

noncomputable def ep1265 := BSN.mul_neg_of_neg_pos_r qz262 qz263 (@ep1263 ep284 ep285 (@ep1264 ep282 ep283 ep284 ep285 (@Eq.refl Real (hardyZApproximantEM 1 17 qz16)) EMRow23.d10) rfl rfl rfl)

noncomputable def ep1266 := @Enclosure.Real.IsNear.pos_val qz263 ep698 ep699

noncomputable def ep1267 := @Enclosure.Real.IsNear.of_eq qz263 (hardyZApproximantEM 1 18 qz149) Bool.false

noncomputable def ep1268 := BSN.gt_trans_le (@Norm.norm Real Real.norm qz262) (BSN.hardyZErrorBoundStrong 1 17 qz16)

noncomputable def ep1269 := @Enclosure.norm_gt_of_isNear qz262 (BSN.hardyZErrorBoundStrong 1 17 qz16) Bool.true

noncomputable def ep1270 := @Enclosure.Real.IsNear.of_eq (BSN.hardyZErrorBoundStrong 1 17 qz16) (@HAdd.hAdd Real Real Real qz380 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 17))) (@HMul.hMul Real Real Real qz0 qz220 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)))) Bool.false 554150623566349889 567453553048682496 158590942467485 1702360659146047488 (@Eq.refl Real (@HAdd.hAdd Real Real Real qz380 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 17))) (@HMul.hMul Real Real Real qz0 qz220 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)))))

noncomputable def ep1271 := BSN.gt_trans_le (@Norm.norm Real Real.norm qz263) (BSN.hardyZErrorBoundStrong 1 18 qz149)

noncomputable def ep1272 := @Enclosure.norm_gt_of_isNear qz263 (BSN.hardyZErrorBoundStrong 1 18 qz149) Bool.false

noncomputable def ep1273 := @Enclosure.Real.IsNear.of_eq (BSN.hardyZErrorBoundStrong 1 18 qz149) (@HAdd.hAdd Real Real Real qz380 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz140 1 18))) (@HMul.hMul Real Real Real qz0 qz242 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 3))) qz243)))) Bool.false 64436939536724959 70931694131085312 29022107336911 283726776524341248 (@Eq.refl Real (@HAdd.hAdd Real Real Real qz380 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz140 1 18))) (@HMul.hMul Real Real Real qz0 qz242 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 3))) qz243)))))

noncomputable def ep1274 := @List.cons EMRow23.d0 (@PSigma.mk Zeta.Certificates.ZIntervalEM Zeta.Certificates.ZIntervalEM.Certificate qz261 (ep1262 (@Enclosure.pos_of_ble 1 rfl) (@Enclosure.pos_of_ble 18 rfl) (ep1265 (@ep1266 ep700 ep701 (@ep1267 ep698 ep699 ep700 ep701 (@Eq.refl Real (hardyZApproximantEM 1 18 qz149)) EMRow23.d14) rfl rfl rfl)) (ep1268 (hardyZErrorBoundEM 1 17 qz16) (BSN.hardyZErrorBoundEM_le_strong 1 17 qz16 rfl) (@ep1269 Bool.false ep282 ep283 ep284 ep285 554150623566349889 567453553048682496 158590942467485 1702360659146047488 (@ep1264 ep282 ep283 ep284 ep285 (@Eq.refl Real (hardyZApproximantEM 1 17 qz16)) EMRow23.d10) (ep1270 EMRow23.d19) rfl rfl rfl rfl rfl)) (ep1271 (hardyZErrorBoundEM 1 18 qz149) (BSN.hardyZErrorBoundEM_le_strong 1 18 qz149 rfl) (@ep1272 Bool.false ep698 ep699 ep700 ep701 64436939536724959 70931694131085312 29022107336911 283726776524341248 (@ep1267 ep698 ep699 ep700 ep701 (@Eq.refl Real (hardyZApproximantEM 1 18 qz149)) EMRow23.d14) (ep1273 EMRow23.d21) rfl rfl rfl rfl rfl)))) (@List.nil EMRow23.d0)

noncomputable abbrev qz486 := (@Enclosure.dec_le_dec qz494 qz508 83585 1000 85999 1000 (@Eq.refl Real qz494) (@Eq.refl Real qz508) rfl rfl rfl)

noncomputable abbrev qz264 := (Zeta.Certificates.CertifiedZeroIntervals.intervals (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedEM ep1274 (@List.IsChain.singleton EMRow23.d1 EMRow23.d22 (EMRow23.d2 qz279 qz402 qz486))))

noncomputable abbrev qz487 := (@NonemptyInterval Real Real.instLE)

noncomputable def ep1275 := And (@Eq (Option Real) (@Option.map qz487 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz487 qz264)) (@Option.some Real qz16))

noncomputable def ep1276 := ep1275 (@Eq (Option Real) (@Option.map qz487 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz487 qz264)) (@Option.some Real qz149))

noncomputable def ep1277 := @And.intro (@Eq Nat (@List.length qz487 qz264) 1) ep1276

noncomputable def ep1278 := @And.intro (@Eq (Option Real) (@Option.map qz487 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz487 qz264)) (@Option.some Real qz16))

noncomputable def ep1279 := @ep1278 (@Eq (Option Real) (@Option.map qz487 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz487 qz264)) (@Option.some Real qz149))

noncomputable abbrev qz265 := (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedEM ep1274 (@List.IsChain.singleton EMRow23.d1 EMRow23.d22 (EMRow23.d2 qz279 qz402 qz486)))

theorem EMRow23.d23 : Zeta.Certificates.BatchSpec 1 83585 1000 85999 1000 := @Exists.intro Zeta.Certificates.CertifiedZeroIntervals (fun (C : Zeta.Certificates.CertifiedZeroIntervals) => And (@Eq Nat (@List.length qz487 (Zeta.Certificates.CertifiedZeroIntervals.intervals C)) 1) (And (@Eq (Option Real) (@Option.map qz487 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz487 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz16)) (@Eq (Option Real) (@Option.map qz487 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz487 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz149)))) qz265 (ep1277 (@Eq.refl Nat 1) (ep1279 (@Eq.refl (Option Real) (@Option.some Real qz16)) (@Eq.refl (Option Real) (@Option.some Real qz149))))

theorem solution : Zeta.Certificates.BatchSpec 1 83585 1000 85999 1000 := EMRow23.d23
#print axioms solution
#check solution
