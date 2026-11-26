-- Prove2me | solution 1 for RHHeight1000.em_main_0017_0017
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-20T08:12:39.511184+00:00
-- url     : https://prove2.me/submissions/4eddb572-8d2d-4925-818c-d407163bce6b

import Definitions.Def_RHT1000_Support_20261118_S005
/- Copyright (c) 2026 Salvatore Mercuri, Bhavik Mehta.
Apache 2.0 license; see the source project LICENSE. -/
set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable def EMRow17.d0 := @PSigma Zeta.Certificates.ZIntervalEM fun (I : Zeta.Certificates.ZIntervalEM) => Zeta.Certificates.ZIntervalEM.Certificate I

noncomputable def EMRow17.d1 := @NonemptyInterval Real Real.instLE

noncomputable def EMRow17.d2 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @NonemptyInterval.mk Real Real.instLE (@Prod.mk Real Real a b) h

noncomputable def EMRow17.d3 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) (fc sc fb sb : Nat) => Zeta.Certificates.ZIntervalEM.mk (EMRow17.d2 a b h) fc sc fb sb

noncomputable def ep0 := nat_lit 26986075409044028275299783

noncomputable def ep1 := nat_lit 4294967296000000000000000

noncomputable def ep2 := nat_lit 26986075409044045455168967

noncomputable abbrev qz263 := (@instHMul Real Real.instMul)

noncomputable abbrev qz0 := qz263

noncomputable abbrev qz1 := (Enclosure.sfrac Bool.false 2 1)

noncomputable abbrev qz264 := (@HMul.hMul Real Real Real qz0 qz1 Real.pi)

noncomputable def ep3 := @BSN.isNear_log_image_fff qz264 884279719003555 140737488355328 1 500000000000000 ep0 ep1 ep2 ep1 4138529546116343 2251799813685248 62500000019157 9578500000000000000 4138529546116343 2251799813685248 62500000019157 9578500000000000000 481788 262144

noncomputable abbrev qz265 := (@Enclosure.Real.IsNear.mulLit_ff qz1 Real.pi 2 1 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 140737488355328 1 500000000000000 (Enclosure.Real.IsNear.const Bool.false 2 1) BSN.pi_near_15 rfl)

noncomputable def ep4 := @ep3 2 262144 qz265 rfl rfl rfl rfl

noncomputable def ep5 := nat_lit 53972150818088056550599566

noncomputable def ep6 := nat_lit 34359738368000000000000000

noncomputable def ep7 := nat_lit 9806206225044028275299783

noncomputable def ep8 := nat_lit 44165944593044028275299783

noncomputable def ep9 := nat_lit 13681445815609410487519367394620474863599256634174726093703677122907123617368241606644861540940610176751640793056574796245399519365549113997355475306157239709119582688278313060810592403844863400465080549957745

noncomputable def ep10 := nat_lit 231714499556395493334623298703961145503103241611736774613091488581016477543539392410113701224645713379230392133956226737605624599560350113120270717249177907454870984269546186598262646369758174842349131395304

noncomputable def ep11 := nat_lit 8978369550011295664474073352761810093897501552430546263638635096022803738134167562509900960712119243631997923545019968443113540909076206607473711060286601587364321108377403290080403445693385008949995305

noncomputable def ep12 := BSN.log_dyadic_bound ep7 ep8 5 4 ep9 524288 153256 ep10 ep11 236759 ep5 ep6 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP ep7) (BSN.artanhQ ep8) 0 4 ep10 ep9 ep11 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz266 := (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))

noncomputable abbrev qz2 := qz266

noncomputable def ep13 := ep4 rfl rfl rfl rfl (BSN.isNear_log_sfrac ep0 ep1 4138529546116343 2251799813685248 62500000019157 9578500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast ep0) (@Nat.cast Real Real.instNatCast ep1))) Bool.false 34716502058787923820544 18889465931478580854784 1000000000306512 153256000000000000000 4138529546116343 2251799813685248 62500000019157 9578500000000000000 (BSN.log_rat_reduce_isNear ep0 ep1 2 ep5 ep6 236759 524288 24973259072661432 36028797018963968 153256 1000000000000000 rfl rfl rfl rfl (ep12 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep14 := nat_lit 53972150818088090910337934

noncomputable def ep15 := nat_lit 9806206225044045455168967

noncomputable def ep16 := nat_lit 44165944593044045455168967

noncomputable def ep17 := nat_lit 13681445815609453062485491347592146866046743284321690683909457683007658987562290830600045658905080811372395010565947827677605470036294121079488508864180301737865471494204890974265645509835068840465080549957745

noncomputable def ep18 := nat_lit 231714499556396865510889920206523150079811393376960301632499817942333196803513131357563499488546302200815366867712007119763002650772307103678175657719139104636874731038771518520299266622696414842349131395304

noncomputable def ep19 := nat_lit 8978369550011421500876706511871067098718760264493934208903156435737864998391937547068187824077011975074541700434630537294838404525415248443919841847024664017658842168336182958576672102333385008949995305

noncomputable def ep20 := BSN.log_dyadic_bound ep15 ep16 5 4 ep17 524288 153256 ep18 ep19 236759 ep14 ep6 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP ep15) (BSN.artanhQ ep16) 0 4 ep18 ep17 ep19 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep21 := ep13 (BSN.isNear_log_sfrac ep2 ep1 4138529546116343 2251799813685248 62500000019157 9578500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast ep2) (@Nat.cast Real Real.instNatCast ep1))) Bool.false 34716502058787923820544 18889465931478580854784 1000000000306512 153256000000000000000 4138529546116343 2251799813685248 62500000019157 9578500000000000000 (BSN.log_rat_reduce_isNear ep2 ep1 2 ep14 ep6 236759 524288 24973259072661432 36028797018963968 153256 1000000000000000 rfl rfl rfl rfl (ep20 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable abbrev qz267 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)

noncomputable abbrev qz3 := (Real.log qz267)

theorem EMRow17.d4 : Enclosure.Real.IsNear qz3 Bool.false 120447 65536 1 131072 := @Enclosure.Real.IsNear.of_eq qz3 (Real.log qz264) Bool.false 120447 65536 1 131072 BSN.log_two_pi_eq (@Enclosure.Real.IsNear.recentre' (Real.log qz264) Bool.false 481788 262144 2 262144 120447 65536 1 131072 (ep21 rfl rfl rfl rfl rfl rfl rfl rfl) rfl)

noncomputable def ep22 := nat_lit 8589934592000000000000000

noncomputable def ep23 := @BSN.isNear_log_image_fff Real.pi 226375608064910080 72057594037927936 1 1000000000000000 ep0 ep22 ep2 ep22 600168 524288 1 153256 600168 524288 1 153256 300084 262144 2 262144 BSN.pi_near_15 rfl rfl rfl

noncomputable def ep24 := nat_lit 17179869184000000000000000

noncomputable def ep25 := nat_lit 18396140817044028275299783

noncomputable def ep26 := nat_lit 35576010001044028275299783

noncomputable def ep27 := nat_lit 145019262663961446558303139663424756232419223153299357158415217874016130572233056993847515999529612750616182853355499335896178729185698845314776375864537073527142908641610750276034469165612529925303649396973267518946591078603565291376312767403717761600170009932259137778521478520425507632472584532570900560707662248426541531715360699177249902784721815296292248142738824858695953661559845440650653128788875447728828657762006237171740033404723254477174341920697506370253193455781322964835857351124092897592956162654178130575

noncomputable def ep28 := nat_lit 15500762873619990602332184736899274490522931101512051618692838888825382235673431503644115344741331161500627469184702974962114537943617674254904297224139410345221262767191485292268260077615645253784097850065864022184521411511133693085443040736512010941548648374196772723338837137976260321103066698629790037694560548409922339907589559883712609967105556007429010014773911317423638534096849366294542840133852248768895750397896505791271178551667935288585787166713880920071720072716082683081155281219708172458141800988558163320

noncomputable def ep29 := nat_lit 12900190794487083783367107939442176642390171280542213571554777169279725287102813254708993369099729304728646904879886535518616983985412662170766446331701281703998252143668221340329975389245922410714088123244705567402747658401492589451585970559635763980329972215329212888079422466283203384882259392047898400615815810081169907384366653346471604103896809335921621947903075223769953790093549808584241881353287841076643853121427928248525828402335494512605306631304432120211393210317325496757155861061354331245840675149075

noncomputable def ep30 := BSN.log_dyadic_bound ep25 ep26 11 10 ep27 524288 153256 ep28 ep29 600168 ep5 ep24 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base10 (BSN.artanhP ep25) (BSN.artanhQ ep26) 0 10 ep28 ep27 ep29 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep31 := nat_lit 18396140817044045455168967

noncomputable def ep32 := nat_lit 35576010001044045455168967

noncomputable def ep33 := nat_lit 145019262663962847171784895425483977818796535899227200426399035286881207006285364467913811844950531107314785650583974625982406238691319033447632878979985852280879486690814033867010958364699188952871572448188560932645032521756218245629809291975913196623825614492380080480004685076434733043183791438169545293975334857826316990371107134320667652578346815517853870648072772035977941843998949310557583393428557296298890786965786350523173236912472938174255438182435383147950274229549088258679583524155427309880956162654178130575

noncomputable def ep34 := nat_lit 15500762873620157189619721156942591192100275120160672416764593300158228469749443299607348495591439275767946573253526107895503597951484257520435868240203420954375895980141891044871083424251900562230440202302413072793440172565998181227591194192658878334739610458454844032013325963992941389843551995646587189684848765634635122388286241104146031552341815777883628509454807838726994150833304950745987647656768534710890974432620160470644835720379148964170536679305861738540146791997074363921127776563807649880221800988558163320

noncomputable def ep35 := nat_lit 12900190794487324729109480814509220959173684627296055849229843377126536688487849343376525559792931631054411655715865486295286288812423905434305314401904993536755333953308594664509631000767632482919425633906965368325056855874260596615770736441041599390097968820060635361729170158825410327022636428624381203910573184452046894301676992229743752846881064485858738985580654099214803581683226335297196686880535448467637789069028262446657986458573827723305156755787640135484017403116612632808333639900906331245840675149075

noncomputable def ep36 := BSN.log_dyadic_bound ep31 ep32 11 10 ep33 524288 153256 ep34 ep35 600168 ep14 ep24 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base10 (BSN.artanhP ep31) (BSN.artanhQ ep32) 0 10 ep34 ep33 ep35 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep37 := @Enclosure.Real.IsNear.recentre' (Real.log Real.pi) Bool.false 300084 262144 2 262144 75021 65536 1 131072 (ep23 rfl rfl rfl rfl rfl (BSN.isNear_log_sfrac ep0 ep22 600168 524288 1 153256 Bool.false (BSN.logfrac_isNear ep5 ep24 1 ep0 ep22 600168 524288 153256 rfl rfl rfl (ep30 rfl))) (BSN.isNear_log_sfrac ep2 ep22 600168 524288 1 153256 Bool.false (BSN.logfrac_isNear ep14 ep24 1 ep2 ep22 600168 524288 153256 rfl rfl rfl (ep36 rfl))) rfl rfl rfl rfl rfl rfl rfl rfl) rfl

theorem EMRow17.d5 : Enclosure.Real.IsNear (Real.log Real.pi) Bool.false 75021 65536 1 131072 := ep37

noncomputable abbrev qz483 := (@HAdd.hAdd Complex Complex Complex (@instHAdd Complex Complex.instAdd) (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (2 : Complex)) (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul) Complex.I ↑(Enclosure.sfrac Bool.false 68454 1000)))

noncomputable abbrev qz461 := qz483

noncomputable abbrev qz268 := qz461

noncomputable abbrev qz4 := (BSN.headSumC qz268 9)

noncomputable abbrev qz484 := (@instHAdd Complex Complex.instAdd)

noncomputable abbrev qz462 := qz484

noncomputable abbrev qz269 := qz462

noncomputable abbrev qz5 := qz269

noncomputable abbrev qz6 := qz268

noncomputable abbrev qz463 := (@instHPow Complex Complex Complex.instPow)

noncomputable abbrev qz270 := qz463

noncomputable abbrev qz464 := (@Neg.neg Complex Complex.instNeg qz483)

noncomputable abbrev qz271 := qz464

noncomputable abbrev qz7 := (@HPow.hPow Complex Complex Complex qz270 (@Nat.cast Complex Complex.instNatCast 8) qz271)

noncomputable def ep38 := @Enclosure.Complex.IsNear.of_eq qz4 (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz6 8) qz7) Bool.false 101905133827 274877906944 16196562093243 5265836063326208 Bool.false 32105078227 274877906944 16159008664457 5265836063326208

noncomputable def ep39 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz6 8) qz7 Bool.false 156487864259 274877906944 14501197504775 5265836063326208 Bool.true 24151120001 137438953472 7230487570953 2632918031663104 Bool.true

noncomputable abbrev qz8 := (@HPow.hPow Complex Complex Complex qz270 (@Nat.cast Complex Complex.instNatCast 7) qz271)

noncomputable def ep40 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz6 8) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz6 7) qz8) Bool.false 156487864259 274877906944 14501197504775 5265836063326208 Bool.true 24151120001 137438953472 7230487570953 2632918031663104

noncomputable def ep41 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz6 7) qz8 Bool.false 124537251117 274877906944 12687907951669 5265836063326208 Bool.false 25278658719 137438953472 6320608652189 2632918031663104 Bool.false

noncomputable abbrev qz9 := (@HPow.hPow Complex Complex Complex qz270 (@Nat.cast Complex Complex.instNatCast 6) qz271)

noncomputable def ep42 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz6 7) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz6 6) qz9) Bool.false 124537251117 274877906944 12687907951669 5265836063326208 Bool.false 25278658719 137438953472 6320608652189 2632918031663104

noncomputable def ep43 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz6 6) qz9 Bool.false 235794723317 274877906944 10726824644869 5265836063326208 Bool.false 8976801011 68719476736 2672195146539 1316459015831552 Bool.true

noncomputable abbrev qz10 := (@HPow.hPow Complex Complex Complex qz270 (@Nat.cast Complex Complex.instNatCast 5) qz271)

noncomputable def ep44 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz6 6) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz6 5) qz10) Bool.false 235794723317 274877906944 10726824644869 5265836063326208 Bool.false 8976801011 68719476736 2672195146539 1316459015831552

noncomputable def ep45 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz6 5) qz10 Bool.false 355851761139 274877906944 8575164439763 5265836063326208 Bool.false 9489816283 274877906944 8544771092983 5265836063326208 Bool.true

noncomputable abbrev qz11 := (@HPow.hPow Complex Complex Complex qz270 (@Nat.cast Complex Complex.instNatCast 4) qz271)

noncomputable def ep46 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz6 5) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz6 4) qz11) Bool.false 355851761139 274877906944 8575164439763 5265836063326208 Bool.false 9489816283 274877906944 8544771092983 5265836063326208

noncomputable def ep47 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz6 4) qz11 Bool.false 61597766979 68719476736 3088768926083 2632918031663104 Bool.false 46300996145 137438953472 3074535006885 2632918031663104 Bool.false

noncomputable abbrev qz465 := (@Nat.cast Complex Complex.instNatCast 3)

noncomputable abbrev qz272 := qz465

noncomputable abbrev qz12 := (@HPow.hPow Complex Complex Complex qz270 qz272 qz271)

noncomputable def ep48 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz6 4) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz6 3) qz12) Bool.false 61597766979 68719476736 3088768926083 2632918031663104 Bool.false 46300996145 137438953472 3074535006885 2632918031663104

noncomputable def ep49 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz6 3) qz12 Bool.false 5666679439 17179869184 1699251579055 2632918031663104 Bool.false 7751227365 34359738368 846468476465 1316459015831552 Bool.false

noncomputable abbrev qz466 := (@Nat.cast Complex Complex.instNatCast 2)

noncomputable abbrev qz273 := qz466

noncomputable abbrev qz13 := (@HPow.hPow Complex Complex Complex qz270 qz273 qz271)

noncomputable def ep50 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz6 3) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz6 2) qz13) Bool.false 5666679439 17179869184 1699251579055 2632918031663104 Bool.false 7751227365 34359738368 846468476465 1316459015831552

noncomputable def ep51 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz6 2) qz13 Bool.false 1 1 0 1 Bool.false 0 1 0 1 Bool.true

noncomputable abbrev qz274 := (Enclosure.sfrac Bool.false 0 1)

noncomputable abbrev qz14 := qz274

noncomputable def ep52 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz6 2) (Complex.mk (Enclosure.sfrac Bool.false 1 1) qz14) Bool.false 1 1 0 1 Bool.false 0 1 0 1 (BSN.head_sum_c_two qz6)

noncomputable abbrev qz275 := (@Nat.cast Real Real.instNatCast 2)

noncomputable abbrev qz15 := (@Inv.inv Real Real.instInv (Real.sqrt qz275))

noncomputable abbrev qz485 := (Enclosure.sfrac Bool.false 68454 1000)

noncomputable abbrev qz467 := qz485

noncomputable abbrev qz276 := qz467

noncomputable abbrev qz16 := (@HMul.hMul Real Real Real qz263 qz276 (Real.log (Enclosure.sfrac Bool.false 2 1)))

noncomputable abbrev qz17 := qz276

noncomputable abbrev qz277 := (@Eq.refl Real qz467)

noncomputable abbrev qz18 := qz277

noncomputable def ep53 := @Enclosure.Complex.IsNear.of_eq qz13 (Complex.mk (@HMul.hMul Real Real Real qz0 qz15 (Real.cos qz16)) (@HMul.hMul Real Real Real qz0 qz15 (@Neg.neg Real Real.instNeg (Real.sin qz16)))) Bool.true 11513189745 17179869184 1699251579055 2632918031663104 Bool.false 7751227365 34359738368 846468476465 1316459015831552 (BSN.cpow_neg_s_mk qz17 68454 1000 2 qz18 rfl)

noncomputable abbrev qz19 := (@Nat.cast Real Real.instNatCast 1)

noncomputable def ep54 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz275) 741455 524288 1 524288 185363 185365 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz275) (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz275 qz19)) Bool.false 741455 524288 1 524288 (BSN.sqrt_natCast_div_one 2) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz275 qz19)) Bool.false 741455 524288 1 524288 741455 524288 1 524288 (BSN.sqrt_enclosure 2 1 370727 370728 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep55 := BSN.log_dyadic_bound 1 3 6 5 613814355 262144 76628 24381081 945 181704 4 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 1) (BSN.artanhQ 3) 0 5 24381081 613814355 945 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep56 := nat_lit 14776687663802335055932070670893056

noncomputable def ep57 := nat_lit 31901471898837980949691369446728269824

noncomputable def ep58 := nat_lit 478522078482569714245370541700924047360

noncomputable abbrev qz278 := (BSN.cosEvenQ 1073741824)

noncomputable abbrev qz279 := (BSN.cosOddQ 1073741824)

noncomputable def ep59 := BSN.cos_dyadic_bound_f 348653696 1073741824 2 1 524288 153406 ep56 ep57 ep56 ep56 ep58 ep56 496890 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 348653696) qz278 0 1 ep56 ep57 ep56 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 348653696) qz279 0 1 ep56 ep58 ep56 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz20 := (@Nat.cast Real Real.instNatCast 524288)

noncomputable abbrev qz21 := (Real.log (Enclosure.sfrac Bool.false 2 1))

noncomputable abbrev qz22 := (Enclosure.Real.IsNear.const Bool.false 68454 1000)

noncomputable abbrev qz23 := (@Nat.cast Real Real.instNatCast 75557863725914323419136)

noncomputable abbrev qz280 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 24876731) qz20)

noncomputable abbrev qz281 := (BSN.isNear_log_sfrac 2 1 181704 262144 1 76628 Bool.false (BSN.logfrac_isNear 4 2 1 2 1 181704 262144 76628 rfl rfl rfl (ep55 rfl)))

noncomputable abbrev qz282 := (@Nat.cast Real Real.instNatCast 24534322743406841823232)

noncomputable def ep60 := @Enclosure.Real.IsNear.cos_image qz16 qz280 Bool.false 24876731 524288 469 524288 Bool.true 496890 524288 1 76628 (@Enclosure.Real.IsNear.recentre' qz16 Bool.false 777397851 16384000 34227 38314000 24876731 524288 469 524288 (@Enclosure.Real.IsNear.mulLit_ff qz17 qz21 68454 1000 0 1 181704 262144 1 76628 777397851 16384000 34227 38314000 qz22 qz281 rfl) rfl) (Enclosure.sfrac_false_div 24876731 524288) (BSN.cos_reduce2 qz280 (@HDiv.hDiv Real Real Real qz2 qz282 qz23) 226375608064910080 72057594037927936 Bool.false 496890 524288 7 1000000000000000 153256 76628 (BSN.sin_reduce_arg_pos_rat_q2 24876731 524288 226375608064910080 72057594037927936 7 24534322743406841823232 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 496890 524288 24534322743406841823232 75557863725914323419136 348653696 1073741824 153406 153256 (ep59 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep61 := nat_lit 159507359494189904748456847233641349120

noncomputable def ep62 := nat_lit 1116551516459329333239197930635489443840

noncomputable abbrev qz283 := (BSN.sinEvenQ 1073741824)

noncomputable abbrev qz284 := (BSN.sinOddQ 1073741824)

noncomputable def ep63 := BSN.sin_dyadic_bound_f 348653696 1073741824 2 1 524288 153406 ep56 ep61 ep56 ep56 ep62 ep56 167265 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 348653696) qz283 0 1 ep56 ep61 ep56 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 348653696) qz284 0 1 ep56 ep62 ep56 rfl rfl rfl rfl) rfl rfl

noncomputable def ep64 := @Enclosure.Real.IsNear.sin_image qz16 qz280 Bool.false 24876731 524288 469 524288 Bool.true 167265 524288 1 76628 (@Enclosure.Real.IsNear.recentre' qz16 Bool.false 777397851 16384000 34227 38314000 24876731 524288 469 524288 (@Enclosure.Real.IsNear.mulLit_ff qz17 qz21 68454 1000 0 1 181704 262144 1 76628 777397851 16384000 34227 38314000 qz22 qz281 rfl) rfl) (Enclosure.sfrac_false_div 24876731 524288) (BSN.sin_reduce2 qz280 (@HDiv.hDiv Real Real Real qz2 qz282 qz23) 226375608064910080 72057594037927936 Bool.false 167265 524288 7 1000000000000000 153256 76628 (BSN.sin_reduce_arg_pos_rat_q2 24876731 524288 226375608064910080 72057594037927936 7 24534322743406841823232 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 167265 524288 24534322743406841823232 75557863725914323419136 348653696 1073741824 153406 153256 (ep63 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz285 := (@Enclosure.Real.IsNear.recentre' qz15 Bool.false 370728 524288 2 524288 46341 65536 1 262144 (ep54 rfl rfl) rfl)

noncomputable def ep65 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz15 (Real.cos qz16)) (@HMul.hMul Real Real Real qz0 qz15 (@Neg.neg Real Real.instNeg (Real.sin qz16))) Bool.true 11513189745 17179869184 1699251579055 2632918031663104 Bool.false 7751227365 34359738368 846468476465 1316459015831552 (@Enclosure.Real.IsNear.mulLit_ft qz15 (Real.cos qz16) 46341 65536 1 262144 248445 262144 9115705 10043785216 11513189745 17179869184 1699251579055 2632918031663104 qz285 (@Enclosure.Real.IsNear.recentre' (Real.cos qz16) Bool.true 496890 524288 36462820 40175140864 248445 262144 9115705 10043785216 (ep60 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz15 (@Neg.neg Real Real.instNeg (Real.sin qz16)) 46341 65536 1 262144 167265 524288 9115705 10043785216 7751227365 34359738368 846468476465 1316459015831552 qz285 (@Enclosure.Real.IsNear.neg (Real.sin qz16) Bool.true 167265 524288 9115705 10043785216 (@Enclosure.Real.IsNear.recentre' (Real.sin qz16) Bool.true 167265 524288 36462820 40175140864 167265 524288 9115705 10043785216 (ep64 rfl rfl) rfl)) rfl)

noncomputable abbrev qz286 := (Enclosure.Real.IsNear.const Bool.false 0 1)

noncomputable abbrev qz24 := qz286

noncomputable def ep66 := @ep51 11513189745 17179869184 1699251579055 2632918031663104 Bool.false 7751227365 34359738368 846468476465 1316459015831552 Bool.false 5666679439 5666679439 17179869184 1699251579055 2632918031663104 Bool.false 7751227365 7751227365 34359738368 846468476465 1316459015831552 (ep52 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 1) qz14 Bool.false 1 1 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 1) qz24)) (ep53 ep65) rfl rfl

noncomputable abbrev qz25 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 3)))

noncomputable abbrev qz26 := (@HMul.hMul Real Real Real qz263 qz276 (Real.log (Enclosure.sfrac Bool.false 3 1)))

noncomputable def ep67 := @Enclosure.Complex.IsNear.of_eq qz12 (Complex.mk (@HMul.hMul Real Real Real qz0 qz25 (Real.cos qz26)) (@HMul.hMul Real Real Real qz0 qz25 (@Neg.neg Real Real.instNeg (Real.sin qz26)))) Bool.false 38931049223 68719476736 347379336757 658229507915776 Bool.false 15296086685 137438953472 1381598053955 2632918031663104 (BSN.cpow_neg_s_mk qz17 68454 1000 3 qz18 rfl)

noncomputable abbrev qz27 := (@Nat.cast Real Real.instNatCast 3)

noncomputable def ep68 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz27) 908093 524288 1 524288 151348 151350 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz27) (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz27 qz19)) Bool.false 908093 524288 1 524288 (BSN.sqrt_natCast_div_one 3) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz27 qz19)) Bool.false 908093 524288 1 524288 908093 524288 1 524288 (BSN.sqrt_enclosure 3 1 454046 454047 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep69 := BSN.log_dyadic_bound 1 2 10 9 171633298636800 262144 76628 16925142283965 34459425 287994 3 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base9 (BSN.artanhP 1) (BSN.artanhQ 2) 0 9 16925142283965 171633298636800 34459425 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep70 := nat_lit 19222032091252900822476385994109773343710961188762635854078751316183309561505

noncomputable def ep71 := nat_lit 641153462866780105519186997069590271023477356498224607523168458325065864314880

noncomputable def ep72 := nat_lit 22814163178330590403576508919208453061347618765587600338147142003553676961

noncomputable def ep73 := nat_lit 50306480165278395483927601351084973642857954587805475883944491407712438136481

noncomputable def ep74 := nat_lit 11754480152557635267851761612942488302097084869134117804591421735959540845772800

noncomputable def ep75 := BSN.sin_dyadic_bound_f 1478344221 1073741824 3 2 524288 153406 ep70 ep71 ep72 ep73 ep74 ep72 514454 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1478344221) qz283 0 2 ep70 ep71 ep72 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1478344221) qz284 0 2 ep73 ep74 ep72 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz28 := (@Nat.cast Real Real.instNatCast 262144)

noncomputable abbrev qz29 := (Real.log (Enclosure.sfrac Bool.false 3 1))

noncomputable abbrev qz30 := (@Nat.cast Real Real.instNatCast 37778931862957161709568)

noncomputable abbrev qz287 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 19714341) qz28)

noncomputable abbrev qz288 := (BSN.isNear_log_sfrac 3 1 287994 262144 1 76628 Bool.false (BSN.logfrac_isNear 3 1 2 3 1 287994 262144 76628 rfl rfl rfl (ep69 rfl)))

noncomputable def ep76 := @Enclosure.Real.IsNear.cos_image qz26 qz287 Bool.false 19714341 262144 469 524288 Bool.false 514454 524288 1 76628 (@Enclosure.Real.IsNear.recentre' qz26 Bool.false 4928585319 65536000 34227 38314000 19714341 262144 469 524288 (@Enclosure.Real.IsNear.mulLit_ff qz17 qz29 68454 1000 0 1 287994 262144 1 76628 4928585319 65536000 34227 38314000 qz22 qz288 rfl) rfl) (Enclosure.sfrac_false_div 19714341 262144) (BSN.cos_reduce3 qz287 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 52014613179870490918912) qz30) 226375608064910080 72057594037927936 Bool.false 514454 524288 11 1000000000000000 153256 76628 (BSN.sin_reduce_arg_pos_rat_q3 19714341 262144 226375608064910080 72057594037927936 11 52014613179870490918912 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 514454 524288 52014613179870490918912 37778931862957161709568 1478344221 1073741824 153406 153256 (ep75 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep77 := nat_lit 10689046345441980719332915111802855614533355157652836630194038349881195835041

noncomputable def ep78 := nat_lit 71239273651864456168798555229954474558164150722024956391463162036118429368320

noncomputable def ep79 := nat_lit 32021510709969280977191592317570149937477370235427334689905820765636480151201

noncomputable def ep80 := nat_lit 3205767314333900527595934985347951355117386782491123037615842291625329321574400

noncomputable def ep81 := BSN.cos_dyadic_bound_f 1478344221 1073741824 3 2 524288 153406 ep77 ep78 ep72 ep79 ep80 ep72 101065 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1478344221) qz278 0 2 ep77 ep78 ep72 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1478344221) qz279 0 2 ep79 ep80 ep72 rfl rfl rfl rfl) rfl rfl

noncomputable def ep82 := @Enclosure.Real.IsNear.sin_image qz26 qz287 Bool.false 19714341 262144 469 524288 Bool.true 101065 524288 1 76628 (@Enclosure.Real.IsNear.recentre' qz26 Bool.false 4928585319 65536000 34227 38314000 19714341 262144 469 524288 (@Enclosure.Real.IsNear.mulLit_ff qz17 qz29 68454 1000 0 1 287994 262144 1 76628 4928585319 65536000 34227 38314000 qz22 qz288 rfl) rfl) (Enclosure.sfrac_false_div 19714341 262144) (BSN.sin_reduce3 qz287 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 52014613179870490918912) qz30) 226375608064910080 72057594037927936 Bool.false 101065 524288 11 1000000000000000 153256 76628 (BSN.sin_reduce_arg_pos_rat_q3 19714341 262144 226375608064910080 72057594037927936 11 52014613179870490918912 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 101065 524288 52014613179870490918912 37778931862957161709568 1478344221 1073741824 153406 153256 (ep81 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz289 := (@Enclosure.Real.IsNear.recentre' qz25 Bool.false 302698 524288 2 524288 151349 262144 1 262144 (ep68 rfl rfl) rfl)

noncomputable def ep83 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz25 (Real.cos qz26)) (@HMul.hMul Real Real Real qz0 qz25 (@Neg.neg Real Real.instNeg (Real.sin qz26))) Bool.false 38931049223 68719476736 347379336757 658229507915776 Bool.false 15296086685 137438953472 1381598053955 2632918031663104 (@Enclosure.Real.IsNear.mulLit_ff qz25 (Real.cos qz26) 151349 262144 1 262144 257227 262144 9115705 10043785216 38931049223 68719476736 347379336757 658229507915776 qz289 (@Enclosure.Real.IsNear.recentre' (Real.cos qz26) Bool.false 514454 524288 36462820 40175140864 257227 262144 9115705 10043785216 (ep76 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz25 (@Neg.neg Real Real.instNeg (Real.sin qz26)) 151349 262144 1 262144 101065 524288 9115705 10043785216 15296086685 137438953472 1381598053955 2632918031663104 qz289 (@Enclosure.Real.IsNear.neg (Real.sin qz26) Bool.true 101065 524288 9115705 10043785216 (@Enclosure.Real.IsNear.recentre' (Real.sin qz26) Bool.true 101065 524288 36462820 40175140864 101065 524288 9115705 10043785216 (ep82 rfl rfl) rfl)) rfl)

noncomputable def ep84 := @ep49 38931049223 68719476736 347379336757 658229507915776 Bool.false 15296086685 137438953472 1381598053955 2632918031663104 Bool.false 1058241578725734875136 61597766979 68719476736 3088768926083 2632918031663104 Bool.false 1590890113719976591360 46300996145 137438953472 3074535006885 2632918031663104 (ep50 (BSN.head_sum_c_succ qz6 2 3 rfl rfl) (ep66 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep67 ep83) rfl rfl

noncomputable abbrev qz290 := (@Nat.cast Real Real.instNatCast 4)

noncomputable abbrev qz31 := (@Inv.inv Real Real.instInv (Real.sqrt qz290))

noncomputable abbrev qz32 := (@HMul.hMul Real Real Real qz263 qz276 (Real.log (Enclosure.sfrac Bool.false 4 1)))

noncomputable def ep85 := @Enclosure.Complex.IsNear.of_eq qz11 (Complex.mk (@HMul.hMul Real Real Real qz0 qz31 (Real.cos qz32)) (@HMul.hMul Real Real Real qz0 qz31 (@Neg.neg Real Real.instNeg (Real.sin qz32)))) Bool.false 109460693223 274877906944 2397626587597 5265836063326208 Bool.true 83112176007 274877906944 2395701079213 5265836063326208 (BSN.cpow_neg_s_mk qz17 68454 1000 4 qz18 rfl)

noncomputable def ep86 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz290) 1048577 524288 1 524288 131071 131072 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz290) (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz290 qz19)) Bool.false 1048577 524288 1 524288 (BSN.sqrt_natCast_div_one 4) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz290 qz19)) Bool.false 1048577 524288 1 524288 1048577 524288 1 524288 (BSN.sqrt_enclosure 4 1 524288 524289 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep87 := nat_lit 471225594319403171539306640625

noncomputable def ep88 := nat_lit 73155514365408823868279100600

noncomputable def ep89 := BSN.log_dyadic_bound 3 5 13 12 ep87 262144 76628 ep88 89313862490502916491225 363408 8 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base12 (BSN.artanhP 3) (BSN.artanhQ 5) 0 12 ep88 ep87 89313862490502916491225 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep90 := nat_lit 236427002620837360894913130734288896

noncomputable def ep91 := BSN.cos_dyadic_bound_f 697307392 1073741824 2 1 524288 153406 ep90 ep57 ep90 ep90 ep58 ep90 417561 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 697307392) qz278 0 1 ep90 ep57 ep90 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 697307392) qz279 0 1 ep90 ep58 ep90 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz33 := (Real.log (Enclosure.sfrac Bool.false 4 1))

noncomputable abbrev qz291 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 24876731) qz28)

noncomputable abbrev qz292 := (BSN.isNear_log_sfrac 4 1 363408 262144 1 76628 Bool.false (BSN.logfrac_isNear 8 2 1 4 1 363408 262144 76628 rfl rfl rfl (ep89 rfl)))

noncomputable def ep92 := @Enclosure.Real.IsNear.cos_image qz32 qz291 Bool.false 24876731 262144 469 524288 Bool.false 417561 524288 1 76628 (@Enclosure.Real.IsNear.recentre' qz32 Bool.false 777397851 8192000 34227 38314000 24876731 262144 469 524288 (@Enclosure.Real.IsNear.mulLit_ff qz17 qz33 68454 1000 0 1 363408 262144 1 76628 777397851 8192000 34227 38314000 qz22 qz292 rfl) rfl) (Enclosure.sfrac_false_div 24876731 262144) (BSN.cos_reduce0 qz291 (@HDiv.hDiv Real Real Real qz2 qz282 qz30) 226375608064910080 72057594037927936 Bool.false 417561 524288 15 1000000000000000 153256 76628 (BSN.sin_reduce_arg_pos_rat_q0 24876731 262144 226375608064910080 72057594037927936 15 24534322743406841823232 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 417561 524288 24534322743406841823232 37778931862957161709568 697307392 1073741824 153406 153256 (ep91 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep93 := BSN.sin_dyadic_bound_f 697307392 1073741824 2 1 524288 153406 ep90 ep61 ep90 ep90 ep62 ep90 317049 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 697307392) qz283 0 1 ep90 ep61 ep90 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 697307392) qz284 0 1 ep90 ep62 ep90 rfl rfl rfl rfl) rfl rfl

noncomputable def ep94 := @Enclosure.Real.IsNear.sin_image qz32 qz291 Bool.false 24876731 262144 469 524288 Bool.false 317049 524288 1 76628 (@Enclosure.Real.IsNear.recentre' qz32 Bool.false 777397851 8192000 34227 38314000 24876731 262144 469 524288 (@Enclosure.Real.IsNear.mulLit_ff qz17 qz33 68454 1000 0 1 363408 262144 1 76628 777397851 8192000 34227 38314000 qz22 qz292 rfl) rfl) (Enclosure.sfrac_false_div 24876731 262144) (BSN.sin_reduce0 qz291 (@HDiv.hDiv Real Real Real qz2 qz282 qz30) 226375608064910080 72057594037927936 Bool.false 317049 524288 15 1000000000000000 153256 76628 (BSN.sin_reduce_arg_pos_rat_q0 24876731 262144 226375608064910080 72057594037927936 15 24534322743406841823232 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 317049 524288 24534322743406841823232 37778931862957161709568 697307392 1073741824 153406 153256 (ep93 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz293 := (@Enclosure.Real.IsNear.recentre' qz31 Bool.false 262143 524288 1 524288 262143 524288 1 524288 (ep86 rfl rfl) rfl)

noncomputable def ep95 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz31 (Real.cos qz32)) (@HMul.hMul Real Real Real qz0 qz31 (@Neg.neg Real Real.instNeg (Real.sin qz32))) Bool.false 109460693223 274877906944 2397626587597 5265836063326208 Bool.true 83112176007 274877906944 2395701079213 5265836063326208 (@Enclosure.Real.IsNear.mulLit_ff qz31 (Real.cos qz32) 262143 524288 1 524288 417561 524288 9115705 10043785216 109460693223 274877906944 2397626587597 5265836063326208 qz293 (@Enclosure.Real.IsNear.recentre' (Real.cos qz32) Bool.false 417561 524288 36462820 40175140864 417561 524288 9115705 10043785216 (ep92 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz31 (@Neg.neg Real Real.instNeg (Real.sin qz32)) 262143 524288 1 524288 317049 524288 9115705 10043785216 83112176007 274877906944 2395701079213 5265836063326208 qz293 (@Enclosure.Real.IsNear.neg (Real.sin qz32) Bool.false 317049 524288 9115705 10043785216 (@Enclosure.Real.IsNear.recentre' (Real.sin qz32) Bool.false 317049 524288 36462820 40175140864 317049 524288 9115705 10043785216 (ep94 rfl rfl) rfl)) rfl)

noncomputable def ep96 := @ep47 109460693223 274877906944 2397626587597 5265836063326208 Bool.true 83112176007 274877906944 2395701079213 5265836063326208 Bool.false 24453946821056139362304 355851761139 274877906944 8575164439763 5265836063326208 Bool.false 1304270418577064984576 9489816283 274877906944 8544771092983 5265836063326208 (ep48 (BSN.head_sum_c_succ qz6 3 4 rfl rfl) (ep84 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep85 ep95) rfl rfl

noncomputable abbrev qz294 := (@Nat.cast Real Real.instNatCast 5)

noncomputable abbrev qz34 := (@Inv.inv Real Real.instInv (Real.sqrt qz294))

noncomputable abbrev qz35 := (@HMul.hMul Real Real Real qz263 qz276 (Real.log (Enclosure.sfrac Bool.false 5 1)))

noncomputable def ep97 := @Enclosure.Complex.IsNear.of_eq qz10 (Complex.mk (@HMul.hMul Real Real Real qz0 qz34 (Real.cos qz35)) (@HMul.hMul Real Real Real qz0 qz34 (@Neg.neg Real Real.instNeg (Real.sin qz35)))) Bool.true 60028518911 137438953472 1075830102553 2632918031663104 Bool.false 26417387761 274877906944 2144009493173 5265836063326208 (BSN.cpow_neg_s_mk qz17 68454 1000 5 qz18 rfl)

noncomputable def ep98 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz294) 1172343 524288 1 524288 117234 117235 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz294) (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz294 qz19)) Bool.false 1172343 524288 1 524288 (BSN.sqrt_natCast_div_one 5) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz294 qz19)) Bool.false 1172343 524288 1 524288 1172343 524288 1 524288 (BSN.sqrt_enclosure 5 1 586171 586172 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep99 := nat_lit 39510257877627786146545168145625

noncomputable def ep100 := nat_lit 8181717556663416291180905432700

noncomputable def ep101 := nat_lit 6646766139202842132480000

noncomputable def ep102 := BSN.log_dyadic_bound 2 3 16 15 ep99 262144 76628 ep100 ep101 421904 5 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base15 (BSN.artanhP 2) (BSN.artanhQ 3) 0 15 ep100 ep99 ep101 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep103 := nat_lit 2925177226006055083518744281864881

noncomputable def ep104 := BSN.cos_dyadic_bound_f 232561621 1073741824 2 1 524288 153406 ep103 ep57 ep103 ep103 ep58 ep103 512038 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 232561621) qz278 0 1 ep103 ep57 ep103 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 232561621) qz279 0 1 ep103 ep58 ep103 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz36 := (Real.log (Enclosure.sfrac Bool.false 5 1))

noncomputable abbrev qz295 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 3610127) (@Nat.cast Real Real.instNatCast 32768))

noncomputable abbrev qz296 := (BSN.isNear_log_sfrac 5 1 421904 262144 1 76628 Bool.false (BSN.logfrac_isNear 5 1 2 5 1 421904 262144 76628 rfl rfl rfl (ep102 rfl)))

noncomputable abbrev qz297 := (@Nat.cast Real Real.instNatCast 4722366482869645213696)

noncomputable def ep105 := @Enclosure.Real.IsNear.cos_image qz35 qz295 Bool.false 3610127 32768 235 262144 Bool.true 512038 524288 1 76628 (@Enclosure.Real.IsNear.recentre' qz35 Bool.false 902531763 8192000 34227 38314000 3610127 32768 235 262144 (@Enclosure.Real.IsNear.mulLit_ff qz17 qz36 68454 1000 0 1 421904 262144 1 76628 902531763 8192000 34227 38314000 qz22 qz296 rfl) rfl) (Enclosure.sfrac_false_div 3610127 32768) (BSN.cos_reduce2 qz295 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 1022816827757186514944) qz297) 226375608064910080 72057594037927936 Bool.false 512038 524288 17 1000000000000000 153256 76628 (BSN.sin_reduce_arg_pos_rat_q2 3610127 32768 226375608064910080 72057594037927936 17 1022816827757186514944 4722366482869645213696 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 512038 524288 1022816827757186514944 4722366482869645213696 232561621 1073741824 153406 153256 (ep104 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep106 := BSN.sin_dyadic_bound_f 232561621 1073741824 2 1 524288 153406 ep103 ep61 ep103 ep103 ep62 ep103 112669 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 232561621) qz283 0 1 ep103 ep61 ep103 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 232561621) qz284 0 1 ep103 ep62 ep103 rfl rfl rfl rfl) rfl rfl

noncomputable def ep107 := @Enclosure.Real.IsNear.sin_image qz35 qz295 Bool.false 3610127 32768 235 262144 Bool.true 112669 524288 1 76628 (@Enclosure.Real.IsNear.recentre' qz35 Bool.false 902531763 8192000 34227 38314000 3610127 32768 235 262144 (@Enclosure.Real.IsNear.mulLit_ff qz17 qz36 68454 1000 0 1 421904 262144 1 76628 902531763 8192000 34227 38314000 qz22 qz296 rfl) rfl) (Enclosure.sfrac_false_div 3610127 32768) (BSN.sin_reduce2 qz295 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 1022816827757186514944) qz297) 226375608064910080 72057594037927936 Bool.false 112669 524288 17 1000000000000000 153256 76628 (BSN.sin_reduce_arg_pos_rat_q2 3610127 32768 226375608064910080 72057594037927936 17 1022816827757186514944 4722366482869645213696 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 112669 524288 1022816827757186514944 4722366482869645213696 232561621 1073741824 153406 153256 (ep106 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz298 := (@Enclosure.Real.IsNear.recentre' qz34 Bool.false 234469 524288 1 524288 234469 524288 1 524288 (ep98 rfl rfl) rfl)

noncomputable def ep108 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz34 (Real.cos qz35)) (@HMul.hMul Real Real Real qz0 qz34 (@Neg.neg Real Real.instNeg (Real.sin qz35))) Bool.true 60028518911 137438953472 1075830102553 2632918031663104 Bool.false 26417387761 274877906944 2144009493173 5265836063326208 (@Enclosure.Real.IsNear.mulLit_ft qz34 (Real.cos qz35) 234469 524288 1 524288 256019 262144 4567431 5021892608 60028518911 137438953472 1075830102553 2632918031663104 qz298 (@Enclosure.Real.IsNear.recentre' (Real.cos qz35) Bool.true 512038 524288 18269724 20087570432 256019 262144 4567431 5021892608 (ep105 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz34 (@Neg.neg Real Real.instNeg (Real.sin qz35)) 234469 524288 1 524288 112669 524288 4567431 5021892608 26417387761 274877906944 2144009493173 5265836063326208 qz298 (@Enclosure.Real.IsNear.neg (Real.sin qz35) Bool.true 112669 524288 4567431 5021892608 (@Enclosure.Real.IsNear.recentre' (Real.sin qz35) Bool.true 112669 524288 18269724 20087570432 112669 524288 4567431 5021892608 (ep107 rfl rfl) rfl)) rfl)

noncomputable def ep109 := @ep45 60028518911 137438953472 1075830102553 2632918031663104 Bool.false 26417387761 274877906944 2144009493173 5265836063326208 Bool.false 32407380006908276506624 235794723317 274877906944 10726824644869 5265836063326208 Bool.false 9870097091825852481536 8976801011 68719476736 2672195146539 1316459015831552 (ep46 (BSN.head_sum_c_succ qz6 4 5 rfl rfl) (ep96 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep97 ep108) rfl rfl

noncomputable abbrev qz299 := (@Nat.cast Real Real.instNatCast 6)

noncomputable abbrev qz37 := (@Inv.inv Real Real.instInv (Real.sqrt qz299))

noncomputable abbrev qz38 := (@HMul.hMul Real Real Real qz263 qz276 (Real.log (Enclosure.sfrac Bool.false 6 1)))

noncomputable def ep110 := @Enclosure.Complex.IsNear.of_eq qz9 (Complex.mk (@HMul.hMul Real Real Real qz0 qz37 (Real.cos qz38)) (@HMul.hMul Real Real Real qz0 qz37 (@Neg.neg Real Real.instNeg (Real.sin qz38)))) Bool.true 13907184025 34359738368 122567706675 329114753957888 Bool.false 7325056697 137438953472 976218359111 2632918031663104 (BSN.cpow_neg_s_mk qz17 68454 1000 6 qz18 rfl)

noncomputable abbrev qz300 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 6) qz19)

noncomputable def ep111 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz299) 1284239 524288 1 524288 107019 107020 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz299) (Real.sqrt qz300) Bool.false 1284239 524288 1 524288 (BSN.sqrt_natCast_div_one 6) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz300) Bool.false 1284239 524288 1 524288 1284239 524288 1 524288 (BSN.sqrt_enclosure 6 1 642119 642120 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep112 := BSN.log_dyadic_bound 2 10 4 3 105000000 262144 76628 1434560 960 106290 12 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 2) (BSN.artanhQ 10) 0 3 1434560 105000000 960 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz39 := (Real.log (Enclosure.sfrac Bool.false 6 1))

noncomputable def ep113 := @Enclosure.Real.IsNear.mulLit_ff qz17 qz39 68454 1000 0 1 4034681531866359 2251799813685248 125000000019157 9578500000000000000 138095044791189869493 1125899906842624000 4278375000655686639 4789250000000000000000 qz22 (BSN.isNear_log_sfrac 6 1 4034681531866359 2251799813685248 125000000019157 9578500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz300) Bool.false 16922680887833197019136 9444732965739290427392 1000000000153256 76628000000000000000 4034681531866359 2251799813685248 125000000019157 9578500000000000000 (BSN.log_rat_reduce_isNear 6 1 2 12 8 106290 262144 24973259072661432 36028797018963968 76628 1000000000000000 rfl rfl rfl rfl (ep112 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep114 := nat_lit 390556281841353262948593174057216

noncomputable def ep115 := BSN.cos_dyadic_bound_f 140579148 1073741824 2 1 524288 153406 ep114 ep57 ep114 ep114 ep58 ep114 519800 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 140579148) qz278 0 1 ep114 ep57 ep114 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 140579148) qz279 0 1 ep114 ep58 ep114 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz301 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 16076379) (@Nat.cast Real Real.instNatCast 131072))

noncomputable abbrev qz302 := (@Nat.cast Real Real.instNatCast 18889465931478580854784)

noncomputable def ep116 := @Enclosure.Real.IsNear.cos_image qz38 qz301 Bool.false 16076379 131072 469 524288 Bool.true 519800 524288 1 76628 (@Enclosure.Real.IsNear.recentre' qz38 Bool.false 138095044791189869493 1125899906842624000 4278375000655686639 4789250000000000000000 16076379 131072 469 524288 (ep113 rfl) rfl) (Enclosure.sfrac_false_div 16076379 131072) (BSN.cos_reduce2 qz301 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 2473094541596015198208) qz302) 226375608064910080 72057594037927936 Bool.false 519800 524288 19 1000000000000000 153256 76628 (BSN.sin_reduce_arg_pos_rat_q2 16076379 131072 226375608064910080 72057594037927936 19 2473094541596015198208 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 519800 524288 2473094541596015198208 18889465931478580854784 140579148 1073741824 153406 153256 (ep115 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep117 := BSN.sin_dyadic_bound_f 140579148 1073741824 1 0 524288 153406 0 1 1 0 1 1 68446 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 140579148) qz283 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 140579148) qz284 0 0 rfl) rfl rfl

noncomputable def ep118 := @Enclosure.Real.IsNear.sin_image qz38 qz301 Bool.false 16076379 131072 469 524288 Bool.true 68446 524288 1 76628 (@Enclosure.Real.IsNear.recentre' qz38 Bool.false 138095044791189869493 1125899906842624000 4278375000655686639 4789250000000000000000 16076379 131072 469 524288 (ep113 rfl) rfl) (Enclosure.sfrac_false_div 16076379 131072) (BSN.sin_reduce2 qz301 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 2473094541596015198208) qz302) 226375608064910080 72057594037927936 Bool.false 68446 524288 19 1000000000000000 153256 76628 (BSN.sin_reduce_arg_pos_rat_q2 16076379 131072 226375608064910080 72057594037927936 19 2473094541596015198208 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 68446 524288 2473094541596015198208 18889465931478580854784 140579148 1073741824 153406 153256 (ep117 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz303 := (@Enclosure.Real.IsNear.recentre' qz37 Bool.false 214039 524288 1 524288 214039 524288 1 524288 (ep111 rfl rfl) rfl)

noncomputable def ep119 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz37 (Real.cos qz38)) (@HMul.hMul Real Real Real qz0 qz37 (@Neg.neg Real Real.instNeg (Real.sin qz38))) Bool.true 13907184025 34359738368 122567706675 329114753957888 Bool.false 7325056697 137438953472 976218359111 2632918031663104 (@Enclosure.Real.IsNear.mulLit_ft qz37 (Real.cos qz38) 214039 524288 1 524288 64975 65536 9115705 10043785216 13907184025 34359738368 122567706675 329114753957888 qz303 (@Enclosure.Real.IsNear.recentre' (Real.cos qz38) Bool.true 519800 524288 36462820 40175140864 64975 65536 9115705 10043785216 (ep116 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz37 (@Neg.neg Real Real.instNeg (Real.sin qz38)) 214039 524288 1 524288 34223 262144 9115705 10043785216 7325056697 137438953472 976218359111 2632918031663104 qz303 (@Enclosure.Real.IsNear.neg (Real.sin qz38) Bool.true 34223 262144 9115705 10043785216 (@Enclosure.Real.IsNear.recentre' (Real.sin qz38) Bool.true 68446 524288 36462820 40175140864 34223 262144 9115705 10043785216 (ep118 rfl rfl) rfl)) rfl)

noncomputable def ep120 := @ep43 13907184025 34359738368 122567706675 329114753957888 Bool.false 7325056697 137438953472 976218359111 2632918031663104 Bool.false 4279067365450035757056 124537251117 274877906944 12687907951669 5265836063326208 Bool.false 1737136199757604061184 25278658719 137438953472 6320608652189 2632918031663104 (ep44 (BSN.head_sum_c_succ qz6 5 6 rfl rfl) (ep109 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep110 ep119) rfl rfl

noncomputable abbrev qz304 := (@Nat.cast Real Real.instNatCast 7)

noncomputable abbrev qz40 := (@Inv.inv Real Real.instInv (Real.sqrt qz304))

noncomputable abbrev qz41 := (@HMul.hMul Real Real Real qz263 qz276 (Real.log (Enclosure.sfrac Bool.false 7 1)))

noncomputable def ep121 := @Enclosure.Complex.IsNear.of_eq qz8 (Complex.mk (@HMul.hMul Real Real Real qz0 qz40 (Real.cos qz41)) (@HMul.hMul Real Real Real qz0 qz40 (@Neg.neg Real Real.instNeg (Real.sin qz41)))) Bool.false 15975306571 137438953472 906644776553 2632918031663104 Bool.true 1544680585 4294967296 227469729691 658229507915776 (BSN.cpow_neg_s_mk qz17 68454 1000 7 qz18 rfl)

noncomputable abbrev qz305 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 7) qz19)

noncomputable def ep122 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz304) 1387135 524288 1 524288 99081 99082 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz304) (Real.sqrt qz305) Bool.false 1387135 524288 1 524288 (BSN.sqrt_natCast_div_one 7) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz305) Bool.false 1387135 524288 1 524288 1387135 524288 1 524288 (BSN.sqrt_enclosure 7 1 693567 693568 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep123 := BSN.log_dyadic_bound 3 11 5 4 202569142545 262144 76628 5259111624 688905 146699 14 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 3) (BSN.artanhQ 11) 0 4 5259111624 202569142545 688905 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz42 := (Real.log (Enclosure.sfrac Bool.false 7 1))

noncomputable def ep124 := @Enclosure.Real.IsNear.mulLit_ff qz17 qz42 68454 1000 0 1 4381792198794487 2251799813685248 125000000019157 9578500000000000000 149975601588138906549 1125899906842624000 4278375000655686639 4789250000000000000000 qz22 (BSN.isNear_log_sfrac 7 1 4381792198794487 2251799813685248 125000000019157 9578500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz305) Bool.false 18378568546572512002048 9444732965739290427392 1000000000153256 76628000000000000000 4381792198794487 2251799813685248 125000000019157 9578500000000000000 (BSN.log_rat_reduce_isNear 7 1 2 14 8 146699 262144 24973259072661432 36028797018963968 76628 1000000000000000 rfl rfl rfl rfl (ep123 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep125 := nat_lit 7449967282926370199276991972106378236813281291752338793783682707813936800000

noncomputable def ep126 := nat_lit 11096767216977426459932152880117650279776434825053439826752193440100000000

noncomputable def ep127 := nat_lit 22327708314345155744911111610558899409880291005606909501697543736561610400000

noncomputable def ep128 := BSN.cos_dyadic_bound_f 1350981990 1073741824 3 2 524288 153406 ep125 ep78 ep126 ep127 ep80 ep126 161234 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1350981990) qz278 0 2 ep125 ep78 ep126 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1350981990) qz279 0 2 ep127 ep80 ep126 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz306 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 69837831) qz20)

noncomputable def ep129 := @Enclosure.Real.IsNear.cos_image qz41 qz306 Bool.false 69837831 524288 235 262144 Bool.false 161234 524288 1 76628 (@Enclosure.Real.IsNear.recentre' qz41 Bool.false 149975601588138906549 1125899906842624000 4278375000655686639 4789250000000000000000 69837831 524288 235 262144 (ep124 rfl) rfl) (Enclosure.sfrac_false_div 69837831 524288) (BSN.cos_reduce0 qz306 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 95066906079449183158272) qz23) 226375608064910080 72057594037927936 Bool.false 161234 524288 21 1000000000000000 153256 76628 (BSN.sin_reduce_arg_pos_rat_q0 69837831 524288 226375608064910080 72057594037927936 21 95066906079449183158272 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 161234 524288 95066906079449183158272 75557863725914323419136 1350981990 1073741824 153406 153256 (ep128 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep130 := nat_lit 13401063695493884417530639827487386706040085177294167076949227119313006240000

noncomputable def ep131 := nat_lit 35080057769846971926883214157803917558223442188910827251337996046916759200000

noncomputable def ep132 := BSN.sin_dyadic_bound_f 1350981990 1073741824 3 2 524288 153406 ep130 ep71 ep126 ep131 ep74 ep126 498880 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1350981990) qz283 0 2 ep130 ep71 ep126 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1350981990) qz284 0 2 ep131 ep74 ep126 rfl rfl rfl rfl) rfl rfl

noncomputable def ep133 := @Enclosure.Real.IsNear.sin_image qz41 qz306 Bool.false 69837831 524288 235 262144 Bool.false 498880 524288 1 76628 (@Enclosure.Real.IsNear.recentre' qz41 Bool.false 149975601588138906549 1125899906842624000 4278375000655686639 4789250000000000000000 69837831 524288 235 262144 (ep124 rfl) rfl) (Enclosure.sfrac_false_div 69837831 524288) (BSN.sin_reduce0 qz306 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 95066906079449183158272) qz23) 226375608064910080 72057594037927936 Bool.false 498880 524288 21 1000000000000000 153256 76628 (BSN.sin_reduce_arg_pos_rat_q0 69837831 524288 226375608064910080 72057594037927936 21 95066906079449183158272 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 498880 524288 95066906079449183158272 75557863725914323419136 1350981990 1073741824 153406 153256 (ep132 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz307 := (@Enclosure.Real.IsNear.recentre' qz40 Bool.false 198163 524288 1 524288 198163 524288 1 524288 (ep122 rfl rfl) rfl)

noncomputable def ep134 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz40 (Real.cos qz41)) (@HMul.hMul Real Real Real qz0 qz40 (@Neg.neg Real Real.instNeg (Real.sin qz41))) Bool.false 15975306571 137438953472 906644776553 2632918031663104 Bool.true 1544680585 4294967296 227469729691 658229507915776 (@Enclosure.Real.IsNear.mulLit_ff qz40 (Real.cos qz41) 198163 524288 1 524288 80617 262144 4567431 5021892608 15975306571 137438953472 906644776553 2632918031663104 qz307 (@Enclosure.Real.IsNear.recentre' (Real.cos qz41) Bool.false 161234 524288 18269724 20087570432 80617 262144 4567431 5021892608 (ep129 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz40 (@Neg.neg Real Real.instNeg (Real.sin qz41)) 198163 524288 1 524288 7795 8192 4567431 5021892608 1544680585 4294967296 227469729691 658229507915776 qz307 (@Enclosure.Real.IsNear.neg (Real.sin qz41) Bool.false 7795 8192 4567431 5021892608 (@Enclosure.Real.IsNear.recentre' (Real.sin qz41) Bool.false 498880 524288 18269724 20087570432 7795 8192 4567431 5021892608 (ep133 rfl rfl) rfl)) rfl)

noncomputable def ep135 := @ep41 15975306571 137438953472 906644776553 2632918031663104 Bool.true 1544680585 4294967296 227469729691 658229507915776 Bool.false 21507528294825352757248 156487864259 274877906944 14501197504775 5265836063326208 Bool.true 103728270566066487296 24151120001 137438953472 7230487570953 2632918031663104 (ep42 (BSN.head_sum_c_succ qz6 6 7 rfl rfl) (ep120 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep121 ep134) rfl rfl

noncomputable abbrev qz308 := (@Nat.cast Real Real.instNatCast 8)

noncomputable abbrev qz43 := (@Inv.inv Real Real.instInv (Real.sqrt qz308))

noncomputable abbrev qz44 := (@HMul.hMul Real Real Real qz263 qz276 (Real.log (Enclosure.sfrac Bool.false 8 1)))

noncomputable def ep136 := @Enclosure.Complex.IsNear.of_eq qz7 (Complex.mk (@HMul.hMul Real Real Real qz0 qz43 (Real.cos qz44)) (@HMul.hMul Real Real Real qz0 qz43 (@Neg.neg Real Real.instNeg (Real.sin qz44)))) Bool.true 852855163 4294967296 423841147117 1316459015831552 Bool.false 80407318229 274877906944 1698033522551 5265836063326208 (BSN.cpow_neg_s_mk qz17 68454 1000 8 qz18 rfl)

noncomputable abbrev qz309 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 8) qz19)

noncomputable def ep137 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz308) 1482911 524288 1 524288 92681 92682 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz308) (Real.sqrt qz309) Bool.false 1482911 524288 1 524288 (BSN.sqrt_natCast_div_one 8) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz309) Bool.false 1482911 524288 1 524288 1482911 524288 1 524288 (BSN.sqrt_enclosure 8 1 741455 741456 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep138 := BSN.log_dyadic_bound 0 16 1 0 1 262144 76628 0 1 0 16 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 0) (BSN.artanhQ 16) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz45 := (Real.log (Enclosure.sfrac Bool.false 8 1))

noncomputable def ep139 := @Enclosure.Real.IsNear.mulLit_ff qz17 qz45 68454 1000 0 1 9364972152248037 4503599627370496 250000000057471 19157000000000000000 320534901854993562399 2251799813685248000 8556750001967059917 9578500000000000000000 qz22 (BSN.isNear_log_sfrac 8 1 9364972152248037 4503599627370496 250000000057471 19157000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz309) Bool.false 19639770079031275290624 9444732965739290427392 1000000000229884 76628000000000000000 9364972152248037 4503599627370496 250000000057471 19157000000000000000 (BSN.log_rat_reduce_isNear 8 1 3 16 16 0 262144 24973259072661432 36028797018963968 76628 1000000000000000 rfl rfl rfl rfl (ep138 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep140 := nat_lit 2677488449161125320162913202030419972286931979478459171483269756406988800000

noncomputable def ep141 := nat_lit 1436057074798962542799483379989063159875543523915318546289760665600000000

noncomputable def ep142 := nat_lit 8029593233333778035403140639331281790541044851387546877357229747889766400000

noncomputable def ep143 := BSN.cos_dyadic_bound_f 1046276480 1073741824 3 2 524288 153406 ep140 ep78 ep141 ep142 ep80 ep141 294464 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1046276480) qz278 0 2 ep140 ep78 ep141 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1046276480) qz279 0 2 ep142 ep80 ep141 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz310 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 74630347) qz20)

noncomputable def ep144 := @Enclosure.Real.IsNear.cos_image qz44 qz310 Bool.false 74630347 524288 469 524288 Bool.true 294464 524288 1 76628 (@Enclosure.Real.IsNear.recentre' qz44 Bool.false 320534901854993562399 2251799813685248000 8556750001967059917 9578500000000000000000 74630347 524288 469 524288 (ep139 rfl) rfl) (Enclosure.sfrac_false_div 74630347 524288) (BSN.cos_reduce2 qz310 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 73625161969184207273984) qz23) 226375608064910080 72057594037927936 Bool.false 294464 524288 22 1000000000000000 153256 76628 (BSN.sin_reduce_arg_pos_rat_q2 74630347 524288 226375608064910080 72057594037927936 22 73625161969184207273984 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 294464 524288 73625161969184207273984 75557863725914323419136 1046276480 1073741824 153406 153256 (ep143 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep145 := nat_lit 4818330362830186406259004176950764699588577128242094253832853753000099840000

noncomputable def ep146 := nat_lit 12617111619767480362751907014160591920473141598738193482392052597732147200000

noncomputable def ep147 := BSN.sin_dyadic_bound_f 1046276480 1073741824 3 2 524288 153406 ep145 ep71 ep141 ep146 ep74 ep141 433783 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1046276480) qz283 0 2 ep145 ep71 ep141 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1046276480) qz284 0 2 ep146 ep74 ep141 rfl rfl rfl rfl) rfl rfl

noncomputable def ep148 := @Enclosure.Real.IsNear.sin_image qz44 qz310 Bool.false 74630347 524288 469 524288 Bool.true 433783 524288 1 76628 (@Enclosure.Real.IsNear.recentre' qz44 Bool.false 320534901854993562399 2251799813685248000 8556750001967059917 9578500000000000000000 74630347 524288 469 524288 (ep139 rfl) rfl) (Enclosure.sfrac_false_div 74630347 524288) (BSN.sin_reduce2 qz310 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 73625161969184207273984) qz23) 226375608064910080 72057594037927936 Bool.false 433783 524288 22 1000000000000000 153256 76628 (BSN.sin_reduce_arg_pos_rat_q2 74630347 524288 226375608064910080 72057594037927936 22 73625161969184207273984 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 433783 524288 73625161969184207273984 75557863725914323419136 1046276480 1073741824 153406 153256 (ep147 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz311 := (@Enclosure.Real.IsNear.recentre' qz43 Bool.false 185363 524288 1 524288 185363 524288 1 524288 (ep137 rfl rfl) rfl)

noncomputable def ep149 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz43 (Real.cos qz44)) (@HMul.hMul Real Real Real qz0 qz43 (@Neg.neg Real Real.instNeg (Real.sin qz44))) Bool.true 852855163 4294967296 423841147117 1316459015831552 Bool.false 80407318229 274877906944 1698033522551 5265836063326208 (@Enclosure.Real.IsNear.mulLit_ft qz43 (Real.cos qz44) 185363 524288 1 524288 4601 8192 9115705 10043785216 852855163 4294967296 423841147117 1316459015831552 qz311 (@Enclosure.Real.IsNear.recentre' (Real.cos qz44) Bool.true 294464 524288 36462820 40175140864 4601 8192 9115705 10043785216 (ep144 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz43 (@Neg.neg Real Real.instNeg (Real.sin qz44)) 185363 524288 1 524288 433783 524288 9115705 10043785216 80407318229 274877906944 1698033522551 5265836063326208 qz311 (@Enclosure.Real.IsNear.neg (Real.sin qz44) Bool.true 433783 524288 9115705 10043785216 (@Enclosure.Real.IsNear.recentre' (Real.sin qz44) Bool.true 433783 524288 36462820 40175140864 433783 524288 9115705 10043785216 (ep148 rfl rfl) rfl)) rfl)

noncomputable def ep150 := @ep39 852855163 4294967296 423841147117 1316459015831552 Bool.false 80407318229 274877906944 1698033522551 5265836063326208 Bool.false 437679217081468321792 101905133827 274877906944 16196562093243 5265836063326208 Bool.false 4412488352655573254144 32105078227 274877906944 16159008664457 5265836063326208 (ep40 (BSN.head_sum_c_succ qz6 7 8 rfl rfl) (ep135 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep136 ep149) rfl rfl

theorem EMRow17.d6 : Enclosure.Complex.IsNear qz4 Bool.false 101905133827 274877906944 16196562093243 5265836063326208 Bool.false 32105078227 274877906944 16159008664457 5265836063326208 := ep38 (BSN.head_sum_c_succ qz6 8 9 rfl rfl) (ep150 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

theorem EMRow17.d7 : @Eq Nat (BSN.factNat (Nat.mul 2 1)) 2 := @Eq.refl Nat 2

theorem EMRow17.d8 : @Eq Nat (Nat.pow 14 1) 14 := @Eq.refl Nat 14

noncomputable def ep151 := nat_lit 3856353088438573671062795892047

noncomputable def ep152 := nat_lit 2363734138774531614579884032000

noncomputable def ep153 := nat_lit 13856292630249983680615733280095871631

noncomputable def ep154 := nat_lit 2602404976956964265717068509745250304000

noncomputable abbrev qz486 := (@instHMul Complex Complex.instMul)

noncomputable abbrev qz468 := qz486

noncomputable abbrev qz312 := qz468

noncomputable abbrev qz46 := qz312

noncomputable abbrev qz47 := (@instHSub Real Real.instSub)

noncomputable abbrev qz469 := (@instHSub Complex Complex.instSub)

noncomputable abbrev qz313 := qz469

noncomputable abbrev qz48 := qz313

noncomputable abbrev qz487 := (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (4 : Complex))

noncomputable abbrev qz488 := (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid))

noncomputable abbrev qz470 := (@HAdd.hAdd Complex Complex Complex qz484 (@HAdd.hAdd Complex Complex Complex qz484 qz487 (@HMul.hMul Complex Complex Complex qz486 Complex.I (@HDiv.hDiv Complex Complex Complex qz488 (↑qz485) (2 : Complex)))) (@Nat.cast Complex Complex.instNatCast 2))

noncomputable abbrev qz314 := qz470

noncomputable abbrev qz49 := (Complex.Stirling.logGammaStirling 1 qz314)

noncomputable abbrev qz471 := (@HAdd.hAdd Complex Complex Complex qz484 qz487 (@HMul.hMul Complex Complex Complex qz486 Complex.I (@HDiv.hDiv Complex Complex Complex qz488 (↑qz485) (2 : Complex))))

noncomputable abbrev qz315 := qz471

noncomputable abbrev qz50 := qz315

noncomputable abbrev qz51 := (@HMul.hMul Real Real Real qz263 (@HDiv.hDiv Real Real Real qz266 qz276 (2 : Real)) (Real.log Real.pi))

noncomputable def ep155 := Complex.re (@HMul.hMul Complex Complex Complex qz46 (Complex.exp (@HMul.hMul Complex Complex Complex qz46 Complex.I ↑(@HSub.hSub Real Real Real qz47 (Complex.im (@HSub.hSub Complex Complex Complex qz48 qz49 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz50 (@Nat.cast Complex Complex.instNatCast j))))) qz51))) (zetaApproximant qz6 1 14))

noncomputable def ep156 := @Enclosure.Real.IsNear.of_eq ep155 (@HSub.hSub Real Real Real qz47 (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz47 (Complex.im (@HSub.hSub Complex Complex Complex qz48 qz49 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz50 (@Nat.cast Complex Complex.instNatCast j))))) qz51)) (Complex.re (zetaApproximant qz6 1 14))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz47 (Complex.im (@HSub.hSub Complex Complex Complex qz48 qz49 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz50 (@Nat.cast Complex Complex.instNatCast j))))) qz51)) (Complex.im (zetaApproximant qz6 1 14))))

noncomputable def ep157 := nat_lit 1928157692217268796264335573411

noncomputable def ep158 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz47 (Complex.im (@HSub.hSub Complex Complex Complex qz48 qz49 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz50 (@Nat.cast Complex Complex.instNatCast j))))) qz51)) (Complex.re (zetaApproximant qz6 1 14))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz47 (Complex.im (@HSub.hSub Complex Complex Complex qz48 qz49 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz50 (@Nat.cast Complex Complex.instNatCast j))))) qz51)) (Complex.im (zetaApproximant qz6 1 14))) ep157

noncomputable def ep159 := nat_lit 1181867069387265807289942016000

noncomputable def ep160 := nat_lit 6906223108744175866132949714346606503

noncomputable def ep161 := nat_lit 1301202488478482132858534254872625152000

noncomputable def ep162 := nat_lit 1508160161443141364989809

noncomputable def ep163 := nat_lit 94549365550981264583195361280

noncomputable def ep164 := nat_lit 116923767364351862266223603740423

noncomputable def ep165 := nat_lit 6939746605218571375245516025987334144

noncomputable def ep166 := nat_lit 182307868926217141725951283496064833656213369618625021870080

noncomputable def ep167 := @Enclosure.Real.IsNear.mulLit_tf (Real.cos (@HSub.hSub Real Real Real qz47 (Complex.im (@HSub.hSub Complex Complex Complex qz48 qz49 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz50 (@Nat.cast Complex Complex.instNatCast j))))) qz51)) (Complex.re (zetaApproximant qz6 1 14)) 524287 524288 4134885

noncomputable def ep168 := nat_lit 3677675952707713134722653

noncomputable def ep169 := nat_lit 2254232538961917509632000

noncomputable def ep170 := nat_lit 1200703515796436208344827259

noncomputable def ep171 := nat_lit 259105996493360722392121344000

noncomputable def ep172 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HSub.hSub Real Real Real qz47 (Complex.im (@HSub.hSub Complex Complex Complex qz48 qz49 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz50 (@Nat.cast Complex Complex.instNatCast j))))) qz51)) Bool.true 524287 524288 16539540

noncomputable abbrev qz316 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 24706765) qz20)

noncomputable def ep173 := @Enclosure.Real.IsNear.cos_image (@HSub.hSub Real Real Real qz47 (Complex.im (@HSub.hSub Complex Complex Complex qz48 qz49 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz50 (@Nat.cast Complex Complex.instNatCast j))))) qz51) qz316 Bool.false 24706765 524288 209

noncomputable def ep174 := nat_lit 251094630400000000000000000

noncomputable def ep175 := @Enclosure.Real.IsNear.recentre' (@HSub.hSub Real Real Real qz47 (Complex.im (@HSub.hSub Complex Complex Complex qz48 qz49 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz50 (@Nat.cast Complex Complex.instNatCast j))))) qz51) Bool.false 212229501114756749593 4503599627370496000 99752756341323962083629 ep174

noncomputable def ep176 := @Enclosure.Real.IsNear.subLit_ff_p (Complex.im (@HSub.hSub Complex Complex Complex qz48 qz49 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz50 (@Nat.cast Complex Complex.instNatCast j))))) qz51 77736701835024450821 900719925474099200 34184092441323962083629 ep174 2567743767 65536000

noncomputable def ep177 := nat_lit 2781734517011339668265369600

noncomputable def ep178 := nat_lit 627736576000000000000000000

noncomputable def ep179 := @Enclosure.Complex.IsNear.im_isNear (@HSub.hSub Complex Complex Complex qz48 qz49 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz50 (@Nat.cast Complex Complex.instNatCast j)))) Bool.true 24196946743079943727 450359962737049600 150268636256979383427751 ep178 Bool.false 77736701835024450821 900719925474099200

noncomputable def ep180 := @Enclosure.Complex.IsNear.subLitP qz49 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz50 (@Nat.cast Complex Complex.instNatCast j))) Bool.true 21014378132805392727 450359962737049600 146172636250702017667751 ep178 Bool.false 80526939930280934021 900719925474099200 30907292441072867453229

noncomputable def ep181 := nat_lit 54486680167819285690311168330039296

noncomputable def ep182 := nat_lit 21880936338576716833525291418648576

noncomputable abbrev qz489 := (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (2 : Complex))

noncomputable abbrev qz472 := qz489

noncomputable abbrev qz317 := (@HSub.hSub Complex Complex Complex qz469 qz470 qz472)

noncomputable abbrev qz318 := (Complex.log qz470)

noncomputable abbrev qz52 := (@HSub.hSub Complex Complex Complex qz313 (@HMul.hMul Complex Complex Complex qz312 qz317 qz318) qz314)

noncomputable abbrev qz319 := qz472

noncomputable abbrev qz53 := (@HMul.hMul Complex Complex Complex qz312 qz319 ↑(Real.log qz267))

noncomputable abbrev qz473 := qz488

noncomputable abbrev qz320 := qz473

noncomputable abbrev qz54 := qz320

noncomputable abbrev qz55 := (@instHMul Nat instMulNat)

noncomputable abbrev qz474 := (@instHPow Complex Int (@ZPow.toPow Complex (@DivInvMonoid.toZPow Complex Complex.instDivInvMonoid)))

noncomputable abbrev qz321 := qz474

noncomputable abbrev qz56 := qz321

noncomputable abbrev qz57 := qz314

noncomputable abbrev qz322 := (@instHSub Int Int.instSub)

noncomputable abbrev qz58 := qz322

noncomputable abbrev qz323 := (@OfNat.ofNat Int 1 (@instOfNat 1))

noncomputable abbrev qz59 := qz323

noncomputable abbrev qz324 := (@instHMul Int Int.instMul)

noncomputable abbrev qz60 := qz324

noncomputable abbrev qz325 := (@OfNat.ofNat Int 2 (@instOfNat 2))

noncomputable abbrev qz61 := qz325

noncomputable def ep183 := @Enclosure.Complex.IsNear.of_eq qz49 (@HAdd.hAdd Complex Complex Complex qz5 (@HAdd.hAdd Complex Complex Complex qz5 qz52 qz53) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz55 2 k))) (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz48 (@HMul.hMul Complex Complex Complex qz46 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz56 qz57 (@HSub.hSub Int Int Int qz58 qz59 (@HMul.hMul Int Int Int qz60 qz61 (@Nat.cast Int instNatCastInt k)))))) Bool.true 21014378132805392727

noncomputable def ep184 := @Enclosure.Complex.IsNear.addLitP (@HAdd.hAdd Complex Complex Complex qz5 qz52 qz53) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz55 2 k))) (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz48 (@HMul.hMul Complex Complex Complex qz46 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz56 qz57 (@HSub.hSub Int Int Int qz58 qz59 (@HMul.hMul Int Int Int qz60 qz61 (@Nat.cast Int instNatCastInt k))))) Bool.true 21014449904005290327 450359962737049600

noncomputable def ep185 := nat_lit 180512133652353412989802512384

noncomputable def ep186 := nat_lit 864651433618782829281321943040000

noncomputable def ep187 := @ep184 8921656312026090389 38314000000000000000000 Bool.false 402645617486333093017 4503599627370496000 235793750329519557 1915700000000000000000 Bool.false 1368927 8589934592 3 8589934592 Bool.true 5206029381 2147483648000 11409 2147483648000 Bool.true ep185 21014378132805392727 450359962737049600 146172636250702017667751 ep178 Bool.false ep186

noncomputable def ep188 := @Enclosure.Complex.IsNear.addLitP qz52 qz53 Bool.true 21428302644726339927 450359962737049600 8775500000990934139 38314000000000000000000

noncomputable def ep189 := nat_lit 2754405977817781413740544

noncomputable def ep190 := @ep188 Bool.false 402645617486333093017 4503599627370496000 235793750329519557 1915700000000000000000 Bool.false 120447 131072 1 262144 Bool.false 0 1 0 1 Bool.true ep189 21014449904005290327 450359962737049600 8921656312026090389 38314000000000000000000 Bool.false 402645617486333093017 402645617486333093017 4503599627370496000

noncomputable abbrev qz62 := (@HMul.hMul Complex Complex Complex qz312 qz317 qz318)

noncomputable def ep191 := @Enclosure.Complex.IsNear.subLitP qz62 qz57 Bool.true 20414992728567978327 450359962737049600 8775500000990934139 38314000000000000000000 Bool.false 556790321932343059609

noncomputable def ep192 := nat_lit 1610582469945332372068000

noncomputable def ep193 := @ep191 4503599627370496000 235793750329519557 1915700000000000000000 Bool.false 9000 4000 0 1 Bool.false 136908 4000 0 1 Bool.true 85713210578905359708000 21428302644726339927 450359962737049600 8775500000990934139 38314000000000000000000 Bool.false ep192 402645617486333093017 4503599627370496000 235793750329519557 1915700000000000000000

noncomputable abbrev qz63 := qz317

noncomputable abbrev qz64 := qz318

noncomputable def ep194 := @Enclosure.Complex.IsNear.mul qz63 qz64 Bool.true 20414992728567978327 450359962737049600 8775500000990934139 38314000000000000000000 Bool.false 556790321932343059609 4503599627370496000 235793750329519557

noncomputable abbrev qz65 := (Complex.re qz317)

noncomputable abbrev qz66 := (Complex.re qz318)

noncomputable abbrev qz67 := (Complex.im qz317)

noncomputable abbrev qz68 := (Complex.im qz318)

noncomputable def ep195 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 qz65 qz66) (@HMul.hMul Real Real Real qz0 qz67 qz68) 111446934230332869 18014398509481984 87500000134099 15325600000000000000 5800291521081575013 112589990684262400

noncomputable def ep196 := nat_lit 91940953645150132583584805727240192

noncomputable def ep197 := @Enclosure.Real.IsNear.mulLit_ff qz65 qz66 7000 4000 0 1 15920990604333267 4503599627370496 12500000019157 3831400000000000000

noncomputable def ep198 := @Enclosure.Complex.IsNear.re_isNear qz63 Bool.false 7000 4000 0 1 Bool.false 136908 4000 0 1

noncomputable abbrev qz326 := (Enclosure.sfrac Bool.false 136908 4000)

noncomputable abbrev qz69 := qz326

noncomputable def ep199 := @Enclosure.Complex.IsNear.of_eq qz63 (Complex.mk (Enclosure.sfrac Bool.false 7000 4000) qz69) Bool.false 7000 4000 0 1 Bool.false 136908 4000 0

noncomputable abbrev qz327 := (Enclosure.sfrac Bool.false 9000 4000)

noncomputable abbrev qz70 := (Complex.mk qz327 qz326)

noncomputable def ep200 := @Enclosure.Complex.IsNear.of_eq qz64 (Complex.log qz70) Bool.false 15920990604333267 4503599627370496 12500000019157 3831400000000000000 Bool.false 847326894130595 562949953421312 250000000019157 38314000000000000000

noncomputable def ep201 := nat_lit 23051339978007009906919893655738620917514240

noncomputable def ep202 := nat_lit 37032879697222267227740796621164265340928

noncomputable def ep203 := nat_lit 106475665571606223424683475305879502848

noncomputable def ep204 := BSN.log_dyadic_bound 2440800464 35208800464 3 2 ep201 524288 153256 ep202 ep203 72807 37649600928 32768000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 2440800464) (BSN.artanhQ 35208800464) 0 2 ep202 ep201 ep203 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz71 := (Enclosure.sfrac Bool.false 1 2)

noncomputable abbrev qz328 := (Real.log (Enclosure.sfrac Bool.false 18824800464 16000000))

noncomputable abbrev qz329 := (Enclosure.Real.IsNear.const Bool.false 1 2)

noncomputable abbrev qz330 := (@Nat.cast Real Real.instNatCast 16000000)

noncomputable def ep205 := @Enclosure.Real.IsNear.mulLit_ff qz71 qz328 1 2 0 1 15920990604333267 2251799813685248 12500000019157 1915700000000000000 15920990604333267 4503599627370496 12500000019157 3831400000000000000 qz329 (BSN.isNear_log_sfrac 18824800464 16000000 15920990604333267 2251799813685248 12500000019157 1915700000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 18824800464) qz330)) Bool.false 133554949151434878222336 18889465931478580854784 1000000001532560 153256000000000000000 15920990604333267 2251799813685248 12500000019157 1915700000000000000 (BSN.log_rat_reduce_isNear 18824800464 16000000 10 37649600928 32768000000 72807 524288 24973259072661432 36028797018963968 153256 1000000000000000 rfl rfl rfl rfl (ep204 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep206 := BSN.arctan_dyadic_bound_f 9000 136908 1 0 524288 153256 0 1 1 0 1 1 34415 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 9000) (BSN.arctanEvenQ 136908) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 9000) (BSN.arctanOddQ 136908) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz72 := (@HMul.hMul Real Real Real qz263 (Enclosure.sfrac Bool.false 1 2) Real.pi)

noncomputable abbrev qz73 := (@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 2) Real.pi 1 2 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 qz329 BSN.pi_near_15 rfl)

noncomputable abbrev qz331 := (Real.arctan (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 9000) (@Nat.cast Real Real.instNatCast 136908)))

noncomputable def ep207 := @Enclosure.Real.IsNear.subLit_ff_p qz72 qz331 884279719003555 562949953421312 1 2000000000000000 34415 524288 1 153256 444243322669941391360 847326894130595 562949953421312 250000000019157 38314000000000000000 qz73 (ep206 rfl) rfl rfl

noncomputable abbrev qz332 := (Real.arctan (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 136908) (@Nat.cast Real Real.instNatCast 9000)))

noncomputable def ep208 := @Enclosure.Complex.IsNear.re_isNear qz64 Bool.false 15920990604333267 4503599627370496 12500000019157 3831400000000000000 Bool.false 847326894130595 562949953421312 250000000019157 38314000000000000000 (ep200 (@congrArg Complex Complex qz57 qz70 Complex.log (BSN.w_shift_mk qz17 Bool.false 68454 1000 2 qz18 rfl)) (@Enclosure.Complex.IsNear.of_parts (Complex.log qz70) Bool.false 15920990604333267 4503599627370496 12500000019157 3831400000000000000 Bool.false 847326894130595 562949953421312 250000000019157 38314000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re (Complex.log qz70)) (@HMul.hMul Real Real Real qz0 qz71 qz328) Bool.false 15920990604333267 4503599627370496 12500000019157 3831400000000000000 (Enclosure.clog_re_eq 9000 136908 4000 18824800464 16000000 rfl rfl rfl) (ep205 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im (Complex.log qz70)) qz332 Bool.false 847326894130595 562949953421312 250000000019157 38314000000000000000 (Enclosure.clog_im_eq 9000 136908 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz332 (@HSub.hSub Real Real Real qz47 qz72 qz331) Bool.false 847326894130595 562949953421312 250000000019157 38314000000000000000 (BSN.arctan_recip 136908 9000 rfl rfl) ep207))))

noncomputable def ep209 := @Enclosure.Real.IsNear.mulLit_ff qz67 qz68 136908 4000 0 1 847326894130595 562949953421312 250000000019157 38314000000000000000

noncomputable def ep210 := @Enclosure.Complex.IsNear.im_isNear qz63 Bool.false 7000 4000 0 1 Bool.false 136908 4000 0 1

noncomputable def ep211 := @Enclosure.Complex.IsNear.im_isNear qz64 Bool.false 15920990604333267 4503599627370496 12500000019157 3831400000000000000 Bool.false 847326894130595 562949953421312 250000000019157 38314000000000000000 (ep200 (@congrArg Complex Complex qz57 qz70 Complex.log (BSN.w_shift_mk qz17 Bool.false 68454 1000 2 qz18 rfl)) (@Enclosure.Complex.IsNear.of_parts (Complex.log qz70) Bool.false 15920990604333267 4503599627370496 12500000019157 3831400000000000000 Bool.false 847326894130595 562949953421312 250000000019157 38314000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re (Complex.log qz70)) (@HMul.hMul Real Real Real qz0 qz71 qz328) Bool.false 15920990604333267 4503599627370496 12500000019157 3831400000000000000 (Enclosure.clog_re_eq 9000 136908 4000 18824800464 16000000 rfl rfl rfl) (ep205 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im (Complex.log qz70)) qz332 Bool.false 847326894130595 562949953421312 250000000019157 38314000000000000000 (Enclosure.clog_im_eq 9000 136908 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz332 (@HSub.hSub Real Real Real qz47 qz72 qz331) Bool.false 847326894130595 562949953421312 250000000019157 38314000000000000000 (BSN.arctan_recip 136908 9000 rfl rfl) ep207))))

noncomputable abbrev qz333 := (Enclosure.Real.IsNear.const Bool.false 136908 4000)

noncomputable abbrev qz74 := (@ep199 1 (BSN.w_sub_half_mk qz276 Bool.false 68454 1000 2 qz277 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7000 4000) qz326 Bool.false 7000 4000 0 1 Bool.false 136908 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 7000 4000) qz333))

noncomputable def ep212 := @ep195 8556750000655686639 38314000000000000000000 ep196 20414992728567978327 450359962737049600 8775500000990934139 38314000000000000000000 (@ep197 111446934230332869 18014398509481984 87500000134099 15325600000000000000 (ep198 qz74) ep208 rfl) (@ep209 5800291521081575013 112589990684262400 8556750000655686639 38314000000000000000000 (ep210 qz74) ep211 rfl) rfl

noncomputable def ep213 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz65 qz68) (@HMul.hMul Real Real Real qz0 qz67 qz66) 5931288258914165 2251799813685248 1750000000134099 153256000000000000000 544927745414514729609 4503599627370496000

noncomputable def ep214 := nat_lit 1253780343188999354802888270027948032

noncomputable def ep215 := @Enclosure.Real.IsNear.mulLit_ff qz65 qz68 7000 4000 0 1 847326894130595 562949953421312 250000000019157 38314000000000000000

noncomputable def ep216 := @Enclosure.Real.IsNear.mulLit_ff qz67 qz66 136908 4000 0 1 15920990604333267 4503599627370496 12500000019157 3831400000000000000

noncomputable def ep217 := @ep213 427837500655686639 3831400000000000000000 ep214 556790321932343059609 4503599627370496000 235793750329519557 1915700000000000000000 (@ep215 5931288258914165 2251799813685248 1750000000134099 153256000000000000000 (ep198 qz74) ep211 rfl) (@ep216 544927745414514729609 4503599627370496000 427837500655686639 3831400000000000000000 (ep210 qz74) ep208 rfl) rfl

noncomputable def ep218 := @Enclosure.Complex.IsNear.of_eq qz57 qz70 Bool.false 9000 4000 0 1 Bool.false 136908 4000 0 1 (BSN.w_shift_mk qz17 Bool.false 68454 1000 2 qz18 rfl)

noncomputable abbrev qz334 := (ep218 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 9000 4000) (Enclosure.sfrac Bool.false 136908 4000) Bool.false 9000 4000 0 1 Bool.false 136908 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 9000 4000) (Enclosure.Real.IsNear.const Bool.false 136908 4000)))

noncomputable abbrev qz75 := qz334

noncomputable def ep219 := ep193 (@ep194 1915700000000000000000 (ep212 rfl) (ep217 rfl)) qz75 rfl rfl rfl rfl rfl rfl

noncomputable abbrev qz76 := qz319

noncomputable def ep220 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re qz76) (Complex.re ↑qz3)) (@HMul.hMul Real Real Real qz0 (Complex.im qz76) (Complex.im ↑qz3)) 120447 131072 1 262144 0 1 0 1 120447 120447

noncomputable def ep221 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re qz76) (Complex.re ↑qz3) 1 2 0 1 120447 65536 1 131072 120447 131072 1 262144

noncomputable abbrev qz77 := (@Enclosure.Complex.IsNear.of_eq qz319 (Complex.mk (Enclosure.sfrac Bool.false 1 2) qz274) Bool.false 1 2 0 1 Bool.false 0 1 0 1 BSN.half_c_mk (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 2) qz274 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz329 qz286))

noncomputable def ep222 := ep221 (@Enclosure.Complex.IsNear.re_isNear qz76 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz77) (@Enclosure.Real.IsNear.of_eq (Complex.re ↑qz3) qz3 Bool.false 120447 65536 1 131072 (Complex.ofReal_re qz3) EMRow17.d4)

noncomputable def ep223 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz76) (Complex.im ↑qz3) 0 1 0 1 0 1 0 1 0 1 0 1

noncomputable def ep224 := ep223 (@Enclosure.Complex.IsNear.im_isNear qz76 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz77) (@Enclosure.Real.IsNear.of_eq (Complex.im ↑qz3) qz14 Bool.false 0 1 0 1 (@Eq.trans Real (Complex.im ↑qz3) (0 : Real) qz14 (Complex.ofReal_im qz3) Enclosure.sfrac_zero_eq) qz24)

noncomputable def ep225 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re qz76) (Complex.im ↑qz3)) (@HMul.hMul Real Real Real qz0 (Complex.im qz76) (Complex.re ↑qz3)) 0 1 0 1 0 1 0 1 0 0

noncomputable def ep226 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re qz76) (Complex.im ↑qz3) 1 2 0 1 0 1 0 1 0 1 0 1

noncomputable def ep227 := ep226 (@Enclosure.Complex.IsNear.re_isNear qz76 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz77) (@Enclosure.Real.IsNear.of_eq (Complex.im ↑qz3) qz14 Bool.false 0 1 0 1 (@Eq.trans Real (Complex.im ↑qz3) (0 : Real) qz14 (Complex.ofReal_im qz3) Enclosure.sfrac_zero_eq) qz24)

noncomputable def ep228 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz76) (Complex.re ↑qz3) 0 1 0 1 120447 65536 1 131072 0 1 0 1

noncomputable def ep229 := ep228 (@Enclosure.Complex.IsNear.im_isNear qz76 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz77) (@Enclosure.Real.IsNear.of_eq (Complex.re ↑qz3) qz3 Bool.false 120447 65536 1 131072 (Complex.ofReal_re qz3) EMRow17.d4)

noncomputable def ep230 := @ep190 235793750329519557 1915700000000000000000 (ep219 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@Enclosure.Complex.IsNear.mul qz76 (↑qz3) Bool.false 120447 131072 1 262144 Bool.false 0 1 0 1 (@ep220 131072 1 262144 (ep222 rfl) (ep224 rfl) rfl rfl) (@ep225 1 0 1 (ep227 rfl) (ep229 rfl) rfl rfl))

noncomputable abbrev qz78 := (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 1)

noncomputable abbrev qz335 := (@Nat.cast Complex Complex.instNatCast 1)

noncomputable abbrev qz79 := (@HMul.hMul Complex Complex Complex qz312 (@HMul.hMul Complex Complex Complex qz312 (2 : Complex) qz335) (@HSub.hSub Complex Complex Complex qz313 (@HMul.hMul Complex Complex Complex qz312 (2 : Complex) qz335) (1 : Complex)))

noncomputable abbrev qz336 := (@HPow.hPow Complex Int Complex qz474 qz470 (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) (@OfNat.ofNat Int 1 (@instOfNat 1)) (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (@OfNat.ofNat Int 2 (@instOfNat 2)) (@Nat.cast Int instNatCastInt 1))))

noncomputable abbrev qz80 := qz336

noncomputable def ep231 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz55 2 k))) (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz48 (@HMul.hMul Complex Complex Complex qz46 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz56 qz57 (@HSub.hSub Int Int Int qz58 qz59 (@HMul.hMul Int Int Int qz60 qz61 (@Nat.cast Int instNatCastInt k))))) (@HAdd.hAdd Complex Complex Complex qz5 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz55 2 k))) (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz48 (@HMul.hMul Complex Complex Complex qz46 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz56 qz57 (@HSub.hSub Int Int Int qz58 qz59 (@HMul.hMul Int Int Int qz60 qz61 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 (@Rat.cast Complex Complex.instRatCast (bernoulli qz78)) qz79) qz80)) Bool.false 1368927 8589934592 3 8589934592

noncomputable def ep232 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz55 2 k))) (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz48 (@HMul.hMul Complex Complex Complex qz46 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz56 qz57 (@HSub.hSub Int Int Int qz58 qz59 (@HMul.hMul Int Int Int qz60 qz61 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 (@Rat.cast Complex Complex.instRatCast (bernoulli qz78)) qz79) qz80) Bool.false 0 1 0 1 Bool.false

noncomputable def ep233 := @ep232 0 1 0 1 Bool.false 1368927 8589934592 3 8589934592 Bool.true 5206029381 2147483648000 11409 2147483648000 Bool.false 1368927 1368927 8589934592 3 8589934592 Bool.true 5206029381 5206029381 2147483648000 11409

noncomputable def ep234 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz55 2 k))) (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz48 (@HMul.hMul Complex Complex Complex qz46 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz56 qz57 (@HSub.hSub Int Int Int qz58 qz59 (@HMul.hMul Int Int Int qz60 qz61 (@Nat.cast Int instNatCastInt k))))) (Complex.mk qz14 qz14) Bool.false 0 1 0 1 Bool.false

noncomputable def ep235 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz54 (@Rat.cast Complex Complex.instRatCast (bernoulli qz78)) qz79) qz80 Bool.false 1368927 8589934592 3 8589934592 Bool.true 5206029381 2147483648000 11409 2147483648000

noncomputable abbrev qz81 := (Complex.re qz336)

noncomputable abbrev qz82 := (Complex.im qz336)

noncomputable def ep236 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz54 (@Rat.cast Complex Complex.instRatCast (bernoulli qz78)) qz79)) qz81) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz54 (@Rat.cast Complex Complex.instRatCast (bernoulli qz78)) qz79)) qz82) 1368927 8589934592 3 8589934592 0 1 0

noncomputable def ep237 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz54 (@Rat.cast Complex Complex.instRatCast (bernoulli qz78)) qz79)) qz81 1 12 0 1 4106781 2147483648 9 2147483648 1368927

noncomputable def ep238 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz54 (@Rat.cast Complex Complex.instRatCast (bernoulli qz78)) qz79) (Complex.mk (Enclosure.sfrac Bool.false 1 12) qz14) Bool.false 1 12 0 1 Bool.false 0 1 0 1

noncomputable abbrev qz337 := (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 12) qz14 Bool.false 1 12 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 12) qz24)

noncomputable def ep239 := @Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz54 (@Rat.cast Complex Complex.instRatCast (bernoulli qz78)) qz79) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (ep238 (BSN.stirling_coeff_mk 1 1 6 Bool.false BSN.bern_real_1 rfl rfl) qz337)

noncomputable def ep240 := @Enclosure.Complex.IsNear.re_isNear qz80 Bool.false 4106781 2147483648 9 2147483648 Bool.true 15618088143 536870912000 34227 536870912000

noncomputable abbrev qz475 := (@instHPow Complex Nat (@NPow.toPow Complex (@Monoid.toNPow Complex (@Semiring.toMonoid Complex Complex.instSemiring))))

noncomputable abbrev qz338 := (@HPow.hPow Complex Nat Complex qz475 qz470 1)

noncomputable abbrev qz83 := (@Inv.inv Complex Complex.instInv qz338)

noncomputable def ep241 := @Enclosure.Complex.IsNear.of_eq qz80 qz83 Bool.false 4106781 2147483648 9 2147483648 Bool.true 15618088143 536870912000 34227

noncomputable def ep242 := @Enclosure.Complex.IsNear.of_parts qz83 Bool.false 4106781 2147483648 9 2147483648 Bool.true 15618088143 536870912000 34227

noncomputable abbrev qz84 := (Complex.re qz338)

noncomputable abbrev qz85 := (@MonoidWithZeroHom Complex Real (@instMulZeroOneClassOfSemiring Complex Complex.instSemiring) (@instMulZeroOneClassOfSemiring Real Real.semiring))

noncomputable abbrev qz86 := (@MonoidWithZeroHom.funLike Complex Real (@instMulZeroOneClassOfSemiring Complex Complex.instSemiring) (@instMulZeroOneClassOfSemiring Real Real.semiring))

noncomputable abbrev qz87 := qz338

noncomputable def ep243 := @Enclosure.Real.IsNear.mulLit_ff qz84 (@Inv.inv Real Real.instInv (@DFunLike.coe qz85 Complex (fun (x : Complex) => Real) qz86 Complex.normSq qz87)) 9000 4000 0 1 456309 536870912 1 536870912

noncomputable def ep244 := @Enclosure.Complex.IsNear.re_isNear qz87 Bool.false 9000 4000 0 1 Bool.false 136908 4000 0 1

noncomputable def ep245 := @Enclosure.Complex.IsNear.of_eq qz87 qz57 Bool.false 9000 4000 0 1 Bool.false 136908 4000 0

noncomputable def ep246 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (@DFunLike.coe qz85 Complex (fun (x : Complex) => Real) qz86 Complex.normSq qz87)) Bool.false 456309 536870912 1 536870912 456309 536870912 1

noncomputable abbrev qz88 := (Complex.im qz338)

noncomputable abbrev qz339 := (@instHAdd Real Real.instAdd)

noncomputable def ep247 := @Enclosure.Real.IsNear.of_eq (@DFunLike.coe qz85 Complex (fun (x : Complex) => Real) qz86 Complex.normSq qz87) (@HAdd.hAdd Real Real Real qz339 (@HMul.hMul Real Real Real qz0 qz84 qz84) (@HMul.hMul Real Real Real qz0 qz88 qz88)) Bool.false 1176550029 1000000 0 1

noncomputable def ep248 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz84 qz84) (@HMul.hMul Real Real Real qz0 qz88 qz88) 81 16 0 1 1171487529 1000000

noncomputable def ep249 := @Enclosure.Real.IsNear.mulLit_ff qz84 qz84 9000 4000 0 1 9000 4000 0 1

noncomputable def ep250 := @Enclosure.Real.IsNear.mulLit_ff qz88 qz88 136908 4000 0 1 136908 4000 0 1

noncomputable def ep251 := @Enclosure.Complex.IsNear.im_isNear qz87 Bool.false 9000 4000 0 1 Bool.false 136908 4000 0 1

noncomputable abbrev qz89 := (ep244 (@ep245 1 (BSN.pow_one_c qz314) qz334))

noncomputable abbrev qz90 := (ep251 (@ep245 1 (BSN.pow_one_c qz314) qz334))

noncomputable def ep252 := @ep248 0 1 18824800464 1176550029 1000000 0 1 (@ep249 81 16 0 1 qz89 qz89 rfl) (@ep250 1171487529 1000000 0 1 qz90 qz90 rfl)

noncomputable def ep253 := @Enclosure.Real.IsNear.inv_image (@DFunLike.coe qz85 Complex (fun (x : Complex) => Real) qz86 Complex.normSq qz87) 1176550029 1000000 0 1 228154 228155 268435456 (ep247 (Enclosure.Complex.normSq_eq_mul_add_mul qz87) (ep252 rfl rfl)) rfl

noncomputable def ep254 := @Enclosure.Real.IsNear.of_eq (Complex.re qz83) (@HMul.hMul Real Real Real qz0 qz84 (@Inv.inv Real Real.instInv (@DFunLike.coe qz85 Complex (fun (x : Complex) => Real) qz86 Complex.normSq qz87))) Bool.false 4106781 2147483648 9 2147483648 (Enclosure.Complex.inv_re_eq_mul qz87) (@ep243 4106781 2147483648 9 2147483648 qz89 (@ep246 536870912 (ep253 rfl rfl rfl rfl rfl) rfl) rfl)

noncomputable def ep255 := @Enclosure.Real.IsNear.of_eq (Complex.im qz83) (@HMul.hMul Real Real Real qz0 (@Neg.neg Real Real.instNeg qz88) (@Inv.inv Real Real.instInv (@DFunLike.coe qz85 Complex (fun (x : Complex) => Real) qz86 Complex.normSq qz87))) Bool.true 15618088143 536870912000 34227 536870912000 (Enclosure.Complex.inv_im_eq_mul qz87)

noncomputable def ep256 := @Enclosure.Real.IsNear.mulLit_tf (@Neg.neg Real Real.instNeg qz88) (@Inv.inv Real Real.instInv (@DFunLike.coe qz85 Complex (fun (x : Complex) => Real) qz86 Complex.normSq qz87)) 136908 4000 0 1 456309 536870912 1

noncomputable def ep257 := @ep256 536870912 15618088143 536870912000 34227 536870912000 (@Enclosure.Real.IsNear.neg qz88 Bool.false 136908 4000 0 1 qz90) (@ep246 536870912 (ep253 rfl rfl rfl rfl rfl) rfl) rfl

noncomputable def ep258 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz54 (@Rat.cast Complex Complex.instRatCast (bernoulli qz78)) qz79)) qz82 0 1 0 1 15618088143 536870912000 34227 536870912000 0

noncomputable def ep259 := @Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz54 (@Rat.cast Complex Complex.instRatCast (bernoulli qz78)) qz79) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (ep238 (BSN.stirling_coeff_mk 1 1 6 Bool.false BSN.bern_real_1 rfl rfl) qz337)

noncomputable def ep260 := @Enclosure.Complex.IsNear.im_isNear qz80 Bool.false 4106781 2147483648 9 2147483648 Bool.true 15618088143 536870912000 34227 536870912000

noncomputable abbrev qz91 := (@ep241 536870912000 (BSN.zpow_one_sub_two_mul qz314 1 1 rfl rfl) (@ep242 536870912000 ep254 (ep255 ep257)))

noncomputable def ep261 := @ep236 1 1368927 1368927 8589934592 3 8589934592 (@ep237 8589934592 3 8589934592 ep239 (ep240 qz91) rfl) (@ep258 1 0 1 ep259 (ep260 qz91) rfl) rfl

noncomputable def ep262 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz54 (@Rat.cast Complex Complex.instRatCast (bernoulli qz78)) qz79)) qz82) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz54 (@Rat.cast Complex Complex.instRatCast (bernoulli qz78)) qz79)) qz81) 5206029381 2147483648000 11409 2147483648000 0 1 0

noncomputable def ep263 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HDiv.hDiv Complex Complex Complex qz54 (@Rat.cast Complex Complex.instRatCast (bernoulli qz78)) qz79)) qz82 1 12 0 1 15618088143 536870912000 34227 536870912000 5206029381

noncomputable def ep264 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz54 (@Rat.cast Complex Complex.instRatCast (bernoulli qz78)) qz79)) qz81 0 1 0 1 4106781 2147483648 9 2147483648 0

noncomputable def ep265 := @ep262 1 5206029381 5206029381 2147483648000 11409 2147483648000 (@ep263 2147483648000 11409 2147483648000 ep239 (ep260 qz91) rfl) (@ep264 1 0 1 ep259 (ep240 qz91) rfl) rfl

noncomputable abbrev qz92 := (@Enclosure.Complex.IsNear.mk qz274 qz274 Bool.false 0 1 0 1 Bool.false 0 1 0 1 qz286 qz286)

noncomputable def ep266 := @ep233 2147483648000 (@ep234 0 1 0 1 (BSN.stirling_sum_base qz57) qz92) (ep235 (ep261 rfl) (ep265 rfl)) rfl rfl rfl rfl rfl

noncomputable def ep267 := @ep187 80526939930280934021 900719925474099200 30907292441072867453229 ep174 (ep230 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep231 Bool.true 5206029381 2147483648000 11409 2147483648000 (BSN.stirling_sum_succ qz57 0 1 rfl) (ep266 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl

noncomputable def ep268 := @Enclosure.Complex.IsNear.of_eq (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz50 (@Nat.cast Complex Complex.instNatCast j))) (BSN.logSumC qz17 2) Bool.false 15912843051372755 2251799813685248 12500000019157 1915700000000000000 Bool.false 871949404767651 281474976710656

noncomputable abbrev qz93 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz269 qz315 qz335))

noncomputable def ep269 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz17 2) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.logSumC qz17 1) qz93) Bool.false 15912843051372755 2251799813685248 12500000019157 1915700000000000000 Bool.false 871949404767651 281474976710656 250000000019157 19157000000000000000

noncomputable def ep270 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz17 1) qz93 Bool.false 15911404237328595 4503599627370496 12500000019157 3831400000000000000 Bool.false 880168361559459 562949953421312 250000000019157 38314000000000000000 Bool.false

noncomputable def ep271 := nat_lit 143330148073135051910247570472960

noncomputable def ep272 := nat_lit 981727753599379707983743156224

noncomputable abbrev qz94 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz269 qz315 (@Nat.cast Complex Complex.instNatCast 0)))

noncomputable def ep273 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz17 1) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.logSumC qz17 0) qz94) Bool.false 15911404237328595 4503599627370496 12500000019157 3831400000000000000 Bool.false 880168361559459 562949953421312 250000000019157 38314000000000000000

noncomputable def ep274 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz17 0) qz94 Bool.false 0 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable abbrev qz340 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz69))

noncomputable def ep275 := @Enclosure.Complex.IsNear.of_eq qz94 qz340 Bool.false 15911404237328595 4503599627370496 12500000019157 3831400000000000000 Bool.false 880168361559459 562949953421312 250000000019157 38314000000000000000

noncomputable def ep276 := nat_lit 22842547683866237241398680883111369717514240

noncomputable def ep277 := nat_lit 34481844115873700844582703059963625340928

noncomputable def ep278 := nat_lit 93187654775584986757793589855639502848

noncomputable def ep279 := BSN.log_dyadic_bound 2360800464 35128800464 3 2 ep276 524288 153256 ep277 ep278 70575 37489600928 32768000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 2360800464) (BSN.artanhQ 35128800464) 0 2 ep277 ep276 ep278 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep280 := @Enclosure.Real.IsNear.mulLit_ff qz71 (Real.log (Enclosure.sfrac Bool.false 18744800464 16000000)) 1 2 0 1 15911404237328595 2251799813685248 12500000019157 1915700000000000000 15911404237328595 4503599627370496 12500000019157 3831400000000000000 qz329 (BSN.isNear_log_sfrac 18744800464 16000000 15911404237328595 2251799813685248 12500000019157 1915700000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 18744800464) qz330)) Bool.false 133474532876488550645760 18889465931478580854784 1000000001532560 153256000000000000000 15911404237328595 2251799813685248 12500000019157 1915700000000000000 (BSN.log_rat_reduce_isNear 18744800464 16000000 10 37489600928 32768000000 70575 524288 24973259072661432 36028797018963968 153256 1000000000000000 rfl rfl rfl rfl (ep279 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep281 := BSN.arctan_dyadic_bound_f 1000 136908 1 0 524288 153256 0 1 1 0 1 1 3829 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 136908) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 136908) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz341 := (@Nat.cast Real Real.instNatCast 1000)

noncomputable abbrev qz342 := (@Nat.cast Real Real.instNatCast 136908)

noncomputable def ep282 := @Enclosure.Real.IsNear.subLit_ff_p qz72 (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz341 qz342)) 884279719003555 562949953421312 1 2000000000000000 3829 524288 1 153256 461461709945285640192 880168361559459 562949953421312 250000000019157 38314000000000000000 qz73 (ep281 rfl) rfl rfl

noncomputable abbrev qz95 := (@HAdd.hAdd Complex Complex Complex qz269 qz315 (@Nat.cast Complex Complex.instNatCast 0))

noncomputable abbrev qz343 := (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz69)

noncomputable def ep283 := @ep274 15911404237328595 4503599627370496 12500000019157 3831400000000000000 Bool.false 880168361559459 562949953421312 250000000019157 38314000000000000000 Bool.false 15911404237328595 15911404237328595 4503599627370496 12500000019157 3831400000000000000 Bool.false 880168361559459 880168361559459 562949953421312 250000000019157 38314000000000000000 (@Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz17 0) (Complex.mk qz14 qz14) Bool.false 0 1 0 1 Bool.false 0 1 0 1 (BSN.log_sum_c_base qz17) qz92) (ep275 (@congrArg Complex Complex qz95 qz343 Complex.log (BSN.w_shift_mk qz17 Bool.false 68454 1000 0 qz18 rfl)) (@Enclosure.Complex.IsNear.of_parts qz340 Bool.false 15911404237328595 4503599627370496 12500000019157 3831400000000000000 Bool.false 880168361559459 562949953421312 250000000019157 38314000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz340) (@HMul.hMul Real Real Real qz0 qz71 (Real.log (Enclosure.sfrac Bool.false 18744800464 16000000))) Bool.false 15911404237328595 4503599627370496 12500000019157 3831400000000000000 (Enclosure.clog_re_eq 1000 136908 4000 18744800464 16000000 rfl rfl rfl) (ep280 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz340) (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz342 qz341)) Bool.false 880168361559459 562949953421312 250000000019157 38314000000000000000 (Enclosure.clog_im_eq 1000 136908 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz342 qz341)) (@HSub.hSub Real Real Real qz47 qz72 (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz341 qz342))) Bool.false 880168361559459 562949953421312 250000000019157 38314000000000000000 (BSN.arctan_recip 136908 1000 rfl rfl) ep282)))) rfl rfl

noncomputable abbrev qz344 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz69))

noncomputable def ep284 := @Enclosure.Complex.IsNear.of_eq qz93 qz344 Bool.false 15914281865416915 4503599627370496 12500000019157 3831400000000000000 Bool.false 863730447975843 562949953421312 250000000019157 38314000000000000000

noncomputable def ep285 := nat_lit 22905035808733370960551818510739545077514240

noncomputable def ep286 := nat_lit 35236404135321276264284155576323817340928

noncomputable def ep287 := nat_lit 97035231166096224280619723490711502848

noncomputable def ep288 := BSN.log_dyadic_bound 2384800464 35152800464 3 2 ep285 524288 153256 ep286 ep287 71245 37537600928 32768000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 2384800464) (BSN.artanhQ 35152800464) 0 2 ep286 ep285 ep287 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep289 := @Enclosure.Real.IsNear.mulLit_ff qz71 (Real.log (Enclosure.sfrac Bool.false 18768800464 16000000)) 1 2 0 1 15914281865416915 2251799813685248 12500000019157 1915700000000000000 15914281865416915 4503599627370496 12500000019157 3831400000000000000 qz329 (BSN.isNear_log_sfrac 18768800464 16000000 15914281865416915 2251799813685248 12500000019157 1915700000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 18768800464) qz330)) Bool.false 133498672170491256504320 18889465931478580854784 1000000001532560 153256000000000000000 15914281865416915 2251799813685248 12500000019157 1915700000000000000 (BSN.log_rat_reduce_isNear 18768800464 16000000 10 37537600928 32768000000 71245 524288 24973259072661432 36028797018963968 153256 1000000000000000 rfl rfl rfl rfl (ep288 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep290 := BSN.arctan_dyadic_bound_f 5000 136908 1 0 524288 153256 0 1 1 0 1 1 19138 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 5000) (BSN.arctanEvenQ 136908) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 5000) (BSN.arctanOddQ 136908) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz345 := (@Nat.cast Real Real.instNatCast 5000)

noncomputable def ep291 := @Enclosure.Real.IsNear.subLit_ff_p qz72 (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz345 qz342)) 884279719003555 562949953421312 1 2000000000000000 19138 524288 1 153256 452843509108358774784 863730447975843 562949953421312 250000000019157 38314000000000000000 qz73 (ep290 rfl) rfl rfl

noncomputable abbrev qz96 := (@HAdd.hAdd Complex Complex Complex qz269 qz315 qz335)

noncomputable abbrev qz346 := (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz69)

noncomputable def ep292 := @ep270 15914281865416915 4503599627370496 12500000019157 3831400000000000000 Bool.false 863730447975843 562949953421312 250000000019157 38314000000000000000 Bool.false ep271 15912843051372755 2251799813685248 12500000019157 1915700000000000000 Bool.false ep272 871949404767651 281474976710656 250000000019157 19157000000000000000 (ep273 (BSN.log_sum_c_succ qz17 0 1 rfl) (ep283 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep284 (@congrArg Complex Complex qz96 qz346 Complex.log (BSN.w_shift_mk qz17 Bool.false 68454 1000 1 qz18 rfl)) (@Enclosure.Complex.IsNear.of_parts qz344 Bool.false 15914281865416915 4503599627370496 12500000019157 3831400000000000000 Bool.false 863730447975843 562949953421312 250000000019157 38314000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz344) (@HMul.hMul Real Real Real qz0 qz71 (Real.log (Enclosure.sfrac Bool.false 18768800464 16000000))) Bool.false 15914281865416915 4503599627370496 12500000019157 3831400000000000000 (Enclosure.clog_re_eq 5000 136908 4000 18768800464 16000000 rfl rfl rfl) (ep289 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz344) (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz342 qz345)) Bool.false 863730447975843 562949953421312 250000000019157 38314000000000000000 (Enclosure.clog_im_eq 5000 136908 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz342 qz345)) (@HSub.hSub Real Real Real qz47 qz72 (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz345 qz342))) Bool.false 863730447975843 562949953421312 250000000019157 38314000000000000000 (BSN.arctan_recip 136908 5000 rfl rfl) ep291)))) rfl rfl

noncomputable def ep293 := @ep180 ep174 Bool.false 15912843051372755 2251799813685248 12500000019157 1915700000000000000 Bool.false 871949404767651 281474976710656 250000000019157 19157000000000000000 Bool.true ep181 24196946743079943727 450359962737049600 150268636256979383427751 ep178 Bool.false ep182 77736701835024450821 900719925474099200 34184092441323962083629 ep174 (@ep183 450359962737049600 146172636250702017667751 ep178 Bool.false 80526939930280934021 900719925474099200 30907292441072867453229 ep174 (BSN.logGammaStirling_unfold 1 qz57) (ep267 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (@ep268 250000000019157 19157000000000000000 (BSN.log_sum_c_eq qz17 2) (ep269 (BSN.log_sum_c_succ qz17 1 2 rfl) (ep292 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)))

noncomputable abbrev qz97 := (@HDiv.hDiv Real Real Real qz266 qz276 (2 : Real))

noncomputable def ep294 := @Enclosure.Real.IsNear.mulLit_ff qz97 (Real.log Real.pi) 68454 2000 0 1 75021 65536 1 131072 2567743767 65536000 34227 131072000 (@Enclosure.Real.IsNear.of_eq qz97 (Enclosure.sfrac Bool.false 68454 2000) Bool.false 68454 2000 0 1 (BSN.t_half_eq qz17 Bool.false 68454 1000 qz18) (Enclosure.Real.IsNear.const Bool.false 68454 2000)) EMRow17.d5 rfl

noncomputable def ep295 := @ep176 34227 131072000 ep177 212229501114756749593 4503599627370496000 99752756341323962083629 ep174 (@ep179 34184092441323962083629 ep174 (ep293 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) ep294 rfl rfl

noncomputable def ep296 := BSN.cos_dyadic_bound_f 563328 1073741824 1 0 524288 153406 0 1 1 0 1 1 524287 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 563328) qz278 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 563328) qz279 0 0 rfl) rfl rfl

noncomputable def ep297 := @ep173 524288 Bool.true 524287 524288 1 76628 (@ep175 24706765 524288 209 524288 ep295 rfl) (Enclosure.sfrac_false_div 24706765 524288) (BSN.cos_reduce2 qz316 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 39640686905922682880) qz23) 226375608064910080 72057594037927936 Bool.false 524287 524288 7 1000000000000000 153256 76628 (BSN.sin_reduce_arg_pos_rat_q2 24706765 524288 226375608064910080 72057594037927936 7 39640686905922682880 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 524287 524288 39640686905922682880 75557863725914323419136 563328 1073741824 153406 153256 (ep296 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep298 := nat_lit 4508465077923835019264000

noncomputable def ep299 := nat_lit 49918239340534547985864079

noncomputable def ep300 := nat_lit 10796083187223363433005056000

noncomputable abbrev qz98 := qz270

noncomputable abbrev qz99 := qz271

noncomputable abbrev qz347 := (@HPow.hPow Complex Complex Complex qz463 (@Nat.cast Complex Complex.instNatCast 14) qz464)

noncomputable abbrev qz100 := qz347

noncomputable abbrev qz348 := (@Nat.cast Complex Complex.instNatCast 14)

noncomputable abbrev qz101 := (@HAdd.hAdd Complex Complex Complex qz269 (@HDiv.hDiv Complex Complex Complex qz320 qz348 (@HSub.hSub Complex Complex Complex qz313 qz268 (1 : Complex))) qz319)

noncomputable abbrev qz102 := (@instHSub Nat instSubNat)

noncomputable abbrev qz349 := qz475

noncomputable abbrev qz103 := qz349

noncomputable abbrev qz104 := qz348

noncomputable def ep301 := @Enclosure.Complex.IsNear.of_eq (zetaApproximant qz6 1 14) (@HAdd.hAdd Complex Complex Complex qz5 (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 14, @HPow.hPow Complex Complex Complex qz98 (@Nat.cast Complex Complex.instNatCast n) qz99) (@HMul.hMul Complex Complex Complex qz46 qz100 (@HAdd.hAdd Complex Complex Complex qz5 qz101 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz55 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz55 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz55 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz103 qz104 (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz55 2 k) 1))))))) Bool.false ep168 ep169 ep170

noncomputable def ep302 := @Enclosure.Complex.IsNear.addLitP (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 14, @HPow.hPow Complex Complex Complex qz98 (@Nat.cast Complex Complex.instNatCast n) qz99) (@HMul.hMul Complex Complex Complex qz46 qz100 (@HAdd.hAdd Complex Complex Complex qz5 qz101 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz55 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz55 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz55 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz103 qz104 (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz55 2 k) 1)))))) Bool.false 462909655069 274877906944 23500123332513 5265836063326208

noncomputable def ep303 := nat_lit 44377568584650573043993259

noncomputable def ep304 := nat_lit 1855137004233520381576329

noncomputable def ep305 := nat_lit 1010911868298577315877339946582802432

noncomputable def ep306 := nat_lit 37687264410346893533882350710030336

noncomputable def ep307 := @ep302 Bool.true 45379262079 274877906944 23442985127917 5265836063326208 Bool.true 118576786035555494284347 ep169 ep303 ep171 Bool.false 607191592043010943620381 ep298 ep304 ep300 Bool.false ep305 ep168 ep169 ep170 ep171 Bool.true ep306 137105469222103760453619 ep298

noncomputable def ep308 := @Enclosure.Complex.IsNear.of_eq (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 14, @HPow.hPow Complex Complex Complex qz98 (@Nat.cast Complex Complex.instNatCast n) qz99) (BSN.headSumC qz6 14) Bool.false 462909655069 274877906944 23500123332513 5265836063326208 Bool.true 45379262079 274877906944 23442985127917

noncomputable abbrev qz105 := (@HPow.hPow Complex Complex Complex qz270 (@Nat.cast Complex Complex.instNatCast 13) qz271)

noncomputable def ep309 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz6 14) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz6 13) qz105) Bool.false 462909655069 274877906944 23500123332513 5265836063326208 Bool.true 45379262079 274877906944 23442985127917 5265836063326208

noncomputable def ep310 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz6 13) qz105 Bool.false 195626356895 137438953472 5541287519545 1316459015831552 Bool.true 17433091 67108864 11057011689249 2632918031663104 Bool.false

noncomputable abbrev qz106 := (@HPow.hPow Complex Complex Complex qz270 (@Nat.cast Complex Complex.instNatCast 12) qz271)

noncomputable def ep311 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz6 13) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz6 12) qz106) Bool.false 195626356895 137438953472 5541287519545 1316459015831552 Bool.true 17433091 67108864 11057011689249 2632918031663104

noncomputable def ep312 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz6 12) qz106 Bool.false 80000233567 68719476736 10386785010167 2632918031663104 Bool.true 9120615421 68719476736 10363520787681 2632918031663104 Bool.false

noncomputable abbrev qz107 := (@HPow.hPow Complex Complex Complex qz270 (@Nat.cast Complex Complex.instNatCast 11) qz271)

noncomputable def ep313 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz6 12) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz6 11) qz107) Bool.false 80000233567 68719476736 10386785010167 2632918031663104 Bool.true 9120615421 68719476736 10363520787681 2632918031663104

noncomputable def ep314 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz6 11) qz107 Bool.false 261227952463 274877906944 19325436897119 5265836063326208 Bool.false 5488097285 68719476736 9639474714485 2632918031663104 Bool.false

noncomputable abbrev qz108 := (@HPow.hPow Complex Complex Complex qz270 (@Nat.cast Complex Complex.instNatCast 10) qz271)

noncomputable def ep315 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz6 11) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz6 10) qz108) Bool.false 261227952463 274877906944 19325436897119 5265836063326208 Bool.false 5488097285 68719476736 9639474714485 2632918031663104

noncomputable def ep316 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz6 10) qz108 Bool.false 186731948293 274877906944 17802305578785 5265836063326208 Bool.false 66742405775 274877906944 17759250527797 5265836063326208 Bool.false

noncomputable abbrev qz109 := (@HPow.hPow Complex Complex Complex qz270 (@Nat.cast Complex Complex.instNatCast 9) qz271)

noncomputable def ep317 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz6 10) (@HAdd.hAdd Complex Complex Complex qz5 qz4 qz109) Bool.false 186731948293 274877906944 17802305578785 5265836063326208 Bool.false 66742405775 274877906944 17759250527797 5265836063326208

noncomputable def ep318 := @Enclosure.Complex.IsNear.addLitP qz4 qz109 Bool.false 101905133827 274877906944 16196562093243 5265836063326208 Bool.false 32105078227 274877906944 16159008664457 5265836063326208 Bool.false

noncomputable abbrev qz350 := (@Nat.cast Real Real.instNatCast 9)

noncomputable abbrev qz110 := (@Inv.inv Real Real.instInv (Real.sqrt qz350))

noncomputable abbrev qz111 := (@HMul.hMul Real Real Real qz263 qz276 (Real.log (Enclosure.sfrac Bool.false 9 1)))

noncomputable def ep319 := @Enclosure.Complex.IsNear.of_eq qz109 (Complex.mk (@HMul.hMul Real Real Real qz0 qz110 (Real.cos qz111)) (@HMul.hMul Real Real Real qz0 qz110 (@Neg.neg Real Real.instNeg (Real.sin qz111)))) Bool.false 42413407233 137438953472 802871742771 2632918031663104 Bool.false 8659331887 68719476736 400060465835 1316459015831552 (BSN.cpow_neg_s_mk qz17 68454 1000 9 qz18 rfl)

noncomputable abbrev qz351 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 9) qz19)

noncomputable def ep320 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz350) 1572865 524288 1 524288 87381 87382 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz350) (Real.sqrt qz351) Bool.false 1572865 524288 1 524288 (BSN.sqrt_natCast_div_one 9) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz351) Bool.false 1572865 524288 1 524288 1572865 524288 1 524288 (BSN.sqrt_enclosure 9 1 786432 786433 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep321 := BSN.log_dyadic_bound 1 17 2 1 867 262144 76628 1 1 30876 18 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 1) (BSN.artanhQ 17) 0 1 1 867 1 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz112 := (Real.log (Enclosure.sfrac Bool.false 9 1))

noncomputable def ep322 := @Enclosure.Real.IsNear.mulLit_ff qz17 qz112 68454 1000 0 1 9895417793173221 4503599627370496 250000000057471 19157000000000000000 338690464806939835167 2251799813685248000 8556750001967059917 9578500000000000000000 qz22 (BSN.isNear_log_sfrac 9 1 9895417793173221 4503599627370496 250000000057471 19157000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz351) Bool.false 20752195215788806766592 9444732965739290427392 1000000000229884 76628000000000000000 9895417793173221 4503599627370496 250000000057471 19157000000000000000 (BSN.log_rat_reduce_isNear 9 1 3 18 16 30876 262144 24973259072661432 36028797018963968 76628 1000000000000000 rfl rfl rfl rfl (ep321 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep323 := nat_lit 10475846656265150457961378063945101166767757653986105940728275756676437991680

noncomputable def ep324 := nat_lit 6783488724374940314700604420440972936606066115663053925832575829097799936

noncomputable def ep325 := nat_lit 27425758451331167962722665379365979575827717367681108709836993287572131635456

noncomputable def ep326 := BSN.sin_dyadic_bound_f 1270374122 1073741824 3 2 524288 153406 ep323 ep71 ep324 ep325 ep74 ep324 485382 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1270374122) qz283 0 2 ep323 ep71 ep324 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1270374122) qz284 0 2 ep325 ep74 ep324 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz352 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 39428759) qz28)

noncomputable def ep327 := @Enclosure.Real.IsNear.cos_image qz111 qz352 Bool.false 39428759 262144 235 262144 Bool.false 485382 524288 1 76628 (@Enclosure.Real.IsNear.recentre' qz111 Bool.false 338690464806939835167 2251799813685248000 8556750001967059917 9578500000000000000000 39428759 262144 235 262144 (ep322 rfl) rfl) (Enclosure.sfrac_false_div 39428759 262144) (BSN.cos_reduce3 qz352 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 44697315828655034728448) qz30) 226375608064910080 72057594037927936 Bool.false 485382 524288 23 1000000000000000 153256 76628 (BSN.sin_reduce_arg_pos_rat_q3 39428759 262144 226375608064910080 72057594037927936 23 44697315828655034728448 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 485382 524288 44697315828655034728448 37778931862957161709568 1270374122 1073741824 153406 153256 (ep326 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep328 := nat_lit 5822929692913694672340632526378585525065023614932575768816078787410953462016

noncomputable def ep329 := nat_lit 17455222101292334136392496370294874629321858712566401198596571210574664786176

noncomputable def ep330 := BSN.cos_dyadic_bound_f 1270374122 1073741824 3 2 524288 153406 ep328 ep78 ep324 ep329 ep80 ep324 198196 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1270374122) qz278 0 2 ep328 ep78 ep324 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1270374122) qz279 0 2 ep329 ep80 ep324 rfl rfl rfl rfl) rfl rfl

noncomputable def ep331 := @Enclosure.Real.IsNear.sin_image qz111 qz352 Bool.false 39428759 262144 235 262144 Bool.true 198196 524288 1 76628 (@Enclosure.Real.IsNear.recentre' qz111 Bool.false 338690464806939835167 2251799813685248000 8556750001967059917 9578500000000000000000 39428759 262144 235 262144 (ep322 rfl) rfl) (Enclosure.sfrac_false_div 39428759 262144) (BSN.sin_reduce3 qz352 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 44697315828655034728448) qz30) 226375608064910080 72057594037927936 Bool.false 198196 524288 23 1000000000000000 153256 76628 (BSN.sin_reduce_arg_pos_rat_q3 39428759 262144 226375608064910080 72057594037927936 23 44697315828655034728448 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 198196 524288 44697315828655034728448 37778931862957161709568 1270374122 1073741824 153406 153256 (ep330 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz353 := (@Enclosure.Real.IsNear.recentre' qz110 Bool.false 174763 524288 1 524288 174763 524288 1 524288 (ep320 rfl rfl) rfl)

noncomputable def ep332 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz110 (Real.cos qz111)) (@HMul.hMul Real Real Real qz0 qz110 (@Neg.neg Real Real.instNeg (Real.sin qz111))) Bool.false 42413407233 137438953472 802871742771 2632918031663104 Bool.false 8659331887 68719476736 400060465835 1316459015831552 (@Enclosure.Real.IsNear.mulLit_ff qz110 (Real.cos qz111) 174763 524288 1 524288 242691 262144 4567431 5021892608 42413407233 137438953472 802871742771 2632918031663104 qz353 (@Enclosure.Real.IsNear.recentre' (Real.cos qz111) Bool.false 485382 524288 18269724 20087570432 242691 262144 4567431 5021892608 (ep327 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz110 (@Neg.neg Real Real.instNeg (Real.sin qz111)) 174763 524288 1 524288 49549 131072 4567431 5021892608 8659331887 68719476736 400060465835 1316459015831552 qz353 (@Enclosure.Real.IsNear.neg (Real.sin qz111) Bool.true 49549 131072 4567431 5021892608 (@Enclosure.Real.IsNear.recentre' (Real.sin qz111) Bool.true 198196 524288 18269724 20087570432 49549 131072 4567431 5021892608 (ep331 rfl rfl) rfl)) rfl)

noncomputable def ep333 := @ep318 42413407233 137438953472 802871742771 2632918031663104 Bool.false 8659331887 68719476736 400060465835 1316459015831552 Bool.false 25664243553177536823296 186731948293 274877906944 17802305578785 5265836063326208 Bool.false 4586503200959784550400 66742405775 274877906944 17759250527797 5265836063326208 EMRow17.d6 (ep319 ep332) rfl rfl

noncomputable abbrev qz354 := (@Nat.cast Real Real.instNatCast 10)

noncomputable abbrev qz113 := (@Inv.inv Real Real.instInv (Real.sqrt qz354))

noncomputable abbrev qz114 := (@HMul.hMul Real Real Real qz263 qz276 (Real.log (Enclosure.sfrac Bool.false 10 1)))

noncomputable def ep334 := @Enclosure.Complex.IsNear.of_eq qz108 (Complex.mk (@HMul.hMul Real Real Real qz0 qz113 (Real.cos qz114)) (@HMul.hMul Real Real Real qz0 qz113 (@Neg.neg Real Real.instNeg (Real.sin qz114)))) Bool.false 37248002085 137438953472 761565659167 2632918031663104 Bool.true 44790016635 274877906944 1519698901173 5265836063326208 (BSN.cpow_neg_s_mk qz17 68454 1000 10 qz18 rfl)

noncomputable abbrev qz355 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 10) qz19)

noncomputable def ep335 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz354) 1657945 524288 1 524288 82897 82898 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz354) (Real.sqrt qz355) Bool.false 1657945 524288 1 524288 (BSN.sqrt_natCast_div_one 10) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz355) Bool.false 1657945 524288 1 524288 1657945 524288 1 524288 (BSN.sqrt_enclosure 10 1 828972 828973 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep336 := BSN.log_dyadic_bound 2 18 3 2 1574640 262144 76628 6528 48 58495 20 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 2) (BSN.artanhQ 18) 0 2 6528 1574640 48 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz115 := (Real.log (Enclosure.sfrac Bool.false 10 1))

noncomputable def ep337 := @Enclosure.Real.IsNear.mulLit_ff qz17 qz115 68454 1000 0 1 10369908600166117 4503599627370496 250000000057471 19157000000000000000 354930861657885686559 2251799813685248000 8556750001967059917 9578500000000000000000 qz22 (BSN.isNear_log_sfrac 10 1 10369908600166117 4503599627370496 250000000057471 19157000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz355) Bool.false 21747274560655572598784 9444732965739290427392 1000000000229884 76628000000000000000 10369908600166117 4503599627370496 250000000057471 19157000000000000000 (BSN.log_rat_reduce_isNear 10 1 3 20 16 58495 262144 24973259072661432 36028797018963968 76628 1000000000000000 rfl rfl rfl rfl (ep336 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep338 := nat_lit 114143782755876677855704256337900721

noncomputable def ep339 := BSN.cos_dyadic_bound_f 581250133 1073741824 2 1 524288 153406 ep338 ep57 ep338 ep338 ep58 ep338 449326 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 581250133) qz278 0 1 ep338 ep57 ep338 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 581250133) qz279 0 1 ep338 ep58 ep338 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz356 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 20659695) (@Nat.cast Real Real.instNatCast 131072))

noncomputable def ep340 := @Enclosure.Real.IsNear.cos_image qz114 qz356 Bool.false 20659695 131072 235 262144 Bool.false 449326 524288 1 76628 (@Enclosure.Real.IsNear.recentre' qz114 Bool.false 354930861657885686559 2251799813685248000 8556750001967059917 9578500000000000000000 20659695 131072 235 262144 (ep337 rfl) rfl) (Enclosure.sfrac_false_div 20659695 131072) (BSN.cos_reduce0 qz356 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 10225460486429778903040) qz302) 226375608064910080 72057594037927936 Bool.false 449326 524288 25 1000000000000000 153256 76628 (BSN.sin_reduce_arg_pos_rat_q0 20659695 131072 226375608064910080 72057594037927936 25 10225460486429778903040 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 449326 524288 10225460486429778903040 18889465931478580854784 581250133 1073741824 153406 153256 (ep339 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep341 := BSN.sin_dyadic_bound_f 581250133 1073741824 2 1 524288 153406 ep338 ep61 ep338 ep338 ep62 ep338 270153 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 581250133) qz283 0 1 ep338 ep61 ep338 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 581250133) qz284 0 1 ep338 ep62 ep338 rfl rfl rfl rfl) rfl rfl

noncomputable def ep342 := @Enclosure.Real.IsNear.sin_image qz114 qz356 Bool.false 20659695 131072 235 262144 Bool.false 270153 524288 1 76628 (@Enclosure.Real.IsNear.recentre' qz114 Bool.false 354930861657885686559 2251799813685248000 8556750001967059917 9578500000000000000000 20659695 131072 235 262144 (ep337 rfl) rfl) (Enclosure.sfrac_false_div 20659695 131072) (BSN.sin_reduce0 qz356 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 10225460486429778903040) qz302) 226375608064910080 72057594037927936 Bool.false 270153 524288 25 1000000000000000 153256 76628 (BSN.sin_reduce_arg_pos_rat_q0 20659695 131072 226375608064910080 72057594037927936 25 10225460486429778903040 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 270153 524288 10225460486429778903040 18889465931478580854784 581250133 1073741824 153406 153256 (ep341 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz357 := (@Enclosure.Real.IsNear.recentre' qz113 Bool.false 165795 524288 1 524288 165795 524288 1 524288 (ep335 rfl rfl) rfl)

noncomputable def ep343 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz113 (Real.cos qz114)) (@HMul.hMul Real Real Real qz0 qz113 (@Neg.neg Real Real.instNeg (Real.sin qz114))) Bool.false 37248002085 137438953472 761565659167 2632918031663104 Bool.true 44790016635 274877906944 1519698901173 5265836063326208 (@Enclosure.Real.IsNear.mulLit_ff qz113 (Real.cos qz114) 165795 524288 1 524288 224663 262144 4567431 5021892608 37248002085 137438953472 761565659167 2632918031663104 qz357 (@Enclosure.Real.IsNear.recentre' (Real.cos qz114) Bool.false 449326 524288 18269724 20087570432 224663 262144 4567431 5021892608 (ep340 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz113 (@Neg.neg Real Real.instNeg (Real.sin qz114)) 165795 524288 1 524288 270153 524288 4567431 5021892608 44790016635 274877906944 1519698901173 5265836063326208 qz357 (@Enclosure.Real.IsNear.neg (Real.sin qz114) Bool.false 270153 524288 4567431 5021892608 (@Enclosure.Real.IsNear.recentre' (Real.sin qz114) Bool.false 270153 524288 18269724 20087570432 270153 524288 4567431 5021892608 (ep342 rfl rfl) rfl)) rfl)

noncomputable def ep344 := @ep316 37248002085 137438953472 761565659167 2632918031663104 Bool.true 44790016635 274877906944 1519698901173 5265836063326208 Bool.false 35902896404148084801536 261227952463 274877906944 19325436897119 5265836063326208 Bool.false 6034226779223396188160 5488097285 68719476736 9639474714485 2632918031663104 (ep317 (BSN.head_sum_c_succ qz6 9 10 rfl rfl) (ep333 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep334 ep343) rfl rfl

noncomputable abbrev qz358 := (@Nat.cast Real Real.instNatCast 11)

noncomputable abbrev qz116 := (@Inv.inv Real Real.instInv (Real.sqrt qz358))

noncomputable abbrev qz117 := (@HMul.hMul Real Real Real qz263 qz276 (Real.log (Enclosure.sfrac Bool.false 11 1)))

noncomputable def ep345 := @Enclosure.Complex.IsNear.of_eq qz107 (Complex.mk (@HMul.hMul Real Real Real qz0 qz116 (Real.cos qz117)) (@HMul.hMul Real Real Real qz0 qz116 (@Neg.neg Real Real.instNeg (Real.sin qz117)))) Bool.false 58772981805 274877906944 1448133123215 5265836063326208 Bool.true 7304356353 34359738368 181011518299 658229507915776 (BSN.cpow_neg_s_mk qz17 68454 1000 11 qz18 rfl)

noncomputable abbrev qz359 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 11) qz19)

noncomputable def ep346 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz358) 1738867 524288 1 524288 79039 79040 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz358) (Real.sqrt qz359) Bool.false 1738867 524288 1 524288 (BSN.sqrt_natCast_div_one 11) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz359) Bool.false 1738867 524288 1 524288 1738867 524288 1 524288 (BSN.sqrt_enclosure 11 1 869433 869434 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep347 := BSN.log_dyadic_bound 3 19 4 3 4939817505 262144 76628 41676111 10935 83480 22 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 3) (BSN.artanhQ 19) 0 3 41676111 4939817505 10935 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz118 := (Real.log (Enclosure.sfrac Bool.false 11 1))

noncomputable def ep348 := @Enclosure.Real.IsNear.mulLit_ff qz17 qz118 68454 1000 0 1 10799147631728357 4503599627370496 250000000057471 19157000000000000000 369622425991166475039 2251799813685248000 8556750001967059917 9578500000000000000000 qz22 (BSN.isNear_log_sfrac 11 1 10799147631728357 4503599627370496 250000000057471 19157000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz359) Bool.false 22647454054174387339264 9444732965739290427392 1000000000229884 76628000000000000000 10799147631728357 4503599627370496 250000000057471 19157000000000000000 (BSN.log_rat_reduce_isNear 11 1 3 22 16 83480 262144 24973259072661432 36028797018963968 76628 1000000000000000 rfl rfl rfl rfl (ep347 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep349 := nat_lit 1113192221498555128399428626603952816977270405710456099088958255533058921601

noncomputable def ep350 := nat_lit 248387063385514771391998165107373994464659409902959701208379974696277121

noncomputable def ep351 := nat_lit 3339079890368894355655501883481643702942881898311562377864458006649784210561

noncomputable def ep352 := BSN.cos_dyadic_bound_f 840216337 1073741824 3 2 524288 153406 ep349 ep78 ep350 ep351 ep80 ep350 371795 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 840216337) qz278 0 2 ep349 ep78 ep350 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 840216337) qz279 0 2 ep351 ep80 ep350 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz360 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 86059427) qz20)

noncomputable def ep353 := @Enclosure.Real.IsNear.cos_image qz117 qz360 Bool.false 86059427 524288 469 524288 Bool.false 371795 524288 1 76628 (@Enclosure.Real.IsNear.recentre' qz117 Bool.false 369622425991166475039 2251799813685248000 8556750001967059917 9578500000000000000000 86059427 524288 469 524288 (ep348 rfl) rfl) (Enclosure.sfrac_false_div 86059427 524288) (BSN.cos_reduce0 qz360 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 59124968487288972509184) qz23) 226375608064910080 72057594037927936 Bool.false 371795 524288 26 1000000000000000 153256 76628 (BSN.sin_reduce_arg_pos_rat_q0 86059427 524288 226375608064910080 72057594037927936 26 59124968487288972509184 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 371795 524288 59124968487288972509184 75557863725914323419136 840216337 1073741824 153406 153256 (ep352 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep354 := nat_lit 498384453394680813043164110220509761

noncomputable def ep355 := BSN.sin_dyadic_bound_f 840216337 1073741824 2 1 524288 153406 ep354 ep61 ep354 ep354 ep62 ep354 369656 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 840216337) qz283 0 1 ep354 ep61 ep354 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 840216337) qz284 0 1 ep354 ep62 ep354 rfl rfl rfl rfl) rfl rfl

noncomputable def ep356 := @Enclosure.Real.IsNear.sin_image qz117 qz360 Bool.false 86059427 524288 469 524288 Bool.false 369656 524288 1 76628 (@Enclosure.Real.IsNear.recentre' qz117 Bool.false 369622425991166475039 2251799813685248000 8556750001967059917 9578500000000000000000 86059427 524288 469 524288 (ep348 rfl) rfl) (Enclosure.sfrac_false_div 86059427 524288) (BSN.sin_reduce0 qz360 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 59124968487288972509184) qz23) 226375608064910080 72057594037927936 Bool.false 369656 524288 26 1000000000000000 153256 76628 (BSN.sin_reduce_arg_pos_rat_q0 86059427 524288 226375608064910080 72057594037927936 26 59124968487288972509184 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 369656 524288 59124968487288972509184 75557863725914323419136 840216337 1073741824 153406 153256 (ep355 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz361 := (@Enclosure.Real.IsNear.recentre' qz116 Bool.false 158079 524288 1 524288 158079 524288 1 524288 (ep346 rfl rfl) rfl)

noncomputable def ep357 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz116 (Real.cos qz117)) (@HMul.hMul Real Real Real qz0 qz116 (@Neg.neg Real Real.instNeg (Real.sin qz117))) Bool.false 58772981805 274877906944 1448133123215 5265836063326208 Bool.true 7304356353 34359738368 181011518299 658229507915776 (@Enclosure.Real.IsNear.mulLit_ff qz116 (Real.cos qz117) 158079 524288 1 524288 371795 524288 9115705 10043785216 58772981805 274877906944 1448133123215 5265836063326208 qz361 (@Enclosure.Real.IsNear.recentre' (Real.cos qz117) Bool.false 371795 524288 36462820 40175140864 371795 524288 9115705 10043785216 (ep353 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz116 (@Neg.neg Real Real.instNeg (Real.sin qz117)) 158079 524288 1 524288 46207 65536 9115705 10043785216 7304356353 34359738368 181011518299 658229507915776 qz361 (@Enclosure.Real.IsNear.neg (Real.sin qz117) Bool.false 46207 65536 9115705 10043785216 (@Enclosure.Real.IsNear.recentre' (Real.sin qz117) Bool.false 369656 524288 36462820 40175140864 46207 65536 9115705 10043785216 (ep356 rfl rfl) rfl)) rfl)

noncomputable def ep358 := @ep314 58772981805 274877906944 1448133123215 5265836063326208 Bool.true 7304356353 34359738368 181011518299 658229507915776 Bool.false 87961187031712364756992 80000233567 68719476736 10386785010167 2632918031663104 Bool.true 313381959620706172928 9120615421 68719476736 10363520787681 2632918031663104 (ep315 (BSN.head_sum_c_succ qz6 10 11 rfl rfl) (ep344 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep345 ep357) rfl rfl

noncomputable abbrev qz362 := (@Nat.cast Real Real.instNatCast 12)

noncomputable abbrev qz119 := (@Inv.inv Real Real.instInv (Real.sqrt qz362))

noncomputable abbrev qz120 := (@HMul.hMul Real Real Real qz263 qz276 (Real.log (Enclosure.sfrac Bool.false 12 1)))

noncomputable def ep359 := @Enclosure.Complex.IsNear.of_eq qz106 (Complex.mk (@HMul.hMul Real Real Real qz0 qz119 (Real.cos qz120)) (@HMul.hMul Real Real Real qz0 qz119 (@Neg.neg Real Real.instNeg (Real.sin qz120)))) Bool.false 35625889761 137438953472 695790028923 2632918031663104 Bool.true 8730869763 68719476736 10835795337 41139344244736 (BSN.cpow_neg_s_mk qz17 68454 1000 12 qz18 rfl)

noncomputable abbrev qz363 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 12) qz19)

noncomputable def ep360 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz362) 1816187 524288 1 524288 75674 75675 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz362) (Real.sqrt qz363) Bool.false 1816187 524288 1 524288 (BSN.sqrt_natCast_div_one 12) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz363) Bool.false 1816187 524288 1 524288 1816187 524288 1 524288 (BSN.sqrt_enclosure 12 1 908093 908094 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep361 := BSN.log_dyadic_bound 4 20 4 3 6720000000 262144 76628 91811840 61440 106290 24 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 4) (BSN.artanhQ 20) 0 3 91811840 6720000000 61440 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz121 := (Real.log (Enclosure.sfrac Bool.false 12 1))

noncomputable def ep362 := @Enclosure.Real.IsNear.mulLit_ff qz17 qz121 68454 1000 0 1 11191020447815397 4503599627370496 250000000057471 19157000000000000000 383035056867377593119 2251799813685248000 8556750001967059917 9578500000000000000000 qz22 (BSN.isNear_log_sfrac 12 1 11191020447815397 4503599627370496 250000000057471 19157000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz363) Bool.false 23469270914176955449344 9444732965739290427392 1000000000229884 76628000000000000000 11191020447815397 4503599627370496 250000000057471 19157000000000000000 (BSN.log_rat_reduce_isNear 12 1 3 24 16 106290 262144 24973259072661432 36028797018963968 76628 1000000000000000 rfl rfl rfl rfl (ep361 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep363 := nat_lit 57336774381203582776221083968573696

noncomputable def ep364 := BSN.cos_dyadic_bound_f 489337292 1073741824 2 1 524288 153406 ep363 ep57 ep363 ep363 ep58 ep363 470778 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 489337292) qz278 0 1 ep363 ep57 ep363 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 489337292) qz279 0 1 ep363 ep58 ep363 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz364 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 44591149) qz28)

noncomputable def ep365 := @Enclosure.Real.IsNear.cos_image qz120 qz364 Bool.false 44591149 262144 235 262144 Bool.false 470778 524288 1 76628 (@Enclosure.Real.IsNear.recentre' qz120 Bool.false 383035056867377593119 2251799813685248000 8556750001967059917 9578500000000000000000 44591149 262144 235 262144 (ep362 rfl) rfl) (Enclosure.sfrac_false_div 44591149 262144) (BSN.cos_reduce0 qz364 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 17217025392191385632768) qz30) 226375608064910080 72057594037927936 Bool.false 470778 524288 27 1000000000000000 153256 76628 (BSN.sin_reduce_arg_pos_rat_q0 44591149 262144 226375608064910080 72057594037927936 27 17217025392191385632768 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 470778 524288 17217025392191385632768 37778931862957161709568 489337292 1073741824 153406 153256 (ep364 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep366 := BSN.sin_dyadic_bound_f 489337292 1073741824 2 1 524288 153406 ep363 ep61 ep363 ep363 ep62 ep363 230748 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 489337292) qz283 0 1 ep363 ep61 ep363 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 489337292) qz284 0 1 ep363 ep62 ep363 rfl rfl rfl rfl) rfl rfl

noncomputable def ep367 := @Enclosure.Real.IsNear.sin_image qz120 qz364 Bool.false 44591149 262144 235 262144 Bool.false 230748 524288 1 76628 (@Enclosure.Real.IsNear.recentre' qz120 Bool.false 383035056867377593119 2251799813685248000 8556750001967059917 9578500000000000000000 44591149 262144 235 262144 (ep362 rfl) rfl) (Enclosure.sfrac_false_div 44591149 262144) (BSN.sin_reduce0 qz364 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 17217025392191385632768) qz30) 226375608064910080 72057594037927936 Bool.false 230748 524288 27 1000000000000000 153256 76628 (BSN.sin_reduce_arg_pos_rat_q0 44591149 262144 226375608064910080 72057594037927936 27 17217025392191385632768 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 230748 524288 17217025392191385632768 37778931862957161709568 489337292 1073741824 153406 153256 (ep366 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz365 := (@Enclosure.Real.IsNear.recentre' qz119 Bool.false 151349 524288 1 524288 151349 524288 1 524288 (ep360 rfl rfl) rfl)

noncomputable def ep368 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz119 (Real.cos qz120)) (@HMul.hMul Real Real Real qz0 qz119 (@Neg.neg Real Real.instNeg (Real.sin qz120))) Bool.false 35625889761 137438953472 695790028923 2632918031663104 Bool.true 8730869763 68719476736 10835795337 41139344244736 (@Enclosure.Real.IsNear.mulLit_ff qz119 (Real.cos qz120) 151349 524288 1 524288 235389 262144 4567431 5021892608 35625889761 137438953472 695790028923 2632918031663104 qz365 (@Enclosure.Real.IsNear.recentre' (Real.cos qz120) Bool.false 470778 524288 18269724 20087570432 235389 262144 4567431 5021892608 (ep365 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz119 (@Neg.neg Real Real.instNeg (Real.sin qz120)) 151349 524288 1 524288 57687 131072 4567431 5021892608 8730869763 68719476736 10835795337 41139344244736 qz365 (@Enclosure.Real.IsNear.neg (Real.sin qz120) Bool.false 57687 131072 4567431 5021892608 (@Enclosure.Real.IsNear.recentre' (Real.sin qz120) Bool.false 230748 524288 18269724 20087570432 57687 131072 4567431 5021892608 (ep367 rfl rfl) rfl)) rfl)

noncomputable def ep369 := @ep312 35625889761 137438953472 695790028923 2632918031663104 Bool.true 8730869763 68719476736 10835795337 41139344244736 Bool.false 13443340881594385694720 195626356895 137438953472 5541287519545 1316459015831552 Bool.true 1226744720804936679424 17433091 67108864 11057011689249 2632918031663104 (ep313 (BSN.head_sum_c_succ qz6 11 12 rfl rfl) (ep358 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep359 ep368) rfl rfl

noncomputable abbrev qz366 := (@Nat.cast Real Real.instNatCast 13)

noncomputable abbrev qz122 := (@Inv.inv Real Real.instInv (Real.sqrt qz366))

noncomputable abbrev qz123 := (@HMul.hMul Real Real Real qz263 qz276 (Real.log (Enclosure.sfrac Bool.false 13 1)))

noncomputable def ep370 := @Enclosure.Complex.IsNear.of_eq qz105 (Complex.mk (@HMul.hMul Real Real Real qz0 qz122 (Real.cos qz123)) (@HMul.hMul Real Real Real qz0 qz122 (@Neg.neg Real Real.instNeg (Real.sin qz123)))) Bool.false 71656941279 274877906944 1334973254333 5265836063326208 Bool.false 26026678657 274877906944 1328961749419 5265836063326208 (BSN.cpow_neg_s_mk qz17 68454 1000 13 qz18 rfl)

noncomputable abbrev qz367 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 13) qz19)

noncomputable def ep371 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz366) 1890347 524288 1 524288 72705 72706 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz366) (Real.sqrt qz367) Bool.false 1890347 524288 1 524288 (BSN.sqrt_natCast_div_one 13) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz367) Bool.false 1890347 524288 1 524288 1890347 524288 1 524288 (BSN.sqrt_enclosure 13 1 945173 945174 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep372 := BSN.log_dyadic_bound 5 21 5 4 35742602096145 262144 76628 699352521000 41015625 127272 26 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 5) (BSN.artanhQ 21) 0 4 699352521000 35742602096145 41015625 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz124 := (Real.log (Enclosure.sfrac Bool.false 13 1))

noncomputable def ep373 := @Enclosure.Real.IsNear.mulLit_ff qz17 qz124 68454 1000 0 1 11551488463034085 4503599627370496 250000000057471 19157000000000000000 79074559124853525459 450359962737049600 8556750001967059917 9578500000000000000000 qz22 (BSN.isNear_log_sfrac 13 1 11551488463034085 4503599627370496 250000000057471 19157000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz367) Bool.false 24225227133228857425920 9444732965739290427392 1000000000229884 76628000000000000000 11551488463034085 4503599627370496 250000000057471 19157000000000000000 (BSN.log_rat_reduce_isNear 13 1 3 26 16 127272 262144 24973259072661432 36028797018963968 76628 1000000000000000 rfl rfl rfl rfl (ep372 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep374 := nat_lit 11938603285952716857605734485999399085292347816524233502719991911003623730625

noncomputable def ep375 := nat_lit 8808529456771278675135443139940174590805898107496589493288491173187890625

noncomputable def ep376 := nat_lit 31253509082184247794921942460152808750237701398722759933658464114538615090625

noncomputable def ep377 := BSN.sin_dyadic_bound_f 1312541145 1073741824 3 2 524288 153406 ep374 ep71 ep375 ep376 ep74 ep375 492789 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1312541145) qz283 0 2 ep374 ep71 ep375 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1312541145) qz284 0 2 ep376 ep74 ep375 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz368 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 46027451) qz28)

noncomputable def ep378 := @Enclosure.Real.IsNear.cos_image qz123 qz368 Bool.false 46027451 262144 469 524288 Bool.false 492789 524288 1 76628 (@Enclosure.Real.IsNear.recentre' qz123 Bool.false 79074559124853525459 450359962737049600 8556750001967059917 9578500000000000000000 46027451 262144 469 524288 (ep373 rfl) rfl) (Enclosure.sfrac_false_div 46027451 262144) (BSN.cos_reduce3 qz368 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 46180936054215962263552) qz30) 226375608064910080 72057594037927936 Bool.false 492789 524288 27 1000000000000000 153256 76628 (BSN.sin_reduce_arg_pos_rat_q3 46027451 262144 226375608064910080 72057594037927936 27 46180936054215962263552 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 492789 524288 46180936054215962263552 37778931862957161709568 1312541145 1073741824 153406 153256 (ep377 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep379 := nat_lit 6636472283065629933636579355839639569424995852783461541285901502190096690625

noncomputable def ep380 := nat_lit 19891799790283347243559467181239038359093375762135391444871127524223914290625

noncomputable def ep381 := BSN.cos_dyadic_bound_f 1312541145 1073741824 3 2 524288 153406 ep379 ep78 ep375 ep380 ep80 ep375 178987 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1312541145) qz278 0 2 ep379 ep78 ep375 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1312541145) qz279 0 2 ep380 ep80 ep375 rfl rfl rfl rfl) rfl rfl

noncomputable def ep382 := @Enclosure.Real.IsNear.sin_image qz123 qz368 Bool.false 46027451 262144 469 524288 Bool.true 178987 524288 1 76628 (@Enclosure.Real.IsNear.recentre' qz123 Bool.false 79074559124853525459 450359962737049600 8556750001967059917 9578500000000000000000 46027451 262144 469 524288 (ep373 rfl) rfl) (Enclosure.sfrac_false_div 46027451 262144) (BSN.sin_reduce3 qz368 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 46180936054215962263552) qz30) 226375608064910080 72057594037927936 Bool.false 178987 524288 27 1000000000000000 153256 76628 (BSN.sin_reduce_arg_pos_rat_q3 46027451 262144 226375608064910080 72057594037927936 27 46180936054215962263552 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 178987 524288 46180936054215962263552 37778931862957161709568 1312541145 1073741824 153406 153256 (ep381 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz369 := (@Enclosure.Real.IsNear.recentre' qz122 Bool.false 145411 524288 1 524288 145411 524288 1 524288 (ep371 rfl rfl) rfl)

noncomputable def ep383 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz122 (Real.cos qz123)) (@HMul.hMul Real Real Real qz0 qz122 (@Neg.neg Real Real.instNeg (Real.sin qz123))) Bool.false 71656941279 274877906944 1334973254333 5265836063326208 Bool.false 26026678657 274877906944 1328961749419 5265836063326208 (@Enclosure.Real.IsNear.mulLit_ff qz122 (Real.cos qz123) 145411 524288 1 524288 492789 524288 9115705 10043785216 71656941279 274877906944 1334973254333 5265836063326208 qz369 (@Enclosure.Real.IsNear.recentre' (Real.cos qz123) Bool.false 492789 524288 36462820 40175140864 492789 524288 9115705 10043785216 (ep378 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz122 (@Neg.neg Real Real.instNeg (Real.sin qz123)) 145411 524288 1 524288 178987 524288 9115705 10043785216 26026678657 274877906944 1328961749419 5265836063326208 qz369 (@Enclosure.Real.IsNear.neg (Real.sin qz123) Bool.true 178987 524288 9115705 10043785216 (@Enclosure.Real.IsNear.recentre' (Real.sin qz123) Bool.true 178987 524288 36462820 40175140864 178987 524288 9115705 10043785216 (ep382 rfl rfl) rfl)) rfl)

noncomputable def ep384 := @ep310 71656941279 274877906944 1334973254333 5265836063326208 Bool.false 26026678657 274877906944 1328961749419 5265836063326208 Bool.false 63621818544767859949568 462909655069 274877906944 23500123332513 5265836063326208 Bool.true 3045350727279968256 45379262079 274877906944 23442985127917 5265836063326208 (ep311 (BSN.head_sum_c_succ qz6 12 13 rfl rfl) (ep369 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep370 ep383) rfl rfl

noncomputable def ep385 := @Enclosure.Complex.IsNear.mul qz100 (@HAdd.hAdd Complex Complex Complex qz5 qz101 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz55 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz55 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz55 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz103 qz104 (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz55 2 k) 1))))) Bool.true 118576786035555494284347 ep169 ep303 ep171 Bool.false

noncomputable abbrev qz125 := (Complex.re qz347)

noncomputable abbrev qz126 := (Complex.im qz347)

noncomputable def ep386 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 qz125 (Complex.re (@HAdd.hAdd Complex Complex Complex qz5 qz101 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz55 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz55 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz55 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz103 qz104 (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz55 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz126 (Complex.im (@HAdd.hAdd Complex Complex Complex qz5 qz101 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz55 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz55 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz55 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz103 qz104 (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz55 2 k) 1))))))) 29513689015516783407 18033860311695340077056 63042604238485630741681

noncomputable def ep387 := nat_lit 518211992986721444784242688

noncomputable def ep388 := nat_lit 4285422155135919224384253

noncomputable def ep389 := nat_lit 86368665497786907464040448000

noncomputable def ep390 := nat_lit 1069198597787497227375744347001679505277321216

noncomputable def ep391 := @Enclosure.Real.IsNear.mulLit_ff qz125 (Complex.re (@HAdd.hAdd Complex Complex Complex qz5 qz101 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz55 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz55 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz55 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz103 qz104 (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz55 2 k) 1)))))) 448527321 137438953472 319358364781 1316459015831552 197403954901

noncomputable abbrev qz370 := (@Nat.cast Real Real.instNatCast 14)

noncomputable abbrev qz127 := (@Inv.inv Real Real.instInv (Real.sqrt qz370))

noncomputable abbrev qz371 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) qz467 (Real.log (Enclosure.sfrac Bool.false 14 1)))

noncomputable abbrev qz128 := (Real.cos qz371)

noncomputable abbrev qz129 := (@Neg.neg Real Real.instNeg (Real.sin qz371))

noncomputable def ep392 := @Enclosure.Complex.IsNear.of_eq qz100 (Complex.mk (@HMul.hMul Real Real Real qz0 qz127 qz128) (@HMul.hMul Real Real Real qz0 qz127 qz129)) Bool.false 448527321 137438953472 319358364781 1316459015831552 Bool.false 9182269251 34359738368 643676917473 2632918031663104 (BSN.cpow_neg_s_mk qz17 68454 1000 14 qz18 rfl)

noncomputable abbrev qz372 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 14) qz19)

noncomputable def ep393 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz370) 1961707 524288 1 524288 70060 70061 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz370) (Real.sqrt qz372) Bool.false 1961707 524288 1 524288 (BSN.sqrt_natCast_div_one 14) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz372) Bool.false 1961707 524288 1 524288 1961707 524288 1 524288 (BSN.sqrt_enclosure 14 1 980853 980854 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep394 := BSN.log_dyadic_bound 6 22 5 4 51857700491520 262144 76628 1346332575744 176359680 146699 28 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 6) (BSN.artanhQ 22) 0 4 1346332575744 51857700491520 176359680 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz373 := (Real.log (Enclosure.sfrac Bool.false 14 1))

noncomputable abbrev qz130 := qz373

noncomputable abbrev qz374 := (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 14) qz19))

noncomputable def ep395 := @Enclosure.Real.IsNear.mulLit_ff qz17 qz130 68454 1000 0 1 11885241781671653 4503599627370496 250000000057471 19157000000000000000 406796170461275667231 2251799813685248000 8556750001967059917 9578500000000000000000 qz22 (BSN.isNear_log_sfrac 14 1 11885241781671653 4503599627370496 250000000057471 19157000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' qz374 Bool.false 24925158572916270432256 9444732965739290427392 1000000000229884 76628000000000000000 11885241781671653 4503599627370496 250000000057471 19157000000000000000 (BSN.log_rat_reduce_isNear 14 1 3 28 16 146699 262144 24973259072661432 36028797018963968 76628 1000000000000000 rfl rfl rfl rfl (ep394 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep396 := BSN.sin_dyadic_bound_f 13112469 1073741824 1 0 524288 153406 0 1 1 0 1 1 6402 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 13112469) qz283 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 13112469) qz284 0 0 rfl) rfl rfl

noncomputable abbrev qz131 := qz371

noncomputable abbrev qz375 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 47357307) qz28)

noncomputable def ep397 := @Enclosure.Real.IsNear.cos_image qz131 qz375 Bool.false 47357307 262144 469 524288 Bool.false 6402 524288 1 76628 (@Enclosure.Real.IsNear.recentre' qz131 Bool.false 406796170461275667231 2251799813685248000 8556750001967059917 9578500000000000000000 47357307 262144 469 524288 (ep395 rfl) rfl) (Enclosure.sfrac_false_div 47357307 262144) (BSN.cos_reduce3 qz375 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 461354005750196731904) qz30) 226375608064910080 72057594037927936 Bool.false 6402 524288 28 1000000000000000 153256 76628 (BSN.sin_reduce_arg_pos_rat_q3 47357307 262144 226375608064910080 72057594037927936 28 461354005750196731904 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 6402 524288 461354005750196731904 37778931862957161709568 13112469 1073741824 153406 153256 (ep396 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep398 := BSN.cos_dyadic_bound_f 13112469 1073741824 1 0 524288 153406 0 1 1 0 1 1 524248 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 13112469) qz278 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 13112469) qz279 0 0 rfl) rfl rfl

noncomputable def ep399 := @Enclosure.Real.IsNear.sin_image qz131 qz375 Bool.false 47357307 262144 469 524288 Bool.true 524248 524288 1 76628 (@Enclosure.Real.IsNear.recentre' qz131 Bool.false 406796170461275667231 2251799813685248000 8556750001967059917 9578500000000000000000 47357307 262144 469 524288 (ep395 rfl) rfl) (Enclosure.sfrac_false_div 47357307 262144) (BSN.sin_reduce3 qz375 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 461354005750196731904) qz30) 226375608064910080 72057594037927936 Bool.false 524248 524288 28 1000000000000000 153256 76628 (BSN.sin_reduce_arg_pos_rat_q3 47357307 262144 226375608064910080 72057594037927936 28 461354005750196731904 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 524248 524288 461354005750196731904 37778931862957161709568 13112469 1073741824 153406 153256 (ep398 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz132 := (Real.sin qz371)

noncomputable abbrev qz376 := (@Enclosure.Real.IsNear.recentre' qz127 Bool.false 140121 524288 1 524288 140121 524288 1 524288 (ep393 rfl rfl) rfl)

noncomputable def ep400 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz127 qz128) (@HMul.hMul Real Real Real qz0 qz127 qz129) Bool.false 448527321 137438953472 319358364781 1316459015831552 Bool.false 9182269251 34359738368 643676917473 2632918031663104 (@Enclosure.Real.IsNear.mulLit_ff qz127 qz128 140121 524288 1 524288 3201 262144 9115705 10043785216 448527321 137438953472 319358364781 1316459015831552 qz376 (@Enclosure.Real.IsNear.recentre' qz128 Bool.false 6402 524288 36462820 40175140864 3201 262144 9115705 10043785216 (ep397 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz127 qz129 140121 524288 1 524288 65531 65536 9115705 10043785216 9182269251 34359738368 643676917473 2632918031663104 qz376 (@Enclosure.Real.IsNear.neg qz132 Bool.true 65531 65536 9115705 10043785216 (@Enclosure.Real.IsNear.recentre' qz132 Bool.true 524248 524288 36462820 40175140864 65531 65536 9115705 10043785216 (ep399 rfl rfl) rfl)) rfl)

noncomputable def ep401 := @ep391 393640809744 0 1 29513689015516783407 18033860311695340077056 63042604238485630741681 ep387 (@Enclosure.Complex.IsNear.re_isNear qz100 Bool.false 448527321 137438953472 319358364781 1316459015831552 Bool.false 9182269251 34359738368 643676917473 2632918031663104 (ep392 ep400))

noncomputable def ep402 := @Enclosure.Complex.IsNear.re_isNear (@HAdd.hAdd Complex Complex Complex qz5 qz101 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz55 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz55 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz55 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz103 qz104 (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz55 2 k) 1))))) Bool.false 197403954901 393640809744 0 1 Bool.false

noncomputable def ep403 := @Enclosure.Complex.IsNear.addLitP qz101 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz55 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz55 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz55 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz103 qz104 (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz55 2 k) 1)))) Bool.false 1168050029 2343100058 0 1 Bool.true 239589000

noncomputable def ep404 := @ep403 1171550029 0 1 Bool.false 1 336 0 1 Bool.false 11409 28000 0 1 Bool.false 394807909802 197403954901 393640809744 0 1 Bool.false 6657722280861 6657722280861 32803400812000 0 1

noncomputable abbrev qz133 := (@HDiv.hDiv Complex Complex Complex qz320 qz348 (@HSub.hSub Complex Complex Complex qz313 qz268 (1 : Complex)))

noncomputable def ep405 := @Enclosure.Complex.IsNear.addLitP qz133 qz76 Bool.true 28000000 18744800464 0 1 Bool.true 3833424000 18744800464 0 1

noncomputable def ep406 := @Enclosure.Complex.IsNear.of_eq qz133 (Complex.mk (Enclosure.sfrac Bool.true 28000000 18744800464) (Enclosure.sfrac Bool.true 3833424000 18744800464)) Bool.true 28000000 18744800464 0 1 Bool.true 3833424000 18744800464 0 1

noncomputable def ep407 := @ep405 Bool.false 1 2 0 1 Bool.false 0 1 0 1 Bool.false 18688800464 1168050029 2343100058 0 1 Bool.true 3833424000 239589000 1171550029 0 1 (ep406 (BSN.N_div_s_sub_one_mk qz17 68454 1000 14 qz18 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 28000000 18744800464) (Enclosure.sfrac Bool.true 3833424000 18744800464) Bool.true 28000000 18744800464 0 1 Bool.true 3833424000 18744800464 0 1 (Enclosure.Real.IsNear.const Bool.true 28000000 18744800464) (Enclosure.Real.IsNear.const Bool.true 3833424000 18744800464))) qz77 rfl

noncomputable abbrev qz134 := (@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 1)))

noncomputable abbrev qz135 := (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz349 qz348 1))

noncomputable def ep408 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz55 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz55 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz55 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz103 qz104 (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz55 2 k) 1)))) (@HAdd.hAdd Complex Complex Complex qz5 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz55 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz55 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz55 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz103 qz104 (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz55 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz78)) ↑qz134) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1))) qz135)) Bool.false 1 336 0 1

noncomputable def ep409 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz55 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz55 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz55 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz103 qz104 (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz55 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz78)) ↑qz134) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1))) qz135) Bool.false 0 1 0 1 Bool.false

noncomputable def ep410 := @ep409 0 1 0 1 Bool.false 1 336 0 1 Bool.false 11409 28000 0 1 Bool.false 1 1 336 0 1 Bool.false 11409 11409 28000 0

noncomputable def ep411 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz55 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz55 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz55 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz103 qz104 (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz55 2 k) 1)))) (Complex.mk qz14 qz14) Bool.false 0 1 0 1 Bool.false

noncomputable def ep412 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz78)) ↑qz134) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1))) qz135 Bool.false 1 336 0 1 Bool.false 11409 28000 0 1

noncomputable def ep413 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz78)) ↑qz134) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz135)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz78)) ↑qz134) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz135)) 1 336 0 1 0 1 0

noncomputable def ep414 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz78)) ↑qz134) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz135) 1 24 0 1 1 14 0 1 1

noncomputable def ep415 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz78)) ↑qz134)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz78)) ↑qz134)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)))) 1 24 0 1 0 1 0 1 1

noncomputable def ep416 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz78)) ↑qz134)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 1 2 0 1 1 24 0

noncomputable def ep417 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz78)) ↑qz134) (Complex.mk (Enclosure.sfrac Bool.false 1 12) qz14) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (BSN.bern_coeff_mk 1 1 6 2 Bool.false BSN.bern_real_1 EMRow17.d7 rfl) qz337

noncomputable def ep418 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)) qz6 Bool.false 1 2 0 1 Bool.false 68454 1000 0 1 (BSN.ascPochhammer_one_eval qz6)

noncomputable def ep419 := ep418 (@Enclosure.Complex.IsNear.of_eq qz6 (Complex.mk qz71 qz17) Bool.false 1 2 0 1 Bool.false 68454 1000 0 1 (BSN.s_crit_mk qz17 Bool.false 68454 1000 qz18) (@Enclosure.Complex.IsNear.mk qz71 qz17 Bool.false 1 2 0 1 Bool.false 68454 1000 0 1 qz329 qz22))

noncomputable def ep420 := @ep416 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz78)) ↑qz134) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep417) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 68454 1000 0 1 ep419)

noncomputable def ep421 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz78)) ↑qz134)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 68454 1000 0 1 0 1 0

noncomputable def ep422 := @ep421 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz78)) ↑qz134) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep417) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 68454 1000 0 1 ep419)

noncomputable def ep423 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz78)) ↑qz134)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz78)) ↑qz134)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)))) 11409 2000 0 1 0 1 0 1 11409

noncomputable def ep424 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz78)) ↑qz134)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 68454 1000 0 1 11409 2000 0

noncomputable def ep425 := @ep424 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz78)) ↑qz134) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep417) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 68454 1000 0 1 ep419)

noncomputable def ep426 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz78)) ↑qz134)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 1 2 0 1 0 1 0

noncomputable def ep427 := @ep426 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz78)) ↑qz134) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep417) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 68454 1000 0 1 ep419)

noncomputable def ep428 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz78)) ↑qz134) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 24 0 1 Bool.false 11409 2000 0 1 (@ep415 1 24 0 1 (ep420 rfl) (ep422 rfl) rfl rfl) (@ep423 11409 2000 0 1 (ep425 rfl) (ep427 rfl) rfl rfl)

noncomputable def ep429 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz78)) ↑qz134) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 11409 2000 0 1 ep428

noncomputable abbrev qz136 := (@Enclosure.Complex.IsNear.of_eq (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz349 qz348 1)) (Complex.mk (Enclosure.sfrac Bool.false 1 14) qz274) Bool.false 1 14 0 1 Bool.false 0 1 0 1 (BSN.natCast_pow_inv_mk 14 1 14 EMRow17.d8 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 14) qz274 Bool.false 1 14 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 14) qz286))

noncomputable def ep430 := @ep414 336 0 1 ep429 (@Enclosure.Complex.IsNear.re_isNear qz135 Bool.false 1 14 0 1 Bool.false 0 1 0 1 qz136)

noncomputable def ep431 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz78)) ↑qz134) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz135) 11409 2000 0 1 0 1 0 1 0

noncomputable def ep432 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz78)) ↑qz134) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 11409 2000 0 1 ep428

noncomputable def ep433 := @ep431 1 0 1 ep432 (@Enclosure.Complex.IsNear.im_isNear qz135 Bool.false 1 14 0 1 Bool.false 0 1 0 1 qz136)

noncomputable def ep434 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz78)) ↑qz134) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz135)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz78)) ↑qz134) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz135)) 0 1 0 1 11409 28000 0

noncomputable def ep435 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz78)) ↑qz134) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz135) 1 24 0 1 0 1 0 1 0

noncomputable def ep436 := @ep435 1 0 1 ep429 (@Enclosure.Complex.IsNear.im_isNear qz135 Bool.false 1 14 0 1 Bool.false 0 1 0 1 qz136)

noncomputable def ep437 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz78)) ↑qz134) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz135) 11409 2000 0 1 1 14 0 1 11409

noncomputable def ep438 := @ep437 28000 0 1 ep432 (@Enclosure.Complex.IsNear.re_isNear qz135 Bool.false 1 14 0 1 Bool.false 0 1 0 1 qz136)

noncomputable def ep439 := @ep410 1 (@ep411 0 1 0 1 (BSN.bern_sum_base qz6 14) qz92) (ep412 (@ep413 1 1 1 336 0 1 (ep430 rfl) (ep433 rfl) rfl rfl) (@ep434 1 11409 11409 28000 0 1 (ep436 rfl) (ep438 rfl) rfl rfl)) rfl rfl rfl rfl rfl

noncomputable def ep440 := ep404 (ep407 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep408 Bool.false 11409 28000 0 1 (BSN.bern_sum_succ qz6 14 0 1 1 rfl rfl) (ep439 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl rfl

noncomputable def ep441 := @Enclosure.Real.IsNear.mulLit_ff qz126 (Complex.im (@HAdd.hAdd Complex Complex Complex qz5 qz101 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz55 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz55 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz55 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz103 qz104 (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz55 2 k) 1)))))) 9182269251 34359738368 643676917473 2632918031663104 6657722280861

noncomputable def ep442 := @ep441 32803400812000 0 1 61132998581247546105111 1127116269480958754816000 ep388 ep389 (@Enclosure.Complex.IsNear.im_isNear qz100 Bool.false 448527321 137438953472 319358364781 1316459015831552 Bool.false 9182269251 34359738368 643676917473 2632918031663104 (ep392 ep400))

noncomputable def ep443 := @Enclosure.Complex.IsNear.im_isNear (@HAdd.hAdd Complex Complex Complex qz5 qz101 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz55 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz55 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz55 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz103 qz104 (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz55 2 k) 1))))) Bool.false 197403954901 393640809744 0 1 Bool.false

noncomputable def ep444 := nat_lit 2126199300781798572756441

noncomputable def ep445 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz125 (Complex.im (@HAdd.hAdd Complex Complex Complex qz5 qz101 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz55 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz55 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz55 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz103 qz104 (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz55 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz126 (Complex.re (@HAdd.hAdd Complex Complex Complex qz5 qz101 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz55 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz55 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz55 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz103 qz104 (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz55 2 k) 1))))))) 2986170338596593903381 ep298 ep444

noncomputable def ep446 := nat_lit 43184332748893453732020224000

noncomputable def ep447 := nat_lit 345474661991147629856161792

noncomputable def ep448 := nat_lit 2737502088334890777373297528150434499038019584

noncomputable def ep449 := @Enclosure.Real.IsNear.mulLit_ff qz125 (Complex.im (@HAdd.hAdd Complex Complex Complex qz5 qz101 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz55 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz55 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz55 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz103 qz104 (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz55 2 k) 1)))))) 448527321 137438953472 319358364781 1316459015831552 6657722280861

noncomputable def ep450 := @ep449 32803400812000 0 1 2986170338596593903381 ep298 ep444 ep446 (@Enclosure.Complex.IsNear.re_isNear qz100 Bool.false 448527321 137438953472 319358364781 1316459015831552 Bool.false 9182269251 34359738368 643676917473 2632918031663104 (ep392 ep400))

noncomputable def ep451 := @Enclosure.Real.IsNear.mulLit_ff qz126 (Complex.re (@HAdd.hAdd Complex Complex Complex qz5 qz101 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz55 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz55 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz55 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz103 qz104 (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz55 2 k) 1)))))) 9182269251 34359738368 643676917473 2632918031663104 197403954901

noncomputable def ep452 := @ep451 393640809744 0 1 604205421704414349717 4508465077923835019264 42354789729218263628391 ep447 (@Enclosure.Complex.IsNear.im_isNear qz100 Bool.false 448527321 137438953472 319358364781 1316459015831552 Bool.false 9182269251 34359738368 643676917473 2632918031663104 (ep392 ep400))

noncomputable abbrev qz377 := (ep440 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable def ep453 := @ep385 607191592043010943620381 ep298 ep304 ep300 (@ep386 ep387 61132998581247546105111 1127116269480958754816000 ep388 ep389 ep390 118576786035555494284347 ep169 ep303 ep171 (ep401 (@ep402 6657722280861 32803400812000 0 1 qz377) rfl) (ep442 (@ep443 6657722280861 32803400812000 0 1 qz377) rfl) rfl rfl) (@ep445 ep446 604205421704414349717 4508465077923835019264 42354789729218263628391 ep447 ep448 607191592043010943620381 ep298 ep304 ep300 (ep450 (@ep443 6657722280861 32803400812000 0 1 qz377) rfl) (ep452 (@ep402 6657722280861 32803400812000 0 1 qz377) rfl) rfl rfl)

noncomputable def ep454 := @ep307 ep299 ep300 (@ep308 5265836063326208 (BSN.head_sum_c_eq qz6 14) (ep309 (BSN.head_sum_c_succ qz6 13 14 rfl rfl) (ep384 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))) ep453 rfl rfl rfl

noncomputable def ep455 := @Enclosure.Complex.IsNear.re_isNear (zetaApproximant qz6 1 14) Bool.false ep168 ep169 ep170 ep171 Bool.true 137105469222103760453619 ep298 ep299 ep300 (@ep301 ep171 Bool.true 137105469222103760453619 ep298 ep299 ep300 (BSN.zetaApproximant_eq_folded' qz6 1 14 rfl) (ep454 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

noncomputable def ep456 := @Enclosure.Real.IsNear.mulLit_tt (Real.sin (@HSub.hSub Real Real Real qz47 (Complex.im (@HSub.hSub Complex Complex Complex qz48 qz49 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz50 (@Nat.cast Complex Complex.instNatCast j))))) qz51)) (Complex.im (zetaApproximant qz6 1 14)) 275 524288 4134885

noncomputable def ep457 := @Enclosure.Real.IsNear.recentre' (Real.sin (@HSub.hSub Real Real Real qz47 (Complex.im (@HSub.hSub Complex Complex Complex qz48 qz49 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz50 (@Nat.cast Complex Complex.instNatCast j))))) qz51)) Bool.true 275 524288 16539540

noncomputable def ep458 := @Enclosure.Real.IsNear.sin_image (@HSub.hSub Real Real Real qz47 (Complex.im (@HSub.hSub Complex Complex Complex qz48 qz49 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz50 (@Nat.cast Complex Complex.instNatCast j))))) qz51) qz316 Bool.false 24706765 524288 209

noncomputable def ep459 := BSN.sin_dyadic_bound_f 563328 1073741824 1 0 524288 153406 0 1 1 0 1 1 275 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 563328) qz283 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 563328) qz284 0 0 rfl) rfl rfl

noncomputable def ep460 := @ep458 524288 Bool.true 275 524288 1 76628 (@ep175 24706765 524288 209 524288 ep295 rfl) (Enclosure.sfrac_false_div 24706765 524288) (BSN.sin_reduce2 qz316 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 39640686905922682880) qz23) 226375608064910080 72057594037927936 Bool.false 275 524288 7 1000000000000000 153256 76628 (BSN.sin_reduce_arg_pos_rat_q2 24706765 524288 226375608064910080 72057594037927936 7 39640686905922682880 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 275 524288 39640686905922682880 75557863725914323419136 563328 1073741824 153406 153256 (ep459 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep461 := @Enclosure.Complex.IsNear.im_isNear (zetaApproximant qz6 1 14) Bool.false ep168 ep169 ep170 ep171 Bool.true 137105469222103760453619 ep298 ep299 ep300 (@ep301 ep171 Bool.true 137105469222103760453619 ep298 ep299 ep300 (BSN.zetaApproximant_eq_folded' qz6 1 14 rfl) (ep454 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

theorem EMRow17.d9 : Enclosure.Real.IsNear (hardyZApproximantEM 1 14 qz17) Bool.true ep151 ep152 ep153 ep154 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantEM 1 14 qz17) ep155 Bool.true ep151 ep152 ep153 ep154 (@Eq.refl Real ep155) (@ep156 Bool.true ep151 ep152 ep153 ep154 (BSN.re_exp_mul (@HSub.hSub Real Real Real qz47 (Complex.im (@HSub.hSub Complex Complex Complex qz48 qz49 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz50 (@Nat.cast Complex Complex.instNatCast j))))) qz51) (zetaApproximant qz6 1 14)) (@ep158 ep159 ep160 ep161 ep162 ep163 ep164 ep165 ep166 ep151 ep152 ep153 ep154 (@ep167 10043785216 ep168 ep169 ep170 ep171 ep157 ep159 ep160 ep161 (@ep172 40175140864 524287 524288 4134885 10043785216 (ep297 rfl rfl) rfl) ep455 rfl) (@ep456 10043785216 137105469222103760453619 ep298 ep299 ep300 ep162 ep163 ep164 ep165 (@ep457 40175140864 275 524288 4134885 10043785216 (ep460 rfl rfl) rfl) ep461 rfl) rfl rfl))

noncomputable abbrev qz490 := (@HAdd.hAdd Complex Complex Complex (@instHAdd Complex Complex.instAdd) (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (2 : Complex)) (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul) Complex.I ↑(Enclosure.sfrac Bool.false 71064 1000)))

noncomputable abbrev qz476 := qz490

noncomputable abbrev qz378 := qz476

noncomputable abbrev qz137 := (BSN.headSumC qz378 9)

noncomputable abbrev qz138 := qz378

noncomputable abbrev qz477 := (@Neg.neg Complex Complex.instNeg qz490)

noncomputable abbrev qz379 := qz477

noncomputable abbrev qz139 := (@HPow.hPow Complex Complex Complex qz270 (@Nat.cast Complex Complex.instNatCast 8) qz379)

noncomputable def ep462 := @Enclosure.Complex.IsNear.of_eq qz137 (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz138 8) qz139) Bool.false 210225092189 274877906944 16783494220929 5265836063326208 Bool.true 6601797251 274877906944 16783103686327 5265836063326208

noncomputable def ep463 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz138 8) qz139 Bool.false 306726182167 274877906944 15019879103503 5265836063326208 Bool.true 2262320825 34359738368 1878534205429 658229507915776 Bool.true

noncomputable abbrev qz140 := (@HPow.hPow Complex Complex Complex qz270 (@Nat.cast Complex Complex.instNatCast 7) qz379)

noncomputable def ep464 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz138 8) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz138 7) qz140) Bool.false 306726182167 274877906944 15019879103503 5265836063326208 Bool.true 2262320825 34359738368 1878534205429 658229507915776

noncomputable def ep465 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz138 7) qz140 Bool.false 202982303103 274877906944 13135113212523 5265836063326208 Bool.true 12508586533 274877906944 13152996578535 5265836063326208 Bool.false

noncomputable abbrev qz141 := (@HPow.hPow Complex Complex Complex qz270 (@Nat.cast Complex Complex.instNatCast 6) qz379)

noncomputable def ep466 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz138 7) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz138 6) qz141) Bool.false 202982303103 274877906944 13135113212523 5265836063326208 Bool.true 12508586533 274877906944 13152996578535 5265836063326208

noncomputable def ep467 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz138 6) qz141 Bool.false 106814836579 137438953472 5552563914019 2632918031663104 Bool.false 99203076425 274877906944 11113965699261 5265836063326208 Bool.true

noncomputable abbrev qz142 := (@HPow.hPow Complex Complex Complex qz270 (@Nat.cast Complex Complex.instNatCast 5) qz379)

noncomputable def ep468 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz138 6) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz138 5) qz142) Bool.false 106814836579 137438953472 5552563914019 2632918031663104 Bool.false 99203076425 274877906944 11113965699261 5265836063326208

noncomputable def ep469 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz138 5) qz142 Bool.false 177869164685 274877906944 8883995356299 5265836063326208 Bool.false 108407887461 137438953472 4443072797725 2632918031663104 Bool.false

noncomputable abbrev qz143 := (@HPow.hPow Complex Complex Complex qz270 (@Nat.cast Complex Complex.instNatCast 4) qz379)

noncomputable def ep470 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz138 5) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz138 4) qz143) Bool.false 177869164685 274877906944 8883995356299 5265836063326208 Bool.false 108407887461 137438953472 4443072797725 2632918031663104

noncomputable def ep471 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz138 4) qz143 Bool.false 14812465655 17179869184 3199826384565 2632918031663104 Bool.false 46373843655 137438953472 3198528727699 2632918031663104 Bool.true

noncomputable abbrev qz144 := (@HPow.hPow Complex Complex Complex qz270 qz272 qz379)

noncomputable def ep472 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz138 4) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz138 3) qz144) Bool.false 14812465655 17179869184 3199826384565 2632918031663104 Bool.false 46373843655 137438953472 3198528727699 2632918031663104

noncomputable def ep473 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz138 3) qz144 Bool.false 11831904611 8589934592 1759012147067 2632918031663104 Bool.false 20545792101 34359738368 440536198873 658229507915776 Bool.true

noncomputable abbrev qz145 := (@HPow.hPow Complex Complex Complex qz270 qz273 qz379)

noncomputable def ep474 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz138 3) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz138 2) qz145) Bool.false 11831904611 8589934592 1759012147067 2632918031663104 Bool.false 20545792101 34359738368 440536198873 658229507915776

noncomputable def ep475 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz138 2) qz145 Bool.false 1 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable def ep476 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz138 2) (Complex.mk (Enclosure.sfrac Bool.false 1 1) qz14) Bool.false 1 1 0 1 Bool.false 0 1 0 1 (BSN.head_sum_c_two qz138)

noncomputable abbrev qz491 := (Enclosure.sfrac Bool.false 71064 1000)

noncomputable abbrev qz478 := qz491

noncomputable abbrev qz380 := qz478

noncomputable abbrev qz146 := (@HMul.hMul Real Real Real qz263 qz380 (Real.log (Enclosure.sfrac Bool.false 2 1)))

noncomputable abbrev qz147 := qz380

noncomputable abbrev qz381 := (@Eq.refl Real qz478)

noncomputable abbrev qz148 := qz381

noncomputable def ep477 := @Enclosure.Complex.IsNear.of_eq qz145 (Complex.mk (@HMul.hMul Real Real Real qz0 qz15 (Real.cos qz146)) (@HMul.hMul Real Real Real qz0 qz15 (@Neg.neg Real Real.instNeg (Real.sin qz146)))) Bool.false 3241970019 8589934592 1759012147067 2632918031663104 Bool.false 20545792101 34359738368 440536198873 658229507915776 (BSN.cpow_neg_s_mk qz147 71064 1000 2 qz148 rfl)

noncomputable def ep478 := nat_lit 133568845584154468729012016640750096

noncomputable def ep479 := BSN.sin_dyadic_bound_f 604541742 1073741824 2 1 524288 153406 ep478 ep61 ep478 ep478 ep62 ep478 279836 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 604541742) qz283 0 1 ep478 ep61 ep478 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 604541742) qz284 0 1 ep478 ep62 ep478 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz382 := (Enclosure.Real.IsNear.const Bool.false 71064 1000)

noncomputable abbrev qz149 := qz382

noncomputable abbrev qz383 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 12912613) qz28)

noncomputable abbrev qz384 := (@Nat.cast Real Real.instNatCast 21270421628140090556416)

noncomputable def ep480 := @Enclosure.Real.IsNear.cos_image qz146 qz383 Bool.false 12912613 262144 487 524288 Bool.false 279836 524288 1 76628 (@Enclosure.Real.IsNear.recentre' qz146 Bool.false 201759579 4096000 8883 9578500 12912613 262144 487 524288 (@Enclosure.Real.IsNear.mulLit_ff qz147 qz21 71064 1000 0 1 181704 262144 1 76628 201759579 4096000 8883 9578500 qz149 qz281 rfl) rfl) (Enclosure.sfrac_false_div 12912613 262144) (BSN.cos_reduce3 qz383 (@HDiv.hDiv Real Real Real qz2 qz384 qz30) 226375608064910080 72057594037927936 Bool.false 279836 524288 7 1000000000000000 153256 76628 (BSN.sin_reduce_arg_pos_rat_q3 12912613 262144 226375608064910080 72057594037927936 7 21270421628140090556416 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 279836 524288 21270421628140090556416 37778931862957161709568 604541742 1073741824 153406 153256 (ep479 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep481 := BSN.cos_dyadic_bound_f 604541742 1073741824 2 1 524288 153406 ep478 ep57 ep478 ep478 ep58 ep478 443361 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 604541742) qz278 0 1 ep478 ep57 ep478 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 604541742) qz279 0 1 ep478 ep58 ep478 rfl rfl rfl rfl) rfl rfl

noncomputable def ep482 := @Enclosure.Real.IsNear.sin_image qz146 qz383 Bool.false 12912613 262144 487 524288 Bool.true 443361 524288 1 76628 (@Enclosure.Real.IsNear.recentre' qz146 Bool.false 201759579 4096000 8883 9578500 12912613 262144 487 524288 (@Enclosure.Real.IsNear.mulLit_ff qz147 qz21 71064 1000 0 1 181704 262144 1 76628 201759579 4096000 8883 9578500 qz149 qz281 rfl) rfl) (Enclosure.sfrac_false_div 12912613 262144) (BSN.sin_reduce3 qz383 (@HDiv.hDiv Real Real Real qz2 qz384 qz30) 226375608064910080 72057594037927936 Bool.false 443361 524288 7 1000000000000000 153256 76628 (BSN.sin_reduce_arg_pos_rat_q3 12912613 262144 226375608064910080 72057594037927936 7 21270421628140090556416 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 443361 524288 21270421628140090556416 37778931862957161709568 604541742 1073741824 153406 153256 (ep481 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep483 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz15 (Real.cos qz146)) (@HMul.hMul Real Real Real qz0 qz15 (@Neg.neg Real Real.instNeg (Real.sin qz146))) Bool.false 3241970019 8589934592 1759012147067 2632918031663104 Bool.false 20545792101 34359738368 440536198873 658229507915776 (@Enclosure.Real.IsNear.mulLit_ff qz15 (Real.cos qz146) 46341 65536 1 262144 69959 131072 9460531 10043785216 3241970019 8589934592 1759012147067 2632918031663104 qz285 (@Enclosure.Real.IsNear.recentre' (Real.cos qz146) Bool.false 279836 524288 37842124 40175140864 69959 131072 9460531 10043785216 (ep480 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz15 (@Neg.neg Real Real.instNeg (Real.sin qz146)) 46341 65536 1 262144 443361 524288 9460531 10043785216 20545792101 34359738368 440536198873 658229507915776 qz285 (@Enclosure.Real.IsNear.neg (Real.sin qz146) Bool.true 443361 524288 9460531 10043785216 (@Enclosure.Real.IsNear.recentre' (Real.sin qz146) Bool.true 443361 524288 37842124 40175140864 443361 524288 9460531 10043785216 (ep482 rfl rfl) rfl)) rfl)

noncomputable def ep484 := @ep475 3241970019 8589934592 1759012147067 2632918031663104 Bool.false 20545792101 34359738368 440536198873 658229507915776 Bool.false 11831904611 11831904611 8589934592 1759012147067 2632918031663104 Bool.false 20545792101 20545792101 34359738368 440536198873 658229507915776 (ep476 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 1) qz14 Bool.false 1 1 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 1) qz24)) (ep477 ep483) rfl rfl

noncomputable abbrev qz150 := (@HMul.hMul Real Real Real qz263 qz380 (Real.log (Enclosure.sfrac Bool.false 3 1)))

noncomputable def ep485 := @Enclosure.Complex.IsNear.of_eq qz144 (Complex.mk (@HMul.hMul Real Real Real qz0 qz25 (Real.cos qz150)) (@HMul.hMul Real Real Real qz0 qz25 (@Neg.neg Real Real.instNeg (Real.sin qz150)))) Bool.true 8851343567 17179869184 720407118749 1316459015831552 Bool.true 35809324749 137438953472 1436383932207 2632918031663104 (BSN.cpow_neg_s_mk qz147 71064 1000 3 qz148 rfl)

noncomputable def ep486 := nat_lit 7900550479409141443230074992027926253539191119598084825800574712188593097185

noncomputable def ep487 := nat_lit 3859470773131980357187930741725545806456025892542497496663665707395697121

noncomputable def ep488 := nat_lit 20685669255296013906929034996015108351773143176073724785911668787443865078241

noncomputable def ep489 := BSN.sin_dyadic_bound_f 1183902587 1073741824 3 2 524288 153406 ep486 ep71 ep487 ep488 ep74 ep487 467864 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1183902587) qz283 0 2 ep486 ep71 ep487 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1183902587) qz284 0 2 ep488 ep74 ep487 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz385 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 40932011) qz20)

noncomputable def ep490 := @Enclosure.Real.IsNear.cos_image qz150 qz385 Bool.false 40932011 524288 487 524288 Bool.true 467864 524288 1 76628 (@Enclosure.Real.IsNear.recentre' qz150 Bool.false 1279125351 16384000 8883 9578500 40932011 524288 487 524288 (@Enclosure.Real.IsNear.mulLit_ff qz147 qz29 71064 1000 0 1 287994 262144 1 76628 1279125351 16384000 8883 9578500 qz149 qz288 rfl) rfl) (Enclosure.sfrac_false_div 40932011 524288) (BSN.cos_reduce1 qz385 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 83309738332358161989632) qz23) 226375608064910080 72057594037927936 Bool.false 467864 524288 12 1000000000000000 153256 76628 (BSN.sin_reduce_arg_pos_rat_q1 40932011 524288 226375608064910080 72057594037927936 12 83309738332358161989632 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 467864 524288 83309738332358161989632 75557863725914323419136 1183902587 1073741824 153406 153256 (ep489 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep491 := nat_lit 4390910031126470570842125187011837050102419966840066013221058691530283141601

noncomputable def ep492 := nat_lit 13165011151833147751811999699552060058694347848735113044669848743176058030561

noncomputable def ep493 := BSN.cos_dyadic_bound_f 1183902587 1073741824 3 2 524288 153406 ep491 ep78 ep487 ep492 ep80 ep487 236601 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1183902587) qz278 0 2 ep491 ep78 ep487 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1183902587) qz279 0 2 ep492 ep80 ep487 rfl rfl rfl rfl) rfl rfl

noncomputable def ep494 := @Enclosure.Real.IsNear.sin_image qz150 qz385 Bool.false 40932011 524288 487 524288 Bool.false 236601 524288 1 76628 (@Enclosure.Real.IsNear.recentre' qz150 Bool.false 1279125351 16384000 8883 9578500 40932011 524288 487 524288 (@Enclosure.Real.IsNear.mulLit_ff qz147 qz29 71064 1000 0 1 287994 262144 1 76628 1279125351 16384000 8883 9578500 qz149 qz288 rfl) rfl) (Enclosure.sfrac_false_div 40932011 524288) (BSN.sin_reduce1 qz385 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 83309738332358161989632) qz23) 226375608064910080 72057594037927936 Bool.false 236601 524288 12 1000000000000000 153256 76628 (BSN.sin_reduce_arg_pos_rat_q1 40932011 524288 226375608064910080 72057594037927936 12 83309738332358161989632 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 236601 524288 83309738332358161989632 75557863725914323419136 1183902587 1073741824 153406 153256 (ep493 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep495 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz25 (Real.cos qz150)) (@HMul.hMul Real Real Real qz0 qz25 (@Neg.neg Real Real.instNeg (Real.sin qz150))) Bool.true 8851343567 17179869184 720407118749 1316459015831552 Bool.true 35809324749 137438953472 1436383932207 2632918031663104 (@Enclosure.Real.IsNear.mulLit_ft qz25 (Real.cos qz150) 151349 262144 1 262144 58483 65536 9460531 10043785216 8851343567 17179869184 720407118749 1316459015831552 qz289 (@Enclosure.Real.IsNear.recentre' (Real.cos qz150) Bool.true 467864 524288 37842124 40175140864 58483 65536 9460531 10043785216 (ep490 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz25 (@Neg.neg Real Real.instNeg (Real.sin qz150)) 151349 262144 1 262144 236601 524288 9460531 10043785216 35809324749 137438953472 1436383932207 2632918031663104 qz289 (@Enclosure.Real.IsNear.neg (Real.sin qz150) Bool.false 236601 524288 9460531 10043785216 (@Enclosure.Real.IsNear.recentre' (Real.sin qz150) Bool.false 236601 524288 37842124 40175140864 236601 524288 9460531 10043785216 (ep494 rfl rfl) rfl)) rfl)

noncomputable def ep496 := @ep473 8851343567 17179869184 720407118749 1316459015831552 Bool.true 35809324749 137438953472 1436383932207 2632918031663104 Bool.false 127238111122696437760 14812465655 17179869184 3199826384565 2632918031663104 Bool.false 1593393135104336855040 46373843655 137438953472 3198528727699 2632918031663104 (ep474 (BSN.head_sum_c_succ qz138 2 3 rfl rfl) (ep484 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep485 ep495) rfl rfl

noncomputable abbrev qz151 := (@HMul.hMul Real Real Real qz263 qz380 (Real.log (Enclosure.sfrac Bool.false 4 1)))

noncomputable def ep497 := @Enclosure.Complex.IsNear.of_eq qz143 (Complex.mk (@HMul.hMul Real Real Real qz0 qz31 (Real.cos qz151)) (@HMul.hMul Real Real Real qz0 qz31 (@Neg.neg Real Real.instNeg (Real.sin qz151)))) Bool.true 59130285795 274877906944 2484342587169 5265836063326208 Bool.false 31017021903 68719476736 622272035013 1316459015831552 (BSN.cpow_neg_s_mk qz147 71064 1000 4 qz148 rfl)

noncomputable def ep498 := nat_lit 4776935125604045407146314344810303075037629524492001184934511568014784190625

noncomputable def ep499 := nat_lit 4567202976954300216483469128894856568274804766483030391978833477875390625

noncomputable def ep500 := nat_lit 14321670970858227621005976096173119511976338963943037494019577037088601790625

noncomputable def ep501 := BSN.cos_dyadic_bound_f 1209083485 1073741824 3 2 524288 153406 ep498 ep78 ep499 ep500 ep80 ep499 225565 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1209083485) qz278 0 2 ep498 ep78 ep499 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1209083485) qz279 0 2 ep500 ep80 ep499 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz386 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 12912613) (@Nat.cast Real Real.instNatCast 131072))

noncomputable def ep502 := @Enclosure.Real.IsNear.cos_image qz151 qz386 Bool.false 12912613 131072 487 524288 Bool.true 225565 524288 1 76628 (@Enclosure.Real.IsNear.recentre' qz151 Bool.false 201759579 2048000 8883 9578500 12912613 131072 487 524288 (@Enclosure.Real.IsNear.mulLit_ff qz147 qz33 71064 1000 0 1 363408 262144 1 76628 201759579 2048000 8883 9578500 qz149 qz292 rfl) rfl) (Enclosure.sfrac_false_div 12912613 131072) (BSN.cos_reduce2 qz386 (@HDiv.hDiv Real Real Real qz2 qz384 qz302) 226375608064910080 72057594037927936 Bool.false 225565 524288 15 1000000000000000 153256 76628 (BSN.sin_reduce_arg_pos_rat_q2 12912613 131072 226375608064910080 72057594037927936 15 21270421628140090556416 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 225565 524288 21270421628140090556416 18889465931478580854784 1209083485 1073741824 153406 153256 (ep501 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep503 := nat_lit 8594829463705718292690179045355429649813113300272415708568537755644311230625

noncomputable def ep504 := nat_lit 22502873123933240947171400454484105029352375626329640044663918867723302590625

noncomputable def ep505 := BSN.sin_dyadic_bound_f 1209083485 1073741824 3 2 524288 153406 ep503 ep71 ep499 ep504 ep74 ep499 473284 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1209083485) qz283 0 2 ep503 ep71 ep499 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1209083485) qz284 0 2 ep504 ep74 ep499 rfl rfl rfl rfl) rfl rfl

noncomputable def ep506 := @Enclosure.Real.IsNear.sin_image qz151 qz386 Bool.false 12912613 131072 487 524288 Bool.true 473284 524288 1 76628 (@Enclosure.Real.IsNear.recentre' qz151 Bool.false 201759579 2048000 8883 9578500 12912613 131072 487 524288 (@Enclosure.Real.IsNear.mulLit_ff qz147 qz33 71064 1000 0 1 363408 262144 1 76628 201759579 2048000 8883 9578500 qz149 qz292 rfl) rfl) (Enclosure.sfrac_false_div 12912613 131072) (BSN.sin_reduce2 qz386 (@HDiv.hDiv Real Real Real qz2 qz384 qz302) 226375608064910080 72057594037927936 Bool.false 473284 524288 15 1000000000000000 153256 76628 (BSN.sin_reduce_arg_pos_rat_q2 12912613 131072 226375608064910080 72057594037927936 15 21270421628140090556416 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 473284 524288 21270421628140090556416 18889465931478580854784 1209083485 1073741824 153406 153256 (ep505 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep507 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz31 (Real.cos qz151)) (@HMul.hMul Real Real Real qz0 qz31 (@Neg.neg Real Real.instNeg (Real.sin qz151))) Bool.true 59130285795 274877906944 2484342587169 5265836063326208 Bool.false 31017021903 68719476736 622272035013 1316459015831552 (@Enclosure.Real.IsNear.mulLit_ft qz31 (Real.cos qz151) 262143 524288 1 524288 225565 524288 9460531 10043785216 59130285795 274877906944 2484342587169 5265836063326208 qz293 (@Enclosure.Real.IsNear.recentre' (Real.cos qz151) Bool.true 225565 524288 37842124 40175140864 225565 524288 9460531 10043785216 (ep502 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz31 (@Neg.neg Real Real.instNeg (Real.sin qz151)) 262143 524288 1 524288 118321 131072 9460531 10043785216 31017021903 68719476736 622272035013 1316459015831552 qz293 (@Enclosure.Real.IsNear.neg (Real.sin qz151) Bool.true 118321 131072 9460531 10043785216 (@Enclosure.Real.IsNear.recentre' (Real.sin qz151) Bool.true 473284 524288 37842124 40175140864 118321 131072 9460531 10043785216 (ep506 rfl rfl) rfl)) rfl)

noncomputable def ep508 := @ep471 59130285795 274877906944 2484342587169 5265836063326208 Bool.false 31017021903 68719476736 622272035013 1316459015831552 Bool.false 3055768981155652567040 177869164685 274877906944 8883995356299 5265836063326208 Bool.false 7449733300375095607296 108407887461 137438953472 4443072797725 2632918031663104 (ep472 (BSN.head_sum_c_succ qz138 3 4 rfl rfl) (ep496 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep497 ep507) rfl rfl

noncomputable abbrev qz152 := (@HMul.hMul Real Real Real qz263 qz380 (Real.log (Enclosure.sfrac Bool.false 5 1)))

noncomputable def ep509 := @Enclosure.Complex.IsNear.of_eq qz142 (Complex.mk (@HMul.hMul Real Real Real qz0 qz34 (Real.cos qz152)) (@HMul.hMul Real Real Real qz0 qz34 (@Neg.neg Real Real.instNeg (Real.sin qz152)))) Bool.false 35760508473 274877906944 2221132471739 5265836063326208 Bool.true 117612698497 274877906944 2227820103811 5265836063326208 (BSN.cpow_neg_s_mk qz147 71064 1000 5 qz148 rfl)

noncomputable def ep510 := nat_lit 7871998137325546871643621461138565120899551821646363412366355313962120191521

noncomputable def ep511 := nat_lit 12387524828740246826213978445790713069340339636200915644585198173387038241

noncomputable def ep512 := nat_lit 23591219362319160121278436426524113936559974785666688405809895545539586498081

noncomputable def ep513 := BSN.cos_dyadic_bound_f 1369692467 1073741824 3 2 524288 153406 ep510 ep78 ep511 ep512 ep80 ep511 152517 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1369692467) qz278 0 2 ep510 ep78 ep511 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1369692467) qz279 0 2 ep512 ep80 ep511 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz387 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 59964371) qz20)

noncomputable def ep514 := @Enclosure.Real.IsNear.cos_image qz152 qz387 Bool.false 59964371 524288 487 524288 Bool.false 152517 524288 1 76628 (@Enclosure.Real.IsNear.recentre' qz152 Bool.false 234235827 2048000 8883 9578500 59964371 524288 487 524288 (@Enclosure.Real.IsNear.mulLit_ff qz147 qz36 71064 1000 0 1 421904 262144 1 76628 234235827 2048000 8883 9578500 qz149 qz296 rfl) rfl) (Enclosure.sfrac_false_div 59964371 524288) (BSN.cos_reduce0 qz387 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 96383538833636177477632) qz23) 226375608064910080 72057594037927936 Bool.false 152517 524288 18 1000000000000000 153256 76628 (BSN.sin_reduce_arg_pos_rat_q0 59964371 524288 226375608064910080 72057594037927936 18 96383538833636177477632 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 152517 524288 96383538833636177477632 75557863725914323419136 1369692467 1073741824 153406 153256 (ep513 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep515 := nat_lit 14159686627322992171497547447292784647163721007254493409743771406593106714145

noncomputable def ep516 := nat_lit 37064837555170828620965420682568870064268908754826966971618644315463129046561

noncomputable def ep517 := BSN.sin_dyadic_bound_f 1369692467 1073741824 3 2 524288 153406 ep515 ep71 ep511 ep516 ep74 ep511 501613 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1369692467) qz283 0 2 ep515 ep71 ep511 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1369692467) qz284 0 2 ep516 ep74 ep511 rfl rfl rfl rfl) rfl rfl

noncomputable def ep518 := @Enclosure.Real.IsNear.sin_image qz152 qz387 Bool.false 59964371 524288 487 524288 Bool.false 501613 524288 1 76628 (@Enclosure.Real.IsNear.recentre' qz152 Bool.false 234235827 2048000 8883 9578500 59964371 524288 487 524288 (@Enclosure.Real.IsNear.mulLit_ff qz147 qz36 71064 1000 0 1 421904 262144 1 76628 234235827 2048000 8883 9578500 qz149 qz296 rfl) rfl) (Enclosure.sfrac_false_div 59964371 524288) (BSN.sin_reduce0 qz387 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 96383538833636177477632) qz23) 226375608064910080 72057594037927936 Bool.false 501613 524288 18 1000000000000000 153256 76628 (BSN.sin_reduce_arg_pos_rat_q0 59964371 524288 226375608064910080 72057594037927936 18 96383538833636177477632 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 501613 524288 96383538833636177477632 75557863725914323419136 1369692467 1073741824 153406 153256 (ep517 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep519 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz34 (Real.cos qz152)) (@HMul.hMul Real Real Real qz0 qz34 (@Neg.neg Real Real.instNeg (Real.sin qz152))) Bool.false 35760508473 274877906944 2221132471739 5265836063326208 Bool.true 117612698497 274877906944 2227820103811 5265836063326208 (@Enclosure.Real.IsNear.mulLit_ff qz34 (Real.cos qz152) 234469 524288 1 524288 152517 524288 9460531 10043785216 35760508473 274877906944 2221132471739 5265836063326208 qz298 (@Enclosure.Real.IsNear.recentre' (Real.cos qz152) Bool.false 152517 524288 37842124 40175140864 152517 524288 9460531 10043785216 (ep514 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz34 (@Neg.neg Real Real.instNeg (Real.sin qz152)) 234469 524288 1 524288 501613 524288 9460531 10043785216 117612698497 274877906944 2227820103811 5265836063326208 qz298 (@Enclosure.Real.IsNear.neg (Real.sin qz152) Bool.false 501613 524288 9460531 10043785216 (@Enclosure.Real.IsNear.recentre' (Real.sin qz152) Bool.false 501613 524288 37842124 40175140864 501613 524288 9460531 10043785216 (ep518 rfl rfl) rfl)) rfl)

noncomputable def ep520 := @ep469 35760508473 274877906944 2221132471739 5265836063326208 Bool.true 117612698497 274877906944 2227820103811 5265836063326208 Bool.false 58722077418801858609152 106814836579 137438953472 5552563914019 2632918031663104 Bool.false 13634367005054835097600 99203076425 274877906944 11113965699261 5265836063326208 (ep470 (BSN.head_sum_c_succ qz138 4 5 rfl rfl) (ep508 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep509 ep519) rfl rfl

noncomputable abbrev qz153 := (@HMul.hMul Real Real Real qz263 qz380 (Real.log (Enclosure.sfrac Bool.false 6 1)))

noncomputable def ep521 := @Enclosure.Complex.IsNear.of_eq qz141 (Complex.mk (@HMul.hMul Real Real Real qz0 qz37 (Real.cos qz153)) (@HMul.hMul Real Real Real qz0 qz37 (@Neg.neg Real Real.instNeg (Real.sin qz153)))) Bool.true 10647370055 274877906944 2029985384485 5265836063326208 Bool.true 55855831479 137438953472 1019515439637 2632918031663104 (BSN.cpow_neg_s_mk qz147 71064 1000 6 qz148 rfl)

noncomputable def ep522 := @Enclosure.Real.IsNear.mulLit_ff qz147 qz39 71064 1000 0 1 4034681531866359 2251799813685248 125000000019157 9578500000000000000 35840076047568866997 281474976710656000 1110375000170171631 1197312500000000000000 qz149 (BSN.isNear_log_sfrac 6 1 4034681531866359 2251799813685248 125000000019157 9578500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz300) Bool.false 16922680887833197019136 9444732965739290427392 1000000000153256 76628000000000000000 4034681531866359 2251799813685248 125000000019157 9578500000000000000 (BSN.log_rat_reduce_isNear 6 1 2 12 8 106290 262144 24973259072661432 36028797018963968 76628 1000000000000000 rfl rfl rfl rfl (ep112 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep523 := BSN.sin_dyadic_bound_f 102031705 1073741824 1 0 524288 153406 0 1 1 0 1 1 49745 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 102031705) qz283 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 102031705) qz284 0 0 rfl) rfl rfl

noncomputable abbrev qz388 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 66757343) qz20)

noncomputable def ep524 := @Enclosure.Real.IsNear.cos_image qz153 qz388 Bool.false 66757343 524288 61 65536 Bool.true 49745 524288 1 76628 (@Enclosure.Real.IsNear.recentre' qz153 Bool.false 35840076047568866997 281474976710656000 1110375000170171631 1197312500000000000000 66757343 524288 61 65536 (ep522 rfl) rfl) (Enclosure.sfrac_false_div 66757343 524288) (BSN.cos_reduce1 qz388 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 7179842997438807801856) qz23) 226375608064910080 72057594037927936 Bool.false 49745 524288 20 1000000000000000 153256 76628 (BSN.sin_reduce_arg_pos_rat_q1 66757343 524288 226375608064910080 72057594037927936 20 7179842997438807801856 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 49745 524288 7179842997438807801856 75557863725914323419136 102031705 1073741824 153406 153256 (ep523 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep525 := nat_lit 108377861160607335242034109350625

noncomputable def ep526 := BSN.cos_dyadic_bound_f 102031705 1073741824 2 1 524288 153406 ep525 ep57 ep525 ep525 ep58 ep525 521922 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 102031705) qz278 0 1 ep525 ep57 ep525 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 102031705) qz279 0 1 ep525 ep58 ep525 rfl rfl rfl rfl) rfl rfl

noncomputable def ep527 := @Enclosure.Real.IsNear.sin_image qz153 qz388 Bool.false 66757343 524288 61 65536 Bool.false 521922 524288 1 76628 (@Enclosure.Real.IsNear.recentre' qz153 Bool.false 35840076047568866997 281474976710656000 1110375000170171631 1197312500000000000000 66757343 524288 61 65536 (ep522 rfl) rfl) (Enclosure.sfrac_false_div 66757343 524288) (BSN.sin_reduce1 qz388 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 7179842997438807801856) qz23) 226375608064910080 72057594037927936 Bool.false 521922 524288 20 1000000000000000 153256 76628 (BSN.sin_reduce_arg_pos_rat_q1 66757343 524288 226375608064910080 72057594037927936 20 7179842997438807801856 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 521922 524288 7179842997438807801856 75557863725914323419136 102031705 1073741824 153406 153256 (ep526 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep528 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz37 (Real.cos qz153)) (@HMul.hMul Real Real Real qz0 qz37 (@Neg.neg Real Real.instNeg (Real.sin qz153))) Bool.true 10647370055 274877906944 2029985384485 5265836063326208 Bool.true 55855831479 137438953472 1019515439637 2632918031663104 (@Enclosure.Real.IsNear.mulLit_ft qz37 (Real.cos qz153) 214039 524288 1 524288 49745 524288 1184961 1255473152 10647370055 274877906944 2029985384485 5265836063326208 qz303 (@Enclosure.Real.IsNear.recentre' (Real.cos qz153) Bool.true 49745 524288 4739844 5021892608 49745 524288 1184961 1255473152 (ep524 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz37 (@Neg.neg Real Real.instNeg (Real.sin qz153)) 214039 524288 1 524288 260961 262144 1184961 1255473152 55855831479 137438953472 1019515439637 2632918031663104 qz303 (@Enclosure.Real.IsNear.neg (Real.sin qz153) Bool.false 260961 262144 1184961 1255473152 (@Enclosure.Real.IsNear.recentre' (Real.sin qz153) Bool.false 521922 524288 4739844 5021892608 260961 262144 1184961 1255473152 (ep527 rfl rfl) rfl)) rfl)

noncomputable def ep529 := @ep467 10647370055 274877906944 2029985384485 5265836063326208 Bool.true 55855831479 137438953472 1019515439637 2632918031663104 Bool.false 27897675311812618223616 202982303103 274877906944 13135113212523 5265836063326208 Bool.true 1719167042509472792576 12508586533 274877906944 13152996578535 5265836063326208 (ep468 (BSN.head_sum_c_succ qz138 5 6 rfl rfl) (ep520 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep521 ep528) rfl rfl

noncomputable abbrev qz154 := (@HMul.hMul Real Real Real qz263 qz380 (Real.log (Enclosure.sfrac Bool.false 7 1)))

noncomputable def ep530 := @Enclosure.Complex.IsNear.of_eq qz140 (Complex.mk (@HMul.hMul Real Real Real qz0 qz40 (Real.cos qz154)) (@HMul.hMul Real Real Real qz0 qz40 (@Neg.neg Real Real.instNeg (Real.sin qz154)))) Bool.false 12967984883 34359738368 471191472745 1316459015831552 Bool.true 5589980067 274877906944 1875277064897 5265836063326208 (BSN.cpow_neg_s_mk qz147 71064 1000 7 qz148 rfl)

noncomputable def ep531 := @Enclosure.Real.IsNear.mulLit_ff qz147 qz42 71064 1000 0 1 4381792198794487 2251799813685248 125000000019157 9578500000000000000 38923460101891428021 281474976710656000 1110375000170171631 1197312500000000000000 qz149 (BSN.isNear_log_sfrac 7 1 4381792198794487 2251799813685248 125000000019157 9578500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz305) Bool.false 18378568546572512002048 9444732965739290427392 1000000000153256 76628000000000000000 4381792198794487 2251799813685248 125000000019157 9578500000000000000 (BSN.log_rat_reduce_isNear 7 1 2 14 8 146699 262144 24973259072661432 36028797018963968 76628 1000000000000000 rfl rfl rfl rfl (ep123 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep532 := BSN.cos_dyadic_bound_f 57801762 1073741824 1 0 524288 153406 0 1 1 0 1 1 523528 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 57801762) qz278 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 57801762) qz279 0 0 rfl) rfl rfl

noncomputable abbrev qz389 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 36250297) qz28)

noncomputable def ep533 := @Enclosure.Real.IsNear.cos_image qz154 qz389 Bool.false 36250297 262144 487 524288 Bool.false 523528 524288 1 76628 (@Enclosure.Real.IsNear.recentre' qz154 Bool.false 38923460101891428021 281474976710656000 1110375000170171631 1197312500000000000000 36250297 262144 487 524288 (ep531 rfl) rfl) (Enclosure.sfrac_false_div 36250297 262144) (BSN.cos_reduce0 qz389 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 2033718710668544180224) qz30) 226375608064910080 72057594037927936 Bool.false 523528 524288 22 1000000000000000 153256 76628 (BSN.sin_reduce_arg_pos_rat_q0 36250297 262144 226375608064910080 72057594037927936 22 2033718710668544180224 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 523528 524288 2033718710668544180224 37778931862957161709568 57801762 1073741824 153406 153256 (ep532 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep534 := BSN.sin_dyadic_bound_f 57801762 1073741824 1 0 524288 153406 0 1 1 0 1 1 28209 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 57801762) qz283 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 57801762) qz284 0 0 rfl) rfl rfl

noncomputable def ep535 := @Enclosure.Real.IsNear.sin_image qz154 qz389 Bool.false 36250297 262144 487 524288 Bool.false 28209 524288 1 76628 (@Enclosure.Real.IsNear.recentre' qz154 Bool.false 38923460101891428021 281474976710656000 1110375000170171631 1197312500000000000000 36250297 262144 487 524288 (ep531 rfl) rfl) (Enclosure.sfrac_false_div 36250297 262144) (BSN.sin_reduce0 qz389 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 2033718710668544180224) qz30) 226375608064910080 72057594037927936 Bool.false 28209 524288 22 1000000000000000 153256 76628 (BSN.sin_reduce_arg_pos_rat_q0 36250297 262144 226375608064910080 72057594037927936 22 2033718710668544180224 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 28209 524288 2033718710668544180224 37778931862957161709568 57801762 1073741824 153406 153256 (ep534 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep536 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz40 (Real.cos qz154)) (@HMul.hMul Real Real Real qz0 qz40 (@Neg.neg Real Real.instNeg (Real.sin qz154))) Bool.false 12967984883 34359738368 471191472745 1316459015831552 Bool.true 5589980067 274877906944 1875277064897 5265836063326208 (@Enclosure.Real.IsNear.mulLit_ff qz40 (Real.cos qz154) 198163 524288 1 524288 65441 65536 9460531 10043785216 12967984883 34359738368 471191472745 1316459015831552 qz307 (@Enclosure.Real.IsNear.recentre' (Real.cos qz154) Bool.false 523528 524288 37842124 40175140864 65441 65536 9460531 10043785216 (ep533 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz40 (@Neg.neg Real Real.instNeg (Real.sin qz154)) 198163 524288 1 524288 28209 524288 9460531 10043785216 5589980067 274877906944 1875277064897 5265836063326208 qz307 (@Enclosure.Real.IsNear.neg (Real.sin qz154) Bool.false 28209 524288 9460531 10043785216 (@Enclosure.Real.IsNear.recentre' (Real.sin qz154) Bool.false 28209 524288 37842124 40175140864 28209 524288 9460531 10043785216 (ep535 rfl rfl) rfl)) rfl)

noncomputable def ep537 := @ep465 12967984883 34359738368 471191472745 1316459015831552 Bool.true 5589980067 274877906944 1875277064897 5265836063326208 Bool.false 10539031369873627283456 306726182167 274877906944 15019879103503 5265836063326208 Bool.true 4974896105694586470400 2262320825 34359738368 1878534205429 658229507915776 (ep466 (BSN.head_sum_c_succ qz138 6 7 rfl rfl) (ep529 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep530 ep536) rfl rfl

noncomputable abbrev qz155 := (@HMul.hMul Real Real Real qz263 qz380 (Real.log (Enclosure.sfrac Bool.false 8 1)))

noncomputable def ep538 := @Enclosure.Complex.IsNear.of_eq qz139 (Complex.mk (@HMul.hMul Real Real Real qz0 qz43 (Real.cos qz155)) (@HMul.hMul Real Real Real qz0 qz43 (@Neg.neg Real Real.instNeg (Real.sin qz155)))) Bool.true 48250544989 137438953472 881807558713 2632918031663104 Bool.false 11496769349 274877906944 1754830042895 5265836063326208 (BSN.cpow_neg_s_mk qz147 71064 1000 8 qz148 rfl)

noncomputable def ep539 := @Enclosure.Real.IsNear.mulLit_ff qz147 qz45 71064 1000 0 1 9364972152248037 4503599627370496 250000000057471 19157000000000000000 83189047628419312671 562949953421312000 2220750000510514893 2394625000000000000000 qz149 (BSN.isNear_log_sfrac 8 1 9364972152248037 4503599627370496 250000000057471 19157000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz309) Bool.false 19639770079031275290624 9444732965739290427392 1000000000229884 76628000000000000000 9364972152248037 4503599627370496 250000000057471 19157000000000000000 (BSN.log_rat_reduce_isNear 8 1 3 16 16 0 262144 24973259072661432 36028797018963968 76628 1000000000000000 rfl rfl rfl rfl (ep138 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep540 := nat_lit 262802875264340309920559314400625

noncomputable def ep541 := BSN.cos_dyadic_bound_f 127323195 1073741824 2 1 524288 153406 ep540 ep57 ep540 ep540 ep58 ep540 520606 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 127323195) qz278 0 1 ep540 ep57 ep540 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 127323195) qz279 0 1 ep540 ep58 ep540 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz390 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 38737919) qz28)

noncomputable def ep542 := @Enclosure.Real.IsNear.cos_image qz155 qz390 Bool.false 38737919 262144 487 524288 Bool.true 520606 524288 1 76628 (@Enclosure.Real.IsNear.recentre' qz155 Bool.false 83189047628419312671 562949953421312000 2220750000510514893 2394625000000000000000 38737919 262144 487 524288 (ep539 rfl) rfl) (Enclosure.sfrac_false_div 38737919 262144) (BSN.cos_reduce2 qz390 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 4479786698898552127488) qz30) 226375608064910080 72057594037927936 Bool.false 520606 524288 23 1000000000000000 153256 76628 (BSN.sin_reduce_arg_pos_rat_q2 38737919 262144 226375608064910080 72057594037927936 23 4479786698898552127488 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 520606 524288 4479786698898552127488 37778931862957161709568 127323195 1073741824 153406 153256 (ep541 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep543 := BSN.sin_dyadic_bound_f 127323195 1073741824 1 0 524288 153406 0 1 1 0 1 1 62023 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 127323195) qz283 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 127323195) qz284 0 0 rfl) rfl rfl

noncomputable def ep544 := @Enclosure.Real.IsNear.sin_image qz155 qz390 Bool.false 38737919 262144 487 524288 Bool.true 62023 524288 1 76628 (@Enclosure.Real.IsNear.recentre' qz155 Bool.false 83189047628419312671 562949953421312000 2220750000510514893 2394625000000000000000 38737919 262144 487 524288 (ep539 rfl) rfl) (Enclosure.sfrac_false_div 38737919 262144) (BSN.sin_reduce2 qz390 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 4479786698898552127488) qz30) 226375608064910080 72057594037927936 Bool.false 62023 524288 23 1000000000000000 153256 76628 (BSN.sin_reduce_arg_pos_rat_q2 38737919 262144 226375608064910080 72057594037927936 23 4479786698898552127488 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 62023 524288 4479786698898552127488 37778931862957161709568 127323195 1073741824 153406 153256 (ep543 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep545 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz43 (Real.cos qz155)) (@HMul.hMul Real Real Real qz0 qz43 (@Neg.neg Real Real.instNeg (Real.sin qz155))) Bool.true 48250544989 137438953472 881807558713 2632918031663104 Bool.false 11496769349 274877906944 1754830042895 5265836063326208 (@Enclosure.Real.IsNear.mulLit_ft qz43 (Real.cos qz155) 185363 524288 1 524288 260303 262144 9460531 10043785216 48250544989 137438953472 881807558713 2632918031663104 qz311 (@Enclosure.Real.IsNear.recentre' (Real.cos qz155) Bool.true 520606 524288 37842124 40175140864 260303 262144 9460531 10043785216 (ep542 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz43 (@Neg.neg Real Real.instNeg (Real.sin qz155)) 185363 524288 1 524288 62023 524288 9460531 10043785216 11496769349 274877906944 1754830042895 5265836063326208 qz311 (@Enclosure.Real.IsNear.neg (Real.sin qz155) Bool.true 62023 524288 9460531 10043785216 (@Enclosure.Real.IsNear.recentre' (Real.sin qz155) Bool.true 62023 524288 37842124 40175140864 62023 524288 9460531 10043785216 (ep544 rfl rfl) rfl)) rfl)

noncomputable def ep546 := @ep463 48250544989 137438953472 881807558713 2632918031663104 Bool.false 11496769349 274877906944 1754830042895 5265836063326208 Bool.false 28893116664010881630208 210225092189 274877906944 16783494220929 5265836063326208 Bool.true 226836026302941626368 6601797251 274877906944 16783103686327 5265836063326208 (ep464 (BSN.head_sum_c_succ qz138 7 8 rfl rfl) (ep537 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep538 ep545) rfl rfl

theorem EMRow17.d10 : Enclosure.Complex.IsNear qz137 Bool.false 210225092189 274877906944 16783494220929 5265836063326208 Bool.true 6601797251 274877906944 16783103686327 5265836063326208 := ep462 (BSN.head_sum_c_succ qz138 8 9 rfl rfl) (ep546 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

theorem EMRow17.d11 : @Eq Nat (Nat.pow 15 1) 15 := @Eq.refl Nat 15

noncomputable def ep547 := nat_lit 1379979700127255169487200353267

noncomputable def ep548 := nat_lit 682341563449173892115988480000

noncomputable def ep549 := nat_lit 4451866204961919927122345034167824001

noncomputable def ep550 := nat_lit 751238919629661015544507786655170560000

noncomputable abbrev qz479 := (@HAdd.hAdd Complex Complex Complex qz484 (@HAdd.hAdd Complex Complex Complex qz484 qz487 (@HMul.hMul Complex Complex Complex qz486 Complex.I (@HDiv.hDiv Complex Complex Complex qz488 (↑qz491) (2 : Complex)))) (@Nat.cast Complex Complex.instNatCast 2))

noncomputable abbrev qz391 := qz479

noncomputable abbrev qz156 := (Complex.Stirling.logGammaStirling 1 qz391)

noncomputable abbrev qz480 := (@HAdd.hAdd Complex Complex Complex qz484 qz487 (@HMul.hMul Complex Complex Complex qz486 Complex.I (@HDiv.hDiv Complex Complex Complex qz488 (↑qz491) (2 : Complex))))

noncomputable abbrev qz392 := qz480

noncomputable abbrev qz157 := qz392

noncomputable abbrev qz158 := (@HMul.hMul Real Real Real qz263 (@HDiv.hDiv Real Real Real qz266 qz380 (2 : Real)) (Real.log Real.pi))

noncomputable def ep551 := Complex.re (@HMul.hMul Complex Complex Complex qz46 (Complex.exp (@HMul.hMul Complex Complex Complex qz46 Complex.I ↑(@HSub.hSub Real Real Real qz47 (Complex.im (@HSub.hSub Complex Complex Complex qz48 qz156 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz157 (@Nat.cast Complex Complex.instNatCast j))))) qz158))) (zetaApproximant qz138 1 15))

noncomputable def ep552 := @Enclosure.Real.IsNear.of_eq ep551 (@HSub.hSub Real Real Real qz47 (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz47 (Complex.im (@HSub.hSub Complex Complex Complex qz48 qz156 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz157 (@Nat.cast Complex Complex.instNatCast j))))) qz158)) (Complex.re (zetaApproximant qz138 1 15))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz47 (Complex.im (@HSub.hSub Complex Complex Complex qz48 qz156 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz157 (@Nat.cast Complex Complex.instNatCast j))))) qz158)) (Complex.im (zetaApproximant qz138 1 15))))

noncomputable def ep553 := nat_lit 4139954890990585952210015115937

noncomputable def ep554 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz47 (Complex.im (@HSub.hSub Complex Complex Complex qz48 qz156 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz157 (@Nat.cast Complex Complex.instNatCast j))))) qz158)) (Complex.re (zetaApproximant qz138 1 15))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz47 (Complex.im (@HSub.hSub Complex Complex Complex qz48 qz156 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz157 (@Nat.cast Complex Complex.instNatCast j))))) qz158)) (Complex.im (zetaApproximant qz138 1 15))) ep553

noncomputable def ep555 := nat_lit 2047024690347521676347965440000

noncomputable def ep556 := nat_lit 1479102547712983052733662831595131651

noncomputable def ep557 := nat_lit 250412973209887005181502595551723520000

noncomputable def ep558 := nat_lit 1973826102555468551757017

noncomputable def ep559 := nat_lit 255878086293440209543495680000

noncomputable def ep560 := nat_lit 1819820227871346115169567422803631

noncomputable def ep561 := nat_lit 93904864953707626943063473331896320000

noncomputable def ep562 := nat_lit 1059319694377072624719307550789990808970510560294265159680000

noncomputable def ep563 := @Enclosure.Real.IsNear.mulLit_ff (Real.cos (@HSub.hSub Real Real Real qz47 (Complex.im (@HSub.hSub Complex Complex Complex qz48 qz156 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz157 (@Nat.cast Complex Complex.instNatCast j))))) qz158)) (Complex.re (zetaApproximant qz138 1 15)) 524287 524288 533623

noncomputable def ep564 := nat_lit 7896352362333199091737951

noncomputable def ep565 := nat_lit 3904389744467776634880000

noncomputable def ep566 := nat_lit 75468220698792653745280111

noncomputable def ep567 := nat_lit 14959278866953839398879232000

noncomputable def ep568 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HSub.hSub Real Real Real qz47 (Complex.im (@HSub.hSub Complex Complex Complex qz48 qz156 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz157 (@Nat.cast Complex Complex.instNatCast j))))) qz158)) Bool.false 524287 524288 2134492

noncomputable abbrev qz393 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 823553) (@Nat.cast Real Real.instNatCast 16384))

noncomputable def ep569 := @Enclosure.Real.IsNear.cos_image (@HSub.hSub Real Real Real qz47 (Complex.im (@HSub.hSub Complex Complex Complex qz48 qz156 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz157 (@Nat.cast Complex Complex.instNatCast j))))) qz158) qz393 Bool.false 823553 16384 27

noncomputable def ep570 := nat_lit 62773657600000000000000000

noncomputable def ep571 := @Enclosure.Real.IsNear.recentre' (@HSub.hSub Real Real Real qz47 (Complex.im (@HSub.hSub Complex Complex Complex qz48 qz156 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz157 (@Nat.cast Complex Complex.instNatCast j))))) qz158) Bool.false 56594131717019617069 1125899906842624000 25830462926339648695341 ep570

noncomputable def ep572 := @Enclosure.Real.IsNear.subLit_ff_p (Complex.im (@HSub.hSub Complex Complex Complex qz48 qz156 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz157 (@Nat.cast Complex Complex.instNatCast j))))) qz158 102389584242809980717 1125899906842624000 8813299826339648695341 ep570 666411543 16384000

noncomputable def ep573 := nat_lit 927238254051649406058496000

noncomputable def ep574 := @Enclosure.Complex.IsNear.im_isNear (@HSub.hSub Complex Complex Complex qz48 qz156 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz157 (@Nat.cast Complex Complex.instNatCast j)))) Bool.true 25124331378284182251 450359962737049600 155613916257388981543591 ep178 Bool.false 102389584242809980717 1125899906842624000

noncomputable def ep575 := @Enclosure.Complex.IsNear.subLitP qz156 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz157 (@Nat.cast Complex Complex.instNatCast j))) Bool.true 21908081204977669651 450359962737049600 151517916251111615783591 ep178 Bool.false 105879192190595848717 1125899906842624000 7994099826276875037741

noncomputable def ep576 := nat_lit 56574964716586751681966198382133248

noncomputable def ep577 := nat_lit 28820105840158689874536407448420352

noncomputable abbrev qz394 := (@HSub.hSub Complex Complex Complex qz469 qz479 qz472)

noncomputable abbrev qz395 := (Complex.log qz479)

noncomputable abbrev qz159 := (@HSub.hSub Complex Complex Complex qz313 (@HMul.hMul Complex Complex Complex qz312 qz394 qz395) qz391)

noncomputable abbrev qz160 := qz391

noncomputable def ep578 := @Enclosure.Complex.IsNear.of_eq qz156 (@HAdd.hAdd Complex Complex Complex qz5 (@HAdd.hAdd Complex Complex Complex qz5 qz159 qz53) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz55 2 k))) (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz48 (@HMul.hMul Complex Complex Complex qz46 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz56 qz160 (@HSub.hSub Int Int Int qz58 qz59 (@HMul.hMul Int Int Int qz60 qz61 (@Nat.cast Int instNatCastInt k)))))) Bool.true 21908081204977669651

noncomputable def ep579 := @Enclosure.Complex.IsNear.addLitP (@HAdd.hAdd Complex Complex Complex qz5 qz159 qz53) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz55 2 k))) (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz48 (@HMul.hMul Complex Complex Complex qz46 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz56 qz160 (@HSub.hSub Int Int Int qz58 qz59 (@HMul.hMul Int Int Int qz60 qz61 (@Nat.cast Int instNatCastInt k))))) Bool.true 21908147821902239251 450359962737049600

noncomputable def ep580 := nat_lit 188188984586982727122673467392

noncomputable def ep581 := nat_lit 2273738338927538844964392796160

noncomputable def ep582 := @ep579 4623953156025545137 19157000000000000000000 Bool.false 4235272889071114261 45035996273704960 487900000684038999 3831400000000000000000 Bool.false 1270617 8589934592 3 8589934592 Bool.true 1254098979 536870912000 2961 536870912000 Bool.true ep580 21908081204977669651 450359962737049600 151517916251111615783591 ep178 Bool.false ep581

noncomputable def ep583 := @Enclosure.Complex.IsNear.addLitP qz159 qz53 Bool.true 22322000562623288851 450359962737049600 1137718750126991753 4789250000000000000000

noncomputable def ep584 := nat_lit 2871544751312370303107072

noncomputable def ep585 := @ep583 Bool.false 4235272889071114261 45035996273704960 487900000684038999 3831400000000000000000 Bool.false 120447 131072 1 262144 Bool.false 0 1 0 1 Bool.true ep584 21908147821902239251 450359962737049600 4623953156025545137 19157000000000000000000 Bool.false 4235272889071114261 4235272889071114261 45035996273704960

noncomputable abbrev qz161 := (@HMul.hMul Complex Complex Complex qz312 qz394 qz395)

noncomputable def ep586 := @Enclosure.Complex.IsNear.subLitP qz161 qz160 Bool.true 21308690646464927251 450359962737049600 1137718750126991753 4789250000000000000000 Bool.false 145887297716709972493

noncomputable def ep587 := @ep586 1125899906842624000 487900000684038999 3831400000000000000000 Bool.false 9000 4000 0 1 Bool.false 142128 4000 0 1 Bool.true 89288002250493155404000 22322000562623288851 450359962737049600 1137718750126991753 4789250000000000000000 Bool.false 423527288907111426100000 4235272889071114261 45035996273704960 487900000684038999 3831400000000000000000

noncomputable abbrev qz162 := qz394

noncomputable abbrev qz163 := qz395

noncomputable def ep588 := @Enclosure.Complex.IsNear.mul qz162 qz163 Bool.true 21308690646464927251 450359962737049600 1137718750126991753 4789250000000000000000 Bool.false 145887297716709972493 1125899906842624000 487900000684038999

noncomputable abbrev qz164 := (Complex.re qz394)

noncomputable abbrev qz165 := (Complex.re qz395)

noncomputable abbrev qz166 := (Complex.im qz394)

noncomputable abbrev qz167 := (Complex.im qz395)

noncomputable def ep589 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 qz164 qz165) (@HMul.hMul Real Real Real qz0 qz166 qz167) 112621685095200197 18014398509481984 87500000134099 15325600000000000000 1507764548365308261 28147497671065600

noncomputable def ep590 := nat_lit 23991452813793154971484601265946624

noncomputable def ep591 := @Enclosure.Real.IsNear.mulLit_ff qz164 qz165 7000 4000 0 1 16088812156457171 4503599627370496 12500000019157 3831400000000000000

noncomputable def ep592 := @Enclosure.Complex.IsNear.re_isNear qz162 Bool.false 7000 4000 0 1 Bool.false 142128 4000 0 1

noncomputable abbrev qz396 := (Enclosure.sfrac Bool.false 142128 4000)

noncomputable abbrev qz168 := qz396

noncomputable def ep593 := @Enclosure.Complex.IsNear.of_eq qz162 (Complex.mk (Enclosure.sfrac Bool.false 7000 4000) qz168) Bool.false 7000 4000 0 1 Bool.false 142128 4000 0

noncomputable abbrev qz169 := (Complex.mk qz327 qz396)

noncomputable def ep594 := @Enclosure.Complex.IsNear.of_eq qz163 (Complex.log qz169) Bool.false 16088812156457171 4503599627370496 12500000019157 3831400000000000000 Bool.false 848679808828835 562949953421312 250000000019157 38314000000000000000

noncomputable def ep595 := nat_lit 27109123135287491785300952755309254845399040

noncomputable def ep596 := nat_lit 102791992466099399115793767317184066879488

noncomputable def ep597 := nat_lit 692160937229936618211308475804505079808

noncomputable def ep598 := BSN.log_dyadic_bound 3897368384 36665368384 3 2 ep595 524288 153256 ep596 ep597 111881 40562736768 32768000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 3897368384) (BSN.artanhQ 36665368384) 0 2 ep596 ep595 ep597 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz397 := (Real.log (Enclosure.sfrac Bool.false 20281368384 16000000))

noncomputable def ep599 := @Enclosure.Real.IsNear.mulLit_ff qz71 qz397 1 2 0 1 16088812156457171 2251799813685248 12500000019157 1915700000000000000 16088812156457171 4503599627370496 12500000019157 3831400000000000000 qz329 (BSN.isNear_log_sfrac 20281368384 16000000 16088812156457171 2251799813685248 12500000019157 1915700000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 20281368384) qz330)) Bool.false 134962738366153876307968 18889465931478580854784 1000000001532560 153256000000000000000 16088812156457171 2251799813685248 12500000019157 1915700000000000000 (BSN.log_rat_reduce_isNear 20281368384 16000000 10 40562736768 32768000000 111881 524288 24973259072661432 36028797018963968 153256 1000000000000000 rfl rfl rfl rfl (ep598 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep600 := BSN.arctan_dyadic_bound_f 9000 142128 1 0 524288 153256 0 1 1 0 1 1 33155 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 9000) (BSN.arctanEvenQ 142128) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 9000) (BSN.arctanOddQ 142128) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz398 := (Real.arctan (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 9000) (@Nat.cast Real Real.instNatCast 142128)))

noncomputable def ep601 := @Enclosure.Real.IsNear.subLit_ff_p qz72 qz398 884279719003555 562949953421312 1 2000000000000000 33155 524288 1 153256 444952639611252244480 848679808828835 562949953421312 250000000019157 38314000000000000000 qz73 (ep600 rfl) rfl rfl

noncomputable abbrev qz399 := (Real.arctan (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 142128) (@Nat.cast Real Real.instNatCast 9000)))

noncomputable def ep602 := @Enclosure.Complex.IsNear.re_isNear qz163 Bool.false 16088812156457171 4503599627370496 12500000019157 3831400000000000000 Bool.false 848679808828835 562949953421312 250000000019157 38314000000000000000 (ep594 (@congrArg Complex Complex qz160 qz169 Complex.log (BSN.w_shift_mk qz147 Bool.false 71064 1000 2 qz148 rfl)) (@Enclosure.Complex.IsNear.of_parts (Complex.log qz169) Bool.false 16088812156457171 4503599627370496 12500000019157 3831400000000000000 Bool.false 848679808828835 562949953421312 250000000019157 38314000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re (Complex.log qz169)) (@HMul.hMul Real Real Real qz0 qz71 qz397) Bool.false 16088812156457171 4503599627370496 12500000019157 3831400000000000000 (Enclosure.clog_re_eq 9000 142128 4000 20281368384 16000000 rfl rfl rfl) (ep599 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im (Complex.log qz169)) qz399 Bool.false 848679808828835 562949953421312 250000000019157 38314000000000000000 (Enclosure.clog_im_eq 9000 142128 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz399 (@HSub.hSub Real Real Real qz47 qz72 qz398) Bool.false 848679808828835 562949953421312 250000000019157 38314000000000000000 (BSN.arctan_recip 142128 9000 rfl rfl) ep601))))

noncomputable def ep603 := @Enclosure.Real.IsNear.mulLit_ff qz166 qz167 142128 4000 0 1 848679808828835 562949953421312 250000000019157 38314000000000000000

noncomputable def ep604 := @Enclosure.Complex.IsNear.im_isNear qz162 Bool.false 7000 4000 0 1 Bool.false 142128 4000 0 1

noncomputable def ep605 := @Enclosure.Complex.IsNear.im_isNear qz163 Bool.false 16088812156457171 4503599627370496 12500000019157 3831400000000000000 Bool.false 848679808828835 562949953421312 250000000019157 38314000000000000000 (ep594 (@congrArg Complex Complex qz160 qz169 Complex.log (BSN.w_shift_mk qz147 Bool.false 71064 1000 2 qz148 rfl)) (@Enclosure.Complex.IsNear.of_parts (Complex.log qz169) Bool.false 16088812156457171 4503599627370496 12500000019157 3831400000000000000 Bool.false 848679808828835 562949953421312 250000000019157 38314000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re (Complex.log qz169)) (@HMul.hMul Real Real Real qz0 qz71 qz397) Bool.false 16088812156457171 4503599627370496 12500000019157 3831400000000000000 (Enclosure.clog_re_eq 9000 142128 4000 20281368384 16000000 rfl rfl rfl) (ep599 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im (Complex.log qz169)) qz399 Bool.false 848679808828835 562949953421312 250000000019157 38314000000000000000 (Enclosure.clog_im_eq 9000 142128 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz399 (@HSub.hSub Real Real Real qz47 qz72 qz398) Bool.false 848679808828835 562949953421312 250000000019157 38314000000000000000 (BSN.arctan_recip 142128 9000 rfl rfl) ep601))))

noncomputable abbrev qz400 := (Enclosure.Real.IsNear.const Bool.false 142128 4000)

noncomputable abbrev qz170 := (@ep593 1 (BSN.w_sub_half_mk qz380 Bool.false 71064 1000 2 qz381 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7000 4000) qz396 Bool.false 7000 4000 0 1 Bool.false 142128 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 7000 4000) qz400))

noncomputable def ep606 := @ep589 2220750000170171631 9578500000000000000000 ep590 21308690646464927251 450359962737049600 1137718750126991753 4789250000000000000000 (@ep591 112621685095200197 18014398509481984 87500000134099 15325600000000000000 (ep592 qz170) ep602 rfl) (@ep603 1507764548365308261 28147497671065600 2220750000170171631 9578500000000000000000 (ep604 qz170) ep605 rfl) rfl

noncomputable def ep607 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz164 qz167) (@HMul.hMul Real Real Real qz0 qz166 qz165) 5940758661801845 2251799813685248 1750000000134099 153256000000000000000 142916918385809049993 1125899906842624000

noncomputable def ep608 := nat_lit 328508989817531822020752619039883264

noncomputable def ep609 := @Enclosure.Real.IsNear.mulLit_ff qz164 qz167 7000 4000 0 1 848679808828835 562949953421312 250000000019157 38314000000000000000

noncomputable def ep610 := @Enclosure.Real.IsNear.mulLit_ff qz166 qz165 142128 4000 0 1 16088812156457171 4503599627370496 12500000019157 3831400000000000000

noncomputable def ep611 := @ep607 111037500170171631 957850000000000000000 ep608 145887297716709972493 1125899906842624000 487900000684038999 3831400000000000000000 (@ep609 5940758661801845 2251799813685248 1750000000134099 153256000000000000000 (ep592 qz170) ep605 rfl) (@ep610 142916918385809049993 1125899906842624000 111037500170171631 957850000000000000000 (ep604 qz170) ep602 rfl) rfl

noncomputable def ep612 := @Enclosure.Complex.IsNear.of_eq qz160 qz169 Bool.false 9000 4000 0 1 Bool.false 142128 4000 0 1 (BSN.w_shift_mk qz147 Bool.false 71064 1000 2 qz148 rfl)

noncomputable abbrev qz401 := (ep612 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 9000 4000) (Enclosure.sfrac Bool.false 142128 4000) Bool.false 9000 4000 0 1 Bool.false 142128 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 9000 4000) (Enclosure.Real.IsNear.const Bool.false 142128 4000)))

noncomputable abbrev qz171 := qz401

noncomputable def ep613 := ep587 (@ep588 3831400000000000000000 (ep606 rfl) (ep611 rfl)) qz171 rfl rfl rfl rfl rfl rfl

noncomputable def ep614 := @ep585 487900000684038999 3831400000000000000000 (ep613 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@Enclosure.Complex.IsNear.mul qz76 (↑qz3) Bool.false 120447 131072 1 262144 Bool.false 0 1 0 1 (@ep220 131072 1 262144 (ep222 rfl) (ep224 rfl) rfl rfl) (@ep225 1 0 1 (ep227 rfl) (ep229 rfl) rfl rfl))

noncomputable abbrev qz402 := (@HPow.hPow Complex Int Complex qz474 qz479 (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) (@OfNat.ofNat Int 1 (@instOfNat 1)) (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (@OfNat.ofNat Int 2 (@instOfNat 2)) (@Nat.cast Int instNatCastInt 1))))

noncomputable abbrev qz172 := qz402

noncomputable def ep615 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz55 2 k))) (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz48 (@HMul.hMul Complex Complex Complex qz46 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz56 qz160 (@HSub.hSub Int Int Int qz58 qz59 (@HMul.hMul Int Int Int qz60 qz61 (@Nat.cast Int instNatCastInt k))))) (@HAdd.hAdd Complex Complex Complex qz5 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz55 2 k))) (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz48 (@HMul.hMul Complex Complex Complex qz46 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz56 qz160 (@HSub.hSub Int Int Int qz58 qz59 (@HMul.hMul Int Int Int qz60 qz61 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 (@Rat.cast Complex Complex.instRatCast (bernoulli qz78)) qz79) qz172)) Bool.false 1270617 8589934592 3 8589934592

noncomputable def ep616 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz55 2 k))) (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz48 (@HMul.hMul Complex Complex Complex qz46 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz56 qz160 (@HSub.hSub Int Int Int qz58 qz59 (@HMul.hMul Int Int Int qz60 qz61 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 (@Rat.cast Complex Complex.instRatCast (bernoulli qz78)) qz79) qz172) Bool.false 0 1 0 1 Bool.false

noncomputable def ep617 := @ep616 0 1 0 1 Bool.false 1270617 8589934592 3 8589934592 Bool.true 1254098979 536870912000 2961 536870912000 Bool.false 1270617 1270617 8589934592 3 8589934592 Bool.true 1254098979 1254098979 536870912000 2961

noncomputable def ep618 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz55 2 k))) (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz48 (@HMul.hMul Complex Complex Complex qz46 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz56 qz160 (@HSub.hSub Int Int Int qz58 qz59 (@HMul.hMul Int Int Int qz60 qz61 (@Nat.cast Int instNatCastInt k))))) (Complex.mk qz14 qz14) Bool.false 0 1 0 1 Bool.false

noncomputable def ep619 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz54 (@Rat.cast Complex Complex.instRatCast (bernoulli qz78)) qz79) qz172 Bool.false 1270617 8589934592 3 8589934592 Bool.true 1254098979 536870912000 2961 536870912000

noncomputable abbrev qz173 := (Complex.re qz402)

noncomputable abbrev qz174 := (Complex.im qz402)

noncomputable def ep620 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz54 (@Rat.cast Complex Complex.instRatCast (bernoulli qz78)) qz79)) qz173) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz54 (@Rat.cast Complex Complex.instRatCast (bernoulli qz78)) qz79)) qz174) 1270617 8589934592 3 8589934592 0 1 0

noncomputable def ep621 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz54 (@Rat.cast Complex Complex.instRatCast (bernoulli qz78)) qz79)) qz173 1 12 0 1 3811851 2147483648 9 2147483648 1270617

noncomputable def ep622 := @Enclosure.Complex.IsNear.re_isNear qz172 Bool.false 3811851 2147483648 9 2147483648 Bool.true 3762296937 134217728000 8883 134217728000

noncomputable abbrev qz403 := (@HPow.hPow Complex Nat Complex qz475 qz479 1)

noncomputable abbrev qz175 := (@Inv.inv Complex Complex.instInv qz403)

noncomputable def ep623 := @Enclosure.Complex.IsNear.of_eq qz172 qz175 Bool.false 3811851 2147483648 9 2147483648 Bool.true 3762296937 134217728000 8883

noncomputable def ep624 := @Enclosure.Complex.IsNear.of_parts qz175 Bool.false 3811851 2147483648 9 2147483648 Bool.true 3762296937 134217728000 8883

noncomputable abbrev qz176 := (Complex.re qz403)

noncomputable abbrev qz177 := qz403

noncomputable def ep625 := @Enclosure.Real.IsNear.mulLit_ff qz176 (@Inv.inv Real Real.instInv (@DFunLike.coe qz85 Complex (fun (x : Complex) => Real) qz86 Complex.normSq qz177)) 9000 4000 0 1 423539 536870912 1 536870912

noncomputable def ep626 := @Enclosure.Complex.IsNear.re_isNear qz177 Bool.false 9000 4000 0 1 Bool.false 142128 4000 0 1

noncomputable def ep627 := @Enclosure.Complex.IsNear.of_eq qz177 qz160 Bool.false 9000 4000 0 1 Bool.false 142128 4000 0

noncomputable def ep628 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (@DFunLike.coe qz85 Complex (fun (x : Complex) => Real) qz86 Complex.normSq qz177)) Bool.false 423539 536870912 1 536870912 423539 536870912 1

noncomputable abbrev qz178 := (Complex.im qz403)

noncomputable def ep629 := @Enclosure.Real.IsNear.of_eq (@DFunLike.coe qz85 Complex (fun (x : Complex) => Real) qz86 Complex.normSq qz177) (@HAdd.hAdd Real Real Real qz339 (@HMul.hMul Real Real Real qz0 qz176 qz176) (@HMul.hMul Real Real Real qz0 qz178 qz178)) Bool.false 316896381 250000 0 1

noncomputable def ep630 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz176 qz176) (@HMul.hMul Real Real Real qz0 qz178 qz178) 81 16 0 1 78907689 62500

noncomputable def ep631 := @Enclosure.Real.IsNear.mulLit_ff qz176 qz176 9000 4000 0 1 9000 4000 0 1

noncomputable def ep632 := @Enclosure.Real.IsNear.mulLit_ff qz178 qz178 142128 4000 0 1 142128 4000 0 1

noncomputable def ep633 := @Enclosure.Complex.IsNear.im_isNear qz177 Bool.false 9000 4000 0 1 Bool.false 142128 4000 0 1

noncomputable abbrev qz179 := (ep626 (@ep627 1 (BSN.pow_one_c qz391) qz401))

noncomputable abbrev qz180 := (ep633 (@ep627 1 (BSN.pow_one_c qz391) qz401))

noncomputable def ep634 := @ep630 0 1 1267585524 316896381 250000 0 1 (@ep631 81 16 0 1 qz179 qz179 rfl) (@ep632 78907689 62500 0 1 qz180 qz180 rfl)

noncomputable def ep635 := @Enclosure.Real.IsNear.inv_image (@DFunLike.coe qz85 Complex (fun (x : Complex) => Real) qz86 Complex.normSq qz177) 316896381 250000 0 1 211769 211770 268435456 (ep629 (Enclosure.Complex.normSq_eq_mul_add_mul qz177) (ep634 rfl rfl)) rfl

noncomputable def ep636 := @Enclosure.Real.IsNear.of_eq (Complex.re qz175) (@HMul.hMul Real Real Real qz0 qz176 (@Inv.inv Real Real.instInv (@DFunLike.coe qz85 Complex (fun (x : Complex) => Real) qz86 Complex.normSq qz177))) Bool.false 3811851 2147483648 9 2147483648 (Enclosure.Complex.inv_re_eq_mul qz177) (@ep625 3811851 2147483648 9 2147483648 qz179 (@ep628 536870912 (ep635 rfl rfl rfl rfl rfl) rfl) rfl)

noncomputable def ep637 := @Enclosure.Real.IsNear.of_eq (Complex.im qz175) (@HMul.hMul Real Real Real qz0 (@Neg.neg Real Real.instNeg qz178) (@Inv.inv Real Real.instInv (@DFunLike.coe qz85 Complex (fun (x : Complex) => Real) qz86 Complex.normSq qz177))) Bool.true 3762296937 134217728000 8883 134217728000 (Enclosure.Complex.inv_im_eq_mul qz177)

noncomputable def ep638 := @Enclosure.Real.IsNear.mulLit_tf (@Neg.neg Real Real.instNeg qz178) (@Inv.inv Real Real.instInv (@DFunLike.coe qz85 Complex (fun (x : Complex) => Real) qz86 Complex.normSq qz177)) 142128 4000 0 1 423539 536870912 1

noncomputable def ep639 := @ep638 536870912 3762296937 134217728000 8883 134217728000 (@Enclosure.Real.IsNear.neg qz178 Bool.false 142128 4000 0 1 qz180) (@ep628 536870912 (ep635 rfl rfl rfl rfl rfl) rfl) rfl

noncomputable def ep640 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz54 (@Rat.cast Complex Complex.instRatCast (bernoulli qz78)) qz79)) qz174 0 1 0 1 3762296937 134217728000 8883 134217728000 0

noncomputable def ep641 := @Enclosure.Complex.IsNear.im_isNear qz172 Bool.false 3811851 2147483648 9 2147483648 Bool.true 3762296937 134217728000 8883 134217728000

noncomputable abbrev qz181 := (@ep623 134217728000 (BSN.zpow_one_sub_two_mul qz391 1 1 rfl rfl) (@ep624 134217728000 ep636 (ep637 ep639)))

noncomputable def ep642 := @ep620 1 1270617 1270617 8589934592 3 8589934592 (@ep621 8589934592 3 8589934592 ep239 (ep622 qz181) rfl) (@ep640 1 0 1 ep259 (ep641 qz181) rfl) rfl

noncomputable def ep643 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz54 (@Rat.cast Complex Complex.instRatCast (bernoulli qz78)) qz79)) qz174) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz54 (@Rat.cast Complex Complex.instRatCast (bernoulli qz78)) qz79)) qz173) 1254098979 536870912000 2961 536870912000 0 1 0

noncomputable def ep644 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HDiv.hDiv Complex Complex Complex qz54 (@Rat.cast Complex Complex.instRatCast (bernoulli qz78)) qz79)) qz174 1 12 0 1 3762296937 134217728000 8883 134217728000 1254098979

noncomputable def ep645 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz54 (@Rat.cast Complex Complex.instRatCast (bernoulli qz78)) qz79)) qz173 0 1 0 1 3811851 2147483648 9 2147483648 0

noncomputable def ep646 := @ep643 1 1254098979 1254098979 536870912000 2961 536870912000 (@ep644 536870912000 2961 536870912000 ep239 (ep641 qz181) rfl) (@ep645 1 0 1 ep259 (ep622 qz181) rfl) rfl

noncomputable def ep647 := @ep617 536870912000 (@ep618 0 1 0 1 (BSN.stirling_sum_base qz160) qz92) (ep619 (ep642 rfl) (ep646 rfl)) rfl rfl rfl rfl rfl

noncomputable def ep648 := @ep582 105879192190595848717 1125899906842624000 7994099826276875037741 ep570 (ep614 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep615 Bool.true 1254098979 536870912000 2961 536870912000 (BSN.stirling_sum_succ qz160 0 1 rfl) (ep647 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl

noncomputable def ep649 := @Enclosure.Complex.IsNear.of_eq (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz157 (@Nat.cast Complex Complex.instNatCast j))) (BSN.logSumC qz147 2) Bool.false 16081250866532563 2251799813685248 12500000019157 1915700000000000000 Bool.false 872401986946467 281474976710656

noncomputable abbrev qz182 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz269 qz392 qz335))

noncomputable def ep650 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz147 2) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.logSumC qz147 1) qz182) Bool.false 16081250866532563 2251799813685248 12500000019157 1915700000000000000 Bool.false 872401986946467 281474976710656 250000000019157 19157000000000000000

noncomputable def ep651 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz147 1) qz182 Bool.false 16079912984219859 4503599627370496 12500000019157 3831400000000000000 Bool.false 880319759156643 562949953421312 250000000019157 38314000000000000000 Bool.false

noncomputable def ep652 := nat_lit 144847030820335033262401698922496

noncomputable def ep653 := nat_lit 982237315832347274180881809408

noncomputable abbrev qz183 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz269 qz392 (@Nat.cast Complex Complex.instNatCast 0)))

noncomputable def ep654 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz147 1) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.logSumC qz147 0) qz183) Bool.false 16079912984219859 4503599627370496 12500000019157 3831400000000000000 Bool.false 880319759156643 562949953421312 250000000019157 38314000000000000000

noncomputable def ep655 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz147 0) qz183 Bool.false 0 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable abbrev qz404 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz168))

noncomputable def ep656 := @Enclosure.Complex.IsNear.of_eq qz183 qz404 Bool.false 16079912984219859 4503599627370496 12500000019157 3831400000000000000 Bool.false 880319759156643 562949953421312 250000000019157 38314000000000000000

noncomputable def ep657 := nat_lit 26873299266343537004952482534283155645399040

noncomputable def ep658 := nat_lit 98161394505914387117460347676597826879488

noncomputable def ep659 := nat_lit 637055902455447633199463310584665079808

noncomputable def ep660 := BSN.log_dyadic_bound 3817368384 36585368384 3 2 ep657 524288 153256 ep658 ep659 109809 40402736768 32768000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 3817368384) (BSN.artanhQ 36585368384) 0 2 ep658 ep657 ep659 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep661 := @Enclosure.Real.IsNear.mulLit_ff qz71 (Real.log (Enclosure.sfrac Bool.false 20201368384 16000000)) 1 2 0 1 16079912984219859 2251799813685248 12500000019157 1915700000000000000 16079912984219859 4503599627370496 12500000019157 3831400000000000000 qz329 (BSN.isNear_log_sfrac 20201368384 16000000 16079912984219859 2251799813685248 12500000019157 1915700000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 20201368384) qz330)) Bool.false 134888086698730582966272 18889465931478580854784 1000000001532560 153256000000000000000 16079912984219859 2251799813685248 12500000019157 1915700000000000000 (BSN.log_rat_reduce_isNear 20201368384 16000000 10 40402736768 32768000000 109809 524288 24973259072661432 36028797018963968 153256 1000000000000000 rfl rfl rfl rfl (ep660 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep662 := BSN.arctan_dyadic_bound_f 1000 142128 1 0 524288 153256 0 1 1 0 1 1 3688 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 142128) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 142128) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz405 := (@Nat.cast Real Real.instNatCast 142128)

noncomputable def ep663 := @Enclosure.Real.IsNear.subLit_ff_p qz72 (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz341 qz405)) 884279719003555 562949953421312 1 2000000000000000 3688 524288 1 153256 461541085888718045184 880319759156643 562949953421312 250000000019157 38314000000000000000 qz73 (ep662 rfl) rfl rfl

noncomputable abbrev qz184 := (@HAdd.hAdd Complex Complex Complex qz269 qz392 (@Nat.cast Complex Complex.instNatCast 0))

noncomputable abbrev qz406 := (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz168)

noncomputable def ep664 := @ep655 16079912984219859 4503599627370496 12500000019157 3831400000000000000 Bool.false 880319759156643 562949953421312 250000000019157 38314000000000000000 Bool.false 16079912984219859 16079912984219859 4503599627370496 12500000019157 3831400000000000000 Bool.false 880319759156643 880319759156643 562949953421312 250000000019157 38314000000000000000 (@Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz147 0) (Complex.mk qz14 qz14) Bool.false 0 1 0 1 Bool.false 0 1 0 1 (BSN.log_sum_c_base qz147) qz92) (ep656 (@congrArg Complex Complex qz184 qz406 Complex.log (BSN.w_shift_mk qz147 Bool.false 71064 1000 0 qz148 rfl)) (@Enclosure.Complex.IsNear.of_parts qz404 Bool.false 16079912984219859 4503599627370496 12500000019157 3831400000000000000 Bool.false 880319759156643 562949953421312 250000000019157 38314000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz404) (@HMul.hMul Real Real Real qz0 qz71 (Real.log (Enclosure.sfrac Bool.false 20201368384 16000000))) Bool.false 16079912984219859 4503599627370496 12500000019157 3831400000000000000 (Enclosure.clog_re_eq 1000 142128 4000 20201368384 16000000 rfl rfl rfl) (ep661 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz404) (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz405 qz341)) Bool.false 880319759156643 562949953421312 250000000019157 38314000000000000000 (Enclosure.clog_im_eq 1000 142128 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz405 qz341)) (@HSub.hSub Real Real Real qz47 qz72 (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz341 qz405))) Bool.false 880319759156643 562949953421312 250000000019157 38314000000000000000 (BSN.arctan_recip 142128 1000 rfl rfl) ep663)))) rfl rfl

noncomputable abbrev qz407 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz168))

noncomputable def ep665 := @Enclosure.Complex.IsNear.of_eq qz182 qz407 Bool.false 16082588748845267 4503599627370496 12500000019157 3831400000000000000 Bool.false 864484214736291 562949953421312 250000000019157 38314000000000000000

noncomputable def ep666 := nat_lit 26943884216370805244858108282830985405399040

noncomputable def ep667 := nat_lit 99537311759612119732920204096773698879488

noncomputable def ep668 := nat_lit 653228440986358719127953308150617079808

noncomputable def ep669 := BSN.log_dyadic_bound 3841368384 36609368384 3 2 ep666 524288 153256 ep667 ep668 110432 40450736768 32768000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 3841368384) (BSN.artanhQ 36609368384) 0 2 ep667 ep666 ep668 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep670 := @Enclosure.Real.IsNear.mulLit_ff qz71 (Real.log (Enclosure.sfrac Bool.false 20225368384 16000000)) 1 2 0 1 16082588748845267 2251799813685248 12500000019157 1915700000000000000 16082588748845267 4503599627370496 12500000019157 3831400000000000000 qz329 (BSN.isNear_log_sfrac 20225368384 16000000 16082588748845267 2251799813685248 12500000019157 1915700000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 20225368384) qz330)) Bool.false 134910532639273397518336 18889465931478580854784 1000000001532560 153256000000000000000 16082588748845267 2251799813685248 12500000019157 1915700000000000000 (BSN.log_rat_reduce_isNear 20225368384 16000000 10 40450736768 32768000000 110432 524288 24973259072661432 36028797018963968 153256 1000000000000000 rfl rfl rfl rfl (ep669 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep671 := BSN.arctan_dyadic_bound_f 5000 142128 1 0 524288 153256 0 1 1 0 1 1 18436 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 5000) (BSN.arctanEvenQ 142128) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 5000) (BSN.arctanOddQ 142128) 0 0 rfl) rfl rfl rfl

noncomputable def ep672 := @Enclosure.Real.IsNear.subLit_ff_p qz72 (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz345 qz405)) 884279719003555 562949953421312 1 2000000000000000 18436 524288 1 153256 453238699975660535808 864484214736291 562949953421312 250000000019157 38314000000000000000 qz73 (ep671 rfl) rfl rfl

noncomputable abbrev qz185 := (@HAdd.hAdd Complex Complex Complex qz269 qz392 qz335)

noncomputable abbrev qz408 := (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz168)

noncomputable def ep673 := @ep651 16082588748845267 4503599627370496 12500000019157 3831400000000000000 Bool.false 864484214736291 562949953421312 250000000019157 38314000000000000000 Bool.false ep652 16081250866532563 2251799813685248 12500000019157 1915700000000000000 Bool.false ep653 872401986946467 281474976710656 250000000019157 19157000000000000000 (ep654 (BSN.log_sum_c_succ qz147 0 1 rfl) (ep664 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep665 (@congrArg Complex Complex qz185 qz408 Complex.log (BSN.w_shift_mk qz147 Bool.false 71064 1000 1 qz148 rfl)) (@Enclosure.Complex.IsNear.of_parts qz407 Bool.false 16082588748845267 4503599627370496 12500000019157 3831400000000000000 Bool.false 864484214736291 562949953421312 250000000019157 38314000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz407) (@HMul.hMul Real Real Real qz0 qz71 (Real.log (Enclosure.sfrac Bool.false 20225368384 16000000))) Bool.false 16082588748845267 4503599627370496 12500000019157 3831400000000000000 (Enclosure.clog_re_eq 5000 142128 4000 20225368384 16000000 rfl rfl rfl) (ep670 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz407) (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz405 qz345)) Bool.false 864484214736291 562949953421312 250000000019157 38314000000000000000 (Enclosure.clog_im_eq 5000 142128 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz405 qz345)) (@HSub.hSub Real Real Real qz47 qz72 (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz345 qz405))) Bool.false 864484214736291 562949953421312 250000000019157 38314000000000000000 (BSN.arctan_recip 142128 5000 rfl rfl) ep672)))) rfl rfl

noncomputable def ep674 := @ep575 ep570 Bool.false 16081250866532563 2251799813685248 12500000019157 1915700000000000000 Bool.false 872401986946467 281474976710656 250000000019157 19157000000000000000 Bool.true ep576 25124331378284182251 450359962737049600 155613916257388981543591 ep178 Bool.false ep577 102389584242809980717 1125899906842624000 8813299826339648695341 ep570 (@ep578 450359962737049600 151517916251111615783591 ep178 Bool.false 105879192190595848717 1125899906842624000 7994099826276875037741 ep570 (BSN.logGammaStirling_unfold 1 qz160) (ep648 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (@ep649 250000000019157 19157000000000000000 (BSN.log_sum_c_eq qz147 2) (ep650 (BSN.log_sum_c_succ qz147 1 2 rfl) (ep673 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)))

noncomputable abbrev qz186 := (@HDiv.hDiv Real Real Real qz266 qz380 (2 : Real))

noncomputable def ep675 := @Enclosure.Real.IsNear.mulLit_ff qz186 (Real.log Real.pi) 71064 2000 0 1 75021 65536 1 131072 666411543 16384000 8883 32768000 (@Enclosure.Real.IsNear.of_eq qz186 (Enclosure.sfrac Bool.false 71064 2000) Bool.false 71064 2000 0 1 (BSN.t_half_eq qz147 Bool.false 71064 1000 qz148) (Enclosure.Real.IsNear.const Bool.false 71064 2000)) EMRow17.d5 rfl

noncomputable def ep676 := @ep572 8883 32768000 ep573 56594131717019617069 1125899906842624000 25830462926339648695341 ep570 (@ep574 8813299826339648695341 ep570 (ep674 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) ep675 rfl rfl

noncomputable def ep677 := BSN.cos_dyadic_bound_f 218589 1073741824 1 0 524288 153406 0 1 1 0 1 1 524287 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 218589) qz278 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 218589) qz279 0 0 rfl) rfl rfl

noncomputable def ep678 := @ep569 65536 Bool.false 524287 524288 1 76628 (@ep571 823553 16384 27 65536 ep676 rfl) (Enclosure.sfrac_false_div 823553 16384) (BSN.cos_reduce0 qz393 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 480684299754930176) (@Nat.cast Real Real.instNatCast 2361183241434822606848)) 226375608064910080 72057594037927936 Bool.false 524287 524288 8 1000000000000000 153256 76628 (BSN.sin_reduce_arg_pos_rat_q0 823553 16384 226375608064910080 72057594037927936 8 480684299754930176 2361183241434822606848 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 524287 524288 480684299754930176 2361183241434822606848 218589 1073741824 153406 153256 (ep677 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep679 := nat_lit 18856834778121129212011931

noncomputable def ep680 := nat_lit 3739819716738459849719808000

noncomputable abbrev qz187 := qz379

noncomputable abbrev qz409 := (@HPow.hPow Complex Complex Complex qz463 (@Nat.cast Complex Complex.instNatCast 15) qz477)

noncomputable abbrev qz188 := qz409

noncomputable abbrev qz410 := (@Nat.cast Complex Complex.instNatCast 15)

noncomputable abbrev qz189 := (@HAdd.hAdd Complex Complex Complex qz269 (@HDiv.hDiv Complex Complex Complex qz320 qz410 (@HSub.hSub Complex Complex Complex qz313 qz378 (1 : Complex))) qz319)

noncomputable abbrev qz190 := qz410

noncomputable def ep681 := @Enclosure.Complex.IsNear.of_eq (zetaApproximant qz138 1 15) (@HAdd.hAdd Complex Complex Complex qz5 (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 15, @HPow.hPow Complex Complex Complex qz98 (@Nat.cast Complex Complex.instNatCast n) qz187) (@HMul.hMul Complex Complex Complex qz46 qz188 (@HAdd.hAdd Complex Complex Complex qz5 qz189 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz55 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz55 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz138 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz55 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz103 qz190 (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz55 2 k) 1))))))) Bool.false ep564 ep565 ep566

noncomputable def ep682 := @Enclosure.Complex.IsNear.addLitP (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 15, @HPow.hPow Complex Complex Complex qz98 (@Nat.cast Complex Complex.instNatCast n) qz187) (@HMul.hMul Complex Complex Complex qz46 qz188 (@HAdd.hAdd Complex Complex Complex qz5 qz189 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz55 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz55 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz138 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz55 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz103 qz190 (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz55 2 k) 1)))))) Bool.false 294969852137 137438953472 12841775133863 2632918031663104

noncomputable def ep683 := nat_lit 2505943459639016748826111

noncomputable def ep684 := nat_lit 1085266404925229835330284907105615872

noncomputable def ep685 := nat_lit 5118501771149814011020601571934208

noncomputable def ep686 := @ep682 Bool.true 3101845747 137438953472 12834529994777 2632918031663104 Bool.true 483202607470225865992049 ep565 ep683 ep567 Bool.false 59271445585376651756689 976097436116944158720000 626556527028238927845431 ep680 Bool.false ep684 ep564 ep565 ep566 ep567 Bool.false ep685 37242001935008840599189 976097436116944158720000

noncomputable def ep687 := @Enclosure.Complex.IsNear.of_eq (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 15, @HPow.hPow Complex Complex Complex qz98 (@Nat.cast Complex Complex.instNatCast n) qz187) (BSN.headSumC qz138 15) Bool.false 294969852137 137438953472 12841775133863 2632918031663104 Bool.true 3101845747 137438953472 12834529994777

noncomputable abbrev qz191 := (@HPow.hPow Complex Complex Complex qz270 qz348 qz379)

noncomputable def ep688 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz138 15) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz138 14) qz191) Bool.false 294969852137 137438953472 12841775133863 2632918031663104 Bool.true 3101845747 137438953472 12834529994777 2632918031663104

noncomputable def ep689 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz138 14) qz191 Bool.false 547436941465 274877906944 24352110869291 5265836063326208 Bool.true 66123774845 274877906944 24335239337705 5265836063326208 Bool.false

noncomputable abbrev qz192 := (@HPow.hPow Complex Complex Complex qz270 (@Nat.cast Complex Complex.instNatCast 13) qz379)

noncomputable def ep690 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz138 14) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz138 13) qz192) Bool.false 547436941465 274877906944 24352110869291 5265836063326208 Bool.true 66123774845 274877906944 24335239337705 5265836063326208

noncomputable def ep691 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz138 13) qz192 Bool.false 471350635715 274877906944 22963626577585 5265836063326208 Bool.true 30664859793 137438953472 5739036839779 1316459015831552 Bool.false

noncomputable abbrev qz193 := (@HPow.hPow Complex Complex Complex qz270 (@Nat.cast Complex Complex.instNatCast 12) qz379)

noncomputable def ep692 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz138 13) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz138 12) qz193) Bool.false 471350635715 274877906944 22963626577585 5265836063326208 Bool.true 30664859793 137438953472 5739036839779 1316459015831552

noncomputable def ep693 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz138 12) qz193 Bool.false 408574702891 274877906944 21523829346903 5265836063326208 Bool.true 12794668219 274877906944 21518152668035 5265836063326208 Bool.false

noncomputable abbrev qz194 := (@HPow.hPow Complex Complex Complex qz270 (@Nat.cast Complex Complex.instNatCast 11) qz379)

noncomputable def ep694 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz138 12) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz138 11) qz194) Bool.false 408574702891 274877906944 21523829346903 5265836063326208 Bool.true 12794668219 274877906944 21518152668035 5265836063326208

noncomputable def ep695 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz138 11) qz194 Bool.false 174188556569 137438953472 5005253371681 1316459015831552 Bool.false 44171628695 274877906944 20015728396093 5265836063326208 Bool.false

noncomputable abbrev qz195 := (@HPow.hPow Complex Complex Complex qz270 (@Nat.cast Complex Complex.instNatCast 10) qz379)

noncomputable def ep696 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz138 11) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz138 10) qz195) Bool.false 174188556569 137438953472 5005253371681 1316459015831552 Bool.false 44171628695 274877906944 20015728396093 5265836063326208

noncomputable def ep697 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz138 10) qz195 Bool.false 264553316473 274877906944 18442809758889 5265836063326208 Bool.false 67179995615 274877906944 18444551666585 5265836063326208 Bool.false

noncomputable abbrev qz196 := (@HPow.hPow Complex Complex Complex qz270 (@Nat.cast Complex Complex.instNatCast 9) qz379)

noncomputable def ep698 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz138 10) (@HAdd.hAdd Complex Complex Complex qz5 qz137 qz196) Bool.false 264553316473 274877906944 18442809758889 5265836063326208 Bool.false 67179995615 274877906944 18444551666585 5265836063326208

noncomputable def ep699 := @Enclosure.Complex.IsNear.addLitP qz137 qz196 Bool.false 210225092189 274877906944 16783494220929 5265836063326208 Bool.true 6601797251 274877906944 16783103686327 5265836063326208 Bool.false

noncomputable abbrev qz197 := (@HMul.hMul Real Real Real qz263 qz380 (Real.log (Enclosure.sfrac Bool.false 9 1)))

noncomputable def ep700 := @Enclosure.Complex.IsNear.of_eq qz196 (Complex.mk (@HMul.hMul Real Real Real qz0 qz110 (Real.cos qz197)) (@HMul.hMul Real Real Real qz0 qz110 (@Neg.neg Real Real.instNeg (Real.sin qz197)))) Bool.false 13582056071 68719476736 207414442245 658229507915776 Bool.false 36890896433 137438953472 830723990129 2632918031663104 (BSN.cpow_neg_s_mk qz147 71064 1000 9 qz148 rfl)

noncomputable def ep701 := @Enclosure.Real.IsNear.mulLit_ff qz147 qz112 71064 1000 0 1 9895417793173221 4503599627370496 250000000057471 19157000000000000000 87900996256757722143 562949953421312000 2220750000510514893 2394625000000000000000 qz149 (BSN.isNear_log_sfrac 9 1 9895417793173221 4503599627370496 250000000057471 19157000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz351) Bool.false 20752195215788806766592 9444732965739290427392 1000000000229884 76628000000000000000 9895417793173221 4503599627370496 250000000057471 19157000000000000000 (BSN.log_rat_reduce_isNear 9 1 3 18 16 30876 262144 24973259072661432 36028797018963968 76628 1000000000000000 rfl rfl rfl rfl (ep321 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep702 := nat_lit 215710581603172821919264358710042896

noncomputable def ep703 := BSN.sin_dyadic_bound_f 681503142 1073741824 2 1 524288 153406 ep702 ep61 ep702 ep702 ep62 ep702 310868 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 681503142) qz283 0 1 ep702 ep61 ep702 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 681503142) qz284 0 1 ep702 ep62 ep702 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz411 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 40932091) qz28)

noncomputable def ep704 := @Enclosure.Real.IsNear.cos_image qz197 qz411 Bool.false 40932091 262144 487 524288 Bool.false 310868 524288 1 76628 (@Enclosure.Real.IsNear.recentre' qz197 Bool.false 87900996256757722143 562949953421312000 2220750000510514893 2394625000000000000000 40932091 262144 487 524288 (ep701 rfl) rfl) (Enclosure.sfrac_false_div 40932091 262144) (BSN.cos_reduce3 qz411 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 23978260146836442447872) qz30) 226375608064910080 72057594037927936 Bool.false 310868 524288 24 1000000000000000 153256 76628 (BSN.sin_reduce_arg_pos_rat_q3 40932091 262144 226375608064910080 72057594037927936 24 23978260146836442447872 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 310868 524288 23978260146836442447872 37778931862957161709568 681503142 1073741824 153406 153256 (ep703 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep705 := BSN.cos_dyadic_bound_f 681503142 1073741824 2 1 524288 153406 ep702 ep57 ep702 ep702 ep58 ep702 422182 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 681503142) qz278 0 1 ep702 ep57 ep702 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 681503142) qz279 0 1 ep702 ep58 ep702 rfl rfl rfl rfl) rfl rfl

noncomputable def ep706 := @Enclosure.Real.IsNear.sin_image qz197 qz411 Bool.false 40932091 262144 487 524288 Bool.true 422182 524288 1 76628 (@Enclosure.Real.IsNear.recentre' qz197 Bool.false 87900996256757722143 562949953421312000 2220750000510514893 2394625000000000000000 40932091 262144 487 524288 (ep701 rfl) rfl) (Enclosure.sfrac_false_div 40932091 262144) (BSN.sin_reduce3 qz411 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 23978260146836442447872) qz30) 226375608064910080 72057594037927936 Bool.false 422182 524288 24 1000000000000000 153256 76628 (BSN.sin_reduce_arg_pos_rat_q3 40932091 262144 226375608064910080 72057594037927936 24 23978260146836442447872 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 422182 524288 23978260146836442447872 37778931862957161709568 681503142 1073741824 153406 153256 (ep705 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep707 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz110 (Real.cos qz197)) (@HMul.hMul Real Real Real qz0 qz110 (@Neg.neg Real Real.instNeg (Real.sin qz197))) Bool.false 13582056071 68719476736 207414442245 658229507915776 Bool.false 36890896433 137438953472 830723990129 2632918031663104 (@Enclosure.Real.IsNear.mulLit_ff qz110 (Real.cos qz197) 174763 524288 1 524288 77717 131072 9460531 10043785216 13582056071 68719476736 207414442245 658229507915776 qz353 (@Enclosure.Real.IsNear.recentre' (Real.cos qz197) Bool.false 310868 524288 37842124 40175140864 77717 131072 9460531 10043785216 (ep704 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz110 (@Neg.neg Real Real.instNeg (Real.sin qz197)) 174763 524288 1 524288 211091 262144 9460531 10043785216 36890896433 137438953472 830723990129 2632918031663104 qz353 (@Enclosure.Real.IsNear.neg (Real.sin qz197) Bool.true 211091 262144 9460531 10043785216 (@Enclosure.Real.IsNear.recentre' (Real.sin qz197) Bool.true 422182 524288 37842124 40175140864 211091 262144 9460531 10043785216 (ep706 rfl rfl) rfl)) rfl)

noncomputable def ep708 := @ep699 13582056071 68719476736 207414442245 658229507915776 Bool.false 36890896433 137438953472 830723990129 2632918031663104 Bool.false 18179965476797969072128 264553316473 274877906944 18442809758889 5265836063326208 Bool.false 9233148291579149025280 67179995615 274877906944 18444551666585 5265836063326208 EMRow17.d10 (ep700 ep707) rfl rfl

noncomputable abbrev qz198 := (@HMul.hMul Real Real Real qz263 qz380 (Real.log (Enclosure.sfrac Bool.false 10 1)))

noncomputable def ep709 := @Enclosure.Complex.IsNear.of_eq qz195 (Complex.mk (@HMul.hMul Real Real Real qz0 qz113 (Real.cos qz198)) (@HMul.hMul Real Real Real qz0 qz113 (@Neg.neg Real Real.instNeg (Real.sin qz198)))) Bool.false 83823796665 274877906944 1578203727835 5265836063326208 Bool.true 2876045865 34359738368 392794182377 1316459015831552 (BSN.cpow_neg_s_mk qz147 71064 1000 10 qz148 rfl)

noncomputable def ep710 := @Enclosure.Real.IsNear.mulLit_ff qz147 qz115 71064 1000 0 1 10369908600166117 4503599627370496 250000000057471 19157000000000000000 92115898095275617311 562949953421312000 2220750000510514893 2394625000000000000000 qz149 (BSN.isNear_log_sfrac 10 1 10369908600166117 4503599627370496 250000000057471 19157000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz355) Bool.false 21747274560655572598784 9444732965739290427392 1000000000229884 76628000000000000000 10369908600166117 4503599627370496 250000000057471 19157000000000000000 (BSN.log_rat_reduce_isNear 10 1 3 20 16 58495 262144 24973259072661432 36028797018963968 76628 1000000000000000 rfl rfl rfl rfl (ep336 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep711 := nat_lit 6845502603276613153724858816447041

noncomputable def ep712 := BSN.cos_dyadic_bound_f 287641361 1073741824 2 1 524288 153406 ep711 ep57 ep711 ep711 ep58 ep711 505587 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 287641361) qz278 0 1 ep711 ep57 ep711 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 287641361) qz279 0 1 ep711 ep58 ep711 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz412 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 85789615) qz20)

noncomputable def ep713 := @Enclosure.Real.IsNear.cos_image qz198 qz412 Bool.false 85789615 524288 487 524288 Bool.false 505587 524288 1 76628 (@Enclosure.Real.IsNear.recentre' qz198 Bool.false 92115898095275617311 562949953421312000 2220750000510514893 2394625000000000000000 85789615 524288 487 524288 (ep710 rfl) rfl) (Enclosure.sfrac_false_div 85789615 524288) (BSN.cos_reduce0 qz412 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 20240961362166147973120) qz23) 226375608064910080 72057594037927936 Bool.false 505587 524288 26 1000000000000000 153256 76628 (BSN.sin_reduce_arg_pos_rat_q0 85789615 524288 226375608064910080 72057594037927936 26 20240961362166147973120 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 505587 524288 20240961362166147973120 75557863725914323419136 287641361 1073741824 153406 153256 (ep712 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep714 := BSN.sin_dyadic_bound_f 287641361 1073741824 2 1 524288 153406 ep711 ep61 ep711 ep711 ep62 ep711 138776 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 287641361) qz283 0 1 ep711 ep61 ep711 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 287641361) qz284 0 1 ep711 ep62 ep711 rfl rfl rfl rfl) rfl rfl

noncomputable def ep715 := @Enclosure.Real.IsNear.sin_image qz198 qz412 Bool.false 85789615 524288 487 524288 Bool.false 138776 524288 1 76628 (@Enclosure.Real.IsNear.recentre' qz198 Bool.false 92115898095275617311 562949953421312000 2220750000510514893 2394625000000000000000 85789615 524288 487 524288 (ep710 rfl) rfl) (Enclosure.sfrac_false_div 85789615 524288) (BSN.sin_reduce0 qz412 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 20240961362166147973120) qz23) 226375608064910080 72057594037927936 Bool.false 138776 524288 26 1000000000000000 153256 76628 (BSN.sin_reduce_arg_pos_rat_q0 85789615 524288 226375608064910080 72057594037927936 26 20240961362166147973120 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 138776 524288 20240961362166147973120 75557863725914323419136 287641361 1073741824 153406 153256 (ep714 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep716 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz113 (Real.cos qz198)) (@HMul.hMul Real Real Real qz0 qz113 (@Neg.neg Real Real.instNeg (Real.sin qz198))) Bool.false 83823796665 274877906944 1578203727835 5265836063326208 Bool.true 2876045865 34359738368 392794182377 1316459015831552 (@Enclosure.Real.IsNear.mulLit_ff qz113 (Real.cos qz198) 165795 524288 1 524288 505587 524288 9460531 10043785216 83823796665 274877906944 1578203727835 5265836063326208 qz357 (@Enclosure.Real.IsNear.recentre' (Real.cos qz198) Bool.false 505587 524288 37842124 40175140864 505587 524288 9460531 10043785216 (ep713 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz113 (@Neg.neg Real Real.instNeg (Real.sin qz198)) 165795 524288 1 524288 17347 65536 9460531 10043785216 2876045865 34359738368 392794182377 1316459015831552 qz357 (@Enclosure.Real.IsNear.neg (Real.sin qz198) Bool.false 17347 65536 9460531 10043785216 (@Enclosure.Real.IsNear.recentre' (Real.sin qz198) Bool.false 138776 524288 37842124 40175140864 17347 65536 9460531 10043785216 (ep715 rfl rfl) rfl)) rfl)

noncomputable def ep717 := @ep697 83823796665 274877906944 1578203727835 5265836063326208 Bool.true 2876045865 34359738368 392794182377 1316459015831552 Bool.false 95761171686566523830272 174188556569 137438953472 5005253371681 1316459015831552 Bool.false 1517725605248641269760 44171628695 274877906944 20015728396093 5265836063326208 (ep698 (BSN.head_sum_c_succ qz138 9 10 rfl rfl) (ep708 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep709 ep716) rfl rfl

noncomputable abbrev qz199 := (@HMul.hMul Real Real Real qz263 qz380 (Real.log (Enclosure.sfrac Bool.false 11 1)))

noncomputable def ep718 := @Enclosure.Complex.IsNear.of_eq qz194 (Complex.mk (@HMul.hMul Real Real Real qz0 qz116 (Real.cos qz199)) (@HMul.hMul Real Real Real qz0 qz116 (@Neg.neg Real Real.instNeg (Real.sin qz199)))) Bool.false 60197589753 274877906944 1502815860179 5265836063326208 Bool.true 28483148457 137438953472 751212135971 2632918031663104 (BSN.cpow_neg_s_mk qz147 71064 1000 11 qz148 rfl)

noncomputable def ep719 := @Enclosure.Real.IsNear.mulLit_ff qz147 qz118 71064 1000 0 1 10799147631728357 4503599627370496 250000000057471 19157000000000000000 95928828412642995231 562949953421312000 2220750000510514893 2394625000000000000000 qz149 (BSN.isNear_log_sfrac 11 1 10799147631728357 4503599627370496 250000000057471 19157000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz359) Bool.false 22647454054174387339264 9444732965739290427392 1000000000229884 76628000000000000000 10799147631728357 4503599627370496 250000000057471 19157000000000000000 (BSN.log_rat_reduce_isNear 11 1 3 22 16 83480 262144 24973259072661432 36028797018963968 76628 1000000000000000 rfl rfl rfl rfl (ep347 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep720 := nat_lit 979201659657887017251353838399196238240405082962106544696837670377441263616

noncomputable def ep721 := nat_lit 192201269745291090780237371285482578846147288617791404663673982287937536

noncomputable def ep722 := nat_lit 2937220576434170469572501040455017749563522954309084051281185663167747915776

noncomputable def ep723 := BSN.cos_dyadic_bound_f 813709772 1073741824 3 2 524288 153406 ep720 ep78 ep721 ep722 ep80 ep721 380807 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 813709772) qz278 0 2 ep720 ep78 ep721 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 813709772) qz279 0 2 ep722 ep80 ep721 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz413 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 89340683) qz20)

noncomputable def ep724 := @Enclosure.Real.IsNear.cos_image qz199 qz413 Bool.false 89340683 524288 487 524288 Bool.false 380807 524288 1 76628 (@Enclosure.Real.IsNear.recentre' qz199 Bool.false 95928828412642995231 562949953421312000 2220750000510514893 2394625000000000000000 89340683 524288 487 524288 (ep719 rfl) rfl) (Enclosure.sfrac_false_div 89340683 524288) (BSN.cos_reduce0 qz413 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 57259734847777203552256) qz23) 226375608064910080 72057594037927936 Bool.false 380807 524288 27 1000000000000000 153256 76628 (BSN.sin_reduce_arg_pos_rat_q0 89340683 524288 226375608064910080 72057594037927936 27 57259734847777203552256 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 380807 524288 57259734847777203552256 75557863725914323419136 813709772 1073741824 153406 153256 (ep723 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep725 := nat_lit 438407652471180172920689139718656256

noncomputable def ep726 := BSN.sin_dyadic_bound_f 813709772 1073741824 2 1 524288 153406 ep725 ep61 ep725 ep725 ep62 ep725 360366 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 813709772) qz283 0 1 ep725 ep61 ep725 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 813709772) qz284 0 1 ep725 ep62 ep725 rfl rfl rfl rfl) rfl rfl

noncomputable def ep727 := @Enclosure.Real.IsNear.sin_image qz199 qz413 Bool.false 89340683 524288 487 524288 Bool.false 360366 524288 1 76628 (@Enclosure.Real.IsNear.recentre' qz199 Bool.false 95928828412642995231 562949953421312000 2220750000510514893 2394625000000000000000 89340683 524288 487 524288 (ep719 rfl) rfl) (Enclosure.sfrac_false_div 89340683 524288) (BSN.sin_reduce0 qz413 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 57259734847777203552256) qz23) 226375608064910080 72057594037927936 Bool.false 360366 524288 27 1000000000000000 153256 76628 (BSN.sin_reduce_arg_pos_rat_q0 89340683 524288 226375608064910080 72057594037927936 27 57259734847777203552256 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 360366 524288 57259734847777203552256 75557863725914323419136 813709772 1073741824 153406 153256 (ep726 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep728 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz116 (Real.cos qz199)) (@HMul.hMul Real Real Real qz0 qz116 (@Neg.neg Real Real.instNeg (Real.sin qz199))) Bool.false 60197589753 274877906944 1502815860179 5265836063326208 Bool.true 28483148457 137438953472 751212135971 2632918031663104 (@Enclosure.Real.IsNear.mulLit_ff qz116 (Real.cos qz199) 158079 524288 1 524288 380807 524288 9460531 10043785216 60197589753 274877906944 1502815860179 5265836063326208 qz361 (@Enclosure.Real.IsNear.recentre' (Real.cos qz199) Bool.false 380807 524288 37842124 40175140864 380807 524288 9460531 10043785216 (ep724 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz116 (@Neg.neg Real Real.instNeg (Real.sin qz199)) 158079 524288 1 524288 180183 262144 9460531 10043785216 28483148457 137438953472 751212135971 2632918031663104 qz361 (@Enclosure.Real.IsNear.neg (Real.sin qz199) Bool.false 180183 262144 9460531 10043785216 (@Enclosure.Real.IsNear.recentre' (Real.sin qz199) Bool.false 360366 524288 37842124 40175140864 180183 262144 9460531 10043785216 (ep727 rfl rfl) rfl)) rfl)

noncomputable def ep729 := @ep695 60197589753 274877906944 1502815860179 5265836063326208 Bool.true 28483148457 137438953472 751212135971 2632918031663104 Bool.false 56154079580472372887552 408574702891 274877906944 21523829346903 5265836063326208 Bool.true 1758485810040818106368 12794668219 274877906944 21518152668035 5265836063326208 (ep696 (BSN.head_sum_c_succ qz138 10 11 rfl rfl) (ep717 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep718 ep728) rfl rfl

noncomputable abbrev qz200 := (@HMul.hMul Real Real Real qz263 qz380 (Real.log (Enclosure.sfrac Bool.false 12 1)))

noncomputable def ep730 := @Enclosure.Complex.IsNear.of_eq qz193 (Complex.mk (@HMul.hMul Real Real Real qz0 qz119 (Real.cos qz200)) (@HMul.hMul Real Real Real qz0 qz119 (@Neg.neg Real Real.instNeg (Real.sin qz200)))) Bool.false 7846991603 34359738368 719898615341 2632918031663104 Bool.true 48535051367 274877906944 1437994691081 5265836063326208 (BSN.cpow_neg_s_mk qz147 71064 1000 12 qz148 rfl)

noncomputable def ep731 := @Enclosure.Real.IsNear.mulLit_ff qz147 qz121 71064 1000 0 1 11191020447815397 4503599627370496 250000000057471 19157000000000000000 99409834637944171551 562949953421312000 2220750000510514893 2394625000000000000000 qz149 (BSN.isNear_log_sfrac 12 1 11191020447815397 4503599627370496 250000000057471 19157000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz363) Bool.false 23469270914176955449344 9444732965739290427392 1000000000229884 76628000000000000000 11191020447815397 4503599627370496 250000000057471 19157000000000000000 (BSN.log_rat_reduce_isNear 12 1 3 24 16 106290 262144 24973259072661432 36028797018963968 76628 1000000000000000 rfl rfl rfl rfl (ep361 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep732 := nat_lit 249402689597292780558205768706560000

noncomputable def ep733 := BSN.cos_dyadic_bound_f 706684040 1073741824 2 1 524288 153406 ep732 ep57 ep732 ep732 ep58 ep732 414776 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 706684040) qz278 0 1 ep732 ep57 ep732 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 706684040) qz279 0 1 ep732 ep58 ep732 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz414 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 92582623) qz20)

noncomputable def ep734 := @Enclosure.Real.IsNear.cos_image qz200 qz414 Bool.false 92582623 524288 487 524288 Bool.false 414776 524288 1 76628 (@Enclosure.Real.IsNear.recentre' qz200 Bool.false 99409834637944171551 562949953421312000 2220750000510514893 2394625000000000000000 92582623 524288 487 524288 (ep731 rfl) rfl) (Enclosure.sfrac_false_div 92582623 524288) (BSN.cos_reduce0 qz414 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 49728468473875085131776) qz23) 226375608064910080 72057594037927936 Bool.false 414776 524288 28 1000000000000000 153256 76628 (BSN.sin_reduce_arg_pos_rat_q0 92582623 524288 226375608064910080 72057594037927936 28 49728468473875085131776 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 414776 524288 49728468473875085131776 75557863725914323419136 706684040 1073741824 153406 153256 (ep733 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep735 := BSN.sin_dyadic_bound_f 706684040 1073741824 2 1 524288 153406 ep732 ep61 ep732 ep732 ep62 ep732 320683 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 706684040) qz283 0 1 ep732 ep61 ep732 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 706684040) qz284 0 1 ep732 ep62 ep732 rfl rfl rfl rfl) rfl rfl

noncomputable def ep736 := @Enclosure.Real.IsNear.sin_image qz200 qz414 Bool.false 92582623 524288 487 524288 Bool.false 320683 524288 1 76628 (@Enclosure.Real.IsNear.recentre' qz200 Bool.false 99409834637944171551 562949953421312000 2220750000510514893 2394625000000000000000 92582623 524288 487 524288 (ep731 rfl) rfl) (Enclosure.sfrac_false_div 92582623 524288) (BSN.sin_reduce0 qz414 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 49728468473875085131776) qz23) 226375608064910080 72057594037927936 Bool.false 320683 524288 28 1000000000000000 153256 76628 (BSN.sin_reduce_arg_pos_rat_q0 92582623 524288 226375608064910080 72057594037927936 28 49728468473875085131776 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 320683 524288 49728468473875085131776 75557863725914323419136 706684040 1073741824 153406 153256 (ep735 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep737 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz119 (Real.cos qz200)) (@HMul.hMul Real Real Real qz0 qz119 (@Neg.neg Real Real.instNeg (Real.sin qz200))) Bool.false 7846991603 34359738368 719898615341 2632918031663104 Bool.true 48535051367 274877906944 1437994691081 5265836063326208 (@Enclosure.Real.IsNear.mulLit_ff qz119 (Real.cos qz200) 151349 524288 1 524288 51847 65536 9460531 10043785216 7846991603 34359738368 719898615341 2632918031663104 qz365 (@Enclosure.Real.IsNear.recentre' (Real.cos qz200) Bool.false 414776 524288 37842124 40175140864 51847 65536 9460531 10043785216 (ep734 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz119 (@Neg.neg Real Real.instNeg (Real.sin qz200)) 151349 524288 1 524288 320683 524288 9460531 10043785216 48535051367 274877906944 1437994691081 5265836063326208 qz365 (@Enclosure.Real.IsNear.neg (Real.sin qz200) Bool.false 320683 524288 9460531 10043785216 (@Enclosure.Real.IsNear.recentre' (Real.sin qz200) Bool.false 320683 524288 37842124 40175140864 320683 524288 9460531 10043785216 (ep736 rfl rfl) rfl)) rfl)

noncomputable def ep738 := @ep693 7846991603 34359738368 719898615341 2632918031663104 Bool.true 48535051367 274877906944 1437994691081 5265836063326208 Bool.false 16195484522757876613120 471350635715 274877906944 22963626577585 5265836063326208 Bool.true 16858184953262122205184 30664859793 137438953472 5739036839779 1316459015831552 (ep694 (BSN.head_sum_c_succ qz138 11 12 rfl rfl) (ep729 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep730 ep737) rfl rfl

noncomputable abbrev qz201 := (@HMul.hMul Real Real Real qz263 qz380 (Real.log (Enclosure.sfrac Bool.false 13 1)))

noncomputable def ep739 := @Enclosure.Complex.IsNear.of_eq qz192 (Complex.mk (@HMul.hMul Real Real Real qz0 qz122 (Real.cos qz201)) (@HMul.hMul Real Real Real qz0 qz122 (@Neg.neg Real Real.instNeg (Real.sin qz201)))) Bool.false 38043152875 137438953472 694242145853 2632918031663104 Bool.true 4794055259 274877906944 1379091978589 5265836063326208 (BSN.cpow_neg_s_mk qz147 71064 1000 13 qz148 rfl)

noncomputable def ep740 := @Enclosure.Real.IsNear.mulLit_ff qz147 qz124 71064 1000 0 1 11551488463034085 4503599627370496 250000000057471 19157000000000000000 20522374403426355411 112589990684262400 2220750000510514893 2394625000000000000000 qz149 (BSN.isNear_log_sfrac 13 1 11551488463034085 4503599627370496 250000000057471 19157000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz367) Bool.false 24225227133228857425920 9444732965739290427392 1000000000229884 76628000000000000000 11551488463034085 4503599627370496 250000000057471 19157000000000000000 (BSN.log_rat_reduce_isNear 13 1 3 26 16 127272 262144 24973259072661432 36028797018963968 76628 1000000000000000 rfl rfl rfl rfl (ep372 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep741 := BSN.cos_dyadic_bound_f 67565380 1073741824 1 0 524288 153406 0 1 1 0 1 1 523250 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 67565380) qz278 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 67565380) qz279 0 0 rfl) rfl rfl

noncomputable abbrev qz415 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 5972797) (@Nat.cast Real Real.instNatCast 32768))

noncomputable def ep742 := @Enclosure.Real.IsNear.cos_image qz201 qz415 Bool.false 5972797 32768 61 65536 Bool.false 523250 524288 1 76628 (@Enclosure.Real.IsNear.recentre' qz201 Bool.false 20522374403426355411 112589990684262400 2220750000510514893 2394625000000000000000 5972797 32768 61 65536 (ep740 rfl) rfl) (Enclosure.sfrac_false_div 5972797 32768) (BSN.cos_reduce0 qz415 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 297155685674798546944) qz297) 226375608064910080 72057594037927936 Bool.false 523250 524288 29 1000000000000000 153256 76628 (BSN.sin_reduce_arg_pos_rat_q0 5972797 32768 226375608064910080 72057594037927936 29 297155685674798546944 4722366482869645213696 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 523250 524288 297155685674798546944 4722366482869645213696 67565380 1073741824 153406 153256 (ep741 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep743 := BSN.sin_dyadic_bound_f 67565380 1073741824 1 0 524288 153406 0 1 1 0 1 1 32969 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 67565380) qz283 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 67565380) qz284 0 0 rfl) rfl rfl

noncomputable def ep744 := @Enclosure.Real.IsNear.sin_image qz201 qz415 Bool.false 5972797 32768 61 65536 Bool.false 32969 524288 1 76628 (@Enclosure.Real.IsNear.recentre' qz201 Bool.false 20522374403426355411 112589990684262400 2220750000510514893 2394625000000000000000 5972797 32768 61 65536 (ep740 rfl) rfl) (Enclosure.sfrac_false_div 5972797 32768) (BSN.sin_reduce0 qz415 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 297155685674798546944) qz297) 226375608064910080 72057594037927936 Bool.false 32969 524288 29 1000000000000000 153256 76628 (BSN.sin_reduce_arg_pos_rat_q0 5972797 32768 226375608064910080 72057594037927936 29 297155685674798546944 4722366482869645213696 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 32969 524288 297155685674798546944 4722366482869645213696 67565380 1073741824 153406 153256 (ep743 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep745 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz122 (Real.cos qz201)) (@HMul.hMul Real Real Real qz0 qz122 (@Neg.neg Real Real.instNeg (Real.sin qz201))) Bool.false 38043152875 137438953472 694242145853 2632918031663104 Bool.true 4794055259 274877906944 1379091978589 5265836063326208 (@Enclosure.Real.IsNear.mulLit_ff qz122 (Real.cos qz201) 145411 524288 1 524288 261625 262144 1184961 1255473152 38043152875 137438953472 694242145853 2632918031663104 qz369 (@Enclosure.Real.IsNear.recentre' (Real.cos qz201) Bool.false 523250 524288 4739844 5021892608 261625 262144 1184961 1255473152 (ep742 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz122 (@Neg.neg Real Real.instNeg (Real.sin qz201)) 145411 524288 1 524288 32969 524288 1184961 1255473152 4794055259 274877906944 1379091978589 5265836063326208 qz369 (@Enclosure.Real.IsNear.neg (Real.sin qz201) Bool.false 32969 524288 1184961 1255473152 (@Enclosure.Real.IsNear.recentre' (Real.sin qz201) Bool.false 32969 524288 4739844 5021892608 32969 524288 1184961 1255473152 (ep744 rfl rfl) rfl)) rfl)

noncomputable def ep746 := @ep691 38043152875 137438953472 694242145853 2632918031663104 Bool.true 4794055259 274877906944 1379091978589 5265836063326208 Bool.false 75239160326862122516480 547436941465 274877906944 24352110869291 5265836063326208 Bool.true 9087982414314959011840 66123774845 274877906944 24335239337705 5265836063326208 (ep692 (BSN.head_sum_c_succ qz138 12 13 rfl rfl) (ep738 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep739 ep745) rfl rfl

noncomputable abbrev qz202 := (@HMul.hMul Real Real Real qz263 qz380 qz373)

noncomputable def ep747 := @Enclosure.Complex.IsNear.of_eq qz191 (Complex.mk (@HMul.hMul Real Real Real qz0 qz127 (Real.cos qz202)) (@HMul.hMul Real Real Real qz0 qz127 (@Neg.neg Real Real.instNeg (Real.sin qz202)))) Bool.false 42502762809 274877906944 1331439398435 5265836063326208 Bool.false 59920083351 274877906944 1333820651849 5265836063326208 (BSN.cpow_neg_s_mk qz147 71064 1000 14 qz148 rfl)

noncomputable def ep748 := @Enclosure.Real.IsNear.mulLit_ff qz147 qz130 71064 1000 0 1 11885241781671653 4503599627370496 250000000057471 19157000000000000000 105576602746589293599 562949953421312000 2220750000510514893 2394625000000000000000 qz149 (BSN.isNear_log_sfrac 14 1 11885241781671653 4503599627370496 250000000057471 19157000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' qz374 Bool.false 24925158572916270432256 9444732965739290427392 1000000000229884 76628000000000000000 11885241781671653 4503599627370496 250000000057471 19157000000000000000 (BSN.log_rat_reduce_isNear 14 1 3 28 16 146699 262144 24973259072661432 36028797018963968 76628 1000000000000000 rfl rfl rfl rfl (ep394 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep749 := nat_lit 192582930460805528477500806691156801

noncomputable def ep750 := BSN.sin_dyadic_bound_f 662452049 1073741824 2 1 524288 153406 ep749 ep61 ep749 ep749 ep62 ep749 303329 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 662452049) qz283 0 1 ep749 ep61 ep749 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 662452049) qz284 0 1 ep749 ep62 ep749 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz416 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 98325873) qz20)

noncomputable def ep751 := @Enclosure.Real.IsNear.cos_image qz202 qz416 Bool.false 98325873 524288 487 524288 Bool.false 303329 524288 1 76628 (@Enclosure.Real.IsNear.recentre' qz202 Bool.false 105576602746589293599 562949953421312000 2220750000510514893 2394625000000000000000 98325873 524288 487 524288 (ep748 rfl) rfl) (Enclosure.sfrac_false_div 98325873 524288) (BSN.cos_reduce3 qz416 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 46615918782585289834496) qz23) 226375608064910080 72057594037927936 Bool.false 303329 524288 29 1000000000000000 153256 76628 (BSN.sin_reduce_arg_pos_rat_q3 98325873 524288 226375608064910080 72057594037927936 29 46615918782585289834496 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 303329 524288 46615918782585289834496 75557863725914323419136 662452049 1073741824 153406 153256 (ep750 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep752 := BSN.cos_dyadic_bound_f 662452049 1073741824 2 1 524288 153406 ep749 ep57 ep749 ep749 ep58 ep749 427631 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 662452049) qz278 0 1 ep749 ep57 ep749 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 662452049) qz279 0 1 ep749 ep58 ep749 rfl rfl rfl rfl) rfl rfl

noncomputable def ep753 := @Enclosure.Real.IsNear.sin_image qz202 qz416 Bool.false 98325873 524288 487 524288 Bool.true 427631 524288 1 76628 (@Enclosure.Real.IsNear.recentre' qz202 Bool.false 105576602746589293599 562949953421312000 2220750000510514893 2394625000000000000000 98325873 524288 487 524288 (ep748 rfl) rfl) (Enclosure.sfrac_false_div 98325873 524288) (BSN.sin_reduce3 qz416 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 46615918782585289834496) qz23) 226375608064910080 72057594037927936 Bool.false 427631 524288 29 1000000000000000 153256 76628 (BSN.sin_reduce_arg_pos_rat_q3 98325873 524288 226375608064910080 72057594037927936 29 46615918782585289834496 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 427631 524288 46615918782585289834496 75557863725914323419136 662452049 1073741824 153406 153256 (ep752 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep754 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz127 (Real.cos qz202)) (@HMul.hMul Real Real Real qz0 qz127 (@Neg.neg Real Real.instNeg (Real.sin qz202))) Bool.false 42502762809 274877906944 1331439398435 5265836063326208 Bool.false 59920083351 274877906944 1333820651849 5265836063326208 (@Enclosure.Real.IsNear.mulLit_ff qz127 (Real.cos qz202) 140121 524288 1 524288 303329 524288 9460531 10043785216 42502762809 274877906944 1331439398435 5265836063326208 qz376 (@Enclosure.Real.IsNear.recentre' (Real.cos qz202) Bool.false 303329 524288 37842124 40175140864 303329 524288 9460531 10043785216 (ep751 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz127 (@Neg.neg Real Real.instNeg (Real.sin qz202)) 140121 524288 1 524288 427631 524288 9460531 10043785216 59920083351 274877906944 1333820651849 5265836063326208 qz376 (@Enclosure.Real.IsNear.neg (Real.sin qz202) Bool.true 427631 524288 9460531 10043785216 (@Enclosure.Real.IsNear.recentre' (Real.sin qz202) Bool.true 427631 524288 37842124 40175140864 427631 524288 9460531 10043785216 (ep753 rfl rfl) rfl)) rfl)

noncomputable def ep755 := @ep689 42502762809 274877906944 1331439398435 5265836063326208 Bool.false 59920083351 274877906944 1333820651849 5265836063326208 Bool.false 162161391133999451078656 294969852137 137438953472 12841775133863 2632918031663104 Bool.true 1705257733197016334336 3101845747 137438953472 12834529994777 2632918031663104 (ep690 (BSN.head_sum_c_succ qz138 13 14 rfl rfl) (ep746 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep747 ep754) rfl rfl

noncomputable def ep756 := @Enclosure.Complex.IsNear.mul qz188 (@HAdd.hAdd Complex Complex Complex qz5 qz189 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz55 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz55 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz138 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz55 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz103 qz190 (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz55 2 k) 1))))) Bool.true 483202607470225865992049 ep565 ep683 ep567 Bool.false

noncomputable abbrev qz203 := (Complex.re qz409)

noncomputable abbrev qz204 := (Complex.im qz409)

noncomputable def ep757 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 qz203 (Complex.re (@HAdd.hAdd Complex Complex Complex qz5 qz189 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz55 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz55 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz138 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz55 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz103 qz190 (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz55 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz204 (Complex.im (@HAdd.hAdd Complex Complex Complex qz5 qz189 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz55 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz55 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz138 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz55 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz103 qz190 (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz55 2 k) 1))))))) 2794983486656851750729 31235117955742213079040 14669569365177297044159

noncomputable def ep758 := nat_lit 119674230935630715191033856

noncomputable def ep759 := nat_lit 415535524082051094413312000

noncomputable def ep760 := nat_lit 419246956690408565829008512562833447568015360

noncomputable def ep761 := @Enclosure.Real.IsNear.mulLit_tf qz203 (Complex.re (@HAdd.hAdd Complex Complex Complex qz5 qz189 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz55 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz55 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz138 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz55 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz103 qz190 (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz55 2 k) 1)))))) 49066437289 274877906944 1287634629595 5265836063326208 56963244961

noncomputable abbrev qz417 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) qz478 (Real.log (Enclosure.sfrac Bool.false 15 1)))

noncomputable abbrev qz205 := (Real.cos qz417)

noncomputable abbrev qz206 := (@Neg.neg Real Real.instNeg (Real.sin qz417))

noncomputable abbrev qz418 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 15)))

noncomputable def ep762 := @Enclosure.Complex.IsNear.of_eq qz188 (Complex.mk (@HMul.hMul Real Real Real qz0 qz418 qz205) (@HMul.hMul Real Real Real qz0 qz418 qz206)) Bool.true 49066437289 274877906944 1287634629595 5265836063326208 Bool.false 25640214997 137438953472 643973971165 2632918031663104 (BSN.cpow_neg_s_mk qz147 71064 1000 15 qz148 rfl)

noncomputable abbrev qz419 := (Real.sqrt (@Nat.cast Real Real.instNatCast 15))

noncomputable abbrev qz420 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 15) qz19)

noncomputable def ep763 := @Enclosure.Real.IsNear.inv_image qz419 2030559 524288 1 524288 67685 67686 262144 (@Enclosure.Real.IsNear.of_eq qz419 (Real.sqrt qz420) Bool.false 2030559 524288 1 524288 (BSN.sqrt_natCast_div_one 15) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz420) Bool.false 2030559 524288 1 524288 2030559 524288 1 524288 (BSN.sqrt_enclosure 15 1 1015279 1015280 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep764 := BSN.log_dyadic_bound 7 23 6 5 430628584065881355 262144 76628 14087658153505881 266939110305 164785 30 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 7) (BSN.artanhQ 23) 0 5 14087658153505881 430628584065881355 266939110305 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz421 := (Real.log (Enclosure.sfrac Bool.false 15 1))

noncomputable abbrev qz207 := qz421

noncomputable def ep765 := @Enclosure.Real.IsNear.mulLit_ff qz147 qz207 71064 1000 0 1 12195956895733477 4503599627370496 250000000057471 19157000000000000000 108336685104800476191 562949953421312000 2220750000510514893 2394625000000000000000 qz149 (BSN.isNear_log_sfrac 15 1 12195956895733477 4503599627370496 250000000057471 19157000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz420) Bool.false 25576775395801252757504 9444732965739290427392 1000000000229884 76628000000000000000 12195956895733477 4503599627370496 250000000057471 19157000000000000000 (BSN.log_rat_reduce_isNear 15 1 3 30 16 164785 262144 24973259072661432 36028797018963968 76628 1000000000000000 rfl rfl rfl rfl (ep764 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep766 := nat_lit 1262116507565378375597103152880057189367000035263240630088874905399453450496

noncomputable def ep767 := nat_lit 319272578694353020378410213006689104234198416954565980626189537733673216

noncomputable def ep768 := nat_lit 3785710977538746420750552638214158189892531708955812758305372337122893005056

noncomputable def ep769 := BSN.cos_dyadic_bound_f 867002206 1073741824 3 2 524288 153406 ep766 ep78 ep767 ep768 ep80 ep767 362459 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 867002206) qz278 0 2 ep766 ep78 ep767 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 867002206) qz279 0 2 ep768 ep80 ep767 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz208 := qz417

noncomputable abbrev qz422 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 6306025) (@Nat.cast Real Real.instNatCast 32768))

noncomputable def ep770 := @Enclosure.Real.IsNear.cos_image qz208 qz422 Bool.false 6306025 32768 487 524288 Bool.true 362459 524288 1 76628 (@Enclosure.Real.IsNear.recentre' qz208 Bool.false 108336685104800476191 562949953421312000 2220750000510514893 2394625000000000000000 6306025 32768 487 524288 (ep765 rfl) rfl) (Enclosure.sfrac_false_div 6306025 32768) (BSN.cos_reduce2 qz422 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 3813116027390258053120) qz297) 226375608064910080 72057594037927936 Bool.false 362459 524288 30 1000000000000000 153256 76628 (BSN.sin_reduce_arg_pos_rat_q2 6306025 32768 226375608064910080 72057594037927936 30 3813116027390258053120 4722366482869645213696 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 362459 524288 3813116027390258053120 4722366482869645213696 867002206 1073741824 153406 153256 (ep769 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep771 := nat_lit 565042103470487427692668588087342096

noncomputable def ep772 := BSN.sin_dyadic_bound_f 867002206 1073741824 2 1 524288 153406 ep771 ep61 ep771 ep771 ep62 ep771 378814 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 867002206) qz283 0 1 ep771 ep61 ep771 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 867002206) qz284 0 1 ep771 ep62 ep771 rfl rfl rfl rfl) rfl rfl

noncomputable def ep773 := @Enclosure.Real.IsNear.sin_image qz208 qz422 Bool.false 6306025 32768 487 524288 Bool.true 378814 524288 1 76628 (@Enclosure.Real.IsNear.recentre' qz208 Bool.false 108336685104800476191 562949953421312000 2220750000510514893 2394625000000000000000 6306025 32768 487 524288 (ep765 rfl) rfl) (Enclosure.sfrac_false_div 6306025 32768) (BSN.sin_reduce2 qz422 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 3813116027390258053120) qz297) 226375608064910080 72057594037927936 Bool.false 378814 524288 30 1000000000000000 153256 76628 (BSN.sin_reduce_arg_pos_rat_q2 6306025 32768 226375608064910080 72057594037927936 30 3813116027390258053120 4722366482869645213696 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 378814 524288 3813116027390258053120 4722366482869645213696 867002206 1073741824 153406 153256 (ep772 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz209 := (Real.sin qz417)

noncomputable def ep774 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz418 qz205) (@HMul.hMul Real Real Real qz0 qz418 qz206) Bool.true 49066437289 274877906944 1287634629595 5265836063326208 Bool.false 25640214997 137438953472 643973971165 2632918031663104 (@Enclosure.Real.IsNear.mulLit_ft qz418 qz205 135371 524288 1 524288 362459 524288 9460531 10043785216 49066437289 274877906944 1287634629595 5265836063326208 (@Enclosure.Real.IsNear.recentre' qz418 Bool.false 135371 524288 1 524288 135371 524288 1 524288 (ep763 rfl rfl) rfl) (@Enclosure.Real.IsNear.recentre' qz205 Bool.true 362459 524288 37842124 40175140864 362459 524288 9460531 10043785216 (ep770 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz418 qz206 135371 524288 1 524288 189407 262144 9460531 10043785216 25640214997 137438953472 643973971165 2632918031663104 (@Enclosure.Real.IsNear.recentre' qz418 Bool.false 135371 524288 1 524288 135371 524288 1 524288 (ep763 rfl rfl) rfl) (@Enclosure.Real.IsNear.neg qz209 Bool.true 189407 262144 9460531 10043785216 (@Enclosure.Real.IsNear.recentre' qz209 Bool.true 378814 524288 37842124 40175140864 189407 262144 9460531 10043785216 (ep773 rfl rfl) rfl)) rfl)

noncomputable def ep775 := @ep761 113632697160 0 1 2794983486656851750729 31235117955742213079040 14669569365177297044159 ep758 (@Enclosure.Complex.IsNear.re_isNear qz188 Bool.true 49066437289 274877906944 1287634629595 5265836063326208 Bool.false 25640214997 137438953472 643973971165 2632918031663104 (ep762 ep774))

noncomputable def ep776 := @Enclosure.Complex.IsNear.re_isNear (@HAdd.hAdd Complex Complex Complex qz5 qz189 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz55 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz55 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz138 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz55 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz103 qz190 (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz55 2 k) 1))))) Bool.false 56963244961 113632697160 0 1 Bool.false

noncomputable def ep777 := @Enclosure.Complex.IsNear.addLitP qz189 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz55 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz55 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz138 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz55 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz103 qz190 (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz55 2 k) 1)))) Bool.false 314708881 631292762 0 1 Bool.true 66622500

noncomputable def ep778 := @ep777 315646381 0 1 Bool.false 1 360 0 1 Bool.false 987 2500 0 1 Bool.false 113926489922 56963244961 113632697160 0 1 Bool.false 144986728047 144986728047 789115952500 0 1

noncomputable abbrev qz210 := (@HDiv.hDiv Complex Complex Complex qz320 qz410 (@HSub.hSub Complex Complex Complex qz313 qz378 (1 : Complex)))

noncomputable def ep779 := @Enclosure.Complex.IsNear.addLitP qz210 qz76 Bool.true 30000000 20201368384 0 1 Bool.true 4263840000 20201368384 0 1

noncomputable def ep780 := @Enclosure.Complex.IsNear.of_eq qz210 (Complex.mk (Enclosure.sfrac Bool.true 30000000 20201368384) (Enclosure.sfrac Bool.true 4263840000 20201368384)) Bool.true 30000000 20201368384 0 1 Bool.true 4263840000 20201368384 0 1

noncomputable def ep781 := @ep779 Bool.false 1 2 0 1 Bool.false 0 1 0 1 Bool.false 20141368384 314708881 631292762 0 1 Bool.true 4263840000 66622500 315646381 0 1 (ep780 (BSN.N_div_s_sub_one_mk qz147 71064 1000 15 qz148 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 30000000 20201368384) (Enclosure.sfrac Bool.true 4263840000 20201368384) Bool.true 30000000 20201368384 0 1 Bool.true 4263840000 20201368384 0 1 (Enclosure.Real.IsNear.const Bool.true 30000000 20201368384) (Enclosure.Real.IsNear.const Bool.true 4263840000 20201368384))) qz77 rfl

noncomputable abbrev qz211 := (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz349 qz410 1))

noncomputable def ep782 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz55 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz55 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz138 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz55 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz103 qz190 (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz55 2 k) 1)))) (@HAdd.hAdd Complex Complex Complex qz5 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz55 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz55 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz138 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz55 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz103 qz190 (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz55 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz78)) ↑qz134) (@Polynomial.eval Complex Complex.instSemiring qz138 (@ascPochhammer Complex Complex.instSemiring 1))) qz211)) Bool.false 1 360 0 1

noncomputable def ep783 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz55 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz55 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz138 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz55 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz103 qz190 (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz55 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz78)) ↑qz134) (@Polynomial.eval Complex Complex.instSemiring qz138 (@ascPochhammer Complex Complex.instSemiring 1))) qz211) Bool.false 0 1 0 1 Bool.false

noncomputable def ep784 := @ep783 0 1 0 1 Bool.false 1 360 0 1 Bool.false 987 2500 0 1 Bool.false 1 1 360 0 1 Bool.false 987 987 2500 0

noncomputable def ep785 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz55 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz55 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz138 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz55 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz103 qz190 (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz55 2 k) 1)))) (Complex.mk qz14 qz14) Bool.false 0 1 0 1 Bool.false

noncomputable def ep786 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz78)) ↑qz134) (@Polynomial.eval Complex Complex.instSemiring qz138 (@ascPochhammer Complex Complex.instSemiring 1))) qz211 Bool.false 1 360 0 1 Bool.false 987 2500 0 1

noncomputable def ep787 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz78)) ↑qz134) (@Polynomial.eval Complex Complex.instSemiring qz138 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz211)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz78)) ↑qz134) (@Polynomial.eval Complex Complex.instSemiring qz138 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz211)) 1 360 0 1 0 1 0

noncomputable def ep788 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz78)) ↑qz134) (@Polynomial.eval Complex Complex.instSemiring qz138 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz211) 1 24 0 1 1 15 0 1 1

noncomputable def ep789 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz78)) ↑qz134)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz138 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz78)) ↑qz134)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz138 (@ascPochhammer Complex Complex.instSemiring 1)))) 1 24 0 1 0 1 0 1 1

noncomputable def ep790 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz78)) ↑qz134)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz138 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 1 2 0 1 1 24 0

noncomputable def ep791 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz138 (@ascPochhammer Complex Complex.instSemiring 1)) qz138 Bool.false 1 2 0 1 Bool.false 71064 1000 0 1 (BSN.ascPochhammer_one_eval qz138)

noncomputable def ep792 := ep791 (@Enclosure.Complex.IsNear.of_eq qz138 (Complex.mk qz71 qz147) Bool.false 1 2 0 1 Bool.false 71064 1000 0 1 (BSN.s_crit_mk qz147 Bool.false 71064 1000 qz148) (@Enclosure.Complex.IsNear.mk qz71 qz147 Bool.false 1 2 0 1 Bool.false 71064 1000 0 1 qz329 qz149))

noncomputable def ep793 := @ep790 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz78)) ↑qz134) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep417) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz138 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 71064 1000 0 1 ep792)

noncomputable def ep794 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz78)) ↑qz134)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz138 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 71064 1000 0 1 0 1 0

noncomputable def ep795 := @ep794 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz78)) ↑qz134) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep417) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz138 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 71064 1000 0 1 ep792)

noncomputable def ep796 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz78)) ↑qz134)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz138 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz78)) ↑qz134)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz138 (@ascPochhammer Complex Complex.instSemiring 1)))) 2961 500 0 1 0 1 0 1 2961

noncomputable def ep797 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz78)) ↑qz134)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz138 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 71064 1000 0 1 2961 500 0

noncomputable def ep798 := @ep797 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz78)) ↑qz134) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep417) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz138 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 71064 1000 0 1 ep792)

noncomputable def ep799 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz78)) ↑qz134)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz138 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 1 2 0 1 0 1 0

noncomputable def ep800 := @ep799 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz78)) ↑qz134) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep417) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz138 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 71064 1000 0 1 ep792)

noncomputable def ep801 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz78)) ↑qz134) (@Polynomial.eval Complex Complex.instSemiring qz138 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 24 0 1 Bool.false 2961 500 0 1 (@ep789 1 24 0 1 (ep793 rfl) (ep795 rfl) rfl rfl) (@ep796 2961 500 0 1 (ep798 rfl) (ep800 rfl) rfl rfl)

noncomputable def ep802 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz78)) ↑qz134) (@Polynomial.eval Complex Complex.instSemiring qz138 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 2961 500 0 1 ep801

noncomputable abbrev qz212 := (@Enclosure.Complex.IsNear.of_eq (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz349 qz410 1)) (Complex.mk (Enclosure.sfrac Bool.false 1 15) qz274) Bool.false 1 15 0 1 Bool.false 0 1 0 1 (BSN.natCast_pow_inv_mk 15 1 15 EMRow17.d11 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 15) qz274 Bool.false 1 15 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 15) qz286))

noncomputable def ep803 := @ep788 360 0 1 ep802 (@Enclosure.Complex.IsNear.re_isNear qz211 Bool.false 1 15 0 1 Bool.false 0 1 0 1 qz212)

noncomputable def ep804 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz78)) ↑qz134) (@Polynomial.eval Complex Complex.instSemiring qz138 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz211) 2961 500 0 1 0 1 0 1 0

noncomputable def ep805 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz78)) ↑qz134) (@Polynomial.eval Complex Complex.instSemiring qz138 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 2961 500 0 1 ep801

noncomputable def ep806 := @ep804 1 0 1 ep805 (@Enclosure.Complex.IsNear.im_isNear qz211 Bool.false 1 15 0 1 Bool.false 0 1 0 1 qz212)

noncomputable def ep807 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz78)) ↑qz134) (@Polynomial.eval Complex Complex.instSemiring qz138 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz211)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz78)) ↑qz134) (@Polynomial.eval Complex Complex.instSemiring qz138 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz211)) 0 1 0 1 987 2500 0

noncomputable def ep808 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz78)) ↑qz134) (@Polynomial.eval Complex Complex.instSemiring qz138 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz211) 1 24 0 1 0 1 0 1 0

noncomputable def ep809 := @ep808 1 0 1 ep802 (@Enclosure.Complex.IsNear.im_isNear qz211 Bool.false 1 15 0 1 Bool.false 0 1 0 1 qz212)

noncomputable def ep810 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz78)) ↑qz134) (@Polynomial.eval Complex Complex.instSemiring qz138 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz211) 2961 500 0 1 1 15 0 1 987

noncomputable def ep811 := @ep810 2500 0 1 ep805 (@Enclosure.Complex.IsNear.re_isNear qz211 Bool.false 1 15 0 1 Bool.false 0 1 0 1 qz212)

noncomputable def ep812 := @ep784 1 (@ep785 0 1 0 1 (BSN.bern_sum_base qz138 15) qz92) (ep786 (@ep787 1 1 1 360 0 1 (ep803 rfl) (ep806 rfl) rfl rfl) (@ep807 1 987 987 2500 0 1 (ep809 rfl) (ep811 rfl) rfl rfl)) rfl rfl rfl rfl rfl

noncomputable def ep813 := ep778 (ep781 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep782 Bool.false 987 2500 0 1 (BSN.bern_sum_succ qz138 15 0 1 1 rfl rfl) (ep812 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl rfl

noncomputable def ep814 := @Enclosure.Real.IsNear.mulLit_ff qz204 (Complex.im (@HAdd.hAdd Complex Complex Complex qz5 qz189 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz55 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz55 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz138 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz55 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz103 qz190 (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz55 2 k) 1)))))) 25640214997 137438953472 643973971165 2632918031663104 144986728047

noncomputable def ep815 := @ep814 789115952500 0 1 3717490878836649920859 108455270679660462080000 18673535805329294952951 ep759 (@Enclosure.Complex.IsNear.im_isNear qz188 Bool.true 49066437289 274877906944 1287634629595 5265836063326208 Bool.false 25640214997 137438953472 643973971165 2632918031663104 (ep762 ep774))

noncomputable def ep816 := @Enclosure.Complex.IsNear.im_isNear (@HAdd.hAdd Complex Complex Complex qz5 qz189 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz55 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz55 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz138 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz55 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz103 qz190 (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz55 2 k) 1))))) Bool.false 56963244961 113632697160 0 1 Bool.false

noncomputable def ep817 := @Enclosure.Real.IsNear.addLit_tf_p (@HMul.hMul Real Real Real qz0 qz203 (Complex.im (@HAdd.hAdd Complex Complex Complex qz5 qz189 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz55 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz55 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz138 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz55 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz103 qz190 (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz55 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz204 (Complex.re (@HAdd.hAdd Complex Complex Complex qz5 qz189 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz55 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz55 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz138 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz55 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz103 qz190 (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz55 2 k) 1))))))) 7113982199455422944583 216910541359320924160000 37337986372997968550193

noncomputable def ep818 := nat_lit 831071048164102188826624000

noncomputable def ep819 := nat_lit 59837115467815357595516928

noncomputable def ep820 := nat_lit 205705621585177309205579232794383663067299840

noncomputable def ep821 := @Enclosure.Real.IsNear.mulLit_tf qz203 (Complex.im (@HAdd.hAdd Complex Complex Complex qz5 qz189 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz55 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz55 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz138 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz55 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz103 qz190 (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz55 2 k) 1)))))) 49066437289 274877906944 1287634629595 5265836063326208 144986728047

noncomputable def ep822 := @ep821 789115952500 0 1 7113982199455422944583 216910541359320924160000 37337986372997968550193 ep818 (@Enclosure.Complex.IsNear.re_isNear qz188 Bool.true 49066437289 274877906944 1287634629595 5265836063326208 Bool.false 25640214997 137438953472 643973971165 2632918031663104 (ep762 ep774))

noncomputable def ep823 := @Enclosure.Real.IsNear.mulLit_ff qz204 (Complex.re (@HAdd.hAdd Complex Complex Complex qz5 qz189 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz55 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz55 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz138 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz55 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz103 qz190 (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz55 2 k) 1)))))) 25640214997 137438953472 643973971165 2632918031663104 56963244961

noncomputable def ep824 := @ep823 113632697160 0 1 1460549847726816880117 15617558977871106539520 7336569413595969109913 ep819 (@Enclosure.Complex.IsNear.im_isNear qz188 Bool.true 49066437289 274877906944 1287634629595 5265836063326208 Bool.false 25640214997 137438953472 643973971165 2632918031663104 (ep762 ep774))

noncomputable abbrev qz423 := (ep813 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable def ep825 := @ep756 59271445585376651756689 976097436116944158720000 626556527028238927845431 ep680 (@ep757 ep758 3717490878836649920859 108455270679660462080000 18673535805329294952951 ep759 ep760 483202607470225865992049 ep565 ep683 ep567 (ep775 (@ep776 144986728047 789115952500 0 1 qz423) rfl) (ep815 (@ep816 144986728047 789115952500 0 1 qz423) rfl) rfl rfl) (@ep817 ep818 1460549847726816880117 15617558977871106539520 7336569413595969109913 ep819 ep820 59271445585376651756689 976097436116944158720000 626556527028238927845431 ep680 (ep822 (@ep816 144986728047 789115952500 0 1 qz423) rfl) (ep824 (@ep776 144986728047 789115952500 0 1 qz423) rfl) rfl rfl)

noncomputable def ep826 := @ep686 ep679 ep680 (@ep687 2632918031663104 (BSN.head_sum_c_eq qz138 15) (ep688 (BSN.head_sum_c_succ qz138 14 15 rfl rfl) (ep755 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))) ep825 rfl rfl rfl

noncomputable def ep827 := @Enclosure.Complex.IsNear.re_isNear (zetaApproximant qz138 1 15) Bool.false ep564 ep565 ep566 ep567 Bool.false 37242001935008840599189 976097436116944158720000 ep679 ep680 (@ep681 ep567 Bool.false 37242001935008840599189 976097436116944158720000 ep679 ep680 (BSN.zetaApproximant_eq_folded' qz138 1 15 rfl) (ep826 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

noncomputable def ep828 := @Enclosure.Real.IsNear.mulLit_ff (Real.sin (@HSub.hSub Real Real Real qz47 (Complex.im (@HSub.hSub Complex Complex Complex qz48 qz156 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz157 (@Nat.cast Complex Complex.instNatCast j))))) qz158)) (Complex.im (zetaApproximant qz138 1 15)) 53 262144 533623

noncomputable def ep829 := @Enclosure.Real.IsNear.recentre' (Real.sin (@HSub.hSub Real Real Real qz47 (Complex.im (@HSub.hSub Complex Complex Complex qz48 qz156 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz157 (@Nat.cast Complex Complex.instNatCast j))))) qz158)) Bool.false 106 524288 2134492

noncomputable def ep830 := @Enclosure.Real.IsNear.sin_image (@HSub.hSub Real Real Real qz47 (Complex.im (@HSub.hSub Complex Complex Complex qz48 qz156 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz157 (@Nat.cast Complex Complex.instNatCast j))))) qz158) qz393 Bool.false 823553 16384 27

noncomputable def ep831 := BSN.sin_dyadic_bound_f 218589 1073741824 1 0 524288 153406 0 1 1 0 1 1 106 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 218589) qz283 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 218589) qz284 0 0 rfl) rfl rfl

noncomputable def ep832 := @ep830 65536 Bool.false 106 524288 1 76628 (@ep571 823553 16384 27 65536 ep676 rfl) (Enclosure.sfrac_false_div 823553 16384) (BSN.sin_reduce0 qz393 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 480684299754930176) (@Nat.cast Real Real.instNatCast 2361183241434822606848)) 226375608064910080 72057594037927936 Bool.false 106 524288 8 1000000000000000 153256 76628 (BSN.sin_reduce_arg_pos_rat_q0 823553 16384 226375608064910080 72057594037927936 8 480684299754930176 2361183241434822606848 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 106 524288 480684299754930176 2361183241434822606848 218589 1073741824 153406 153256 (ep831 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep833 := @Enclosure.Complex.IsNear.im_isNear (zetaApproximant qz138 1 15) Bool.false ep564 ep565 ep566 ep567 Bool.false 37242001935008840599189 976097436116944158720000 ep679 ep680 (@ep681 ep567 Bool.false 37242001935008840599189 976097436116944158720000 ep679 ep680 (BSN.zetaApproximant_eq_folded' qz138 1 15 rfl) (ep826 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

theorem EMRow17.d12 : Enclosure.Real.IsNear (hardyZApproximantEM 1 15 qz147) Bool.false ep547 ep548 ep549 ep550 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantEM 1 15 qz147) ep551 Bool.false ep547 ep548 ep549 ep550 (@Eq.refl Real ep551) (@ep552 Bool.false ep547 ep548 ep549 ep550 (BSN.re_exp_mul (@HSub.hSub Real Real Real qz47 (Complex.im (@HSub.hSub Complex Complex Complex qz48 qz156 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz157 (@Nat.cast Complex Complex.instNatCast j))))) qz158) (zetaApproximant qz138 1 15)) (@ep554 ep555 ep556 ep557 ep558 ep559 ep560 ep561 ep562 ep547 ep548 ep549 ep550 (@ep563 1255473152 ep564 ep565 ep566 ep567 ep553 ep555 ep556 ep557 (@ep568 5021892608 524287 524288 533623 1255473152 (ep678 rfl rfl) rfl) ep827 rfl) (@ep828 1255473152 37242001935008840599189 976097436116944158720000 ep679 ep680 ep558 ep559 ep560 ep561 (@ep829 5021892608 53 262144 533623 1255473152 (ep832 rfl rfl) rfl) ep833 rfl) rfl rfl))

theorem EMRow17.d13 : @Eq Nat (Nat.mul (BSN.factNat (Nat.succ (Nat.mul 2 1))) (Nat.pow 4 (Nat.mul 2 1))) 96 := @Eq.refl Nat 96

theorem EMRow17.d14 : @Eq Nat (Nat.mul (Nat.mul 2 1) (Nat.pow (Nat.succ (Nat.mul 4 2)) (Nat.mul 2 1))) 162 := @Eq.refl Nat 162

theorem EMRow17.d15 : @Eq Nat (BSN.factNat (Nat.mul 2 2)) 24 := @Eq.refl Nat 24

theorem EMRow17.d16 : @Eq Nat (Nat.pow 14 (Nat.succ (Nat.mul 2 3))) 105413504 := @Eq.refl Nat 105413504

noncomputable abbrev qz481 := (@HAdd.hAdd Complex Complex Complex qz484 qz483 (@Nat.cast Complex Complex.instNatCast 3))

noncomputable abbrev qz424 := qz481

noncomputable abbrev qz213 := (@HDiv.hDiv Real Real Real qz266 (@Norm.norm Complex Complex.instNorm qz424) (@HAdd.hAdd Real Real Real qz339 (Complex.re qz268) (@Nat.cast Real Real.instNatCast 3)))

noncomputable abbrev qz214 := (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 2)

noncomputable abbrev qz215 := (@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 2)))

noncomputable abbrev qz425 := (@HPow.hPow Complex Complex Complex qz463 (@Nat.cast Complex Complex.instNatCast 14) (@HSub.hSub Complex Complex Complex qz469 qz464 qz465))

noncomputable abbrev qz216 := qz425

noncomputable def ep834 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz6 1 14))) (@HMul.hMul Real Real Real qz0 qz213 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz216))) 473410099 19327352832 8455355 115964116992 13407456628120739 15762598695796736 8782226657

noncomputable def ep835 := nat_lit 266592818240500939423219712

noncomputable def ep836 := @Enclosure.Real.IsNear.mulLit_ff (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz6 1 14)) 4427 294912 1 884736 106937 65536 1241 262144 473410099 19327352832

noncomputable abbrev qz426 := (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid)))

noncomputable abbrev qz217 := (@HPow.hPow Real Nat Real qz426 qz267 2)

noncomputable def ep837 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 96 162) (@Inv.inv Real Real.instInv qz217) 96 162 0 1 13281 524288 1 524288 4427 294912 1 884736

noncomputable def ep838 := nat_lit 781950621441006189802102638025

noncomputable def ep839 := nat_lit 19807040628566084398385987584

noncomputable def ep840 := nat_lit 26986075409044041160201671

noncomputable def ep841 := nat_lit 1073741824000000000000000000000000000000

noncomputable abbrev qz218 := qz267

noncomputable abbrev qz427 := (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) qz218 1)

noncomputable def ep842 := @Enclosure.Real.IsNear.mulLit_ff qz427 qz218 884279719003555 140737488355328 1 500000000000000 884279719003555 140737488355328 1 500000000000000 ep838 ep839 ep840 ep841

noncomputable def ep843 := ep842 (@Enclosure.Real.IsNear.of_eq qz427 qz218 Bool.false 884279719003555 140737488355328 1 500000000000000 (BSN.pow_one_r qz218) (@Enclosure.Real.IsNear.of_eq qz218 qz264 Bool.false 884279719003555 140737488355328 1 500000000000000 BSN.two_pi_eq qz265)) (@Enclosure.Real.IsNear.of_eq qz218 qz264 Bool.false 884279719003555 140737488355328 1 500000000000000 BSN.two_pi_eq qz265) rfl

noncomputable def ep844 := @Enclosure.Real.IsNear.inv_image qz217 ep838 ep839 ep840 ep841 6640 6641 262144 (@Enclosure.Real.IsNear.of_eq qz217 (@HMul.hMul Real Real Real qz0 qz427 qz218) Bool.false ep838 ep839 ep840 ep841 (BSN.pow_succ_r qz218 1 2 rfl) ep843) rfl rfl rfl

noncomputable def ep845 := ep837 (Enclosure.Real.IsNear.const Bool.false 96 162) (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz217) Bool.false 13281 524288 1 524288 13281 524288 1 524288 (ep844 rfl rfl rfl) rfl)

noncomputable def ep846 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (zetaApproximant qz6 1 14)) (Real.sqrt (@HAdd.hAdd Real Real Real qz339 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz6 1 14)) (Complex.re (zetaApproximant qz6 1 14))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz6 1 14)) (Complex.im (zetaApproximant qz6 1 14))))) Bool.false 106937 65536 1241 262144

noncomputable def ep847 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz339 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz6 1 14)) (Complex.re (zetaApproximant qz6 1 14))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz6 1 14)) (Complex.im (zetaApproximant qz6 1 14))))) Bool.false 855496 524288 2482 524288

noncomputable def ep848 := nat_lit 46195209954784572901420988141218649188993

noncomputable def ep849 := nat_lit 17349884218097502836028015351169024000000

noncomputable def ep850 := nat_lit 1036878482091445856163429073391204549732273481803137500973

noncomputable def ep851 := nat_lit 67135917418817458968785009179233070928659884420366336000000

noncomputable def ep852 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz339 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz6 1 14)) (Complex.re (zetaApproximant qz6 1 14))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz6 1 14)) (Complex.im (zetaApproximant qz6 1 14)))) ep848 ep849 ep850 ep851 426507 428989

noncomputable def ep853 := nat_lit 13525300413124585457468932136540275995371231358409

noncomputable def ep854 := nat_lit 5081564339714692943094050907368628812775424000000

noncomputable def ep855 := nat_lit 1016563098979582908812594001895608200591598504235651680349

noncomputable def ep856 := nat_lit 18797909690613241536644251892260571220650197161

noncomputable def ep857 := nat_lit 20326257358858771772376203629474515251101696000000

noncomputable def ep858 := nat_lit 141079049387937134380799107608307980143576233107540421

noncomputable def ep859 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz6 1 14)) (Complex.re (zetaApproximant qz6 1 14))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz6 1 14)) (Complex.im (zetaApproximant qz6 1 14))) ep853 ep854 ep855 ep851 ep856 ep857 ep858

noncomputable def ep860 := nat_lit 466221648741787909505451452633562992560138086252544000000

noncomputable def ep861 := nat_lit 275014259840594188637911882861657775127514007475836465022792393509829054868353017001099132928000000

noncomputable def ep862 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (zetaApproximant qz6 1 14)) (Complex.re (zetaApproximant qz6 1 14)) ep168 ep169 ep170 ep171 ep168 ep169 ep170 ep171 ep853

noncomputable def ep863 := @Enclosure.Real.IsNear.mulLit_tt (Complex.im (zetaApproximant qz6 1 14)) (Complex.im (zetaApproximant qz6 1 14)) 137105469222103760453619 ep298 ep299 ep300 137105469222103760453619 ep298 ep299 ep300 ep856

noncomputable def ep864 := @ep834 15762598695796736 ep835 124141954928869819 141863388262170624 31268408255419 425590164786511872 (@ep836 8455355 115964116992 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaStirlingErrorBound 1 2) (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 96 162) (@Inv.inv Real Real.instInv qz217)) Bool.false 4427 294912 1 884736 (BSN.theta_err_eq 1 2 96 162 EMRow17.d13 EMRow17.d14 rfl) (ep845 rfl)) (ep846 (BSN.norm_eq_sqrt_mul_add (zetaApproximant qz6 1 14)) (@ep847 106937 65536 1241 262144 (@ep852 262144 (@ep859 ep860 ep861 ep848 ep849 ep850 ep851 (@ep862 ep854 ep855 ep851 ep455 ep455 rfl) (@ep863 ep857 ep858 ep860 ep461 ep461 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl)

noncomputable abbrev qz219 := (@Norm.norm Complex Complex.instNorm qz424)

noncomputable abbrev qz428 := (Enclosure.sfrac Bool.false 2 7)

noncomputable def ep865 := @Enclosure.Real.IsNear.of_eq (@HMul.hMul Real Real Real qz0 qz213 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz216))) (@HMul.hMul Real Real Real qz0 (@HMul.hMul Real Real Real qz0 qz219 qz428) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz216))) Bool.false 13407456628120739 15762598695796736 8782226657 15762598695796736 (BSN.zrb_shape_eq qz219 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz216)) qz17 3)

noncomputable def ep866 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz0 qz219 qz428) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz216)) 35936491 1835008 1 1835008 373087529 8589934592 117 4294967296

noncomputable def ep867 := @Enclosure.Real.IsNear.mulLit_ff qz219 qz428 35936491 524288 1 524288 2 7 0 1 35936491 1835008

noncomputable abbrev qz429 := (Complex.re qz481)

noncomputable abbrev qz430 := (Complex.im qz481)

noncomputable abbrev qz220 := (@HAdd.hAdd Real Real Real qz339 (@HMul.hMul Real Real Real qz263 qz429 qz429) (@HMul.hMul Real Real Real qz263 qz430 qz430))

noncomputable abbrev qz221 := qz424

noncomputable def ep868 := @Enclosure.Real.IsNear.of_eq qz219 (Real.sqrt qz220) Bool.false 35936491 524288 1 524288 (BSN.norm_eq_sqrt_mul_add qz221)

noncomputable def ep869 := @Enclosure.Real.IsNear.recentre' (Real.sqrt qz220) Bool.false 35936491 524288 1 524288 35936491

noncomputable def ep870 := @Enclosure.Real.IsNear.sqrt_image qz220 1174550029 250000 0 1 17968245 17968246 262144

noncomputable abbrev qz222 := (@HMul.hMul Real Real Real qz263 qz429 qz429)

noncomputable abbrev qz223 := (@HMul.hMul Real Real Real qz263 qz430 qz430)

noncomputable def ep871 := @Enclosure.Real.IsNear.addLit_ff qz222 qz223 49 4 0 1 1171487529 250000 0 1

noncomputable abbrev qz224 := qz429

noncomputable def ep872 := @Enclosure.Real.IsNear.mulLit_ff qz224 qz224 7 2 0 1 7 2 0 1 49 4

noncomputable abbrev qz431 := (Enclosure.sfrac Bool.false 7 2)

noncomputable def ep873 := @Enclosure.Complex.IsNear.of_eq qz221 (Complex.mk qz431 qz17) Bool.false 7 2 0 1 Bool.false 68454 1000 0 1 (BSN.s_add_nat_mk qz17 Bool.false 68454 1000 3 qz18)

noncomputable abbrev qz432 := (ep873 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7 2) qz17 Bool.false 7 2 0 1 Bool.false 68454 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 7 2) qz22))

noncomputable def ep874 := @ep872 0 1 (@Enclosure.Complex.IsNear.re_isNear qz221 Bool.false 7 2 0 1 Bool.false 68454 1000 0 1 qz432)

noncomputable def ep875 := ep874 (@Enclosure.Complex.IsNear.re_isNear qz221 Bool.false 7 2 0 1 Bool.false 68454 1000 0 1 qz432)

noncomputable abbrev qz225 := qz430

noncomputable def ep876 := @Enclosure.Real.IsNear.mulLit_ff qz225 qz225 68454 1000 0 1 68454 1000 0 1 1171487529 250000

noncomputable def ep877 := @ep876 0 1 (@Enclosure.Complex.IsNear.im_isNear qz221 Bool.false 7 2 0 1 Bool.false 68454 1000 0 1 qz432)

noncomputable def ep878 := ep877 (@Enclosure.Complex.IsNear.im_isNear qz221 Bool.false 7 2 0 1 Bool.false 68454 1000 0 1 qz432)

noncomputable def ep879 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz216)) (Real.sqrt (@HAdd.hAdd Real Real Real qz339 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz216)) (Complex.re (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz216))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz216)) (Complex.im (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz216))))) Bool.false 373087529 8589934592

noncomputable def ep880 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz339 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz216)) (Complex.re (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz216))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz216)) (Complex.im (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz216))))) Bool.false 746175058 17179869184

noncomputable def ep881 := nat_lit 14789846603705439999505876725843680882065923758196648527221

noncomputable def ep882 := nat_lit 7840105733858422198196150955227939591946240000000000000000000

noncomputable def ep883 := nat_lit 13051485343113231933568157591628546175150118977227333545798557581289

noncomputable def ep884 := nat_lit 5528915895543087599259953267899991102807014345143138385920000000000000000000

noncomputable def ep885 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz339 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz216)) (Complex.re (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz216))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz216)) (Complex.im (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz216)))) ep881 ep882 ep883 ep884

noncomputable def ep886 := nat_lit 146996551443327439971355224397942205292190902604062653343241

noncomputable def ep887 := nat_lit 78401057338584221981961509552279395919462400000000000000000000

noncomputable def ep888 := nat_lit 25868874464117434215105992495003998450401692515572231205833406303937

noncomputable def ep889 := nat_lit 11057831791086175198519906535799982205614028690286276771840000000000000000000

noncomputable def ep890 := nat_lit 100212732636328891522615873388289280940926108655981325441

noncomputable def ep891 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz216)) (Complex.re (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz216))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz216)) (Complex.im (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz216))) ep886 ep887 ep888 ep889 ep890

noncomputable def ep892 := nat_lit 8711228593176024664662389950253266213273600000000000000000000

noncomputable def ep893 := nat_lit 78032074036343217343440896084364633299515146294145295254569619547

noncomputable def ep894 := nat_lit 3685943930362058399506635511933327401871342896762092257280000000000000000000

noncomputable def ep895 := nat_lit 1288377346228861464621669361926697617251307782932346837632367756270510287027759214509738931211206656000000000000000000000

noncomputable def ep896 := nat_lit 383401292959905705077718232829

noncomputable def ep897 := nat_lit 8854437155380584775680000000000

noncomputable def ep898 := nat_lit 11001842636550642916737253433539

noncomputable def ep899 := nat_lit 407268310658087695977031925760000000000

noncomputable def ep900 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz216)) (Complex.re (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz216)) ep896 ep897 ep898 ep899 ep896 ep897 ep898

noncomputable def ep901 := nat_lit 10010630980928669289623212479

noncomputable def ep902 := nat_lit 2951479051793528258560000000000

noncomputable def ep903 := nat_lit 84734806715602741242946891417

noncomputable def ep904 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz216) Bool.true ep896 ep897 ep898 ep899 Bool.false ep901 ep902 ep903

noncomputable def ep905 := nat_lit 27151220710539179731802128384000000000

noncomputable def ep906 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz216 Bool.true ep896 ep897 ep898 ep899 Bool.false ep901 ep902 ep903 ep905

noncomputable def ep907 := nat_lit 1257966951045744418871329

noncomputable def ep908 := nat_lit 35417748621522339102720000000

noncomputable def ep909 := nat_lit 4131842076532345109238881

noncomputable def ep910 := nat_lit 46544949789495736683089362944000000

noncomputable def ep911 := nat_lit 127905261565889047060812021693

noncomputable def ep912 := nat_lit 3655229672793661632343804408263

noncomputable abbrev qz226 := (Complex.re qz425)

noncomputable abbrev qz227 := (Complex.im qz425)

noncomputable def ep913 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)))) qz226) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)))) qz227) ep907 ep908 ep909 ep910 ep911 ep902 ep912

noncomputable def ep914 := nat_lit 135756103552695898659010641920000000000

noncomputable def ep915 := nat_lit 4526403538406860927217584212510658656136627969064960000000

noncomputable def ep916 := nat_lit 13575610355269589865901064192

noncomputable def ep917 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)))) qz226 3514150087 120000000 0 1 357971890756567 295147905179352825856 41152047891639205 ep916 ep907

noncomputable def ep918 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)))) 3514150087 120000000 0 1 0 1 0 1 3514150087

noncomputable def ep919 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 10542450261 500000 0 1 3514150087 120000000 0

noncomputable def ep920 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (Complex.mk (Enclosure.sfrac Bool.true 1 720) qz14) Bool.true 1 720 0 1 Bool.false 0 1 0 1 (BSN.bern_coeff_mk 2 1 30 24 Bool.true BSN.bern_real_2 EMRow17.d15 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 1 720) qz14 Bool.true 1 720 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.true 1 720) qz24)

noncomputable abbrev qz433 := (@HAdd.hAdd Complex Complex Complex qz462 qz461 qz466)

noncomputable abbrev qz228 := qz433

noncomputable def ep921 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)) (@HMul.hMul Complex Complex Complex qz46 (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 2)) qz228) Bool.true 10542450261 500000 0 1 Bool.true 40047302342583 125000000 0 1

noncomputable abbrev qz229 := (Complex.re qz433)

noncomputable abbrev qz230 := (Complex.im qz433)

noncomputable def ep922 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 2))) qz229) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 2))) qz230) 1171300029 100000 0 1 1171487529 125000 0 1

noncomputable def ep923 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 2))) qz229 1171300029 250000 0 1 5 2 0 1 1171300029 100000

noncomputable abbrev qz434 := (@HAdd.hAdd Complex Complex Complex qz462 qz461 (@Nat.cast Complex Complex.instNatCast 1))

noncomputable abbrev qz231 := qz434

noncomputable def ep924 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 2)) (@HMul.hMul Complex Complex Complex qz46 (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)) qz231) Bool.true 1171300029 250000 0 1 Bool.false 34227 250 0 1

noncomputable abbrev qz232 := (Complex.re qz434)

noncomputable abbrev qz233 := (Complex.im qz434)

noncomputable def ep925 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1))) qz232) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1))) qz233) 3 4 0 1 1171487529 250000 0 1

noncomputable def ep926 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1))) qz232 1 2 0 1 3 2 0 1 3 4

noncomputable def ep927 := @ep926 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 68454 1000 0 1 ep419)

noncomputable abbrev qz435 := (Enclosure.sfrac Bool.false 3 2)

noncomputable def ep928 := @Enclosure.Complex.IsNear.of_eq qz231 (Complex.mk qz435 qz17) Bool.false 3 2 0 1 Bool.false 68454 1000 0 1 (BSN.s_add_nat_mk qz17 Bool.false 68454 1000 1 qz18)

noncomputable abbrev qz436 := (ep928 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 3 2) qz17 Bool.false 3 2 0 1 Bool.false 68454 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 3 2) qz22))

noncomputable def ep929 := ep927 (@Enclosure.Complex.IsNear.re_isNear qz231 Bool.false 3 2 0 1 Bool.false 68454 1000 0 1 qz436)

noncomputable def ep930 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1))) qz233 68454 1000 0 1 68454 1000 0 1 1171487529 250000

noncomputable def ep931 := @ep930 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 68454 1000 0 1 ep419)

noncomputable def ep932 := ep931 (@Enclosure.Complex.IsNear.im_isNear qz231 Bool.false 3 2 0 1 Bool.false 68454 1000 0 1 qz436)

noncomputable def ep933 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)) qz231 Bool.true 1171300029 250000 0 1 Bool.false 34227 250 0 1 (@ep925 4685200116 1171300029 250000 0 1 (ep929 rfl) (ep932 rfl) rfl rfl)

noncomputable def ep934 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1))) qz233) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1))) qz232) 34227 1000 0 1 102681 1000 0 1

noncomputable def ep935 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1))) qz233 1 2 0 1 68454 1000 0 1 34227 1000

noncomputable def ep936 := @ep935 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 68454 1000 0 1 ep419)

noncomputable def ep937 := ep936 (@Enclosure.Complex.IsNear.im_isNear qz231 Bool.false 3 2 0 1 Bool.false 68454 1000 0 1 qz436)

noncomputable def ep938 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1))) qz232 68454 1000 0 1 3 2 0 1 102681 1000

noncomputable def ep939 := @ep938 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 68454 1000 0 1 ep419)

noncomputable def ep940 := ep939 (@Enclosure.Complex.IsNear.re_isNear qz231 Bool.false 3 2 0 1 Bool.false 68454 1000 0 1 qz436)

noncomputable abbrev qz234 := (ep924 (BSN.ascPochhammer_succ_eval_c 1 2 qz268 rfl) (ep933 (@ep934 136908000 34227 250 0 1 (ep937 rfl) (ep940 rfl) rfl rfl)))

noncomputable def ep941 := @ep923 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 1171300029 250000 0 1 Bool.false 34227 250 0 1 qz234)

noncomputable abbrev qz437 := (Enclosure.sfrac Bool.false 5 2)

noncomputable def ep942 := @Enclosure.Complex.IsNear.of_eq qz228 (Complex.mk qz437 qz17) Bool.false 5 2 0 1 Bool.false 68454 1000 0 1 (BSN.s_add_nat_mk qz17 Bool.false 68454 1000 2 qz18)

noncomputable abbrev qz438 := (ep942 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 5 2) qz17 Bool.false 5 2 0 1 Bool.false 68454 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 5 2) qz22))

noncomputable def ep943 := ep941 (@Enclosure.Complex.IsNear.re_isNear qz228 Bool.false 5 2 0 1 Bool.false 68454 1000 0 1 qz438)

noncomputable def ep944 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 2))) qz230 34227 250 0 1 68454 1000 0 1 1171487529 125000

noncomputable def ep945 := @ep944 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 1171300029 250000 0 1 Bool.false 34227 250 0 1 qz234)

noncomputable def ep946 := ep945 (@Enclosure.Complex.IsNear.im_isNear qz228 Bool.false 5 2 0 1 Bool.false 68454 1000 0 1 qz438)

noncomputable def ep947 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 2)) qz228 Bool.true 10542450261 500000 0 1 Bool.true 40047302342583 125000000 0 1 (@ep922 263561256525000 10542450261 500000 0 1 (ep943 rfl) (ep946 rfl) rfl rfl)

noncomputable def ep948 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 2))) qz230) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 2))) qz229) 40090086092583 125000000 0 1 34227 100 0 1

noncomputable def ep949 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 2))) qz230 1171300029 250000 0 1 68454 1000 0 1 40090086092583 125000000

noncomputable def ep950 := @ep949 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 1171300029 250000 0 1 Bool.false 34227 250 0 1 qz234)

noncomputable def ep951 := ep950 (@Enclosure.Complex.IsNear.im_isNear qz228 Bool.false 5 2 0 1 Bool.false 68454 1000 0 1 qz438)

noncomputable def ep952 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 2))) qz229 34227 250 0 1 5 2 0 1 34227 100

noncomputable def ep953 := @ep952 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 1171300029 250000 0 1 Bool.false 34227 250 0 1 qz234)

noncomputable def ep954 := ep953 (@Enclosure.Complex.IsNear.re_isNear qz228 Bool.false 5 2 0 1 Bool.false 68454 1000 0 1 qz438)

noncomputable abbrev qz235 := (ep921 (BSN.ascPochhammer_succ_eval_c 2 3 qz268 rfl) (ep947 (@ep948 4004730234258300 40047302342583 125000000 0 1 (ep951 rfl) (ep954 rfl) rfl rfl)))

noncomputable def ep955 := @ep919 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep920) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 10542450261 500000 0 1 Bool.true 40047302342583 125000000 0 1 qz235)

noncomputable def ep956 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 40047302342583 125000000 0 1 0 1 0

noncomputable def ep957 := @ep956 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep920) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 10542450261 500000 0 1 Bool.true 40047302342583 125000000 0 1 qz235)

noncomputable def ep958 := @Enclosure.Real.IsNear.addLit_ft_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)))) 4449700260287 10000000000 0 1 0 1 0 1 4449700260287

noncomputable def ep959 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 40047302342583 125000000 0 1 4449700260287 10000000000 0

noncomputable def ep960 := @ep959 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep920) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 10542450261 500000 0 1 Bool.true 40047302342583 125000000 0 1 qz235)

noncomputable def ep961 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 10542450261 500000 0 1 0 1 0

noncomputable def ep962 := @ep961 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep920) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 10542450261 500000 0 1 Bool.true 40047302342583 125000000 0 1 qz235)

noncomputable def ep963 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.false 3514150087 120000000 0 1 Bool.false 4449700260287 10000000000 0 1 (@ep918 3514150087 120000000 0 1 (ep955 rfl) (ep957 rfl) rfl rfl) (@ep958 4449700260287 10000000000 0 1 (ep960 rfl) (ep962 rfl) rfl rfl)

noncomputable def ep964 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 3514150087 120000000 0 1 Bool.false 4449700260287 10000000000 0 1 ep963

noncomputable def ep965 := @Enclosure.Complex.IsNear.re_isNear qz216 Bool.false 357971890756567 295147905179352825856 41152047891639205 ep916 Bool.false 28744691571121539 295147905179352825856 821455257428486649 ep916

noncomputable abbrev qz439 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 105413504)))

noncomputable def ep966 := @Enclosure.Complex.IsNear.of_eq qz216 (Complex.mk (@HMul.hMul Real Real Real qz0 qz439 qz128) (@HMul.hMul Real Real Real qz0 qz439 qz129)) Bool.false 357971890756567 295147905179352825856 41152047891639205 ep916 Bool.false 28744691571121539 295147905179352825856 821455257428486649

noncomputable abbrev qz440 := (Real.sqrt (@Nat.cast Real Real.instNatCast 105413504))

noncomputable abbrev qz441 := (@Nat.cast Real Real.instNatCast 105413504)

noncomputable def ep967 := @Enclosure.Real.IsNear.inv_image qz440 176387570092723 17179869184 1 17179869184 836645 836646 8589934592 (@Enclosure.Real.IsNear.of_eq qz440 (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz441 qz19)) Bool.false 176387570092723 17179869184 1 17179869184 (BSN.sqrt_natCast_div_one 105413504) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz441 qz19)) Bool.false 176387570092723 17179869184 1 17179869184 176387570092723 17179869184 1 17179869184 (BSN.sqrt_enclosure 105413504 1 88193785046361 88193785046362 8589934592 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep968 := nat_lit 22997978500000000000000000

noncomputable def ep969 := nat_lit 816748683538471975894646784

noncomputable def ep970 := nat_lit 309485009821345068724781056

noncomputable def ep971 := nat_lit 2943741248000000000000000

noncomputable def ep972 := nat_lit 103769785630983789875522764800

noncomputable def ep973 := nat_lit 2694100009858475599347056640

noncomputable def ep974 := BSN.log_dyadic_bound 6 22 9 8 ep972 8589934592 2943741248 ep973 5718460310160998400 4807063014 28 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.artanhP 6) (BSN.artanhQ 22) 0 8 ep973 ep972 5718460310160998400 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep975 := @Enclosure.Real.IsNear.mulLit_ff qz17 qz130 68454 1000 0 1 11885257605732069 4503599627370496 15625137987871 45995957000000000000000 406796712071391525663 2251799813685248000 534801597910860717 ep968 qz22 (BSN.isNear_log_sfrac 14 1 11885257605732069 4503599627370496 15625137987871 45995957000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' qz374 Bool.false ep969 ep970 1000008831223744 ep971 11885257605732069 4503599627370496 15625137987871 45995957000000000000000 (BSN.log_rat_reduce_isNear 14 1 3 28 16 4807063014 8589934592 24973259072661432 36028797018963968 2943741248 1000000000000000 rfl rfl rfl rfl (ep974 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep976 := nat_lit 30831767987588589477167104

noncomputable def ep977 := nat_lit 2475880078570760549798248448

noncomputable def ep978 := BSN.sin_dyadic_bound_f 438145775484 35184372088832 1 0 17179869184 5893231991 0 1 1 0 1 1 213932837 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 438145775484) (BSN.sinEvenQ 35184372088832) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 438145775484) (BSN.sinOddQ 35184372088832) 0 0 rfl) rfl rfl

noncomputable abbrev qz442 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 3103612610407) (@Nat.cast Real Real.instNatCast 17179869184))

noncomputable def ep979 := @Enclosure.Real.IsNear.cos_image qz131 qz442 Bool.false 3103612610407 17179869184 401 17179869184 Bool.false 213932837 17179869184 1 2943741248 (@Enclosure.Real.IsNear.recentre' qz131 Bool.false 406796712071391525663 2251799813685248000 534801597910860717 ep968 3103612610407 17179869184 401 17179869184 (ep975 rfl) rfl) (Enclosure.sfrac_false_div 3103612610407 17179869184) (BSN.cos_reduce3 qz442 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast ep976) (@Nat.cast Real Real.instNatCast ep977)) 226375608064910080 72057594037927936 Bool.false 213932837 17179869184 28 1000000000000000 5887482496 2943741248 (BSN.sin_reduce_arg_pos_rat_q3 3103612610407 17179869184 226375608064910080 72057594037927936 28 ep976 ep977 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 213932837 17179869184 ep976 ep977 438145775484 35184372088832 5893231991 5887482496 (ep978 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep980 := nat_lit 36853141500324590389180513083369294744898273536

noncomputable def ep981 := nat_lit 36779892980781332600600328651607420406849738932406452224

noncomputable def ep982 := nat_lit 551698394711719989009004929774111306102746083986096783360

noncomputable def ep983 := BSN.cos_dyadic_bound_f 438145775484 35184372088832 2 1 17179869184 5893231991 ep980 ep981 ep980 ep980 ep982 ep980 17178537129 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 438145775484) (BSN.cosEvenQ 35184372088832) 0 1 ep980 ep981 ep980 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 438145775484) (BSN.cosOddQ 35184372088832) 0 1 ep980 ep982 ep980 rfl rfl rfl rfl) rfl rfl

noncomputable def ep984 := @Enclosure.Real.IsNear.sin_image qz131 qz442 Bool.false 3103612610407 17179869184 401 17179869184 Bool.true 17178537129 17179869184 1 2943741248 (@Enclosure.Real.IsNear.recentre' qz131 Bool.false 406796712071391525663 2251799813685248000 534801597910860717 ep968 3103612610407 17179869184 401 17179869184 (ep975 rfl) rfl) (Enclosure.sfrac_false_div 3103612610407 17179869184) (BSN.sin_reduce3 qz442 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast ep976) (@Nat.cast Real Real.instNatCast ep977)) 226375608064910080 72057594037927936 Bool.false 17178537129 17179869184 28 1000000000000000 5887482496 2943741248 (BSN.sin_reduce_arg_pos_rat_q3 3103612610407 17179869184 226375608064910080 72057594037927936 28 ep976 ep977 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 17178537129 17179869184 ep976 ep977 438145775484 35184372088832 5893231991 5887482496 (ep983 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep985 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz439 qz128) (@HMul.hMul Real Real Real qz0 qz439 qz129) Bool.false 357971890756567 295147905179352825856 41152047891639205 ep916 Bool.false 28744691571121539 295147905179352825856 821455257428486649 ep916 (@Enclosure.Real.IsNear.mulLit_ff qz439 qz128 1673291 17179869184 1 17179869184 213932837 17179869184 18712814213 790204524252889088 357971890756567 295147905179352825856 41152047891639205 ep916 (@Enclosure.Real.IsNear.recentre' qz439 Bool.false 1673291 17179869184 1 17179869184 1673291 17179869184 1 17179869184 (ep967 rfl rfl) rfl) (@Enclosure.Real.IsNear.recentre' qz128 Bool.false 213932837 17179869184 1197620109632 50573089552184901632 213932837 17179869184 18712814213 790204524252889088 (ep979 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz439 qz129 1673291 17179869184 1 17179869184 17178537129 17179869184 18712814213 790204524252889088 28744691571121539 295147905179352825856 821455257428486649 ep916 (@Enclosure.Real.IsNear.recentre' qz439 Bool.false 1673291 17179869184 1 17179869184 1673291 17179869184 1 17179869184 (ep967 rfl rfl) rfl) (@Enclosure.Real.IsNear.neg qz132 Bool.true 17178537129 17179869184 18712814213 790204524252889088 (@Enclosure.Real.IsNear.recentre' qz132 Bool.true 17178537129 17179869184 1197620109632 50573089552184901632 17178537129 17179869184 18712814213 790204524252889088 (ep984 rfl rfl) rfl)) rfl)

noncomputable def ep986 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)))) qz227 4449700260287 10000000000 0 1 28744691571121539 295147905179352825856 821455257428486649 ep916 ep911

noncomputable def ep987 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 3514150087 120000000 0 1 Bool.false 4449700260287 10000000000 0 1 ep963

noncomputable def ep988 := @Enclosure.Complex.IsNear.im_isNear qz216 Bool.false 357971890756567 295147905179352825856 41152047891639205 ep916 Bool.false 28744691571121539 295147905179352825856 821455257428486649 ep916

noncomputable def ep989 := nat_lit 33671053461814974321474631

noncomputable def ep990 := nat_lit 11805916207174113034240000000

noncomputable def ep991 := nat_lit 137462717350424940660080403

noncomputable def ep992 := nat_lit 77574916315826227805148938240000000

noncomputable def ep993 := nat_lit 1592867615474925709254554729

noncomputable def ep994 := nat_lit 36622855642954012011918750367

noncomputable def ep995 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)))) qz227) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)))) qz226) ep989 ep990 ep991 ep992 ep993 ep902 ep994

noncomputable def ep996 := nat_lit 118184670541785066012052299312252550024054922280960000000

noncomputable def ep997 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)))) qz227 3514150087 120000000 0 1 28744691571121539 295147905179352825856 821455257428486649 ep916 ep989

noncomputable def ep998 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)))) qz226 4449700260287 10000000000 0 1 357971890756567 295147905179352825856 41152047891639205 ep916 ep993

noncomputable abbrev qz443 := (@ep966 ep916 (BSN.cpow_neg_s_sub_mk qz17 68454 1000 14 3 105413504 qz18 rfl EMRow17.d16) ep985)

noncomputable def ep999 := ep906 (@ep913 ep914 ep915 ep896 ep897 ep898 ep899 (@ep917 ep908 ep909 ep910 ep964 (ep965 qz443) rfl) (@ep986 ep902 ep912 ep914 ep987 (ep988 qz443) rfl) rfl rfl) (@ep995 ep905 ep996 ep901 ep902 ep903 ep905 (@ep997 ep990 ep991 ep992 ep964 (ep988 qz443) rfl) (@ep998 ep902 ep994 ep905 ep987 (ep965 qz443) rfl) rfl rfl)

noncomputable def ep1000 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz216)) (Complex.im (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz216)) ep901 ep902 ep903 ep905 ep901 ep902 ep903

noncomputable def ep1001 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz216) Bool.true ep896 ep897 ep898 ep899 Bool.false ep901 ep902 ep903

noncomputable def ep1002 := @ep866 13407456628120739 15762598695796736 8782226657 15762598695796736 (@ep867 1 1835008 (ep868 (@ep869 524288 1 524288 (ep870 (@ep871 4698200116 1174550029 250000 0 1 (ep875 rfl) (ep878 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) (Enclosure.Real.IsNear.const Bool.false 2 7) rfl) (@ep879 117 4294967296 (BSN.norm_eq_sqrt_mul_add (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz216)) (@ep880 468 17179869184 373087529 8589934592 117 4294967296 (@ep885 373087295 373087763 8589934592 (@ep891 ep892 ep893 ep894 ep895 ep881 ep882 ep883 ep884 (@ep900 ep899 ep886 ep887 ep888 ep889 (@ep904 ep905 ep999) (@ep904 ep905 ep999) rfl) (@ep1000 ep905 ep890 ep892 ep893 ep894 (@ep1001 ep905 ep999) (@ep1001 ep905 ep999) rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl

theorem EMRow17.d17 : Enclosure.Real.IsNear (@HAdd.hAdd Real Real Real qz339 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz6 1 14))) (@HMul.hMul Real Real Real qz0 qz213 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz216)))) Bool.false 124141954928869819 141863388262170624 31268408255419 425590164786511872 := ep864 (ep865 ep1002) rfl rfl

theorem EMRow17.d18 : @Eq Nat (Nat.pow 15 (Nat.succ (Nat.mul 2 3))) 170859375 := @Eq.refl Nat 170859375

noncomputable abbrev qz482 := (@HAdd.hAdd Complex Complex Complex qz484 qz490 (@Nat.cast Complex Complex.instNatCast 3))

noncomputable abbrev qz444 := qz482

noncomputable abbrev qz236 := (@HDiv.hDiv Real Real Real qz266 (@Norm.norm Complex Complex.instNorm qz444) (@HAdd.hAdd Real Real Real qz339 (Complex.re qz378) (@Nat.cast Real Real.instNatCast 3)))

noncomputable abbrev qz445 := (@HPow.hPow Complex Complex Complex qz463 (@Nat.cast Complex Complex.instNatCast 15) (@HSub.hSub Complex Complex Complex qz469 qz477 qz465))

noncomputable abbrev qz237 := qz445

noncomputable def ep1003 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz138 1 15))) (@HMul.hMul Real Real Real qz0 qz236 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz138 (@ascPochhammer Complex Complex.instSemiring 3))) qz237))) 586865255 19327352832 9237121 115964116992 12229488392867923 15762598695796736 10548907457

noncomputable def ep1004 := nat_lit 245614158626878399096815616

noncomputable def ep1005 := @Enclosure.Real.IsNear.mulLit_ff (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz138 1 15)) 4427 294912 1 884736 132565 65536 1351 262144 586865255 19327352832

noncomputable def ep1006 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (zetaApproximant qz138 1 15)) (Real.sqrt (@HAdd.hAdd Real Real Real qz339 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz138 1 15)) (Complex.re (zetaApproximant qz138 1 15))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz138 1 15)) (Complex.im (zetaApproximant qz138 1 15))))) Bool.false 132565 65536 1351 262144

noncomputable def ep1007 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz339 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz138 1 15)) (Complex.re (zetaApproximant qz138 1 15))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz138 1 15)) (Complex.im (zetaApproximant qz138 1 15))))) Bool.false 1060520 524288 2702 524288

noncomputable def ep1008 := nat_lit 197609020258195607666012356622849420442677

noncomputable def ep1009 := nat_lit 48295371638381465009210494707302400000000

noncomputable def ep1010 := nat_lit 4663929795568668190974239300954250273489497697511117331

noncomputable def ep1011 := nat_lit 223780024219291745079334288286676118647937720909824000000

noncomputable def ep1012 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz339 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz138 1 15)) (Complex.re (zetaApproximant qz138 1 15))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz138 1 15)) (Complex.im (zetaApproximant qz138 1 15)))) ep1008 ep1009 ep1010 ep1011 528909 531611

noncomputable def ep1013 := nat_lit 62352380630125093914233469762515519486349653678401

noncomputable def ep1014 := nat_lit 15244259276705150127635424321579656832614400000000

noncomputable def ep1015 := nat_lit 846692462149738728078698918289096786845103228596097917

noncomputable def ep1016 := nat_lit 41440745225794767607284127460495577527395874242560000000

noncomputable def ep1017 := nat_lit 1386966708127202227449206673017624020547457721

noncomputable def ep1018 := nat_lit 952766204794071882977214020098728552038400000000

noncomputable def ep1019 := nat_lit 28684531237524706046645356935352382664356332216308931

noncomputable def ep1020 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz138 1 15)) (Complex.re (zetaApproximant qz138 1 15))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz138 1 15)) (Complex.im (zetaApproximant qz138 1 15))) ep1013 ep1014 ep1015 ep1016 ep1017 ep1018 ep1019

noncomputable def ep1021 := nat_lit 69931257568528670337291965089586287077480537784320000000

noncomputable def ep1022 := nat_lit 59428384332946535375778106725179843098617454543774172898611010759993171706553264264498380800000000

noncomputable def ep1023 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (zetaApproximant qz138 1 15)) (Complex.re (zetaApproximant qz138 1 15)) ep564 ep565 ep566 ep567 ep564 ep565 ep566 ep567 ep1013

noncomputable def ep1024 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (zetaApproximant qz138 1 15)) (Complex.im (zetaApproximant qz138 1 15)) 37242001935008840599189 976097436116944158720000 ep679 ep680 37242001935008840599189 976097436116944158720000 ep679 ep680 ep1017

noncomputable def ep1025 := @ep1003 15762598695796736 ep1004 114373005287199467 141863388262170624 34185202365275 425590164786511872 (@ep1005 9237121 115964116992 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaStirlingErrorBound 1 2) (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 96 162) (@Inv.inv Real Real.instInv qz217)) Bool.false 4427 294912 1 884736 (BSN.theta_err_eq 1 2 96 162 EMRow17.d13 EMRow17.d14 rfl) (ep845 rfl)) (ep1006 (BSN.norm_eq_sqrt_mul_add (zetaApproximant qz138 1 15)) (@ep1007 132565 65536 1351 262144 (@ep1012 262144 (@ep1020 ep1021 ep1022 ep1008 ep1009 ep1010 ep1011 (@ep1023 ep1014 ep1015 ep1016 ep827 ep827 rfl) (@ep1024 ep1018 ep1019 ep1021 ep833 ep833 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl)

noncomputable abbrev qz238 := (@Norm.norm Complex Complex.instNorm qz444)

noncomputable def ep1026 := @Enclosure.Real.IsNear.of_eq (@HMul.hMul Real Real Real qz0 qz236 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz138 (@ascPochhammer Complex Complex.instSemiring 3))) qz237))) (@HMul.hMul Real Real Real qz0 (@HMul.hMul Real Real Real qz0 qz238 qz428) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz138 (@ascPochhammer Complex Complex.instSemiring 3))) qz237))) Bool.false 12229488392867923 15762598695796736 10548907457 15762598695796736 (BSN.zrb_shape_eq qz238 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz138 (@ascPochhammer Complex Complex.instSemiring 3))) qz237)) qz147 3)

noncomputable def ep1027 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz0 qz238 qz428) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz138 (@ascPochhammer Complex Complex.instSemiring 3))) qz237)) 37303163 1835008 1 1835008 327840521 8589934592 137 4294967296

noncomputable def ep1028 := @Enclosure.Real.IsNear.mulLit_ff qz238 qz428 37303163 524288 1 524288 2 7 0 1 37303163 1835008

noncomputable abbrev qz446 := (Complex.re qz482)

noncomputable abbrev qz447 := (Complex.im qz482)

noncomputable abbrev qz239 := (@HAdd.hAdd Real Real Real qz339 (@HMul.hMul Real Real Real qz263 qz446 qz446) (@HMul.hMul Real Real Real qz263 qz447 qz447))

noncomputable abbrev qz240 := qz444

noncomputable def ep1029 := @Enclosure.Real.IsNear.of_eq qz238 (Real.sqrt qz239) Bool.false 37303163 524288 1 524288 (BSN.norm_eq_sqrt_mul_add qz240)

noncomputable def ep1030 := @Enclosure.Real.IsNear.recentre' (Real.sqrt qz239) Bool.false 37303163 524288 1 524288 37303163

noncomputable def ep1031 := @Enclosure.Real.IsNear.sqrt_image qz239 316396381 62500 0 1 18651581 18651582 262144

noncomputable abbrev qz241 := (@HMul.hMul Real Real Real qz263 qz446 qz446)

noncomputable abbrev qz242 := (@HMul.hMul Real Real Real qz263 qz447 qz447)

noncomputable def ep1032 := @Enclosure.Real.IsNear.addLit_ff qz241 qz242 49 4 0 1 78907689 15625 0 1

noncomputable abbrev qz243 := qz446

noncomputable def ep1033 := @Enclosure.Real.IsNear.mulLit_ff qz243 qz243 7 2 0 1 7 2 0 1 49 4

noncomputable def ep1034 := @Enclosure.Complex.IsNear.of_eq qz240 (Complex.mk qz431 qz147) Bool.false 7 2 0 1 Bool.false 71064 1000 0 1 (BSN.s_add_nat_mk qz147 Bool.false 71064 1000 3 qz148)

noncomputable abbrev qz448 := (Enclosure.Real.IsNear.const Bool.false 7 2)

noncomputable abbrev qz244 := (ep1034 (@Enclosure.Complex.IsNear.mk qz431 qz380 Bool.false 7 2 0 1 Bool.false 71064 1000 0 1 qz448 qz382))

noncomputable def ep1035 := @ep1033 0 1 (@Enclosure.Complex.IsNear.re_isNear qz240 Bool.false 7 2 0 1 Bool.false 71064 1000 0 1 qz244)

noncomputable def ep1036 := ep1035 (@Enclosure.Complex.IsNear.re_isNear qz240 Bool.false 7 2 0 1 Bool.false 71064 1000 0 1 qz244)

noncomputable abbrev qz245 := qz447

noncomputable def ep1037 := @Enclosure.Real.IsNear.mulLit_ff qz245 qz245 71064 1000 0 1 71064 1000 0 1 78907689 15625

noncomputable def ep1038 := @ep1037 0 1 (@Enclosure.Complex.IsNear.im_isNear qz240 Bool.false 7 2 0 1 Bool.false 71064 1000 0 1 qz244)

noncomputable def ep1039 := ep1038 (@Enclosure.Complex.IsNear.im_isNear qz240 Bool.false 7 2 0 1 Bool.false 71064 1000 0 1 qz244)

noncomputable def ep1040 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz138 (@ascPochhammer Complex Complex.instSemiring 3))) qz237)) (Real.sqrt (@HAdd.hAdd Real Real Real qz339 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz138 (@ascPochhammer Complex Complex.instSemiring 3))) qz237)) (Complex.re (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz138 (@ascPochhammer Complex Complex.instSemiring 3))) qz237))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz138 (@ascPochhammer Complex Complex.instSemiring 3))) qz237)) (Complex.im (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz138 (@ascPochhammer Complex Complex.instSemiring 3))) qz237))))) Bool.false 327840521 8589934592

noncomputable def ep1041 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz339 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz138 (@ascPochhammer Complex Complex.instSemiring 3))) qz237)) (Complex.re (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz138 (@ascPochhammer Complex Complex.instSemiring 3))) qz237))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz138 (@ascPochhammer Complex Complex.instSemiring 3))) qz237)) (Complex.im (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz138 (@ascPochhammer Complex Complex.instSemiring 3))) qz237))))) Bool.false 655681042 17179869184

noncomputable def ep1042 := nat_lit 1784380603284203452521384051763253144913985873264320015893

noncomputable def ep1043 := nat_lit 1225016520915378468468148586754365561241600000000000000000000

noncomputable def ep1044 := nat_lit 310879485125512869100013843880778577745525054629107975746923864177423

noncomputable def ep1045 := nat_lit 128021970416354304876998095570997382749417436610560000000000000000000000000000

noncomputable def ep1046 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz339 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz138 (@ascPochhammer Complex Complex.instSemiring 3))) qz237)) (Complex.re (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz138 (@ascPochhammer Complex Complex.instSemiring 3))) qz237))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz138 (@ascPochhammer Complex Complex.instSemiring 3))) qz237)) (Complex.im (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz138 (@ascPochhammer Complex Complex.instSemiring 3))) qz237)))) ep1042 ep1043 ep1044 ep1045

noncomputable def ep1047 := nat_lit 1044249611684475799300102848398553632958964476512450954449

noncomputable def ep1048 := nat_lit 171711994668593970935595606046852988849197939038888188500853396480899

noncomputable def ep1049 := nat_lit 185032747899931913305320300841174877988755349187967265361

noncomputable def ep1050 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz138 (@ascPochhammer Complex Complex.instSemiring 3))) qz237)) (Complex.re (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz138 (@ascPochhammer Complex Complex.instSemiring 3))) qz237))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz138 (@ascPochhammer Complex Complex.instSemiring 3))) qz237)) (Complex.im (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz138 (@ascPochhammer Complex Complex.instSemiring 3))) qz237))) ep1047 ep1043 ep1048 ep1045 ep1049

noncomputable def ep1051 := nat_lit 306254130228844617117037146688591390310400000000000000000000

noncomputable def ep1052 := nat_lit 34791872614229724541104559458481397224081778897554946811517616924131

noncomputable def ep1053 := nat_lit 32005492604088576219249523892749345687354359152640000000000000000000000000000

noncomputable def ep1054 := nat_lit 546473929656024767044574074825814394925895762132944197965866107629147955364534533587827894203187200000000000000000000

noncomputable def ep1055 := nat_lit 32314851255799952997872199607

noncomputable def ep1056 := nat_lit 1106804644422573096960000000000

noncomputable def ep1057 := nat_lit 8218584499349421793681058920157

noncomputable def ep1058 := nat_lit 357801579672804553811558400000000000000

noncomputable def ep1059 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz138 (@ascPochhammer Complex Complex.instSemiring 3))) qz237)) (Complex.re (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz138 (@ascPochhammer Complex Complex.instSemiring 3))) qz237)) ep1055 ep1056 ep1057 ep1058 ep1055 ep1056 ep1057

noncomputable def ep1060 := nat_lit 13602674292209304873403657481

noncomputable def ep1061 := nat_lit 553402322211286548480000000000

noncomputable def ep1062 := nat_lit 3955961292332395247246392830391

noncomputable def ep1063 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz138 (@ascPochhammer Complex Complex.instSemiring 3))) qz237) Bool.true ep1055 ep1056 ep1057 ep1058 Bool.true ep1060 ep1061 ep1062

noncomputable def ep1064 := nat_lit 178900789836402276905779200000000000000

noncomputable def ep1065 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz138 (@ascPochhammer Complex Complex.instSemiring 3))) qz237 Bool.true ep1055 ep1056 ep1057 ep1058 Bool.true ep1060 ep1061 ep1062 ep1064

noncomputable def ep1066 := nat_lit 14775844738913167791140963

noncomputable def ep1067 := nat_lit 8854437155380584775680000000

noncomputable def ep1068 := nat_lit 3763227001902076121136061393

noncomputable def ep1069 := nat_lit 2862412637382436430492467200000000000

noncomputable def ep1070 := nat_lit 317373652744122989833120617

noncomputable def ep1071 := nat_lit 11529215046068469760000000000

noncomputable def ep1072 := nat_lit 53806813361886543600965633653

noncomputable abbrev qz246 := (Complex.re qz445)

noncomputable abbrev qz247 := (Complex.im qz445)

noncomputable def ep1073 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz138 (@ascPochhammer Complex Complex.instSemiring 3)))) qz246) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz138 (@ascPochhammer Complex Complex.instSemiring 3)))) qz247) ep1066 ep1067 ep1068 ep1069 ep1070 ep1071 ep1072

noncomputable def ep1074 := nat_lit 2484733192172253845913600000000000000

noncomputable def ep1075 := nat_lit 2980518954478667223832650328671322215518107074560000000

noncomputable def ep1076 := nat_lit 95413754579414547683082240000

noncomputable def ep1077 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz138 (@ascPochhammer Complex Complex.instSemiring 3)))) qz246 946814143 30000000 0 1 15605855540027741 295147905179352825856 3974620605030480751 ep1076 ep1066

noncomputable def ep1078 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz138 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz138 (@ascPochhammer Complex Complex.instSemiring 3)))) 946814143 30000000 0 1 0 1 0 1 946814143

noncomputable def ep1079 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz138 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 2840442429 125000 0 1 946814143 30000000 0

noncomputable abbrev qz449 := (@HAdd.hAdd Complex Complex Complex qz462 qz476 qz466)

noncomputable abbrev qz248 := qz449

noncomputable def ep1080 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz138 (@ascPochhammer Complex Complex.instSemiring 3)) (@HMul.hMul Complex Complex Complex qz46 (@Polynomial.eval Complex Complex.instSemiring qz138 (@ascPochhammer Complex Complex.instSemiring 2)) qz248) Bool.true 2840442429 125000 0 1 Bool.true 2800555677423 7812500 0 1

noncomputable abbrev qz249 := (Complex.re qz449)

noncomputable abbrev qz250 := (Complex.im qz449)

noncomputable def ep1081 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz138 (@ascPochhammer Complex Complex.instSemiring 2))) qz249) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz138 (@ascPochhammer Complex Complex.instSemiring 2))) qz250) 315583881 25000 0 1 157815378 15625 0 1

noncomputable def ep1082 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz138 (@ascPochhammer Complex Complex.instSemiring 2))) qz249 315583881 62500 0 1 5 2 0 1 315583881 25000

noncomputable abbrev qz450 := (@HAdd.hAdd Complex Complex Complex qz462 qz476 (@Nat.cast Complex Complex.instNatCast 1))

noncomputable abbrev qz251 := qz450

noncomputable def ep1083 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz138 (@ascPochhammer Complex Complex.instSemiring 2)) (@HMul.hMul Complex Complex Complex qz46 (@Polynomial.eval Complex Complex.instSemiring qz138 (@ascPochhammer Complex Complex.instSemiring 1)) qz251) Bool.true 315583881 62500 0 1 Bool.false 17766 125 0 1

noncomputable abbrev qz252 := (Complex.re qz450)

noncomputable abbrev qz253 := (Complex.im qz450)

noncomputable def ep1084 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz138 (@ascPochhammer Complex Complex.instSemiring 1))) qz252) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz138 (@ascPochhammer Complex Complex.instSemiring 1))) qz253) 3 4 0 1 78907689 15625 0 1

noncomputable def ep1085 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz138 (@ascPochhammer Complex Complex.instSemiring 1))) qz252 1 2 0 1 3 2 0 1 3 4

noncomputable def ep1086 := @ep1085 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz138 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 71064 1000 0 1 ep792)

noncomputable def ep1087 := @Enclosure.Complex.IsNear.of_eq qz251 (Complex.mk qz435 qz147) Bool.false 3 2 0 1 Bool.false 71064 1000 0 1 (BSN.s_add_nat_mk qz147 Bool.false 71064 1000 1 qz148)

noncomputable abbrev qz451 := (Enclosure.Real.IsNear.const Bool.false 3 2)

noncomputable abbrev qz254 := (ep1087 (@Enclosure.Complex.IsNear.mk qz435 qz380 Bool.false 3 2 0 1 Bool.false 71064 1000 0 1 qz451 qz382))

noncomputable def ep1088 := ep1086 (@Enclosure.Complex.IsNear.re_isNear qz251 Bool.false 3 2 0 1 Bool.false 71064 1000 0 1 qz254)

noncomputable def ep1089 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz138 (@ascPochhammer Complex Complex.instSemiring 1))) qz253 71064 1000 0 1 71064 1000 0 1 78907689 15625

noncomputable def ep1090 := @ep1089 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz138 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 71064 1000 0 1 ep792)

noncomputable def ep1091 := ep1090 (@Enclosure.Complex.IsNear.im_isNear qz251 Bool.false 3 2 0 1 Bool.false 71064 1000 0 1 qz254)

noncomputable def ep1092 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz138 (@ascPochhammer Complex Complex.instSemiring 1)) qz251 Bool.true 315583881 62500 0 1 Bool.false 17766 125 0 1 (@ep1084 315583881 315583881 62500 0 1 (ep1088 rfl) (ep1091 rfl) rfl rfl)

noncomputable def ep1093 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz138 (@ascPochhammer Complex Complex.instSemiring 1))) qz253) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz138 (@ascPochhammer Complex Complex.instSemiring 1))) qz252) 8883 250 0 1 26649 250 0 1

noncomputable def ep1094 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz138 (@ascPochhammer Complex Complex.instSemiring 1))) qz253 1 2 0 1 71064 1000 0 1 8883 250

noncomputable def ep1095 := @ep1094 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz138 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 71064 1000 0 1 ep792)

noncomputable def ep1096 := ep1095 (@Enclosure.Complex.IsNear.im_isNear qz251 Bool.false 3 2 0 1 Bool.false 71064 1000 0 1 qz254)

noncomputable def ep1097 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz138 (@ascPochhammer Complex Complex.instSemiring 1))) qz252 71064 1000 0 1 3 2 0 1 26649 250

noncomputable def ep1098 := @ep1097 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz138 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 71064 1000 0 1 ep792)

noncomputable def ep1099 := ep1098 (@Enclosure.Complex.IsNear.re_isNear qz251 Bool.false 3 2 0 1 Bool.false 71064 1000 0 1 qz254)

noncomputable abbrev qz255 := (ep1083 (BSN.ascPochhammer_succ_eval_c 1 2 qz378 rfl) (ep1092 (@ep1093 8883000 17766 125 0 1 (ep1096 rfl) (ep1099 rfl) rfl rfl)))

noncomputable def ep1100 := @ep1082 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz138 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 315583881 62500 0 1 Bool.false 17766 125 0 1 qz255)

noncomputable def ep1101 := @Enclosure.Complex.IsNear.of_eq qz248 (Complex.mk qz437 qz147) Bool.false 5 2 0 1 Bool.false 71064 1000 0 1 (BSN.s_add_nat_mk qz147 Bool.false 71064 1000 2 qz148)

noncomputable abbrev qz452 := (Enclosure.Real.IsNear.const Bool.false 5 2)

noncomputable abbrev qz256 := (ep1101 (@Enclosure.Complex.IsNear.mk qz437 qz380 Bool.false 5 2 0 1 Bool.false 71064 1000 0 1 qz452 qz382))

noncomputable def ep1102 := ep1100 (@Enclosure.Complex.IsNear.re_isNear qz248 Bool.false 5 2 0 1 Bool.false 71064 1000 0 1 qz256)

noncomputable def ep1103 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz138 (@ascPochhammer Complex Complex.instSemiring 2))) qz250 17766 125 0 1 71064 1000 0 1 157815378 15625

noncomputable def ep1104 := @ep1103 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz138 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 315583881 62500 0 1 Bool.false 17766 125 0 1 qz255)

noncomputable def ep1105 := ep1104 (@Enclosure.Complex.IsNear.im_isNear qz248 Bool.false 5 2 0 1 Bool.false 71064 1000 0 1 qz256)

noncomputable def ep1106 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz138 (@ascPochhammer Complex Complex.instSemiring 2)) qz248 Bool.true 2840442429 125000 0 1 Bool.true 2800555677423 7812500 0 1 (@ep1081 8876382590625 2840442429 125000 0 1 (ep1102 rfl) (ep1105 rfl) rfl rfl)

noncomputable def ep1107 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz138 (@ascPochhammer Complex Complex.instSemiring 2))) qz250) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz138 (@ascPochhammer Complex Complex.instSemiring 2))) qz249) 2803331614923 7812500 0 1 8883 25 0 1

noncomputable def ep1108 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz138 (@ascPochhammer Complex Complex.instSemiring 2))) qz250 315583881 62500 0 1 71064 1000 0 1 2803331614923 7812500

noncomputable def ep1109 := @ep1108 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz138 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 315583881 62500 0 1 Bool.false 17766 125 0 1 qz255)

noncomputable def ep1110 := ep1109 (@Enclosure.Complex.IsNear.im_isNear qz248 Bool.false 5 2 0 1 Bool.false 71064 1000 0 1 qz256)

noncomputable def ep1111 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz138 (@ascPochhammer Complex Complex.instSemiring 2))) qz249 17766 125 0 1 5 2 0 1 8883 25

noncomputable def ep1112 := @ep1111 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz138 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 315583881 62500 0 1 Bool.false 17766 125 0 1 qz255)

noncomputable def ep1113 := ep1112 (@Enclosure.Complex.IsNear.re_isNear qz248 Bool.false 5 2 0 1 Bool.false 71064 1000 0 1 qz256)

noncomputable abbrev qz257 := (ep1080 (BSN.ascPochhammer_succ_eval_c 2 3 qz378 rfl) (ep1106 (@ep1107 70013891935575 2800555677423 7812500 0 1 (ep1110 rfl) (ep1113 rfl) rfl rfl)))

noncomputable def ep1114 := @ep1079 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep920) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz138 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 2840442429 125000 0 1 Bool.true 2800555677423 7812500 0 1 qz257)

noncomputable def ep1115 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz138 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 2800555677423 7812500 0 1 0 1 0

noncomputable def ep1116 := @ep1115 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep920) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz138 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 2840442429 125000 0 1 Bool.true 2800555677423 7812500 0 1 qz257)

noncomputable def ep1117 := @Enclosure.Real.IsNear.addLit_ft_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz138 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz138 (@ascPochhammer Complex Complex.instSemiring 3)))) 311172853047 625000000 0 1 0 1 0 1 311172853047

noncomputable def ep1118 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz138 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 2800555677423 7812500 0 1 311172853047 625000000 0

noncomputable def ep1119 := @ep1118 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep920) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz138 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 2840442429 125000 0 1 Bool.true 2800555677423 7812500 0 1 qz257)

noncomputable def ep1120 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz138 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 2840442429 125000 0 1 0 1 0

noncomputable def ep1121 := @ep1120 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep920) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz138 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 2840442429 125000 0 1 Bool.true 2800555677423 7812500 0 1 qz257)

noncomputable def ep1122 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz138 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.false 946814143 30000000 0 1 Bool.false 311172853047 625000000 0 1 (@ep1078 946814143 30000000 0 1 (ep1114 rfl) (ep1116 rfl) rfl rfl) (@ep1117 311172853047 625000000 0 1 (ep1119 rfl) (ep1121 rfl) rfl rfl)

noncomputable def ep1123 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz138 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 946814143 30000000 0 1 Bool.false 311172853047 625000000 0 1 ep1122

noncomputable def ep1124 := nat_lit 11926719322426818460385280000

noncomputable def ep1125 := @Enclosure.Complex.IsNear.re_isNear qz237 Bool.true 15605855540027741 295147905179352825856 3974620605030480751 ep1076 Bool.false 1019927187209311 18446744073709551616 518748465700118297 ep1124

noncomputable abbrev qz453 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 170859375)))

noncomputable def ep1126 := @Enclosure.Complex.IsNear.of_eq qz237 (Complex.mk (@HMul.hMul Real Real Real qz0 qz453 qz205) (@HMul.hMul Real Real Real qz0 qz453 qz206)) Bool.true 15605855540027741 295147905179352825856 3974620605030480751 ep1076 Bool.false 1019927187209311 18446744073709551616 518748465700118297

noncomputable abbrev qz454 := (Real.sqrt (@Nat.cast Real Real.instNatCast 170859375))

noncomputable abbrev qz455 := (@Nat.cast Real Real.instNatCast 170859375)

noncomputable def ep1127 := @Enclosure.Real.IsNear.inv_image qz454 224563546933833 17179869184 1 17179869184 657158 657159 8589934592 (@Enclosure.Real.IsNear.of_eq qz454 (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz455 qz19)) Bool.false 224563546933833 17179869184 1 17179869184 (BSN.sqrt_natCast_div_one 170859375) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz455 qz19)) Bool.false 224563546933833 17179869184 1 17179869184 224563546933833 17179869184 1 17179869184 (BSN.sqrt_enclosure 170859375 1 112281773466916 112281773466917 8589934592 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep1128 := nat_lit 838100943070293300562886656

noncomputable def ep1129 := nat_lit 3879292500000000000000000

noncomputable def ep1130 := nat_lit 2124039924396124256730046692528675

noncomputable def ep1131 := nat_lit 69486322526432349988248161643105

noncomputable def ep1132 := BSN.log_dyadic_bound 7 23 10 9 ep1130 8589934592 3879292500 ep1131 56114196246175274031825 5399707268 30 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base9 (BSN.artanhP 7) (BSN.artanhQ 23) 0 9 ep1131 ep1130 56114196246175274031825 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep1133 := @Enclosure.Real.IsNear.mulLit_ff qz147 qz207 71064 1000 0 1 12195973876373221 4503599627370496 400004655151 1551717000000000000000 108336835943823322143 562949953421312000 131601531544679 7183875000000000000000 qz149 (BSN.isNear_log_sfrac 15 1 12195973876373221 4503599627370496 400004655151 1551717000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz420) Bool.false ep1128 ep970 1000011637877500 ep1129 12195973876373221 4503599627370496 400004655151 1551717000000000000000 (BSN.log_rat_reduce_isNear 15 1 3 30 16 5399707268 8589934592 24973259072661432 36028797018963968 3879292500 1000000000000000 rfl rfl rfl rfl (ep1132 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1134 := nat_lit 999918360101577836315279360

noncomputable def ep1135 := nat_lit 1237940039285380274899124224

noncomputable def ep1136 := nat_lit 30583919299955063987071613672124025137865418357298586612574287928795645878972444825716806654299079870025196764484329834015561416515536004177930906189094203359614238185041

noncomputable def ep1137 := nat_lit 1723989524678609869184368353634558086375647288945605880257499904391989104065417411410730399287089189440146844853530817917959165259045966673531664948206962296697359276441600

noncomputable def ep1138 := nat_lit 277572767177085169950502982608971158667290451521151977783476412771480742370908265156855851628142762289730055222392076357433570264557686395470670580282063638484561

noncomputable def ep1139 := nat_lit 185511110035038125896357582516145117156526203522474762963205857346234093359416545872502656903429195191801510713124291906916457445077920788615271809604177916204229323380305

noncomputable def ep1140 := nat_lit 156883046745753498095777520180744785860183903294050135103432491299671008469952984438376466335125116239053362881671304430534284038573182967291381510286833568999459694156185600

noncomputable def ep1141 := BSN.cos_dyadic_bound_f 28419389084933 35184372088832 4 3 17179869184 7766161744 ep1136 ep1137 ep1138 ep1139 ep1140 ep1138 11873737873 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 28419389084933) (BSN.cosEvenQ 35184372088832) 0 3 ep1136 ep1137 ep1138 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 28419389084933) (BSN.cosOddQ 35184372088832) 0 3 ep1139 ep1140 ep1138 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz456 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 1653088927365) (@Nat.cast Real Real.instNatCast 8589934592))

noncomputable def ep1142 := @Enclosure.Real.IsNear.cos_image qz208 qz456 Bool.false 1653088927365 8589934592 79 4294967296 Bool.true 11873737873 17179869184 1 3879292500 (@Enclosure.Real.IsNear.recentre' qz208 Bool.false 108336835943823322143 562949953421312000 131601531544679 7183875000000000000000 1653088927365 8589934592 79 4294967296 (ep1133 rfl) rfl) (Enclosure.sfrac_false_div 1653088927365 8589934592) (BSN.cos_reduce2 qz456 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast ep1134) (@Nat.cast Real Real.instNatCast ep1135)) 226375608064910080 72057594037927936 Bool.false 11873737873 17179869184 30 1000000000000000 7758585000 3879292500 (BSN.sin_reduce_arg_pos_rat_q2 1653088927365 8589934592 226375608064910080 72057594037927936 30 ep1134 ep1135 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 11873737873 17179869184 ep1134 ep1135 28419389084933 35184372088832 7766161744 7758585000 (ep1141 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1143 := nat_lit 3023438122681059046577101654558980630489421211222949184931057831311345203658405302683004822639598604693664267745

noncomputable def ep1144 := nat_lit 852239132436968601736534718962914620494087683347851114682261747749608011033589111964107092533864866956228564090880

noncomputable def ep1145 := nat_lit 425517967923684632687993519045676235295446691804449615270102729027387475565327844442316131724176663581916641

noncomputable def ep1146 := nat_lit 7917839482692802013534723772433161032615148639511469232585190344254145477478241452421629833176157202456654740961

noncomputable def ep1147 := nat_lit 15624384094677757698503136514320101375724940861377270435841465375409480202282467052675296696454189227530857008332800

noncomputable def ep1148 := BSN.sin_dyadic_bound_f 28419389084933 35184372088832 3 2 17179869184 7766161744 ep1143 ep1144 ep1145 ep1146 ep1147 ep1145 12416209328 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 28419389084933) (BSN.sinEvenQ 35184372088832) 0 2 ep1143 ep1144 ep1145 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 28419389084933) (BSN.sinOddQ 35184372088832) 0 2 ep1146 ep1147 ep1145 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1149 := @Enclosure.Real.IsNear.sin_image qz208 qz456 Bool.false 1653088927365 8589934592 79 4294967296 Bool.true 12416209328 17179869184 1 3879292500 (@Enclosure.Real.IsNear.recentre' qz208 Bool.false 108336835943823322143 562949953421312000 131601531544679 7183875000000000000000 1653088927365 8589934592 79 4294967296 (ep1133 rfl) rfl) (Enclosure.sfrac_false_div 1653088927365 8589934592) (BSN.sin_reduce2 qz456 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast ep1134) (@Nat.cast Real Real.instNatCast ep1135)) 226375608064910080 72057594037927936 Bool.false 12416209328 17179869184 30 1000000000000000 7758585000 3879292500 (BSN.sin_reduce_arg_pos_rat_q2 1653088927365 8589934592 226375608064910080 72057594037927936 30 ep1134 ep1135 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 12416209328 17179869184 ep1134 ep1135 28419389084933 35184372088832 7766161744 7758585000 (ep1148 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1150 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz453 qz205) (@HMul.hMul Real Real Real qz0 qz453 qz206) Bool.true 15605855540027741 295147905179352825856 3974620605030480751 ep1076 Bool.false 1019927187209311 18446744073709551616 518748465700118297 ep1124 (@Enclosure.Real.IsNear.mulLit_ft qz453 qz205 1314317 17179869184 1 17179869184 11873737873 17179869184 77689768699 4165358604779520000 15605855540027741 295147905179352825856 3974620605030480751 ep1076 (@Enclosure.Real.IsNear.recentre' qz453 Bool.false 1314317 17179869184 1 17179869184 1314317 17179869184 1 17179869184 (ep1127 rfl rfl) rfl) (@Enclosure.Real.IsNear.recentre' qz205 Bool.true 11873737873 17179869184 310759074796 16661434419118080000 11873737873 17179869184 77689768699 4165358604779520000 (ep1142 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz453 qz206 1314317 17179869184 1 17179869184 776013083 1073741824 77689768699 4165358604779520000 1019927187209311 18446744073709551616 518748465700118297 ep1124 (@Enclosure.Real.IsNear.recentre' qz453 Bool.false 1314317 17179869184 1 17179869184 1314317 17179869184 1 17179869184 (ep1127 rfl rfl) rfl) (@Enclosure.Real.IsNear.neg qz209 Bool.true 776013083 1073741824 77689768699 4165358604779520000 (@Enclosure.Real.IsNear.recentre' qz209 Bool.true 12416209328 17179869184 310759074796 16661434419118080000 776013083 1073741824 77689768699 4165358604779520000 (ep1149 rfl rfl) rfl)) rfl)

noncomputable def ep1151 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz138 (@ascPochhammer Complex Complex.instSemiring 3)))) qz247 311172853047 625000000 0 1 1019927187209311 18446744073709551616 518748465700118297 ep1124 ep1070

noncomputable def ep1152 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz138 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 946814143 30000000 0 1 Bool.false 311172853047 625000000 0 1 ep1122

noncomputable def ep1153 := @Enclosure.Complex.IsNear.im_isNear qz237 Bool.true 15605855540027741 295147905179352825856 3974620605030480751 ep1076 Bool.false 1019927187209311 18446744073709551616 518748465700118297 ep1124

noncomputable def ep1154 := nat_lit 553402322211286548480000000

noncomputable def ep1155 := nat_lit 491158383984422400372674471

noncomputable def ep1156 := nat_lit 357801579672804553811558400000000000

noncomputable def ep1157 := nat_lit 4856118592629763076496376827

noncomputable def ep1158 := nat_lit 184467440737095516160000000000

noncomputable def ep1159 := nat_lit 412264677815576005228895066099

noncomputable def ep1160 := @Enclosure.Real.IsNear.addLit_ft_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz138 (@ascPochhammer Complex Complex.instSemiring 3)))) qz247) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz138 (@ascPochhammer Complex Complex.instSemiring 3)))) qz246) 965681485679984356085473 ep1154 ep1155 ep1156 ep1157 ep1158 ep1159

noncomputable def ep1161 := nat_lit 19877865537378030767308800000000000000

noncomputable def ep1162 := nat_lit 2509250513864132642748677024573191006989540392960000000

noncomputable def ep1163 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz138 (@ascPochhammer Complex Complex.instSemiring 3)))) qz247 946814143 30000000 0 1 1019927187209311 18446744073709551616 518748465700118297 ep1124 965681485679984356085473

noncomputable def ep1164 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz138 (@ascPochhammer Complex Complex.instSemiring 3)))) qz246 311172853047 625000000 0 1 15605855540027741 295147905179352825856 3974620605030480751 ep1076 ep1157

noncomputable abbrev qz457 := (@ep1126 ep1124 (BSN.cpow_neg_s_sub_mk qz147 71064 1000 15 3 170859375 qz148 rfl EMRow17.d18) ep1150)

noncomputable def ep1165 := ep1065 (@ep1073 ep1074 ep1075 ep1055 ep1056 ep1057 ep1058 (@ep1077 ep1067 ep1068 ep1069 ep1123 (ep1125 qz457) rfl) (@ep1151 ep1071 ep1072 ep1074 ep1152 (ep1153 qz457) rfl) rfl rfl) (@ep1160 ep1161 ep1162 ep1060 ep1061 ep1062 ep1064 (@ep1163 ep1154 ep1155 ep1156 ep1123 (ep1153 qz457) rfl) (@ep1164 ep1158 ep1159 ep1161 ep1152 (ep1125 qz457) rfl) rfl rfl)

noncomputable def ep1166 := @Enclosure.Real.IsNear.mulLit_tt (Complex.im (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz138 (@ascPochhammer Complex Complex.instSemiring 3))) qz237)) (Complex.im (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz138 (@ascPochhammer Complex Complex.instSemiring 3))) qz237)) ep1060 ep1061 ep1062 ep1064 ep1060 ep1061 ep1062

noncomputable def ep1167 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz138 (@ascPochhammer Complex Complex.instSemiring 3))) qz237) Bool.true ep1055 ep1056 ep1057 ep1058 Bool.true ep1060 ep1061 ep1062

noncomputable def ep1168 := @ep1027 12229488392867923 15762598695796736 10548907457 15762598695796736 (@ep1028 1 1835008 (ep1029 (@ep1030 524288 1 524288 (ep1031 (@ep1032 316396381 316396381 62500 0 1 (ep1036 rfl) (ep1039 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) (Enclosure.Real.IsNear.const Bool.false 2 7) rfl) (@ep1040 137 4294967296 (BSN.norm_eq_sqrt_mul_add (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz138 (@ascPochhammer Complex Complex.instSemiring 3))) qz237)) (@ep1041 548 17179869184 327840521 8589934592 137 4294967296 (@ep1046 327840247 327840795 8589934592 (@ep1050 ep1051 ep1052 ep1053 ep1054 ep1042 ep1043 ep1044 ep1045 (@ep1059 ep1058 ep1047 ep1043 ep1048 ep1045 (@ep1063 ep1064 ep1165) (@ep1063 ep1064 ep1165) rfl) (@ep1166 ep1064 ep1049 ep1051 ep1052 ep1053 (@ep1167 ep1064 ep1165) (@ep1167 ep1064 ep1165) rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl

theorem EMRow17.d19 : Enclosure.Real.IsNear (@HAdd.hAdd Real Real Real qz339 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz138 1 15))) (@HMul.hMul Real Real Real qz0 qz236 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz138 (@ascPochhammer Complex Complex.instSemiring 3))) qz237)))) Bool.false 114373005287199467 141863388262170624 34185202365275 425590164786511872 := ep1025 (ep1026 ep1168) rfl rfl

noncomputable def EMRow17.d20 := fun (I J : @NonemptyInterval Real Real.instLE) => @LE.le Real Real.instLE (@Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE I)) (@Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE J))

noncomputable abbrev qz458 := (EMRow17.d3 qz467 qz478 (@Enclosure.dec_le_dec qz467 qz478 68454 1000 71064 1000 (@Eq.refl Real qz467) (@Eq.refl Real qz478) rfl rfl rfl) 14 15 1 1)

noncomputable abbrev qz258 := qz458

noncomputable def ep1169 := @Zeta.Certificates.ZIntervalEM.Certificate.mk qz258 (@Enclosure.dec_nonneg qz17 68454 1000 qz18) (@Enclosure.pos_of_ble 1 rfl) (@Enclosure.pos_of_ble 14 rfl)

noncomputable abbrev qz259 := (Zeta.Certificates.ZIntervalEM.fstVal qz458)

noncomputable def ep1170 := @Enclosure.Real.IsNear.neg_val qz259 ep151 ep152

noncomputable def ep1171 := @Enclosure.Real.IsNear.of_eq qz259 (hardyZApproximantEM 1 14 qz17) Bool.true

noncomputable abbrev qz260 := (Zeta.Certificates.ZIntervalEM.sndVal qz458)

noncomputable def ep1172 := BSN.mul_neg_of_neg_pos_r qz259 qz260 (@ep1170 ep153 ep154 (@ep1171 ep151 ep152 ep153 ep154 (@Eq.refl Real (hardyZApproximantEM 1 14 qz17)) EMRow17.d9) rfl rfl rfl)

noncomputable def ep1173 := @Enclosure.Real.IsNear.pos_val qz260 ep547 ep548

noncomputable def ep1174 := @Enclosure.Real.IsNear.of_eq qz260 (hardyZApproximantEM 1 15 qz147) Bool.false

noncomputable def ep1175 := BSN.gt_trans_le (@Norm.norm Real Real.norm qz259) (BSN.hardyZErrorBoundStrong 1 14 qz17)

noncomputable def ep1176 := @Enclosure.norm_gt_of_isNear qz259 (BSN.hardyZErrorBoundStrong 1 14 qz17) Bool.true

noncomputable def ep1177 := @Enclosure.Real.IsNear.of_eq (BSN.hardyZErrorBoundStrong 1 14 qz17) (@HAdd.hAdd Real Real Real qz339 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz6 1 14))) (@HMul.hMul Real Real Real qz0 qz213 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz216)))) Bool.false 124141954928869819 141863388262170624 31268408255419 425590164786511872 (@Eq.refl Real (@HAdd.hAdd Real Real Real qz339 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz6 1 14))) (@HMul.hMul Real Real Real qz0 qz213 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz216)))))

noncomputable def ep1178 := BSN.gt_trans_le (@Norm.norm Real Real.norm qz260) (BSN.hardyZErrorBoundStrong 1 15 qz147)

noncomputable def ep1179 := @Enclosure.norm_gt_of_isNear qz260 (BSN.hardyZErrorBoundStrong 1 15 qz147) Bool.false

noncomputable def ep1180 := @Enclosure.Real.IsNear.of_eq (BSN.hardyZErrorBoundStrong 1 15 qz147) (@HAdd.hAdd Real Real Real qz339 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz138 1 15))) (@HMul.hMul Real Real Real qz0 qz236 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz138 (@ascPochhammer Complex Complex.instSemiring 3))) qz237)))) Bool.false 114373005287199467 141863388262170624 34185202365275 425590164786511872 (@Eq.refl Real (@HAdd.hAdd Real Real Real qz339 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz138 1 15))) (@HMul.hMul Real Real Real qz0 qz236 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz54 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz214)) ↑qz215) (@Polynomial.eval Complex Complex.instSemiring qz138 (@ascPochhammer Complex Complex.instSemiring 3))) qz237)))))

noncomputable def ep1181 := @List.cons EMRow17.d0 (@PSigma.mk Zeta.Certificates.ZIntervalEM Zeta.Certificates.ZIntervalEM.Certificate qz258 (ep1169 (@Enclosure.pos_of_ble 1 rfl) (@Enclosure.pos_of_ble 15 rfl) (ep1172 (@ep1173 ep549 ep550 (@ep1174 ep547 ep548 ep549 ep550 (@Eq.refl Real (hardyZApproximantEM 1 15 qz147)) EMRow17.d12) rfl rfl rfl)) (ep1175 (hardyZErrorBoundEM 1 14 qz17) (BSN.hardyZErrorBoundEM_le_strong 1 14 qz17 rfl) (@ep1176 Bool.false ep151 ep152 ep153 ep154 124141954928869819 141863388262170624 31268408255419 425590164786511872 (@ep1171 ep151 ep152 ep153 ep154 (@Eq.refl Real (hardyZApproximantEM 1 14 qz17)) EMRow17.d9) (ep1177 EMRow17.d17) rfl rfl rfl rfl rfl)) (ep1178 (hardyZErrorBoundEM 1 15 qz147) (BSN.hardyZErrorBoundEM_le_strong 1 15 qz147 rfl) (@ep1179 Bool.false ep547 ep548 ep549 ep550 114373005287199467 141863388262170624 34185202365275 425590164786511872 (@ep1174 ep547 ep548 ep549 ep550 (@Eq.refl Real (hardyZApproximantEM 1 15 qz147)) EMRow17.d12) (ep1180 EMRow17.d19) rfl rfl rfl rfl rfl)))) (@List.nil EMRow17.d0)

noncomputable abbrev qz459 := (@Enclosure.dec_le_dec qz467 qz478 68454 1000 71064 1000 (@Eq.refl Real qz467) (@Eq.refl Real qz478) rfl rfl rfl)

noncomputable abbrev qz261 := (Zeta.Certificates.CertifiedZeroIntervals.intervals (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedEM ep1181 (@List.IsChain.singleton EMRow17.d1 EMRow17.d20 (EMRow17.d2 qz276 qz380 qz459))))

noncomputable abbrev qz460 := (@NonemptyInterval Real Real.instLE)

noncomputable def ep1182 := And (@Eq (Option Real) (@Option.map qz460 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz460 qz261)) (@Option.some Real qz17))

noncomputable def ep1183 := ep1182 (@Eq (Option Real) (@Option.map qz460 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz460 qz261)) (@Option.some Real qz147))

noncomputable def ep1184 := @And.intro (@Eq Nat (@List.length qz460 qz261) 1) ep1183

noncomputable def ep1185 := @And.intro (@Eq (Option Real) (@Option.map qz460 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz460 qz261)) (@Option.some Real qz17))

noncomputable def ep1186 := @ep1185 (@Eq (Option Real) (@Option.map qz460 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz460 qz261)) (@Option.some Real qz147))

noncomputable abbrev qz262 := (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedEM ep1181 (@List.IsChain.singleton EMRow17.d1 EMRow17.d20 (EMRow17.d2 qz276 qz380 qz459)))

theorem EMRow17.d21 : Zeta.Certificates.BatchSpec 1 68454 1000 71064 1000 := @Exists.intro Zeta.Certificates.CertifiedZeroIntervals (fun (C : Zeta.Certificates.CertifiedZeroIntervals) => And (@Eq Nat (@List.length qz460 (Zeta.Certificates.CertifiedZeroIntervals.intervals C)) 1) (And (@Eq (Option Real) (@Option.map qz460 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz460 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz17)) (@Eq (Option Real) (@Option.map qz460 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz460 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz147)))) qz262 (ep1184 (@Eq.refl Nat 1) (ep1186 (@Eq.refl (Option Real) (@Option.some Real qz17)) (@Eq.refl (Option Real) (@Option.some Real qz147))))

theorem solution : Zeta.Certificates.BatchSpec 1 68454 1000 71064 1000 := EMRow17.d21
#print axioms solution
#check solution
