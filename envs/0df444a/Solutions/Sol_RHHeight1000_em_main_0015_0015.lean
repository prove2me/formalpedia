-- Prove2me | solution 1 for RHHeight1000.em_main_0015_0015
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-20T08:09:25.503175+00:00
-- url     : https://prove2.me/submissions/223e0879-5974-4bf8-9267-6af454061aaf

import Definitions.Def_RHT1000_Support_20261118_S005
/- Copyright (c) 2026 Salvatore Mercuri, Bhavik Mehta.
Apache 2.0 license; see the source project LICENSE. -/
set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable def EMRow15.d0 := @PSigma Zeta.Certificates.ZIntervalEM fun (I : Zeta.Certificates.ZIntervalEM) => Zeta.Certificates.ZIntervalEM.Certificate I

noncomputable def EMRow15.d1 := @NonemptyInterval Real Real.instLE

noncomputable def EMRow15.d2 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @NonemptyInterval.mk Real Real.instLE (@Prod.mk Real Real a b) h

noncomputable def EMRow15.d3 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) (fc sc fb sb : Nat) => Zeta.Certificates.ZIntervalEM.mk (EMRow15.d2 a b h) fc sc fb sb

noncomputable def ep0 := nat_lit 26986075409044028275299783

noncomputable def ep1 := nat_lit 4294967296000000000000000

noncomputable def ep2 := nat_lit 26986075409044045455168967

noncomputable abbrev qz263 := (@instHMul Real Real.instMul)

noncomputable abbrev qz0 := qz263

noncomputable abbrev qz1 := (Enclosure.sfrac Bool.false 2 1)

noncomputable abbrev qz264 := (@HMul.hMul Real Real Real qz0 qz1 Real.pi)

noncomputable def ep3 := @BSN.isNear_log_image_fff qz264 884279719003555 140737488355328 1 500000000000000 ep0 ep1 ep2 ep1 4138529546116343 2251799813685248 250000000074101 37050500000000000000 4138529546116343 2251799813685248 250000000074101 37050500000000000000 481788 262144

noncomputable abbrev qz265 := (@Enclosure.Real.IsNear.mulLit_ff qz1 Real.pi 2 1 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 140737488355328 1 500000000000000 (Enclosure.Real.IsNear.const Bool.false 2 1) BSN.pi_near_15 rfl)

noncomputable def ep4 := @ep3 3 262144 qz265 rfl rfl rfl rfl

noncomputable def ep5 := nat_lit 53972150818088056550599566

noncomputable def ep6 := nat_lit 34359738368000000000000000

noncomputable def ep7 := nat_lit 9806206225044028275299783

noncomputable def ep8 := nat_lit 44165944593044028275299783

noncomputable def ep9 := nat_lit 13681445815609410487519367394620474863599256634174726093703677122907123617368241606644861540940610176751640793056574796245399519365549113997355475306157239709119582688278313060810592403844863400465080549957745

noncomputable def ep10 := nat_lit 231714499556395493334623298703961145503103241611736774613091488581016477543539392410113701224645713379230392133956226737605624599560350113120270717249177907454870984269546186598262646369758174842349131395304

noncomputable def ep11 := nat_lit 8978369550011295664474073352761810093897501552430546263638635096022803738134167562509900960712119243631997923545019968443113540909076206607473711060286601587364321108377403290080403445693385008949995305

noncomputable def ep12 := BSN.log_dyadic_bound ep7 ep8 5 4 ep9 524288 148202 ep10 ep11 236759 ep5 ep6 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP ep7) (BSN.artanhQ ep8) 0 4 ep10 ep9 ep11 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz266 := (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))

noncomputable abbrev qz2 := qz266

noncomputable def ep13 := ep4 rfl rfl rfl rfl (BSN.isNear_log_sfrac ep0 ep1 4138529546116343 2251799813685248 250000000074101 37050500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast ep0) (@Nat.cast Real Real.instNatCast ep1))) Bool.false 34716502058787923820544 18889465931478580854784 1000000000296404 148202000000000000000 4138529546116343 2251799813685248 250000000074101 37050500000000000000 (BSN.log_rat_reduce_isNear ep0 ep1 2 ep5 ep6 236759 524288 24973259072661432 36028797018963968 148202 1000000000000000 rfl rfl rfl rfl (ep12 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep14 := nat_lit 53972150818088090910337934

noncomputable def ep15 := nat_lit 9806206225044045455168967

noncomputable def ep16 := nat_lit 44165944593044045455168967

noncomputable def ep17 := nat_lit 13681445815609453062485491347592146866046743284321690683909457683007658987562290830600045658905080811372395010565947827677605470036294121079488508864180301737865471494204890974265645509835068840465080549957745

noncomputable def ep18 := nat_lit 231714499556396865510889920206523150079811393376960301632499817942333196803513131357563499488546302200815366867712007119763002650772307103678175657719139104636874731038771518520299266622696414842349131395304

noncomputable def ep19 := nat_lit 8978369550011421500876706511871067098718760264493934208903156435737864998391937547068187824077011975074541700434630537294838404525415248443919841847024664017658842168336182958576672102333385008949995305

noncomputable def ep20 := BSN.log_dyadic_bound ep15 ep16 5 4 ep17 524288 148202 ep18 ep19 236759 ep14 ep6 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP ep15) (BSN.artanhQ ep16) 0 4 ep18 ep17 ep19 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep21 := ep13 (BSN.isNear_log_sfrac ep2 ep1 4138529546116343 2251799813685248 250000000074101 37050500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast ep2) (@Nat.cast Real Real.instNatCast ep1))) Bool.false 34716502058787923820544 18889465931478580854784 1000000000296404 148202000000000000000 4138529546116343 2251799813685248 250000000074101 37050500000000000000 (BSN.log_rat_reduce_isNear ep2 ep1 2 ep14 ep6 236759 524288 24973259072661432 36028797018963968 148202 1000000000000000 rfl rfl rfl rfl (ep20 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable abbrev qz267 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)

noncomputable abbrev qz3 := (Real.log qz267)

theorem EMRow15.d4 : Enclosure.Real.IsNear qz3 Bool.false 120447 65536 3 262144 := @Enclosure.Real.IsNear.of_eq qz3 (Real.log qz264) Bool.false 120447 65536 3 262144 BSN.log_two_pi_eq (@Enclosure.Real.IsNear.recentre' (Real.log qz264) Bool.false 481788 262144 3 262144 120447 65536 3 262144 (ep21 rfl rfl rfl rfl rfl rfl rfl rfl) rfl)

noncomputable def ep22 := nat_lit 8589934592000000000000000

noncomputable def ep23 := @BSN.isNear_log_image_fff Real.pi 226375608064910080 72057594037927936 1 1000000000000000 ep0 ep22 ep2 ep22 600168 524288 1 148202 600168 524288 1 148202 300084 262144 2 262144 BSN.pi_near_15 rfl rfl rfl

noncomputable def ep24 := nat_lit 17179869184000000000000000

noncomputable def ep25 := nat_lit 18396140817044028275299783

noncomputable def ep26 := nat_lit 35576010001044028275299783

noncomputable def ep27 := nat_lit 145019262663961446558303139663424756232419223153299357158415217874016130572233056993847515999529612750616182853355499335896178729185698845314776375864537073527142908641610750276034469165612529925303649396973267518946591078603565291376312767403717761600170009932259137778521478520425507632472584532570900560707662248426541531715360699177249902784721815296292248142738824858695953661559845440650653128788875447728828657762006237171740033404723254477174341920697506370253193455781322964835857351124092897592956162654178130575

noncomputable def ep28 := nat_lit 15500762873619990602332184736899274490522931101512051618692838888825382235673431503644115344741331161500627469184702974962114537943617674254904297224139410345221262767191485292268260077615645253784097850065864022184521411511133693085443040736512010941548648374196772723338837137976260321103066698629790037694560548409922339907589559883712609967105556007429010014773911317423638534096849366294542840133852248768895750397896505791271178551667935288585787166713880920071720072716082683081155281219708172458141800988558163320

noncomputable def ep29 := nat_lit 12900190794487083783367107939442176642390171280542213571554777169279725287102813254708993369099729304728646904879886535518616983985412662170766446331701281703998252143668221340329975389245922410714088123244705567402747658401492589451585970559635763980329972215329212888079422466283203384882259392047898400615815810081169907384366653346471604103896809335921621947903075223769953790093549808584241881353287841076643853121427928248525828402335494512605306631304432120211393210317325496757155861061354331245840675149075

noncomputable def ep30 := BSN.log_dyadic_bound ep25 ep26 11 10 ep27 524288 148202 ep28 ep29 600168 ep5 ep24 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base10 (BSN.artanhP ep25) (BSN.artanhQ ep26) 0 10 ep28 ep27 ep29 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep31 := nat_lit 18396140817044045455168967

noncomputable def ep32 := nat_lit 35576010001044045455168967

noncomputable def ep33 := nat_lit 145019262663962847171784895425483977818796535899227200426399035286881207006285364467913811844950531107314785650583974625982406238691319033447632878979985852280879486690814033867010958364699188952871572448188560932645032521756218245629809291975913196623825614492380080480004685076434733043183791438169545293975334857826316990371107134320667652578346815517853870648072772035977941843998949310557583393428557296298890786965786350523173236912472938174255438182435383147950274229549088258679583524155427309880956162654178130575

noncomputable def ep34 := nat_lit 15500762873620157189619721156942591192100275120160672416764593300158228469749443299607348495591439275767946573253526107895503597951484257520435868240203420954375895980141891044871083424251900562230440202302413072793440172565998181227591194192658878334739610458454844032013325963992941389843551995646587189684848765634635122388286241104146031552341815777883628509454807838726994150833304950745987647656768534710890974432620160470644835720379148964170536679305861738540146791997074363921127776563807649880221800988558163320

noncomputable def ep35 := nat_lit 12900190794487324729109480814509220959173684627296055849229843377126536688487849343376525559792931631054411655715865486295286288812423905434305314401904993536755333953308594664509631000767632482919425633906965368325056855874260596615770736441041599390097968820060635361729170158825410327022636428624381203910573184452046894301676992229743752846881064485858738985580654099214803581683226335297196686880535448467637789069028262446657986458573827723305156755787640135484017403116612632808333639900906331245840675149075

noncomputable def ep36 := BSN.log_dyadic_bound ep31 ep32 11 10 ep33 524288 148202 ep34 ep35 600168 ep14 ep24 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base10 (BSN.artanhP ep31) (BSN.artanhQ ep32) 0 10 ep34 ep33 ep35 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep37 := @Enclosure.Real.IsNear.recentre' (Real.log Real.pi) Bool.false 300084 262144 2 262144 75021 65536 1 131072 (ep23 rfl rfl rfl rfl rfl (BSN.isNear_log_sfrac ep0 ep22 600168 524288 1 148202 Bool.false (BSN.logfrac_isNear ep5 ep24 1 ep0 ep22 600168 524288 148202 rfl rfl rfl (ep30 rfl))) (BSN.isNear_log_sfrac ep2 ep22 600168 524288 1 148202 Bool.false (BSN.logfrac_isNear ep14 ep24 1 ep2 ep22 600168 524288 148202 rfl rfl rfl (ep36 rfl))) rfl rfl rfl rfl rfl rfl rfl rfl) rfl

theorem EMRow15.d5 : Enclosure.Real.IsNear (Real.log Real.pi) Bool.false 75021 65536 1 131072 := ep37

noncomputable abbrev qz471 := (@HAdd.hAdd Complex Complex Complex (@instHAdd Complex Complex.instAdd) (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (2 : Complex)) (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul) Complex.I ↑(Enclosure.sfrac Bool.false 63102 1000)))

noncomputable abbrev qz447 := qz471

noncomputable abbrev qz268 := qz447

noncomputable abbrev qz4 := (BSN.headSumC qz268 9)

noncomputable abbrev qz472 := (@instHAdd Complex Complex.instAdd)

noncomputable abbrev qz448 := qz472

noncomputable abbrev qz269 := qz448

noncomputable abbrev qz5 := qz269

noncomputable abbrev qz6 := qz268

noncomputable abbrev qz449 := (@instHPow Complex Complex Complex.instPow)

noncomputable abbrev qz270 := qz449

noncomputable abbrev qz450 := (@Neg.neg Complex Complex.instNeg qz471)

noncomputable abbrev qz271 := qz450

noncomputable abbrev qz7 := (@HPow.hPow Complex Complex Complex qz270 (@Nat.cast Complex Complex.instNatCast 8) qz271)

noncomputable def ep38 := @Enclosure.Complex.IsNear.of_eq qz4 (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz6 8) qz7) Bool.false 444076798561 137438953472 29933086341051 10184363891228672 Bool.false 69066327811 274877906944 59678950503421 20368727782457344

noncomputable def ep39 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz6 8) qz7 Bool.false 815733199837 274877906944 53586462992803 20368727782457344 Bool.false 1064882597 68719476736 13350571109649 5092181945614336 Bool.false

noncomputable abbrev qz8 := (@HPow.hPow Complex Complex Complex qz270 (@Nat.cast Complex Complex.instNatCast 7) qz271)

noncomputable def ep40 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz6 8) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz6 7) qz8) Bool.false 815733199837 274877906944 53586462992803 20368727782457344 Bool.false 1064882597 68719476736 13350571109649 5092181945614336

noncomputable def ep41 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz6 7) qz8 Bool.false 915905388989 274877906944 46881294331559 20368727782457344 Bool.true 23300781489 274877906944 46724268236277 20368727782457344 Bool.true

noncomputable abbrev qz9 := (@HPow.hPow Complex Complex Complex qz270 (@Nat.cast Complex Complex.instNatCast 6) qz271)

noncomputable def ep42 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz6 7) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz6 6) qz9) Bool.false 915905388989 274877906944 46881294331559 20368727782457344 Bool.true 23300781489 274877906944 46724268236277 20368727782457344

noncomputable def ep43 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz6 6) qz9 Bool.false 803751521457 274877906944 39624708731331 20368727782457344 Bool.true 27091840257 274877906944 39505198193925 20368727782457344 Bool.false

noncomputable abbrev qz10 := (@HPow.hPow Complex Complex Complex qz270 (@Nat.cast Complex Complex.instNatCast 5) qz271)

noncomputable def ep44 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz6 6) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz6 5) qz10) Bool.false 803751521457 274877906944 39624708731331 20368727782457344 Bool.true 27091840257 274877906944 39505198193925 20368727782457344

noncomputable def ep45 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz6 5) qz10 Bool.false 185054891687 68719476736 7928829041455 5092181945614336 Bool.false 78147225703 274877906944 31582624616635 20368727782457344 Bool.false

noncomputable abbrev qz11 := (@HPow.hPow Complex Complex Complex qz270 (@Nat.cast Complex Complex.instNatCast 4) qz271)

noncomputable def ep46 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz6 5) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz6 4) qz11) Bool.false 185054891687 68719476736 7928829041455 5092181945614336 Bool.false 78147225703 274877906944 31582624616635 20368727782457344

noncomputable def ep47 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz6 4) qz11 Bool.false 154687197995 68719476736 5715126585051 5092181945614336 Bool.false 6925050689 137438953472 5685994073305 5092181945614336 Bool.false

noncomputable abbrev qz451 := (@Nat.cast Complex Complex.instNatCast 3)

noncomputable abbrev qz272 := qz451

noncomputable abbrev qz12 := (@HPow.hPow Complex Complex Complex qz270 qz272 qz271)

noncomputable def ep48 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz6 4) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz6 3) qz12) Bool.false 154687197995 68719476736 5715126585051 5092181945614336 Bool.false 6925050689 137438953472 5685994073305 5092181945614336

noncomputable def ep49 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz6 3) qz12 Bool.false 1810610065 1073741824 196515546271 318261371600896 Bool.false 5855787783 34359738368 6260156145303 10184363891228672 Bool.false

noncomputable abbrev qz452 := (@Nat.cast Complex Complex.instNatCast 2)

noncomputable abbrev qz273 := qz452

noncomputable abbrev qz13 := (@HPow.hPow Complex Complex Complex qz270 qz273 qz271)

noncomputable def ep50 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz6 3) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz6 2) qz13) Bool.false 1810610065 1073741824 196515546271 318261371600896 Bool.false 5855787783 34359738368 6260156145303 10184363891228672

noncomputable def ep51 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz6 2) qz13 Bool.false 1 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable abbrev qz274 := (Enclosure.sfrac Bool.false 0 1)

noncomputable abbrev qz14 := qz274

noncomputable def ep52 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz6 2) (Complex.mk (Enclosure.sfrac Bool.false 1 1) qz14) Bool.false 1 1 0 1 Bool.false 0 1 0 1 (BSN.head_sum_c_two qz6)

noncomputable abbrev qz275 := (@Nat.cast Real Real.instNatCast 2)

noncomputable abbrev qz15 := (@Inv.inv Real Real.instInv (Real.sqrt qz275))

noncomputable abbrev qz473 := (Enclosure.sfrac Bool.false 63102 1000)

noncomputable abbrev qz453 := qz473

noncomputable abbrev qz276 := qz453

noncomputable abbrev qz16 := (@HMul.hMul Real Real Real qz263 qz276 (Real.log (Enclosure.sfrac Bool.false 2 1)))

noncomputable abbrev qz17 := qz276

noncomputable abbrev qz277 := (@Eq.refl Real qz453)

noncomputable abbrev qz18 := qz277

noncomputable def ep53 := @Enclosure.Complex.IsNear.of_eq qz13 (Complex.mk (@HMul.hMul Real Real Real qz0 qz15 (Real.cos qz16)) (@HMul.hMul Real Real Real qz0 qz15 (@Neg.neg Real Real.instNeg (Real.sin qz16)))) Bool.false 736868241 1073741824 196515546271 318261371600896 Bool.false 5855787783 34359738368 6260156145303 10184363891228672 (BSN.cpow_neg_s_mk qz17 63102 1000 2 qz18 rfl)

noncomputable abbrev qz19 := (@Nat.cast Real Real.instNatCast 1)

noncomputable def ep54 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz275) 741455 524288 1 524288 185363 185365 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz275) (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz275 qz19)) Bool.false 741455 524288 1 524288 (BSN.sqrt_natCast_div_one 2) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz275 qz19)) Bool.false 741455 524288 1 524288 741455 524288 1 524288 (BSN.sqrt_enclosure 2 1 370727 370728 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep55 := BSN.log_dyadic_bound 1 3 6 5 613814355 262144 74101 24381081 945 181704 4 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 1) (BSN.artanhQ 3) 0 5 24381081 613814355 945 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep56 := nat_lit 16603860160245459783152303032850897000930050532962770949148268451431426030625

noncomputable def ep57 := nat_lit 641153462866780105519186997069590271023477356498224607523168458325065864314880

noncomputable def ep58 := nat_lit 17028028395910085471770962296559478807919087975844060590812255700625390625

noncomputable def ep59 := nat_lit 43458731230859016436539831147081729179603977634370176387765102292138436590625

noncomputable def ep60 := nat_lit 11754480152557635267851761612942488302097084869134117804591421735959540845772800

noncomputable abbrev qz278 := (BSN.sinEvenQ 1073741824)

noncomputable abbrev qz279 := (BSN.sinOddQ 1073741824)

noncomputable def ep61 := BSN.sin_dyadic_bound_f 1425264755 1073741824 3 2 524288 148347 ep56 ep57 ep58 ep59 ep60 ep58 508832 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1425264755) qz278 0 2 ep56 ep57 ep58 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1425264755) qz279 0 2 ep59 ep60 ep58 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz20 := (@Nat.cast Real Real.instNatCast 524288)

noncomputable abbrev qz21 := (Real.log (Enclosure.sfrac Bool.false 2 1))

noncomputable abbrev qz280 := (Enclosure.Real.IsNear.const Bool.false 63102 1000)

noncomputable abbrev qz22 := qz280

noncomputable abbrev qz23 := (@Nat.cast Real Real.instNatCast 75557863725914323419136)

noncomputable abbrev qz281 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 22931771) qz20)

noncomputable abbrev qz282 := (BSN.isNear_log_sfrac 2 1 181704 262144 1 74101 Bool.false (BSN.logfrac_isNear 4 2 1 2 1 181704 262144 74101 rfl rfl rfl (ep55 rfl)))

noncomputable def ep62 := @Enclosure.Real.IsNear.cos_image qz16 qz281 Bool.false 22931771 524288 7 8192 Bool.false 508832 524288 1 74101 (@Enclosure.Real.IsNear.recentre' qz16 Bool.false 716617863 16384000 31551 37050500 22931771 524288 7 8192 (@Enclosure.Real.IsNear.mulLit_ff qz17 qz21 63102 1000 0 1 181704 262144 1 74101 716617863 16384000 31551 37050500 qz22 qz282 rfl) rfl) (Enclosure.sfrac_false_div 22931771 524288) (BSN.cos_reduce3 qz281 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 100294090946796933087232) qz23) 226375608064910080 72057594037927936 Bool.false 508832 524288 6 1000000000000000 148202 74101 (BSN.sin_reduce_arg_pos_rat_q3 22931771 524288 226375608064910080 72057594037927936 6 100294090946796933087232 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 508832 524288 100294090946796933087232 75557863725914323419136 1425264755 1073741824 148347 148202 (ep61 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep63 := nat_lit 9231934768312326584183177668160080324431325446301914554233843475551070190625

noncomputable def ep64 := nat_lit 71239273651864456168798555229954474558164150722024956391463162036118429368320

noncomputable def ep65 := nat_lit 27661748248145159581605991079887122015678138162954055541519905915251959790625

noncomputable def ep66 := nat_lit 3205767314333900527595934985347951355117386782491123037615842291625329321574400

noncomputable abbrev qz283 := (BSN.cosEvenQ 1073741824)

noncomputable abbrev qz284 := (BSN.cosOddQ 1073741824)

noncomputable def ep67 := BSN.cos_dyadic_bound_f 1425264755 1073741824 3 2 524288 148347 ep63 ep64 ep58 ep65 ep66 ep58 126363 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1425264755) qz283 0 2 ep63 ep64 ep58 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1425264755) qz284 0 2 ep65 ep66 ep58 rfl rfl rfl rfl) rfl rfl

noncomputable def ep68 := @Enclosure.Real.IsNear.sin_image qz16 qz281 Bool.false 22931771 524288 7 8192 Bool.true 126363 524288 1 74101 (@Enclosure.Real.IsNear.recentre' qz16 Bool.false 716617863 16384000 31551 37050500 22931771 524288 7 8192 (@Enclosure.Real.IsNear.mulLit_ff qz17 qz21 63102 1000 0 1 181704 262144 1 74101 716617863 16384000 31551 37050500 qz22 qz282 rfl) rfl) (Enclosure.sfrac_false_div 22931771 524288) (BSN.sin_reduce3 qz281 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 100294090946796933087232) qz23) 226375608064910080 72057594037927936 Bool.false 126363 524288 6 1000000000000000 148202 74101 (BSN.sin_reduce_arg_pos_rat_q3 22931771 524288 226375608064910080 72057594037927936 6 100294090946796933087232 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 126363 524288 100294090946796933087232 75557863725914323419136 1425264755 1073741824 148347 148202 (ep67 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz285 := (@Enclosure.Real.IsNear.recentre' qz15 Bool.false 370728 524288 2 524288 46341 65536 1 262144 (ep54 rfl rfl) rfl)

noncomputable def ep69 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz15 (Real.cos qz16)) (@HMul.hMul Real Real Real qz0 qz15 (@Neg.neg Real Real.instNeg (Real.sin qz16))) Bool.false 736868241 1073741824 196515546271 318261371600896 Bool.false 5855787783 34359738368 6260156145303 10184363891228672 (@Enclosure.Real.IsNear.mulLit_ff qz15 (Real.cos qz16) 46341 65536 1 262144 15901 16384 526899 607035392 736868241 1073741824 196515546271 318261371600896 qz285 (@Enclosure.Real.IsNear.recentre' (Real.cos qz16) Bool.false 508832 524288 526899 607035392 15901 16384 526899 607035392 (ep62 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz15 (@Neg.neg Real Real.instNeg (Real.sin qz16)) 46341 65536 1 262144 126363 524288 526899 607035392 5855787783 34359738368 6260156145303 10184363891228672 qz285 (@Enclosure.Real.IsNear.neg (Real.sin qz16) Bool.true 126363 524288 526899 607035392 (@Enclosure.Real.IsNear.recentre' (Real.sin qz16) Bool.true 126363 524288 526899 607035392 126363 524288 526899 607035392 (ep68 rfl rfl) rfl)) rfl)

noncomputable abbrev qz286 := (Enclosure.Real.IsNear.const Bool.false 0 1)

noncomputable abbrev qz24 := qz286

noncomputable def ep70 := @ep51 736868241 1073741824 196515546271 318261371600896 Bool.false 5855787783 34359738368 6260156145303 10184363891228672 Bool.false 1810610065 1810610065 1073741824 196515546271 318261371600896 Bool.false 5855787783 5855787783 34359738368 6260156145303 10184363891228672 (ep52 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 1) qz14 Bool.false 1 1 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 1) qz24)) (ep53 ep69) rfl rfl

noncomputable abbrev qz25 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 3)))

noncomputable abbrev qz26 := (@HMul.hMul Real Real Real qz263 qz276 (Real.log (Enclosure.sfrac Bool.false 3 1)))

noncomputable def ep71 := @Enclosure.Complex.IsNear.of_eq qz12 (Complex.mk (@HMul.hMul Real Real Real qz0 qz25 (Real.cos qz26)) (@HMul.hMul Real Real Real qz0 qz25 (@Neg.neg Real Real.instNeg (Real.sin qz26)))) Bool.false 38808153835 68719476736 2570877844715 5092181945614336 Bool.true 16498100443 137438953472 5111832001307 10184363891228672 (BSN.cpow_neg_s_mk qz17 63102 1000 3 qz18 rfl)

noncomputable abbrev qz27 := (@Nat.cast Real Real.instNatCast 3)

noncomputable def ep72 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz27) 908093 524288 1 524288 151348 151350 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz27) (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz27 qz19)) Bool.false 908093 524288 1 524288 (BSN.sqrt_natCast_div_one 3) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz27 qz19)) Bool.false 908093 524288 1 524288 908093 524288 1 524288 (BSN.sqrt_enclosure 3 1 454046 454047 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep73 := BSN.log_dyadic_bound 1 2 10 9 171633298636800 262144 74101 16925142283965 34459425 287994 3 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base9 (BSN.artanhP 1) (BSN.artanhQ 2) 0 9 16925142283965 171633298636800 34459425 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep74 := nat_lit 2557806765654616327153457620573761

noncomputable def ep75 := nat_lit 31901471898837980949691369446728269824

noncomputable def ep76 := nat_lit 478522078482569714245370541700924047360

noncomputable def ep77 := BSN.cos_dyadic_bound_f 224888337 1073741824 2 1 524288 148347 ep74 ep75 ep74 ep74 ep76 ep74 512830 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 224888337) qz283 0 1 ep74 ep75 ep74 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 224888337) qz284 0 1 ep74 ep76 ep74 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz28 := (@Nat.cast Real Real.instNatCast 262144)

noncomputable abbrev qz29 := (Real.log (Enclosure.sfrac Bool.false 3 1))

noncomputable abbrev qz287 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 18172997) qz28)

noncomputable abbrev qz288 := (BSN.isNear_log_sfrac 3 1 287994 262144 1 74101 Bool.false (BSN.logfrac_isNear 3 1 2 3 1 287994 262144 74101 rfl rfl rfl (ep73 rfl)))

noncomputable abbrev qz289 := (@Nat.cast Real Real.instNatCast 37778931862957161709568)

noncomputable def ep78 := @Enclosure.Real.IsNear.cos_image qz26 qz287 Bool.false 18172997 262144 7 8192 Bool.false 512830 524288 1 74101 (@Enclosure.Real.IsNear.recentre' qz26 Bool.false 4543249347 65536000 31551 37050500 18172997 262144 7 8192 (@Enclosure.Real.IsNear.mulLit_ff qz17 qz29 63102 1000 0 1 287994 262144 1 74101 4543249347 65536000 31551 37050500 qz22 qz288 rfl) rfl) (Enclosure.sfrac_false_div 18172997 262144) (BSN.cos_reduce0 qz287 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 7912554931981861781504) qz289) 226375608064910080 72057594037927936 Bool.false 512830 524288 11 1000000000000000 148202 74101 (BSN.sin_reduce_arg_pos_rat_q0 18172997 262144 226375608064910080 72057594037927936 11 7912554931981861781504 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 512830 524288 7912554931981861781504 37778931862957161709568 224888337 1073741824 148347 148202 (ep77 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep79 := nat_lit 159507359494189904748456847233641349120

noncomputable def ep80 := nat_lit 1116551516459329333239197930635489443840

noncomputable def ep81 := BSN.sin_dyadic_bound_f 224888337 1073741824 2 1 524288 148347 ep74 ep79 ep74 ep74 ep80 ep74 109007 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 224888337) qz278 0 1 ep74 ep79 ep74 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 224888337) qz279 0 1 ep74 ep80 ep74 rfl rfl rfl rfl) rfl rfl

noncomputable def ep82 := @Enclosure.Real.IsNear.sin_image qz26 qz287 Bool.false 18172997 262144 7 8192 Bool.false 109007 524288 1 74101 (@Enclosure.Real.IsNear.recentre' qz26 Bool.false 4543249347 65536000 31551 37050500 18172997 262144 7 8192 (@Enclosure.Real.IsNear.mulLit_ff qz17 qz29 63102 1000 0 1 287994 262144 1 74101 4543249347 65536000 31551 37050500 qz22 qz288 rfl) rfl) (Enclosure.sfrac_false_div 18172997 262144) (BSN.sin_reduce0 qz287 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 7912554931981861781504) qz289) 226375608064910080 72057594037927936 Bool.false 109007 524288 11 1000000000000000 148202 74101 (BSN.sin_reduce_arg_pos_rat_q0 18172997 262144 226375608064910080 72057594037927936 11 7912554931981861781504 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 109007 524288 7912554931981861781504 37778931862957161709568 224888337 1073741824 148347 148202 (ep81 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz290 := (@Enclosure.Real.IsNear.recentre' qz25 Bool.false 302698 524288 2 524288 151349 262144 1 262144 (ep72 rfl rfl) rfl)

noncomputable def ep83 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz25 (Real.cos qz26)) (@HMul.hMul Real Real Real qz0 qz25 (@Neg.neg Real Real.instNeg (Real.sin qz26))) Bool.false 38808153835 68719476736 2570877844715 5092181945614336 Bool.true 16498100443 137438953472 5111832001307 10184363891228672 (@Enclosure.Real.IsNear.mulLit_ff qz25 (Real.cos qz26) 151349 262144 1 262144 256415 262144 526899 607035392 38808153835 68719476736 2570877844715 5092181945614336 qz290 (@Enclosure.Real.IsNear.recentre' (Real.cos qz26) Bool.false 512830 524288 526899 607035392 256415 262144 526899 607035392 (ep78 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz25 (@Neg.neg Real Real.instNeg (Real.sin qz26)) 151349 262144 1 262144 109007 524288 526899 607035392 16498100443 137438953472 5111832001307 10184363891228672 qz290 (@Enclosure.Real.IsNear.neg (Real.sin qz26) Bool.false 109007 524288 526899 607035392 (@Enclosure.Real.IsNear.recentre' (Real.sin qz26) Bool.false 109007 524288 526899 607035392 109007 524288 526899 607035392 (ep82 rfl rfl) rfl)) rfl)

noncomputable def ep84 := @ep49 38808153835 68719476736 2570877844715 5092181945614336 Bool.true 16498100443 137438953472 5111832001307 10184363891228672 Bool.false 166094114124600442880 154687197995 68719476736 5715126585051 5092181945614336 Bool.false 237942929859178135552 6925050689 137438953472 5685994073305 5092181945614336 (ep50 (BSN.head_sum_c_succ qz6 2 3 rfl rfl) (ep70 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep71 ep83) rfl rfl

noncomputable abbrev qz291 := (@Nat.cast Real Real.instNatCast 4)

noncomputable abbrev qz30 := (@Inv.inv Real Real.instInv (Real.sqrt qz291))

noncomputable abbrev qz31 := (@HMul.hMul Real Real Real qz263 qz276 (Real.log (Enclosure.sfrac Bool.false 4 1)))

noncomputable def ep85 := @Enclosure.Complex.IsNear.of_eq qz11 (Complex.mk (@HMul.hMul Real Real Real qz0 qz30 (Real.cos qz31)) (@HMul.hMul Real Real Real qz0 qz30 (@Neg.neg Real Real.instNeg (Real.sin qz31)))) Bool.false 7591923423 17179869184 553425614101 1273045486403584 Bool.false 64297124325 274877906944 8838648323415 20368727782457344 (BSN.cpow_neg_s_mk qz17 63102 1000 4 qz18 rfl)

noncomputable def ep86 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz291) 1048577 524288 1 524288 131071 131072 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz291) (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz291 qz19)) Bool.false 1048577 524288 1 524288 (BSN.sqrt_natCast_div_one 4) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz291 qz19)) Bool.false 1048577 524288 1 524288 1048577 524288 1 524288 (BSN.sqrt_enclosure 4 1 524288 524289 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep87 := nat_lit 471225594319403171539306640625

noncomputable def ep88 := nat_lit 73155514365408823868279100600

noncomputable def ep89 := BSN.log_dyadic_bound 3 5 13 12 ep87 262144 74101 ep88 89313862490502916491225 363408 8 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base12 (BSN.artanhP 3) (BSN.artanhQ 5) 0 12 ep88 ep87 89313862490502916491225 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep90 := nat_lit 7379805621735208791491064702654796997033104480666855355925172516420327830625

noncomputable def ep91 := nat_lit 3367680273551482452132836338944408883532707883421351299352264110250390625

noncomputable def ep92 := nat_lit 19322609907911225387077906771928082139751458779459081839605071972541405590625

noncomputable def ep93 := BSN.sin_dyadic_bound_f 1163901845 1073741824 3 2 524288 148347 ep90 ep57 ep91 ep92 ep60 ep91 463376 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1163901845) qz278 0 2 ep90 ep57 ep91 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1163901845) qz279 0 2 ep92 ep60 ep91 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz32 := (Real.log (Enclosure.sfrac Bool.false 4 1))

noncomputable abbrev qz292 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 45863543) qz20)

noncomputable abbrev qz293 := (BSN.isNear_log_sfrac 4 1 363408 262144 1 74101 Bool.false (BSN.logfrac_isNear 8 2 1 4 1 363408 262144 74101 rfl rfl rfl (ep89 rfl)))

noncomputable def ep94 := @Enclosure.Real.IsNear.cos_image qz31 qz292 Bool.false 45863543 524288 447 524288 Bool.false 463376 524288 1 74101 (@Enclosure.Real.IsNear.recentre' qz31 Bool.false 716617863 8192000 31551 37050500 45863543 524288 447 524288 (@Enclosure.Real.IsNear.mulLit_ff qz17 qz32 63102 1000 0 1 363408 262144 1 74101 716617863 8192000 31551 37050500 qz22 qz293 rfl) rfl) (Enclosure.sfrac_false_div 45863543 524288) (BSN.cos_reduce3 qz292 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 81902311207646366007296) qz23) 226375608064910080 72057594037927936 Bool.false 463376 524288 13 1000000000000000 148202 74101 (BSN.sin_reduce_arg_pos_rat_q3 45863543 524288 226375608064910080 72057594037927936 13 81902311207646366007296 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 463376 524288 81902311207646366007296 75557863725914323419136 1163901845 1073741824 148347 148202 (ep93 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep95 := nat_lit 4101388758863361098584872762069973624522183692763106909424807959838071190625

noncomputable def ep96 := nat_lit 12297430916042980330850352613532032055799485662522478025675719351293712790625

noncomputable def ep97 := BSN.cos_dyadic_bound_f 1163901845 1073741824 3 2 524288 148347 ep95 ep64 ep91 ep96 ep66 ep91 245275 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1163901845) qz283 0 2 ep95 ep64 ep91 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1163901845) qz284 0 2 ep96 ep66 ep91 rfl rfl rfl rfl) rfl rfl

noncomputable def ep98 := @Enclosure.Real.IsNear.sin_image qz31 qz292 Bool.false 45863543 524288 447 524288 Bool.true 245275 524288 1 74101 (@Enclosure.Real.IsNear.recentre' qz31 Bool.false 716617863 8192000 31551 37050500 45863543 524288 447 524288 (@Enclosure.Real.IsNear.mulLit_ff qz17 qz32 63102 1000 0 1 363408 262144 1 74101 716617863 8192000 31551 37050500 qz22 qz293 rfl) rfl) (Enclosure.sfrac_false_div 45863543 524288) (BSN.sin_reduce3 qz292 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 81902311207646366007296) qz23) 226375608064910080 72057594037927936 Bool.false 245275 524288 13 1000000000000000 148202 74101 (BSN.sin_reduce_arg_pos_rat_q3 45863543 524288 226375608064910080 72057594037927936 13 81902311207646366007296 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 245275 524288 81902311207646366007296 75557863725914323419136 1163901845 1073741824 148347 148202 (ep97 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz294 := (@Enclosure.Real.IsNear.recentre' qz30 Bool.false 262143 524288 1 524288 262143 524288 1 524288 (ep86 rfl rfl) rfl)

noncomputable def ep99 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz30 (Real.cos qz31)) (@HMul.hMul Real Real Real qz0 qz30 (@Neg.neg Real Real.instNeg (Real.sin qz31))) Bool.false 7591923423 17179869184 553425614101 1273045486403584 Bool.false 64297124325 274877906944 8838648323415 20368727782457344 (@Enclosure.Real.IsNear.mulLit_ff qz30 (Real.cos qz31) 262143 524288 1 524288 28961 32768 33647435 38850265088 7591923423 17179869184 553425614101 1273045486403584 qz294 (@Enclosure.Real.IsNear.recentre' (Real.cos qz31) Bool.false 463376 524288 33647435 38850265088 28961 32768 33647435 38850265088 (ep94 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz30 (@Neg.neg Real Real.instNeg (Real.sin qz31)) 262143 524288 1 524288 245275 524288 33647435 38850265088 64297124325 274877906944 8838648323415 20368727782457344 qz294 (@Enclosure.Real.IsNear.neg (Real.sin qz31) Bool.true 245275 524288 33647435 38850265088 (@Enclosure.Real.IsNear.recentre' (Real.sin qz31) Bool.true 245275 524288 33647435 38850265088 245275 524288 33647435 38850265088 (ep98 rfl rfl) rfl)) rfl)

noncomputable def ep100 := @ep47 7591923423 17179869184 553425614101 1273045486403584 Bool.false 64297124325 274877906944 8838648323415 20368727782457344 Bool.false 3179218831041949073408 185054891687 68719476736 7928829041455 5092181945614336 Bool.false 10740472917360499490816 78147225703 274877906944 31582624616635 20368727782457344 (ep48 (BSN.head_sum_c_succ qz6 3 4 rfl rfl) (ep84 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep85 ep99) rfl rfl

noncomputable abbrev qz295 := (@Nat.cast Real Real.instNatCast 5)

noncomputable abbrev qz33 := (@Inv.inv Real Real.instInv (Real.sqrt qz295))

noncomputable abbrev qz34 := (@HMul.hMul Real Real Real qz263 qz276 (Real.log (Enclosure.sfrac Bool.false 5 1)))

noncomputable def ep101 := @Enclosure.Complex.IsNear.of_eq qz10 (Complex.mk (@HMul.hMul Real Real Real qz0 qz33 (Real.cos qz34)) (@HMul.hMul Real Real Real qz0 qz33 (@Neg.neg Real Real.instNeg (Real.sin qz34)))) Bool.false 63531954709 274877906944 7909392565511 20368727782457344 Bool.true 13154883245 34359738368 3961286788645 10184363891228672 (BSN.cpow_neg_s_mk qz17 63102 1000 5 qz18 rfl)

noncomputable def ep102 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz295) 1172343 524288 1 524288 117234 117235 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz295) (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz295 qz19)) Bool.false 1172343 524288 1 524288 (BSN.sqrt_natCast_div_one 5) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz295 qz19)) Bool.false 1172343 524288 1 524288 1172343 524288 1 524288 (BSN.sqrt_enclosure 5 1 586171 586172 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep103 := nat_lit 39510257877627786146545168145625

noncomputable def ep104 := nat_lit 8181717556663416291180905432700

noncomputable def ep105 := nat_lit 6646766139202842132480000

noncomputable def ep106 := BSN.log_dyadic_bound 2 3 16 15 ep103 262144 74101 ep104 ep105 421904 5 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base15 (BSN.artanhP 2) (BSN.artanhQ 3) 0 15 ep104 ep103 ep105 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep107 := nat_lit 3312882890090255345374533006423101926841638059865493535488172949839042916321

noncomputable def ep108 := nat_lit 2197951895697963042772670880120737311524433738884458752028008230674051041

noncomputable def ep109 := nat_lit 9934252766479370110038053677509064305901865312118711688960462833055780646881

noncomputable def ep110 := BSN.cos_dyadic_bound_f 1103449019 1073741824 3 2 524288 148347 ep107 ep64 ep108 ep109 ep66 ep108 270961 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1103449019) qz283 0 2 ep107 ep64 ep108 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1103449019) qz284 0 2 ep109 ep66 ep108 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz35 := (Real.log (Enclosure.sfrac Bool.false 5 1))

noncomputable abbrev qz296 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 13311493) (@Nat.cast Real Real.instNatCast 131072))

noncomputable abbrev qz297 := (BSN.isNear_log_sfrac 5 1 421904 262144 1 74101 Bool.false (BSN.logfrac_isNear 5 1 2 5 1 421904 262144 74101 rfl rfl rfl (ep106 rfl)))

noncomputable abbrev qz298 := (@Nat.cast Real Real.instNatCast 18889465931478580854784)

noncomputable def ep111 := @Enclosure.Real.IsNear.cos_image qz34 qz296 Bool.false 13311493 131072 447 524288 Bool.false 270961 524288 1 74101 (@Enclosure.Real.IsNear.recentre' qz34 Bool.false 831968319 8192000 31551 37050500 13311493 131072 447 524288 (@Enclosure.Real.IsNear.mulLit_ff qz17 qz35 63102 1000 0 1 421904 262144 1 74101 831968319 8192000 31551 37050500 qz22 qz297 rfl) rfl) (Enclosure.sfrac_false_div 13311493 131072) (BSN.cos_reduce0 qz296 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 19412080447269692768256) qz298) 226375608064910080 72057594037927936 Bool.false 270961 524288 16 1000000000000000 148202 74101 (BSN.sin_reduce_arg_pos_rat_q0 13311493 131072 226375608064910080 72057594037927936 16 19412080447269692768256 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 270961 524288 19412080447269692768256 18889465931478580854784 1103449019 1073741824 148347 148202 (ep110 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep112 := nat_lit 5961430840645901251239941274857486878465728960766780796877088903125738008545

noncomputable def ep113 := nat_lit 15609712660527182765463928538439889202239202956907184391936711304384412987361

noncomputable def ep114 := BSN.sin_dyadic_bound_f 1103449019 1073741824 3 2 524288 148347 ep112 ep57 ep108 ep113 ep60 ep108 448840 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1103449019) qz278 0 2 ep112 ep57 ep108 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1103449019) qz279 0 2 ep113 ep60 ep108 rfl rfl rfl rfl) rfl rfl

noncomputable def ep115 := @Enclosure.Real.IsNear.sin_image qz34 qz296 Bool.false 13311493 131072 447 524288 Bool.false 448840 524288 1 74101 (@Enclosure.Real.IsNear.recentre' qz34 Bool.false 831968319 8192000 31551 37050500 13311493 131072 447 524288 (@Enclosure.Real.IsNear.mulLit_ff qz17 qz35 63102 1000 0 1 421904 262144 1 74101 831968319 8192000 31551 37050500 qz22 qz297 rfl) rfl) (Enclosure.sfrac_false_div 13311493 131072) (BSN.sin_reduce0 qz296 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 19412080447269692768256) qz298) 226375608064910080 72057594037927936 Bool.false 448840 524288 16 1000000000000000 148202 74101 (BSN.sin_reduce_arg_pos_rat_q0 13311493 131072 226375608064910080 72057594037927936 16 19412080447269692768256 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 448840 524288 19412080447269692768256 18889465931478580854784 1103449019 1073741824 148347 148202 (ep114 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz299 := (@Enclosure.Real.IsNear.recentre' qz33 Bool.false 234469 524288 1 524288 234469 524288 1 524288 (ep102 rfl rfl) rfl)

noncomputable def ep116 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz33 (Real.cos qz34)) (@HMul.hMul Real Real Real qz0 qz33 (@Neg.neg Real Real.instNeg (Real.sin qz34))) Bool.false 63531954709 274877906944 7909392565511 20368727782457344 Bool.true 13154883245 34359738368 3961286788645 10184363891228672 (@Enclosure.Real.IsNear.mulLit_ff qz33 (Real.cos qz34) 234469 524288 1 524288 270961 524288 33647435 38850265088 63531954709 274877906944 7909392565511 20368727782457344 qz299 (@Enclosure.Real.IsNear.recentre' (Real.cos qz34) Bool.false 270961 524288 33647435 38850265088 270961 524288 33647435 38850265088 (ep111 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz33 (@Neg.neg Real Real.instNeg (Real.sin qz34)) 234469 524288 1 524288 56105 65536 33647435 38850265088 13154883245 34359738368 3961286788645 10184363891228672 qz299 (@Enclosure.Real.IsNear.neg (Real.sin qz34) Bool.false 56105 65536 33647435 38850265088 (@Enclosure.Real.IsNear.recentre' (Real.sin qz34) Bool.false 448840 524288 33647435 38850265088 56105 65536 33647435 38850265088 (ep115 rfl rfl) rfl)) rfl)

noncomputable def ep117 := @ep45 63531954709 274877906944 7909392565511 20368727782457344 Bool.true 13154883245 34359738368 3961286788645 10184363891228672 Bool.false 55233383980288916324352 803751521457 274877906944 39624708731331 20368727782457344 Bool.true 930868543138169880576 27091840257 274877906944 39505198193925 20368727782457344 (ep46 (BSN.head_sum_c_succ qz6 4 5 rfl rfl) (ep100 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep101 ep116) rfl rfl

noncomputable abbrev qz300 := (@Nat.cast Real Real.instNatCast 6)

noncomputable abbrev qz36 := (@Inv.inv Real Real.instInv (Real.sqrt qz300))

noncomputable abbrev qz37 := (@HMul.hMul Real Real Real qz263 qz276 (Real.log (Enclosure.sfrac Bool.false 6 1)))

noncomputable def ep118 := @Enclosure.Complex.IsNear.of_eq qz9 (Complex.mk (@HMul.hMul Real Real Real qz0 qz36 (Real.cos qz37)) (@HMul.hMul Real Real Real qz0 qz36 (@Neg.neg Real Real.instNeg (Real.sin qz37)))) Bool.false 28038466883 68719476736 1814146400057 5092181945614336 Bool.false 236941173 17179869184 451191877647 1273045486403584 (BSN.cpow_neg_s_mk qz17 63102 1000 6 qz18 rfl)

noncomputable abbrev qz301 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 6) qz19)

noncomputable def ep119 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz300) 1284239 524288 1 524288 107019 107020 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz300) (Real.sqrt qz301) Bool.false 1284239 524288 1 524288 (BSN.sqrt_natCast_div_one 6) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz301) Bool.false 1284239 524288 1 524288 1284239 524288 1 524288 (BSN.sqrt_enclosure 6 1 642119 642120 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep120 := BSN.log_dyadic_bound 2 10 4 3 105000000 262144 74101 1434560 960 106290 12 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 2) (BSN.artanhQ 10) 0 3 1434560 105000000 960 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz38 := (Real.log (Enclosure.sfrac Bool.false 6 1))

noncomputable def ep121 := @Enclosure.Real.IsNear.mulLit_ff qz17 qz38 63102 1000 0 1 4034681531866359 2251799813685248 500000000074101 37050500000000000000 127298237011915492809 1125899906842624000 15775500002337960651 18525250000000000000000 qz22 (BSN.isNear_log_sfrac 6 1 4034681531866359 2251799813685248 500000000074101 37050500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz301) Bool.false 16922680887833197019136 9444732965739290427392 1000000000148202 74101000000000000000 4034681531866359 2251799813685248 500000000074101 37050500000000000000 (BSN.log_rat_reduce_isNear 6 1 2 12 8 106290 262144 24973259072661432 36028797018963968 74101 1000000000000000 rfl rfl rfl rfl (ep120 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep122 := nat_lit 29873340476682617294687916450348601908426217341642636849967883881149265674240

noncomputable def ep123 := nat_lit 55030507386249038690218617791893204890247665524162428949264643291160313856

noncomputable def ep124 := nat_lit 78150604236495784947255617703059463618913025388691595436378981694824293400576

noncomputable def ep125 := BSN.sin_dyadic_bound_f 1650347652 1073741824 3 2 524288 148347 ep122 ep57 ep123 ep124 ep60 ep123 523988 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1650347652) qz278 0 2 ep122 ep57 ep123 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1650347652) qz279 0 2 ep124 ep60 ep123 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz302 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 14819465) (@Nat.cast Real Real.instNatCast 131072))

noncomputable def ep126 := @Enclosure.Real.IsNear.cos_image qz37 qz302 Bool.false 14819465 131072 7 8192 Bool.false 523988 524288 1 74101 (@Enclosure.Real.IsNear.recentre' qz37 Bool.false 127298237011915492809 1125899906842624000 15775500002337960651 18525250000000000000000 14819465 131072 7 8192 (ep121 rfl) rfl) (Enclosure.sfrac_false_div 14819465 131072) (BSN.cos_reduce3 qz302 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 29033222938406965739520) qz298) 226375608064910080 72057594037927936 Bool.false 523988 524288 17 1000000000000000 148202 74101 (BSN.sin_reduce_arg_pos_rat_q3 14819465 131072 226375608064910080 72057594037927936 17 29033222938406965739520 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 523988 524288 29033222938406965739520 18889465931478580854784 1650347652 1073741824 148347 148202 (ep125 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep127 := nat_lit 16620758268106453625355606302545620262410230818923314885070719775434552180736

noncomputable def ep128 := nat_lit 49752213789546862798686381672053074377450197125721619797313630039721335914496

noncomputable def ep129 := BSN.cos_dyadic_bound_f 1650347652 1073741824 3 2 524288 148347 ep127 ep64 ep123 ep128 ep66 ep123 17712 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1650347652) qz283 0 2 ep127 ep64 ep123 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1650347652) qz284 0 2 ep128 ep66 ep123 rfl rfl rfl rfl) rfl rfl

noncomputable def ep130 := @Enclosure.Real.IsNear.sin_image qz37 qz302 Bool.false 14819465 131072 7 8192 Bool.true 17712 524288 1 74101 (@Enclosure.Real.IsNear.recentre' qz37 Bool.false 127298237011915492809 1125899906842624000 15775500002337960651 18525250000000000000000 14819465 131072 7 8192 (ep121 rfl) rfl) (Enclosure.sfrac_false_div 14819465 131072) (BSN.sin_reduce3 qz302 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 29033222938406965739520) qz298) 226375608064910080 72057594037927936 Bool.false 17712 524288 17 1000000000000000 148202 74101 (BSN.sin_reduce_arg_pos_rat_q3 14819465 131072 226375608064910080 72057594037927936 17 29033222938406965739520 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 17712 524288 29033222938406965739520 18889465931478580854784 1650347652 1073741824 148347 148202 (ep129 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz303 := (@Enclosure.Real.IsNear.recentre' qz36 Bool.false 214039 524288 1 524288 214039 524288 1 524288 (ep119 rfl rfl) rfl)

noncomputable def ep131 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz36 (Real.cos qz37)) (@HMul.hMul Real Real Real qz0 qz36 (@Neg.neg Real Real.instNeg (Real.sin qz37))) Bool.false 28038466883 68719476736 1814146400057 5092181945614336 Bool.false 236941173 17179869184 451191877647 1273045486403584 (@Enclosure.Real.IsNear.mulLit_ff qz36 (Real.cos qz37) 214039 524288 1 524288 130997 131072 526899 607035392 28038466883 68719476736 1814146400057 5092181945614336 qz303 (@Enclosure.Real.IsNear.recentre' (Real.cos qz37) Bool.false 523988 524288 526899 607035392 130997 131072 526899 607035392 (ep126 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz36 (@Neg.neg Real Real.instNeg (Real.sin qz37)) 214039 524288 1 524288 1107 32768 526899 607035392 236941173 17179869184 451191877647 1273045486403584 qz303 (@Enclosure.Real.IsNear.neg (Real.sin qz37) Bool.true 1107 32768 526899 607035392 (@Enclosure.Real.IsNear.recentre' (Real.sin qz37) Bool.true 17712 524288 526899 607035392 1107 32768 526899 607035392 (ep130 rfl rfl) rfl)) rfl)

noncomputable def ep132 := @ep43 28038466883 68719476736 1814146400057 5092181945614336 Bool.false 236941173 17179869184 451191877647 1273045486403584 Bool.false 62940539071006616059904 915905388989 274877906944 46881294331559 20368727782457344 Bool.true 400304377865988734976 23300781489 274877906944 46724268236277 20368727782457344 (ep44 (BSN.head_sum_c_succ qz6 5 6 rfl rfl) (ep117 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep118 ep131) rfl rfl

noncomputable abbrev qz304 := (@Nat.cast Real Real.instNatCast 7)

noncomputable abbrev qz39 := (@Inv.inv Real Real.instInv (Real.sqrt qz304))

noncomputable abbrev qz40 := (@HMul.hMul Real Real Real qz263 qz276 (Real.log (Enclosure.sfrac Bool.false 7 1)))

noncomputable def ep133 := @Enclosure.Complex.IsNear.of_eq qz8 (Complex.mk (@HMul.hMul Real Real Real qz0 qz39 (Real.cos qz40)) (@HMul.hMul Real Real Real qz0 qz39 (@Neg.neg Real Real.instNeg (Real.sin qz40)))) Bool.true 3130380911 8589934592 1676292165311 5092181945614336 Bool.false 27560311877 274877906944 6678016202319 20368727782457344 (BSN.cpow_neg_s_mk qz17 63102 1000 7 qz18 rfl)

noncomputable abbrev qz305 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 7) qz19)

noncomputable def ep134 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz304) 1387135 524288 1 524288 99081 99082 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz304) (Real.sqrt qz305) Bool.false 1387135 524288 1 524288 (BSN.sqrt_natCast_div_one 7) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz305) Bool.false 1387135 524288 1 524288 1387135 524288 1 524288 (BSN.sqrt_enclosure 7 1 693567 693568 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep135 := BSN.log_dyadic_bound 3 11 5 4 202569142545 262144 74101 5259111624 688905 146699 14 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 3) (BSN.artanhQ 11) 0 4 5259111624 202569142545 688905 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz41 := (Real.log (Enclosure.sfrac Bool.false 7 1))

noncomputable def ep136 := @Enclosure.Real.IsNear.mulLit_ff qz17 qz41 63102 1000 0 1 4381792198794487 2251799813685248 500000000074101 37050500000000000000 138249925664164859337 1125899906842624000 15775500002337960651 18525250000000000000000 qz22 (BSN.isNear_log_sfrac 7 1 4381792198794487 2251799813685248 500000000074101 37050500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz305) Bool.false 18378568546572512002048 9444732965739290427392 1000000000148202 74101000000000000000 4381792198794487 2251799813685248 500000000074101 37050500000000000000 (BSN.log_rat_reduce_isNear 7 1 2 14 8 146699 262144 24973259072661432 36028797018963968 74101 1000000000000000 rfl rfl rfl rfl (ep135 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep137 := nat_lit 6906980142854546623802231400960256

noncomputable def ep138 := BSN.cos_dyadic_bound_f 288285004 1073741824 2 1 524288 148347 ep137 ep75 ep137 ep137 ep76 ep137 505504 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 288285004) qz283 0 1 ep137 ep75 ep137 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 288285004) qz284 0 1 ep137 ep76 ep137 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz306 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 32188819) qz28)

noncomputable def ep139 := @Enclosure.Real.IsNear.cos_image qz40 qz306 Bool.false 32188819 262144 447 524288 Bool.true 505504 524288 1 74101 (@Enclosure.Real.IsNear.recentre' qz40 Bool.false 138249925664164859337 1125899906842624000 15775500002337960651 18525250000000000000000 32188819 262144 447 524288 (ep136 rfl) rfl) (Enclosure.sfrac_false_div 32188819 262144) (BSN.cos_reduce2 qz306 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 10143126880395468996608) qz289) 226375608064910080 72057594037927936 Bool.false 505504 524288 19 1000000000000000 148202 74101 (BSN.sin_reduce_arg_pos_rat_q2 32188819 262144 226375608064910080 72057594037927936 19 10143126880395468996608 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 505504 524288 10143126880395468996608 37778931862957161709568 288285004 1073741824 148347 148202 (ep138 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep140 := BSN.sin_dyadic_bound_f 288285004 1073741824 2 1 524288 148347 ep137 ep79 ep137 ep137 ep80 ep137 139079 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 288285004) qz278 0 1 ep137 ep79 ep137 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 288285004) qz279 0 1 ep137 ep80 ep137 rfl rfl rfl rfl) rfl rfl

noncomputable def ep141 := @Enclosure.Real.IsNear.sin_image qz40 qz306 Bool.false 32188819 262144 447 524288 Bool.true 139079 524288 1 74101 (@Enclosure.Real.IsNear.recentre' qz40 Bool.false 138249925664164859337 1125899906842624000 15775500002337960651 18525250000000000000000 32188819 262144 447 524288 (ep136 rfl) rfl) (Enclosure.sfrac_false_div 32188819 262144) (BSN.sin_reduce2 qz306 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 10143126880395468996608) qz289) 226375608064910080 72057594037927936 Bool.false 139079 524288 19 1000000000000000 148202 74101 (BSN.sin_reduce_arg_pos_rat_q2 32188819 262144 226375608064910080 72057594037927936 19 10143126880395468996608 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 139079 524288 10143126880395468996608 37778931862957161709568 288285004 1073741824 148347 148202 (ep140 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz307 := (@Enclosure.Real.IsNear.recentre' qz39 Bool.false 198163 524288 1 524288 198163 524288 1 524288 (ep134 rfl rfl) rfl)

noncomputable def ep142 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz39 (Real.cos qz40)) (@HMul.hMul Real Real Real qz0 qz39 (@Neg.neg Real Real.instNeg (Real.sin qz40))) Bool.true 3130380911 8589934592 1676292165311 5092181945614336 Bool.false 27560311877 274877906944 6678016202319 20368727782457344 (@Enclosure.Real.IsNear.mulLit_ft qz39 (Real.cos qz40) 198163 524288 1 524288 15797 16384 33647435 38850265088 3130380911 8589934592 1676292165311 5092181945614336 qz307 (@Enclosure.Real.IsNear.recentre' (Real.cos qz40) Bool.true 505504 524288 33647435 38850265088 15797 16384 33647435 38850265088 (ep139 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz39 (@Neg.neg Real Real.instNeg (Real.sin qz40)) 198163 524288 1 524288 139079 524288 33647435 38850265088 27560311877 274877906944 6678016202319 20368727782457344 qz307 (@Enclosure.Real.IsNear.neg (Real.sin qz40) Bool.true 139079 524288 33647435 38850265088 (@Enclosure.Real.IsNear.recentre' (Real.sin qz40) Bool.true 139079 524288 33647435 38850265088 139079 524288 33647435 38850265088 (ep141 rfl rfl) rfl)) rfl)

noncomputable def ep143 := @ep41 3130380911 8589934592 1676292165311 5092181945614336 Bool.false 27560311877 274877906944 6678016202319 20368727782457344 Bool.false 7007094831122695061504 815733199837 274877906944 53586462992803 20368727782457344 Bool.false 1170850797617804214272 1064882597 68719476736 13350571109649 5092181945614336 (ep42 (BSN.head_sum_c_succ qz6 6 7 rfl rfl) (ep132 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep133 ep142) rfl rfl

noncomputable abbrev qz308 := (@Nat.cast Real Real.instNatCast 8)

noncomputable abbrev qz42 := (@Inv.inv Real Real.instInv (Real.sqrt qz308))

noncomputable abbrev qz43 := (@HMul.hMul Real Real Real qz263 qz276 (Real.log (Enclosure.sfrac Bool.false 8 1)))

noncomputable def ep144 := @Enclosure.Complex.IsNear.of_eq qz7 (Complex.mk (@HMul.hMul Real Real Real qz0 qz42 (Real.cos qz43)) (@HMul.hMul Real Real Real qz0 qz42 (@Neg.neg Real Real.instNeg (Real.sin qz43)))) Bool.false 72420397285 274877906944 6279709689299 20368727782457344 Bool.false 64806797423 274877906944 6276666064825 20368727782457344 (BSN.cpow_neg_s_mk qz17 63102 1000 8 qz18 rfl)

noncomputable abbrev qz309 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 8) qz19)

noncomputable def ep145 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz308) 1482911 524288 1 524288 92681 92682 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz308) (Real.sqrt qz309) Bool.false 1482911 524288 1 524288 (BSN.sqrt_natCast_div_one 8) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz309) Bool.false 1482911 524288 1 524288 1482911 524288 1 524288 (BSN.sqrt_enclosure 8 1 741455 741456 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep146 := BSN.log_dyadic_bound 0 16 1 0 1 262144 74101 0 1 0 16 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 0) (BSN.artanhQ 16) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz44 := (Real.log (Enclosure.sfrac Bool.false 8 1))

noncomputable def ep147 := @Enclosure.Real.IsNear.mulLit_ff qz17 qz44 63102 1000 0 1 9364972152248037 4503599627370496 1000000000222303 74101000000000000000 295474236375577815387 2251799813685248000 31551000007013881953 37050500000000000000000 qz22 (BSN.isNear_log_sfrac 8 1 9364972152248037 4503599627370496 1000000000222303 74101000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz309) Bool.false 19639770079031275290624 9444732965739290427392 1000000000222303 74101000000000000000 9364972152248037 4503599627370496 1000000000222303 74101000000000000000 (BSN.log_rat_reduce_isNear 8 1 3 16 16 0 262144 24973259072661432 36028797018963968 74101 1000000000000000 rfl rfl rfl rfl (ep146 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep148 := nat_lit 664384523502772491396309738715051681

noncomputable def ep149 := BSN.sin_dyadic_bound_f 902827703 1073741824 2 1 524288 148347 ep148 ep79 ep148 ep148 ep80 ep148 390695 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 902827703) qz278 0 1 ep148 ep79 ep148 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 902827703) qz279 0 1 ep148 ep80 ep148 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz310 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 1074929) (@Nat.cast Real Real.instNatCast 8192))

noncomputable def ep150 := @Enclosure.Real.IsNear.cos_image qz43 qz310 Bool.false 1074929 8192 7 8192 Bool.false 390695 524288 1 74101 (@Enclosure.Real.IsNear.recentre' qz43 Bool.false 295474236375577815387 2251799813685248000 31551000007013881953 37050500000000000000000 1074929 8192 7 8192 (ep147 rfl) rfl) (Enclosure.sfrac_false_div 1074929 8192) (BSN.cos_reduce3 qz310 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 992669557968976478208) (@Nat.cast Real Real.instNatCast 1180591620717411303424)) 226375608064910080 72057594037927936 Bool.false 390695 524288 20 1000000000000000 148202 74101 (BSN.sin_reduce_arg_pos_rat_q3 1074929 8192 226375608064910080 72057594037927936 20 992669557968976478208 1180591620717411303424 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 390695 524288 992669557968976478208 1180591620717411303424 902827703 1073741824 148347 148202 (ep149 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep151 := nat_lit 1484080501253329117386235119597095596686058299259164718920466916053595115841

noncomputable def ep152 := nat_lit 441406795070006053000497877537760838242779080700607275218438062500925761

noncomputable def ep153 := nat_lit 4451358690169847340052704363036211268381689339616092942210963872035783496001

noncomputable def ep154 := BSN.cos_dyadic_bound_f 902827703 1073741824 3 2 524288 148347 ep151 ep64 ep152 ep153 ep66 ep152 349621 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 902827703) qz283 0 2 ep151 ep64 ep152 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 902827703) qz284 0 2 ep153 ep66 ep152 rfl rfl rfl rfl) rfl rfl

noncomputable def ep155 := @Enclosure.Real.IsNear.sin_image qz43 qz310 Bool.false 1074929 8192 7 8192 Bool.true 349621 524288 1 74101 (@Enclosure.Real.IsNear.recentre' qz43 Bool.false 295474236375577815387 2251799813685248000 31551000007013881953 37050500000000000000000 1074929 8192 7 8192 (ep147 rfl) rfl) (Enclosure.sfrac_false_div 1074929 8192) (BSN.sin_reduce3 qz310 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 992669557968976478208) (@Nat.cast Real Real.instNatCast 1180591620717411303424)) 226375608064910080 72057594037927936 Bool.false 349621 524288 20 1000000000000000 148202 74101 (BSN.sin_reduce_arg_pos_rat_q3 1074929 8192 226375608064910080 72057594037927936 20 992669557968976478208 1180591620717411303424 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 349621 524288 992669557968976478208 1180591620717411303424 902827703 1073741824 148347 148202 (ep154 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz311 := (@Enclosure.Real.IsNear.recentre' qz42 Bool.false 185363 524288 1 524288 185363 524288 1 524288 (ep145 rfl rfl) rfl)

noncomputable def ep156 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz42 (Real.cos qz43)) (@HMul.hMul Real Real Real qz0 qz42 (@Neg.neg Real Real.instNeg (Real.sin qz43))) Bool.false 72420397285 274877906944 6279709689299 20368727782457344 Bool.false 64806797423 274877906944 6276666064825 20368727782457344 (@Enclosure.Real.IsNear.mulLit_ff qz42 (Real.cos qz43) 185363 524288 1 524288 390695 524288 526899 607035392 72420397285 274877906944 6279709689299 20368727782457344 qz311 (@Enclosure.Real.IsNear.recentre' (Real.cos qz43) Bool.false 390695 524288 526899 607035392 390695 524288 526899 607035392 (ep150 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz42 (@Neg.neg Real Real.instNeg (Real.sin qz43)) 185363 524288 1 524288 349621 524288 526899 607035392 64806797423 274877906944 6276666064825 20368727782457344 qz311 (@Enclosure.Real.IsNear.neg (Real.sin qz43) Bool.true 349621 524288 526899 607035392 (@Enclosure.Real.IsNear.recentre' (Real.sin qz43) Bool.true 349621 524288 526899 607035392 349621 524288 526899 607035392 (ep155 rfl rfl) rfl)) rfl)

noncomputable def ep157 := @ep39 72420397285 274877906944 6279709689299 20368727782457344 Bool.false 64806797423 274877906944 6276666064825 20368727782457344 Bool.false 244133801821679982215168 444076798561 137438953472 29933086341051 10184363891228672 Bool.false 4746201907248964304896 69066327811 274877906944 59678950503421 20368727782457344 (ep40 (BSN.head_sum_c_succ qz6 7 8 rfl rfl) (ep143 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep144 ep156) rfl rfl

theorem EMRow15.d6 : Enclosure.Complex.IsNear qz4 Bool.false 444076798561 137438953472 29933086341051 10184363891228672 Bool.false 69066327811 274877906944 59678950503421 20368727782457344 := ep38 (BSN.head_sum_c_succ qz6 8 9 rfl rfl) (ep157 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

theorem EMRow15.d7 : @Eq Nat (BSN.factNat (Nat.mul 2 1)) 2 := @Eq.refl Nat 2

theorem EMRow15.d8 : @Eq Nat (Nat.pow 13 1) 13 := @Eq.refl Nat 13

noncomputable def ep158 := nat_lit 7932318250701209628996677964749

noncomputable def ep159 := nat_lit 1865119353635390322624167936000

noncomputable def ep160 := nat_lit 179875441443908607644222817288150708023

noncomputable def ep161 := nat_lit 30723877232064196967547632306941329408000

noncomputable abbrev qz474 := (@instHMul Complex Complex.instMul)

noncomputable abbrev qz454 := qz474

noncomputable abbrev qz312 := qz454

noncomputable abbrev qz45 := qz312

noncomputable abbrev qz46 := (@instHSub Real Real.instSub)

noncomputable abbrev qz455 := (@instHSub Complex Complex.instSub)

noncomputable abbrev qz313 := qz455

noncomputable abbrev qz47 := qz313

noncomputable abbrev qz475 := (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (4 : Complex))

noncomputable abbrev qz476 := (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid))

noncomputable abbrev qz456 := (@HAdd.hAdd Complex Complex Complex qz472 (@HAdd.hAdd Complex Complex Complex qz472 qz475 (@HMul.hMul Complex Complex Complex qz474 Complex.I (@HDiv.hDiv Complex Complex Complex qz476 (↑qz473) (2 : Complex)))) (@Nat.cast Complex Complex.instNatCast 2))

noncomputable abbrev qz314 := qz456

noncomputable abbrev qz48 := (Complex.Stirling.logGammaStirling 1 qz314)

noncomputable abbrev qz457 := (@HAdd.hAdd Complex Complex Complex qz472 qz475 (@HMul.hMul Complex Complex Complex qz474 Complex.I (@HDiv.hDiv Complex Complex Complex qz476 (↑qz473) (2 : Complex))))

noncomputable abbrev qz315 := qz457

noncomputable abbrev qz49 := qz315

noncomputable abbrev qz50 := (@HMul.hMul Real Real Real qz263 (@HDiv.hDiv Real Real Real qz266 qz276 (2 : Real)) (Real.log Real.pi))

noncomputable def ep162 := Complex.re (@HMul.hMul Complex Complex Complex qz45 (Complex.exp (@HMul.hMul Complex Complex Complex qz45 Complex.I ↑(@HSub.hSub Real Real Real qz46 (Complex.im (@HSub.hSub Complex Complex Complex qz47 qz48 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz49 (@Nat.cast Complex Complex.instNatCast j))))) qz50))) (zetaApproximant qz6 1 13))

noncomputable def ep163 := @Enclosure.Real.IsNear.of_eq ep162 (@HSub.hSub Real Real Real qz46 (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz46 (Complex.im (@HSub.hSub Complex Complex Complex qz47 qz48 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz49 (@Nat.cast Complex Complex.instNatCast j))))) qz50)) (Complex.re (zetaApproximant qz6 1 13))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz46 (Complex.im (@HSub.hSub Complex Complex Complex qz47 qz48 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz49 (@Nat.cast Complex Complex.instNatCast j))))) qz50)) (Complex.im (zetaApproximant qz6 1 13))))

noncomputable def ep164 := nat_lit 23796925102074981678258610766429

noncomputable def ep165 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz46 (Complex.im (@HSub.hSub Complex Complex Complex qz47 qz48 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz49 (@Nat.cast Complex Complex.instNatCast j))))) qz50)) (Complex.re (zetaApproximant qz6 1 13))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz46 (Complex.im (@HSub.hSub Complex Complex Complex qz47 qz48 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz49 (@Nat.cast Complex Complex.instNatCast j))))) qz50)) (Complex.im (zetaApproximant qz6 1 13))) ep164

noncomputable def ep166 := nat_lit 5595358060906170967872503808000

noncomputable def ep167 := nat_lit 179387869925364407462494615581686807251

noncomputable def ep168 := nat_lit 14825014323604365711563909

noncomputable def ep169 := nat_lit 2797679030453085483936251904000

noncomputable def ep170 := nat_lit 121892879636050045432050426615975193

noncomputable def ep171 := nat_lit 7680969308016049241886908076735332352000

noncomputable def ep172 := nat_lit 66576241298601225684100219801297572014325092978814288396288000

noncomputable def ep173 := @Enclosure.Real.IsNear.mulLit_tf (Real.cos (@HSub.hSub Real Real Real qz46 (Complex.im (@HSub.hSub Complex Complex Complex qz47 qz48 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz49 (@Nat.cast Complex Complex.instNatCast j))))) qz50)) (Complex.re (zetaApproximant qz6 1 13)) 524287 524288 3762021

noncomputable def ep174 := nat_lit 45389119131458498261941667

noncomputable def ep175 := nat_lit 10672298547565786300416000

noncomputable def ep176 := nat_lit 3313383926888002881028963513

noncomputable def ep177 := nat_lit 790827994673172330647126016000

noncomputable def ep178 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HSub.hSub Real Real Real qz46 (Complex.im (@HSub.hSub Complex Complex Complex qz47 qz48 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz49 (@Nat.cast Complex Complex.instNatCast j))))) qz50)) Bool.true 524287 524288 3762021

noncomputable abbrev qz316 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 21412371) qz20)

noncomputable def ep179 := @Enclosure.Real.IsNear.cos_image (@HSub.hSub Real Real Real qz46 (Complex.im (@HSub.hSub Complex Complex Complex qz47 qz48 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz49 (@Nat.cast Complex Complex.instNatCast j))))) qz50) qz316 Bool.false 21412371 524288 49

noncomputable def ep180 := nat_lit 1808815693164204871840837

noncomputable def ep181 := nat_lit 4856283136000000000000000000

noncomputable def ep182 := @Enclosure.Real.IsNear.recentre' (@HSub.hSub Real Real Real qz46 (Complex.im (@HSub.hSub Complex Complex Complex qz47 qz48 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz49 (@Nat.cast Complex Complex.instNatCast j))))) qz50) Bool.false 367861740463828707633 9007199254740992000 ep180 ep181

noncomputable def ep183 := @Enclosure.Real.IsNear.subLit_ff_p (Complex.im (@HSub.hSub Complex Complex Complex qz47 qz48 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz49 (@Nat.cast Complex Complex.instNatCast j))))) qz50 138635607020660000829 1801439850948198400 639835367664204871840837 ep181 2366987571 65536000

noncomputable def ep184 := nat_lit 4821637404607495636687257600

noncomputable def ep185 := nat_lit 2428141568000000000000000000

noncomputable def ep186 := @Enclosure.Complex.IsNear.im_isNear (@HSub.hSub Complex Complex Complex qz47 qz48 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz49 (@Nat.cast Complex Complex.instNatCast j)))) Bool.true 44589396740136578783 900719925474099200 561546369597926276500359 ep185 Bool.false 138635607020660000829 1801439850948198400

noncomputable def ep187 := @Enclosure.Complex.IsNear.subLitP qz48 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz49 (@Nat.cast Complex Complex.instNatCast j))) Bool.true 38370804231508166183 900719925474099200 545162369576073002388359 ep185 Bool.false 144209393370112717629 1801439850948198400 574299367659348588704837

noncomputable def ep188 := nat_lit 200812790543554305270808555833786368

noncomputable def ep189 := nat_lit 39022454257407931180376908653133824

noncomputable abbrev qz477 := (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (2 : Complex))

noncomputable abbrev qz458 := qz477

noncomputable abbrev qz317 := (@HSub.hSub Complex Complex Complex qz455 qz456 qz458)

noncomputable abbrev qz318 := (Complex.log qz456)

noncomputable abbrev qz51 := (@HSub.hSub Complex Complex Complex qz313 (@HMul.hMul Complex Complex Complex qz312 qz317 qz318) qz314)

noncomputable abbrev qz319 := qz458

noncomputable abbrev qz52 := (@HMul.hMul Complex Complex Complex qz312 qz319 ↑(Real.log qz267))

noncomputable abbrev qz459 := qz476

noncomputable abbrev qz320 := qz459

noncomputable abbrev qz53 := qz320

noncomputable abbrev qz54 := (@instHMul Nat instMulNat)

noncomputable abbrev qz460 := (@instHPow Complex Int (@ZPow.toPow Complex (@DivInvMonoid.toZPow Complex Complex.instDivInvMonoid)))

noncomputable abbrev qz321 := qz460

noncomputable abbrev qz55 := qz321

noncomputable abbrev qz56 := qz314

noncomputable abbrev qz322 := (@instHSub Int Int.instSub)

noncomputable abbrev qz57 := qz322

noncomputable abbrev qz323 := (@OfNat.ofNat Int 1 (@instOfNat 1))

noncomputable abbrev qz58 := qz323

noncomputable abbrev qz324 := (@instHMul Int Int.instMul)

noncomputable abbrev qz59 := qz324

noncomputable abbrev qz325 := (@OfNat.ofNat Int 2 (@instOfNat 2))

noncomputable abbrev qz60 := qz325

noncomputable def ep190 := @Enclosure.Complex.IsNear.of_eq qz48 (@HAdd.hAdd Complex Complex Complex qz5 (@HAdd.hAdd Complex Complex Complex qz5 qz51 qz52) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz47 (@HMul.hMul Complex Complex Complex qz45 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz55 qz56 (@HSub.hSub Int Int Int qz57 qz58 (@HMul.hMul Int Int Int qz59 qz60 (@Nat.cast Int instNatCastInt k)))))) Bool.true 38370804231508166183

noncomputable def ep191 := @Enclosure.Complex.IsNear.addLitP (@HAdd.hAdd Complex Complex Complex qz5 qz51 qz52) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz47 (@HMul.hMul Complex Complex Complex qz45 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz55 qz56 (@HSub.hSub Int Int Int qz57 qz58 (@HMul.hMul Int Int Int qz59 qz60 (@Nat.cast Int instNatCastInt k))))) Bool.true 38370973027183199783 900719925474099200

noncomputable def ep192 := nat_lit 329602698591091973025836302336

noncomputable def ep193 := nat_lit 1548436570751583365125594152960000

noncomputable def ep194 := @ep191 2079626165609080361 9262625000000000000000 Bool.false 721070636505421299761 9007199254740992000 17525500021171322609 148202000000000000000000 Bool.false 1609761 8589934592 3 8589934592 Bool.true 5643285479 2147483648000 10517 2147483648000 Bool.true ep192 38370804231508166183 900719925474099200 545162369576073002388359 ep185 Bool.false ep193

noncomputable def ep195 := @Enclosure.Complex.IsNear.addLitP qz51 qz52 Bool.true 39198678508625298983 900719925474099200 32426000003505051401 148202000000000000000000

noncomputable def ep196 := nat_lit 5029360176618956361957376

noncomputable def ep197 := @ep195 Bool.false 721070636505421299761 9007199254740992000 17525500021171322609 148202000000000000000000 Bool.false 120447 131072 3 524288 Bool.false 0 1 0 1 Bool.true ep196 38370973027183199783 900719925474099200 2079626165609080361 9262625000000000000000 Bool.false 721070636505421299761 721070636505421299761 9007199254740992000

noncomputable abbrev qz61 := (@HMul.hMul Complex Complex Complex qz312 qz317 qz318)

noncomputable def ep198 := @Enclosure.Complex.IsNear.subLitP qz61 qz56 Bool.true 37172058676308575783 900719925474099200 32426000003505051401 148202000000000000000000 Bool.false 1005256780191754338353

noncomputable def ep199 := nat_lit 2884282546021685199044000

noncomputable def ep200 := @ep198 9007199254740992000 17525500021171322609 148202000000000000000000 Bool.false 9000 4000 0 1 Bool.false 126204 4000 0 1 Bool.true 156794714034501195932000 39198678508625298983 900719925474099200 32426000003505051401 148202000000000000000000 Bool.false ep199 721070636505421299761 9007199254740992000 17525500021171322609 148202000000000000000000

noncomputable abbrev qz62 := qz317

noncomputable abbrev qz63 := qz318

noncomputable def ep201 := @Enclosure.Complex.IsNear.mul qz62 qz63 Bool.true 37172058676308575783 900719925474099200 32426000003505051401 148202000000000000000000 Bool.false 1005256780191754338353 9007199254740992000 17525500021171322609

noncomputable abbrev qz64 := (Complex.re qz317)

noncomputable abbrev qz65 := (Complex.re qz318)

noncomputable abbrev qz66 := (Complex.im qz317)

noncomputable abbrev qz67 := (Complex.im qz318)

noncomputable def ep202 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 qz64 qz65) (@HMul.hMul Real Real Real qz0 qz66 qz67) 217784977004830921 36028797018963968 3500000004668363 592808000000000000000 5327085387678668601 112589990684262400

noncomputable def ep203 := nat_lit 167408069603217514684557655034298368

noncomputable def ep204 := @Enclosure.Real.IsNear.mulLit_ff qz64 qz65 7000 4000 0 1 31112139572118703 9007199254740992 500000000666909 148202000000000000000

noncomputable def ep205 := @Enclosure.Complex.IsNear.re_isNear qz62 Bool.false 7000 4000 0 1 Bool.false 126204 4000 0 1

noncomputable abbrev qz326 := (Enclosure.sfrac Bool.false 126204 4000)

noncomputable abbrev qz68 := qz326

noncomputable def ep206 := @Enclosure.Complex.IsNear.of_eq qz62 (Complex.mk (Enclosure.sfrac Bool.false 7000 4000) qz68) Bool.false 7000 4000 0 1 Bool.false 126204 4000 0

noncomputable abbrev qz327 := (Enclosure.sfrac Bool.false 9000 4000)

noncomputable abbrev qz69 := (Complex.mk qz327 qz326)

noncomputable def ep207 := @Enclosure.Complex.IsNear.of_eq qz63 (Complex.log qz69) Bool.false 31112139572118703 9007199254740992 500000000666909 148202000000000000000 Bool.false 844202305422755 562949953421312 1000000000074101 148202000000000000000

noncomputable def ep208 := nat_lit 716240444564264294568200230424197544953405785569636439697480328239743435443511845199688504559877035151851520

noncomputable def ep209 := nat_lit 26591681868544723072078338383359816903719699591733841952323826958281563851642914785243180687633861106991104

noncomputable def ep210 := nat_lit 804502015872228639047265110910785499907445531589906569908374174378366432802002414731796560031850168320

noncomputable def ep211 := BSN.log_dyadic_bound 7816449616 24200449616 6 5 ep208 524288 148202 ep209 ep210 351251 32016899232 16384000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 7816449616) (BSN.artanhQ 24200449616) 0 5 ep209 ep208 ep210 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz70 := (Enclosure.sfrac Bool.false 1 2)

noncomputable abbrev qz328 := (Real.log (Enclosure.sfrac Bool.false 16008449616 16000000))

noncomputable abbrev qz329 := (Enclosure.Real.IsNear.const Bool.false 1 2)

noncomputable abbrev qz330 := (@Nat.cast Real Real.instNatCast 16000000)

noncomputable def ep212 := @Enclosure.Real.IsNear.mulLit_ff qz70 qz328 1 2 0 1 31112139572118703 4503599627370496 500000000666909 74101000000000000000 31112139572118703 9007199254740992 500000000666909 148202000000000000000 qz329 (BSN.isNear_log_sfrac 16008449616 16000000 31112139572118703 4503599627370496 500000000666909 74101000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 16008449616) qz330)) Bool.false 130493771455895764467712 18889465931478580854784 1000000001333818 148202000000000000000 31112139572118703 4503599627370496 500000000666909 74101000000000000000 (BSN.log_rat_reduce_isNear 16008449616 16000000 9 32016899232 16384000000 351251 524288 24973259072661432 36028797018963968 148202 1000000000000000 rfl rfl rfl rfl (ep211 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep213 := BSN.arctan_dyadic_bound_f 9000 126204 1 0 524288 148202 0 1 1 0 1 1 37325 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 9000) (BSN.arctanEvenQ 126204) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 9000) (BSN.arctanOddQ 126204) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz71 := (@HMul.hMul Real Real Real qz263 (Enclosure.sfrac Bool.false 1 2) Real.pi)

noncomputable abbrev qz72 := (@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 2) Real.pi 1 2 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 qz329 BSN.pi_near_15 rfl)

noncomputable abbrev qz331 := (Real.arctan (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 9000) (@Nat.cast Real Real.instNatCast 126204)))

noncomputable def ep214 := @Enclosure.Real.IsNear.subLit_ff_p qz71 qz331 884279719003555 562949953421312 1 2000000000000000 37325 524288 1 148202 442605138305485373440 844202305422755 562949953421312 1000000000074101 148202000000000000000 qz72 (ep213 rfl) rfl rfl

noncomputable abbrev qz332 := (Real.arctan (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 126204) (@Nat.cast Real Real.instNatCast 9000)))

noncomputable def ep215 := @Enclosure.Complex.IsNear.re_isNear qz63 Bool.false 31112139572118703 9007199254740992 500000000666909 148202000000000000000 Bool.false 844202305422755 562949953421312 1000000000074101 148202000000000000000 (ep207 (@congrArg Complex Complex qz56 qz69 Complex.log (BSN.w_shift_mk qz17 Bool.false 63102 1000 2 qz18 rfl)) (@Enclosure.Complex.IsNear.of_parts (Complex.log qz69) Bool.false 31112139572118703 9007199254740992 500000000666909 148202000000000000000 Bool.false 844202305422755 562949953421312 1000000000074101 148202000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re (Complex.log qz69)) (@HMul.hMul Real Real Real qz0 qz70 qz328) Bool.false 31112139572118703 9007199254740992 500000000666909 148202000000000000000 (Enclosure.clog_re_eq 9000 126204 4000 16008449616 16000000 rfl rfl rfl) (ep212 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im (Complex.log qz69)) qz332 Bool.false 844202305422755 562949953421312 1000000000074101 148202000000000000000 (Enclosure.clog_im_eq 9000 126204 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz332 (@HSub.hSub Real Real Real qz46 qz71 qz331) Bool.false 844202305422755 562949953421312 1000000000074101 148202000000000000000 (BSN.arctan_recip 126204 9000 rfl rfl) ep214))))

noncomputable def ep216 := @Enclosure.Real.IsNear.mulLit_ff qz66 qz67 126204 4000 0 1 844202305422755 562949953421312 1000000000074101 148202000000000000000

noncomputable def ep217 := @Enclosure.Complex.IsNear.im_isNear qz62 Bool.false 7000 4000 0 1 Bool.false 126204 4000 0 1

noncomputable def ep218 := @Enclosure.Complex.IsNear.im_isNear qz63 Bool.false 31112139572118703 9007199254740992 500000000666909 148202000000000000000 Bool.false 844202305422755 562949953421312 1000000000074101 148202000000000000000 (ep207 (@congrArg Complex Complex qz56 qz69 Complex.log (BSN.w_shift_mk qz17 Bool.false 63102 1000 2 qz18 rfl)) (@Enclosure.Complex.IsNear.of_parts (Complex.log qz69) Bool.false 31112139572118703 9007199254740992 500000000666909 148202000000000000000 Bool.false 844202305422755 562949953421312 1000000000074101 148202000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re (Complex.log qz69)) (@HMul.hMul Real Real Real qz0 qz70 qz328) Bool.false 31112139572118703 9007199254740992 500000000666909 148202000000000000000 (Enclosure.clog_re_eq 9000 126204 4000 16008449616 16000000 rfl rfl rfl) (ep212 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im (Complex.log qz69)) qz332 Bool.false 844202305422755 562949953421312 1000000000074101 148202000000000000000 (Enclosure.clog_im_eq 9000 126204 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz332 (@HSub.hSub Real Real Real qz46 qz71 qz331) Bool.false 844202305422755 562949953421312 1000000000074101 148202000000000000000 (BSN.arctan_recip 126204 9000 rfl rfl) ep214))))

noncomputable abbrev qz333 := (Enclosure.Real.IsNear.const Bool.false 126204 4000)

noncomputable abbrev qz73 := (@ep206 1 (BSN.w_sub_half_mk qz276 Bool.false 63102 1000 2 qz277 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7000 4000) qz326 Bool.false 7000 4000 0 1 Bool.false 126204 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 7000 4000) qz333))

noncomputable def ep219 := @ep202 31551000002337960651 148202000000000000000000 ep203 37172058676308575783 900719925474099200 32426000003505051401 148202000000000000000000 (@ep204 217784977004830921 36028797018963968 3500000004668363 592808000000000000000 (ep205 qz73) ep215 rfl) (@ep216 5327085387678668601 112589990684262400 31551000002337960651 148202000000000000000000 (ep217 qz73) ep218 rfl) rfl

noncomputable def ep220 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz64 qz67) (@HMul.hMul Real Real Real qz0 qz66 qz65) 5909416137959285 2251799813685248 7000000000518707 592808000000000000000 981619115639917198353 9007199254740992000

noncomputable def ep221 := nat_lit 2263637030341624721358063404836716544

noncomputable def ep222 := @Enclosure.Real.IsNear.mulLit_ff qz64 qz67 7000 4000 0 1 844202305422755 562949953421312 1000000000074101 148202000000000000000

noncomputable def ep223 := @Enclosure.Real.IsNear.mulLit_ff qz66 qz65 126204 4000 0 1 31112139572118703 9007199254740992 500000000666909 148202000000000000000

noncomputable def ep224 := @ep220 15775500021041645859 148202000000000000000000 ep221 1005256780191754338353 9007199254740992000 17525500021171322609 148202000000000000000000 (@ep222 5909416137959285 2251799813685248 7000000000518707 592808000000000000000 (ep205 qz73) ep218 rfl) (@ep223 981619115639917198353 9007199254740992000 15775500021041645859 148202000000000000000000 (ep217 qz73) ep215 rfl) rfl

noncomputable def ep225 := @Enclosure.Complex.IsNear.of_eq qz56 qz69 Bool.false 9000 4000 0 1 Bool.false 126204 4000 0 1 (BSN.w_shift_mk qz17 Bool.false 63102 1000 2 qz18 rfl)

noncomputable abbrev qz334 := (ep225 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 9000 4000) (Enclosure.sfrac Bool.false 126204 4000) Bool.false 9000 4000 0 1 Bool.false 126204 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 9000 4000) (Enclosure.Real.IsNear.const Bool.false 126204 4000)))

noncomputable abbrev qz74 := qz334

noncomputable def ep226 := ep200 (@ep201 148202000000000000000000 (ep219 rfl) (ep224 rfl)) qz74 rfl rfl rfl rfl rfl rfl

noncomputable abbrev qz75 := qz319

noncomputable def ep227 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re qz75) (Complex.re ↑qz3)) (@HMul.hMul Real Real Real qz0 (Complex.im qz75) (Complex.im ↑qz3)) 120447 131072 3 524288 0 1 0 1 120447 120447

noncomputable def ep228 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re qz75) (Complex.re ↑qz3) 1 2 0 1 120447 65536 3 262144 120447 131072 3 524288

noncomputable abbrev qz76 := (@Enclosure.Complex.IsNear.of_eq qz319 (Complex.mk (Enclosure.sfrac Bool.false 1 2) qz274) Bool.false 1 2 0 1 Bool.false 0 1 0 1 BSN.half_c_mk (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 2) qz274 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz329 qz286))

noncomputable def ep229 := ep228 (@Enclosure.Complex.IsNear.re_isNear qz75 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz76) (@Enclosure.Real.IsNear.of_eq (Complex.re ↑qz3) qz3 Bool.false 120447 65536 3 262144 (Complex.ofReal_re qz3) EMRow15.d4)

noncomputable def ep230 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz75) (Complex.im ↑qz3) 0 1 0 1 0 1 0 1 0 1 0 1

noncomputable def ep231 := ep230 (@Enclosure.Complex.IsNear.im_isNear qz75 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz76) (@Enclosure.Real.IsNear.of_eq (Complex.im ↑qz3) qz14 Bool.false 0 1 0 1 (@Eq.trans Real (Complex.im ↑qz3) (0 : Real) qz14 (Complex.ofReal_im qz3) Enclosure.sfrac_zero_eq) qz24)

noncomputable def ep232 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re qz75) (Complex.im ↑qz3)) (@HMul.hMul Real Real Real qz0 (Complex.im qz75) (Complex.re ↑qz3)) 0 1 0 1 0 1 0 1 0 0

noncomputable def ep233 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re qz75) (Complex.im ↑qz3) 1 2 0 1 0 1 0 1 0 1 0 1

noncomputable def ep234 := ep233 (@Enclosure.Complex.IsNear.re_isNear qz75 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz76) (@Enclosure.Real.IsNear.of_eq (Complex.im ↑qz3) qz14 Bool.false 0 1 0 1 (@Eq.trans Real (Complex.im ↑qz3) (0 : Real) qz14 (Complex.ofReal_im qz3) Enclosure.sfrac_zero_eq) qz24)

noncomputable def ep235 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz75) (Complex.re ↑qz3) 0 1 0 1 120447 65536 3 262144 0 1 0 1

noncomputable def ep236 := ep235 (@Enclosure.Complex.IsNear.im_isNear qz75 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz76) (@Enclosure.Real.IsNear.of_eq (Complex.re ↑qz3) qz3 Bool.false 120447 65536 3 262144 (Complex.ofReal_re qz3) EMRow15.d4)

noncomputable def ep237 := @ep197 17525500021171322609 148202000000000000000000 (ep226 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@Enclosure.Complex.IsNear.mul qz75 (↑qz3) Bool.false 120447 131072 3 524288 Bool.false 0 1 0 1 (@ep227 131072 3 524288 (ep229 rfl) (ep231 rfl) rfl rfl) (@ep232 1 0 1 (ep234 rfl) (ep236 rfl) rfl rfl))

noncomputable abbrev qz77 := (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 1)

noncomputable abbrev qz335 := (@Nat.cast Complex Complex.instNatCast 1)

noncomputable abbrev qz78 := (@HMul.hMul Complex Complex Complex qz312 (@HMul.hMul Complex Complex Complex qz312 (2 : Complex) qz335) (@HSub.hSub Complex Complex Complex qz313 (@HMul.hMul Complex Complex Complex qz312 (2 : Complex) qz335) (1 : Complex)))

noncomputable abbrev qz336 := (@HPow.hPow Complex Int Complex qz460 qz456 (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) (@OfNat.ofNat Int 1 (@instOfNat 1)) (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (@OfNat.ofNat Int 2 (@instOfNat 2)) (@Nat.cast Int instNatCastInt 1))))

noncomputable abbrev qz79 := qz336

noncomputable def ep238 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz47 (@HMul.hMul Complex Complex Complex qz45 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz55 qz56 (@HSub.hSub Int Int Int qz57 qz58 (@HMul.hMul Int Int Int qz59 qz60 (@Nat.cast Int instNatCastInt k))))) (@HAdd.hAdd Complex Complex Complex qz5 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz47 (@HMul.hMul Complex Complex Complex qz45 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz55 qz56 (@HSub.hSub Int Int Int qz57 qz58 (@HMul.hMul Int Int Int qz59 qz60 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli qz77)) qz78) qz79)) Bool.false 1609761 8589934592 3 8589934592

noncomputable def ep239 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz47 (@HMul.hMul Complex Complex Complex qz45 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz55 qz56 (@HSub.hSub Int Int Int qz57 qz58 (@HMul.hMul Int Int Int qz59 qz60 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli qz77)) qz78) qz79) Bool.false 0 1 0 1 Bool.false

noncomputable def ep240 := @ep239 0 1 0 1 Bool.false 1609761 8589934592 3 8589934592 Bool.true 5643285479 2147483648000 10517 2147483648000 Bool.false 1609761 1609761 8589934592 3 8589934592 Bool.true 5643285479 5643285479 2147483648000 10517

noncomputable def ep241 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz47 (@HMul.hMul Complex Complex Complex qz45 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz55 qz56 (@HSub.hSub Int Int Int qz57 qz58 (@HMul.hMul Int Int Int qz59 qz60 (@Nat.cast Int instNatCastInt k))))) (Complex.mk qz14 qz14) Bool.false 0 1 0 1 Bool.false

noncomputable def ep242 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli qz77)) qz78) qz79 Bool.false 1609761 8589934592 3 8589934592 Bool.true 5643285479 2147483648000 10517 2147483648000

noncomputable abbrev qz80 := (Complex.re qz336)

noncomputable abbrev qz81 := (Complex.im qz336)

noncomputable def ep243 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli qz77)) qz78)) qz80) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli qz77)) qz78)) qz81) 1609761 8589934592 3 8589934592 0 1 0

noncomputable def ep244 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli qz77)) qz78)) qz80 1 12 0 1 4829283 2147483648 9 2147483648 1609761

noncomputable def ep245 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli qz77)) qz78) (Complex.mk (Enclosure.sfrac Bool.false 1 12) qz14) Bool.false 1 12 0 1 Bool.false 0 1 0 1

noncomputable abbrev qz337 := (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 12) qz14 Bool.false 1 12 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 12) qz24)

noncomputable def ep246 := @Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli qz77)) qz78) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (ep245 (BSN.stirling_coeff_mk 1 1 6 Bool.false BSN.bern_real_1 rfl rfl) qz337)

noncomputable def ep247 := @Enclosure.Complex.IsNear.re_isNear qz79 Bool.false 4829283 2147483648 9 2147483648 Bool.true 16929856437 536870912000 31551 536870912000

noncomputable abbrev qz461 := (@instHPow Complex Nat (@NPow.toPow Complex (@Monoid.toNPow Complex (@Semiring.toMonoid Complex Complex.instSemiring))))

noncomputable abbrev qz338 := (@HPow.hPow Complex Nat Complex qz461 qz456 1)

noncomputable abbrev qz82 := (@Inv.inv Complex Complex.instInv qz338)

noncomputable def ep248 := @Enclosure.Complex.IsNear.of_eq qz79 qz82 Bool.false 4829283 2147483648 9 2147483648 Bool.true 16929856437 536870912000 31551

noncomputable def ep249 := @Enclosure.Complex.IsNear.of_parts qz82 Bool.false 4829283 2147483648 9 2147483648 Bool.true 16929856437 536870912000 31551

noncomputable abbrev qz83 := (Complex.re qz338)

noncomputable abbrev qz84 := (@MonoidWithZeroHom Complex Real (@instMulZeroOneClassOfSemiring Complex Complex.instSemiring) (@instMulZeroOneClassOfSemiring Real Real.semiring))

noncomputable abbrev qz85 := (@MonoidWithZeroHom.funLike Complex Real (@instMulZeroOneClassOfSemiring Complex Complex.instSemiring) (@instMulZeroOneClassOfSemiring Real Real.semiring))

noncomputable abbrev qz86 := qz338

noncomputable def ep250 := @Enclosure.Real.IsNear.mulLit_ff qz83 (@Inv.inv Real Real.instInv (@DFunLike.coe qz84 Complex (fun (x : Complex) => Real) qz85 Complex.normSq qz86)) 9000 4000 0 1 536587 536870912 1 536870912

noncomputable def ep251 := @Enclosure.Complex.IsNear.re_isNear qz86 Bool.false 9000 4000 0 1 Bool.false 126204 4000 0 1

noncomputable def ep252 := @Enclosure.Complex.IsNear.of_eq qz86 qz56 Bool.false 9000 4000 0 1 Bool.false 126204 4000 0

noncomputable def ep253 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (@DFunLike.coe qz84 Complex (fun (x : Complex) => Real) qz85 Complex.normSq qz86)) Bool.false 536587 536870912 1 536870912 536587 536870912 1

noncomputable abbrev qz87 := (@instHAdd Real Real.instAdd)

noncomputable abbrev qz88 := (Complex.im qz338)

noncomputable def ep254 := @Enclosure.Real.IsNear.of_eq (@DFunLike.coe qz84 Complex (fun (x : Complex) => Real) qz85 Complex.normSq qz86) (@HAdd.hAdd Real Real Real qz87 (@HMul.hMul Real Real Real qz0 qz83 qz83) (@HMul.hMul Real Real Real qz0 qz88 qz88)) Bool.false 1000528101 1000000 0 1

noncomputable def ep255 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz83 qz83) (@HMul.hMul Real Real Real qz0 qz88 qz88) 81 16 0 1 995465601 1000000

noncomputable def ep256 := @Enclosure.Real.IsNear.mulLit_ff qz83 qz83 9000 4000 0 1 9000 4000 0 1

noncomputable def ep257 := @Enclosure.Real.IsNear.mulLit_ff qz88 qz88 126204 4000 0 1 126204 4000 0 1

noncomputable def ep258 := @Enclosure.Complex.IsNear.im_isNear qz86 Bool.false 9000 4000 0 1 Bool.false 126204 4000 0 1

noncomputable abbrev qz89 := (ep251 (@ep252 1 (BSN.pow_one_c qz314) qz334))

noncomputable abbrev qz90 := (ep258 (@ep252 1 (BSN.pow_one_c qz314) qz334))

noncomputable def ep259 := @ep255 0 1 16008449616 1000528101 1000000 0 1 (@ep256 81 16 0 1 qz89 qz89 rfl) (@ep257 995465601 1000000 0 1 qz90 qz90 rfl)

noncomputable def ep260 := @Enclosure.Real.IsNear.inv_image (@DFunLike.coe qz84 Complex (fun (x : Complex) => Real) qz85 Complex.normSq qz86) 1000528101 1000000 0 1 268293 268294 268435456 (ep254 (Enclosure.Complex.normSq_eq_mul_add_mul qz86) (ep259 rfl rfl)) rfl

noncomputable def ep261 := @Enclosure.Real.IsNear.of_eq (Complex.re qz82) (@HMul.hMul Real Real Real qz0 qz83 (@Inv.inv Real Real.instInv (@DFunLike.coe qz84 Complex (fun (x : Complex) => Real) qz85 Complex.normSq qz86))) Bool.false 4829283 2147483648 9 2147483648 (Enclosure.Complex.inv_re_eq_mul qz86) (@ep250 4829283 2147483648 9 2147483648 qz89 (@ep253 536870912 (ep260 rfl rfl rfl rfl rfl) rfl) rfl)

noncomputable def ep262 := @Enclosure.Real.IsNear.of_eq (Complex.im qz82) (@HMul.hMul Real Real Real qz0 (@Neg.neg Real Real.instNeg qz88) (@Inv.inv Real Real.instInv (@DFunLike.coe qz84 Complex (fun (x : Complex) => Real) qz85 Complex.normSq qz86))) Bool.true 16929856437 536870912000 31551 536870912000 (Enclosure.Complex.inv_im_eq_mul qz86)

noncomputable def ep263 := @Enclosure.Real.IsNear.mulLit_tf (@Neg.neg Real Real.instNeg qz88) (@Inv.inv Real Real.instInv (@DFunLike.coe qz84 Complex (fun (x : Complex) => Real) qz85 Complex.normSq qz86)) 126204 4000 0 1 536587 536870912 1

noncomputable def ep264 := @ep263 536870912 16929856437 536870912000 31551 536870912000 (@Enclosure.Real.IsNear.neg qz88 Bool.false 126204 4000 0 1 qz90) (@ep253 536870912 (ep260 rfl rfl rfl rfl rfl) rfl) rfl

noncomputable def ep265 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli qz77)) qz78)) qz81 0 1 0 1 16929856437 536870912000 31551 536870912000 0

noncomputable def ep266 := @Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli qz77)) qz78) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (ep245 (BSN.stirling_coeff_mk 1 1 6 Bool.false BSN.bern_real_1 rfl rfl) qz337)

noncomputable def ep267 := @Enclosure.Complex.IsNear.im_isNear qz79 Bool.false 4829283 2147483648 9 2147483648 Bool.true 16929856437 536870912000 31551 536870912000

noncomputable abbrev qz91 := (@ep248 536870912000 (BSN.zpow_one_sub_two_mul qz314 1 1 rfl rfl) (@ep249 536870912000 ep261 (ep262 ep264)))

noncomputable def ep268 := @ep243 1 1609761 1609761 8589934592 3 8589934592 (@ep244 8589934592 3 8589934592 ep246 (ep247 qz91) rfl) (@ep265 1 0 1 ep266 (ep267 qz91) rfl) rfl

noncomputable def ep269 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli qz77)) qz78)) qz81) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli qz77)) qz78)) qz80) 5643285479 2147483648000 10517 2147483648000 0 1 0

noncomputable def ep270 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli qz77)) qz78)) qz81 1 12 0 1 16929856437 536870912000 31551 536870912000 5643285479

noncomputable def ep271 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli qz77)) qz78)) qz80 0 1 0 1 4829283 2147483648 9 2147483648 0

noncomputable def ep272 := @ep269 1 5643285479 5643285479 2147483648000 10517 2147483648000 (@ep270 2147483648000 10517 2147483648000 ep246 (ep267 qz91) rfl) (@ep271 1 0 1 ep266 (ep247 qz91) rfl) rfl

noncomputable abbrev qz92 := (@Enclosure.Complex.IsNear.mk qz274 qz274 Bool.false 0 1 0 1 Bool.false 0 1 0 1 qz286 qz286)

noncomputable def ep273 := @ep240 2147483648000 (@ep241 0 1 0 1 (BSN.stirling_sum_base qz56) qz92) (ep242 (ep268 rfl) (ep272 rfl)) rfl rfl rfl rfl rfl

noncomputable def ep274 := @ep194 144209393370112717629 1801439850948198400 574299367659348588704837 ep181 (ep237 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep238 Bool.true 5643285479 2147483648000 10517 2147483648000 (BSN.stirling_sum_succ qz56 0 1 rfl) (ep273 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl

noncomputable def ep275 := @Enclosure.Complex.IsNear.of_eq (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz49 (@Nat.cast Complex Complex.instNatCast j))) (BSN.logSumC qz17 2) Bool.false 31092962543142063 4503599627370496 500000000666909 74101000000000000000 Bool.false 870904117101987 281474976710656

noncomputable abbrev qz93 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz269 qz315 qz335))

noncomputable def ep276 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz17 2) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.logSumC qz17 1) qz93) Bool.false 31092962543142063 4503599627370496 500000000666909 74101000000000000000 Bool.false 870904117101987 281474976710656 1000000000074101 74101000000000000000

noncomputable def ep277 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz17 1) qz93 Bool.false 31089573813945519 9007199254740992 500000000666909 148202000000000000000 Bool.false 879819395466659 562949953421312 1000000000074101 148202000000000000000 Bool.false

noncomputable def ep278 := nat_lit 560121018092557538340777851092992

noncomputable def ep279 := nat_lit 980550864313984866482166693888

noncomputable abbrev qz94 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz269 qz315 (@Nat.cast Complex Complex.instNatCast 0)))

noncomputable def ep280 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz17 1) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.logSumC qz17 0) qz94) Bool.false 31089573813945519 9007199254740992 500000000666909 148202000000000000000 Bool.false 879819395466659 562949953421312 1000000000074101 148202000000000000000

noncomputable def ep281 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz17 0) qz94 Bool.false 0 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable abbrev qz339 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz68))

noncomputable def ep282 := @Enclosure.Complex.IsNear.of_eq qz94 qz339 Bool.false 31089573813945519 9007199254740992 500000000666909 148202000000000000000 Bool.false 879819395466659 562949953421312 1000000000074101 148202000000000000000

noncomputable def ep283 := nat_lit 692912639692736604420311604543779027072546753571945732499180369596291553449328324211471713394310059151851520

noncomputable def ep284 := nat_lit 25345078892645866746941203327662774387809283655346852707323372041879395861353252468485083912993425906991104

noncomputable def ep285 := nat_lit 725853246623388114637466398311028570111632484724991619182457631729963376392971484758164781215850168320

noncomputable def ep286 := BSN.log_dyadic_bound 7736449616 24120449616 6 5 ep283 524288 148202 ep284 ep285 348624 31856899232 16384000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 7736449616) (BSN.artanhQ 24120449616) 0 5 ep284 ep283 ep285 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep287 := @Enclosure.Real.IsNear.mulLit_ff qz70 (Real.log (Enclosure.sfrac Bool.false 15928449616 16000000)) 1 2 0 1 31089573813945519 4503599627370496 500000000666909 74101000000000000000 31089573813945519 9007199254740992 500000000666909 148202000000000000000 qz329 (BSN.isNear_log_sfrac 15928449616 16000000 31089573813945519 4503599627370496 500000000666909 74101000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 15928449616) qz330)) Bool.false 130399123806126946123776 18889465931478580854784 1000000001333818 148202000000000000000 31089573813945519 4503599627370496 500000000666909 74101000000000000000 (BSN.log_rat_reduce_isNear 15928449616 16000000 9 31856899232 16384000000 348624 524288 24973259072661432 36028797018963968 148202 1000000000000000 rfl rfl rfl rfl (ep286 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep288 := BSN.arctan_dyadic_bound_f 1000 126204 1 0 524288 148202 0 1 1 0 1 1 4154 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 126204) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 126204) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz340 := (@Nat.cast Real Real.instNatCast 1000)

noncomputable abbrev qz341 := (@Nat.cast Real Real.instNatCast 126204)

noncomputable def ep289 := @Enclosure.Real.IsNear.subLit_ff_p qz71 (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz340 qz341)) 884279719003555 562949953421312 1 2000000000000000 4154 524288 1 148202 461278751210423713792 879819395466659 562949953421312 1000000000074101 148202000000000000000 qz72 (ep288 rfl) rfl rfl

noncomputable abbrev qz95 := (@HAdd.hAdd Complex Complex Complex qz269 qz315 (@Nat.cast Complex Complex.instNatCast 0))

noncomputable abbrev qz342 := (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz68)

noncomputable def ep290 := @ep281 31089573813945519 9007199254740992 500000000666909 148202000000000000000 Bool.false 879819395466659 562949953421312 1000000000074101 148202000000000000000 Bool.false 31089573813945519 31089573813945519 9007199254740992 500000000666909 148202000000000000000 Bool.false 879819395466659 879819395466659 562949953421312 1000000000074101 148202000000000000000 (@Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz17 0) (Complex.mk qz14 qz14) Bool.false 0 1 0 1 Bool.false 0 1 0 1 (BSN.log_sum_c_base qz17) qz92) (ep282 (@congrArg Complex Complex qz95 qz342 Complex.log (BSN.w_shift_mk qz17 Bool.false 63102 1000 0 qz18 rfl)) (@Enclosure.Complex.IsNear.of_parts qz339 Bool.false 31089573813945519 9007199254740992 500000000666909 148202000000000000000 Bool.false 879819395466659 562949953421312 1000000000074101 148202000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz339) (@HMul.hMul Real Real Real qz0 qz70 (Real.log (Enclosure.sfrac Bool.false 15928449616 16000000))) Bool.false 31089573813945519 9007199254740992 500000000666909 148202000000000000000 (Enclosure.clog_re_eq 1000 126204 4000 15928449616 16000000 rfl rfl rfl) (ep287 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz339) (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz341 qz340)) Bool.false 879819395466659 562949953421312 1000000000074101 148202000000000000000 (Enclosure.clog_im_eq 1000 126204 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz341 qz340)) (@HSub.hSub Real Real Real qz46 qz71 (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz340 qz341))) Bool.false 879819395466659 562949953421312 1000000000074101 148202000000000000000 (BSN.arctan_recip 126204 1000 rfl rfl) ep289)))) rfl rfl

noncomputable abbrev qz343 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz68))

noncomputable def ep291 := @Enclosure.Complex.IsNear.of_eq qz93 qz343 Bool.false 31096351272338607 9007199254740992 500000000666909 148202000000000000000 Bool.false 861988838737315 562949953421312 1000000000074101 148202000000000000000

noncomputable def ep292 := nat_lit 699838116787715779982656807111554726887291619378534140545864362213629056727125551308260991742380151951851520

noncomputable def ep293 := nat_lit 25713600341310037446787508424594765257399462942336782549583601226431131183849729345894892281065556466991104

noncomputable def ep294 := nat_lit 748687608023801390563050488278996258902650841174752335923914027751508431511137228426708714860650168320

noncomputable def ep295 := BSN.log_dyadic_bound 7760449616 24144449616 6 5 ep292 524288 148202 ep293 ep294 349413 31904899232 16384000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 7760449616) (BSN.artanhQ 24144449616) 0 5 ep293 ep292 ep294 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep296 := @Enclosure.Real.IsNear.mulLit_ff qz70 (Real.log (Enclosure.sfrac Bool.false 15952449616 16000000)) 1 2 0 1 31096351272338607 4503599627370496 500000000666909 74101000000000000000 31096351272338607 9007199254740992 500000000666909 148202000000000000000 qz329 (BSN.isNear_log_sfrac 15952449616 16000000 31096351272338607 4503599627370496 500000000666909 74101000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 15952449616) qz330)) Bool.false 130427550526974908694528 18889465931478580854784 1000000001333818 148202000000000000000 31096351272338607 4503599627370496 500000000666909 74101000000000000000 (BSN.log_rat_reduce_isNear 15952449616 16000000 9 31904899232 16384000000 349413 524288 24973259072661432 36028797018963968 148202 1000000000000000 rfl rfl rfl rfl (ep295 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep297 := BSN.arctan_dyadic_bound_f 5000 126204 1 0 524288 148202 0 1 1 0 1 1 20760 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 5000) (BSN.arctanEvenQ 126204) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 5000) (BSN.arctanOddQ 126204) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz344 := (@Nat.cast Real Real.instNatCast 5000)

noncomputable def ep298 := @Enclosure.Real.IsNear.subLit_ff_p qz71 (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz344 qz341)) 884279719003555 562949953421312 1 2000000000000000 20760 524288 1 148202 451930404283909406720 861988838737315 562949953421312 1000000000074101 148202000000000000000 qz72 (ep297 rfl) rfl rfl

noncomputable abbrev qz96 := (@HAdd.hAdd Complex Complex Complex qz269 qz315 qz335)

noncomputable abbrev qz345 := (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz68)

noncomputable def ep299 := @ep277 31096351272338607 9007199254740992 500000000666909 148202000000000000000 Bool.false 861988838737315 562949953421312 1000000000074101 148202000000000000000 Bool.false ep278 31092962543142063 4503599627370496 500000000666909 74101000000000000000 Bool.false ep279 870904117101987 281474976710656 1000000000074101 74101000000000000000 (ep280 (BSN.log_sum_c_succ qz17 0 1 rfl) (ep290 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep291 (@congrArg Complex Complex qz96 qz345 Complex.log (BSN.w_shift_mk qz17 Bool.false 63102 1000 1 qz18 rfl)) (@Enclosure.Complex.IsNear.of_parts qz343 Bool.false 31096351272338607 9007199254740992 500000000666909 148202000000000000000 Bool.false 861988838737315 562949953421312 1000000000074101 148202000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz343) (@HMul.hMul Real Real Real qz0 qz70 (Real.log (Enclosure.sfrac Bool.false 15952449616 16000000))) Bool.false 31096351272338607 9007199254740992 500000000666909 148202000000000000000 (Enclosure.clog_re_eq 5000 126204 4000 15952449616 16000000 rfl rfl rfl) (ep296 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz343) (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz341 qz344)) Bool.false 861988838737315 562949953421312 1000000000074101 148202000000000000000 (Enclosure.clog_im_eq 5000 126204 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz341 qz344)) (@HSub.hSub Real Real Real qz46 qz71 (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz344 qz341))) Bool.false 861988838737315 562949953421312 1000000000074101 148202000000000000000 (BSN.arctan_recip 126204 5000 rfl rfl) ep298)))) rfl rfl

noncomputable def ep300 := @ep187 ep181 Bool.false 31092962543142063 4503599627370496 500000000666909 74101000000000000000 Bool.false 870904117101987 281474976710656 1000000000074101 74101000000000000000 Bool.true ep188 44589396740136578783 900719925474099200 561546369597926276500359 ep185 Bool.false ep189 138635607020660000829 1801439850948198400 639835367664204871840837 ep181 (@ep190 900719925474099200 545162369576073002388359 ep185 Bool.false 144209393370112717629 1801439850948198400 574299367659348588704837 ep181 (BSN.logGammaStirling_unfold 1 qz56) (ep274 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (@ep275 1000000000074101 74101000000000000000 (BSN.log_sum_c_eq qz17 2) (ep276 (BSN.log_sum_c_succ qz17 1 2 rfl) (ep299 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)))

noncomputable abbrev qz97 := (@HDiv.hDiv Real Real Real qz266 qz276 (2 : Real))

noncomputable def ep301 := @Enclosure.Real.IsNear.mulLit_ff qz97 (Real.log Real.pi) 63102 2000 0 1 75021 65536 1 131072 2366987571 65536000 31551 131072000 (@Enclosure.Real.IsNear.of_eq qz97 (Enclosure.sfrac Bool.false 63102 2000) Bool.false 63102 2000 0 1 (BSN.t_half_eq qz17 Bool.false 63102 1000 qz18) (Enclosure.Real.IsNear.const Bool.false 63102 2000)) EMRow15.d5 rfl

noncomputable def ep302 := @ep183 31551 131072000 ep184 367861740463828707633 9007199254740992000 ep180 ep181 (@ep186 639835367664204871840837 ep181 (ep300 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) ep301 rfl rfl

noncomputable def ep303 := BSN.cos_dyadic_bound_f 163268 1073741824 1 0 524288 148347 0 1 1 0 1 1 524287 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 163268) qz283 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 163268) qz284 0 0 rfl) rfl rfl

noncomputable def ep304 := @ep179 131072 Bool.true 524287 524288 1 74101 (@ep182 21412371 524288 49 131072 ep302 rfl) (Enclosure.sfrac_false_div 21412371 524288) (BSN.cos_reduce2 qz316 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 11488985477097193472) qz23) 226375608064910080 72057594037927936 Bool.false 524287 524288 6 1000000000000000 148202 74101 (BSN.sin_reduce_arg_pos_rat_q2 21412371 524288 226375608064910080 72057594037927936 6 11488985477097193472 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 524287 524288 11488985477097193472 75557863725914323419136 163268 1073741824 148347 148202 (ep303 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep305 := nat_lit 5336149273782893150208000

noncomputable def ep306 := nat_lit 826042436601986516047789597

noncomputable def ep307 := nat_lit 197706998668293082661781504000

noncomputable abbrev qz98 := qz270

noncomputable abbrev qz99 := qz271

noncomputable abbrev qz462 := (@Nat.cast Complex Complex.instNatCast 13)

noncomputable abbrev qz346 := (@HPow.hPow Complex Complex Complex qz449 qz462 qz450)

noncomputable abbrev qz100 := qz346

noncomputable abbrev qz347 := qz462

noncomputable abbrev qz101 := (@HAdd.hAdd Complex Complex Complex qz269 (@HDiv.hDiv Complex Complex Complex qz320 qz347 (@HSub.hSub Complex Complex Complex qz313 qz268 (1 : Complex))) qz319)

noncomputable abbrev qz102 := (@instHSub Nat instSubNat)

noncomputable abbrev qz348 := qz461

noncomputable abbrev qz103 := qz348

noncomputable abbrev qz104 := qz347

noncomputable def ep308 := @Enclosure.Complex.IsNear.of_eq (zetaApproximant qz6 1 13) (@HAdd.hAdd Complex Complex Complex qz5 (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 13, @HPow.hPow Complex Complex Complex qz98 (@Nat.cast Complex Complex.instNatCast n) qz99) (@HMul.hMul Complex Complex Complex qz45 qz100 (@HAdd.hAdd Complex Complex Complex qz5 qz101 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz103 qz104 (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz54 2 k) 1))))))) Bool.false ep174 ep175 ep176

noncomputable def ep309 := @Enclosure.Complex.IsNear.addLitP (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 13, @HPow.hPow Complex Complex Complex qz98 (@Nat.cast Complex Complex.instNatCast n) qz99) (@HMul.hMul Complex Complex Complex qz45 qz100 (@HAdd.hAdd Complex Complex Complex qz5 qz101 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz103 qz104 (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))))) Bool.false 73863625587 17179869184 40953022362847 10184363891228672

noncomputable def ep310 := nat_lit 133332929406545545672297513

noncomputable def ep311 := nat_lit 33440319086377546144809847

noncomputable def ep312 := nat_lit 779779129055448699265249204898889728

noncomputable def ep313 := nat_lit 51583150730217568870068462314061824

noncomputable def ep314 := @ep309 Bool.true 48758899117 274877906944 81657689814821 20368727782457344 Bool.true 495669374628600797146333 ep175 ep310 ep177 Bool.false 758888248614004009873729 ep305 ep311 ep307 Bool.false ep312 ep174 ep175 ep176 ep177 Bool.true ep313 187658409159548933057771 ep305

noncomputable def ep315 := @Enclosure.Complex.IsNear.of_eq (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 13, @HPow.hPow Complex Complex Complex qz98 (@Nat.cast Complex Complex.instNatCast n) qz99) (BSN.headSumC qz6 13) Bool.false 73863625587 17179869184 40953022362847 10184363891228672 Bool.true 48758899117 274877906944 81657689814821

noncomputable abbrev qz105 := (@HPow.hPow Complex Complex Complex qz270 (@Nat.cast Complex Complex.instNatCast 12) qz271)

noncomputable def ep316 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz6 13) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz6 12) qz105) Bool.false 73863625587 17179869184 40953022362847 10184363891228672 Bool.true 48758899117 274877906944 81657689814821 20368727782457344

noncomputable def ep317 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz6 12) qz105 Bool.false 1105494978927 274877906944 76764922229309 20368727782457344 Bool.true 17616910733 68719476736 38271653332143 10184363891228672 Bool.false

noncomputable abbrev qz106 := (@HPow.hPow Complex Complex Complex qz270 (@Nat.cast Complex Complex.instNatCast 11) qz271)

noncomputable def ep318 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz6 12) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz6 11) qz106) Bool.false 1105494978927 274877906944 76764922229309 20368727782457344 Bool.true 17616910733 68719476736 38271653332143 10184363891228672

noncomputable def ep319 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz6 11) qz106 Bool.false 1033380919917 274877906944 71400417683239 20368727782457344 Bool.true 29620819727 274877906944 71193458925511 20368727782457344 Bool.false

noncomputable abbrev qz107 := (@HPow.hPow Complex Complex Complex qz270 (@Nat.cast Complex Complex.instNatCast 10) qz271)

noncomputable def ep320 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz6 11) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz6 10) qz107) Bool.false 1033380919917 274877906944 71400417683239 20368727782457344 Bool.true 29620819727 274877906944 71193458925511 20368727782457344

noncomputable def ep321 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz6 10) qz107 Bool.false 485923798911 137438953472 32891009990671 10184363891228672 Bool.false 7943806027 68719476736 32787561289621 10184363891228672 Bool.false

noncomputable abbrev qz108 := (@HPow.hPow Complex Complex Complex qz270 (@Nat.cast Complex Complex.instNatCast 9) qz271)

noncomputable def ep322 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz6 10) (@HAdd.hAdd Complex Complex Complex qz5 qz4 qz108) Bool.false 485923798911 137438953472 32891009990671 10184363891228672 Bool.false 7943806027 68719476736 32787561289621 10184363891228672

noncomputable def ep323 := @Enclosure.Complex.IsNear.addLitP qz4 qz108 Bool.false 444076798561 137438953472 29933086341051 10184363891228672 Bool.false 69066327811 274877906944 59678950503421 20368727782457344 Bool.false

noncomputable abbrev qz349 := (@Nat.cast Real Real.instNatCast 9)

noncomputable abbrev qz109 := (@Inv.inv Real Real.instInv (Real.sqrt qz349))

noncomputable abbrev qz110 := (@HMul.hMul Real Real Real qz263 qz276 (Real.log (Enclosure.sfrac Bool.false 9 1)))

noncomputable def ep324 := @Enclosure.Complex.IsNear.of_eq qz108 (Complex.mk (@HMul.hMul Real Real Real qz0 qz109 (Real.cos qz110)) (@HMul.hMul Real Real Real qz0 qz109 (@Neg.neg Real Real.instNeg (Real.sin qz110)))) Bool.false 20923500175 68719476736 739480912405 2546090972807168 Bool.true 37291103703 274877906944 5896172075821 20368727782457344 (BSN.cpow_neg_s_mk qz17 63102 1000 9 qz18 rfl)

noncomputable abbrev qz350 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 9) qz19)

noncomputable def ep325 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz349) 1572865 524288 1 524288 87381 87382 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz349) (Real.sqrt qz350) Bool.false 1572865 524288 1 524288 (BSN.sqrt_natCast_div_one 9) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz350) Bool.false 1572865 524288 1 524288 1572865 524288 1 524288 (BSN.sqrt_enclosure 9 1 786432 786433 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep326 := BSN.log_dyadic_bound 1 17 2 1 867 262144 74101 1 1 30876 18 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 1) (BSN.artanhQ 17) 0 1 1 867 1 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz111 := (Real.log (Enclosure.sfrac Bool.false 9 1))

noncomputable def ep327 := @Enclosure.Real.IsNear.mulLit_ff qz17 qz111 63102 1000 0 1 9895417793173221 4503599627370496 1000000000222303 74101000000000000000 312210326792408295771 2251799813685248000 31551000007013881953 37050500000000000000000 qz22 (BSN.isNear_log_sfrac 9 1 9895417793173221 4503599627370496 1000000000222303 74101000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz350) Bool.false 20752195215788806766592 9444732965739290427392 1000000000222303 74101000000000000000 9895417793173221 4503599627370496 1000000000222303 74101000000000000000 (BSN.log_rat_reduce_isNear 9 1 3 18 16 30876 262144 24973259072661432 36028797018963968 74101 1000000000000000 rfl rfl rfl rfl (ep326 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep328 := nat_lit 41031602476778413826715657642501136

noncomputable def ep329 := BSN.cos_dyadic_bound_f 450069538 1073741824 2 1 524288 148347 ep328 ep75 ep328 ep328 ep76 ep328 478900 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 450069538) qz283 0 1 ep328 ep75 ep328 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 450069538) qz284 0 1 ep328 ep76 ep328 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz351 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 72692131) qz20)

noncomputable def ep330 := @Enclosure.Real.IsNear.cos_image qz110 qz351 Bool.false 72692131 524288 447 524288 Bool.false 478900 524288 1 74101 (@Enclosure.Real.IsNear.recentre' qz110 Bool.false 312210326792408295771 2251799813685248000 31551000007013881953 37050500000000000000000 72692131 524288 447 524288 (ep327 rfl) rfl) (Enclosure.sfrac_false_div 72692131 524288) (BSN.cos_reduce0 qz351 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 31670828199822294515712) qz23) 226375608064910080 72057594037927936 Bool.false 478900 524288 22 1000000000000000 148202 74101 (BSN.sin_reduce_arg_pos_rat_q0 72692131 524288 226375608064910080 72057594037927936 22 31670828199822294515712 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 478900 524288 31670828199822294515712 75557863725914323419136 450069538 1073741824 148347 148202 (ep329 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep331 := BSN.sin_dyadic_bound_f 450069538 1073741824 2 1 524288 148347 ep328 ep79 ep328 ep328 ep80 ep328 213381 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 450069538) qz278 0 1 ep328 ep79 ep328 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 450069538) qz279 0 1 ep328 ep80 ep328 rfl rfl rfl rfl) rfl rfl

noncomputable def ep332 := @Enclosure.Real.IsNear.sin_image qz110 qz351 Bool.false 72692131 524288 447 524288 Bool.false 213381 524288 1 74101 (@Enclosure.Real.IsNear.recentre' qz110 Bool.false 312210326792408295771 2251799813685248000 31551000007013881953 37050500000000000000000 72692131 524288 447 524288 (ep327 rfl) rfl) (Enclosure.sfrac_false_div 72692131 524288) (BSN.sin_reduce0 qz351 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 31670828199822294515712) qz23) 226375608064910080 72057594037927936 Bool.false 213381 524288 22 1000000000000000 148202 74101 (BSN.sin_reduce_arg_pos_rat_q0 72692131 524288 226375608064910080 72057594037927936 22 31670828199822294515712 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 213381 524288 31670828199822294515712 75557863725914323419136 450069538 1073741824 148347 148202 (ep331 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz352 := (@Enclosure.Real.IsNear.recentre' qz109 Bool.false 174763 524288 1 524288 174763 524288 1 524288 (ep325 rfl rfl) rfl)

noncomputable def ep333 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz109 (Real.cos qz110)) (@HMul.hMul Real Real Real qz0 qz109 (@Neg.neg Real Real.instNeg (Real.sin qz110))) Bool.false 20923500175 68719476736 739480912405 2546090972807168 Bool.true 37291103703 274877906944 5896172075821 20368727782457344 (@Enclosure.Real.IsNear.mulLit_ff qz109 (Real.cos qz110) 174763 524288 1 524288 119725 131072 33647435 38850265088 20923500175 68719476736 739480912405 2546090972807168 qz352 (@Enclosure.Real.IsNear.recentre' (Real.cos qz110) Bool.false 478900 524288 33647435 38850265088 119725 131072 33647435 38850265088 (ep330 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz109 (@Neg.neg Real Real.instNeg (Real.sin qz110)) 174763 524288 1 524288 213381 524288 33647435 38850265088 37291103703 274877906944 5896172075821 20368727782457344 qz352 (@Enclosure.Real.IsNear.neg (Real.sin qz110) Bool.false 213381 524288 33647435 38850265088 (@Enclosure.Real.IsNear.recentre' (Real.sin qz110) Bool.false 213381 524288 33647435 38850265088 213381 524288 33647435 38850265088 (ep332 rfl rfl) rfl)) rfl)

noncomputable def ep334 := @ep323 20923500175 68719476736 739480912405 2546090972807168 Bool.true 37291103703 274877906944 5896172075821 20368727782457344 Bool.false 33392429194733206634496 485923798911 137438953472 32891009990671 10184363891228672 Bool.false 8734307095483569405952 7943806027 68719476736 32787561289621 10184363891228672 EMRow15.d6 (ep324 ep333) rfl rfl

noncomputable abbrev qz353 := (@Nat.cast Real Real.instNatCast 10)

noncomputable abbrev qz112 := (@Inv.inv Real Real.instInv (Real.sqrt qz353))

noncomputable abbrev qz113 := (@HMul.hMul Real Real Real qz263 qz276 (Real.log (Enclosure.sfrac Bool.false 10 1)))

noncomputable def ep335 := @Enclosure.Complex.IsNear.of_eq qz107 (Complex.mk (@HMul.hMul Real Real Real qz0 qz112 (Real.cos qz113)) (@HMul.hMul Real Real Real qz0 qz112 (@Neg.neg Real Real.instNeg (Real.sin qz113)))) Bool.false 61533322095 274877906944 5618397701897 20368727782457344 Bool.true 61396043835 274877906944 5618336346269 20368727782457344 (BSN.cpow_neg_s_mk qz17 63102 1000 10 qz18 rfl)

noncomputable abbrev qz354 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 10) qz19)

noncomputable def ep336 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz353) 1657945 524288 1 524288 82897 82898 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz353) (Real.sqrt qz354) Bool.false 1657945 524288 1 524288 (BSN.sqrt_natCast_div_one 10) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz354) Bool.false 1657945 524288 1 524288 1657945 524288 1 524288 (BSN.sqrt_enclosure 10 1 828972 828973 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep337 := BSN.log_dyadic_bound 2 18 3 2 1574640 262144 74101 6528 48 58495 20 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 2) (BSN.artanhQ 18) 0 2 6528 1574640 48 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz114 := (Real.log (Enclosure.sfrac Bool.false 10 1))

noncomputable def ep338 := @Enclosure.Real.IsNear.mulLit_ff qz17 qz114 63102 1000 0 1 10369908600166117 4503599627370496 1000000000222303 74101000000000000000 327180986243841157467 2251799813685248000 31551000007013881953 37050500000000000000000 qz22 (BSN.isNear_log_sfrac 10 1 10369908600166117 4503599627370496 1000000000222303 74101000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz354) Bool.false 21747274560655572598784 9444732965739290427392 1000000000222303 74101000000000000000 10369908600166117 4503599627370496 1000000000222303 74101000000000000000 (BSN.log_rat_reduce_isNear 10 1 3 20 16 58495 262144 24973259072661432 36028797018963968 74101 1000000000000000 rfl rfl rfl rfl (ep337 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep339 := nat_lit 1123300473824501165433813784999737163863013694468780527068563042908416404641

noncomputable def ep340 := nat_lit 252917436700130885703978700458005442765462072550802738115261512114662561

noncomputable def ep341 := nat_lit 3369395586600103234530033397598295480703510159261239975729458605701019888801

noncomputable def ep342 := BSN.cos_dyadic_bound_f 842116829 1073741824 3 2 524288 148347 ep339 ep64 ep340 ep341 ep66 ep340 371141 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 842116829) qz283 0 2 ep339 ep64 ep340 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 842116829) qz284 0 2 ep341 ep66 ep340 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz355 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 76177759) qz20)

noncomputable def ep343 := @Enclosure.Real.IsNear.cos_image qz113 qz355 Bool.false 76177759 524288 7 8192 Bool.false 371141 524288 1 74101 (@Enclosure.Real.IsNear.recentre' qz113 Bool.false 327180986243841157467 2251799813685248000 31551000007013881953 37050500000000000000000 76177759 524288 7 8192 (ep338 rfl) rfl) (Enclosure.sfrac_false_div 76177759 524288) (BSN.cos_reduce0 qz355 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 59258703777749341831168) qz23) 226375608064910080 72057594037927936 Bool.false 371141 524288 23 1000000000000000 148202 74101 (BSN.sin_reduce_arg_pos_rat_q0 76177759 524288 226375608064910080 72057594037927936 23 59258703777749341831168 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 371141 524288 59258703777749341831168 75557863725914323419136 842116829 1073741824 148347 148202 (ep342 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep344 := nat_lit 502908974567098857717318826402288081

noncomputable def ep345 := BSN.sin_dyadic_bound_f 842116829 1073741824 2 1 524288 148347 ep344 ep79 ep344 ep344 ep80 ep344 370313 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 842116829) qz278 0 1 ep344 ep79 ep344 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 842116829) qz279 0 1 ep344 ep80 ep344 rfl rfl rfl rfl) rfl rfl

noncomputable def ep346 := @Enclosure.Real.IsNear.sin_image qz113 qz355 Bool.false 76177759 524288 7 8192 Bool.false 370313 524288 1 74101 (@Enclosure.Real.IsNear.recentre' qz113 Bool.false 327180986243841157467 2251799813685248000 31551000007013881953 37050500000000000000000 76177759 524288 7 8192 (ep338 rfl) rfl) (Enclosure.sfrac_false_div 76177759 524288) (BSN.sin_reduce0 qz355 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 59258703777749341831168) qz23) 226375608064910080 72057594037927936 Bool.false 370313 524288 23 1000000000000000 148202 74101 (BSN.sin_reduce_arg_pos_rat_q0 76177759 524288 226375608064910080 72057594037927936 23 59258703777749341831168 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 370313 524288 59258703777749341831168 75557863725914323419136 842116829 1073741824 148347 148202 (ep345 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz356 := (@Enclosure.Real.IsNear.recentre' qz112 Bool.false 165795 524288 1 524288 165795 524288 1 524288 (ep336 rfl rfl) rfl)

noncomputable def ep347 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz112 (Real.cos qz113)) (@HMul.hMul Real Real Real qz0 qz112 (@Neg.neg Real Real.instNeg (Real.sin qz113))) Bool.false 61533322095 274877906944 5618397701897 20368727782457344 Bool.true 61396043835 274877906944 5618336346269 20368727782457344 (@Enclosure.Real.IsNear.mulLit_ff qz112 (Real.cos qz113) 165795 524288 1 524288 371141 524288 526899 607035392 61533322095 274877906944 5618397701897 20368727782457344 qz356 (@Enclosure.Real.IsNear.recentre' (Real.cos qz113) Bool.false 371141 524288 526899 607035392 371141 524288 526899 607035392 (ep343 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz112 (@Neg.neg Real Real.instNeg (Real.sin qz113)) 165795 524288 1 524288 370313 524288 526899 607035392 61396043835 274877906944 5618336346269 20368727782457344 qz356 (@Enclosure.Real.IsNear.neg (Real.sin qz113) Bool.false 370313 524288 526899 607035392 (@Enclosure.Real.IsNear.recentre' (Real.sin qz113) Bool.false 370313 524288 526899 607035392 370313 524288 526899 607035392 (ep346 rfl rfl) rfl)) rfl)

noncomputable def ep348 := @ep321 61533322095 274877906944 5618397701897 20368727782457344 Bool.true 61396043835 274877906944 5618336346269 20368727782457344 Bool.false 142026792171325121101824 1033380919917 274877906944 71400417683239 20368727782457344 Bool.true 2035527232130826371072 29620819727 274877906944 71193458925511 20368727782457344 (ep322 (BSN.head_sum_c_succ qz6 9 10 rfl rfl) (ep334 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep335 ep347) rfl rfl

noncomputable abbrev qz357 := (@Nat.cast Real Real.instNatCast 11)

noncomputable abbrev qz115 := (@Inv.inv Real Real.instInv (Real.sqrt qz357))

noncomputable abbrev qz116 := (@HMul.hMul Real Real Real qz263 qz276 (Real.log (Enclosure.sfrac Bool.false 11 1)))

noncomputable def ep349 := @Enclosure.Complex.IsNear.of_eq qz106 (Complex.mk (@HMul.hMul Real Real Real qz0 qz115 (Real.cos qz116)) (@HMul.hMul Real Real Real qz0 qz115 (@Neg.neg Real Real.instNeg (Real.sin qz116)))) Bool.false 36057029505 137438953472 2682252273035 10184363891228672 Bool.true 40846823205 274877906944 5349847738775 20368727782457344 (BSN.cpow_neg_s_mk qz17 63102 1000 11 qz18 rfl)

noncomputable abbrev qz358 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 11) qz19)

noncomputable def ep350 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz357) 1738867 524288 1 524288 79039 79040 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz357) (Real.sqrt qz358) Bool.false 1738867 524288 1 524288 (BSN.sqrt_natCast_div_one 11) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz358) Bool.false 1738867 524288 1 524288 1738867 524288 1 524288 (BSN.sqrt_enclosure 11 1 869433 869434 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep351 := BSN.log_dyadic_bound 3 19 4 3 4939817505 262144 74101 41676111 10935 83480 22 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 3) (BSN.artanhQ 19) 0 3 41676111 4939817505 10935 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz117 := (Real.log (Enclosure.sfrac Bool.false 11 1))

noncomputable def ep352 := @Enclosure.Real.IsNear.mulLit_ff qz17 qz117 63102 1000 0 1 10799147631728357 4503599627370496 1000000000222303 74101000000000000000 340723906928661391707 2251799813685248000 31551000007013881953 37050500000000000000000 qz22 (BSN.isNear_log_sfrac 11 1 10799147631728357 4503599627370496 1000000000222303 74101000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz358) Bool.false 22647454054174387339264 9444732965739290427392 1000000000222303 74101000000000000000 10799147631728357 4503599627370496 1000000000222303 74101000000000000000 (BSN.log_rat_reduce_isNear 11 1 3 22 16 83480 262144 24973259072661432 36028797018963968 74101 1000000000000000 rfl rfl rfl rfl (ep351 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep353 := nat_lit 93766911931076588276793641156897761

noncomputable def ep354 := BSN.cos_dyadic_bound_f 553365913 1073741824 2 1 524288 148347 ep353 ep75 ep353 ep353 ep76 ep353 456190 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 553365913) qz283 0 1 ep353 ep75 ep353 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 553365913) qz284 0 1 ep353 ep76 ep353 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz359 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 39665483) qz28)

noncomputable def ep355 := @Enclosure.Real.IsNear.cos_image qz116 qz359 Bool.false 39665483 262144 7 8192 Bool.false 456190 524288 1 74101 (@Enclosure.Real.IsNear.recentre' qz116 Bool.false 340723906928661391707 2251799813685248000 31551000007013881953 37050500000000000000000 39665483 262144 7 8192 (ep352 rfl) rfl) (Enclosure.sfrac_false_div 39665483 262144) (BSN.cos_reduce0 qz359 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 19469832210156152160256) qz289) 226375608064910080 72057594037927936 Bool.false 456190 524288 24 1000000000000000 148202 74101 (BSN.sin_reduce_arg_pos_rat_q0 39665483 262144 226375608064910080 72057594037927936 24 19469832210156152160256 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 456190 524288 19469832210156152160256 37778931862957161709568 553365913 1073741824 148347 148202 (ep354 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep356 := BSN.sin_dyadic_bound_f 553365913 1073741824 2 1 524288 148347 ep353 ep79 ep353 ep353 ep80 ep353 258395 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 553365913) qz278 0 1 ep353 ep79 ep353 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 553365913) qz279 0 1 ep353 ep80 ep353 rfl rfl rfl rfl) rfl rfl

noncomputable def ep357 := @Enclosure.Real.IsNear.sin_image qz116 qz359 Bool.false 39665483 262144 7 8192 Bool.false 258395 524288 1 74101 (@Enclosure.Real.IsNear.recentre' qz116 Bool.false 340723906928661391707 2251799813685248000 31551000007013881953 37050500000000000000000 39665483 262144 7 8192 (ep352 rfl) rfl) (Enclosure.sfrac_false_div 39665483 262144) (BSN.sin_reduce0 qz359 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 19469832210156152160256) qz289) 226375608064910080 72057594037927936 Bool.false 258395 524288 24 1000000000000000 148202 74101 (BSN.sin_reduce_arg_pos_rat_q0 39665483 262144 226375608064910080 72057594037927936 24 19469832210156152160256 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 258395 524288 19469832210156152160256 37778931862957161709568 553365913 1073741824 148347 148202 (ep356 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz360 := (@Enclosure.Real.IsNear.recentre' qz115 Bool.false 158079 524288 1 524288 158079 524288 1 524288 (ep350 rfl rfl) rfl)

noncomputable def ep358 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz115 (Real.cos qz116)) (@HMul.hMul Real Real Real qz0 qz115 (@Neg.neg Real Real.instNeg (Real.sin qz116))) Bool.false 36057029505 137438953472 2682252273035 10184363891228672 Bool.true 40846823205 274877906944 5349847738775 20368727782457344 (@Enclosure.Real.IsNear.mulLit_ff qz115 (Real.cos qz116) 158079 524288 1 524288 228095 262144 526899 607035392 36057029505 137438953472 2682252273035 10184363891228672 qz360 (@Enclosure.Real.IsNear.recentre' (Real.cos qz116) Bool.false 456190 524288 526899 607035392 228095 262144 526899 607035392 (ep355 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz115 (@Neg.neg Real Real.instNeg (Real.sin qz116)) 158079 524288 1 524288 258395 524288 526899 607035392 40846823205 274877906944 5349847738775 20368727782457344 qz360 (@Enclosure.Real.IsNear.neg (Real.sin qz116) Bool.false 258395 524288 526899 607035392 (@Enclosure.Real.IsNear.recentre' (Real.sin qz116) Bool.false 258395 524288 526899 607035392 258395 524288 526899 607035392 (ep357 rfl rfl) rfl)) rfl)

noncomputable def ep359 := @ep319 36057029505 137438953472 2682252273035 10184363891228672 Bool.true 40846823205 274877906944 5349847738775 20368727782457344 Bool.false 151938072972277573484544 1105494978927 274877906944 76764922229309 20368727782457344 Bool.true 19369998196425315319808 17616910733 68719476736 38271653332143 10184363891228672 (ep320 (BSN.head_sum_c_succ qz6 10 11 rfl rfl) (ep348 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep349 ep358) rfl rfl

noncomputable abbrev qz361 := (@Nat.cast Real Real.instNatCast 12)

noncomputable abbrev qz118 := (@Inv.inv Real Real.instInv (Real.sqrt qz361))

noncomputable abbrev qz119 := (@HMul.hMul Real Real Real qz263 qz276 (Real.log (Enclosure.sfrac Bool.false 12 1)))

noncomputable def ep360 := @Enclosure.Complex.IsNear.of_eq qz105 (Complex.mk (@HMul.hMul Real Real Real qz0 qz118 (Real.cos qz119)) (@HMul.hMul Real Real Real qz0 qz118 (@Neg.neg Real Real.instNeg (Real.sin qz119)))) Bool.false 76323030465 274877906944 5141122496385 20368727782457344 Bool.false 21708743815 274877906944 5114383150535 20368727782457344 (BSN.cpow_neg_s_mk qz17 63102 1000 12 qz18 rfl)

noncomputable abbrev qz362 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 12) qz19)

noncomputable def ep361 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz361) 1816187 524288 1 524288 75674 75675 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz361) (Real.sqrt qz362) Bool.false 1816187 524288 1 524288 (BSN.sqrt_natCast_div_one 12) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz362) Bool.false 1816187 524288 1 524288 1816187 524288 1 524288 (BSN.sqrt_enclosure 12 1 908093 908094 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep362 := BSN.log_dyadic_bound 4 20 4 3 6720000000 262144 74101 91811840 61440 106290 24 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 4) (BSN.artanhQ 20) 0 3 91811840 6720000000 61440 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz120 := (Real.log (Enclosure.sfrac Bool.false 12 1))

noncomputable def ep363 := @Enclosure.Real.IsNear.mulLit_ff qz17 qz120 63102 1000 0 1 11191020447815397 4503599627370496 1000000000222303 74101000000000000000 353087886149023590747 2251799813685248000 31551000007013881953 37050500000000000000000 qz22 (BSN.isNear_log_sfrac 12 1 11191020447815397 4503599627370496 1000000000222303 74101000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz362) Bool.false 23469270914176955449344 9444732965739290427392 1000000000222303 74101000000000000000 11191020447815397 4503599627370496 1000000000222303 74101000000000000000 (BSN.log_rat_reduce_isNear 12 1 3 24 16 106290 262144 24973259072661432 36028797018963968 74101 1000000000000000 rfl rfl rfl rfl (ep362 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep364 := nat_lit 14979372747966382041223124453001122128998569294605152627768885900797909213440

noncomputable def ep365 := nat_lit 13861829834451789317536491767460553059448784666357499782898548318893056256

noncomputable def ep366 := nat_lit 39209247567799031020498838294998478966233335834506059025460484471478221086976

noncomputable def ep367 := BSN.sin_dyadic_bound_f 1389080998 1073741824 3 2 524288 148347 ep364 ep57 ep365 ep366 ep60 ep365 504285 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1389080998) qz278 0 2 ep364 ep57 ep365 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1389080998) qz279 0 2 ep366 ep60 ep365 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz363 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 82209679) qz20)

noncomputable def ep368 := @Enclosure.Real.IsNear.cos_image qz119 qz363 Bool.false 82209679 524288 7 8192 Bool.false 504285 524288 1 74101 (@Enclosure.Real.IsNear.recentre' qz119 Bool.false 353087886149023590747 2251799813685248000 31551000007013881953 37050500000000000000000 82209679 524288 7 8192 (ep363 rfl) rfl) (Enclosure.sfrac_false_div 82209679 524288) (BSN.cos_reduce3 qz363 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 97747885428316861104128) qz23) 226375608064910080 72057594037927936 Bool.false 504285 524288 24 1000000000000000 148202 74101 (BSN.sin_reduce_arg_pos_rat_q3 82209679 524288 226375608064910080 72057594037927936 24 97747885428316861104128 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 504285 524288 97747885428316861104128 75557863725914323419136 1389080998 1073741824 148347 148202 (ep367 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep369 := nat_lit 8328034562129968595931752025786161428581182401299021459775113744140568699136

noncomputable def ep370 := nat_lit 24956380026721002209160183093823563179624649634564349379759544135783919984896

noncomputable def ep371 := BSN.cos_dyadic_bound_f 1389080998 1073741824 3 2 524288 148347 ep369 ep64 ep365 ep370 ep66 ep365 143435 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1389080998) qz283 0 2 ep369 ep64 ep365 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1389080998) qz284 0 2 ep370 ep66 ep365 rfl rfl rfl rfl) rfl rfl

noncomputable def ep372 := @Enclosure.Real.IsNear.sin_image qz119 qz363 Bool.false 82209679 524288 7 8192 Bool.true 143435 524288 1 74101 (@Enclosure.Real.IsNear.recentre' qz119 Bool.false 353087886149023590747 2251799813685248000 31551000007013881953 37050500000000000000000 82209679 524288 7 8192 (ep363 rfl) rfl) (Enclosure.sfrac_false_div 82209679 524288) (BSN.sin_reduce3 qz363 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 97747885428316861104128) qz23) 226375608064910080 72057594037927936 Bool.false 143435 524288 24 1000000000000000 148202 74101 (BSN.sin_reduce_arg_pos_rat_q3 82209679 524288 226375608064910080 72057594037927936 24 97747885428316861104128 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 143435 524288 97747885428316861104128 75557863725914323419136 1389080998 1073741824 148347 148202 (ep371 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz364 := (@Enclosure.Real.IsNear.recentre' qz118 Bool.false 151349 524288 1 524288 151349 524288 1 524288 (ep361 rfl rfl) rfl)

noncomputable def ep373 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz118 (Real.cos qz119)) (@HMul.hMul Real Real Real qz0 qz118 (@Neg.neg Real Real.instNeg (Real.sin qz119))) Bool.false 76323030465 274877906944 5141122496385 20368727782457344 Bool.false 21708743815 274877906944 5114383150535 20368727782457344 (@Enclosure.Real.IsNear.mulLit_ff qz118 (Real.cos qz119) 151349 524288 1 524288 504285 524288 526899 607035392 76323030465 274877906944 5141122496385 20368727782457344 qz364 (@Enclosure.Real.IsNear.recentre' (Real.cos qz119) Bool.false 504285 524288 526899 607035392 504285 524288 526899 607035392 (ep368 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz118 (@Neg.neg Real Real.instNeg (Real.sin qz119)) 151349 524288 1 524288 143435 524288 526899 607035392 21708743815 274877906944 5114383150535 20368727782457344 qz364 (@Enclosure.Real.IsNear.neg (Real.sin qz119) Bool.true 143435 524288 526899 607035392 (@Enclosure.Real.IsNear.recentre' (Real.sin qz119) Bool.true 143435 524288 526899 607035392 143435 524288 526899 607035392 (ep372 rfl rfl) rfl)) rfl)

noncomputable def ep374 := @ep317 76323030465 274877906944 5141122496385 20368727782457344 Bool.false 21708743815 274877906944 5114383150535 20368727782457344 Bool.false 324855660810397494018048 73863625587 17179869184 40953022362847 10184363891228672 Bool.true 3350686033543652442112 48758899117 274877906944 81657689814821 20368727782457344 (ep318 (BSN.head_sum_c_succ qz6 11 12 rfl rfl) (ep359 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep360 ep373) rfl rfl

noncomputable def ep375 := @Enclosure.Complex.IsNear.mul qz100 (@HAdd.hAdd Complex Complex Complex qz5 qz101 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz103 qz104 (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz54 2 k) 1))))) Bool.true 495669374628600797146333 ep175 ep310 ep177 Bool.false

noncomputable abbrev qz121 := (Complex.re qz346)

noncomputable abbrev qz122 := (Complex.im qz346)

noncomputable def ep376 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 qz121 (Complex.re (@HAdd.hAdd Complex Complex Complex qz5 qz101 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz103 qz104 (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz54 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz122 (Complex.im (@HAdd.hAdd Complex Complex Complex qz5 qz101 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz103 qz104 (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz54 2 k) 1))))))) 90773425122141175589 10672298547565786300416 190653654106163677582433

noncomputable def ep377 := nat_lit 1581655989346344661294252032

noncomputable def ep378 := nat_lit 20277640889055700785823744000

noncomputable def ep379 := nat_lit 135639270433888663941755892341490339442327552

noncomputable def ep380 := @Enclosure.Real.IsNear.mulLit_ff qz121 (Complex.re (@HAdd.hAdd Complex Complex Complex qz5 qz101 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz103 qz104 (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))))) 582661877 34359738368 1223779049969 5092181945614336 155790911857

noncomputable abbrev qz365 := (@Nat.cast Real Real.instNatCast 13)

noncomputable abbrev qz123 := (@Inv.inv Real Real.instInv (Real.sqrt qz365))

noncomputable abbrev qz366 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) qz453 (Real.log (Enclosure.sfrac Bool.false 13 1)))

noncomputable abbrev qz124 := (Real.cos qz366)

noncomputable abbrev qz125 := (@Neg.neg Real Real.instNeg (Real.sin qz366))

noncomputable def ep381 := @Enclosure.Complex.IsNear.of_eq qz100 (Complex.mk (@HMul.hMul Real Real Real qz0 qz123 qz124) (@HMul.hMul Real Real Real qz0 qz123 qz125)) Bool.false 582661877 34359738368 1223779049969 5092181945614336 Bool.false 38047224383 137438953472 2465759158063 10184363891228672 (BSN.cpow_neg_s_mk qz17 63102 1000 13 qz18 rfl)

noncomputable abbrev qz367 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 13) qz19)

noncomputable def ep382 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz365) 1890347 524288 1 524288 72705 72706 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz365) (Real.sqrt qz367) Bool.false 1890347 524288 1 524288 (BSN.sqrt_natCast_div_one 13) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz367) Bool.false 1890347 524288 1 524288 1890347 524288 1 524288 (BSN.sqrt_enclosure 13 1 945173 945174 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep383 := BSN.log_dyadic_bound 5 21 5 4 35742602096145 262144 74101 699352521000 41015625 127272 26 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 5) (BSN.artanhQ 21) 0 4 699352521000 35742602096145 41015625 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz368 := (Real.log (Enclosure.sfrac Bool.false 13 1))

noncomputable abbrev qz126 := qz368

noncomputable abbrev qz369 := (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 13) qz19))

noncomputable def ep384 := @Enclosure.Real.IsNear.mulLit_ff qz17 qz126 63102 1000 0 1 11551488463034085 4503599627370496 1000000000222303 74101000000000000000 72892202499437683167 450359962737049600 31551000007013881953 37050500000000000000000 qz22 (BSN.isNear_log_sfrac 13 1 11551488463034085 4503599627370496 1000000000222303 74101000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' qz369 Bool.false 24225227133228857425920 9444732965739290427392 1000000000222303 74101000000000000000 11551488463034085 4503599627370496 1000000000222303 74101000000000000000 (BSN.log_rat_reduce_isNear 13 1 3 26 16 127272 262144 24973259072661432 36028797018963968 74101 1000000000000000 rfl rfl rfl rfl (ep383 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep385 := BSN.sin_dyadic_bound_f 65692770 1073741824 1 0 524288 148347 0 1 1 0 1 1 32056 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 65692770) qz278 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 65692770) qz279 0 0 rfl) rfl rfl

noncomputable abbrev qz127 := qz366

noncomputable abbrev qz370 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 21214423) (@Nat.cast Real Real.instNatCast 131072))

noncomputable def ep386 := @Enclosure.Real.IsNear.cos_image qz127 qz370 Bool.false 21214423 131072 447 524288 Bool.false 32056 524288 1 74101 (@Enclosure.Real.IsNear.recentre' qz127 Bool.false 72892202499437683167 450359962737049600 31551000007013881953 37050500000000000000000 21214423 131072 447 524288 (ep384 rfl) rfl) (Enclosure.sfrac_false_div 21214423 131072) (BSN.cos_reduce3 qz370 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 1155679436521473048576) qz298) 226375608064910080 72057594037927936 Bool.false 32056 524288 25 1000000000000000 148202 74101 (BSN.sin_reduce_arg_pos_rat_q3 21214423 131072 226375608064910080 72057594037927936 25 1155679436521473048576 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 32056 524288 1155679436521473048576 18889465931478580854784 65692770 1073741824 148347 148202 (ep385 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep387 := BSN.cos_dyadic_bound_f 65692770 1073741824 1 0 524288 148347 0 1 1 0 1 1 523306 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 65692770) qz283 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 65692770) qz284 0 0 rfl) rfl rfl

noncomputable def ep388 := @Enclosure.Real.IsNear.sin_image qz127 qz370 Bool.false 21214423 131072 447 524288 Bool.true 523306 524288 1 74101 (@Enclosure.Real.IsNear.recentre' qz127 Bool.false 72892202499437683167 450359962737049600 31551000007013881953 37050500000000000000000 21214423 131072 447 524288 (ep384 rfl) rfl) (Enclosure.sfrac_false_div 21214423 131072) (BSN.sin_reduce3 qz370 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 1155679436521473048576) qz298) 226375608064910080 72057594037927936 Bool.false 523306 524288 25 1000000000000000 148202 74101 (BSN.sin_reduce_arg_pos_rat_q3 21214423 131072 226375608064910080 72057594037927936 25 1155679436521473048576 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 523306 524288 1155679436521473048576 18889465931478580854784 65692770 1073741824 148347 148202 (ep387 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz128 := (Real.sin qz366)

noncomputable abbrev qz371 := (@Enclosure.Real.IsNear.recentre' qz123 Bool.false 145411 524288 1 524288 145411 524288 1 524288 (ep382 rfl rfl) rfl)

noncomputable def ep389 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz123 qz124) (@HMul.hMul Real Real Real qz0 qz123 qz125) Bool.false 582661877 34359738368 1223779049969 5092181945614336 Bool.false 38047224383 137438953472 2465759158063 10184363891228672 (@Enclosure.Real.IsNear.mulLit_ff qz123 qz124 145411 524288 1 524288 4007 65536 33647435 38850265088 582661877 34359738368 1223779049969 5092181945614336 qz371 (@Enclosure.Real.IsNear.recentre' qz124 Bool.false 32056 524288 33647435 38850265088 4007 65536 33647435 38850265088 (ep386 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz123 qz125 145411 524288 1 524288 261653 262144 33647435 38850265088 38047224383 137438953472 2465759158063 10184363891228672 qz371 (@Enclosure.Real.IsNear.neg qz128 Bool.true 261653 262144 33647435 38850265088 (@Enclosure.Real.IsNear.recentre' qz128 Bool.true 523306 524288 33647435 38850265088 261653 262144 33647435 38850265088 (ep388 rfl rfl) rfl)) rfl)

noncomputable def ep390 := @ep380 310604767512 0 1 90773425122141175589 10672298547565786300416 190653654106163677582433 ep377 (@Enclosure.Complex.IsNear.re_isNear qz100 Bool.false 582661877 34359738368 1223779049969 5092181945614336 Bool.false 38047224383 137438953472 2465759158063 10184363891228672 (ep381 ep389))

noncomputable def ep391 := @Enclosure.Complex.IsNear.re_isNear (@HAdd.hAdd Complex Complex Complex qz5 qz101 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz103 qz104 (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz54 2 k) 1))))) Bool.false 155790911857 310604767512 0 1 Bool.false

noncomputable def ep392 := @Enclosure.Complex.IsNear.addLitP qz101 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz103 qz104 (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) Bool.false 992278101 1991056202 0 1 Bool.true 205081500

noncomputable def ep393 := @ep392 995528101 0 1 Bool.false 1 312 0 1 Bool.false 809 2000 0 1 Bool.false 311581823714 155790911857 310604767512 0 1 Bool.false 395219233709 395219233709 1991056202000 0 1

noncomputable abbrev qz129 := (@HDiv.hDiv Complex Complex Complex qz320 qz347 (@HSub.hSub Complex Complex Complex qz313 qz268 (1 : Complex)))

noncomputable def ep394 := @Enclosure.Complex.IsNear.addLitP qz129 qz75 Bool.true 26000000 15928449616 0 1 Bool.true 3281304000 15928449616 0 1

noncomputable def ep395 := @Enclosure.Complex.IsNear.of_eq qz129 (Complex.mk (Enclosure.sfrac Bool.true 26000000 15928449616) (Enclosure.sfrac Bool.true 3281304000 15928449616)) Bool.true 26000000 15928449616 0 1 Bool.true 3281304000 15928449616 0 1

noncomputable def ep396 := @ep394 Bool.false 1 2 0 1 Bool.false 0 1 0 1 Bool.false 15876449616 992278101 1991056202 0 1 Bool.true 3281304000 205081500 995528101 0 1 (ep395 (BSN.N_div_s_sub_one_mk qz17 63102 1000 13 qz18 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 26000000 15928449616) (Enclosure.sfrac Bool.true 3281304000 15928449616) Bool.true 26000000 15928449616 0 1 Bool.true 3281304000 15928449616 0 1 (Enclosure.Real.IsNear.const Bool.true 26000000 15928449616) (Enclosure.Real.IsNear.const Bool.true 3281304000 15928449616))) qz76 rfl

noncomputable abbrev qz130 := (@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 1)))

noncomputable abbrev qz372 := (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz461 qz462 1))

noncomputable abbrev qz131 := qz372

noncomputable def ep397 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz103 qz104 (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@HAdd.hAdd Complex Complex Complex qz5 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz103 qz104 (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz130) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1))) qz131)) Bool.false 1 312 0 1

noncomputable def ep398 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz103 qz104 (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz130) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1))) qz131) Bool.false 0 1 0 1 Bool.false

noncomputable def ep399 := @ep398 0 1 0 1 Bool.false 1 312 0 1 Bool.false 809 2000 0 1 Bool.false 1 1 312 0 1 Bool.false 809 809 2000 0

noncomputable def ep400 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz103 qz104 (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (Complex.mk qz14 qz14) Bool.false 0 1 0 1 Bool.false

noncomputable def ep401 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz130) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1))) qz131 Bool.false 1 312 0 1 Bool.false 809 2000 0 1

noncomputable abbrev qz132 := (Complex.re qz372)

noncomputable abbrev qz133 := (Complex.im qz372)

noncomputable def ep402 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz130) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)))) qz132) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz130) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)))) qz133) 1 312 0 1 0 1 0

noncomputable def ep403 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz130) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)))) qz132 1 24 0 1 1 13 0 1 1

noncomputable def ep404 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz130)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz130)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)))) 1 24 0 1 0 1 0 1 1

noncomputable def ep405 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz130)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 1 2 0 1 1 24 0

noncomputable def ep406 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz130) (Complex.mk (Enclosure.sfrac Bool.false 1 12) qz14) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (BSN.bern_coeff_mk 1 1 6 2 Bool.false BSN.bern_real_1 EMRow15.d7 rfl) qz337

noncomputable def ep407 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)) qz6 Bool.false 1 2 0 1 Bool.false 63102 1000 0 1 (BSN.ascPochhammer_one_eval qz6)

noncomputable def ep408 := ep407 (@Enclosure.Complex.IsNear.of_eq qz6 (Complex.mk qz70 qz17) Bool.false 1 2 0 1 Bool.false 63102 1000 0 1 (BSN.s_crit_mk qz17 Bool.false 63102 1000 qz18) (@Enclosure.Complex.IsNear.mk qz70 qz17 Bool.false 1 2 0 1 Bool.false 63102 1000 0 1 qz329 qz22))

noncomputable def ep409 := @ep405 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz130) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep406) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 63102 1000 0 1 ep408)

noncomputable def ep410 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz130)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 63102 1000 0 1 0 1 0

noncomputable def ep411 := @ep410 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz130) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep406) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 63102 1000 0 1 ep408)

noncomputable def ep412 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz130)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz130)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)))) 10517 2000 0 1 0 1 0 1 10517

noncomputable def ep413 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz130)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 63102 1000 0 1 10517 2000 0

noncomputable def ep414 := @ep413 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz130) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep406) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 63102 1000 0 1 ep408)

noncomputable def ep415 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz130)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 1 2 0 1 0 1 0

noncomputable def ep416 := @ep415 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz130) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep406) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 63102 1000 0 1 ep408)

noncomputable def ep417 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz130) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 24 0 1 Bool.false 10517 2000 0 1 (@ep404 1 24 0 1 (ep409 rfl) (ep411 rfl) rfl rfl) (@ep412 10517 2000 0 1 (ep414 rfl) (ep416 rfl) rfl rfl)

noncomputable def ep418 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz130) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 10517 2000 0 1 ep417

noncomputable abbrev qz134 := (@Enclosure.Complex.IsNear.of_eq qz372 (Complex.mk (Enclosure.sfrac Bool.false 1 13) qz274) Bool.false 1 13 0 1 Bool.false 0 1 0 1 (BSN.natCast_pow_inv_mk 13 1 13 EMRow15.d8 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 13) qz274 Bool.false 1 13 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 13) qz286))

noncomputable def ep419 := @ep403 312 0 1 ep418 (@Enclosure.Complex.IsNear.re_isNear qz131 Bool.false 1 13 0 1 Bool.false 0 1 0 1 qz134)

noncomputable def ep420 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz130) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)))) qz133 10517 2000 0 1 0 1 0 1 0

noncomputable def ep421 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz130) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 10517 2000 0 1 ep417

noncomputable def ep422 := @ep420 1 0 1 ep421 (@Enclosure.Complex.IsNear.im_isNear qz131 Bool.false 1 13 0 1 Bool.false 0 1 0 1 qz134)

noncomputable def ep423 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz130) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)))) qz133) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz130) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)))) qz132) 0 1 0 1 809 2000 0

noncomputable def ep424 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz130) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)))) qz133 1 24 0 1 0 1 0 1 0

noncomputable def ep425 := @ep424 1 0 1 ep418 (@Enclosure.Complex.IsNear.im_isNear qz131 Bool.false 1 13 0 1 Bool.false 0 1 0 1 qz134)

noncomputable def ep426 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz130) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)))) qz132 10517 2000 0 1 1 13 0 1 809

noncomputable def ep427 := @ep426 2000 0 1 ep421 (@Enclosure.Complex.IsNear.re_isNear qz131 Bool.false 1 13 0 1 Bool.false 0 1 0 1 qz134)

noncomputable def ep428 := @ep399 1 (@ep400 0 1 0 1 (BSN.bern_sum_base qz6 13) qz92) (ep401 (@ep402 1 1 1 312 0 1 (ep419 rfl) (ep422 rfl) rfl rfl) (@ep423 1 809 809 2000 0 1 (ep425 rfl) (ep427 rfl) rfl rfl)) rfl rfl rfl rfl rfl

noncomputable def ep429 := ep393 (ep396 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep397 Bool.false 809 2000 0 1 (BSN.bern_sum_succ qz6 13 0 1 1 rfl rfl) (ep428 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl rfl

noncomputable def ep430 := @Enclosure.Real.IsNear.mulLit_ff qz122 (Complex.im (@HAdd.hAdd Complex Complex Complex qz5 qz101 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz103 qz104 (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))))) 38047224383 137438953472 2465759158063 10184363891228672 395219233709

noncomputable def ep431 := @ep430 1991056202000 0 1 15036994865403640326547 273648680706815033344000 974515444960607868745667 ep378 (@Enclosure.Complex.IsNear.im_isNear qz100 Bool.false 582661877 34359738368 1223779049969 5092181945614336 Bool.false 38047224383 137438953472 2465759158063 10184363891228672 (ep381 ep389))

noncomputable def ep432 := @Enclosure.Complex.IsNear.im_isNear (@HAdd.hAdd Complex Complex Complex qz5 qz101 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz103 qz104 (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz54 2 k) 1))))) Bool.false 155790911857 310604767512 0 1 Bool.false

noncomputable def ep433 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz121 (Complex.im (@HAdd.hAdd Complex Complex Complex qz5 qz101 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz103 qz104 (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz54 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz122 (Complex.re (@HAdd.hAdd Complex Complex Complex qz5 qz101 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz103 qz104 (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz54 2 k) 1))))))) 230279180539387611793 68412170176703758336000 483661018357876200205021

noncomputable def ep434 := nat_lit 10138820444527850392911872000

noncomputable def ep435 := nat_lit 3163311978692689322588504064

noncomputable def ep436 := nat_lit 415337536074255299130259827103938936729239552

noncomputable def ep437 := @Enclosure.Real.IsNear.mulLit_ff qz121 (Complex.im (@HAdd.hAdd Complex Complex Complex qz5 qz101 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz103 qz104 (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))))) 582661877 34359738368 1223779049969 5092181945614336 395219233709

noncomputable def ep438 := @ep437 1991056202000 0 1 230279180539387611793 68412170176703758336000 483661018357876200205021 ep434 (@Enclosure.Complex.IsNear.re_isNear qz100 Bool.false 582661877 34359738368 1223779049969 5092181945614336 Bool.false 38047224383 137438953472 2465759158063 10184363891228672 (ep381 ep389))

noncomputable def ep439 := @Enclosure.Real.IsNear.mulLit_ff qz122 (Complex.re (@HAdd.hAdd Complex Complex Complex qz5 qz101 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz103 qz104 (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))))) 38047224383 137438953472 2465759158063 10184363891228672 155790911857

noncomputable def ep440 := @ep439 310604767512 0 1 5927411780255454209231 42689194190263145201664 384142867654383363852991 ep435 (@Enclosure.Complex.IsNear.im_isNear qz100 Bool.false 582661877 34359738368 1223779049969 5092181945614336 Bool.false 38047224383 137438953472 2465759158063 10184363891228672 (ep381 ep389))

noncomputable abbrev qz373 := (ep429 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable def ep441 := @ep375 758888248614004009873729 ep305 ep311 ep307 (@ep376 ep377 15036994865403640326547 273648680706815033344000 974515444960607868745667 ep378 ep379 495669374628600797146333 ep175 ep310 ep177 (ep390 (@ep391 395219233709 1991056202000 0 1 qz373) rfl) (ep431 (@ep432 395219233709 1991056202000 0 1 qz373) rfl) rfl rfl) (@ep433 ep434 5927411780255454209231 42689194190263145201664 384142867654383363852991 ep435 ep436 758888248614004009873729 ep305 ep311 ep307 (ep438 (@ep432 395219233709 1991056202000 0 1 qz373) rfl) (ep440 (@ep391 395219233709 1991056202000 0 1 qz373) rfl) rfl rfl)

noncomputable def ep442 := @ep314 ep306 ep307 (@ep315 20368727782457344 (BSN.head_sum_c_eq qz6 13) (ep316 (BSN.head_sum_c_succ qz6 12 13 rfl rfl) (ep374 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))) ep441 rfl rfl rfl

noncomputable def ep443 := @Enclosure.Complex.IsNear.re_isNear (zetaApproximant qz6 1 13) Bool.false ep174 ep175 ep176 ep177 Bool.true 187658409159548933057771 ep305 ep306 ep307 (@ep308 ep177 Bool.true 187658409159548933057771 ep305 ep306 ep307 (BSN.zetaApproximant_eq_folded' qz6 1 13 rfl) (ep442 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

noncomputable def ep444 := @Enclosure.Real.IsNear.mulLit_tt (Real.sin (@HSub.hSub Real Real Real qz46 (Complex.im (@HSub.hSub Complex Complex Complex qz47 qz48 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz49 (@Nat.cast Complex Complex.instNatCast j))))) qz50)) (Complex.im (zetaApproximant qz6 1 13)) 79 524288 3762021

noncomputable def ep445 := @Enclosure.Real.IsNear.recentre' (Real.sin (@HSub.hSub Real Real Real qz46 (Complex.im (@HSub.hSub Complex Complex Complex qz47 qz48 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz49 (@Nat.cast Complex Complex.instNatCast j))))) qz50)) Bool.true 79 524288 3762021

noncomputable def ep446 := @Enclosure.Real.IsNear.sin_image (@HSub.hSub Real Real Real qz46 (Complex.im (@HSub.hSub Complex Complex Complex qz47 qz48 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz49 (@Nat.cast Complex Complex.instNatCast j))))) qz50) qz316 Bool.false 21412371 524288 49

noncomputable def ep447 := BSN.sin_dyadic_bound_f 163268 1073741824 1 0 524288 148347 0 1 1 0 1 1 79 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 163268) qz278 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 163268) qz279 0 0 rfl) rfl rfl

noncomputable def ep448 := @ep446 131072 Bool.true 79 524288 1 74101 (@ep182 21412371 524288 49 131072 ep302 rfl) (Enclosure.sfrac_false_div 21412371 524288) (BSN.sin_reduce2 qz316 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 11488985477097193472) qz23) 226375608064910080 72057594037927936 Bool.false 79 524288 6 1000000000000000 148202 74101 (BSN.sin_reduce_arg_pos_rat_q2 21412371 524288 226375608064910080 72057594037927936 6 11488985477097193472 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 79 524288 11488985477097193472 75557863725914323419136 163268 1073741824 148347 148202 (ep447 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep449 := @Enclosure.Complex.IsNear.im_isNear (zetaApproximant qz6 1 13) Bool.false ep174 ep175 ep176 ep177 Bool.true 187658409159548933057771 ep305 ep306 ep307 (@ep308 ep177 Bool.true 187658409159548933057771 ep305 ep306 ep307 (BSN.zetaApproximant_eq_folded' qz6 1 13 rfl) (ep442 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

theorem EMRow15.d9 : Enclosure.Real.IsNear (hardyZApproximantEM 1 13 qz17) Bool.true ep158 ep159 ep160 ep161 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantEM 1 13 qz17) ep162 Bool.true ep158 ep159 ep160 ep161 (@Eq.refl Real ep162) (@ep163 Bool.true ep158 ep159 ep160 ep161 (BSN.re_exp_mul (@HSub.hSub Real Real Real qz46 (Complex.im (@HSub.hSub Complex Complex Complex qz47 qz48 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz49 (@Nat.cast Complex Complex.instNatCast j))))) qz50) (zetaApproximant qz6 1 13)) (@ep165 ep166 ep167 ep161 ep168 ep169 ep170 ep171 ep172 ep158 ep159 ep160 ep161 (@ep173 9712566272 ep174 ep175 ep176 ep177 ep164 ep166 ep167 ep161 (@ep178 9712566272 524287 524288 3762021 9712566272 (ep304 rfl rfl) rfl) ep443 rfl) (@ep444 9712566272 187658409159548933057771 ep305 ep306 ep307 ep168 ep169 ep170 ep171 (@ep445 9712566272 79 524288 3762021 9712566272 (ep448 rfl rfl) rfl) ep449 rfl) rfl rfl))

noncomputable abbrev qz478 := (@HAdd.hAdd Complex Complex Complex (@instHAdd Complex Complex.instAdd) (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (2 : Complex)) (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul) Complex.I ↑(Enclosure.sfrac Bool.false 65801 1000)))

noncomputable abbrev qz463 := qz478

noncomputable abbrev qz374 := qz463

noncomputable abbrev qz135 := (BSN.headSumC qz374 9)

noncomputable abbrev qz136 := qz374

noncomputable abbrev qz464 := (@Neg.neg Complex Complex.instNeg qz478)

noncomputable abbrev qz375 := qz464

noncomputable abbrev qz137 := (@HPow.hPow Complex Complex Complex qz270 (@Nat.cast Complex Complex.instNatCast 8) qz375)

noncomputable def ep450 := @Enclosure.Complex.IsNear.of_eq qz135 (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz136 8) qz137) Bool.true 1151657567 68719476736 121531834045 39782671450112 Bool.false 29824012517 137438953472 15565192218901 5092181945614336

noncomputable def ep451 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz136 8) qz137 Bool.true 10526573903 137438953472 27859861853429 10184363891228672 Bool.true 36133671141 274877906944 55724478397523 20368727782457344 Bool.false

noncomputable abbrev qz138 := (@HPow.hPow Complex Complex Complex qz270 (@Nat.cast Complex Complex.instNatCast 7) qz375)

noncomputable def ep452 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz136 8) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz136 7) qz138) Bool.true 10526573903 137438953472 27859861853429 10184363891228672 Bool.true 36133671141 274877906944 55724478397523 20368727782457344

noncomputable def ep453 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz136 7) qz138 Bool.false 13514936173 68719476736 1522820084331 636522743201792 Bool.false 17822168115 137438953472 24368122217493 10184363891228672 Bool.true

noncomputable abbrev qz139 := (@HPow.hPow Complex Complex Complex qz270 (@Nat.cast Complex Complex.instNatCast 6) qz375)

noncomputable def ep454 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz136 7) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz136 6) qz139) Bool.false 13514936173 68719476736 1522820084331 636522743201792 Bool.false 17822168115 137438953472 24368122217493 10184363891228672

noncomputable def ep455 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz136 6) qz139 Bool.false 43998841497 274877906944 41207651032887 20368727782457344 Bool.true 38060846317 137438953472 20589221061505 10184363891228672 Bool.false

noncomputable abbrev qz140 := (@HPow.hPow Complex Complex Complex qz270 (@Nat.cast Complex Complex.instNatCast 5) qz375)

noncomputable def ep456 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz136 6) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz136 5) qz140) Bool.false 43998841497 274877906944 41207651032887 20368727782457344 Bool.true 38060846317 137438953472 20589221061505 10184363891228672

noncomputable def ep457 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz136 5) qz140 Bool.true 31288216527 274877906944 32964428645811 20368727782457344 Bool.true 173299010967 274877906944 32928301592473 20368727782457344 Bool.false

noncomputable abbrev qz141 := (@HPow.hPow Complex Complex Complex qz270 (@Nat.cast Complex Complex.instNatCast 4) qz375)

noncomputable def ep458 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz136 5) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz136 4) qz141) Bool.true 31288216527 274877906944 32964428645811 20368727782457344 Bool.true 173299010967 274877906944 32928301592473 20368727782457344

noncomputable def ep459 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz136 4) qz141 Bool.false 26317680723 68719476736 11858425569029 10184363891228672 Bool.true 47205190035 68719476736 11857469073321 10184363891228672 Bool.true

noncomputable abbrev qz142 := (@HPow.hPow Complex Complex Complex qz270 qz272 qz375)

noncomputable def ep460 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz136 4) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz136 3) qz142) Bool.false 26317680723 68719476736 11858425569029 10184363891228672 Bool.true 47205190035 68719476736 11857469073321 10184363891228672

noncomputable def ep461 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz136 3) qz142 Bool.false 8246408759 8589934592 6513968668927 10184363891228672 Bool.true 3032137971 4294967296 6550559446323 10184363891228672 Bool.true

noncomputable abbrev qz143 := (@HPow.hPow Complex Complex Complex qz270 qz273 qz375)

noncomputable def ep462 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz136 3) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz136 2) qz143) Bool.false 8246408759 8589934592 6513968668927 10184363891228672 Bool.true 3032137971 4294967296 6550559446323 10184363891228672

noncomputable def ep463 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz136 2) qz143 Bool.false 1 1 0 1 Bool.false 0 1 0 1 Bool.true

noncomputable def ep464 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz136 2) (Complex.mk (Enclosure.sfrac Bool.false 1 1) qz14) Bool.false 1 1 0 1 Bool.false 0 1 0 1 (BSN.head_sum_c_two qz136)

noncomputable abbrev qz479 := (Enclosure.sfrac Bool.false 65801 1000)

noncomputable abbrev qz465 := qz479

noncomputable abbrev qz376 := qz465

noncomputable abbrev qz144 := (@HMul.hMul Real Real Real qz263 qz376 (Real.log (Enclosure.sfrac Bool.false 2 1)))

noncomputable abbrev qz145 := qz376

noncomputable abbrev qz377 := (@Eq.refl Real qz465)

noncomputable abbrev qz146 := qz377

noncomputable def ep465 := @Enclosure.Complex.IsNear.of_eq qz143 (Complex.mk (@HMul.hMul Real Real Real qz0 qz15 (Real.cos qz144)) (@HMul.hMul Real Real Real qz0 qz15 (@Neg.neg Real Real.instNeg (Real.sin qz144)))) Bool.true 343525833 8589934592 6513968668927 10184363891228672 Bool.true 3032137971 4294967296 6550559446323 10184363891228672 (BSN.cpow_neg_s_mk qz145 65801 1000 2 qz146 rfl)

noncomputable def ep466 := BSN.sin_dyadic_bound_f 60761553 1073741824 1 0 524288 148347 0 1 1 0 1 1 29652 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 60761553) qz278 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 60761553) qz279 0 0 rfl) rfl rfl

noncomputable abbrev qz378 := (Enclosure.Real.IsNear.const Bool.false 65801 1000)

noncomputable abbrev qz147 := qz378

noncomputable abbrev qz379 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 23912609) qz20)

noncomputable def ep467 := @Enclosure.Real.IsNear.cos_image qz144 qz379 Bool.false 23912609 524288 467 524288 Bool.true 29652 524288 1 74101 (@Enclosure.Real.IsNear.recentre' qz144 Bool.false 1494538113 32768000 65801 74101000 23912609 524288 467 524288 (@Enclosure.Real.IsNear.mulLit_ff qz145 qz21 65801 1000 0 1 181704 262144 1 74101 1494538113 32768000 65801 74101000 qz147 qz282 rfl) rfl) (Enclosure.sfrac_false_div 23912609 524288) (BSN.cos_reduce1 qz379 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 4275714186472102821888) qz23) 226375608064910080 72057594037927936 Bool.false 29652 524288 7 1000000000000000 148202 74101 (BSN.sin_reduce_arg_pos_rat_q1 23912609 524288 226375608064910080 72057594037927936 7 4275714186472102821888 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 29652 524288 4275714186472102821888 75557863725914323419136 60761553 1073741824 148347 148202 (ep466 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep468 := BSN.cos_dyadic_bound_f 60761553 1073741824 1 0 524288 148347 0 1 1 0 1 1 523448 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 60761553) qz283 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 60761553) qz284 0 0 rfl) rfl rfl

noncomputable def ep469 := @Enclosure.Real.IsNear.sin_image qz144 qz379 Bool.false 23912609 524288 467 524288 Bool.false 523448 524288 1 74101 (@Enclosure.Real.IsNear.recentre' qz144 Bool.false 1494538113 32768000 65801 74101000 23912609 524288 467 524288 (@Enclosure.Real.IsNear.mulLit_ff qz145 qz21 65801 1000 0 1 181704 262144 1 74101 1494538113 32768000 65801 74101000 qz147 qz282 rfl) rfl) (Enclosure.sfrac_false_div 23912609 524288) (BSN.sin_reduce1 qz379 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 4275714186472102821888) qz23) 226375608064910080 72057594037927936 Bool.false 523448 524288 7 1000000000000000 148202 74101 (BSN.sin_reduce_arg_pos_rat_q1 23912609 524288 226375608064910080 72057594037927936 7 4275714186472102821888 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 523448 524288 4275714186472102821888 75557863725914323419136 60761553 1073741824 148347 148202 (ep468 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep470 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz15 (Real.cos qz144)) (@HMul.hMul Real Real Real qz0 qz15 (@Neg.neg Real Real.instNeg (Real.sin qz144))) Bool.true 343525833 8589934592 6513968668927 10184363891228672 Bool.true 3032137971 4294967296 6550559446323 10184363891228672 (@Enclosure.Real.IsNear.mulLit_ft qz15 (Real.cos qz144) 46341 65536 1 262144 7413 131072 35129455 38850265088 343525833 8589934592 6513968668927 10184363891228672 qz285 (@Enclosure.Real.IsNear.recentre' (Real.cos qz144) Bool.true 29652 524288 35129455 38850265088 7413 131072 35129455 38850265088 (ep467 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz15 (@Neg.neg Real Real.instNeg (Real.sin qz144)) 46341 65536 1 262144 65431 65536 35129455 38850265088 3032137971 4294967296 6550559446323 10184363891228672 qz285 (@Enclosure.Real.IsNear.neg (Real.sin qz144) Bool.false 65431 65536 35129455 38850265088 (@Enclosure.Real.IsNear.recentre' (Real.sin qz144) Bool.false 523448 524288 35129455 38850265088 65431 65536 35129455 38850265088 (ep469 rfl rfl) rfl)) rfl)

noncomputable def ep471 := @ep463 343525833 8589934592 6513968668927 10184363891228672 Bool.true 3032137971 4294967296 6550559446323 10184363891228672 Bool.false 8246408759 8246408759 8589934592 6513968668927 10184363891228672 Bool.true 3032137971 3032137971 4294967296 6550559446323 10184363891228672 (ep464 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 1) qz14 Bool.false 1 1 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 1) qz24)) (ep465 ep470) rfl rfl

noncomputable abbrev qz148 := (@HMul.hMul Real Real Real qz263 qz376 (Real.log (Enclosure.sfrac Bool.false 3 1)))

noncomputable def ep472 := @Enclosure.Complex.IsNear.of_eq qz142 (Complex.mk (@HMul.hMul Real Real Real qz0 qz25 (Real.cos qz148)) (@HMul.hMul Real Real Real qz0 qz25 (@Neg.neg Real Real.instNeg (Real.sin qz148)))) Bool.true 39653589349 68719476736 2672228450051 5092181945614336 Bool.false 1309017501 68719476736 2653454813499 5092181945614336 (BSN.cpow_neg_s_mk qz145 65801 1000 3 qz146 rfl)

noncomputable def ep473 := BSN.cos_dyadic_bound_f 35433326 1073741824 1 0 524288 148347 0 1 1 0 1 1 524002 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 35433326) qz283 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 35433326) qz284 0 0 rfl) rfl rfl

noncomputable abbrev qz380 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 18950293) qz28)

noncomputable def ep474 := @Enclosure.Real.IsNear.cos_image qz148 qz380 Bool.false 18950293 262144 233 262144 Bool.true 524002 524288 1 74101 (@Enclosure.Real.IsNear.recentre' qz148 Bool.false 9475146597 131072000 65801 74101000 18950293 262144 233 262144 (@Enclosure.Real.IsNear.mulLit_ff qz145 qz29 65801 1000 0 1 287994 262144 1 74101 9475146597 131072000 65801 74101000 qz147 qz288 rfl) rfl) (Enclosure.sfrac_false_div 18950293 262144) (BSN.cos_reduce2 qz380 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 1246699361456751640576) qz289) 226375608064910080 72057594037927936 Bool.false 524002 524288 11 1000000000000000 148202 74101 (BSN.sin_reduce_arg_pos_rat_q2 18950293 262144 226375608064910080 72057594037927936 11 1246699361456751640576 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 524002 524288 1246699361456751640576 37778931862957161709568 35433326 1073741824 148347 148202 (ep473 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep475 := BSN.sin_dyadic_bound_f 35433326 1073741824 1 0 524288 148347 0 1 1 0 1 1 17298 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 35433326) qz278 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 35433326) qz279 0 0 rfl) rfl rfl

noncomputable def ep476 := @Enclosure.Real.IsNear.sin_image qz148 qz380 Bool.false 18950293 262144 233 262144 Bool.true 17298 524288 1 74101 (@Enclosure.Real.IsNear.recentre' qz148 Bool.false 9475146597 131072000 65801 74101000 18950293 262144 233 262144 (@Enclosure.Real.IsNear.mulLit_ff qz145 qz29 65801 1000 0 1 287994 262144 1 74101 9475146597 131072000 65801 74101000 qz147 qz288 rfl) rfl) (Enclosure.sfrac_false_div 18950293 262144) (BSN.sin_reduce2 qz380 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 1246699361456751640576) qz289) 226375608064910080 72057594037927936 Bool.false 17298 524288 11 1000000000000000 148202 74101 (BSN.sin_reduce_arg_pos_rat_q2 18950293 262144 226375608064910080 72057594037927936 11 1246699361456751640576 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 17298 524288 1246699361456751640576 37778931862957161709568 35433326 1073741824 148347 148202 (ep475 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep477 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz25 (Real.cos qz148)) (@HMul.hMul Real Real Real qz0 qz25 (@Neg.neg Real Real.instNeg (Real.sin qz148))) Bool.true 39653589349 68719476736 2672228450051 5092181945614336 Bool.false 1309017501 68719476736 2653454813499 5092181945614336 (@Enclosure.Real.IsNear.mulLit_ft qz25 (Real.cos qz148) 151349 262144 1 262144 262001 262144 17527677 19425132544 39653589349 68719476736 2672228450051 5092181945614336 qz290 (@Enclosure.Real.IsNear.recentre' (Real.cos qz148) Bool.true 524002 524288 17527677 19425132544 262001 262144 17527677 19425132544 (ep474 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz25 (@Neg.neg Real Real.instNeg (Real.sin qz148)) 151349 262144 1 262144 8649 262144 17527677 19425132544 1309017501 68719476736 2653454813499 5092181945614336 qz290 (@Enclosure.Real.IsNear.neg (Real.sin qz148) Bool.true 8649 262144 17527677 19425132544 (@Enclosure.Real.IsNear.recentre' (Real.sin qz148) Bool.true 17298 524288 17527677 19425132544 8649 262144 17527677 19425132544 (ep476 rfl rfl) rfl)) rfl)

noncomputable def ep478 := @ep461 39653589349 68719476736 2672228450051 5092181945614336 Bool.false 1309017501 68719476736 2653454813499 5092181945614336 Bool.false 226067156023709270016 26317680723 68719476736 11858425569029 10184363891228672 Bool.true 202744747401790095360 47205190035 68719476736 11857469073321 10184363891228672 (ep462 (BSN.head_sum_c_succ qz136 2 3 rfl rfl) (ep471 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep472 ep477) rfl rfl

noncomputable abbrev qz149 := (@HMul.hMul Real Real Real qz263 qz376 (Real.log (Enclosure.sfrac Bool.false 4 1)))

noncomputable def ep479 := @Enclosure.Complex.IsNear.of_eq qz141 (Complex.mk (@HMul.hMul Real Real Real qz0 qz30 (Real.cos qz149)) (@HMul.hMul Real Real Real qz0 qz30 (@Neg.neg Real Real.instNeg (Real.sin qz149)))) Bool.true 136558939419 274877906944 9247577507753 20368727782457344 Bool.false 15521749173 274877906944 9213363445831 20368727782457344 (BSN.cpow_neg_s_mk qz145 65801 1000 4 qz146 rfl)

noncomputable def ep480 := nat_lit 218104547316128408188501092848656

noncomputable def ep481 := BSN.cos_dyadic_bound_f 121525154 1073741824 2 1 524288 148347 ep480 ep75 ep480 ep480 ep76 ep480 520933 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 121525154) qz283 0 1 ep480 ep75 ep480 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 121525154) qz284 0 1 ep480 ep76 ep480 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz381 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 47825219) qz20)

noncomputable def ep482 := @Enclosure.Real.IsNear.cos_image qz149 qz381 Bool.false 47825219 524288 467 524288 Bool.true 520933 524288 1 74101 (@Enclosure.Real.IsNear.recentre' qz149 Bool.false 1494538113 16384000 65801 74101000 47825219 524288 467 524288 (@Enclosure.Real.IsNear.mulLit_ff qz145 qz32 65801 1000 0 1 363408 262144 1 74101 1494538113 16384000 65801 74101000 qz147 qz293 rfl) rfl) (Enclosure.sfrac_false_div 47825219 524288) (BSN.cos_reduce2 qz381 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 8551572488132281499648) qz23) 226375608064910080 72057594037927936 Bool.false 520933 524288 14 1000000000000000 148202 74101 (BSN.sin_reduce_arg_pos_rat_q2 47825219 524288 226375608064910080 72057594037927936 14 8551572488132281499648 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 520933 524288 8551572488132281499648 75557863725914323419136 121525154 1073741824 148347 148202 (ep481 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep483 := BSN.sin_dyadic_bound_f 121525154 1073741824 1 0 524288 148347 0 1 1 0 1 1 59211 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 121525154) qz278 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 121525154) qz279 0 0 rfl) rfl rfl

noncomputable def ep484 := @Enclosure.Real.IsNear.sin_image qz149 qz381 Bool.false 47825219 524288 467 524288 Bool.true 59211 524288 1 74101 (@Enclosure.Real.IsNear.recentre' qz149 Bool.false 1494538113 16384000 65801 74101000 47825219 524288 467 524288 (@Enclosure.Real.IsNear.mulLit_ff qz145 qz32 65801 1000 0 1 363408 262144 1 74101 1494538113 16384000 65801 74101000 qz147 qz293 rfl) rfl) (Enclosure.sfrac_false_div 47825219 524288) (BSN.sin_reduce2 qz381 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 8551572488132281499648) qz23) 226375608064910080 72057594037927936 Bool.false 59211 524288 14 1000000000000000 148202 74101 (BSN.sin_reduce_arg_pos_rat_q2 47825219 524288 226375608064910080 72057594037927936 14 8551572488132281499648 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 59211 524288 8551572488132281499648 75557863725914323419136 121525154 1073741824 148347 148202 (ep483 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep485 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz30 (Real.cos qz149)) (@HMul.hMul Real Real Real qz0 qz30 (@Neg.neg Real Real.instNeg (Real.sin qz149))) Bool.true 136558939419 274877906944 9247577507753 20368727782457344 Bool.false 15521749173 274877906944 9213363445831 20368727782457344 (@Enclosure.Real.IsNear.mulLit_ft qz30 (Real.cos qz149) 262143 524288 1 524288 520933 524288 35129455 38850265088 136558939419 274877906944 9247577507753 20368727782457344 qz294 (@Enclosure.Real.IsNear.recentre' (Real.cos qz149) Bool.true 520933 524288 35129455 38850265088 520933 524288 35129455 38850265088 (ep482 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz30 (@Neg.neg Real Real.instNeg (Real.sin qz149)) 262143 524288 1 524288 59211 524288 35129455 38850265088 15521749173 274877906944 9213363445831 20368727782457344 qz294 (@Enclosure.Real.IsNear.neg (Real.sin qz149) Bool.true 59211 524288 35129455 38850265088 (@Enclosure.Real.IsNear.recentre' (Real.sin qz149) Bool.true 59211 524288 35129455 38850265088 59211 524288 35129455 38850265088 (ep484 rfl rfl) rfl)) rfl)

noncomputable def ep486 := @ep459 136558939419 274877906944 9247577507753 20368727782457344 Bool.false 15521749173 274877906944 9213363445831 20368727782457344 Bool.true 2150109867738107215872 31288216527 274877906944 32964428645811 20368727782457344 Bool.true 11909017352518565363712 173299010967 274877906944 32928301592473 20368727782457344 (ep460 (BSN.head_sum_c_succ qz136 3 4 rfl rfl) (ep478 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep479 ep485) rfl rfl

noncomputable abbrev qz150 := (@HMul.hMul Real Real Real qz263 qz376 (Real.log (Enclosure.sfrac Bool.false 5 1)))

noncomputable def ep487 := @Enclosure.Complex.IsNear.of_eq qz140 (Complex.mk (@HMul.hMul Real Real Real qz0 qz33 (Real.cos qz150)) (@HMul.hMul Real Real Real qz0 qz33 (@Neg.neg Real Real.instNeg (Real.sin qz150)))) Bool.false 9410882253 34359738368 2060805596769 5092181945614336 Bool.false 97177318333 274877906944 8250140530537 20368727782457344 (BSN.cpow_neg_s_mk qz145 65801 1000 5 qz146 rfl)

noncomputable def ep488 := nat_lit 250915008832927338603244895516102656

noncomputable def ep489 := BSN.sin_dyadic_bound_f 707752904 1073741824 2 1 524288 148347 ep488 ep79 ep488 ep488 ep80 ep488 321096 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 707752904) qz278 0 1 ep488 ep79 ep488 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 707752904) qz279 0 1 ep488 ep80 ep488 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz382 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 27761705) qz28)

noncomputable def ep490 := @Enclosure.Real.IsNear.cos_image qz150 qz382 Bool.false 27761705 262144 233 262144 Bool.false 321096 524288 1 74101 (@Enclosure.Real.IsNear.recentre' qz150 Bool.false 1735106569 16384000 65801 74101000 27761705 262144 233 262144 (@Enclosure.Real.IsNear.mulLit_ff qz145 qz35 65801 1000 0 1 421904 262144 1 74101 1735106569 16384000 65801 74101000 qz147 qz297 rfl) rfl) (Enclosure.sfrac_false_div 27761705 262144) (BSN.cos_reduce3 qz382 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 24901841543386544209920) qz289) 226375608064910080 72057594037927936 Bool.false 321096 524288 16 1000000000000000 148202 74101 (BSN.sin_reduce_arg_pos_rat_q3 27761705 262144 226375608064910080 72057594037927936 16 24901841543386544209920 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 321096 524288 24901841543386544209920 37778931862957161709568 707752904 1073741824 148347 148202 (ep489 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep491 := BSN.cos_dyadic_bound_f 707752904 1073741824 2 1 524288 148347 ep488 ep75 ep488 ep488 ep76 ep488 414457 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 707752904) qz283 0 1 ep488 ep75 ep488 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 707752904) qz284 0 1 ep488 ep76 ep488 rfl rfl rfl rfl) rfl rfl

noncomputable def ep492 := @Enclosure.Real.IsNear.sin_image qz150 qz382 Bool.false 27761705 262144 233 262144 Bool.true 414457 524288 1 74101 (@Enclosure.Real.IsNear.recentre' qz150 Bool.false 1735106569 16384000 65801 74101000 27761705 262144 233 262144 (@Enclosure.Real.IsNear.mulLit_ff qz145 qz35 65801 1000 0 1 421904 262144 1 74101 1735106569 16384000 65801 74101000 qz147 qz297 rfl) rfl) (Enclosure.sfrac_false_div 27761705 262144) (BSN.sin_reduce3 qz382 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 24901841543386544209920) qz289) 226375608064910080 72057594037927936 Bool.false 414457 524288 16 1000000000000000 148202 74101 (BSN.sin_reduce_arg_pos_rat_q3 27761705 262144 226375608064910080 72057594037927936 16 24901841543386544209920 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 414457 524288 24901841543386544209920 37778931862957161709568 707752904 1073741824 148347 148202 (ep491 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep493 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz33 (Real.cos qz150)) (@HMul.hMul Real Real Real qz0 qz33 (@Neg.neg Real Real.instNeg (Real.sin qz150))) Bool.false 9410882253 34359738368 2060805596769 5092181945614336 Bool.false 97177318333 274877906944 8250140530537 20368727782457344 (@Enclosure.Real.IsNear.mulLit_ff qz33 (Real.cos qz150) 234469 524288 1 524288 40137 65536 17527677 19425132544 9410882253 34359738368 2060805596769 5092181945614336 qz299 (@Enclosure.Real.IsNear.recentre' (Real.cos qz150) Bool.false 321096 524288 17527677 19425132544 40137 65536 17527677 19425132544 (ep490 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz33 (@Neg.neg Real Real.instNeg (Real.sin qz150)) 234469 524288 1 524288 414457 524288 17527677 19425132544 97177318333 274877906944 8250140530537 20368727782457344 qz299 (@Enclosure.Real.IsNear.neg (Real.sin qz150) Bool.true 414457 524288 17527677 19425132544 (@Enclosure.Real.IsNear.recentre' (Real.sin qz150) Bool.true 414457 524288 17527677 19425132544 414457 524288 17527677 19425132544 (ep492 rfl rfl) rfl)) rfl)

noncomputable def ep494 := @ep457 9410882253 34359738368 2060805596769 5092181945614336 Bool.false 97177318333 274877906944 8250140530537 20368727782457344 Bool.false 1511788682332021456896 43998841497 274877906944 41207651032887 20368727782457344 Bool.true 20924171544268422250496 38060846317 137438953472 20589221061505 10184363891228672 (ep458 (BSN.head_sum_c_succ qz136 4 5 rfl rfl) (ep486 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep487 ep493) rfl rfl

noncomputable abbrev qz151 := (@HMul.hMul Real Real Real qz263 qz376 (Real.log (Enclosure.sfrac Bool.false 6 1)))

noncomputable def ep495 := @Enclosure.Complex.IsNear.of_eq qz139 (Complex.mk (@HMul.hMul Real Real Real qz0 qz36 (Real.cos qz151)) (@HMul.hMul Real Real Real qz0 qz36 (@Neg.neg Real Real.instNeg (Real.sin qz151)))) Bool.false 10060903195 274877906944 7522591665705 20368727782457344 Bool.false 1746344201 4294967296 944725288997 2546090972807168 (BSN.cpow_neg_s_mk qz145 65801 1000 6 qz146 rfl)

noncomputable def ep496 := @Enclosure.Real.IsNear.mulLit_ff qz145 qz38 65801 1000 0 1 4034681531866359 2251799813685248 500000000074101 37050500000000000000 265486079478338288559 2251799813685248000 32900500004875919901 37050500000000000000000 qz147 (BSN.isNear_log_sfrac 6 1 4034681531866359 2251799813685248 500000000074101 37050500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz301) Bool.false 16922680887833197019136 9444732965739290427392 1000000000148202 74101000000000000000 4034681531866359 2251799813685248 500000000074101 37050500000000000000 (BSN.log_rat_reduce_isNear 6 1 2 12 8 106290 262144 24973259072661432 36028797018963968 74101 1000000000000000 rfl rfl rfl rfl (ep120 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep497 := BSN.sin_dyadic_bound_f 96397632 1073741824 1 0 524288 148347 0 1 1 0 1 1 47005 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 96397632) qz278 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 96397632) qz279 0 0 rfl) rfl rfl

noncomputable abbrev qz383 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 30906647) qz28)

noncomputable def ep498 := @Enclosure.Real.IsNear.cos_image qz151 qz383 Bool.false 30906647 262144 467 524288 Bool.false 47005 524288 1 74101 (@Enclosure.Real.IsNear.recentre' qz151 Bool.false 265486079478338288559 2251799813685248000 32900500004875919901 37050500000000000000000 30906647 262144 467 524288 (ep496 rfl) rfl) (Enclosure.sfrac_false_div 30906647 262144) (BSN.cos_reduce3 qz383 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 3391690156502557917184) qz289) 226375608064910080 72057594037927936 Bool.false 47005 524288 18 1000000000000000 148202 74101 (BSN.sin_reduce_arg_pos_rat_q3 30906647 262144 226375608064910080 72057594037927936 18 3391690156502557917184 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 47005 524288 3391690156502557917184 37778931862957161709568 96397632 1073741824 148347 148202 (ep497 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep499 := nat_lit 86350620465041913498342864715776

noncomputable def ep500 := BSN.cos_dyadic_bound_f 96397632 1073741824 2 1 524288 148347 ep499 ep75 ep499 ep499 ep76 ep499 522176 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 96397632) qz283 0 1 ep499 ep75 ep499 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 96397632) qz284 0 1 ep499 ep76 ep499 rfl rfl rfl rfl) rfl rfl

noncomputable def ep501 := @Enclosure.Real.IsNear.sin_image qz151 qz383 Bool.false 30906647 262144 467 524288 Bool.true 522176 524288 1 74101 (@Enclosure.Real.IsNear.recentre' qz151 Bool.false 265486079478338288559 2251799813685248000 32900500004875919901 37050500000000000000000 30906647 262144 467 524288 (ep496 rfl) rfl) (Enclosure.sfrac_false_div 30906647 262144) (BSN.sin_reduce3 qz383 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 3391690156502557917184) qz289) 226375608064910080 72057594037927936 Bool.false 522176 524288 18 1000000000000000 148202 74101 (BSN.sin_reduce_arg_pos_rat_q3 30906647 262144 226375608064910080 72057594037927936 18 3391690156502557917184 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 522176 524288 3391690156502557917184 37778931862957161709568 96397632 1073741824 148347 148202 (ep500 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep502 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz36 (Real.cos qz151)) (@HMul.hMul Real Real Real qz0 qz36 (@Neg.neg Real Real.instNeg (Real.sin qz151))) Bool.false 10060903195 274877906944 7522591665705 20368727782457344 Bool.false 1746344201 4294967296 944725288997 2546090972807168 (@Enclosure.Real.IsNear.mulLit_ff qz36 (Real.cos qz151) 214039 524288 1 524288 47005 524288 35129455 38850265088 10060903195 274877906944 7522591665705 20368727782457344 qz303 (@Enclosure.Real.IsNear.recentre' (Real.cos qz151) Bool.false 47005 524288 35129455 38850265088 47005 524288 35129455 38850265088 (ep498 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz36 (@Neg.neg Real Real.instNeg (Real.sin qz151)) 214039 524288 1 524288 8159 8192 35129455 38850265088 1746344201 4294967296 944725288997 2546090972807168 qz303 (@Enclosure.Real.IsNear.neg (Real.sin qz151) Bool.true 8159 8192 35129455 38850265088 (@Enclosure.Real.IsNear.recentre' (Real.sin qz151) Bool.true 522176 524288 35129455 38850265088 8159 8192 35129455 38850265088 (ep501 rfl rfl) rfl)) rfl)

noncomputable def ep503 := @ep455 10060903195 274877906944 7522591665705 20368727782457344 Bool.false 1746344201 4294967296 944725288997 2546090972807168 Bool.false 14859829470863973941248 13514936173 68719476736 1522820084331 636522743201792 Bool.false 76545629197738967040 17822168115 137438953472 24368122217493 10184363891228672 (ep456 (BSN.head_sum_c_succ qz136 5 6 rfl rfl) (ep494 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep495 ep502) rfl rfl

noncomputable abbrev qz152 := (@HMul.hMul Real Real Real qz263 qz376 (Real.log (Enclosure.sfrac Bool.false 7 1)))

noncomputable def ep504 := @Enclosure.Complex.IsNear.of_eq qz138 (Complex.mk (@HMul.hMul Real Real Real qz0 qz39 (Real.cos qz152)) (@HMul.hMul Real Real Real qz0 qz39 (@Neg.neg Real Real.instNeg (Real.sin qz152)))) Bool.true 37556446249 137438953472 3494740504133 10184363891228672 Bool.true 71778007371 274877906944 6988233962537 20368727782457344 (BSN.cpow_neg_s_mk qz145 65801 1000 7 qz146 rfl)

noncomputable def ep505 := @Enclosure.Real.IsNear.mulLit_ff qz145 qz41 65801 1000 0 1 4381792198794487 2251799813685248 500000000074101 37050500000000000000 288326308472876039087 2251799813685248000 32900500004875919901 37050500000000000000000 qz147 (BSN.isNear_log_sfrac 7 1 4381792198794487 2251799813685248 500000000074101 37050500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz305) Bool.false 18378568546572512002048 9444732965739290427392 1000000000148202 74101000000000000000 4381792198794487 2251799813685248 500000000074101 37050500000000000000 (BSN.log_rat_reduce_isNear 7 1 2 14 8 146699 262144 24973259072661432 36028797018963968 74101 1000000000000000 rfl rfl rfl rfl (ep135 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep506 := nat_lit 566834078788479688673435720874328801

noncomputable def ep507 := BSN.sin_dyadic_bound_f 867688793 1073741824 2 1 524288 148347 ep506 ep79 ep506 ep506 ep80 ep506 379046 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 867688793) qz278 0 1 ep506 ep79 ep506 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 867688793) qz279 0 1 ep506 ep80 ep506 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz384 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 67131199) qz20)

noncomputable def ep508 := @Enclosure.Real.IsNear.cos_image qz152 qz384 Bool.false 67131199 524288 467 524288 Bool.true 379046 524288 1 74101 (@Enclosure.Real.IsNear.recentre' qz152 Bool.false 288326308472876039087 2251799813685248000 32900500004875919901 37050500000000000000000 67131199 524288 467 524288 (ep505 rfl) rfl) (Enclosure.sfrac_false_div 67131199 524288) (BSN.cos_reduce1 qz384 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 61058170750725980684288) qz23) 226375608064910080 72057594037927936 Bool.false 379046 524288 20 1000000000000000 148202 74101 (BSN.sin_reduce_arg_pos_rat_q1 67131199 524288 226375608064910080 72057594037927936 20 61058170750725980684288 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 379046 524288 61058170750725980684288 75557863725914323419136 867688793 1073741824 148347 148202 (ep507 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep509 := nat_lit 1266120201377083902780723658605478440324530787869463287025998030853826169281

noncomputable def ep510 := nat_lit 321300872875984399323568179318689158186968346593315068000794292258097601

noncomputable def ep511 := nat_lit 3797718002385499739543523839457797942657218426915203230941992503976962312641

noncomputable def ep512 := BSN.cos_dyadic_bound_f 867688793 1073741824 3 2 524288 148347 ep509 ep64 ep510 ep511 ep66 ep510 362217 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 867688793) qz283 0 2 ep509 ep64 ep510 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 867688793) qz284 0 2 ep511 ep66 ep510 rfl rfl rfl rfl) rfl rfl

noncomputable def ep513 := @Enclosure.Real.IsNear.sin_image qz152 qz384 Bool.false 67131199 524288 467 524288 Bool.false 362217 524288 1 74101 (@Enclosure.Real.IsNear.recentre' qz152 Bool.false 288326308472876039087 2251799813685248000 32900500004875919901 37050500000000000000000 67131199 524288 467 524288 (ep505 rfl) rfl) (Enclosure.sfrac_false_div 67131199 524288) (BSN.sin_reduce1 qz384 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 61058170750725980684288) qz23) 226375608064910080 72057594037927936 Bool.false 362217 524288 20 1000000000000000 148202 74101 (BSN.sin_reduce_arg_pos_rat_q1 67131199 524288 226375608064910080 72057594037927936 20 61058170750725980684288 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 362217 524288 61058170750725980684288 75557863725914323419136 867688793 1073741824 148347 148202 (ep512 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep514 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz39 (Real.cos qz152)) (@HMul.hMul Real Real Real qz0 qz39 (@Neg.neg Real Real.instNeg (Real.sin qz152))) Bool.true 37556446249 137438953472 3494740504133 10184363891228672 Bool.true 71778007371 274877906944 6988233962537 20368727782457344 (@Enclosure.Real.IsNear.mulLit_ft qz39 (Real.cos qz152) 198163 524288 1 524288 189523 262144 35129455 38850265088 37556446249 137438953472 3494740504133 10184363891228672 qz307 (@Enclosure.Real.IsNear.recentre' (Real.cos qz152) Bool.true 379046 524288 35129455 38850265088 189523 262144 35129455 38850265088 (ep508 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz39 (@Neg.neg Real Real.instNeg (Real.sin qz152)) 198163 524288 1 524288 362217 524288 35129455 38850265088 71778007371 274877906944 6988233962537 20368727782457344 qz307 (@Enclosure.Real.IsNear.neg (Real.sin qz152) Bool.false 362217 524288 35129455 38850265088 (@Enclosure.Real.IsNear.recentre' (Real.sin qz152) Bool.false 362217 524288 35129455 38850265088 362217 524288 35129455 38850265088 (ep513 rfl rfl) rfl)) rfl)

noncomputable def ep515 := @ep453 37556446249 137438953472 3494740504133 10184363891228672 Bool.true 71778007371 274877906944 6988233962537 20368727782457344 Bool.true 723380650436993220608 10526573903 137438953472 27859861853429 10184363891228672 Bool.true 4966173946720448151552 36133671141 274877906944 55724478397523 20368727782457344 (ep454 (BSN.head_sum_c_succ qz136 6 7 rfl rfl) (ep503 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep504 ep514) rfl rfl

noncomputable abbrev qz153 := (@HMul.hMul Real Real Real qz263 qz376 (Real.log (Enclosure.sfrac Bool.false 8 1)))

noncomputable def ep516 := @Enclosure.Complex.IsNear.of_eq qz137 (Complex.mk (@HMul.hMul Real Real Real qz0 qz42 (Real.cos qz153)) (@HMul.hMul Real Real Real qz0 qz42 (@Neg.neg Real Real.instNeg (Real.sin qz153)))) Bool.false 8223258769 137438953472 3252287662091 10184363891228672 Bool.false 95781696175 274877906944 6536290478081 20368727782457344 (BSN.cpow_neg_s_mk qz145 65801 1000 8 qz146 rfl)

noncomputable def ep517 := @Enclosure.Real.IsNear.mulLit_ff qz145 qz44 65801 1000 0 1 9364972152248037 4503599627370496 1000000000222303 74101000000000000000 616224532590073082637 4503599627370496000 65801000014627759703 74101000000000000000000 qz147 (BSN.isNear_log_sfrac 8 1 9364972152248037 4503599627370496 1000000000222303 74101000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz309) Bool.false 19639770079031275290624 9444732965739290427392 1000000000222303 74101000000000000000 9364972152248037 4503599627370496 1000000000222303 74101000000000000000 (BSN.log_rat_reduce_isNear 8 1 3 16 16 0 262144 24973259072661432 36028797018963968 74101 1000000000000000 rfl rfl rfl rfl (ep146 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep518 := BSN.sin_dyadic_bound_f 182591859 1073741824 1 0 524288 148347 0 1 1 0 1 1 88726 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 182591859) qz278 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 182591859) qz279 0 0 rfl) rfl rfl

noncomputable abbrev qz385 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 71737977) qz20)

noncomputable def ep519 := @Enclosure.Real.IsNear.cos_image qz153 qz385 Bool.false 71737977 524288 233 262144 Bool.false 88726 524288 1 74101 (@Enclosure.Real.IsNear.recentre' qz153 Bool.false 616224532590073082637 4503599627370496000 65801000014627759703 74101000000000000000000 71737977 524288 233 262144 (ep517 rfl) rfl) (Enclosure.sfrac_false_div 71737977 524288) (BSN.cos_reduce3 qz385 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 12848759837627686846464) qz23) 226375608064910080 72057594037927936 Bool.false 88726 524288 21 1000000000000000 148202 74101 (BSN.sin_reduce_arg_pos_rat_q3 71737977 524288 226375608064910080 72057594037927936 21 12848759837627686846464 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 88726 524288 12848759837627686846464 75557863725914323419136 182591859 1073741824 148347 148202 (ep518 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep520 := nat_lit 1111541395410080215479602183926161

noncomputable def ep521 := BSN.cos_dyadic_bound_f 182591859 1073741824 2 1 524288 148347 ep520 ep75 ep520 ep520 ep76 ep520 516725 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 182591859) qz283 0 1 ep520 ep75 ep520 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 182591859) qz284 0 1 ep520 ep76 ep520 rfl rfl rfl rfl) rfl rfl

noncomputable def ep522 := @Enclosure.Real.IsNear.sin_image qz153 qz385 Bool.false 71737977 524288 233 262144 Bool.true 516725 524288 1 74101 (@Enclosure.Real.IsNear.recentre' qz153 Bool.false 616224532590073082637 4503599627370496000 65801000014627759703 74101000000000000000000 71737977 524288 233 262144 (ep517 rfl) rfl) (Enclosure.sfrac_false_div 71737977 524288) (BSN.sin_reduce3 qz385 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 12848759837627686846464) qz23) 226375608064910080 72057594037927936 Bool.false 516725 524288 21 1000000000000000 148202 74101 (BSN.sin_reduce_arg_pos_rat_q3 71737977 524288 226375608064910080 72057594037927936 21 12848759837627686846464 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 516725 524288 12848759837627686846464 75557863725914323419136 182591859 1073741824 148347 148202 (ep521 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep523 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz42 (Real.cos qz153)) (@HMul.hMul Real Real Real qz0 qz42 (@Neg.neg Real Real.instNeg (Real.sin qz153))) Bool.false 8223258769 137438953472 3252287662091 10184363891228672 Bool.false 95781696175 274877906944 6536290478081 20368727782457344 (@Enclosure.Real.IsNear.mulLit_ff qz42 (Real.cos qz153) 185363 524288 1 524288 44363 262144 17527677 19425132544 8223258769 137438953472 3252287662091 10184363891228672 qz311 (@Enclosure.Real.IsNear.recentre' (Real.cos qz153) Bool.false 88726 524288 17527677 19425132544 44363 262144 17527677 19425132544 (ep519 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz42 (@Neg.neg Real Real.instNeg (Real.sin qz153)) 185363 524288 1 524288 516725 524288 17527677 19425132544 95781696175 274877906944 6536290478081 20368727782457344 qz311 (@Enclosure.Real.IsNear.neg (Real.sin qz153) Bool.true 516725 524288 17527677 19425132544 (@Enclosure.Real.IsNear.recentre' (Real.sin qz153) Bool.true 516725 524288 17527677 19425132544 516725 524288 17527677 19425132544 (ep522 rfl rfl) rfl)) rfl)

noncomputable def ep524 := @ep451 8223258769 137438953472 3252287662091 10184363891228672 Bool.false 95781696175 274877906944 6536290478081 20368727782457344 Bool.true 316565221533179445248 1151657567 68719476736 121531834045 39782671450112 Bool.false 16395924274689234436096 29824012517 137438953472 15565192218901 5092181945614336 (ep452 (BSN.head_sum_c_succ qz136 7 8 rfl rfl) (ep515 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep516 ep523) rfl rfl

theorem EMRow15.d10 : Enclosure.Complex.IsNear qz135 Bool.true 1151657567 68719476736 121531834045 39782671450112 Bool.false 29824012517 137438953472 15565192218901 5092181945614336 := ep450 (BSN.head_sum_c_succ qz136 8 9 rfl rfl) (ep524 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

theorem EMRow15.d11 : @Eq Nat (Nat.pow 14 1) 14 := @Eq.refl Nat 14

noncomputable def ep525 := nat_lit 39326387007577491180921324389789

noncomputable def ep526 := nat_lit 34945225134435478930070700032000

noncomputable def ep527 := nat_lit 138936379676944210135885481981053669209

noncomputable def ep528 := nat_lit 27411824362531402933776345121503051776000

noncomputable abbrev qz466 := (@HAdd.hAdd Complex Complex Complex qz472 (@HAdd.hAdd Complex Complex Complex qz472 qz475 (@HMul.hMul Complex Complex Complex qz474 Complex.I (@HDiv.hDiv Complex Complex Complex qz476 (↑qz479) (2 : Complex)))) (@Nat.cast Complex Complex.instNatCast 2))

noncomputable abbrev qz386 := qz466

noncomputable abbrev qz154 := (Complex.Stirling.logGammaStirling 1 qz386)

noncomputable abbrev qz467 := (@HAdd.hAdd Complex Complex Complex qz472 qz475 (@HMul.hMul Complex Complex Complex qz474 Complex.I (@HDiv.hDiv Complex Complex Complex qz476 (↑qz479) (2 : Complex))))

noncomputable abbrev qz387 := qz467

noncomputable abbrev qz155 := qz387

noncomputable abbrev qz156 := (@HMul.hMul Real Real Real qz263 (@HDiv.hDiv Real Real Real qz266 qz376 (2 : Real)) (Real.log Real.pi))

noncomputable def ep529 := Complex.re (@HMul.hMul Complex Complex Complex qz45 (Complex.exp (@HMul.hMul Complex Complex Complex qz45 Complex.I ↑(@HSub.hSub Real Real Real qz46 (Complex.im (@HSub.hSub Complex Complex Complex qz47 qz154 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz155 (@Nat.cast Complex Complex.instNatCast j))))) qz156))) (zetaApproximant qz136 1 14))

noncomputable def ep530 := @Enclosure.Real.IsNear.of_eq ep529 (@HSub.hSub Real Real Real qz46 (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz46 (Complex.im (@HSub.hSub Complex Complex Complex qz47 qz154 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz155 (@Nat.cast Complex Complex.instNatCast j))))) qz156)) (Complex.re (zetaApproximant qz136 1 14))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz46 (Complex.im (@HSub.hSub Complex Complex Complex qz47 qz154 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz155 (@Nat.cast Complex Complex.instNatCast j))))) qz156)) (Complex.im (zetaApproximant qz136 1 14))))

noncomputable def ep531 := nat_lit 5618076043858496313060981185267

noncomputable def ep532 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz46 (Complex.im (@HSub.hSub Complex Complex Complex qz47 qz154 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz155 (@Nat.cast Complex Complex.instNatCast j))))) qz156)) (Complex.re (zetaApproximant qz136 1 14))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz46 (Complex.im (@HSub.hSub Complex Complex Complex qz47 qz154 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz155 (@Nat.cast Complex Complex.instNatCast j))))) qz156)) (Complex.im (zetaApproximant qz136 1 14))) ep531

noncomputable def ep533 := nat_lit 4992175019205068418581528576000

noncomputable def ep534 := nat_lit 5540211558116134103720780659445287249

noncomputable def ep535 := nat_lit 1096472974501256117351053804860122071040

noncomputable def ep536 := nat_lit 3632485799575262638597677

noncomputable def ep537 := nat_lit 873630628360886973251767500800

noncomputable def ep538 := nat_lit 26943170252553596429122843432592999

noncomputable def ep539 := nat_lit 1713239022658212683361021570093940736000

noncomputable def ep540 := nat_lit 4908105170370477879306433324693049797804089543105751652761600

noncomputable def ep541 := @Enclosure.Real.IsNear.mulLit_ff (Real.cos (@HSub.hSub Real Real Real qz46 (Complex.im (@HSub.hSub Complex Complex Complex qz47 qz154 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz155 (@Nat.cast Complex Complex.instNatCast j))))) qz156)) (Complex.re (zetaApproximant qz136 1 14)) 524287 524288 3910223

noncomputable def ep542 := nat_lit 10715650099770729224758541

noncomputable def ep543 := nat_lit 9521818197641503178752000

noncomputable def ep544 := nat_lit 22708906006359477462486971949

noncomputable def ep545 := nat_lit 4939033751844031189340913664000

noncomputable def ep546 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HSub.hSub Real Real Real qz46 (Complex.im (@HSub.hSub Complex Complex Complex qz47 qz154 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz155 (@Nat.cast Complex Complex.instNatCast j))))) qz156)) Bool.false 524287 524288 3910223

noncomputable abbrev qz388 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 23059457) qz20)

noncomputable def ep547 := @Enclosure.Real.IsNear.cos_image (@HSub.hSub Real Real Real qz46 (Complex.im (@HSub.hSub Complex Complex Complex qz47 qz154 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz155 (@Nat.cast Complex Complex.instNatCast j))))) qz156) qz388 Bool.false 23059457 524288 51

noncomputable def ep548 := nat_lit 2257111881922873498904933

noncomputable def ep549 := nat_lit 5827539763200000000000000000

noncomputable def ep550 := @Enclosure.Real.IsNear.recentre' (@HSub.hSub Real Real Real qz46 (Complex.im (@HSub.hSub Complex Complex Complex qz47 qz154 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz155 (@Nat.cast Complex Complex.instNatCast j))))) qz156) Bool.false 79231691787257536079 1801439850948198400 ep548 ep549

noncomputable def ep551 := @Enclosure.Real.IsNear.subLit_ff_p (Complex.im (@HSub.hSub Complex Complex Complex qz47 qz154 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz155 (@Nat.cast Complex Complex.instNatCast j))))) qz156 735389188605265696651 9007199254740992000 794335911622873498904933 ep549 4936456821 131072000

noncomputable def ep552 := nat_lit 51925281529697098844733440000

noncomputable def ep553 := @Enclosure.Complex.IsNear.im_isNear (@HSub.hSub Complex Complex Complex qz47 qz154 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz155 (@Nat.cast Complex Complex.instNatCast j)))) Bool.true 116270397691885675133 2251799813685248000 583656577604117430463367 ep185 Bool.false 735389188605265696651 9007199254740992000

noncomputable def ep554 := @Enclosure.Complex.IsNear.subLitP qz154 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz155 (@Nat.cast Complex Complex.instNatCast j))) Bool.true 100535439301011352133 2251799813685248000 567272577579836014783367 ep185 Bool.false 763275678178835328651 9007199254740992000 715692711617045959141733

noncomputable def ep555 := nat_lit 261817659859697852359437425242537984

noncomputable def ep556 := nat_lit 206993654735935374655927204295213056

noncomputable abbrev qz389 := (@HSub.hSub Complex Complex Complex qz455 qz466 qz458)

noncomputable abbrev qz390 := (Complex.log qz466)

noncomputable abbrev qz157 := (@HSub.hSub Complex Complex Complex qz313 (@HMul.hMul Complex Complex Complex qz312 qz389 qz390) qz386)

noncomputable abbrev qz158 := qz386

noncomputable def ep557 := @Enclosure.Complex.IsNear.of_eq qz154 (@HAdd.hAdd Complex Complex Complex qz5 (@HAdd.hAdd Complex Complex Complex qz5 qz157 qz52) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz47 (@HMul.hMul Complex Complex Complex qz45 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz55 qz158 (@HSub.hSub Int Int Int qz57 qz58 (@HMul.hMul Int Int Int qz59 qz60 (@Nat.cast Int instNatCastInt k)))))) Bool.true 100535439301011352133

noncomputable def ep558 := @Enclosure.Complex.IsNear.addLitP (@HAdd.hAdd Complex Complex Complex qz5 qz157 qz52) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz47 (@HMul.hMul Complex Complex Complex qz45 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz55 qz158 (@HSub.hSub Int Int Int qz57 qz58 (@HMul.hMul Int Int Int qz59 qz60 (@Nat.cast Int instNatCastInt k))))) Bool.true 100535827539683224133 2251799813685248000

noncomputable def ep559 := nat_lit 863592847773673714271949684736

noncomputable def ep560 := nat_lit 655648815122063715185091359539200

noncomputable def ep561 := @ep558 69247037299949923651 296404000000000000000000 Bool.false 152659677234495572303 1801439850948198400 3640050004901855251 29640400000000000000000 Bool.false 1481013 8589934592 3 8589934592 Bool.true 10828015157 4294967296000 65801 12884901888000 Bool.true ep559 100535439301011352133 2251799813685248000 567272577579836014783367 ep185 Bool.false ep560

noncomputable def ep562 := @Enclosure.Complex.IsNear.addLitP qz157 qz52 Bool.true 102605091243288472133 2251799813685248000 67551000007469454901 296404000000000000000000

noncomputable def ep563 := nat_lit 13177431987281359553560576

noncomputable def ep564 := @ep562 Bool.false 152659677234495572303 1801439850948198400 3640050004901855251 29640400000000000000000 Bool.false 120447 131072 3 524288 Bool.false 0 1 0 1 Bool.true ep563 100535827539683224133 2251799813685248000 69247037299949923651 296404000000000000000000 Bool.false 152659677234495572303 152659677234495572303 1801439850948198400

noncomputable abbrev qz159 := (@HMul.hMul Complex Complex Complex qz312 qz389 qz390)

noncomputable def ep565 := @Enclosure.Complex.IsNear.subLitP qz159 qz158 Bool.true 97538541662496664133 2251799813685248000 67551000007469454901 296404000000000000000000 Bool.false 1059639745253083868811

noncomputable def ep566 := nat_lit 3053193544689911446060000

noncomputable def ep567 := @ep565 9007199254740992000 3640050004901855251 29640400000000000000000 Bool.false 9000 4000 0 1 Bool.false 131602 4000 0 1 Bool.true 410420364973153888532000 102605091243288472133 2251799813685248000 67551000007469454901 296404000000000000000000 Bool.false ep566 152659677234495572303 1801439850948198400 3640050004901855251 29640400000000000000000

noncomputable abbrev qz160 := qz389

noncomputable abbrev qz161 := qz390

noncomputable def ep568 := @Enclosure.Complex.IsNear.mul qz160 qz161 Bool.true 97538541662496664133 2251799813685248000 67551000007469454901 296404000000000000000000 Bool.false 1059639745253083868811 9007199254740992000 3640050004901855251

noncomputable abbrev qz162 := (Complex.re qz389)

noncomputable abbrev qz163 := (Complex.re qz390)

noncomputable abbrev qz164 := (Complex.im qz389)

noncomputable abbrev qz165 := (Complex.im qz390)

noncomputable def ep569 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 qz162 qz163) (@HMul.hMul Real Real Real qz0 qz164 qz165) 110206431711131077 18014398509481984 350000000518707 59280800000000000000 55657172813194024379 1125899906842624000

noncomputable def ep570 := nat_lit 878549079770963152019822884931239936

noncomputable def ep571 := @Enclosure.Real.IsNear.mulLit_ff qz162 qz163 7000 4000 0 1 15743775958733011 4503599627370496 50000000074101 14820200000000000000

noncomputable def ep572 := @Enclosure.Complex.IsNear.re_isNear qz160 Bool.false 7000 4000 0 1 Bool.false 131602 4000 0 1

noncomputable abbrev qz391 := (Enclosure.sfrac Bool.false 131602 4000)

noncomputable abbrev qz166 := qz391

noncomputable def ep573 := @Enclosure.Complex.IsNear.of_eq qz160 (Complex.mk (Enclosure.sfrac Bool.false 7000 4000) qz166) Bool.false 7000 4000 0 1 Bool.false 131602 4000 0

noncomputable abbrev qz167 := (Complex.mk qz327 qz391)

noncomputable def ep574 := @Enclosure.Complex.IsNear.of_eq qz161 (Complex.log qz167) Bool.false 15743775958733011 4503599627370496 50000000074101 14820200000000000000 Bool.false 845840835446179 562949953421312 1000000000074101 148202000000000000000

noncomputable def ep575 := BSN.log_dyadic_bound 1016086404 33784086404 2 1 3424093482458812953648 524288 148202 1032431580393651216 1032431580393651216 31546 34800172808 32768000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 1016086404) (BSN.artanhQ 33784086404) 0 1 1032431580393651216 3424093482458812953648 1032431580393651216 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz392 := (Real.log (Enclosure.sfrac Bool.false 17400086404 16000000))

noncomputable def ep576 := @Enclosure.Real.IsNear.mulLit_ff qz70 qz392 1 2 0 1 15743775958733011 2251799813685248 50000000074101 7410100000000000000 15743775958733011 4503599627370496 50000000074101 14820200000000000000 qz329 (BSN.isNear_log_sfrac 17400086404 16000000 15743775958733011 2251799813685248 50000000074101 7410100000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 17400086404) qz330)) Bool.false 132068364957635405938688 18889465931478580854784 1000000001482020 148202000000000000000 15743775958733011 2251799813685248 50000000074101 7410100000000000000 (BSN.log_rat_reduce_isNear 17400086404 16000000 10 34800172808 32768000000 31546 524288 24973259072661432 36028797018963968 148202 1000000000000000 rfl rfl rfl rfl (ep575 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep577 := BSN.arctan_dyadic_bound_f 9000 131602 1 0 524288 148202 0 1 1 0 1 1 35799 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 9000) (BSN.arctanEvenQ 131602) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 9000) (BSN.arctanOddQ 131602) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz393 := (Real.arctan (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 9000) (@Nat.cast Real Real.instNatCast 131602)))

noncomputable def ep578 := @Enclosure.Real.IsNear.subLit_ff_p qz71 qz393 884279719003555 562949953421312 1 2000000000000000 35799 524288 1 148202 443464199934406295552 845840835446179 562949953421312 1000000000074101 148202000000000000000 qz72 (ep577 rfl) rfl rfl

noncomputable abbrev qz394 := (Real.arctan (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 131602) (@Nat.cast Real Real.instNatCast 9000)))

noncomputable def ep579 := @Enclosure.Complex.IsNear.re_isNear qz161 Bool.false 15743775958733011 4503599627370496 50000000074101 14820200000000000000 Bool.false 845840835446179 562949953421312 1000000000074101 148202000000000000000 (ep574 (@congrArg Complex Complex qz158 qz167 Complex.log (BSN.w_shift_mk qz145 Bool.false 65801 1000 2 qz146 rfl)) (@Enclosure.Complex.IsNear.of_parts (Complex.log qz167) Bool.false 15743775958733011 4503599627370496 50000000074101 14820200000000000000 Bool.false 845840835446179 562949953421312 1000000000074101 148202000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re (Complex.log qz167)) (@HMul.hMul Real Real Real qz0 qz70 qz392) Bool.false 15743775958733011 4503599627370496 50000000074101 14820200000000000000 (Enclosure.clog_re_eq 9000 131602 4000 17400086404 16000000 rfl rfl rfl) (ep576 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im (Complex.log qz167)) qz394 Bool.false 845840835446179 562949953421312 1000000000074101 148202000000000000000 (Enclosure.clog_im_eq 9000 131602 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz394 (@HSub.hSub Real Real Real qz46 qz71 qz393) Bool.false 845840835446179 562949953421312 1000000000074101 148202000000000000000 (BSN.arctan_recip 131602 9000 rfl rfl) ep578))))

noncomputable def ep580 := @Enclosure.Real.IsNear.mulLit_ff qz164 qz165 131602 4000 0 1 845840835446179 562949953421312 1000000000074101 148202000000000000000

noncomputable def ep581 := @Enclosure.Complex.IsNear.im_isNear qz160 Bool.false 7000 4000 0 1 Bool.false 131602 4000 0 1

noncomputable def ep582 := @Enclosure.Complex.IsNear.im_isNear qz161 Bool.false 15743775958733011 4503599627370496 50000000074101 14820200000000000000 Bool.false 845840835446179 562949953421312 1000000000074101 148202000000000000000 (ep574 (@congrArg Complex Complex qz158 qz167 Complex.log (BSN.w_shift_mk qz145 Bool.false 65801 1000 2 qz146 rfl)) (@Enclosure.Complex.IsNear.of_parts (Complex.log qz167) Bool.false 15743775958733011 4503599627370496 50000000074101 14820200000000000000 Bool.false 845840835446179 562949953421312 1000000000074101 148202000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re (Complex.log qz167)) (@HMul.hMul Real Real Real qz0 qz70 qz392) Bool.false 15743775958733011 4503599627370496 50000000074101 14820200000000000000 (Enclosure.clog_re_eq 9000 131602 4000 17400086404 16000000 rfl rfl rfl) (ep576 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im (Complex.log qz167)) qz394 Bool.false 845840835446179 562949953421312 1000000000074101 148202000000000000000 (Enclosure.clog_im_eq 9000 131602 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz394 (@HSub.hSub Real Real Real qz46 qz71 qz393) Bool.false 845840835446179 562949953421312 1000000000074101 148202000000000000000 (BSN.arctan_recip 131602 9000 rfl rfl) ep578))))

noncomputable abbrev qz395 := (Enclosure.Real.IsNear.const Bool.false 131602 4000)

noncomputable abbrev qz168 := (@ep573 1 (BSN.w_sub_half_mk qz376 Bool.false 65801 1000 2 qz377 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7000 4000) qz391 Bool.false 7000 4000 0 1 Bool.false 131602 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 7000 4000) qz395))

noncomputable def ep583 := @ep569 65801000004875919901 296404000000000000000000 ep570 97538541662496664133 2251799813685248000 67551000007469454901 296404000000000000000000 (@ep571 110206431711131077 18014398509481984 350000000518707 59280800000000000000 (ep572 qz168) ep579 rfl) (@ep580 55657172813194024379 1125899906842624000 65801000004875919901 296404000000000000000000 (ep581 qz168) ep582 rfl) rfl

noncomputable def ep584 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz162 qz165) (@HMul.hMul Real Real Real qz0 qz164 qz163) 5920885848123253 2251799813685248 7000000000518707 592808000000000000000 1035956201860590856811 9007199254740992000

noncomputable def ep585 := nat_lit 2386096580934377909617111547278000128

noncomputable def ep586 := @Enclosure.Real.IsNear.mulLit_ff qz162 qz165 7000 4000 0 1 845840835446179 562949953421312 1000000000074101 148202000000000000000

noncomputable def ep587 := @Enclosure.Real.IsNear.mulLit_ff qz164 qz163 131602 4000 0 1 15743775958733011 4503599627370496 50000000074101 14820200000000000000

noncomputable def ep588 := @ep584 3290050004875919901 29640400000000000000000 ep585 1059639745253083868811 9007199254740992000 3640050004901855251 29640400000000000000000 (@ep586 5920885848123253 2251799813685248 7000000000518707 592808000000000000000 (ep572 qz168) ep582 rfl) (@ep587 1035956201860590856811 9007199254740992000 3290050004875919901 29640400000000000000000 (ep581 qz168) ep579 rfl) rfl

noncomputable def ep589 := @Enclosure.Complex.IsNear.of_eq qz158 qz167 Bool.false 9000 4000 0 1 Bool.false 131602 4000 0 1 (BSN.w_shift_mk qz145 Bool.false 65801 1000 2 qz146 rfl)

noncomputable abbrev qz396 := (ep589 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 9000 4000) (Enclosure.sfrac Bool.false 131602 4000) Bool.false 9000 4000 0 1 Bool.false 131602 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 9000 4000) (Enclosure.Real.IsNear.const Bool.false 131602 4000)))

noncomputable abbrev qz169 := qz396

noncomputable def ep590 := ep567 (@ep568 29640400000000000000000 (ep583 rfl) (ep588 rfl)) qz169 rfl rfl rfl rfl rfl rfl

noncomputable def ep591 := @ep564 3640050004901855251 29640400000000000000000 (ep590 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@Enclosure.Complex.IsNear.mul qz75 (↑qz3) Bool.false 120447 131072 3 524288 Bool.false 0 1 0 1 (@ep227 131072 3 524288 (ep229 rfl) (ep231 rfl) rfl rfl) (@ep232 1 0 1 (ep234 rfl) (ep236 rfl) rfl rfl))

noncomputable abbrev qz397 := (@HPow.hPow Complex Int Complex qz460 qz466 (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) (@OfNat.ofNat Int 1 (@instOfNat 1)) (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (@OfNat.ofNat Int 2 (@instOfNat 2)) (@Nat.cast Int instNatCastInt 1))))

noncomputable abbrev qz170 := qz397

noncomputable def ep592 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz47 (@HMul.hMul Complex Complex Complex qz45 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz55 qz158 (@HSub.hSub Int Int Int qz57 qz58 (@HMul.hMul Int Int Int qz59 qz60 (@Nat.cast Int instNatCastInt k))))) (@HAdd.hAdd Complex Complex Complex qz5 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz47 (@HMul.hMul Complex Complex Complex qz45 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz55 qz158 (@HSub.hSub Int Int Int qz57 qz58 (@HMul.hMul Int Int Int qz59 qz60 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli qz77)) qz78) qz170)) Bool.false 1481013 8589934592 3 8589934592

noncomputable def ep593 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz47 (@HMul.hMul Complex Complex Complex qz45 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz55 qz158 (@HSub.hSub Int Int Int qz57 qz58 (@HMul.hMul Int Int Int qz59 qz60 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli qz77)) qz78) qz170) Bool.false 0 1 0 1 Bool.false

noncomputable def ep594 := @ep593 0 1 0 1 Bool.false 1481013 8589934592 3 8589934592 Bool.true 10828015157 4294967296000 65801 12884901888000 Bool.false 1481013 1481013 8589934592 3 8589934592 Bool.true 10828015157 10828015157 4294967296000 65801

noncomputable def ep595 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz47 (@HMul.hMul Complex Complex Complex qz45 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz55 qz158 (@HSub.hSub Int Int Int qz57 qz58 (@HMul.hMul Int Int Int qz59 qz60 (@Nat.cast Int instNatCastInt k))))) (Complex.mk qz14 qz14) Bool.false 0 1 0 1 Bool.false

noncomputable def ep596 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli qz77)) qz78) qz170 Bool.false 1481013 8589934592 3 8589934592 Bool.true 10828015157 4294967296000 65801 12884901888000

noncomputable abbrev qz171 := (Complex.re qz397)

noncomputable abbrev qz172 := (Complex.im qz397)

noncomputable def ep597 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli qz77)) qz78)) qz171) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli qz77)) qz78)) qz172) 1481013 8589934592 3 8589934592 0 1 0

noncomputable def ep598 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli qz77)) qz78)) qz171 1 12 0 1 4443039 2147483648 9 2147483648 1481013

noncomputable def ep599 := @Enclosure.Complex.IsNear.re_isNear qz170 Bool.false 4443039 2147483648 9 2147483648 Bool.true 32484045471 1073741824000 65801 1073741824000

noncomputable abbrev qz398 := (@HPow.hPow Complex Nat Complex qz461 qz466 1)

noncomputable abbrev qz173 := (@Inv.inv Complex Complex.instInv qz398)

noncomputable def ep600 := @Enclosure.Complex.IsNear.of_eq qz170 qz173 Bool.false 4443039 2147483648 9 2147483648 Bool.true 32484045471 1073741824000 65801

noncomputable def ep601 := @Enclosure.Complex.IsNear.of_parts qz173 Bool.false 4443039 2147483648 9 2147483648 Bool.true 32484045471 1073741824000 65801

noncomputable abbrev qz174 := (Complex.re qz398)

noncomputable abbrev qz175 := qz398

noncomputable def ep602 := @Enclosure.Real.IsNear.mulLit_ff qz174 (@Inv.inv Real Real.instInv (@DFunLike.coe qz84 Complex (fun (x : Complex) => Real) qz85 Complex.normSq qz175)) 9000 4000 0 1 493671 536870912 1 536870912

noncomputable def ep603 := @Enclosure.Complex.IsNear.re_isNear qz175 Bool.false 9000 4000 0 1 Bool.false 131602 4000 0 1

noncomputable def ep604 := @Enclosure.Complex.IsNear.of_eq qz175 qz158 Bool.false 9000 4000 0 1 Bool.false 131602 4000 0

noncomputable def ep605 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (@DFunLike.coe qz84 Complex (fun (x : Complex) => Real) qz85 Complex.normSq qz175)) Bool.false 493671 536870912 1 536870912 493671 536870912 1

noncomputable abbrev qz176 := (Complex.im qz398)

noncomputable def ep606 := @Enclosure.Real.IsNear.of_eq (@DFunLike.coe qz84 Complex (fun (x : Complex) => Real) qz85 Complex.normSq qz175) (@HAdd.hAdd Real Real Real qz87 (@HMul.hMul Real Real Real qz0 qz174 qz174) (@HMul.hMul Real Real Real qz0 qz176 qz176)) Bool.false 4350021601 4000000 0 1

noncomputable def ep607 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz174 qz174) (@HMul.hMul Real Real Real qz0 qz176 qz176) 81 16 0 1 4329771601 4000000

noncomputable def ep608 := @Enclosure.Real.IsNear.mulLit_ff qz174 qz174 9000 4000 0 1 9000 4000 0 1

noncomputable def ep609 := @Enclosure.Real.IsNear.mulLit_ff qz176 qz176 131602 4000 0 1 131602 4000 0 1

noncomputable def ep610 := @Enclosure.Complex.IsNear.im_isNear qz175 Bool.false 9000 4000 0 1 Bool.false 131602 4000 0 1

noncomputable abbrev qz177 := (ep603 (@ep604 1 (BSN.pow_one_c qz386) qz396))

noncomputable abbrev qz178 := (ep610 (@ep604 1 (BSN.pow_one_c qz386) qz396))

noncomputable def ep611 := @ep607 0 1 69600345616 4350021601 4000000 0 1 (@ep608 81 16 0 1 qz177 qz177 rfl) (@ep609 4329771601 4000000 0 1 qz178 qz178 rfl)

noncomputable def ep612 := @Enclosure.Real.IsNear.inv_image (@DFunLike.coe qz84 Complex (fun (x : Complex) => Real) qz85 Complex.normSq qz175) 4350021601 4000000 0 1 246835 246836 268435456 (ep606 (Enclosure.Complex.normSq_eq_mul_add_mul qz175) (ep611 rfl rfl)) rfl

noncomputable def ep613 := @Enclosure.Real.IsNear.of_eq (Complex.re qz173) (@HMul.hMul Real Real Real qz0 qz174 (@Inv.inv Real Real.instInv (@DFunLike.coe qz84 Complex (fun (x : Complex) => Real) qz85 Complex.normSq qz175))) Bool.false 4443039 2147483648 9 2147483648 (Enclosure.Complex.inv_re_eq_mul qz175) (@ep602 4443039 2147483648 9 2147483648 qz177 (@ep605 536870912 (ep612 rfl rfl rfl rfl rfl) rfl) rfl)

noncomputable def ep614 := @Enclosure.Real.IsNear.of_eq (Complex.im qz173) (@HMul.hMul Real Real Real qz0 (@Neg.neg Real Real.instNeg qz176) (@Inv.inv Real Real.instInv (@DFunLike.coe qz84 Complex (fun (x : Complex) => Real) qz85 Complex.normSq qz175))) Bool.true 32484045471 1073741824000 65801 1073741824000 (Enclosure.Complex.inv_im_eq_mul qz175)

noncomputable def ep615 := @Enclosure.Real.IsNear.mulLit_tf (@Neg.neg Real Real.instNeg qz176) (@Inv.inv Real Real.instInv (@DFunLike.coe qz84 Complex (fun (x : Complex) => Real) qz85 Complex.normSq qz175)) 131602 4000 0 1 493671 536870912 1

noncomputable def ep616 := @ep615 536870912 32484045471 1073741824000 65801 1073741824000 (@Enclosure.Real.IsNear.neg qz176 Bool.false 131602 4000 0 1 qz178) (@ep605 536870912 (ep612 rfl rfl rfl rfl rfl) rfl) rfl

noncomputable def ep617 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli qz77)) qz78)) qz172 0 1 0 1 32484045471 1073741824000 65801 1073741824000 0

noncomputable def ep618 := @Enclosure.Complex.IsNear.im_isNear qz170 Bool.false 4443039 2147483648 9 2147483648 Bool.true 32484045471 1073741824000 65801 1073741824000

noncomputable abbrev qz179 := (@ep600 1073741824000 (BSN.zpow_one_sub_two_mul qz386 1 1 rfl rfl) (@ep601 1073741824000 ep613 (ep614 ep616)))

noncomputable def ep619 := @ep597 1 1481013 1481013 8589934592 3 8589934592 (@ep598 8589934592 3 8589934592 ep246 (ep599 qz179) rfl) (@ep617 1 0 1 ep266 (ep618 qz179) rfl) rfl

noncomputable def ep620 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli qz77)) qz78)) qz172) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli qz77)) qz78)) qz171) 10828015157 4294967296000 65801 12884901888000 0 1 0

noncomputable def ep621 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli qz77)) qz78)) qz172 1 12 0 1 32484045471 1073741824000 65801 1073741824000 10828015157

noncomputable def ep622 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli qz77)) qz78)) qz171 0 1 0 1 4443039 2147483648 9 2147483648 0

noncomputable def ep623 := @ep620 1 10828015157 10828015157 4294967296000 65801 12884901888000 (@ep621 4294967296000 65801 12884901888000 ep246 (ep618 qz179) rfl) (@ep622 1 0 1 ep266 (ep599 qz179) rfl) rfl

noncomputable def ep624 := @ep594 12884901888000 (@ep595 0 1 0 1 (BSN.stirling_sum_base qz158) qz92) (ep596 (ep619 rfl) (ep623 rfl)) rfl rfl rfl rfl rfl

noncomputable def ep625 := @ep561 763275678178835328651 9007199254740992000 715692711617045959141733 ep549 (ep591 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep592 Bool.true 10828015157 4294967296000 65801 12884901888000 (BSN.stirling_sum_succ qz158 0 1 rfl) (ep624 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl

noncomputable def ep626 := @Enclosure.Complex.IsNear.of_eq (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz155 (@Nat.cast Complex Complex.instNatCast j))) (BSN.logSumC qz145 2) Bool.false 15734958390874323 2251799813685248 50000000074101 7410100000000000000 Bool.false 871452799174051 281474976710656

noncomputable abbrev qz180 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz269 qz387 qz335))

noncomputable def ep627 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz145 2) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.logSumC qz145 1) qz180) Bool.false 15734958390874323 2251799813685248 50000000074101 7410100000000000000 Bool.false 871452799174051 281474976710656 1000000000074101 74101000000000000000

noncomputable def ep628 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz145 1) qz180 Bool.false 15733399317745875 4503599627370496 50000000074101 14820200000000000000 Bool.false 880003005318563 562949953421312 1000000000074101 148202000000000000000 Bool.false

noncomputable def ep629 := nat_lit 141727905491663720821325788348416

noncomputable def ep630 := nat_lit 981168625407807941990441549824

noncomputable abbrev qz181 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz269 qz387 (@Nat.cast Complex Complex.instNatCast 0)))

noncomputable def ep631 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz145 1) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.logSumC qz145 0) qz181) Bool.false 15733399317745875 4503599627370496 50000000074101 14820200000000000000 Bool.false 880003005318563 562949953421312 1000000000074101 148202000000000000000

noncomputable def ep632 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz145 0) qz181 Bool.false 0 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable abbrev qz399 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz166))

noncomputable def ep633 := @Enclosure.Complex.IsNear.of_eq qz181 qz399 Bool.false 15733399317745875 4503599627370496 50000000074101 14820200000000000000 Bool.false 880003005318563 562949953421312 1000000000074101 148202000000000000000

noncomputable def ep634 := BSN.log_dyadic_bound 936086404 33704086404 2 1 3407896320984892953648 524288 148202 876257755753651216 876257755753651216 29130 34640172808 32768000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 936086404) (BSN.artanhQ 33704086404) 0 1 876257755753651216 3407896320984892953648 876257755753651216 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep635 := @Enclosure.Real.IsNear.mulLit_ff qz70 (Real.log (Enclosure.sfrac Bool.false 17320086404 16000000)) 1 2 0 1 15733399317745875 2251799813685248 50000000074101 7410100000000000000 15733399317745875 4503599627370496 50000000074101 14820200000000000000 qz329 (BSN.isNear_log_sfrac 17320086404 16000000 15733399317745875 2251799813685248 50000000074101 7410100000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 17320086404) qz330)) Bool.false 131981319384037588992000 18889465931478580854784 1000000001482020 148202000000000000000 15733399317745875 2251799813685248 50000000074101 7410100000000000000 (BSN.log_rat_reduce_isNear 17320086404 16000000 10 34640172808 32768000000 29130 524288 24973259072661432 36028797018963968 148202 1000000000000000 rfl rfl rfl rfl (ep634 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep636 := BSN.arctan_dyadic_bound_f 1000 131602 1 0 524288 148202 0 1 1 0 1 1 3983 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 131602) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 131602) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz400 := (@Nat.cast Real Real.instNatCast 131602)

noncomputable def ep637 := @Enclosure.Real.IsNear.subLit_ff_p qz71 (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz340 qz400)) 884279719003555 562949953421312 1 2000000000000000 3983 524288 1 148202 461375015652458758144 880003005318563 562949953421312 1000000000074101 148202000000000000000 qz72 (ep636 rfl) rfl rfl

noncomputable abbrev qz182 := (@HAdd.hAdd Complex Complex Complex qz269 qz387 (@Nat.cast Complex Complex.instNatCast 0))

noncomputable abbrev qz401 := (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz166)

noncomputable def ep638 := @ep632 15733399317745875 4503599627370496 50000000074101 14820200000000000000 Bool.false 880003005318563 562949953421312 1000000000074101 148202000000000000000 Bool.false 15733399317745875 15733399317745875 4503599627370496 50000000074101 14820200000000000000 Bool.false 880003005318563 880003005318563 562949953421312 1000000000074101 148202000000000000000 (@Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz145 0) (Complex.mk qz14 qz14) Bool.false 0 1 0 1 Bool.false 0 1 0 1 (BSN.log_sum_c_base qz145) qz92) (ep633 (@congrArg Complex Complex qz182 qz401 Complex.log (BSN.w_shift_mk qz145 Bool.false 65801 1000 0 qz146 rfl)) (@Enclosure.Complex.IsNear.of_parts qz399 Bool.false 15733399317745875 4503599627370496 50000000074101 14820200000000000000 Bool.false 880003005318563 562949953421312 1000000000074101 148202000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz399) (@HMul.hMul Real Real Real qz0 qz70 (Real.log (Enclosure.sfrac Bool.false 17320086404 16000000))) Bool.false 15733399317745875 4503599627370496 50000000074101 14820200000000000000 (Enclosure.clog_re_eq 1000 131602 4000 17320086404 16000000 rfl rfl rfl) (ep635 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz399) (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz400 qz340)) Bool.false 880003005318563 562949953421312 1000000000074101 148202000000000000000 (Enclosure.clog_im_eq 1000 131602 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz400 qz340)) (@HSub.hSub Real Real Real qz46 qz71 (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz340 qz400))) Bool.false 880003005318563 562949953421312 1000000000074101 148202000000000000000 (BSN.arctan_recip 131602 1000 rfl rfl) ep637)))) rfl rfl

noncomputable abbrev qz402 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz166))

noncomputable def ep639 := @Enclosure.Complex.IsNear.of_eq qz180 qz402 Bool.false 15736517464002771 4503599627370496 50000000074101 14820200000000000000 Bool.false 862902593029539 562949953421312 1000000000074101 148202000000000000000

noncomputable def ep640 := BSN.log_dyadic_bound 960086404 33728086404 2 1 3412751437427068953648 524288 148202 921765903145651216 921765903145651216 29856 34688172808 32768000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 960086404) (BSN.artanhQ 33728086404) 0 1 921765903145651216 3412751437427068953648 921765903145651216 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep641 := @Enclosure.Real.IsNear.mulLit_ff qz70 (Real.log (Enclosure.sfrac Bool.false 17344086404 16000000)) 1 2 0 1 15736517464002771 2251799813685248 50000000074101 7410100000000000000 15736517464002771 4503599627370496 50000000074101 14820200000000000000 qz329 (BSN.isNear_log_sfrac 17344086404 16000000 15736517464002771 2251799813685248 50000000074101 7410100000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 17344086404) qz330)) Bool.false 132007476290673356832768 18889465931478580854784 1000000001482020 148202000000000000000 15736517464002771 2251799813685248 50000000074101 7410100000000000000 (BSN.log_rat_reduce_isNear 17344086404 16000000 10 34688172808 32768000000 29856 524288 24973259072661432 36028797018963968 148202 1000000000000000 rfl rfl rfl rfl (ep640 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep642 := BSN.arctan_dyadic_bound_f 5000 131602 1 0 524288 148202 0 1 1 0 1 1 19909 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 5000) (BSN.arctanEvenQ 131602) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 5000) (BSN.arctanOddQ 131602) 0 0 rfl) rfl rfl rfl

noncomputable def ep643 := @Enclosure.Real.IsNear.subLit_ff_p qz71 (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz344 qz400)) 884279719003555 562949953421312 1 2000000000000000 19909 524288 1 148202 452409474694270943232 862902593029539 562949953421312 1000000000074101 148202000000000000000 qz72 (ep642 rfl) rfl rfl

noncomputable abbrev qz183 := (@HAdd.hAdd Complex Complex Complex qz269 qz387 qz335)

noncomputable abbrev qz403 := (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz166)

noncomputable def ep644 := @ep628 15736517464002771 4503599627370496 50000000074101 14820200000000000000 Bool.false 862902593029539 562949953421312 1000000000074101 148202000000000000000 Bool.false ep629 15734958390874323 2251799813685248 50000000074101 7410100000000000000 Bool.false ep630 871452799174051 281474976710656 1000000000074101 74101000000000000000 (ep631 (BSN.log_sum_c_succ qz145 0 1 rfl) (ep638 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep639 (@congrArg Complex Complex qz183 qz403 Complex.log (BSN.w_shift_mk qz145 Bool.false 65801 1000 1 qz146 rfl)) (@Enclosure.Complex.IsNear.of_parts qz402 Bool.false 15736517464002771 4503599627370496 50000000074101 14820200000000000000 Bool.false 862902593029539 562949953421312 1000000000074101 148202000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz402) (@HMul.hMul Real Real Real qz0 qz70 (Real.log (Enclosure.sfrac Bool.false 17344086404 16000000))) Bool.false 15736517464002771 4503599627370496 50000000074101 14820200000000000000 (Enclosure.clog_re_eq 5000 131602 4000 17344086404 16000000 rfl rfl rfl) (ep641 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz402) (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz400 qz344)) Bool.false 862902593029539 562949953421312 1000000000074101 148202000000000000000 (Enclosure.clog_im_eq 5000 131602 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz400 qz344)) (@HSub.hSub Real Real Real qz46 qz71 (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz344 qz400))) Bool.false 862902593029539 562949953421312 1000000000074101 148202000000000000000 (BSN.arctan_recip 131602 5000 rfl rfl) ep643)))) rfl rfl

noncomputable def ep645 := @ep554 ep549 Bool.false 15734958390874323 2251799813685248 50000000074101 7410100000000000000 Bool.false 871452799174051 281474976710656 1000000000074101 74101000000000000000 Bool.true ep555 116270397691885675133 2251799813685248000 583656577604117430463367 ep185 Bool.false ep556 735389188605265696651 9007199254740992000 794335911622873498904933 ep549 (@ep557 2251799813685248000 567272577579836014783367 ep185 Bool.false 763275678178835328651 9007199254740992000 715692711617045959141733 ep549 (BSN.logGammaStirling_unfold 1 qz158) (ep625 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (@ep626 1000000000074101 74101000000000000000 (BSN.log_sum_c_eq qz145 2) (ep627 (BSN.log_sum_c_succ qz145 1 2 rfl) (ep644 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)))

noncomputable abbrev qz184 := (@HDiv.hDiv Real Real Real qz266 qz376 (2 : Real))

noncomputable def ep646 := @Enclosure.Real.IsNear.mulLit_ff qz184 (Real.log Real.pi) 65801 2000 0 1 75021 65536 1 131072 4936456821 131072000 65801 262144000 (@Enclosure.Real.IsNear.of_eq qz184 (Enclosure.sfrac Bool.false 65801 2000) Bool.false 65801 2000 0 1 (BSN.t_half_eq qz145 Bool.false 65801 1000 qz146) (Enclosure.Real.IsNear.const Bool.false 65801 2000)) EMRow15.d5 rfl

noncomputable def ep647 := @ep551 65801 262144000 ep552 79231691787257536079 1801439850948198400 ep548 ep549 (@ep553 794335911622873498904933 ep549 (ep645 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) ep646 rfl rfl

noncomputable def ep648 := BSN.cos_dyadic_bound_f 135970 1073741824 1 0 524288 148347 0 1 1 0 1 1 524287 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 135970) qz283 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 135970) qz284 0 0 rfl) rfl rfl

noncomputable def ep649 := @ep547 131072 Bool.false 524287 524288 1 74101 (@ep550 23059457 524288 51 131072 ep647 rfl) (Enclosure.sfrac_false_div 23059457 524288) (BSN.cos_reduce0 qz388 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 9568050315089936384) qz23) 226375608064910080 72057594037927936 Bool.false 524287 524288 7 1000000000000000 148202 74101 (BSN.sin_reduce_arg_pos_rat_q0 23059457 524288 226375608064910080 72057594037927936 7 9568050315089936384 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 524287 524288 9568050315089936384 75557863725914323419136 135970 1073741824 148347 148202 (ep648 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep650 := nat_lit 3332636369174526112563200

noncomputable def ep651 := nat_lit 1418780390276018916441559001

noncomputable def ep652 := nat_lit 308689609490251949333807104000

noncomputable abbrev qz185 := qz375

noncomputable abbrev qz468 := (@Nat.cast Complex Complex.instNatCast 14)

noncomputable abbrev qz404 := (@HPow.hPow Complex Complex Complex qz449 qz468 qz464)

noncomputable abbrev qz186 := qz404

noncomputable abbrev qz405 := qz468

noncomputable abbrev qz187 := (@HAdd.hAdd Complex Complex Complex qz269 (@HDiv.hDiv Complex Complex Complex qz320 qz405 (@HSub.hSub Complex Complex Complex qz313 qz374 (1 : Complex))) qz319)

noncomputable abbrev qz188 := qz405

noncomputable def ep653 := @Enclosure.Complex.IsNear.of_eq (zetaApproximant qz136 1 14) (@HAdd.hAdd Complex Complex Complex qz5 (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 14, @HPow.hPow Complex Complex Complex qz98 (@Nat.cast Complex Complex.instNatCast n) qz185) (@HMul.hMul Complex Complex Complex qz45 qz186 (@HAdd.hAdd Complex Complex Complex qz5 qz187 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz136 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz103 qz188 (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz54 2 k) 1))))))) Bool.false ep542 ep543 ep544

noncomputable def ep654 := @Enclosure.Complex.IsNear.addLitP (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 14, @HPow.hPow Complex Complex Complex qz98 (@Nat.cast Complex Complex.instNatCast n) qz185) (@HMul.hMul Complex Complex Complex qz45 qz186 (@HAdd.hAdd Complex Complex Complex qz5 qz187 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz136 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz103 qz188 (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))))) Bool.false 171620244667 137438953472 2821648162793 636522743201792

noncomputable def ep655 := nat_lit 814612894753824613552315949

noncomputable def ep656 := nat_lit 50934596993434797141882001

noncomputable def ep657 := nat_lit 1472747735484621411789099746933604352

noncomputable def ep658 := nat_lit 15128637781682583004497153955463168

noncomputable def ep659 := @ep654 Bool.true 5210060765 137438953472 45128306485211 10184363891228672 Bool.true 1174259765461511605113459 ep543 ep655 ep545 Bool.false 236409510927702918277869 ep650 ep656 ep652 Bool.false ep657 ep542 ep543 ep544 ep545 Bool.false ep658 110075327259856443593869 ep650

noncomputable def ep660 := @Enclosure.Complex.IsNear.of_eq (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 14, @HPow.hPow Complex Complex Complex qz98 (@Nat.cast Complex Complex.instNatCast n) qz185) (BSN.headSumC qz136 14) Bool.false 171620244667 137438953472 2821648162793 636522743201792 Bool.true 5210060765 137438953472 45128306485211

noncomputable abbrev qz189 := (@HPow.hPow Complex Complex Complex qz270 qz347 qz375)

noncomputable def ep661 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz136 14) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz136 13) qz189) Bool.false 171620244667 137438953472 2821648162793 636522743201792 Bool.true 5210060765 137438953472 45128306485211 10184363891228672

noncomputable def ep662 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz136 13) qz189 Bool.false 73520348141 68719476736 42585110374229 10184363891228672 Bool.true 68690816971 274877906944 85129449266743 20368727782457344 Bool.false

noncomputable abbrev qz190 := (@HPow.hPow Complex Complex Complex qz270 (@Nat.cast Complex Complex.instNatCast 12) qz375)

noncomputable def ep663 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz136 13) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz136 12) qz190) Bool.false 73520348141 68719476736 42585110374229 10184363891228672 Bool.true 68690816971 274877906944 85129449266743 20368727782457344

noncomputable def ep664 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz136 12) qz190 Bool.false 107790300669 137438953472 39907471736067 10184363891228672 Bool.true 28555325467 137438953472 9975867070335 2546090972807168 Bool.false

noncomputable abbrev qz191 := (@HPow.hPow Complex Complex Complex qz270 (@Nat.cast Complex Complex.instNatCast 11) qz375)

noncomputable def ep665 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz136 12) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz136 11) qz191) Bool.false 107790300669 137438953472 39907471736067 10184363891228672 Bool.true 28555325467 137438953472 9975867070335 2546090972807168

noncomputable def ep666 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz136 11) qz191 Bool.false 76205167995 137438953472 37121890731501 10184363891228672 Bool.true 1729951483 137438953472 9280029614471 2546090972807168 Bool.false

noncomputable abbrev qz192 := (@HPow.hPow Complex Complex Complex qz270 (@Nat.cast Complex Complex.instNatCast 10) qz375)

noncomputable def ep667 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz136 11) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz136 10) qz192) Bool.false 76205167995 137438953472 37121890731501 10184363891228672 Bool.true 1729951483 137438953472 9280029614471 2546090972807168

noncomputable def ep668 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz136 10) qz192 Bool.false 21704546625 68719476736 17100607001349 5092181945614336 Bool.false 53579379859 274877906944 68402706106449 20368727782457344 Bool.false

noncomputable abbrev qz193 := (@HPow.hPow Complex Complex Complex qz270 (@Nat.cast Complex Complex.instNatCast 9) qz375)

noncomputable def ep669 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz136 10) (@HAdd.hAdd Complex Complex Complex qz5 qz135 qz193) Bool.false 21704546625 68719476736 17100607001349 5092181945614336 Bool.false 53579379859 274877906944 68402706106449 20368727782457344

noncomputable def ep670 := @Enclosure.Complex.IsNear.addLitP qz135 qz193 Bool.true 1151657567 68719476736 121531834045 39782671450112 Bool.false 29824012517 137438953472 15565192218901 5092181945614336 Bool.false

noncomputable abbrev qz194 := (@HMul.hMul Real Real Real qz263 qz376 (Real.log (Enclosure.sfrac Bool.false 9 1)))

noncomputable def ep671 := @Enclosure.Complex.IsNear.of_eq qz193 (Complex.mk (@HMul.hMul Real Real Real qz0 qz109 (Real.cos qz194)) (@HMul.hMul Real Real Real qz0 qz109 (@Neg.neg Real Real.instNeg (Real.sin qz194)))) Bool.false 714256381 2147483648 1544532243589 5092181945614336 Bool.true 6068645175 274877906944 6141937230845 20368727782457344 (BSN.cpow_neg_s_mk qz145 65801 1000 9 qz146 rfl)

noncomputable def ep672 := @Enclosure.Real.IsNear.mulLit_ff qz145 qz111 65801 1000 0 1 9895417793173221 4503599627370496 1000000000222303 74101000000000000000 651128386208591115021 4503599627370496000 65801000014627759703 74101000000000000000000 qz147 (BSN.isNear_log_sfrac 9 1 9895417793173221 4503599627370496 1000000000222303 74101000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz350) Bool.false 20752195215788806766592 9444732965739290427392 1000000000222303 74101000000000000000 9895417793173221 4503599627370496 1000000000222303 74101000000000000000 (BSN.log_rat_reduce_isNear 9 1 3 18 16 30876 262144 24973259072661432 36028797018963968 74101 1000000000000000 rfl rfl rfl rfl (ep326 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep673 := BSN.cos_dyadic_bound_f 71169757 1073741824 1 0 524288 148347 0 1 1 0 1 1 523136 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 71169757) qz283 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 71169757) qz284 0 0 rfl) rfl rfl

noncomputable abbrev qz406 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 9475165) (@Nat.cast Real Real.instNatCast 65536))

noncomputable def ep674 := @Enclosure.Real.IsNear.cos_image qz194 qz406 Bool.false 9475165 65536 467 524288 Bool.false 523136 524288 1 74101 (@Enclosure.Real.IsNear.recentre' qz194 Bool.false 651128386208591115021 4503599627370496000 65801000014627759703 74101000000000000000000 9475165 65536 467 524288 (ep672 rfl) rfl) (Enclosure.sfrac_false_div 9475165 65536) (BSN.cos_reduce0 qz406 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 626015811707779153920) (@Nat.cast Real Real.instNatCast 9444732965739290427392)) 226375608064910080 72057594037927936 Bool.false 523136 524288 23 1000000000000000 148202 74101 (BSN.sin_reduce_arg_pos_rat_q0 9475165 65536 226375608064910080 72057594037927936 23 626015811707779153920 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 523136 524288 626015811707779153920 9444732965739290427392 71169757 1073741824 148347 148202 (ep673 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep675 := BSN.sin_dyadic_bound_f 71169757 1073741824 1 0 524288 148347 0 1 1 0 1 1 34725 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 71169757) qz278 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 71169757) qz279 0 0 rfl) rfl rfl

noncomputable def ep676 := @Enclosure.Real.IsNear.sin_image qz194 qz406 Bool.false 9475165 65536 467 524288 Bool.false 34725 524288 1 74101 (@Enclosure.Real.IsNear.recentre' qz194 Bool.false 651128386208591115021 4503599627370496000 65801000014627759703 74101000000000000000000 9475165 65536 467 524288 (ep672 rfl) rfl) (Enclosure.sfrac_false_div 9475165 65536) (BSN.sin_reduce0 qz406 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 626015811707779153920) (@Nat.cast Real Real.instNatCast 9444732965739290427392)) 226375608064910080 72057594037927936 Bool.false 34725 524288 23 1000000000000000 148202 74101 (BSN.sin_reduce_arg_pos_rat_q0 9475165 65536 226375608064910080 72057594037927936 23 626015811707779153920 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 34725 524288 626015811707779153920 9444732965739290427392 71169757 1073741824 148347 148202 (ep675 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep677 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz109 (Real.cos qz194)) (@HMul.hMul Real Real Real qz0 qz109 (@Neg.neg Real Real.instNeg (Real.sin qz194))) Bool.false 714256381 2147483648 1544532243589 5092181945614336 Bool.true 6068645175 274877906944 6141937230845 20368727782457344 (@Enclosure.Real.IsNear.mulLit_ff qz109 (Real.cos qz194) 174763 524288 1 524288 4087 4096 35129455 38850265088 714256381 2147483648 1544532243589 5092181945614336 qz352 (@Enclosure.Real.IsNear.recentre' (Real.cos qz194) Bool.false 523136 524288 35129455 38850265088 4087 4096 35129455 38850265088 (ep674 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz109 (@Neg.neg Real Real.instNeg (Real.sin qz194)) 174763 524288 1 524288 34725 524288 35129455 38850265088 6068645175 274877906944 6141937230845 20368727782457344 qz352 (@Enclosure.Real.IsNear.neg (Real.sin qz194) Bool.false 34725 524288 35129455 38850265088 (@Enclosure.Real.IsNear.recentre' (Real.sin qz194) Bool.false 34725 524288 35129455 38850265088 34725 524288 35129455 38850265088 (ep676 rfl rfl) rfl)) rfl)

noncomputable def ep678 := @ep670 714256381 2147483648 1544532243589 5092181945614336 Bool.true 6068645175 274877906944 6141937230845 20368727782457344 Bool.false 46610158964441088000 21704546625 68719476736 17100607001349 5092181945614336 Bool.false 7363893895499714920448 53579379859 274877906944 68402706106449 20368727782457344 EMRow15.d10 (ep671 ep677) rfl rfl

noncomputable abbrev qz195 := (@HMul.hMul Real Real Real qz263 qz376 (Real.log (Enclosure.sfrac Bool.false 10 1)))

noncomputable def ep679 := @Enclosure.Complex.IsNear.of_eq qz192 (Complex.mk (@HMul.hMul Real Real Real qz0 qz112 (Real.cos qz195)) (@HMul.hMul Real Real Real qz0 qz112 (@Neg.neg Real Real.instNeg (Real.sin qz195)))) Bool.false 32796074745 137438953472 2920676728803 10184363891228672 Bool.true 57039282825 274877906944 5837530809319 20368727782457344 (BSN.cpow_neg_s_mk qz145 65801 1000 10 qz146 rfl)

noncomputable def ep680 := @Enclosure.Real.IsNear.mulLit_ff qz145 qz114 65801 1000 0 1 10369908600166117 4503599627370496 1000000000222303 74101000000000000000 682350355799530664717 4503599627370496000 65801000014627759703 74101000000000000000000 qz147 (BSN.isNear_log_sfrac 10 1 10369908600166117 4503599627370496 1000000000222303 74101000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz354) Bool.false 21747274560655572598784 9444732965739290427392 1000000000222303 74101000000000000000 10369908600166117 4503599627370496 1000000000222303 74101000000000000000 (BSN.log_rat_reduce_isNear 10 1 3 20 16 58495 262144 24973259072661432 36028797018963968 74101 1000000000000000 rfl rfl rfl rfl (ep337 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep681 := nat_lit 779226067166231266275023013970238513195237806026196006128123054666938932161

noncomputable def ep682 := nat_lit 121723303034229876888005790196120378230084651462230981152509085607353281

noncomputable def ep683 := nat_lit 2337434754892625339071293030330323298829253248775663556422064145829602089921

noncomputable def ep684 := BSN.cos_dyadic_bound_f 768549273 1073741824 3 2 524288 148347 ep681 ep64 ep682 ep683 ep66 ep682 395622 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 768549273) qz283 0 2 ep681 ep64 ep682 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 768549273) qz284 0 2 ep683 ep66 ep682 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz407 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 19859009) (@Nat.cast Real Real.instNatCast 131072))

noncomputable def ep685 := @Enclosure.Real.IsNear.cos_image qz195 qz407 Bool.false 19859009 131072 233 262144 Bool.false 395622 524288 1 74101 (@Enclosure.Real.IsNear.recentre' qz195 Bool.false 682350355799530664717 4503599627370496000 65801000014627759703 74101000000000000000000 19859009 131072 233 262144 (ep680 rfl) rfl) (Enclosure.sfrac_false_div 19859009 131072) (BSN.cos_reduce0 qz407 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 13520461807860620197888) qz298) 226375608064910080 72057594037927936 Bool.false 395622 524288 24 1000000000000000 148202 74101 (BSN.sin_reduce_arg_pos_rat_q0 19859009 131072 226375608064910080 72057594037927936 24 13520461807860620197888 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 395622 524288 13520461807860620197888 18889465931478580854784 768549273 1073741824 148347 148202 (ep684 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep686 := nat_lit 348888668538016403270719214084303841

noncomputable def ep687 := BSN.sin_dyadic_bound_f 768549273 1073741824 2 1 524288 148347 ep686 ep79 ep686 ep686 ep80 ep686 344035 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 768549273) qz278 0 1 ep686 ep79 ep686 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 768549273) qz279 0 1 ep686 ep80 ep686 rfl rfl rfl rfl) rfl rfl

noncomputable def ep688 := @Enclosure.Real.IsNear.sin_image qz195 qz407 Bool.false 19859009 131072 233 262144 Bool.false 344035 524288 1 74101 (@Enclosure.Real.IsNear.recentre' qz195 Bool.false 682350355799530664717 4503599627370496000 65801000014627759703 74101000000000000000000 19859009 131072 233 262144 (ep680 rfl) rfl) (Enclosure.sfrac_false_div 19859009 131072) (BSN.sin_reduce0 qz407 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 13520461807860620197888) qz298) 226375608064910080 72057594037927936 Bool.false 344035 524288 24 1000000000000000 148202 74101 (BSN.sin_reduce_arg_pos_rat_q0 19859009 131072 226375608064910080 72057594037927936 24 13520461807860620197888 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 344035 524288 13520461807860620197888 18889465931478580854784 768549273 1073741824 148347 148202 (ep687 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep689 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz112 (Real.cos qz195)) (@HMul.hMul Real Real Real qz0 qz112 (@Neg.neg Real Real.instNeg (Real.sin qz195))) Bool.false 32796074745 137438953472 2920676728803 10184363891228672 Bool.true 57039282825 274877906944 5837530809319 20368727782457344 (@Enclosure.Real.IsNear.mulLit_ff qz112 (Real.cos qz195) 165795 524288 1 524288 197811 262144 17527677 19425132544 32796074745 137438953472 2920676728803 10184363891228672 qz356 (@Enclosure.Real.IsNear.recentre' (Real.cos qz195) Bool.false 395622 524288 17527677 19425132544 197811 262144 17527677 19425132544 (ep685 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz112 (@Neg.neg Real Real.instNeg (Real.sin qz195)) 165795 524288 1 524288 344035 524288 17527677 19425132544 57039282825 274877906944 5837530809319 20368727782457344 qz356 (@Enclosure.Real.IsNear.neg (Real.sin qz195) Bool.false 344035 524288 17527677 19425132544 (@Enclosure.Real.IsNear.recentre' (Real.sin qz195) Bool.false 344035 524288 17527677 19425132544 344035 524288 17527677 19425132544 (ep688 rfl rfl) rfl)) rfl)

noncomputable def ep690 := @ep668 32796074745 137438953472 2920676728803 10184363891228672 Bool.true 57039282825 274877906944 5837530809319 20368727782457344 Bool.false 5236779269195374264320 76205167995 137438953472 37121890731501 10184363891228672 Bool.true 951050885523417595904 1729951483 137438953472 9280029614471 2546090972807168 (ep669 (BSN.head_sum_c_succ qz136 9 10 rfl rfl) (ep678 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep679 ep689) rfl rfl

noncomputable abbrev qz196 := (@HMul.hMul Real Real Real qz263 qz376 (Real.log (Enclosure.sfrac Bool.false 11 1)))

noncomputable def ep691 := @Enclosure.Complex.IsNear.of_eq qz191 (Complex.mk (@HMul.hMul Real Real Real qz0 qz115 (Real.cos qz196)) (@HMul.hMul Real Real Real qz0 qz115 (@Neg.neg Real Real.instNeg (Real.sin qz196)))) Bool.false 15792566337 68719476736 1392790502283 5092181945614336 Bool.true 838292937 4294967296 86979681983 318261371600896 (BSN.cpow_neg_s_mk qz145 65801 1000 11 qz146 rfl)

noncomputable def ep692 := @Enclosure.Real.IsNear.mulLit_ff qz145 qz117 65801 1000 0 1 10799147631728357 4503599627370496 1000000000222303 74101000000000000000 710594713315357618957 4503599627370496000 65801000014627759703 74101000000000000000000 qz147 (BSN.isNear_log_sfrac 11 1 10799147631728357 4503599627370496 1000000000222303 74101000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz358) Bool.false 22647454054174387339264 9444732965739290427392 1000000000222303 74101000000000000000 10799147631728357 4503599627370496 1000000000222303 74101000000000000000 (BSN.log_rat_reduce_isNear 11 1 3 22 16 83480 262144 24973259072661432 36028797018963968 74101 1000000000000000 rfl rfl rfl rfl (ep351 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep693 := nat_lit 326670802146728947617366200979027121

noncomputable def ep694 := BSN.cos_dyadic_bound_f 756010069 1073741824 2 1 524288 148347 ep693 ep75 ep693 ep693 ep76 ep693 399612 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 756010069) qz283 0 1 ep693 ep75 ep693 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 756010069) qz284 0 1 ep693 ep76 ep693 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz408 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 5170257) (@Nat.cast Real Real.instNatCast 32768))

noncomputable def ep695 := @Enclosure.Real.IsNear.cos_image qz196 qz408 Bool.false 5170257 32768 233 262144 Bool.false 399612 524288 1 74101 (@Enclosure.Real.IsNear.recentre' qz196 Bool.false 710594713315357618957 4503599627370496000 65801000014627759703 74101000000000000000000 5170257 32768 233 262144 (ep692 rfl) rfl) (Enclosure.sfrac_false_div 5170257 32768) (BSN.cos_reduce0 qz408 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 3324967448413003055104) (@Nat.cast Real Real.instNatCast 4722366482869645213696)) 226375608064910080 72057594037927936 Bool.false 399612 524288 25 1000000000000000 148202 74101 (BSN.sin_reduce_arg_pos_rat_q0 5170257 32768 226375608064910080 72057594037927936 25 3324967448413003055104 4722366482869645213696 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 399612 524288 3324967448413003055104 4722366482869645213696 756010069 1073741824 148347 148202 (ep694 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep696 := BSN.sin_dyadic_bound_f 756010069 1073741824 2 1 524288 148347 ep693 ep79 ep693 ep693 ep80 ep693 339392 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 756010069) qz278 0 1 ep693 ep79 ep693 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 756010069) qz279 0 1 ep693 ep80 ep693 rfl rfl rfl rfl) rfl rfl

noncomputable def ep697 := @Enclosure.Real.IsNear.sin_image qz196 qz408 Bool.false 5170257 32768 233 262144 Bool.false 339392 524288 1 74101 (@Enclosure.Real.IsNear.recentre' qz196 Bool.false 710594713315357618957 4503599627370496000 65801000014627759703 74101000000000000000000 5170257 32768 233 262144 (ep692 rfl) rfl) (Enclosure.sfrac_false_div 5170257 32768) (BSN.sin_reduce0 qz408 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 3324967448413003055104) (@Nat.cast Real Real.instNatCast 4722366482869645213696)) 226375608064910080 72057594037927936 Bool.false 339392 524288 25 1000000000000000 148202 74101 (BSN.sin_reduce_arg_pos_rat_q0 5170257 32768 226375608064910080 72057594037927936 25 3324967448413003055104 4722366482869645213696 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 339392 524288 3324967448413003055104 4722366482869645213696 756010069 1073741824 148347 148202 (ep696 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep698 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz115 (Real.cos qz196)) (@HMul.hMul Real Real Real qz0 qz115 (@Neg.neg Real Real.instNeg (Real.sin qz196))) Bool.false 15792566337 68719476736 1392790502283 5092181945614336 Bool.true 838292937 4294967296 86979681983 318261371600896 (@Enclosure.Real.IsNear.mulLit_ff qz115 (Real.cos qz196) 158079 524288 1 524288 99903 131072 17527677 19425132544 15792566337 68719476736 1392790502283 5092181945614336 qz360 (@Enclosure.Real.IsNear.recentre' (Real.cos qz196) Bool.false 399612 524288 17527677 19425132544 99903 131072 17527677 19425132544 (ep695 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz115 (@Neg.neg Real Real.instNeg (Real.sin qz196)) 158079 524288 1 524288 5303 8192 17527677 19425132544 838292937 4294967296 86979681983 318261371600896 qz360 (@Enclosure.Real.IsNear.neg (Real.sin qz196) Bool.false 5303 8192 17527677 19425132544 (@Enclosure.Real.IsNear.recentre' (Real.sin qz196) Bool.false 339392 524288 17527677 19425132544 5303 8192 17527677 19425132544 (ep697 rfl rfl) rfl)) rfl)

noncomputable def ep699 := @ep666 15792566337 68719476736 1392790502283 5092181945614336 Bool.true 838292937 4294967296 86979681983 318261371600896 Bool.false 7407293059189790736384 107790300669 137438953472 39907471736067 10184363891228672 Bool.true 122644189007400927232 28555325467 137438953472 9975867070335 2546090972807168 (ep667 (BSN.head_sum_c_succ qz136 10 11 rfl rfl) (ep690 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep691 ep698) rfl rfl

noncomputable abbrev qz197 := (@HMul.hMul Real Real Real qz263 qz376 (Real.log (Enclosure.sfrac Bool.false 12 1)))

noncomputable def ep700 := @Enclosure.Complex.IsNear.of_eq qz190 (Complex.mk (@HMul.hMul Real Real Real qz0 qz118 (Real.cos qz197)) (@HMul.hMul Real Real Real qz0 qz118 (@Neg.neg Real Real.instNeg (Real.sin qz197)))) Bool.false 39250395613 137438953472 1338819319081 5092181945614336 Bool.true 11580166037 274877906944 5322512704063 20368727782457344 (BSN.cpow_neg_s_mk qz145 65801 1000 12 qz146 rfl)

noncomputable def ep701 := @Enclosure.Real.IsNear.mulLit_ff qz145 qz120 65801 1000 0 1 11191020447815397 4503599627370496 1000000000222303 74101000000000000000 736380336486700937997 4503599627370496000 65801000014627759703 74101000000000000000000 qz147 (BSN.isNear_log_sfrac 12 1 11191020447815397 4503599627370496 1000000000222303 74101000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz362) Bool.false 23469270914176955449344 9444732965739290427392 1000000000222303 74101000000000000000 11191020447815397 4503599627370496 1000000000222303 74101000000000000000 (BSN.log_rat_reduce_isNear 12 1 3 24 16 106290 262144 24973259072661432 36028797018963968 74101 1000000000000000 rfl rfl rfl rfl (ep362 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep702 := nat_lit 611632555987304172008443464450625

noncomputable def ep703 := BSN.cos_dyadic_bound_f 157261585 1073741824 2 1 524288 148347 ep702 ep75 ep702 ep702 ep76 ep702 518674 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 157261585) qz283 0 1 ep702 ep75 ep702 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 157261585) qz284 0 1 ep702 ep76 ep702 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz409 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 85725953) qz20)

noncomputable def ep704 := @Enclosure.Real.IsNear.cos_image qz197 qz409 Bool.false 85725953 524288 467 524288 Bool.false 518674 524288 1 74101 (@Enclosure.Real.IsNear.recentre' qz197 Bool.false 736380336486700937997 4503599627370496000 65801000014627759703 74101000000000000000000 85725953 524288 467 524288 (ep701 rfl) rfl) (Enclosure.sfrac_false_div 85725953 524288) (BSN.cos_reduce0 qz409 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 11066300258881011449856) qz23) 226375608064910080 72057594037927936 Bool.false 518674 524288 26 1000000000000000 148202 74101 (BSN.sin_reduce_arg_pos_rat_q0 85725953 524288 226375608064910080 72057594037927936 26 11066300258881011449856 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 518674 524288 11066300258881011449856 75557863725914323419136 157261585 1073741824 148347 148202 (ep703 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep705 := BSN.sin_dyadic_bound_f 157261585 1073741824 1 0 524288 148347 0 1 1 0 1 1 76513 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 157261585) qz278 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 157261585) qz279 0 0 rfl) rfl rfl

noncomputable def ep706 := @Enclosure.Real.IsNear.sin_image qz197 qz409 Bool.false 85725953 524288 467 524288 Bool.false 76513 524288 1 74101 (@Enclosure.Real.IsNear.recentre' qz197 Bool.false 736380336486700937997 4503599627370496000 65801000014627759703 74101000000000000000000 85725953 524288 467 524288 (ep701 rfl) rfl) (Enclosure.sfrac_false_div 85725953 524288) (BSN.sin_reduce0 qz409 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 11066300258881011449856) qz23) 226375608064910080 72057594037927936 Bool.false 76513 524288 26 1000000000000000 148202 74101 (BSN.sin_reduce_arg_pos_rat_q0 85725953 524288 226375608064910080 72057594037927936 26 11066300258881011449856 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 76513 524288 11066300258881011449856 75557863725914323419136 157261585 1073741824 148347 148202 (ep705 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep707 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz118 (Real.cos qz197)) (@HMul.hMul Real Real Real qz0 qz118 (@Neg.neg Real Real.instNeg (Real.sin qz197))) Bool.false 39250395613 137438953472 1338819319081 5092181945614336 Bool.true 11580166037 274877906944 5322512704063 20368727782457344 (@Enclosure.Real.IsNear.mulLit_ff qz118 (Real.cos qz197) 151349 524288 1 524288 259337 262144 35129455 38850265088 39250395613 137438953472 1338819319081 5092181945614336 qz364 (@Enclosure.Real.IsNear.recentre' (Real.cos qz197) Bool.false 518674 524288 35129455 38850265088 259337 262144 35129455 38850265088 (ep704 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz118 (@Neg.neg Real Real.instNeg (Real.sin qz197)) 151349 524288 1 524288 76513 524288 35129455 38850265088 11580166037 274877906944 5322512704063 20368727782457344 qz364 (@Enclosure.Real.IsNear.neg (Real.sin qz197) Bool.false 76513 524288 35129455 38850265088 (@Enclosure.Real.IsNear.recentre' (Real.sin qz197) Bool.false 76513 524288 35129455 38850265088 76513 524288 35129455 38850265088 (ep706 rfl rfl) rfl)) rfl)

noncomputable def ep708 := @ep664 39250395613 137438953472 1338819319081 5092181945614336 Bool.true 11580166037 274877906944 5322512704063 20368727782457344 Bool.false 20209119414792281391104 73520348141 68719476736 42585110374229 10184363891228672 Bool.true 9440793997630936973312 68690816971 274877906944 85129449266743 20368727782457344 (ep665 (BSN.head_sum_c_succ qz136 11 12 rfl rfl) (ep699 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep700 ep707) rfl rfl

noncomputable abbrev qz198 := (@HMul.hMul Real Real Real qz263 qz376 qz368)

noncomputable def ep709 := @Enclosure.Complex.IsNear.of_eq qz189 (Complex.mk (@HMul.hMul Real Real Real qz0 qz123 (Real.cos qz198)) (@HMul.hMul Real Real Real qz0 qz123 (@Neg.neg Real Real.instNeg (Real.sin qz198)))) Bool.false 24579548385 137438953472 2561260230459 10184363891228672 Bool.false 58270695441 274877906944 5127163703679 20368727782457344 (BSN.cpow_neg_s_mk qz145 65801 1000 13 qz146 rfl)

noncomputable def ep710 := @Enclosure.Real.IsNear.mulLit_ff qz145 qz126 65801 1000 0 1 11551488463034085 4503599627370496 1000000000222303 74101000000000000000 152019898471221165417 900719925474099200 65801000014627759703 74101000000000000000000 qz147 (BSN.isNear_log_sfrac 13 1 11551488463034085 4503599627370496 1000000000222303 74101000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' qz369 Bool.false 24225227133228857425920 9444732965739290427392 1000000000222303 74101000000000000000 11551488463034085 4503599627370496 1000000000222303 74101000000000000000 (BSN.log_rat_reduce_isNear 13 1 3 26 16 127272 262144 24973259072661432 36028797018963968 74101 1000000000000000 rfl rfl rfl rfl (ep383 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep711 := nat_lit 320580692103024186349949581742668816

noncomputable def ep712 := BSN.sin_dyadic_bound_f 752461598 1073741824 2 1 524288 148347 ep711 ep79 ep711 ep711 ep80 ep711 338070 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 752461598) qz278 0 1 ep711 ep79 ep711 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 752461598) qz279 0 1 ep711 ep80 ep711 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz410 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 88487227) qz20)

noncomputable def ep713 := @Enclosure.Real.IsNear.cos_image qz198 qz410 Bool.false 88487227 524288 233 262144 Bool.false 338070 524288 1 74101 (@Enclosure.Real.IsNear.recentre' qz198 Bool.false 152019898471221165417 900719925474099200 65801000014627759703 74101000000000000000000 88487227 524288 233 262144 (ep710 rfl) rfl) (Enclosure.sfrac_false_div 88487227 524288) (BSN.cos_reduce3 qz410 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 52949777694445130481664) qz23) 226375608064910080 72057594037927936 Bool.false 338070 524288 26 1000000000000000 148202 74101 (BSN.sin_reduce_arg_pos_rat_q3 88487227 524288 226375608064910080 72057594037927936 26 52949777694445130481664 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 338070 524288 52949777694445130481664 75557863725914323419136 752461598 1073741824 148347 148202 (ep712 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep714 := BSN.cos_dyadic_bound_f 752461598 1073741824 2 1 524288 148347 ep711 ep75 ep711 ep711 ep76 ep711 400731 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 752461598) qz283 0 1 ep711 ep75 ep711 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 752461598) qz284 0 1 ep711 ep76 ep711 rfl rfl rfl rfl) rfl rfl

noncomputable def ep715 := @Enclosure.Real.IsNear.sin_image qz198 qz410 Bool.false 88487227 524288 233 262144 Bool.true 400731 524288 1 74101 (@Enclosure.Real.IsNear.recentre' qz198 Bool.false 152019898471221165417 900719925474099200 65801000014627759703 74101000000000000000000 88487227 524288 233 262144 (ep710 rfl) rfl) (Enclosure.sfrac_false_div 88487227 524288) (BSN.sin_reduce3 qz410 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 52949777694445130481664) qz23) 226375608064910080 72057594037927936 Bool.false 400731 524288 26 1000000000000000 148202 74101 (BSN.sin_reduce_arg_pos_rat_q3 88487227 524288 226375608064910080 72057594037927936 26 52949777694445130481664 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 400731 524288 52949777694445130481664 75557863725914323419136 752461598 1073741824 148347 148202 (ep714 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep716 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz123 (Real.cos qz198)) (@HMul.hMul Real Real Real qz0 qz123 (@Neg.neg Real Real.instNeg (Real.sin qz198))) Bool.false 24579548385 137438953472 2561260230459 10184363891228672 Bool.false 58270695441 274877906944 5127163703679 20368727782457344 (@Enclosure.Real.IsNear.mulLit_ff qz123 (Real.cos qz198) 145411 524288 1 524288 169035 262144 17527677 19425132544 24579548385 137438953472 2561260230459 10184363891228672 qz371 (@Enclosure.Real.IsNear.recentre' (Real.cos qz198) Bool.false 338070 524288 17527677 19425132544 169035 262144 17527677 19425132544 (ep713 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz123 (@Neg.neg Real Real.instNeg (Real.sin qz198)) 145411 524288 1 524288 400731 524288 17527677 19425132544 58270695441 274877906944 5127163703679 20368727782457344 qz371 (@Enclosure.Real.IsNear.neg (Real.sin qz198) Bool.true 400731 524288 17527677 19425132544 (@Enclosure.Real.IsNear.recentre' (Real.sin qz198) Bool.true 400731 524288 17527677 19425132544 400731 524288 17527677 19425132544 (ep715 rfl rfl) rfl)) rfl)

noncomputable def ep717 := @ep662 24579548385 137438953472 2561260230459 10184363891228672 Bool.false 58270695441 274877906944 5127163703679 20368727782457344 Bool.false 11793653410820534566912 171620244667 137438953472 2821648162793 636522743201792 Bool.true 2864261196268510904320 5210060765 137438953472 45128306485211 10184363891228672 (ep663 (BSN.head_sum_c_succ qz136 12 13 rfl rfl) (ep708 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep709 ep716) rfl rfl

noncomputable def ep718 := @Enclosure.Complex.IsNear.mul qz186 (@HAdd.hAdd Complex Complex Complex qz5 qz187 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz136 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz103 qz188 (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz54 2 k) 1))))) Bool.true 1174259765461511605113459 ep543 ep655 ep545 Bool.false

noncomputable abbrev qz199 := (Complex.re qz404)

noncomputable abbrev qz200 := (Complex.im qz404)

noncomputable def ep719 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 qz199 (Complex.re (@HAdd.hAdd Complex Complex Complex qz5 qz187 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz136 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz103 qz188 (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz54 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz200 (Complex.im (@HAdd.hAdd Complex Complex Complex qz5 qz187 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz136 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz103 qz188 (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz54 2 k) 1))))))) 181077250731066194145 2082897730734078820352 900331071552885970504753

noncomputable def ep720 := nat_lit 7408550627766046784011370496

noncomputable def ep721 := nat_lit 2425346334836463023154213

noncomputable def ep722 := nat_lit 66652727383490522251264000

noncomputable def ep723 := nat_lit 91882363022243128521063121

noncomputable def ep724 := nat_lit 2116728750790299081146105856000

noncomputable def ep725 := nat_lit 17121041005404799036533979428419612236868222976

noncomputable def ep726 := @Enclosure.Real.IsNear.mulLit_tf qz199 (Complex.re (@HAdd.hAdd Complex Complex Complex qz5 qz187 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz136 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz103 qz188 (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))))) 744743115 4294967296 1234308127337 5092181945614336 729421650569

noncomputable abbrev qz411 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) qz465 (Real.log (Enclosure.sfrac Bool.false 14 1)))

noncomputable abbrev qz201 := (Real.cos qz411)

noncomputable abbrev qz202 := (@Neg.neg Real Real.instNeg (Real.sin qz411))

noncomputable abbrev qz412 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 14)))

noncomputable def ep727 := @Enclosure.Complex.IsNear.of_eq qz186 (Complex.mk (@HMul.hMul Real Real Real qz0 qz412 qz201) (@HMul.hMul Real Real Real qz0 qz412 qz202)) Bool.true 744743115 4294967296 1234308127337 5092181945614336 Bool.false 55902534039 274877906944 4941589574047 20368727782457344 (BSN.cpow_neg_s_mk qz145 65801 1000 14 qz146 rfl)

noncomputable abbrev qz413 := (Real.sqrt (@Nat.cast Real Real.instNatCast 14))

noncomputable abbrev qz414 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 14) qz19)

noncomputable def ep728 := @Enclosure.Real.IsNear.inv_image qz413 1961707 524288 1 524288 70060 70061 262144 (@Enclosure.Real.IsNear.of_eq qz413 (Real.sqrt qz414) Bool.false 1961707 524288 1 524288 (BSN.sqrt_natCast_div_one 14) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz414) Bool.false 1961707 524288 1 524288 1961707 524288 1 524288 (BSN.sqrt_enclosure 14 1 980853 980854 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep729 := BSN.log_dyadic_bound 6 22 5 4 51857700491520 262144 74101 1346332575744 176359680 146699 28 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 6) (BSN.artanhQ 22) 0 4 1346332575744 51857700491520 176359680 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz415 := (Real.log (Enclosure.sfrac Bool.false 14 1))

noncomputable abbrev qz203 := qz415

noncomputable def ep730 := @Enclosure.Real.IsNear.mulLit_ff qz145 qz203 65801 1000 0 1 11885241781671653 4503599627370496 1000000000222303 74101000000000000000 782060794475776439053 4503599627370496000 65801000014627759703 74101000000000000000000 qz147 (BSN.isNear_log_sfrac 14 1 11885241781671653 4503599627370496 1000000000222303 74101000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz414) Bool.false 24925158572916270432256 9444732965739290427392 1000000000222303 74101000000000000000 11885241781671653 4503599627370496 1000000000222303 74101000000000000000 (BSN.log_rat_reduce_isNear 14 1 3 28 16 146699 262144 24973259072661432 36028797018963968 74101 1000000000000000 rfl rfl rfl rfl (ep729 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep731 := nat_lit 1660670468262233438914357688399277016640366726293046926151032716881187594496

noncomputable def ep732 := nat_lit 552662875502827299528359624775987650409451848705221175954181458876457216

noncomputable def ep733 := nat_lit 4980906079035694662144016345948279074620281275181730336101189787725809869056

noncomputable def ep734 := BSN.cos_dyadic_bound_f 928554794 1073741824 3 2 524288 148347 ep731 ep64 ep732 ep733 ep66 ep732 340160 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 928554794) qz283 0 2 ep731 ep64 ep732 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 928554794) qz284 0 2 ep733 ep66 ep732 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz204 := qz411

noncomputable abbrev qz416 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 91043859) qz20)

noncomputable def ep735 := @Enclosure.Real.IsNear.cos_image qz204 qz416 Bool.false 91043859 524288 233 262144 Bool.true 340160 524288 1 74101 (@Enclosure.Real.IsNear.recentre' qz204 Bool.false 782060794475776439053 4503599627370496000 65801000014627759703 74101000000000000000000 91043859 524288 233 262144 (ep730 rfl) rfl) (Enclosure.sfrac_false_div 91043859 524288) (BSN.cos_reduce2 qz416 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 65341234811789952155648) qz23) 226375608064910080 72057594037927936 Bool.false 340160 524288 27 1000000000000000 148202 74101 (BSN.sin_reduce_arg_pos_rat_q2 91043859 524288 226375608064910080 72057594037927936 27 65341234811789952155648 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 340160 524288 65341234811789952155648 75557863725914323419136 928554794 1073741824 148347 148202 (ep734 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep736 := nat_lit 743412991212036393162384347377294096

noncomputable def ep737 := BSN.sin_dyadic_bound_f 928554794 1073741824 2 1 524288 148347 ep736 ep79 ep736 ep736 ep80 ep736 398959 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 928554794) qz278 0 1 ep736 ep79 ep736 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 928554794) qz279 0 1 ep736 ep80 ep736 rfl rfl rfl rfl) rfl rfl

noncomputable def ep738 := @Enclosure.Real.IsNear.sin_image qz204 qz416 Bool.false 91043859 524288 233 262144 Bool.true 398959 524288 1 74101 (@Enclosure.Real.IsNear.recentre' qz204 Bool.false 782060794475776439053 4503599627370496000 65801000014627759703 74101000000000000000000 91043859 524288 233 262144 (ep730 rfl) rfl) (Enclosure.sfrac_false_div 91043859 524288) (BSN.sin_reduce2 qz416 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 65341234811789952155648) qz23) 226375608064910080 72057594037927936 Bool.false 398959 524288 27 1000000000000000 148202 74101 (BSN.sin_reduce_arg_pos_rat_q2 91043859 524288 226375608064910080 72057594037927936 27 65341234811789952155648 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 398959 524288 65341234811789952155648 75557863725914323419136 928554794 1073741824 148347 148202 (ep737 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz205 := (Real.sin qz411)

noncomputable def ep739 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz412 qz201) (@HMul.hMul Real Real Real qz0 qz412 qz202) Bool.true 744743115 4294967296 1234308127337 5092181945614336 Bool.false 55902534039 274877906944 4941589574047 20368727782457344 (@Enclosure.Real.IsNear.mulLit_ft qz412 qz201 140121 524288 1 524288 5315 8192 17527677 19425132544 744743115 4294967296 1234308127337 5092181945614336 (@Enclosure.Real.IsNear.recentre' qz412 Bool.false 140121 524288 1 524288 140121 524288 1 524288 (ep728 rfl rfl) rfl) (@Enclosure.Real.IsNear.recentre' qz201 Bool.true 340160 524288 17527677 19425132544 5315 8192 17527677 19425132544 (ep735 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz412 qz202 140121 524288 1 524288 398959 524288 17527677 19425132544 55902534039 274877906944 4941589574047 20368727782457344 (@Enclosure.Real.IsNear.recentre' qz412 Bool.false 140121 524288 1 524288 140121 524288 1 524288 (ep728 rfl rfl) rfl) (@Enclosure.Real.IsNear.neg qz205 Bool.true 398959 524288 17527677 19425132544 (@Enclosure.Real.IsNear.recentre' qz205 Bool.true 398959 524288 17527677 19425132544 398959 524288 17527677 19425132544 (ep738 rfl rfl) rfl)) rfl)

noncomputable def ep740 := @ep726 1454887257936 0 1 181077250731066194145 2082897730734078820352 900331071552885970504753 ep720 (@Enclosure.Complex.IsNear.re_isNear qz186 Bool.true 744743115 4294967296 1234308127337 5092181945614336 Bool.false 55902534039 274877906944 4941589574047 20368727782457344 (ep727 ep739))

noncomputable def ep741 := @Enclosure.Complex.IsNear.re_isNear (@HAdd.hAdd Complex Complex Complex qz5 qz187 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz136 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz103 qz188 (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz54 2 k) 1))))) Bool.false 729421650569 1454887257936 0 1 Bool.false

noncomputable def ep742 := @Enclosure.Complex.IsNear.addLitP qz187 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz136 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz103 qz188 (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) Bool.false 4316021601 8660043202 0 1 Bool.true 921214000

noncomputable def ep743 := @ep742 4330021601 0 1 Bool.false 1 336 0 1 Bool.false 65801 168000 0 1 Bool.false 1458843301138 729421650569 1454887257936 0 1 Bool.false 130155799367401 130155799367401 727443628968000 0 1

noncomputable abbrev qz206 := (@HDiv.hDiv Complex Complex Complex qz320 qz405 (@HSub.hSub Complex Complex Complex qz313 qz374 (1 : Complex)))

noncomputable def ep744 := @Enclosure.Complex.IsNear.addLitP qz206 qz75 Bool.true 28000000 17320086404 0 1 Bool.true 3684856000 17320086404 0 1

noncomputable def ep745 := @Enclosure.Complex.IsNear.of_eq qz206 (Complex.mk (Enclosure.sfrac Bool.true 28000000 17320086404) (Enclosure.sfrac Bool.true 3684856000 17320086404)) Bool.true 28000000 17320086404 0 1 Bool.true 3684856000 17320086404 0 1

noncomputable def ep746 := @ep744 Bool.false 1 2 0 1 Bool.false 0 1 0 1 Bool.false 17264086404 4316021601 8660043202 0 1 Bool.true 3684856000 921214000 4330021601 0 1 (ep745 (BSN.N_div_s_sub_one_mk qz145 65801 1000 14 qz146 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 28000000 17320086404) (Enclosure.sfrac Bool.true 3684856000 17320086404) Bool.true 28000000 17320086404 0 1 Bool.true 3684856000 17320086404 0 1 (Enclosure.Real.IsNear.const Bool.true 28000000 17320086404) (Enclosure.Real.IsNear.const Bool.true 3684856000 17320086404))) qz76 rfl

noncomputable abbrev qz417 := (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz461 qz468 1))

noncomputable abbrev qz207 := qz417

noncomputable def ep747 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz136 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz103 qz188 (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@HAdd.hAdd Complex Complex Complex qz5 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz136 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz103 qz188 (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz130) (@Polynomial.eval Complex Complex.instSemiring qz136 (@ascPochhammer Complex Complex.instSemiring 1))) qz207)) Bool.false 1 336 0 1

noncomputable def ep748 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz136 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz103 qz188 (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz130) (@Polynomial.eval Complex Complex.instSemiring qz136 (@ascPochhammer Complex Complex.instSemiring 1))) qz207) Bool.false 0 1 0 1 Bool.false

noncomputable def ep749 := @ep748 0 1 0 1 Bool.false 1 336 0 1 Bool.false 65801 168000 0 1 Bool.false 1 1 336 0 1 Bool.false 65801 65801 168000 0

noncomputable def ep750 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz136 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz103 qz188 (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (Complex.mk qz14 qz14) Bool.false 0 1 0 1 Bool.false

noncomputable def ep751 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz130) (@Polynomial.eval Complex Complex.instSemiring qz136 (@ascPochhammer Complex Complex.instSemiring 1))) qz207 Bool.false 1 336 0 1 Bool.false 65801 168000 0 1

noncomputable abbrev qz208 := (Complex.re qz417)

noncomputable def ep752 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz130) (@Polynomial.eval Complex Complex.instSemiring qz136 (@ascPochhammer Complex Complex.instSemiring 1)))) qz208) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz130) (@Polynomial.eval Complex Complex.instSemiring qz136 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz207)) 1 336 0 1 0 1 0

noncomputable def ep753 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz130) (@Polynomial.eval Complex Complex.instSemiring qz136 (@ascPochhammer Complex Complex.instSemiring 1)))) qz208 1 24 0 1 1 14 0 1 1

noncomputable def ep754 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz130)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz136 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz130)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz136 (@ascPochhammer Complex Complex.instSemiring 1)))) 1 24 0 1 0 1 0 1 1

noncomputable def ep755 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz130)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz136 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 1 2 0 1 1 24 0

noncomputable def ep756 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz136 (@ascPochhammer Complex Complex.instSemiring 1)) qz136 Bool.false 1 2 0 1 Bool.false 65801 1000 0 1 (BSN.ascPochhammer_one_eval qz136)

noncomputable def ep757 := ep756 (@Enclosure.Complex.IsNear.of_eq qz136 (Complex.mk qz70 qz145) Bool.false 1 2 0 1 Bool.false 65801 1000 0 1 (BSN.s_crit_mk qz145 Bool.false 65801 1000 qz146) (@Enclosure.Complex.IsNear.mk qz70 qz145 Bool.false 1 2 0 1 Bool.false 65801 1000 0 1 qz329 qz147))

noncomputable def ep758 := @ep755 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz130) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep406) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz136 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 65801 1000 0 1 ep757)

noncomputable def ep759 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz130)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz136 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 65801 1000 0 1 0 1 0

noncomputable def ep760 := @ep759 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz130) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep406) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz136 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 65801 1000 0 1 ep757)

noncomputable def ep761 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz130)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz136 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz130)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz136 (@ascPochhammer Complex Complex.instSemiring 1)))) 65801 12000 0 1 0 1 0 1 65801

noncomputable def ep762 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz130)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz136 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 65801 1000 0 1 65801 12000 0

noncomputable def ep763 := @ep762 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz130) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep406) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz136 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 65801 1000 0 1 ep757)

noncomputable def ep764 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz130)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz136 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 1 2 0 1 0 1 0

noncomputable def ep765 := @ep764 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz130) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep406) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz136 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 65801 1000 0 1 ep757)

noncomputable def ep766 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz130) (@Polynomial.eval Complex Complex.instSemiring qz136 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 24 0 1 Bool.false 65801 12000 0 1 (@ep754 1 24 0 1 (ep758 rfl) (ep760 rfl) rfl rfl) (@ep761 65801 12000 0 1 (ep763 rfl) (ep765 rfl) rfl rfl)

noncomputable def ep767 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz130) (@Polynomial.eval Complex Complex.instSemiring qz136 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 65801 12000 0 1 ep766

noncomputable abbrev qz209 := (@Enclosure.Complex.IsNear.of_eq qz417 (Complex.mk (Enclosure.sfrac Bool.false 1 14) qz274) Bool.false 1 14 0 1 Bool.false 0 1 0 1 (BSN.natCast_pow_inv_mk 14 1 14 EMRow15.d11 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 14) qz274 Bool.false 1 14 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 14) qz286))

noncomputable def ep768 := @ep753 336 0 1 ep767 (@Enclosure.Complex.IsNear.re_isNear qz207 Bool.false 1 14 0 1 Bool.false 0 1 0 1 qz209)

noncomputable def ep769 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz130) (@Polynomial.eval Complex Complex.instSemiring qz136 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz207) 65801 12000 0 1 0 1 0 1 0

noncomputable def ep770 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz130) (@Polynomial.eval Complex Complex.instSemiring qz136 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 65801 12000 0 1 ep766

noncomputable def ep771 := @ep769 1 0 1 ep770 (@Enclosure.Complex.IsNear.im_isNear qz207 Bool.false 1 14 0 1 Bool.false 0 1 0 1 qz209)

noncomputable def ep772 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz130) (@Polynomial.eval Complex Complex.instSemiring qz136 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz207)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz130) (@Polynomial.eval Complex Complex.instSemiring qz136 (@ascPochhammer Complex Complex.instSemiring 1)))) qz208) 0 1 0 1 65801 168000 0

noncomputable def ep773 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz130) (@Polynomial.eval Complex Complex.instSemiring qz136 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz207) 1 24 0 1 0 1 0 1 0

noncomputable def ep774 := @ep773 1 0 1 ep767 (@Enclosure.Complex.IsNear.im_isNear qz207 Bool.false 1 14 0 1 Bool.false 0 1 0 1 qz209)

noncomputable def ep775 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz130) (@Polynomial.eval Complex Complex.instSemiring qz136 (@ascPochhammer Complex Complex.instSemiring 1)))) qz208 65801 12000 0 1 1 14 0 1 65801

noncomputable def ep776 := @ep775 168000 0 1 ep770 (@Enclosure.Complex.IsNear.re_isNear qz207 Bool.false 1 14 0 1 Bool.false 0 1 0 1 qz209)

noncomputable def ep777 := @ep749 1 (@ep750 0 1 0 1 (BSN.bern_sum_base qz136 14) qz92) (ep751 (@ep752 1 1 1 336 0 1 (ep768 rfl) (ep771 rfl) rfl rfl) (@ep772 1 65801 65801 168000 0 1 (ep774 rfl) (ep776 rfl) rfl rfl)) rfl rfl rfl rfl rfl

noncomputable def ep778 := ep743 (ep746 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep747 Bool.false 65801 168000 0 1 (BSN.bern_sum_succ qz136 14 0 1 1 rfl rfl) (ep777 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl rfl

noncomputable def ep779 := @Enclosure.Real.IsNear.mulLit_ff qz200 (Complex.im (@HAdd.hAdd Complex Complex Complex qz5 qz187 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz136 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz103 qz188 (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))))) 55902534039 274877906944 4941589574047 20368727782457344 130155799367401

noncomputable def ep780 := @ep779 727443628968000 0 1 ep721 ep722 ep723 ep724 (@Enclosure.Complex.IsNear.im_isNear qz186 Bool.true 744743115 4294967296 1234308127337 5092181945614336 Bool.false 55902534039 274877906944 4941589574047 20368727782457344 (ep727 ep739))

noncomputable def ep781 := @Enclosure.Complex.IsNear.im_isNear (@HAdd.hAdd Complex Complex Complex qz5 qz187 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz136 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz103 qz188 (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz54 2 k) 1))))) Bool.false 729421650569 1454887257936 0 1 Bool.false

noncomputable def ep782 := nat_lit 160652360979227017554741137

noncomputable def ep783 := @Enclosure.Real.IsNear.addLit_tf_p (@HMul.hMul Real Real Real qz0 qz199 (Complex.im (@HAdd.hAdd Complex Complex Complex qz5 qz187 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz136 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz103 qz188 (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz54 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz200 (Complex.re (@HAdd.hAdd Complex Complex Complex qz5 qz187 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz136 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz103 qz188 (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz54 2 k) 1))))))) 6462175697079550012941 208289773073407882035200 ep782

noncomputable def ep784 := nat_lit 3704275313883023392005685248000

noncomputable def ep785 := nat_lit 4233457501580598162292211712

noncomputable def ep786 := nat_lit 1969667335341063269988601042975583739473559552

noncomputable def ep787 := @Enclosure.Real.IsNear.mulLit_tf qz199 (Complex.im (@HAdd.hAdd Complex Complex Complex qz5 qz187 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz136 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz103 qz188 (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))))) 744743115 4294967296 1234308127337 5092181945614336 130155799367401

noncomputable def ep788 := @ep787 727443628968000 0 1 6462175697079550012941 208289773073407882035200 ep782 ep784 (@Enclosure.Complex.IsNear.re_isNear qz186 Bool.true 744743115 4294967296 1234308127337 5092181945614336 Bool.false 55902534039 274877906944 4941589574047 20368727782457344 (ep727 ep739))

noncomputable def ep789 := @Enclosure.Real.IsNear.mulLit_ff qz200 (Complex.re (@HAdd.hAdd Complex Complex Complex qz5 qz187 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz136 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz103 qz188 (@HSub.hSub Nat Nat Nat qz102 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))))) 55902534039 274877906944 4941589574047 20368727782457344 729421650569

noncomputable def ep790 := @ep789 1454887257936 0 1 13592172883239028739397 133305454766981044502528 514928917647989197883249 ep785 (@Enclosure.Complex.IsNear.im_isNear qz186 Bool.true 744743115 4294967296 1234308127337 5092181945614336 Bool.false 55902534039 274877906944 4941589574047 20368727782457344 (ep727 ep739))

noncomputable abbrev qz418 := (ep778 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable def ep791 := @ep718 236409510927702918277869 ep650 ep656 ep652 (@ep719 ep720 ep721 ep722 ep723 ep724 ep725 1174259765461511605113459 ep543 ep655 ep545 (ep740 (@ep741 130155799367401 727443628968000 0 1 qz418) rfl) (ep780 (@ep781 130155799367401 727443628968000 0 1 qz418) rfl) rfl rfl) (@ep783 ep784 13592172883239028739397 133305454766981044502528 514928917647989197883249 ep785 ep786 236409510927702918277869 ep650 ep656 ep652 (ep788 (@ep781 130155799367401 727443628968000 0 1 qz418) rfl) (ep790 (@ep741 130155799367401 727443628968000 0 1 qz418) rfl) rfl rfl)

noncomputable def ep792 := @ep659 ep651 ep652 (@ep660 10184363891228672 (BSN.head_sum_c_eq qz136 14) (ep661 (BSN.head_sum_c_succ qz136 13 14 rfl rfl) (ep717 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))) ep791 rfl rfl rfl

noncomputable def ep793 := @Enclosure.Complex.IsNear.re_isNear (zetaApproximant qz136 1 14) Bool.false ep542 ep543 ep544 ep545 Bool.false 110075327259856443593869 ep650 ep651 ep652 (@ep653 ep545 Bool.false 110075327259856443593869 ep650 ep651 ep652 (BSN.zetaApproximant_eq_folded' qz136 1 14 rfl) (ep792 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

noncomputable def ep794 := @Enclosure.Real.IsNear.mulLit_ff (Real.sin (@HSub.hSub Real Real Real qz46 (Complex.im (@HSub.hSub Complex Complex Complex qz47 qz154 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz155 (@Nat.cast Complex Complex.instNatCast j))))) qz156)) (Complex.im (zetaApproximant qz136 1 14)) 33 262144 3910223

noncomputable def ep795 := @Enclosure.Real.IsNear.recentre' (Real.sin (@HSub.hSub Real Real Real qz46 (Complex.im (@HSub.hSub Complex Complex Complex qz47 qz154 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz155 (@Nat.cast Complex Complex.instNatCast j))))) qz156)) Bool.false 66 524288 3910223

noncomputable def ep796 := @Enclosure.Real.IsNear.sin_image (@HSub.hSub Real Real Real qz46 (Complex.im (@HSub.hSub Complex Complex Complex qz47 qz154 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz155 (@Nat.cast Complex Complex.instNatCast j))))) qz156) qz388 Bool.false 23059457 524288 51

noncomputable def ep797 := BSN.sin_dyadic_bound_f 135970 1073741824 1 0 524288 148347 0 1 1 0 1 1 66 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 135970) qz278 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 135970) qz279 0 0 rfl) rfl rfl

noncomputable def ep798 := @ep796 131072 Bool.false 66 524288 1 74101 (@ep550 23059457 524288 51 131072 ep647 rfl) (Enclosure.sfrac_false_div 23059457 524288) (BSN.sin_reduce0 qz388 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 9568050315089936384) qz23) 226375608064910080 72057594037927936 Bool.false 66 524288 7 1000000000000000 148202 74101 (BSN.sin_reduce_arg_pos_rat_q0 23059457 524288 226375608064910080 72057594037927936 7 9568050315089936384 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 66 524288 9568050315089936384 75557863725914323419136 135970 1073741824 148347 148202 (ep797 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep799 := @Enclosure.Complex.IsNear.im_isNear (zetaApproximant qz136 1 14) Bool.false ep542 ep543 ep544 ep545 Bool.false 110075327259856443593869 ep650 ep651 ep652 (@ep653 ep545 Bool.false 110075327259856443593869 ep650 ep651 ep652 (BSN.zetaApproximant_eq_folded' qz136 1 14 rfl) (ep792 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

theorem EMRow15.d12 : Enclosure.Real.IsNear (hardyZApproximantEM 1 14 qz145) Bool.false ep525 ep526 ep527 ep528 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantEM 1 14 qz145) ep529 Bool.false ep525 ep526 ep527 ep528 (@Eq.refl Real ep529) (@ep530 Bool.false ep525 ep526 ep527 ep528 (BSN.re_exp_mul (@HSub.hSub Real Real Real qz46 (Complex.im (@HSub.hSub Complex Complex Complex qz47 qz154 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz155 (@Nat.cast Complex Complex.instNatCast j))))) qz156) (zetaApproximant qz136 1 14)) (@ep532 ep533 ep534 ep535 ep536 ep537 ep538 ep539 ep540 ep525 ep526 ep527 ep528 (@ep541 9712566272 ep542 ep543 ep544 ep545 ep531 ep533 ep534 ep535 (@ep546 9712566272 524287 524288 3910223 9712566272 (ep649 rfl rfl) rfl) ep793 rfl) (@ep794 9712566272 110075327259856443593869 ep650 ep651 ep652 ep536 ep537 ep538 ep539 (@ep795 9712566272 33 262144 3910223 9712566272 (ep798 rfl rfl) rfl) ep799 rfl) rfl rfl))

theorem EMRow15.d13 : @Eq Nat (Nat.mul (BSN.factNat (Nat.succ (Nat.mul 2 1))) (Nat.pow 4 (Nat.mul 2 1))) 96 := @Eq.refl Nat 96

theorem EMRow15.d14 : @Eq Nat (Nat.mul (Nat.mul 2 1) (Nat.pow (Nat.succ (Nat.mul 4 2)) (Nat.mul 2 1))) 162 := @Eq.refl Nat 162

theorem EMRow15.d15 : @Eq Nat (BSN.factNat (Nat.mul 2 2)) 24 := @Eq.refl Nat 24

theorem EMRow15.d16 : @Eq Nat (Nat.pow 13 (Nat.succ (Nat.mul 2 3))) 62748517 := @Eq.refl Nat 62748517

noncomputable abbrev qz469 := (@HAdd.hAdd Complex Complex Complex qz472 qz471 (@Nat.cast Complex Complex.instNatCast 3))

noncomputable abbrev qz419 := qz469

noncomputable abbrev qz210 := (@HDiv.hDiv Real Real Real qz266 (@Norm.norm Complex Complex.instNorm qz419) (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (Complex.re qz268) (@Nat.cast Real Real.instNatCast 3)))

noncomputable abbrev qz211 := (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 2)

noncomputable abbrev qz212 := (@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 2)))

noncomputable abbrev qz420 := (@HPow.hPow Complex Complex Complex qz449 qz462 (@HSub.hSub Complex Complex Complex qz455 qz450 qz451))

noncomputable abbrev qz213 := qz420

noncomputable def ep800 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz6 1 13))) (@HMul.hMul Real Real Real qz0 qz210 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz213))) 411316997 6442450944 7922335 115964116992 224157923888881 281474976710656 1571541483

noncomputable def ep801 := nat_lit 1559901870514273513373696

noncomputable def ep802 := @Enclosure.Real.IsNear.mulLit_ff (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz6 1 13)) 4427 294912 1 884736 278733 65536 1109 262144 411316997 6442450944

noncomputable abbrev qz421 := (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid)))

noncomputable abbrev qz214 := (@HPow.hPow Real Nat Real qz421 qz267 2)

noncomputable def ep803 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 96 162) (@Inv.inv Real Real.instInv qz214) 96 162 0 1 13281 524288 1 524288 4427 294912 1 884736

noncomputable def ep804 := nat_lit 781950621441006189802102638025

noncomputable def ep805 := nat_lit 19807040628566084398385987584

noncomputable def ep806 := nat_lit 26986075409044041160201671

noncomputable def ep807 := nat_lit 1073741824000000000000000000000000000000

noncomputable abbrev qz215 := qz267

noncomputable abbrev qz422 := (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) qz215 1)

noncomputable def ep808 := @Enclosure.Real.IsNear.mulLit_ff qz422 qz215 884279719003555 140737488355328 1 500000000000000 884279719003555 140737488355328 1 500000000000000 ep804 ep805 ep806 ep807

noncomputable def ep809 := ep808 (@Enclosure.Real.IsNear.of_eq qz422 qz215 Bool.false 884279719003555 140737488355328 1 500000000000000 (BSN.pow_one_r qz215) (@Enclosure.Real.IsNear.of_eq qz215 qz264 Bool.false 884279719003555 140737488355328 1 500000000000000 BSN.two_pi_eq qz265)) (@Enclosure.Real.IsNear.of_eq qz215 qz264 Bool.false 884279719003555 140737488355328 1 500000000000000 BSN.two_pi_eq qz265) rfl

noncomputable def ep810 := @Enclosure.Real.IsNear.inv_image qz214 ep804 ep805 ep806 ep807 6640 6641 262144 (@Enclosure.Real.IsNear.of_eq qz214 (@HMul.hMul Real Real Real qz0 qz422 qz215) Bool.false ep804 ep805 ep806 ep807 (BSN.pow_succ_r qz215 1 2 rfl) ep809) rfl rfl rfl

noncomputable def ep811 := ep803 (Enclosure.Real.IsNear.const Bool.false 96 162) (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz214) Bool.false 13281 524288 1 524288 13281 524288 1 524288 (ep810 rfl rfl rfl) rfl)

noncomputable def ep812 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (zetaApproximant qz6 1 13)) (Real.sqrt (@HAdd.hAdd Real Real Real qz87 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz6 1 13)) (Complex.re (zetaApproximant qz6 1 13))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz6 1 13)) (Complex.im (zetaApproximant qz6 1 13))))) Bool.false 278733 65536 1109 262144

noncomputable def ep813 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz87 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz6 1 13)) (Complex.re (zetaApproximant qz6 1 13))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz6 1 13)) (Complex.im (zetaApproximant qz6 1 13))))) Bool.false 2229864 524288 2218 524288

noncomputable def ep814 := nat_lit 2069567896852210533775829325648936641973353

noncomputable def ep815 := nat_lit 114409584394418608011753631783059456000000

noncomputable def ep816 := nat_lit 22494015514592732648000387705180840361647233030943021394047

noncomputable def ep817 := nat_lit 625408917158791084177103764945867364407446640584032256000000

noncomputable def ep818 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz87 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz6 1 13)) (Complex.re (zetaApproximant qz6 1 13))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz6 1 13)) (Complex.im (zetaApproximant qz6 1 13)))) ep814 ep815 ep816 ep817 1113823 1116041

noncomputable def ep819 := nat_lit 2060172135529731859626463754327666283485768910738889

noncomputable def ep820 := nat_lit 113897956288374791833004478728842424201773056000000

noncomputable def ep821 := nat_lit 22299311124055029158354335520672904626991687874724952635711

noncomputable def ep822 := nat_lit 35215678528292678895993483932551091820023488441

noncomputable def ep823 := nat_lit 28474489072093697958251119682210606050443264000000

noncomputable def ep824 := nat_lit 338028455794624113968840598104055094888099229545258261

noncomputable def ep825 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz6 1 13)) (Complex.re (zetaApproximant qz6 1 13))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz6 1 13)) (Complex.im (zetaApproximant qz6 1 13))) ep819 ep820 ep821 ep817 ep822 ep823 ep824

noncomputable def ep826 := nat_lit 1085779370067345632251916258586575285429594862125056000000

noncomputable def ep827 := nat_lit 58666359953586967629029837471323382050365474859313982145761789270602959341222791026366734139392000000

noncomputable def ep828 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (zetaApproximant qz6 1 13)) (Complex.re (zetaApproximant qz6 1 13)) ep174 ep175 ep176 ep177 ep174 ep175 ep176 ep177 ep819

noncomputable def ep829 := @Enclosure.Real.IsNear.mulLit_tt (Complex.im (zetaApproximant qz6 1 13)) (Complex.im (zetaApproximant qz6 1 13)) 187658409159548933057771 ep305 ep306 ep307 187658409159548933057771 ep305 ep306 ep307 ep822

noncomputable def ep830 := @ep800 1970324836974592 ep801 726385913097427 844424930131968 3676818645961 53198770598313984 (@ep802 7922335 115964116992 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaStirlingErrorBound 1 2) (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 96 162) (@Inv.inv Real Real.instInv qz214)) Bool.false 4427 294912 1 884736 (BSN.theta_err_eq 1 2 96 162 EMRow15.d13 EMRow15.d14 rfl) (ep811 rfl)) (ep812 (BSN.norm_eq_sqrt_mul_add (zetaApproximant qz6 1 13)) (@ep813 278733 65536 1109 262144 (@ep818 262144 (@ep825 ep826 ep827 ep814 ep815 ep816 ep817 (@ep828 ep820 ep821 ep817 ep443 ep443 rfl) (@ep829 ep823 ep824 ep826 ep449 ep449 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl)

noncomputable abbrev qz216 := (@Norm.norm Complex Complex.instNorm qz419)

noncomputable abbrev qz423 := (Enclosure.sfrac Bool.false 2 7)

noncomputable def ep831 := @Enclosure.Real.IsNear.of_eq (@HMul.hMul Real Real Real qz0 qz210 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz213))) (@HMul.hMul Real Real Real qz0 (@HMul.hMul Real Real Real qz0 qz216 qz423) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz213))) Bool.false 224157923888881 281474976710656 1571541483 1970324836974592 (BSN.zrb_shape_eq qz216 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz213)) qz17 3)

noncomputable def ep832 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz0 qz216 qz423) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz213)) 33134473 1835008 1 1835008 47355679 1073741824 23 536870912

noncomputable def ep833 := @Enclosure.Real.IsNear.mulLit_ff qz216 qz423 33134473 524288 1 524288 2 7 0 1 33134473 1835008

noncomputable abbrev qz424 := (Complex.re qz469)

noncomputable abbrev qz425 := (Complex.im qz469)

noncomputable abbrev qz217 := (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (@HMul.hMul Real Real Real qz263 qz424 qz424) (@HMul.hMul Real Real Real qz263 qz425 qz425))

noncomputable abbrev qz218 := qz419

noncomputable def ep834 := @Enclosure.Real.IsNear.of_eq qz216 (Real.sqrt qz217) Bool.false 33134473 524288 1 524288 (BSN.norm_eq_sqrt_mul_add qz218)

noncomputable def ep835 := @Enclosure.Real.IsNear.recentre' (Real.sqrt qz217) Bool.false 33134473 524288 1 524288 33134473

noncomputable def ep836 := @Enclosure.Real.IsNear.sqrt_image qz217 998528101 250000 0 1 16567236 16567237 262144

noncomputable abbrev qz219 := (@HMul.hMul Real Real Real qz263 qz424 qz424)

noncomputable abbrev qz220 := (@HMul.hMul Real Real Real qz263 qz425 qz425)

noncomputable def ep837 := @Enclosure.Real.IsNear.addLit_ff qz219 qz220 49 4 0 1 995465601 250000 0 1

noncomputable abbrev qz221 := qz424

noncomputable def ep838 := @Enclosure.Real.IsNear.mulLit_ff qz221 qz221 7 2 0 1 7 2 0 1 49 4

noncomputable def ep839 := @Enclosure.Complex.IsNear.of_eq qz218 (Complex.mk (Enclosure.sfrac Bool.false 7 2) qz17) Bool.false 7 2 0 1 Bool.false 63102 1000 0 1 (BSN.s_add_nat_mk qz17 Bool.false 63102 1000 3 qz18)

noncomputable abbrev qz222 := (ep839 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7 2) qz276 Bool.false 7 2 0 1 Bool.false 63102 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 7 2) qz280))

noncomputable def ep840 := @ep838 0 1 (@Enclosure.Complex.IsNear.re_isNear qz218 Bool.false 7 2 0 1 Bool.false 63102 1000 0 1 qz222)

noncomputable def ep841 := ep840 (@Enclosure.Complex.IsNear.re_isNear qz218 Bool.false 7 2 0 1 Bool.false 63102 1000 0 1 qz222)

noncomputable abbrev qz223 := qz425

noncomputable def ep842 := @Enclosure.Real.IsNear.mulLit_ff qz223 qz223 63102 1000 0 1 63102 1000 0 1 995465601 250000

noncomputable def ep843 := @ep842 0 1 (@Enclosure.Complex.IsNear.im_isNear qz218 Bool.false 7 2 0 1 Bool.false 63102 1000 0 1 qz222)

noncomputable def ep844 := ep843 (@Enclosure.Complex.IsNear.im_isNear qz218 Bool.false 7 2 0 1 Bool.false 63102 1000 0 1 qz222)

noncomputable def ep845 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz213)) (Real.sqrt (@HAdd.hAdd Real Real Real qz87 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz213)) (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz213))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz213)) (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz213))))) Bool.false 47355679 1073741824

noncomputable def ep846 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz87 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz213)) (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz213))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz213)) (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz213))))) Bool.false 378845432 8589934592

noncomputable def ep847 := nat_lit 953117257323385402574554603556085160828501870184019979057

noncomputable def ep848 := nat_lit 490006608366151387387259434701746224496640000000000000000000

noncomputable def ep849 := nat_lit 13755968347375313378059736294153718435150966843106591115910165733554281

noncomputable def ep850 := nat_lit 3658016355062317442399383768830011373296043936533512087142400000000000000000000

noncomputable def ep851 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz87 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz213)) (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz213))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz213)) (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz213)))) ep847 ep848 ep849 ep850

noncomputable def ep852 := nat_lit 1040479681419279916167449714714221004208724909176683132841

noncomputable def ep853 := nat_lit 544451787073501541541399371890829138329600000000000000000000

noncomputable def ep854 := nat_lit 80790486506373534392721526149228709445484993373886016082184623796593207

noncomputable def ep855 := nat_lit 21948098130373904654396302612980068239776263619201072522854400000000000000000000

noncomputable def ep856 := nat_lit 166855440460334780238498603132862570406494519250051595001

noncomputable def ep857 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz213)) (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz213))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz213)) (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz213))) ep852 ep853 ep854 ep855 ep856

noncomputable def ep858 := nat_lit 4900066083661513873872594347017462244966400000000000000000000

noncomputable def ep859 := nat_lit 1745323577878345875636891615693601165420807684753530613276370604732479

noncomputable def ep860 := nat_lit 5189263940403116070044101015145128769001852794041395768245506740919606536063856088777783479631872000000000000000000000

noncomputable def ep861 := nat_lit 32256467280520350190177102221

noncomputable def ep862 := nat_lit 737869762948382064640000000000

noncomputable def ep863 := nat_lit 197239768413266197588166674376773

noncomputable def ep864 := nat_lit 4684879734889029641161534341120000000000

noncomputable def ep865 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz213)) (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz213)) ep861 ep862 ep863 ep864 ep861 ep862 ep863

noncomputable def ep866 := nat_lit 12917253595882322083602327499

noncomputable def ep867 := nat_lit 2213609288845146193920000000000

noncomputable def ep868 := nat_lit 31921114243936708226376478988141

noncomputable def ep869 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz213) Bool.true ep861 ep862 ep863 ep864 Bool.false ep866 ep867 ep868

noncomputable def ep870 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz213 Bool.true ep861 ep862 ep863 ep864 Bool.false ep866 ep867 ep868 ep864

noncomputable def ep871 := nat_lit 1707124833727562322945691

noncomputable def ep872 := nat_lit 8854437155380584775680000000

noncomputable def ep873 := nat_lit 5120832275553767566852763069

noncomputable def ep874 := nat_lit 18739518939556118564646137364480000000

noncomputable def ep875 := nat_lit 97196183049992941151267729413

noncomputable def ep876 := nat_lit 15073812334182904284342575662271

noncomputable abbrev qz224 := (Complex.re qz420)

noncomputable abbrev qz225 := (Complex.im qz420)

noncomputable def ep877 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)))) qz224) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)))) qz225) ep871 ep872 ep873 ep874 ep875 ep867 ep876

noncomputable def ep878 := nat_lit 360375364222233049320118026240000000000

noncomputable def ep879 := nat_lit 856838587169872550465104641139977057129755144355840000000

noncomputable def ep880 := nat_lit 156162657829634321372051144704

noncomputable def ep881 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)))) qz224 2986084303 120000000 0 1 571693448846197 73786976294838206464 1714898762372204723 ep880 ep871

noncomputable def ep882 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)))) 2986084303 120000000 0 1 0 1 0 1 2986084303

noncomputable def ep883 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 8958252909 500000 0 1 2986084303 120000000 0

noncomputable def ep884 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (Complex.mk (Enclosure.sfrac Bool.true 1 720) qz14) Bool.true 1 720 0 1 Bool.false 0 1 0 1 (BSN.bern_coeff_mk 2 1 30 24 Bool.true BSN.bern_real_2 EMRow15.d15 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 1 720) qz14 Bool.true 1 720 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.true 1 720) qz24)

noncomputable abbrev qz426 := (@HAdd.hAdd Complex Complex Complex qz448 qz447 qz452)

noncomputable abbrev qz226 := qz426

noncomputable def ep885 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)) (@HMul.hMul Complex Complex Complex qz45 (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 2)) qz226) Bool.true 8958252909 500000 0 1 Bool.true 31362580614651 125000000 0 1

noncomputable abbrev qz227 := (Complex.re qz426)

noncomputable abbrev qz228 := (Complex.im qz426)

noncomputable def ep886 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 2))) qz227) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 2))) qz228) 995278101 100000 0 1 995465601 125000 0 1

noncomputable def ep887 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 2))) qz227 995278101 250000 0 1 5 2 0 1 995278101 100000

noncomputable abbrev qz427 := (@HAdd.hAdd Complex Complex Complex qz448 qz447 (@Nat.cast Complex Complex.instNatCast 1))

noncomputable abbrev qz229 := qz427

noncomputable def ep888 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 2)) (@HMul.hMul Complex Complex Complex qz45 (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)) qz229) Bool.true 995278101 250000 0 1 Bool.false 31551 250 0 1

noncomputable abbrev qz230 := (Complex.re qz427)

noncomputable abbrev qz231 := (Complex.im qz427)

noncomputable def ep889 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1))) qz230) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1))) qz231) 3 4 0 1 995465601 250000 0 1

noncomputable def ep890 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1))) qz230 1 2 0 1 3 2 0 1 3 4

noncomputable def ep891 := @ep890 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 63102 1000 0 1 ep408)

noncomputable def ep892 := @Enclosure.Complex.IsNear.of_eq qz229 (Complex.mk (Enclosure.sfrac Bool.false 3 2) qz17) Bool.false 3 2 0 1 Bool.false 63102 1000 0 1 (BSN.s_add_nat_mk qz17 Bool.false 63102 1000 1 qz18)

noncomputable abbrev qz232 := (ep892 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 3 2) qz276 Bool.false 3 2 0 1 Bool.false 63102 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 3 2) qz280))

noncomputable def ep893 := ep891 (@Enclosure.Complex.IsNear.re_isNear qz229 Bool.false 3 2 0 1 Bool.false 63102 1000 0 1 qz232)

noncomputable def ep894 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1))) qz231 63102 1000 0 1 63102 1000 0 1 995465601 250000

noncomputable def ep895 := @ep894 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 63102 1000 0 1 ep408)

noncomputable def ep896 := ep895 (@Enclosure.Complex.IsNear.im_isNear qz229 Bool.false 3 2 0 1 Bool.false 63102 1000 0 1 qz232)

noncomputable def ep897 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)) qz229 Bool.true 995278101 250000 0 1 Bool.false 31551 250 0 1 (@ep889 3981112404 995278101 250000 0 1 (ep893 rfl) (ep896 rfl) rfl rfl)

noncomputable def ep898 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1))) qz231) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1))) qz230) 31551 1000 0 1 94653 1000 0 1

noncomputable def ep899 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1))) qz231 1 2 0 1 63102 1000 0 1 31551 1000

noncomputable def ep900 := @ep899 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 63102 1000 0 1 ep408)

noncomputable def ep901 := ep900 (@Enclosure.Complex.IsNear.im_isNear qz229 Bool.false 3 2 0 1 Bool.false 63102 1000 0 1 qz232)

noncomputable def ep902 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1))) qz230 63102 1000 0 1 3 2 0 1 94653 1000

noncomputable def ep903 := @ep902 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 63102 1000 0 1 ep408)

noncomputable def ep904 := ep903 (@Enclosure.Complex.IsNear.re_isNear qz229 Bool.false 3 2 0 1 Bool.false 63102 1000 0 1 qz232)

noncomputable abbrev qz233 := (ep888 (BSN.ascPochhammer_succ_eval_c 1 2 qz268 rfl) (ep897 (@ep898 126204000 31551 250 0 1 (ep901 rfl) (ep904 rfl) rfl rfl)))

noncomputable def ep905 := @ep887 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 995278101 250000 0 1 Bool.false 31551 250 0 1 qz233)

noncomputable def ep906 := @Enclosure.Complex.IsNear.of_eq qz226 (Complex.mk (Enclosure.sfrac Bool.false 5 2) qz17) Bool.false 5 2 0 1 Bool.false 63102 1000 0 1 (BSN.s_add_nat_mk qz17 Bool.false 63102 1000 2 qz18)

noncomputable abbrev qz234 := (ep906 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 5 2) qz276 Bool.false 5 2 0 1 Bool.false 63102 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 5 2) qz280))

noncomputable def ep907 := ep905 (@Enclosure.Complex.IsNear.re_isNear qz226 Bool.false 5 2 0 1 Bool.false 63102 1000 0 1 qz234)

noncomputable def ep908 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 2))) qz228 31551 250 0 1 63102 1000 0 1 995465601 125000

noncomputable def ep909 := @ep908 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 995278101 250000 0 1 Bool.false 31551 250 0 1 qz233)

noncomputable def ep910 := ep909 (@Enclosure.Complex.IsNear.im_isNear qz226 Bool.false 5 2 0 1 Bool.false 63102 1000 0 1 qz234)

noncomputable def ep911 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 2)) qz226 Bool.true 8958252909 500000 0 1 Bool.true 31362580614651 125000000 0 1 (@ep886 223956322725000 8958252909 500000 0 1 (ep907 rfl) (ep910 rfl) rfl rfl)

noncomputable def ep912 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 2))) qz228) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 2))) qz227) 31402019364651 125000000 0 1 31551 100 0 1

noncomputable def ep913 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 2))) qz228 995278101 250000 0 1 63102 1000 0 1 31402019364651 125000000

noncomputable def ep914 := @ep913 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 995278101 250000 0 1 Bool.false 31551 250 0 1 qz233)

noncomputable def ep915 := ep914 (@Enclosure.Complex.IsNear.im_isNear qz226 Bool.false 5 2 0 1 Bool.false 63102 1000 0 1 qz234)

noncomputable def ep916 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 2))) qz227 31551 250 0 1 5 2 0 1 31551 100

noncomputable def ep917 := @ep916 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 995278101 250000 0 1 Bool.false 31551 250 0 1 qz233)

noncomputable def ep918 := ep917 (@Enclosure.Complex.IsNear.re_isNear qz226 Bool.false 5 2 0 1 Bool.false 63102 1000 0 1 qz234)

noncomputable abbrev qz235 := (ep885 (BSN.ascPochhammer_succ_eval_c 2 3 qz268 rfl) (ep911 (@ep912 3136258061465100 31362580614651 125000000 0 1 (ep915 rfl) (ep918 rfl) rfl rfl)))

noncomputable def ep919 := @ep883 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep884) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 8958252909 500000 0 1 Bool.true 31362580614651 125000000 0 1 qz235)

noncomputable def ep920 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 31362580614651 125000000 0 1 0 1 0

noncomputable def ep921 := @ep920 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep884) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 8958252909 500000 0 1 Bool.true 31362580614651 125000000 0 1 qz235)

noncomputable def ep922 := @Enclosure.Real.IsNear.addLit_ft_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)))) 10454193538217 30000000000 0 1 0 1 0 1 10454193538217

noncomputable def ep923 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 31362580614651 125000000 0 1 10454193538217 30000000000 0

noncomputable def ep924 := @ep923 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep884) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 8958252909 500000 0 1 Bool.true 31362580614651 125000000 0 1 qz235)

noncomputable def ep925 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 8958252909 500000 0 1 0 1 0

noncomputable def ep926 := @ep925 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep884) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 8958252909 500000 0 1 Bool.true 31362580614651 125000000 0 1 qz235)

noncomputable def ep927 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.false 2986084303 120000000 0 1 Bool.false 10454193538217 30000000000 0 1 (@ep882 2986084303 120000000 0 1 (ep919 rfl) (ep921 rfl) rfl rfl) (@ep922 10454193538217 30000000000 0 1 (ep924 rfl) (ep926 rfl) rfl rfl)

noncomputable def ep928 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 2986084303 120000000 0 1 Bool.false 10454193538217 30000000000 0 1 ep927

noncomputable def ep929 := @Enclosure.Complex.IsNear.re_isNear qz213 Bool.false 571693448846197 73786976294838206464 1714898762372204723 ep880 Bool.false 9297339167739389 73786976294838206464 18744588918123220219 ep880

noncomputable abbrev qz428 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 62748517)))

noncomputable def ep930 := @Enclosure.Complex.IsNear.of_eq qz213 (Complex.mk (@HMul.hMul Real Real Real qz0 qz428 qz124) (@HMul.hMul Real Real Real qz0 qz428 qz125)) Bool.false 571693448846197 73786976294838206464 1714898762372204723 ep880 Bool.false 9297339167739389 73786976294838206464 18744588918123220219

noncomputable abbrev qz429 := (Real.sqrt (@Nat.cast Real Real.instNatCast 62748517))

noncomputable abbrev qz430 := (@Nat.cast Real Real.instNatCast 62748517)

noncomputable def ep931 := @Enclosure.Real.IsNear.inv_image qz429 68044274824671 8589934592 1 8589934592 542198 542199 4294967296 (@Enclosure.Real.IsNear.of_eq qz429 (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz430 qz19)) Bool.false 68044274824671 8589934592 1 8589934592 (BSN.sqrt_natCast_div_one 62748517) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz430 qz19)) Bool.false 68044274824671 8589934592 1 8589934592 68044274824671 8589934592 1 8589934592 (BSN.sqrt_enclosure 62748517 1 34022137412335 34022137412336 4294967296 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep932 := nat_lit 81399948500000000000000000

noncomputable def ep933 := nat_lit 2116398661000000000000000

noncomputable def ep934 := nat_lit 396906688516144272597057536

noncomputable def ep935 := nat_lit 154742504910672534362390528

noncomputable def ep936 := nat_lit 6575506801219411134104025

noncomputable def ep937 := BSN.log_dyadic_bound 5 21 8 7 ep936 4294967296 2116398661 128659082644411320054375 824798583984375 2085240190 26 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base7 (BSN.artanhP 5) (BSN.artanhQ 21) 0 7 128659082644411320054375 ep936 824798583984375 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep938 := @Enclosure.Real.IsNear.mulLit_ff qz17 qz126 63102 1000 0 1 11551504969717477 4503599627370496 1000006349195983 ep933 364461533299556116827 2251799813685248000 2427015409498650741 ep932 qz22 (BSN.isNear_log_sfrac 13 1 11551504969717477 4503599627370496 1000006349195983 ep933 Bool.false (@Enclosure.Real.IsNear.recentre' qz369 Bool.false ep934 ep935 1000006349195983 ep933 11551504969717477 4503599627370496 1000006349195983 ep933 (BSN.log_rat_reduce_isNear 13 1 3 26 16 2085240190 4294967296 24973259072661432 36028797018963968 2116398661 1000000000000000 rfl rfl rfl rfl (ep937 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep939 := nat_lit 76025220235036817973313536

noncomputable def ep940 := nat_lit 1237940039285380274899124224

noncomputable def ep941 := nat_lit 1362421678762501335704535798064238305376600002801

noncomputable def ep942 := nat_lit 11493716556494166437687602703627318877140543416377016320

noncomputable def ep943 := nat_lit 80456015895459165063813218925391232139983803914639114240

noncomputable def ep944 := BSN.sin_dyadic_bound_f 1080383359451 17592186044416 2 1 8589934592 4236930914 ep941 ep942 ep941 ep941 ep943 ep941 527199401 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1080383359451) (BSN.sinEvenQ 17592186044416) 0 1 ep941 ep942 ep941 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1080383359451) (BSN.sinOddQ 17592186044416) 0 1 ep941 ep943 ep941 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz431 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 1390310414503) (@Nat.cast Real Real.instNatCast 8589934592))

noncomputable def ep945 := @Enclosure.Real.IsNear.cos_image qz127 qz431 Bool.false 1390310414503 8589934592 257 8589934592 Bool.false 527199401 8589934592 1 2116398661 (@Enclosure.Real.IsNear.recentre' qz127 Bool.false 364461533299556116827 2251799813685248000 2427015409498650741 ep932 1390310414503 8589934592 257 8589934592 (ep938 rfl) rfl) (Enclosure.sfrac_false_div 1390310414503 8589934592) (BSN.cos_reduce3 qz431 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast ep939) (@Nat.cast Real Real.instNatCast ep940)) 226375608064910080 72057594037927936 Bool.false 527199401 8589934592 25 1000000000000000 4232797322 2116398661 (BSN.sin_reduce_arg_pos_rat_q3 1390310414503 8589934592 226375608064910080 72057594037927936 25 ep939 ep940 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 527199401 8589934592 ep939 ep940 1080383359451 17592186044416 4236930914 4232797322 (ep944 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep946 := nat_lit 2298743311298833287537520540725463775428108683275403264

noncomputable def ep947 := nat_lit 34481149669482499313062808110881956631421630249131048960

noncomputable def ep948 := BSN.cos_dyadic_bound_f 1080383359451 17592186044416 2 1 8589934592 4236930914 ep941 ep946 ep941 ep941 ep947 ep941 8573741137 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1080383359451) (BSN.cosEvenQ 17592186044416) 0 1 ep941 ep946 ep941 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1080383359451) (BSN.cosOddQ 17592186044416) 0 1 ep941 ep947 ep941 rfl rfl rfl rfl) rfl rfl

noncomputable def ep949 := @Enclosure.Real.IsNear.sin_image qz127 qz431 Bool.false 1390310414503 8589934592 257 8589934592 Bool.true 8573741137 8589934592 1 2116398661 (@Enclosure.Real.IsNear.recentre' qz127 Bool.false 364461533299556116827 2251799813685248000 2427015409498650741 ep932 1390310414503 8589934592 257 8589934592 (ep938 rfl) rfl) (Enclosure.sfrac_false_div 1390310414503 8589934592) (BSN.sin_reduce3 qz431 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast ep939) (@Nat.cast Real Real.instNatCast ep940)) 226375608064910080 72057594037927936 Bool.false 8573741137 8589934592 25 1000000000000000 4232797322 2116398661 (BSN.sin_reduce_arg_pos_rat_q3 1390310414503 8589934592 226375608064910080 72057594037927936 25 ep939 ep940 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 8573741137 8589934592 ep939 ep940 1080383359451 17592186044416 4236930914 4232797322 (ep948 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep950 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz428 qz124) (@HMul.hMul Real Real Real qz0 qz428 qz125) Bool.false 571693448846197 73786976294838206464 1714898762372204723 ep880 Bool.false 9297339167739389 73786976294838206464 18744588918123220219 ep880 (@Enclosure.Real.IsNear.mulLit_ff qz428 qz124 1084397 8589934592 1 8589934592 527199401 8589934592 552504390469 18179726068586381312 571693448846197 73786976294838206464 1714898762372204723 ep880 (@Enclosure.Real.IsNear.recentre' qz428 Bool.false 1084397 8589934592 1 8589934592 1084397 8589934592 1 8589934592 (ep931 rfl rfl) rfl) (@Enclosure.Real.IsNear.recentre' qz124 Bool.false 527199401 8589934592 552504390469 18179726068586381312 527199401 8589934592 552504390469 18179726068586381312 (ep945 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz428 qz125 1084397 8589934592 1 8589934592 8573741137 8589934592 552504390469 18179726068586381312 9297339167739389 73786976294838206464 18744588918123220219 ep880 (@Enclosure.Real.IsNear.recentre' qz428 Bool.false 1084397 8589934592 1 8589934592 1084397 8589934592 1 8589934592 (ep931 rfl rfl) rfl) (@Enclosure.Real.IsNear.neg qz128 Bool.true 8573741137 8589934592 552504390469 18179726068586381312 (@Enclosure.Real.IsNear.recentre' qz128 Bool.true 8573741137 8589934592 552504390469 18179726068586381312 8573741137 8589934592 552504390469 18179726068586381312 (ep949 rfl rfl) rfl)) rfl)

noncomputable def ep951 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)))) qz225 10454193538217 30000000000 0 1 9297339167739389 73786976294838206464 18744588918123220219 ep880 ep875

noncomputable def ep952 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 2986084303 120000000 0 1 Bool.false 10454193538217 30000000000 0 1 ep927

noncomputable def ep953 := @Enclosure.Complex.IsNear.im_isNear qz213 Bool.false 571693448846197 73786976294838206464 1714898762372204723 ep880 Bool.false 9297339167739389 73786976294838206464 18744588918123220219 ep880

noncomputable def ep954 := nat_lit 27762638548453673487710867

noncomputable def ep955 := nat_lit 55972922734595500115768122357

noncomputable def ep956 := nat_lit 5976593958768903711674610749

noncomputable def ep957 := nat_lit 1379067966175987169033419107607

noncomputable def ep958 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)))) qz225) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)))) qz224) ep954 ep872 ep955 ep874 ep956 ep867 ep957

noncomputable def ep959 := nat_lit 114375010184853897726916011773489127362532810424320000000

noncomputable def ep960 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)))) qz225 2986084303 120000000 0 1 9297339167739389 73786976294838206464 18744588918123220219 ep880 ep954

noncomputable def ep961 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)))) qz224 10454193538217 30000000000 0 1 571693448846197 73786976294838206464 1714898762372204723 ep880 ep956

noncomputable abbrev qz432 := (@ep930 ep880 (BSN.cpow_neg_s_sub_mk qz17 63102 1000 13 3 62748517 qz18 rfl EMRow15.d16) ep950)

noncomputable def ep962 := ep870 (@ep877 ep878 ep879 ep861 ep862 ep863 ep864 (@ep881 ep872 ep873 ep874 ep928 (ep929 qz432) rfl) (@ep951 ep867 ep876 ep878 ep952 (ep953 qz432) rfl) rfl rfl) (@ep958 ep878 ep959 ep866 ep867 ep868 ep864 (@ep960 ep872 ep955 ep874 ep928 (ep953 qz432) rfl) (@ep961 ep867 ep957 ep878 ep952 (ep929 qz432) rfl) rfl rfl)

noncomputable def ep963 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz213)) (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz213)) ep866 ep867 ep868 ep864 ep866 ep867 ep868

noncomputable def ep964 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz213) Bool.true ep861 ep862 ep863 ep864 Bool.false ep866 ep867 ep868

noncomputable def ep965 := @ep832 224157923888881 281474976710656 1571541483 1970324836974592 (@ep833 1 1835008 (ep834 (@ep835 524288 1 524288 (ep836 (@ep837 3994112404 998528101 250000 0 1 (ep841 rfl) (ep844 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) (Enclosure.Real.IsNear.const Bool.false 2 7) rfl) (@ep845 23 536870912 (BSN.norm_eq_sqrt_mul_add (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz213)) (@ep846 368 8589934592 47355679 1073741824 23 536870912 (@ep851 189422532 189422900 4294967296 (@ep857 ep858 ep859 ep855 ep860 ep847 ep848 ep849 ep850 (@ep865 ep864 ep852 ep853 ep854 ep855 (@ep869 ep864 ep962) (@ep869 ep864 ep962) rfl) (@ep963 ep864 ep856 ep858 ep859 ep855 (@ep964 ep864 ep962) (@ep964 ep864 ep962) rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl

theorem EMRow15.d17 : Enclosure.Real.IsNear (@HAdd.hAdd Real Real Real qz87 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz6 1 13))) (@HMul.hMul Real Real Real qz0 qz210 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz213)))) Bool.false 726385913097427 844424930131968 3676818645961 53198770598313984 := ep830 (ep831 ep965) rfl rfl

theorem EMRow15.d18 : @Eq Nat (Nat.pow 14 (Nat.succ (Nat.mul 2 3))) 105413504 := @Eq.refl Nat 105413504

noncomputable abbrev qz470 := (@HAdd.hAdd Complex Complex Complex qz472 qz478 (@Nat.cast Complex Complex.instNatCast 3))

noncomputable abbrev qz433 := qz470

noncomputable abbrev qz236 := (@HDiv.hDiv Real Real Real qz266 (@Norm.norm Complex Complex.instNorm qz433) (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (Complex.re qz374) (@Nat.cast Real Real.instNatCast 3)))

noncomputable abbrev qz434 := (@HPow.hPow Complex Complex Complex qz449 qz468 (@HSub.hSub Complex Complex Complex qz455 qz464 qz451))

noncomputable abbrev qz237 := qz434

noncomputable def ep966 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz136 1 14))) (@HMul.hMul Real Real Real qz0 qz236 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz136 (@ascPochhammer Complex Complex.instSemiring 3))) qz237))) 871043239 51539607552 33675733 463856467968 3271093098639541 4503599627370496 16036401189

noncomputable def ep967 := nat_lit 172513684576521558138290176

noncomputable def ep968 := @Enclosure.Real.IsNear.mulLit_ff (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz136 1 14)) 4427 294912 1 884736 590271 524288 2491 524288 871043239 51539607552

noncomputable def ep969 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (zetaApproximant qz136 1 14)) (Real.sqrt (@HAdd.hAdd Real Real Real qz87 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz136 1 14)) (Complex.re (zetaApproximant qz136 1 14))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz136 1 14)) (Complex.im (zetaApproximant qz136 1 14))))) Bool.false 590271 524288 2491 524288

noncomputable def ep970 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz87 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz136 1 14)) (Complex.re (zetaApproximant qz136 1 14))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz136 1 14)) (Complex.im (zetaApproximant qz136 1 14))))) Bool.false 590271 524288 2491 524288

noncomputable def ep971 := nat_lit 1300519915591906378177412758755206221279369

noncomputable def ep972 := nat_lit 1025996282935842869128178801989124096000000

noncomputable def ep973 := nat_lit 2192289754903095588248627685526386661379518928348111370297

noncomputable def ep974 := nat_lit 204992053797096866082481316906944408230762648052957184000000

noncomputable def ep975 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz87 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz136 1 14)) (Complex.re (zetaApproximant qz136 1 14))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz136 1 14)) (Complex.im (zetaApproximant qz136 1 14)))) ep971 ep972 ep973 ep974 293890 296381

noncomputable def ep976 := nat_lit 114825157060716439188766129773388019609179752448681

noncomputable def ep977 := nat_lit 90665021788936884091159801028636920464277504000000

noncomputable def ep978 := nat_lit 252960733934544598345526641722178944960844305676287457884927

noncomputable def ep979 := nat_lit 24394054401854527063815276711926384579460755118301904896000000

noncomputable def ep980 := nat_lit 12116577671364495070829742017579621248614389161

noncomputable def ep981 := nat_lit 11106465169144768301167075626008022756873994240000

noncomputable def ep982 := nat_lit 61888647647842005125469162933289591744675365602639024847

noncomputable def ep983 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz136 1 14)) (Complex.re (zetaApproximant qz136 1 14))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz136 1 14)) (Complex.im (zetaApproximant qz136 1 14))) ep976 ep977 ep978 ep979 ep980 ep981 ep982

noncomputable def ep984 := nat_lit 190578550014488492686056849311924879527037149361733632000000

noncomputable def ep985 := nat_lit 1276400157215006201032806194783115954140700411583978616858722193657416687895596801127762823741440000

noncomputable def ep986 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (zetaApproximant qz136 1 14)) (Complex.re (zetaApproximant qz136 1 14)) ep542 ep543 ep544 ep545 ep542 ep543 ep544 ep545 ep976

noncomputable def ep987 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (zetaApproximant qz136 1 14)) (Complex.im (zetaApproximant qz136 1 14)) 110075327259856443593869 ep650 ep651 ep652 110075327259856443593869 ep650 ep651 ep652 ep980

noncomputable def ep988 := @ep966 31525197391593472 ep967 10041618054763039 13510798882111488 62228222292967 851180329573023744 (@ep968 33675733 463856467968 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaStirlingErrorBound 1 2) (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 96 162) (@Inv.inv Real Real.instInv qz214)) Bool.false 4427 294912 1 884736 (BSN.theta_err_eq 1 2 96 162 EMRow15.d13 EMRow15.d14 rfl) (ep811 rfl)) (ep969 (BSN.norm_eq_sqrt_mul_add (zetaApproximant qz136 1 14)) (@ep970 590271 524288 2491 524288 (@ep975 262144 (@ep983 ep984 ep985 ep971 ep972 ep973 ep974 (@ep986 ep977 ep978 ep979 ep793 ep793 rfl) (@ep987 ep981 ep982 ep984 ep799 ep799 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl)

noncomputable abbrev qz238 := (@Norm.norm Complex Complex.instNorm qz433)

noncomputable def ep989 := @Enclosure.Real.IsNear.of_eq (@HMul.hMul Real Real Real qz0 qz236 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz136 (@ascPochhammer Complex Complex.instSemiring 3))) qz237))) (@HMul.hMul Real Real Real qz0 (@HMul.hMul Real Real Real qz0 qz238 qz423) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz136 (@ascPochhammer Complex Complex.instSemiring 3))) qz237))) Bool.false 3271093098639541 4503599627370496 16036401189 31525197391593472 (BSN.zrb_shape_eq qz238 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz136 (@ascPochhammer Complex Complex.instSemiring 3))) qz237)) qz145 3)

noncomputable def ep990 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz0 qz238 qz423) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz136 (@ascPochhammer Complex Complex.instSemiring 3))) qz237)) 4935349 262144 1 1835008 662788609 17179869184 445 17179869184

noncomputable def ep991 := @Enclosure.Real.IsNear.mulLit_ff qz238 qz423 34547443 524288 1 524288 2 7 0 1 4935349 262144

noncomputable abbrev qz435 := (Complex.re qz470)

noncomputable abbrev qz436 := (Complex.im qz470)

noncomputable abbrev qz239 := (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (@HMul.hMul Real Real Real qz263 qz435 qz435) (@HMul.hMul Real Real Real qz263 qz436 qz436))

noncomputable abbrev qz240 := qz433

noncomputable def ep992 := @Enclosure.Real.IsNear.of_eq qz238 (Real.sqrt qz239) Bool.false 34547443 524288 1 524288 (BSN.norm_eq_sqrt_mul_add qz240)

noncomputable def ep993 := @Enclosure.Real.IsNear.recentre' (Real.sqrt qz239) Bool.false 34547443 524288 1 524288 34547443

noncomputable def ep994 := @Enclosure.Real.IsNear.sqrt_image qz239 4342021601 1000000 0 1 17273721 17273722 262144

noncomputable abbrev qz241 := (@HMul.hMul Real Real Real qz263 qz435 qz435)

noncomputable abbrev qz242 := (@HMul.hMul Real Real Real qz263 qz436 qz436)

noncomputable def ep995 := @Enclosure.Real.IsNear.addLit_ff qz241 qz242 49 4 0 1 4329771601 1000000 0 1

noncomputable abbrev qz243 := qz435

noncomputable def ep996 := @Enclosure.Real.IsNear.mulLit_ff qz243 qz243 7 2 0 1 7 2 0 1 49 4

noncomputable def ep997 := @Enclosure.Complex.IsNear.of_eq qz240 (Complex.mk (Enclosure.sfrac Bool.false 7 2) qz145) Bool.false 7 2 0 1 Bool.false 65801 1000 0 1 (BSN.s_add_nat_mk qz145 Bool.false 65801 1000 3 qz146)

noncomputable abbrev qz244 := (ep997 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7 2) qz376 Bool.false 7 2 0 1 Bool.false 65801 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 7 2) qz378))

noncomputable def ep998 := @ep996 0 1 (@Enclosure.Complex.IsNear.re_isNear qz240 Bool.false 7 2 0 1 Bool.false 65801 1000 0 1 qz244)

noncomputable def ep999 := ep998 (@Enclosure.Complex.IsNear.re_isNear qz240 Bool.false 7 2 0 1 Bool.false 65801 1000 0 1 qz244)

noncomputable abbrev qz245 := qz436

noncomputable def ep1000 := @Enclosure.Real.IsNear.mulLit_ff qz245 qz245 65801 1000 0 1 65801 1000 0 1 4329771601 1000000

noncomputable def ep1001 := @ep1000 0 1 (@Enclosure.Complex.IsNear.im_isNear qz240 Bool.false 7 2 0 1 Bool.false 65801 1000 0 1 qz244)

noncomputable def ep1002 := ep1001 (@Enclosure.Complex.IsNear.im_isNear qz240 Bool.false 7 2 0 1 Bool.false 65801 1000 0 1 qz244)

noncomputable def ep1003 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz136 (@ascPochhammer Complex Complex.instSemiring 3))) qz237)) (Real.sqrt (@HAdd.hAdd Real Real Real qz87 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz136 (@ascPochhammer Complex Complex.instSemiring 3))) qz237)) (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz136 (@ascPochhammer Complex Complex.instSemiring 3))) qz237))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz136 (@ascPochhammer Complex Complex.instSemiring 3))) qz237)) (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz136 (@ascPochhammer Complex Complex.instSemiring 3))) qz237))))) Bool.false 662788609 17179869184

noncomputable def ep1004 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz87 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz136 (@ascPochhammer Complex Complex.instSemiring 3))) qz237)) (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz136 (@ascPochhammer Complex Complex.instSemiring 3))) qz237))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz136 (@ascPochhammer Complex Complex.instSemiring 3))) qz237)) (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz136 (@ascPochhammer Complex Complex.instSemiring 3))) qz237))))) Bool.false 662788609 17179869184

noncomputable def ep1005 := nat_lit 33606615196456116705061536571039409851648657476850668654032441

noncomputable def ep1006 := nat_lit 22579504513512255930804914751056466024805171200000000000000000000

noncomputable def ep1007 := nat_lit 284958138049179073421186932308527145812012853700724890577458997679648467

noncomputable def ep1008 := nat_lit 142947597623887369612752260753902239898381830658105641522954240000000000000000000

noncomputable def ep1009 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz87 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz136 (@ascPochhammer Complex Complex.instSemiring 3))) qz237)) (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz136 (@ascPochhammer Complex Complex.instSemiring 3))) qz237))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz136 (@ascPochhammer Complex Complex.instSemiring 3))) qz237)) (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz136 (@ascPochhammer Complex Complex.instSemiring 3))) qz237)))) ep1005 ep1006 ep1007 ep1008

noncomputable def ep1010 := nat_lit 535906756005914991336706510272618097330523340174454879354441

noncomputable def ep1011 := nat_lit 557518629963265578538392956816209037649510400000000000000000000

noncomputable def ep1012 := nat_lit 4266856725135474315577041785936378762534170904346590397475354594363203

noncomputable def ep1013 := nat_lit 3529570311700922706487710142071660244404489645879151642542080000000000000000000

noncomputable def ep1014 := nat_lit 23804783156433119111849845809996753819524924399570492080355161

noncomputable def ep1015 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz136 (@ascPochhammer Complex Complex.instSemiring 3))) qz237)) (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz136 (@ascPochhammer Complex Complex.instSemiring 3))) qz237))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz136 (@ascPochhammer Complex Complex.instSemiring 3))) qz237)) (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz136 (@ascPochhammer Complex Complex.instSemiring 3))) qz237))) ep1010 ep1011 ep1012 ep1013 ep1014

noncomputable def ep1016 := nat_lit 45159009027024511861609829502112932049610342400000000000000000000

noncomputable def ep1017 := nat_lit 224300881362384727280633479956207611858757864149375958959414273215877491

noncomputable def ep1018 := nat_lit 285895195247774739225504521507804479796763661316211283045908480000000000000000000

noncomputable def ep1019 := nat_lit 37472628124061750948002709926920723762813175683179629839112448815764924935736718924103538746234778733772800000000000000000000

noncomputable def ep1020 := nat_lit 732056525144004840552421219229

noncomputable def ep1021 := nat_lit 23611832414348226068480000000000

noncomputable def ep1022 := nat_lit 16380120146752897107563178344431

noncomputable def ep1023 := nat_lit 840186921071843715532189597696000000000

noncomputable def ep1024 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz136 (@ascPochhammer Complex Complex.instSemiring 3))) qz237)) (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz136 (@ascPochhammer Complex Complex.instSemiring 3))) qz237)) ep1020 ep1021 ep1022 ep1023 ep1020 ep1021 ep1022

noncomputable def ep1025 := nat_lit 4879014568171847456535439705381

noncomputable def ep1026 := nat_lit 212506491729134034616320000000000

noncomputable def ep1027 := nat_lit 129197014797099154033003319849983

noncomputable def ep1028 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz136 (@ascPochhammer Complex Complex.instSemiring 3))) qz237) Bool.true ep1020 ep1021 ep1022 ep1023 Bool.true ep1025 ep1026 ep1027

noncomputable def ep1029 := nat_lit 7561682289646593439789706379264000000000

noncomputable def ep1030 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz136 (@ascPochhammer Complex Complex.instSemiring 3))) qz237 Bool.true ep1020 ep1021 ep1022 ep1023 Bool.true ep1025 ep1026 ep1027 ep1029

noncomputable def ep1031 := nat_lit 242176353667466593098400243

noncomputable def ep1032 := nat_lit 141670994486089356410880000000

noncomputable def ep1033 := nat_lit 111478405555306465852990801

noncomputable def ep1034 := nat_lit 102880031151654332514145665024000000

noncomputable def ep1035 := nat_lit 2075081398598281225108063536187

noncomputable def ep1036 := nat_lit 70835497243044678205440000000000

noncomputable def ep1037 := nat_lit 46409139504153682909291260408793

noncomputable abbrev qz246 := (Complex.re qz434)

noncomputable abbrev qz247 := (Complex.im qz434)

noncomputable def ep1038 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz136 (@ascPochhammer Complex Complex.instSemiring 3)))) qz246) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz136 (@ascPochhammer Complex Complex.instSemiring 3)))) qz247) ep1031 ep1032 ep1033 ep1034 ep1035 ep1036 ep1037

noncomputable def ep1039 := nat_lit 2520560763215531146596568793088000000000

noncomputable def ep1040 := nat_lit 311133527811546132196522585473126501623814771242434560000000

noncomputable def ep1041 := nat_lit 52511682566990232220761849856

noncomputable def ep1042 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz136 (@ascPochhammer Complex Complex.instSemiring 3)))) qz246 12988064803 480000000 0 1 18646069090410481 295147905179352825856 2102869809730351415 ep1041 ep1031

noncomputable def ep1043 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz136 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz136 (@ascPochhammer Complex Complex.instSemiring 3)))) 12988064803 480000000 0 1 0 1 0 1 12988064803

noncomputable def ep1044 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz136 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 38964194409 2000000 0 1 12988064803 480000000 0

noncomputable abbrev qz437 := (@HAdd.hAdd Complex Complex Complex qz448 qz463 qz452)

noncomputable abbrev qz248 := qz437

noncomputable def ep1045 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz136 (@ascPochhammer Complex Complex.instSemiring 3)) (@HMul.hMul Complex Complex Complex qz45 (@Polynomial.eval Complex Complex.instSemiring qz136 (@ascPochhammer Complex Complex.instSemiring 2)) qz248) Bool.true 38964194409 2000000 0 1 Bool.true 284524945367401 1000000000 0 1

noncomputable abbrev qz249 := (Complex.re qz437)

noncomputable abbrev qz250 := (Complex.im qz437)

noncomputable def ep1046 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz136 (@ascPochhammer Complex Complex.instSemiring 2))) qz249) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz136 (@ascPochhammer Complex Complex.instSemiring 2))) qz250) 4329021601 400000 0 1 4329771601 500000 0 1

noncomputable def ep1047 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz136 (@ascPochhammer Complex Complex.instSemiring 2))) qz249 4329021601 1000000 0 1 5 2 0 1 4329021601 400000

noncomputable abbrev qz438 := (@HAdd.hAdd Complex Complex Complex qz448 qz463 (@Nat.cast Complex Complex.instNatCast 1))

noncomputable abbrev qz251 := qz438

noncomputable def ep1048 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz136 (@ascPochhammer Complex Complex.instSemiring 2)) (@HMul.hMul Complex Complex Complex qz45 (@Polynomial.eval Complex Complex.instSemiring qz136 (@ascPochhammer Complex Complex.instSemiring 1)) qz251) Bool.true 4329021601 1000000 0 1 Bool.false 65801 500 0 1

noncomputable abbrev qz252 := (Complex.re qz438)

noncomputable abbrev qz253 := (Complex.im qz438)

noncomputable def ep1049 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz136 (@ascPochhammer Complex Complex.instSemiring 1))) qz252) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz136 (@ascPochhammer Complex Complex.instSemiring 1))) qz253) 3 4 0 1 4329771601 1000000 0 1

noncomputable def ep1050 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz136 (@ascPochhammer Complex Complex.instSemiring 1))) qz252 1 2 0 1 3 2 0 1 3 4

noncomputable def ep1051 := @ep1050 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz136 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 65801 1000 0 1 ep757)

noncomputable def ep1052 := @Enclosure.Complex.IsNear.of_eq qz251 (Complex.mk (Enclosure.sfrac Bool.false 3 2) qz145) Bool.false 3 2 0 1 Bool.false 65801 1000 0 1 (BSN.s_add_nat_mk qz145 Bool.false 65801 1000 1 qz146)

noncomputable abbrev qz254 := (ep1052 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 3 2) qz376 Bool.false 3 2 0 1 Bool.false 65801 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 3 2) qz378))

noncomputable def ep1053 := ep1051 (@Enclosure.Complex.IsNear.re_isNear qz251 Bool.false 3 2 0 1 Bool.false 65801 1000 0 1 qz254)

noncomputable def ep1054 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz136 (@ascPochhammer Complex Complex.instSemiring 1))) qz253 65801 1000 0 1 65801 1000 0 1 4329771601 1000000

noncomputable def ep1055 := @ep1054 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz136 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 65801 1000 0 1 ep757)

noncomputable def ep1056 := ep1055 (@Enclosure.Complex.IsNear.im_isNear qz251 Bool.false 3 2 0 1 Bool.false 65801 1000 0 1 qz254)

noncomputable def ep1057 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz136 (@ascPochhammer Complex Complex.instSemiring 1)) qz251 Bool.true 4329021601 1000000 0 1 Bool.false 65801 500 0 1 (@ep1049 17316086404 4329021601 1000000 0 1 (ep1053 rfl) (ep1056 rfl) rfl rfl)

noncomputable def ep1058 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz136 (@ascPochhammer Complex Complex.instSemiring 1))) qz253) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz136 (@ascPochhammer Complex Complex.instSemiring 1))) qz252) 65801 2000 0 1 197403 2000 0 1

noncomputable def ep1059 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz136 (@ascPochhammer Complex Complex.instSemiring 1))) qz253 1 2 0 1 65801 1000 0 1 65801 2000

noncomputable def ep1060 := @ep1059 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz136 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 65801 1000 0 1 ep757)

noncomputable def ep1061 := ep1060 (@Enclosure.Complex.IsNear.im_isNear qz251 Bool.false 3 2 0 1 Bool.false 65801 1000 0 1 qz254)

noncomputable def ep1062 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz136 (@ascPochhammer Complex Complex.instSemiring 1))) qz252 65801 1000 0 1 3 2 0 1 197403 2000

noncomputable def ep1063 := @ep1062 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz136 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 65801 1000 0 1 ep757)

noncomputable def ep1064 := ep1063 (@Enclosure.Complex.IsNear.re_isNear qz251 Bool.false 3 2 0 1 Bool.false 65801 1000 0 1 qz254)

noncomputable abbrev qz255 := (ep1048 (BSN.ascPochhammer_succ_eval_c 1 2 qz374 rfl) (ep1057 (@ep1058 526408000 65801 500 0 1 (ep1061 rfl) (ep1064 rfl) rfl rfl)))

noncomputable def ep1065 := @ep1047 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz136 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 4329021601 1000000 0 1 Bool.false 65801 500 0 1 qz255)

noncomputable def ep1066 := @Enclosure.Complex.IsNear.of_eq qz248 (Complex.mk (Enclosure.sfrac Bool.false 5 2) qz145) Bool.false 5 2 0 1 Bool.false 65801 1000 0 1 (BSN.s_add_nat_mk qz145 Bool.false 65801 1000 2 qz146)

noncomputable abbrev qz256 := (ep1066 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 5 2) qz376 Bool.false 5 2 0 1 Bool.false 65801 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 5 2) qz378))

noncomputable def ep1067 := ep1065 (@Enclosure.Complex.IsNear.re_isNear qz248 Bool.false 5 2 0 1 Bool.false 65801 1000 0 1 qz256)

noncomputable def ep1068 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz136 (@ascPochhammer Complex Complex.instSemiring 2))) qz250 65801 500 0 1 65801 1000 0 1 4329771601 500000

noncomputable def ep1069 := @ep1068 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz136 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 4329021601 1000000 0 1 Bool.false 65801 500 0 1 qz255)

noncomputable def ep1070 := ep1069 (@Enclosure.Complex.IsNear.im_isNear qz248 Bool.false 5 2 0 1 Bool.false 65801 1000 0 1 qz256)

noncomputable def ep1071 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz136 (@ascPochhammer Complex Complex.instSemiring 2)) qz248 Bool.true 38964194409 2000000 0 1 Bool.true 284524945367401 1000000000 0 1 (@ep1046 3896419440900000 38964194409 2000000 0 1 (ep1067 rfl) (ep1070 rfl) rfl rfl)

noncomputable def ep1072 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz136 (@ascPochhammer Complex Complex.instSemiring 2))) qz250) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz136 (@ascPochhammer Complex Complex.instSemiring 2))) qz249) 284853950367401 1000000000 0 1 65801 200 0 1

noncomputable def ep1073 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz136 (@ascPochhammer Complex Complex.instSemiring 2))) qz250 4329021601 1000000 0 1 65801 1000 0 1 284853950367401 1000000000

noncomputable def ep1074 := @ep1073 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz136 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 4329021601 1000000 0 1 Bool.false 65801 500 0 1 qz255)

noncomputable def ep1075 := ep1074 (@Enclosure.Complex.IsNear.im_isNear qz248 Bool.false 5 2 0 1 Bool.false 65801 1000 0 1 qz256)

noncomputable def ep1076 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz136 (@ascPochhammer Complex Complex.instSemiring 2))) qz249 65801 500 0 1 5 2 0 1 65801 200

noncomputable def ep1077 := @ep1076 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz136 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 4329021601 1000000 0 1 Bool.false 65801 500 0 1 qz255)

noncomputable def ep1078 := ep1077 (@Enclosure.Complex.IsNear.re_isNear qz248 Bool.false 5 2 0 1 Bool.false 65801 1000 0 1 qz256)

noncomputable abbrev qz257 := (ep1045 (BSN.ascPochhammer_succ_eval_c 2 3 qz374 rfl) (ep1071 (@ep1072 56904989073480200 284524945367401 1000000000 0 1 (ep1075 rfl) (ep1078 rfl) rfl rfl)))

noncomputable def ep1079 := @ep1044 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep884) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz136 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 38964194409 2000000 0 1 Bool.true 284524945367401 1000000000 0 1 qz257)

noncomputable def ep1080 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz136 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 284524945367401 1000000000 0 1 0 1 0

noncomputable def ep1081 := @ep1080 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep884) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz136 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 38964194409 2000000 0 1 Bool.true 284524945367401 1000000000 0 1 qz257)

noncomputable def ep1082 := @Enclosure.Real.IsNear.addLit_ft_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz136 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz136 (@ascPochhammer Complex Complex.instSemiring 3)))) 284524945367401 720000000000 0 1 0 1 0 1 284524945367401

noncomputable def ep1083 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz136 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 284524945367401 1000000000 0 1 284524945367401 720000000000 0

noncomputable def ep1084 := @ep1083 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep884) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz136 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 38964194409 2000000 0 1 Bool.true 284524945367401 1000000000 0 1 qz257)

noncomputable def ep1085 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz136 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 38964194409 2000000 0 1 0 1 0

noncomputable def ep1086 := @ep1085 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep884) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz136 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 38964194409 2000000 0 1 Bool.true 284524945367401 1000000000 0 1 qz257)

noncomputable def ep1087 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz136 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.false 12988064803 480000000 0 1 Bool.false 284524945367401 720000000000 0 1 (@ep1043 12988064803 480000000 0 1 (ep1079 rfl) (ep1081 rfl) rfl rfl) (@ep1082 284524945367401 720000000000 0 1 (ep1084 rfl) (ep1086 rfl) rfl rfl)

noncomputable def ep1088 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz136 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 12988064803 480000000 0 1 Bool.false 284524945367401 720000000000 0 1 ep1087

noncomputable def ep1089 := @Enclosure.Complex.IsNear.re_isNear qz237 Bool.true 18646069090410481 295147905179352825856 2102869809730351415 ep1041 Bool.false 21879432004657161 295147905179352825856 2446664532923108895 ep1041

noncomputable abbrev qz439 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 105413504)))

noncomputable def ep1090 := @Enclosure.Complex.IsNear.of_eq qz237 (Complex.mk (@HMul.hMul Real Real Real qz0 qz439 qz201) (@HMul.hMul Real Real Real qz0 qz439 qz202)) Bool.true 18646069090410481 295147905179352825856 2102869809730351415 ep1041 Bool.false 21879432004657161 295147905179352825856 2446664532923108895

noncomputable abbrev qz440 := (Real.sqrt (@Nat.cast Real Real.instNatCast 105413504))

noncomputable abbrev qz441 := (@Nat.cast Real Real.instNatCast 105413504)

noncomputable def ep1091 := @Enclosure.Real.IsNear.inv_image qz440 176387570092723 17179869184 1 17179869184 836645 836646 8589934592 (@Enclosure.Real.IsNear.of_eq qz440 (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz441 qz19)) Bool.false 176387570092723 17179869184 1 17179869184 (BSN.sqrt_natCast_div_one 105413504) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz441 qz19)) Bool.false 176387570092723 17179869184 1 17179869184 176387570092723 17179869184 1 17179869184 (BSN.sqrt_enclosure 105413504 1 88193785046361 88193785046362 8589934592 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep1092 := nat_lit 177916501000000000000000000

noncomputable def ep1093 := nat_lit 816748683538471975894646784

noncomputable def ep1094 := nat_lit 309485009821345068724781056

noncomputable def ep1095 := nat_lit 2846664016000000000000000

noncomputable def ep1096 := nat_lit 103769785630983789875522764800

noncomputable def ep1097 := nat_lit 2694100009858475599347056640

noncomputable def ep1098 := BSN.log_dyadic_bound 6 22 9 8 ep1096 8589934592 2846664016 ep1097 5718460310160998400 4807063014 28 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.artanhP 6) (BSN.artanhQ 22) 0 8 ep1097 ep1096 5718460310160998400 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep1099 := @Enclosure.Real.IsNear.mulLit_ff qz145 qz203 65801 1000 0 1 11885257605732069 4503599627370496 62500533749503 177916501000000000000000 782061835714775872269 4503599627370496000 4112597621251046903 ep1092 qz147 (BSN.isNear_log_sfrac 14 1 11885257605732069 4503599627370496 62500533749503 177916501000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz414) Bool.false ep1093 ep1094 1000008539992048 ep1095 11885257605732069 4503599627370496 62500533749503 177916501000000000000000 (BSN.log_rat_reduce_isNear 14 1 3 28 16 4807063014 8589934592 24973259072661432 36028797018963968 2846664016 1000000000000000 rfl rfl rfl rfl (ep1098 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1100 := nat_lit 1070837186802058894141030400

noncomputable def ep1101 := nat_lit 40231241651651103874200789874188392360775642161748864888370242927270730343861002379443347403948630877026069125353994516181305916390199401146594099329425593050045819285761

noncomputable def ep1102 := nat_lit 1723989524678609869184368353634558086375647288945605880257499904391989104065417411410730399287089189440146844853530817917959165259045966673531664948206962296697359276441600

noncomputable def ep1103 := nat_lit 631660434800245446997223479428600769828250898221216357107143159845051025849459816866429914575622117549949093245194075728806794520387923785503556527208180815130881

noncomputable def ep1104 := nat_lit 244015321452984941790061243675387562541957967797188360867910684758926224642951105042635790902162346211391377695390186793673850753225005145667204221986988764358926644441345

noncomputable def ep1105 := nat_lit 156883046745753498095777520180744785860183903294050135103432491299671008469952984438376466335125116239053362881671304430534284038573182967291381510286833568999459694156185600

noncomputable def ep1106 := BSN.cos_dyadic_bound_f 30435023370559 35184372088832 4 3 17179869184 5698887923 ep1101 ep1102 ep1103 ep1104 ep1105 ep1103 11143351091 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 30435023370559) (BSN.cosEvenQ 35184372088832) 0 3 ep1101 ep1102 ep1103 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 30435023370559) (BSN.cosOddQ 35184372088832) 0 3 ep1104 ep1105 ep1103 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz442 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 1491664573125) (@Nat.cast Real Real.instNatCast 8589934592))

noncomputable def ep1107 := @Enclosure.Real.IsNear.cos_image qz204 qz442 Bool.false 1491664573125 8589934592 199 8589934592 Bool.true 11143351091 17179869184 1 2846664016 (@Enclosure.Real.IsNear.recentre' qz204 Bool.false 782061835714775872269 4503599627370496000 4112597621251046903 ep1092 1491664573125 8589934592 199 8589934592 (ep1099 rfl) rfl) (Enclosure.sfrac_false_div 1491664573125 8589934592) (BSN.cos_reduce2 qz442 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast ep1100) (@Nat.cast Real Real.instNatCast ep940)) 226375608064910080 72057594037927936 Bool.false 11143351091 17179869184 27 1000000000000000 5693328032 2846664016 (BSN.sin_reduce_arg_pos_rat_q2 1491664573125 8589934592 226375608064910080 72057594037927936 27 ep1100 ep940 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 11143351091 17179869184 ep1100 ep940 30435023370559 35184372088832 5698887923 5693328032 (ep1106 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1108 := nat_lit 3977003424548989524423998783475493377255503861820661088042475742379414974091186125854496342483567849911868061185

noncomputable def ep1109 := nat_lit 852239132436968601736534718962914620494087683347851114682261747749608011033589111964107092533864866956228564090880

noncomputable def ep1110 := nat_lit 736188648434119186923965724755351814665899550998592173505940110674308789093204950162617436979847187584120321

noncomputable def ep1111 := nat_lit 10414769425530841132903072297929069227969241515019162271830331612719280813151717521604369992558996044798803965441

noncomputable def ep1112 := nat_lit 15624384094677757698503136514320101375724940861377270435841465375409480202282467052675296696454189227530857008332800

noncomputable def ep1113 := BSN.sin_dyadic_bound_f 30435023370559 35184372088832 3 2 17179869184 5698887923 ep1108 ep1109 ep1110 ep1111 ep1112 ep1110 13075688571 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 30435023370559) (BSN.sinEvenQ 35184372088832) 0 2 ep1108 ep1109 ep1110 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 30435023370559) (BSN.sinOddQ 35184372088832) 0 2 ep1111 ep1112 ep1110 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1114 := @Enclosure.Real.IsNear.sin_image qz204 qz442 Bool.false 1491664573125 8589934592 199 8589934592 Bool.true 13075688571 17179869184 1 2846664016 (@Enclosure.Real.IsNear.recentre' qz204 Bool.false 782061835714775872269 4503599627370496000 4112597621251046903 ep1092 1491664573125 8589934592 199 8589934592 (ep1099 rfl) rfl) (Enclosure.sfrac_false_div 1491664573125 8589934592) (BSN.sin_reduce2 qz442 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast ep1100) (@Nat.cast Real Real.instNatCast ep940)) 226375608064910080 72057594037927936 Bool.false 13075688571 17179869184 27 1000000000000000 5693328032 2846664016 (BSN.sin_reduce_arg_pos_rat_q2 1491664573125 8589934592 226375608064910080 72057594037927936 27 ep1100 ep940 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 13075688571 17179869184 ep1100 ep940 30435023370559 35184372088832 5698887923 5693328032 (ep1113 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1115 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz439 qz201) (@HMul.hMul Real Real Real qz0 qz439 qz202) Bool.true 18646069090410481 295147905179352825856 2102869809730351415 ep1041 Bool.false 21879432004657161 295147905179352825856 2446664532923108895 ep1041 (@Enclosure.Real.IsNear.mulLit_ft qz439 qz201 1673291 17179869184 1 17179869184 11143351091 17179869184 35942254611 1528291106427502592 18646069090410481 295147905179352825856 2102869809730351415 ep1041 (@Enclosure.Real.IsNear.recentre' qz439 Bool.false 1673291 17179869184 1 17179869184 1673291 17179869184 1 17179869184 (ep1091 rfl rfl) rfl) (@Enclosure.Real.IsNear.recentre' qz201 Bool.true 11143351091 17179869184 575076073776 24452657702840041472 11143351091 17179869184 35942254611 1528291106427502592 (ep1107 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz439 qz202 1673291 17179869184 1 17179869184 13075688571 17179869184 35942254611 1528291106427502592 21879432004657161 295147905179352825856 2446664532923108895 ep1041 (@Enclosure.Real.IsNear.recentre' qz439 Bool.false 1673291 17179869184 1 17179869184 1673291 17179869184 1 17179869184 (ep1091 rfl rfl) rfl) (@Enclosure.Real.IsNear.neg qz205 Bool.true 13075688571 17179869184 35942254611 1528291106427502592 (@Enclosure.Real.IsNear.recentre' qz205 Bool.true 13075688571 17179869184 575076073776 24452657702840041472 13075688571 17179869184 35942254611 1528291106427502592 (ep1114 rfl rfl) rfl)) rfl)

noncomputable def ep1116 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz136 (@ascPochhammer Complex Complex.instSemiring 3)))) qz247 284524945367401 720000000000 0 1 21879432004657161 295147905179352825856 2446664532923108895 ep1041 ep1035

noncomputable def ep1117 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz136 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 12988064803 480000000 0 1 Bool.false 284524945367401 720000000000 0 1 ep1087

noncomputable def ep1118 := @Enclosure.Complex.IsNear.im_isNear qz237 Bool.true 18646069090410481 295147905179352825856 2102869809730351415 ep1041 Bool.false 21879432004657161 295147905179352825856 2446664532923108895 ep1041

noncomputable def ep1119 := nat_lit 94723826909773134955334761

noncomputable def ep1120 := nat_lit 47223664828696452136960000000

noncomputable def ep1121 := nat_lit 43234608850077639924470371

noncomputable def ep1122 := nat_lit 34293343717218110838048555008000000

noncomputable def ep1123 := nat_lit 5305271789265826563834446129881

noncomputable def ep1124 := nat_lit 119663783545657034429657603044483

noncomputable def ep1125 := @Enclosure.Real.IsNear.addLit_ft_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz136 (@ascPochhammer Complex Complex.instSemiring 3)))) qz247) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz136 (@ascPochhammer Complex Complex.instSemiring 3)))) qz246) ep1119 ep1120 ep1121 ep1122 ep1123 ep1026 ep1124

noncomputable def ep1126 := nat_lit 230404948661674481115236157512130659740253830260981760000000

noncomputable def ep1127 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz136 (@ascPochhammer Complex Complex.instSemiring 3)))) qz247 12988064803 480000000 0 1 21879432004657161 295147905179352825856 2446664532923108895 ep1041 ep1119

noncomputable def ep1128 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz136 (@ascPochhammer Complex Complex.instSemiring 3)))) qz246 284524945367401 720000000000 0 1 18646069090410481 295147905179352825856 2102869809730351415 ep1041 ep1123

noncomputable abbrev qz443 := (@ep1090 ep1041 (BSN.cpow_neg_s_sub_mk qz145 65801 1000 14 3 105413504 qz146 rfl EMRow15.d18) ep1115)

noncomputable def ep1129 := ep1030 (@ep1038 ep1039 ep1040 ep1020 ep1021 ep1022 ep1023 (@ep1042 ep1032 ep1033 ep1034 ep1088 (ep1089 qz443) rfl) (@ep1116 ep1036 ep1037 ep1039 ep1117 (ep1118 qz443) rfl) rfl rfl) (@ep1125 ep1029 ep1126 ep1025 ep1026 ep1027 ep1029 (@ep1127 ep1120 ep1121 ep1122 ep1088 (ep1118 qz443) rfl) (@ep1128 ep1026 ep1124 ep1029 ep1117 (ep1089 qz443) rfl) rfl rfl)

noncomputable def ep1130 := @Enclosure.Real.IsNear.mulLit_tt (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz136 (@ascPochhammer Complex Complex.instSemiring 3))) qz237)) (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz136 (@ascPochhammer Complex Complex.instSemiring 3))) qz237)) ep1025 ep1026 ep1027 ep1029 ep1025 ep1026 ep1027

noncomputable def ep1131 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz136 (@ascPochhammer Complex Complex.instSemiring 3))) qz237) Bool.true ep1020 ep1021 ep1022 ep1023 Bool.true ep1025 ep1026 ep1027

noncomputable def ep1132 := @ep990 3271093098639541 4503599627370496 16036401189 31525197391593472 (@ep991 1 1835008 (ep992 (@ep993 524288 1 524288 (ep994 (@ep995 17368086404 4342021601 1000000 0 1 (ep999 rfl) (ep1002 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) (Enclosure.Real.IsNear.const Bool.false 2 7) rfl) (@ep1003 445 17179869184 (BSN.norm_eq_sqrt_mul_add (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz136 (@ascPochhammer Complex Complex.instSemiring 3))) qz237)) (@ep1004 445 17179869184 662788609 17179869184 445 17179869184 (@ep1009 331394082 331394527 8589934592 (@ep1015 ep1016 ep1017 ep1018 ep1019 ep1005 ep1006 ep1007 ep1008 (@ep1024 ep1023 ep1010 ep1011 ep1012 ep1013 (@ep1028 ep1029 ep1129) (@ep1028 ep1029 ep1129) rfl) (@ep1130 ep1029 ep1014 ep1016 ep1017 ep1018 (@ep1131 ep1029 ep1129) (@ep1131 ep1029 ep1129) rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl

theorem EMRow15.d19 : Enclosure.Real.IsNear (@HAdd.hAdd Real Real Real qz87 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz136 1 14))) (@HMul.hMul Real Real Real qz0 qz236 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz136 (@ascPochhammer Complex Complex.instSemiring 3))) qz237)))) Bool.false 10041618054763039 13510798882111488 62228222292967 851180329573023744 := ep988 (ep989 ep1132) rfl rfl

noncomputable def EMRow15.d20 := fun (I J : @NonemptyInterval Real Real.instLE) => @LE.le Real Real.instLE (@Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE I)) (@Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE J))

noncomputable abbrev qz444 := (EMRow15.d3 qz453 qz465 (@Enclosure.dec_le_dec qz453 qz465 63102 1000 65801 1000 (@Eq.refl Real qz453) (@Eq.refl Real qz465) rfl rfl rfl) 13 14 1 1)

noncomputable abbrev qz258 := qz444

noncomputable def ep1133 := @Zeta.Certificates.ZIntervalEM.Certificate.mk qz258 (@Enclosure.dec_nonneg qz17 63102 1000 qz18) (@Enclosure.pos_of_ble 1 rfl) (@Enclosure.pos_of_ble 13 rfl)

noncomputable abbrev qz259 := (Zeta.Certificates.ZIntervalEM.fstVal qz444)

noncomputable def ep1134 := @Enclosure.Real.IsNear.neg_val qz259 ep158 ep159

noncomputable def ep1135 := @Enclosure.Real.IsNear.of_eq qz259 (hardyZApproximantEM 1 13 qz17) Bool.true

noncomputable abbrev qz260 := (Zeta.Certificates.ZIntervalEM.sndVal qz444)

noncomputable def ep1136 := BSN.mul_neg_of_neg_pos_r qz259 qz260 (@ep1134 ep160 ep161 (@ep1135 ep158 ep159 ep160 ep161 (@Eq.refl Real (hardyZApproximantEM 1 13 qz17)) EMRow15.d9) rfl rfl rfl)

noncomputable def ep1137 := @Enclosure.Real.IsNear.pos_val qz260 ep525 ep526

noncomputable def ep1138 := @Enclosure.Real.IsNear.of_eq qz260 (hardyZApproximantEM 1 14 qz145) Bool.false

noncomputable def ep1139 := BSN.gt_trans_le (@Norm.norm Real Real.norm qz259) (BSN.hardyZErrorBoundStrong 1 13 qz17)

noncomputable def ep1140 := @Enclosure.norm_gt_of_isNear qz259 (BSN.hardyZErrorBoundStrong 1 13 qz17) Bool.true

noncomputable def ep1141 := @Enclosure.Real.IsNear.of_eq (BSN.hardyZErrorBoundStrong 1 13 qz17) (@HAdd.hAdd Real Real Real qz87 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz6 1 13))) (@HMul.hMul Real Real Real qz0 qz210 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz213)))) Bool.false 726385913097427 844424930131968 3676818645961 53198770598313984 (@Eq.refl Real (@HAdd.hAdd Real Real Real qz87 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz6 1 13))) (@HMul.hMul Real Real Real qz0 qz210 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz213)))))

noncomputable def ep1142 := BSN.gt_trans_le (@Norm.norm Real Real.norm qz260) (BSN.hardyZErrorBoundStrong 1 14 qz145)

noncomputable def ep1143 := @Enclosure.norm_gt_of_isNear qz260 (BSN.hardyZErrorBoundStrong 1 14 qz145) Bool.false

noncomputable def ep1144 := @Enclosure.Real.IsNear.of_eq (BSN.hardyZErrorBoundStrong 1 14 qz145) (@HAdd.hAdd Real Real Real qz87 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz136 1 14))) (@HMul.hMul Real Real Real qz0 qz236 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz136 (@ascPochhammer Complex Complex.instSemiring 3))) qz237)))) Bool.false 10041618054763039 13510798882111488 62228222292967 851180329573023744 (@Eq.refl Real (@HAdd.hAdd Real Real Real qz87 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz136 1 14))) (@HMul.hMul Real Real Real qz0 qz236 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz136 (@ascPochhammer Complex Complex.instSemiring 3))) qz237)))))

noncomputable def ep1145 := @List.cons EMRow15.d0 (@PSigma.mk Zeta.Certificates.ZIntervalEM Zeta.Certificates.ZIntervalEM.Certificate qz258 (ep1133 (@Enclosure.pos_of_ble 1 rfl) (@Enclosure.pos_of_ble 14 rfl) (ep1136 (@ep1137 ep527 ep528 (@ep1138 ep525 ep526 ep527 ep528 (@Eq.refl Real (hardyZApproximantEM 1 14 qz145)) EMRow15.d12) rfl rfl rfl)) (ep1139 (hardyZErrorBoundEM 1 13 qz17) (BSN.hardyZErrorBoundEM_le_strong 1 13 qz17 rfl) (@ep1140 Bool.false ep158 ep159 ep160 ep161 726385913097427 844424930131968 3676818645961 53198770598313984 (@ep1135 ep158 ep159 ep160 ep161 (@Eq.refl Real (hardyZApproximantEM 1 13 qz17)) EMRow15.d9) (ep1141 EMRow15.d17) rfl rfl rfl rfl rfl)) (ep1142 (hardyZErrorBoundEM 1 14 qz145) (BSN.hardyZErrorBoundEM_le_strong 1 14 qz145 rfl) (@ep1143 Bool.false ep525 ep526 ep527 ep528 10041618054763039 13510798882111488 62228222292967 851180329573023744 (@ep1138 ep525 ep526 ep527 ep528 (@Eq.refl Real (hardyZApproximantEM 1 14 qz145)) EMRow15.d12) (ep1144 EMRow15.d19) rfl rfl rfl rfl rfl)))) (@List.nil EMRow15.d0)

noncomputable abbrev qz445 := (@Enclosure.dec_le_dec qz453 qz465 63102 1000 65801 1000 (@Eq.refl Real qz453) (@Eq.refl Real qz465) rfl rfl rfl)

noncomputable abbrev qz261 := (Zeta.Certificates.CertifiedZeroIntervals.intervals (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedEM ep1145 (@List.IsChain.singleton EMRow15.d1 EMRow15.d20 (EMRow15.d2 qz276 qz376 qz445))))

noncomputable abbrev qz446 := (@NonemptyInterval Real Real.instLE)

noncomputable def ep1146 := And (@Eq (Option Real) (@Option.map qz446 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz446 qz261)) (@Option.some Real qz17))

noncomputable def ep1147 := ep1146 (@Eq (Option Real) (@Option.map qz446 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz446 qz261)) (@Option.some Real qz145))

noncomputable def ep1148 := @And.intro (@Eq Nat (@List.length qz446 qz261) 1) ep1147

noncomputable def ep1149 := @And.intro (@Eq (Option Real) (@Option.map qz446 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz446 qz261)) (@Option.some Real qz17))

noncomputable def ep1150 := @ep1149 (@Eq (Option Real) (@Option.map qz446 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz446 qz261)) (@Option.some Real qz145))

noncomputable abbrev qz262 := (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedEM ep1145 (@List.IsChain.singleton EMRow15.d1 EMRow15.d20 (EMRow15.d2 qz276 qz376 qz445)))

theorem EMRow15.d21 : Zeta.Certificates.BatchSpec 1 63102 1000 65801 1000 := @Exists.intro Zeta.Certificates.CertifiedZeroIntervals (fun (C : Zeta.Certificates.CertifiedZeroIntervals) => And (@Eq Nat (@List.length qz446 (Zeta.Certificates.CertifiedZeroIntervals.intervals C)) 1) (And (@Eq (Option Real) (@Option.map qz446 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz446 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz17)) (@Eq (Option Real) (@Option.map qz446 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz446 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz145)))) qz262 (ep1148 (@Eq.refl Nat 1) (ep1150 (@Eq.refl (Option Real) (@Option.some Real qz17)) (@Eq.refl (Option Real) (@Option.some Real qz145))))

theorem solution : Zeta.Certificates.BatchSpec 1 63102 1000 65801 1000 := EMRow15.d21
#print axioms solution
#check solution
