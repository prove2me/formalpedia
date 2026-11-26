-- Prove2me | solution 1 for RHHeight1000.em_main_0031_0031
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-20T09:01:40.313875+00:00
-- url     : https://prove2.me/submissions/a6e70755-c670-43c4-865e-d86850bc740f

import Definitions.Def_RHT1000_Support_20261118_S005
/- Copyright (c) 2026 Salvatore Mercuri, Bhavik Mehta.
Apache 2.0 license; see the source project LICENSE. -/
set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable def EMRow31.d0 := @PSigma Zeta.Certificates.ZIntervalEM fun (I : Zeta.Certificates.ZIntervalEM) => Zeta.Certificates.ZIntervalEM.Certificate I

noncomputable def EMRow31.d1 := @NonemptyInterval Real Real.instLE

noncomputable def EMRow31.d2 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @NonemptyInterval.mk Real Real.instLE (@Prod.mk Real Real a b) h

noncomputable def EMRow31.d3 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) (fc sc fb sb : Nat) => Zeta.Certificates.ZIntervalEM.mk (EMRow31.d2 a b h) fc sc fb sb

noncomputable def ep0 := nat_lit 26986075409044028275299783

noncomputable def ep1 := nat_lit 4294967296000000000000000

noncomputable def ep2 := nat_lit 26986075409044045455168967

noncomputable abbrev qz268 := (@instHMul Real Real.instMul)

noncomputable abbrev qz0 := qz268

noncomputable abbrev qz269 := (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 2 1) Real.pi)

noncomputable def ep3 := @BSN.isNear_log_image_fff qz269 884279719003555 140737488355328 1 500000000000000 ep0 ep1 ep2 ep1 4138529546116343 2251799813685248 250000000133689 66844500000000000000 4138529546116343 2251799813685248 250000000133689 66844500000000000000 963576 524288

noncomputable abbrev qz270 := (@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 2 1) Real.pi 2 1 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 140737488355328 1 500000000000000 (Enclosure.Real.IsNear.const Bool.false 2 1) BSN.pi_near_15 rfl)

noncomputable def ep4 := @ep3 3 524288 qz270 rfl rfl rfl rfl

noncomputable def ep5 := nat_lit 53972150818088056550599566

noncomputable def ep6 := nat_lit 34359738368000000000000000

noncomputable def ep7 := nat_lit 9806206225044028275299783

noncomputable def ep8 := nat_lit 44165944593044028275299783

noncomputable def ep9 := nat_lit 13681445815609410487519367394620474863599256634174726093703677122907123617368241606644861540940610176751640793056574796245399519365549113997355475306157239709119582688278313060810592403844863400465080549957745

noncomputable def ep10 := nat_lit 231714499556395493334623298703961145503103241611736774613091488581016477543539392410113701224645713379230392133956226737605624599560350113120270717249177907454870984269546186598262646369758174842349131395304

noncomputable def ep11 := nat_lit 8978369550011295664474073352761810093897501552430546263638635096022803738134167562509900960712119243631997923545019968443113540909076206607473711060286601587364321108377403290080403445693385008949995305

noncomputable def ep12 := BSN.log_dyadic_bound ep7 ep8 5 4 ep9 1048576 267378 ep10 ep11 473518 ep5 ep6 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP ep7) (BSN.artanhQ ep8) 0 4 ep10 ep9 ep11 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz271 := (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))

noncomputable abbrev qz1 := qz271

noncomputable def ep13 := ep4 rfl rfl rfl rfl (BSN.isNear_log_sfrac ep0 ep1 4138529546116343 2251799813685248 250000000133689 66844500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep0) (@Nat.cast Real Real.instNatCast ep1))) Bool.false 69433004117575847641088 37778931862957161709568 1000000000534756 267378000000000000000 4138529546116343 2251799813685248 250000000133689 66844500000000000000 (BSN.log_rat_reduce_isNear ep0 ep1 2 ep5 ep6 473518 1048576 24973259072661432 36028797018963968 267378 1000000000000000 rfl rfl rfl rfl (ep12 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep14 := nat_lit 53972150818088090910337934

noncomputable def ep15 := nat_lit 9806206225044045455168967

noncomputable def ep16 := nat_lit 44165944593044045455168967

noncomputable def ep17 := nat_lit 13681445815609453062485491347592146866046743284321690683909457683007658987562290830600045658905080811372395010565947827677605470036294121079488508864180301737865471494204890974265645509835068840465080549957745

noncomputable def ep18 := nat_lit 231714499556396865510889920206523150079811393376960301632499817942333196803513131357563499488546302200815366867712007119763002650772307103678175657719139104636874731038771518520299266622696414842349131395304

noncomputable def ep19 := nat_lit 8978369550011421500876706511871067098718760264493934208903156435737864998391937547068187824077011975074541700434630537294838404525415248443919841847024664017658842168336182958576672102333385008949995305

noncomputable def ep20 := BSN.log_dyadic_bound ep15 ep16 5 4 ep17 1048576 267378 ep18 ep19 473518 ep14 ep6 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP ep15) (BSN.artanhQ ep16) 0 4 ep18 ep17 ep19 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep21 := ep13 (BSN.isNear_log_sfrac ep2 ep1 4138529546116343 2251799813685248 250000000133689 66844500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep2) (@Nat.cast Real Real.instNatCast ep1))) Bool.false 69433004117575847641088 37778931862957161709568 1000000000534756 267378000000000000000 4138529546116343 2251799813685248 250000000133689 66844500000000000000 (BSN.log_rat_reduce_isNear ep2 ep1 2 ep14 ep6 473518 1048576 24973259072661432 36028797018963968 267378 1000000000000000 rfl rfl rfl rfl (ep20 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable abbrev qz2 := (Real.log (@HMul.hMul Real Real Real qz268 (2 : Real) Real.pi))

theorem EMRow31.d4 : Enclosure.Real.IsNear qz2 Bool.false 120447 65536 3 524288 := @Enclosure.Real.IsNear.of_eq qz2 (Real.log qz269) Bool.false 120447 65536 3 524288 BSN.log_two_pi_eq (@Enclosure.Real.IsNear.recentre' (Real.log qz269) Bool.false 963576 524288 3 524288 120447 65536 3 524288 (ep21 rfl rfl rfl rfl rfl rfl rfl rfl) rfl)

noncomputable def ep22 := nat_lit 8589934592000000000000000

noncomputable def ep23 := @BSN.isNear_log_image_fff Real.pi 226375608064910080 72057594037927936 1 1000000000000000 ep0 ep22 ep2 ep22 1200336 1048576 1 267378 1200336 1048576 1 267378 600168 524288 2 524288 BSN.pi_near_15 rfl rfl rfl

noncomputable def ep24 := nat_lit 17179869184000000000000000

noncomputable def ep25 := nat_lit 18396140817044028275299783

noncomputable def ep26 := nat_lit 35576010001044028275299783

noncomputable def ep27 := nat_lit 145019262663961446558303139663424756232419223153299357158415217874016130572233056993847515999529612750616182853355499335896178729185698845314776375864537073527142908641610750276034469165612529925303649396973267518946591078603565291376312767403717761600170009932259137778521478520425507632472584532570900560707662248426541531715360699177249902784721815296292248142738824858695953661559845440650653128788875447728828657762006237171740033404723254477174341920697506370253193455781322964835857351124092897592956162654178130575

noncomputable def ep28 := nat_lit 15500762873619990602332184736899274490522931101512051618692838888825382235673431503644115344741331161500627469184702974962114537943617674254904297224139410345221262767191485292268260077615645253784097850065864022184521411511133693085443040736512010941548648374196772723338837137976260321103066698629790037694560548409922339907589559883712609967105556007429010014773911317423638534096849366294542840133852248768895750397896505791271178551667935288585787166713880920071720072716082683081155281219708172458141800988558163320

noncomputable def ep29 := nat_lit 12900190794487083783367107939442176642390171280542213571554777169279725287102813254708993369099729304728646904879886535518616983985412662170766446331701281703998252143668221340329975389245922410714088123244705567402747658401492589451585970559635763980329972215329212888079422466283203384882259392047898400615815810081169907384366653346471604103896809335921621947903075223769953790093549808584241881353287841076643853121427928248525828402335494512605306631304432120211393210317325496757155861061354331245840675149075

noncomputable def ep30 := BSN.log_dyadic_bound ep25 ep26 11 10 ep27 1048576 267378 ep28 ep29 1200336 ep5 ep24 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base10 (BSN.artanhP ep25) (BSN.artanhQ ep26) 0 10 ep28 ep27 ep29 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep31 := nat_lit 18396140817044045455168967

noncomputable def ep32 := nat_lit 35576010001044045455168967

noncomputable def ep33 := nat_lit 145019262663962847171784895425483977818796535899227200426399035286881207006285364467913811844950531107314785650583974625982406238691319033447632878979985852280879486690814033867010958364699188952871572448188560932645032521756218245629809291975913196623825614492380080480004685076434733043183791438169545293975334857826316990371107134320667652578346815517853870648072772035977941843998949310557583393428557296298890786965786350523173236912472938174255438182435383147950274229549088258679583524155427309880956162654178130575

noncomputable def ep34 := nat_lit 15500762873620157189619721156942591192100275120160672416764593300158228469749443299607348495591439275767946573253526107895503597951484257520435868240203420954375895980141891044871083424251900562230440202302413072793440172565998181227591194192658878334739610458454844032013325963992941389843551995646587189684848765634635122388286241104146031552341815777883628509454807838726994150833304950745987647656768534710890974432620160470644835720379148964170536679305861738540146791997074363921127776563807649880221800988558163320

noncomputable def ep35 := nat_lit 12900190794487324729109480814509220959173684627296055849229843377126536688487849343376525559792931631054411655715865486295286288812423905434305314401904993536755333953308594664509631000767632482919425633906965368325056855874260596615770736441041599390097968820060635361729170158825410327022636428624381203910573184452046894301676992229743752846881064485858738985580654099214803581683226335297196686880535448467637789069028262446657986458573827723305156755787640135484017403116612632808333639900906331245840675149075

noncomputable def ep36 := BSN.log_dyadic_bound ep31 ep32 11 10 ep33 1048576 267378 ep34 ep35 1200336 ep14 ep24 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base10 (BSN.artanhP ep31) (BSN.artanhQ ep32) 0 10 ep34 ep33 ep35 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep37 := @Enclosure.Real.IsNear.recentre' (Real.log Real.pi) Bool.false 600168 524288 2 524288 75021 65536 1 262144 (ep23 rfl rfl rfl rfl rfl (BSN.isNear_log_sfrac ep0 ep22 1200336 1048576 1 267378 Bool.false (BSN.logfrac_isNear ep5 ep24 1 ep0 ep22 1200336 1048576 267378 rfl rfl rfl (ep30 rfl))) (BSN.isNear_log_sfrac ep2 ep22 1200336 1048576 1 267378 Bool.false (BSN.logfrac_isNear ep14 ep24 1 ep2 ep22 1200336 1048576 267378 rfl rfl rfl (ep36 rfl))) rfl rfl rfl rfl rfl rfl rfl rfl) rfl

theorem EMRow31.d5 : Enclosure.Real.IsNear (Real.log Real.pi) Bool.false 75021 65536 1 262144 := ep37

noncomputable abbrev qz602 := (@HAdd.hAdd Complex Complex Complex (@instHAdd Complex Complex.instAdd) (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (2 : Complex)) (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul) Complex.I ↑(Enclosure.sfrac Bool.false 102256 1000)))

noncomputable abbrev qz533 := qz602

noncomputable abbrev qz272 := qz533

noncomputable abbrev qz3 := (BSN.headSumC qz272 9)

noncomputable abbrev qz603 := (@instHAdd Complex Complex.instAdd)

noncomputable abbrev qz534 := qz603

noncomputable abbrev qz273 := qz534

noncomputable abbrev qz4 := qz273

noncomputable abbrev qz5 := qz272

noncomputable abbrev qz535 := (@instHPow Complex Complex Complex.instPow)

noncomputable abbrev qz274 := qz535

noncomputable abbrev qz6 := qz274

noncomputable abbrev qz536 := (@Neg.neg Complex Complex.instNeg qz602)

noncomputable abbrev qz275 := qz536

noncomputable abbrev qz7 := qz275

noncomputable abbrev qz276 := (@Nat.cast Complex Complex.instNatCast 8)

noncomputable def ep38 := @Enclosure.Complex.IsNear.of_eq qz3 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 8) (@HPow.hPow Complex Complex Complex qz6 qz276 qz7)) Bool.false 662496782227 549755813888 1998687009357 765586510446592 Bool.true 33937459585 137438953472 63999322319677 24498768334290944

noncomputable def ep39 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 8) (@HPow.hPow Complex Complex Complex qz6 qz276 qz7) Bool.false 1112650407029 1099511627776 114494701451955 48997536668581888 Bool.true 149278783103 274877906944 57281880834439 24498768334290944 Bool.false

noncomputable def ep40 := nat_lit 1456845830845541912674304

noncomputable abbrev qz277 := (@Nat.cast Complex Complex.instNatCast 7)

noncomputable def ep41 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 8) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 7) (@HPow.hPow Complex Complex Complex qz6 qz277 qz7)) Bool.false 1112650407029 1099511627776 114494701451955 48997536668581888 Bool.true 149278783103 274877906944 57281880834439 24498768334290944

noncomputable def ep42 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 7) (@HPow.hPow Complex Complex Complex qz6 qz277 qz7) Bool.false 1315637767579 1099511627776 300453559823161 146992610005745664 Bool.true 59984036307 68719476736 75151722435649 36748152501436416 Bool.true

noncomputable abbrev qz278 := (@Nat.cast Complex Complex.instNatCast 6)

noncomputable def ep43 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 7) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 6) (@HPow.hPow Complex Complex Complex qz6 qz278 qz7)) Bool.false 1315637767579 1099511627776 300453559823161 146992610005745664 Bool.true 59984036307 68719476736 75151722435649 36748152501436416

noncomputable def ep44 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 6) (@HPow.hPow Complex Complex Complex qz6 qz278 qz7) Bool.false 268815604855 274877906944 330695648139 191396627611648 Bool.true 580657938225 1099511627776 84694756058713 48997536668581888 Bool.false

noncomputable abbrev qz279 := (@Nat.cast Complex Complex.instNatCast 5)

noncomputable def ep45 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 6) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 5) (@HPow.hPow Complex Complex Complex qz6 qz279 qz7)) Bool.false 268815604855 274877906944 330695648139 191396627611648 Bool.true 580657938225 1099511627776 84694756058713 48997536668581888

noncomputable def ep46 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 5) (@HPow.hPow Complex Complex Complex qz6 qz279 qz7) Bool.false 451223471279 549755813888 50772928845901 36748152501436416 Bool.true 120310926191 1099511627776 203119753576507 146992610005745664 Bool.false

noncomputable abbrev qz280 := (@Nat.cast Complex Complex.instNatCast 4)

noncomputable def ep47 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 5) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 4) (@HPow.hPow Complex Complex Complex qz6 qz280 qz7)) Bool.false 451223471279 549755813888 50772928845901 36748152501436416 Bool.true 120310926191 1099511627776 203119753576507 146992610005745664

noncomputable def ep48 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 4) (@HPow.hPow Complex Complex Complex qz6 qz280 qz7) Bool.false 1411927553391 1099511627776 146128540719869 146992610005745664 Bool.true 81713054245 274877906944 18279228252655 18374076250718208 Bool.true

noncomputable abbrev qz537 := (@Nat.cast Complex Complex.instNatCast 3)

noncomputable abbrev qz281 := qz537

noncomputable abbrev qz8 := qz281

noncomputable def ep49 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 4) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 3) (@HPow.hPow Complex Complex Complex qz6 qz8 qz7)) Bool.false 1411927553391 1099511627776 146128540719869 146992610005745664 Bool.true 81713054245 274877906944 18279228252655 18374076250718208

noncomputable def ep50 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 3) (@HPow.hPow Complex Complex Complex qz6 qz8 qz7) Bool.false 475394550483 549755813888 13400211842401 24498768334290944 Bool.true 190778595865 274877906944 6709337480873 12249384167145472 Bool.false

noncomputable abbrev qz538 := (@Nat.cast Complex Complex.instNatCast 2)

noncomputable abbrev qz282 := qz538

noncomputable abbrev qz9 := qz282

noncomputable def ep51 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 3) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 2) (@HPow.hPow Complex Complex Complex qz6 qz9 qz7)) Bool.false 475394550483 549755813888 13400211842401 24498768334290944 Bool.true 190778595865 274877906944 6709337480873 12249384167145472

noncomputable def ep52 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 2) (@HPow.hPow Complex Complex Complex qz6 qz9 qz7) Bool.false 1 1 0 1 Bool.false 0 1 0 1 Bool.true

noncomputable abbrev qz283 := (Enclosure.sfrac Bool.false 0 1)

noncomputable abbrev qz10 := qz283

noncomputable def ep53 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 2) (Complex.mk (Enclosure.sfrac Bool.false 1 1) qz10) Bool.false 1 1 0 1 Bool.false 0 1 0 1 (BSN.head_sum_c_two qz5)

noncomputable abbrev qz539 := (@Nat.cast Real Real.instNatCast 2)

noncomputable abbrev qz11 := (@Inv.inv Real Real.instInv (Real.sqrt qz539))

noncomputable abbrev qz604 := (Enclosure.sfrac Bool.false 102256 1000)

noncomputable abbrev qz540 := qz604

noncomputable abbrev qz284 := qz540

noncomputable abbrev qz285 := (Real.log (Enclosure.sfrac Bool.false 2 1))

noncomputable abbrev qz12 := (@HMul.hMul Real Real Real qz268 qz284 qz285)

noncomputable abbrev qz13 := qz284

noncomputable abbrev qz286 := (@Eq.refl Real qz540)

noncomputable abbrev qz14 := qz286

noncomputable def ep54 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz9 qz7) (Complex.mk (@HMul.hMul Real Real Real qz0 qz11 (Real.cos qz12)) (@HMul.hMul Real Real Real qz0 qz11 (@Neg.neg Real Real.instNeg (Real.sin qz12)))) Bool.true 74361263405 549755813888 13400211842401 24498768334290944 Bool.true 190778595865 274877906944 6709337480873 12249384167145472 (BSN.cpow_neg_s_mk qz13 102256 1000 2 qz14 rfl)

noncomputable abbrev qz15 := (@Nat.cast Real Real.instNatCast 1)

noncomputable def ep55 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz539) 1482911 1048576 1 1048576 370727 370728 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz539) (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz539 qz15)) Bool.false 1482911 1048576 1 1048576 (BSN.sqrt_natCast_div_one 2) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz539 qz15)) Bool.false 1482911 1048576 1 1048576 1482911 1048576 1 1048576 (BSN.sqrt_enclosure 2 1 741455 741456 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep56 := BSN.log_dyadic_bound 1 3 6 5 613814355 524288 133689 24381081 945 363408 4 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 1) (BSN.artanhQ 3) 0 5 24381081 613814355 945 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep57 := nat_lit 29189716367770463968293383701528576

noncomputable def ep58 := nat_lit 2552117751907038475975309555738261585920

noncomputable def ep59 := nat_lit 17864824263349269331827166890167831101440

noncomputable abbrev qz287 := (BSN.sinEvenQ 2147483648)

noncomputable abbrev qz288 := (BSN.sinOddQ 2147483648)

noncomputable def ep60 := BSN.sin_dyadic_bound_f 413340032 2147483648 2 1 1048576 267640 ep57 ep58 ep57 ep57 ep59 ep57 200582 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 413340032) qz287 0 1 ep57 ep58 ep57 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 413340032) qz288 0 1 ep57 ep59 ep57 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz16 := (Enclosure.Real.IsNear.const Bool.false 102256 1000)

noncomputable abbrev qz289 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 4645081) (@Nat.cast Real Real.instNatCast 65536))

noncomputable abbrev qz290 := (BSN.isNear_log_sfrac 2 1 363408 524288 1 133689 Bool.false (BSN.logfrac_isNear 4 2 1 2 1 363408 524288 133689 rfl rfl rfl (ep56 rfl)))

noncomputable abbrev qz291 := (@Nat.cast Real Real.instNatCast 9444732965739290427392)

noncomputable def ep61 := @Enclosure.Real.IsNear.cos_image qz12 qz289 Bool.false 4645081 65536 803 1048576 Bool.true 200582 1048576 1 133689 (@Enclosure.Real.IsNear.recentre' qz12 Bool.false 145158783 2048000 12782 16711125 4645081 65536 803 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz13 qz285 102256 1000 0 1 363408 524288 1 133689 145158783 2048000 12782 16711125 qz16 qz290 rfl) rfl) (Enclosure.sfrac_false_div 4645081 65536) (BSN.cos_reduce1 qz289 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 1817888686197054636032) qz291) 226375608064910080 72057594037927936 Bool.false 200582 1048576 11 1000000000000000 267378 133689 (BSN.sin_reduce_arg_pos_rat_q1 4645081 65536 226375608064910080 72057594037927936 11 1817888686197054636032 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 200582 1048576 1817888686197054636032 9444732965739290427392 413340032 2147483648 267640 267378 (ep60 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep62 := nat_lit 510423550381407695195061911147652317184

noncomputable def ep63 := nat_lit 7656353255721115427925928667214784757760

noncomputable abbrev qz292 := (BSN.cosEvenQ 2147483648)

noncomputable abbrev qz293 := (BSN.cosOddQ 2147483648)

noncomputable def ep64 := BSN.cos_dyadic_bound_f 413340032 2147483648 2 1 1048576 267640 ep57 ep62 ep57 ep57 ep63 ep57 1029212 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 413340032) qz292 0 1 ep57 ep62 ep57 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 413340032) qz293 0 1 ep57 ep63 ep57 rfl rfl rfl rfl) rfl rfl

noncomputable def ep65 := @Enclosure.Real.IsNear.sin_image qz12 qz289 Bool.false 4645081 65536 803 1048576 Bool.false 1029212 1048576 1 133689 (@Enclosure.Real.IsNear.recentre' qz12 Bool.false 145158783 2048000 12782 16711125 4645081 65536 803 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz13 qz285 102256 1000 0 1 363408 524288 1 133689 145158783 2048000 12782 16711125 qz16 qz290 rfl) rfl) (Enclosure.sfrac_false_div 4645081 65536) (BSN.sin_reduce1 qz289 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 1817888686197054636032) qz291) 226375608064910080 72057594037927936 Bool.false 1029212 1048576 11 1000000000000000 267378 133689 (BSN.sin_reduce_arg_pos_rat_q1 4645081 65536 226375608064910080 72057594037927936 11 1817888686197054636032 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1029212 1048576 1817888686197054636032 9444732965739290427392 413340032 2147483648 267640 267378 (ep64 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz294 := (@Enclosure.Real.IsNear.recentre' qz11 Bool.false 741455 1048576 1 1048576 741455 1048576 1 1048576 (ep55 rfl rfl) rfl)

noncomputable def ep66 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz11 (Real.cos qz12)) (@HMul.hMul Real Real Real qz0 qz11 (@Neg.neg Real Real.instNeg (Real.sin qz12))) Bool.true 74361263405 549755813888 13400211842401 24498768334290944 Bool.true 190778595865 274877906944 6709337480873 12249384167145472 (@Enclosure.Real.IsNear.mulLit_ft qz11 (Real.cos qz12) 741455 1048576 1 1048576 100291 524288 108400843 140183076864 74361263405 549755813888 13400211842401 24498768334290944 qz294 (@Enclosure.Real.IsNear.recentre' (Real.cos qz12) Bool.true 200582 1048576 108400843 140183076864 100291 524288 108400843 140183076864 (ep61 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz11 (@Neg.neg Real Real.instNeg (Real.sin qz12)) 741455 1048576 1 1048576 257303 262144 108400843 140183076864 190778595865 274877906944 6709337480873 12249384167145472 qz294 (@Enclosure.Real.IsNear.neg (Real.sin qz12) Bool.false 257303 262144 108400843 140183076864 (@Enclosure.Real.IsNear.recentre' (Real.sin qz12) Bool.false 1029212 1048576 108400843 140183076864 257303 262144 108400843 140183076864 (ep65 rfl rfl) rfl)) rfl)

noncomputable abbrev qz295 := (Enclosure.Real.IsNear.const Bool.false 0 1)

noncomputable abbrev qz17 := qz295

noncomputable def ep67 := @ep52 74361263405 549755813888 13400211842401 24498768334290944 Bool.true 190778595865 274877906944 6709337480873 12249384167145472 Bool.false 475394550483 475394550483 549755813888 13400211842401 24498768334290944 Bool.true 190778595865 190778595865 274877906944 6709337480873 12249384167145472 (ep53 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 1) qz10 Bool.false 1 1 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 1) qz17)) (ep54 ep66) rfl rfl

noncomputable abbrev qz296 := (@Nat.cast Real Real.instNatCast 3)

noncomputable abbrev qz18 := (@Inv.inv Real Real.instInv (Real.sqrt qz296))

noncomputable abbrev qz297 := (Real.log (Enclosure.sfrac Bool.false 3 1))

noncomputable abbrev qz19 := (@HMul.hMul Real Real Real qz268 qz284 qz297)

noncomputable def ep68 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz8 qz7) (Complex.mk (@HMul.hMul Real Real Real qz0 qz18 (Real.cos qz19)) (@HMul.hMul Real Real Real qz0 qz18 (@Neg.neg Real Real.instNeg (Real.sin qz19)))) Bool.false 461138452425 1099511627776 65727269665463 146992610005745664 Bool.false 27266385405 68719476736 16430444062691 36748152501436416 (BSN.cpow_neg_s_mk qz13 102256 1000 3 qz14 rfl)

noncomputable def ep69 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz296) 1816187 1048576 1 1048576 302697 302698 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz296) (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz296 qz15)) Bool.false 1816187 1048576 1 1048576 (BSN.sqrt_natCast_div_one 3) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz296 qz15)) Bool.false 1816187 1048576 1 1048576 1816187 1048576 1 1048576 (BSN.sqrt_enclosure 3 1 908093 908094 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep70 := BSN.log_dyadic_bound 1 2 10 9 171633298636800 524288 133689 16925142283965 34459425 575989 3 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base9 (BSN.artanhP 1) (BSN.artanhQ 2) 0 9 16925142283965 171633298636800 34459425 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep71 := nat_lit 9296527135887191270152707341724160000

noncomputable def ep72 := BSN.sin_dyadic_bound_f 1746144520 2147483648 2 1 1048576 267640 ep71 ep58 ep71 ep71 ep59 ep71 761715 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1746144520) qz287 0 1 ep71 ep58 ep71 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1746144520) qz288 0 1 ep71 ep59 ep71 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz20 := (@Nat.cast Real Real.instNatCast 524288)

noncomputable abbrev qz21 := (@Nat.cast Real Real.instNatCast 75557863725914323419136)

noncomputable abbrev qz298 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 58898331) qz20)

noncomputable abbrev qz299 := (BSN.isNear_log_sfrac 3 1 575989 524288 1 133689 Bool.false (BSN.logfrac_isNear 3 1 2 3 1 575989 524288 133689 rfl rfl rfl (ep70 rfl)))

noncomputable def ep73 := @Enclosure.Real.IsNear.cos_image qz19 qz298 Bool.false 58898331 524288 803 1048576 Bool.false 761715 1048576 1 133689 (@Enclosure.Real.IsNear.recentre' qz19 Bool.false 3681145699 32768000 12782 16711125 58898331 524288 803 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz13 qz297 102256 1000 0 1 575989 524288 1 133689 3681145699 32768000 12782 16711125 qz16 qz299 rfl) rfl) (Enclosure.sfrac_false_div 58898331 524288) (BSN.cos_reduce3 qz298 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 61436998538386359713792) qz21) 226375608064910080 72057594037927936 Bool.false 761715 1048576 17 1000000000000000 267378 133689 (BSN.sin_reduce_arg_pos_rat_q3 58898331 524288 226375608064910080 72057594037927936 17 61436998538386359713792 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 761715 1048576 61436998538386359713792 75557863725914323419136 1746144520 2147483648 267640 267378 (ep72 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep74 := nat_lit 332248072500953055813680243947781827846245124420789947129821522010623180800000

noncomputable def ep75 := nat_lit 18237254054877300779212430138868345486890022584838388836214569481246317918289920

noncomputable def ep76 := nat_lit 86425416788286903659606627141939916391071682532382859377641527705600000000

noncomputable def ep77 := nat_lit 996571366669282593633721518589061603705953229897305075670709282976458342400000

noncomputable def ep78 := nat_lit 820676432469478535064559356249075546910051016317727497629655626656084306323046400

noncomputable def ep79 := BSN.cos_dyadic_bound_f 1746144520 2147483648 3 2 1048576 267640 ep74 ep75 ep76 ep77 ep78 ep76 720624 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1746144520) qz292 0 2 ep74 ep75 ep76 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1746144520) qz293 0 2 ep77 ep78 ep76 rfl rfl rfl rfl) rfl rfl

noncomputable def ep80 := @Enclosure.Real.IsNear.sin_image qz19 qz298 Bool.false 58898331 524288 803 1048576 Bool.true 720624 1048576 1 133689 (@Enclosure.Real.IsNear.recentre' qz19 Bool.false 3681145699 32768000 12782 16711125 58898331 524288 803 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz13 qz297 102256 1000 0 1 575989 524288 1 133689 3681145699 32768000 12782 16711125 qz16 qz299 rfl) rfl) (Enclosure.sfrac_false_div 58898331 524288) (BSN.sin_reduce3 qz298 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 61436998538386359713792) qz21) 226375608064910080 72057594037927936 Bool.false 720624 1048576 17 1000000000000000 267378 133689 (BSN.sin_reduce_arg_pos_rat_q3 58898331 524288 226375608064910080 72057594037927936 17 61436998538386359713792 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 720624 1048576 61436998538386359713792 75557863725914323419136 1746144520 2147483648 267640 267378 (ep79 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz300 := (@Enclosure.Real.IsNear.recentre' qz18 Bool.false 605395 1048576 1 1048576 605395 1048576 1 1048576 (ep69 rfl rfl) rfl)

noncomputable def ep81 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz18 (Real.cos qz19)) (@HMul.hMul Real Real Real qz0 qz18 (@Neg.neg Real Real.instNeg (Real.sin qz19))) Bool.false 461138452425 1099511627776 65727269665463 146992610005745664 Bool.false 27266385405 68719476736 16430444062691 36748152501436416 (@Enclosure.Real.IsNear.mulLit_ff qz18 (Real.cos qz19) 605395 1048576 1 1048576 761715 1048576 108400843 140183076864 461138452425 1099511627776 65727269665463 146992610005745664 qz300 (@Enclosure.Real.IsNear.recentre' (Real.cos qz19) Bool.false 761715 1048576 108400843 140183076864 761715 1048576 108400843 140183076864 (ep73 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz18 (@Neg.neg Real Real.instNeg (Real.sin qz19)) 605395 1048576 1 1048576 45039 65536 108400843 140183076864 27266385405 68719476736 16430444062691 36748152501436416 qz300 (@Enclosure.Real.IsNear.neg (Real.sin qz19) Bool.true 45039 65536 108400843 140183076864 (@Enclosure.Real.IsNear.recentre' (Real.sin qz19) Bool.true 720624 1048576 108400843 140183076864 45039 65536 108400843 140183076864 (ep80 rfl rfl) rfl)) rfl)

noncomputable def ep82 := @ep50 461138452425 1099511627776 65727269665463 146992610005745664 Bool.false 27266385405 68719476736 16430444062691 36748152501436416 Bool.false 776215381265361779294208 1411927553391 1099511627776 146128540719869 146992610005745664 Bool.true 5615278330216783544320 81713054245 274877906944 18279228252655 18374076250718208 (ep51 (BSN.head_sum_c_succ qz5 2 3 rfl rfl) (ep67 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep68 ep81) rfl rfl

noncomputable abbrev qz541 := (@Nat.cast Real Real.instNatCast 4)

noncomputable abbrev qz22 := (@Inv.inv Real Real.instInv (Real.sqrt qz541))

noncomputable abbrev qz301 := (Real.log (Enclosure.sfrac Bool.false 4 1))

noncomputable abbrev qz23 := (@HMul.hMul Real Real Real qz268 qz284 qz301)

noncomputable def ep83 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz280 qz7) (Complex.mk (@HMul.hMul Real Real Real qz0 qz22 (Real.cos qz23)) (@HMul.hMul Real Real Real qz0 qz22 (@Neg.neg Real Real.instNeg (Real.sin qz23)))) Bool.true 509480610833 1099511627776 56963174663735 146992610005745664 Bool.false 206541290789 1099511627776 56885927555267 146992610005745664 (BSN.cpow_neg_s_mk qz13 102256 1000 4 qz14 rfl)

noncomputable def ep84 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz541) 2097153 1048576 1 1048576 262143 262144 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz541) (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz541 qz15)) Bool.false 2097153 1048576 1 1048576 (BSN.sqrt_natCast_div_one 4) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz541 qz15)) Bool.false 2097153 1048576 1 1048576 2097153 1048576 1 1048576 (BSN.sqrt_enclosure 4 1 1048576 1048577 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep85 := nat_lit 318077276165597140789031982421875

noncomputable def ep86 := nat_lit 49379992292270016474244603430625

noncomputable def ep87 := nat_lit 20095619060363156210525625

noncomputable def ep88 := BSN.log_dyadic_bound 3 5 14 13 ep85 524288 133689 ep86 ep87 726817 8 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base13 (BSN.artanhP 3) (BSN.artanhQ 5) 0 13 ep86 ep85 ep87 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep89 := nat_lit 467989579688398448495749397443772416

noncomputable def ep90 := BSN.cos_dyadic_bound_f 827101952 2147483648 2 1 1048576 267640 ep89 ep62 ep89 ep89 ep63 ep89 971759 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 827101952) qz292 0 1 ep89 ep62 ep89 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 827101952) qz293 0 1 ep89 ep63 ep89 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz302 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 74321399) qz20)

noncomputable abbrev qz303 := (BSN.isNear_log_sfrac 4 1 726817 524288 1 133689 Bool.false (BSN.logfrac_isNear 8 2 1 4 1 726817 524288 133689 rfl rfl rfl (ep88 rfl)))

noncomputable def ep91 := @Enclosure.Real.IsNear.cos_image qz23 qz302 Bool.false 74321399 524288 803 1048576 Bool.true 971759 1048576 1 133689 (@Enclosure.Real.IsNear.recentre' qz23 Bool.false 4645087447 32768000 12782 16711125 74321399 524288 803 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz13 qz301 102256 1000 0 1 726817 524288 1 133689 4645087447 32768000 12782 16711125 qz16 qz303 rfl) rfl) (Enclosure.sfrac_false_div 74321399 524288) (BSN.cos_reduce2 qz302 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 29101062843524687331328) qz21) 226375608064910080 72057594037927936 Bool.false 971759 1048576 22 1000000000000000 267378 133689 (BSN.sin_reduce_arg_pos_rat_q2 74321399 524288 226375608064910080 72057594037927936 22 29101062843524687331328 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 971759 1048576 29101062843524687331328 75557863725914323419136 827101952 2147483648 267640 267378 (ep90 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep92 := BSN.sin_dyadic_bound_f 827101952 2147483648 2 1 1048576 267640 ep89 ep58 ep89 ep89 ep59 ep89 393947 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 827101952) qz287 0 1 ep89 ep58 ep89 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 827101952) qz288 0 1 ep89 ep59 ep89 rfl rfl rfl rfl) rfl rfl

noncomputable def ep93 := @Enclosure.Real.IsNear.sin_image qz23 qz302 Bool.false 74321399 524288 803 1048576 Bool.true 393947 1048576 1 133689 (@Enclosure.Real.IsNear.recentre' qz23 Bool.false 4645087447 32768000 12782 16711125 74321399 524288 803 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz13 qz301 102256 1000 0 1 726817 524288 1 133689 4645087447 32768000 12782 16711125 qz16 qz303 rfl) rfl) (Enclosure.sfrac_false_div 74321399 524288) (BSN.sin_reduce2 qz302 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 29101062843524687331328) qz21) 226375608064910080 72057594037927936 Bool.false 393947 1048576 22 1000000000000000 267378 133689 (BSN.sin_reduce_arg_pos_rat_q2 74321399 524288 226375608064910080 72057594037927936 22 29101062843524687331328 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 393947 1048576 29101062843524687331328 75557863725914323419136 827101952 2147483648 267640 267378 (ep92 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz304 := (@Enclosure.Real.IsNear.recentre' qz22 Bool.false 524287 1048576 1 1048576 524287 1048576 1 1048576 (ep84 rfl rfl) rfl)

noncomputable def ep94 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz22 (Real.cos qz23)) (@HMul.hMul Real Real Real qz0 qz22 (@Neg.neg Real Real.instNeg (Real.sin qz23))) Bool.true 509480610833 1099511627776 56963174663735 146992610005745664 Bool.false 206541290789 1099511627776 56885927555267 146992610005745664 (@Enclosure.Real.IsNear.mulLit_ft qz22 (Real.cos qz23) 524287 1048576 1 1048576 971759 1048576 108400843 140183076864 509480610833 1099511627776 56963174663735 146992610005745664 qz304 (@Enclosure.Real.IsNear.recentre' (Real.cos qz23) Bool.true 971759 1048576 108400843 140183076864 971759 1048576 108400843 140183076864 (ep91 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz22 (@Neg.neg Real Real.instNeg (Real.sin qz23)) 524287 1048576 1 1048576 393947 1048576 108400843 140183076864 206541290789 1099511627776 56885927555267 146992610005745664 qz304 (@Enclosure.Real.IsNear.neg (Real.sin qz23) Bool.true 393947 1048576 108400843 140183076864 (@Enclosure.Real.IsNear.recentre' (Real.sin qz23) Bool.true 393947 1048576 108400843 140183076864 393947 1048576 108400843 140183076864 (ep93 rfl rfl) rfl)) rfl)

noncomputable def ep95 := @ep48 509480610833 1099511627776 56963174663735 146992610005745664 Bool.false 206541290789 1099511627776 56885927555267 146992610005745664 Bool.false 992250906793420949291008 451223471279 549755813888 50772928845901 36748152501436416 Bool.true 33070815573876150370304 120310926191 1099511627776 203119753576507 146992610005745664 (ep49 (BSN.head_sum_c_succ qz5 3 4 rfl rfl) (ep82 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep83 ep94) rfl rfl

noncomputable abbrev qz542 := (@Nat.cast Real Real.instNatCast 5)

noncomputable abbrev qz24 := (@Inv.inv Real Real.instInv (Real.sqrt qz542))

noncomputable abbrev qz305 := (Real.log (Enclosure.sfrac Bool.false 5 1))

noncomputable abbrev qz25 := (@HMul.hMul Real Real Real qz268 qz284 qz305)

noncomputable def ep96 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz279 qz7) (Complex.mk (@HMul.hMul Real Real Real qz0 qz24 (Real.cos qz25)) (@HMul.hMul Real Real Real qz0 qz24 (@Neg.neg Real Real.instNeg (Real.sin qz25)))) Bool.false 86407738431 549755813888 12720635596787 36748152501436416 Bool.true 230173506017 549755813888 3185282162477 9187038125359104 (BSN.cpow_neg_s_mk qz13 102256 1000 5 qz14 rfl)

noncomputable def ep97 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz542) 2344687 1048576 1 1048576 234468 234469 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz542) (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz542 qz15)) Bool.false 2344687 1048576 1 1048576 (BSN.sqrt_natCast_div_one 5) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz542 qz15)) Bool.false 2344687 1048576 1 1048576 2344687 1048576 1 1048576 (BSN.sqrt_enclosure 5 1 1172343 1172344 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep98 := nat_lit 11734546589655452485523914939250625

noncomputable def ep99 := nat_lit 2429970938528035899633153341031900

noncomputable def ep100 := nat_lit 824199001261152424427520000

noncomputable def ep101 := BSN.log_dyadic_bound 2 3 17 16 ep98 524288 133689 ep99 ep100 843808 5 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base16 (BSN.artanhP 2) (BSN.artanhQ 3) 0 16 ep99 ep98 ep100 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep102 := nat_lit 1640008682680863242593990498625678074972406028512140090061213848492315568800000

noncomputable def ep103 := nat_lit 2101459903646524644265829711200583960576568244468838246653242815760100000000

noncomputable def ep104 := nat_lit 4915823128235296678493439836454633056996064949047482593690335059845426506400000

noncomputable def ep105 := BSN.cos_dyadic_bound_f 2602047010 2147483648 3 2 1048576 267640 ep102 ep75 ep103 ep104 ep78 ep103 368526 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2602047010) qz292 0 2 ep102 ep75 ep103 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2602047010) qz293 0 2 ep104 ep78 ep103 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz26 := (@Nat.cast Real Real.instNatCast 1048576)

noncomputable abbrev qz27 := (@Nat.cast Real Real.instNatCast 151115727451828646838272)

noncomputable abbrev qz306 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 172568861) qz26)

noncomputable abbrev qz307 := (BSN.isNear_log_sfrac 5 1 843808 524288 1 133689 Bool.false (BSN.logfrac_isNear 5 1 2 5 1 843808 524288 133689 rfl rfl rfl (ep101 rfl)))

noncomputable def ep106 := @Enclosure.Real.IsNear.cos_image qz25 qz306 Bool.false 172568861 1048576 803 1048576 Bool.false 368526 1048576 1 133689 (@Enclosure.Real.IsNear.recentre' qz25 Bool.false 168524279 1024000 12782 16711125 172568861 1048576 803 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz13 qz305 102256 1000 0 1 843808 524288 1 133689 168524279 1024000 12782 16711125 qz16 qz307 rfl) rfl) (Enclosure.sfrac_false_div 172568861 1048576) (BSN.cos_reduce0 qz306 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 183102780415029618409472) qz27) 226375608064910080 72057594037927936 Bool.false 368526 1048576 26 1000000000000000 267378 133689 (BSN.sin_reduce_arg_pos_rat_q0 172568861 1048576 226375608064910080 72057594037927936 26 183102780415029618409472 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 368526 1048576 183102780415029618409472 151115727451828646838272 2602047010 2147483648 267640 267378 (ep105 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep107 := nat_lit 2950334460902636616953770233757260067781869596726277091512862333033559943840000

noncomputable def ep108 := nat_lit 164135286493895707012911871249815109382010203263545499525931125331216861264609280

noncomputable def ep109 := nat_lit 7723664081567668194978682126022308755873486880934919025372438955290950167200000

noncomputable def ep110 := nat_lit 3009146919054754628570050972913277005336853726498334157975403964405642456517836800

noncomputable def ep111 := BSN.sin_dyadic_bound_f 2602047010 2147483648 3 2 1048576 267640 ep107 ep108 ep103 ep109 ep110 ep103 981682 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2602047010) qz287 0 2 ep107 ep108 ep103 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2602047010) qz288 0 2 ep109 ep110 ep103 rfl rfl rfl rfl) rfl rfl

noncomputable def ep112 := @Enclosure.Real.IsNear.sin_image qz25 qz306 Bool.false 172568861 1048576 803 1048576 Bool.false 981682 1048576 1 133689 (@Enclosure.Real.IsNear.recentre' qz25 Bool.false 168524279 1024000 12782 16711125 172568861 1048576 803 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz13 qz305 102256 1000 0 1 843808 524288 1 133689 168524279 1024000 12782 16711125 qz16 qz307 rfl) rfl) (Enclosure.sfrac_false_div 172568861 1048576) (BSN.sin_reduce0 qz306 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 183102780415029618409472) qz27) 226375608064910080 72057594037927936 Bool.false 981682 1048576 26 1000000000000000 267378 133689 (BSN.sin_reduce_arg_pos_rat_q0 172568861 1048576 226375608064910080 72057594037927936 26 183102780415029618409472 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 981682 1048576 183102780415029618409472 151115727451828646838272 2602047010 2147483648 267640 267378 (ep111 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz308 := (@Enclosure.Real.IsNear.recentre' qz24 Bool.false 468937 1048576 1 1048576 468937 1048576 1 1048576 (ep97 rfl rfl) rfl)

noncomputable def ep113 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz24 (Real.cos qz25)) (@HMul.hMul Real Real Real qz0 qz24 (@Neg.neg Real Real.instNeg (Real.sin qz25))) Bool.false 86407738431 549755813888 12720635596787 36748152501436416 Bool.true 230173506017 549755813888 3185282162477 9187038125359104 (@Enclosure.Real.IsNear.mulLit_ff qz24 (Real.cos qz25) 468937 1048576 1 1048576 184263 524288 108400843 140183076864 86407738431 549755813888 12720635596787 36748152501436416 qz308 (@Enclosure.Real.IsNear.recentre' (Real.cos qz25) Bool.false 368526 1048576 108400843 140183076864 184263 524288 108400843 140183076864 (ep106 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz24 (@Neg.neg Real Real.instNeg (Real.sin qz25)) 468937 1048576 1 1048576 490841 524288 108400843 140183076864 230173506017 549755813888 3185282162477 9187038125359104 qz308 (@Enclosure.Real.IsNear.neg (Real.sin qz25) Bool.false 490841 524288 108400843 140183076864 (@Enclosure.Real.IsNear.recentre' (Real.sin qz25) Bool.false 981682 1048576 108400843 140183076864 490841 524288 108400843 140183076864 (ep112 rfl rfl) rfl)) rfl)

noncomputable def ep114 := @ep46 86407738431 549755813888 12720635596787 36748152501436416 Bool.true 230173506017 549755813888 3185282162477 9187038125359104 Bool.false 295565883265711058452480 268815604855 274877906944 330695648139 191396627611648 Bool.true 319220077419412901068800 580657938225 1099511627776 84694756058713 48997536668581888 (ep47 (BSN.head_sum_c_succ qz5 4 5 rfl rfl) (ep95 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep96 ep113) rfl rfl

noncomputable abbrev qz309 := (@Nat.cast Real Real.instNatCast 6)

noncomputable abbrev qz28 := (@Inv.inv Real Real.instInv (Real.sqrt qz309))

noncomputable abbrev qz543 := (Real.log (Enclosure.sfrac Bool.false 6 1))

noncomputable abbrev qz29 := (@HMul.hMul Real Real Real qz268 qz284 qz543)

noncomputable def ep115 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz278 qz7) (Complex.mk (@HMul.hMul Real Real Real qz0 qz28 (Real.cos qz29)) (@HMul.hMul Real Real Real qz0 qz28 (@Neg.neg Real Real.instNeg (Real.sin qz29)))) Bool.false 240375348159 1099511627776 46479302052409 146992610005745664 Bool.true 379086642687 1099511627776 46522621566457 146992610005745664 (BSN.cpow_neg_s_mk qz13 102256 1000 6 qz14 rfl)

noncomputable abbrev qz310 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 6) qz15)

noncomputable def ep116 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz309) 2568477 1048576 1 1048576 214039 214040 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz309) (Real.sqrt qz310) Bool.false 2568477 1048576 1 1048576 (BSN.sqrt_natCast_div_one 6) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz310) Bool.false 2568477 1048576 1 1048576 2568477 1048576 1 1048576 (BSN.sqrt_enclosure 6 1 1284238 1284239 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep117 := BSN.log_dyadic_bound 2 10 4 3 105000000 524288 133689 1434560 960 212580 12 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 2) (BSN.artanhQ 10) 0 3 1434560 105000000 960 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep118 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz543 102256 1000 0 1 4034681531866359 2251799813685248 500000000133689 66844500000000000000 25785649670157900369 140737488355328000 3195500000854406399 4177781250000000000000 qz16 (BSN.isNear_log_sfrac 6 1 4034681531866359 2251799813685248 500000000133689 66844500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz310) Bool.false 33845361775666394038272 18889465931478580854784 1000000000267378 133689000000000000000 4034681531866359 2251799813685248 500000000133689 66844500000000000000 (BSN.log_rat_reduce_isNear 6 1 2 12 8 212580 524288 24973259072661432 36028797018963968 133689 1000000000000000 rfl rfl rfl rfl (ep117 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep119 := nat_lit 777791500472948840047972759308484616800509043743883901227999193517354769186816

noncomputable def ep120 := nat_lit 473304006293943985054067670254318866285271788456923589867223887976423489536

noncomputable def ep121 := nat_lit 2332427893406258632173810142584945212668956587654737856504263132776111460581376

noncomputable def ep122 := BSN.cos_dyadic_bound_f 2159695496 2147483648 3 2 1048576 267640 ep119 ep75 ep120 ep121 ep78 ep120 561521 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2159695496) qz292 0 2 ep119 ep75 ep120 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2159695496) qz293 0 2 ep121 ep78 ep120 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz311 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 192118061) qz26)

noncomputable def ep123 := @Enclosure.Real.IsNear.cos_image qz29 qz311 Bool.false 192118061 1048576 803 1048576 Bool.false 561521 1048576 1 133689 (@Enclosure.Real.IsNear.recentre' qz29 Bool.false 25785649670157900369 140737488355328000 3195500000854406399 4177781250000000000000 192118061 1048576 803 1048576 (ep118 rfl) rfl) (Enclosure.sfrac_false_div 192118061 1048576) (BSN.cos_reduce0 qz311 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 151975059920297406758912) qz27) 226375608064910080 72057594037927936 Bool.false 561521 1048576 29 1000000000000000 267378 133689 (BSN.sin_reduce_arg_pos_rat_q0 192118061 1048576 226375608064910080 72057594037927936 29 151975059920297406758912 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 561521 1048576 151975059920297406758912 151115727451828646838272 2159695496 2147483648 267640 267378 (ep122 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep124 := nat_lit 1399646057646272756898307712619068855147888061308225483338504769220857445744640

noncomputable def ep125 := nat_lit 3664973373063381311138813613964768580556197339578326961026775080712188624633856

noncomputable def ep126 := BSN.sin_dyadic_bound_f 2159695496 2147483648 3 2 1048576 267640 ep124 ep108 ep120 ep125 ep110 ep120 885553 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2159695496) qz287 0 2 ep124 ep108 ep120 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2159695496) qz288 0 2 ep125 ep110 ep120 rfl rfl rfl rfl) rfl rfl

noncomputable def ep127 := @Enclosure.Real.IsNear.sin_image qz29 qz311 Bool.false 192118061 1048576 803 1048576 Bool.false 885553 1048576 1 133689 (@Enclosure.Real.IsNear.recentre' qz29 Bool.false 25785649670157900369 140737488355328000 3195500000854406399 4177781250000000000000 192118061 1048576 803 1048576 (ep118 rfl) rfl) (Enclosure.sfrac_false_div 192118061 1048576) (BSN.sin_reduce0 qz311 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 151975059920297406758912) qz27) 226375608064910080 72057594037927936 Bool.false 885553 1048576 29 1000000000000000 267378 133689 (BSN.sin_reduce_arg_pos_rat_q0 192118061 1048576 226375608064910080 72057594037927936 29 151975059920297406758912 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 885553 1048576 151975059920297406758912 151115727451828646838272 2159695496 2147483648 267640 267378 (ep126 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz312 := (@Enclosure.Real.IsNear.recentre' qz28 Bool.false 428079 1048576 1 1048576 428079 1048576 1 1048576 (ep116 rfl rfl) rfl)

noncomputable def ep128 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz28 (Real.cos qz29)) (@HMul.hMul Real Real Real qz0 qz28 (@Neg.neg Real Real.instNeg (Real.sin qz29))) Bool.false 240375348159 1099511627776 46479302052409 146992610005745664 Bool.true 379086642687 1099511627776 46522621566457 146992610005745664 (@Enclosure.Real.IsNear.mulLit_ff qz28 (Real.cos qz29) 428079 1048576 1 1048576 561521 1048576 108400843 140183076864 240375348159 1099511627776 46479302052409 146992610005745664 qz312 (@Enclosure.Real.IsNear.recentre' (Real.cos qz29) Bool.false 561521 1048576 108400843 140183076864 561521 1048576 108400843 140183076864 (ep123 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz28 (@Neg.neg Real Real.instNeg (Real.sin qz29)) 428079 1048576 1 1048576 885553 1048576 108400843 140183076864 379086642687 1099511627776 46522621566457 146992610005745664 qz312 (@Enclosure.Real.IsNear.neg (Real.sin qz29) Bool.false 885553 1048576 108400843 140183076864 (@Enclosure.Real.IsNear.recentre' (Real.sin qz29) Bool.false 885553 1048576 108400843 140183076864 885553 1048576 108400843 140183076864 (ep127 rfl rfl) rfl)) rfl)

noncomputable def ep129 := @ep44 240375348159 1099511627776 46479302052409 146992610005745664 Bool.true 379086642687 1099511627776 46522621566457 146992610005745664 Bool.false 361639755848592262168576 1315637767579 1099511627776 300453559823161 146992610005745664 Bool.true 1055250326407748058611712 59984036307 68719476736 75151722435649 36748152501436416 (ep45 (BSN.head_sum_c_succ qz5 5 6 rfl rfl) (ep114 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep115 ep128) rfl rfl

noncomputable abbrev qz313 := (@Nat.cast Real Real.instNatCast 7)

noncomputable abbrev qz30 := (@Inv.inv Real Real.instInv (Real.sqrt qz313))

noncomputable abbrev qz544 := (Real.log (Enclosure.sfrac Bool.false 7 1))

noncomputable abbrev qz31 := (@HMul.hMul Real Real Real qz268 qz284 qz544)

noncomputable def ep130 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz277 qz7) (Complex.mk (@HMul.hMul Real Real Real qz0 qz30 (Real.cos qz31)) (@HMul.hMul Real Real Real qz0 qz30 (@Neg.neg Real Real.instNeg (Real.sin qz31)))) Bool.true 101493680275 549755813888 1344704516647 4593519062679552 Bool.false 90657362125 274877906944 21542197632019 73496305002872832 (BSN.cpow_neg_s_mk qz13 102256 1000 7 qz14 rfl)

noncomputable abbrev qz314 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 7) qz15)

noncomputable def ep131 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz313) 2774271 1048576 1 1048576 198162 198163 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz313) (Real.sqrt qz314) Bool.false 2774271 1048576 1 1048576 (BSN.sqrt_natCast_div_one 7) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz314) Bool.false 2774271 1048576 1 1048576 2774271 1048576 1 1048576 (BSN.sqrt_enclosure 7 1 1387135 1387136 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep132 := BSN.log_dyadic_bound 3 11 5 4 202569142545 524288 133689 5259111624 688905 293399 14 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 3) (BSN.artanhQ 11) 0 4 5259111624 202569142545 688905 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep133 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz544 102256 1000 0 1 4381796493761783 2251799813685248 500000000133689 66844500000000000000 28004061391631555153 140737488355328000 3195500000854406399 4177781250000000000000 qz16 (BSN.isNear_log_sfrac 7 1 4381796493761783 2251799813685248 500000000133689 66844500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz314) Bool.false 36757173121942042968064 18889465931478580854784 1000000000267378 133689000000000000000 4381796493761783 2251799813685248 500000000133689 66844500000000000000 (BSN.log_rat_reduce_isNear 7 1 2 14 8 293399 524288 24973259072661432 36028797018963968 133689 1000000000000000 rfl rfl rfl rfl (ep132 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep134 := nat_lit 961823446659465448232615308418799100826006029925618268729652187819084025390625

noncomputable def ep135 := nat_lit 723568340876383569509468763044767896911140409074176501328225561676025390625

noncomputable def ep136 := nat_lit 2884023203296643577558826987730307766684195808958706453186300112333900025390625

noncomputable def ep137 := BSN.cos_dyadic_bound_f 2277377075 2147483648 3 2 1048576 267640 ep134 ep75 ep135 ep136 ep78 ep135 512174 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2277377075) qz292 0 2 ep134 ep75 ep135 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2277377075) qz293 0 2 ep136 ep78 ep135 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz315 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 52161629) (@Nat.cast Real Real.instNatCast 262144))

noncomputable abbrev qz316 := (@Nat.cast Real Real.instNatCast 37778931862957161709568)

noncomputable def ep138 := @Enclosure.Real.IsNear.cos_image qz31 qz315 Bool.false 52161629 262144 803 1048576 Bool.true 512174 1048576 1 133689 (@Enclosure.Real.IsNear.recentre' qz31 Bool.false 28004061391631555153 140737488355328000 3195500000854406399 4177781250000000000000 52161629 262144 803 1048576 (ep133 rfl) rfl) (Enclosure.sfrac_false_div 52161629 262144) (BSN.cos_reduce2 qz315 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 40064041206476563283968) qz316) 226375608064910080 72057594037927936 Bool.false 512174 1048576 31 1000000000000000 267378 133689 (BSN.sin_reduce_arg_pos_rat_q2 52161629 262144 226375608064910080 72057594037927936 31 40064041206476563283968 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 512174 1048576 40064041206476563283968 37778931862957161709568 2277377075 2147483648 267640 267378 (ep137 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep139 := nat_lit 1730703349314336699963099980143402567169281941538853542512311357625010425390625

noncomputable def ep140 := nat_lit 4531622994699939116981294141425886623134072762415639182720569761918028025390625

noncomputable def ep141 := BSN.sin_dyadic_bound_f 2277377075 2147483648 3 2 1048576 267640 ep139 ep108 ep135 ep140 ep110 ep135 914980 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2277377075) qz287 0 2 ep139 ep108 ep135 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2277377075) qz288 0 2 ep140 ep110 ep135 rfl rfl rfl rfl) rfl rfl

noncomputable def ep142 := @Enclosure.Real.IsNear.sin_image qz31 qz315 Bool.false 52161629 262144 803 1048576 Bool.true 914980 1048576 1 133689 (@Enclosure.Real.IsNear.recentre' qz31 Bool.false 28004061391631555153 140737488355328000 3195500000854406399 4177781250000000000000 52161629 262144 803 1048576 (ep133 rfl) rfl) (Enclosure.sfrac_false_div 52161629 262144) (BSN.sin_reduce2 qz315 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 40064041206476563283968) qz316) 226375608064910080 72057594037927936 Bool.false 914980 1048576 31 1000000000000000 267378 133689 (BSN.sin_reduce_arg_pos_rat_q2 52161629 262144 226375608064910080 72057594037927936 31 40064041206476563283968 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 914980 1048576 40064041206476563283968 37778931862957161709568 2277377075 2147483648 267640 267378 (ep141 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz317 := (@Enclosure.Real.IsNear.recentre' qz30 Bool.false 396325 1048576 1 1048576 396325 1048576 1 1048576 (ep131 rfl rfl) rfl)

noncomputable def ep143 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz30 (Real.cos qz31)) (@HMul.hMul Real Real Real qz0 qz30 (@Neg.neg Real Real.instNeg (Real.sin qz31))) Bool.true 101493680275 549755813888 1344704516647 4593519062679552 Bool.false 90657362125 274877906944 21542197632019 73496305002872832 (@Enclosure.Real.IsNear.mulLit_ft qz30 (Real.cos qz31) 396325 1048576 1 1048576 256087 524288 108400843 140183076864 101493680275 549755813888 1344704516647 4593519062679552 qz317 (@Enclosure.Real.IsNear.recentre' (Real.cos qz31) Bool.true 512174 1048576 108400843 140183076864 256087 524288 108400843 140183076864 (ep138 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz30 (@Neg.neg Real Real.instNeg (Real.sin qz31)) 396325 1048576 1 1048576 228745 262144 108400843 140183076864 90657362125 274877906944 21542197632019 73496305002872832 qz317 (@Enclosure.Real.IsNear.neg (Real.sin qz31) Bool.true 228745 262144 108400843 140183076864 (@Enclosure.Real.IsNear.recentre' (Real.sin qz31) Bool.true 914980 1048576 108400843 140183076864 228745 262144 108400843 140183076864 (ep142 rfl rfl) rfl)) rfl)

noncomputable def ep144 := @ep42 101493680275 549755813888 1344704516647 4593519062679552 Bool.false 90657362125 274877906944 21542197632019 73496305002872832 Bool.false 611686030089042371018752 1112650407029 1099511627776 114494701451955 48997536668581888 Bool.true 10258359862624998391808 149278783103 274877906944 57281880834439 24498768334290944 (ep43 (BSN.head_sum_c_succ qz5 6 7 rfl rfl) (ep129 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep130 ep143) rfl rfl

noncomputable abbrev qz318 := (@Nat.cast Real Real.instNatCast 8)

noncomputable abbrev qz32 := (@Inv.inv Real Real.instInv (Real.sqrt qz318))

noncomputable abbrev qz545 := (Real.log (Enclosure.sfrac Bool.false 8 1))

noncomputable abbrev qz33 := (@HMul.hMul Real Real Real qz268 qz284 qz545)

noncomputable def ep145 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz276 qz7) (Complex.mk (@HMul.hMul Real Real Real qz0 qz32 (Real.cos qz33)) (@HMul.hMul Real Real Real qz0 qz32 (@Neg.neg Real Real.instNeg (Real.sin qz33)))) Bool.false 212343157425 1099511627776 13421267146893 48997536668581888 Bool.false 81403863933 274877906944 3358720742619 12249384167145472 (BSN.cpow_neg_s_mk qz13 102256 1000 8 qz14 rfl)

noncomputable abbrev qz319 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 8) qz15)

noncomputable def ep146 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz318) 2965821 1048576 1 1048576 185363 185364 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz318) (Real.sqrt qz319) Bool.false 2965821 1048576 1 1048576 (BSN.sqrt_natCast_div_one 8) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz319) Bool.false 2965821 1048576 1 1048576 2965821 1048576 1 1048576 (BSN.sqrt_enclosure 8 1 1482910 1482911 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep147 := BSN.log_dyadic_bound 0 16 1 0 1 524288 133689 0 1 0 16 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 0) (BSN.artanhQ 16) 0 0 rfl) rfl rfl rfl

noncomputable def ep148 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz545 102256 1000 0 1 9364972152248037 4503599627370496 1000000000401067 133689000000000000000 59851537025017204467 281474976710656000 6391000002563219197 8355562500000000000000 qz16 (BSN.isNear_log_sfrac 8 1 9364972152248037 4503599627370496 1000000000401067 133689000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz319) Bool.false 39279540158062550581248 18889465931478580854784 1000000000401067 133689000000000000000 9364972152248037 4503599627370496 1000000000401067 133689000000000000000 (BSN.log_rat_reduce_isNear 8 1 3 16 16 0 524288 24973259072661432 36028797018963968 133689 1000000000000000 rfl rfl rfl rfl (ep147 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep149 := nat_lit 2371591647791413824459374706353504256

noncomputable def ep150 := BSN.sin_dyadic_bound_f 1240966272 2147483648 2 1 1048576 267640 ep149 ep58 ep149 ep149 ep59 ep149 572775 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1240966272) qz287 0 1 ep149 ep58 ep149 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1240966272) qz288 0 1 ep149 ep59 ep149 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz320 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 111482175) qz20)

noncomputable def ep151 := @Enclosure.Real.IsNear.cos_image qz33 qz320 Bool.false 111482175 524288 803 1048576 Bool.false 572775 1048576 1 133689 (@Enclosure.Real.IsNear.recentre' qz33 Bool.false 59851537025017204467 281474976710656000 6391000002563219197 8355562500000000000000 111482175 524288 803 1048576 (ep148 rfl) rfl) (Enclosure.sfrac_false_div 111482175 524288) (BSN.cos_reduce3 qz320 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 43662619077174833971200) qz21) 226375608064910080 72057594037927936 Bool.false 572775 1048576 33 1000000000000000 267378 133689 (BSN.sin_reduce_arg_pos_rat_q3 111482175 524288 226375608064910080 72057594037927936 33 43662619077174833971200 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 572775 1048576 43662619077174833971200 75557863725914323419136 1240966272 2147483648 267640 267378 (ep150 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep152 := BSN.cos_dyadic_bound_f 1240966272 2147483648 2 1 1048576 267640 ep149 ep62 ep149 ep149 ep63 ep149 878316 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1240966272) qz292 0 1 ep149 ep62 ep149 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1240966272) qz293 0 1 ep149 ep63 ep149 rfl rfl rfl rfl) rfl rfl

noncomputable def ep153 := @Enclosure.Real.IsNear.sin_image qz33 qz320 Bool.false 111482175 524288 803 1048576 Bool.true 878316 1048576 1 133689 (@Enclosure.Real.IsNear.recentre' qz33 Bool.false 59851537025017204467 281474976710656000 6391000002563219197 8355562500000000000000 111482175 524288 803 1048576 (ep148 rfl) rfl) (Enclosure.sfrac_false_div 111482175 524288) (BSN.sin_reduce3 qz320 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 43662619077174833971200) qz21) 226375608064910080 72057594037927936 Bool.false 878316 1048576 33 1000000000000000 267378 133689 (BSN.sin_reduce_arg_pos_rat_q3 111482175 524288 226375608064910080 72057594037927936 33 43662619077174833971200 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 878316 1048576 43662619077174833971200 75557863725914323419136 1240966272 2147483648 267640 267378 (ep152 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz321 := (@Enclosure.Real.IsNear.recentre' qz32 Bool.false 370727 1048576 1 1048576 370727 1048576 1 1048576 (ep146 rfl rfl) rfl)

noncomputable def ep154 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz32 (Real.cos qz33)) (@HMul.hMul Real Real Real qz0 qz32 (@Neg.neg Real Real.instNeg (Real.sin qz33))) Bool.false 212343157425 1099511627776 13421267146893 48997536668581888 Bool.false 81403863933 274877906944 3358720742619 12249384167145472 (@Enclosure.Real.IsNear.mulLit_ff qz32 (Real.cos qz33) 370727 1048576 1 1048576 572775 1048576 108400843 140183076864 212343157425 1099511627776 13421267146893 48997536668581888 qz321 (@Enclosure.Real.IsNear.recentre' (Real.cos qz33) Bool.false 572775 1048576 108400843 140183076864 572775 1048576 108400843 140183076864 (ep151 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz32 (@Neg.neg Real Real.instNeg (Real.sin qz33)) 370727 1048576 1 1048576 219579 262144 108400843 140183076864 81403863933 274877906944 3358720742619 12249384167145472 qz321 (@Enclosure.Real.IsNear.neg (Real.sin qz33) Bool.true 219579 262144 108400843 140183076864 (@Enclosure.Real.IsNear.recentre' (Real.sin qz33) Bool.true 878316 1048576 108400843 140183076864 219579 262144 108400843 140183076864 (ep153 rfl rfl) rfl)) rfl)

noncomputable def ep155 := @ep39 212343157425 1099511627776 13421267146893 48997536668581888 Bool.false 81403863933 274877906944 3358720742619 12249384167145472 Bool.false ep40 662496782227 549755813888 1998687009357 765586510446592 Bool.true 18657315715442781716480 33937459585 137438953472 63999322319677 24498768334290944 (ep41 (BSN.head_sum_c_succ qz5 7 8 rfl rfl) (ep144 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep145 ep154) rfl rfl

theorem EMRow31.d6 : Enclosure.Complex.IsNear qz3 Bool.false 662496782227 549755813888 1998687009357 765586510446592 Bool.true 33937459585 137438953472 63999322319677 24498768334290944 := ep38 (BSN.head_sum_c_succ qz5 8 9 rfl rfl) (ep155 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable abbrev qz34 := (BSN.headSumC qz272 17)

noncomputable abbrev qz35 := (@HPow.hPow Complex Complex Complex qz274 (@Nat.cast Complex Complex.instNatCast 16) qz275)

noncomputable def ep156 := @Enclosure.Complex.IsNear.of_eq qz34 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 16) qz35) Bool.false 438285926375 274877906944 322558094612965 73496305002872832 Bool.true 49282991443 1099511627776 645162334256993 146992610005745664

noncomputable def ep157 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 16) qz35 Bool.false 1555901283011 1099511627776 616598967960091 146992610005745664 Bool.false 35541386615 274877906944 77081008473179 18374076250718208 Bool.false

noncomputable def ep158 := nat_lit 1927601889359553363968000

noncomputable abbrev qz36 := (@HPow.hPow Complex Complex Complex qz274 (@Nat.cast Complex Complex.instNatCast 15) qz275)

noncomputable def ep159 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 16) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 15) qz36) Bool.false 1555901283011 1099511627776 616598967960091 146992610005745664 Bool.false 35541386615 274877906944 77081008473179 18374076250718208

noncomputable def ep160 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 15) qz36 Bool.false 1300771750553 1099511627776 195708108899901 48997536668581888 Bool.false 133339936921 549755813888 24468246787977 6124692083572736 Bool.false

noncomputable abbrev qz37 := (@HPow.hPow Complex Complex Complex qz274 (@Nat.cast Complex Complex.instNatCast 14) qz275)

noncomputable def ep161 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 15) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 14) qz37) Bool.false 1300771750553 1099511627776 195708108899901 48997536668581888 Bool.false 133339936921 549755813888 24468246787977 6124692083572736

noncomputable def ep162 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 14) qz37 Bool.false 510810148519 549755813888 278306236286333 73496305002872832 Bool.false 174888240893 1099511627776 556815448169629 146992610005745664 Bool.false

noncomputable abbrev qz38 := (@HPow.hPow Complex Complex Complex qz274 (@Nat.cast Complex Complex.instNatCast 13) qz275)

noncomputable def ep163 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 14) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 13) qz38) Bool.false 510810148519 549755813888 278306236286333 73496305002872832 Bool.false 174888240893 1099511627776 556815448169629 146992610005745664

noncomputable def ep164 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 13) qz38 Bool.false 1034334206129 1099511627776 175027020442007 48997536668581888 Bool.true 129796546579 1099511627776 175049940084167 48997536668581888 Bool.true

noncomputable abbrev qz546 := (@Nat.cast Complex Complex.instNatCast 12)

noncomputable abbrev qz39 := (@HPow.hPow Complex Complex Complex qz274 qz546 qz275)

noncomputable def ep165 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 13) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 12) qz39) Bool.false 1034334206129 1099511627776 175027020442007 48997536668581888 Bool.true 129796546579 1099511627776 175049940084167 48997536668581888

noncomputable def ep166 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 12) qz39 Bool.false 1329969285119 1099511627776 492137772915977 146992610005745664 Bool.true 14284344409 1099511627776 492286084818797 146992610005745664 Bool.true

noncomputable abbrev qz547 := (@Nat.cast Complex Complex.instNatCast 11)

noncomputable abbrev qz40 := (@HPow.hPow Complex Complex Complex qz274 qz547 qz275)

noncomputable def ep167 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 12) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 11) qz40) Bool.false 1329969285119 1099511627776 492137772915977 146992610005745664 Bool.true 14284344409 1099511627776 492286084818797 146992610005745664

noncomputable def ep168 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 11) qz40 Bool.false 62651381055 68719476736 114431868445295 36748152501436416 Bool.false 4606084459 137438953472 228996334587283 73496305002872832 Bool.false

noncomputable abbrev qz548 := (@Nat.cast Complex Complex.instNatCast 10)

noncomputable abbrev qz41 := (@HPow.hPow Complex Complex Complex qz274 qz548 qz275)

noncomputable def ep169 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 11) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 10) qz41) Bool.false 62651381055 68719476736 114431868445295 36748152501436416 Bool.false 4606084459 137438953472 228996334587283 73496305002872832

noncomputable def ep170 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 10) qz41 Bool.false 1345315297479 1099511627776 421644591659111 146992610005745664 Bool.false 47219858185 549755813888 211012407135649 73496305002872832 Bool.true

noncomputable abbrev qz322 := (@Nat.cast Complex Complex.instNatCast 9)

noncomputable def ep171 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 10) (@HAdd.hAdd Complex Complex Complex qz4 qz3 (@HPow.hPow Complex Complex Complex qz6 qz322 qz7)) Bool.false 1345315297479 1099511627776 421644591659111 146992610005745664 Bool.false 47219858185 549755813888 211012407135649 73496305002872832

noncomputable def ep172 := @Enclosure.Complex.IsNear.addLitP qz3 (@HPow.hPow Complex Complex Complex qz6 qz322 qz7) Bool.false 662496782227 549755813888 1998687009357 765586510446592 Bool.true 33937459585 137438953472 63999322319677 24498768334290944 Bool.false

noncomputable abbrev qz323 := (@Nat.cast Real Real.instNatCast 9)

noncomputable abbrev qz42 := (@Inv.inv Real Real.instInv (Real.sqrt qz323))

noncomputable abbrev qz549 := (Real.log (Enclosure.sfrac Bool.false 9 1))

noncomputable abbrev qz43 := (@HMul.hMul Real Real Real qz268 qz284 qz549)

noncomputable def ep173 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz322 qz7) (Complex.mk (@HMul.hMul Real Real Real qz0 qz42 (Real.cos qz43)) (@HMul.hMul Real Real Real qz0 qz42 (@Neg.neg Real Real.instNeg (Real.sin qz43)))) Bool.false 20321733025 1099511627776 37896685862567 146992610005745664 Bool.false 182969696525 549755813888 9507220088309 36748152501436416 (BSN.cpow_neg_s_mk qz13 102256 1000 9 qz14 rfl)

noncomputable abbrev qz324 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 9) qz15)

noncomputable def ep174 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz323) 3145729 1048576 1 1048576 174762 174763 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz323) (Real.sqrt qz324) Bool.false 3145729 1048576 1 1048576 (BSN.sqrt_natCast_div_one 9) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz324) Bool.false 3145729 1048576 1 1048576 3145729 1048576 1 1048576 (BSN.sqrt_enclosure 9 1 1572864 1572865 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep175 := BSN.log_dyadic_bound 1 17 2 1 867 524288 133689 1 1 61752 18 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 1) (BSN.artanhQ 17) 0 1 1 867 1 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep176 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz549 102256 1000 0 1 9895417793173221 4503599627370496 1000000000401067 133689000000000000000 63241615116170055411 281474976710656000 6391000002563219197 8355562500000000000000 qz16 (BSN.isNear_log_sfrac 9 1 9895417793173221 4503599627370496 1000000000401067 133689000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz324) Bool.false 41504390431577613533184 18889465931478580854784 1000000000401067 133689000000000000000 9895417793173221 4503599627370496 1000000000401067 133689000000000000000 (BSN.log_rat_reduce_isNear 9 1 3 18 16 61752 524288 24973259072661432 36028797018963968 133689 1000000000000000 rfl rfl rfl rfl (ep175 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep177 := BSN.sin_dyadic_bound_f 119134063 2147483648 1 0 1048576 267640 0 1 1 0 1 1 58141 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 119134063) qz287 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 119134063) qz288 0 0 rfl) rfl rfl

noncomputable abbrev qz325 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 235593375) qz26)

noncomputable def ep178 := @Enclosure.Real.IsNear.cos_image qz43 qz325 Bool.false 235593375 1048576 803 1048576 Bool.false 58141 1048576 1 133689 (@Enclosure.Real.IsNear.recentre' qz43 Bool.false 63241615116170055411 281474976710656000 6391000002563219197 8355562500000000000000 235593375 1048576 803 1048576 (ep176 rfl) rfl) (Enclosure.sfrac_false_div 235593375 1048576) (BSN.cos_reduce3 qz325 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 8383314425866155458560) qz27) 226375608064910080 72057594037927936 Bool.false 58141 1048576 35 1000000000000000 267378 133689 (BSN.sin_reduce_arg_pos_rat_q3 235593375 1048576 226375608064910080 72057594037927936 35 8383314425866155458560 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 58141 1048576 8383314425866155458560 151115727451828646838272 119134063 2147483648 267640 267378 (ep177 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep179 := BSN.cos_dyadic_bound_f 119134063 2147483648 1 0 1048576 267640 0 1 1 0 1 1 1046962 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 119134063) qz292 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 119134063) qz293 0 0 rfl) rfl rfl

noncomputable def ep180 := @Enclosure.Real.IsNear.sin_image qz43 qz325 Bool.false 235593375 1048576 803 1048576 Bool.true 1046962 1048576 1 133689 (@Enclosure.Real.IsNear.recentre' qz43 Bool.false 63241615116170055411 281474976710656000 6391000002563219197 8355562500000000000000 235593375 1048576 803 1048576 (ep176 rfl) rfl) (Enclosure.sfrac_false_div 235593375 1048576) (BSN.sin_reduce3 qz325 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 8383314425866155458560) qz27) 226375608064910080 72057594037927936 Bool.false 1046962 1048576 35 1000000000000000 267378 133689 (BSN.sin_reduce_arg_pos_rat_q3 235593375 1048576 226375608064910080 72057594037927936 35 8383314425866155458560 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1046962 1048576 8383314425866155458560 151115727451828646838272 119134063 2147483648 267640 267378 (ep179 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz326 := (@Enclosure.Real.IsNear.recentre' qz42 Bool.false 349525 1048576 1 1048576 349525 1048576 1 1048576 (ep174 rfl rfl) rfl)

noncomputable def ep181 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz42 (Real.cos qz43)) (@HMul.hMul Real Real Real qz0 qz42 (@Neg.neg Real Real.instNeg (Real.sin qz43))) Bool.false 20321733025 1099511627776 37896685862567 146992610005745664 Bool.false 182969696525 549755813888 9507220088309 36748152501436416 (@Enclosure.Real.IsNear.mulLit_ff qz42 (Real.cos qz43) 349525 1048576 1 1048576 58141 1048576 108400843 140183076864 20321733025 1099511627776 37896685862567 146992610005745664 qz326 (@Enclosure.Real.IsNear.recentre' (Real.cos qz43) Bool.false 58141 1048576 108400843 140183076864 58141 1048576 108400843 140183076864 (ep178 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz42 (@Neg.neg Real Real.instNeg (Real.sin qz43)) 349525 1048576 1 1048576 523481 524288 108400843 140183076864 182969696525 549755813888 9507220088309 36748152501436416 qz326 (@Enclosure.Real.IsNear.neg (Real.sin qz43) Bool.true 523481 524288 108400843 140183076864 (@Enclosure.Real.IsNear.recentre' (Real.sin qz43) Bool.true 1046962 1048576 108400843 140183076864 523481 524288 108400843 140183076864 (ep180 rfl rfl) rfl)) rfl)

noncomputable def ep182 := @ep172 20321733025 1099511627776 37896685862567 146992610005745664 Bool.false 182969696525 549755813888 9507220088309 36748152501436416 Bool.false 739594906301544479588352 1345315297479 1099511627776 421644591659111 146992610005745664 Bool.false 6489847892042653368320 47219858185 549755813888 211012407135649 73496305002872832 EMRow31.d6 (ep173 ep181) rfl rfl

noncomputable abbrev qz327 := (@Nat.cast Real Real.instNatCast 10)

noncomputable abbrev qz44 := (@Inv.inv Real Real.instInv (Real.sqrt qz327))

noncomputable abbrev qz550 := (Real.log (Enclosure.sfrac Bool.false 10 1))

noncomputable abbrev qz45 := (@HMul.hMul Real Real Real qz268 qz284 qz550)

noncomputable def ep183 := @Enclosure.Complex.IsNear.of_eq qz41 (Complex.mk (@HMul.hMul Real Real Real qz0 qz44 (Real.cos qz45)) (@HMul.hMul Real Real Real qz0 qz44 (@Neg.neg Real Real.instNeg (Real.sin qz45)))) Bool.true 342893200599 1099511627776 12027627374023 48997536668581888 Bool.true 28795520349 549755813888 2997321241939 12249384167145472 (BSN.cpow_neg_s_mk qz13 102256 1000 10 qz14 rfl)

noncomputable abbrev qz328 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 10) qz15)

noncomputable def ep184 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz327) 3315889 1048576 1 1048576 165794 165795 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz327) (Real.sqrt qz328) Bool.false 3315889 1048576 1 1048576 (BSN.sqrt_natCast_div_one 10) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz328) Bool.false 3315889 1048576 1 1048576 3315889 1048576 1 1048576 (BSN.sqrt_enclosure 10 1 1657944 1657945 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep185 := BSN.log_dyadic_bound 2 18 3 2 1574640 524288 133689 6528 48 116991 20 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 2) (BSN.artanhQ 18) 0 2 6528 1574640 48 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep186 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz550 102256 1000 0 1 10369917190100709 4503599627370496 1000000000401067 133689000000000000000 66274140761933631219 281474976710656000 6391000002563219197 8355562500000000000000 qz16 (BSN.isNear_log_sfrac 10 1 10369917190100709 4503599627370496 1000000000401067 133689000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz328) Bool.false 43494585150108164161536 18889465931478580854784 1000000000401067 133689000000000000000 10369917190100709 4503599627370496 1000000000401067 133689000000000000000 (BSN.log_rat_reduce_isNear 10 1 3 20 16 116991 524288 24973259072661432 36028797018963968 133689 1000000000000000 rfl rfl rfl rfl (ep185 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep187 := nat_lit 5327627327613706024046405595076219545977695331958510337640292460762586196640000

noncomputable def ep188 := nat_lit 6844607526116510852589562820467981387713314624468464858352114797584100000000

noncomputable def ep189 := nat_lit 13942227922041231902550679171109341126742428121927911465001529211372589591200000

noncomputable def ep190 := BSN.sin_dyadic_bound_f 3015911330 2147483648 3 2 1048576 267640 ep187 ep108 ep188 ep189 ep110 ep188 1034091 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3015911330) qz287 0 2 ep187 ep108 ep188 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3015911330) qz288 0 2 ep189 ep110 ep188 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz329 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 246890413) qz26)

noncomputable def ep191 := @Enclosure.Real.IsNear.cos_image qz45 qz329 Bool.false 246890413 1048576 803 1048576 Bool.true 1034091 1048576 1 133689 (@Enclosure.Real.IsNear.recentre' qz45 Bool.false 66274140761933631219 281474976710656000 6391000002563219197 8355562500000000000000 246890413 1048576 803 1048576 (ep186 rfl) rfl) (Enclosure.sfrac_false_div 246890413 1048576) (BSN.cos_reduce1 qz329 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 212225892882329911689216) qz27) 226375608064910080 72057594037927936 Bool.false 1034091 1048576 37 1000000000000000 267378 133689 (BSN.sin_reduce_arg_pos_rat_q1 246890413 1048576 226375608064910080 72057594037927936 37 212225892882329911689216 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1034091 1048576 212225892882329911689216 151115727451828646838272 3015911330 2147483648 267640 267378 (ep190 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep192 := nat_lit 2962835007574777351515820691851441072826592213143380616403874529222585264800000

noncomputable def ep193 := nat_lit 8874815807672099032842282949913387255704350010181204919494919358072587594400000

noncomputable def ep194 := BSN.cos_dyadic_bound_f 3015911330 2147483648 3 2 1048576 267640 ep192 ep75 ep188 ep193 ep78 ep188 173682 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3015911330) qz292 0 2 ep192 ep75 ep188 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3015911330) qz293 0 2 ep193 ep78 ep188 rfl rfl rfl rfl) rfl rfl

noncomputable def ep195 := @Enclosure.Real.IsNear.sin_image qz45 qz329 Bool.false 246890413 1048576 803 1048576 Bool.false 173682 1048576 1 133689 (@Enclosure.Real.IsNear.recentre' qz45 Bool.false 66274140761933631219 281474976710656000 6391000002563219197 8355562500000000000000 246890413 1048576 803 1048576 (ep186 rfl) rfl) (Enclosure.sfrac_false_div 246890413 1048576) (BSN.sin_reduce1 qz329 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 212225892882329911689216) qz27) 226375608064910080 72057594037927936 Bool.false 173682 1048576 37 1000000000000000 267378 133689 (BSN.sin_reduce_arg_pos_rat_q1 246890413 1048576 226375608064910080 72057594037927936 37 212225892882329911689216 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 173682 1048576 212225892882329911689216 151115727451828646838272 3015911330 2147483648 267640 267378 (ep194 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz330 := (@Enclosure.Real.IsNear.recentre' qz44 Bool.false 331589 1048576 1 1048576 331589 1048576 1 1048576 (ep184 rfl rfl) rfl)

noncomputable def ep196 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz44 (Real.cos qz45)) (@HMul.hMul Real Real Real qz0 qz44 (@Neg.neg Real Real.instNeg (Real.sin qz45))) Bool.true 342893200599 1099511627776 12027627374023 48997536668581888 Bool.true 28795520349 549755813888 2997321241939 12249384167145472 (@Enclosure.Real.IsNear.mulLit_ft qz44 (Real.cos qz45) 331589 1048576 1 1048576 1034091 1048576 108400843 140183076864 342893200599 1099511627776 12027627374023 48997536668581888 qz330 (@Enclosure.Real.IsNear.recentre' (Real.cos qz45) Bool.true 1034091 1048576 108400843 140183076864 1034091 1048576 108400843 140183076864 (ep191 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz44 (@Neg.neg Real Real.instNeg (Real.sin qz45)) 331589 1048576 1 1048576 86841 524288 108400843 140183076864 28795520349 549755813888 2997321241939 12249384167145472 qz330 (@Enclosure.Real.IsNear.neg (Real.sin qz45) Bool.false 86841 524288 108400843 140183076864 (@Enclosure.Real.IsNear.recentre' (Real.sin qz45) Bool.false 173682 1048576 108400843 140183076864 86841 524288 108400843 140183076864 (ep195 rfl rfl) rfl)) rfl)

noncomputable def ep197 := @ep170 342893200599 1099511627776 12027627374023 48997536668581888 Bool.true 28795520349 549755813888 2997321241939 12249384167145472 Bool.false 1102174751459159970938880 62651381055 68719476736 114431868445295 36748152501436416 Bool.false 10128886842377652666368 4606084459 137438953472 228996334587283 73496305002872832 (ep171 (BSN.head_sum_c_succ qz5 9 10 rfl rfl) (ep182 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep183 ep196) rfl rfl

noncomputable abbrev qz331 := (@Nat.cast Real Real.instNatCast 11)

noncomputable abbrev qz46 := (@Inv.inv Real Real.instInv (Real.sqrt qz331))

noncomputable abbrev qz551 := (Real.log (Enclosure.sfrac Bool.false 11 1))

noncomputable abbrev qz47 := (@HMul.hMul Real Real Real qz268 qz284 qz551)

noncomputable def ep198 := @Enclosure.Complex.IsNear.of_eq qz40 (Complex.mk (@HMul.hMul Real Real Real qz0 qz46 (Real.cos qz47)) (@HMul.hMul Real Real Real qz0 qz46 (@Neg.neg Real Real.instNeg (Real.sin qz47)))) Bool.false 327547188239 1099511627776 11470099711599 48997536668581888 Bool.true 51133020081 1099511627776 11431138548077 48997536668581888 (BSN.cpow_neg_s_mk qz13 102256 1000 11 qz14 rfl)

noncomputable abbrev qz332 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 11) qz15)

noncomputable def ep199 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz331) 3477733 1048576 1 1048576 158078 158079 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz331) (Real.sqrt qz332) Bool.false 3477733 1048576 1 1048576 (BSN.sqrt_natCast_div_one 11) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz332) Bool.false 3477733 1048576 1 1048576 3477733 1048576 1 1048576 (BSN.sqrt_enclosure 11 1 1738866 1738867 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep200 := BSN.log_dyadic_bound 3 19 4 3 4939817505 524288 133689 41676111 10935 166961 22 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 3) (BSN.artanhQ 19) 0 3 41676111 4939817505 10935 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep201 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz551 102256 1000 0 1 10799156221662949 4503599627370496 1000000000401067 133689000000000000000 69017407412647907059 281474976710656000 6391000002563219197 8355562500000000000000 qz16 (BSN.isNear_log_sfrac 11 1 10799156221662949 4503599627370496 1000000000401067 133689000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz332) Bool.false 45294944137145793642496 18889465931478580854784 1000000000401067 133689000000000000000 10799156221662949 4503599627370496 1000000000401067 133689000000000000000 (BSN.log_rat_reduce_isNear 11 1 3 22 16 166961 524288 24973259072661432 36028797018963968 133689 1000000000000000 rfl rfl rfl rfl (ep200 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep202 := nat_lit 12231460200419063792426823237490321

noncomputable def ep203 := BSN.cos_dyadic_bound_f 332559667 2147483648 2 1 1048576 267640 ep202 ep62 ep202 ep202 ep63 ep202 1036027 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 332559667) qz292 0 1 ep202 ep62 ep202 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 332559667) qz293 0 1 ep202 ep63 ep202 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz333 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 128554939) qz20)

noncomputable def ep204 := @Enclosure.Real.IsNear.cos_image qz47 qz333 Bool.false 128554939 524288 803 1048576 Bool.false 1036027 1048576 1 133689 (@Enclosure.Real.IsNear.recentre' qz47 Bool.false 69017407412647907059 281474976710656000 6391000002563219197 8355562500000000000000 128554939 524288 803 1048576 (ep201 rfl) rfl) (Enclosure.sfrac_false_div 128554939 524288) (BSN.cos_reduce0 qz333 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 11700903088029138157568) qz21) 226375608064910080 72057594037927936 Bool.false 1036027 1048576 39 1000000000000000 267378 133689 (BSN.sin_reduce_arg_pos_rat_q0 128554939 524288 226375608064910080 72057594037927936 39 11700903088029138157568 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1036027 1048576 11700903088029138157568 75557863725914323419136 332559667 2147483648 267640 267378 (ep203 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep205 := BSN.sin_dyadic_bound_f 332559667 2147483648 1 0 1048576 267640 0 1 1 0 1 1 161733 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 332559667) qz287 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 332559667) qz288 0 0 rfl) rfl rfl

noncomputable def ep206 := @Enclosure.Real.IsNear.sin_image qz47 qz333 Bool.false 128554939 524288 803 1048576 Bool.false 161733 1048576 1 133689 (@Enclosure.Real.IsNear.recentre' qz47 Bool.false 69017407412647907059 281474976710656000 6391000002563219197 8355562500000000000000 128554939 524288 803 1048576 (ep201 rfl) rfl) (Enclosure.sfrac_false_div 128554939 524288) (BSN.sin_reduce0 qz333 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 11700903088029138157568) qz21) 226375608064910080 72057594037927936 Bool.false 161733 1048576 39 1000000000000000 267378 133689 (BSN.sin_reduce_arg_pos_rat_q0 128554939 524288 226375608064910080 72057594037927936 39 11700903088029138157568 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 161733 1048576 11700903088029138157568 75557863725914323419136 332559667 2147483648 267640 267378 (ep205 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz334 := (@Enclosure.Real.IsNear.recentre' qz46 Bool.false 316157 1048576 1 1048576 316157 1048576 1 1048576 (ep199 rfl rfl) rfl)

noncomputable def ep207 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz46 (Real.cos qz47)) (@HMul.hMul Real Real Real qz0 qz46 (@Neg.neg Real Real.instNeg (Real.sin qz47))) Bool.false 327547188239 1099511627776 11470099711599 48997536668581888 Bool.true 51133020081 1099511627776 11431138548077 48997536668581888 (@Enclosure.Real.IsNear.mulLit_ff qz46 (Real.cos qz47) 316157 1048576 1 1048576 1036027 1048576 108400843 140183076864 327547188239 1099511627776 11470099711599 48997536668581888 qz334 (@Enclosure.Real.IsNear.recentre' (Real.cos qz47) Bool.false 1036027 1048576 108400843 140183076864 1036027 1048576 108400843 140183076864 (ep204 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz46 (@Neg.neg Real Real.instNeg (Real.sin qz47)) 316157 1048576 1 1048576 161733 1048576 108400843 140183076864 51133020081 1099511627776 11431138548077 48997536668581888 qz334 (@Enclosure.Real.IsNear.neg (Real.sin qz47) Bool.false 161733 1048576 108400843 140183076864 (@Enclosure.Real.IsNear.recentre' (Real.sin qz47) Bool.false 161733 1048576 108400843 140183076864 161733 1048576 108400843 140183076864 (ep206 rfl rfl) rfl)) rfl)

noncomputable def ep208 := @ep168 327547188239 1099511627776 11470099711599 48997536668581888 Bool.true 51133020081 1099511627776 11431138548077 48997536668581888 Bool.false 91394793348329671491584 1329969285119 1099511627776 492137772915977 146992610005745664 Bool.true 1963225346606574338048 14284344409 1099511627776 492286084818797 146992610005745664 (ep169 (BSN.head_sum_c_succ qz5 10 11 rfl rfl) (ep197 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep198 ep207) rfl rfl

noncomputable abbrev qz335 := (@Nat.cast Real Real.instNatCast 12)

noncomputable abbrev qz48 := (@Inv.inv Real Real.instInv (Real.sqrt qz335))

noncomputable abbrev qz552 := (Real.log (Enclosure.sfrac Bool.false 12 1))

noncomputable abbrev qz49 := (@HMul.hMul Real Real Real qz268 qz284 qz552)

noncomputable def ep209 := @Enclosure.Complex.IsNear.of_eq qz39 (Complex.mk (@HMul.hMul Real Real Real qz0 qz48 (Real.cos qz49)) (@HMul.hMul Real Real Real qz0 qz48 (@Neg.neg Real Real.instNeg (Real.sin qz49)))) Bool.true 147817539495 549755813888 8235822102511 36748152501436416 Bool.true 57756101085 549755813888 4107966929213 18374076250718208 (BSN.cpow_neg_s_mk qz13 102256 1000 12 qz14 rfl)

noncomputable abbrev qz336 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 12) qz15)

noncomputable def ep210 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz335) 3632373 1048576 1 1048576 151348 151349 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz335) (Real.sqrt qz336) Bool.false 3632373 1048576 1 1048576 (BSN.sqrt_natCast_div_one 12) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz336) Bool.false 3632373 1048576 1 1048576 3632373 1048576 1 1048576 (BSN.sqrt_enclosure 12 1 1816186 1816187 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep211 := BSN.log_dyadic_bound 4 20 4 3 6720000000 524288 133689 91811840 61440 212580 24 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 4) (BSN.artanhQ 20) 0 3 91811840 6720000000 61440 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep212 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz552 102256 1000 0 1 11191020447815397 4503599627370496 1000000000401067 133689000000000000000 71521811681988202227 281474976710656000 6391000002563219197 8355562500000000000000 qz16 (BSN.isNear_log_sfrac 12 1 11191020447815397 4503599627370496 1000000000401067 133689000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz336) Bool.false 46938541828353910898688 18889465931478580854784 1000000000401067 133689000000000000000 11191020447815397 4503599627370496 1000000000401067 133689000000000000000 (BSN.log_rat_reduce_isNear 12 1 3 24 16 212580 524288 24973259072661432 36028797018963968 133689 1000000000000000 rfl rfl rfl rfl (ep211 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep213 := nat_lit 2822236021400899672490978749235130520434163533902376606867894430830837104640000

noncomputable def ep214 := nat_lit 1923056788467146198452817687793967206796034961907229109287159601561600000000

noncomputable def ep215 := nat_lit 7388457011725790429345544543168913511373710913139327028000877631868711731200000

noncomputable def ep216 := BSN.sin_dyadic_bound_f 2573350920 2147483648 3 2 1048576 267640 ep213 ep108 ep214 ep215 ep110 ep214 976670 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2573350920) qz287 0 2 ep213 ep108 ep214 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2573350920) qz288 0 2 ep215 ep110 ep214 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz337 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 266439511) qz26)

noncomputable def ep217 := @Enclosure.Real.IsNear.cos_image qz49 qz337 Bool.false 266439511 1048576 803 1048576 Bool.true 976670 1048576 1 133689 (@Enclosure.Real.IsNear.recentre' qz49 Bool.false 71521811681988202227 281474976710656000 6391000002563219197 8355562500000000000000 266439511 1048576 803 1048576 (ep212 rfl) rfl) (Enclosure.sfrac_false_div 266439511 1048576) (BSN.cos_reduce1 qz337 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 181083472638413962739712) qz27) 226375608064910080 72057594037927936 Bool.false 976670 1048576 40 1000000000000000 267378 133689 (BSN.sin_reduce_arg_pos_rat_q1 266439511 1048576 226375608064910080 72057594037927936 40 181083472638413962739712 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 976670 1048576 181083472638413962739712 151115727451828646838272 2573350920 2147483648 267640 267378 (ep216 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep218 := nat_lit 1568763592684262994138745001880758718999777978817723550086291199173381324800000

noncomputable def ep219 := nat_lit 4702444664475854690019329370266688222585741866529356192040299278317020774400000

noncomputable def ep220 := BSN.cos_dyadic_bound_f 2573350920 2147483648 3 2 1048576 267640 ep218 ep75 ep214 ep219 ep78 ep214 381610 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2573350920) qz292 0 2 ep218 ep75 ep214 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2573350920) qz293 0 2 ep219 ep78 ep214 rfl rfl rfl rfl) rfl rfl

noncomputable def ep221 := @Enclosure.Real.IsNear.sin_image qz49 qz337 Bool.false 266439511 1048576 803 1048576 Bool.false 381610 1048576 1 133689 (@Enclosure.Real.IsNear.recentre' qz49 Bool.false 71521811681988202227 281474976710656000 6391000002563219197 8355562500000000000000 266439511 1048576 803 1048576 (ep212 rfl) rfl) (Enclosure.sfrac_false_div 266439511 1048576) (BSN.sin_reduce1 qz337 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 181083472638413962739712) qz27) 226375608064910080 72057594037927936 Bool.false 381610 1048576 40 1000000000000000 267378 133689 (BSN.sin_reduce_arg_pos_rat_q1 266439511 1048576 226375608064910080 72057594037927936 40 181083472638413962739712 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 381610 1048576 181083472638413962739712 151115727451828646838272 2573350920 2147483648 267640 267378 (ep220 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz338 := (@Enclosure.Real.IsNear.recentre' qz48 Bool.false 302697 1048576 1 1048576 302697 1048576 1 1048576 (ep210 rfl rfl) rfl)

noncomputable def ep222 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz48 (Real.cos qz49)) (@HMul.hMul Real Real Real qz0 qz48 (@Neg.neg Real Real.instNeg (Real.sin qz49))) Bool.true 147817539495 549755813888 8235822102511 36748152501436416 Bool.true 57756101085 549755813888 4107966929213 18374076250718208 (@Enclosure.Real.IsNear.mulLit_ft qz48 (Real.cos qz49) 302697 1048576 1 1048576 488335 524288 108400843 140183076864 147817539495 549755813888 8235822102511 36748152501436416 qz338 (@Enclosure.Real.IsNear.recentre' (Real.cos qz49) Bool.true 976670 1048576 108400843 140183076864 488335 524288 108400843 140183076864 (ep217 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz48 (@Neg.neg Real Real.instNeg (Real.sin qz49)) 302697 1048576 1 1048576 190805 524288 108400843 140183076864 57756101085 549755813888 4107966929213 18374076250718208 qz338 (@Enclosure.Real.IsNear.neg (Real.sin qz49) Bool.false 190805 524288 108400843 140183076864 (@Enclosure.Real.IsNear.recentre' (Real.sin qz49) Bool.false 381610 1048576 108400843 140183076864 190805 524288 108400843 140183076864 (ep221 rfl rfl) rfl)) rfl)

noncomputable def ep223 := @ep166 147817539495 549755813888 8235822102511 36748152501436416 Bool.true 57756101085 549755813888 4107966929213 18374076250718208 Bool.false 568631243322646752919552 1034334206129 1099511627776 175027020442007 48997536668581888 Bool.true 71356406104389847089152 129796546579 1099511627776 175049940084167 48997536668581888 (ep167 (BSN.head_sum_c_succ qz5 11 12 rfl rfl) (ep208 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep209 ep222) rfl rfl

noncomputable abbrev qz339 := (@Nat.cast Real Real.instNatCast 13)

noncomputable abbrev qz50 := (@Inv.inv Real Real.instInv (Real.sqrt qz339))

noncomputable abbrev qz553 := (Real.log (Enclosure.sfrac Bool.false 13 1))

noncomputable abbrev qz51 := (@HMul.hMul Real Real Real qz268 qz284 qz553)

noncomputable def ep224 := @Enclosure.Complex.IsNear.of_eq qz38 (Complex.mk (@HMul.hMul Real Real Real qz0 qz50 (Real.cos qz51)) (@HMul.hMul Real Real Real qz0 qz50 (@Neg.neg Real Real.instNeg (Real.sin qz51)))) Bool.true 12713909091 1099511627776 31531411246645 146992610005745664 Bool.false 19042799217 68719476736 3958203489641 18374076250718208 (BSN.cpow_neg_s_mk qz13 102256 1000 13 qz14 rfl)

noncomputable abbrev qz340 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 13) qz15)

noncomputable def ep225 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz339) 3780695 1048576 1 1048576 145411 145412 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz339) (Real.sqrt qz340) Bool.false 3780695 1048576 1 1048576 (BSN.sqrt_natCast_div_one 13) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz340) Bool.false 3780695 1048576 1 1048576 3780695 1048576 1 1048576 (BSN.sqrt_enclosure 13 1 1890347 1890348 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep226 := BSN.log_dyadic_bound 5 21 5 4 35742602096145 524288 133689 699352521000 41015625 254545 26 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 5) (BSN.artanhQ 21) 0 4 699352521000 35742602096145 41015625 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep227 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz553 102256 1000 0 1 11551497052968677 4503599627370496 1000000000401067 133689000000000000000 73825617665522814707 281474976710656000 6391000002563219197 8355562500000000000000 qz16 (BSN.isNear_log_sfrac 13 1 11551497052968677 4503599627370496 1000000000401067 133689000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz340) Bool.false 48450490295254733815808 18889465931478580854784 1000000000401067 133689000000000000000 11551497052968677 4503599627370496 1000000000401067 133689000000000000000 (BSN.log_rat_reduce_isNear 13 1 3 26 16 254545 524288 24973259072661432 36028797018963968 133689 1000000000000000 rfl rfl rfl rfl (ep226 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep228 := nat_lit 4167664112019485360395804777581893712070155206180657722003597143463166410260736

noncomputable def ep229 := nat_lit 13517802242367200352659080332336712779982149487432367265092089172652832358656

noncomputable def ep230 := nat_lit 12475956731573721680482096172081007710650501319567108431480607252044193566064896

noncomputable def ep231 := BSN.cos_dyadic_bound_f 3283698398 2147483648 3 2 1048576 267640 ep228 ep75 ep229 ep230 ep78 ep229 43717 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3283698398) qz292 0 2 ep228 ep75 ep229 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3283698398) qz293 0 2 ep230 ep78 ep229 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz341 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 275021857) qz26)

noncomputable def ep232 := @Enclosure.Real.IsNear.cos_image qz51 qz341 Bool.false 275021857 1048576 803 1048576 Bool.true 43717 1048576 1 133689 (@Enclosure.Real.IsNear.recentre' qz51 Bool.false 73825617665522814707 281474976710656000 6391000002563219197 8355562500000000000000 275021857 1048576 803 1048576 (ep227 rfl) rfl) (Enclosure.sfrac_false_div 275021857 1048576) (BSN.cos_reduce2 qz341 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 231069732549127542145024) qz27) 226375608064910080 72057594037927936 Bool.false 43717 1048576 41 1000000000000000 267378 133689 (BSN.sin_reduce_arg_pos_rat_q2 275021857 1048576 226375608064910080 72057594037927936 41 231069732549127542145024 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 43717 1048576 231069732549127542145024 151115727451828646838272 3283698398 2147483648 267640 267378 (ep231 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep233 := nat_lit 7490981159841179888430321335381539311502293651535238005794401186895577272582400

noncomputable def ep234 := nat_lit 19597350405477352811984631653080248280862226559612637611032330202256502556754176

noncomputable def ep235 := BSN.sin_dyadic_bound_f 3283698398 2147483648 3 2 1048576 267640 ep233 ep108 ep229 ep234 ep110 ep229 1047664 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3283698398) qz287 0 2 ep233 ep108 ep229 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3283698398) qz288 0 2 ep234 ep110 ep229 rfl rfl rfl rfl) rfl rfl

noncomputable def ep236 := @Enclosure.Real.IsNear.sin_image qz51 qz341 Bool.false 275021857 1048576 803 1048576 Bool.true 1047664 1048576 1 133689 (@Enclosure.Real.IsNear.recentre' qz51 Bool.false 73825617665522814707 281474976710656000 6391000002563219197 8355562500000000000000 275021857 1048576 803 1048576 (ep227 rfl) rfl) (Enclosure.sfrac_false_div 275021857 1048576) (BSN.sin_reduce2 qz341 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 231069732549127542145024) qz27) 226375608064910080 72057594037927936 Bool.false 1047664 1048576 41 1000000000000000 267378 133689 (BSN.sin_reduce_arg_pos_rat_q2 275021857 1048576 226375608064910080 72057594037927936 41 231069732549127542145024 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1047664 1048576 231069732549127542145024 151115727451828646838272 3283698398 2147483648 267640 267378 (ep235 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz342 := (@Enclosure.Real.IsNear.recentre' qz50 Bool.false 290823 1048576 1 1048576 290823 1048576 1 1048576 (ep225 rfl rfl) rfl)

noncomputable def ep237 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz50 (Real.cos qz51)) (@HMul.hMul Real Real Real qz0 qz50 (@Neg.neg Real Real.instNeg (Real.sin qz51))) Bool.true 12713909091 1099511627776 31531411246645 146992610005745664 Bool.false 19042799217 68719476736 3958203489641 18374076250718208 (@Enclosure.Real.IsNear.mulLit_ft qz50 (Real.cos qz51) 290823 1048576 1 1048576 43717 1048576 108400843 140183076864 12713909091 1099511627776 31531411246645 146992610005745664 qz342 (@Enclosure.Real.IsNear.recentre' (Real.cos qz51) Bool.true 43717 1048576 108400843 140183076864 43717 1048576 108400843 140183076864 (ep232 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz50 (@Neg.neg Real Real.instNeg (Real.sin qz51)) 290823 1048576 1 1048576 65479 65536 108400843 140183076864 19042799217 68719476736 3958203489641 18374076250718208 qz342 (@Enclosure.Real.IsNear.neg (Real.sin qz51) Bool.true 65479 65536 108400843 140183076864 (@Enclosure.Real.IsNear.recentre' (Real.sin qz51) Bool.true 1047664 1048576 108400843 140183076864 65479 65536 108400843 140183076864 (ep236 rfl rfl) rfl)) rfl)

noncomputable def ep238 := @ep164 12713909091 1099511627776 31531411246645 146992610005745664 Bool.false 19042799217 68719476736 3958203489641 18374076250718208 Bool.false 1123283395765252011327488 510810148519 549755813888 278306236286333 73496305002872832 Bool.false 12018228401446477365248 174888240893 1099511627776 556815448169629 146992610005745664 (ep165 (BSN.head_sum_c_succ qz5 12 13 rfl rfl) (ep223 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep224 ep237) rfl rfl

noncomputable abbrev qz343 := (@Nat.cast Real Real.instNatCast 14)

noncomputable abbrev qz52 := (@Inv.inv Real Real.instInv (Real.sqrt qz343))

noncomputable abbrev qz554 := (Real.log (Enclosure.sfrac Bool.false 14 1))

noncomputable abbrev qz53 := (@HMul.hMul Real Real Real qz268 qz284 qz554)

noncomputable def ep239 := @Enclosure.Complex.IsNear.of_eq qz37 (Complex.mk (@HMul.hMul Real Real Real qz0 qz52 (Real.cos qz53)) (@HMul.hMul Real Real Real qz0 qz52 (@Neg.neg Real Real.instNeg (Real.sin qz53)))) Bool.false 279151453515 1099511627776 30511854127037 146992610005745664 Bool.false 91791632949 1099511627776 30422474741819 146992610005745664 (BSN.cpow_neg_s_mk qz13 102256 1000 14 qz14 rfl)

noncomputable abbrev qz344 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 14) qz15)

noncomputable def ep240 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz343) 3923413 1048576 1 1048576 140121 140122 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz343) (Real.sqrt qz344) Bool.false 3923413 1048576 1 1048576 (BSN.sqrt_natCast_div_one 14) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz344) Bool.false 3923413 1048576 1 1048576 3923413 1048576 1 1048576 (BSN.sqrt_enclosure 14 1 1961706 1961707 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep241 := BSN.log_dyadic_bound 6 22 5 4 51857700491520 524288 133689 1346332575744 176359680 293399 28 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 6) (BSN.artanhQ 22) 0 4 1346332575744 51857700491520 176359680 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep242 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz554 102256 1000 0 1 11885250371606245 4503599627370496 1000000000401067 133689000000000000000 15191727024987102359 56294995342131200 6391000002563219197 8355562500000000000000 qz16 (BSN.isNear_log_sfrac 14 1 11885250371606245 4503599627370496 1000000000401067 133689000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz344) Bool.false 49850353174629559828480 18889465931478580854784 1000000000401067 133689000000000000000 11885250371606245 4503599627370496 1000000000401067 133689000000000000000 (BSN.log_rat_reduce_isNear 14 1 3 28 16 293399 524288 24973259072661432 36028797018963968 133689 1000000000000000 rfl rfl rfl rfl (ep241 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep243 := nat_lit 3375444739333423916618082582550530281337596435751253424975738859705549788785185

noncomputable def ep244 := nat_lit 2750119347361253976174804664269698539638369785720552949642801727628046740001

noncomputable def ep245 := nat_lit 8835997933596572989466885651509237891581909494933544741589418191669804037810721

noncomputable def ep246 := BSN.sin_dyadic_bound_f 2691032499 2147483648 3 2 1048576 267640 ep243 ep108 ep244 ep245 ep110 ep244 996105 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2691032499) qz287 0 2 ep243 ep108 ep244 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2691032499) qz288 0 2 ep245 ep110 ep244 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz345 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 141483983) qz20)

noncomputable def ep247 := @Enclosure.Real.IsNear.cos_image qz53 qz345 Bool.false 141483983 524288 803 1048576 Bool.false 996105 1048576 1 133689 (@Enclosure.Real.IsNear.recentre' qz53 Bool.false 15191727024987102359 56294995342131200 6391000002563219197 8355562500000000000000 141483983 524288 803 1048576 (ep242 rfl) rfl) (Enclosure.sfrac_false_div 141483983 524288) (BSN.cos_reduce3 qz345 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 94682288772011404558336) qz21) 226375608064910080 72057594037927936 Bool.false 996105 1048576 42 1000000000000000 267378 133689 (BSN.sin_reduce_arg_pos_rat_q3 141483983 524288 226375608064910080 72057594037927936 42 94682288772011404558336 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 996105 1048576 94682288772011404558336 75557863725914323419136 2691032499 2147483648 267640 267378 (ep246 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep248 := nat_lit 1876469352672951622110568014601081133427392850877683259630807278382029014542881

noncomputable def ep249 := nat_lit 5623907819324132358379354434474704003202901813061608672993136231690830950148641

noncomputable def ep250 := BSN.cos_dyadic_bound_f 2691032499 2147483648 3 2 1048576 267640 ep248 ep75 ep244 ep249 ep78 ep244 327543 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2691032499) qz292 0 2 ep248 ep75 ep244 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2691032499) qz293 0 2 ep249 ep78 ep244 rfl rfl rfl rfl) rfl rfl

noncomputable def ep251 := @Enclosure.Real.IsNear.sin_image qz53 qz345 Bool.false 141483983 524288 803 1048576 Bool.true 327543 1048576 1 133689 (@Enclosure.Real.IsNear.recentre' qz53 Bool.false 15191727024987102359 56294995342131200 6391000002563219197 8355562500000000000000 141483983 524288 803 1048576 (ep242 rfl) rfl) (Enclosure.sfrac_false_div 141483983 524288) (BSN.sin_reduce3 qz345 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 94682288772011404558336) qz21) 226375608064910080 72057594037927936 Bool.false 327543 1048576 42 1000000000000000 267378 133689 (BSN.sin_reduce_arg_pos_rat_q3 141483983 524288 226375608064910080 72057594037927936 42 94682288772011404558336 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 327543 1048576 94682288772011404558336 75557863725914323419136 2691032499 2147483648 267640 267378 (ep250 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz346 := (@Enclosure.Real.IsNear.recentre' qz52 Bool.false 280243 1048576 1 1048576 280243 1048576 1 1048576 (ep240 rfl rfl) rfl)

noncomputable def ep252 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz52 (Real.cos qz53)) (@HMul.hMul Real Real Real qz0 qz52 (@Neg.neg Real Real.instNeg (Real.sin qz53))) Bool.false 279151453515 1099511627776 30511854127037 146992610005745664 Bool.false 91791632949 1099511627776 30422474741819 146992610005745664 (@Enclosure.Real.IsNear.mulLit_ff qz52 (Real.cos qz53) 280243 1048576 1 1048576 996105 1048576 108400843 140183076864 279151453515 1099511627776 30511854127037 146992610005745664 qz346 (@Enclosure.Real.IsNear.recentre' (Real.cos qz53) Bool.false 996105 1048576 108400843 140183076864 996105 1048576 108400843 140183076864 (ep247 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz52 (@Neg.neg Real Real.instNeg (Real.sin qz53)) 280243 1048576 1 1048576 327543 1048576 108400843 140183076864 91791632949 1099511627776 30422474741819 146992610005745664 qz346 (@Enclosure.Real.IsNear.neg (Real.sin qz53) Bool.true 327543 1048576 108400843 140183076864 (@Enclosure.Real.IsNear.recentre' (Real.sin qz53) Bool.true 327543 1048576 108400843 140183076864 327543 1048576 108400843 140183076864 (ep251 rfl rfl) rfl)) rfl)

noncomputable def ep253 := @ep162 279151453515 1099511627776 30511854127037 146992610005745664 Bool.false 91791632949 1099511627776 30422474741819 146992610005745664 Bool.false 715106832407783029080064 1300771750553 1099511627776 195708108899901 48997536668581888 Bool.false 293217622183115743035392 133339936921 549755813888 24468246787977 6124692083572736 (ep163 (BSN.head_sum_c_succ qz5 13 14 rfl rfl) (ep238 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep239 ep252) rfl rfl

noncomputable abbrev qz347 := (@Nat.cast Real Real.instNatCast 15)

noncomputable abbrev qz54 := (@Inv.inv Real Real.instInv (Real.sqrt qz347))

noncomputable abbrev qz555 := (Real.log (Enclosure.sfrac Bool.false 15 1))

noncomputable abbrev qz55 := (@HMul.hMul Real Real Real qz268 qz284 qz555)

noncomputable def ep254 := @Enclosure.Complex.IsNear.of_eq qz36 (Complex.mk (@HMul.hMul Real Real Real qz0 qz54 (Real.cos qz55)) (@HMul.hMul Real Real Real qz0 qz54 (@Neg.neg Real Real.instNeg (Real.sin qz55)))) Bool.false 127564766229 549755813888 7368660315097 36748152501436416 Bool.true 62257163691 549755813888 57441689207 287094941417472 (BSN.cpow_neg_s_mk qz13 102256 1000 15 qz14 rfl)

noncomputable abbrev qz348 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 15) qz15)

noncomputable def ep255 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz347) 4061117 1048576 1 1048576 135370 135371 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz347) (Real.sqrt qz348) Bool.false 4061117 1048576 1 1048576 (BSN.sqrt_natCast_div_one 15) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz348) Bool.false 4061117 1048576 1 1048576 4061117 1048576 1 1048576 (BSN.sqrt_enclosure 15 1 2030558 2030559 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep256 := BSN.log_dyadic_bound 7 23 6 5 430628584065881355 524288 133689 14087658153505881 266939110305 329571 30 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 7) (BSN.artanhQ 23) 0 5 14087658153505881 430628584065881355 266939110305 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep257 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz555 102256 1000 0 1 12195965485668069 4503599627370496 1000000000401067 133689000000000000000 77944415418904628979 281474976710656000 6391000002563219197 8355562500000000000000 qz16 (BSN.isNear_log_sfrac 15 1 12195965485668069 4503599627370496 1000000000401067 133689000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz348) Bool.false 51153586820399524478976 18889465931478580854784 1000000000401067 133689000000000000000 12195965485668069 4503599627370496 1000000000401067 133689000000000000000 (BSN.log_rat_reduce_isNear 15 1 3 30 16 329571 524288 24973259072661432 36028797018963968 133689 1000000000000000 rfl rfl rfl rfl (ep256 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep258 := nat_lit 903823416209032742984860558785432481

noncomputable def ep259 := BSN.cos_dyadic_bound_f 975036553 2147483648 2 1 1048576 267640 ep258 ep62 ep258 ep258 ep63 ep258 942338 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 975036553) qz292 0 1 ep258 ep62 ep258 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 975036553) qz293 0 1 ep258 ep63 ep258 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz349 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 145182787) qz20)

noncomputable def ep260 := @Enclosure.Real.IsNear.cos_image qz55 qz349 Bool.false 145182787 524288 803 1048576 Bool.false 942338 1048576 1 133689 (@Enclosure.Real.IsNear.recentre' qz55 Bool.false 77944415418904628979 281474976710656000 6391000002563219197 8355562500000000000000 145182787 524288 803 1048576 (ep257 rfl) rfl) (Enclosure.sfrac_false_div 145182787 524288) (BSN.cos_reduce0 qz349 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 34306048882061527220224) qz21) 226375608064910080 72057594037927936 Bool.false 942338 1048576 44 1000000000000000 267378 133689 (BSN.sin_reduce_arg_pos_rat_q0 145182787 524288 226375608064910080 72057594037927936 44 34306048882061527220224 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 942338 1048576 34306048882061527220224 75557863725914323419136 975036553 2147483648 267640 267378 (ep259 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep261 := BSN.sin_dyadic_bound_f 975036553 2147483648 2 1 1048576 267640 ep258 ep58 ep258 ep258 ep59 ep258 459902 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 975036553) qz287 0 1 ep258 ep58 ep258 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 975036553) qz288 0 1 ep258 ep59 ep258 rfl rfl rfl rfl) rfl rfl

noncomputable def ep262 := @Enclosure.Real.IsNear.sin_image qz55 qz349 Bool.false 145182787 524288 803 1048576 Bool.false 459902 1048576 1 133689 (@Enclosure.Real.IsNear.recentre' qz55 Bool.false 77944415418904628979 281474976710656000 6391000002563219197 8355562500000000000000 145182787 524288 803 1048576 (ep257 rfl) rfl) (Enclosure.sfrac_false_div 145182787 524288) (BSN.sin_reduce0 qz349 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 34306048882061527220224) qz21) 226375608064910080 72057594037927936 Bool.false 459902 1048576 44 1000000000000000 267378 133689 (BSN.sin_reduce_arg_pos_rat_q0 145182787 524288 226375608064910080 72057594037927936 44 34306048882061527220224 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 459902 1048576 34306048882061527220224 75557863725914323419136 975036553 2147483648 267640 267378 (ep261 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz350 := (@Enclosure.Real.IsNear.recentre' qz54 Bool.false 270741 1048576 1 1048576 270741 1048576 1 1048576 (ep255 rfl rfl) rfl)

noncomputable def ep263 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz54 (Real.cos qz55)) (@HMul.hMul Real Real Real qz0 qz54 (@Neg.neg Real Real.instNeg (Real.sin qz55))) Bool.false 127564766229 549755813888 7368660315097 36748152501436416 Bool.true 62257163691 549755813888 57441689207 287094941417472 (@Enclosure.Real.IsNear.mulLit_ff qz54 (Real.cos qz55) 270741 1048576 1 1048576 471169 524288 108400843 140183076864 127564766229 549755813888 7368660315097 36748152501436416 qz350 (@Enclosure.Real.IsNear.recentre' (Real.cos qz55) Bool.false 942338 1048576 108400843 140183076864 471169 524288 108400843 140183076864 (ep260 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz54 (@Neg.neg Real Real.instNeg (Real.sin qz55)) 270741 1048576 1 1048576 229951 524288 108400843 140183076864 62257163691 549755813888 57441689207 287094941417472 qz350 (@Enclosure.Real.IsNear.neg (Real.sin qz55) Bool.false 229951 524288 108400843 140183076864 (@Enclosure.Real.IsNear.recentre' (Real.sin qz55) Bool.false 459902 1048576 108400843 140183076864 229951 524288 108400843 140183076864 (ep262 rfl rfl) rfl)) rfl)

noncomputable def ep264 := @ep160 127564766229 549755813888 7368660315097 36748152501436416 Bool.true 62257163691 549755813888 57441689207 287094941417472 Bool.false 855365776171095732256768 1555901283011 1099511627776 616598967960091 146992610005745664 Bool.false 39078167850474788618240 35541386615 274877906944 77081008473179 18374076250718208 (ep161 (BSN.head_sum_c_succ qz5 14 15 rfl rfl) (ep253 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep254 ep263) rfl rfl

noncomputable abbrev qz351 := (@Nat.cast Real Real.instNatCast 16)

noncomputable abbrev qz56 := (@Inv.inv Real Real.instInv (Real.sqrt qz351))

noncomputable abbrev qz556 := (Real.log (Enclosure.sfrac Bool.false 16 1))

noncomputable abbrev qz57 := (@HMul.hMul Real Real Real qz268 qz284 qz556)

noncomputable def ep265 := @Enclosure.Complex.IsNear.of_eq qz35 (Complex.mk (@HMul.hMul Real Real Real qz0 qz56 (Real.cos qz57)) (@HMul.hMul Real Real Real qz0 qz56 (@Neg.neg Real Real.instNeg (Real.sin qz57)))) Bool.false 197242422489 1099511627776 28517221265839 146992610005745664 Bool.true 191448537903 1099511627776 28514266471561 146992610005745664 (BSN.cpow_neg_s_mk qz13 102256 1000 16 qz14 rfl)

noncomputable abbrev qz352 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 16) qz15)

noncomputable def ep266 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz351) 4194305 1048576 1 1048576 131071 131072 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz351) (Real.sqrt qz352) Bool.false 4194305 1048576 1 1048576 (BSN.sqrt_natCast_div_one 16) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz352) Bool.false 4194305 1048576 1 1048576 4194305 1048576 1 1048576 (BSN.sqrt_enclosure 16 1 2097152 2097153 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep267 := BSN.log_dyadic_bound 0 32 1 0 1 524288 133689 0 1 0 32 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 0) (BSN.artanhQ 32) 0 0 rfl) rfl rfl rfl

noncomputable def ep268 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz556 102256 1000 0 1 3121657384082679 1125899906842624 250000000133689 33422250000000000000 19950512341672401489 70368744177664000 1597750000854406399 2088890625000000000000 qz16 (BSN.isNear_log_sfrac 16 1 3121657384082679 1125899906842624 250000000133689 33422250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz352) Bool.false 52372720210750067441664 18889465931478580854784 1000000000534756 133689000000000000000 3121657384082679 1125899906842624 250000000133689 33422250000000000000 (BSN.log_rat_reduce_isNear 16 1 4 32 32 0 524288 24973259072661432 36028797018963968 133689 1000000000000000 rfl rfl rfl rfl (ep267 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep269 := nat_lit 267864215875281711501220203342607517820491027743307099885933465637294929084416

noncomputable def ep270 := nat_lit 56181032603829604345808895991584612314655489397932405592802168806504923136

noncomputable def ep271 := nat_lit 803480285560637475294968992235839384236843772251125434846614792574271777406976

noncomputable def ep272 := BSN.cos_dyadic_bound_f 1654621696 2147483648 3 2 1048576 267640 ep269 ep75 ep270 ep271 ep78 ep270 752423 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1654621696) qz292 0 2 ep269 ep75 ep270 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1654621696) qz293 0 2 ep271 ep78 ep270 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz353 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 37160725) (@Nat.cast Real Real.instNatCast 131072))

noncomputable abbrev qz354 := (@Nat.cast Real Real.instNatCast 18889465931478580854784)

noncomputable def ep273 := @Enclosure.Real.IsNear.cos_image qz57 qz353 Bool.false 37160725 131072 803 1048576 Bool.false 752423 1048576 1 133689 (@Enclosure.Real.IsNear.recentre' qz57 Bool.false 19950512341672401489 70368744177664000 1597750000854406399 2088890625000000000000 37160725 131072 803 1048576 (ep268 rfl) rfl) (Enclosure.sfrac_false_div 37160725 131072) (BSN.cos_reduce0 qz353 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 14554206359058277990400) qz354) 226375608064910080 72057594037927936 Bool.false 752423 1048576 45 1000000000000000 267378 133689 (BSN.sin_reduce_arg_pos_rat_q0 37160725 131072 226375608064910080 72057594037927936 45 14554206359058277990400 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 752423 1048576 14554206359058277990400 18889465931478580854784 1654621696 2147483648 267640 267378 (ep272 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep274 := nat_lit 7495400763390147395822221294154285056

noncomputable def ep275 := BSN.sin_dyadic_bound_f 1654621696 2147483648 2 1 1048576 267640 ep274 ep58 ep274 ep274 ep59 ep274 730321 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1654621696) qz287 0 1 ep274 ep58 ep274 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1654621696) qz288 0 1 ep274 ep59 ep274 rfl rfl rfl rfl) rfl rfl

noncomputable def ep276 := @Enclosure.Real.IsNear.sin_image qz57 qz353 Bool.false 37160725 131072 803 1048576 Bool.false 730321 1048576 1 133689 (@Enclosure.Real.IsNear.recentre' qz57 Bool.false 19950512341672401489 70368744177664000 1597750000854406399 2088890625000000000000 37160725 131072 803 1048576 (ep268 rfl) rfl) (Enclosure.sfrac_false_div 37160725 131072) (BSN.sin_reduce0 qz353 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 14554206359058277990400) qz354) 226375608064910080 72057594037927936 Bool.false 730321 1048576 45 1000000000000000 267378 133689 (BSN.sin_reduce_arg_pos_rat_q0 37160725 131072 226375608064910080 72057594037927936 45 14554206359058277990400 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 730321 1048576 14554206359058277990400 18889465931478580854784 1654621696 2147483648 267640 267378 (ep275 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz355 := (@Enclosure.Real.IsNear.recentre' qz56 Bool.false 262143 1048576 1 1048576 262143 1048576 1 1048576 (ep266 rfl rfl) rfl)

noncomputable def ep277 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz56 (Real.cos qz57)) (@HMul.hMul Real Real Real qz0 qz56 (@Neg.neg Real Real.instNeg (Real.sin qz57))) Bool.false 197242422489 1099511627776 28517221265839 146992610005745664 Bool.true 191448537903 1099511627776 28514266471561 146992610005745664 (@Enclosure.Real.IsNear.mulLit_ff qz56 (Real.cos qz57) 262143 1048576 1 1048576 752423 1048576 108400843 140183076864 197242422489 1099511627776 28517221265839 146992610005745664 qz355 (@Enclosure.Real.IsNear.recentre' (Real.cos qz57) Bool.false 752423 1048576 108400843 140183076864 752423 1048576 108400843 140183076864 (ep273 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz56 (@Neg.neg Real Real.instNeg (Real.sin qz57)) 262143 1048576 1 1048576 730321 1048576 108400843 140183076864 191448537903 1099511627776 28514266471561 146992610005745664 qz355 (@Enclosure.Real.IsNear.neg (Real.sin qz57) Bool.false 730321 1048576 108400843 140183076864 (@Enclosure.Real.IsNear.recentre' (Real.sin qz57) Bool.false 730321 1048576 108400843 140183076864 730321 1048576 108400843 140183076864 (ep276 rfl rfl) rfl)) rfl)

noncomputable def ep278 := @ep157 197242422489 1099511627776 28517221265839 146992610005745664 Bool.true 191448537903 1099511627776 28514266471561 146992610005745664 Bool.false ep158 438285926375 274877906944 322558094612965 73496305002872832 Bool.true 13546805535790902280192 49282991443 1099511627776 645162334256993 146992610005745664 (ep159 (BSN.head_sum_c_succ qz5 15 16 rfl rfl) (ep264 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep265 ep277) rfl rfl

theorem EMRow31.d7 : Enclosure.Complex.IsNear qz34 Bool.false 438285926375 274877906944 322558094612965 73496305002872832 Bool.true 49282991443 1099511627776 645162334256993 146992610005745664 := ep156 (BSN.head_sum_c_succ qz5 16 17 rfl rfl) (ep278 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable abbrev qz58 := (BSN.headSumC qz272 25)

noncomputable abbrev qz557 := (@Nat.cast Complex Complex.instNatCast 24)

noncomputable abbrev qz59 := (@HPow.hPow Complex Complex Complex qz274 qz557 qz275)

noncomputable def ep279 := @Enclosure.Complex.IsNear.of_eq qz58 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 24) qz59) Bool.false 1157118903181 549755813888 423896079809177 73496305002872832 Bool.false 14627143323 137438953472 105962410767179 18374076250718208

noncomputable def ep280 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 24) qz59 Bool.false 1177194049069 549755813888 412282482632629 73496305002872832 Bool.true 25949582039 274877906944 206089812026993 36748152501436416 Bool.true

noncomputable abbrev qz558 := (@Nat.cast Complex Complex.instNatCast 23)

noncomputable abbrev qz60 := (@HPow.hPow Complex Complex Complex qz274 qz558 qz275)

noncomputable def ep281 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 24) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 23) qz60) Bool.false 1177194049069 549755813888 412282482632629 73496305002872832 Bool.true 25949582039 274877906944 206089812026993 36748152501436416

noncomputable def ep282 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 23) qz60 Bool.false 1039476031 536870912 6255670816097 1148379765669888 Bool.true 62651683343 1099511627776 800632895124481 146992610005745664 Bool.false

noncomputable abbrev qz559 := (@Nat.cast Complex Complex.instNatCast 22)

noncomputable abbrev qz61 := (@HPow.hPow Complex Complex Complex qz274 qz559 qz275)

noncomputable def ep283 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 23) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 22) qz61) Bool.false 1039476031 536870912 6255670816097 1148379765669888 Bool.true 62651683343 1099511627776 800632895124481 146992610005745664

noncomputable def ep284 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 22) qz61 Bool.false 1104336651853 549755813888 64703687661253 12249384167145472 Bool.false 78877140371 549755813888 129377869135257 24498768334290944 Bool.true

noncomputable abbrev qz560 := (@Nat.cast Complex Complex.instNatCast 21)

noncomputable abbrev qz62 := (@HPow.hPow Complex Complex Complex qz274 qz560 qz275)

noncomputable def ep285 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 22) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 21) qz62) Bool.false 1104336651853 549755813888 64703687661253 12249384167145472 Bool.false 78877140371 549755813888 129377869135257 24498768334290944

noncomputable def ep286 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 21) qz62 Bool.false 1218841755413 549755813888 46960773027641 9187038125359104 Bool.false 43092522169 549755813888 375689651980099 73496305002872832 Bool.true

noncomputable abbrev qz561 := (@Nat.cast Complex Complex.instNatCast 20)

noncomputable abbrev qz63 := (@HPow.hPow Complex Complex Complex qz274 qz561 qz275)

noncomputable def ep287 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 21) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 20) qz63) Bool.false 1218841755413 549755813888 46960773027641 9187038125359104 Bool.false 43092522169 549755813888 375689651980099 73496305002872832

noncomputable def ep288 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 20) qz63 Bool.false 18994046547 8589934592 60495995639453 12249384167145472 Bool.true 159588878497 1099511627776 241940807828951 48997536668581888 Bool.false

noncomputable abbrev qz562 := (@Nat.cast Complex Complex.instNatCast 19)

noncomputable abbrev qz64 := (@HPow.hPow Complex Complex Complex qz274 qz562 qz275)

noncomputable def ep289 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 20) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 19) qz64) Bool.false 18994046547 8589934592 60495995639453 12249384167145472 Bool.true 159588878497 1099511627776 241940807828951 48997536668581888

noncomputable def ep290 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 19) qz64 Bool.false 2210645114457 1099511627776 699720287708827 146992610005745664 Bool.true 281924195711 1099511627776 699645369462739 146992610005745664 Bool.false

noncomputable def ep291 := nat_lit 2673174404728970507452416

noncomputable abbrev qz356 := (@Nat.cast Complex Complex.instNatCast 18)

noncomputable def ep292 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 19) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 18) (@HPow.hPow Complex Complex Complex qz6 qz356 qz7)) Bool.false 2210645114457 1099511627776 699720287708827 146992610005745664 Bool.true 281924195711 1099511627776 699645369462739 146992610005745664

noncomputable def ep293 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 18) (@HPow.hPow Complex Complex Complex qz6 qz356 qz7) Bool.false 979711892319 549755813888 336396455917775 73496305002872832 Bool.true 218285284721 1099511627776 672819460732993 146992610005745664 Bool.false

noncomputable def ep294 := nat_lit 1215315004115838950178816

noncomputable abbrev qz357 := (@Nat.cast Complex Complex.instNatCast 17)

noncomputable def ep295 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 18) (@HAdd.hAdd Complex Complex Complex qz4 qz34 (@HPow.hPow Complex Complex Complex qz6 qz357 qz7)) Bool.false 979711892319 549755813888 336396455917775 73496305002872832 Bool.true 218285284721 1099511627776 672819460732993 146992610005745664

noncomputable def ep296 := @Enclosure.Complex.IsNear.addLitP qz34 (@HPow.hPow Complex Complex Complex qz6 qz357 qz7) Bool.false 438285926375 274877906944 322558094612965 73496305002872832 Bool.true 49282991443 1099511627776 645162334256993 146992610005745664 Bool.false

noncomputable abbrev qz358 := (@Nat.cast Real Real.instNatCast 17)

noncomputable abbrev qz65 := (@Inv.inv Real Real.instInv (Real.sqrt qz358))

noncomputable abbrev qz563 := (Real.log (Enclosure.sfrac Bool.false 17 1))

noncomputable abbrev qz66 := (@HMul.hMul Real Real Real qz268 qz284 qz563)

noncomputable def ep297 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz357 qz7) (Complex.mk (@HMul.hMul Real Real Real qz0 qz65 (Real.cos qz66)) (@HMul.hMul Real Real Real qz0 qz65 (@Neg.neg Real Real.instNeg (Real.sin qz66)))) Bool.false 103140039569 549755813888 6919180652405 36748152501436416 Bool.true 84501146639 549755813888 864285202375 4593519062679552 (BSN.cpow_neg_s_mk qz13 102256 1000 17 qz14 rfl)

noncomputable abbrev qz359 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 17) qz15)

noncomputable def ep298 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz358) 4323389 1048576 1 1048576 127158 127159 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz358) (Real.sqrt qz359) Bool.false 4323389 1048576 1 1048576 (BSN.sqrt_natCast_div_one 17) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz359) Bool.false 4323389 1048576 1 1048576 4323389 1048576 1 1048576 (BSN.sqrt_enclosure 17 1 2161694 2161695 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep299 := BSN.log_dyadic_bound 1 33 2 1 3267 524288 133689 1 1 31784 34 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 1) (BSN.artanhQ 33) 0 1 1 3267 1 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep300 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz563 102256 1000 0 1 3189913004350711 1125899906842624 250000000133689 33422250000000000000 20386734010805394001 70368744177664000 1597750000854406399 2088890625000000000000 qz16 (BSN.isNear_log_sfrac 17 1 3189913004350711 1125899906842624 250000000133689 33422250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz359) Bool.false 53517859495200818200576 18889465931478580854784 1000000000534756 133689000000000000000 3189913004350711 1125899906842624 250000000133689 33422250000000000000 (BSN.log_rat_reduce_isNear 17 1 4 34 32 31784 524288 24973259072661432 36028797018963968 133689 1000000000000000 rfl rfl rfl rfl (ep299 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep301 := nat_lit 168690343998298508728170973866642933836687865551676690383731054376678148119361

noncomputable def ep302 := nat_lit 22284772631847836977762833400798875260384237779614837760651064133025897281

noncomputable def ep303 := nat_lit 506026462449631830510557395933127203759542828179470841475671861001768392563521

noncomputable def ep304 := BSN.cos_dyadic_bound_f 1474012023 2147483648 3 2 1048576 267640 ep301 ep75 ep302 ep303 ep78 ep302 811114 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1474012023) qz292 0 2 ep301 ep75 ep302 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1474012023) qz293 0 2 ep303 ep78 ep302 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz360 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 303786009) qz26)

noncomputable def ep305 := @Enclosure.Real.IsNear.cos_image qz66 qz360 Bool.false 303786009 1048576 803 1048576 Bool.false 811114 1048576 1 133689 (@Enclosure.Real.IsNear.recentre' qz66 Bool.false 20386734010805394001 70368744177664000 1597750000854406399 2088890625000000000000 303786009 1048576 803 1048576 (ep300 rfl) rfl) (Enclosure.sfrac_false_div 303786009 1048576) (BSN.cos_reduce0 qz360 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 103724375030752637616128) qz27) 226375608064910080 72057594037927936 Bool.false 811114 1048576 46 1000000000000000 267378 133689 (BSN.sin_reduce_arg_pos_rat_q0 303786009 1048576 226375608064910080 72057594037927936 46 103724375030752637616128 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 811114 1048576 103724375030752637616128 151115727451828646838272 1474012023 2147483648 267640 267378 (ep304 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep306 := nat_lit 4720675018665004117989530594272295841

noncomputable def ep307 := BSN.sin_dyadic_bound_f 1474012023 2147483648 2 1 1048576 267640 ep306 ep58 ep306 ep306 ep59 ep306 664534 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1474012023) qz287 0 1 ep306 ep58 ep306 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1474012023) qz288 0 1 ep306 ep59 ep306 rfl rfl rfl rfl) rfl rfl

noncomputable def ep308 := @Enclosure.Real.IsNear.sin_image qz66 qz360 Bool.false 303786009 1048576 803 1048576 Bool.false 664534 1048576 1 133689 (@Enclosure.Real.IsNear.recentre' qz66 Bool.false 20386734010805394001 70368744177664000 1597750000854406399 2088890625000000000000 303786009 1048576 803 1048576 (ep300 rfl) rfl) (Enclosure.sfrac_false_div 303786009 1048576) (BSN.sin_reduce0 qz360 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 103724375030752637616128) qz27) 226375608064910080 72057594037927936 Bool.false 664534 1048576 46 1000000000000000 267378 133689 (BSN.sin_reduce_arg_pos_rat_q0 303786009 1048576 226375608064910080 72057594037927936 46 103724375030752637616128 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 664534 1048576 103724375030752637616128 151115727451828646838272 1474012023 2147483648 267640 267378 (ep307 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz361 := (@Enclosure.Real.IsNear.recentre' qz65 Bool.false 254317 1048576 1 1048576 254317 1048576 1 1048576 (ep298 rfl rfl) rfl)

noncomputable def ep309 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz65 (Real.cos qz66)) (@HMul.hMul Real Real Real qz0 qz65 (@Neg.neg Real Real.instNeg (Real.sin qz66))) Bool.false 103140039569 549755813888 6919180652405 36748152501436416 Bool.true 84501146639 549755813888 864285202375 4593519062679552 (@Enclosure.Real.IsNear.mulLit_ff qz65 (Real.cos qz66) 254317 1048576 1 1048576 405557 524288 108400843 140183076864 103140039569 549755813888 6919180652405 36748152501436416 qz361 (@Enclosure.Real.IsNear.recentre' (Real.cos qz66) Bool.false 811114 1048576 108400843 140183076864 405557 524288 108400843 140183076864 (ep305 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz65 (@Neg.neg Real Real.instNeg (Real.sin qz66)) 254317 1048576 1 1048576 332267 524288 108400843 140183076864 84501146639 549755813888 864285202375 4593519062679552 qz361 (@Enclosure.Real.IsNear.neg (Real.sin qz66) Bool.false 332267 524288 108400843 140183076864 (@Enclosure.Real.IsNear.recentre' (Real.sin qz66) Bool.false 664534 1048576 108400843 140183076864 332267 524288 108400843 140183076864 (ep308 rfl rfl) rfl)) rfl)

noncomputable def ep310 := @ep296 103140039569 549755813888 6919180652405 36748152501436416 Bool.true 84501146639 549755813888 864285202375 4593519062679552 Bool.false 269301154368792230363136 979711892319 549755813888 336396455917775 73496305002872832 Bool.true 120003604361567166005248 218285284721 1099511627776 672819460732993 146992610005745664 EMRow31.d7 (ep297 ep309) rfl rfl

noncomputable abbrev qz362 := (@Nat.cast Real Real.instNatCast 18)

noncomputable abbrev qz67 := (@Inv.inv Real Real.instInv (Real.sqrt qz362))

noncomputable abbrev qz564 := (Real.log (Enclosure.sfrac Bool.false 18 1))

noncomputable abbrev qz68 := (@HMul.hMul Real Real Real qz268 qz284 qz564)

noncomputable def ep311 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz356 qz7) (Complex.mk (@HMul.hMul Real Real Real qz0 qz67 (Real.cos qz68)) (@HMul.hMul Real Real Real qz0 qz67 (@Neg.neg Real Real.instNeg (Real.sin qz68)))) Bool.false 251221329819 1099511627776 8975791957759 48997536668581888 Bool.true 31819455495 549755813888 4470984788291 24498768334290944 (BSN.cpow_neg_s_mk qz13 102256 1000 18 qz14 rfl)

noncomputable abbrev qz363 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 18) qz15)

noncomputable def ep312 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz362) 4448731 1048576 1 1048576 123575 123576 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz362) (Real.sqrt qz363) Bool.false 4448731 1048576 1 1048576 (BSN.sqrt_natCast_div_one 18) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz363) Bool.false 4448731 1048576 1 1048576 4448731 1048576 1 1048576 (BSN.sqrt_enclosure 18 1 2224365 2224366 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep313 := BSN.log_dyadic_bound 2 34 2 1 3468 524288 133689 4 4 61752 36 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 2) (BSN.artanhQ 34) 0 1 4 3468 4 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep314 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz564 102256 1000 0 1 3254268794313975 1125899906842624 250000000133689 33422250000000000000 831921274578424569 2814749767106560 1597750000854406399 2088890625000000000000 qz16 (BSN.isNear_log_sfrac 18 1 3254268794313975 1125899906842624 250000000133689 33422250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz363) Bool.false 54597570484265130393600 18889465931478580854784 1000000000534756 133689000000000000000 3254268794313975 1125899906842624 250000000133689 33422250000000000000 (BSN.log_rat_reduce_isNear 18 1 4 36 32 61752 524288 24973259072661432 36028797018963968 133689 1000000000000000 rfl rfl rfl rfl (ep313 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep315 := nat_lit 80579132399004611638859805439402561

noncomputable def ep316 := BSN.cos_dyadic_bound_f 532789487 2147483648 2 1 1048576 267640 ep315 ep62 ep315 ep315 ep63 ep315 1016469 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 532789487) qz292 0 1 ep315 ep62 ep315 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 532789487) qz293 0 1 ep315 ep63 ep315 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz364 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 309914825) qz26)

noncomputable def ep317 := @Enclosure.Real.IsNear.cos_image qz68 qz364 Bool.false 309914825 1048576 803 1048576 Bool.false 1016469 1048576 1 133689 (@Enclosure.Real.IsNear.recentre' qz68 Bool.false 831921274578424569 2814749767106560 1597750000854406399 2088890625000000000000 309914825 1048576 803 1048576 (ep314 rfl) rfl) (Enclosure.sfrac_false_div 309914825 1048576) (BSN.cos_reduce0 qz364 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 37491727143982711439360) qz27) 226375608064910080 72057594037927936 Bool.false 1016469 1048576 47 1000000000000000 267378 133689 (BSN.sin_reduce_arg_pos_rat_q0 309914825 1048576 226375608064910080 72057594037927936 47 37491727143982711439360 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1016469 1048576 37491727143982711439360 151115727451828646838272 532789487 2147483648 267640 267378 (ep316 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep318 := BSN.sin_dyadic_bound_f 532789487 2147483648 2 1 1048576 267640 ep315 ep58 ep315 ep315 ep59 ep315 257490 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 532789487) qz287 0 1 ep315 ep58 ep315 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 532789487) qz288 0 1 ep315 ep59 ep315 rfl rfl rfl rfl) rfl rfl

noncomputable def ep319 := @Enclosure.Real.IsNear.sin_image qz68 qz364 Bool.false 309914825 1048576 803 1048576 Bool.false 257490 1048576 1 133689 (@Enclosure.Real.IsNear.recentre' qz68 Bool.false 831921274578424569 2814749767106560 1597750000854406399 2088890625000000000000 309914825 1048576 803 1048576 (ep314 rfl) rfl) (Enclosure.sfrac_false_div 309914825 1048576) (BSN.sin_reduce0 qz364 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 37491727143982711439360) qz27) 226375608064910080 72057594037927936 Bool.false 257490 1048576 47 1000000000000000 267378 133689 (BSN.sin_reduce_arg_pos_rat_q0 309914825 1048576 226375608064910080 72057594037927936 47 37491727143982711439360 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 257490 1048576 37491727143982711439360 151115727451828646838272 532789487 2147483648 267640 267378 (ep318 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz365 := (@Enclosure.Real.IsNear.recentre' qz67 Bool.false 247151 1048576 1 1048576 247151 1048576 1 1048576 (ep312 rfl rfl) rfl)

noncomputable def ep320 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz67 (Real.cos qz68)) (@HMul.hMul Real Real Real qz0 qz67 (@Neg.neg Real Real.instNeg (Real.sin qz68))) Bool.false 251221329819 1099511627776 8975791957759 48997536668581888 Bool.true 31819455495 549755813888 4470984788291 24498768334290944 (@Enclosure.Real.IsNear.mulLit_ff qz67 (Real.cos qz68) 247151 1048576 1 1048576 1016469 1048576 108400843 140183076864 251221329819 1099511627776 8975791957759 48997536668581888 qz365 (@Enclosure.Real.IsNear.recentre' (Real.cos qz68) Bool.false 1016469 1048576 108400843 140183076864 1016469 1048576 108400843 140183076864 (ep317 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz67 (@Neg.neg Real Real.instNeg (Real.sin qz68)) 247151 1048576 1 1048576 128745 524288 108400843 140183076864 31819455495 549755813888 4470984788291 24498768334290944 qz365 (@Enclosure.Real.IsNear.neg (Real.sin qz68) Bool.false 128745 524288 108400843 140183076864 (@Enclosure.Real.IsNear.recentre' (Real.sin qz68) Bool.false 257490 1048576 108400843 140183076864 128745 524288 108400843 140183076864 (ep319 rfl rfl) rfl)) rfl)

noncomputable def ep321 := @ep293 251221329819 1099511627776 8975791957759 48997536668581888 Bool.true 31819455495 549755813888 4470984788291 24498768334290944 Bool.false ep294 2210645114457 1099511627776 699720287708827 146992610005745664 Bool.true 154989465667820603834368 281924195711 1099511627776 699645369462739 146992610005745664 (ep295 (BSN.head_sum_c_succ qz5 17 18 rfl rfl) (ep310 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep311 ep320) rfl rfl

noncomputable abbrev qz366 := (@Nat.cast Real Real.instNatCast 19)

noncomputable abbrev qz69 := (@Inv.inv Real Real.instInv (Real.sqrt qz366))

noncomputable abbrev qz565 := (Real.log (Enclosure.sfrac Bool.false 19 1))

noncomputable abbrev qz70 := (@HMul.hMul Real Real Real qz268 qz284 qz565)

noncomputable def ep322 := @Enclosure.Complex.IsNear.of_eq qz64 (Complex.mk (@HMul.hMul Real Real Real qz0 qz69 (Real.cos qz70)) (@HMul.hMul Real Real Real qz0 qz69 (@Neg.neg Real Real.instNeg (Real.sin qz70)))) Bool.false 220592843559 1099511627776 26231659964609 146992610005745664 Bool.false 61167658607 549755813888 13088527012057 73496305002872832 (BSN.cpow_neg_s_mk qz13 102256 1000 19 qz14 rfl)

noncomputable abbrev qz367 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 19) qz15)

noncomputable def ep323 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz366) 4570637 1048576 1 1048576 120279 120280 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz366) (Real.sqrt qz367) Bool.false 4570637 1048576 1 1048576 (BSN.sqrt_natCast_div_one 19) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz367) Bool.false 4570637 1048576 1 1048576 4570637 1048576 1 1048576 (BSN.sqrt_enclosure 19 1 2285318 2285319 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep324 := BSN.log_dyadic_bound 3 35 3 2 22509375 524288 133689 55368 243 90099 38 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 3) (BSN.artanhQ 35) 0 2 55368 22509375 243 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep325 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz565 102256 1000 0 1 3315143513283831 1125899906842624 250000000133689 33422250000000000000 21187082193396963921 70368744177664000 1597750000854406399 2088890625000000000000 qz16 (BSN.isNear_log_sfrac 19 1 3315143513283831 1125899906842624 250000000133689 33422250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz367) Bool.false 55618878793361701994496 18889465931478580854784 1000000000534756 133689000000000000000 3315143513283831 1125899906842624 250000000133689 33422250000000000000 (BSN.log_rat_reduce_isNear 19 1 4 38 32 90099 524288 24973259072661432 36028797018963968 133689 1000000000000000 rfl rfl rfl rfl (ep324 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep326 := nat_lit 1756718094215200795442550392487181065538032560736613353302731242151408252952385

noncomputable def ep327 := nat_lit 745474824002098608605791006124688712239478417631537078414766809420940910401

noncomputable def ep328 := nat_lit 4599721382753332018887984509170796151827411836872107722427815059371768662925121

noncomputable def ep329 := BSN.sin_dyadic_bound_f 2285883657 2147483648 3 2 1048576 267640 ep326 ep108 ep327 ep328 ep110 ep327 917001 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2285883657) qz287 0 2 ep326 ep108 ep327 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2285883657) qz288 0 2 ep328 ep110 ep327 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz368 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 157856063) qz20)

noncomputable def ep330 := @Enclosure.Real.IsNear.cos_image qz70 qz368 Bool.false 157856063 524288 201 262144 Bool.false 917001 1048576 1 133689 (@Enclosure.Real.IsNear.recentre' qz70 Bool.false 21187082193396963921 70368744177664000 1597750000854406399 2088890625000000000000 157856063 524288 201 262144 (ep325 rfl) rfl) (Enclosure.sfrac_false_div 157856063 524288) (BSN.cos_reduce3 qz368 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 80427381142258288951296) qz21) 226375608064910080 72057594037927936 Bool.false 917001 1048576 47 1000000000000000 267378 133689 (BSN.sin_reduce_arg_pos_rat_q3 157856063 524288 226375608064910080 72057594037927936 47 80427381142258288951296 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 917001 1048576 80427381142258288951296 75557863725914323419136 2285883657 2147483648 267640 267378 (ep329 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep331 := nat_lit 976285818930223596849686125162267120282124524150399212758590586443858336489281

noncomputable def ep332 := nat_lit 2927366507142666593331846793474551983421894615615934564118942225712733127647041

noncomputable def ep333 := BSN.cos_dyadic_bound_f 2285883657 2147483648 3 2 1048576 267640 ep331 ep75 ep327 ep332 ep78 ep327 508546 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2285883657) qz292 0 2 ep331 ep75 ep327 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2285883657) qz293 0 2 ep332 ep78 ep327 rfl rfl rfl rfl) rfl rfl

noncomputable def ep334 := @Enclosure.Real.IsNear.sin_image qz70 qz368 Bool.false 157856063 524288 201 262144 Bool.true 508546 1048576 1 133689 (@Enclosure.Real.IsNear.recentre' qz70 Bool.false 21187082193396963921 70368744177664000 1597750000854406399 2088890625000000000000 157856063 524288 201 262144 (ep325 rfl) rfl) (Enclosure.sfrac_false_div 157856063 524288) (BSN.sin_reduce3 qz368 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 80427381142258288951296) qz21) 226375608064910080 72057594037927936 Bool.false 508546 1048576 47 1000000000000000 267378 133689 (BSN.sin_reduce_arg_pos_rat_q3 157856063 524288 226375608064910080 72057594037927936 47 80427381142258288951296 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 508546 1048576 80427381142258288951296 75557863725914323419136 2285883657 2147483648 267640 267378 (ep333 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz369 := (@Enclosure.Real.IsNear.recentre' qz69 Bool.false 240559 1048576 1 1048576 240559 1048576 1 1048576 (ep323 rfl rfl) rfl)

noncomputable def ep335 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz69 (Real.cos qz70)) (@HMul.hMul Real Real Real qz0 qz69 (@Neg.neg Real Real.instNeg (Real.sin qz70))) Bool.false 220592843559 1099511627776 26231659964609 146992610005745664 Bool.false 61167658607 549755813888 13088527012057 73496305002872832 (@Enclosure.Real.IsNear.mulLit_ff qz69 (Real.cos qz70) 240559 1048576 1 1048576 917001 1048576 27133633 35045769216 220592843559 1099511627776 26231659964609 146992610005745664 qz369 (@Enclosure.Real.IsNear.recentre' (Real.cos qz70) Bool.false 917001 1048576 27133633 35045769216 917001 1048576 27133633 35045769216 (ep330 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz69 (@Neg.neg Real Real.instNeg (Real.sin qz70)) 240559 1048576 1 1048576 254273 524288 27133633 35045769216 61167658607 549755813888 13088527012057 73496305002872832 qz369 (@Enclosure.Real.IsNear.neg (Real.sin qz70) Bool.true 254273 524288 27133633 35045769216 (@Enclosure.Real.IsNear.recentre' (Real.sin qz70) Bool.true 508546 1048576 27133633 35045769216 254273 524288 27133633 35045769216 (ep334 rfl rfl) rfl)) rfl)

noncomputable def ep336 := @ep290 220592843559 1099511627776 26231659964609 146992610005745664 Bool.false 61167658607 549755813888 13088527012057 73496305002872832 Bool.false ep291 18994046547 8589934592 60495995639453 12249384167145472 Bool.true 87734913785591377166336 159588878497 1099511627776 241940807828951 48997536668581888 (ep292 (BSN.head_sum_c_succ qz5 18 19 rfl rfl) (ep321 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep322 ep335) rfl rfl

noncomputable abbrev qz370 := (@Nat.cast Real Real.instNatCast 20)

noncomputable abbrev qz71 := (@Inv.inv Real Real.instInv (Real.sqrt qz370))

noncomputable abbrev qz566 := (Real.log (Enclosure.sfrac Bool.false 20 1))

noncomputable abbrev qz72 := (@HMul.hMul Real Real Real qz268 qz284 qz566)

noncomputable def ep337 := @Enclosure.Complex.IsNear.of_eq qz63 (Complex.mk (@HMul.hMul Real Real Real qz0 qz71 (Real.cos qz72)) (@HMul.hMul Real Real Real qz0 qz71 (@Neg.neg Real Real.instNeg (Real.sin qz72)))) Bool.false 3222776405 549755813888 6355105192205 36748152501436416 Bool.false 245773922835 1099511627776 25556880473345 146992610005745664 (BSN.cpow_neg_s_mk qz13 102256 1000 20 qz14 rfl)

noncomputable abbrev qz371 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 20) qz15)

noncomputable def ep338 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz370) 4689375 1048576 1 1048576 117234 117235 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz370) (Real.sqrt qz371) Bool.false 4689375 1048576 1 1048576 (BSN.sqrt_natCast_div_one 20) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz371) Bool.false 4689375 1048576 1 1048576 4689375 1048576 1 1048576 (BSN.sqrt_enclosure 20 1 2344687 2344688 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep339 := BSN.log_dyadic_bound 4 36 3 2 25194240 524288 133689 104448 768 116991 40 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 4) (BSN.artanhQ 36) 0 2 104448 25194240 768 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep340 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz566 102256 1000 0 1 3372893643545847 1125899906842624 250000000133689 33422250000000000000 21556163275901508177 70368744177664000 1597750000854406399 2088890625000000000000 qz16 (BSN.isNear_log_sfrac 20 1 3372893643545847 1125899906842624 250000000133689 33422250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz371) Bool.false 56587765202795681021952 18889465931478580854784 1000000000534756 133689000000000000000 3372893643545847 1125899906842624 250000000133689 33422250000000000000 (BSN.log_rat_reduce_isNear 20 1 4 40 32 116991 524288 24973259072661432 36028797018963968 133689 1000000000000000 rfl rfl rfl rfl (ep339 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep341 := BSN.sin_dyadic_bound_f 56307328 2147483648 1 0 1048576 267640 0 1 1 0 1 1 27490 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 56307328) qz287 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 56307328) qz288 0 0 rfl) rfl rfl

noncomputable abbrev qz372 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 321211863) qz26)

noncomputable def ep342 := @Enclosure.Real.IsNear.cos_image qz72 qz372 Bool.false 321211863 1048576 803 1048576 Bool.false 27490 1048576 1 133689 (@Enclosure.Real.IsNear.recentre' qz72 Bool.false 21556163275901508177 70368744177664000 1597750000854406399 2088890625000000000000 321211863 1048576 803 1048576 (ep340 rfl) rfl) (Enclosure.sfrac_false_div 321211863 1048576) (BSN.cos_reduce3 qz372 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 3962275998175315623936) qz27) 226375608064910080 72057594037927936 Bool.false 27490 1048576 48 1000000000000000 267378 133689 (BSN.sin_reduce_arg_pos_rat_q3 321211863 1048576 226375608064910080 72057594037927936 48 3962275998175315623936 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 27490 1048576 3962275998175315623936 151115727451828646838272 56307328 2147483648 267640 267378 (ep341 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep343 := BSN.cos_dyadic_bound_f 56307328 2147483648 1 0 1048576 267640 0 1 1 0 1 1 1048215 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 56307328) qz292 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 56307328) qz293 0 0 rfl) rfl rfl

noncomputable def ep344 := @Enclosure.Real.IsNear.sin_image qz72 qz372 Bool.false 321211863 1048576 803 1048576 Bool.true 1048215 1048576 1 133689 (@Enclosure.Real.IsNear.recentre' qz72 Bool.false 21556163275901508177 70368744177664000 1597750000854406399 2088890625000000000000 321211863 1048576 803 1048576 (ep340 rfl) rfl) (Enclosure.sfrac_false_div 321211863 1048576) (BSN.sin_reduce3 qz372 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 3962275998175315623936) qz27) 226375608064910080 72057594037927936 Bool.false 1048215 1048576 48 1000000000000000 267378 133689 (BSN.sin_reduce_arg_pos_rat_q3 321211863 1048576 226375608064910080 72057594037927936 48 3962275998175315623936 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1048215 1048576 3962275998175315623936 151115727451828646838272 56307328 2147483648 267640 267378 (ep343 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz373 := (@Enclosure.Real.IsNear.recentre' qz71 Bool.false 234469 1048576 1 1048576 234469 1048576 1 1048576 (ep338 rfl rfl) rfl)

noncomputable def ep345 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz71 (Real.cos qz72)) (@HMul.hMul Real Real Real qz0 qz71 (@Neg.neg Real Real.instNeg (Real.sin qz72))) Bool.false 3222776405 549755813888 6355105192205 36748152501436416 Bool.false 245773922835 1099511627776 25556880473345 146992610005745664 (@Enclosure.Real.IsNear.mulLit_ff qz71 (Real.cos qz72) 234469 1048576 1 1048576 13745 524288 108400843 140183076864 3222776405 549755813888 6355105192205 36748152501436416 qz373 (@Enclosure.Real.IsNear.recentre' (Real.cos qz72) Bool.false 27490 1048576 108400843 140183076864 13745 524288 108400843 140183076864 (ep342 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz71 (@Neg.neg Real Real.instNeg (Real.sin qz72)) 234469 1048576 1 1048576 1048215 1048576 108400843 140183076864 245773922835 1099511627776 25556880473345 146992610005745664 qz373 (@Enclosure.Real.IsNear.neg (Real.sin qz72) Bool.true 1048215 1048576 108400843 140183076864 (@Enclosure.Real.IsNear.recentre' (Real.sin qz72) Bool.true 1048215 1048576 108400843 140183076864 1048215 1048576 108400843 140183076864 (ep344 rfl rfl) rfl)) rfl)

noncomputable def ep346 := @ep288 3222776405 549755813888 6355105192205 36748152501436416 Bool.false 245773922835 1099511627776 25556880473345 146992610005745664 Bool.false 10469770956996131946496 1218841755413 549755813888 46960773027641 9187038125359104 Bool.false 94761458390021112332288 43092522169 549755813888 375689651980099 73496305002872832 (ep289 (BSN.head_sum_c_succ qz5 19 20 rfl rfl) (ep336 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep337 ep345) rfl rfl

noncomputable abbrev qz374 := (@Nat.cast Real Real.instNatCast 21)

noncomputable abbrev qz73 := (@Inv.inv Real Real.instInv (Real.sqrt qz374))

noncomputable abbrev qz567 := (Real.log (Enclosure.sfrac Bool.false 21 1))

noncomputable abbrev qz74 := (@HMul.hMul Real Real Real qz268 qz284 qz567)

noncomputable def ep347 := @Enclosure.Complex.IsNear.of_eq qz62 (Complex.mk (@HMul.hMul Real Real Real qz0 qz73 (Real.cos qz74)) (@HMul.hMul Real Real Real qz0 qz73 (@Neg.neg Real Real.instNeg (Real.sin qz74)))) Bool.true 14313137945 68719476736 6267970873195 36748152501436416 Bool.false 17892309101 274877906944 1555494428209 9187038125359104 (BSN.cpow_neg_s_mk qz13 102256 1000 21 qz14 rfl)

noncomputable abbrev qz375 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 21) qz15)

noncomputable def ep348 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz374) 4805179 1048576 1 1048576 114408 114410 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz374) (Real.sqrt qz375) Bool.false 4805179 1048576 1 1048576 (BSN.sqrt_natCast_div_one 21) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz375) Bool.false 4805179 1048576 1 1048576 4805179 1048576 1 1048576 (BSN.sqrt_enclosure 21 1 2402589 2402590 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep349 := BSN.log_dyadic_bound 5 37 3 2 28112415 524288 133689 173000 1875 142571 42 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 5) (BSN.artanhQ 37) 0 2 173000 28112415 1875 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep350 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz567 102256 1000 0 1 3427826275261687 1125899906842624 250000000133689 33422250000000000000 21907237725197441617 70368744177664000 1597750000854406399 2088890625000000000000 qz16 (BSN.isNear_log_sfrac 21 1 3427826275261687 1125899906842624 250000000133689 33422250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz375) Bool.false 57509381830540779323392 18889465931478580854784 1000000000534756 133689000000000000000 3427826275261687 1125899906842624 250000000133689 33422250000000000000 (BSN.log_rat_reduce_isNear 21 1 4 42 32 142571 524288 24973259072661432 36028797018963968 133689 1000000000000000 rfl rfl rfl rfl (ep349 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep351 := nat_lit 179024278797382011830297171637438736

noncomputable def ep352 := BSN.cos_dyadic_bound_f 650471066 2147483648 2 1 1048576 267640 ep351 ep62 ep351 ep351 ep63 ep351 1000840 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 650471066) qz292 0 1 ep351 ep62 ep351 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 650471066) qz293 0 1 ep351 ep63 ep351 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz376 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 20402705) (@Nat.cast Real Real.instNatCast 65536))

noncomputable def ep353 := @Enclosure.Real.IsNear.cos_image qz74 qz376 Bool.false 20402705 65536 803 1048576 Bool.true 1000840 1048576 1 133689 (@Enclosure.Real.IsNear.recentre' qz74 Bool.false 21907237725197441617 70368744177664000 1597750000854406399 2088890625000000000000 20402705 65536 803 1048576 (ep350 rfl) rfl) (Enclosure.sfrac_false_div 20402705 65536) (BSN.cos_reduce2 qz376 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 2860802003099472363520) qz291) 226375608064910080 72057594037927936 Bool.false 1000840 1048576 49 1000000000000000 267378 133689 (BSN.sin_reduce_arg_pos_rat_q2 20402705 65536 226375608064910080 72057594037927936 49 2860802003099472363520 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1000840 1048576 2860802003099472363520 9444732965739290427392 650471066 2147483648 267640 267378 (ep352 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep354 := BSN.sin_dyadic_bound_f 650471066 2147483648 2 1 1048576 267640 ep351 ep58 ep351 ep351 ep59 ep351 312778 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 650471066) qz287 0 1 ep351 ep58 ep351 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 650471066) qz288 0 1 ep351 ep59 ep351 rfl rfl rfl rfl) rfl rfl

noncomputable def ep355 := @Enclosure.Real.IsNear.sin_image qz74 qz376 Bool.false 20402705 65536 803 1048576 Bool.true 312778 1048576 1 133689 (@Enclosure.Real.IsNear.recentre' qz74 Bool.false 21907237725197441617 70368744177664000 1597750000854406399 2088890625000000000000 20402705 65536 803 1048576 (ep350 rfl) rfl) (Enclosure.sfrac_false_div 20402705 65536) (BSN.sin_reduce2 qz376 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 2860802003099472363520) qz291) 226375608064910080 72057594037927936 Bool.false 312778 1048576 49 1000000000000000 267378 133689 (BSN.sin_reduce_arg_pos_rat_q2 20402705 65536 226375608064910080 72057594037927936 49 2860802003099472363520 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 312778 1048576 2860802003099472363520 9444732965739290427392 650471066 2147483648 267640 267378 (ep354 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz377 := (@Enclosure.Real.IsNear.recentre' qz73 Bool.false 228818 1048576 2 1048576 114409 524288 1 524288 (ep348 rfl rfl) rfl)

noncomputable def ep356 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz73 (Real.cos qz74)) (@HMul.hMul Real Real Real qz0 qz73 (@Neg.neg Real Real.instNeg (Real.sin qz74))) Bool.true 14313137945 68719476736 6267970873195 36748152501436416 Bool.false 17892309101 274877906944 1555494428209 9187038125359104 (@Enclosure.Real.IsNear.mulLit_ft qz73 (Real.cos qz74) 114409 524288 1 524288 125105 131072 108400843 140183076864 14313137945 68719476736 6267970873195 36748152501436416 qz377 (@Enclosure.Real.IsNear.recentre' (Real.cos qz74) Bool.true 1000840 1048576 108400843 140183076864 125105 131072 108400843 140183076864 (ep353 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz73 (@Neg.neg Real Real.instNeg (Real.sin qz74)) 114409 524288 1 524288 156389 524288 108400843 140183076864 17892309101 274877906944 1555494428209 9187038125359104 qz377 (@Enclosure.Real.IsNear.neg (Real.sin qz74) Bool.true 156389 524288 108400843 140183076864 (@Enclosure.Real.IsNear.recentre' (Real.sin qz74) Bool.true 312778 1048576 108400843 140183076864 156389 524288 108400843 140183076864 (ep355 rfl rfl) rfl)) rfl)

noncomputable def ep357 := @ep286 14313137945 68719476736 6267970873195 36748152501436416 Bool.false 17892309101 274877906944 1555494428209 9187038125359104 Bool.false 75889436855724364791808 1104336651853 549755813888 64703687661253 12249384167145472 Bool.false 21681583250908563636224 78877140371 549755813888 129377869135257 24498768334290944 (ep287 (BSN.head_sum_c_succ qz5 20 21 rfl rfl) (ep346 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep347 ep356) rfl rfl

noncomputable abbrev qz378 := (@Nat.cast Real Real.instNatCast 22)

noncomputable abbrev qz75 := (@Inv.inv Real Real.instInv (Real.sqrt qz378))

noncomputable abbrev qz568 := (Real.log (Enclosure.sfrac Bool.false 22 1))

noncomputable abbrev qz76 := (@HMul.hMul Real Real Real qz268 qz284 qz568)

noncomputable def ep358 := @Enclosure.Complex.IsNear.of_eq qz61 (Complex.mk (@HMul.hMul Real Real Real qz0 qz75 (Real.cos qz76)) (@HMul.hMul Real Real Real qz0 qz75 (@Neg.neg Real Real.instNeg (Real.sin qz76)))) Bool.true 39913196109 549755813888 6070403131345 36748152501436416 Bool.true 220405964085 1099511627776 24365680312939 146992610005745664 (BSN.cpow_neg_s_mk qz13 102256 1000 22 qz14 rfl)

noncomputable abbrev qz379 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 22) qz15)

noncomputable def ep359 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz378) 4918257 1048576 1 1048576 111778 111779 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz378) (Real.sqrt qz379) Bool.false 4918257 1048576 1 1048576 (BSN.sqrt_natCast_div_one 22) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz379) Bool.false 4918257 1048576 1 1048576 4918257 1048576 1 1048576 (BSN.sqrt_enclosure 22 1 2459128 2459129 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep360 := BSN.log_dyadic_bound 6 38 4 3 316148320320 524288 133689 2667271104 699840 166961 44 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 6) (BSN.artanhQ 38) 0 3 2667271104 316148320320 699840 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep361 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz568 102256 1000 0 1 3480203401436407 1125899906842624 250000000133689 33422250000000000000 22241979938580077137 70368744177664000 1597750000854406399 2088890625000000000000 qz16 (BSN.isNear_log_sfrac 22 1 3480203401436407 1125899906842624 250000000133689 33422250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz379) Bool.false 58388124189833310502912 18889465931478580854784 1000000000534756 133689000000000000000 3480203401436407 1125899906842624 250000000133689 33422250000000000000 (BSN.log_rat_reduce_isNear 22 1 4 44 32 166961 524288 24973259072661432 36028797018963968 133689 1000000000000000 rfl rfl rfl rfl (ep360 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep362 := nat_lit 310067402289635705209190619353634961

noncomputable def ep363 := BSN.sin_dyadic_bound_f 746215091 2147483648 2 1 1048576 267640 ep362 ep58 ep362 ep362 ep59 ep362 357074 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 746215091) qz287 0 1 ep362 ep58 ep362 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 746215091) qz288 0 1 ep362 ep59 ep362 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz380 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 10357229) (@Nat.cast Real Real.instNatCast 32768))

noncomputable abbrev qz381 := (@Nat.cast Real Real.instNatCast 4722366482869645213696)

noncomputable def ep364 := @Enclosure.Real.IsNear.cos_image qz76 qz380 Bool.false 10357229 32768 803 1048576 Bool.true 357074 1048576 1 133689 (@Enclosure.Real.IsNear.recentre' qz76 Bool.false 22241979938580077137 70368744177664000 1597750000854406399 2088890625000000000000 10357229 32768 803 1048576 (ep361 rfl) rfl) (Enclosure.sfrac_false_div 10357229 32768) (BSN.cos_reduce1 qz380 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 1640944340442963509248) qz381) 226375608064910080 72057594037927936 Bool.false 357074 1048576 50 1000000000000000 267378 133689 (BSN.sin_reduce_arg_pos_rat_q1 10357229 32768 226375608064910080 72057594037927936 50 1640944340442963509248 4722366482869645213696 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 357074 1048576 1640944340442963509248 4722366482869645213696 746215091 2147483648 267640 267378 (ep363 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep365 := BSN.cos_dyadic_bound_f 746215091 2147483648 2 1 1048576 267640 ep362 ep62 ep362 ep362 ep63 ep362 985905 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 746215091) qz292 0 1 ep362 ep62 ep362 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 746215091) qz293 0 1 ep362 ep63 ep362 rfl rfl rfl rfl) rfl rfl

noncomputable def ep366 := @Enclosure.Real.IsNear.sin_image qz76 qz380 Bool.false 10357229 32768 803 1048576 Bool.false 985905 1048576 1 133689 (@Enclosure.Real.IsNear.recentre' qz76 Bool.false 22241979938580077137 70368744177664000 1597750000854406399 2088890625000000000000 10357229 32768 803 1048576 (ep361 rfl) rfl) (Enclosure.sfrac_false_div 10357229 32768) (BSN.sin_reduce1 qz380 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 1640944340442963509248) qz381) 226375608064910080 72057594037927936 Bool.false 985905 1048576 50 1000000000000000 267378 133689 (BSN.sin_reduce_arg_pos_rat_q1 10357229 32768 226375608064910080 72057594037927936 50 1640944340442963509248 4722366482869645213696 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 985905 1048576 1640944340442963509248 4722366482869645213696 746215091 2147483648 267640 267378 (ep365 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz382 := (@Enclosure.Real.IsNear.recentre' qz75 Bool.false 223557 1048576 1 1048576 223557 1048576 1 1048576 (ep359 rfl rfl) rfl)

noncomputable def ep367 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz75 (Real.cos qz76)) (@HMul.hMul Real Real Real qz0 qz75 (@Neg.neg Real Real.instNeg (Real.sin qz76))) Bool.true 39913196109 549755813888 6070403131345 36748152501436416 Bool.true 220405964085 1099511627776 24365680312939 146992610005745664 (@Enclosure.Real.IsNear.mulLit_ft qz75 (Real.cos qz76) 223557 1048576 1 1048576 178537 524288 108400843 140183076864 39913196109 549755813888 6070403131345 36748152501436416 qz382 (@Enclosure.Real.IsNear.recentre' (Real.cos qz76) Bool.true 357074 1048576 108400843 140183076864 178537 524288 108400843 140183076864 (ep364 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz75 (@Neg.neg Real Real.instNeg (Real.sin qz76)) 223557 1048576 1 1048576 985905 1048576 108400843 140183076864 220405964085 1099511627776 24365680312939 146992610005745664 qz382 (@Enclosure.Real.IsNear.neg (Real.sin qz76) Bool.false 985905 1048576 108400843 140183076864 (@Enclosure.Real.IsNear.recentre' (Real.sin qz76) Bool.false 985905 1048576 108400843 140183076864 985905 1048576 108400843 140183076864 (ep366 rfl rfl) rfl)) rfl)

noncomputable def ep368 := @ep284 39913196109 549755813888 6070403131345 36748152501436416 Bool.true 220405964085 1099511627776 24365680312939 146992610005745664 Bool.false 585172983234020268572672 1039476031 536870912 6255670816097 1148379765669888 Bool.true 34443127167684217667584 62651683343 1099511627776 800632895124481 146992610005745664 (ep285 (BSN.head_sum_c_succ qz5 21 22 rfl rfl) (ep357 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep358 ep367) rfl rfl

noncomputable abbrev qz383 := (@Nat.cast Real Real.instNatCast 23)

noncomputable abbrev qz77 := (@Inv.inv Real Real.instInv (Real.sqrt qz383))

noncomputable abbrev qz569 := (Real.log (Enclosure.sfrac Bool.false 23 1))

noncomputable abbrev qz78 := (@HMul.hMul Real Real Real qz268 qz284 qz569)

noncomputable def ep369 := @Enclosure.Complex.IsNear.of_eq qz60 (Complex.mk (@HMul.hMul Real Real Real qz0 qz77 (Real.cos qz78)) (@HMul.hMul Real Real Real qz0 qz77 (@Neg.neg Real Real.instNeg (Real.sin qz78)))) Bool.false 112770593325 549755813888 11919550402421 73496305002872832 Bool.true 41146644813 1099511627776 23726352983491 146992610005745664 (BSN.cpow_neg_s_mk qz13 102256 1000 23 qz14 rfl)

noncomputable abbrev qz384 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 23) qz15)

noncomputable def ep370 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz383) 5028793 1048576 1 1048576 109321 109322 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz383) (Real.sqrt qz384) Bool.false 5028793 1048576 1 1048576 (BSN.sqrt_natCast_div_one 23) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz384) Bool.false 5028793 1048576 1 1048576 5028793 1048576 1 1048576 (BSN.sqrt_enclosure 23 1 2514396 2514397 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep371 := BSN.log_dyadic_bound 7 39 4 3 369468094905 524288 133689 4046006391 1764735 190266 46 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 7) (BSN.artanhQ 39) 0 3 4046006391 369468094905 1764735 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep372 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz569 102256 1000 0 1 3530250507853047 1125899906842624 250000000133689 33422250000000000000 22561830995688823377 70368744177664000 1597750000854406399 2088890625000000000000 qz16 (BSN.isNear_log_sfrac 23 1 3530250507853047 1125899906842624 250000000133689 33422250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz384) Bool.false 59227775304360265777152 18889465931478580854784 1000000000534756 133689000000000000000 3530250507853047 1125899906842624 250000000133689 33422250000000000000 (BSN.log_rat_reduce_isNear 23 1 4 46 32 190266 524288 24973259072661432 36028797018963968 133689 1000000000000000 rfl rfl rfl rfl (ep371 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep373 := nat_lit 22550648891760591045331383189014161

noncomputable def ep374 := BSN.cos_dyadic_bound_f 387516109 2147483648 2 1 1048576 267640 ep373 ep62 ep373 ep373 ep63 ep373 1031550 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 387516109) qz292 0 1 ep373 ep62 ep373 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 387516109) qz293 0 1 ep373 ep63 ep373 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz385 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 42024685) (@Nat.cast Real Real.instNatCast 131072))

noncomputable def ep375 := @Enclosure.Real.IsNear.cos_image qz78 qz385 Bool.false 42024685 131072 803 1048576 Bool.false 1031550 1048576 1 133689 (@Enclosure.Real.IsNear.recentre' qz78 Bool.false 22561830995688823377 70368744177664000 1597750000854406399 2088890625000000000000 42024685 131072 803 1048576 (ep372 rfl) rfl) (Enclosure.sfrac_false_div 42024685 131072) (BSN.cos_reduce0 qz385 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 3408627745684749025280) qz354) 226375608064910080 72057594037927936 Bool.false 1031550 1048576 51 1000000000000000 267378 133689 (BSN.sin_reduce_arg_pos_rat_q0 42024685 131072 226375608064910080 72057594037927936 51 3408627745684749025280 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1031550 1048576 3408627745684749025280 18889465931478580854784 387516109 2147483648 267640 267378 (ep374 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep376 := BSN.sin_dyadic_bound_f 387516109 2147483648 2 1 1048576 267640 ep373 ep58 ep373 ep373 ep59 ep373 188191 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 387516109) qz287 0 1 ep373 ep58 ep373 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 387516109) qz288 0 1 ep373 ep59 ep373 rfl rfl rfl rfl) rfl rfl

noncomputable def ep377 := @Enclosure.Real.IsNear.sin_image qz78 qz385 Bool.false 42024685 131072 803 1048576 Bool.false 188191 1048576 1 133689 (@Enclosure.Real.IsNear.recentre' qz78 Bool.false 22561830995688823377 70368744177664000 1597750000854406399 2088890625000000000000 42024685 131072 803 1048576 (ep372 rfl) rfl) (Enclosure.sfrac_false_div 42024685 131072) (BSN.sin_reduce0 qz385 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 3408627745684749025280) qz354) 226375608064910080 72057594037927936 Bool.false 188191 1048576 51 1000000000000000 267378 133689 (BSN.sin_reduce_arg_pos_rat_q0 42024685 131072 226375608064910080 72057594037927936 51 3408627745684749025280 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 188191 1048576 3408627745684749025280 18889465931478580854784 387516109 2147483648 267640 267378 (ep376 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz386 := (@Enclosure.Real.IsNear.recentre' qz77 Bool.false 218643 1048576 1 1048576 218643 1048576 1 1048576 (ep370 rfl rfl) rfl)

noncomputable def ep378 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz77 (Real.cos qz78)) (@HMul.hMul Real Real Real qz0 qz77 (@Neg.neg Real Real.instNeg (Real.sin qz78))) Bool.false 112770593325 549755813888 11919550402421 73496305002872832 Bool.true 41146644813 1099511627776 23726352983491 146992610005745664 (@Enclosure.Real.IsNear.mulLit_ff qz77 (Real.cos qz78) 218643 1048576 1 1048576 515775 524288 108400843 140183076864 112770593325 549755813888 11919550402421 73496305002872832 qz386 (@Enclosure.Real.IsNear.recentre' (Real.cos qz78) Bool.false 1031550 1048576 108400843 140183076864 515775 524288 108400843 140183076864 (ep375 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz77 (@Neg.neg Real Real.instNeg (Real.sin qz78)) 218643 1048576 1 1048576 188191 1048576 108400843 140183076864 41146644813 1099511627776 23726352983491 146992610005745664 qz386 (@Enclosure.Real.IsNear.neg (Real.sin qz78) Bool.false 188191 1048576 108400843 140183076864 (@Enclosure.Real.IsNear.recentre' (Real.sin qz78) Bool.false 188191 1048576 108400843 140183076864 188191 1048576 108400843 140183076864 (ep377 rfl rfl) rfl)) rfl)

noncomputable def ep379 := @ep282 112770593325 549755813888 11919550402421 73496305002872832 Bool.true 41146644813 1099511627776 23726352983491 146992610005745664 Bool.false 632001242724646780928 1177194049069 549755813888 412282482632629 73496305002872832 Bool.true 114127468751230972461056 25949582039 274877906944 206089812026993 36748152501436416 (ep283 (BSN.head_sum_c_succ qz5 22 23 rfl rfl) (ep368 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep369 ep378) rfl rfl

noncomputable abbrev qz387 := (@Nat.cast Real Real.instNatCast 24)

noncomputable abbrev qz79 := (@Inv.inv Real Real.instInv (Real.sqrt qz387))

noncomputable abbrev qz570 := (Real.log (Enclosure.sfrac Bool.false 24 1))

noncomputable abbrev qz80 := (@HMul.hMul Real Real Real qz268 qz284 qz570)

noncomputable def ep380 := @Enclosure.Complex.IsNear.of_eq qz59 (Complex.mk (@HMul.hMul Real Real Real qz0 qz79 (Real.cos qz80)) (@HMul.hMul Real Real Real qz0 qz79 (@Neg.neg Real Real.instNeg (Real.sin qz80)))) Bool.true 627348309 17179869184 2903399294137 18374076250718208 Bool.false 55203868685 274877906944 5835009507365 36748152501436416 (BSN.cpow_neg_s_mk qz13 102256 1000 24 qz14 rfl)

noncomputable abbrev qz388 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 24) qz15)

noncomputable def ep381 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz387) 5136953 1048576 1 1048576 107019 107020 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz387) (Real.sqrt qz388) Bool.false 5136953 1048576 1 1048576 (BSN.sqrt_natCast_div_one 24) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz388) Bool.false 5136953 1048576 1 1048576 5136953 1048576 1 1048576 (BSN.sqrt_enclosure 24 1 2568476 2568477 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep382 := BSN.log_dyadic_bound 8 40 4 3 430080000000 524288 133689 5875957760 3932160 212580 48 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 8) (BSN.artanhQ 40) 0 3 5875957760 430080000000 3932160 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep383 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz570 102256 1000 0 1 3578169457974519 1125899906842624 250000000133689 33422250000000000000 22868081005915150929 70368744177664000 1597750000854406399 2088890625000000000000 qz16 (BSN.isNear_log_sfrac 24 1 3578169457974519 1125899906842624 250000000133689 33422250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz388) Bool.false 60031721881041427759104 18889465931478580854784 1000000000534756 133689000000000000000 3578169457974519 1125899906842624 250000000133689 33422250000000000000 (BSN.log_rat_reduce_isNear 24 1 4 48 32 212580 524288 24973259072661432 36028797018963968 133689 1000000000000000 rfl rfl rfl rfl (ep382 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep384 := nat_lit 2850623478789136811738727929063188823868260476270518649722416745677934390690625

noncomputable def ep385 := nat_lit 6337079581618672014835608885309775609632931722430590854470324252344937890625

noncomputable def ep386 := nat_lit 8539196277204173091186512569418946920385515565366694767458309588529113296290625

noncomputable def ep387 := BSN.cos_dyadic_bound_f 2987006345 2147483648 3 2 1048576 267640 ep384 ep75 ep385 ep386 ep78 ep385 187584 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2987006345) qz292 0 2 ep384 ep75 ep385 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2987006345) qz293 0 2 ep386 ep78 ep385 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz389 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 340760961) qz26)

noncomputable def ep388 := @Enclosure.Real.IsNear.cos_image qz80 qz389 Bool.false 340760961 1048576 803 1048576 Bool.true 187584 1048576 1 133689 (@Enclosure.Real.IsNear.recentre' qz80 Bool.false 22868081005915150929 70368744177664000 1597750000854406399 2088890625000000000000 340760961 1048576 803 1048576 (ep383 rfl) rfl) (Enclosure.sfrac_false_div 340760961 1048576) (BSN.cos_reduce2 qz389 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 210191885356530518720512) qz27) 226375608064910080 72057594037927936 Bool.false 187584 1048576 51 1000000000000000 267378 133689 (BSN.sin_reduce_arg_pos_rat_q2 340760961 1048576 226375608064910080 72057594037927936 51 210191885356530518720512 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 187584 1048576 210191885356530518720512 151115727451828646838272 2987006345 2147483648 267640 267378 (ep387 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep389 := nat_lit 5126052598155151323517841785205492062475162511908989096816773882818405952930625

noncomputable def ep390 := nat_lit 13415115818702775616427470832581025288828877070306274296946217739544409501090625

noncomputable def ep391 := BSN.sin_dyadic_bound_f 2987006345 2147483648 3 2 1048576 267640 ep389 ep108 ep385 ep390 ep110 ep385 1031660 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2987006345) qz287 0 2 ep389 ep108 ep385 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2987006345) qz288 0 2 ep390 ep110 ep385 rfl rfl rfl rfl) rfl rfl

noncomputable def ep392 := @Enclosure.Real.IsNear.sin_image qz80 qz389 Bool.false 340760961 1048576 803 1048576 Bool.true 1031660 1048576 1 133689 (@Enclosure.Real.IsNear.recentre' qz80 Bool.false 22868081005915150929 70368744177664000 1597750000854406399 2088890625000000000000 340760961 1048576 803 1048576 (ep383 rfl) rfl) (Enclosure.sfrac_false_div 340760961 1048576) (BSN.sin_reduce2 qz389 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 210191885356530518720512) qz27) 226375608064910080 72057594037927936 Bool.false 1031660 1048576 51 1000000000000000 267378 133689 (BSN.sin_reduce_arg_pos_rat_q2 340760961 1048576 226375608064910080 72057594037927936 51 210191885356530518720512 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1031660 1048576 210191885356530518720512 151115727451828646838272 2987006345 2147483648 267640 267378 (ep391 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz390 := (@Enclosure.Real.IsNear.recentre' qz79 Bool.false 214039 1048576 1 1048576 214039 1048576 1 1048576 (ep381 rfl rfl) rfl)

noncomputable def ep393 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz79 (Real.cos qz80)) (@HMul.hMul Real Real Real qz0 qz79 (@Neg.neg Real Real.instNeg (Real.sin qz80))) Bool.true 627348309 17179869184 2903399294137 18374076250718208 Bool.false 55203868685 274877906944 5835009507365 36748152501436416 (@Enclosure.Real.IsNear.mulLit_ft qz79 (Real.cos qz80) 214039 1048576 1 1048576 2931 16384 108400843 140183076864 627348309 17179869184 2903399294137 18374076250718208 qz390 (@Enclosure.Real.IsNear.recentre' (Real.cos qz80) Bool.true 187584 1048576 108400843 140183076864 2931 16384 108400843 140183076864 (ep388 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz79 (@Neg.neg Real Real.instNeg (Real.sin qz80)) 214039 1048576 1 1048576 257915 262144 108400843 140183076864 55203868685 274877906944 5835009507365 36748152501436416 qz390 (@Enclosure.Real.IsNear.neg (Real.sin qz80) Bool.true 257915 262144 108400843 140183076864 (@Enclosure.Real.IsNear.recentre' (Real.sin qz80) Bool.true 1031660 1048576 108400843 140183076864 257915 262144 108400843 140183076864 (ep392 rfl rfl) rfl)) rfl)

noncomputable def ep394 := @ep280 627348309 17179869184 2903399294137 18374076250718208 Bool.false 55203868685 274877906944 5835009507365 36748152501436416 Bool.false 19879151386983141474304 1157118903181 549755813888 423896079809177 73496305002872832 Bool.false 8041357082392289869824 14627143323 137438953472 105962410767179 18374076250718208 (ep281 (BSN.head_sum_c_succ qz5 23 24 rfl rfl) (ep379 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep380 ep393) rfl rfl

theorem EMRow31.d8 : Enclosure.Complex.IsNear qz58 Bool.false 1157118903181 549755813888 423896079809177 73496305002872832 Bool.false 14627143323 137438953472 105962410767179 18374076250718208 := ep279 (BSN.head_sum_c_succ qz5 24 25 rfl rfl) (ep394 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

theorem EMRow31.d9 : @Eq Nat (BSN.factNat (Nat.mul 2 1)) 2 := @Eq.refl Nat 2

theorem EMRow31.d10 : @Eq Nat (Nat.pow 26 1) 26 := @Eq.refl Nat 26

noncomputable def ep395 := nat_lit 40225743686296525370270306221623

noncomputable def ep396 := nat_lit 19590300104092415003874820096000

noncomputable def ep397 := nat_lit 2333563644872687008336278144975210283013

noncomputable def ep398 := nat_lit 350132511129423877126304900914889097216000

noncomputable abbrev qz605 := (@instHMul Complex Complex.instMul)

noncomputable abbrev qz571 := qz605

noncomputable abbrev qz391 := qz571

noncomputable abbrev qz81 := qz391

noncomputable abbrev qz572 := (@instHSub Complex Complex.instSub)

noncomputable abbrev qz392 := qz572

noncomputable abbrev qz82 := qz392

noncomputable abbrev qz606 := (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (4 : Complex))

noncomputable abbrev qz607 := (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid))

noncomputable abbrev qz573 := (@HAdd.hAdd Complex Complex Complex qz603 (@HAdd.hAdd Complex Complex Complex qz603 qz606 (@HMul.hMul Complex Complex Complex qz605 Complex.I (@HDiv.hDiv Complex Complex Complex qz607 (↑qz604) (2 : Complex)))) (@Nat.cast Complex Complex.instNatCast 2))

noncomputable abbrev qz393 := qz573

noncomputable abbrev qz83 := (Complex.Stirling.logGammaStirling 1 qz393)

noncomputable abbrev qz574 := (@HAdd.hAdd Complex Complex Complex qz603 qz606 (@HMul.hMul Complex Complex Complex qz605 Complex.I (@HDiv.hDiv Complex Complex Complex qz607 (↑qz604) (2 : Complex))))

noncomputable abbrev qz394 := qz574

noncomputable abbrev qz84 := qz394

noncomputable abbrev qz85 := (@HMul.hMul Real Real Real qz268 (@HDiv.hDiv Real Real Real qz271 qz284 (2 : Real)) (Real.log Real.pi))

noncomputable abbrev qz395 := (@instHSub Real Real.instSub)

noncomputable def ep399 := Complex.re (@HMul.hMul Complex Complex Complex qz81 (Complex.exp (@HMul.hMul Complex Complex Complex qz81 Complex.I ↑(@HSub.hSub Real Real Real qz395 (Complex.im (@HSub.hSub Complex Complex Complex qz82 qz83 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz84 (@Nat.cast Complex Complex.instNatCast j))))) qz85))) (zetaApproximant qz5 1 26))

noncomputable def ep400 := @Enclosure.Real.IsNear.of_eq ep399 (@HSub.hSub Real Real Real qz395 (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz395 (Complex.im (@HSub.hSub Complex Complex Complex qz82 qz83 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz84 (@Nat.cast Complex Complex.instNatCast j))))) qz85)) (Complex.re (zetaApproximant qz5 1 26))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz395 (Complex.im (@HSub.hSub Complex Complex Complex qz82 qz83 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz84 (@Nat.cast Complex Complex.instNatCast j))))) qz85)) (Complex.im (zetaApproximant qz5 1 26))))

noncomputable def ep401 := nat_lit 1609027848868266365792319303171

noncomputable def ep402 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz395 (Complex.im (@HSub.hSub Complex Complex Complex qz82 qz83 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz84 (@Nat.cast Complex Complex.instNatCast j))))) qz85)) (Complex.re (zetaApproximant qz5 1 26))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz395 (Complex.im (@HSub.hSub Complex Complex Complex qz82 qz83 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz84 (@Nat.cast Complex Complex.instNatCast j))))) qz85)) (Complex.im (zetaApproximant qz5 1 26))) ep401

noncomputable def ep403 := nat_lit 783612004163696600154992803840

noncomputable def ep404 := nat_lit 465979574479964376129459394406226622081

noncomputable def ep405 := nat_lit 70026502225884775425260980182977819443200

noncomputable def ep406 := nat_lit 11866147466556365580910587

noncomputable def ep407 := nat_lit 4897575026023103750968705024000

noncomputable def ep408 := nat_lit 9546282481419603356721804541867637

noncomputable def ep409 := nat_lit 911803414399541346683085679465857024000

noncomputable def ep410 := nat_lit 7880343907248496265946816318858733306179605130446186301358080

noncomputable def ep411 := @Enclosure.Real.IsNear.mulLit_tf (Real.cos (@HSub.hSub Real Real Real qz395 (Complex.im (@HSub.hSub Complex Complex Complex qz82 qz83 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz84 (@Nat.cast Complex Complex.instNatCast j))))) qz85)) (Complex.re (zetaApproximant qz5 1 26)) 1048575 1048576 684829

noncomputable def ep412 := nat_lit 38362249931294050635202997

noncomputable def ep413 := nat_lit 18682766059963622096896000

noncomputable def ep414 := nat_lit 15012223896982052769412587347

noncomputable def ep415 := nat_lit 2497680311790476674511929344000

noncomputable def ep416 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HSub.hSub Real Real Real qz395 (Complex.im (@HSub.hSub Complex Complex Complex qz82 qz83 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz84 (@Nat.cast Complex Complex.instNatCast j))))) qz85)) Bool.true 1048575 1048576 684829

noncomputable abbrev qz396 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 95531861) qz26)

noncomputable def ep417 := @Enclosure.Real.IsNear.cos_image (@HSub.hSub Real Real Real qz395 (Complex.im (@HSub.hSub Complex Complex Complex qz82 qz83 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz84 (@Nat.cast Complex Complex.instNatCast j))))) qz85) qz396 Bool.false 95531861 1048576 5

noncomputable def ep418 := nat_lit 1460240384000000000000000000

noncomputable def ep419 := @Enclosure.Real.IsNear.recentre' (@HSub.hSub Real Real Real qz395 (Complex.im (@HSub.hSub Complex Complex Complex qz82 qz83 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz84 (@Nat.cast Complex Complex.instNatCast j))))) qz85) Bool.false 102576555233722638111 1125899906842624000 444898555903811385709211 ep418

noncomputable def ep420 := @Enclosure.Real.IsNear.subLit_ff_p (Complex.im (@HSub.hSub Complex Complex Complex qz82 qz83 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz84 (@Nat.cast Complex Complex.instNatCast j))))) qz85 168472927426073468703 1125899906842624000 160096422903811385709211 ep418 479459211 8192000

noncomputable def ep421 := nat_lit 840307140474655851405312000

noncomputable def ep422 := nat_lit 3523739513758552749580787

noncomputable def ep423 := nat_lit 17522884608000000000000000000

noncomputable def ep424 := @Enclosure.Complex.IsNear.im_isNear (@HSub.hSub Complex Complex Complex qz82 qz83 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz84 (@Nat.cast Complex Complex.instNatCast j)))) Bool.true 14479311305877814353 180143985094819840 ep422 ep423 Bool.false 168472927426073468703 1125899906842624000

noncomputable def ep425 := nat_lit 3458203513565801018892787

noncomputable def ep426 := @Enclosure.Complex.IsNear.subLitP qz83 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz84 (@Nat.cast Complex Complex.instNatCast j))) Bool.true 13061762851165385673 180143985094819840 ep425 ep423 Bool.false 171977021224806920703 1125899906842624000 447521268707053435975633

noncomputable def ep427 := nat_lit 4380721152000000000000000000

noncomputable def ep428 := nat_lit 65209021001732734549328553037529088

noncomputable def ep429 := nat_lit 47420913323630068090317343102599168

noncomputable abbrev qz608 := (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (2 : Complex))

noncomputable abbrev qz575 := qz608

noncomputable abbrev qz397 := (@HSub.hSub Complex Complex Complex qz572 qz573 qz575)

noncomputable abbrev qz398 := (Complex.log qz573)

noncomputable abbrev qz86 := (@HSub.hSub Complex Complex Complex qz392 (@HMul.hMul Complex Complex Complex qz391 qz397 qz398) qz393)

noncomputable abbrev qz399 := qz575

noncomputable abbrev qz87 := (@HMul.hMul Complex Complex Complex qz391 qz399 ↑(Real.log (@HMul.hMul Real Real Real qz268 (2 : Real) Real.pi)))

noncomputable abbrev qz576 := qz607

noncomputable abbrev qz400 := qz576

noncomputable abbrev qz88 := qz400

noncomputable abbrev qz89 := (@instHMul Nat instMulNat)

noncomputable abbrev qz577 := (@instHPow Complex Int (@ZPow.toPow Complex (@DivInvMonoid.toZPow Complex Complex.instDivInvMonoid)))

noncomputable abbrev qz401 := qz577

noncomputable abbrev qz90 := qz401

noncomputable abbrev qz91 := qz393

noncomputable abbrev qz402 := (@OfNat.ofNat Int 1 (@instOfNat 1))

noncomputable abbrev qz92 := qz402

noncomputable abbrev qz403 := (@OfNat.ofNat Int 2 (@instOfNat 2))

noncomputable abbrev qz93 := qz403

noncomputable abbrev qz404 := (@instHSub Int Int.instSub)

noncomputable abbrev qz405 := (@instHMul Int Int.instMul)

noncomputable def ep430 := @Enclosure.Complex.IsNear.of_eq qz83 (@HAdd.hAdd Complex Complex Complex qz4 (@HAdd.hAdd Complex Complex Complex qz4 qz86 qz87) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz89 2 k))) (@HMul.hMul Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz81 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz82 (@HMul.hMul Complex Complex Complex qz81 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz90 qz91 (@HSub.hSub Int Int Int qz404 qz92 (@HMul.hMul Int Int Int qz405 qz93 (@Nat.cast Int instNatCastInt k)))))) Bool.true 13061762851165385673

noncomputable def ep431 := @Enclosure.Complex.IsNear.addLitP (@HAdd.hAdd Complex Complex Complex qz4 qz86 qz87) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz89 2 k))) (@HMul.hMul Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz81 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz82 (@HMul.hMul Complex Complex Complex qz81 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz90 qz91 (@HSub.hSub Int Int Int qz404 qz92 (@HMul.hMul Int Int Int qz405 qz93 (@Nat.cast Int instNatCastInt k))))) Bool.true 13061775747407623113 180143985094819840

noncomputable def ep432 := nat_lit 448798754190904375622095601664

noncomputable def ep433 := nat_lit 36931784091202179416692516454400

noncomputable def ep434 := @ep431 105535949207049950759 534756000000000000000000 Bool.false 34395770555557559603 225179981368524800 13657000037710859431 133689000000000000000000 Bool.false 2459763 34359738368 3 34359738368 Bool.true 1746705037 1073741824000 6391 3221225472000 Bool.true ep432 13061762851165385673 180143985094819840 ep425 ep423 Bool.false ep433

noncomputable def ep435 := @Enclosure.Complex.IsNear.addLitP qz86 qz87 Bool.true 13227316843696042953 180143985094819840 26001500004704382221 133689000000000000000000

noncomputable def ep436 := nat_lit 1712033070764211976667136

noncomputable def ep437 := @ep435 Bool.false 34395770555557559603 225179981368524800 13657000037710859431 133689000000000000000000 Bool.false 120447 131072 3 1048576 Bool.false 0 1 0 1 Bool.true ep436 13061775747407623113 180143985094819840 105535949207049950759 534756000000000000000000 Bool.false 34395770555557559603 34395770555557559603 225179981368524800

noncomputable abbrev qz94 := (@HMul.hMul Complex Complex Complex qz391 qz397 qz398)

noncomputable def ep438 := @Enclosure.Complex.IsNear.subLitP qz94 qz91 Bool.true 12821992877232698313 180143985094819840 26001500004704382221 133689000000000000000000 Bool.false 229543863214837477887

noncomputable def ep439 := @ep438 1125899906842624000 13657000037710859431 133689000000000000000000 Bool.false 9000 4000 0 1 Bool.false 204512 4000 0 1 Bool.true 52909267374784171812000 13227316843696042953 180143985094819840 26001500004704382221 133689000000000000000000 Bool.false 687915411111151192060000 34395770555557559603 225179981368524800 13657000037710859431 133689000000000000000000

noncomputable abbrev qz95 := qz397

noncomputable abbrev qz96 := qz398

noncomputable def ep440 := @Enclosure.Complex.IsNear.mul qz95 qz96 Bool.true 12821992877232698313 180143985094819840 26001500004704382221 133689000000000000000000 Bool.false 229543863214837477887 1125899906842624000 13657000037710859431

noncomputable abbrev qz97 := (Complex.re qz397)

noncomputable abbrev qz98 := (Complex.re qz398)

noncomputable abbrev qz99 := (Complex.im qz397)

noncomputable abbrev qz100 := (Complex.im qz398)

noncomputable def ep441 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 qz97 qz98) (@HMul.hMul Real Real Real qz0 qz99 qz100) 248122164847425099 36028797018963968 3500000010294053 1069512000000000000000 219728182835465997 2814749767106560

noncomputable def ep442 := nat_lit 7218140293006541748459191880646656

noncomputable def ep443 := @Enclosure.Real.IsNear.mulLit_ff qz97 qz98 7000 4000 0 1 35446023549632157 9007199254740992 500000001470579 267378000000000000000

noncomputable def ep444 := @Enclosure.Complex.IsNear.re_isNear qz95 Bool.false 7000 4000 0 1 Bool.false 204512 4000 0 1

noncomputable abbrev qz101 := (Enclosure.sfrac Bool.false 204512 4000)

noncomputable def ep445 := @Enclosure.Complex.IsNear.of_eq qz95 (Complex.mk (Enclosure.sfrac Bool.false 7000 4000) qz101) Bool.false 7000 4000 0 1 Bool.false 204512 4000 0

noncomputable abbrev qz406 := (Enclosure.sfrac Bool.false 9000 4000)

noncomputable abbrev qz102 := qz406

noncomputable abbrev qz407 := (Complex.log (Complex.mk qz102 qz101))

noncomputable def ep446 := @Enclosure.Complex.IsNear.of_eq qz96 qz407 Bool.false 35446023549632157 9007199254740992 500000001470579 267378000000000000000 Bool.false 859521916896675 562949953421312 1000000000133689 267378000000000000000

noncomputable def ep447 := nat_lit 466415097547261849902252562518215121898045440

noncomputable def ep448 := nat_lit 2349161158254954107176092390870600350957568

noncomputable def ep449 := nat_lit 20919723172288010387513987124407291609088

noncomputable def ep450 := BSN.log_dyadic_bound 9138158144 74674158144 3 2 ep447 1048576 267378 ep448 ep449 257928 83812316288 65536000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 9138158144) (BSN.artanhQ 74674158144) 0 2 ep448 ep447 ep449 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz103 := (Enclosure.sfrac Bool.false 1 2)

noncomputable abbrev qz408 := (Enclosure.Real.IsNear.const Bool.false 1 2)

noncomputable abbrev qz409 := (@Nat.cast Real Real.instNatCast 16000000)

noncomputable abbrev qz578 := (Real.log (Enclosure.sfrac Bool.false 41906158144 16000000))

noncomputable def ep451 := @Enclosure.Real.IsNear.mulLit_ff qz103 qz578 1 2 0 1 35446023549632157 4503599627370496 500000001470579 133689000000000000000 35446023549632157 9007199254740992 500000001470579 267378000000000000000 qz408 (BSN.isNear_log_sfrac 41906158144 16000000 35446023549632157 4503599627370496 500000001470579 133689000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 41906158144) qz409)) Bool.false 297342796716632709267456 37778931862957161709568 1000000002941158 267378000000000000000 35446023549632157 4503599627370496 500000001470579 133689000000000000000 (BSN.log_rat_reduce_isNear 41906158144 16000000 11 83812316288 65536000000 257928 1048576 24973259072661432 36028797018963968 267378 1000000000000000 rfl rfl rfl rfl (ep450 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep452 := BSN.arctan_dyadic_bound_f 9000 204512 1 0 1048576 267378 0 1 1 0 1 1 46115 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 9000) (BSN.arctanEvenQ 204512) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 9000) (BSN.arctanOddQ 204512) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz104 := (@HMul.hMul Real Real Real qz268 (Enclosure.sfrac Bool.false 1 2) Real.pi)

noncomputable abbrev qz105 := (@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 2) Real.pi 1 2 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 qz408 BSN.pi_near_15 rfl)

noncomputable abbrev qz410 := (Real.arctan (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 9000) (@Nat.cast Real Real.instNatCast 204512)))

noncomputable def ep453 := @Enclosure.Real.IsNear.subLit_ff_p qz104 qz410 884279719003555 562949953421312 1 2000000000000000 46115 1048576 1 267378 901274053531847884800 859521916896675 562949953421312 1000000000133689 267378000000000000000 qz105 (ep452 rfl) rfl rfl

noncomputable abbrev qz411 := (Real.arctan (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 204512) (@Nat.cast Real Real.instNatCast 9000)))

noncomputable def ep454 := @Enclosure.Complex.IsNear.re_isNear qz96 Bool.false 35446023549632157 9007199254740992 500000001470579 267378000000000000000 Bool.false 859521916896675 562949953421312 1000000000133689 267378000000000000000 (ep446 (@congrArg Complex Complex qz91 (Complex.mk qz102 qz101) Complex.log (BSN.w_shift_mk qz13 Bool.false 102256 1000 2 qz14 rfl)) (@Enclosure.Complex.IsNear.of_parts qz407 Bool.false 35446023549632157 9007199254740992 500000001470579 267378000000000000000 Bool.false 859521916896675 562949953421312 1000000000133689 267378000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz407) (@HMul.hMul Real Real Real qz0 qz103 qz578) Bool.false 35446023549632157 9007199254740992 500000001470579 267378000000000000000 (Enclosure.clog_re_eq 9000 204512 4000 41906158144 16000000 rfl rfl rfl) (ep451 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz407) qz411 Bool.false 859521916896675 562949953421312 1000000000133689 267378000000000000000 (Enclosure.clog_im_eq 9000 204512 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz411 (@HSub.hSub Real Real Real qz395 qz104 qz410) Bool.false 859521916896675 562949953421312 1000000000133689 267378000000000000000 (BSN.arctan_recip 204512 9000 rfl rfl) ep453))))

noncomputable def ep455 := @Enclosure.Real.IsNear.mulLit_ff qz99 qz100 204512 4000 0 1 859521916896675 562949953421312 1000000000133689 267378000000000000000

noncomputable def ep456 := @Enclosure.Complex.IsNear.im_isNear qz95 Bool.false 7000 4000 0 1 Bool.false 204512 4000 0 1

noncomputable def ep457 := @Enclosure.Complex.IsNear.im_isNear qz96 Bool.false 35446023549632157 9007199254740992 500000001470579 267378000000000000000 Bool.false 859521916896675 562949953421312 1000000000133689 267378000000000000000 (ep446 (@congrArg Complex Complex qz91 (Complex.mk qz102 qz101) Complex.log (BSN.w_shift_mk qz13 Bool.false 102256 1000 2 qz14 rfl)) (@Enclosure.Complex.IsNear.of_parts qz407 Bool.false 35446023549632157 9007199254740992 500000001470579 267378000000000000000 Bool.false 859521916896675 562949953421312 1000000000133689 267378000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz407) (@HMul.hMul Real Real Real qz0 qz103 qz578) Bool.false 35446023549632157 9007199254740992 500000001470579 267378000000000000000 (Enclosure.clog_re_eq 9000 204512 4000 41906158144 16000000 rfl rfl rfl) (ep451 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz407) qz411 Bool.false 859521916896675 562949953421312 1000000000133689 267378000000000000000 (Enclosure.clog_im_eq 9000 204512 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz411 (@HSub.hSub Real Real Real qz395 qz104 qz410) Bool.false 859521916896675 562949953421312 1000000000133689 267378000000000000000 (BSN.arctan_recip 204512 9000 rfl rfl) ep453))))

noncomputable abbrev qz106 := (@ep445 1 (BSN.w_sub_half_mk qz284 Bool.false 102256 1000 2 qz286 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7000 4000) (Enclosure.sfrac Bool.false 204512 4000) Bool.false 7000 4000 0 1 Bool.false 204512 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 7000 4000) (Enclosure.Real.IsNear.const Bool.false 204512 4000)))

noncomputable def ep458 := @ep441 6391000000854406399 33422250000000000000000 ep442 12821992877232698313 180143985094819840 26001500004704382221 133689000000000000000000 (@ep443 248122164847425099 36028797018963968 3500000010294053 1069512000000000000000 (ep444 qz106) ep454 rfl) (@ep455 219728182835465997 2814749767106560 6391000000854406399 33422250000000000000000 (ep456 qz106) ep457 rfl) rfl

noncomputable def ep459 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz97 qz100) (@HMul.hMul Real Real Real qz0 qz99 qz98) 6016653418276725 2251799813685248 7000000000935823 1069512000000000000000 226535536505699115387 1125899906842624000

noncomputable def ep460 := nat_lit 516886828419763084711579187178110976

noncomputable def ep461 := @Enclosure.Real.IsNear.mulLit_ff qz97 qz100 7000 4000 0 1 859521916896675 562949953421312 1000000000133689 267378000000000000000

noncomputable def ep462 := @Enclosure.Real.IsNear.mulLit_ff qz99 qz98 204512 4000 0 1 35446023549632157 9007199254740992 500000001470579 267378000000000000000

noncomputable def ep463 := @ep459 3195500009398470389 33422250000000000000000 ep460 229543863214837477887 1125899906842624000 13657000037710859431 133689000000000000000000 (@ep461 6016653418276725 2251799813685248 7000000000935823 1069512000000000000000 (ep444 qz106) ep457 rfl) (@ep462 226535536505699115387 1125899906842624000 3195500009398470389 33422250000000000000000 (ep456 qz106) ep454 rfl) rfl

noncomputable def ep464 := @Enclosure.Complex.IsNear.of_eq qz91 (Complex.mk qz102 qz101) Bool.false 9000 4000 0 1 Bool.false 204512 4000 0 1 (BSN.w_shift_mk qz13 Bool.false 102256 1000 2 qz14 rfl)

noncomputable abbrev qz412 := (ep464 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 9000 4000) (Enclosure.sfrac Bool.false 204512 4000) Bool.false 9000 4000 0 1 Bool.false 204512 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 9000 4000) (Enclosure.Real.IsNear.const Bool.false 204512 4000)))

noncomputable abbrev qz107 := qz412

noncomputable def ep465 := ep439 (@ep440 133689000000000000000000 (ep458 rfl) (ep463 rfl)) qz107 rfl rfl rfl rfl rfl rfl

noncomputable abbrev qz108 := qz399

noncomputable def ep466 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re qz108) (Complex.re ↑qz2)) (@HMul.hMul Real Real Real qz0 (Complex.im qz108) (Complex.im ↑qz2)) 120447 131072 3 1048576 0 1 0 1 120447 120447

noncomputable def ep467 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re qz108) (Complex.re ↑qz2) 1 2 0 1 120447 65536 3 524288 120447 131072 3 1048576

noncomputable abbrev qz109 := (@Enclosure.Complex.IsNear.of_eq qz399 (Complex.mk (Enclosure.sfrac Bool.false 1 2) qz283) Bool.false 1 2 0 1 Bool.false 0 1 0 1 BSN.half_c_mk (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 2) qz283 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz408 qz295))

noncomputable def ep468 := ep467 (@Enclosure.Complex.IsNear.re_isNear qz108 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz109) (@Enclosure.Real.IsNear.of_eq (Complex.re ↑qz2) qz2 Bool.false 120447 65536 3 524288 (Complex.ofReal_re qz2) EMRow31.d4)

noncomputable def ep469 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz108) (Complex.im ↑qz2) 0 1 0 1 0 1 0 1 0 1 0 1

noncomputable def ep470 := ep469 (@Enclosure.Complex.IsNear.im_isNear qz108 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz109) (@Enclosure.Real.IsNear.of_eq (Complex.im ↑qz2) qz10 Bool.false 0 1 0 1 (@Eq.trans Real (Complex.im ↑qz2) (0 : Real) qz10 (Complex.ofReal_im qz2) Enclosure.sfrac_zero_eq) qz17)

noncomputable def ep471 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re qz108) (Complex.im ↑qz2)) (@HMul.hMul Real Real Real qz0 (Complex.im qz108) (Complex.re ↑qz2)) 0 1 0 1 0 1 0 1 0 0

noncomputable def ep472 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re qz108) (Complex.im ↑qz2) 1 2 0 1 0 1 0 1 0 1 0 1

noncomputable def ep473 := ep472 (@Enclosure.Complex.IsNear.re_isNear qz108 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz109) (@Enclosure.Real.IsNear.of_eq (Complex.im ↑qz2) qz10 Bool.false 0 1 0 1 (@Eq.trans Real (Complex.im ↑qz2) (0 : Real) qz10 (Complex.ofReal_im qz2) Enclosure.sfrac_zero_eq) qz17)

noncomputable def ep474 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz108) (Complex.re ↑qz2) 0 1 0 1 120447 65536 3 524288 0 1 0 1

noncomputable def ep475 := ep474 (@Enclosure.Complex.IsNear.im_isNear qz108 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz109) (@Enclosure.Real.IsNear.of_eq (Complex.re ↑qz2) qz2 Bool.false 120447 65536 3 524288 (Complex.ofReal_re qz2) EMRow31.d4)

noncomputable def ep476 := @ep437 13657000037710859431 133689000000000000000000 (ep465 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@Enclosure.Complex.IsNear.mul qz108 (↑qz2) Bool.false 120447 131072 3 1048576 Bool.false 0 1 0 1 (@ep466 131072 3 1048576 (ep468 rfl) (ep470 rfl) rfl rfl) (@ep471 1 0 1 (ep473 rfl) (ep475 rfl) rfl rfl))

noncomputable abbrev qz110 := (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 1)

noncomputable abbrev qz413 := (@Nat.cast Complex Complex.instNatCast 1)

noncomputable abbrev qz111 := (@HMul.hMul Complex Complex Complex qz391 (@HMul.hMul Complex Complex Complex qz391 (2 : Complex) qz413) (@HSub.hSub Complex Complex Complex qz392 (@HMul.hMul Complex Complex Complex qz391 (2 : Complex) qz413) (1 : Complex)))

noncomputable abbrev qz414 := (@HPow.hPow Complex Int Complex qz577 qz573 (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) (@OfNat.ofNat Int 1 (@instOfNat 1)) (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (@OfNat.ofNat Int 2 (@instOfNat 2)) (@Nat.cast Int instNatCastInt 1))))

noncomputable abbrev qz112 := qz414

noncomputable def ep477 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz89 2 k))) (@HMul.hMul Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz81 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz82 (@HMul.hMul Complex Complex Complex qz81 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz90 qz91 (@HSub.hSub Int Int Int qz404 qz92 (@HMul.hMul Int Int Int qz405 qz93 (@Nat.cast Int instNatCastInt k))))) (@HAdd.hAdd Complex Complex Complex qz4 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz89 2 k))) (@HMul.hMul Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz81 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz82 (@HMul.hMul Complex Complex Complex qz81 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz90 qz91 (@HSub.hSub Int Int Int qz404 qz92 (@HMul.hMul Int Int Int qz405 qz93 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 (@Rat.cast Complex Complex.instRatCast (bernoulli qz110)) qz111) qz112)) Bool.false 2459763 34359738368 3 34359738368

noncomputable def ep478 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz89 2 k))) (@HMul.hMul Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz81 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz82 (@HMul.hMul Complex Complex Complex qz81 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz90 qz91 (@HSub.hSub Int Int Int qz404 qz92 (@HMul.hMul Int Int Int qz405 qz93 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 (@Rat.cast Complex Complex.instRatCast (bernoulli qz110)) qz111) qz112) Bool.false 0 1 0 1 Bool.false

noncomputable def ep479 := @ep478 0 1 0 1 Bool.false 2459763 34359738368 3 34359738368 Bool.true 1746705037 1073741824000 6391 3221225472000 Bool.false 2459763 2459763 34359738368 3 34359738368 Bool.true 1746705037 1746705037 1073741824000 6391

noncomputable def ep480 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz89 2 k))) (@HMul.hMul Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz81 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz82 (@HMul.hMul Complex Complex Complex qz81 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz90 qz91 (@HSub.hSub Int Int Int qz404 qz92 (@HMul.hMul Int Int Int qz405 qz93 (@Nat.cast Int instNatCastInt k))))) (Complex.mk qz10 qz10) Bool.false 0 1 0 1 Bool.false

noncomputable def ep481 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz88 (@Rat.cast Complex Complex.instRatCast (bernoulli qz110)) qz111) qz112 Bool.false 2459763 34359738368 3 34359738368 Bool.true 1746705037 1073741824000 6391 3221225472000

noncomputable abbrev qz113 := (Complex.re qz414)

noncomputable abbrev qz114 := (Complex.im qz414)

noncomputable def ep482 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz88 (@Rat.cast Complex Complex.instRatCast (bernoulli qz110)) qz111)) qz113) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz88 (@Rat.cast Complex Complex.instRatCast (bernoulli qz110)) qz111)) qz114) 2459763 34359738368 3 34359738368 0 1 0

noncomputable def ep483 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz88 (@Rat.cast Complex Complex.instRatCast (bernoulli qz110)) qz111)) qz113 1 12 0 1 7379289 8589934592 9 8589934592 2459763

noncomputable def ep484 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz88 (@Rat.cast Complex Complex.instRatCast (bernoulli qz110)) qz111) (Complex.mk (Enclosure.sfrac Bool.false 1 12) qz10) Bool.false 1 12 0 1 Bool.false 0 1 0 1

noncomputable abbrev qz415 := (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 12) qz10 Bool.false 1 12 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 12) qz17)

noncomputable def ep485 := @Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz88 (@Rat.cast Complex Complex.instRatCast (bernoulli qz110)) qz111) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (ep484 (BSN.stirling_coeff_mk 1 1 6 Bool.false BSN.bern_real_1 rfl rfl) qz415)

noncomputable def ep486 := @Enclosure.Complex.IsNear.re_isNear qz112 Bool.false 7379289 8589934592 9 8589934592 Bool.true 5240115111 268435456000 6391 268435456000

noncomputable abbrev qz579 := (@instHPow Complex Nat (@NPow.toPow Complex (@Monoid.toNPow Complex (@Semiring.toMonoid Complex Complex.instSemiring))))

noncomputable abbrev qz416 := (@HPow.hPow Complex Nat Complex qz579 qz573 1)

noncomputable abbrev qz115 := (@Inv.inv Complex Complex.instInv qz416)

noncomputable def ep487 := @Enclosure.Complex.IsNear.of_eq qz112 qz115 Bool.false 7379289 8589934592 9 8589934592 Bool.true 5240115111 268435456000 6391

noncomputable def ep488 := @Enclosure.Complex.IsNear.of_parts qz115 Bool.false 7379289 8589934592 9 8589934592 Bool.true 5240115111 268435456000 6391

noncomputable abbrev qz116 := (Complex.re qz416)

noncomputable abbrev qz117 := (@MonoidWithZeroHom Complex Real (@instMulZeroOneClassOfSemiring Complex Complex.instSemiring) (@instMulZeroOneClassOfSemiring Real Real.semiring))

noncomputable abbrev qz118 := (@MonoidWithZeroHom.funLike Complex Real (@instMulZeroOneClassOfSemiring Complex Complex.instSemiring) (@instMulZeroOneClassOfSemiring Real Real.semiring))

noncomputable abbrev qz119 := qz416

noncomputable def ep489 := @Enclosure.Real.IsNear.mulLit_ff qz116 (@Inv.inv Real Real.instInv (@DFunLike.coe qz117 Complex (fun (x : Complex) => Real) qz118 Complex.normSq qz119)) 9000 4000 0 1 819921 2147483648 1 2147483648

noncomputable def ep490 := @Enclosure.Complex.IsNear.re_isNear qz119 Bool.false 9000 4000 0 1 Bool.false 204512 4000 0 1

noncomputable def ep491 := @Enclosure.Complex.IsNear.of_eq qz119 qz91 Bool.false 9000 4000 0 1 Bool.false 204512 4000 0

noncomputable def ep492 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (@DFunLike.coe qz117 Complex (fun (x : Complex) => Real) qz118 Complex.normSq qz119)) Bool.false 819921 2147483648 1 2147483648 819921 2147483648 1

noncomputable abbrev qz120 := (Complex.im qz416)

noncomputable abbrev qz417 := (@instHAdd Real Real.instAdd)

noncomputable def ep493 := @Enclosure.Real.IsNear.of_eq (@DFunLike.coe qz117 Complex (fun (x : Complex) => Real) qz118 Complex.normSq qz119) (@HAdd.hAdd Real Real Real qz417 (@HMul.hMul Real Real Real qz0 qz116 qz116) (@HMul.hMul Real Real Real qz0 qz120 qz120)) Bool.false 654783721 250000 0 1

noncomputable def ep494 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz116 qz116) (@HMul.hMul Real Real Real qz0 qz120 qz120) 81 16 0 1 40844881 15625

noncomputable def ep495 := @Enclosure.Real.IsNear.mulLit_ff qz116 qz116 9000 4000 0 1 9000 4000 0 1

noncomputable def ep496 := @Enclosure.Real.IsNear.mulLit_ff qz120 qz120 204512 4000 0 1 204512 4000 0 1

noncomputable def ep497 := @Enclosure.Complex.IsNear.im_isNear qz119 Bool.false 9000 4000 0 1 Bool.false 204512 4000 0 1

noncomputable abbrev qz121 := (ep490 (@ep491 1 (BSN.pow_one_c qz393) qz412))

noncomputable abbrev qz122 := (ep497 (@ep491 1 (BSN.pow_one_c qz393) qz412))

noncomputable def ep498 := @ep494 0 1 654783721 654783721 250000 0 1 (@ep495 81 16 0 1 qz121 qz121 rfl) (@ep496 40844881 15625 0 1 qz122 qz122 rfl)

noncomputable def ep499 := @Enclosure.Real.IsNear.inv_image (@DFunLike.coe qz117 Complex (fun (x : Complex) => Real) qz118 Complex.normSq qz119) 654783721 250000 0 1 409960 409961 1073741824 (ep493 (Enclosure.Complex.normSq_eq_mul_add_mul qz119) (ep498 rfl rfl)) rfl

noncomputable def ep500 := @Enclosure.Real.IsNear.of_eq (Complex.re qz115) (@HMul.hMul Real Real Real qz0 qz116 (@Inv.inv Real Real.instInv (@DFunLike.coe qz117 Complex (fun (x : Complex) => Real) qz118 Complex.normSq qz119))) Bool.false 7379289 8589934592 9 8589934592 (Enclosure.Complex.inv_re_eq_mul qz119) (@ep489 7379289 8589934592 9 8589934592 qz121 (@ep492 2147483648 (ep499 rfl rfl rfl rfl rfl) rfl) rfl)

noncomputable def ep501 := @Enclosure.Real.IsNear.of_eq (Complex.im qz115) (@HMul.hMul Real Real Real qz0 (@Neg.neg Real Real.instNeg qz120) (@Inv.inv Real Real.instInv (@DFunLike.coe qz117 Complex (fun (x : Complex) => Real) qz118 Complex.normSq qz119))) Bool.true 5240115111 268435456000 6391 268435456000 (Enclosure.Complex.inv_im_eq_mul qz119)

noncomputable def ep502 := @Enclosure.Real.IsNear.mulLit_tf (@Neg.neg Real Real.instNeg qz120) (@Inv.inv Real Real.instInv (@DFunLike.coe qz117 Complex (fun (x : Complex) => Real) qz118 Complex.normSq qz119)) 204512 4000 0 1 819921 2147483648 1

noncomputable def ep503 := @ep502 2147483648 5240115111 268435456000 6391 268435456000 (@Enclosure.Real.IsNear.neg qz120 Bool.false 204512 4000 0 1 qz122) (@ep492 2147483648 (ep499 rfl rfl rfl rfl rfl) rfl) rfl

noncomputable def ep504 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz88 (@Rat.cast Complex Complex.instRatCast (bernoulli qz110)) qz111)) qz114 0 1 0 1 5240115111 268435456000 6391 268435456000 0

noncomputable def ep505 := @Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz88 (@Rat.cast Complex Complex.instRatCast (bernoulli qz110)) qz111) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (ep484 (BSN.stirling_coeff_mk 1 1 6 Bool.false BSN.bern_real_1 rfl rfl) qz415)

noncomputable def ep506 := @Enclosure.Complex.IsNear.im_isNear qz112 Bool.false 7379289 8589934592 9 8589934592 Bool.true 5240115111 268435456000 6391 268435456000

noncomputable abbrev qz123 := (@ep487 268435456000 (BSN.zpow_one_sub_two_mul qz393 1 1 rfl rfl) (@ep488 268435456000 ep500 (ep501 ep503)))

noncomputable def ep507 := @ep482 1 2459763 2459763 34359738368 3 34359738368 (@ep483 34359738368 3 34359738368 ep485 (ep486 qz123) rfl) (@ep504 1 0 1 ep505 (ep506 qz123) rfl) rfl

noncomputable def ep508 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz88 (@Rat.cast Complex Complex.instRatCast (bernoulli qz110)) qz111)) qz114) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz88 (@Rat.cast Complex Complex.instRatCast (bernoulli qz110)) qz111)) qz113) 1746705037 1073741824000 6391 3221225472000 0 1 0

noncomputable def ep509 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HDiv.hDiv Complex Complex Complex qz88 (@Rat.cast Complex Complex.instRatCast (bernoulli qz110)) qz111)) qz114 1 12 0 1 5240115111 268435456000 6391 268435456000 1746705037

noncomputable def ep510 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz88 (@Rat.cast Complex Complex.instRatCast (bernoulli qz110)) qz111)) qz113 0 1 0 1 7379289 8589934592 9 8589934592 0

noncomputable def ep511 := @ep508 1 1746705037 1746705037 1073741824000 6391 3221225472000 (@ep509 1073741824000 6391 3221225472000 ep485 (ep506 qz123) rfl) (@ep510 1 0 1 ep505 (ep486 qz123) rfl) rfl

noncomputable abbrev qz124 := (@Enclosure.Complex.IsNear.mk qz283 qz283 Bool.false 0 1 0 1 Bool.false 0 1 0 1 qz295 qz295)

noncomputable def ep512 := @ep479 3221225472000 (@ep480 0 1 0 1 (BSN.stirling_sum_base qz91) qz124) (ep481 (ep507 rfl) (ep511 rfl)) rfl rfl rfl rfl rfl

noncomputable def ep513 := @ep434 171977021224806920703 1125899906842624000 447521268707053435975633 ep427 (ep476 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep477 Bool.true 1746705037 1073741824000 6391 3221225472000 (BSN.stirling_sum_succ qz91 0 1 rfl) (ep512 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl

noncomputable def ep514 := @Enclosure.Complex.IsNear.of_eq (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz84 (@Nat.cast Complex Complex.instNatCast j))) (BSN.logSumC qz13 2) Bool.false 35438711367810717 4503599627370496 500000001470579 133689000000000000000 Bool.false 876023449683363 281474976710656

noncomputable abbrev qz125 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz273 qz394 qz413))

noncomputable def ep515 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz13 2) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.logSumC qz13 1) qz125) Bool.false 35438711367810717 4503599627370496 500000001470579 133689000000000000000 Bool.false 876023449683363 281474976710656 1000000000133689 133689000000000000000

noncomputable def ep516 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz13 1) qz125 Bool.false 35437420730138269 9007199254740992 500000001470579 267378000000000000000 Bool.false 881527181837731 562949953421312 1000000000133689 267378000000000000000 Bool.false

noncomputable def ep517 := nat_lit 638407069242251622778923833622528

noncomputable def ep518 := nat_lit 986314720390452514729872064512

noncomputable abbrev qz126 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz273 qz394 (@Nat.cast Complex Complex.instNatCast 0)))

noncomputable def ep519 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz13 1) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.logSumC qz13 0) qz126) Bool.false 35437420730138269 9007199254740992 500000001470579 267378000000000000000 Bool.false 881527181837731 562949953421312 1000000000133689 267378000000000000000

noncomputable def ep520 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz13 0) qz126 Bool.false 0 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable abbrev qz418 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz101))

noncomputable def ep521 := @Enclosure.Complex.IsNear.of_eq qz126 qz418 Bool.false 35437420730138269 9007199254740992 500000001470579 267378000000000000000 Bool.false 881527181837731 562949953421312 1000000000133689 267378000000000000000

noncomputable def ep522 := nat_lit 464419585851951803838470740989335198698045440

noncomputable def ep523 := nat_lit 2302952418347331775448654301014641310957568

noncomputable def ep524 := nat_lit 20196720218008838626313349828422651609088

noncomputable def ep525 := BSN.log_dyadic_bound 9058158144 74594158144 3 2 ep522 1048576 267378 ep523 ep524 255925 83652316288 65536000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 9058158144) (BSN.artanhQ 74594158144) 0 2 ep523 ep522 ep524 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep526 := @Enclosure.Real.IsNear.mulLit_ff qz103 (Real.log (Enclosure.sfrac Bool.false 41826158144 16000000)) 1 2 0 1 35437420730138269 4503599627370496 500000001470579 133689000000000000000 35437420730138269 9007199254740992 500000001470579 267378000000000000000 qz408 (BSN.isNear_log_sfrac 41826158144 16000000 35437420730138269 4503599627370496 500000001470579 133689000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 41826158144) qz409)) Bool.false 297270631036203724439552 37778931862957161709568 1000000002941158 267378000000000000000 35437420730138269 4503599627370496 500000001470579 133689000000000000000 (BSN.log_rat_reduce_isNear 41826158144 16000000 11 83652316288 65536000000 255925 1048576 24973259072661432 36028797018963968 267378 1000000000000000 rfl rfl rfl rfl (ep525 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep527 := BSN.arctan_dyadic_bound_f 1000 204512 1 0 1048576 267378 0 1 1 0 1 1 5127 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 204512) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 204512) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz419 := (@Nat.cast Real Real.instNatCast 1000)

noncomputable abbrev qz420 := (@Nat.cast Real Real.instNatCast 204512)

noncomputable def ep528 := @Enclosure.Real.IsNear.subLit_ff_p qz104 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz419 qz420)) 884279719003555 562949953421312 1 2000000000000000 5127 1048576 1 267378 924348246222680621056 881527181837731 562949953421312 1000000000133689 267378000000000000000 qz105 (ep527 rfl) rfl rfl

noncomputable abbrev qz127 := (@HAdd.hAdd Complex Complex Complex qz273 qz394 (@Nat.cast Complex Complex.instNatCast 0))

noncomputable abbrev qz421 := (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz101)

noncomputable def ep529 := @ep520 35437420730138269 9007199254740992 500000001470579 267378000000000000000 Bool.false 881527181837731 562949953421312 1000000000133689 267378000000000000000 Bool.false 35437420730138269 35437420730138269 9007199254740992 500000001470579 267378000000000000000 Bool.false 881527181837731 881527181837731 562949953421312 1000000000133689 267378000000000000000 (@Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz13 0) (Complex.mk qz10 qz10) Bool.false 0 1 0 1 Bool.false 0 1 0 1 (BSN.log_sum_c_base qz13) qz124) (ep521 (@congrArg Complex Complex qz127 qz421 Complex.log (BSN.w_shift_mk qz13 Bool.false 102256 1000 0 qz14 rfl)) (@Enclosure.Complex.IsNear.of_parts qz418 Bool.false 35437420730138269 9007199254740992 500000001470579 267378000000000000000 Bool.false 881527181837731 562949953421312 1000000000133689 267378000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz418) (@HMul.hMul Real Real Real qz0 qz103 (Real.log (Enclosure.sfrac Bool.false 41826158144 16000000))) Bool.false 35437420730138269 9007199254740992 500000001470579 267378000000000000000 (Enclosure.clog_re_eq 1000 204512 4000 41826158144 16000000 rfl rfl rfl) (ep526 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz418) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz420 qz419)) Bool.false 881527181837731 562949953421312 1000000000133689 267378000000000000000 (Enclosure.clog_im_eq 1000 204512 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz420 qz419)) (@HSub.hSub Real Real Real qz395 qz104 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz419 qz420))) Bool.false 881527181837731 562949953421312 1000000000133689 267378000000000000000 (BSN.arctan_recip 204512 1000 rfl rfl) ep528)))) rfl rfl

noncomputable abbrev qz422 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz101))

noncomputable def ep530 := @Enclosure.Complex.IsNear.of_eq qz125 qz422 Bool.false 35440002005483165 9007199254740992 500000001470579 267378000000000000000 Bool.false 870519717528995 562949953421312 1000000000133689 267378000000000000000

noncomputable def ep531 := nat_lit 465017565678448693880079415381439175658045440

noncomputable def ep532 := nat_lit 2316756817318720129941289959139429022957568

noncomputable def ep533 := nat_lit 20411620915927523552155127705218043609088

noncomputable def ep534 := BSN.log_dyadic_bound 9082158144 74618158144 3 2 ep531 1048576 267378 ep532 ep533 256526 83700316288 65536000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 9082158144) (BSN.artanhQ 74618158144) 0 2 ep532 ep531 ep533 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep535 := @Enclosure.Real.IsNear.mulLit_ff qz103 (Real.log (Enclosure.sfrac Bool.false 41850158144 16000000)) 1 2 0 1 35440002005483165 4503599627370496 500000001470579 133689000000000000000 35440002005483165 9007199254740992 500000001470579 267378000000000000000 qz408 (BSN.isNear_log_sfrac 41850158144 16000000 35440002005483165 4503599627370496 500000001470579 133689000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 41850158144) qz409)) Bool.false 297292284343212121784320 37778931862957161709568 1000000002941158 267378000000000000000 35440002005483165 4503599627370496 500000001470579 133689000000000000000 (BSN.log_rat_reduce_isNear 41850158144 16000000 11 83700316288 65536000000 256526 1048576 24973259072661432 36028797018963968 267378 1000000000000000 rfl rfl rfl rfl (ep534 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep536 := BSN.arctan_dyadic_bound_f 5000 204512 1 0 1048576 267378 0 1 1 0 1 1 25630 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 5000) (BSN.arctanEvenQ 204512) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 5000) (BSN.arctanOddQ 204512) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz423 := (@Nat.cast Real Real.instNatCast 5000)

noncomputable def ep537 := @Enclosure.Real.IsNear.subLit_ff_p qz104 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz423 qz420)) 884279719003555 562949953421312 1 2000000000000000 25630 1048576 1 267378 912806083327683461120 870519717528995 562949953421312 1000000000133689 267378000000000000000 qz105 (ep536 rfl) rfl rfl

noncomputable abbrev qz128 := (@HAdd.hAdd Complex Complex Complex qz273 qz394 qz413)

noncomputable abbrev qz424 := (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz101)

noncomputable def ep538 := @ep516 35440002005483165 9007199254740992 500000001470579 267378000000000000000 Bool.false 870519717528995 562949953421312 1000000000133689 267378000000000000000 Bool.false ep517 35438711367810717 4503599627370496 500000001470579 133689000000000000000 Bool.false ep518 876023449683363 281474976710656 1000000000133689 133689000000000000000 (ep519 (BSN.log_sum_c_succ qz13 0 1 rfl) (ep529 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep530 (@congrArg Complex Complex qz128 qz424 Complex.log (BSN.w_shift_mk qz13 Bool.false 102256 1000 1 qz14 rfl)) (@Enclosure.Complex.IsNear.of_parts qz422 Bool.false 35440002005483165 9007199254740992 500000001470579 267378000000000000000 Bool.false 870519717528995 562949953421312 1000000000133689 267378000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz422) (@HMul.hMul Real Real Real qz0 qz103 (Real.log (Enclosure.sfrac Bool.false 41850158144 16000000))) Bool.false 35440002005483165 9007199254740992 500000001470579 267378000000000000000 (Enclosure.clog_re_eq 5000 204512 4000 41850158144 16000000 rfl rfl rfl) (ep535 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz422) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz420 qz423)) Bool.false 870519717528995 562949953421312 1000000000133689 267378000000000000000 (Enclosure.clog_im_eq 5000 204512 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz420 qz423)) (@HSub.hSub Real Real Real qz395 qz104 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz423 qz420))) Bool.false 870519717528995 562949953421312 1000000000133689 267378000000000000000 (BSN.arctan_recip 204512 5000 rfl rfl) ep537)))) rfl rfl

noncomputable def ep539 := @ep426 ep427 Bool.false 35438711367810717 4503599627370496 500000001470579 133689000000000000000 Bool.false 876023449683363 281474976710656 1000000000133689 133689000000000000000 Bool.true ep428 14479311305877814353 180143985094819840 ep422 ep423 Bool.false ep429 168472927426073468703 1125899906842624000 160096422903811385709211 ep418 (@ep430 180143985094819840 ep425 ep423 Bool.false 171977021224806920703 1125899906842624000 447521268707053435975633 ep427 (BSN.logGammaStirling_unfold 1 qz91) (ep513 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (@ep514 1000000000133689 133689000000000000000 (BSN.log_sum_c_eq qz13 2) (ep515 (BSN.log_sum_c_succ qz13 1 2 rfl) (ep538 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)))

noncomputable abbrev qz129 := (@HDiv.hDiv Real Real Real qz271 qz284 (2 : Real))

noncomputable def ep540 := @Enclosure.Real.IsNear.mulLit_ff qz129 (Real.log Real.pi) 102256 2000 0 1 75021 65536 1 262144 479459211 8192000 6391 32768000 (@Enclosure.Real.IsNear.of_eq qz129 (Enclosure.sfrac Bool.false 102256 2000) Bool.false 102256 2000 0 1 (BSN.t_half_eq qz13 Bool.false 102256 1000 qz14) (Enclosure.Real.IsNear.const Bool.false 102256 2000)) EMRow31.d5 rfl

noncomputable def ep541 := @ep420 6391 32768000 ep421 102576555233722638111 1125899906842624000 444898555903811385709211 ep418 (@ep424 160096422903811385709211 ep418 (ep539 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) ep540 rfl rfl

noncomputable def ep542 := BSN.cos_dyadic_bound_f 204612 2147483648 1 0 1048576 267640 0 1 1 0 1 1 1048575 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 204612) qz292 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 204612) qz293 0 0 rfl) rfl rfl

noncomputable def ep543 := @ep417 16384 Bool.true 1048575 1048576 1 133689 (@ep419 95531861 1048576 5 16384 ep541 rfl) (Enclosure.sfrac_false_div 95531861 1048576) (BSN.cos_reduce2 qz396 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 14398319793801265152) qz27) 226375608064910080 72057594037927936 Bool.false 1048575 1048576 14 1000000000000000 267378 133689 (BSN.sin_reduce_arg_pos_rat_q2 95531861 1048576 226375608064910080 72057594037927936 14 14398319793801265152 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1048575 1048576 14398319793801265152 151115727451828646838272 204612 2147483648 267640 267378 (ep542 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep544 := nat_lit 14012074544972716572672000

noncomputable def ep545 := nat_lit 23452448026755970094070083

noncomputable def ep546 := nat_lit 3902625487172619803924889600

noncomputable abbrev qz425 := (@HPow.hPow Complex Complex Complex qz535 (@Nat.cast Complex Complex.instNatCast 26) qz536)

noncomputable abbrev qz130 := qz425

noncomputable abbrev qz426 := (@Nat.cast Complex Complex.instNatCast 26)

noncomputable abbrev qz131 := (@HAdd.hAdd Complex Complex Complex qz273 (@HDiv.hDiv Complex Complex Complex qz400 qz426 (@HSub.hSub Complex Complex Complex qz392 qz272 (1 : Complex))) qz399)

noncomputable abbrev qz132 := (@instHSub Nat instSubNat)

noncomputable abbrev qz427 := qz579

noncomputable abbrev qz133 := qz427

noncomputable abbrev qz134 := qz426

noncomputable def ep547 := @Enclosure.Complex.IsNear.of_eq (zetaApproximant qz5 1 26) (@HAdd.hAdd Complex Complex Complex qz4 (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 26, @HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast n) qz7) (@HMul.hMul Complex Complex Complex qz81 qz130 (@HAdd.hAdd Complex Complex Complex qz4 qz131 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz89 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz89 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz132 (@HMul.hMul Nat Nat Nat qz89 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz133 qz134 (@HSub.hSub Nat Nat Nat qz132 (@HMul.hMul Nat Nat Nat qz89 2 k) 1))))))) Bool.false ep412 ep413 ep414

noncomputable def ep548 := @Enclosure.Complex.IsNear.addLitP (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 26, @HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast n) qz7) (@HMul.hMul Complex Complex Complex qz81 qz130 (@HAdd.hAdd Complex Complex Complex qz4 qz131 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz89 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz89 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz132 (@HMul.hMul Nat Nat Nat qz89 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz133 qz134 (@HSub.hSub Nat Nat Nat qz132 (@HMul.hMul Nat Nat Nat qz89 2 k) 1)))))) Bool.false 268579020289 137438953472 217657780250393 36748152501436416

noncomputable def ep549 := nat_lit 1852957056797080238450997

noncomputable def ep550 := nat_lit 72855732563843091055958449

noncomputable def ep551 := nat_lit 832560103930158891503976448000

noncomputable def ep552 := nat_lit 10407001299126986143799705600

noncomputable def ep553 := nat_lit 5272467483388358222002076749957955584

noncomputable def ep554 := nat_lit 395362639890407516397622404384292864

noncomputable def ep555 := @ep548 Bool.true 27660408471 1099511627776 870524906294273 146992610005745664 Bool.false ep549 ep413 ep550 ep551 Bool.true 7078537646849068957639 ep544 907145104368060160538313 ep552 Bool.false ep553 ep412 ep413 ep414 ep415 Bool.true ep554 359580226259283805482139 ep544

noncomputable def ep556 := @Enclosure.Complex.IsNear.of_eq (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 26, @HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast n) qz7) (BSN.headSumC qz5 26) Bool.false 268579020289 137438953472 217657780250393 36748152501436416 Bool.true 27660408471 1099511627776 870524906294273

noncomputable abbrev qz428 := (@Nat.cast Complex Complex.instNatCast 25)

noncomputable def ep557 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 26) (@HAdd.hAdd Complex Complex Complex qz4 qz58 (@HPow.hPow Complex Complex Complex qz6 qz428 qz7)) Bool.false 268579020289 137438953472 217657780250393 36748152501436416 Bool.true 27660408471 1099511627776 870524906294273 146992610005745664

noncomputable def ep558 := @Enclosure.Complex.IsNear.addLitP qz58 (@HPow.hPow Complex Complex Complex qz6 qz428 qz7) Bool.false 1157118903181 549755813888 423896079809177 73496305002872832 Bool.false 14627143323 137438953472 105962410767179 18374076250718208 Bool.true

noncomputable abbrev qz429 := (@Nat.cast Real Real.instNatCast 25)

noncomputable abbrev qz135 := (@Inv.inv Real Real.instInv (Real.sqrt qz429))

noncomputable abbrev qz580 := (Real.log (Enclosure.sfrac Bool.false 25 1))

noncomputable abbrev qz136 := (@HMul.hMul Real Real Real qz268 qz284 qz580)

noncomputable def ep559 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz428 qz7) (Complex.mk (@HMul.hMul Real Real Real qz0 qz135 (Real.cos qz136)) (@HMul.hMul Real Real Real qz0 qz135 (@Neg.neg Real Real.instNeg (Real.sin qz136)))) Bool.true 82802822025 549755813888 11419480691609 73496305002872832 Bool.true 144677555055 1099511627776 22825620156841 146992610005745664 (BSN.cpow_neg_s_mk qz13 102256 1000 25 qz14 rfl)

noncomputable abbrev qz430 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 25) qz15)

noncomputable def ep560 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz429) 5242881 1048576 1 1048576 104857 104858 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz429) (Real.sqrt qz430) Bool.false 5242881 1048576 1 1048576 (BSN.sqrt_natCast_div_one 25) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz430) Bool.false 5242881 1048576 1 1048576 5242881 1048576 1 1048576 (BSN.sqrt_enclosure 25 1 2621440 2621441 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep561 := BSN.log_dyadic_bound 9 41 5 4 7545754341519345 524288 133689 124828057765224 4519905705 233982 50 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 9) (BSN.artanhQ 41) 0 4 124828057765224 7545754341519345 4519905705 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep562 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz580 102256 1000 0 1 3624129903009015 1125899906842624 250000000133689 33422250000000000000 4632362842026122973 14073748835532800 1597750000854406399 2088890625000000000000 qz16 (BSN.isNear_log_sfrac 25 1 3624129903009015 1125899906842624 250000000133689 33422250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz430) Bool.false 60802810194841294602240 18889465931478580854784 1000000000534756 133689000000000000000 3624129903009015 1125899906842624 250000000133689 33422250000000000000 (BSN.log_rat_reduce_isNear 25 1 4 50 32 233982 524288 24973259072661432 36028797018963968 133689 1000000000000000 rfl rfl rfl rfl (ep561 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep563 := nat_lit 11245913973365347568763509571398046736

noncomputable def ep564 := BSN.sin_dyadic_bound_f 1831254434 2147483648 2 1 1048576 267640 ep563 ep58 ep563 ep563 ep59 ep563 789670 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1831254434) qz287 0 1 ep563 ep58 ep563 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1831254434) qz288 0 1 ep563 ep59 ep563 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz431 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 345137927) qz26)

noncomputable def ep565 := @Enclosure.Real.IsNear.cos_image qz136 qz431 Bool.false 345137927 1048576 803 1048576 Bool.true 789670 1048576 1 133689 (@Enclosure.Real.IsNear.recentre' qz136 Bool.false 4632362842026122973 14073748835532800 1597750000854406399 2088890625000000000000 345137927 1048576 803 1048576 (ep562 rfl) rfl) (Enclosure.sfrac_false_div 345137927 1048576) (BSN.cos_reduce1 qz431 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 128863074841343635226624) qz27) 226375608064910080 72057594037927936 Bool.false 789670 1048576 52 1000000000000000 267378 133689 (BSN.sin_reduce_arg_pos_rat_q1 345137927 1048576 226375608064910080 72057594037927936 52 128863074841343635226624 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 789670 1048576 128863074841343635226624 151115727451828646838272 1831254434 2147483648 267640 267378 (ep564 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep566 := nat_lit 401939024210928033717661294045114280789996500928275541979001416150450994053376

noncomputable def ep567 := nat_lit 126470581096333979386251740089010477221271828591512305122441061716040253696

noncomputable def ep568 := nat_lit 1205564131470591433194211378655164821415546959127643601326759366327920901652736

noncomputable def ep569 := BSN.cos_dyadic_bound_f 1831254434 2147483648 3 2 1048576 267640 ep566 ep75 ep567 ep568 ep78 ep567 689877 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1831254434) qz292 0 2 ep566 ep75 ep567 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1831254434) qz293 0 2 ep568 ep78 ep567 rfl rfl rfl rfl) rfl rfl

noncomputable def ep570 := @Enclosure.Real.IsNear.sin_image qz136 qz431 Bool.false 345137927 1048576 803 1048576 Bool.false 689877 1048576 1 133689 (@Enclosure.Real.IsNear.recentre' qz136 Bool.false 4632362842026122973 14073748835532800 1597750000854406399 2088890625000000000000 345137927 1048576 803 1048576 (ep562 rfl) rfl) (Enclosure.sfrac_false_div 345137927 1048576) (BSN.sin_reduce1 qz431 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 128863074841343635226624) qz27) 226375608064910080 72057594037927936 Bool.false 689877 1048576 52 1000000000000000 267378 133689 (BSN.sin_reduce_arg_pos_rat_q1 345137927 1048576 226375608064910080 72057594037927936 52 128863074841343635226624 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 689877 1048576 128863074841343635226624 151115727451828646838272 1831254434 2147483648 267640 267378 (ep569 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz432 := (@Enclosure.Real.IsNear.recentre' qz135 Bool.false 209715 1048576 1 1048576 209715 1048576 1 1048576 (ep560 rfl rfl) rfl)

noncomputable def ep571 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz135 (Real.cos qz136)) (@HMul.hMul Real Real Real qz0 qz135 (@Neg.neg Real Real.instNeg (Real.sin qz136))) Bool.true 82802822025 549755813888 11419480691609 73496305002872832 Bool.true 144677555055 1099511627776 22825620156841 146992610005745664 (@Enclosure.Real.IsNear.mulLit_ft qz135 (Real.cos qz136) 209715 1048576 1 1048576 394835 524288 108400843 140183076864 82802822025 549755813888 11419480691609 73496305002872832 qz432 (@Enclosure.Real.IsNear.recentre' (Real.cos qz136) Bool.true 789670 1048576 108400843 140183076864 394835 524288 108400843 140183076864 (ep565 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz135 (@Neg.neg Real Real.instNeg (Real.sin qz136)) 209715 1048576 1 1048576 689877 1048576 108400843 140183076864 144677555055 1099511627776 22825620156841 146992610005745664 qz432 (@Enclosure.Real.IsNear.neg (Real.sin qz136) Bool.false 689877 1048576 108400843 140183076864 (@Enclosure.Real.IsNear.recentre' (Real.sin qz136) Bool.false 689877 1048576 108400843 140183076864 689877 1048576 108400843 140183076864 (ep570 rfl rfl) rfl)) rfl)

noncomputable def ep572 := @ep558 82802822025 549755813888 11419480691609 73496305002872832 Bool.true 144677555055 1099511627776 22825620156841 146992610005745664 Bool.false 590611511568883439894528 268579020289 137438953472 217657780250393 36748152501436416 Bool.true 3801617592862283661312 27660408471 1099511627776 870524906294273 146992610005745664 EMRow31.d8 (ep559 ep571) rfl rfl

noncomputable def ep573 := @Enclosure.Complex.IsNear.mul qz130 (@HAdd.hAdd Complex Complex Complex qz4 qz131 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz89 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz89 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz132 (@HMul.hMul Nat Nat Nat qz89 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz133 qz134 (@HSub.hSub Nat Nat Nat qz132 (@HMul.hMul Nat Nat Nat qz89 2 k) 1))))) Bool.false ep549 ep413 ep550 ep551 Bool.true

noncomputable def ep574 := nat_lit 1525645711299712734108415

noncomputable abbrev qz137 := (Complex.re qz425)

noncomputable abbrev qz138 := (Complex.im qz425)

noncomputable def ep575 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 qz137 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz131 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz89 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz89 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz132 (@HMul.hMul Nat Nat Nat qz89 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz133 qz134 (@HSub.hSub Nat Nat Nat qz132 (@HMul.hMul Nat Nat Nat qz89 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz138 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz131 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz89 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz89 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz132 (@HMul.hMul Nat Nat Nat qz89 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz133 qz134 (@HSub.hSub Nat Nat Nat qz132 (@HMul.hMul Nat Nat Nat qz89 2 k) 1))))))) 43499433648779878272523 448386385439126930325504 ep574

noncomputable def ep576 := nat_lit 19981442494323813396095434752

noncomputable def ep577 := nat_lit 1741342736191573837770217

noncomputable def ep578 := nat_lit 156105019486904792156995584000

noncomputable def ep579 := nat_lit 38945658612710898330481076079664503468092030976

noncomputable def ep580 := @Enclosure.Real.IsNear.mulLit_ff qz137 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz131 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz89 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz89 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz132 (@HMul.hMul Nat Nat Nat qz89 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz133 qz134 (@HSub.hSub Nat Nat Nat qz132 (@HMul.hMul Nat Nat Nat qz89 2 k) 1)))))) 213181255451 1099511627776 7476857531855 48997536668581888 204049054673

noncomputable abbrev qz433 := (@Nat.cast Real Real.instNatCast 26)

noncomputable abbrev qz139 := (@Inv.inv Real Real.instInv (Real.sqrt qz433))

noncomputable abbrev qz434 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) qz540 (Real.log (Enclosure.sfrac Bool.false 26 1)))

noncomputable abbrev qz140 := (Real.cos qz434)

noncomputable abbrev qz141 := (Real.sin qz434)

noncomputable abbrev qz581 := (@Neg.neg Real Real.instNeg qz141)

noncomputable def ep581 := @Enclosure.Complex.IsNear.of_eq qz130 (Complex.mk (@HMul.hMul Real Real Real qz0 qz139 qz140) (@HMul.hMul Real Real Real qz0 qz139 qz581)) Bool.false 213181255451 1099511627776 7476857531855 48997536668581888 Bool.true 2026200479 68719476736 1859421563447 12249384167145472 (BSN.cpow_neg_s_mk qz13 102256 1000 26 qz14 rfl)

noncomputable abbrev qz435 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 26) qz15)

noncomputable def ep582 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz433) 5346709 1048576 1 1048576 102821 102822 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz433) (Real.sqrt qz435) Bool.false 5346709 1048576 1 1048576 (BSN.sqrt_natCast_div_one 26) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz435) Bool.false 5346709 1048576 1 1048576 5346709 1048576 1 1048576 (BSN.sqrt_enclosure 26 1 2673354 2673355 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep583 := BSN.log_dyadic_bound 10 42 5 4 9150106136613120 524288 133689 179034245376000 10500000000 254545 52 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 10) (BSN.artanhQ 42) 0 4 179034245376000 9150106136613120 10500000000 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz142 := (Real.log (Enclosure.sfrac Bool.false 26 1))

noncomputable def ep584 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz142 102256 1000 0 1 3668288609262839 1125899906842624 250000000133689 33422250000000000000 23444032501798804049 70368744177664000 1597750000854406399 2088890625000000000000 qz16 (BSN.isNear_log_sfrac 26 1 3668288609262839 1125899906842624 250000000133689 33422250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz435) Bool.false 61543670347942250676224 18889465931478580854784 1000000000534756 133689000000000000000 3668288609262839 1125899906842624 250000000133689 33422250000000000000 (BSN.log_rat_reduce_isNear 26 1 4 52 32 254545 524288 24973259072661432 36028797018963968 133689 1000000000000000 rfl rfl rfl rfl (ep583 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep585 := nat_lit 11032808661074900971439819178393856

noncomputable def ep586 := BSN.cos_dyadic_bound_f 324094396 2147483648 2 1 1048576 267640 ep585 ep62 ep585 ep585 ep63 ep585 1036657 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 324094396) qz292 0 1 ep585 ep62 ep585 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 324094396) qz293 0 1 ep585 ep63 ep585 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz143 := qz434

noncomputable abbrev qz436 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 349343307) qz26)

noncomputable def ep587 := @Enclosure.Real.IsNear.cos_image qz143 qz436 Bool.false 349343307 1048576 803 1048576 Bool.false 1036657 1048576 1 133689 (@Enclosure.Real.IsNear.recentre' qz143 Bool.false 23444032501798804049 70368744177664000 1597750000854406399 2088890625000000000000 349343307 1048576 803 1048576 (ep584 rfl) rfl) (Enclosure.sfrac_false_div 349343307 1048576) (BSN.cos_reduce0 qz436 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 22806115664972946079744) qz27) 226375608064910080 72057594037927936 Bool.false 1036657 1048576 53 1000000000000000 267378 133689 (BSN.sin_reduce_arg_pos_rat_q0 349343307 1048576 226375608064910080 72057594037927936 53 22806115664972946079744 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1036657 1048576 22806115664972946079744 151115727451828646838272 324094396 2147483648 267640 267378 (ep586 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep588 := BSN.sin_dyadic_bound_f 324094396 2147483648 1 0 1048576 267640 0 1 1 0 1 1 157648 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 324094396) qz287 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 324094396) qz288 0 0 rfl) rfl rfl

noncomputable def ep589 := @Enclosure.Real.IsNear.sin_image qz143 qz436 Bool.false 349343307 1048576 803 1048576 Bool.false 157648 1048576 1 133689 (@Enclosure.Real.IsNear.recentre' qz143 Bool.false 23444032501798804049 70368744177664000 1597750000854406399 2088890625000000000000 349343307 1048576 803 1048576 (ep584 rfl) rfl) (Enclosure.sfrac_false_div 349343307 1048576) (BSN.sin_reduce0 qz436 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 22806115664972946079744) qz27) 226375608064910080 72057594037927936 Bool.false 157648 1048576 53 1000000000000000 267378 133689 (BSN.sin_reduce_arg_pos_rat_q0 349343307 1048576 226375608064910080 72057594037927936 53 22806115664972946079744 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 157648 1048576 22806115664972946079744 151115727451828646838272 324094396 2147483648 267640 267378 (ep588 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz437 := (@Enclosure.Real.IsNear.recentre' qz139 Bool.false 205643 1048576 1 1048576 205643 1048576 1 1048576 (ep582 rfl rfl) rfl)

noncomputable def ep590 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz139 qz140) (@HMul.hMul Real Real Real qz0 qz139 qz581) Bool.false 213181255451 1099511627776 7476857531855 48997536668581888 Bool.true 2026200479 68719476736 1859421563447 12249384167145472 (@Enclosure.Real.IsNear.mulLit_ff qz139 qz140 205643 1048576 1 1048576 1036657 1048576 108400843 140183076864 213181255451 1099511627776 7476857531855 48997536668581888 qz437 (@Enclosure.Real.IsNear.recentre' qz140 Bool.false 1036657 1048576 108400843 140183076864 1036657 1048576 108400843 140183076864 (ep587 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz139 qz581 205643 1048576 1 1048576 9853 65536 108400843 140183076864 2026200479 68719476736 1859421563447 12249384167145472 qz437 (@Enclosure.Real.IsNear.neg qz141 Bool.false 9853 65536 108400843 140183076864 (@Enclosure.Real.IsNear.recentre' qz141 Bool.false 157648 1048576 108400843 140183076864 9853 65536 108400843 140183076864 (ep589 rfl rfl) rfl)) rfl)

noncomputable def ep591 := @ep580 407805041904 0 1 43499433648779878272523 448386385439126930325504 ep574 ep576 (@Enclosure.Complex.IsNear.re_isNear qz130 Bool.false 213181255451 1099511627776 7476857531855 48997536668581888 Bool.true 2026200479 68719476736 1859421563447 12249384167145472 (ep581 ep590))

noncomputable def ep592 := @Enclosure.Complex.IsNear.re_isNear (@HAdd.hAdd Complex Complex Complex qz4 qz131 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz89 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz89 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz132 (@HMul.hMul Nat Nat Nat qz89 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz133 qz134 (@HSub.hSub Nat Nat Nat qz132 (@HMul.hMul Nat Nat Nat qz89 2 k) 1))))) Bool.false 204049054673 407805041904 0 1 Bool.false

noncomputable def ep593 := @Enclosure.Complex.IsNear.addLitP qz131 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz89 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz89 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz132 (@HMul.hMul Nat Nat Nat qz89 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz133 qz134 (@HSub.hSub Nat Nat Nat qz132 (@HMul.hMul Nat Nat Nat qz89 2 k) 1)))) Bool.false 651908721 1307067442 0 1 Bool.true 166166000

noncomputable def ep594 := @ep593 653533721 0 1 Bool.false 1 624 0 1 Bool.false 6391 19500 0 1 Bool.false 408098109346 204049054673 407805041904 0 1 Bool.false 936497010911 936497010911 12743907559500 0 1

noncomputable abbrev qz144 := (@HDiv.hDiv Complex Complex Complex qz400 qz426 (@HSub.hSub Complex Complex Complex qz392 qz272 (1 : Complex)))

noncomputable def ep595 := @Enclosure.Complex.IsNear.addLitP qz144 qz108 Bool.true 52000000 41826158144 0 1 Bool.true 10634624000 41826158144 0 1

noncomputable def ep596 := @Enclosure.Complex.IsNear.of_eq qz144 (Complex.mk (Enclosure.sfrac Bool.true 52000000 41826158144) (Enclosure.sfrac Bool.true 10634624000 41826158144)) Bool.true 52000000 41826158144 0 1 Bool.true 10634624000 41826158144 0 1

noncomputable def ep597 := @ep595 Bool.false 1 2 0 1 Bool.false 0 1 0 1 Bool.false 41722158144 651908721 1307067442 0 1 Bool.true 10634624000 166166000 653533721 0 1 (ep596 (BSN.N_div_s_sub_one_mk qz13 102256 1000 26 qz14 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 52000000 41826158144) (Enclosure.sfrac Bool.true 10634624000 41826158144) Bool.true 52000000 41826158144 0 1 Bool.true 10634624000 41826158144 0 1 (Enclosure.Real.IsNear.const Bool.true 52000000 41826158144) (Enclosure.Real.IsNear.const Bool.true 10634624000 41826158144))) qz109 rfl

noncomputable abbrev qz145 := (@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 1)))

noncomputable abbrev qz146 := (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz427 qz426 1))

noncomputable def ep598 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz89 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz89 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz132 (@HMul.hMul Nat Nat Nat qz89 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz133 qz134 (@HSub.hSub Nat Nat Nat qz132 (@HMul.hMul Nat Nat Nat qz89 2 k) 1)))) (@HAdd.hAdd Complex Complex Complex qz4 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz89 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz89 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz132 (@HMul.hMul Nat Nat Nat qz89 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz133 qz134 (@HSub.hSub Nat Nat Nat qz132 (@HMul.hMul Nat Nat Nat qz89 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz110)) ↑qz145) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz146)) Bool.false 1 624 0 1

noncomputable def ep599 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz89 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz89 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz132 (@HMul.hMul Nat Nat Nat qz89 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz133 qz134 (@HSub.hSub Nat Nat Nat qz132 (@HMul.hMul Nat Nat Nat qz89 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz110)) ↑qz145) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz146) Bool.false 0 1 0 1 Bool.false

noncomputable def ep600 := @ep599 0 1 0 1 Bool.false 1 624 0 1 Bool.false 6391 19500 0 1 Bool.false 1 1 624 0 1 Bool.false 6391 6391 19500 0

noncomputable def ep601 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz89 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz89 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz132 (@HMul.hMul Nat Nat Nat qz89 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz133 qz134 (@HSub.hSub Nat Nat Nat qz132 (@HMul.hMul Nat Nat Nat qz89 2 k) 1)))) (Complex.mk qz10 qz10) Bool.false 0 1 0 1 Bool.false

noncomputable def ep602 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz110)) ↑qz145) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz146 Bool.false 1 624 0 1 Bool.false 6391 19500 0 1

noncomputable def ep603 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz110)) ↑qz145) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz146)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz110)) ↑qz145) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz146)) 1 624 0 1 0 1 0

noncomputable def ep604 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz110)) ↑qz145) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz146) 1 24 0 1 1 26 0 1 1

noncomputable def ep605 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz110)) ↑qz145)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz110)) ↑qz145)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) 1 24 0 1 0 1 0 1 1

noncomputable def ep606 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz110)) ↑qz145)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 1 2 0 1 1 24 0

noncomputable def ep607 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz110)) ↑qz145) (Complex.mk (Enclosure.sfrac Bool.false 1 12) qz10) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (BSN.bern_coeff_mk 1 1 6 2 Bool.false BSN.bern_real_1 EMRow31.d9 rfl) qz415

noncomputable def ep608 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) qz5 Bool.false 1 2 0 1 Bool.false 102256 1000 0 1 (BSN.ascPochhammer_one_eval qz5)

noncomputable def ep609 := ep608 (@Enclosure.Complex.IsNear.of_eq qz5 (Complex.mk qz103 qz13) Bool.false 1 2 0 1 Bool.false 102256 1000 0 1 (BSN.s_crit_mk qz13 Bool.false 102256 1000 qz14) (@Enclosure.Complex.IsNear.mk qz103 qz13 Bool.false 1 2 0 1 Bool.false 102256 1000 0 1 qz408 qz16))

noncomputable def ep610 := @ep606 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz110)) ↑qz145) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep607) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 102256 1000 0 1 ep609)

noncomputable def ep611 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz110)) ↑qz145)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 102256 1000 0 1 0 1 0

noncomputable def ep612 := @ep611 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz110)) ↑qz145) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep607) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 102256 1000 0 1 ep609)

noncomputable def ep613 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz110)) ↑qz145)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz110)) ↑qz145)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) 6391 750 0 1 0 1 0 1 6391

noncomputable def ep614 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz110)) ↑qz145)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 102256 1000 0 1 6391 750 0

noncomputable def ep615 := @ep614 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz110)) ↑qz145) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep607) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 102256 1000 0 1 ep609)

noncomputable def ep616 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz110)) ↑qz145)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 1 2 0 1 0 1 0

noncomputable def ep617 := @ep616 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz110)) ↑qz145) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep607) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 102256 1000 0 1 ep609)

noncomputable def ep618 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz110)) ↑qz145) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 24 0 1 Bool.false 6391 750 0 1 (@ep605 1 24 0 1 (ep610 rfl) (ep612 rfl) rfl rfl) (@ep613 6391 750 0 1 (ep615 rfl) (ep617 rfl) rfl rfl)

noncomputable def ep619 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz110)) ↑qz145) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 6391 750 0 1 ep618

noncomputable abbrev qz147 := (@Enclosure.Complex.IsNear.of_eq (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz427 qz426 1)) (Complex.mk (Enclosure.sfrac Bool.false 1 26) qz283) Bool.false 1 26 0 1 Bool.false 0 1 0 1 (BSN.natCast_pow_inv_mk 26 1 26 EMRow31.d10 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 26) qz283 Bool.false 1 26 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 26) qz295))

noncomputable def ep620 := @ep604 624 0 1 ep619 (@Enclosure.Complex.IsNear.re_isNear qz146 Bool.false 1 26 0 1 Bool.false 0 1 0 1 qz147)

noncomputable def ep621 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz110)) ↑qz145) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz146) 6391 750 0 1 0 1 0 1 0

noncomputable def ep622 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz110)) ↑qz145) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 6391 750 0 1 ep618

noncomputable def ep623 := @ep621 1 0 1 ep622 (@Enclosure.Complex.IsNear.im_isNear qz146 Bool.false 1 26 0 1 Bool.false 0 1 0 1 qz147)

noncomputable def ep624 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz110)) ↑qz145) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz146)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz110)) ↑qz145) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz146)) 0 1 0 1 6391 19500 0

noncomputable def ep625 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz110)) ↑qz145) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz146) 1 24 0 1 0 1 0 1 0

noncomputable def ep626 := @ep625 1 0 1 ep619 (@Enclosure.Complex.IsNear.im_isNear qz146 Bool.false 1 26 0 1 Bool.false 0 1 0 1 qz147)

noncomputable def ep627 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz110)) ↑qz145) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz146) 6391 750 0 1 1 26 0 1 6391

noncomputable def ep628 := @ep627 19500 0 1 ep622 (@Enclosure.Complex.IsNear.re_isNear qz146 Bool.false 1 26 0 1 Bool.false 0 1 0 1 qz147)

noncomputable def ep629 := @ep600 1 (@ep601 0 1 0 1 (BSN.bern_sum_base qz5 26) qz124) (ep602 (@ep603 1 1 1 624 0 1 (ep620 rfl) (ep623 rfl) rfl rfl) (@ep624 1 6391 6391 19500 0 1 (ep626 rfl) (ep628 rfl) rfl rfl)) rfl rfl rfl rfl rfl

noncomputable def ep630 := ep594 (ep597 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep598 Bool.false 6391 19500 0 1 (BSN.bern_sum_succ qz5 26 0 1 1 rfl rfl) (ep629 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl rfl

noncomputable def ep631 := @Enclosure.Real.IsNear.mulLit_tf qz138 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz131 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz89 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz89 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz132 (@HMul.hMul Nat Nat Nat qz89 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz133 qz134 (@HSub.hSub Nat Nat Nat qz132 (@HMul.hMul Nat Nat Nat qz89 2 k) 1)))))) 2026200479 68719476736 1859421563447 12249384167145472 936497010911

noncomputable def ep632 := @ep631 12743907559500 0 1 1897530692089936426369 875754659060794785792000 ep577 ep578 (@Enclosure.Complex.IsNear.im_isNear qz130 Bool.false 213181255451 1099511627776 7476857531855 48997536668581888 Bool.true 2026200479 68719476736 1859421563447 12249384167145472 (ep581 ep590))

noncomputable def ep633 := @Enclosure.Complex.IsNear.im_isNear (@HAdd.hAdd Complex Complex Complex qz4 qz131 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz89 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz89 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz132 (@HMul.hMul Nat Nat Nat qz89 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz133 qz134 (@HSub.hSub Nat Nat Nat qz132 (@HMul.hMul Nat Nat Nat qz89 2 k) 1))))) Bool.false 204049054673 407805041904 0 1 Bool.false

noncomputable def ep634 := nat_lit 1400410945917920893013981

noncomputable def ep635 := @Enclosure.Real.IsNear.addLit_ft_n (@HMul.hMul Real Real Real qz0 qz137 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz131 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz89 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz89 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz132 (@HMul.hMul Nat Nat Nat qz89 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz133 qz134 (@HSub.hSub Nat Nat Nat qz132 (@HMul.hMul Nat Nat Nat qz89 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz138 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz131 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz89 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz89 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz132 (@HMul.hMul Nat Nat Nat qz89 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz133 qz134 (@HSub.hSub Nat Nat Nat qz132 (@HMul.hMul Nat Nat Nat qz89 2 k) 1))))))) 199643608512115825225861 ep544 ep634

noncomputable def ep636 := nat_lit 124884015589523833725596467200

noncomputable def ep637 := nat_lit 4995360623580953349023858688

noncomputable def ep638 := nat_lit 198369994354089823661613592996329591266082816

noncomputable def ep639 := @Enclosure.Real.IsNear.mulLit_ff qz137 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz131 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz89 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz89 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz132 (@HMul.hMul Nat Nat Nat qz89 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz133 qz134 (@HSub.hSub Nat Nat Nat qz132 (@HMul.hMul Nat Nat Nat qz89 2 k) 1)))))) 213181255451 1099511627776 7476857531855 48997536668581888 936497010911

noncomputable def ep640 := @ep639 12743907559500 0 1 199643608512115825225861 ep544 ep634 ep636 (@Enclosure.Complex.IsNear.re_isNear qz130 Bool.false 213181255451 1099511627776 7476857531855 48997536668581888 Bool.true 2026200479 68719476736 1859421563447 12249384167145472 (ep581 ep590))

noncomputable def ep641 := @Enclosure.Real.IsNear.mulLit_tf qz138 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz131 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz89 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz89 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz132 (@HMul.hMul Nat Nat Nat qz89 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz133 qz134 (@HSub.hSub Nat Nat Nat qz132 (@HMul.hMul Nat Nat Nat qz89 2 k) 1)))))) 2026200479 68719476736 1859421563447 12249384167145472 204049054673

noncomputable def ep642 := @ep641 407805041904 0 1 413444292317929788367 28024149089945433145344 379413212259952041337831 ep637 (@Enclosure.Complex.IsNear.im_isNear qz130 Bool.false 213181255451 1099511627776 7476857531855 48997536668581888 Bool.true 2026200479 68719476736 1859421563447 12249384167145472 (ep581 ep590))

noncomputable abbrev qz438 := (ep630 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable def ep643 := @ep573 7078537646849068957639 ep544 907145104368060160538313 ep552 (@ep575 ep576 1897530692089936426369 875754659060794785792000 ep577 ep578 ep579 ep549 ep413 ep550 ep551 (ep591 (@ep592 936497010911 12743907559500 0 1 qz438) rfl) (ep632 (@ep633 936497010911 12743907559500 0 1 qz438) rfl) rfl rfl) (@ep635 ep636 413444292317929788367 28024149089945433145344 379413212259952041337831 ep637 ep638 7078537646849068957639 ep544 907145104368060160538313 ep552 (ep640 (@ep633 936497010911 12743907559500 0 1 qz438) rfl) (ep642 (@ep592 936497010911 12743907559500 0 1 qz438) rfl) rfl rfl)

noncomputable def ep644 := @ep555 ep545 ep546 (@ep556 146992610005745664 (BSN.head_sum_c_eq qz5 26) (ep557 (BSN.head_sum_c_succ qz5 25 26 rfl rfl) (ep572 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))) ep643 rfl rfl rfl

noncomputable def ep645 := @Enclosure.Complex.IsNear.re_isNear (zetaApproximant qz5 1 26) Bool.false ep412 ep413 ep414 ep415 Bool.true 359580226259283805482139 ep544 ep545 ep546 (@ep547 ep415 Bool.true 359580226259283805482139 ep544 ep545 ep546 (BSN.zetaApproximant_eq_folded' qz5 1 26 rfl) (ep644 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

noncomputable def ep646 := @Enclosure.Real.IsNear.mulLit_tt (Real.sin (@HSub.hSub Real Real Real qz395 (Complex.im (@HSub.hSub Complex Complex Complex qz82 qz83 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz84 (@Nat.cast Complex Complex.instNatCast j))))) qz85)) (Complex.im (zetaApproximant qz5 1 26)) 99 1048576 684829

noncomputable def ep647 := @Enclosure.Real.IsNear.recentre' (Real.sin (@HSub.hSub Real Real Real qz395 (Complex.im (@HSub.hSub Complex Complex Complex qz82 qz83 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz84 (@Nat.cast Complex Complex.instNatCast j))))) qz85)) Bool.true 99 1048576 684829

noncomputable def ep648 := @Enclosure.Real.IsNear.sin_image (@HSub.hSub Real Real Real qz395 (Complex.im (@HSub.hSub Complex Complex Complex qz82 qz83 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz84 (@Nat.cast Complex Complex.instNatCast j))))) qz85) qz396 Bool.false 95531861 1048576 5

noncomputable def ep649 := BSN.sin_dyadic_bound_f 204612 2147483648 1 0 1048576 267640 0 1 1 0 1 1 99 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 204612) qz287 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 204612) qz288 0 0 rfl) rfl rfl

noncomputable def ep650 := @ep648 16384 Bool.true 99 1048576 1 133689 (@ep419 95531861 1048576 5 16384 ep541 rfl) (Enclosure.sfrac_false_div 95531861 1048576) (BSN.sin_reduce2 qz396 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 14398319793801265152) qz27) 226375608064910080 72057594037927936 Bool.false 99 1048576 14 1000000000000000 267378 133689 (BSN.sin_reduce_arg_pos_rat_q2 95531861 1048576 226375608064910080 72057594037927936 14 14398319793801265152 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 99 1048576 14398319793801265152 151115727451828646838272 204612 2147483648 267640 267378 (ep649 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep651 := @Enclosure.Complex.IsNear.im_isNear (zetaApproximant qz5 1 26) Bool.false ep412 ep413 ep414 ep415 Bool.true 359580226259283805482139 ep544 ep545 ep546 (@ep547 ep415 Bool.true 359580226259283805482139 ep544 ep545 ep546 (BSN.zetaApproximant_eq_folded' qz5 1 26 rfl) (ep644 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

theorem EMRow31.d11 : Enclosure.Real.IsNear (hardyZApproximantEM 1 26 qz13) Bool.true ep395 ep396 ep397 ep398 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantEM 1 26 qz13) ep399 Bool.true ep395 ep396 ep397 ep398 (@Eq.refl Real ep399) (@ep400 Bool.true ep395 ep396 ep397 ep398 (BSN.re_exp_mul (@HSub.hSub Real Real Real qz395 (Complex.im (@HSub.hSub Complex Complex Complex qz82 qz83 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz84 (@Nat.cast Complex Complex.instNatCast j))))) qz85) (zetaApproximant qz5 1 26)) (@ep402 ep403 ep404 ep405 ep406 ep407 ep408 ep409 ep410 ep395 ep396 ep397 ep398 (@ep411 2190360576 ep412 ep413 ep414 ep415 ep401 ep403 ep404 ep405 (@ep416 2190360576 1048575 1048576 684829 2190360576 (ep543 rfl rfl) rfl) ep645 rfl) (@ep646 2190360576 359580226259283805482139 ep544 ep545 ep546 ep406 ep407 ep408 ep409 (@ep647 2190360576 99 1048576 684829 2190360576 (ep650 rfl rfl) rfl) ep651 rfl) rfl rfl))

noncomputable abbrev qz609 := (@HAdd.hAdd Complex Complex Complex (@instHAdd Complex Complex.instAdd) (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (2 : Complex)) (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul) Complex.I ↑(Enclosure.sfrac Bool.false 104500 1000)))

noncomputable abbrev qz582 := qz609

noncomputable abbrev qz439 := qz582

noncomputable abbrev qz148 := (BSN.headSumC qz439 9)

noncomputable abbrev qz149 := qz439

noncomputable abbrev qz583 := (@Neg.neg Complex Complex.instNeg qz609)

noncomputable abbrev qz440 := qz583

noncomputable abbrev qz150 := qz440

noncomputable def ep652 := @Enclosure.Complex.IsNear.of_eq qz148 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz149 8) (@HPow.hPow Complex Complex Complex qz6 qz276 qz150)) Bool.false 348830576303 1099511627776 130583322393685 48997536668581888 Bool.false 58085757325 549755813888 32654308497497 12249384167145472

noncomputable def ep653 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz149 8) (@HPow.hPow Complex Complex Complex qz6 qz276 qz150) Bool.false 683889931633 1099511627776 116849930691795 48997536668581888 Bool.true 632288355 8589934592 58450212535829 24498768334290944 Bool.true

noncomputable def ep654 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz149 8) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz149 7) (@HPow.hPow Complex Complex Complex qz6 qz277 qz150)) Bool.false 683889931633 1099511627776 116849930691795 48997536668581888 Bool.true 632288355 8589934592 58450212535829 24498768334290944

noncomputable def ep655 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz149 7) (@HPow.hPow Complex Complex Complex qz6 qz277 qz150) Bool.false 956260324633 1099511627776 306595107891769 146992610005745664 Bool.false 232943411835 1099511627776 306732590183455 146992610005745664 Bool.true

noncomputable def ep656 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz149 7) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz149 6) (@HPow.hPow Complex Complex Complex qz6 qz278 qz150)) Bool.false 956260324633 1099511627776 306595107891769 146992610005745664 Bool.false 232943411835 1099511627776 306732590183455 146992610005745664

noncomputable def ep657 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz149 6) (@HPow.hPow Complex Complex Complex qz6 qz278 qz150) Bool.false 817617522745 1099511627776 86391557971827 48997536668581888 Bool.true 48495478815 274877906944 43203687603805 24498768334290944 Bool.false

noncomputable def ep658 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz149 6) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz149 5) (@HPow.hPow Complex Complex Complex qz6 qz279 qz150)) Bool.false 817617522745 1099511627776 86391557971827 48997536668581888 Bool.true 48495478815 274877906944 43203687603805 24498768334290944

noncomputable def ep659 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz149 5) (@HPow.hPow Complex Complex Complex qz6 qz279 qz150) Bool.false 190804621515 274877906944 51820751966663 36748152501436416 Bool.true 682679451503 1099511627776 207206645645675 146992610005745664 Bool.false

noncomputable def ep660 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz149 5) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz149 4) (@HPow.hPow Complex Complex Complex qz6 qz280 qz150)) Bool.false 190804621515 274877906944 51820751966663 36748152501436416 Bool.true 682679451503 1099511627776 207206645645675 146992610005745664

noncomputable def ep661 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz149 4) (@HPow.hPow Complex Complex Complex qz6 qz280 qz150) Bool.false 7738386213 34359738368 18644037266825 18374076250718208 Bool.true 491899800795 1099511627776 149158759992415 146992610005745664 Bool.false

noncomputable def ep662 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz149 4) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz149 3) (@HPow.hPow Complex Complex Complex qz6 qz8 qz150)) Bool.false 7738386213 34359738368 18644037266825 18374076250718208 Bool.true 491899800795 1099511627776 149158759992415 146992610005745664

noncomputable def ep663 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz149 3) (@HPow.hPow Complex Complex Complex qz6 qz8 qz150) Bool.false 167100527303 549755813888 13693564715349 24498768334290944 Bool.false 136971206515 1099511627776 27349364917415 48997536668581888 Bool.true

noncomputable def ep664 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz149 3) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz149 2) (@HPow.hPow Complex Complex Complex qz6 qz9 qz150)) Bool.false 167100527303 549755813888 13693564715349 24498768334290944 Bool.false 136971206515 1099511627776 27349364917415 48997536668581888

noncomputable def ep665 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz149 2) (@HPow.hPow Complex Complex Complex qz6 qz9 qz150) Bool.false 1 1 0 1 Bool.false 0 1 0 1 Bool.true

noncomputable def ep666 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz149 2) (Complex.mk (Enclosure.sfrac Bool.false 1 1) qz10) Bool.false 1 1 0 1 Bool.false 0 1 0 1 (BSN.head_sum_c_two qz149)

noncomputable abbrev qz610 := (Enclosure.sfrac Bool.false 104500 1000)

noncomputable abbrev qz584 := qz610

noncomputable abbrev qz441 := qz584

noncomputable abbrev qz151 := (@HMul.hMul Real Real Real qz268 qz441 qz285)

noncomputable abbrev qz152 := qz441

noncomputable abbrev qz442 := (@Eq.refl Real qz584)

noncomputable abbrev qz153 := qz442

noncomputable def ep667 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz9 qz150) (Complex.mk (@HMul.hMul Real Real Real qz0 qz11 (Real.cos qz151)) (@HMul.hMul Real Real Real qz0 qz11 (@Neg.neg Real Real.instNeg (Real.sin qz151)))) Bool.true 382655286585 549755813888 13693564715349 24498768334290944 Bool.false 136971206515 1099511627776 27349364917415 48997536668581888 (BSN.cpow_neg_s_mk qz152 104500 1000 2 qz153 rfl)

noncomputable def ep668 := nat_lit 20921564565936714913839073992585681

noncomputable def ep669 := BSN.cos_dyadic_bound_f 380319453 2147483648 2 1 1048576 267640 ep668 ep62 ep668 ep668 ep63 ep668 1032174 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 380319453) qz292 0 1 ep668 ep62 ep668 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 380319453) qz293 0 1 ep668 ep63 ep668 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz154 := (Enclosure.Real.IsNear.const Bool.false 104500 1000)

noncomputable abbrev qz443 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 4747017) (@Nat.cast Real Real.instNatCast 65536))

noncomputable def ep670 := @Enclosure.Real.IsNear.cos_image qz151 qz443 Bool.false 4747017 65536 209 267378 Bool.true 1032174 1048576 1 133689 (@Enclosure.Real.IsNear.mulLit_ff qz152 qz285 104500 1000 0 1 363408 524288 1 133689 4747017 65536 209 267378 qz154 qz290 rfl) (Enclosure.sfrac_false_div 4747017 65536) (BSN.cos_reduce2 qz443 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 1672662647755551801344) qz291) 226375608064910080 72057594037927936 Bool.false 1032174 1048576 11 1000000000000000 267378 133689 (BSN.sin_reduce_arg_pos_rat_q2 4747017 65536 226375608064910080 72057594037927936 11 1672662647755551801344 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1032174 1048576 1672662647755551801344 9444732965739290427392 380319453 2147483648 267640 267378 (ep669 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep671 := BSN.sin_dyadic_bound_f 380319453 2147483648 2 1 1048576 267640 ep668 ep58 ep668 ep668 ep59 ep668 184733 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 380319453) qz287 0 1 ep668 ep58 ep668 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 380319453) qz288 0 1 ep668 ep59 ep668 rfl rfl rfl rfl) rfl rfl

noncomputable def ep672 := @Enclosure.Real.IsNear.sin_image qz151 qz443 Bool.false 4747017 65536 209 267378 Bool.true 184733 1048576 1 133689 (@Enclosure.Real.IsNear.mulLit_ff qz152 qz285 104500 1000 0 1 363408 524288 1 133689 4747017 65536 209 267378 qz154 qz290 rfl) (Enclosure.sfrac_false_div 4747017 65536) (BSN.sin_reduce2 qz443 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 1672662647755551801344) qz291) 226375608064910080 72057594037927936 Bool.false 184733 1048576 11 1000000000000000 267378 133689 (BSN.sin_reduce_arg_pos_rat_q2 4747017 65536 226375608064910080 72057594037927936 11 1672662647755551801344 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 184733 1048576 1672662647755551801344 9444732965739290427392 380319453 2147483648 267640 267378 (ep671 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep673 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz11 (Real.cos qz151)) (@HMul.hMul Real Real Real qz0 qz11 (@Neg.neg Real Real.instNeg (Real.sin qz151))) Bool.true 382655286585 549755813888 13693564715349 24498768334290944 Bool.false 136971206515 1099511627776 27349364917415 48997536668581888 (@Enclosure.Real.IsNear.mulLit_ft qz11 (Real.cos qz151) 741455 1048576 1 1048576 516087 524288 211 267378 382655286585 549755813888 13693564715349 24498768334290944 qz294 (@Enclosure.Real.IsNear.recentre' (Real.cos qz151) Bool.true 1032174 1048576 28208379 35745497442 516087 524288 211 267378 (ep670 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz11 (@Neg.neg Real Real.instNeg (Real.sin qz151)) 741455 1048576 1 1048576 184733 1048576 211 267378 136971206515 1099511627776 27349364917415 48997536668581888 qz294 (@Enclosure.Real.IsNear.neg (Real.sin qz151) Bool.true 184733 1048576 211 267378 (@Enclosure.Real.IsNear.recentre' (Real.sin qz151) Bool.true 184733 1048576 28208379 35745497442 184733 1048576 211 267378 (ep672 rfl rfl) rfl)) rfl)

noncomputable def ep674 := @ep665 382655286585 549755813888 13693564715349 24498768334290944 Bool.false 136971206515 1099511627776 27349364917415 48997536668581888 Bool.false 167100527303 167100527303 549755813888 13693564715349 24498768334290944 Bool.false 136971206515 136971206515 1099511627776 27349364917415 48997536668581888 (ep666 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 1) qz10 Bool.false 1 1 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 1) qz17)) (ep667 ep673) rfl rfl

noncomputable abbrev qz155 := (@HMul.hMul Real Real Real qz268 qz441 qz297)

noncomputable def ep675 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz8 qz150) (Complex.mk (@HMul.hMul Real Real Real qz0 qz18 (Real.cos qz155)) (@HMul.hMul Real Real Real qz0 qz18 (@Neg.neg Real Real.instNeg (Real.sin qz155)))) Bool.true 43286347895 549755813888 33495454921253 73496305002872832 Bool.true 314435503655 549755813888 33555332620085 73496305002872832 (BSN.cpow_neg_s_mk qz152 104500 1000 3 qz153 rfl)

noncomputable def ep676 := BSN.sin_dyadic_bound_f 293785540 2147483648 1 0 1048576 267640 0 1 1 0 1 1 143002 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 293785540) qz287 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 293785540) qz288 0 0 rfl) rfl rfl

noncomputable abbrev qz444 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 120381701) qz26)

noncomputable def ep677 := @Enclosure.Real.IsNear.cos_image qz155 qz444 Bool.false 120381701 1048576 209 267378 Bool.true 143002 1048576 1 133689 (@Enclosure.Real.IsNear.mulLit_ff qz152 qz297 104500 1000 0 1 575989 524288 1 133689 120381701 1048576 209 267378 qz154 qz299 rfl) (Enclosure.sfrac_false_div 120381701 1048576) (BSN.cos_reduce1 qz444 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 20673319540652802834432) qz27) 226375608064910080 72057594037927936 Bool.false 143002 1048576 18 1000000000000000 267378 133689 (BSN.sin_reduce_arg_pos_rat_q1 120381701 1048576 226375608064910080 72057594037927936 18 20673319540652802834432 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 143002 1048576 20673319540652802834432 151115727451828646838272 293785540 2147483648 267640 267378 (ep676 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep678 := nat_lit 7449406349233062762820589990560000

noncomputable def ep679 := BSN.cos_dyadic_bound_f 293785540 2147483648 2 1 1048576 267640 ep678 ep62 ep678 ep678 ep63 ep678 1038778 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 293785540) qz292 0 1 ep678 ep62 ep678 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 293785540) qz293 0 1 ep678 ep63 ep678 rfl rfl rfl rfl) rfl rfl

noncomputable def ep680 := @Enclosure.Real.IsNear.sin_image qz155 qz444 Bool.false 120381701 1048576 209 267378 Bool.false 1038778 1048576 1 133689 (@Enclosure.Real.IsNear.mulLit_ff qz152 qz297 104500 1000 0 1 575989 524288 1 133689 120381701 1048576 209 267378 qz154 qz299 rfl) (Enclosure.sfrac_false_div 120381701 1048576) (BSN.sin_reduce1 qz444 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 20673319540652802834432) qz27) 226375608064910080 72057594037927936 Bool.false 1038778 1048576 18 1000000000000000 267378 133689 (BSN.sin_reduce_arg_pos_rat_q1 120381701 1048576 226375608064910080 72057594037927936 18 20673319540652802834432 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1038778 1048576 20673319540652802834432 151115727451828646838272 293785540 2147483648 267640 267378 (ep679 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep681 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz18 (Real.cos qz155)) (@HMul.hMul Real Real Real qz0 qz18 (@Neg.neg Real Real.instNeg (Real.sin qz155))) Bool.true 43286347895 549755813888 33495454921253 73496305002872832 Bool.true 314435503655 549755813888 33555332620085 73496305002872832 (@Enclosure.Real.IsNear.mulLit_ft qz18 (Real.cos qz155) 605395 1048576 1 1048576 71501 524288 211 267378 43286347895 549755813888 33495454921253 73496305002872832 qz300 (@Enclosure.Real.IsNear.recentre' (Real.cos qz155) Bool.true 143002 1048576 28208379 35745497442 71501 524288 211 267378 (ep677 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz18 (@Neg.neg Real Real.instNeg (Real.sin qz155)) 605395 1048576 1 1048576 519389 524288 211 267378 314435503655 549755813888 33555332620085 73496305002872832 qz300 (@Enclosure.Real.IsNear.neg (Real.sin qz155) Bool.false 519389 524288 211 267378 (@Enclosure.Real.IsNear.recentre' (Real.sin qz155) Bool.false 1038778 1048576 28208379 35745497442 519389 524288 211 267378 (ep680 rfl rfl) rfl)) rfl)

noncomputable def ep682 := @ep663 43286347895 549755813888 33495454921253 73496305002872832 Bool.true 314435503655 549755813888 33555332620085 73496305002872832 Bool.false 68067564971319890018304 7738386213 34359738368 18644037266825 18374076250718208 Bool.true 270424775337400294440960 491899800795 1099511627776 149158759992415 146992610005745664 (ep664 (BSN.head_sum_c_succ qz149 2 3 rfl rfl) (ep674 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep675 ep681) rfl rfl

noncomputable abbrev qz156 := (@HMul.hMul Real Real Real qz268 qz441 qz301)

noncomputable def ep683 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz280 qz150) (Complex.mk (@HMul.hMul Real Real Real qz0 qz22 (Real.cos qz156)) (@HMul.hMul Real Real Real qz0 qz22 (@Neg.neg Real Real.instNeg (Real.sin qz156)))) Bool.false 128897531811 274877906944 14532677433013 36748152501436416 Bool.true 47694912677 274877906944 14511971413315 36748152501436416 (BSN.cpow_neg_s_mk qz152 104500 1000 4 qz153 rfl)

noncomputable def ep684 := nat_lit 335499151247772813450833582432937841

noncomputable def ep685 := BSN.cos_dyadic_bound_f 761066939 2147483648 2 1 1048576 267640 ep684 ep62 ep684 ep684 ep63 ep684 983412 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 761066939) qz292 0 1 ep684 ep62 ep684 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 761066939) qz293 0 1 ep684 ep63 ep684 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz445 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 151904753) qz26)

noncomputable def ep686 := @Enclosure.Real.IsNear.cos_image qz156 qz445 Bool.false 151904753 1048576 209 267378 Bool.false 983412 1048576 1 133689 (@Enclosure.Real.IsNear.mulLit_ff qz152 qz301 104500 1000 0 1 726817 524288 1 133689 151904753 1048576 209 267378 qz154 qz303 rfl) (Enclosure.sfrac_false_div 151904753 1048576) (BSN.cos_reduce0 qz445 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 53555324802485511520256) qz27) 226375608064910080 72057594037927936 Bool.false 983412 1048576 23 1000000000000000 267378 133689 (BSN.sin_reduce_arg_pos_rat_q0 151904753 1048576 226375608064910080 72057594037927936 23 53555324802485511520256 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 983412 1048576 53555324802485511520256 151115727451828646838272 761066939 2147483648 267640 267378 (ep685 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep687 := BSN.sin_dyadic_bound_f 761066939 2147483648 2 1 1048576 267640 ep684 ep58 ep684 ep684 ep59 ep684 363884 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 761066939) qz287 0 1 ep684 ep58 ep684 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 761066939) qz288 0 1 ep684 ep59 ep684 rfl rfl rfl rfl) rfl rfl

noncomputable def ep688 := @Enclosure.Real.IsNear.sin_image qz156 qz445 Bool.false 151904753 1048576 209 267378 Bool.false 363884 1048576 1 133689 (@Enclosure.Real.IsNear.mulLit_ff qz152 qz301 104500 1000 0 1 726817 524288 1 133689 151904753 1048576 209 267378 qz154 qz303 rfl) (Enclosure.sfrac_false_div 151904753 1048576) (BSN.sin_reduce0 qz445 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 53555324802485511520256) qz27) 226375608064910080 72057594037927936 Bool.false 363884 1048576 23 1000000000000000 267378 133689 (BSN.sin_reduce_arg_pos_rat_q0 151904753 1048576 226375608064910080 72057594037927936 23 53555324802485511520256 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 363884 1048576 53555324802485511520256 151115727451828646838272 761066939 2147483648 267640 267378 (ep687 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep689 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz22 (Real.cos qz156)) (@HMul.hMul Real Real Real qz0 qz22 (@Neg.neg Real Real.instNeg (Real.sin qz156))) Bool.false 128897531811 274877906944 14532677433013 36748152501436416 Bool.true 47694912677 274877906944 14511971413315 36748152501436416 (@Enclosure.Real.IsNear.mulLit_ff qz22 (Real.cos qz156) 524287 1048576 1 1048576 245853 262144 211 267378 128897531811 274877906944 14532677433013 36748152501436416 qz304 (@Enclosure.Real.IsNear.recentre' (Real.cos qz156) Bool.false 983412 1048576 28208379 35745497442 245853 262144 211 267378 (ep686 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz22 (@Neg.neg Real Real.instNeg (Real.sin qz156)) 524287 1048576 1 1048576 90971 262144 211 267378 47694912677 274877906944 14511971413315 36748152501436416 qz304 (@Enclosure.Real.IsNear.neg (Real.sin qz156) Bool.false 90971 262144 211 267378 (@Enclosure.Real.IsNear.recentre' (Real.sin qz156) Bool.false 363884 1048576 28208379 35745497442 90971 262144 211 267378 (ep688 rfl rfl) rfl)) rfl)

noncomputable def ep690 := @ep661 128897531811 274877906944 14532677433013 36748152501436416 Bool.true 47694912677 274877906944 14511971413315 36748152501436416 Bool.false 6555996874660663787520 190804621515 274877906944 51820751966663 36748152501436416 Bool.true 187653498742822594936832 682679451503 1099511627776 207206645645675 146992610005745664 (ep662 (BSN.head_sum_c_succ qz149 3 4 rfl rfl) (ep682 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep683 ep689) rfl rfl

noncomputable abbrev qz157 := (@HMul.hMul Real Real Real qz268 qz441 qz305)

noncomputable def ep691 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz279 qz150) (Complex.mk (@HMul.hMul Real Real Real qz0 qz24 (Real.cos qz157)) (@HMul.hMul Real Real Real qz0 qz24 (@Neg.neg Real Real.instNeg (Real.sin qz157)))) Bool.false 54399036685 1099511627776 51891666048829 146992610005745664 Bool.false 488697536243 1099511627776 52015479977155 146992610005745664 (BSN.cpow_neg_s_mk qz152 104500 1000 5 qz153 rfl)

noncomputable def ep692 := BSN.sin_dyadic_bound_f 238067260 2147483648 1 0 1048576 267640 0 1 1 0 1 1 116005 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 238067260) qz287 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 238067260) qz288 0 0 rfl) rfl rfl

noncomputable abbrev qz446 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 5511121) (@Nat.cast Real Real.instNatCast 32768))

noncomputable def ep693 := @Enclosure.Real.IsNear.cos_image qz157 qz446 Bool.false 5511121 32768 209 267378 Bool.false 116005 1048576 1 133689 (@Enclosure.Real.IsNear.mulLit_ff qz152 qz305 104500 1000 0 1 843808 524288 1 133689 5511121 32768 209 267378 qz154 qz307 rfl) (Enclosure.sfrac_false_div 5511121 32768) (BSN.cos_reduce3 qz446 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 523515441204724498432) qz381) 226375608064910080 72057594037927936 Bool.false 116005 1048576 26 1000000000000000 267378 133689 (BSN.sin_reduce_arg_pos_rat_q3 5511121 32768 226375608064910080 72057594037927936 26 523515441204724498432 4722366482869645213696 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 116005 1048576 523515441204724498432 4722366482869645213696 238067260 2147483648 267640 267378 (ep692 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep694 := nat_lit 3212171275221905712107525337760000

noncomputable def ep695 := BSN.cos_dyadic_bound_f 238067260 2147483648 2 1 1048576 267640 ep694 ep62 ep694 ep694 ep63 ep694 1042139 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 238067260) qz292 0 1 ep694 ep62 ep694 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 238067260) qz293 0 1 ep694 ep63 ep694 rfl rfl rfl rfl) rfl rfl

noncomputable def ep696 := @Enclosure.Real.IsNear.sin_image qz157 qz446 Bool.false 5511121 32768 209 267378 Bool.true 1042139 1048576 1 133689 (@Enclosure.Real.IsNear.mulLit_ff qz152 qz305 104500 1000 0 1 843808 524288 1 133689 5511121 32768 209 267378 qz154 qz307 rfl) (Enclosure.sfrac_false_div 5511121 32768) (BSN.sin_reduce3 qz446 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 523515441204724498432) qz381) 226375608064910080 72057594037927936 Bool.false 1042139 1048576 26 1000000000000000 267378 133689 (BSN.sin_reduce_arg_pos_rat_q3 5511121 32768 226375608064910080 72057594037927936 26 523515441204724498432 4722366482869645213696 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1042139 1048576 523515441204724498432 4722366482869645213696 238067260 2147483648 267640 267378 (ep695 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep697 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz24 (Real.cos qz157)) (@HMul.hMul Real Real Real qz0 qz24 (@Neg.neg Real Real.instNeg (Real.sin qz157))) Bool.false 54399036685 1099511627776 51891666048829 146992610005745664 Bool.false 488697536243 1099511627776 52015479977155 146992610005745664 (@Enclosure.Real.IsNear.mulLit_ff qz24 (Real.cos qz157) 468937 1048576 1 1048576 116005 1048576 211 267378 54399036685 1099511627776 51891666048829 146992610005745664 qz308 (@Enclosure.Real.IsNear.recentre' (Real.cos qz157) Bool.false 116005 1048576 28208379 35745497442 116005 1048576 211 267378 (ep693 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz24 (@Neg.neg Real Real.instNeg (Real.sin qz157)) 468937 1048576 1 1048576 1042139 1048576 211 267378 488697536243 1099511627776 52015479977155 146992610005745664 qz308 (@Enclosure.Real.IsNear.neg (Real.sin qz157) Bool.true 1042139 1048576 211 267378 (@Enclosure.Real.IsNear.recentre' (Real.sin qz157) Bool.true 1042139 1048576 28208379 35745497442 1042139 1048576 211 267378 (ep696 rfl rfl) rfl)) rfl)

noncomputable def ep698 := @ep659 54399036685 1099511627776 51891666048829 146992610005745664 Bool.false 488697536243 1099511627776 52015479977155 146992610005745664 Bool.false 224744993332883913441280 817617522745 1099511627776 86391557971827 48997536668581888 Bool.true 213285371406628694261760 48495478815 274877906944 43203687603805 24498768334290944 (ep660 (BSN.head_sum_c_succ qz149 4 5 rfl rfl) (ep690 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep691 ep697) rfl rfl

noncomputable abbrev qz158 := (@HMul.hMul Real Real Real qz268 qz441 qz543)

noncomputable def ep699 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz278 qz150) (Complex.mk (@HMul.hMul Real Real Real qz0 qz28 (Real.cos qz158)) (@HMul.hMul Real Real Real qz0 qz28 (@Neg.neg Real Real.instNeg (Real.sin qz158)))) Bool.false 4332587559 34359738368 1481888561759 4593519062679552 Bool.false 426925327095 1099511627776 47510464560625 146992610005745664 (BSN.cpow_neg_s_mk qz152 104500 1000 6 qz153 rfl)

noncomputable def ep700 := @Enclosure.Real.IsNear.mulLit_ff qz152 qz543 104500 1000 0 1 4034681531866359 2251799813685248 500000000133689 66844500000000000000 843248440160069031 4503599627370496 104500000027941001 133689000000000000000 qz154 (BSN.isNear_log_sfrac 6 1 4034681531866359 2251799813685248 500000000133689 66844500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz310) Bool.false 33845361775666394038272 18889465931478580854784 1000000000267378 133689000000000000000 4034681531866359 2251799813685248 500000000133689 66844500000000000000 (BSN.log_rat_reduce_isNear 6 1 2 12 8 212580 524288 24973259072661432 36028797018963968 133689 1000000000000000 rfl rfl rfl rfl (ep117 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep701 := nat_lit 206756406255998504170588192509670416

noncomputable def ep702 := BSN.sin_dyadic_bound_f 674317986 2147483648 2 1 1048576 267640 ep701 ep58 ep701 ep701 ep59 ep701 323872 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 674317986) qz287 0 1 ep701 ep58 ep701 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 674317986) qz288 0 1 ep701 ep59 ep701 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz447 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 196334077) qz26)

noncomputable def ep703 := @Enclosure.Real.IsNear.cos_image qz158 qz447 Bool.false 196334077 1048576 205 262144 Bool.false 323872 1048576 1 133689 (@Enclosure.Real.IsNear.recentre' qz158 Bool.false 843248440160069031 4503599627370496 104500000027941001 133689000000000000000 196334077 1048576 205 262144 (ep700 rfl) rfl) (Enclosure.sfrac_false_div 196334077 1048576) (BSN.cos_reduce3 qz447 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 47450909884301520666624) qz27) 226375608064910080 72057594037927936 Bool.false 323872 1048576 29 1000000000000000 267378 133689 (BSN.sin_reduce_arg_pos_rat_q3 196334077 1048576 226375608064910080 72057594037927936 29 47450909884301520666624 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 323872 1048576 47450909884301520666624 151115727451828646838272 674317986 2147483648 267640 267378 (ep702 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep704 := BSN.cos_dyadic_bound_f 674317986 2147483648 2 1 1048576 267640 ep701 ep62 ep701 ep701 ep63 ep701 997305 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 674317986) qz292 0 1 ep701 ep62 ep701 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 674317986) qz293 0 1 ep701 ep63 ep701 rfl rfl rfl rfl) rfl rfl

noncomputable def ep705 := @Enclosure.Real.IsNear.sin_image qz158 qz447 Bool.false 196334077 1048576 205 262144 Bool.true 997305 1048576 1 133689 (@Enclosure.Real.IsNear.recentre' qz158 Bool.false 843248440160069031 4503599627370496 104500000027941001 133689000000000000000 196334077 1048576 205 262144 (ep700 rfl) rfl) (Enclosure.sfrac_false_div 196334077 1048576) (BSN.sin_reduce3 qz447 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 47450909884301520666624) qz27) 226375608064910080 72057594037927936 Bool.false 997305 1048576 29 1000000000000000 267378 133689 (BSN.sin_reduce_arg_pos_rat_q3 196334077 1048576 226375608064910080 72057594037927936 29 47450909884301520666624 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 997305 1048576 47450909884301520666624 151115727451828646838272 674317986 2147483648 267640 267378 (ep704 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep706 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz28 (Real.cos qz158)) (@HMul.hMul Real Real Real qz0 qz28 (@Neg.neg Real Real.instNeg (Real.sin qz158))) Bool.false 4332587559 34359738368 1481888561759 4593519062679552 Bool.false 426925327095 1099511627776 47510464560625 146992610005745664 (@Enclosure.Real.IsNear.mulLit_ff qz28 (Real.cos qz158) 428079 1048576 1 1048576 10121 32768 27668389 35045769216 4332587559 34359738368 1481888561759 4593519062679552 qz312 (@Enclosure.Real.IsNear.recentre' (Real.cos qz158) Bool.false 323872 1048576 27668389 35045769216 10121 32768 27668389 35045769216 (ep703 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz28 (@Neg.neg Real Real.instNeg (Real.sin qz158)) 428079 1048576 1 1048576 997305 1048576 27668389 35045769216 426925327095 1099511627776 47510464560625 146992610005745664 qz312 (@Enclosure.Real.IsNear.neg (Real.sin qz158) Bool.true 997305 1048576 27668389 35045769216 (@Enclosure.Real.IsNear.recentre' (Real.sin qz158) Bool.true 997305 1048576 27668389 35045769216 997305 1048576 27668389 35045769216 (ep705 rfl rfl) rfl)) rfl)

noncomputable def ep707 := @ep657 4332587559 34359738368 1481888561759 4593519062679552 Bool.false 426925327095 1099511627776 47510464560625 146992610005745664 Bool.false 32856854566088625618944 956260324633 1099511627776 306595107891769 146992610005745664 Bool.false 64030997481598998282240 232943411835 1099511627776 306732590183455 146992610005745664 (ep658 (BSN.head_sum_c_succ qz149 5 6 rfl rfl) (ep698 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep699 ep706) rfl rfl

noncomputable abbrev qz159 := (@HMul.hMul Real Real Real qz268 qz441 qz544)

noncomputable def ep708 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz277 qz150) (Complex.mk (@HMul.hMul Real Real Real qz0 qz30 (Real.cos qz159)) (@HMul.hMul Real Real Real qz0 qz30 (@Neg.neg Real Real.instNeg (Real.sin qz159)))) Bool.true 34046299125 137438953472 686791940369 2296759531339776 Bool.true 313876321275 1099511627776 43968685031519 146992610005745664 (BSN.cpow_neg_s_mk qz152 104500 1000 7 qz153 rfl)

noncomputable def ep709 := @Enclosure.Real.IsNear.mulLit_ff qz152 qz544 104500 1000 0 1 4381796493761783 2251799813685248 500000000133689 66844500000000000000 915795467196212647 4503599627370496 104500000027941001 133689000000000000000 qz154 (BSN.isNear_log_sfrac 7 1 4381796493761783 2251799813685248 500000000133689 66844500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz314) Bool.false 36757173121942042968064 18889465931478580854784 1000000000267378 133689000000000000000 4381796493761783 2251799813685248 500000000133689 66844500000000000000 (BSN.log_rat_reduce_isNear 7 1 2 14 8 293399 524288 24973259072661432 36028797018963968 133689 1000000000000000 rfl rfl rfl rfl (ep132 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep710 := nat_lit 5549509813524096063205781461658367121

noncomputable def ep711 := BSN.sin_dyadic_bound_f 1534841933 2147483648 2 1 1048576 267640 ep710 ep58 ep710 ep710 ep59 ep710 687240 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1534841933) qz287 0 1 ep710 ep58 ep710 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1534841933) qz288 0 1 ep710 ep59 ep710 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz448 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 6663289) (@Nat.cast Real Real.instNatCast 32768))

noncomputable def ep712 := @Enclosure.Real.IsNear.cos_image qz159 qz448 Bool.false 6663289 32768 205 262144 Bool.true 687240 1048576 1 133689 (@Enclosure.Real.IsNear.recentre' qz159 Bool.false 915795467196212647 4503599627370496 104500000027941001 133689000000000000000 6663289 32768 205 262144 (ep709 rfl) rfl) (Enclosure.sfrac_false_div 6663289 32768) (BSN.cos_reduce1 qz448 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 3375153104626015797248) qz381) 226375608064910080 72057594037927936 Bool.false 687240 1048576 32 1000000000000000 267378 133689 (BSN.sin_reduce_arg_pos_rat_q1 6663289 32768 226375608064910080 72057594037927936 32 3375153104626015797248 4722366482869645213696 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 687240 1048576 3375153104626015797248 4722366482869645213696 1534841933 2147483648 267640 267378 (ep711 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep713 := nat_lit 198312832191850701186739290535391490965193690713737943713347262080646637337121

noncomputable def ep714 := nat_lit 30797059170400247460704981603080981659921534074211743263500934828013828641

noncomputable def ep715 := nat_lit 594876902457211303065296461642968310932261229073065407653514784372283884354081

noncomputable def ep716 := BSN.cos_dyadic_bound_f 1534841933 2147483648 3 2 1048576 267640 ep713 ep75 ep714 ep715 ep78 ep714 791967 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1534841933) qz292 0 2 ep713 ep75 ep714 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1534841933) qz293 0 2 ep715 ep78 ep714 rfl rfl rfl rfl) rfl rfl

noncomputable def ep717 := @Enclosure.Real.IsNear.sin_image qz159 qz448 Bool.false 6663289 32768 205 262144 Bool.false 791967 1048576 1 133689 (@Enclosure.Real.IsNear.recentre' qz159 Bool.false 915795467196212647 4503599627370496 104500000027941001 133689000000000000000 6663289 32768 205 262144 (ep709 rfl) rfl) (Enclosure.sfrac_false_div 6663289 32768) (BSN.sin_reduce1 qz448 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 3375153104626015797248) qz381) 226375608064910080 72057594037927936 Bool.false 791967 1048576 32 1000000000000000 267378 133689 (BSN.sin_reduce_arg_pos_rat_q1 6663289 32768 226375608064910080 72057594037927936 32 3375153104626015797248 4722366482869645213696 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 791967 1048576 3375153104626015797248 4722366482869645213696 1534841933 2147483648 267640 267378 (ep716 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep718 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz30 (Real.cos qz159)) (@HMul.hMul Real Real Real qz0 qz30 (@Neg.neg Real Real.instNeg (Real.sin qz159))) Bool.true 34046299125 137438953472 686791940369 2296759531339776 Bool.true 313876321275 1099511627776 43968685031519 146992610005745664 (@Enclosure.Real.IsNear.mulLit_ft qz30 (Real.cos qz159) 396325 1048576 1 1048576 85905 131072 27668389 35045769216 34046299125 137438953472 686791940369 2296759531339776 qz317 (@Enclosure.Real.IsNear.recentre' (Real.cos qz159) Bool.true 687240 1048576 27668389 35045769216 85905 131072 27668389 35045769216 (ep712 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz30 (@Neg.neg Real Real.instNeg (Real.sin qz159)) 396325 1048576 1 1048576 791967 1048576 27668389 35045769216 313876321275 1099511627776 43968685031519 146992610005745664 qz317 (@Enclosure.Real.IsNear.neg (Real.sin qz159) Bool.false 791967 1048576 27668389 35045769216 (@Enclosure.Real.IsNear.recentre' (Real.sin qz159) Bool.false 791967 1048576 27668389 35045769216 791967 1048576 27668389 35045769216 (ep717 rfl rfl) rfl)) rfl)

noncomputable def ep719 := @ep655 34046299125 137438953472 686791940369 2296759531339776 Bool.true 313876321275 1099511627776 43968685031519 146992610005745664 Bool.false 93993116493677147979776 683889931633 1099511627776 116849930691795 48997536668581888 Bool.true 88986674999021996605440 632288355 8589934592 58450212535829 24498768334290944 (ep656 (BSN.head_sum_c_succ qz149 6 7 rfl rfl) (ep707 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep708 ep718) rfl rfl

noncomputable abbrev qz160 := (@HMul.hMul Real Real Real qz268 qz441 qz545)

noncomputable def ep720 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz276 qz150) (Complex.mk (@HMul.hMul Real Real Real qz0 qz32 (Real.cos qz160)) (@HMul.hMul Real Real Real qz0 qz32 (@Neg.neg Real Real.instNeg (Real.sin qz160)))) Bool.true 167529677665 549755813888 6866695850945 24498768334290944 Bool.false 98552212045 549755813888 6858404459165 24498768334290944 (BSN.cpow_neg_s_mk qz152 104500 1000 8 qz153 rfl)

noncomputable def ep721 := @Enclosure.Real.IsNear.mulLit_ff qz152 qz545 104500 1000 0 1 9364972152248037 4503599627370496 1000000000401067 133689000000000000000 1957279179819839733 9007199254740992 209000000083823003 267378000000000000000 qz154 (BSN.isNear_log_sfrac 8 1 9364972152248037 4503599627370496 1000000000401067 133689000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz319) Bool.false 39279540158062550581248 18889465931478580854784 1000000000401067 133689000000000000000 9364972152248037 4503599627370496 1000000000401067 133689000000000000000 (BSN.log_rat_reduce_isNear 8 1 3 16 16 0 524288 24973259072661432 36028797018963968 133689 1000000000000000 rfl rfl rfl rfl (ep147 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep722 := nat_lit 1700360482688600134082442516606236641

noncomputable def ep723 := BSN.cos_dyadic_bound_f 1141918873 2147483648 2 1 1048576 267640 ep722 ep62 ep722 ep722 ep63 ep722 903790 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1141918873) qz292 0 1 ep722 ep62 ep722 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1141918873) qz293 0 1 ep722 ep63 ep722 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz449 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 227857285) qz26)

noncomputable def ep724 := @Enclosure.Real.IsNear.cos_image qz160 qz449 Bool.false 227857285 1048576 821 1048576 Bool.true 903790 1048576 1 133689 (@Enclosure.Real.IsNear.recentre' qz160 Bool.false 1957279179819839733 9007199254740992 209000000083823003 267378000000000000000 227857285 1048576 821 1048576 (ep721 rfl) rfl) (Enclosure.sfrac_false_div 227857285 1048576) (BSN.cos_reduce2 qz449 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 80355397115474062868480) qz27) 226375608064910080 72057594037927936 Bool.false 903790 1048576 34 1000000000000000 267378 133689 (BSN.sin_reduce_arg_pos_rat_q2 227857285 1048576 226375608064910080 72057594037927936 34 80355397115474062868480 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 903790 1048576 80355397115474062868480 151115727451828646838272 1141918873 2147483648 267640 267378 (ep723 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep725 := BSN.sin_dyadic_bound_f 1141918873 2147483648 2 1 1048576 267640 ep722 ep58 ep722 ep722 ep59 ep722 531670 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1141918873) qz287 0 1 ep722 ep58 ep722 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1141918873) qz288 0 1 ep722 ep59 ep722 rfl rfl rfl rfl) rfl rfl

noncomputable def ep726 := @Enclosure.Real.IsNear.sin_image qz160 qz449 Bool.false 227857285 1048576 821 1048576 Bool.true 531670 1048576 1 133689 (@Enclosure.Real.IsNear.recentre' qz160 Bool.false 1957279179819839733 9007199254740992 209000000083823003 267378000000000000000 227857285 1048576 821 1048576 (ep721 rfl) rfl) (Enclosure.sfrac_false_div 227857285 1048576) (BSN.sin_reduce2 qz449 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 80355397115474062868480) qz27) 226375608064910080 72057594037927936 Bool.false 531670 1048576 34 1000000000000000 267378 133689 (BSN.sin_reduce_arg_pos_rat_q2 227857285 1048576 226375608064910080 72057594037927936 34 80355397115474062868480 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 531670 1048576 80355397115474062868480 151115727451828646838272 1141918873 2147483648 267640 267378 (ep725 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep727 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz32 (Real.cos qz160)) (@HMul.hMul Real Real Real qz0 qz32 (@Neg.neg Real Real.instNeg (Real.sin qz160))) Bool.true 167529677665 549755813888 6866695850945 24498768334290944 Bool.false 98552212045 549755813888 6858404459165 24498768334290944 (@Enclosure.Real.IsNear.mulLit_ft qz32 (Real.cos qz160) 370727 1048576 1 1048576 451895 524288 110807245 140183076864 167529677665 549755813888 6866695850945 24498768334290944 qz321 (@Enclosure.Real.IsNear.recentre' (Real.cos qz160) Bool.true 903790 1048576 110807245 140183076864 451895 524288 110807245 140183076864 (ep724 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz32 (@Neg.neg Real Real.instNeg (Real.sin qz160)) 370727 1048576 1 1048576 265835 524288 110807245 140183076864 98552212045 549755813888 6858404459165 24498768334290944 qz321 (@Enclosure.Real.IsNear.neg (Real.sin qz160) Bool.true 265835 524288 110807245 140183076864 (@Enclosure.Real.IsNear.recentre' (Real.sin qz160) Bool.true 531670 1048576 110807245 140183076864 265835 524288 110807245 140183076864 (ep726 rfl rfl) rfl)) rfl)

noncomputable def ep728 := @ep653 167529677665 549755813888 6866695850945 24498768334290944 Bool.false 98552212045 549755813888 6858404459165 24498768334290944 Bool.false 191771637384475851096064 348830576303 1099511627776 130583322393685 48997536668581888 Bool.false 498952856148534886400 58085757325 549755813888 32654308497497 12249384167145472 (ep654 (BSN.head_sum_c_succ qz149 7 8 rfl rfl) (ep719 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep720 ep727) rfl rfl

theorem EMRow31.d12 : Enclosure.Complex.IsNear qz148 Bool.false 348830576303 1099511627776 130583322393685 48997536668581888 Bool.false 58085757325 549755813888 32654308497497 12249384167145472 := ep652 (BSN.head_sum_c_succ qz149 8 9 rfl rfl) (ep728 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable abbrev qz161 := (BSN.headSumC qz439 17)

noncomputable abbrev qz450 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 16) qz150)

noncomputable def ep729 := @Enclosure.Complex.IsNear.of_eq qz161 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz149 16) qz450) Bool.false 269391073475 549755813888 329429024728663 73496305002872832 Bool.false 5041728619 274877906944 164728000180697 36748152501436416

noncomputable def ep730 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz149 16) qz450 Bool.false 330146465395 1099511627776 629739239723497 146992610005745664 Bool.false 199131678433 1099511627776 629808322712113 146992610005745664 Bool.false

noncomputable abbrev qz451 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 15) qz150)

noncomputable def ep731 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz149 16) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz149 15) qz451) Bool.false 330146465395 1099511627776 629739239723497 146992610005745664 Bool.false 199131678433 1099511627776 629808322712113 146992610005745664

noncomputable def ep732 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz149 15) qz451 Bool.false 27459778883 549755813888 99933860084111 24498768334290944 Bool.false 268738106569 1099511627776 199924592226393 48997536668581888 Bool.false

noncomputable abbrev qz452 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 14) qz150)

noncomputable def ep733 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz149 15) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz149 14) qz452) Bool.false 27459778883 549755813888 99933860084111 24498768334290944 Bool.false 268738106569 1099511627776 199924592226393 48997536668581888

noncomputable def ep734 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz149 14) qz452 Bool.true 10861917371 68719476736 142110247368085 36748152501436416 Bool.false 21057719875 274877906944 35539543284157 9187038125359104 Bool.false

noncomputable abbrev qz453 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 13) qz150)

noncomputable def ep735 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz149 14) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz149 13) qz453) Bool.true 10861917371 68719476736 142110247368085 36748152501436416 Bool.false 21057719875 274877906944 35539543284157 9187038125359104

noncomputable def ep736 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz149 13) qz453 Bool.true 9448636397 1099511627776 178713345511461 48997536668581888 Bool.true 86323339147 549755813888 89381533629015 24498768334290944 Bool.true

noncomputable abbrev qz585 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 12) qz150)

noncomputable def ep737 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz149 13) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz149 12) qz585) Bool.true 9448636397 1099511627776 178713345511461 48997536668581888 Bool.true 86323339147 549755813888 89381533629015 24498768334290944

noncomputable def ep738 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz149 12) qz585 Bool.false 8767432573 68719476736 7852074632687 2296759531339776 Bool.false 13402387223 137438953472 251312232476797 73496305002872832 Bool.true

noncomputable abbrev qz586 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 11) qz150)

noncomputable def ep739 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz149 12) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz149 11) qz586) Bool.false 8767432573 68719476736 7852074632687 2296759531339776 Bool.false 13402387223 137438953472 251312232476797 73496305002872832

noncomputable def ep740 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz149 11) qz586 Bool.true 51430809841 549755813888 29212335375113 9187038125359104 Bool.true 118134766403 1099511627776 467496575672885 146992610005745664 Bool.false

noncomputable abbrev qz587 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 10) qz150)

noncomputable def ep741 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz149 11) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz149 10) qz587) Bool.true 51430809841 549755813888 29212335375113 9187038125359104 Bool.true 118134766403 1099511627776 467496575672885 146992610005745664

noncomputable def ep742 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz149 10) qz587 Bool.true 2017417061 549755813888 215307473481349 73496305002872832 Bool.false 26902576025 137438953472 26913725008877 9187038125359104 Bool.true

noncomputable def ep743 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz149 10) (@HAdd.hAdd Complex Complex Complex qz4 qz148 (@HPow.hPow Complex Complex Complex qz6 qz322 qz150)) Bool.true 2017417061 549755813888 215307473481349 73496305002872832 Bool.false 26902576025 137438953472 26913725008877 9187038125359104

noncomputable def ep744 := @Enclosure.Complex.IsNear.addLitP qz148 (@HPow.hPow Complex Complex Complex qz6 qz322 qz150) Bool.false 348830576303 1099511627776 130583322393685 48997536668581888 Bool.false 58085757325 549755813888 32654308497497 12249384167145472 Bool.true

noncomputable abbrev qz162 := (@HMul.hMul Real Real Real qz268 qz441 qz549)

noncomputable def ep745 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz322 qz150) (Complex.mk (@HMul.hMul Real Real Real qz0 qz42 (Real.cos qz162)) (@HMul.hMul Real Real Real qz0 qz42 (@Neg.neg Real Real.instNeg (Real.sin qz162)))) Bool.true 352865410425 1099511627776 38864979781643 146992610005745664 Bool.false 49524546775 549755813888 9691974543017 36748152501436416 (BSN.cpow_neg_s_mk qz152 104500 1000 9 qz153 rfl)

noncomputable def ep746 := @Enclosure.Real.IsNear.mulLit_ff qz152 qz549 104500 1000 0 1 9895417793173221 4503599627370496 1000000000401067 133689000000000000000 2068142318773203189 9007199254740992 209000000083823003 267378000000000000000 qz154 (BSN.isNear_log_sfrac 9 1 9895417793173221 4503599627370496 1000000000401067 133689000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz324) Bool.false 41504390431577613533184 18889465931478580854784 1000000000401067 133689000000000000000 9895417793173221 4503599627370496 1000000000401067 133689000000000000000 (BSN.log_rat_reduce_isNear 9 1 3 18 16 61752 524288 24973259072661432 36028797018963968 133689 1000000000000000 rfl rfl rfl rfl (ep175 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep747 := nat_lit 119275274510207355046629863486918656

noncomputable def ep748 := BSN.cos_dyadic_bound_f 587675528 2147483648 2 1 1048576 267640 ep747 ep62 ep747 ep747 ep63 ep747 1009557 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 587675528) qz292 0 1 ep747 ep62 ep747 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 587675528) qz293 0 1 ep747 ep63 ep747 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz454 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 240763453) qz26)

noncomputable def ep749 := @Enclosure.Real.IsNear.cos_image qz162 qz454 Bool.false 240763453 1048576 821 1048576 Bool.true 1009557 1048576 1 133689 (@Enclosure.Real.IsNear.recentre' qz162 Bool.false 2068142318773203189 9007199254740992 209000000083823003 267378000000000000000 240763453 1048576 821 1048576 (ep746 rfl) rfl) (Enclosure.sfrac_false_div 240763453 1048576) (BSN.cos_reduce2 qz454 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 41353988955897474318336) qz27) 226375608064910080 72057594037927936 Bool.false 1009557 1048576 36 1000000000000000 267378 133689 (BSN.sin_reduce_arg_pos_rat_q2 240763453 1048576 226375608064910080 72057594037927936 36 41353988955897474318336 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1009557 1048576 41353988955897474318336 151115727451828646838272 587675528 2147483648 267640 267378 (ep748 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep750 := BSN.sin_dyadic_bound_f 587675528 2147483648 2 1 1048576 267640 ep747 ep58 ep747 ep747 ep59 ep747 283382 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 587675528) qz287 0 1 ep747 ep58 ep747 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 587675528) qz288 0 1 ep747 ep59 ep747 rfl rfl rfl rfl) rfl rfl

noncomputable def ep751 := @Enclosure.Real.IsNear.sin_image qz162 qz454 Bool.false 240763453 1048576 821 1048576 Bool.true 283382 1048576 1 133689 (@Enclosure.Real.IsNear.recentre' qz162 Bool.false 2068142318773203189 9007199254740992 209000000083823003 267378000000000000000 240763453 1048576 821 1048576 (ep746 rfl) rfl) (Enclosure.sfrac_false_div 240763453 1048576) (BSN.sin_reduce2 qz454 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 41353988955897474318336) qz27) 226375608064910080 72057594037927936 Bool.false 283382 1048576 36 1000000000000000 267378 133689 (BSN.sin_reduce_arg_pos_rat_q2 240763453 1048576 226375608064910080 72057594037927936 36 41353988955897474318336 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 283382 1048576 41353988955897474318336 151115727451828646838272 587675528 2147483648 267640 267378 (ep750 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep752 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz42 (Real.cos qz162)) (@HMul.hMul Real Real Real qz0 qz42 (@Neg.neg Real Real.instNeg (Real.sin qz162))) Bool.true 352865410425 1099511627776 38864979781643 146992610005745664 Bool.false 49524546775 549755813888 9691974543017 36748152501436416 (@Enclosure.Real.IsNear.mulLit_ft qz42 (Real.cos qz162) 349525 1048576 1 1048576 1009557 1048576 110807245 140183076864 352865410425 1099511627776 38864979781643 146992610005745664 qz326 (@Enclosure.Real.IsNear.recentre' (Real.cos qz162) Bool.true 1009557 1048576 110807245 140183076864 1009557 1048576 110807245 140183076864 (ep749 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz42 (@Neg.neg Real Real.instNeg (Real.sin qz162)) 349525 1048576 1 1048576 141691 524288 110807245 140183076864 49524546775 549755813888 9691974543017 36748152501436416 qz326 (@Enclosure.Real.IsNear.neg (Real.sin qz162) Bool.true 141691 524288 110807245 140183076864 (@Enclosure.Real.IsNear.recentre' (Real.sin qz162) Bool.true 283382 1048576 110807245 140183076864 141691 524288 110807245 140183076864 (ep751 rfl rfl) rfl)) rfl)

noncomputable def ep753 := @ep744 352865410425 1099511627776 38864979781643 146992610005745664 Bool.false 49524546775 549755813888 9691974543017 36748152501436416 Bool.true 4436347033286367772672 2017417061 549755813888 215307473481349 73496305002872832 Bool.false 59159390313230683340800 26902576025 137438953472 26913725008877 9187038125359104 EMRow31.d12 (ep745 ep752) rfl rfl

noncomputable abbrev qz163 := (@HMul.hMul Real Real Real qz268 qz441 qz550)

noncomputable def ep754 := @Enclosure.Complex.IsNear.of_eq qz587 (Complex.mk (@HMul.hMul Real Real Real qz0 qz44 (Real.cos qz163)) (@HMul.hMul Real Real Real qz0 qz44 (@Neg.neg Real Real.instNeg (Real.sin qz163)))) Bool.true 12353348195 137438953472 6130403173185 24498768334290944 Bool.true 333355374603 1099511627776 12292325176951 48997536668581888 (BSN.cpow_neg_s_mk qz152 104500 1000 10 qz153 rfl)

noncomputable def ep755 := @Enclosure.Real.IsNear.mulLit_ff qz152 qz550 104500 1000 0 1 10369917190100709 4503599627370496 1000000000401067 133689000000000000000 2167312692731048181 9007199254740992 209000000083823003 267378000000000000000 qz154 (BSN.isNear_log_sfrac 10 1 10369917190100709 4503599627370496 1000000000401067 133689000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz328) Bool.false 43494585150108164161536 18889465931478580854784 1000000000401067 133689000000000000000 10369917190100709 4503599627370496 1000000000401067 133689000000000000000 (BSN.log_rat_reduce_isNear 10 1 3 20 16 116991 524288 24973259072661432 36028797018963968 133689 1000000000000000 rfl rfl rfl rfl (ep185 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep756 := nat_lit 146735705742615557140831377328052496

noncomputable def ep757 := BSN.sin_dyadic_bound_f 618919194 2147483648 2 1 1048576 267640 ep756 ep58 ep756 ep756 ep59 ep756 298040 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 618919194) qz287 0 1 ep756 ep58 ep756 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 618919194) qz288 0 1 ep756 ep59 ep756 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz455 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 63077101) (@Nat.cast Real Real.instNatCast 262144))

noncomputable def ep758 := @Enclosure.Real.IsNear.cos_image qz163 qz455 Bool.false 63077101 262144 821 1048576 Bool.true 298040 1048576 1 133689 (@Enclosure.Real.IsNear.recentre' qz163 Bool.false 2167312692731048181 9007199254740992 209000000083823003 267378000000000000000 63077101 262144 821 1048576 (ep755 rfl) rfl) (Enclosure.sfrac_false_div 63077101 262144) (BSN.cos_reduce1 qz455 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 10888141607884933824512) qz316) 226375608064910080 72057594037927936 Bool.false 298040 1048576 38 1000000000000000 267378 133689 (BSN.sin_reduce_arg_pos_rat_q1 63077101 262144 226375608064910080 72057594037927936 38 10888141607884933824512 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 298040 1048576 10888141607884933824512 37778931862957161709568 618919194 2147483648 267640 267378 (ep757 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep759 := BSN.cos_dyadic_bound_f 618919194 2147483648 2 1 1048576 267640 ep756 ep62 ep756 ep756 ep63 ep756 1005327 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 618919194) qz292 0 1 ep756 ep62 ep756 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 618919194) qz293 0 1 ep756 ep63 ep756 rfl rfl rfl rfl) rfl rfl

noncomputable def ep760 := @Enclosure.Real.IsNear.sin_image qz163 qz455 Bool.false 63077101 262144 821 1048576 Bool.false 1005327 1048576 1 133689 (@Enclosure.Real.IsNear.recentre' qz163 Bool.false 2167312692731048181 9007199254740992 209000000083823003 267378000000000000000 63077101 262144 821 1048576 (ep755 rfl) rfl) (Enclosure.sfrac_false_div 63077101 262144) (BSN.sin_reduce1 qz455 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 10888141607884933824512) qz316) 226375608064910080 72057594037927936 Bool.false 1005327 1048576 38 1000000000000000 267378 133689 (BSN.sin_reduce_arg_pos_rat_q1 63077101 262144 226375608064910080 72057594037927936 38 10888141607884933824512 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1005327 1048576 10888141607884933824512 37778931862957161709568 618919194 2147483648 267640 267378 (ep759 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep761 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz44 (Real.cos qz163)) (@HMul.hMul Real Real Real qz0 qz44 (@Neg.neg Real Real.instNeg (Real.sin qz163))) Bool.true 12353348195 137438953472 6130403173185 24498768334290944 Bool.true 333355374603 1099511627776 12292325176951 48997536668581888 (@Enclosure.Real.IsNear.mulLit_ft qz44 (Real.cos qz163) 331589 1048576 1 1048576 37255 131072 110807245 140183076864 12353348195 137438953472 6130403173185 24498768334290944 qz330 (@Enclosure.Real.IsNear.recentre' (Real.cos qz163) Bool.true 298040 1048576 110807245 140183076864 37255 131072 110807245 140183076864 (ep758 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz44 (@Neg.neg Real Real.instNeg (Real.sin qz163)) 331589 1048576 1 1048576 1005327 1048576 110807245 140183076864 333355374603 1099511627776 12292325176951 48997536668581888 qz330 (@Enclosure.Real.IsNear.neg (Real.sin qz163) Bool.false 1005327 1048576 110807245 140183076864 (@Enclosure.Real.IsNear.recentre' (Real.sin qz163) Bool.false 1005327 1048576 110807245 140183076864 1005327 1048576 110807245 140183076864 (ep760 rfl rfl) rfl)) rfl)

noncomputable def ep762 := @ep742 12353348195 137438953472 6130403173185 24498768334290944 Bool.true 333355374603 1099511627776 12292325176951 48997536668581888 Bool.true 7068596680764478717952 51430809841 549755813888 29212335375113 9187038125359104 Bool.true 16236318663087505801216 118134766403 1099511627776 467496575672885 146992610005745664 (ep743 (BSN.head_sum_c_succ qz149 9 10 rfl rfl) (ep753 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep754 ep761) rfl rfl

noncomputable abbrev qz164 := (@HMul.hMul Real Real Real qz268 qz441 qz551)

noncomputable def ep763 := @Enclosure.Complex.IsNear.of_eq qz586 (Complex.mk (@HMul.hMul Real Real Real qz0 qz46 (Real.cos qz164)) (@HMul.hMul Real Real Real qz0 qz46 (@Neg.neg Real Real.instNeg (Real.sin qz164)))) Bool.false 121570270425 549755813888 731987718545 3062346041786368 Bool.false 225353864187 1099511627776 11709296426903 48997536668581888 (BSN.cpow_neg_s_mk qz152 104500 1000 11 qz153 rfl)

noncomputable def ep764 := @Enclosure.Real.IsNear.mulLit_ff qz152 qz551 104500 1000 0 1 10799156221662949 4503599627370496 1000000000401067 133689000000000000000 2257023650327556341 9007199254740992 209000000083823003 267378000000000000000 qz154 (BSN.isNear_log_sfrac 11 1 10799156221662949 4503599627370496 1000000000401067 133689000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz332) Bool.false 45294944137145793642496 18889465931478580854784 1000000000401067 133689000000000000000 10799156221662949 4503599627370496 1000000000401067 133689000000000000000 (BSN.log_rat_reduce_isNear 11 1 3 22 16 166961 524288 24973259072661432 36028797018963968 133689 1000000000000000 rfl rfl rfl rfl (ep200 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep765 := nat_lit 9773465727412957759480206610922244241

noncomputable def ep766 := BSN.sin_dyadic_bound_f 1768121677 2147483648 2 1 1048576 267640 ep765 ep58 ep765 ep765 ep59 ep765 769050 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1768121677) qz287 0 1 ep765 ep58 ep765 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1768121677) qz288 0 1 ep765 ep59 ep765 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz456 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 131376067) qz20)

noncomputable def ep767 := @Enclosure.Real.IsNear.cos_image qz164 qz456 Bool.false 131376067 524288 821 1048576 Bool.false 769050 1048576 1 133689 (@Enclosure.Real.IsNear.recentre' qz164 Bool.false 2257023650327556341 9007199254740992 209000000083823003 267378000000000000000 131376067 524288 821 1048576 (ep764 rfl) rfl) (Enclosure.sfrac_false_div 131376067 524288) (BSN.cos_reduce3 qz456 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 62210250990685534552064) qz21) 226375608064910080 72057594037927936 Bool.false 769050 1048576 39 1000000000000000 267378 133689 (BSN.sin_reduce_arg_pos_rat_q3 131376067 524288 226375608064910080 72057594037927936 39 62210250990685534552064 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 769050 1048576 62210250990685534552064 75557863725914323419136 1768121677 2147483648 267640 267378 (ep766 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep768 := nat_lit 349298015960523963388357832952099921522667364611590047957576436350787511280161

noncomputable def ep769 := nat_lit 95520632324915695547127551404569668075710724613201459499975800460057666081

noncomputable def ep770 := nat_lit 1047703006616922058773979243753490625231850672385543740953729357451442418508321

noncomputable def ep771 := BSN.cos_dyadic_bound_f 1768121677 2147483648 3 2 1048576 267640 ep768 ep75 ep769 ep770 ep78 ep769 712791 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1768121677) qz292 0 2 ep768 ep75 ep769 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1768121677) qz293 0 2 ep770 ep78 ep769 rfl rfl rfl rfl) rfl rfl

noncomputable def ep772 := @Enclosure.Real.IsNear.sin_image qz164 qz456 Bool.false 131376067 524288 821 1048576 Bool.true 712791 1048576 1 133689 (@Enclosure.Real.IsNear.recentre' qz164 Bool.false 2257023650327556341 9007199254740992 209000000083823003 267378000000000000000 131376067 524288 821 1048576 (ep764 rfl) rfl) (Enclosure.sfrac_false_div 131376067 524288) (BSN.sin_reduce3 qz456 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 62210250990685534552064) qz21) 226375608064910080 72057594037927936 Bool.false 712791 1048576 39 1000000000000000 267378 133689 (BSN.sin_reduce_arg_pos_rat_q3 131376067 524288 226375608064910080 72057594037927936 39 62210250990685534552064 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 712791 1048576 62210250990685534552064 75557863725914323419136 1768121677 2147483648 267640 267378 (ep771 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep773 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz46 (Real.cos qz164)) (@HMul.hMul Real Real Real qz0 qz46 (@Neg.neg Real Real.instNeg (Real.sin qz164))) Bool.false 121570270425 549755813888 731987718545 3062346041786368 Bool.false 225353864187 1099511627776 11709296426903 48997536668581888 (@Enclosure.Real.IsNear.mulLit_ff qz46 (Real.cos qz164) 316157 1048576 1 1048576 384525 524288 110807245 140183076864 121570270425 549755813888 731987718545 3062346041786368 qz334 (@Enclosure.Real.IsNear.recentre' (Real.cos qz164) Bool.false 769050 1048576 110807245 140183076864 384525 524288 110807245 140183076864 (ep767 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz46 (@Neg.neg Real Real.instNeg (Real.sin qz164)) 316157 1048576 1 1048576 712791 1048576 110807245 140183076864 225353864187 1099511627776 11709296426903 48997536668581888 qz334 (@Enclosure.Real.IsNear.neg (Real.sin qz164) Bool.true 712791 1048576 110807245 140183076864 (@Enclosure.Real.IsNear.recentre' (Real.sin qz164) Bool.true 712791 1048576 110807245 140183076864 712791 1048576 110807245 140183076864 (ep772 rfl rfl) rfl)) rfl)

noncomputable def ep774 := @ep740 121570270425 549755813888 731987718545 3062346041786368 Bool.false 225353864187 1099511627776 11709296426903 48997536668581888 Bool.false 38559576239022215790592 8767432573 68719476736 7852074632687 2296759531339776 Bool.false 117888644733159954448384 13402387223 137438953472 251312232476797 73496305002872832 (ep741 (BSN.head_sum_c_succ qz149 10 11 rfl rfl) (ep762 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep763 ep773) rfl rfl

noncomputable abbrev qz165 := (@HMul.hMul Real Real Real qz268 qz441 qz552)

noncomputable def ep775 := @Enclosure.Complex.IsNear.of_eq qz585 (Complex.mk (@HMul.hMul Real Real Real qz0 qz48 (Real.cos qz165)) (@HMul.hMul Real Real Real qz0 qz48 (@Neg.neg Real Real.instNeg (Real.sin qz165)))) Bool.true 149727557565 1099511627776 33607260042415 146992610005745664 Bool.true 139932888039 549755813888 2104046051281 9187038125359104 (BSN.cpow_neg_s_mk qz152 104500 1000 12 qz153 rfl)

noncomputable def ep776 := @Enclosure.Real.IsNear.mulLit_ff qz152 qz552 104500 1000 0 1 11191020447815397 4503599627370496 1000000000401067 133689000000000000000 2338923273593417973 9007199254740992 209000000083823003 267378000000000000000 qz154 (BSN.isNear_log_sfrac 12 1 11191020447815397 4503599627370496 1000000000401067 133689000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz336) Bool.false 46938541828353910898688 18889465931478580854784 1000000000401067 133689000000000000000 11191020447815397 4503599627370496 1000000000401067 133689000000000000000 (BSN.log_rat_reduce_isNear 12 1 3 24 16 212580 524288 24973259072661432 36028797018963968 133689 1000000000000000 rfl rfl rfl rfl (ep211 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep777 := nat_lit 1238622355315931870007235564961529856

noncomputable def ep778 := BSN.sin_dyadic_bound_f 1054956928 2147483648 2 1 1048576 267640 ep777 ep58 ep777 ep777 ep59 ep777 494645 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1054956928) qz287 0 1 ep777 ep58 ep777 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1054956928) qz288 0 1 ep777 ep59 ep777 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz457 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 272286505) qz26)

noncomputable def ep779 := @Enclosure.Real.IsNear.cos_image qz165 qz457 Bool.false 272286505 1048576 821 1048576 Bool.true 494645 1048576 1 133689 (@Enclosure.Real.IsNear.recentre' qz165 Bool.false 2338923273593417973 9007199254740992 209000000083823003 267378000000000000000 272286505 1048576 821 1048576 (ep776 rfl) rfl) (Enclosure.sfrac_false_div 272286505 1048576) (BSN.cos_reduce1 qz457 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 74235994217730183004160) qz27) 226375608064910080 72057594037927936 Bool.false 494645 1048576 41 1000000000000000 267378 133689 (BSN.sin_reduce_arg_pos_rat_q1 272286505 1048576 226375608064910080 72057594037927936 41 74235994217730183004160 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 494645 1048576 74235994217730183004160 151115727451828646838272 1054956928 2147483648 267640 267378 (ep778 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep780 := BSN.cos_dyadic_bound_f 1054956928 2147483648 2 1 1048576 267640 ep777 ep62 ep777 ep777 ep63 ep777 924574 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1054956928) qz292 0 1 ep777 ep62 ep777 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1054956928) qz293 0 1 ep777 ep63 ep777 rfl rfl rfl rfl) rfl rfl

noncomputable def ep781 := @Enclosure.Real.IsNear.sin_image qz165 qz457 Bool.false 272286505 1048576 821 1048576 Bool.false 924574 1048576 1 133689 (@Enclosure.Real.IsNear.recentre' qz165 Bool.false 2338923273593417973 9007199254740992 209000000083823003 267378000000000000000 272286505 1048576 821 1048576 (ep776 rfl) rfl) (Enclosure.sfrac_false_div 272286505 1048576) (BSN.sin_reduce1 qz457 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 74235994217730183004160) qz27) 226375608064910080 72057594037927936 Bool.false 924574 1048576 41 1000000000000000 267378 133689 (BSN.sin_reduce_arg_pos_rat_q1 272286505 1048576 226375608064910080 72057594037927936 41 74235994217730183004160 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 924574 1048576 74235994217730183004160 151115727451828646838272 1054956928 2147483648 267640 267378 (ep780 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep782 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz48 (Real.cos qz165)) (@HMul.hMul Real Real Real qz0 qz48 (@Neg.neg Real Real.instNeg (Real.sin qz165))) Bool.true 149727557565 1099511627776 33607260042415 146992610005745664 Bool.true 139932888039 549755813888 2104046051281 9187038125359104 (@Enclosure.Real.IsNear.mulLit_ft qz48 (Real.cos qz165) 302697 1048576 1 1048576 494645 1048576 110807245 140183076864 149727557565 1099511627776 33607260042415 146992610005745664 qz338 (@Enclosure.Real.IsNear.recentre' (Real.cos qz165) Bool.true 494645 1048576 110807245 140183076864 494645 1048576 110807245 140183076864 (ep779 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz48 (@Neg.neg Real Real.instNeg (Real.sin qz165)) 302697 1048576 1 1048576 462287 524288 110807245 140183076864 139932888039 549755813888 2104046051281 9187038125359104 qz338 (@Enclosure.Real.IsNear.neg (Real.sin qz165) Bool.false 462287 524288 110807245 140183076864 (@Enclosure.Real.IsNear.recentre' (Real.sin qz165) Bool.false 924574 1048576 110807245 140183076864 462287 524288 110807245 140183076864 (ep781 rfl rfl) rfl)) rfl)

noncomputable def ep783 := @ep738 149727557565 1099511627776 33607260042415 146992610005745664 Bool.true 139932888039 549755813888 2104046051281 9187038125359104 Bool.true 649305349070564360192 9448636397 1099511627776 178713345511461 48997536668581888 Bool.true 11864189392572209168384 86323339147 549755813888 89381533629015 24498768334290944 (ep739 (BSN.head_sum_c_succ qz149 11 12 rfl rfl) (ep774 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep775 ep782) rfl rfl

noncomputable abbrev qz166 := (@HMul.hMul Real Real Real qz268 qz441 qz553)

noncomputable def ep784 := @Enclosure.Complex.IsNear.of_eq qz453 (Complex.mk (@HMul.hMul Real Real Real qz0 qz50 (Real.cos qz166)) (@HMul.hMul Real Real Real qz0 qz50 (@Neg.neg Real Real.instNeg (Real.sin qz166)))) Bool.true 164342041539 1099511627776 32300952937957 146992610005745664 Bool.false 128438778897 549755813888 16171745386211 73496305002872832 (BSN.cpow_neg_s_mk qz152 104500 1000 13 qz153 rfl)

noncomputable def ep785 := @Enclosure.Real.IsNear.mulLit_ff qz152 qz553 104500 1000 0 1 11551497052968677 4503599627370496 1000000000401067 133689000000000000000 2414262884070453493 9007199254740992 209000000083823003 267378000000000000000 qz154 (BSN.isNear_log_sfrac 13 1 11551497052968677 4503599627370496 1000000000401067 133689000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz340) Bool.false 48450490295254733815808 18889465931478580854784 1000000000401067 133689000000000000000 11551497052968677 4503599627370496 1000000000401067 133689000000000000000 (BSN.log_rat_reduce_isNear 13 1 3 26 16 254545 524288 24973259072661432 36028797018963968 133689 1000000000000000 rfl rfl rfl rfl (ep226 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep786 := nat_lit 765365424066595709718638356022733952961827556041886583791803635518599450264161

noncomputable def ep787 := nat_lit 458310610057424285075676880674245040015340335468923099067486356526368490081

noncomputable def ep788 := nat_lit 2295179650979672280585763714306853368805451987454721905177275933842745613812321

noncomputable def ep789 := BSN.cos_dyadic_bound_f 2151022677 2147483648 3 2 1048576 267640 ep786 ep75 ep787 ep788 ep78 ep787 565093 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2151022677) qz292 0 2 ep786 ep75 ep787 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2151022677) qz293 0 2 ep788 ep78 ep787 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz458 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 140528595) qz20)

noncomputable def ep790 := @Enclosure.Real.IsNear.cos_image qz166 qz458 Bool.false 140528595 524288 821 1048576 Bool.true 565093 1048576 1 133689 (@Enclosure.Real.IsNear.recentre' qz166 Bool.false 2414262884070453493 9007199254740992 209000000083823003 267378000000000000000 140528595 524288 821 1048576 (ep785 rfl) rfl) (Enclosure.sfrac_false_div 140528595 524288) (BSN.cos_reduce2 qz458 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 75682382267731190743040) qz21) 226375608064910080 72057594037927936 Bool.false 565093 1048576 42 1000000000000000 267378 133689 (BSN.sin_reduce_arg_pos_rat_q2 140528595 524288 226375608064910080 72057594037927936 42 75682382267731190743040 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 565093 1048576 75682382267731190743040 75557863725914323419136 2151022677 2147483648 267640 267378 (ep789 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep791 := nat_lit 1377291114831826338065488499336381719299277328607020712345992554848257915683425

noncomputable def ep792 := nat_lit 3606448988333737912757585449978955725242844357237152180650537903834870896853601

noncomputable def ep793 := BSN.sin_dyadic_bound_f 2151022677 2147483648 3 2 1048576 267640 ep791 ep108 ep787 ep792 ep110 ep787 883278 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2151022677) qz287 0 2 ep791 ep108 ep787 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2151022677) qz288 0 2 ep792 ep110 ep787 rfl rfl rfl rfl) rfl rfl

noncomputable def ep794 := @Enclosure.Real.IsNear.sin_image qz166 qz458 Bool.false 140528595 524288 821 1048576 Bool.true 883278 1048576 1 133689 (@Enclosure.Real.IsNear.recentre' qz166 Bool.false 2414262884070453493 9007199254740992 209000000083823003 267378000000000000000 140528595 524288 821 1048576 (ep785 rfl) rfl) (Enclosure.sfrac_false_div 140528595 524288) (BSN.sin_reduce2 qz458 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 75682382267731190743040) qz21) 226375608064910080 72057594037927936 Bool.false 883278 1048576 42 1000000000000000 267378 133689 (BSN.sin_reduce_arg_pos_rat_q2 140528595 524288 226375608064910080 72057594037927936 42 75682382267731190743040 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 883278 1048576 75682382267731190743040 75557863725914323419136 2151022677 2147483648 267640 267378 (ep793 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep795 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz50 (Real.cos qz166)) (@HMul.hMul Real Real Real qz0 qz50 (@Neg.neg Real Real.instNeg (Real.sin qz166))) Bool.true 164342041539 1099511627776 32300952937957 146992610005745664 Bool.false 128438778897 549755813888 16171745386211 73496305002872832 (@Enclosure.Real.IsNear.mulLit_ft qz50 (Real.cos qz166) 290823 1048576 1 1048576 565093 1048576 110807245 140183076864 164342041539 1099511627776 32300952937957 146992610005745664 qz342 (@Enclosure.Real.IsNear.recentre' (Real.cos qz166) Bool.true 565093 1048576 110807245 140183076864 565093 1048576 110807245 140183076864 (ep790 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz50 (@Neg.neg Real Real.instNeg (Real.sin qz166)) 290823 1048576 1 1048576 441639 524288 110807245 140183076864 128438778897 549755813888 16171745386211 73496305002872832 qz342 (@Enclosure.Real.IsNear.neg (Real.sin qz166) Bool.true 441639 524288 110807245 140183076864 (@Enclosure.Real.IsNear.recentre' (Real.sin qz166) Bool.true 883278 1048576 110807245 140183076864 441639 524288 110807245 140183076864 (ep794 rfl rfl) rfl)) rfl)

noncomputable def ep796 := @ep736 164342041539 1099511627776 32300952937957 146992610005745664 Bool.false 128438778897 549755813888 16171745386211 73496305002872832 Bool.true 191084871189705927950336 10861917371 68719476736 142110247368085 36748152501436416 Bool.false 23153207857012277248000 21057719875 274877906944 35539543284157 9187038125359104 (ep737 (BSN.head_sum_c_succ qz149 12 13 rfl rfl) (ep783 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep784 ep795) rfl rfl

noncomputable abbrev qz167 := (@HMul.hMul Real Real Real qz268 qz441 qz554)

noncomputable def ep797 := @Enclosure.Complex.IsNear.of_eq qz452 (Complex.mk (@HMul.hMul Real Real Real qz0 qz52 (Real.cos qz167)) (@HMul.hMul Real Real Real qz0 qz52 (@Neg.neg Real Real.instNeg (Real.sin qz167)))) Bool.false 114355117851 549755813888 15581085516163 73496305002872832 Bool.false 184507227069 1099511627776 31141084132667 146992610005745664 (BSN.cpow_neg_s_mk qz152 104500 1000 14 qz153 rfl)

noncomputable def ep798 := @Enclosure.Real.IsNear.mulLit_ff qz152 qz554 104500 1000 0 1 11885250371606245 4503599627370496 1000000000401067 133689000000000000000 2484017327665705205 9007199254740992 209000000083823003 267378000000000000000 qz154 (BSN.isNear_log_sfrac 14 1 11885250371606245 4503599627370496 1000000000401067 133689000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz344) Bool.false 49850353174629559828480 18889465931478580854784 1000000000401067 133689000000000000000 11885250371606245 4503599627370496 1000000000401067 133689000000000000000 (BSN.log_rat_reduce_isNear 14 1 3 28 16 293399 524288 24973259072661432 36028797018963968 133689 1000000000000000 rfl rfl rfl rfl (ep241 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep799 := nat_lit 865971155964583677629589620458566609720556651776162278515503699495441650390625

noncomputable def ep800 := nat_lit 181226858105191355169983283702904740341494350823338228282988071441650390625

noncomputable def ep801 := nat_lit 2267726279279834560169126175884536417783762144750520562790051517991441650390625

noncomputable def ep802 := BSN.sin_dyadic_bound_f 1915480875 2147483648 3 2 1048576 267640 ep799 ep108 ep800 ep801 ep110 ep800 816114 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1915480875) qz287 0 2 ep799 ep108 ep800 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1915480875) qz288 0 2 ep801 ep110 ep800 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz459 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 72294419) (@Nat.cast Real Real.instNatCast 262144))

noncomputable def ep803 := @Enclosure.Real.IsNear.cos_image qz167 qz459 Bool.false 72294419 262144 821 1048576 Bool.false 816114 1048576 1 133689 (@Enclosure.Real.IsNear.recentre' qz167 Bool.false 2484017327665705205 9007199254740992 209000000083823003 267378000000000000000 72294419 262144 821 1048576 (ep798 rfl) rfl) (Enclosure.sfrac_false_div 72294419 262144) (BSN.cos_reduce3 qz459 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 33697495920365291962368) qz316) 226375608064910080 72057594037927936 Bool.false 816114 1048576 43 1000000000000000 267378 133689 (BSN.sin_reduce_arg_pos_rat_q3 72294419 262144 226375608064910080 72057594037927936 43 33697495920365291962368 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 816114 1048576 33697495920365291962368 37778931862957161709568 1915480875 2147483648 267640 267378 (ep802 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep804 := nat_lit 481175631917259905952069781714182740840461026253789416165627827751441650390625

noncomputable def ep805 := nat_lit 1443164442035569335145869378575142413040700090059721572040317507111441650390625

noncomputable def ep806 := BSN.cos_dyadic_bound_f 1915480875 2147483648 3 2 1048576 267640 ep804 ep75 ep800 ep805 ep78 ep800 658383 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1915480875) qz292 0 2 ep804 ep75 ep800 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1915480875) qz293 0 2 ep805 ep78 ep800 rfl rfl rfl rfl) rfl rfl

noncomputable def ep807 := @Enclosure.Real.IsNear.sin_image qz167 qz459 Bool.false 72294419 262144 821 1048576 Bool.true 658383 1048576 1 133689 (@Enclosure.Real.IsNear.recentre' qz167 Bool.false 2484017327665705205 9007199254740992 209000000083823003 267378000000000000000 72294419 262144 821 1048576 (ep798 rfl) rfl) (Enclosure.sfrac_false_div 72294419 262144) (BSN.sin_reduce3 qz459 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 33697495920365291962368) qz316) 226375608064910080 72057594037927936 Bool.false 658383 1048576 43 1000000000000000 267378 133689 (BSN.sin_reduce_arg_pos_rat_q3 72294419 262144 226375608064910080 72057594037927936 43 33697495920365291962368 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 658383 1048576 33697495920365291962368 37778931862957161709568 1915480875 2147483648 267640 267378 (ep806 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep808 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz52 (Real.cos qz167)) (@HMul.hMul Real Real Real qz0 qz52 (@Neg.neg Real Real.instNeg (Real.sin qz167))) Bool.false 114355117851 549755813888 15581085516163 73496305002872832 Bool.false 184507227069 1099511627776 31141084132667 146992610005745664 (@Enclosure.Real.IsNear.mulLit_ff qz52 (Real.cos qz167) 280243 1048576 1 1048576 408057 524288 110807245 140183076864 114355117851 549755813888 15581085516163 73496305002872832 qz346 (@Enclosure.Real.IsNear.recentre' (Real.cos qz167) Bool.false 816114 1048576 110807245 140183076864 408057 524288 110807245 140183076864 (ep803 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz52 (@Neg.neg Real Real.instNeg (Real.sin qz167)) 280243 1048576 1 1048576 658383 1048576 110807245 140183076864 184507227069 1099511627776 31141084132667 146992610005745664 qz346 (@Enclosure.Real.IsNear.neg (Real.sin qz167) Bool.true 658383 1048576 110807245 140183076864 (@Enclosure.Real.IsNear.recentre' (Real.sin qz167) Bool.true 658383 1048576 110807245 140183076864 658383 1048576 110807245 140183076864 (ep807 rfl rfl) rfl)) rfl)

noncomputable def ep809 := @ep734 114355117851 549755813888 15581085516163 73496305002872832 Bool.false 184507227069 1099511627776 31141084132667 146992610005745664 Bool.false 1887021636126022565888 27459778883 549755813888 99933860084111 24498768334290944 Bool.false 73870168249780337115136 268738106569 1099511627776 199924592226393 48997536668581888 (ep735 (BSN.head_sum_c_succ qz149 13 14 rfl rfl) (ep796 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep797 ep808) rfl rfl

noncomputable abbrev qz168 := (@HMul.hMul Real Real Real qz268 qz441 qz555)

noncomputable def ep810 := @Enclosure.Complex.IsNear.of_eq qz451 (Complex.mk (@HMul.hMul Real Real Real qz0 qz54 (Real.cos qz168)) (@HMul.hMul Real Real Real qz0 qz54 (@Neg.neg Real Real.instNeg (Real.sin qz168)))) Bool.false 275226907629 1099511627776 30136079218831 146992610005745664 Bool.true 8700803517 137438953472 15017273016467 73496305002872832 (BSN.cpow_neg_s_mk qz152 104500 1000 15 qz153 rfl)

noncomputable def ep811 := @Enclosure.Real.IsNear.mulLit_ff qz152 qz555 104500 1000 0 1 12195965485668069 4503599627370496 1000000000401067 133689000000000000000 2548956786504626421 9007199254740992 209000000083823003 267378000000000000000 qz154 (BSN.isNear_log_sfrac 15 1 12195965485668069 4503599627370496 1000000000401067 133689000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz348) Bool.false 51153586820399524478976 18889465931478580854784 1000000000401067 133689000000000000000 12195965485668069 4503599627370496 1000000000401067 133689000000000000000 (BSN.log_rat_reduce_isNear 15 1 3 30 16 329571 524288 24973259072661432 36028797018963968 133689 1000000000000000 rfl rfl rfl rfl (ep256 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep812 := nat_lit 80076839215710262406026080620118016

noncomputable def ep813 := BSN.cos_dyadic_bound_f 531957248 2147483648 2 1 1048576 267640 ep812 ep62 ep812 ep812 ep63 ep812 1016569 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 531957248) qz292 0 1 ep812 ep62 ep812 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 531957248) qz293 0 1 ep812 ep63 ep812 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz460 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 37092203) (@Nat.cast Real Real.instNatCast 131072))

noncomputable def ep814 := @Enclosure.Real.IsNear.cos_image qz168 qz460 Bool.false 37092203 131072 821 1048576 Bool.false 1016569 1048576 1 133689 (@Enclosure.Real.IsNear.recentre' qz168 Bool.false 2548956786504626421 9007199254740992 209000000083823003 267378000000000000000 37092203 131072 821 1048576 (ep811 rfl) rfl) (Enclosure.sfrac_false_div 37092203 131072) (BSN.cos_reduce0 qz460 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 4679145441724481929216) qz354) 226375608064910080 72057594037927936 Bool.false 1016569 1048576 45 1000000000000000 267378 133689 (BSN.sin_reduce_arg_pos_rat_q0 37092203 131072 226375608064910080 72057594037927936 45 4679145441724481929216 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1016569 1048576 4679145441724481929216 18889465931478580854784 531957248 2147483648 267640 267378 (ep813 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep815 := BSN.sin_dyadic_bound_f 531957248 2147483648 2 1 1048576 267640 ep812 ep58 ep812 ep812 ep59 ep812 257096 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 531957248) qz287 0 1 ep812 ep58 ep812 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 531957248) qz288 0 1 ep812 ep59 ep812 rfl rfl rfl rfl) rfl rfl

noncomputable def ep816 := @Enclosure.Real.IsNear.sin_image qz168 qz460 Bool.false 37092203 131072 821 1048576 Bool.false 257096 1048576 1 133689 (@Enclosure.Real.IsNear.recentre' qz168 Bool.false 2548956786504626421 9007199254740992 209000000083823003 267378000000000000000 37092203 131072 821 1048576 (ep811 rfl) rfl) (Enclosure.sfrac_false_div 37092203 131072) (BSN.sin_reduce0 qz460 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 4679145441724481929216) qz354) 226375608064910080 72057594037927936 Bool.false 257096 1048576 45 1000000000000000 267378 133689 (BSN.sin_reduce_arg_pos_rat_q0 37092203 131072 226375608064910080 72057594037927936 45 4679145441724481929216 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 257096 1048576 4679145441724481929216 18889465931478580854784 531957248 2147483648 267640 267378 (ep815 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep817 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz54 (Real.cos qz168)) (@HMul.hMul Real Real Real qz0 qz54 (@Neg.neg Real Real.instNeg (Real.sin qz168))) Bool.false 275226907629 1099511627776 30136079218831 146992610005745664 Bool.true 8700803517 137438953472 15017273016467 73496305002872832 (@Enclosure.Real.IsNear.mulLit_ff qz54 (Real.cos qz168) 270741 1048576 1 1048576 1016569 1048576 110807245 140183076864 275226907629 1099511627776 30136079218831 146992610005745664 qz350 (@Enclosure.Real.IsNear.recentre' (Real.cos qz168) Bool.false 1016569 1048576 110807245 140183076864 1016569 1048576 110807245 140183076864 (ep814 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz54 (@Neg.neg Real Real.instNeg (Real.sin qz168)) 270741 1048576 1 1048576 32137 131072 110807245 140183076864 8700803517 137438953472 15017273016467 73496305002872832 qz350 (@Enclosure.Real.IsNear.neg (Real.sin qz168) Bool.false 32137 131072 110807245 140183076864 (@Enclosure.Real.IsNear.recentre' (Real.sin qz168) Bool.false 257096 1048576 110807245 140183076864 32137 131072 110807245 140183076864 (ep816 rfl rfl) rfl)) rfl)

noncomputable def ep818 := @ep732 275226907629 1099511627776 30136079218831 146992610005745664 Bool.true 8700803517 137438953472 15017273016467 73496305002872832 Bool.false 181499938785474652405760 330146465395 1099511627776 629739239723497 146992610005745664 Bool.false 27368449486954352869376 199131678433 1099511627776 629808322712113 146992610005745664 (ep733 (BSN.head_sum_c_succ qz149 14 15 rfl rfl) (ep809 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep810 ep817) rfl rfl

noncomputable abbrev qz169 := (@HMul.hMul Real Real Real qz268 qz441 qz556)

noncomputable def ep819 := @Enclosure.Complex.IsNear.of_eq qz450 (Complex.mk (@HMul.hMul Real Real Real qz0 qz56 (Real.cos qz169)) (@HMul.hMul Real Real Real qz0 qz56 (@Neg.neg Real Real.instNeg (Real.sin qz169)))) Bool.false 208635681555 1099511627776 29118809733829 146992610005745664 Bool.true 178964763957 1099511627776 29103678010675 146992610005745664 (BSN.cpow_neg_s_mk qz152 104500 1000 16 qz153 rfl)

noncomputable def ep820 := @Enclosure.Real.IsNear.mulLit_ff qz152 qz556 104500 1000 0 1 3121657384082679 1125899906842624 250000000133689 33422250000000000000 652426393273279911 2251799813685248 52250000027941001 66844500000000000000 qz154 (BSN.isNear_log_sfrac 16 1 3121657384082679 1125899906842624 250000000133689 33422250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz352) Bool.false 52372720210750067441664 18889465931478580854784 1000000000534756 133689000000000000000 3121657384082679 1125899906842624 250000000133689 33422250000000000000 (BSN.log_rat_reduce_isNear 16 1 4 32 32 0 524288 24973259072661432 36028797018963968 133689 1000000000000000 rfl rfl rfl rfl (ep267 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep821 := nat_lit 192039942807991725837655791415596550197905619588557631386480390108667993480001

noncomputable def ep822 := nat_lit 28879855475434888877964650306793313983472534062081175439307454463179840321

noncomputable def ep823 := nat_lit 576062068713024307735211444946176063965749913697548731808562555417077620759361

noncomputable def ep824 := BSN.cos_dyadic_bound_f 1522559863 2147483648 3 2 1048576 267640 ep821 ep75 ep822 ep823 ep78 ep822 795885 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1522559863) qz292 0 2 ep821 ep75 ep822 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1522559863) qz293 0 2 ep823 ep78 ep822 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz461 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 151904857) qz20)

noncomputable def ep825 := @Enclosure.Real.IsNear.cos_image qz169 qz461 Bool.false 151904857 524288 205 262144 Bool.false 795885 1048576 1 133689 (@Enclosure.Real.IsNear.recentre' qz169 Bool.false 652426393273279911 2251799813685248 52250000027941001 66844500000000000000 151904857 524288 205 262144 (ep820 rfl) rfl) (Enclosure.sfrac_false_div 151904857 524288) (BSN.cos_reduce0 qz461 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 53570312782045400530944) qz21) 226375608064910080 72057594037927936 Bool.false 795885 1048576 46 1000000000000000 267378 133689 (BSN.sin_reduce_arg_pos_rat_q0 151904857 524288 226375608064910080 72057594037927936 46 53570312782045400530944 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 795885 1048576 53570312782045400530944 75557863725914323419136 1522559863 2147483648 267640 267378 (ep824 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep826 := nat_lit 5373998090382512303592792553857555361

noncomputable def ep827 := BSN.sin_dyadic_bound_f 1522559863 2147483648 2 1 1048576 267640 ep826 ep58 ep826 ep826 ep59 ep826 682699 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1522559863) qz287 0 1 ep826 ep58 ep826 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1522559863) qz288 0 1 ep826 ep59 ep826 rfl rfl rfl rfl) rfl rfl

noncomputable def ep828 := @Enclosure.Real.IsNear.sin_image qz169 qz461 Bool.false 151904857 524288 205 262144 Bool.false 682699 1048576 1 133689 (@Enclosure.Real.IsNear.recentre' qz169 Bool.false 652426393273279911 2251799813685248 52250000027941001 66844500000000000000 151904857 524288 205 262144 (ep820 rfl) rfl) (Enclosure.sfrac_false_div 151904857 524288) (BSN.sin_reduce0 qz461 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 53570312782045400530944) qz21) 226375608064910080 72057594037927936 Bool.false 682699 1048576 46 1000000000000000 267378 133689 (BSN.sin_reduce_arg_pos_rat_q0 151904857 524288 226375608064910080 72057594037927936 46 53570312782045400530944 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 682699 1048576 53570312782045400530944 75557863725914323419136 1522559863 2147483648 267640 267378 (ep827 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep829 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz56 (Real.cos qz169)) (@HMul.hMul Real Real Real qz0 qz56 (@Neg.neg Real Real.instNeg (Real.sin qz169))) Bool.false 208635681555 1099511627776 29118809733829 146992610005745664 Bool.true 178964763957 1099511627776 29103678010675 146992610005745664 (@Enclosure.Real.IsNear.mulLit_ff qz56 (Real.cos qz169) 262143 1048576 1 1048576 795885 1048576 27668389 35045769216 208635681555 1099511627776 29118809733829 146992610005745664 qz355 (@Enclosure.Real.IsNear.recentre' (Real.cos qz169) Bool.false 795885 1048576 27668389 35045769216 795885 1048576 27668389 35045769216 (ep825 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz56 (@Neg.neg Real Real.instNeg (Real.sin qz169)) 262143 1048576 1 1048576 682699 1048576 27668389 35045769216 178964763957 1099511627776 29103678010675 146992610005745664 qz355 (@Enclosure.Real.IsNear.neg (Real.sin qz169) Bool.false 682699 1048576 27668389 35045769216 (@Enclosure.Real.IsNear.recentre' (Real.sin qz169) Bool.false 682699 1048576 27668389 35045769216 682699 1048576 27668389 35045769216 (ep828 rfl rfl) rfl)) rfl)

noncomputable def ep830 := @ep730 208635681555 1099511627776 29118809733829 146992610005745664 Bool.true 178964763957 1099511627776 29103678010675 146992610005745664 Bool.false 592397235409642533683200 269391073475 549755813888 329429024728663 73496305002872832 Bool.false 22173756962726138085376 5041728619 274877906944 164728000180697 36748152501436416 (ep731 (BSN.head_sum_c_succ qz149 15 16 rfl rfl) (ep818 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep819 ep829) rfl rfl

theorem EMRow31.d13 : Enclosure.Complex.IsNear qz161 Bool.false 269391073475 549755813888 329429024728663 73496305002872832 Bool.false 5041728619 274877906944 164728000180697 36748152501436416 := ep729 (BSN.head_sum_c_succ qz149 16 17 rfl rfl) (ep830 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable abbrev qz170 := (BSN.headSumC qz439 25)

noncomputable abbrev qz588 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 24) qz150)

noncomputable def ep831 := @Enclosure.Complex.IsNear.of_eq qz170 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz149 24) qz588) Bool.false 621872755945 549755813888 432892614490433 73496305002872832 Bool.false 8653240819 274877906944 54109711298287 9187038125359104

noncomputable def ep832 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz149 24) qz588 Bool.false 1104637499049 1099511627776 842009774033435 146992610005745664 Bool.true 70756654327 549755813888 420978402089461 73496305002872832 Bool.false

noncomputable def ep833 := nat_lit 1367512652317268262256640

noncomputable abbrev qz589 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 23) qz150)

noncomputable def ep834 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz149 24) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz149 23) qz589) Bool.false 1104637499049 1099511627776 842009774033435 146992610005745664 Bool.true 70756654327 549755813888 420978402089461 73496305002872832

noncomputable def ep835 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz149 23) qz589 Bool.false 242046311277 274877906944 204432057872107 36748152501436416 Bool.false 10680460609 274877906944 204411511209697 36748152501436416 Bool.false

noncomputable abbrev qz590 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 22) qz150)

noncomputable def ep836 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz149 23) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz149 22) qz590) Bool.false 242046311277 274877906944 204432057872107 36748152501436416 Bool.false 10680460609 274877906944 204411511209697 36748152501436416

noncomputable def ep837 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz149 22) qz590 Bool.false 1165515208539 1099511627776 264289422549531 48997536668581888 Bool.false 84630011345 549755813888 132138069181897 24498768334290944 Bool.true

noncomputable abbrev qz591 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 21) qz150)

noncomputable def ep838 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz149 22) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz149 21) qz591) Bool.false 1165515208539 1099511627776 264289422549531 48997536668581888 Bool.false 84630011345 549755813888 132138069181897 24498768334290944

noncomputable def ep839 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz149 21) qz591 Bool.false 1323574674309 1099511627776 767359249200503 146992610005745664 Bool.true 5626562301 549755813888 383646579553765 73496305002872832 Bool.true

noncomputable abbrev qz592 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 20) qz150)

noncomputable def ep840 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz149 21) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz149 20) qz592) Bool.false 1323574674309 1099511627776 767359249200503 146992610005745664 Bool.true 5626562301 549755813888 383646579553765 73496305002872832

noncomputable def ep841 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz149 20) qz592 Bool.false 151653228179 137438953472 123557783678341 24498768334290944 Bool.true 230956439327 1099511627776 247072753498995 48997536668581888 Bool.false

noncomputable abbrev qz593 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 19) qz150)

noncomputable def ep842 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz149 20) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz149 19) qz593) Bool.false 151653228179 137438953472 123557783678341 24498768334290944 Bool.true 230956439327 1099511627776 247072753498995 48997536668581888

noncomputable def ep843 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz149 19) qz593 Bool.false 965157295129 1099511627776 714585209069173 146992610005745664 Bool.true 34583041655 137438953472 357284614009901 73496305002872832 Bool.false

noncomputable def ep844 := nat_lit 1333955902180619538399232

noncomputable def ep845 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz149 19) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz149 18) (@HPow.hPow Complex Complex Complex qz6 qz356 qz150)) Bool.false 965157295129 1099511627776 714585209069173 146992610005745664 Bool.true 34583041655 137438953472 357284614009901 73496305002872832

noncomputable def ep846 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz149 18) (@HPow.hPow Complex Complex Complex qz6 qz356 qz150) Bool.false 731903101557 1099511627776 687105846421753 146992610005745664 Bool.true 163728436639 1099511627776 687154947985051 146992610005745664 Bool.false

noncomputable def ep847 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz149 18) (@HAdd.hAdd Complex Complex Complex qz4 qz161 (@HPow.hPow Complex Complex Complex qz6 qz357 qz150)) Bool.false 731903101557 1099511627776 687105846421753 146992610005745664 Bool.true 163728436639 1099511627776 687154947985051 146992610005745664

noncomputable def ep848 := @Enclosure.Complex.IsNear.addLitP qz161 (@HPow.hPow Complex Complex Complex qz6 qz357 qz150) Bool.false 269391073475 549755813888 329429024728663 73496305002872832 Bool.false 5041728619 274877906944 164728000180697 36748152501436416 Bool.false

noncomputable abbrev qz171 := (@HMul.hMul Real Real Real qz268 qz441 qz563)

noncomputable def ep849 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz357 qz150) (Complex.mk (@HMul.hMul Real Real Real qz0 qz65 (Real.cos qz171)) (@HMul.hMul Real Real Real qz0 qz65 (@Neg.neg Real Real.instNeg (Real.sin qz171)))) Bool.false 193120954607 1099511627776 28247796964427 146992610005745664 Bool.true 183895351115 1099511627776 28242947262263 146992610005745664 (BSN.cpow_neg_s_mk qz152 104500 1000 17 qz153 rfl)

noncomputable def ep850 := @Enclosure.Real.IsNear.mulLit_ff qz152 qz563 104500 1000 0 1 3189913004350711 1125899906842624 250000000133689 33422250000000000000 666691817909298599 2251799813685248 52250000027941001 66844500000000000000 qz154 (BSN.isNear_log_sfrac 17 1 3189913004350711 1125899906842624 250000000133689 33422250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz359) Bool.false 53517859495200818200576 18889465931478580854784 1000000000534756 133689000000000000000 3189913004350711 1125899906842624 250000000133689 33422250000000000000 (BSN.log_rat_reduce_isNear 17 1 4 34 32 31784 524288 24973259072661432 36028797018963968 133689 1000000000000000 rfl rfl rfl rfl (ep299 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep851 := nat_lit 254812435360317829887506958548702284286493120601768628128748982973051441779841

noncomputable def ep852 := nat_lit 50840572179261023167098916191732593563015716688776555018843178839545746561

noncomputable def ep853 := nat_lit 764335624936594967616186677813723387672353330371928331276209262561475233846401

noncomputable def ep854 := BSN.cos_dyadic_bound_f 1634091247 2147483648 3 2 1048576 267640 ep851 ep75 ep852 ep853 ep78 ep852 759371 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1634091247) qz292 0 2 ep851 ep75 ep852 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1634091247) qz293 0 2 ep853 ep78 ep852 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz462 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 155226285) qz20)

noncomputable def ep855 := @Enclosure.Real.IsNear.cos_image qz171 qz462 Bool.false 155226285 524288 205 262144 Bool.false 759371 1048576 1 133689 (@Enclosure.Real.IsNear.recentre' qz171 Bool.false 666691817909298599 2251799813685248 52250000027941001 66844500000000000000 155226285 524288 205 262144 (ep850 rfl) rfl) (Enclosure.sfrac_false_div 155226285 524288) (BSN.cos_reduce0 qz462 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 57494474477916913664000) qz21) 226375608064910080 72057594037927936 Bool.false 759371 1048576 47 1000000000000000 267378 133689 (BSN.sin_reduce_arg_pos_rat_q0 155226285 524288 226375608064910080 72057594037927936 47 57494474477916913664000 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 759371 1048576 57494474477916913664000 75557863725914323419136 1634091247 2147483648 267640 267378 (ep854 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep856 := nat_lit 7130257511426990752895165323621270081

noncomputable def ep857 := BSN.sin_dyadic_bound_f 1634091247 2147483648 2 1 1048576 267640 ep856 ep58 ep856 ep856 ep59 ep856 723095 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1634091247) qz287 0 1 ep856 ep58 ep856 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1634091247) qz288 0 1 ep856 ep59 ep856 rfl rfl rfl rfl) rfl rfl

noncomputable def ep858 := @Enclosure.Real.IsNear.sin_image qz171 qz462 Bool.false 155226285 524288 205 262144 Bool.false 723095 1048576 1 133689 (@Enclosure.Real.IsNear.recentre' qz171 Bool.false 666691817909298599 2251799813685248 52250000027941001 66844500000000000000 155226285 524288 205 262144 (ep850 rfl) rfl) (Enclosure.sfrac_false_div 155226285 524288) (BSN.sin_reduce0 qz462 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 57494474477916913664000) qz21) 226375608064910080 72057594037927936 Bool.false 723095 1048576 47 1000000000000000 267378 133689 (BSN.sin_reduce_arg_pos_rat_q0 155226285 524288 226375608064910080 72057594037927936 47 57494474477916913664000 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 723095 1048576 57494474477916913664000 75557863725914323419136 1634091247 2147483648 267640 267378 (ep857 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep859 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz65 (Real.cos qz171)) (@HMul.hMul Real Real Real qz0 qz65 (@Neg.neg Real Real.instNeg (Real.sin qz171))) Bool.false 193120954607 1099511627776 28247796964427 146992610005745664 Bool.true 183895351115 1099511627776 28242947262263 146992610005745664 (@Enclosure.Real.IsNear.mulLit_ff qz65 (Real.cos qz171) 254317 1048576 1 1048576 759371 1048576 27668389 35045769216 193120954607 1099511627776 28247796964427 146992610005745664 qz361 (@Enclosure.Real.IsNear.recentre' (Real.cos qz171) Bool.false 759371 1048576 27668389 35045769216 759371 1048576 27668389 35045769216 (ep855 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz65 (@Neg.neg Real Real.instNeg (Real.sin qz171)) 254317 1048576 1 1048576 723095 1048576 27668389 35045769216 183895351115 1099511627776 28242947262263 146992610005745664 qz361 (@Enclosure.Real.IsNear.neg (Real.sin qz171) Bool.false 723095 1048576 27668389 35045769216 (@Enclosure.Real.IsNear.recentre' (Real.sin qz171) Bool.false 723095 1048576 27668389 35045769216 723095 1048576 27668389 35045769216 (ep858 rfl rfl) rfl)) rfl)

noncomputable def ep860 := @ep848 193120954607 1099511627776 28247796964427 146992610005745664 Bool.true 183895351115 1099511627776 28242947262263 146992610005745664 Bool.false 402367985283620055023616 731903101557 1099511627776 687105846421753 146992610005745664 Bool.true 45005329970541642121216 163728436639 1099511627776 687154947985051 146992610005745664 EMRow31.d13 (ep849 ep859) rfl rfl

noncomputable abbrev qz172 := (@HMul.hMul Real Real Real qz268 qz441 qz564)

noncomputable def ep861 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz356 qz150) (Complex.mk (@HMul.hMul Real Real Real qz0 qz67 (Real.cos qz172)) (@HMul.hMul Real Real Real qz0 qz67 (@Neg.neg Real Real.instNeg (Real.sin qz172)))) Bool.false 58313548393 274877906944 2289946887285 12249384167145472 Bool.true 112935896601 1099511627776 9138093344917 48997536668581888 (BSN.cpow_neg_s_mk qz152 104500 1000 18 qz153 rfl)

noncomputable def ep862 := @Enclosure.Real.IsNear.mulLit_ff qz152 qz564 104500 1000 0 1 3254268794313975 1125899906842624 250000000133689 33422250000000000000 680142178011620775 2251799813685248 52250000027941001 66844500000000000000 qz154 (BSN.isNear_log_sfrac 18 1 3254268794313975 1125899906842624 250000000133689 33422250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz363) Bool.false 54597570484265130393600 18889465931478580854784 1000000000534756 133689000000000000000 3254268794313975 1125899906842624 250000000133689 33422250000000000000 (BSN.log_rat_reduce_isNear 18 1 4 36 32 61752 524288 24973259072661432 36028797018963968 133689 1000000000000000 rfl rfl rfl rfl (ep313 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep863 := nat_lit 879162916920202411387850955241416976

noncomputable def ep864 := BSN.cos_dyadic_bound_f 968316518 2147483648 2 1 1048576 267640 ep863 ep62 ep863 ep863 ep63 ep863 943772 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 968316518) qz292 0 1 ep863 ep62 ep863 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 968316518) qz293 0 1 ep863 ep63 ep863 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz463 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 158357941) qz20)

noncomputable def ep865 := @Enclosure.Real.IsNear.cos_image qz172 qz463 Bool.false 158357941 524288 205 262144 Bool.false 943772 1048576 1 133689 (@Enclosure.Real.IsNear.recentre' qz172 Bool.false 680142178011620775 2251799813685248 52250000027941001 66844500000000000000 158357941 524288 205 262144 (ep862 rfl) rfl) (Enclosure.sfrac_false_div 158357941 524288) (BSN.cos_reduce0 qz463 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 34069608702257106255872) qz21) 226375608064910080 72057594037927936 Bool.false 943772 1048576 48 1000000000000000 267378 133689 (BSN.sin_reduce_arg_pos_rat_q0 158357941 524288 226375608064910080 72057594037927936 48 34069608702257106255872 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 943772 1048576 34069608702257106255872 75557863725914323419136 968316518 2147483648 267640 267378 (ep864 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep866 := BSN.sin_dyadic_bound_f 968316518 2147483648 2 1 1048576 267640 ep863 ep58 ep863 ep863 ep59 ep863 456951 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 968316518) qz287 0 1 ep863 ep58 ep863 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 968316518) qz288 0 1 ep863 ep59 ep863 rfl rfl rfl rfl) rfl rfl

noncomputable def ep867 := @Enclosure.Real.IsNear.sin_image qz172 qz463 Bool.false 158357941 524288 205 262144 Bool.false 456951 1048576 1 133689 (@Enclosure.Real.IsNear.recentre' qz172 Bool.false 680142178011620775 2251799813685248 52250000027941001 66844500000000000000 158357941 524288 205 262144 (ep862 rfl) rfl) (Enclosure.sfrac_false_div 158357941 524288) (BSN.sin_reduce0 qz463 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 34069608702257106255872) qz21) 226375608064910080 72057594037927936 Bool.false 456951 1048576 48 1000000000000000 267378 133689 (BSN.sin_reduce_arg_pos_rat_q0 158357941 524288 226375608064910080 72057594037927936 48 34069608702257106255872 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 456951 1048576 34069608702257106255872 75557863725914323419136 968316518 2147483648 267640 267378 (ep866 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep868 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz67 (Real.cos qz172)) (@HMul.hMul Real Real Real qz0 qz67 (@Neg.neg Real Real.instNeg (Real.sin qz172))) Bool.false 58313548393 274877906944 2289946887285 12249384167145472 Bool.true 112935896601 1099511627776 9138093344917 48997536668581888 (@Enclosure.Real.IsNear.mulLit_ff qz67 (Real.cos qz172) 247151 1048576 1 1048576 235943 262144 27668389 35045769216 58313548393 274877906944 2289946887285 12249384167145472 qz365 (@Enclosure.Real.IsNear.recentre' (Real.cos qz172) Bool.false 943772 1048576 27668389 35045769216 235943 262144 27668389 35045769216 (ep865 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz67 (@Neg.neg Real Real.instNeg (Real.sin qz172)) 247151 1048576 1 1048576 456951 1048576 27668389 35045769216 112935896601 1099511627776 9138093344917 48997536668581888 qz365 (@Enclosure.Real.IsNear.neg (Real.sin qz172) Bool.false 456951 1048576 27668389 35045769216 (@Enclosure.Real.IsNear.recentre' (Real.sin qz172) Bool.false 456951 1048576 27668389 35045769216 456951 1048576 27668389 35045769216 (ep867 rfl rfl) rfl)) rfl)

noncomputable def ep869 := @ep846 58313548393 274877906944 2289946887285 12249384167145472 Bool.true 112935896601 1099511627776 9138093344917 48997536668581888 Bool.false 265300417156792006475776 965157295129 1099511627776 714585209069173 146992610005745664 Bool.true 304195651388274104074240 34583041655 137438953472 357284614009901 73496305002872832 (ep847 (BSN.head_sum_c_succ qz149 17 18 rfl rfl) (ep860 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep861 ep868) rfl rfl

noncomputable abbrev qz173 := (@HMul.hMul Real Real Real qz268 qz441 qz565)

noncomputable def ep870 := @Enclosure.Complex.IsNear.of_eq qz593 (Complex.mk (@HMul.hMul Real Real Real qz0 qz69 (Real.cos qz173)) (@HMul.hMul Real Real Real qz0 qz69 (@Neg.neg Real Real.instNeg (Real.sin qz173)))) Bool.false 248068530303 1099511627776 26761493000873 146992610005745664 Bool.false 45707893913 1099511627776 26649032477183 146992610005745664 (BSN.cpow_neg_s_mk qz152 104500 1000 19 qz153 rfl)

noncomputable def ep871 := @Enclosure.Real.IsNear.mulLit_ff qz152 qz565 104500 1000 0 1 3315143513283831 1125899906842624 250000000133689 33422250000000000000 692864994276320679 2251799813685248 52250000027941001 66844500000000000000 qz154 (BSN.isNear_log_sfrac 19 1 3315143513283831 1125899906842624 250000000133689 33422250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz367) Bool.false 55618878793361701994496 18889465931478580854784 1000000000534756 133689000000000000000 3315143513283831 1125899906842624 250000000133689 33422250000000000000 (BSN.log_rat_reduce_isNear 19 1 4 38 32 90099 524288 24973259072661432 36028797018963968 133689 1000000000000000 rfl rfl rfl rfl (ep324 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep872 := nat_lit 5091466570537913523749542562633764454650096999971826576638724923962588586311680

noncomputable def ep873 := nat_lit 6251958321998609382241715571546524371077416877538946781273453210552097570816

noncomputable def ep874 := nat_lit 13324671180792251956534696315020212532244700134505435120217455876608742901415936

noncomputable def ep875 := BSN.sin_dyadic_bound_f 2981961344 2147483648 3 2 1048576 267640 ep872 ep108 ep873 ep874 ep110 ep873 1031217 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2981961344) qz287 0 2 ep872 ep108 ep873 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2981961344) qz288 0 2 ep874 ep110 ep873 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz464 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 322640405) qz26)

noncomputable def ep876 := @Enclosure.Real.IsNear.cos_image qz173 qz464 Bool.false 322640405 1048576 205 262144 Bool.false 1031217 1048576 1 133689 (@Enclosure.Real.IsNear.recentre' qz173 Bool.false 692864994276320679 2251799813685248 52250000027941001 66844500000000000000 322640405 1048576 205 262144 (ep871 rfl) rfl) (Enclosure.sfrac_false_div 322640405 1048576) (BSN.cos_reduce3 qz464 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 209836875002434614722560) qz27) 226375608064910080 72057594037927936 Bool.false 1031217 1048576 48 1000000000000000 267378 133689 (BSN.sin_reduce_arg_pos_rat_q3 322640405 1048576 226375608064910080 72057594037927936 48 209836875002434614722560 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1031217 1048576 209836875002434614722560 151115727451828646838272 2981961344 2147483648 267640 267378 (ep875 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep877 := nat_lit 2831371187330840228475186630606112041192754963041032074479857603628350146871296

noncomputable def ep878 := nat_lit 8481609645348523466661076460675243074836110055368018329877025904463946245472256

noncomputable def ep879 := BSN.cos_dyadic_bound_f 2981961344 2147483648 3 2 1048576 267640 ep877 ep75 ep873 ep878 ep78 ep873 190007 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2981961344) qz292 0 2 ep877 ep75 ep873 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2981961344) qz293 0 2 ep878 ep78 ep873 rfl rfl rfl rfl) rfl rfl

noncomputable def ep880 := @Enclosure.Real.IsNear.sin_image qz173 qz464 Bool.false 322640405 1048576 205 262144 Bool.true 190007 1048576 1 133689 (@Enclosure.Real.IsNear.recentre' qz173 Bool.false 692864994276320679 2251799813685248 52250000027941001 66844500000000000000 322640405 1048576 205 262144 (ep871 rfl) rfl) (Enclosure.sfrac_false_div 322640405 1048576) (BSN.sin_reduce3 qz464 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 209836875002434614722560) qz27) 226375608064910080 72057594037927936 Bool.false 190007 1048576 48 1000000000000000 267378 133689 (BSN.sin_reduce_arg_pos_rat_q3 322640405 1048576 226375608064910080 72057594037927936 48 209836875002434614722560 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 190007 1048576 209836875002434614722560 151115727451828646838272 2981961344 2147483648 267640 267378 (ep879 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep881 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz69 (Real.cos qz173)) (@HMul.hMul Real Real Real qz0 qz69 (@Neg.neg Real Real.instNeg (Real.sin qz173))) Bool.false 248068530303 1099511627776 26761493000873 146992610005745664 Bool.false 45707893913 1099511627776 26649032477183 146992610005745664 (@Enclosure.Real.IsNear.mulLit_ff qz69 (Real.cos qz173) 240559 1048576 1 1048576 1031217 1048576 27668389 35045769216 248068530303 1099511627776 26761493000873 146992610005745664 qz369 (@Enclosure.Real.IsNear.recentre' (Real.cos qz173) Bool.false 1031217 1048576 27668389 35045769216 1031217 1048576 27668389 35045769216 (ep876 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz69 (@Neg.neg Real Real.instNeg (Real.sin qz173)) 240559 1048576 1 1048576 190007 1048576 27668389 35045769216 45707893913 1099511627776 26649032477183 146992610005745664 qz369 (@Enclosure.Real.IsNear.neg (Real.sin qz173) Bool.true 190007 1048576 27668389 35045769216 (@Enclosure.Real.IsNear.recentre' (Real.sin qz173) Bool.true 190007 1048576 27668389 35045769216 190007 1048576 27668389 35045769216 (ep880 rfl rfl) rfl)) rfl)

noncomputable def ep882 := @ep843 248068530303 1099511627776 26761493000873 146992610005745664 Bool.false 45707893913 1099511627776 26649032477183 146992610005745664 Bool.false ep844 151653228179 137438953472 123557783678341 24498768334290944 Bool.true 31742411318722343993344 230956439327 1099511627776 247072753498995 48997536668581888 (ep845 (BSN.head_sum_c_succ qz149 18 19 rfl rfl) (ep869 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep870 ep881) rfl rfl

noncomputable abbrev qz174 := (@HMul.hMul Real Real Real qz268 qz441 qz566)

noncomputable def ep883 := @Enclosure.Complex.IsNear.of_eq qz592 (Complex.mk (@HMul.hMul Real Real Real qz0 qz71 (Real.cos qz174)) (@HMul.hMul Real Real Real qz0 qz71 (@Neg.neg Real Real.instNeg (Real.sin qz174)))) Bool.false 110348848877 1099511627776 26012547130457 146992610005745664 Bool.false 219703314725 1099511627776 26074898610545 146992610005745664 (BSN.cpow_neg_s_mk qz152 104500 1000 20 qz153 rfl)

noncomputable def ep884 := @Enclosure.Real.IsNear.mulLit_ff qz152 qz566 104500 1000 0 1 3372893643545847 1125899906842624 250000000133689 33422250000000000000 704934771501082023 2251799813685248 52250000027941001 66844500000000000000 qz154 (BSN.isNear_log_sfrac 20 1 3372893643545847 1125899906842624 250000000133689 33422250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz371) Bool.false 56587765202795681021952 18889465931478580854784 1000000000534756 133689000000000000000 3372893643545847 1125899906842624 250000000133689 33422250000000000000 (BSN.log_rat_reduce_isNear 20 1 4 40 32 116991 524288 24973259072661432 36028797018963968 133689 1000000000000000 rfl rfl rfl rfl (ep339 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep885 := nat_lit 998241896288411844369130182819188736

noncomputable def ep886 := BSN.sin_dyadic_bound_f 999560184 2147483648 2 1 1048576 267640 ep885 ep58 ep885 ep885 ep59 ep885 470633 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 999560184) qz287 0 1 ep885 ep58 ep885 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 999560184) qz288 0 1 ep885 ep59 ep885 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz465 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 328260833) qz26)

noncomputable def ep887 := @Enclosure.Real.IsNear.cos_image qz174 qz465 Bool.false 328260833 1048576 205 262144 Bool.false 470633 1048576 1 133689 (@Enclosure.Real.IsNear.recentre' qz174 Bool.false 704934771501082023 2251799813685248 52250000027941001 66844500000000000000 328260833 1048576 205 262144 (ep884 rfl) rfl) (Enclosure.sfrac_false_div 328260833 1048576) (BSN.cos_reduce3 qz465 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 70337794880156473491456) qz27) 226375608064910080 72057594037927936 Bool.false 470633 1048576 49 1000000000000000 267378 133689 (BSN.sin_reduce_arg_pos_rat_q3 328260833 1048576 226375608064910080 72057594037927936 49 70337794880156473491456 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 470633 1048576 70337794880156473491456 151115727451828646838272 999560184 2147483648 267640 267378 (ep886 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep888 := BSN.cos_dyadic_bound_f 999560184 2147483648 2 1 1048576 267640 ep885 ep62 ep885 ep885 ep63 ep885 937025 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 999560184) qz292 0 1 ep885 ep62 ep885 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 999560184) qz293 0 1 ep885 ep63 ep885 rfl rfl rfl rfl) rfl rfl

noncomputable def ep889 := @Enclosure.Real.IsNear.sin_image qz174 qz465 Bool.false 328260833 1048576 205 262144 Bool.true 937025 1048576 1 133689 (@Enclosure.Real.IsNear.recentre' qz174 Bool.false 704934771501082023 2251799813685248 52250000027941001 66844500000000000000 328260833 1048576 205 262144 (ep884 rfl) rfl) (Enclosure.sfrac_false_div 328260833 1048576) (BSN.sin_reduce3 qz465 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 70337794880156473491456) qz27) 226375608064910080 72057594037927936 Bool.false 937025 1048576 49 1000000000000000 267378 133689 (BSN.sin_reduce_arg_pos_rat_q3 328260833 1048576 226375608064910080 72057594037927936 49 70337794880156473491456 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 937025 1048576 70337794880156473491456 151115727451828646838272 999560184 2147483648 267640 267378 (ep888 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep890 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz71 (Real.cos qz174)) (@HMul.hMul Real Real Real qz0 qz71 (@Neg.neg Real Real.instNeg (Real.sin qz174))) Bool.false 110348848877 1099511627776 26012547130457 146992610005745664 Bool.false 219703314725 1099511627776 26074898610545 146992610005745664 (@Enclosure.Real.IsNear.mulLit_ff qz71 (Real.cos qz174) 234469 1048576 1 1048576 470633 1048576 27668389 35045769216 110348848877 1099511627776 26012547130457 146992610005745664 qz373 (@Enclosure.Real.IsNear.recentre' (Real.cos qz174) Bool.false 470633 1048576 27668389 35045769216 470633 1048576 27668389 35045769216 (ep887 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz71 (@Neg.neg Real Real.instNeg (Real.sin qz174)) 234469 1048576 1 1048576 937025 1048576 27668389 35045769216 219703314725 1099511627776 26074898610545 146992610005745664 qz373 (@Enclosure.Real.IsNear.neg (Real.sin qz174) Bool.true 937025 1048576 27668389 35045769216 (@Enclosure.Real.IsNear.recentre' (Real.sin qz174) Bool.true 937025 1048576 27668389 35045769216 937025 1048576 27668389 35045769216 (ep889 rfl rfl) rfl)) rfl)

noncomputable def ep891 := @ep841 110348848877 1099511627776 26012547130457 146992610005745664 Bool.false 219703314725 1099511627776 26074898610545 146992610005745664 Bool.false 181910718079072204750848 1323574674309 1099511627776 767359249200503 146992610005745664 Bool.true 12372941348711172145152 5626562301 549755813888 383646579553765 73496305002872832 (ep842 (BSN.head_sum_c_succ qz149 19 20 rfl rfl) (ep882 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep883 ep890) rfl rfl

noncomputable abbrev qz175 := (@HMul.hMul Real Real Real qz268 qz441 qz567)

noncomputable def ep892 := @Enclosure.Complex.IsNear.of_eq qz591 (Complex.mk (@HMul.hMul Real Real Real qz0 qz73 (Real.cos qz175)) (@HMul.hMul Real Real Real qz0 qz73 (@Neg.neg Real Real.instNeg (Real.sin qz175)))) Bool.true 79029732885 549755813888 12754509224045 73496305002872832 Bool.false 45128286823 274877906944 6383813995963 36748152501436416 (BSN.cpow_neg_s_mk qz152 104500 1000 21 qz153 rfl)

noncomputable def ep893 := @Enclosure.Real.IsNear.mulLit_ff qz152 qz567 104500 1000 0 1 3427826275261687 1125899906842624 250000000133689 33422250000000000000 716415691529692583 2251799813685248 52250000027941001 66844500000000000000 qz154 (BSN.isNear_log_sfrac 21 1 3427826275261687 1125899906842624 250000000133689 33422250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz375) Bool.false 57509381830540779323392 18889465931478580854784 1000000000534756 133689000000000000000 3427826275261687 1125899906842624 250000000133689 33422250000000000000 (BSN.log_rat_reduce_isNear 21 1 4 42 32 142571 524288 24973259072661432 36028797018963968 133689 1000000000000000 rfl rfl rfl rfl (ep349 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep894 := nat_lit 399823196760115237509521029567661586323113066920025272196494981127784499690625

noncomputable def ep895 := nat_lit 125143004921185950439534560822766246245001717392777808931214513929062890625

noncomputable def ep896 := nat_lit 1199219304270503340627684019581339226476849197325290260971622514355495373290625

noncomputable def ep897 := BSN.cos_dyadic_bound_f 1828840465 2147483648 3 2 1048576 267640 ep894 ep75 ep895 ep896 ep78 ep895 690765 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1828840465) qz292 0 2 ep894 ep75 ep895 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1828840465) qz293 0 2 ep896 ep78 ep895 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz466 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 333607053) qz26)

noncomputable def ep898 := @Enclosure.Real.IsNear.cos_image qz175 qz466 Bool.false 333607053 1048576 205 262144 Bool.true 690765 1048576 1 133689 (@Enclosure.Real.IsNear.recentre' qz175 Bool.false 716415691529692583 2251799813685248 52250000027941001 66844500000000000000 333607053 1048576 205 262144 (ep893 rfl) rfl) (Enclosure.sfrac_false_div 333607053 1048576) (BSN.cos_reduce2 qz466 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 128693206868245197357056) qz27) 226375608064910080 72057594037927936 Bool.false 690765 1048576 50 1000000000000000 267378 133689 (BSN.sin_reduce_arg_pos_rat_q2 333607053 1048576 226375608064910080 72057594037927936 50 128693206868245197357056 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 690765 1048576 128693206868245197357056 151115727451828646838272 1828840465 2147483648 267640 267378 (ep897 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep899 := nat_lit 11186733433902228745800514334693250625

noncomputable def ep900 := BSN.sin_dyadic_bound_f 1828840465 2147483648 2 1 1048576 267640 ep899 ep58 ep899 ep899 ep59 ep899 788894 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1828840465) qz287 0 1 ep899 ep58 ep899 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1828840465) qz288 0 1 ep899 ep59 ep899 rfl rfl rfl rfl) rfl rfl

noncomputable def ep901 := @Enclosure.Real.IsNear.sin_image qz175 qz466 Bool.false 333607053 1048576 205 262144 Bool.true 788894 1048576 1 133689 (@Enclosure.Real.IsNear.recentre' qz175 Bool.false 716415691529692583 2251799813685248 52250000027941001 66844500000000000000 333607053 1048576 205 262144 (ep893 rfl) rfl) (Enclosure.sfrac_false_div 333607053 1048576) (BSN.sin_reduce2 qz466 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 128693206868245197357056) qz27) 226375608064910080 72057594037927936 Bool.false 788894 1048576 50 1000000000000000 267378 133689 (BSN.sin_reduce_arg_pos_rat_q2 333607053 1048576 226375608064910080 72057594037927936 50 128693206868245197357056 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 788894 1048576 128693206868245197357056 151115727451828646838272 1828840465 2147483648 267640 267378 (ep900 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep902 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz73 (Real.cos qz175)) (@HMul.hMul Real Real Real qz0 qz73 (@Neg.neg Real Real.instNeg (Real.sin qz175))) Bool.true 79029732885 549755813888 12754509224045 73496305002872832 Bool.false 45128286823 274877906944 6383813995963 36748152501436416 (@Enclosure.Real.IsNear.mulLit_ft qz73 (Real.cos qz175) 114409 524288 1 524288 690765 1048576 27668389 35045769216 79029732885 549755813888 12754509224045 73496305002872832 qz377 (@Enclosure.Real.IsNear.recentre' (Real.cos qz175) Bool.true 690765 1048576 27668389 35045769216 690765 1048576 27668389 35045769216 (ep898 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz73 (@Neg.neg Real Real.instNeg (Real.sin qz175)) 114409 524288 1 524288 394447 524288 27668389 35045769216 45128286823 274877906944 6383813995963 36748152501436416 qz377 (@Enclosure.Real.IsNear.neg (Real.sin qz175) Bool.true 394447 524288 27668389 35045769216 (@Enclosure.Real.IsNear.recentre' (Real.sin qz175) Bool.true 788894 1048576 27668389 35045769216 394447 524288 27668389 35045769216 (ep901 rfl rfl) rfl)) rfl)

noncomputable def ep903 := @ep839 79029732885 549755813888 12754509224045 73496305002872832 Bool.false 45128286823 274877906944 6383813995963 36748152501436416 Bool.false 640748762069199992389632 1165515208539 1099511627776 264289422549531 48997536668581888 Bool.false 23262920383160574279680 84630011345 549755813888 132138069181897 24498768334290944 (ep840 (BSN.head_sum_c_succ qz149 20 21 rfl rfl) (ep891 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep892 ep902) rfl rfl

noncomputable abbrev qz176 := (@HMul.hMul Real Real Real qz268 qz441 qz568)

noncomputable def ep904 := @Enclosure.Complex.IsNear.of_eq qz590 (Complex.mk (@HMul.hMul Real Real Real qz0 qz75 (Real.cos qz176)) (@HMul.hMul Real Real Real qz0 qz75 (@Neg.neg Real Real.instNeg (Real.sin qz176)))) Bool.true 197329963431 1099511627776 24859963839835 146992610005745664 Bool.true 63269090127 549755813888 12408814873703 73496305002872832 (BSN.cpow_neg_s_mk qz152 104500 1000 22 qz153 rfl)

noncomputable def ep905 := @Enclosure.Real.IsNear.mulLit_ff qz152 qz568 104500 1000 0 1 3480203401436407 1125899906842624 250000000133689 33422250000000000000 727362510900209063 2251799813685248 52250000027941001 66844500000000000000 qz154 (BSN.isNear_log_sfrac 22 1 3480203401436407 1125899906842624 250000000133689 33422250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz379) Bool.false 58388124189833310502912 18889465931478580854784 1000000000534756 133689000000000000000 3480203401436407 1125899906842624 250000000133689 33422250000000000000 (BSN.log_rat_reduce_isNear 22 1 4 44 32 166961 524288 24973259072661432 36028797018963968 133689 1000000000000000 rfl rfl rfl rfl (ep360 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep906 := nat_lit 1371510014762568416731311238729442179942843883677755554046493019994081593323105

noncomputable def ep907 := nat_lit 454472489222695381826231016628733142261645241553531932784532732645068435041

noncomputable def ep908 := nat_lit 3591314226062271013201906013121616331905691317336368351754401999369740728856161

noncomputable def ep909 := BSN.sin_dyadic_bound_f 2148762667 2147483648 3 2 1048576 267640 ep906 ep108 ep907 ep908 ep110 ep907 882683 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2148762667) qz287 0 2 ep906 ep108 ep907 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2148762667) qz288 0 2 ep908 ep110 ep907 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz467 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 338704563) qz26)

noncomputable def ep910 := @Enclosure.Real.IsNear.cos_image qz176 qz467 Bool.false 338704563 1048576 205 262144 Bool.true 882683 1048576 1 133689 (@Enclosure.Real.IsNear.recentre' qz176 Bool.false 727362510900209063 2251799813685248 52250000027941001 66844500000000000000 338704563 1048576 205 262144 (ep905 rfl) rfl) (Enclosure.sfrac_false_div 338704563 1048576) (BSN.cos_reduce1 qz467 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 151205730429987807297536) qz27) 226375608064910080 72057594037927936 Bool.false 882683 1048576 51 1000000000000000 267378 133689 (BSN.sin_reduce_arg_pos_rat_q1 338704563 1048576 226375608064910080 72057594037927936 51 151205730429987807297536 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 882683 1048576 151205730429987807297536 151115727451828646838272 2148762667 2147483648 267640 267378 (ep909 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep911 := nat_lit 762151995974414762798206790857080648031473999928332433107067025655665360039521

noncomputable def ep912 := nat_lit 2285547042944798897630967910537984477809898709301890235455632011501705943248481

noncomputable def ep913 := BSN.cos_dyadic_bound_f 2148762667 2147483648 3 2 1048576 267640 ep911 ep75 ep907 ep912 ep78 ep907 566022 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2148762667) qz292 0 2 ep911 ep75 ep907 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2148762667) qz293 0 2 ep912 ep78 ep907 rfl rfl rfl rfl) rfl rfl

noncomputable def ep914 := @Enclosure.Real.IsNear.sin_image qz176 qz467 Bool.false 338704563 1048576 205 262144 Bool.false 566022 1048576 1 133689 (@Enclosure.Real.IsNear.recentre' qz176 Bool.false 727362510900209063 2251799813685248 52250000027941001 66844500000000000000 338704563 1048576 205 262144 (ep905 rfl) rfl) (Enclosure.sfrac_false_div 338704563 1048576) (BSN.sin_reduce1 qz467 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 151205730429987807297536) qz27) 226375608064910080 72057594037927936 Bool.false 566022 1048576 51 1000000000000000 267378 133689 (BSN.sin_reduce_arg_pos_rat_q1 338704563 1048576 226375608064910080 72057594037927936 51 151205730429987807297536 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 566022 1048576 151205730429987807297536 151115727451828646838272 2148762667 2147483648 267640 267378 (ep913 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep915 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz75 (Real.cos qz176)) (@HMul.hMul Real Real Real qz0 qz75 (@Neg.neg Real Real.instNeg (Real.sin qz176))) Bool.true 197329963431 1099511627776 24859963839835 146992610005745664 Bool.true 63269090127 549755813888 12408814873703 73496305002872832 (@Enclosure.Real.IsNear.mulLit_ft qz75 (Real.cos qz176) 223557 1048576 1 1048576 882683 1048576 27668389 35045769216 197329963431 1099511627776 24859963839835 146992610005745664 qz382 (@Enclosure.Real.IsNear.recentre' (Real.cos qz176) Bool.true 882683 1048576 27668389 35045769216 882683 1048576 27668389 35045769216 (ep910 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz75 (@Neg.neg Real Real.instNeg (Real.sin qz176)) 223557 1048576 1 1048576 283011 524288 27668389 35045769216 63269090127 549755813888 12408814873703 73496305002872832 qz382 (@Enclosure.Real.IsNear.neg (Real.sin qz176) Bool.false 283011 524288 27668389 35045769216 (@Enclosure.Real.IsNear.recentre' (Real.sin qz176) Bool.false 566022 1048576 27668389 35045769216 283011 524288 27668389 35045769216 (ep914 rfl rfl) rfl)) rfl)

noncomputable def ep916 := @ep837 197329963431 1099511627776 24859963839835 146992610005745664 Bool.true 63269090127 549755813888 12408814873703 73496305002872832 Bool.false 1064530934837402620919808 242046311277 274877906944 204432057872107 36748152501436416 Bool.false 11743290629599038275584 10680460609 274877906944 204411511209697 36748152501436416 (ep838 (BSN.head_sum_c_succ qz149 21 22 rfl rfl) (ep903 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep904 ep915) rfl rfl

noncomputable abbrev qz177 := (@HMul.hMul Real Real Real qz268 qz441 qz569)

noncomputable def ep917 := @Enclosure.Complex.IsNear.of_eq qz589 (Complex.mk (@HMul.hMul Real Real Real qz0 qz77 (Real.cos qz177)) (@HMul.hMul Real Real Real qz0 qz77 (@Neg.neg Real Real.instNeg (Real.sin qz177)))) Bool.false 136452253941 1099511627776 24281542545007 146992610005745664 Bool.true 92117575545 549755813888 12155379670067 73496305002872832 (BSN.cpow_neg_s_mk qz152 104500 1000 23 qz153 rfl)

noncomputable def ep918 := @Enclosure.Real.IsNear.mulLit_ff qz152 qz569 104500 1000 0 1 3530250507853047 1125899906842624 250000000133689 33422250000000000000 737822356141286823 2251799813685248 52250000027941001 66844500000000000000 qz154 (BSN.isNear_log_sfrac 23 1 3530250507853047 1125899906842624 250000000133689 33422250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz384) Bool.false 59227775304360265777152 18889465931478580854784 1000000000534756 133689000000000000000 3530250507853047 1125899906842624 250000000133689 33422250000000000000 (BSN.log_rat_reduce_isNear 23 1 4 46 32 190266 524288 24973259072661432 36028797018963968 133689 1000000000000000 rfl rfl rfl rfl (ep371 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep919 := nat_lit 576832708538908534240561654223498674502294143035957253374887040581871285108736

noncomputable def ep920 := nat_lit 260405447076544535496673082248498819576656787297206844006493281994271686656

noncomputable def ep921 := nat_lit 1729977314722572513650691616505999025867729115533277346436648135181625311952896

noncomputable def ep922 := BSN.cos_dyadic_bound_f 2004270148 2147483648 3 2 1048576 267640 ep919 ep75 ep920 ep921 ep78 ep920 624087 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2004270148) qz292 0 2 ep919 ep75 ep920 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2004270148) qz293 0 2 ep921 ep78 ep920 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz468 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 85893827) (@Nat.cast Real Real.instNatCast 262144))

noncomputable def ep923 := @Enclosure.Real.IsNear.cos_image qz177 qz468 Bool.false 85893827 262144 205 262144 Bool.false 624087 1048576 1 133689 (@Enclosure.Real.IsNear.recentre' qz177 Bool.false 737822356141286823 2251799813685248 52250000027941001 66844500000000000000 85893827 262144 205 262144 (ep918 rfl) rfl) (Enclosure.sfrac_false_div 85893827 262144) (BSN.cos_reduce0 qz468 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 35259493341927240105984) qz316) 226375608064910080 72057594037927936 Bool.false 624087 1048576 52 1000000000000000 267378 133689 (BSN.sin_reduce_arg_pos_rat_q0 85893827 262144 226375608064910080 72057594037927936 52 35259493341927240105984 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 624087 1048576 35259493341927240105984 37778931862957161709568 2004270148 2147483648 267640 267378 (ep922 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep924 := nat_lit 1038090551012374126004613639136498815048468132034885290599591478421772895846400

noncomputable def ep925 := nat_lit 2718386977165713067430803012748142184180959091959551711918157644838557334962176

noncomputable def ep926 := BSN.sin_dyadic_bound_f 2004270148 2147483648 3 2 1048576 267640 ep924 ep108 ep920 ep925 ep110 ep920 842630 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2004270148) qz287 0 2 ep924 ep108 ep920 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2004270148) qz288 0 2 ep925 ep110 ep920 rfl rfl rfl rfl) rfl rfl

noncomputable def ep927 := @Enclosure.Real.IsNear.sin_image qz177 qz468 Bool.false 85893827 262144 205 262144 Bool.false 842630 1048576 1 133689 (@Enclosure.Real.IsNear.recentre' qz177 Bool.false 737822356141286823 2251799813685248 52250000027941001 66844500000000000000 85893827 262144 205 262144 (ep918 rfl) rfl) (Enclosure.sfrac_false_div 85893827 262144) (BSN.sin_reduce0 qz468 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 35259493341927240105984) qz316) 226375608064910080 72057594037927936 Bool.false 842630 1048576 52 1000000000000000 267378 133689 (BSN.sin_reduce_arg_pos_rat_q0 85893827 262144 226375608064910080 72057594037927936 52 35259493341927240105984 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 842630 1048576 35259493341927240105984 37778931862957161709568 2004270148 2147483648 267640 267378 (ep926 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep928 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz77 (Real.cos qz177)) (@HMul.hMul Real Real Real qz0 qz77 (@Neg.neg Real Real.instNeg (Real.sin qz177))) Bool.false 136452253941 1099511627776 24281542545007 146992610005745664 Bool.true 92117575545 549755813888 12155379670067 73496305002872832 (@Enclosure.Real.IsNear.mulLit_ff qz77 (Real.cos qz177) 218643 1048576 1 1048576 624087 1048576 27668389 35045769216 136452253941 1099511627776 24281542545007 146992610005745664 qz386 (@Enclosure.Real.IsNear.recentre' (Real.cos qz177) Bool.false 624087 1048576 27668389 35045769216 624087 1048576 27668389 35045769216 (ep923 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz77 (@Neg.neg Real Real.instNeg (Real.sin qz177)) 218643 1048576 1 1048576 421315 524288 27668389 35045769216 92117575545 549755813888 12155379670067 73496305002872832 qz386 (@Enclosure.Real.IsNear.neg (Real.sin qz177) Bool.false 421315 524288 27668389 35045769216 (@Enclosure.Real.IsNear.recentre' (Real.sin qz177) Bool.false 842630 1048576 27668389 35045769216 421315 524288 27668389 35045769216 (ep927 rfl rfl) rfl)) rfl)

noncomputable def ep929 := @ep835 136452253941 1099511627776 24281542545007 146992610005745664 Bool.true 92117575545 549755813888 12155379670067 73496305002872832 Bool.false 303640443670443910496256 1104637499049 1099511627776 842009774033435 146992610005745664 Bool.true 19449441043765880946688 70756654327 549755813888 420978402089461 73496305002872832 (ep836 (BSN.head_sum_c_succ qz149 22 23 rfl rfl) (ep916 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep917 ep928) rfl rfl

noncomputable abbrev qz178 := (@HMul.hMul Real Real Real qz268 qz441 qz570)

noncomputable def ep930 := @Enclosure.Complex.IsNear.of_eq qz588 (Complex.mk (@HMul.hMul Real Real Real qz0 qz79 (Real.cos qz178)) (@HMul.hMul Real Real Real qz0 qz79 (@Neg.neg Real Real.instNeg (Real.sin qz178)))) Bool.false 139108012841 1099511627776 23775454947431 146992610005745664 Bool.false 88063135965 549755813888 11899288296835 73496305002872832 (BSN.cpow_neg_s_mk qz152 104500 1000 24 qz153 rfl)

noncomputable def ep931 := @Enclosure.Real.IsNear.mulLit_ff qz152 qz570 104500 1000 0 1 3578169457974519 1125899906842624 250000000133689 33422250000000000000 747837416716674471 2251799813685248 52250000027941001 66844500000000000000 qz154 (BSN.isNear_log_sfrac 24 1 3578169457974519 1125899906842624 250000000133689 33422250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz388) Bool.false 60031721881041427759104 18889465931478580854784 1000000000534756 133689000000000000000 3578169457974519 1125899906842624 250000000133689 33422250000000000000 (BSN.log_rat_reduce_isNear 24 1 4 48 32 212580 524288 24973259072661432 36028797018963968 133689 1000000000000000 rfl rfl rfl rfl (ep382 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep932 := nat_lit 4247479380724033402832231468628956176

noncomputable def ep933 := BSN.sin_dyadic_bound_f 1435597918 2147483648 2 1 1048576 267640 ep932 ep58 ep932 ep932 ep59 ep932 649919 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1435597918) qz287 0 1 ep932 ep58 ep932 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1435597918) qz288 0 1 ep932 ep59 ep932 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz469 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 174119467) qz20)

noncomputable def ep934 := @Enclosure.Real.IsNear.cos_image qz178 qz469 Bool.false 174119467 524288 205 262144 Bool.false 649919 1048576 1 133689 (@Enclosure.Real.IsNear.recentre' qz178 Bool.false 747837416716674471 2251799813685248 52250000027941001 66844500000000000000 174119467 524288 205 262144 (ep931 rfl) rfl) (Enclosure.sfrac_false_div 174119467 524288) (BSN.cos_reduce3 qz469 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 50510611333173460598784) qz21) 226375608064910080 72057594037927936 Bool.false 649919 1048576 52 1000000000000000 267378 133689 (BSN.sin_reduce_arg_pos_rat_q3 174119467 524288 226375608064910080 72057594037927936 52 50510611333173460598784 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 649919 1048576 50510611333173460598784 75557863725914323419136 1435597918 2147483648 267640 267378 (ep933 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep935 := nat_lit 151778986478758557273088153321551294893906903720133950936694194201998469529856

noncomputable def ep936 := nat_lit 18041081089675818298446497893194036824625669809012690771715878607328542976

noncomputable def ep937 := nat_lit 455300877274096320182667566968867496608071459820783827428539150848780751503616

noncomputable def ep938 := BSN.cos_dyadic_bound_f 1435597918 2147483648 3 2 1048576 267640 ep935 ep75 ep936 ep937 ep78 ep936 822870 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1435597918) qz292 0 2 ep935 ep75 ep936 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1435597918) qz293 0 2 ep937 ep78 ep936 rfl rfl rfl rfl) rfl rfl

noncomputable def ep939 := @Enclosure.Real.IsNear.sin_image qz178 qz469 Bool.false 174119467 524288 205 262144 Bool.true 822870 1048576 1 133689 (@Enclosure.Real.IsNear.recentre' qz178 Bool.false 747837416716674471 2251799813685248 52250000027941001 66844500000000000000 174119467 524288 205 262144 (ep931 rfl) rfl) (Enclosure.sfrac_false_div 174119467 524288) (BSN.sin_reduce3 qz469 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 50510611333173460598784) qz21) 226375608064910080 72057594037927936 Bool.false 822870 1048576 52 1000000000000000 267378 133689 (BSN.sin_reduce_arg_pos_rat_q3 174119467 524288 226375608064910080 72057594037927936 52 50510611333173460598784 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 822870 1048576 50510611333173460598784 75557863725914323419136 1435597918 2147483648 267640 267378 (ep938 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep940 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz79 (Real.cos qz178)) (@HMul.hMul Real Real Real qz0 qz79 (@Neg.neg Real Real.instNeg (Real.sin qz178))) Bool.false 139108012841 1099511627776 23775454947431 146992610005745664 Bool.false 88063135965 549755813888 11899288296835 73496305002872832 (@Enclosure.Real.IsNear.mulLit_ff qz79 (Real.cos qz178) 214039 1048576 1 1048576 649919 1048576 27668389 35045769216 139108012841 1099511627776 23775454947431 146992610005745664 qz390 (@Enclosure.Real.IsNear.recentre' (Real.cos qz178) Bool.false 649919 1048576 27668389 35045769216 649919 1048576 27668389 35045769216 (ep934 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz79 (@Neg.neg Real Real.instNeg (Real.sin qz178)) 214039 1048576 1 1048576 411435 524288 27668389 35045769216 88063135965 549755813888 11899288296835 73496305002872832 qz390 (@Enclosure.Real.IsNear.neg (Real.sin qz178) Bool.true 411435 524288 27668389 35045769216 (@Enclosure.Real.IsNear.recentre' (Real.sin qz178) Bool.true 822870 1048576 27668389 35045769216 411435 524288 27668389 35045769216 (ep939 rfl rfl) rfl)) rfl)

noncomputable def ep941 := @ep832 139108012841 1099511627776 23775454947431 146992610005745664 Bool.false 88063135965 549755813888 11899288296835 73496305002872832 Bool.false ep833 621872755945 549755813888 432892614490433 73496305002872832 Bool.false 9514338898436417388544 8653240819 274877906944 54109711298287 9187038125359104 (ep834 (BSN.head_sum_c_succ qz149 23 24 rfl rfl) (ep929 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep930 ep940) rfl rfl

theorem EMRow31.d14 : Enclosure.Complex.IsNear qz170 Bool.false 621872755945 549755813888 432892614490433 73496305002872832 Bool.false 8653240819 274877906944 54109711298287 9187038125359104 := ep831 (BSN.head_sum_c_succ qz149 24 25 rfl rfl) (ep941 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

theorem EMRow31.d15 : @Eq Nat (Nat.pow 27 1) 27 := @Eq.refl Nat 27

noncomputable def ep942 := nat_lit 53740111292079958464343656708133

noncomputable def ep943 := nat_lit 8100953015257908827917604301570048

noncomputable abbrev qz594 := (@HAdd.hAdd Complex Complex Complex qz603 (@HAdd.hAdd Complex Complex Complex qz603 qz606 (@HMul.hMul Complex Complex Complex qz605 Complex.I (@HDiv.hDiv Complex Complex Complex qz607 (↑qz610) (2 : Complex)))) (@Nat.cast Complex Complex.instNatCast 2))

noncomputable abbrev qz470 := qz594

noncomputable abbrev qz179 := (Complex.Stirling.logGammaStirling 1 qz470)

noncomputable abbrev qz595 := (@HAdd.hAdd Complex Complex Complex qz603 qz606 (@HMul.hMul Complex Complex Complex qz605 Complex.I (@HDiv.hDiv Complex Complex Complex qz607 (↑qz610) (2 : Complex))))

noncomputable abbrev qz471 := qz595

noncomputable abbrev qz180 := qz471

noncomputable abbrev qz181 := (@HMul.hMul Real Real Real qz268 (@HDiv.hDiv Real Real Real qz271 qz441 (2 : Real)) (Real.log Real.pi))

noncomputable def ep944 := Complex.re (@HMul.hMul Complex Complex Complex qz81 (Complex.exp (@HMul.hMul Complex Complex Complex qz81 Complex.I ↑(@HSub.hSub Real Real Real qz395 (Complex.im (@HSub.hSub Complex Complex Complex qz82 qz179 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz180 (@Nat.cast Complex Complex.instNatCast j))))) qz181))) (zetaApproximant qz149 1 27))

noncomputable def ep945 := @Enclosure.Real.IsNear.of_eq ep944 (@HSub.hSub Real Real Real qz395 (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz395 (Complex.im (@HSub.hSub Complex Complex Complex qz82 qz179 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz180 (@Nat.cast Complex Complex.instNatCast j))))) qz181)) (Complex.re (zetaApproximant qz149 1 27))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz395 (Complex.im (@HSub.hSub Complex Complex Complex qz82 qz179 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz180 (@Nat.cast Complex Complex.instNatCast j))))) qz181)) (Complex.im (zetaApproximant qz149 1 27))))

noncomputable def ep946 := nat_lit 5646221437141467243651425

noncomputable def ep947 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz395 (Complex.im (@HSub.hSub Complex Complex Complex qz82 qz179 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz180 (@Nat.cast Complex Complex.instNatCast j))))) qz181)) (Complex.re (zetaApproximant qz149 1 27))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz395 (Complex.im (@HSub.hSub Complex Complex Complex qz82 qz179 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz180 (@Nat.cast Complex Complex.instNatCast j))))) qz181)) (Complex.im (zetaApproximant qz149 1 27))) ep946

noncomputable def ep948 := nat_lit 5439087053737519277408256

noncomputable def ep949 := nat_lit 643882440782725953474072914846599

noncomputable def ep950 := nat_lit 97211436183094905935011251618840576

noncomputable def ep951 := nat_lit 998894722233548098050965650997

noncomputable def ep952 := nat_lit 1137427456253857854762297703911731426587391819776

noncomputable def ep953 := @Enclosure.Real.IsNear.mulLit_ff (Real.cos (@HSub.hSub Real Real Real qz395 (Complex.im (@HSub.hSub Complex Complex Complex qz82 qz179 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz180 (@Nat.cast Complex Complex.instNatCast j))))) qz181)) (Complex.re (zetaApproximant qz149 1 27)) 1048575 1048576 44764879

noncomputable def ep954 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HSub.hSub Real Real Real qz395 (Complex.im (@HSub.hSub Complex Complex Complex qz82 qz179 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz180 (@Nat.cast Complex Complex.instNatCast j))))) qz181)) Bool.false 1048575 1048576 44764879

noncomputable abbrev qz472 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 98826671) qz26)

noncomputable def ep955 := @Enclosure.Real.IsNear.cos_image (@HSub.hSub Real Real Real qz395 (Complex.im (@HSub.hSub Complex Complex Complex qz82 qz179 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz180 (@Nat.cast Complex Complex.instNatCast j))))) qz181) qz472 Bool.false 98826671 1048576 327

noncomputable def ep956 := nat_lit 46727692288000000000000000

noncomputable def ep957 := @Enclosure.Real.IsNear.recentre' (@HSub.hSub Real Real Real qz395 (Complex.im (@HSub.hSub Complex Complex Complex qz82 qz179 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz180 (@Nat.cast Complex Complex.instNatCast j))))) qz181) Bool.false 3395658585273451517 36028797018963968 14534796423702752572429 ep956

noncomputable def ep958 := @Enclosure.Real.IsNear.subLit_ff_p (Complex.im (@HSub.hSub Complex Complex Complex qz82 qz179 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz180 (@Nat.cast Complex Complex.instNatCast j))))) qz181 5550617400513840125 36028797018963968 5221129423702752572429 ep956 15679389 262144

noncomputable def ep959 := nat_lit 140183076864000000000000000

noncomputable def ep960 := @Enclosure.Complex.IsNear.im_isNear (@HSub.hSub Complex Complex Complex qz82 qz179 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz180 (@Nat.cast Complex Complex.instNatCast j)))) Bool.true 2959556084171399117 36028797018963968 28778167246147064702767 ep959 Bool.false 5550617400513840125 36028797018963968

noncomputable def ep961 := @Enclosure.Complex.IsNear.subLitP qz179 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz180 (@Nat.cast Complex Complex.instNatCast j))) Bool.true 2674482664355916517 36028797018963968 28253879244605050857263 ep959 Bool.false 5662771079500633469 36028797018963968 14614812270968074640423

noncomputable def ep962 := nat_lit 13328655677856397358350496046252032

noncomputable def ep963 := nat_lit 1562359903539395096231775567872000

noncomputable abbrev qz473 := (@HSub.hSub Complex Complex Complex qz572 qz594 qz575)

noncomputable abbrev qz474 := (Complex.log qz594)

noncomputable abbrev qz182 := (@HSub.hSub Complex Complex Complex qz392 (@HMul.hMul Complex Complex Complex qz391 qz473 qz474) qz470)

noncomputable abbrev qz183 := qz470

noncomputable def ep964 := @Enclosure.Complex.IsNear.of_eq qz179 (@HAdd.hAdd Complex Complex Complex qz4 (@HAdd.hAdd Complex Complex Complex qz4 qz182 qz87) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz89 2 k))) (@HMul.hMul Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz81 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz82 (@HMul.hMul Complex Complex Complex qz81 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz90 qz183 (@HSub.hSub Int Int Int qz404 qz92 (@HMul.hMul Int Int Int qz405 qz93 (@Nat.cast Int instNatCastInt k)))))) Bool.true 2674482664355916517

noncomputable def ep965 := @Enclosure.Complex.IsNear.addLitP (@HAdd.hAdd Complex Complex Complex qz4 qz182 qz87) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz89 2 k))) (@HMul.hMul Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz81 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz82 (@HMul.hMul Complex Complex Complex qz81 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz90 qz183 (@HSub.hSub Int Int Int qz404 qz92 (@HMul.hMul Int Int Int qz405 qz93 (@Nat.cast Int instNatCastInt k))))) Bool.true 2674485134227401445 36028797018963968

noncomputable def ep966 := nat_lit 91894524617020850756969824256

noncomputable def ep967 := nat_lit 194571332729518694085104238592

noncomputable def ep968 := @ep965 862239593658799591 4278048000000000000000 Bool.false 5662828435405116797 36028797018963968 55750000154143417 534756000000000000000 Bool.false 2355453 34359738368 3 34359738368 Bool.true 54698853 34359738368 209 103079215104 Bool.true ep966 2674482664355916517 36028797018963968 28253879244605050857263 ep959 Bool.false ep967

noncomputable def ep969 := @Enclosure.Complex.IsNear.addLitP qz182 qz87 Bool.true 2707593353485085413 36028797018963968 106250000019117527 534756000000000000000

noncomputable def ep970 := @ep969 Bool.false 5662828435405116797 36028797018963968 55750000154143417 534756000000000000000 Bool.false 120447 131072 3 1048576 Bool.false 0 1 0 1 Bool.true 350550115513453962199040 2674485134227401445 36028797018963968 862239593658799591 4278048000000000000000 Bool.false 5662828435405116797 5662828435405116797 36028797018963968

noncomputable abbrev qz184 := (@HMul.hMul Complex Complex Complex qz391 qz473 qz474)

noncomputable def ep971 := @Enclosure.Complex.IsNear.subLitP qz184 qz183 Bool.true 2626528560192416485 36028797018963968 106250000019117527 534756000000000000000 Bool.false 7545333079645984125

noncomputable def ep972 := @ep971 36028797018963968 55750000154143417 534756000000000000000 Bool.false 9000 4000 0 1 Bool.false 209000 4000 0 1 Bool.true 10830373413940341652000 2707593353485085413 36028797018963968 106250000019117527 534756000000000000000 Bool.false 22651313741620467188000 5662828435405116797 36028797018963968 55750000154143417 534756000000000000000

noncomputable abbrev qz185 := qz473

noncomputable abbrev qz186 := qz474

noncomputable def ep973 := @Enclosure.Complex.IsNear.mul qz185 qz186 Bool.true 2626528560192416485 36028797018963968 106250000019117527 534756000000000000000 Bool.false 7545333079645984125 36028797018963968 55750000154143417

noncomputable abbrev qz187 := (Complex.re qz473)

noncomputable abbrev qz188 := (Complex.re qz474)

noncomputable abbrev qz189 := (Complex.im qz473)

noncomputable abbrev qz190 := (Complex.im qz474)

noncomputable def ep974 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 qz187 qz188) (@HMul.hMul Real Real Real qz0 qz189 qz190) 249488277980165707 36028797018963968 3500000010294053 1069512000000000000000 179751052385786387 2251799813685248

noncomputable def ep975 := nat_lit 5914416522480266127755850316513280

noncomputable def ep976 := @Enclosure.Real.IsNear.mulLit_ff qz187 qz188 7000 4000 0 1 35641182568595101 9007199254740992 500000001470579 267378000000000000000

noncomputable def ep977 := @Enclosure.Complex.IsNear.re_isNear qz185 Bool.false 7000 4000 0 1 Bool.false 209000 4000 0 1

noncomputable abbrev qz191 := (Enclosure.sfrac Bool.false 209000 4000)

noncomputable def ep978 := @Enclosure.Complex.IsNear.of_eq qz185 (Complex.mk (Enclosure.sfrac Bool.false 7000 4000) qz191) Bool.false 7000 4000 0 1 Bool.false 209000 4000 0

noncomputable abbrev qz475 := (Complex.log (Complex.mk qz102 qz191))

noncomputable def ep979 := @Enclosure.Complex.IsNear.of_eq qz186 qz475 Bool.false 35641182568595101 9007199254740992 500000001470579 267378000000000000000 Bool.false 860052882228643 562949953421312 1000000000133689 267378000000000000000

noncomputable def ep980 := nat_lit 21095002396047264010402545000000000000000000000000000000000000000000

noncomputable def ep981 := nat_lit 146936325170627687889839394240000000000000000000000000000000000000

noncomputable def ep982 := nat_lit 26486565965886475902459840000000000000000000000000000000000000

noncomputable def ep983 := BSN.log_dyadic_bound 10994000000 76530000000 4 3 ep980 1048576 267378 ep981 ep982 303367 87524000000 65536000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 10994000000) (BSN.artanhQ 76530000000) 0 3 ep981 ep980 ep982 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz596 := (Real.log (Enclosure.sfrac Bool.false 43762000000 16000000))

noncomputable def ep984 := @Enclosure.Real.IsNear.mulLit_ff qz103 qz596 1 2 0 1 35641182568595101 4503599627370496 500000001470579 133689000000000000000 35641182568595101 9007199254740992 500000001470579 267378000000000000000 qz408 (BSN.isNear_log_sfrac 43762000000 16000000 35641182568595101 4503599627370496 500000001470579 133689000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 43762000000) qz409)) Bool.false 298979909224377413009408 37778931862957161709568 1000000002941158 267378000000000000000 35641182568595101 4503599627370496 500000001470579 133689000000000000000 (BSN.log_rat_reduce_isNear 43762000000 16000000 11 87524000000 65536000000 303367 1048576 24973259072661432 36028797018963968 267378 1000000000000000 rfl rfl rfl rfl (ep983 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep985 := BSN.arctan_dyadic_bound_f 9000 209000 1 0 1048576 267378 0 1 1 0 1 1 45126 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 9000) (BSN.arctanEvenQ 209000) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 9000) (BSN.arctanOddQ 209000) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz476 := (Real.arctan (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 9000) (@Nat.cast Real Real.instNatCast 209000)))

noncomputable def ep986 := @Enclosure.Real.IsNear.subLit_ff_p qz104 qz476 884279719003555 562949953421312 1 2000000000000000 45126 1048576 1 267378 901830811035781562368 860052882228643 562949953421312 1000000000133689 267378000000000000000 qz105 (ep985 rfl) rfl rfl

noncomputable abbrev qz477 := (Real.arctan (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 209000) (@Nat.cast Real Real.instNatCast 9000)))

noncomputable def ep987 := @Enclosure.Complex.IsNear.re_isNear qz186 Bool.false 35641182568595101 9007199254740992 500000001470579 267378000000000000000 Bool.false 860052882228643 562949953421312 1000000000133689 267378000000000000000 (ep979 (@congrArg Complex Complex qz183 (Complex.mk qz102 qz191) Complex.log (BSN.w_shift_mk qz152 Bool.false 104500 1000 2 qz153 rfl)) (@Enclosure.Complex.IsNear.of_parts qz475 Bool.false 35641182568595101 9007199254740992 500000001470579 267378000000000000000 Bool.false 860052882228643 562949953421312 1000000000133689 267378000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz475) (@HMul.hMul Real Real Real qz0 qz103 qz596) Bool.false 35641182568595101 9007199254740992 500000001470579 267378000000000000000 (Enclosure.clog_re_eq 9000 209000 4000 43762000000 16000000 rfl rfl rfl) (ep984 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz475) qz477 Bool.false 860052882228643 562949953421312 1000000000133689 267378000000000000000 (Enclosure.clog_im_eq 9000 209000 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz477 (@HSub.hSub Real Real Real qz395 qz104 qz476) Bool.false 860052882228643 562949953421312 1000000000133689 267378000000000000000 (BSN.arctan_recip 209000 9000 rfl rfl) ep986))))

noncomputable def ep988 := @Enclosure.Real.IsNear.mulLit_ff qz189 qz190 209000 4000 0 1 860052882228643 562949953421312 1000000000133689 267378000000000000000

noncomputable def ep989 := @Enclosure.Complex.IsNear.im_isNear qz185 Bool.false 7000 4000 0 1 Bool.false 209000 4000 0 1

noncomputable def ep990 := @Enclosure.Complex.IsNear.im_isNear qz186 Bool.false 35641182568595101 9007199254740992 500000001470579 267378000000000000000 Bool.false 860052882228643 562949953421312 1000000000133689 267378000000000000000 (ep979 (@congrArg Complex Complex qz183 (Complex.mk qz102 qz191) Complex.log (BSN.w_shift_mk qz152 Bool.false 104500 1000 2 qz153 rfl)) (@Enclosure.Complex.IsNear.of_parts qz475 Bool.false 35641182568595101 9007199254740992 500000001470579 267378000000000000000 Bool.false 860052882228643 562949953421312 1000000000133689 267378000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz475) (@HMul.hMul Real Real Real qz0 qz103 qz596) Bool.false 35641182568595101 9007199254740992 500000001470579 267378000000000000000 (Enclosure.clog_re_eq 9000 209000 4000 43762000000 16000000 rfl rfl rfl) (ep984 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz475) qz477 Bool.false 860052882228643 562949953421312 1000000000133689 267378000000000000000 (Enclosure.clog_im_eq 9000 209000 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz477 (@HSub.hSub Real Real Real qz395 qz104 qz476) Bool.false 860052882228643 562949953421312 1000000000133689 267378000000000000000 (BSN.arctan_recip 209000 9000 rfl rfl) ep986))))

noncomputable abbrev qz192 := (@ep978 1 (BSN.w_sub_half_mk qz441 Bool.false 104500 1000 2 qz442 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7000 4000) (Enclosure.sfrac Bool.false 209000 4000) Bool.false 7000 4000 0 1 Bool.false 209000 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 7000 4000) (Enclosure.Real.IsNear.const Bool.false 209000 4000)))

noncomputable def ep991 := @ep974 209000000027941001 1069512000000000000000 ep975 2626528560192416485 36028797018963968 106250000019117527 534756000000000000000 (@ep976 249488277980165707 36028797018963968 3500000010294053 1069512000000000000000 (ep977 qz192) ep987 rfl) (@ep988 179751052385786387 2251799813685248 209000000027941001 1069512000000000000000 (ep989 qz192) ep990 rfl) rfl

noncomputable def ep992 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz187 qz190) (@HMul.hMul Real Real Real qz0 qz189 qz188) 6020370175600501 2251799813685248 7000000000935823 1069512000000000000000 7449007156836376109 36028797018963968

noncomputable def ep993 := nat_lit 16990579622939965561037219954688000

noncomputable def ep994 := @Enclosure.Real.IsNear.mulLit_ff qz187 qz190 7000 4000 0 1 860052882228643 562949953421312 1000000000133689 267378000000000000000

noncomputable def ep995 := @Enclosure.Real.IsNear.mulLit_ff qz189 qz188 209000 4000 0 1 35641182568595101 9007199254740992 500000001470579 267378000000000000000

noncomputable def ep996 := @ep992 104500000307351011 1069512000000000000000 ep993 7545333079645984125 36028797018963968 55750000154143417 534756000000000000000 (@ep994 6020370175600501 2251799813685248 7000000000935823 1069512000000000000000 (ep977 qz192) ep990 rfl) (@ep995 7449007156836376109 36028797018963968 104500000307351011 1069512000000000000000 (ep989 qz192) ep987 rfl) rfl

noncomputable def ep997 := @Enclosure.Complex.IsNear.of_eq qz183 (Complex.mk qz102 qz191) Bool.false 9000 4000 0 1 Bool.false 209000 4000 0 1 (BSN.w_shift_mk qz152 Bool.false 104500 1000 2 qz153 rfl)

noncomputable abbrev qz478 := (ep997 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 9000 4000) (Enclosure.sfrac Bool.false 209000 4000) Bool.false 9000 4000 0 1 Bool.false 209000 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 9000 4000) (Enclosure.Real.IsNear.const Bool.false 209000 4000)))

noncomputable abbrev qz193 := qz478

noncomputable def ep998 := ep972 (@ep973 534756000000000000000 (ep991 rfl) (ep996 rfl)) qz193 rfl rfl rfl rfl rfl rfl

noncomputable def ep999 := @ep970 55750000154143417 534756000000000000000 (ep998 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@Enclosure.Complex.IsNear.mul qz108 (↑qz2) Bool.false 120447 131072 3 1048576 Bool.false 0 1 0 1 (@ep466 131072 3 1048576 (ep468 rfl) (ep470 rfl) rfl rfl) (@ep471 1 0 1 (ep473 rfl) (ep475 rfl) rfl rfl))

noncomputable abbrev qz479 := (@HPow.hPow Complex Int Complex qz577 qz594 (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) (@OfNat.ofNat Int 1 (@instOfNat 1)) (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (@OfNat.ofNat Int 2 (@instOfNat 2)) (@Nat.cast Int instNatCastInt 1))))

noncomputable abbrev qz194 := qz479

noncomputable def ep1000 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz89 2 k))) (@HMul.hMul Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz81 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz82 (@HMul.hMul Complex Complex Complex qz81 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz90 qz183 (@HSub.hSub Int Int Int qz404 qz92 (@HMul.hMul Int Int Int qz405 qz93 (@Nat.cast Int instNatCastInt k))))) (@HAdd.hAdd Complex Complex Complex qz4 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz89 2 k))) (@HMul.hMul Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz81 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz82 (@HMul.hMul Complex Complex Complex qz81 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz90 qz183 (@HSub.hSub Int Int Int qz404 qz92 (@HMul.hMul Int Int Int qz405 qz93 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 (@Rat.cast Complex Complex.instRatCast (bernoulli qz110)) qz111) qz194)) Bool.false 2355453 34359738368 3 34359738368

noncomputable def ep1001 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz89 2 k))) (@HMul.hMul Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz81 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz82 (@HMul.hMul Complex Complex Complex qz81 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz90 qz183 (@HSub.hSub Int Int Int qz404 qz92 (@HMul.hMul Int Int Int qz405 qz93 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 (@Rat.cast Complex Complex.instRatCast (bernoulli qz110)) qz111) qz194) Bool.false 0 1 0 1 Bool.false

noncomputable def ep1002 := @ep1001 0 1 0 1 Bool.false 2355453 34359738368 3 34359738368 Bool.true 54698853 34359738368 209 103079215104 Bool.false 2355453 2355453 34359738368 3 34359738368 Bool.true 54698853 54698853 34359738368 209

noncomputable def ep1003 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz89 2 k))) (@HMul.hMul Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz81 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz82 (@HMul.hMul Complex Complex Complex qz81 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz90 qz183 (@HSub.hSub Int Int Int qz404 qz92 (@HMul.hMul Int Int Int qz405 qz93 (@Nat.cast Int instNatCastInt k))))) (Complex.mk qz10 qz10) Bool.false 0 1 0 1 Bool.false

noncomputable def ep1004 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz88 (@Rat.cast Complex Complex.instRatCast (bernoulli qz110)) qz111) qz194 Bool.false 2355453 34359738368 3 34359738368 Bool.true 54698853 34359738368 209 103079215104

noncomputable abbrev qz195 := (Complex.re qz479)

noncomputable abbrev qz196 := (Complex.im qz479)

noncomputable def ep1005 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz88 (@Rat.cast Complex Complex.instRatCast (bernoulli qz110)) qz111)) qz195) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz88 (@Rat.cast Complex Complex.instRatCast (bernoulli qz110)) qz111)) qz196) 2355453 34359738368 3 34359738368 0 1 0

noncomputable def ep1006 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz88 (@Rat.cast Complex Complex.instRatCast (bernoulli qz110)) qz111)) qz195 1 12 0 1 7066359 8589934592 9 8589934592 2355453

noncomputable def ep1007 := @Enclosure.Complex.IsNear.re_isNear qz194 Bool.false 7066359 8589934592 9 8589934592 Bool.true 164096559 8589934592 209 8589934592

noncomputable abbrev qz480 := (@HPow.hPow Complex Nat Complex qz579 qz594 1)

noncomputable abbrev qz197 := (@Inv.inv Complex Complex.instInv qz480)

noncomputable def ep1008 := @Enclosure.Complex.IsNear.of_eq qz194 qz197 Bool.false 7066359 8589934592 9 8589934592 Bool.true 164096559 8589934592 209

noncomputable def ep1009 := @Enclosure.Complex.IsNear.of_parts qz197 Bool.false 7066359 8589934592 9 8589934592 Bool.true 164096559 8589934592 209

noncomputable abbrev qz198 := (Complex.re qz480)

noncomputable abbrev qz199 := qz480

noncomputable def ep1010 := @Enclosure.Real.IsNear.mulLit_ff qz198 (@Inv.inv Real Real.instInv (@DFunLike.coe qz117 Complex (fun (x : Complex) => Real) qz118 Complex.normSq qz199)) 9000 4000 0 1 785151 2147483648 1 2147483648

noncomputable def ep1011 := @Enclosure.Complex.IsNear.re_isNear qz199 Bool.false 9000 4000 0 1 Bool.false 209000 4000 0 1

noncomputable def ep1012 := @Enclosure.Complex.IsNear.of_eq qz199 qz183 Bool.false 9000 4000 0 1 Bool.false 209000 4000 0

noncomputable def ep1013 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (@DFunLike.coe qz117 Complex (fun (x : Complex) => Real) qz118 Complex.normSq qz199)) Bool.false 785151 2147483648 1 2147483648 785151 2147483648 1

noncomputable abbrev qz200 := (Complex.im qz480)

noncomputable def ep1014 := @Enclosure.Real.IsNear.of_eq (@DFunLike.coe qz117 Complex (fun (x : Complex) => Real) qz118 Complex.normSq qz199) (@HAdd.hAdd Real Real Real qz417 (@HMul.hMul Real Real Real qz0 qz198 qz198) (@HMul.hMul Real Real Real qz0 qz200 qz200)) Bool.false 21881 8 0 1

noncomputable def ep1015 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz198 qz198) (@HMul.hMul Real Real Real qz0 qz200 qz200) 81 16 0 1 43681 16

noncomputable def ep1016 := @Enclosure.Real.IsNear.mulLit_ff qz198 qz198 9000 4000 0 1 9000 4000 0 1

noncomputable def ep1017 := @Enclosure.Real.IsNear.mulLit_ff qz200 qz200 209000 4000 0 1 209000 4000 0 1

noncomputable def ep1018 := @Enclosure.Complex.IsNear.im_isNear qz199 Bool.false 9000 4000 0 1 Bool.false 209000 4000 0 1

noncomputable abbrev qz201 := (ep1011 (@ep1012 1 (BSN.pow_one_c qz470) qz478))

noncomputable abbrev qz202 := (ep1018 (@ep1012 1 (BSN.pow_one_c qz470) qz478))

noncomputable def ep1019 := @ep1015 0 1 700192 21881 8 0 1 (@ep1016 81 16 0 1 qz201 qz201 rfl) (@ep1017 43681 16 0 1 qz202 qz202 rfl)

noncomputable def ep1020 := @Enclosure.Real.IsNear.inv_image (@DFunLike.coe qz117 Complex (fun (x : Complex) => Real) qz118 Complex.normSq qz199) 21881 8 0 1 392575 392576 1073741824 (ep1014 (Enclosure.Complex.normSq_eq_mul_add_mul qz199) (ep1019 rfl rfl)) rfl

noncomputable def ep1021 := @Enclosure.Real.IsNear.of_eq (Complex.re qz197) (@HMul.hMul Real Real Real qz0 qz198 (@Inv.inv Real Real.instInv (@DFunLike.coe qz117 Complex (fun (x : Complex) => Real) qz118 Complex.normSq qz199))) Bool.false 7066359 8589934592 9 8589934592 (Enclosure.Complex.inv_re_eq_mul qz199) (@ep1010 7066359 8589934592 9 8589934592 qz201 (@ep1013 2147483648 (ep1020 rfl rfl rfl rfl rfl) rfl) rfl)

noncomputable def ep1022 := @Enclosure.Real.IsNear.of_eq (Complex.im qz197) (@HMul.hMul Real Real Real qz0 (@Neg.neg Real Real.instNeg qz200) (@Inv.inv Real Real.instInv (@DFunLike.coe qz117 Complex (fun (x : Complex) => Real) qz118 Complex.normSq qz199))) Bool.true 164096559 8589934592 209 8589934592 (Enclosure.Complex.inv_im_eq_mul qz199)

noncomputable def ep1023 := @Enclosure.Real.IsNear.mulLit_tf (@Neg.neg Real Real.instNeg qz200) (@Inv.inv Real Real.instInv (@DFunLike.coe qz117 Complex (fun (x : Complex) => Real) qz118 Complex.normSq qz199)) 209000 4000 0 1 785151 2147483648 1

noncomputable def ep1024 := @ep1023 2147483648 164096559 8589934592 209 8589934592 (@Enclosure.Real.IsNear.neg qz200 Bool.false 209000 4000 0 1 qz202) (@ep1013 2147483648 (ep1020 rfl rfl rfl rfl rfl) rfl) rfl

noncomputable def ep1025 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz88 (@Rat.cast Complex Complex.instRatCast (bernoulli qz110)) qz111)) qz196 0 1 0 1 164096559 8589934592 209 8589934592 0

noncomputable def ep1026 := @Enclosure.Complex.IsNear.im_isNear qz194 Bool.false 7066359 8589934592 9 8589934592 Bool.true 164096559 8589934592 209 8589934592

noncomputable abbrev qz203 := (@ep1008 8589934592 (BSN.zpow_one_sub_two_mul qz470 1 1 rfl rfl) (@ep1009 8589934592 ep1021 (ep1022 ep1024)))

noncomputable def ep1027 := @ep1005 1 2355453 2355453 34359738368 3 34359738368 (@ep1006 34359738368 3 34359738368 ep485 (ep1007 qz203) rfl) (@ep1025 1 0 1 ep505 (ep1026 qz203) rfl) rfl

noncomputable def ep1028 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz88 (@Rat.cast Complex Complex.instRatCast (bernoulli qz110)) qz111)) qz196) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz88 (@Rat.cast Complex Complex.instRatCast (bernoulli qz110)) qz111)) qz195) 54698853 34359738368 209 103079215104 0 1 0

noncomputable def ep1029 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HDiv.hDiv Complex Complex Complex qz88 (@Rat.cast Complex Complex.instRatCast (bernoulli qz110)) qz111)) qz196 1 12 0 1 164096559 8589934592 209 8589934592 54698853

noncomputable def ep1030 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz88 (@Rat.cast Complex Complex.instRatCast (bernoulli qz110)) qz111)) qz195 0 1 0 1 7066359 8589934592 9 8589934592 0

noncomputable def ep1031 := @ep1028 1 54698853 54698853 34359738368 209 103079215104 (@ep1029 34359738368 209 103079215104 ep485 (ep1026 qz203) rfl) (@ep1030 1 0 1 ep505 (ep1007 qz203) rfl) rfl

noncomputable def ep1032 := @ep1002 103079215104 (@ep1003 0 1 0 1 (BSN.stirling_sum_base qz183) qz124) (ep1004 (ep1027 rfl) (ep1031 rfl)) rfl rfl rfl rfl rfl

noncomputable def ep1033 := @ep968 5662771079500633469 36028797018963968 14614812270968074640423 ep959 (ep999 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep1000 Bool.true 54698853 34359738368 209 103079215104 (BSN.stirling_sum_succ qz183 0 1 rfl) (ep1032 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl

noncomputable def ep1034 := @Enclosure.Complex.IsNear.of_eq (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz180 (@Nat.cast Complex Complex.instNatCast j))) (BSN.logSumC qz152 2) Bool.false 35634177476935325 4503599627370496 500000001470579 133689000000000000000 Bool.false 876200617084323 281474976710656

noncomputable abbrev qz204 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz273 qz471 qz413))

noncomputable def ep1035 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz152 2) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.logSumC qz152 1) qz204) Bool.false 35634177476935325 4503599627370496 500000001470579 133689000000000000000 Bool.false 876200617084323 281474976710656 1000000000133689 133689000000000000000

noncomputable def ep1036 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz152 1) qz204 Bool.false 35632940526354077 9007199254740992 500000001470579 267378000000000000000 Bool.false 881586237638051 562949953421312 1000000000133689 267378000000000000000 Bool.false

noncomputable def ep1037 := nat_lit 641928273627120203966473620684800

noncomputable def ep1038 := nat_lit 986514193150688928543698583552

noncomputable abbrev qz205 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz273 qz471 (@Nat.cast Complex Complex.instNatCast 0)))

noncomputable def ep1039 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz152 1) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.logSumC qz152 0) qz205) Bool.false 35632940526354077 9007199254740992 500000001470579 267378000000000000000 Bool.false 881586237638051 562949953421312 1000000000133689 267378000000000000000

noncomputable def ep1040 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz152 0) qz205 Bool.false 0 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable abbrev qz481 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz191))

noncomputable def ep1041 := @Enclosure.Complex.IsNear.of_eq qz205 qz481 Bool.false 35632940526354077 9007199254740992 500000001470579 267378000000000000000 Bool.false 881586237638051 562949953421312 1000000000133689 267378000000000000000

noncomputable def ep1042 := nat_lit 20963038771055250057890625000000000000000000000000000000000000000000

noncomputable def ep1043 := nat_lit 144178573144358318142607727040000000000000000000000000000000000000

noncomputable def ep1044 := nat_lit 25350991855517756634287040000000000000000000000000000000000000

noncomputable def ep1045 := BSN.log_dyadic_bound 10914000000 76450000000 4 3 ep1042 1048576 267378 ep1043 ep1044 301448 87364000000 65536000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 10914000000) (BSN.artanhQ 76450000000) 0 3 ep1043 ep1042 ep1044 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep1046 := @Enclosure.Real.IsNear.mulLit_ff qz103 (Real.log (Enclosure.sfrac Bool.false 43682000000 16000000)) 1 2 0 1 35632940526354077 4503599627370496 500000001470579 133689000000000000000 35632940526354077 9007199254740992 500000001470579 267378000000000000000 qz408 (BSN.isNear_log_sfrac 43682000000 16000000 35632940526354077 4503599627370496 500000001470579 133689000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 43682000000) qz409)) Bool.false 298910769962898021154816 37778931862957161709568 1000000002941158 267378000000000000000 35632940526354077 4503599627370496 500000001470579 133689000000000000000 (BSN.log_rat_reduce_isNear 43682000000 16000000 11 87364000000 65536000000 301448 1048576 24973259072661432 36028797018963968 267378 1000000000000000 rfl rfl rfl rfl (ep1045 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1047 := BSN.arctan_dyadic_bound_f 1000 209000 1 0 1048576 267378 0 1 1 0 1 1 5017 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 209000) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 209000) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz482 := (@Nat.cast Real Real.instNatCast 209000)

noncomputable def ep1048 := @Enclosure.Real.IsNear.subLit_ff_p qz104 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz419 qz482)) 884279719003555 562949953421312 1 2000000000000000 5017 1048576 1 267378 924410170717556965376 881586237638051 562949953421312 1000000000133689 267378000000000000000 qz105 (ep1047 rfl) rfl rfl

noncomputable abbrev qz206 := (@HAdd.hAdd Complex Complex Complex qz273 qz471 (@Nat.cast Complex Complex.instNatCast 0))

noncomputable abbrev qz483 := (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz191)

noncomputable def ep1049 := @ep1040 35632940526354077 9007199254740992 500000001470579 267378000000000000000 Bool.false 881586237638051 562949953421312 1000000000133689 267378000000000000000 Bool.false 35632940526354077 35632940526354077 9007199254740992 500000001470579 267378000000000000000 Bool.false 881586237638051 881586237638051 562949953421312 1000000000133689 267378000000000000000 (@Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz152 0) (Complex.mk qz10 qz10) Bool.false 0 1 0 1 Bool.false 0 1 0 1 (BSN.log_sum_c_base qz152) qz124) (ep1041 (@congrArg Complex Complex qz206 qz483 Complex.log (BSN.w_shift_mk qz152 Bool.false 104500 1000 0 qz153 rfl)) (@Enclosure.Complex.IsNear.of_parts qz481 Bool.false 35632940526354077 9007199254740992 500000001470579 267378000000000000000 Bool.false 881586237638051 562949953421312 1000000000133689 267378000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz481) (@HMul.hMul Real Real Real qz0 qz103 (Real.log (Enclosure.sfrac Bool.false 43682000000 16000000))) Bool.false 35632940526354077 9007199254740992 500000001470579 267378000000000000000 (Enclosure.clog_re_eq 1000 209000 4000 43682000000 16000000 rfl rfl rfl) (ep1046 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz481) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz482 qz419)) Bool.false 881586237638051 562949953421312 1000000000133689 267378000000000000000 (Enclosure.clog_im_eq 1000 209000 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz482 qz419)) (@HSub.hSub Real Real Real qz395 qz104 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz419 qz482))) Bool.false 881586237638051 562949953421312 1000000000133689 267378000000000000000 (BSN.arctan_recip 209000 1000 rfl rfl) ep1048)))) rfl rfl

noncomputable abbrev qz484 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz191))

noncomputable def ep1050 := @Enclosure.Complex.IsNear.of_eq qz204 qz484 Bool.false 35635414427516573 9007199254740992 500000001470579 267378000000000000000 Bool.false 870814996530595 562949953421312 1000000000133689 267378000000000000000

noncomputable def ep1051 := nat_lit 21002555418715730998288219836480000000000000000000000000000000000000

noncomputable def ep1052 := nat_lit 145002101392198585388360350656000000000000000000000000000000000000

noncomputable def ep1053 := nat_lit 25687318657909228099853760000000000000000000000000000000000000

noncomputable def ep1054 := BSN.log_dyadic_bound 10938000000 76474000000 4 3 ep1051 1048576 267378 ep1052 ep1053 302024 87412000000 65536000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 10938000000) (BSN.artanhQ 76474000000) 0 3 ep1052 ep1051 ep1053 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep1055 := @Enclosure.Real.IsNear.mulLit_ff qz103 (Real.log (Enclosure.sfrac Bool.false 43706000000 16000000)) 1 2 0 1 35635414427516573 4503599627370496 500000001470579 133689000000000000000 35635414427516573 9007199254740992 500000001470579 267378000000000000000 qz408 (BSN.isNear_log_sfrac 43706000000 16000000 35635414427516573 4503599627370496 500000001470579 133689000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 43706000000) qz409)) Bool.false 298931522549980944400384 37778931862957161709568 1000000002941158 267378000000000000000 35635414427516573 4503599627370496 500000001470579 133689000000000000000 (BSN.log_rat_reduce_isNear 43706000000 16000000 11 87412000000 65536000000 302024 1048576 24973259072661432 36028797018963968 267378 1000000000000000 rfl rfl rfl rfl (ep1054 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1056 := BSN.arctan_dyadic_bound_f 5000 209000 1 0 1048576 267378 0 1 1 0 1 1 25080 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 5000) (BSN.arctanEvenQ 209000) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 5000) (BSN.arctanOddQ 209000) 0 0 rfl) rfl rfl rfl

noncomputable def ep1057 := @Enclosure.Real.IsNear.subLit_ff_p qz104 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz423 qz482)) 884279719003555 562949953421312 1 2000000000000000 25080 1048576 1 267378 913115705802065182720 870814996530595 562949953421312 1000000000133689 267378000000000000000 qz105 (ep1056 rfl) rfl rfl

noncomputable abbrev qz207 := (@HAdd.hAdd Complex Complex Complex qz273 qz471 qz413)

noncomputable abbrev qz485 := (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz191)

noncomputable def ep1058 := @ep1036 35635414427516573 9007199254740992 500000001470579 267378000000000000000 Bool.false 870814996530595 562949953421312 1000000000133689 267378000000000000000 Bool.false ep1037 35634177476935325 4503599627370496 500000001470579 133689000000000000000 Bool.false ep1038 876200617084323 281474976710656 1000000000133689 133689000000000000000 (ep1039 (BSN.log_sum_c_succ qz152 0 1 rfl) (ep1049 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1050 (@congrArg Complex Complex qz207 qz485 Complex.log (BSN.w_shift_mk qz152 Bool.false 104500 1000 1 qz153 rfl)) (@Enclosure.Complex.IsNear.of_parts qz484 Bool.false 35635414427516573 9007199254740992 500000001470579 267378000000000000000 Bool.false 870814996530595 562949953421312 1000000000133689 267378000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz484) (@HMul.hMul Real Real Real qz0 qz103 (Real.log (Enclosure.sfrac Bool.false 43706000000 16000000))) Bool.false 35635414427516573 9007199254740992 500000001470579 267378000000000000000 (Enclosure.clog_re_eq 5000 209000 4000 43706000000 16000000 rfl rfl rfl) (ep1055 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz484) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz482 qz423)) Bool.false 870814996530595 562949953421312 1000000000133689 267378000000000000000 (Enclosure.clog_im_eq 5000 209000 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz482 qz423)) (@HSub.hSub Real Real Real qz395 qz104 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz423 qz482))) Bool.false 870814996530595 562949953421312 1000000000133689 267378000000000000000 (BSN.arctan_recip 209000 5000 rfl rfl) ep1057)))) rfl rfl

noncomputable def ep1059 := @ep961 ep959 Bool.false 35634177476935325 4503599627370496 500000001470579 133689000000000000000 Bool.false 876200617084323 281474976710656 1000000000133689 133689000000000000000 Bool.true ep962 2959556084171399117 36028797018963968 28778167246147064702767 ep959 Bool.false ep963 5550617400513840125 36028797018963968 5221129423702752572429 ep956 (@ep964 36028797018963968 28253879244605050857263 ep959 Bool.false 5662771079500633469 36028797018963968 14614812270968074640423 ep959 (BSN.logGammaStirling_unfold 1 qz183) (ep1033 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (@ep1034 1000000000133689 133689000000000000000 (BSN.log_sum_c_eq qz152 2) (ep1035 (BSN.log_sum_c_succ qz152 1 2 rfl) (ep1058 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)))

noncomputable abbrev qz208 := (@HDiv.hDiv Real Real Real qz271 qz441 (2 : Real))

noncomputable def ep1060 := @Enclosure.Real.IsNear.mulLit_ff qz208 (Real.log Real.pi) 104500 2000 0 1 75021 65536 1 262144 15679389 262144 209 1048576 (@Enclosure.Real.IsNear.of_eq qz208 (Enclosure.sfrac Bool.false 104500 2000) Bool.false 104500 2000 0 1 (BSN.t_half_eq qz152 Bool.false 104500 1000 qz153) (Enclosure.Real.IsNear.const Bool.false 104500 2000)) EMRow31.d5 rfl

noncomputable def ep1061 := @ep958 209 1048576 890151524177923674472448 3395658585273451517 36028797018963968 14534796423702752572429 ep956 (@ep960 5221129423702752572429 ep956 (ep1059 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) ep1060 rfl rfl

noncomputable def ep1062 := BSN.cos_dyadic_bound_f 1456640 2147483648 1 0 1048576 267640 0 1 1 0 1 1 1048575 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 1456640) qz292 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 1456640) qz293 0 0 rfl) rfl rfl

noncomputable def ep1063 := @ep955 1048576 Bool.false 1048575 1048576 1 133689 (@ep957 98826671 1048576 327 1048576 ep1061 rfl) (Enclosure.sfrac_false_div 98826671 1048576) (BSN.cos_reduce0 qz472 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 102501939462182797312) qz27) 226375608064910080 72057594037927936 Bool.false 1048575 1048576 15 1000000000000000 267378 133689 (BSN.sin_reduce_arg_pos_rat_q0 98826671 1048576 226375608064910080 72057594037927936 15 102501939462182797312 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1048575 1048576 102501939462182797312 151115727451828646838272 1456640 2147483648 267640 267378 (ep1062 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz486 := (@HPow.hPow Complex Complex Complex qz535 (@Nat.cast Complex Complex.instNatCast 27) qz583)

noncomputable abbrev qz209 := qz486

noncomputable abbrev qz487 := (@Nat.cast Complex Complex.instNatCast 27)

noncomputable abbrev qz210 := (@HAdd.hAdd Complex Complex Complex qz273 (@HDiv.hDiv Complex Complex Complex qz400 qz487 (@HSub.hSub Complex Complex Complex qz392 qz439 (1 : Complex))) qz399)

noncomputable abbrev qz211 := qz487

noncomputable def ep1064 := @Enclosure.Complex.IsNear.of_eq (zetaApproximant qz149 1 27) (@HAdd.hAdd Complex Complex Complex qz4 (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 27, @HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast n) qz150) (@HMul.hMul Complex Complex Complex qz81 qz209 (@HAdd.hAdd Complex Complex Complex qz4 qz210 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz89 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz89 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz132 (@HMul.hMul Nat Nat Nat qz89 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz133 qz211 (@HSub.hSub Nat Nat Nat qz132 (@HMul.hMul Nat Nat Nat qz89 2 k) 1))))))) Bool.false 16153984513672747997 15561352883541639168 4361887927095848709245

noncomputable def ep1065 := @Enclosure.Complex.IsNear.addLitP (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 27, @HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast n) qz150) (@HMul.hMul Complex Complex Complex qz81 qz209 (@HAdd.hAdd Complex Complex Complex qz4 qz210 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz89 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz89 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz132 (@HMul.hMul Nat Nat Nat qz89 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz133 qz211 (@HSub.hSub Nat Nat Nat qz132 (@HMul.hMul Nat Nat Nat qz89 2 k) 1)))))) Bool.false 1111595412131 1099511627776 911944884642377 146992610005745664

noncomputable def ep1066 := nat_lit 17761493807696618878352513564672

noncomputable def ep1067 := nat_lit 1985467480259166863519383552

noncomputable def ep1068 := @ep1065 Bool.true 29067754757 274877906944 227971289536451 36748152501436416 Bool.false 421610216835893189 15561352883541639168 59645670393431000933 693460568549266066243584 Bool.false 53724319222820519 576346403094134784 59795071657208166881 693460568549266066243584 Bool.false ep1066 16153984513672747997 15561352883541639168 4361887927095848709245 693460568549266066243584 Bool.true ep1067 7223088615352633 576346403094134784

noncomputable def ep1069 := @Enclosure.Complex.IsNear.of_eq (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 27, @HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast n) qz150) (BSN.headSumC qz149 27) Bool.false 1111595412131 1099511627776 911944884642377 146992610005745664 Bool.true 29067754757 274877906944 227971289536451

noncomputable def ep1070 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz149 27) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz149 26) (@HPow.hPow Complex Complex Complex qz6 qz134 qz150)) Bool.false 1111595412131 1099511627776 911944884642377 146992610005745664 Bool.true 29067754757 274877906944 227971289536451 36748152501436416

noncomputable def ep1071 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz149 26) (@HPow.hPow Complex Complex Complex qz6 qz134 qz150) Bool.false 128654500945 137438953472 55570749365555 9187038125359104 Bool.false 41506544063 549755813888 444498125163499 73496305002872832 Bool.false

noncomputable def ep1072 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz149 26) (@HAdd.hAdd Complex Complex Complex qz4 qz170 (@HPow.hPow Complex Complex Complex qz6 qz428 qz150)) Bool.false 128654500945 137438953472 55570749365555 9187038125359104 Bool.false 41506544063 549755813888 444498125163499 73496305002872832

noncomputable def ep1073 := @Enclosure.Complex.IsNear.addLitP qz170 (@HPow.hPow Complex Complex Complex qz6 qz428 qz150) Bool.false 621872755945 549755813888 432892614490433 73496305002872832 Bool.false 8653240819 274877906944 54109711298287 9187038125359104 Bool.true

noncomputable abbrev qz212 := (@HMul.hMul Real Real Real qz268 qz441 qz580)

noncomputable def ep1074 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz428 qz150) (Complex.mk (@HMul.hMul Real Real Real qz0 qz135 (Real.cos qz212)) (@HMul.hMul Real Real Real qz0 qz135 (@Neg.neg Real Real.instNeg (Real.sin qz212)))) Bool.true 107254752165 549755813888 11673380434007 73496305002872832 Bool.false 24200062425 549755813888 11620434777203 73496305002872832 (BSN.cpow_neg_s_mk qz152 104500 1000 25 qz153 rfl)

noncomputable def ep1075 := @Enclosure.Real.IsNear.mulLit_ff qz152 qz580 104500 1000 0 1 3624129903009015 1125899906842624 250000000133689 33422250000000000000 757443149728884135 2251799813685248 52250000027941001 66844500000000000000 qz154 (BSN.isNear_log_sfrac 25 1 3624129903009015 1125899906842624 250000000133689 33422250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz430) Bool.false 60802810194841294602240 18889465931478580854784 1000000000534756 133689000000000000000 3624129903009015 1125899906842624 250000000133689 33422250000000000000 (BSN.log_rat_reduce_isNear 25 1 4 50 32 233982 524288 24973259072661432 36028797018963968 133689 1000000000000000 rfl rfl rfl rfl (ep561 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1076 := nat_lit 51578913024702645438012681883488256

noncomputable def ep1077 := BSN.cos_dyadic_bound_f 476560504 2147483648 2 1 1048576 267640 ep1076 ep62 ep1076 ep1076 ep63 ep1076 1022862 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 476560504) qz292 0 1 ep1076 ep62 ep1076 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 476560504) qz293 0 1 ep1076 ep63 ep1076 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz488 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 22044497) (@Nat.cast Real Real.instNatCast 65536))

noncomputable def ep1078 := @Enclosure.Real.IsNear.cos_image qz212 qz488 Bool.false 22044497 65536 205 262144 Bool.true 1022862 1048576 1 133689 (@Enclosure.Real.IsNear.recentre' qz212 Bool.false 757443149728884135 2251799813685248 52250000027941001 66844500000000000000 22044497 65536 205 262144 (ep1075 rfl) rfl) (Enclosure.sfrac_false_div 22044497 65536) (BSN.cos_reduce2 qz488 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 2095935262263884120064) qz291) 226375608064910080 72057594037927936 Bool.false 1022862 1048576 53 1000000000000000 267378 133689 (BSN.sin_reduce_arg_pos_rat_q2 22044497 65536 226375608064910080 72057594037927936 53 2095935262263884120064 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1022862 1048576 2095935262263884120064 9444732965739290427392 476560504 2147483648 267640 267378 (ep1077 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1079 := BSN.sin_dyadic_bound_f 476560504 2147483648 2 1 1048576 267640 ep1076 ep58 ep1076 ep1076 ep59 ep1076 230790 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 476560504) qz287 0 1 ep1076 ep58 ep1076 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 476560504) qz288 0 1 ep1076 ep59 ep1076 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1080 := @Enclosure.Real.IsNear.sin_image qz212 qz488 Bool.false 22044497 65536 205 262144 Bool.true 230790 1048576 1 133689 (@Enclosure.Real.IsNear.recentre' qz212 Bool.false 757443149728884135 2251799813685248 52250000027941001 66844500000000000000 22044497 65536 205 262144 (ep1075 rfl) rfl) (Enclosure.sfrac_false_div 22044497 65536) (BSN.sin_reduce2 qz488 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 2095935262263884120064) qz291) 226375608064910080 72057594037927936 Bool.false 230790 1048576 53 1000000000000000 267378 133689 (BSN.sin_reduce_arg_pos_rat_q2 22044497 65536 226375608064910080 72057594037927936 53 2095935262263884120064 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 230790 1048576 2095935262263884120064 9444732965739290427392 476560504 2147483648 267640 267378 (ep1079 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1081 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz135 (Real.cos qz212)) (@HMul.hMul Real Real Real qz0 qz135 (@Neg.neg Real Real.instNeg (Real.sin qz212))) Bool.true 107254752165 549755813888 11673380434007 73496305002872832 Bool.false 24200062425 549755813888 11620434777203 73496305002872832 (@Enclosure.Real.IsNear.mulLit_ft qz135 (Real.cos qz212) 209715 1048576 1 1048576 511431 524288 27668389 35045769216 107254752165 549755813888 11673380434007 73496305002872832 qz432 (@Enclosure.Real.IsNear.recentre' (Real.cos qz212) Bool.true 1022862 1048576 27668389 35045769216 511431 524288 27668389 35045769216 (ep1078 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz135 (@Neg.neg Real Real.instNeg (Real.sin qz212)) 209715 1048576 1 1048576 115395 524288 27668389 35045769216 24200062425 549755813888 11620434777203 73496305002872832 qz432 (@Enclosure.Real.IsNear.neg (Real.sin qz212) Bool.true 115395 524288 27668389 35045769216 (@Enclosure.Real.IsNear.recentre' (Real.sin qz212) Bool.true 230790 1048576 27668389 35045769216 115395 524288 27668389 35045769216 (ep1080 rfl rfl) rfl)) rfl)

noncomputable def ep1082 := @ep1073 107254752165 549755813888 11673380434007 73496305002872832 Bool.false 24200062425 549755813888 11620434777203 73496305002872832 Bool.false 282914239509491760496640 128654500945 137438953472 55570749365555 9187038125359104 Bool.false 11409231956516349673472 41506544063 549755813888 444498125163499 73496305002872832 EMRow31.d14 (ep1074 ep1081) rfl rfl

noncomputable abbrev qz213 := (@HMul.hMul Real Real Real qz268 qz441 (Real.log (Enclosure.sfrac Bool.false 26 1)))

noncomputable def ep1083 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz134 qz150) (Complex.mk (@HMul.hMul Real Real Real qz0 qz139 (Real.cos qz213)) (@HMul.hMul Real Real Real qz0 qz139 (@Neg.neg Real Real.instNeg (Real.sin qz213)))) Bool.false 82359404571 1099511627776 7604298264499 48997536668581888 Bool.true 99642053577 549755813888 3814817969801 24498768334290944 (BSN.cpow_neg_s_mk qz152 104500 1000 26 qz153 rfl)

noncomputable def ep1084 := @Enclosure.Real.IsNear.mulLit_ff qz152 qz142 104500 1000 0 1 3668288609262839 1125899906842624 250000000133689 33422250000000000000 766672319335933351 2251799813685248 52250000027941001 66844500000000000000 qz154 (BSN.isNear_log_sfrac 26 1 3668288609262839 1125899906842624 250000000133689 33422250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz435) Bool.false 61543670347942250676224 18889465931478580854784 1000000000534756 133689000000000000000 3668288609262839 1125899906842624 250000000133689 33422250000000000000 (BSN.log_rat_reduce_isNear 26 1 4 52 32 254545 524288 24973259072661432 36028797018963968 133689 1000000000000000 rfl rfl rfl rfl (ep583 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1085 := nat_lit 1469439850686578641613916720625900456943751856371924321443587355539055312383521

noncomputable def ep1086 := nat_lit 1687516668223566505774422680123140649172351701993203882485036277528023019041

noncomputable def ep1087 := nat_lit 4404944518723288791830201316517455089532910865711786556565791994062109891112481

noncomputable def ep1088 := BSN.cos_dyadic_bound_f 2531663667 2147483648 3 2 1048576 267640 ep1085 ep75 ep1086 ep1087 ep78 ep1086 400497 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2531663667) qz292 0 2 ep1085 ep75 ep1086 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2531663667) qz293 0 2 ep1087 ep78 ep1086 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz489 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 357009619) qz26)

noncomputable def ep1089 := @Enclosure.Real.IsNear.cos_image qz213 qz489 Bool.false 357009619 1048576 205 262144 Bool.false 400497 1048576 1 133689 (@Enclosure.Real.IsNear.recentre' qz213 Bool.false 766672319335933351 2251799813685248 52250000027941001 66844500000000000000 357009619 1048576 205 262144 (ep1084 rfl) rfl) (Enclosure.sfrac_false_div 357009619 1048576) (BSN.cos_reduce0 qz489 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 178149992984079119679488) qz27) 226375608064910080 72057594037927936 Bool.false 400497 1048576 54 1000000000000000 267378 133689 (BSN.sin_reduce_arg_pos_rat_q0 357009619 1048576 226375608064910080 72057594037927936 54 178149992984079119679488 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 400497 1048576 178149992984079119679488 151115727451828646838272 2531663667 2147483648 267640 267378 (ep1088 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1090 := nat_lit 2643641717901262701700430558982522309979415460107869215492469210948277143875105

noncomputable def ep1091 := nat_lit 6921091377040468920587016684424501917466475730860239900956253112796156672880161

noncomputable def ep1092 := BSN.sin_dyadic_bound_f 2531663667 2147483648 3 2 1048576 267640 ep1090 ep108 ep1086 ep1091 ep110 ep1086 969078 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2531663667) qz287 0 2 ep1090 ep108 ep1086 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2531663667) qz288 0 2 ep1091 ep110 ep1086 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1093 := @Enclosure.Real.IsNear.sin_image qz213 qz489 Bool.false 357009619 1048576 205 262144 Bool.false 969078 1048576 1 133689 (@Enclosure.Real.IsNear.recentre' qz213 Bool.false 766672319335933351 2251799813685248 52250000027941001 66844500000000000000 357009619 1048576 205 262144 (ep1084 rfl) rfl) (Enclosure.sfrac_false_div 357009619 1048576) (BSN.sin_reduce0 qz489 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 178149992984079119679488) qz27) 226375608064910080 72057594037927936 Bool.false 969078 1048576 54 1000000000000000 267378 133689 (BSN.sin_reduce_arg_pos_rat_q0 357009619 1048576 226375608064910080 72057594037927936 54 178149992984079119679488 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 969078 1048576 178149992984079119679488 151115727451828646838272 2531663667 2147483648 267640 267378 (ep1092 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1094 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz139 (Real.cos qz213)) (@HMul.hMul Real Real Real qz0 qz139 (@Neg.neg Real Real.instNeg (Real.sin qz213))) Bool.false 82359404571 1099511627776 7604298264499 48997536668581888 Bool.true 99642053577 549755813888 3814817969801 24498768334290944 (@Enclosure.Real.IsNear.mulLit_ff qz139 (Real.cos qz213) 205643 1048576 1 1048576 400497 1048576 27668389 35045769216 82359404571 1099511627776 7604298264499 48997536668581888 qz437 (@Enclosure.Real.IsNear.recentre' (Real.cos qz213) Bool.false 400497 1048576 27668389 35045769216 400497 1048576 27668389 35045769216 (ep1089 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz139 (@Neg.neg Real Real.instNeg (Real.sin qz213)) 205643 1048576 1 1048576 484539 524288 27668389 35045769216 99642053577 549755813888 3814817969801 24498768334290944 qz437 (@Enclosure.Real.IsNear.neg (Real.sin qz213) Bool.false 484539 524288 27668389 35045769216 (@Enclosure.Real.IsNear.recentre' (Real.sin qz213) Bool.false 969078 1048576 27668389 35045769216 484539 524288 27668389 35045769216 (ep1093 rfl rfl) rfl)) rfl)

noncomputable def ep1095 := @ep1071 82359404571 1099511627776 7604298264499 48997536668581888 Bool.true 99642053577 549755813888 3814817969801 24498768334290944 Bool.false 152776510127561173368832 1111595412131 1099511627776 911944884642377 146992610005745664 Bool.true 31960334348662637330432 29067754757 274877906944 227971289536451 36748152501436416 (ep1072 (BSN.head_sum_c_succ qz149 25 26 rfl rfl) (ep1082 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1083 ep1094) rfl rfl

noncomputable def ep1096 := @Enclosure.Complex.IsNear.mul qz209 (@HAdd.hAdd Complex Complex Complex qz4 qz210 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz89 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz89 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz132 (@HMul.hMul Nat Nat Nat qz89 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz133 qz211 (@HSub.hSub Nat Nat Nat qz132 (@HMul.hMul Nat Nat Nat qz89 2 k) 1))))) Bool.false 421610216835893189 15561352883541639168 59645670393431000933 693460568549266066243584 Bool.false

noncomputable abbrev qz214 := (Complex.re qz486)

noncomputable abbrev qz215 := (Complex.im qz486)

noncomputable def ep1097 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 qz214 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz210 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz89 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz89 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz132 (@HMul.hMul Nat Nat Nat qz89 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz133 qz211 (@HSub.hSub Nat Nat Nat qz132 (@HMul.hMul Nat Nat Nat qz89 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz215 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz210 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz89 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz89 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz132 (@HMul.hMul Nat Nat Nat qz89 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz133 qz211 (@HSub.hSub Nat Nat Nat qz132 (@HMul.hMul Nat Nat Nat qz89 2 k) 1))))))) 597809226007073899 15561352883541639168 158538734122750599989

noncomputable def ep1098 := nat_lit 2080381705647798198730752

noncomputable def ep1099 := nat_lit 3280412681744921110796253333213413376

noncomputable def ep1100 := @Enclosure.Real.IsNear.mulLit_ff qz214 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz210 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz89 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz89 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz132 (@HMul.hMul Nat Nat Nat qz89 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz133 qz211 (@HSub.hSub Nat Nat Nat qz132 (@HMul.hMul Nat Nat Nat qz89 2 k) 1)))))) 84426445831 1099511627776 22389854934041 146992610005745664 7080829

noncomputable abbrev qz490 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) qz584 (Real.log (Enclosure.sfrac Bool.false 27 1)))

noncomputable abbrev qz216 := (Real.cos qz490)

noncomputable abbrev qz217 := (Real.sin qz490)

noncomputable abbrev qz491 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 27)))

noncomputable abbrev qz597 := (@Neg.neg Real Real.instNeg qz217)

noncomputable def ep1101 := @Enclosure.Complex.IsNear.of_eq qz209 (Complex.mk (@HMul.hMul Real Real Real qz0 qz491 qz216) (@HMul.hMul Real Real Real qz0 qz491 qz597)) Bool.false 84426445831 1099511627776 22389854934041 146992610005745664 Bool.false 97014667451 549755813888 11231232653461 73496305002872832 (BSN.cpow_neg_s_mk qz152 104500 1000 27 qz153 rfl)

noncomputable abbrev qz492 := (Real.sqrt (@Nat.cast Real Real.instNatCast 27))

noncomputable abbrev qz493 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 27) qz15)

noncomputable def ep1102 := @Enclosure.Real.IsNear.inv_image qz492 5448561 1048576 1 1048576 100899 100900 524288 (@Enclosure.Real.IsNear.of_eq qz492 (Real.sqrt qz493) Bool.false 5448561 1048576 1 1048576 (BSN.sqrt_natCast_div_one 27) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz493) Bool.false 5448561 1048576 1 1048576 5448561 1048576 1 1048576 (BSN.sqrt_enclosure 27 1 2724280 2724281 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep1103 := BSN.log_dyadic_bound 11 43 5 4 11045349262332945 524288 133689 250863800262504 22507682505 274332 54 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 11) (BSN.artanhQ 43) 0 4 250863800262504 11045349262332945 22507682505 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep1104 := @Enclosure.Real.IsNear.mulLit_ff qz152 (Real.log (Enclosure.sfrac Bool.false 27 1)) 104500 1000 0 1 3710780868205815 1125899906842624 250000000133689 33422250000000000000 775553201455015335 2251799813685248 52250000027941001 66844500000000000000 qz154 (BSN.isNear_log_sfrac 27 1 3710780868205815 1125899906842624 250000000133689 33422250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz493) Bool.false 62256572154556490711040 18889465931478580854784 1000000000534756 133689000000000000000 3710780868205815 1125899906842624 250000000133689 33422250000000000000 (BSN.log_rat_reduce_isNear 27 1 4 54 32 274332 524288 24973259072661432 36028797018963968 133689 1000000000000000 rfl rfl rfl rfl (ep1103 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1105 := nat_lit 603396308568751817675415595136004241

noncomputable def ep1106 := BSN.sin_dyadic_bound_f 881354573 2147483648 2 1 1048576 267640 ep1105 ep58 ep1105 ep1105 ep59 ep1105 418369 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 881354573) qz287 0 1 ep1105 ep58 ep1105 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 881354573) qz288 0 1 ep1105 ep59 ep1105 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz218 := qz490

noncomputable abbrev qz494 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 180572551) qz20)

noncomputable def ep1107 := @Enclosure.Real.IsNear.cos_image qz218 qz494 Bool.false 180572551 524288 205 262144 Bool.false 418369 1048576 1 133689 (@Enclosure.Real.IsNear.recentre' qz218 Bool.false 775553201455015335 2251799813685248 52250000027941001 66844500000000000000 180572551 524288 205 262144 (ep1104 rfl) rfl) (Enclosure.sfrac_false_div 180572551 524288) (BSN.cos_reduce3 qz494 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 31009907253385166323712) qz21) 226375608064910080 72057594037927936 Bool.false 418369 1048576 54 1000000000000000 267378 133689 (BSN.sin_reduce_arg_pos_rat_q3 180572551 524288 226375608064910080 72057594037927936 54 31009907253385166323712 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 418369 1048576 31009907253385166323712 75557863725914323419136 881354573 2147483648 267640 267378 (ep1106 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1108 := BSN.cos_dyadic_bound_f 881354573 2147483648 2 1 1048576 267640 ep1105 ep62 ep1105 ep1105 ep63 ep1105 961498 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 881354573) qz292 0 1 ep1105 ep62 ep1105 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 881354573) qz293 0 1 ep1105 ep63 ep1105 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1109 := @Enclosure.Real.IsNear.sin_image qz218 qz494 Bool.false 180572551 524288 205 262144 Bool.true 961498 1048576 1 133689 (@Enclosure.Real.IsNear.recentre' qz218 Bool.false 775553201455015335 2251799813685248 52250000027941001 66844500000000000000 180572551 524288 205 262144 (ep1104 rfl) rfl) (Enclosure.sfrac_false_div 180572551 524288) (BSN.sin_reduce3 qz494 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 31009907253385166323712) qz21) 226375608064910080 72057594037927936 Bool.false 961498 1048576 54 1000000000000000 267378 133689 (BSN.sin_reduce_arg_pos_rat_q3 180572551 524288 226375608064910080 72057594037927936 54 31009907253385166323712 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 961498 1048576 31009907253385166323712 75557863725914323419136 881354573 2147483648 267640 267378 (ep1108 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1110 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz491 qz216) (@HMul.hMul Real Real Real qz0 qz491 qz597) Bool.false 84426445831 1099511627776 22389854934041 146992610005745664 Bool.false 97014667451 549755813888 11231232653461 73496305002872832 (@Enclosure.Real.IsNear.mulLit_ff qz491 qz216 201799 1048576 1 1048576 418369 1048576 27668389 35045769216 84426445831 1099511627776 22389854934041 146992610005745664 (@Enclosure.Real.IsNear.recentre' qz491 Bool.false 201799 1048576 1 1048576 201799 1048576 1 1048576 (ep1102 rfl rfl) rfl) (@Enclosure.Real.IsNear.recentre' qz216 Bool.false 418369 1048576 27668389 35045769216 418369 1048576 27668389 35045769216 (ep1107 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz491 qz597 201799 1048576 1 1048576 480749 524288 27668389 35045769216 97014667451 549755813888 11231232653461 73496305002872832 (@Enclosure.Real.IsNear.recentre' qz491 Bool.false 201799 1048576 1 1048576 201799 1048576 1 1048576 (ep1102 rfl rfl) rfl) (@Enclosure.Real.IsNear.neg qz217 Bool.true 480749 524288 27668389 35045769216 (@Enclosure.Real.IsNear.recentre' qz217 Bool.true 961498 1048576 27668389 35045769216 480749 524288 27668389 35045769216 (ep1109 rfl rfl) rfl)) rfl)

noncomputable def ep1111 := @ep1100 14152968 0 1 597809226007073899 15561352883541639168 158538734122750599989 ep1098 (@Enclosure.Complex.IsNear.re_isNear qz209 Bool.false 84426445831 1099511627776 22389854934041 146992610005745664 Bool.false 97014667451 549755813888 11231232653461 73496305002872832 (ep1101 ep1110))

noncomputable def ep1112 := @Enclosure.Complex.IsNear.re_isNear (@HAdd.hAdd Complex Complex Complex qz4 qz210 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz89 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz89 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz132 (@HMul.hMul Nat Nat Nat qz89 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz133 qz211 (@HSub.hSub Nat Nat Nat qz132 (@HMul.hMul Nat Nat Nat qz89 2 k) 1))))) Bool.false 7080829 14152968 0 1 Bool.false

noncomputable def ep1113 := @Enclosure.Complex.IsNear.addLitP qz210 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz89 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz89 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz132 (@HMul.hMul Nat Nat Nat qz89 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz133 qz211 (@HSub.hSub Nat Nat Nat qz132 (@HMul.hMul Nat Nat Nat qz89 2 k) 1)))) Bool.false 21787 43682 0 1 Bool.true 5643

noncomputable def ep1114 := @ep1113 21841 0 1 Bool.false 1 648 0 1 Bool.false 209 648 0 1 Bool.false 14161658 7080829 14152968 0 1 Bool.false 908105 908105 14152968 0 1

noncomputable abbrev qz219 := (@HDiv.hDiv Complex Complex Complex qz400 qz487 (@HSub.hSub Complex Complex Complex qz392 qz439 (1 : Complex)))

noncomputable def ep1115 := @Enclosure.Complex.IsNear.addLitP qz219 qz108 Bool.true 54000000 43682000000 0 1 Bool.true 11286000000 43682000000 0 1

noncomputable def ep1116 := @Enclosure.Complex.IsNear.of_eq qz219 (Complex.mk (Enclosure.sfrac Bool.true 54000000 43682000000) (Enclosure.sfrac Bool.true 11286000000 43682000000)) Bool.true 54000000 43682000000 0 1 Bool.true 11286000000 43682000000 0 1

noncomputable def ep1117 := @ep1115 Bool.false 1 2 0 1 Bool.false 0 1 0 1 Bool.false 43574000000 21787 43682 0 1 Bool.true 11286000000 5643 21841 0 1 (ep1116 (BSN.N_div_s_sub_one_mk qz152 104500 1000 27 qz153 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 54000000 43682000000) (Enclosure.sfrac Bool.true 11286000000 43682000000) Bool.true 54000000 43682000000 0 1 Bool.true 11286000000 43682000000 0 1 (Enclosure.Real.IsNear.const Bool.true 54000000 43682000000) (Enclosure.Real.IsNear.const Bool.true 11286000000 43682000000))) qz109 rfl

noncomputable abbrev qz220 := (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz427 qz487 1))

noncomputable def ep1118 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz89 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz89 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz132 (@HMul.hMul Nat Nat Nat qz89 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz133 qz211 (@HSub.hSub Nat Nat Nat qz132 (@HMul.hMul Nat Nat Nat qz89 2 k) 1)))) (@HAdd.hAdd Complex Complex Complex qz4 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz89 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz89 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz132 (@HMul.hMul Nat Nat Nat qz89 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz133 qz211 (@HSub.hSub Nat Nat Nat qz132 (@HMul.hMul Nat Nat Nat qz89 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz110)) ↑qz145) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 1))) qz220)) Bool.false 1 648 0 1

noncomputable def ep1119 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz89 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz89 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz132 (@HMul.hMul Nat Nat Nat qz89 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz133 qz211 (@HSub.hSub Nat Nat Nat qz132 (@HMul.hMul Nat Nat Nat qz89 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz110)) ↑qz145) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 1))) qz220) Bool.false 0 1 0 1 Bool.false

noncomputable def ep1120 := @ep1119 0 1 0 1 Bool.false 1 648 0 1 Bool.false 209 648 0 1 Bool.false 1 1 648 0 1 Bool.false 209 209 648 0

noncomputable def ep1121 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz89 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz89 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz132 (@HMul.hMul Nat Nat Nat qz89 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz133 qz211 (@HSub.hSub Nat Nat Nat qz132 (@HMul.hMul Nat Nat Nat qz89 2 k) 1)))) (Complex.mk qz10 qz10) Bool.false 0 1 0 1 Bool.false

noncomputable def ep1122 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz110)) ↑qz145) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 1))) qz220 Bool.false 1 648 0 1 Bool.false 209 648 0 1

noncomputable def ep1123 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz110)) ↑qz145) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz220)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz110)) ↑qz145) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz220)) 1 648 0 1 0 1 0

noncomputable def ep1124 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz110)) ↑qz145) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz220) 1 24 0 1 1 27 0 1 1

noncomputable def ep1125 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz110)) ↑qz145)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz110)) ↑qz145)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 1)))) 1 24 0 1 0 1 0 1 1

noncomputable def ep1126 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz110)) ↑qz145)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 1 2 0 1 1 24 0

noncomputable def ep1127 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 1)) qz149 Bool.false 1 2 0 1 Bool.false 104500 1000 0 1 (BSN.ascPochhammer_one_eval qz149)

noncomputable def ep1128 := ep1127 (@Enclosure.Complex.IsNear.of_eq qz149 (Complex.mk qz103 qz152) Bool.false 1 2 0 1 Bool.false 104500 1000 0 1 (BSN.s_crit_mk qz152 Bool.false 104500 1000 qz153) (@Enclosure.Complex.IsNear.mk qz103 qz152 Bool.false 1 2 0 1 Bool.false 104500 1000 0 1 qz408 qz154))

noncomputable def ep1129 := @ep1126 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz110)) ↑qz145) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep607) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 104500 1000 0 1 ep1128)

noncomputable def ep1130 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz110)) ↑qz145)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 104500 1000 0 1 0 1 0

noncomputable def ep1131 := @ep1130 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz110)) ↑qz145) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep607) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 104500 1000 0 1 ep1128)

noncomputable def ep1132 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz110)) ↑qz145)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz110)) ↑qz145)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 1)))) 209 24 0 1 0 1 0 1 209

noncomputable def ep1133 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz110)) ↑qz145)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 104500 1000 0 1 209 24 0

noncomputable def ep1134 := @ep1133 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz110)) ↑qz145) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep607) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 104500 1000 0 1 ep1128)

noncomputable def ep1135 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz110)) ↑qz145)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 1 2 0 1 0 1 0

noncomputable def ep1136 := @ep1135 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz110)) ↑qz145) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep607) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 104500 1000 0 1 ep1128)

noncomputable def ep1137 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz110)) ↑qz145) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 24 0 1 Bool.false 209 24 0 1 (@ep1125 1 24 0 1 (ep1129 rfl) (ep1131 rfl) rfl rfl) (@ep1132 209 24 0 1 (ep1134 rfl) (ep1136 rfl) rfl rfl)

noncomputable def ep1138 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz110)) ↑qz145) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 209 24 0 1 ep1137

noncomputable abbrev qz221 := (@Enclosure.Complex.IsNear.of_eq (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz427 qz487 1)) (Complex.mk (Enclosure.sfrac Bool.false 1 27) qz283) Bool.false 1 27 0 1 Bool.false 0 1 0 1 (BSN.natCast_pow_inv_mk 27 1 27 EMRow31.d15 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 27) qz283 Bool.false 1 27 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 27) qz295))

noncomputable def ep1139 := @ep1124 648 0 1 ep1138 (@Enclosure.Complex.IsNear.re_isNear qz220 Bool.false 1 27 0 1 Bool.false 0 1 0 1 qz221)

noncomputable def ep1140 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz110)) ↑qz145) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz220) 209 24 0 1 0 1 0 1 0

noncomputable def ep1141 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz110)) ↑qz145) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 209 24 0 1 ep1137

noncomputable def ep1142 := @ep1140 1 0 1 ep1141 (@Enclosure.Complex.IsNear.im_isNear qz220 Bool.false 1 27 0 1 Bool.false 0 1 0 1 qz221)

noncomputable def ep1143 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz110)) ↑qz145) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz220)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz110)) ↑qz145) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz220)) 0 1 0 1 209 648 0

noncomputable def ep1144 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz110)) ↑qz145) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz220) 1 24 0 1 0 1 0 1 0

noncomputable def ep1145 := @ep1144 1 0 1 ep1138 (@Enclosure.Complex.IsNear.im_isNear qz220 Bool.false 1 27 0 1 Bool.false 0 1 0 1 qz221)

noncomputable def ep1146 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz110)) ↑qz145) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz220) 209 24 0 1 1 27 0 1 209

noncomputable def ep1147 := @ep1146 648 0 1 ep1141 (@Enclosure.Complex.IsNear.re_isNear qz220 Bool.false 1 27 0 1 Bool.false 0 1 0 1 qz221)

noncomputable def ep1148 := @ep1120 1 (@ep1121 0 1 0 1 (BSN.bern_sum_base qz149 27) qz124) (ep1122 (@ep1123 1 1 1 648 0 1 (ep1139 rfl) (ep1142 rfl) rfl rfl) (@ep1143 1 209 209 648 0 1 (ep1145 rfl) (ep1147 rfl) rfl rfl)) rfl rfl rfl rfl rfl

noncomputable def ep1149 := ep1114 (ep1117 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep1118 Bool.false 209 648 0 1 (BSN.bern_sum_succ qz149 27 0 1 1 rfl rfl) (ep1148 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl rfl

noncomputable def ep1150 := @Enclosure.Real.IsNear.mulLit_ff qz215 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz210 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz89 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz89 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz132 (@HMul.hMul Nat Nat Nat qz89 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz133 qz211 (@HSub.hSub Nat Nat Nat qz132 (@HMul.hMul Nat Nat Nat qz89 2 k) 1)))))) 97014667451 549755813888 11231232653461 73496305002872832 908105

noncomputable def ep1151 := @ep1150 14152968 0 1 88099504585590355 7780676441770819584 10199138528771201405 1040190852823899099365376 (@Enclosure.Complex.IsNear.im_isNear qz209 Bool.false 84426445831 1099511627776 22389854934041 146992610005745664 Bool.false 97014667451 549755813888 11231232653461 73496305002872832 (ep1101 ep1110))

noncomputable def ep1152 := @Enclosure.Complex.IsNear.im_isNear (@HAdd.hAdd Complex Complex Complex qz4 qz210 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz89 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz89 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz132 (@HMul.hMul Nat Nat Nat qz89 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz133 qz211 (@HSub.hSub Nat Nat Nat qz132 (@HMul.hMul Nat Nat Nat qz89 2 k) 1))))) Bool.false 7080829 14152968 0 1 Bool.false

noncomputable def ep1153 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz214 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz210 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz89 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz89 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz132 (@HMul.hMul Nat Nat Nat qz89 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz133 qz211 (@HSub.hSub Nat Nat Nat qz132 (@HMul.hMul Nat Nat Nat qz89 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz215 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz210 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz89 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz89 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz132 (@HMul.hMul Nat Nat Nat qz89 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz133 qz211 (@HSub.hSub Nat Nat Nat qz132 (@HMul.hMul Nat Nat Nat qz89 2 k) 1))))))) 76668077591360255 15561352883541639168 20332339214877302305

noncomputable def ep1154 := nat_lit 11286311713033719577015186058580590592

noncomputable def ep1155 := @Enclosure.Real.IsNear.mulLit_ff qz214 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz210 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz89 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz89 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz132 (@HMul.hMul Nat Nat Nat qz89 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz133 qz211 (@HSub.hSub Nat Nat Nat qz132 (@HMul.hMul Nat Nat Nat qz89 2 k) 1)))))) 84426445831 1099511627776 22389854934041 146992610005745664 908105

noncomputable def ep1156 := @ep1155 14152968 0 1 76668077591360255 15561352883541639168 20332339214877302305 ep1098 (@Enclosure.Complex.IsNear.re_isNear qz209 Bool.false 84426445831 1099511627776 22389854934041 146992610005745664 Bool.false 97014667451 549755813888 11231232653461 73496305002872832 (ep1101 ep1110))

noncomputable def ep1157 := @Enclosure.Real.IsNear.mulLit_ff qz215 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz210 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz89 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz89 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz132 (@HMul.hMul Nat Nat Nat qz89 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz133 qz211 (@HSub.hSub Nat Nat Nat qz132 (@HMul.hMul Nat Nat Nat qz89 2 k) 1)))))) 97014667451 549755813888 11231232653461 73496305002872832 7080829

noncomputable def ep1158 := @ep1157 14152968 0 1 686944270712396879 7780676441770819584 79526437878373599169 1040190852823899099365376 (@Enclosure.Complex.IsNear.im_isNear qz209 Bool.false 84426445831 1099511627776 22389854934041 146992610005745664 Bool.false 97014667451 549755813888 11231232653461 73496305002872832 (ep1101 ep1110))

noncomputable abbrev qz495 := (ep1149 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable def ep1159 := @ep1096 53724319222820519 576346403094134784 59795071657208166881 693460568549266066243584 (@ep1097 ep1098 88099504585590355 7780676441770819584 10199138528771201405 1040190852823899099365376 ep1099 421610216835893189 15561352883541639168 59645670393431000933 693460568549266066243584 (ep1111 (@ep1112 908105 14152968 0 1 qz495) rfl) (ep1151 (@ep1152 908105 14152968 0 1 qz495) rfl) rfl rfl) (@ep1153 ep1098 686944270712396879 7780676441770819584 79526437878373599169 1040190852823899099365376 ep1154 53724319222820519 576346403094134784 59795071657208166881 693460568549266066243584 (ep1156 (@ep1152 908105 14152968 0 1 qz495) rfl) (ep1158 (@ep1112 908105 14152968 0 1 qz495) rfl) rfl rfl)

noncomputable def ep1160 := @ep1068 4361755559294709282305 693460568549266066243584 (@ep1069 36748152501436416 (BSN.head_sum_c_eq qz149 27) (ep1070 (BSN.head_sum_c_succ qz149 26 27 rfl rfl) (ep1095 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))) ep1159 rfl rfl rfl

noncomputable def ep1161 := @Enclosure.Complex.IsNear.re_isNear (zetaApproximant qz149 1 27) Bool.false 16153984513672747997 15561352883541639168 4361887927095848709245 693460568549266066243584 Bool.true 7223088615352633 576346403094134784 4361755559294709282305 693460568549266066243584 (@ep1064 693460568549266066243584 Bool.true 7223088615352633 576346403094134784 4361755559294709282305 693460568549266066243584 (BSN.zetaApproximant_eq_folded' qz149 1 27 rfl) (ep1160 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

noncomputable def ep1162 := @Enclosure.Real.IsNear.mulLit_ft (Real.sin (@HSub.hSub Real Real Real qz395 (Complex.im (@HSub.hSub Complex Complex Complex qz82 qz179 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz180 (@Nat.cast Complex Complex.instNatCast j))))) qz181)) (Complex.im (zetaApproximant qz149 1 27)) 711 1048576 44764879

noncomputable def ep1163 := @Enclosure.Real.IsNear.recentre' (Real.sin (@HSub.hSub Real Real Real qz395 (Complex.im (@HSub.hSub Complex Complex Complex qz82 qz179 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz180 (@Nat.cast Complex Complex.instNatCast j))))) qz181)) Bool.false 711 1048576 44764879

noncomputable def ep1164 := @Enclosure.Real.IsNear.sin_image (@HSub.hSub Real Real Real qz395 (Complex.im (@HSub.hSub Complex Complex Complex qz82 qz179 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz180 (@Nat.cast Complex Complex.instNatCast j))))) qz181) qz472 Bool.false 98826671 1048576 327

noncomputable def ep1165 := BSN.sin_dyadic_bound_f 1456640 2147483648 1 0 1048576 267640 0 1 1 0 1 1 711 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 1456640) qz287 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 1456640) qz288 0 0 rfl) rfl rfl

noncomputable def ep1166 := @ep1164 1048576 Bool.false 711 1048576 1 133689 (@ep957 98826671 1048576 327 1048576 ep1061 rfl) (Enclosure.sfrac_false_div 98826671 1048576) (BSN.sin_reduce0 qz472 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 102501939462182797312) qz27) 226375608064910080 72057594037927936 Bool.false 711 1048576 15 1000000000000000 267378 133689 (BSN.sin_reduce_arg_pos_rat_q0 98826671 1048576 226375608064910080 72057594037927936 15 102501939462182797312 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 711 1048576 102501939462182797312 151115727451828646838272 1456640 2147483648 267640 267378 (ep1165 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1167 := @Enclosure.Complex.IsNear.im_isNear (zetaApproximant qz149 1 27) Bool.false 16153984513672747997 15561352883541639168 4361887927095848709245 693460568549266066243584 Bool.true 7223088615352633 576346403094134784 4361755559294709282305 693460568549266066243584 (@ep1064 693460568549266066243584 Bool.true 7223088615352633 576346403094134784 4361755559294709282305 693460568549266066243584 (BSN.zetaApproximant_eq_folded' qz149 1 27 rfl) (ep1160 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

theorem EMRow31.d16 : Enclosure.Real.IsNear (hardyZApproximantEM 1 27 qz152) Bool.false 705783457210689610643749 679885881717189909676032 ep942 ep943 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantEM 1 27 qz152) ep944 Bool.false 705783457210689610643749 679885881717189909676032 ep942 ep943 (@Eq.refl Real ep944) (@ep945 Bool.false 705783457210689610643749 679885881717189909676032 ep942 ep943 (BSN.re_exp_mul (@HSub.hSub Real Real Real qz395 (Complex.im (@HSub.hSub Complex Complex Complex qz82 qz179 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz180 (@Nat.cast Complex Complex.instNatCast j))))) qz181) (zetaApproximant qz149 1 27)) (@ep947 ep948 ep949 ep950 1711872001838574021 201447668656945158422528 ep951 ep950 ep952 705783457210689610643749 679885881717189909676032 ep942 ep943 (@ep953 140183076864 16153984513672747997 15561352883541639168 4361887927095848709245 693460568549266066243584 ep946 ep948 ep949 ep950 (@ep954 140183076864 1048575 1048576 44764879 140183076864 (ep1063 rfl rfl) rfl) ep1161 rfl) (@ep1162 140183076864 7223088615352633 576346403094134784 4361755559294709282305 693460568549266066243584 1711872001838574021 201447668656945158422528 ep951 ep950 (@ep1163 140183076864 711 1048576 44764879 140183076864 (ep1166 rfl rfl) rfl) ep1167 rfl) rfl rfl))

theorem EMRow31.d17 : @Eq Nat (Nat.mul (BSN.factNat (Nat.succ (Nat.mul 2 1))) (Nat.pow 4 (Nat.mul 2 1))) 96 := @Eq.refl Nat 96

theorem EMRow31.d18 : @Eq Nat (Nat.mul (Nat.mul 2 1) (Nat.pow (Nat.succ (Nat.mul 4 2)) (Nat.mul 2 1))) 162 := @Eq.refl Nat 162

theorem EMRow31.d19 : @Eq Nat (BSN.factNat (Nat.mul 2 2)) 24 := @Eq.refl Nat 24

theorem EMRow31.d20 : @Eq Nat (Nat.pow 26 (Nat.succ (Nat.mul 2 3))) 8031810176 := @Eq.refl Nat 8031810176

noncomputable abbrev qz598 := (@HAdd.hAdd Complex Complex Complex qz603 qz602 (@Nat.cast Complex Complex.instNatCast 3))

noncomputable abbrev qz496 := qz598

noncomputable abbrev qz222 := (@HDiv.hDiv Real Real Real qz271 (@Norm.norm Complex Complex.instNorm qz496) (@HAdd.hAdd Real Real Real qz417 (Complex.re qz272) qz296))

noncomputable abbrev qz223 := (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 2)

noncomputable abbrev qz224 := (@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 2)))

noncomputable abbrev qz497 := (@HPow.hPow Complex Complex Complex qz535 (@Nat.cast Complex Complex.instNatCast 26) (@HSub.hSub Complex Complex Complex qz572 qz536 qz537))

noncomputable abbrev qz225 := qz497

noncomputable def ep1168 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 26))) (@HMul.hMul Real Real Real qz0 qz222 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225))) 14298131593 463856467968 43037513 463856467968 488868110181101583 1008806316530991104 167094938949

noncomputable def ep1169 := nat_lit 241188680356406563181497942016

noncomputable def ep1170 := @Enclosure.Real.IsNear.mulLit_ff (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 26)) 26561 1769472 1 1769472 538313 262144 25 4096 14298131593 463856467968

noncomputable abbrev qz226 := (@HMul.hMul Real Real Real qz268 (2 : Real) Real.pi)

noncomputable abbrev qz599 := (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid)))

noncomputable abbrev qz498 := (@Inv.inv Real Real.instInv (@HPow.hPow Real Nat Real qz599 qz226 2))

noncomputable def ep1171 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 96 162) qz498 96 162 0 1 26561 1048576 1 1048576 26561 1769472 1 1769472

noncomputable def ep1172 := nat_lit 781950621441006189802102638025

noncomputable def ep1173 := nat_lit 19807040628566084398385987584

noncomputable def ep1174 := nat_lit 26986075409044041160201671

noncomputable def ep1175 := nat_lit 1073741824000000000000000000000000000000

noncomputable abbrev qz499 := (@HPow.hPow Real Nat Real qz599 qz226 1)

noncomputable def ep1176 := @Enclosure.Real.IsNear.mulLit_ff qz499 qz226 884279719003555 140737488355328 1 500000000000000 884279719003555 140737488355328 1 500000000000000 ep1172 ep1173 ep1174 ep1175

noncomputable def ep1177 := ep1176 (@Enclosure.Real.IsNear.of_eq qz499 qz226 Bool.false 884279719003555 140737488355328 1 500000000000000 (BSN.pow_one_r qz226) (@Enclosure.Real.IsNear.of_eq qz226 qz269 Bool.false 884279719003555 140737488355328 1 500000000000000 BSN.two_pi_eq qz270)) (@Enclosure.Real.IsNear.of_eq qz226 qz269 Bool.false 884279719003555 140737488355328 1 500000000000000 BSN.two_pi_eq qz270) rfl

noncomputable abbrev qz500 := (@HPow.hPow Real Nat Real qz599 qz226 2)

noncomputable def ep1178 := @Enclosure.Real.IsNear.inv_image qz500 ep1172 ep1173 ep1174 ep1175 13280 13281 524288 (@Enclosure.Real.IsNear.of_eq qz500 (@HMul.hMul Real Real Real qz0 qz499 qz226) Bool.false ep1172 ep1173 ep1174 ep1175 (BSN.pow_succ_r qz226 1 2 rfl) ep1177) rfl rfl rfl

noncomputable def ep1179 := ep1171 (Enclosure.Real.IsNear.const Bool.false 96 162) (@Enclosure.Real.IsNear.recentre' qz498 Bool.false 26561 1048576 1 1048576 26561 1048576 1 1048576 (ep1178 rfl rfl rfl) rfl)

noncomputable def ep1180 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 26)) (Real.sqrt (@HAdd.hAdd Real Real Real qz417 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz5 1 26)) (Complex.re (zetaApproximant qz5 1 26))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz5 1 26)) (Complex.im (zetaApproximant qz5 1 26))))) Bool.false 538313 262144 25 4096

noncomputable def ep1181 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz417 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz5 1 26)) (Complex.re (zetaApproximant qz5 1 26))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz5 1 26)) (Complex.im (zetaApproximant qz5 1 26))))) Bool.false 2153252 1048576 6400 1048576

noncomputable def ep1182 := nat_lit 1559219024851264699479392408376192601564829

noncomputable def ep1183 := nat_lit 369754533395078546791854780425699328000000

noncomputable def ep1184 := nat_lit 52119488441571358847894227061436495758897304863224045515677

noncomputable def ep1185 := nat_lit 2079468979968590924697085429070443551532771788416090112000000

noncomputable def ep1186 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz417 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz5 1 26)) (Complex.re (zetaApproximant qz5 1 26))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz5 1 26)) (Complex.im (zetaApproximant qz5 1 26)))) ep1182 ep1183 ep1184 ep1185 1073426 1079826

noncomputable def ep1187 := nat_lit 1471662219791070392681139821444549700018547397782009

noncomputable def ep1188 := nat_lit 349045747651328643893110563651354244012834816000000

noncomputable def ep1189 := nat_lit 154209075019196180655470770905553372495463152468596207197911

noncomputable def ep1190 := nat_lit 6238406939905772774091256287211330654598315365248270336000000

noncomputable def ep1191 := nat_lit 129297939116677734814043252952127694150248015321

noncomputable def ep1192 := nat_lit 196338233053872362189874692053886762257219584000000

noncomputable def ep1193 := nat_lit 32292522618958772358952978947657974477595584751741727

noncomputable def ep1194 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz5 1 26)) (Complex.re (zetaApproximant qz5 1 26))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz5 1 26)) (Complex.im (zetaApproximant qz5 1 26))) ep1187 ep1188 ep1189 ep1190 ep1191 ep1192 ep1193

noncomputable def ep1195 := nat_lit 93726065803872788072284499507381770652017959213465600000

noncomputable def ep1196 := nat_lit 288988690781747066954820119636813002488609501380904232043903301669129005102239833888583887880192000000

noncomputable def ep1197 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (zetaApproximant qz5 1 26)) (Complex.re (zetaApproximant qz5 1 26)) ep412 ep413 ep414 ep415 ep412 ep413 ep414 ep415 ep1187

noncomputable def ep1198 := @Enclosure.Real.IsNear.mulLit_tt (Complex.im (zetaApproximant qz5 1 26)) (Complex.im (zetaApproximant qz5 1 26)) 359580226259283805482139 ep544 ep545 ep546 359580226259283805482139 ep544 ep545 ep546 ep1191

noncomputable def ep1199 := @ep1168 1008806316530991104 ep1169 14039028922352390549 27237770546336759808 2531685344314951 27237770546336759808 (@ep1170 43037513 463856467968 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaStirlingErrorBound 1 2) (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 96 162) qz498) Bool.false 26561 1769472 1 1769472 (BSN.theta_err_eq 1 2 96 162 EMRow31.d17 EMRow31.d18 rfl) (ep1179 rfl)) (ep1180 (BSN.norm_eq_sqrt_mul_add (zetaApproximant qz5 1 26)) (@ep1181 538313 262144 25 4096 (@ep1186 524288 (@ep1194 ep1195 ep1196 ep1182 ep1183 ep1184 ep1185 (@ep1197 ep1188 ep1189 ep1190 ep645 ep645 rfl) (@ep1198 ep1192 ep1193 ep1195 ep651 ep651 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl)

noncomputable abbrev qz227 := (@Norm.norm Complex Complex.instNorm qz496)

noncomputable abbrev qz600 := (Enclosure.sfrac Bool.false 2 7)

noncomputable def ep1200 := @Enclosure.Real.IsNear.of_eq (@HMul.hMul Real Real Real qz0 qz222 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225))) (@HMul.hMul Real Real Real qz0 (@HMul.hMul Real Real Real qz0 qz227 qz600) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225))) Bool.false 488868110181101583 1008806316530991104 167094938949 1008806316530991104 (BSN.zrb_shape_eq qz227 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)) qz13 3)

noncomputable def ep1201 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz0 qz227 qz600) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)) 107285977 3670016 1 3670016 4556682279 274877906944 1515 274877906944

noncomputable def ep1202 := @Enclosure.Real.IsNear.mulLit_ff qz227 qz600 107285977 1048576 1 1048576 2 7 0 1 107285977 3670016

noncomputable abbrev qz501 := (Complex.re qz598)

noncomputable abbrev qz502 := (Complex.im qz598)

noncomputable abbrev qz228 := (@HAdd.hAdd Real Real Real qz417 (@HMul.hMul Real Real Real qz268 qz501 qz501) (@HMul.hMul Real Real Real qz268 qz502 qz502))

noncomputable abbrev qz229 := qz496

noncomputable def ep1203 := @Enclosure.Real.IsNear.of_eq qz227 (Real.sqrt qz228) Bool.false 107285977 1048576 1 1048576 (BSN.norm_eq_sqrt_mul_add qz229)

noncomputable def ep1204 := @Enclosure.Real.IsNear.recentre' (Real.sqrt qz228) Bool.false 107285977 1048576 1 1048576 107285977

noncomputable def ep1205 := @Enclosure.Real.IsNear.sqrt_image qz228 654283721 62500 0 1 53642988 53642989 524288

noncomputable abbrev qz230 := (@HMul.hMul Real Real Real qz268 qz501 qz501)

noncomputable abbrev qz231 := (@HMul.hMul Real Real Real qz268 qz502 qz502)

noncomputable def ep1206 := @Enclosure.Real.IsNear.addLit_ff qz230 qz231 49 4 0 1 163379524 15625 0 1

noncomputable abbrev qz232 := qz501

noncomputable def ep1207 := @Enclosure.Real.IsNear.mulLit_ff qz232 qz232 7 2 0 1 7 2 0 1 49 4

noncomputable abbrev qz503 := (Enclosure.sfrac Bool.false 7 2)

noncomputable def ep1208 := @Enclosure.Complex.IsNear.of_eq qz229 (Complex.mk qz503 qz13) Bool.false 7 2 0 1 Bool.false 102256 1000 0 1 (BSN.s_add_nat_mk qz13 Bool.false 102256 1000 3 qz14)

noncomputable abbrev qz504 := (ep1208 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7 2) qz13 Bool.false 7 2 0 1 Bool.false 102256 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 7 2) qz16))

noncomputable def ep1209 := @ep1207 0 1 (@Enclosure.Complex.IsNear.re_isNear qz229 Bool.false 7 2 0 1 Bool.false 102256 1000 0 1 qz504)

noncomputable def ep1210 := ep1209 (@Enclosure.Complex.IsNear.re_isNear qz229 Bool.false 7 2 0 1 Bool.false 102256 1000 0 1 qz504)

noncomputable abbrev qz233 := qz502

noncomputable def ep1211 := @Enclosure.Real.IsNear.mulLit_ff qz233 qz233 102256 1000 0 1 102256 1000 0 1 163379524 15625

noncomputable def ep1212 := @ep1211 0 1 (@Enclosure.Complex.IsNear.im_isNear qz229 Bool.false 7 2 0 1 Bool.false 102256 1000 0 1 qz504)

noncomputable def ep1213 := ep1212 (@Enclosure.Complex.IsNear.im_isNear qz229 Bool.false 7 2 0 1 Bool.false 102256 1000 0 1 qz504)

noncomputable def ep1214 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)) (Real.sqrt (@HAdd.hAdd Real Real Real qz417 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)) (Complex.re (@HMul.hMul Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)) (Complex.im (@HMul.hMul Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225))))) Bool.false 4556682279 274877906944

noncomputable def ep1215 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz417 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)) (Complex.re (@HMul.hMul Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)) (Complex.im (@HMul.hMul Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225))))) Bool.false 4556682279 274877906944

noncomputable def ep1216 := nat_lit 1225652051757980856899074929769924861187861303538317483268961

noncomputable def ep1217 := nat_lit 4460149039706124628307143654529672301196083200000000000000000000

noncomputable def ep1218 := nat_lit 962084421577529711415514236747081999010644764776041652267614533621199031969

noncomputable def ep1219 := nat_lit 5267112058476100810130472706285199046652690383810379206442038067200000000000000000000

noncomputable def ep1220 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz417 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)) (Complex.re (@HMul.hMul Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)) (Complex.im (@HMul.hMul Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)))) ep1216 ep1217 ep1218 ep1219

noncomputable def ep1221 := nat_lit 92128162028152446050293865258904589026442106891298383923561

noncomputable def ep1222 := nat_lit 8920298079412249256614287309059344602392166400000000000000000000

noncomputable def ep1223 := nat_lit 72926009666014632077125241143092843184486801844162697724381294564860224119

noncomputable def ep1224 := nat_lit 10534224116952201620260945412570398093305380767620758412884076134400000000000000000000

noncomputable def ep1225 := nat_lit 2359175941487809267747855994280945133349280500185336582614361

noncomputable def ep1226 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)) (Complex.re (@HMul.hMul Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)) (Complex.im (@HMul.hMul Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225))) ep1221 ep1222 ep1223 ep1224 ep1225

noncomputable def ep1227 := nat_lit 1851242833489044790753903232351071154836802727707920606810847772677537839819

noncomputable def ep1228 := nat_lit 21866363286648798715841191187880162743310183539072910318833556766412697965400369019636232757938341334220800000000000000000000

noncomputable def ep1229 := nat_lit 303526213082416402440176397331

noncomputable def ep1230 := nat_lit 94447329657392904273920000000000

noncomputable def ep1231 := nat_lit 3495783959871364998116452230942509

noncomputable def ep1232 := nat_lit 3245646948907444187524349684613120000000000

noncomputable def ep1233 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)) (Complex.re (@HMul.hMul Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)) ep1229 ep1230 ep1231 ep1232 ep1229 ep1230 ep1231

noncomputable def ep1234 := nat_lit 1535960917955860382036721746981

noncomputable def ep1235 := nat_lit 17536445251689290551646552808919709

noncomputable def ep1236 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225) Bool.false ep1229 ep1230 ep1231 ep1232 Bool.false ep1234 ep1230 ep1235

noncomputable def ep1237 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225 Bool.false ep1229 ep1230 ep1231 ep1232 Bool.false ep1234 ep1230 ep1235 ep1232

noncomputable def ep1238 := nat_lit 544674092329735953500836011

noncomputable def ep1239 := nat_lit 755578637259143234191360000000

noncomputable def ep1240 := nat_lit 2044888757170294791831500353543

noncomputable def ep1241 := nat_lit 8655058530419851166731599158968320000000

noncomputable def ep1242 := nat_lit 58860487885299852063142973989

noncomputable def ep1243 := nat_lit 23611832414348226068480000000000

noncomputable def ep1244 := nat_lit 682237668983126112794909899590971

noncomputable abbrev qz234 := (Complex.re qz497)

noncomputable abbrev qz235 := (Complex.im qz497)

noncomputable def ep1245 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz234) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz235) ep1238 ep1239 ep1240 ep1241 ep1242 ep1243 ep1244

noncomputable def ep1246 := nat_lit 811411737226861046881087421153280000000000

noncomputable def ep1247 := nat_lit 57334480613310129635556306883342855938194115961815040000000

noncomputable def ep1248 := nat_lit 288501951013995038891053305298944

noncomputable def ep1249 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz234 1960476163 30000000 0 1 833482348741624491 75557863725914323419136 1043057189760024025261 ep1248 ep1238

noncomputable def ep1250 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) 1960476163 30000000 0 1 0 1 0 1 1960476163

noncomputable def ep1251 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 5881428489 125000 0 1 1960476163 30000000 0

noncomputable def ep1252 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (Complex.mk (Enclosure.sfrac Bool.true 1 720) qz10) Bool.true 1 720 0 1 Bool.false 0 1 0 1 (BSN.bern_coeff_mk 2 1 30 24 Bool.true BSN.bern_real_2 EMRow31.d19 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 1 720) qz10 Bool.true 1 720 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.true 1 720) qz17)

noncomputable abbrev qz505 := (@HAdd.hAdd Complex Complex Complex qz534 qz533 qz538)

noncomputable abbrev qz236 := qz505

noncomputable def ep1253 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) (@HMul.hMul Complex Complex Complex qz81 (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) qz236) Bool.true 5881428489 125000 0 1 Bool.true 4174337385911 3906250 0 1

noncomputable abbrev qz237 := (Complex.re qz505)

noncomputable abbrev qz238 := (Complex.im qz505)

noncomputable def ep1254 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz237) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz238) 653471221 25000 0 1 326759048 15625 0 1

noncomputable def ep1255 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz237 653471221 62500 0 1 5 2 0 1 653471221 25000

noncomputable abbrev qz506 := (@HAdd.hAdd Complex Complex Complex qz534 qz533 (@Nat.cast Complex Complex.instNatCast 1))

noncomputable abbrev qz239 := qz506

noncomputable def ep1256 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) (@HMul.hMul Complex Complex Complex qz81 (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) qz239) Bool.true 653471221 62500 0 1 Bool.false 25564 125 0 1

noncomputable abbrev qz240 := (Complex.re qz506)

noncomputable abbrev qz241 := (Complex.im qz506)

noncomputable def ep1257 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz240) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz241) 3 4 0 1 163379524 15625 0 1

noncomputable def ep1258 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz240 1 2 0 1 3 2 0 1 3 4

noncomputable def ep1259 := @ep1258 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 102256 1000 0 1 ep609)

noncomputable abbrev qz507 := (Enclosure.sfrac Bool.false 3 2)

noncomputable def ep1260 := @Enclosure.Complex.IsNear.of_eq qz239 (Complex.mk qz507 qz13) Bool.false 3 2 0 1 Bool.false 102256 1000 0 1 (BSN.s_add_nat_mk qz13 Bool.false 102256 1000 1 qz14)

noncomputable abbrev qz508 := (ep1260 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 3 2) qz13 Bool.false 3 2 0 1 Bool.false 102256 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 3 2) qz16))

noncomputable def ep1261 := ep1259 (@Enclosure.Complex.IsNear.re_isNear qz239 Bool.false 3 2 0 1 Bool.false 102256 1000 0 1 qz508)

noncomputable def ep1262 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz241 102256 1000 0 1 102256 1000 0 1 163379524 15625

noncomputable def ep1263 := @ep1262 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 102256 1000 0 1 ep609)

noncomputable def ep1264 := ep1263 (@Enclosure.Complex.IsNear.im_isNear qz239 Bool.false 3 2 0 1 Bool.false 102256 1000 0 1 qz508)

noncomputable def ep1265 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) qz239 Bool.true 653471221 62500 0 1 Bool.false 25564 125 0 1 (@ep1257 653471221 653471221 62500 0 1 (ep1261 rfl) (ep1264 rfl) rfl rfl)

noncomputable def ep1266 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz241) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz240) 6391 125 0 1 19173 125 0 1

noncomputable def ep1267 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz241 1 2 0 1 102256 1000 0 1 6391 125

noncomputable def ep1268 := @ep1267 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 102256 1000 0 1 ep609)

noncomputable def ep1269 := ep1268 (@Enclosure.Complex.IsNear.im_isNear qz239 Bool.false 3 2 0 1 Bool.false 102256 1000 0 1 qz508)

noncomputable def ep1270 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz240 102256 1000 0 1 3 2 0 1 19173 125

noncomputable def ep1271 := @ep1270 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 102256 1000 0 1 ep609)

noncomputable def ep1272 := ep1271 (@Enclosure.Complex.IsNear.re_isNear qz239 Bool.false 3 2 0 1 Bool.false 102256 1000 0 1 qz508)

noncomputable abbrev qz242 := (ep1256 (BSN.ascPochhammer_succ_eval_c 1 2 qz272 rfl) (ep1265 (@ep1266 3195500 25564 125 0 1 (ep1269 rfl) (ep1272 rfl) rfl rfl)))

noncomputable def ep1273 := @ep1255 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 653471221 62500 0 1 Bool.false 25564 125 0 1 qz242)

noncomputable abbrev qz509 := (Enclosure.sfrac Bool.false 5 2)

noncomputable def ep1274 := @Enclosure.Complex.IsNear.of_eq qz236 (Complex.mk qz509 qz13) Bool.false 5 2 0 1 Bool.false 102256 1000 0 1 (BSN.s_add_nat_mk qz13 Bool.false 102256 1000 2 qz14)

noncomputable abbrev qz510 := (ep1274 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 5 2) qz13 Bool.false 5 2 0 1 Bool.false 102256 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 5 2) qz16))

noncomputable def ep1275 := ep1273 (@Enclosure.Complex.IsNear.re_isNear qz236 Bool.false 5 2 0 1 Bool.false 102256 1000 0 1 qz510)

noncomputable def ep1276 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz238 25564 125 0 1 102256 1000 0 1 326759048 15625

noncomputable def ep1277 := @ep1276 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 653471221 62500 0 1 Bool.false 25564 125 0 1 qz242)

noncomputable def ep1278 := ep1277 (@Enclosure.Complex.IsNear.im_isNear qz236 Bool.false 5 2 0 1 Bool.false 102256 1000 0 1 qz510)

noncomputable def ep1279 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) qz236 Bool.true 5881428489 125000 0 1 Bool.true 4174337385911 3906250 0 1 (@ep1254 18379464028125 5881428489 125000 0 1 (ep1275 rfl) (ep1278 rfl) rfl rfl)

noncomputable def ep1280 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz238) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz237) 4176334573411 3906250 0 1 12782 25 0 1

noncomputable def ep1281 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz238 653471221 62500 0 1 102256 1000 0 1 4176334573411 3906250

noncomputable def ep1282 := @ep1281 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 653471221 62500 0 1 Bool.false 25564 125 0 1 qz242)

noncomputable def ep1283 := ep1282 (@Enclosure.Complex.IsNear.im_isNear qz236 Bool.false 5 2 0 1 Bool.false 102256 1000 0 1 qz510)

noncomputable def ep1284 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz237 25564 125 0 1 5 2 0 1 12782 25

noncomputable def ep1285 := @ep1284 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 653471221 62500 0 1 Bool.false 25564 125 0 1 qz242)

noncomputable def ep1286 := ep1285 (@Enclosure.Complex.IsNear.re_isNear qz236 Bool.false 5 2 0 1 Bool.false 102256 1000 0 1 qz510)

noncomputable abbrev qz243 := (ep1253 (BSN.ascPochhammer_succ_eval_c 2 3 qz272 rfl) (ep1279 (@ep1280 104358434647775 4174337385911 3906250 0 1 (ep1283 rfl) (ep1286 rfl) rfl rfl)))

noncomputable def ep1287 := @ep1251 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1252) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 5881428489 125000 0 1 Bool.true 4174337385911 3906250 0 1 qz243)

noncomputable def ep1288 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 4174337385911 3906250 0 1 0 1 0

noncomputable def ep1289 := @ep1288 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1252) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 5881428489 125000 0 1 Bool.true 4174337385911 3906250 0 1 qz243)

noncomputable def ep1290 := @Enclosure.Real.IsNear.addLit_ft_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) 4174337385911 2812500000 0 1 0 1 0 1 4174337385911

noncomputable def ep1291 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 4174337385911 3906250 0 1 4174337385911 2812500000 0

noncomputable def ep1292 := @ep1291 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1252) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 5881428489 125000 0 1 Bool.true 4174337385911 3906250 0 1 qz243)

noncomputable def ep1293 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 5881428489 125000 0 1 0 1 0

noncomputable def ep1294 := @ep1293 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1252) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 5881428489 125000 0 1 Bool.true 4174337385911 3906250 0 1 qz243)

noncomputable def ep1295 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.false 1960476163 30000000 0 1 Bool.false 4174337385911 2812500000 0 1 (@ep1250 1960476163 30000000 0 1 (ep1287 rfl) (ep1289 rfl) rfl rfl) (@ep1290 4174337385911 2812500000 0 1 (ep1292 rfl) (ep1294 rfl) rfl rfl)

noncomputable def ep1296 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 1960476163 30000000 0 1 Bool.false 4174337385911 2812500000 0 1 ep1295

noncomputable def ep1297 := @Enclosure.Complex.IsNear.re_isNear qz225 Bool.false 833482348741624491 75557863725914323419136 1043057189760024025261 ep1248 Bool.true 126905025155768091 75557863725914323419136 163436159062221026461 ep1248

noncomputable abbrev qz511 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 8031810176)))

noncomputable def ep1298 := @Enclosure.Complex.IsNear.of_eq qz225 (Complex.mk (@HMul.hMul Real Real Real qz0 qz511 qz140) (@HMul.hMul Real Real Real qz0 qz511 qz581)) Bool.false 833482348741624491 75557863725914323419136 1043057189760024025261 ep1248 Bool.true 126905025155768091 75557863725914323419136 163436159062221026461

noncomputable abbrev qz512 := (Real.sqrt (@Nat.cast Real Real.instNatCast 8031810176))

noncomputable abbrev qz513 := (@Nat.cast Real Real.instNatCast 8031810176)

noncomputable def ep1299 := @Enclosure.Real.IsNear.inv_image qz512 24634658892516047 274877906944 1 274877906944 1533568 1533569 137438953472 (@Enclosure.Real.IsNear.of_eq qz512 (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz513 qz15)) Bool.false 24634658892516047 274877906944 1 274877906944 (BSN.sqrt_natCast_div_one 8031810176) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz513 qz15)) Bool.false 24634658892516047 274877906944 1 274877906944 24634658892516047 274877906944 1 274877906944 (BSN.sqrt_enclosure 8031810176 1 12317329446258023 12317329446258024 137438953472 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep1300 := nat_lit 59660805140625000000000000

noncomputable def ep1301 := nat_lit 16133312625076995474398904320

noncomputable def ep1302 := nat_lit 4951760157141521099596496896

noncomputable def ep1303 := nat_lit 61092664464000000000000000

noncomputable def ep1304 := nat_lit 3230700305694190814650556443852800

noncomputable def ep1305 := nat_lit 63213216916730749612313149440000

noncomputable def ep1306 := BSN.log_dyadic_bound 10 42 9 8 ep1304 137438953472 61092664464 ep1305 20270250000000000000000 66727686103 52 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.artanhP 10) (BSN.artanhQ 42) 0 8 ep1305 ep1304 20270250000000000000000 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep1307 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz142 102256 1000 0 1 3668290588638455 1125899906842624 15628818291529 954572882250000000000000 4688809030397673181 14073748835532800 99883777701161839 ep1300 qz16 (BSN.isNear_log_sfrac 26 1 3668290588638455 1125899906842624 15628818291529 954572882250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz435) Bool.false ep1301 ep1302 1000244370657856 ep1303 3668290588638455 1125899906842624 15628818291529 954572882250000000000000 (BSN.log_rat_reduce_isNear 26 1 4 52 32 66727686103 137438953472 24973259072661432 36028797018963968 61092664464 1000000000000000 rfl rfl rfl rfl (ep1306 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1308 := nat_lit 2992810385329552725402189824

noncomputable def ep1309 := nat_lit 8832957809378480932103273955047377108644525635560948426550848557642506293983076443000066576654515343252417672244166656

noncomputable def ep1310 := nat_lit 406704355798688102870807269590474370206928662370602703270828848655152000467652488154169143141621708451154749585707730206720

noncomputable def ep1311 := nat_lit 2740533901550775676567834263307930794487125534785671841525755475701071123549526154957355464559319022280785330176

noncomputable def ep1312 := nat_lit 26498867947067639694758468729473604710071987932431775708308862621416567479806982229947889815252616911119208455161839616

noncomputable def ep1313 := nat_lit 18301696010940964629186327131571346659311789806677121647187298189481840021044361966937611441372976880301963731356847859302400

noncomputable def ep1314 := BSN.cos_dyadic_bound_f 85060787152132 562949953421312 3 2 274877906944 122304650539 ep1309 ep1310 ep1311 ep1312 ep1313 ep1311 271746044843 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 85060787152132) (BSN.cosEvenQ 562949953421312) 0 2 ep1309 ep1310 ep1311 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 85060787152132) (BSN.cosOddQ 562949953421312) 0 2 ep1312 ep1313 ep1311 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz514 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 45789150687477) (@Nat.cast Real Real.instNatCast 137438953472))

noncomputable def ep1315 := @Enclosure.Real.IsNear.cos_image qz143 qz514 Bool.false 45789150687477 137438953472 461 274877906944 Bool.false 271746044843 274877906944 1 61092664464 (@Enclosure.Real.IsNear.recentre' qz143 Bool.false 4688809030397673181 14073748835532800 99883777701161839 ep1300 45789150687477 137438953472 461 274877906944 (ep1307 rfl) rfl) (Enclosure.sfrac_false_div 45789150687477 137438953472) (BSN.cos_reduce0 qz514 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep1308) (@Nat.cast Real Real.instNatCast ep1173)) 226375608064910080 72057594037927936 Bool.false 271746044843 274877906944 53 1000000000000000 122185328928 61092664464 (BSN.sin_reduce_arg_pos_rat_q0 45789150687477 137438953472 226375608064910080 72057594037927936 53 ep1308 ep1173 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 271746044843 274877906944 ep1308 ep1173 85060787152132 562949953421312 122304650539 122185328928 (ep1314 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1316 := nat_lit 52350108897219838319764268573848942166494290938524139776

noncomputable def ep1317 := nat_lit 12052035331942427066564715692558719518916522453370946264760320

noncomputable def ep1318 := nat_lit 84364247323596989465953009847911036632415657173596623853322240

noncomputable def ep1319 := BSN.sin_dyadic_bound_f 85060787152132 562949953421312 2 1 274877906944 122304650539 ep1316 ep1317 ep1316 ep1316 ep1318 ep1316 41375727643 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 85060787152132) (BSN.sinEvenQ 562949953421312) 0 1 ep1316 ep1317 ep1316 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 85060787152132) (BSN.sinOddQ 562949953421312) 0 1 ep1316 ep1318 ep1316 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1320 := @Enclosure.Real.IsNear.sin_image qz143 qz514 Bool.false 45789150687477 137438953472 461 274877906944 Bool.false 41375727643 274877906944 1 61092664464 (@Enclosure.Real.IsNear.recentre' qz143 Bool.false 4688809030397673181 14073748835532800 99883777701161839 ep1300 45789150687477 137438953472 461 274877906944 (ep1307 rfl) rfl) (Enclosure.sfrac_false_div 45789150687477 137438953472) (BSN.sin_reduce0 qz514 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep1308) (@Nat.cast Real Real.instNatCast ep1173)) 226375608064910080 72057594037927936 Bool.false 41375727643 274877906944 53 1000000000000000 122185328928 61092664464 (BSN.sin_reduce_arg_pos_rat_q0 45789150687477 137438953472 226375608064910080 72057594037927936 53 ep1308 ep1173 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 41375727643 274877906944 ep1308 ep1173 85060787152132 562949953421312 122304650539 122185328928 (ep1319 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1321 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz511 qz140) (@HMul.hMul Real Real Real qz0 qz511 qz581) Bool.false 833482348741624491 75557863725914323419136 1043057189760024025261 ep1248 Bool.true 126905025155768091 75557863725914323419136 163436159062221026461 ep1248 (@Enclosure.Real.IsNear.mulLit_ff qz511 qz140 3067137 274877906944 1 274877906944 271746044843 274877906944 1777412264053 1049563983593525477376 833482348741624491 75557863725914323419136 1043057189760024025261 ep1248 (@Enclosure.Real.IsNear.recentre' qz511 Bool.false 3067137 274877906944 1 274877906944 3067137 274877906944 1 274877906944 (ep1299 rfl rfl) rfl) (@Enclosure.Real.IsNear.recentre' qz140 Bool.false 271746044843 274877906944 28438596224848 16793023737496407638016 271746044843 274877906944 1777412264053 1049563983593525477376 (ep1315 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz511 qz581 3067137 274877906944 1 274877906944 41375727643 274877906944 1777412264053 1049563983593525477376 126905025155768091 75557863725914323419136 163436159062221026461 ep1248 (@Enclosure.Real.IsNear.recentre' qz511 Bool.false 3067137 274877906944 1 274877906944 3067137 274877906944 1 274877906944 (ep1299 rfl rfl) rfl) (@Enclosure.Real.IsNear.neg qz141 Bool.false 41375727643 274877906944 1777412264053 1049563983593525477376 (@Enclosure.Real.IsNear.recentre' qz141 Bool.false 41375727643 274877906944 28438596224848 16793023737496407638016 41375727643 274877906944 1777412264053 1049563983593525477376 (ep1320 rfl rfl) rfl)) rfl)

noncomputable def ep1322 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz235 4174337385911 2812500000 0 1 126905025155768091 75557863725914323419136 163436159062221026461 ep1248 ep1242

noncomputable def ep1323 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 1960476163 30000000 0 1 Bool.false 4174337385911 2812500000 0 1 ep1295

noncomputable def ep1324 := @Enclosure.Complex.IsNear.im_isNear qz225 Bool.false 833482348741624491 75557863725914323419136 1043057189760024025261 ep1248 Bool.true 126905025155768091 75557863725914323419136 163436159062221026461 ep1248

noncomputable def ep1325 := nat_lit 82931425594266234787171611

noncomputable def ep1326 := nat_lit 320412694013760756214182749143

noncomputable def ep1327 := nat_lit 386581836538785915346279549589

noncomputable def ep1328 := nat_lit 4354072622858532567016558569497771

noncomputable def ep1329 := @Enclosure.Real.IsNear.addLit_tf_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz235) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz234) ep1325 ep1239 ep1326 ep1241 ep1327 ep1243 ep1328

noncomputable def ep1330 := nat_lit 290134814318097923373054327861416966968583287514071040000000

noncomputable def ep1331 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz235 1960476163 30000000 0 1 126905025155768091 75557863725914323419136 163436159062221026461 ep1248 ep1325

noncomputable def ep1332 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz234 4174337385911 2812500000 0 1 833482348741624491 75557863725914323419136 1043057189760024025261 ep1248 ep1327

noncomputable abbrev qz515 := (@ep1298 ep1248 (BSN.cpow_neg_s_sub_mk qz13 102256 1000 26 3 8031810176 qz14 rfl EMRow31.d20) ep1321)

noncomputable def ep1333 := ep1237 (@ep1245 ep1246 ep1247 ep1229 ep1230 ep1231 ep1232 (@ep1249 ep1239 ep1240 ep1241 ep1296 (ep1297 qz515) rfl) (@ep1322 ep1243 ep1244 ep1246 ep1323 (ep1324 qz515) rfl) rfl rfl) (@ep1329 ep1246 ep1330 ep1234 ep1230 ep1235 ep1232 (@ep1331 ep1239 ep1326 ep1241 ep1296 (ep1324 qz515) rfl) (@ep1332 ep1243 ep1328 ep1246 ep1323 (ep1297 qz515) rfl) rfl rfl)

noncomputable def ep1334 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)) (Complex.im (@HMul.hMul Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)) ep1234 ep1230 ep1235 ep1232 ep1234 ep1230 ep1235

noncomputable def ep1335 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225) Bool.false ep1229 ep1230 ep1231 ep1232 Bool.false ep1234 ep1230 ep1235

noncomputable def ep1336 := @ep1201 488868110181101583 1008806316530991104 167094938949 1008806316530991104 (@ep1202 1 3670016 (ep1203 (@ep1204 1048576 1 1048576 (ep1205 (@ep1206 654283721 654283721 62500 0 1 (ep1210 rfl) (ep1213 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) (Enclosure.Real.IsNear.const Bool.false 2 7) rfl) (@ep1214 1515 274877906944 (BSN.norm_eq_sqrt_mul_add (@HMul.hMul Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)) (@ep1215 1515 274877906944 4556682279 274877906944 1515 274877906944 (@ep1220 2278340382 2278341897 137438953472 (@ep1226 ep1222 ep1227 ep1224 ep1228 ep1216 ep1217 ep1218 ep1219 (@ep1233 ep1232 ep1221 ep1222 ep1223 ep1224 (@ep1236 ep1232 ep1333) (@ep1236 ep1232 ep1333) rfl) (@ep1334 ep1232 ep1225 ep1222 ep1227 ep1224 (@ep1335 ep1232 ep1333) (@ep1335 ep1232 ep1333) rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl

theorem EMRow31.d21 : Enclosure.Real.IsNear (@HAdd.hAdd Real Real Real qz417 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 26))) (@HMul.hMul Real Real Real qz0 qz222 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)))) Bool.false 14039028922352390549 27237770546336759808 2531685344314951 27237770546336759808 := ep1199 (ep1200 ep1336) rfl rfl

theorem EMRow31.d22 : @Eq Nat (Nat.pow 27 (Nat.succ (Nat.mul 2 3))) 10460353203 := @Eq.refl Nat 10460353203

noncomputable abbrev qz601 := (@HAdd.hAdd Complex Complex Complex qz603 qz609 (@Nat.cast Complex Complex.instNatCast 3))

noncomputable abbrev qz516 := qz601

noncomputable abbrev qz244 := (@HDiv.hDiv Real Real Real qz271 (@Norm.norm Complex Complex.instNorm qz516) (@HAdd.hAdd Real Real Real qz417 (Complex.re qz439) qz296))

noncomputable abbrev qz517 := (@HPow.hPow Complex Complex Complex qz535 (@Nat.cast Complex Complex.instNatCast 27) (@HSub.hSub Complex Complex Complex qz572 qz583 qz537))

noncomputable abbrev qz245 := qz517

noncomputable def ep1337 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz149 1 27))) (@HMul.hMul Real Real Real qz0 qz244 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3))) qz245))) 401575759 25769803776 3739145 38654705664 133489957140568585 288230376151711744 189753904105

noncomputable def ep1338 := nat_lit 3555756333649081627265990656

noncomputable def ep1339 := @Enclosure.Real.IsNear.mulLit_ff (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz149 1 27)) 26561 1769472 1 1769472 136071 131072 1679 262144 401575759 25769803776

noncomputable def ep1340 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (zetaApproximant qz149 1 27)) (Real.sqrt (@HAdd.hAdd Real Real Real qz417 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz149 1 27)) (Complex.re (zetaApproximant qz149 1 27))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz149 1 27)) (Complex.im (zetaApproximant qz149 1 27))))) Bool.false 136071 131072 1679 262144

noncomputable def ep1341 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz417 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz149 1 27)) (Complex.re (zetaApproximant qz149 1 27))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz149 1 27)) (Complex.im (zetaApproximant qz149 1 27))))) Bool.false 1088568 1048576 6716 1048576

noncomputable def ep1342 := nat_lit 5974755043076000326414873135496345

noncomputable def ep1343 := nat_lit 5543603854358996569440465539039232

noncomputable def ep1344 := nat_lit 3196925067757168740820487005837409744517483785

noncomputable def ep1345 := nat_lit 240443780066335670431247992759062603450210582528

noncomputable def ep1346 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz417 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz149 1 27)) (Complex.re (zetaApproximant qz149 1 27))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz149 1 27)) (Complex.im (zetaApproximant qz149 1 27)))) ep1342 ep1343 ep1344 ep1345 540926 547642

noncomputable def ep1347 := nat_lit 260951215667978968618832130789467512009

noncomputable def ep1348 := nat_lit 242155703566109688146298415676311732224

noncomputable def ep1349 := nat_lit 2099670231369464616463889858525912855356906805

noncomputable def ep1350 := nat_lit 160295853377557113620831995172708402300140388352

noncomputable def ep1351 := nat_lit 52173009145236817040270940032689

noncomputable def ep1352 := nat_lit 332175176359546897320025261558726656

noncomputable def ep1353 := nat_lit 94839441405943632249304436097080922964247155

noncomputable def ep1354 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz149 1 27)) (Complex.re (zetaApproximant qz149 1 27))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz149 1 27)) (Complex.im (zetaApproximant qz149 1 27))) ep1347 ep1348 ep1349 ep1350 ep1351 ep1352 ep1353

noncomputable def ep1355 := nat_lit 480887560132671340862495985518125206900421165056

noncomputable def ep1356 := nat_lit 86694150077485797307038374614374398403575880009580257965162414079203082240

noncomputable def ep1357 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (zetaApproximant qz149 1 27)) (Complex.re (zetaApproximant qz149 1 27)) 16153984513672747997 15561352883541639168 4361887927095848709245 693460568549266066243584 16153984513672747997 15561352883541639168 4361887927095848709245 693460568549266066243584 ep1347

noncomputable def ep1358 := @Enclosure.Real.IsNear.mulLit_tt (Complex.im (zetaApproximant qz149 1 27)) (Complex.im (zetaApproximant qz149 1 27)) 7223088615352633 576346403094134784 4361755559294709282305 693460568549266066243584 7223088615352633 576346403094134784 4361755559294709282305 693460568549266066243584 ep1351

noncomputable def ep1359 := @ep1337 2017612633061982208 ep1338 413944517919919643 864691128455135232 1758216198105905 18158513697557839872 (@ep1339 3739145 38654705664 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaStirlingErrorBound 1 2) (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 96 162) qz498) Bool.false 26561 1769472 1 1769472 (BSN.theta_err_eq 1 2 96 162 EMRow31.d17 EMRow31.d18 rfl) (ep1179 rfl)) (ep1340 (BSN.norm_eq_sqrt_mul_add (zetaApproximant qz149 1 27)) (@ep1341 136071 131072 1679 262144 (@ep1346 524288 (@ep1354 ep1355 ep1356 ep1342 ep1343 ep1344 ep1345 (@ep1357 ep1348 ep1349 ep1350 ep1161 ep1161 rfl) (@ep1358 ep1352 ep1353 ep1355 ep1167 ep1167 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl)

noncomputable abbrev qz246 := (@Norm.norm Complex Complex.instNorm qz516)

noncomputable def ep1360 := @Enclosure.Real.IsNear.of_eq (@HMul.hMul Real Real Real qz0 qz244 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3))) qz245))) (@HMul.hMul Real Real Real qz0 (@HMul.hMul Real Real Real qz0 qz246 qz600) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3))) qz245))) Bool.false 133489957140568585 288230376151711744 189753904105 2017612633061982208 (BSN.zrb_shape_eq qz246 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)) qz152 3)

noncomputable def ep1361 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz0 qz246 qz600) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)) 109637635 3670016 1 3670016 8522891797 549755813888 1653 549755813888

noncomputable def ep1362 := @Enclosure.Real.IsNear.mulLit_ff qz246 qz600 109637635 1048576 1 1048576 2 7 0 1 109637635 3670016

noncomputable abbrev qz518 := (Complex.re qz601)

noncomputable abbrev qz519 := (Complex.im qz601)

noncomputable abbrev qz247 := (@HAdd.hAdd Real Real Real qz417 (@HMul.hMul Real Real Real qz268 qz518 qz518) (@HMul.hMul Real Real Real qz268 qz519 qz519))

noncomputable abbrev qz248 := qz516

noncomputable def ep1363 := @Enclosure.Real.IsNear.of_eq qz246 (Real.sqrt qz247) Bool.false 109637635 1048576 1 1048576 (BSN.norm_eq_sqrt_mul_add qz248)

noncomputable def ep1364 := @Enclosure.Real.IsNear.recentre' (Real.sqrt qz247) Bool.false 109637635 1048576 1 1048576 109637635

noncomputable def ep1365 := @Enclosure.Real.IsNear.sqrt_image qz247 21865 2 0 1 54818817 54818818 524288

noncomputable abbrev qz249 := (@HMul.hMul Real Real Real qz268 qz518 qz518)

noncomputable abbrev qz250 := (@HMul.hMul Real Real Real qz268 qz519 qz519)

noncomputable def ep1366 := @Enclosure.Real.IsNear.addLit_ff qz249 qz250 49 4 0 1 43681 4 0 1

noncomputable abbrev qz251 := qz518

noncomputable def ep1367 := @Enclosure.Real.IsNear.mulLit_ff qz251 qz251 7 2 0 1 7 2 0 1 49 4

noncomputable def ep1368 := @Enclosure.Complex.IsNear.of_eq qz248 (Complex.mk qz503 qz152) Bool.false 7 2 0 1 Bool.false 104500 1000 0 1 (BSN.s_add_nat_mk qz152 Bool.false 104500 1000 3 qz153)

noncomputable abbrev qz520 := (ep1368 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7 2) qz152 Bool.false 7 2 0 1 Bool.false 104500 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 7 2) qz154))

noncomputable def ep1369 := @ep1367 0 1 (@Enclosure.Complex.IsNear.re_isNear qz248 Bool.false 7 2 0 1 Bool.false 104500 1000 0 1 qz520)

noncomputable def ep1370 := ep1369 (@Enclosure.Complex.IsNear.re_isNear qz248 Bool.false 7 2 0 1 Bool.false 104500 1000 0 1 qz520)

noncomputable abbrev qz252 := qz519

noncomputable def ep1371 := @Enclosure.Real.IsNear.mulLit_ff qz252 qz252 104500 1000 0 1 104500 1000 0 1 43681 4

noncomputable def ep1372 := @ep1371 0 1 (@Enclosure.Complex.IsNear.im_isNear qz248 Bool.false 7 2 0 1 Bool.false 104500 1000 0 1 qz520)

noncomputable def ep1373 := ep1372 (@Enclosure.Complex.IsNear.im_isNear qz248 Bool.false 7 2 0 1 Bool.false 104500 1000 0 1 qz520)

noncomputable def ep1374 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)) (Real.sqrt (@HAdd.hAdd Real Real Real qz417 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)) (Complex.re (@HMul.hMul Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3))) qz245))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)) (Complex.im (@HMul.hMul Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3))) qz245))))) Bool.false 8522891797 549755813888

noncomputable def ep1375 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz417 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)) (Complex.re (@HMul.hMul Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3))) qz245))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)) (Complex.im (@HMul.hMul Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3))) qz245))))) Bool.false 8522891797 549755813888

noncomputable def ep1376 := nat_lit 3641904746674779549487445227951857230492464395625

noncomputable def ep1377 := nat_lit 15152848975846801455935804345602422347792708605575168

noncomputable def ep1378 := nat_lit 3959761749590153680264473033202616246005478815491142574587462517

noncomputable def ep1379 := nat_lit 42493573284508881572009743126503490780225706251348700675844626089519349760

noncomputable def ep1380 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz417 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)) (Complex.re (@HMul.hMul Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3))) qz245))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)) (Complex.im (@HMul.hMul Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)))) ep1376 ep1377 ep1378 ep1379

noncomputable def ep1381 := nat_lit 5885072639612909255438108139335687528575538265625

noncomputable def ep1382 := nat_lit 30305697951693602911871608691204844695585417211150336

noncomputable def ep1383 := nat_lit 32161462607609925683790306273721248746148456582554146887946055431

noncomputable def ep1384 := nat_lit 424935732845088815720097431265034907802257062513487006758446260895193497600

noncomputable def ep1385 := nat_lit 1398736853736649843536782316568026932409390525625

noncomputable def ep1386 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)) (Complex.re (@HMul.hMul Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3))) qz245))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)) (Complex.im (@HMul.hMul Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3))) qz245))) ep1381 ep1382 ep1383 ep1384 ep1385

noncomputable def ep1387 := nat_lit 7436154888291611118854424058304913713906331572357278857928569739

noncomputable def ep1388 := nat_lit 220740930443130152786662064881030008479732965511017631016757315667776332027459231061963806458511360000

noncomputable def ep1389 := nat_lit 2425916865767025672549125

noncomputable def ep1390 := nat_lit 174085318024506601157689344

noncomputable def ep1391 := nat_lit 55979673109307191094275752541

noncomputable def ep1392 := nat_lit 20613969361699575780227337871436021760

noncomputable def ep1393 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HMul.hMul Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)) (Complex.re (@HMul.hMul Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)) ep1389 ep1390 ep1391 ep1392 ep1389 ep1390 ep1391

noncomputable def ep1394 := nat_lit 26549167067901990151647544933

noncomputable def ep1395 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3))) qz245) Bool.true ep1389 ep1390 ep1391 ep1392 Bool.false 1182682059446514916794475 ep1390 ep1394

noncomputable def ep1396 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3))) qz245 Bool.true ep1389 ep1390 ep1391 ep1392 Bool.false 1182682059446514916794475 ep1390 ep1394 ep1392

noncomputable def ep1397 := nat_lit 58028439341502200385896448

noncomputable def ep1398 := nat_lit 347283503559421408074496927

noncomputable def ep1399 := nat_lit 6871323120566525260075779290478673920

noncomputable def ep1400 := nat_lit 43521329506126650289422336

noncomputable def ep1401 := nat_lit 85840347810357698234456659

noncomputable abbrev qz253 := (Complex.re qz517)

noncomputable abbrev qz254 := (Complex.im qz517)

noncomputable def ep1402 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3)))) qz253) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3)))) qz254) 15454937979896776150045 ep1397 ep1398 ep1399 618070419926679000249815 ep1400 ep1401

noncomputable def ep1403 := nat_lit 32209327127655587156605215424118784

noncomputable def ep1404 := nat_lit 35193042423172246265911882710167199534129610752000

noncomputable def ep1405 := nat_lit 7157628250590130479245603427581952

noncomputable def ep1406 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3)))) qz253 65519 960 0 1 1179424134975867775 302231454903657293676544 5300500672467855249233 ep1405 15454937979896776150045

noncomputable def ep1407 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3)))) 65519 960 0 1 0 1 0 1 65519

noncomputable def ep1408 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 196557 4 0 1 65519 960 0

noncomputable abbrev qz521 := (@HAdd.hAdd Complex Complex Complex qz534 qz582 qz538)

noncomputable abbrev qz255 := qz521

noncomputable def ep1409 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3)) (@HMul.hMul Complex Complex Complex qz81 (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 2)) qz255) Bool.true 196557 4 0 1 Bool.true 4562261 4 0 1

noncomputable abbrev qz256 := (Complex.re qz521)

noncomputable abbrev qz257 := (Complex.im qz521)

noncomputable def ep1410 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 2))) qz256) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 2))) qz257) 109195 4 0 1 43681 2 0 1

noncomputable def ep1411 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 2))) qz256 21839 2 0 1 5 2 0 1 109195 4

noncomputable abbrev qz522 := (@HAdd.hAdd Complex Complex Complex qz534 qz582 (@Nat.cast Complex Complex.instNatCast 1))

noncomputable abbrev qz258 := qz522

noncomputable def ep1412 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 2)) (@HMul.hMul Complex Complex Complex qz81 (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 1)) qz258) Bool.true 21839 2 0 1 Bool.false 209 1 0 1

noncomputable abbrev qz259 := (Complex.re qz522)

noncomputable abbrev qz260 := (Complex.im qz522)

noncomputable def ep1413 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 1))) qz259) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 1))) qz260) 3 4 0 1 43681 4 0 1

noncomputable def ep1414 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 1))) qz259 1 2 0 1 3 2 0 1 3 4

noncomputable def ep1415 := @ep1414 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 104500 1000 0 1 ep1128)

noncomputable def ep1416 := @Enclosure.Complex.IsNear.of_eq qz258 (Complex.mk qz507 qz152) Bool.false 3 2 0 1 Bool.false 104500 1000 0 1 (BSN.s_add_nat_mk qz152 Bool.false 104500 1000 1 qz153)

noncomputable abbrev qz523 := (ep1416 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 3 2) qz152 Bool.false 3 2 0 1 Bool.false 104500 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 3 2) qz154))

noncomputable def ep1417 := ep1415 (@Enclosure.Complex.IsNear.re_isNear qz258 Bool.false 3 2 0 1 Bool.false 104500 1000 0 1 qz523)

noncomputable def ep1418 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 1))) qz260 104500 1000 0 1 104500 1000 0 1 43681 4

noncomputable def ep1419 := @ep1418 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 104500 1000 0 1 ep1128)

noncomputable def ep1420 := ep1419 (@Enclosure.Complex.IsNear.im_isNear qz258 Bool.false 3 2 0 1 Bool.false 104500 1000 0 1 qz523)

noncomputable def ep1421 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 1)) qz258 Bool.true 21839 2 0 1 Bool.false 209 1 0 1 (@ep1413 174712 21839 2 0 1 (ep1417 rfl) (ep1420 rfl) rfl rfl)

noncomputable def ep1422 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 1))) qz260) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 1))) qz259) 209 4 0 1 627 4 0 1

noncomputable def ep1423 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 1))) qz260 1 2 0 1 104500 1000 0 1 209 4

noncomputable def ep1424 := @ep1423 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 104500 1000 0 1 ep1128)

noncomputable def ep1425 := ep1424 (@Enclosure.Complex.IsNear.im_isNear qz258 Bool.false 3 2 0 1 Bool.false 104500 1000 0 1 qz523)

noncomputable def ep1426 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 1))) qz259 104500 1000 0 1 3 2 0 1 627 4

noncomputable def ep1427 := @ep1426 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 104500 1000 0 1 ep1128)

noncomputable def ep1428 := ep1427 (@Enclosure.Complex.IsNear.re_isNear qz258 Bool.false 3 2 0 1 Bool.false 104500 1000 0 1 qz523)

noncomputable abbrev qz261 := (ep1412 (BSN.ascPochhammer_succ_eval_c 1 2 qz439 rfl) (ep1421 (@ep1422 3344 209 1 0 1 (ep1425 rfl) (ep1428 rfl) rfl rfl)))

noncomputable def ep1429 := @ep1411 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 21839 2 0 1 Bool.false 209 1 0 1 qz261)

noncomputable def ep1430 := @Enclosure.Complex.IsNear.of_eq qz255 (Complex.mk qz509 qz152) Bool.false 5 2 0 1 Bool.false 104500 1000 0 1 (BSN.s_add_nat_mk qz152 Bool.false 104500 1000 2 qz153)

noncomputable abbrev qz524 := (ep1430 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 5 2) qz152 Bool.false 5 2 0 1 Bool.false 104500 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 5 2) qz154))

noncomputable def ep1431 := ep1429 (@Enclosure.Complex.IsNear.re_isNear qz255 Bool.false 5 2 0 1 Bool.false 104500 1000 0 1 qz524)

noncomputable def ep1432 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 2))) qz257 209 1 0 1 104500 1000 0 1 43681 2

noncomputable def ep1433 := @ep1432 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 21839 2 0 1 Bool.false 209 1 0 1 qz261)

noncomputable def ep1434 := ep1433 (@Enclosure.Complex.IsNear.im_isNear qz255 Bool.false 5 2 0 1 Bool.false 104500 1000 0 1 qz524)

noncomputable def ep1435 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 2)) qz255 Bool.true 196557 4 0 1 Bool.true 4562261 4 0 1 (@ep1410 393114 196557 4 0 1 (ep1431 rfl) (ep1434 rfl) rfl rfl)

noncomputable def ep1436 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 2))) qz257) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 2))) qz256) 4564351 4 0 1 1045 2 0 1

noncomputable def ep1437 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 2))) qz257 21839 2 0 1 104500 1000 0 1 4564351 4

noncomputable def ep1438 := @ep1437 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 21839 2 0 1 Bool.false 209 1 0 1 qz261)

noncomputable def ep1439 := ep1438 (@Enclosure.Complex.IsNear.im_isNear qz255 Bool.false 5 2 0 1 Bool.false 104500 1000 0 1 qz524)

noncomputable def ep1440 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 2))) qz256 209 1 0 1 5 2 0 1 1045 2

noncomputable def ep1441 := @ep1440 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 21839 2 0 1 Bool.false 209 1 0 1 qz261)

noncomputable def ep1442 := ep1441 (@Enclosure.Complex.IsNear.re_isNear qz255 Bool.false 5 2 0 1 Bool.false 104500 1000 0 1 qz524)

noncomputable abbrev qz262 := (ep1409 (BSN.ascPochhammer_succ_eval_c 2 3 qz439 rfl) (ep1435 (@ep1436 9124522 4562261 4 0 1 (ep1439 rfl) (ep1442 rfl) rfl rfl)))

noncomputable def ep1443 := @ep1408 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1252) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 196557 4 0 1 Bool.true 4562261 4 0 1 qz262)

noncomputable def ep1444 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 4562261 4 0 1 0 1 0

noncomputable def ep1445 := @ep1444 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1252) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 196557 4 0 1 Bool.true 4562261 4 0 1 qz262)

noncomputable def ep1446 := @Enclosure.Real.IsNear.addLit_ft_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3)))) 4562261 2880 0 1 0 1 0 1 4562261

noncomputable def ep1447 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 4562261 4 0 1 4562261 2880 0

noncomputable def ep1448 := @ep1447 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1252) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 196557 4 0 1 Bool.true 4562261 4 0 1 qz262)

noncomputable def ep1449 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 196557 4 0 1 0 1 0

noncomputable def ep1450 := @ep1449 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1252) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 196557 4 0 1 Bool.true 4562261 4 0 1 qz262)

noncomputable def ep1451 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.false 65519 960 0 1 Bool.false 4562261 2880 0 1 (@ep1407 65519 960 0 1 (ep1443 rfl) (ep1445 rfl) rfl rfl) (@ep1446 4562261 2880 0 1 (ep1448 rfl) (ep1450 rfl) rfl rfl)

noncomputable def ep1452 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 65519 960 0 1 Bool.false 4562261 2880 0 1 ep1451

noncomputable def ep1453 := nat_lit 55918970707735394369106276777984

noncomputable def ep1454 := @Enclosure.Complex.IsNear.re_isNear qz245 Bool.false 1179424134975867775 302231454903657293676544 5300500672467855249233 ep1405 Bool.false 677372929701609575 75557863725914323419136 94076542103090658595 ep1453

noncomputable abbrev qz525 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 10460353203)))

noncomputable def ep1455 := @Enclosure.Complex.IsNear.of_eq qz245 (Complex.mk (@HMul.hMul Real Real Real qz0 qz525 qz216) (@HMul.hMul Real Real Real qz0 qz525 qz597)) Bool.false 1179424134975867775 302231454903657293676544 5300500672467855249233 ep1405 Bool.false 677372929701609575 75557863725914323419136 94076542103090658595

noncomputable abbrev qz526 := (Real.sqrt (@Nat.cast Real Real.instNatCast 10460353203))

noncomputable abbrev qz527 := (@Nat.cast Real Real.instNatCast 10460353203)

noncomputable def ep1456 := @Enclosure.Real.IsNear.inv_image qz526 56226753128282463 549755813888 1 549755813888 2687612 2687613 274877906944 (@Enclosure.Real.IsNear.of_eq qz526 (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz527 qz15)) Bool.false 56226753128282463 549755813888 1 549755813888 (BSN.sqrt_natCast_div_one 10460353203) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz527 qz15)) Bool.false 56226753128282463 549755813888 1 549755813888 56226753128282463 549755813888 1 549755813888 (BSN.sqrt_enclosure 10460353203 1 28113376564141231 28113376564141232 274877906944 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep1457 := nat_lit 35523907924500000000000000

noncomputable def ep1458 := nat_lit 17761953962250000000000000

noncomputable def ep1459 := nat_lit 32640387355024858926381268992

noncomputable def ep1460 := nat_lit 9903520314283042199192993792

noncomputable def ep1461 := nat_lit 71047815849000000000000000

noncomputable def ep1462 := nat_lit 165384128016192829869617185803053619675

noncomputable def ep1463 := nat_lit 3756250787496183507247588531701759465

noncomputable def ep1464 := nat_lit 191591553670487038802158425

noncomputable def ep1465 := BSN.log_dyadic_bound 11 43 10 9 ep1462 274877906944 71047815849 ep1463 ep1464 143829354570 54 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base9 (BSN.artanhP 11) (BSN.artanhQ 43) 0 9 ep1463 ep1462 ep1464 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep1466 := @Enclosure.Real.IsNear.mulLit_ff qz152 (Real.log (Enclosure.sfrac Bool.false 27 1)) 104500 1000 0 1 3710782420401399 1125899906842624 250071047815849 ep1458 775553525863892391 2251799813685248 52264848993512441 ep1457 qz154 (BSN.isNear_log_sfrac 27 1 3710782420401399 1125899906842624 250071047815849 ep1458 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz493) Bool.false ep1459 ep1460 1000284191263396 ep1461 3710782420401399 1125899906842624 250071047815849 ep1458 (BSN.log_rat_reduce_isNear 27 1 4 54 32 143829354570 274877906944 24973259072661432 36028797018963968 71047815849 1000000000000000 rfl rfl rfl rfl (ep1465 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1467 := nat_lit 8131917777857095091630374912

noncomputable def ep1468 := nat_lit 221859320419280750341286229374643082974032674422290385167615156285963641121322789456087045615304753215975255707769673580800

noncomputable def ep1469 := nat_lit 937046835760177389014339949136452948956763638101868628335989667301470209077471332707205705798296416271460543045470610396282880

noncomputable def ep1470 := nat_lit 2084420601222426112097033492390917437784850938488320505007628123274765061727866515606474968218060042152727011616850176

noncomputable def ep1471 := nat_lit 581056750131428557442044348403172774875186305156860122920079206493895662840983555839202708985373429182724089105187479716096

noncomputable def ep1472 := nat_lit 17179191988936585465262899067501637397540666698534258186159810567193620499753641099632104606302100964976776622500294523931852800

noncomputable def ep1473 := BSN.sin_dyadic_bound_f 462246008388382 1125899906842624 3 2 549755813888 142234396964 ep1468 ep1469 ep1470 ep1471 ep1472 ep1470 219418561079 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 462246008388382) (BSN.sinEvenQ 1125899906842624) 0 2 ep1468 ep1469 ep1470 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 462246008388382) (BSN.sinOddQ 1125899906842624) 0 2 ep1471 ep1472 ep1470 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz528 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 47336030631341) (@Nat.cast Real Real.instNatCast 137438953472))

noncomputable def ep1474 := @Enclosure.Real.IsNear.cos_image qz218 qz528 Bool.false 47336030631341 137438953472 405 274877906944 Bool.false 219418561079 549755813888 1 71047815849 (@Enclosure.Real.IsNear.recentre' qz218 Bool.false 775553525863892391 2251799813685248 52264848993512441 ep1457 47336030631341 137438953472 405 274877906944 (ep1466 rfl) rfl) (Enclosure.sfrac_false_div 47336030631341 137438953472) (BSN.cos_reduce3 qz528 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep1467) (@Nat.cast Real Real.instNatCast ep1173)) 226375608064910080 72057594037927936 Bool.false 219418561079 549755813888 54 1000000000000000 142095631698 71047815849 (BSN.sin_reduce_arg_pos_rat_q3 47336030631341 137438953472 226375608064910080 72057594037927936 54 ep1467 ep1173 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 219418561079 549755813888 ep1467 ep1173 462246008388382 1125899906842624 142234396964 142095631698 (ep1473 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1475 := nat_lit 123256104419867626823431059445242775393323834612800653235566201326923478296317873194055294886266293146671654382988315033856

noncomputable def ep1476 := nat_lit 104116315084464154334926661015161438772973737566874292037332185255718912119719036967467300644255157363495615893941178932920320

noncomputable def ep1477 := nat_lit 369764144418400435618068984268743544345095934136524983065688588724523885358830163849134671708862443319930657694941711401216

noncomputable def ep1478 := nat_lit 4685234178800886945071699745682264744783818190509343141679948336507351045387356663536028528991482081357302715227353051981414400

noncomputable def ep1479 := BSN.cos_dyadic_bound_f 462246008388382 1125899906842624 3 2 549755813888 142234396964 ep1475 ep1476 ep1470 ep1477 ep1478 ep1470 504070381948 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 462246008388382) (BSN.cosEvenQ 1125899906842624) 0 2 ep1475 ep1476 ep1470 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 462246008388382) (BSN.cosOddQ 1125899906842624) 0 2 ep1477 ep1478 ep1470 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1480 := @Enclosure.Real.IsNear.sin_image qz218 qz528 Bool.false 47336030631341 137438953472 405 274877906944 Bool.true 504070381948 549755813888 1 71047815849 (@Enclosure.Real.IsNear.recentre' qz218 Bool.false 775553525863892391 2251799813685248 52264848993512441 ep1457 47336030631341 137438953472 405 274877906944 (ep1466 rfl) rfl) (Enclosure.sfrac_false_div 47336030631341 137438953472) (BSN.sin_reduce3 qz528 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep1467) (@Nat.cast Real Real.instNatCast ep1173)) 226375608064910080 72057594037927936 Bool.false 504070381948 549755813888 54 1000000000000000 142095631698 71047815849 (BSN.sin_reduce_arg_pos_rat_q3 47336030631341 137438953472 226375608064910080 72057594037927936 54 ep1467 ep1173 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 504070381948 549755813888 ep1467 ep1173 462246008388382 1125899906842624 142234396964 142095631698 (ep1479 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1481 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz525 qz216) (@HMul.hMul Real Real Real qz0 qz525 qz597) Bool.false 1179424134975867775 302231454903657293676544 5300500672467855249233 ep1405 Bool.false 677372929701609575 75557863725914323419136 94076542103090658595 ep1453 (@Enclosure.Real.IsNear.mulLit_ff qz525 qz216 5375225 549755813888 1 549755813888 219418561079 549755813888 29049243325789 19529474913515870355456 1179424134975867775 302231454903657293676544 5300500672467855249233 ep1405 (@Enclosure.Real.IsNear.recentre' qz525 Bool.false 5375225 549755813888 1 549755813888 5375225 549755813888 1 549755813888 (ep1456 rfl rfl) rfl) (@Enclosure.Real.IsNear.recentre' qz216 Bool.false 219418561079 549755813888 29049243325789 19529474913515870355456 219418561079 549755813888 29049243325789 19529474913515870355456 (ep1474 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz525 qz597 5375225 549755813888 1 549755813888 126017595487 137438953472 29049243325789 19529474913515870355456 677372929701609575 75557863725914323419136 94076542103090658595 ep1453 (@Enclosure.Real.IsNear.recentre' qz525 Bool.false 5375225 549755813888 1 549755813888 5375225 549755813888 1 549755813888 (ep1456 rfl rfl) rfl) (@Enclosure.Real.IsNear.neg qz217 Bool.true 126017595487 137438953472 29049243325789 19529474913515870355456 (@Enclosure.Real.IsNear.recentre' qz217 Bool.true 504070381948 549755813888 29049243325789 19529474913515870355456 126017595487 137438953472 29049243325789 19529474913515870355456 (ep1480 rfl rfl) rfl)) rfl)

noncomputable def ep1482 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3)))) qz254 4562261 2880 0 1 677372929701609575 75557863725914323419136 94076542103090658595 ep1453 618070419926679000249815

noncomputable def ep1483 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 65519 960 0 1 Bool.false 4562261 2880 0 1 ep1451

noncomputable def ep1484 := @Enclosure.Complex.IsNear.im_isNear qz245 Bool.false 1179424134975867775 302231454903657293676544 5300500672467855249233 ep1405 Bool.false 677372929701609575 75557863725914323419136 94076542103090658595 ep1453

noncomputable def ep1485 := nat_lit 14507109835375550096474112

noncomputable def ep1486 := nat_lit 1232760192410479372097161

noncomputable def ep1487 := nat_lit 10736442375885195718868405141372928

noncomputable def ep1488 := nat_lit 24182267498473869757220995813

noncomputable def ep1489 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3)))) qz254) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3)))) qz253) 8876159396223951548885 ep1485 ep1486 ep1487 1076168146691827498207855 ep1390 ep1488

noncomputable def ep1490 := nat_lit 17157298536718747567426675086597528178750862131200

noncomputable def ep1491 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3)))) qz254 65519 960 0 1 677372929701609575 75557863725914323419136 94076542103090658595 ep1453 8876159396223951548885

noncomputable def ep1492 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3)))) qz253 4562261 2880 0 1 1179424134975867775 302231454903657293676544 5300500672467855249233 ep1405 1076168146691827498207855

noncomputable abbrev qz529 := (@ep1455 ep1453 (BSN.cpow_neg_s_sub_mk qz152 104500 1000 27 3 10460353203 qz153 rfl EMRow31.d22) ep1481)

noncomputable def ep1493 := ep1396 (@ep1402 ep1403 ep1404 ep1389 ep1390 ep1391 ep1392 (@ep1406 ep1397 ep1398 ep1399 ep1452 (ep1454 qz529) rfl) (@ep1482 ep1400 ep1401 ep1403 ep1483 (ep1484 qz529) rfl) rfl rfl) (@ep1489 ep1392 ep1490 1182682059446514916794475 ep1390 ep1394 ep1392 (@ep1491 ep1485 ep1486 ep1487 ep1452 (ep1484 qz529) rfl) (@ep1492 ep1390 ep1488 ep1392 ep1483 (ep1454 qz529) rfl) rfl rfl)

noncomputable def ep1494 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)) (Complex.im (@HMul.hMul Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)) 1182682059446514916794475 ep1390 ep1394 ep1392 1182682059446514916794475 ep1390 ep1394

noncomputable def ep1495 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3))) qz245) Bool.true ep1389 ep1390 ep1391 ep1392 Bool.false 1182682059446514916794475 ep1390 ep1394

noncomputable def ep1496 := @ep1361 133489957140568585 288230376151711744 189753904105 2017612633061982208 (@ep1362 1 3670016 (ep1363 (@ep1364 1048576 1 1048576 (ep1365 (@ep1366 174920 21865 2 0 1 (ep1370 rfl) (ep1373 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) (Enclosure.Real.IsNear.const Bool.false 2 7) rfl) (@ep1374 1653 549755813888 (BSN.norm_eq_sqrt_mul_add (@HMul.hMul Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)) (@ep1375 1653 549755813888 8522891797 549755813888 1653 549755813888 (@ep1380 4261445072 4261446725 274877906944 (@ep1386 ep1382 ep1387 ep1384 ep1388 ep1376 ep1377 ep1378 ep1379 (@ep1393 ep1392 ep1381 ep1382 ep1383 ep1384 (@ep1395 ep1392 ep1493) (@ep1395 ep1392 ep1493) rfl) (@ep1494 ep1392 ep1385 ep1382 ep1387 ep1384 (@ep1495 ep1392 ep1493) (@ep1495 ep1392 ep1493) rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl

theorem EMRow31.d23 : Enclosure.Real.IsNear (@HAdd.hAdd Real Real Real qz417 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz149 1 27))) (@HMul.hMul Real Real Real qz0 qz244 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)))) Bool.false 413944517919919643 864691128455135232 1758216198105905 18158513697557839872 := ep1359 (ep1360 ep1496) rfl rfl

noncomputable def EMRow31.d24 := fun (I J : @NonemptyInterval Real Real.instLE) => @LE.le Real Real.instLE (@Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE I)) (@Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE J))

noncomputable abbrev qz530 := (EMRow31.d3 qz540 qz584 (@Enclosure.dec_le_dec qz540 qz584 102256 1000 104500 1000 (@Eq.refl Real qz540) (@Eq.refl Real qz584) rfl rfl rfl) 26 27 1 1)

noncomputable abbrev qz263 := qz530

noncomputable def ep1497 := @Zeta.Certificates.ZIntervalEM.Certificate.mk qz263 (@Enclosure.dec_nonneg qz13 102256 1000 qz14) (@Enclosure.pos_of_ble 1 rfl) (@Enclosure.pos_of_ble 26 rfl)

noncomputable abbrev qz264 := (Zeta.Certificates.ZIntervalEM.fstVal qz530)

noncomputable def ep1498 := @Enclosure.Real.IsNear.neg_val qz264 ep395 ep396

noncomputable def ep1499 := @Enclosure.Real.IsNear.of_eq qz264 (hardyZApproximantEM 1 26 qz13) Bool.true

noncomputable abbrev qz265 := (Zeta.Certificates.ZIntervalEM.sndVal qz530)

noncomputable def ep1500 := BSN.mul_neg_of_neg_pos_r qz264 qz265 (@ep1498 ep397 ep398 (@ep1499 ep395 ep396 ep397 ep398 (@Eq.refl Real (hardyZApproximantEM 1 26 qz13)) EMRow31.d11) rfl rfl rfl)

noncomputable def ep1501 := @Enclosure.Real.IsNear.pos_val qz265 705783457210689610643749 679885881717189909676032

noncomputable def ep1502 := @Enclosure.Real.IsNear.of_eq qz265 (hardyZApproximantEM 1 27 qz152) Bool.false

noncomputable def ep1503 := BSN.gt_trans_le (@Norm.norm Real Real.norm qz264) (BSN.hardyZErrorBoundStrong 1 26 qz13)

noncomputable def ep1504 := @Enclosure.norm_gt_of_isNear qz264 (BSN.hardyZErrorBoundStrong 1 26 qz13) Bool.true

noncomputable def ep1505 := @Enclosure.Real.IsNear.of_eq (BSN.hardyZErrorBoundStrong 1 26 qz13) (@HAdd.hAdd Real Real Real qz417 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 26))) (@HMul.hMul Real Real Real qz0 qz222 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)))) Bool.false 14039028922352390549 27237770546336759808 2531685344314951 27237770546336759808 (@Eq.refl Real (@HAdd.hAdd Real Real Real qz417 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 26))) (@HMul.hMul Real Real Real qz0 qz222 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)))))

noncomputable def ep1506 := BSN.gt_trans_le (@Norm.norm Real Real.norm qz265) (BSN.hardyZErrorBoundStrong 1 27 qz152)

noncomputable def ep1507 := @Enclosure.norm_gt_of_isNear qz265 (BSN.hardyZErrorBoundStrong 1 27 qz152) Bool.false

noncomputable def ep1508 := @Enclosure.Real.IsNear.of_eq (BSN.hardyZErrorBoundStrong 1 27 qz152) (@HAdd.hAdd Real Real Real qz417 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz149 1 27))) (@HMul.hMul Real Real Real qz0 qz244 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)))) Bool.false 413944517919919643 864691128455135232 1758216198105905 18158513697557839872 (@Eq.refl Real (@HAdd.hAdd Real Real Real qz417 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz149 1 27))) (@HMul.hMul Real Real Real qz0 qz244 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz81 (@HDiv.hDiv Complex Complex Complex qz88 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)))))

noncomputable def ep1509 := @List.cons EMRow31.d0 (@PSigma.mk Zeta.Certificates.ZIntervalEM Zeta.Certificates.ZIntervalEM.Certificate qz263 (ep1497 (@Enclosure.pos_of_ble 1 rfl) (@Enclosure.pos_of_ble 27 rfl) (ep1500 (@ep1501 ep942 ep943 (@ep1502 705783457210689610643749 679885881717189909676032 ep942 ep943 (@Eq.refl Real (hardyZApproximantEM 1 27 qz152)) EMRow31.d16) rfl rfl rfl)) (ep1503 (hardyZErrorBoundEM 1 26 qz13) (BSN.hardyZErrorBoundEM_le_strong 1 26 qz13 rfl) (@ep1504 Bool.false ep395 ep396 ep397 ep398 14039028922352390549 27237770546336759808 2531685344314951 27237770546336759808 (@ep1499 ep395 ep396 ep397 ep398 (@Eq.refl Real (hardyZApproximantEM 1 26 qz13)) EMRow31.d11) (ep1505 EMRow31.d21) rfl rfl rfl rfl rfl)) (ep1506 (hardyZErrorBoundEM 1 27 qz152) (BSN.hardyZErrorBoundEM_le_strong 1 27 qz152 rfl) (@ep1507 Bool.false 705783457210689610643749 679885881717189909676032 ep942 ep943 413944517919919643 864691128455135232 1758216198105905 18158513697557839872 (@ep1502 705783457210689610643749 679885881717189909676032 ep942 ep943 (@Eq.refl Real (hardyZApproximantEM 1 27 qz152)) EMRow31.d16) (ep1508 EMRow31.d23) rfl rfl rfl rfl rfl)))) (@List.nil EMRow31.d0)

noncomputable abbrev qz531 := (@Enclosure.dec_le_dec qz540 qz584 102256 1000 104500 1000 (@Eq.refl Real qz540) (@Eq.refl Real qz584) rfl rfl rfl)

noncomputable abbrev qz266 := (Zeta.Certificates.CertifiedZeroIntervals.intervals (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedEM ep1509 (@List.IsChain.singleton EMRow31.d1 EMRow31.d24 (EMRow31.d2 qz284 qz441 qz531))))

noncomputable abbrev qz532 := (@NonemptyInterval Real Real.instLE)

noncomputable def ep1510 := And (@Eq (Option Real) (@Option.map qz532 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz532 qz266)) (@Option.some Real qz13))

noncomputable def ep1511 := ep1510 (@Eq (Option Real) (@Option.map qz532 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz532 qz266)) (@Option.some Real qz152))

noncomputable def ep1512 := @And.intro (@Eq Nat (@List.length qz532 qz266) 1) ep1511

noncomputable def ep1513 := @And.intro (@Eq (Option Real) (@Option.map qz532 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz532 qz266)) (@Option.some Real qz13))

noncomputable def ep1514 := @ep1513 (@Eq (Option Real) (@Option.map qz532 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz532 qz266)) (@Option.some Real qz152))

noncomputable abbrev qz267 := (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedEM ep1509 (@List.IsChain.singleton EMRow31.d1 EMRow31.d24 (EMRow31.d2 qz284 qz441 qz531)))

theorem EMRow31.d25 : Zeta.Certificates.BatchSpec 1 102256 1000 104500 1000 := @Exists.intro Zeta.Certificates.CertifiedZeroIntervals (fun (C : Zeta.Certificates.CertifiedZeroIntervals) => And (@Eq Nat (@List.length qz532 (Zeta.Certificates.CertifiedZeroIntervals.intervals C)) 1) (And (@Eq (Option Real) (@Option.map qz532 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz532 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz13)) (@Eq (Option Real) (@Option.map qz532 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz532 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz152)))) qz267 (ep1512 (@Eq.refl Nat 1) (ep1514 (@Eq.refl (Option Real) (@Option.some Real qz13)) (@Eq.refl (Option Real) (@Option.some Real qz152))))

theorem solution : Zeta.Certificates.BatchSpec 1 102256 1000 104500 1000 := EMRow31.d25
#print axioms solution
#check solution
