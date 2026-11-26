-- Prove2me | solution 1 for RHHeight1000.em_main_0022_0022
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-20T08:20:52.583026+00:00
-- url     : https://prove2.me/submissions/4d4374ac-d239-4ac8-8210-0f5470f52817

import Definitions.Def_RHT1000_Support_20261118_S005
/- Copyright (c) 2026 Salvatore Mercuri, Bhavik Mehta.
Apache 2.0 license; see the source project LICENSE. -/
set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable def EMRow22.d0 := @PSigma Zeta.Certificates.ZIntervalEM fun (I : Zeta.Certificates.ZIntervalEM) => Zeta.Certificates.ZIntervalEM.Certificate I

noncomputable def EMRow22.d1 := @NonemptyInterval Real Real.instLE

noncomputable def EMRow22.d2 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @NonemptyInterval.mk Real Real.instLE (@Prod.mk Real Real a b) h

noncomputable def EMRow22.d3 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) (fc sc fb sb : Nat) => Zeta.Certificates.ZIntervalEM.mk (EMRow22.d2 a b h) fc sc fb sb

noncomputable def ep0 := nat_lit 26986075409044028275299783

noncomputable def ep1 := nat_lit 4294967296000000000000000

noncomputable def ep2 := nat_lit 26986075409044045455168967

noncomputable abbrev qz265 := (@instHMul Real Real.instMul)

noncomputable abbrev qz0 := qz265

noncomputable abbrev qz266 := (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 2 1) Real.pi)

noncomputable def ep3 := @BSN.isNear_log_image_fff qz266 884279719003555 140737488355328 1 500000000000000 ep0 ep1 ep2 ep1 4138529546116343 2251799813685248 2500000000819 409500000000000000 4138529546116343 2251799813685248 2500000000819 409500000000000000 481788 262144

noncomputable abbrev qz267 := (@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 2 1) Real.pi 2 1 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 140737488355328 1 500000000000000 (Enclosure.Real.IsNear.const Bool.false 2 1) BSN.pi_near_15 rfl)

noncomputable def ep4 := @ep3 2 262144 qz267 rfl rfl rfl rfl

noncomputable def ep5 := nat_lit 53972150818088056550599566

noncomputable def ep6 := nat_lit 34359738368000000000000000

noncomputable def ep7 := nat_lit 9806206225044028275299783

noncomputable def ep8 := nat_lit 44165944593044028275299783

noncomputable def ep9 := nat_lit 13681445815609410487519367394620474863599256634174726093703677122907123617368241606644861540940610176751640793056574796245399519365549113997355475306157239709119582688278313060810592403844863400465080549957745

noncomputable def ep10 := nat_lit 231714499556395493334623298703961145503103241611736774613091488581016477543539392410113701224645713379230392133956226737605624599560350113120270717249177907454870984269546186598262646369758174842349131395304

noncomputable def ep11 := nat_lit 8978369550011295664474073352761810093897501552430546263638635096022803738134167562509900960712119243631997923545019968443113540909076206607473711060286601587364321108377403290080403445693385008949995305

noncomputable def ep12 := BSN.log_dyadic_bound ep7 ep8 5 4 ep9 524288 163800 ep10 ep11 236759 ep5 ep6 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP ep7) (BSN.artanhQ ep8) 0 4 ep10 ep9 ep11 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz268 := (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))

noncomputable abbrev qz1 := qz268

noncomputable def ep13 := ep4 rfl rfl rfl rfl (BSN.isNear_log_sfrac ep0 ep1 4138529546116343 2251799813685248 2500000000819 409500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep0) (@Nat.cast Real Real.instNatCast ep1))) Bool.false 34716502058787923820544 18889465931478580854784 1000000000327600 163800000000000000000 4138529546116343 2251799813685248 2500000000819 409500000000000000 (BSN.log_rat_reduce_isNear ep0 ep1 2 ep5 ep6 236759 524288 24973259072661432 36028797018963968 163800 1000000000000000 rfl rfl rfl rfl (ep12 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep14 := nat_lit 53972150818088090910337934

noncomputable def ep15 := nat_lit 9806206225044045455168967

noncomputable def ep16 := nat_lit 44165944593044045455168967

noncomputable def ep17 := nat_lit 13681445815609453062485491347592146866046743284321690683909457683007658987562290830600045658905080811372395010565947827677605470036294121079488508864180301737865471494204890974265645509835068840465080549957745

noncomputable def ep18 := nat_lit 231714499556396865510889920206523150079811393376960301632499817942333196803513131357563499488546302200815366867712007119763002650772307103678175657719139104636874731038771518520299266622696414842349131395304

noncomputable def ep19 := nat_lit 8978369550011421500876706511871067098718760264493934208903156435737864998391937547068187824077011975074541700434630537294838404525415248443919841847024664017658842168336182958576672102333385008949995305

noncomputable def ep20 := BSN.log_dyadic_bound ep15 ep16 5 4 ep17 524288 163800 ep18 ep19 236759 ep14 ep6 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP ep15) (BSN.artanhQ ep16) 0 4 ep18 ep17 ep19 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep21 := ep13 (BSN.isNear_log_sfrac ep2 ep1 4138529546116343 2251799813685248 2500000000819 409500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep2) (@Nat.cast Real Real.instNatCast ep1))) Bool.false 34716502058787923820544 18889465931478580854784 1000000000327600 163800000000000000000 4138529546116343 2251799813685248 2500000000819 409500000000000000 (BSN.log_rat_reduce_isNear ep2 ep1 2 ep14 ep6 236759 524288 24973259072661432 36028797018963968 163800 1000000000000000 rfl rfl rfl rfl (ep20 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable abbrev qz269 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)

noncomputable abbrev qz2 := (Real.log qz269)

theorem EMRow22.d4 : Enclosure.Real.IsNear qz2 Bool.false 120447 65536 1 131072 := @Enclosure.Real.IsNear.of_eq qz2 (Real.log qz266) Bool.false 120447 65536 1 131072 BSN.log_two_pi_eq (@Enclosure.Real.IsNear.recentre' (Real.log qz266) Bool.false 481788 262144 2 262144 120447 65536 1 131072 (ep21 rfl rfl rfl rfl rfl rfl rfl rfl) rfl)

noncomputable def ep22 := nat_lit 8589934592000000000000000

noncomputable def ep23 := @BSN.isNear_log_image_fff Real.pi 226375608064910080 72057594037927936 1 1000000000000000 ep0 ep22 ep2 ep22 600168 524288 1 163800 600168 524288 1 163800 300084 262144 2 262144 BSN.pi_near_15 rfl rfl rfl

noncomputable def ep24 := nat_lit 17179869184000000000000000

noncomputable def ep25 := nat_lit 18396140817044028275299783

noncomputable def ep26 := nat_lit 35576010001044028275299783

noncomputable def ep27 := nat_lit 145019262663961446558303139663424756232419223153299357158415217874016130572233056993847515999529612750616182853355499335896178729185698845314776375864537073527142908641610750276034469165612529925303649396973267518946591078603565291376312767403717761600170009932259137778521478520425507632472584532570900560707662248426541531715360699177249902784721815296292248142738824858695953661559845440650653128788875447728828657762006237171740033404723254477174341920697506370253193455781322964835857351124092897592956162654178130575

noncomputable def ep28 := nat_lit 15500762873619990602332184736899274490522931101512051618692838888825382235673431503644115344741331161500627469184702974962114537943617674254904297224139410345221262767191485292268260077615645253784097850065864022184521411511133693085443040736512010941548648374196772723338837137976260321103066698629790037694560548409922339907589559883712609967105556007429010014773911317423638534096849366294542840133852248768895750397896505791271178551667935288585787166713880920071720072716082683081155281219708172458141800988558163320

noncomputable def ep29 := nat_lit 12900190794487083783367107939442176642390171280542213571554777169279725287102813254708993369099729304728646904879886535518616983985412662170766446331701281703998252143668221340329975389245922410714088123244705567402747658401492589451585970559635763980329972215329212888079422466283203384882259392047898400615815810081169907384366653346471604103896809335921621947903075223769953790093549808584241881353287841076643853121427928248525828402335494512605306631304432120211393210317325496757155861061354331245840675149075

noncomputable def ep30 := BSN.log_dyadic_bound ep25 ep26 11 10 ep27 524288 163800 ep28 ep29 600168 ep5 ep24 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base10 (BSN.artanhP ep25) (BSN.artanhQ ep26) 0 10 ep28 ep27 ep29 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep31 := nat_lit 18396140817044045455168967

noncomputable def ep32 := nat_lit 35576010001044045455168967

noncomputable def ep33 := nat_lit 145019262663962847171784895425483977818796535899227200426399035286881207006285364467913811844950531107314785650583974625982406238691319033447632878979985852280879486690814033867010958364699188952871572448188560932645032521756218245629809291975913196623825614492380080480004685076434733043183791438169545293975334857826316990371107134320667652578346815517853870648072772035977941843998949310557583393428557296298890786965786350523173236912472938174255438182435383147950274229549088258679583524155427309880956162654178130575

noncomputable def ep34 := nat_lit 15500762873620157189619721156942591192100275120160672416764593300158228469749443299607348495591439275767946573253526107895503597951484257520435868240203420954375895980141891044871083424251900562230440202302413072793440172565998181227591194192658878334739610458454844032013325963992941389843551995646587189684848765634635122388286241104146031552341815777883628509454807838726994150833304950745987647656768534710890974432620160470644835720379148964170536679305861738540146791997074363921127776563807649880221800988558163320

noncomputable def ep35 := nat_lit 12900190794487324729109480814509220959173684627296055849229843377126536688487849343376525559792931631054411655715865486295286288812423905434305314401904993536755333953308594664509631000767632482919425633906965368325056855874260596615770736441041599390097968820060635361729170158825410327022636428624381203910573184452046894301676992229743752846881064485858738985580654099214803581683226335297196686880535448467637789069028262446657986458573827723305156755787640135484017403116612632808333639900906331245840675149075

noncomputable def ep36 := BSN.log_dyadic_bound ep31 ep32 11 10 ep33 524288 163800 ep34 ep35 600168 ep14 ep24 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base10 (BSN.artanhP ep31) (BSN.artanhQ ep32) 0 10 ep34 ep33 ep35 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep37 := @Enclosure.Real.IsNear.recentre' (Real.log Real.pi) Bool.false 300084 262144 2 262144 75021 65536 1 131072 (ep23 rfl rfl rfl rfl rfl (BSN.isNear_log_sfrac ep0 ep22 600168 524288 1 163800 Bool.false (BSN.logfrac_isNear ep5 ep24 1 ep0 ep22 600168 524288 163800 rfl rfl rfl (ep30 rfl))) (BSN.isNear_log_sfrac ep2 ep22 600168 524288 1 163800 Bool.false (BSN.logfrac_isNear ep14 ep24 1 ep2 ep22 600168 524288 163800 rfl rfl rfl (ep36 rfl))) rfl rfl rfl rfl rfl rfl rfl rfl) rfl

theorem EMRow22.d5 : Enclosure.Real.IsNear (Real.log Real.pi) Bool.false 75021 65536 1 131072 := ep37

noncomputable abbrev qz502 := (@HAdd.hAdd Complex Complex Complex (@instHAdd Complex Complex.instAdd) (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (2 : Complex)) (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul) Complex.I ↑(Enclosure.sfrac Bool.false 81143 1000)))

noncomputable abbrev qz477 := qz502

noncomputable abbrev qz270 := qz477

noncomputable abbrev qz3 := (BSN.headSumC qz270 9)

noncomputable abbrev qz503 := (@instHAdd Complex Complex.instAdd)

noncomputable abbrev qz478 := qz503

noncomputable abbrev qz271 := qz478

noncomputable abbrev qz4 := qz271

noncomputable abbrev qz5 := qz270

noncomputable abbrev qz479 := (@instHPow Complex Complex Complex.instPow)

noncomputable abbrev qz272 := qz479

noncomputable abbrev qz480 := (@Neg.neg Complex Complex.instNeg qz502)

noncomputable abbrev qz273 := qz480

noncomputable abbrev qz6 := (@HPow.hPow Complex Complex Complex qz272 (@Nat.cast Complex Complex.instNatCast 8) qz273)

noncomputable def ep38 := @Enclosure.Complex.IsNear.of_eq qz3 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 8) qz6) Bool.false 13475398257 4294967296 455175817867 134002979635200 Bool.false 197796089 2147483648 28458785287 8375186227200

noncomputable def ep39 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 8) qz6 Bool.false 803077631375 274877906944 5704320770327 1876041714892800 Bool.true 51639442681 274877906944 5705978849477 1876041714892800 Bool.false

noncomputable abbrev qz7 := (@HPow.hPow Complex Complex Complex qz272 (@Nat.cast Complex Complex.instNatCast 7) qz273)

noncomputable def ep40 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 8) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 7) qz7) Bool.false 803077631375 274877906944 5704320770327 1876041714892800 Bool.true 51639442681 274877906944 5705978849477 1876041714892800

noncomputable def ep41 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 7) qz7 Bool.false 731976350649 274877906944 1151522306171 432932703436800 Bool.false 24114308959 274877906944 1151867961971 432932703436800 Bool.false

noncomputable abbrev qz8 := (@HPow.hPow Complex Complex Complex qz272 (@Nat.cast Complex Complex.instNatCast 6) qz273)

noncomputable def ep42 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 7) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 6) qz8) Bool.false 731976350649 274877906944 1151522306171 432932703436800 Bool.false 24114308959 274877906944 1151867961971 432932703436800

noncomputable def ep43 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 6) qz8 Bool.false 330039790177 137438953472 3163993448617 1407031286169600 Bool.false 27568766573 68719476736 6329551412459 2814062572339200 Bool.false

noncomputable abbrev qz9 := (@HPow.hPow Complex Complex Complex qz272 (@Nat.cast Complex Complex.instNatCast 5) qz273)

noncomputable def ep44 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 6) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 5) qz9) Bool.false 330039790177 137438953472 3163993448617 1407031286169600 Bool.false 27568766573 68719476736 6329551412459 2814062572339200

noncomputable def ep45 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 5) qz9 Bool.false 158362030599 68719476736 1687752276863 938020857446400 Bool.true 1216826099 34359738368 1686914740163 938020857446400 Bool.false

noncomputable abbrev qz10 := (@HPow.hPow Complex Complex Complex qz272 (@Nat.cast Complex Complex.instNatCast 4) qz273)

noncomputable def ep46 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 5) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 4) qz10) Bool.false 158362030599 68719476736 1687752276863 938020857446400 Bool.true 1216826099 34359738368 1686914740163 938020857446400

noncomputable def ep47 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 4) qz10 Bool.false 260378258349 137438953472 91086718007 70351564308480 Bool.true 44205269405 137438953472 182114226409 140703128616960 Bool.false

noncomputable abbrev qz481 := (@Nat.cast Complex Complex.instNatCast 3)

noncomputable abbrev qz274 := qz481

noncomputable abbrev qz11 := (@HPow.hPow Complex Complex Complex qz272 qz274 qz273)

noncomputable def ep48 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 4) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 3) qz11) Bool.false 260378258349 137438953472 91086718007 70351564308480 Bool.true 44205269405 137438953472 182114226409 140703128616960

noncomputable def ep49 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 3) qz11 Bool.false 57536309039 34359738368 401623499701 562812514467840 Bool.false 7289949051 34359738368 400219651801 562812514467840 Bool.false

noncomputable abbrev qz482 := (@Nat.cast Complex Complex.instNatCast 2)

noncomputable abbrev qz275 := qz482

noncomputable abbrev qz12 := (@HPow.hPow Complex Complex Complex qz272 qz275 qz273)

noncomputable def ep50 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 3) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 2) qz12) Bool.false 57536309039 34359738368 401623499701 562812514467840 Bool.false 7289949051 34359738368 400219651801 562812514467840

noncomputable def ep51 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 2) qz12 Bool.false 1 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable abbrev qz276 := (Enclosure.sfrac Bool.false 0 1)

noncomputable abbrev qz13 := qz276

noncomputable def ep52 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 2) (Complex.mk (Enclosure.sfrac Bool.false 1 1) qz13) Bool.false 1 1 0 1 Bool.false 0 1 0 1 (BSN.head_sum_c_two qz5)

noncomputable abbrev qz277 := (@Nat.cast Real Real.instNatCast 2)

noncomputable abbrev qz14 := (@Inv.inv Real Real.instInv (Real.sqrt qz277))

noncomputable abbrev qz504 := (Enclosure.sfrac Bool.false 81143 1000)

noncomputable abbrev qz483 := qz504

noncomputable abbrev qz278 := qz483

noncomputable abbrev qz279 := (Enclosure.sfrac Bool.false 2 1)

noncomputable abbrev qz15 := (@HMul.hMul Real Real Real qz265 qz278 (Real.log qz279))

noncomputable abbrev qz16 := qz278

noncomputable abbrev qz280 := (@Eq.refl Real qz483)

noncomputable abbrev qz17 := qz280

noncomputable def ep53 := @Enclosure.Complex.IsNear.of_eq qz12 (Complex.mk (@HMul.hMul Real Real Real qz0 qz14 (Real.cos qz15)) (@HMul.hMul Real Real Real qz0 qz14 (@Neg.neg Real Real.instNeg (Real.sin qz15)))) Bool.false 23176570671 34359738368 401623499701 562812514467840 Bool.false 7289949051 34359738368 400219651801 562812514467840 (BSN.cpow_neg_s_mk qz16 81143 1000 2 qz17 rfl)

noncomputable abbrev qz18 := (@Nat.cast Real Real.instNatCast 1)

noncomputable def ep54 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz277) 741455 524288 1 524288 185363 185365 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz277) (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz277 qz18)) Bool.false 741455 524288 1 524288 (BSN.sqrt_natCast_div_one 2) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz277 qz18)) Bool.false 741455 524288 1 524288 741455 524288 1 524288 (BSN.sqrt_enclosure 2 1 370727 370728 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep55 := BSN.log_dyadic_bound 1 3 6 5 613814355 262144 81900 24381081 945 181704 4 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 1) (BSN.artanhQ 3) 0 5 24381081 613814355 945 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep56 := nat_lit 13739091737463338076642898879200177197588466338739395322291356684855379452160

noncomputable def ep57 := nat_lit 641153462866780105519186997069590271023477356498224607523168458325065864314880

noncomputable def ep58 := nat_lit 11663149787510043615569031428700026548431852213144148096920137839076925696

noncomputable def ep59 := nat_lit 35964452307986107272972861489877806903081855507400944842415682522881774018816

noncomputable def ep60 := nat_lit 11754480152557635267851761612942488302097084869134117804591421735959540845772800

noncomputable abbrev qz281 := (BSN.sinEvenQ 1073741824)

noncomputable abbrev qz282 := (BSN.sinOddQ 1073741824)

noncomputable def ep61 := BSN.sin_dyadic_bound_f 1359414762 1073741824 3 2 524288 163960 ep56 ep57 ep58 ep59 ep60 ep58 500131 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1359414762) qz281 0 2 ep56 ep57 ep58 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1359414762) qz282 0 2 ep59 ep60 ep58 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz19 := (@Nat.cast Real Real.instNatCast 524288)

noncomputable abbrev qz20 := (Real.log qz279)

noncomputable abbrev qz21 := (Enclosure.Real.IsNear.const Bool.false 81143 1000)

noncomputable abbrev qz22 := (@Nat.cast Real Real.instNatCast 75557863725914323419136)

noncomputable abbrev qz283 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 29488015) qz19)

noncomputable abbrev qz284 := (BSN.isNear_log_sfrac 2 1 181704 262144 1 81900 Bool.false (BSN.logfrac_isNear 4 2 1 2 1 181704 262144 81900 rfl rfl rfl (ep55 rfl)))

noncomputable def ep62 := @Enclosure.Real.IsNear.cos_image qz15 qz283 Bool.false 29488015 524288 65 65536 Bool.false 500131 524288 1 81900 (@Enclosure.Real.IsNear.recentre' qz15 Bool.false 1843000959 32768000 81143 81900000 29488015 524288 65 65536 (@Enclosure.Real.IsNear.mulLit_ff qz16 qz20 81143 1000 0 1 181704 262144 1 81900 1843000959 32768000 81143 81900000 qz21 qz284 rfl) rfl) (Enclosure.sfrac_false_div 29488015 524288) (BSN.cos_reduce3 qz283 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 95660309668913930567680) qz22) 226375608064910080 72057594037927936 Bool.false 500131 524288 8 1000000000000000 163800 81900 (BSN.sin_reduce_arg_pos_rat_q3 29488015 524288 226375608064910080 72057594037927936 8 95660309668913930567680 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 500131 524288 95660309668913930567680 75557863725914323419136 1359414762 1073741824 163960 163800 (ep61 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep63 := nat_lit 7638012365162970061964085613523965121570673233616617022649384886181467218176

noncomputable def ep64 := nat_lit 71239273651864456168798555229954474558164150722024956391463162036118429368320

noncomputable def ep65 := nat_lit 22890710795913890098661118777714495311615155996423562771754314382866247803136

noncomputable def ep66 := nat_lit 3205767314333900527595934985347951355117386782491123037615842291625329321574400

noncomputable abbrev qz285 := (BSN.cosEvenQ 1073741824)

noncomputable abbrev qz286 := (BSN.cosOddQ 1073741824)

noncomputable def ep67 := BSN.cos_dyadic_bound_f 1359414762 1073741824 3 2 524288 163960 ep63 ep64 ep58 ep65 ep66 ep58 157311 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1359414762) qz285 0 2 ep63 ep64 ep58 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1359414762) qz286 0 2 ep65 ep66 ep58 rfl rfl rfl rfl) rfl rfl

noncomputable def ep68 := @Enclosure.Real.IsNear.sin_image qz15 qz283 Bool.false 29488015 524288 65 65536 Bool.true 157311 524288 1 81900 (@Enclosure.Real.IsNear.recentre' qz15 Bool.false 1843000959 32768000 81143 81900000 29488015 524288 65 65536 (@Enclosure.Real.IsNear.mulLit_ff qz16 qz20 81143 1000 0 1 181704 262144 1 81900 1843000959 32768000 81143 81900000 qz21 qz284 rfl) rfl) (Enclosure.sfrac_false_div 29488015 524288) (BSN.sin_reduce3 qz283 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 95660309668913930567680) qz22) 226375608064910080 72057594037927936 Bool.false 157311 524288 8 1000000000000000 163800 81900 (BSN.sin_reduce_arg_pos_rat_q3 29488015 524288 226375608064910080 72057594037927936 8 95660309668913930567680 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 157311 524288 95660309668913930567680 75557863725914323419136 1359414762 1073741824 163960 163800 (ep67 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz287 := (@Enclosure.Real.IsNear.recentre' qz14 Bool.false 370728 524288 2 524288 46341 65536 1 262144 (ep54 rfl rfl) rfl)

noncomputable def ep69 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz14 (Real.cos qz15)) (@HMul.hMul Real Real Real qz0 qz14 (@Neg.neg Real Real.instNeg (Real.sin qz15))) Bool.false 23176570671 34359738368 401623499701 562812514467840 Bool.false 7289949051 34359738368 400219651801 562812514467840 (@Enclosure.Real.IsNear.mulLit_ff qz14 (Real.cos qz15) 46341 65536 1 262144 500131 524288 1347259 1341849600 23176570671 34359738368 401623499701 562812514467840 qz287 (@Enclosure.Real.IsNear.recentre' (Real.cos qz15) Bool.false 500131 524288 5389036 5367398400 500131 524288 1347259 1341849600 (ep62 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz14 (@Neg.neg Real Real.instNeg (Real.sin qz15)) 46341 65536 1 262144 157311 524288 1347259 1341849600 7289949051 34359738368 400219651801 562812514467840 qz287 (@Enclosure.Real.IsNear.neg (Real.sin qz15) Bool.true 157311 524288 1347259 1341849600 (@Enclosure.Real.IsNear.recentre' (Real.sin qz15) Bool.true 157311 524288 5389036 5367398400 157311 524288 1347259 1341849600 (ep68 rfl rfl) rfl)) rfl)

noncomputable abbrev qz288 := (Enclosure.Real.IsNear.const Bool.false 0 1)

noncomputable abbrev qz23 := qz288

noncomputable def ep70 := @ep51 23176570671 34359738368 401623499701 562812514467840 Bool.false 7289949051 34359738368 400219651801 562812514467840 Bool.false 57536309039 57536309039 34359738368 401623499701 562812514467840 Bool.false 7289949051 7289949051 34359738368 400219651801 562812514467840 (ep52 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 1) qz13 Bool.false 1 1 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 1) qz23)) (ep53 ep69) rfl rfl

noncomputable abbrev qz289 := (@Nat.cast Real Real.instNatCast 3)

noncomputable abbrev qz24 := (@Inv.inv Real Real.instInv (Real.sqrt qz289))

noncomputable abbrev qz25 := (@HMul.hMul Real Real Real qz265 qz278 (Real.log (Enclosure.sfrac Bool.false 3 1)))

noncomputable def ep71 := @Enclosure.Complex.IsNear.of_eq qz11 (Complex.mk (@HMul.hMul Real Real Real qz0 qz24 (Real.cos qz25)) (@HMul.hMul Real Real Real qz0 qz24 (@Neg.neg Real Real.instNeg (Real.sin qz25)))) Bool.false 30233022193 137438953472 21804682957 37520834297856 Bool.true 73365065609 137438953472 21882483589 37520834297856 (BSN.cpow_neg_s_mk qz16 81143 1000 3 qz17 rfl)

noncomputable def ep72 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz289) 908093 524288 1 524288 151348 151350 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz289) (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz289 qz18)) Bool.false 908093 524288 1 524288 (BSN.sqrt_natCast_div_one 3) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz289 qz18)) Bool.false 908093 524288 1 524288 908093 524288 1 524288 (BSN.sqrt_enclosure 3 1 454046 454047 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep73 := BSN.log_dyadic_bound 1 2 10 9 171633298636800 262144 81900 16925142283965 34459425 287994 3 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base9 (BSN.artanhP 1) (BSN.artanhQ 2) 0 9 16925142283965 171633298636800 34459425 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep74 := nat_lit 5759766542127135822752118380814047292549792073628635271402979663786188800000

noncomputable def ep75 := nat_lit 6637289177414205011119071022683139775870909774944665937843261465600000000

noncomputable def ep76 := nat_lit 17266025048026579058234117000396775598097634401336016482333252468427366400000

noncomputable def ep77 := BSN.cos_dyadic_bound_f 1266918980 1073741824 3 2 524288 163960 ep74 ep64 ep75 ep76 ep66 ep75 199757 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1266918980) qz285 0 2 ep74 ep64 ep75 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1266918980) qz286 0 2 ep76 ep66 ep75 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz26 := (@Nat.cast Real Real.instNatCast 262144)

noncomputable abbrev qz27 := (Real.log (Enclosure.sfrac Bool.false 3 1))

noncomputable abbrev qz290 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 23368697) qz26)

noncomputable abbrev qz291 := (BSN.isNear_log_sfrac 3 1 287994 262144 1 81900 Bool.false (BSN.logfrac_isNear 3 1 2 3 1 287994 262144 81900 rfl rfl rfl (ep73 rfl)))

noncomputable abbrev qz292 := (@Nat.cast Real Real.instNatCast 37778931862957161709568)

noncomputable def ep78 := @Enclosure.Real.IsNear.cos_image qz25 qz290 Bool.false 23368697 262144 65 65536 Bool.false 199757 524288 1 81900 (@Enclosure.Real.IsNear.recentre' qz25 Bool.false 11684348571 131072000 81143 81900000 23368697 262144 65 65536 (@Enclosure.Real.IsNear.mulLit_ff qz16 qz27 81143 1000 0 1 287994 262144 1 81900 11684348571 131072000 81143 81900000 qz21 qz291 rfl) rfl) (Enclosure.sfrac_false_div 23368697 262144) (BSN.cos_reduce0 qz290 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 44575748810892759793664) qz292) 226375608064910080 72057594037927936 Bool.false 199757 524288 14 1000000000000000 163800 81900 (BSN.sin_reduce_arg_pos_rat_q0 23368697 262144 226375608064910080 72057594037927936 14 44575748810892759793664 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 199757 524288 44575748810892759793664 37778931862957161709568 1266918980 1073741824 163960 163800 (ep77 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep79 := nat_lit 10362269944486913116944917828647138614768929004711587755775088785642659840000

noncomputable def ep80 := nat_lit 27128532338797530402932972960039114145710070682228057520273486300976947200000

noncomputable def ep81 := BSN.sin_dyadic_bound_f 1266918980 1073741824 3 2 524288 163960 ep79 ep57 ep75 ep80 ep60 ep75 484741 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1266918980) qz281 0 2 ep79 ep57 ep75 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1266918980) qz282 0 2 ep80 ep60 ep75 rfl rfl rfl rfl) rfl rfl

noncomputable def ep82 := @Enclosure.Real.IsNear.sin_image qz25 qz290 Bool.false 23368697 262144 65 65536 Bool.false 484741 524288 1 81900 (@Enclosure.Real.IsNear.recentre' qz25 Bool.false 11684348571 131072000 81143 81900000 23368697 262144 65 65536 (@Enclosure.Real.IsNear.mulLit_ff qz16 qz27 81143 1000 0 1 287994 262144 1 81900 11684348571 131072000 81143 81900000 qz21 qz291 rfl) rfl) (Enclosure.sfrac_false_div 23368697 262144) (BSN.sin_reduce0 qz290 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 44575748810892759793664) qz292) 226375608064910080 72057594037927936 Bool.false 484741 524288 14 1000000000000000 163800 81900 (BSN.sin_reduce_arg_pos_rat_q0 23368697 262144 226375608064910080 72057594037927936 14 44575748810892759793664 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 484741 524288 44575748810892759793664 37778931862957161709568 1266918980 1073741824 163960 163800 (ep81 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz293 := (@Enclosure.Real.IsNear.recentre' qz24 Bool.false 302698 524288 2 524288 151349 262144 1 262144 (ep72 rfl rfl) rfl)

noncomputable def ep83 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz24 (Real.cos qz25)) (@HMul.hMul Real Real Real qz0 qz24 (@Neg.neg Real Real.instNeg (Real.sin qz25))) Bool.false 30233022193 137438953472 21804682957 37520834297856 Bool.true 73365065609 137438953472 21882483589 37520834297856 (@Enclosure.Real.IsNear.mulLit_ff qz24 (Real.cos qz25) 151349 262144 1 262144 199757 524288 1347259 1341849600 30233022193 137438953472 21804682957 37520834297856 qz293 (@Enclosure.Real.IsNear.recentre' (Real.cos qz25) Bool.false 199757 524288 5389036 5367398400 199757 524288 1347259 1341849600 (ep78 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz24 (@Neg.neg Real Real.instNeg (Real.sin qz25)) 151349 262144 1 262144 484741 524288 1347259 1341849600 73365065609 137438953472 21882483589 37520834297856 qz293 (@Enclosure.Real.IsNear.neg (Real.sin qz25) Bool.false 484741 524288 1347259 1341849600 (@Enclosure.Real.IsNear.recentre' (Real.sin qz25) Bool.false 484741 524288 5389036 5367398400 484741 524288 1347259 1341849600 (ep82 rfl rfl) rfl)) rfl)

noncomputable def ep84 := @ep49 30233022193 137438953472 21804682957 37520834297856 Bool.true 73365065609 137438953472 21882483589 37520834297856 Bool.false 8946528833587151634432 260378258349 137438953472 91086718007 70351564308480 Bool.true 1518881491242755031040 44205269405 137438953472 182114226409 140703128616960 (ep50 (BSN.head_sum_c_succ qz5 2 3 rfl rfl) (ep70 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep71 ep83) rfl rfl

noncomputable abbrev qz294 := (@Nat.cast Real Real.instNatCast 4)

noncomputable abbrev qz28 := (@Inv.inv Real Real.instInv (Real.sqrt qz294))

noncomputable abbrev qz29 := (@HMul.hMul Real Real Real qz265 qz278 (Real.log (Enclosure.sfrac Bool.false 4 1)))

noncomputable def ep85 := @Enclosure.Complex.IsNear.of_eq qz10 (Complex.mk (@HMul.hMul Real Real Real qz0 qz28 (Real.cos qz29)) (@HMul.hMul Real Real Real qz0 qz28 (@Neg.neg Real Real.instNeg (Real.sin qz29)))) Bool.false 56345802849 137438953472 1419788110309 2814062572339200 Bool.false 39337965009 137438953472 1418459692309 2814062572339200 (BSN.cpow_neg_s_mk qz16 81143 1000 4 qz17 rfl)

noncomputable def ep86 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz294) 1048577 524288 1 524288 131071 131072 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz294) (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz294 qz18)) Bool.false 1048577 524288 1 524288 (BSN.sqrt_natCast_div_one 4) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz294 qz18)) Bool.false 1048577 524288 1 524288 1048577 524288 1 524288 (BSN.sqrt_enclosure 4 1 524288 524289 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep87 := nat_lit 471225594319403171539306640625

noncomputable def ep88 := nat_lit 73155514365408823868279100600

noncomputable def ep89 := BSN.log_dyadic_bound 3 5 13 12 ep87 262144 81900 ep88 89313862490502916491225 363408 8 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base12 (BSN.artanhP 3) (BSN.artanhQ 5) 0 12 ep88 ep87 89313862490502916491225 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep90 := nat_lit 4564140437311572389727489840584924607729092193948700040264775357540255989760

noncomputable def ep91 := nat_lit 1288576494933191175770928098837346901115327212375705161862838318645968896

noncomputable def ep92 := nat_lit 11951614878633750139763606175086208744307721406759891820907586102946672214016

noncomputable def ep93 := BSN.sin_dyadic_bound_f 1032199812 1073741824 3 2 524288 163960 ep90 ep57 ep91 ep92 ep60 ep91 429886 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1032199812) qz281 0 2 ep90 ep57 ep91 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1032199812) qz282 0 2 ep92 ep60 ep91 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz30 := (Real.log (Enclosure.sfrac Bool.false 4 1))

noncomputable abbrev qz295 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 29488015) qz26)

noncomputable abbrev qz296 := (BSN.isNear_log_sfrac 4 1 363408 262144 1 81900 Bool.false (BSN.logfrac_isNear 8 2 1 4 1 363408 262144 81900 rfl rfl rfl (ep89 rfl)))

noncomputable def ep94 := @Enclosure.Real.IsNear.cos_image qz29 qz295 Bool.false 29488015 262144 521 524288 Bool.false 429886 524288 1 81900 (@Enclosure.Real.IsNear.recentre' qz29 Bool.false 1843000959 16384000 81143 81900000 29488015 262144 521 524288 (@Enclosure.Real.IsNear.mulLit_ff qz16 qz30 81143 1000 0 1 363408 262144 1 81900 1843000959 16384000 81143 81900000 qz21 qz296 rfl) rfl) (Enclosure.sfrac_false_div 29488015 262144) (BSN.cos_reduce3 qz295 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 36317302268346142556160) qz292) 226375608064910080 72057594037927936 Bool.false 429886 524288 17 1000000000000000 163800 81900 (BSN.sin_reduce_arg_pos_rat_q3 29488015 262144 226375608064910080 72057594037927936 17 36317302268346142556160 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 429886 524288 36317302268346142556160 37778931862957161709568 1032199812 1073741824 163960 163800 (ep93 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep95 := nat_lit 2536206276948621634815614768368885825138880253177000335774592015663984869376

noncomputable def ep96 := nat_lit 7606041677855998522095302448908982781614410105106249597000050370354662670336

noncomputable def ep97 := BSN.cos_dyadic_bound_f 1032199812 1073741824 3 2 524288 163960 ep95 ep64 ep91 ep96 ep66 ep91 300126 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1032199812) qz285 0 2 ep95 ep64 ep91 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1032199812) qz286 0 2 ep96 ep66 ep91 rfl rfl rfl rfl) rfl rfl

noncomputable def ep98 := @Enclosure.Real.IsNear.sin_image qz29 qz295 Bool.false 29488015 262144 521 524288 Bool.true 300126 524288 1 81900 (@Enclosure.Real.IsNear.recentre' qz29 Bool.false 1843000959 16384000 81143 81900000 29488015 262144 521 524288 (@Enclosure.Real.IsNear.mulLit_ff qz16 qz30 81143 1000 0 1 363408 262144 1 81900 1843000959 16384000 81143 81900000 qz21 qz296 rfl) rfl) (Enclosure.sfrac_false_div 29488015 262144) (BSN.sin_reduce3 qz295 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 36317302268346142556160) qz292) 226375608064910080 72057594037927936 Bool.false 300126 524288 17 1000000000000000 163800 81900 (BSN.sin_reduce_arg_pos_rat_q3 29488015 262144 226375608064910080 72057594037927936 17 36317302268346142556160 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 300126 524288 36317302268346142556160 37778931862957161709568 1032199812 1073741824 163960 163800 (ep97 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz297 := (@Enclosure.Real.IsNear.recentre' qz28 Bool.false 262143 524288 1 524288 262143 524288 1 524288 (ep86 rfl rfl) rfl)

noncomputable def ep99 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz28 (Real.cos qz29)) (@HMul.hMul Real Real Real qz0 qz28 (@Neg.neg Real Real.instNeg (Real.sin qz29))) Bool.false 56345802849 137438953472 1419788110309 2814062572339200 Bool.false 39337965009 137438953472 1418459692309 2814062572339200 (@Enclosure.Real.IsNear.mulLit_ff qz28 (Real.cos qz29) 262143 524288 1 524288 214943 262144 10798547 10734796800 56345802849 137438953472 1419788110309 2814062572339200 qz297 (@Enclosure.Real.IsNear.recentre' (Real.cos qz29) Bool.false 429886 524288 43194188 42939187200 214943 262144 10798547 10734796800 (ep94 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz28 (@Neg.neg Real Real.instNeg (Real.sin qz29)) 262143 524288 1 524288 150063 262144 10798547 10734796800 39337965009 137438953472 1418459692309 2814062572339200 qz297 (@Enclosure.Real.IsNear.neg (Real.sin qz29) Bool.true 150063 262144 10798547 10734796800 (@Enclosure.Real.IsNear.recentre' (Real.sin qz29) Bool.true 300126 524288 43194188 42939187200 150063 262144 10798547 10734796800 (ep98 rfl rfl) rfl)) rfl)

noncomputable def ep100 := @ep47 56345802849 137438953472 1419788110309 2814062572339200 Bool.false 39337965009 137438953472 1418459692309 2814062572339200 Bool.false 43530223510454802579456 158362030599 68719476736 1687752276863 938020857446400 Bool.true 668957222415905062912 1216826099 34359738368 1686914740163 938020857446400 (ep48 (BSN.head_sum_c_succ qz5 3 4 rfl rfl) (ep84 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep85 ep99) rfl rfl

noncomputable abbrev qz298 := (@Nat.cast Real Real.instNatCast 5)

noncomputable abbrev qz31 := (@Inv.inv Real Real.instInv (Real.sqrt qz298))

noncomputable abbrev qz32 := (@HMul.hMul Real Real Real qz265 qz278 (Real.log (Enclosure.sfrac Bool.false 5 1)))

noncomputable def ep101 := @Enclosure.Complex.IsNear.of_eq qz9 (Complex.mk (@HMul.hMul Real Real Real qz0 qz31 (Real.cos qz32)) (@HMul.hMul Real Real Real qz0 qz31 (@Neg.neg Real Real.instNeg (Real.sin qz32)))) Bool.false 13315728979 137438953472 252946013329 562812514467840 Bool.false 30002418771 68719476736 126880719197 281406257233920 (BSN.cpow_neg_s_mk qz16 81143 1000 5 qz17 rfl)

noncomputable def ep102 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz298) 1172343 524288 1 524288 117234 117235 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz298) (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz298 qz18)) Bool.false 1172343 524288 1 524288 (BSN.sqrt_natCast_div_one 5) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz298 qz18)) Bool.false 1172343 524288 1 524288 1172343 524288 1 524288 (BSN.sqrt_enclosure 5 1 586171 586172 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep103 := nat_lit 11734546589655452485523914939250625

noncomputable def ep104 := nat_lit 2429970938528035899633153341031900

noncomputable def ep105 := nat_lit 824199001261152424427520000

noncomputable def ep106 := BSN.log_dyadic_bound 2 3 17 16 ep103 262144 81900 ep104 ep105 421904 5 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base16 (BSN.artanhP 2) (BSN.artanhQ 3) 0 16 ep104 ep103 ep105 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep107 := nat_lit 3022648128703419761032621291763361

noncomputable def ep108 := nat_lit 159507359494189904748456847233641349120

noncomputable def ep109 := nat_lit 1116551516459329333239197930635489443840

noncomputable def ep110 := BSN.sin_dyadic_bound_f 234475191 1073741824 2 1 524288 163960 ep107 ep108 ep107 ep107 ep109 ep107 113582 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 234475191) qz281 0 1 ep107 ep108 ep107 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 234475191) qz282 0 1 ep107 ep109 ep107 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz33 := (Real.log (Enclosure.sfrac Bool.false 5 1))

noncomputable abbrev qz484 := (@Nat.cast Real Real.instNatCast 65536)

noncomputable abbrev qz299 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 8558639) qz484)

noncomputable abbrev qz300 := (BSN.isNear_log_sfrac 5 1 421904 262144 1 81900 Bool.false (BSN.logfrac_isNear 5 1 2 5 1 421904 262144 81900 rfl rfl rfl (ep106 rfl)))

noncomputable abbrev qz301 := (@Nat.cast Real Real.instNatCast 9444732965739290427392)

noncomputable def ep111 := @Enclosure.Real.IsNear.cos_image qz32 qz299 Bool.false 8558639 65536 65 65536 Bool.false 113582 524288 1 81900 (@Enclosure.Real.IsNear.recentre' qz32 Bool.false 2139659767 16384000 81143 81900000 8558639 65536 65 65536 (@Enclosure.Real.IsNear.mulLit_ff qz16 qz33 81143 1000 0 1 421904 262144 1 81900 2139659767 16384000 81143 81900000 qz21 qz300 rfl) rfl) (Enclosure.sfrac_false_div 8558639 65536) (BSN.cos_reduce3 qz299 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 2062465596573423239168) qz301) 226375608064910080 72057594037927936 Bool.false 113582 524288 20 1000000000000000 163800 81900 (BSN.sin_reduce_arg_pos_rat_q3 8558639 65536 226375608064910080 72057594037927936 20 2062465596573423239168 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 113582 524288 2062465596573423239168 9444732965739290427392 234475191 1073741824 163960 163800 (ep110 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep112 := nat_lit 31901471898837980949691369446728269824

noncomputable def ep113 := nat_lit 478522078482569714245370541700924047360

noncomputable def ep114 := BSN.cos_dyadic_bound_f 234475191 1073741824 2 1 524288 163960 ep107 ep112 ep107 ep107 ep113 ep107 511836 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 234475191) qz285 0 1 ep107 ep112 ep107 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 234475191) qz286 0 1 ep107 ep113 ep107 rfl rfl rfl rfl) rfl rfl

noncomputable def ep115 := @Enclosure.Real.IsNear.sin_image qz32 qz299 Bool.false 8558639 65536 65 65536 Bool.true 511836 524288 1 81900 (@Enclosure.Real.IsNear.recentre' qz32 Bool.false 2139659767 16384000 81143 81900000 8558639 65536 65 65536 (@Enclosure.Real.IsNear.mulLit_ff qz16 qz33 81143 1000 0 1 421904 262144 1 81900 2139659767 16384000 81143 81900000 qz21 qz300 rfl) rfl) (Enclosure.sfrac_false_div 8558639 65536) (BSN.sin_reduce3 qz299 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 2062465596573423239168) qz301) 226375608064910080 72057594037927936 Bool.false 511836 524288 20 1000000000000000 163800 81900 (BSN.sin_reduce_arg_pos_rat_q3 8558639 65536 226375608064910080 72057594037927936 20 2062465596573423239168 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 511836 524288 2062465596573423239168 9444732965739290427392 234475191 1073741824 163960 163800 (ep114 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz302 := (@Enclosure.Real.IsNear.recentre' qz31 Bool.false 234469 524288 1 524288 234469 524288 1 524288 (ep102 rfl rfl) rfl)

noncomputable def ep116 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz31 (Real.cos qz32)) (@HMul.hMul Real Real Real qz0 qz31 (@Neg.neg Real Real.instNeg (Real.sin qz32))) Bool.false 13315728979 137438953472 252946013329 562812514467840 Bool.false 30002418771 68719476736 126880719197 281406257233920 (@Enclosure.Real.IsNear.mulLit_ff qz31 (Real.cos qz32) 234469 524288 1 524288 56791 262144 1347259 1341849600 13315728979 137438953472 252946013329 562812514467840 qz302 (@Enclosure.Real.IsNear.recentre' (Real.cos qz32) Bool.false 113582 524288 5389036 5367398400 56791 262144 1347259 1341849600 (ep111 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz31 (@Neg.neg Real Real.instNeg (Real.sin qz32)) 234469 524288 1 524288 127959 131072 1347259 1341849600 30002418771 68719476736 126880719197 281406257233920 qz302 (@Enclosure.Real.IsNear.neg (Real.sin qz32) Bool.true 127959 131072 1347259 1341849600 (@Enclosure.Real.IsNear.recentre' (Real.sin qz32) Bool.true 511836 524288 5389036 5367398400 127959 131072 1347259 1341849600 (ep115 rfl rfl) rfl)) rfl)

noncomputable def ep117 := @ep45 13315728979 137438953472 252946013329 562812514467840 Bool.false 30002418771 68719476736 126880719197 281406257233920 Bool.false 22680161683022672822272 330039790177 137438953472 3163993448617 1407031286169600 Bool.false 947255606576743972864 27568766573 68719476736 6329551412459 2814062572339200 (ep46 (BSN.head_sum_c_succ qz5 4 5 rfl rfl) (ep100 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep101 ep116) rfl rfl

noncomputable abbrev qz303 := (@Nat.cast Real Real.instNatCast 6)

noncomputable abbrev qz34 := (@Inv.inv Real Real.instInv (Real.sqrt qz303))

noncomputable abbrev qz35 := (@HMul.hMul Real Real Real qz265 qz278 (Real.log (Enclosure.sfrac Bool.false 6 1)))

noncomputable def ep118 := @Enclosure.Complex.IsNear.of_eq qz8 (Complex.mk (@HMul.hMul Real Real Real qz0 qz34 (Real.cos qz35)) (@HMul.hMul Real Real Real qz0 qz34 (@Neg.neg Real Real.instNeg (Real.sin qz35)))) Bool.false 71896770295 274877906944 462763237151 1125625028935680 Bool.true 86160757333 274877906944 463036136141 1125625028935680 (BSN.cpow_neg_s_mk qz16 81143 1000 6 qz17 rfl)

noncomputable abbrev qz304 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 6) qz18)

noncomputable def ep119 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz303) 1284239 524288 1 524288 107019 107020 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz303) (Real.sqrt qz304) Bool.false 1284239 524288 1 524288 (BSN.sqrt_natCast_div_one 6) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz304) Bool.false 1284239 524288 1 524288 1284239 524288 1 524288 (BSN.sqrt_enclosure 6 1 642119 642120 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep120 := BSN.log_dyadic_bound 2 10 4 3 105000000 262144 81900 1434560 960 106290 12 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 2) (BSN.artanhQ 10) 0 3 1434560 105000000 960 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz36 := (Real.log (Enclosure.sfrac Bool.false 6 1))

noncomputable def ep121 := @Enclosure.Real.IsNear.mulLit_ff qz16 qz36 81143 1000 0 1 4034681531866359 2251799813685248 5000000000819 409500000000000000 327386163540231968337 2251799813685248000 405715000066456117 409500000000000000000 qz21 (BSN.isNear_log_sfrac 6 1 4034681531866359 2251799813685248 5000000000819 409500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz304) Bool.false 16922680887833197019136 9444732965739290427392 1000000000163800 81900000000000000000 4034681531866359 2251799813685248 5000000000819 409500000000000000 (BSN.log_rat_reduce_isNear 6 1 2 12 8 106290 262144 24973259072661432 36028797018963968 81900 1000000000000000 rfl rfl rfl rfl (ep120 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep122 := nat_lit 1743760092789158203886499987961410558073063452764476878788741073083792190625

noncomputable def ep123 := nat_lit 609329743261029115451688242647286728015506675084261563971851079875390625

noncomputable def ep124 := nat_lit 5230061618880952553428596587398937100763159344943262113238279517091625790625

noncomputable def ep125 := BSN.cos_dyadic_bound_f 939953885 1073741824 3 2 524288 163960 ep122 ep64 ep123 ep124 ep66 ep123 335905 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 939953885) qz285 0 2 ep122 ep64 ep123 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 939953885) qz286 0 2 ep124 ep66 ep123 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz305 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 76225531) qz19)

noncomputable def ep126 := @Enclosure.Real.IsNear.cos_image qz35 qz305 Bool.false 76225531 524288 65 65536 Bool.false 335905 524288 1 81900 (@Enclosure.Real.IsNear.recentre' qz35 Bool.false 327386163540231968337 2251799813685248000 405715000066456117 409500000000000000000 76225531 524288 65 65536 (ep121 rfl) rfl) (Enclosure.sfrac_false_div 76225531 524288) (BSN.cos_reduce0 qz305 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 66143374542509128548352) qz22) 226375608064910080 72057594037927936 Bool.false 335905 524288 23 1000000000000000 163800 81900 (BSN.sin_reduce_arg_pos_rat_q0 76225531 524288 226375608064910080 72057594037927936 23 66143374542509128548352 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 335905 524288 66143374542509128548352 75557863725914323419136 939953885 1073741824 163960 163800 (ep125 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep127 := nat_lit 780595761749337911079292254615900625

noncomputable def ep128 := BSN.sin_dyadic_bound_f 939953885 1073741824 2 1 524288 163960 ep127 ep108 ep127 ep127 ep109 ep127 402547 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 939953885) qz281 0 1 ep127 ep108 ep127 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 939953885) qz282 0 1 ep127 ep109 ep127 rfl rfl rfl rfl) rfl rfl

noncomputable def ep129 := @Enclosure.Real.IsNear.sin_image qz35 qz305 Bool.false 76225531 524288 65 65536 Bool.false 402547 524288 1 81900 (@Enclosure.Real.IsNear.recentre' qz35 Bool.false 327386163540231968337 2251799813685248000 405715000066456117 409500000000000000000 76225531 524288 65 65536 (ep121 rfl) rfl) (Enclosure.sfrac_false_div 76225531 524288) (BSN.sin_reduce0 qz305 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 66143374542509128548352) qz22) 226375608064910080 72057594037927936 Bool.false 402547 524288 23 1000000000000000 163800 81900 (BSN.sin_reduce_arg_pos_rat_q0 76225531 524288 226375608064910080 72057594037927936 23 66143374542509128548352 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 402547 524288 66143374542509128548352 75557863725914323419136 939953885 1073741824 163960 163800 (ep128 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz306 := (@Enclosure.Real.IsNear.recentre' qz34 Bool.false 214039 524288 1 524288 214039 524288 1 524288 (ep119 rfl rfl) rfl)

noncomputable def ep130 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz34 (Real.cos qz35)) (@HMul.hMul Real Real Real qz0 qz34 (@Neg.neg Real Real.instNeg (Real.sin qz35))) Bool.false 71896770295 274877906944 462763237151 1125625028935680 Bool.true 86160757333 274877906944 463036136141 1125625028935680 (@Enclosure.Real.IsNear.mulLit_ff qz34 (Real.cos qz35) 214039 524288 1 524288 335905 524288 1347259 1341849600 71896770295 274877906944 462763237151 1125625028935680 qz306 (@Enclosure.Real.IsNear.recentre' (Real.cos qz35) Bool.false 335905 524288 5389036 5367398400 335905 524288 1347259 1341849600 (ep126 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz34 (@Neg.neg Real Real.instNeg (Real.sin qz35)) 214039 524288 1 524288 402547 524288 1347259 1341849600 86160757333 274877906944 463036136141 1125625028935680 qz306 (@Enclosure.Real.IsNear.neg (Real.sin qz35) Bool.false 402547 524288 1347259 1341849600 (@Enclosure.Real.IsNear.recentre' (Real.sin qz35) Bool.false 402547 524288 5389036 5367398400 402547 524288 1347259 1341849600 (ep129 rfl rfl) rfl)) rfl)

noncomputable def ep131 := @ep43 71896770295 274877906944 462763237151 1125625028935680 Bool.true 86160757333 274877906944 463036136141 1125625028935680 Bool.false 100602063599452268003328 731976350649 274877906944 1151522306171 432932703436800 Bool.false 1657122693512716877824 24114308959 274877906944 1151867961971 432932703436800 (ep44 (BSN.head_sum_c_succ qz5 5 6 rfl rfl) (ep117 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep118 ep130) rfl rfl

noncomputable abbrev qz307 := (@Nat.cast Real Real.instNatCast 7)

noncomputable abbrev qz37 := (@Inv.inv Real Real.instInv (Real.sqrt qz307))

noncomputable abbrev qz38 := (@HMul.hMul Real Real Real qz265 qz278 (Real.log (Enclosure.sfrac Bool.false 7 1)))

noncomputable def ep132 := @Enclosure.Complex.IsNear.of_eq qz7 (Complex.mk (@HMul.hMul Real Real Real qz0 qz37 (Real.cos qz38)) (@HMul.hMul Real Real Real qz0 qz37 (@Neg.neg Real Real.instNeg (Real.sin qz38)))) Bool.false 35550640363 137438953472 1071586165379 2814062572339200 Bool.true 9469218955 34359738368 267956630351 703515643084800 (BSN.cpow_neg_s_mk qz16 81143 1000 7 qz17 rfl)

noncomputable abbrev qz308 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 7) qz18)

noncomputable def ep133 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz307) 1387135 524288 1 524288 99081 99082 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz307) (Real.sqrt qz308) Bool.false 1387135 524288 1 524288 (BSN.sqrt_natCast_div_one 7) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz308) Bool.false 1387135 524288 1 524288 1387135 524288 1 524288 (BSN.sqrt_enclosure 7 1 693567 693568 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep134 := BSN.log_dyadic_bound 3 11 5 4 202569142545 262144 81900 5259111624 688905 146699 14 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 3) (BSN.artanhQ 11) 0 4 5259111624 202569142545 688905 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz39 := (Real.log (Enclosure.sfrac Bool.false 7 1))

noncomputable def ep135 := @Enclosure.Real.IsNear.mulLit_ff qz16 qz39 81143 1000 0 1 4381792198794487 2251799813685248 5000000000819 409500000000000000 355551764386781058641 2251799813685248000 405715000066456117 409500000000000000000 qz21 (BSN.isNear_log_sfrac 7 1 4381792198794487 2251799813685248 5000000000819 409500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz308) Bool.false 18378568546572512002048 9444732965739290427392 1000000000163800 81900000000000000000 4381792198794487 2251799813685248 5000000000819 409500000000000000 (BSN.log_rat_reduce_isNear 7 1 2 14 8 146699 262144 24973259072661432 36028797018963968 81900 1000000000000000 rfl rfl rfl rfl (ep134 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep136 := nat_lit 1323301050794422768859026055461137603502765498920406706564853694621934314081

noncomputable def ep137 := nat_lit 350969511989400756309754856832454448770829188373037654182834767593890401

noncomputable def ep138 := nat_lit 3969201213359289505064458656669747901610754838384474044386195414330615161441

noncomputable def ep139 := BSN.cos_dyadic_bound_f 877321301 1073741824 3 2 524288 163960 ep136 ep64 ep137 ep138 ep66 ep137 358802 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 877321301) qz285 0 2 ep136 ep64 ep137 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 877321301) qz286 0 2 ep138 ep66 ep137 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz309 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 41391673) qz26)

noncomputable def ep140 := @Enclosure.Real.IsNear.cos_image qz38 qz309 Bool.false 41391673 262144 65 65536 Bool.false 358802 524288 1 81900 (@Enclosure.Real.IsNear.recentre' qz38 Bool.false 355551764386781058641 2251799813685248000 405715000066456117 409500000000000000000 41391673 262144 65 65536 (ep135 rfl) rfl) (Enclosure.sfrac_false_div 41391673 262144) (BSN.cos_reduce0 qz309 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 30867999112546647801856) qz292) 226375608064910080 72057594037927936 Bool.false 358802 524288 25 1000000000000000 163800 81900 (BSN.sin_reduce_arg_pos_rat_q0 41391673 262144 226375608064910080 72057594037927936 25 30867999112546647801856 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 358802 524288 30867999112546647801856 37778931862957161709568 877321301 1073741824 163960 163800 (ep139 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep141 := nat_lit 592426798844718668175612498599425201

noncomputable def ep142 := BSN.sin_dyadic_bound_f 877321301 1073741824 2 1 524288 163960 ep141 ep108 ep141 ep141 ep109 ep141 382280 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 877321301) qz281 0 1 ep141 ep108 ep141 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 877321301) qz282 0 1 ep141 ep109 ep141 rfl rfl rfl rfl) rfl rfl

noncomputable def ep143 := @Enclosure.Real.IsNear.sin_image qz38 qz309 Bool.false 41391673 262144 65 65536 Bool.false 382280 524288 1 81900 (@Enclosure.Real.IsNear.recentre' qz38 Bool.false 355551764386781058641 2251799813685248000 405715000066456117 409500000000000000000 41391673 262144 65 65536 (ep135 rfl) rfl) (Enclosure.sfrac_false_div 41391673 262144) (BSN.sin_reduce0 qz309 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 30867999112546647801856) qz292) 226375608064910080 72057594037927936 Bool.false 382280 524288 25 1000000000000000 163800 81900 (BSN.sin_reduce_arg_pos_rat_q0 41391673 262144 226375608064910080 72057594037927936 25 30867999112546647801856 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 382280 524288 30867999112546647801856 37778931862957161709568 877321301 1073741824 163960 163800 (ep142 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz310 := (@Enclosure.Real.IsNear.recentre' qz37 Bool.false 198163 524288 1 524288 198163 524288 1 524288 (ep133 rfl rfl) rfl)

noncomputable def ep144 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz37 (Real.cos qz38)) (@HMul.hMul Real Real Real qz0 qz37 (@Neg.neg Real Real.instNeg (Real.sin qz38))) Bool.false 35550640363 137438953472 1071586165379 2814062572339200 Bool.true 9469218955 34359738368 267956630351 703515643084800 (@Enclosure.Real.IsNear.mulLit_ff qz37 (Real.cos qz38) 198163 524288 1 524288 179401 262144 1347259 1341849600 35550640363 137438953472 1071586165379 2814062572339200 qz310 (@Enclosure.Real.IsNear.recentre' (Real.cos qz38) Bool.false 358802 524288 5389036 5367398400 179401 262144 1347259 1341849600 (ep140 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz37 (@Neg.neg Real Real.instNeg (Real.sin qz38)) 198163 524288 1 524288 47785 65536 1347259 1341849600 9469218955 34359738368 267956630351 703515643084800 qz310 (@Enclosure.Real.IsNear.neg (Real.sin qz38) Bool.false 47785 65536 1347259 1341849600 (@Enclosure.Real.IsNear.recentre' (Real.sin qz38) Bool.false 382280 524288 5389036 5367398400 47785 65536 1347259 1341849600 (ep143 rfl rfl) rfl)) rfl)

noncomputable def ep145 := @ep41 35550640363 137438953472 1071586165379 2814062572339200 Bool.true 9469218955 34359738368 267956630351 703515643084800 Bool.false 110374149212952592384000 803077631375 274877906944 5704320770327 1876041714892800 Bool.true 1774317739988492484608 51639442681 274877906944 5705978849477 1876041714892800 (ep42 (BSN.head_sum_c_succ qz5 6 7 rfl rfl) (ep131 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep132 ep144) rfl rfl

noncomputable abbrev qz311 := (@Nat.cast Real Real.instNatCast 8)

noncomputable abbrev qz40 := (@Inv.inv Real Real.instInv (Real.sqrt qz311))

noncomputable abbrev qz41 := (@HMul.hMul Real Real Real qz265 qz278 (Real.log (Enclosure.sfrac Bool.false 8 1)))

noncomputable def ep146 := @Enclosure.Complex.IsNear.of_eq qz6 (Complex.mk (@HMul.hMul Real Real Real qz0 qz40 (Real.cos qz41)) (@HMul.hMul Real Real Real qz0 qz40 (@Neg.neg Real Real.instNeg (Real.sin qz41)))) Bool.false 59347857073 274877906944 222713559937 625347238297600 Bool.false 76957342073 274877906944 222929684937 625347238297600 (BSN.cpow_neg_s_mk qz16 81143 1000 8 qz17 rfl)

noncomputable abbrev qz312 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 8) qz18)

noncomputable def ep147 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz311) 1482911 524288 1 524288 92681 92682 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz311) (Real.sqrt qz312) Bool.false 1482911 524288 1 524288 (BSN.sqrt_natCast_div_one 8) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz312) Bool.false 1482911 524288 1 524288 1482911 524288 1 524288 (BSN.sqrt_enclosure 8 1 741455 741456 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep148 := BSN.log_dyadic_bound 0 16 1 0 1 262144 81900 0 1 0 16 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 0) (BSN.artanhQ 16) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz42 := (Real.log (Enclosure.sfrac Bool.false 8 1))

noncomputable def ep149 := @Enclosure.Real.IsNear.mulLit_ff qz16 qz42 81143 1000 0 1 9364972152248037 4503599627370496 10000000002457 819000000000000000 759901935349862466291 4503599627370496000 811430000199368351 819000000000000000000 qz21 (BSN.isNear_log_sfrac 8 1 9364972152248037 4503599627370496 10000000002457 819000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz312) Bool.false 19639770079031275290624 9444732965739290427392 1000000000245700 81900000000000000000 9364972152248037 4503599627370496 10000000002457 819000000000000000 (BSN.log_rat_reduce_isNear 8 1 3 16 16 0 262144 24973259072661432 36028797018963968 81900 1000000000000000 rfl rfl rfl rfl (ep148 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep150 := nat_lit 247538320093005219575194999739939856

noncomputable def ep151 := BSN.sin_dyadic_bound_f 705359646 1073741824 2 1 524288 163960 ep150 ep108 ep150 ep150 ep109 ep150 320171 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 705359646) qz281 0 1 ep150 ep108 ep150 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 705359646) qz282 0 1 ep150 ep109 ep150 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz313 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 22116057) (@Nat.cast Real Real.instNatCast 131072))

noncomputable abbrev qz314 := (@Nat.cast Real Real.instNatCast 18889465931478580854784)

noncomputable def ep152 := @Enclosure.Real.IsNear.cos_image qz41 qz313 Bool.false 22116057 131072 65 65536 Bool.false 320171 524288 1 81900 (@Enclosure.Real.IsNear.recentre' qz41 Bool.false 759901935349862466291 4503599627370496000 811430000199368351 819000000000000000000 22116057 131072 65 65536 (ep149 rfl) rfl) (Enclosure.sfrac_false_div 22116057 131072) (BSN.cos_reduce3 qz313 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 12408818120972130320384) qz314) 226375608064910080 72057594037927936 Bool.false 320171 524288 26 1000000000000000 163800 81900 (BSN.sin_reduce_arg_pos_rat_q3 22116057 131072 226375608064910080 72057594037927936 26 12408818120972130320384 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 320171 524288 12408818120972130320384 18889465931478580854784 705359646 1073741824 163960 163800 (ep151 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep153 := BSN.cos_dyadic_bound_f 705359646 1073741824 2 1 524288 163960 ep150 ep112 ep150 ep150 ep113 ep150 415171 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 705359646) qz285 0 1 ep150 ep112 ep150 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 705359646) qz286 0 1 ep150 ep113 ep150 rfl rfl rfl rfl) rfl rfl

noncomputable def ep154 := @Enclosure.Real.IsNear.sin_image qz41 qz313 Bool.false 22116057 131072 65 65536 Bool.true 415171 524288 1 81900 (@Enclosure.Real.IsNear.recentre' qz41 Bool.false 759901935349862466291 4503599627370496000 811430000199368351 819000000000000000000 22116057 131072 65 65536 (ep149 rfl) rfl) (Enclosure.sfrac_false_div 22116057 131072) (BSN.sin_reduce3 qz313 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 12408818120972130320384) qz314) 226375608064910080 72057594037927936 Bool.false 415171 524288 26 1000000000000000 163800 81900 (BSN.sin_reduce_arg_pos_rat_q3 22116057 131072 226375608064910080 72057594037927936 26 12408818120972130320384 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 415171 524288 12408818120972130320384 18889465931478580854784 705359646 1073741824 163960 163800 (ep153 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz315 := (@Enclosure.Real.IsNear.recentre' qz40 Bool.false 185363 524288 1 524288 185363 524288 1 524288 (ep147 rfl rfl) rfl)

noncomputable def ep155 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz40 (Real.cos qz41)) (@HMul.hMul Real Real Real qz0 qz40 (@Neg.neg Real Real.instNeg (Real.sin qz41))) Bool.false 59347857073 274877906944 222713559937 625347238297600 Bool.false 76957342073 274877906944 222929684937 625347238297600 (@Enclosure.Real.IsNear.mulLit_ff qz40 (Real.cos qz41) 185363 524288 1 524288 320171 524288 1347259 1341849600 59347857073 274877906944 222713559937 625347238297600 qz315 (@Enclosure.Real.IsNear.recentre' (Real.cos qz41) Bool.false 320171 524288 5389036 5367398400 320171 524288 1347259 1341849600 (ep152 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz40 (@Neg.neg Real Real.instNeg (Real.sin qz41)) 185363 524288 1 524288 415171 524288 1347259 1341849600 76957342073 274877906944 222929684937 625347238297600 qz315 (@Enclosure.Real.IsNear.neg (Real.sin qz41) Bool.true 415171 524288 1347259 1341849600 (@Enclosure.Real.IsNear.recentre' (Real.sin qz41) Bool.true 415171 524288 5389036 5367398400 415171 524288 1347259 1341849600 (ep154 rfl rfl) rfl)) rfl)

noncomputable def ep156 := @ep39 59347857073 274877906944 222713559937 625347238297600 Bool.false 76957342073 274877906944 222929684937 625347238297600 Bool.false 237061713159743090982912 13475398257 4294967296 455175817867 134002979635200 Bool.false 6959331193091730178048 197796089 2147483648 28458785287 8375186227200 (ep40 (BSN.head_sum_c_succ qz5 7 8 rfl rfl) (ep145 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep146 ep155) rfl rfl

theorem EMRow22.d6 : Enclosure.Complex.IsNear qz3 Bool.false 13475398257 4294967296 455175817867 134002979635200 Bool.false 197796089 2147483648 28458785287 8375186227200 := ep38 (BSN.head_sum_c_succ qz5 8 9 rfl rfl) (ep156 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable abbrev qz43 := (@HPow.hPow Complex Complex Complex qz272 (@Nat.cast Complex Complex.instNatCast 16) qz273)

noncomputable def ep157 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 17) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 16) qz43) Bool.false 1149508361535 274877906944 2142973281679 375208342978560 Bool.false 8433164951 274877906944 2142879162199 375208342978560

noncomputable def ep158 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 16) qz43 Bool.false 140724620285 34359738368 15364095871063 2814062572339200 Bool.true 56065301297 274877906944 30720408478001 5628125144678400 Bool.false

noncomputable abbrev qz44 := (@HPow.hPow Complex Complex Complex qz272 (@Nat.cast Complex Complex.instNatCast 15) qz273)

noncomputable def ep159 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 16) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 15) qz44) Bool.false 140724620285 34359738368 15364095871063 2814062572339200 Bool.true 56065301297 274877906944 30720408478001 5628125144678400

noncomputable def ep160 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 15) qz44 Bool.false 1055876622441 274877906944 29255795315867 5628125144678400 Bool.true 34122924253 137438953472 7314186313373 1407031286169600 Bool.false

noncomputable abbrev qz45 := (@HPow.hPow Complex Complex Complex qz272 (@Nat.cast Complex Complex.instNatCast 14) qz273)

noncomputable def ep161 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 15) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 14) qz45) Bool.false 1055876622441 274877906944 29255795315867 5628125144678400 Bool.true 34122924253 137438953472 7314186313373 1407031286169600

noncomputable def ep162 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 14) qz45 Bool.false 991849452459 274877906944 9245398141211 1876041714892800 Bool.true 8056516001 68719476736 4623539484043 938020857446400 Bool.false

noncomputable abbrev qz46 := (@HPow.hPow Complex Complex Complex qz272 (@Nat.cast Complex Complex.instNatCast 13) qz273)

noncomputable def ep163 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 14) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 13) qz46) Bool.false 991849452459 274877906944 9245398141211 1876041714892800 Bool.true 8056516001 68719476736 4623539484043 938020857446400

noncomputable def ep164 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 13) qz46 Bool.false 937773428135 274877906944 26161319093069 5628125144678400 Bool.false 10756448811 137438953472 3270801129343 703515643084800 Bool.false

noncomputable abbrev qz47 := (@HPow.hPow Complex Complex Complex qz272 (@Nat.cast Complex Complex.instNatCast 12) qz273)

noncomputable def ep165 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 13) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 12) qz47) Bool.false 937773428135 274877906944 26161319093069 5628125144678400 Bool.false 10756448811 137438953472 3270801129343 703515643084800

noncomputable def ep166 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 12) qz47 Bool.false 54437589229 17179869184 6130256188961 1407031286169600 Bool.false 32192310379 137438953472 3066168500893 703515643084800 Bool.false

noncomputable abbrev qz48 := (@HPow.hPow Complex Complex Complex qz272 (@Nat.cast Complex Complex.instNatCast 11) qz273)

noncomputable def ep167 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 12) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 11) qz48) Bool.false 54437589229 17179869184 6130256188961 1407031286169600 Bool.false 32192310379 137438953472 3066168500893 703515643084800

noncomputable def ep168 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 11) qz48 Bool.false 789884295367 274877906944 7601161281053 1876041714892800 Bool.false 11846754551 68719476736 3803352017089 938020857446400 Bool.false

noncomputable abbrev qz49 := (@HPow.hPow Complex Complex Complex qz272 (@Nat.cast Complex Complex.instNatCast 10) qz273)

noncomputable def ep169 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 11) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 10) qz49) Bool.false 789884295367 274877906944 7601161281053 1876041714892800 Bool.false 11846754551 68719476736 3803352017089 938020857446400

noncomputable def ep170 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 10) qz49 Bool.false 797379224137 274877906944 21012202351897 5628125144678400 Bool.true 39213513121 274877906944 21019061394997 5628125144678400 Bool.true

noncomputable abbrev qz50 := (@HPow.hPow Complex Complex Complex qz272 (@Nat.cast Complex Complex.instNatCast 9) qz273)

noncomputable def ep171 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 10) (@HAdd.hAdd Complex Complex Complex qz4 qz3 qz50) Bool.false 797379224137 274877906944 21012202351897 5628125144678400 Bool.true 39213513121 274877906944 21019061394997 5628125144678400

noncomputable def ep172 := @Enclosure.Complex.IsNear.addLitP qz3 qz50 Bool.false 13475398257 4294967296 455175817867 134002979635200 Bool.false 197796089 2147483648 28458785287 8375186227200 Bool.true

noncomputable abbrev qz316 := (@Nat.cast Real Real.instNatCast 9)

noncomputable abbrev qz51 := (@Inv.inv Real Real.instInv (Real.sqrt qz316))

noncomputable abbrev qz317 := (Real.log (Enclosure.sfrac Bool.false 9 1))

noncomputable abbrev qz52 := (@HMul.hMul Real Real Real qz265 qz278 qz317)

noncomputable def ep173 := @Enclosure.Complex.IsNear.of_eq qz50 (Complex.mk (@HMul.hMul Real Real Real qz0 qz51 (Real.cos qz52)) (@HMul.hMul Real Real Real qz0 qz51 (@Neg.neg Real Real.instNeg (Real.sin qz52)))) Bool.true 65046264311 274877906944 1894818001483 5628125144678400 Bool.true 64531412513 274877906944 1894757682133 5628125144678400 (BSN.cpow_neg_s_mk qz16 81143 1000 9 qz17 rfl)

noncomputable abbrev qz318 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 9) qz18)

noncomputable def ep174 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz316) 1572865 524288 1 524288 87381 87382 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz316) (Real.sqrt qz318) Bool.false 1572865 524288 1 524288 (BSN.sqrt_natCast_div_one 9) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz318) Bool.false 1572865 524288 1 524288 1572865 524288 1 524288 (BSN.sqrt_enclosure 9 1 786432 786433 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep175 := BSN.log_dyadic_bound 1 17 2 1 867 262144 81900 1 1 30876 18 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 1) (BSN.artanhQ 17) 0 1 1 867 1 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep176 := @Enclosure.Real.IsNear.mulLit_ff qz16 qz317 81143 1000 0 1 9895417793173221 4503599627370496 10000000002457 819000000000000000 802943885991454671603 4503599627370496000 811430000199368351 819000000000000000000 qz21 (BSN.isNear_log_sfrac 9 1 9895417793173221 4503599627370496 10000000002457 819000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz318) Bool.false 20752195215788806766592 9444732965739290427392 1000000000245700 81900000000000000000 9895417793173221 4503599627370496 10000000002457 819000000000000000 (BSN.log_rat_reduce_isNear 9 1 3 18 16 30876 262144 24973259072661432 36028797018963968 81900 1000000000000000 rfl rfl rfl rfl (ep175 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep177 := nat_lit 516089253519451123088694762112271521

noncomputable def ep178 := BSN.sin_dyadic_bound_f 847580983 1073741824 2 1 524288 163960 ep177 ep108 ep177 ep177 ep109 ep177 372197 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 847580983) qz281 0 1 ep177 ep108 ep177 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 847580983) qz282 0 1 ep177 ep109 ep177 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz319 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 46737485) qz26)

noncomputable def ep179 := @Enclosure.Real.IsNear.cos_image qz52 qz319 Bool.false 46737485 262144 521 524288 Bool.true 372197 524288 1 81900 (@Enclosure.Real.IsNear.recentre' qz52 Bool.false 802943885991454671603 4503599627370496000 811430000199368351 819000000000000000000 46737485 262144 521 524288 (ep176 rfl) rfl) (Enclosure.sfrac_false_div 46737485 262144) (BSN.cos_reduce1 qz319 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 29821604703332634460160) qz292) 226375608064910080 72057594037927936 Bool.false 372197 524288 28 1000000000000000 163800 81900 (BSN.sin_reduce_arg_pos_rat_q1 46737485 262144 226375608064910080 72057594037927936 28 29821604703332634460160 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 372197 524288 29821604703332634460160 37778931862957161709568 847580983 1073741824 163960 163800 (ep178 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep180 := nat_lit 1152746825408611103660618755448753956074720739351397460176481675937149414721

noncomputable def ep181 := nat_lit 266348117598264293439540534325176139386868974154888601681550898427653441

noncomputable def ep182 := nat_lit 3457707779990636782394977185277611515945388480105882603326081926014592937281

noncomputable def ep183 := BSN.cos_dyadic_bound_f 847580983 1073741824 3 2 524288 163960 ep180 ep64 ep181 ep182 ep66 ep181 369251 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 847580983) qz285 0 2 ep180 ep64 ep181 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 847580983) qz286 0 2 ep182 ep66 ep181 rfl rfl rfl rfl) rfl rfl

noncomputable def ep184 := @Enclosure.Real.IsNear.sin_image qz52 qz319 Bool.false 46737485 262144 521 524288 Bool.false 369251 524288 1 81900 (@Enclosure.Real.IsNear.recentre' qz52 Bool.false 802943885991454671603 4503599627370496000 811430000199368351 819000000000000000000 46737485 262144 521 524288 (ep176 rfl) rfl) (Enclosure.sfrac_false_div 46737485 262144) (BSN.sin_reduce1 qz319 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 29821604703332634460160) qz292) 226375608064910080 72057594037927936 Bool.false 369251 524288 28 1000000000000000 163800 81900 (BSN.sin_reduce_arg_pos_rat_q1 46737485 262144 226375608064910080 72057594037927936 28 29821604703332634460160 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 369251 524288 29821604703332634460160 37778931862957161709568 847580983 1073741824 163960 163800 (ep183 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz320 := (@Enclosure.Real.IsNear.recentre' qz51 Bool.false 174763 524288 1 524288 174763 524288 1 524288 (ep174 rfl rfl) rfl)

noncomputable def ep185 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz51 (Real.cos qz52)) (@HMul.hMul Real Real Real qz0 qz51 (@Neg.neg Real Real.instNeg (Real.sin qz52))) Bool.true 65046264311 274877906944 1894818001483 5628125144678400 Bool.true 64531412513 274877906944 1894757682133 5628125144678400 (@Enclosure.Real.IsNear.mulLit_ft qz51 (Real.cos qz52) 174763 524288 1 524288 372197 524288 10798547 10734796800 65046264311 274877906944 1894818001483 5628125144678400 qz320 (@Enclosure.Real.IsNear.recentre' (Real.cos qz52) Bool.true 372197 524288 43194188 42939187200 372197 524288 10798547 10734796800 (ep179 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz51 (@Neg.neg Real Real.instNeg (Real.sin qz52)) 174763 524288 1 524288 369251 524288 10798547 10734796800 64531412513 274877906944 1894757682133 5628125144678400 qz320 (@Enclosure.Real.IsNear.neg (Real.sin qz52) Bool.false 369251 524288 10798547 10734796800 (@Enclosure.Real.IsNear.recentre' (Real.sin qz52) Bool.false 369251 524288 43194188 42939187200 369251 524288 10798547 10734796800 (ep184 rfl rfl) rfl)) rfl)

noncomputable def ep186 := @ep172 65046264311 274877906944 1894818001483 5628125144678400 Bool.true 64531412513 274877906944 1894757682133 5628125144678400 Bool.false 3424717690178268823552 797379224137 274877906944 21012202351897 5628125144678400 Bool.true 84210378207980945408 39213513121 274877906944 21019061394997 5628125144678400 EMRow22.d6 (ep173 ep185) rfl rfl

noncomputable abbrev qz321 := (@Nat.cast Real Real.instNatCast 10)

noncomputable abbrev qz53 := (@Inv.inv Real Real.instInv (Real.sqrt qz321))

noncomputable abbrev qz54 := (@HMul.hMul Real Real Real qz265 qz278 (Real.log (Enclosure.sfrac Bool.false 10 1)))

noncomputable def ep187 := @Enclosure.Complex.IsNear.of_eq qz49 (Complex.mk (@HMul.hMul Real Real Real qz0 qz53 (Real.cos qz54)) (@HMul.hMul Real Real Real qz0 qz53 (@Neg.neg Real Real.instNeg (Real.sin qz54)))) Bool.true 3747464385 137438953472 895640745631 2814062572339200 Bool.false 86600531325 274877906944 1801050707537 5628125144678400 (BSN.cpow_neg_s_mk qz16 81143 1000 10 qz17 rfl)

noncomputable abbrev qz322 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 10) qz18)

noncomputable def ep188 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz321) 1657945 524288 1 524288 82897 82898 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz321) (Real.sqrt qz322) Bool.false 1657945 524288 1 524288 (BSN.sqrt_natCast_div_one 10) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz322) Bool.false 1657945 524288 1 524288 1657945 524288 1 524288 (BSN.sqrt_enclosure 10 1 828972 828973 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep189 := BSN.log_dyadic_bound 2 18 3 2 1574640 262144 81900 6528 48 58495 20 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 2) (BSN.artanhQ 18) 0 2 6528 1574640 48 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz55 := (Real.log (Enclosure.sfrac Bool.false 10 1))

noncomputable def ep190 := @Enclosure.Real.IsNear.mulLit_ff qz16 qz55 81143 1000 0 1 10369908600166117 4503599627370496 10000000002457 819000000000000000 841445493543279231731 4503599627370496000 811430000199368351 819000000000000000000 qz21 (BSN.isNear_log_sfrac 10 1 10369908600166117 4503599627370496 10000000002457 819000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz322) Bool.false 21747274560655572598784 9444732965739290427392 1000000000245700 81900000000000000000 10369908600166117 4503599627370496 10000000002457 819000000000000000 (BSN.log_rat_reduce_isNear 10 1 3 20 16 58495 262144 24973259072661432 36028797018963968 81900 1000000000000000 rfl rfl rfl rfl (ep189 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep191 := nat_lit 14455737159253601996406053334433272437021809687703597441669799006909873684736

noncomputable def ep192 := nat_lit 41663519142118821304644478842829479390774155208021820100516845736143257856

noncomputable def ep193 := nat_lit 43283884439476568346608871045614158352283880752694748684808363329257334538496

noncomputable def ep194 := BSN.cos_dyadic_bound_f 1593930914 1073741824 3 2 524288 163960 ep191 ep64 ep192 ep193 ep66 ep192 45206 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1593930914) qz285 0 2 ep191 ep64 ep192 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1593930914) qz286 0 2 ep193 ep66 ep192 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz323 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 97957147) qz19)

noncomputable def ep195 := @Enclosure.Real.IsNear.cos_image qz54 qz323 Bool.false 97957147 524288 521 524288 Bool.true 45206 524288 1 81900 (@Enclosure.Real.IsNear.recentre' qz54 Bool.false 841445493543279231731 4503599627370496000 811430000199368351 819000000000000000000 97957147 524288 521 524288 (ep190 rfl) rfl) (Enclosure.sfrac_false_div 97957147 524288) (BSN.cos_reduce2 qz323 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 112162916745262833598464) qz22) 226375608064910080 72057594037927936 Bool.false 45206 524288 29 1000000000000000 163800 81900 (BSN.sin_reduce_arg_pos_rat_q2 97957147 524288 226375608064910080 72057594037927936 29 112162916745262833598464 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 45206 524288 112162916745262833598464 75557863725914323419136 1593930914 1073741824 163960 163800 (ep194 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep196 := nat_lit 25986996071342788536487180418905626803126638113700057938925224735848858026240

noncomputable def ep197 := nat_lit 67993724965381968075354143369483489136794227379830021178927132748412300984576

noncomputable def ep198 := BSN.sin_dyadic_bound_f 1593930914 1073741824 3 2 524288 163960 ep196 ep57 ep192 ep197 ep60 ep192 522335 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1593930914) qz281 0 2 ep196 ep57 ep192 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1593930914) qz282 0 2 ep197 ep60 ep192 rfl rfl rfl rfl) rfl rfl

noncomputable def ep199 := @Enclosure.Real.IsNear.sin_image qz54 qz323 Bool.false 97957147 524288 521 524288 Bool.true 522335 524288 1 81900 (@Enclosure.Real.IsNear.recentre' qz54 Bool.false 841445493543279231731 4503599627370496000 811430000199368351 819000000000000000000 97957147 524288 521 524288 (ep190 rfl) rfl) (Enclosure.sfrac_false_div 97957147 524288) (BSN.sin_reduce2 qz323 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 112162916745262833598464) qz22) 226375608064910080 72057594037927936 Bool.false 522335 524288 29 1000000000000000 163800 81900 (BSN.sin_reduce_arg_pos_rat_q2 97957147 524288 226375608064910080 72057594037927936 29 112162916745262833598464 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 522335 524288 112162916745262833598464 75557863725914323419136 1593930914 1073741824 163960 163800 (ep198 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz324 := (@Enclosure.Real.IsNear.recentre' qz53 Bool.false 165795 524288 1 524288 165795 524288 1 524288 (ep188 rfl rfl) rfl)

noncomputable def ep200 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz53 (Real.cos qz54)) (@HMul.hMul Real Real Real qz0 qz53 (@Neg.neg Real Real.instNeg (Real.sin qz54))) Bool.true 3747464385 137438953472 895640745631 2814062572339200 Bool.false 86600531325 274877906944 1801050707537 5628125144678400 (@Enclosure.Real.IsNear.mulLit_ft qz53 (Real.cos qz54) 165795 524288 1 524288 22603 262144 10798547 10734796800 3747464385 137438953472 895640745631 2814062572339200 qz324 (@Enclosure.Real.IsNear.recentre' (Real.cos qz54) Bool.true 45206 524288 43194188 42939187200 22603 262144 10798547 10734796800 (ep195 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz53 (@Neg.neg Real Real.instNeg (Real.sin qz54)) 165795 524288 1 524288 522335 524288 10798547 10734796800 86600531325 274877906944 1801050707537 5628125144678400 qz324 (@Enclosure.Real.IsNear.neg (Real.sin qz54) Bool.true 522335 524288 10798547 10734796800 (@Enclosure.Real.IsNear.recentre' (Real.sin qz54) Bool.true 522335 524288 43194188 42939187200 522335 524288 10798547 10734796800 (ep199 rfl rfl) rfl)) rfl)

noncomputable def ep201 := @ep170 3747464385 137438953472 895640745631 2814062572339200 Bool.false 86600531325 274877906944 1801050707537 5628125144678400 Bool.false 108560870919208618164224 789884295367 274877906944 7601161281053 1876041714892800 Bool.false 13025644380232746008576 11846754551 68719476736 3803352017089 938020857446400 (ep171 (BSN.head_sum_c_succ qz5 9 10 rfl rfl) (ep186 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep187 ep200) rfl rfl

noncomputable abbrev qz325 := (@Nat.cast Real Real.instNatCast 11)

noncomputable abbrev qz56 := (@Inv.inv Real Real.instInv (Real.sqrt qz325))

noncomputable abbrev qz57 := (@HMul.hMul Real Real Real qz265 qz278 (Real.log (Enclosure.sfrac Bool.false 11 1)))

noncomputable def ep202 := @Enclosure.Complex.IsNear.of_eq qz48 (Complex.mk (@HMul.hMul Real Real Real qz0 qz56 (Real.cos qz57)) (@HMul.hMul Real Real Real qz0 qz56 (@Neg.neg Real Real.instNeg (Real.sin qz57)))) Bool.false 81117132297 274877906944 26423706349 86586540687360 Bool.false 8498801277 137438953472 13147968497 43293270343680 (BSN.cpow_neg_s_mk qz16 81143 1000 11 qz17 rfl)

noncomputable abbrev qz326 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 11) qz18)

noncomputable def ep203 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz325) 1738867 524288 1 524288 79039 79040 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz325) (Real.sqrt qz326) Bool.false 1738867 524288 1 524288 (BSN.sqrt_natCast_div_one 11) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz326) Bool.false 1738867 524288 1 524288 1738867 524288 1 524288 (BSN.sqrt_enclosure 11 1 869433 869434 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep204 := BSN.log_dyadic_bound 3 19 4 3 4939817505 262144 81900 41676111 10935 83480 22 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 3) (BSN.artanhQ 19) 0 3 41676111 4939817505 10935 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz58 := (Real.log (Enclosure.sfrac Bool.false 11 1))

noncomputable def ep205 := @Enclosure.Real.IsNear.mulLit_ff qz16 qz58 81143 1000 0 1 10799147631728357 4503599627370496 10000000002457 819000000000000000 876275236281334072051 4503599627370496000 811430000199368351 819000000000000000000 qz21 (BSN.isNear_log_sfrac 11 1 10799147631728357 4503599627370496 10000000002457 819000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz326) Bool.false 22647454054174387339264 9444732965739290427392 1000000000245700 81900000000000000000 10799147631728357 4503599627370496 10000000002457 819000000000000000 (BSN.log_rat_reduce_isNear 11 1 3 22 16 83480 262144 24973259072661432 36028797018963968 81900 1000000000000000 rfl rfl rfl rfl (ep204 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep206 := nat_lit 18528491424784214395446662626401197843239300116803079407515838972444723445760

noncomputable def ep207 := nat_lit 21199383100557892993464989487256270923174458926306497060647173084529360896

noncomputable def ep208 := nat_lit 48492678539891086827989934990928531817465408324794045072062339980932656726016

noncomputable def ep209 := BSN.sin_dyadic_bound_f 1464840716 1073741824 3 2 524288 163960 ep206 ep57 ep207 ep208 ep60 ep207 513143 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1464840716) qz281 0 2 ep206 ep57 ep207 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1464840716) qz282 0 2 ep208 ep60 ep207 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz327 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 102011863) qz19)

noncomputable def ep210 := @Enclosure.Real.IsNear.cos_image qz57 qz327 Bool.false 102011863 524288 521 524288 Bool.false 513143 524288 1 81900 (@Enclosure.Real.IsNear.recentre' qz57 Bool.false 876275236281334072051 4503599627370496000 811430000199368351 819000000000000000000 102011863 524288 521 524288 (ep205 rfl) rfl) (Enclosure.sfrac_false_div 102011863 524288) (BSN.cos_reduce3 qz327 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 103079001673766971375616) qz22) 226375608064910080 72057594037927936 Bool.false 513143 524288 30 1000000000000000 163800 81900 (BSN.sin_reduce_arg_pos_rat_q3 102011863 524288 226375608064910080 72057594037927936 30 103079001673766971375616 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 513143 524288 103079001673766971375616 75557863725914323419136 1464840716 1073741824 163960 163800 (ep209 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep211 := nat_lit 10303028295147033727689685898883890477765466491080069225091309283840192741376

noncomputable def ep212 := nat_lit 30866686119239985397082127717677158891450050555387594681152633505351519502336

noncomputable def ep213 := BSN.cos_dyadic_bound_f 1464840716 1073741824 3 2 524288 163960 ep211 ep64 ep207 ep212 ep66 ep207 107526 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1464840716) qz285 0 2 ep211 ep64 ep207 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1464840716) qz286 0 2 ep212 ep66 ep207 rfl rfl rfl rfl) rfl rfl

noncomputable def ep214 := @Enclosure.Real.IsNear.sin_image qz57 qz327 Bool.false 102011863 524288 521 524288 Bool.true 107526 524288 1 81900 (@Enclosure.Real.IsNear.recentre' qz57 Bool.false 876275236281334072051 4503599627370496000 811430000199368351 819000000000000000000 102011863 524288 521 524288 (ep205 rfl) rfl) (Enclosure.sfrac_false_div 102011863 524288) (BSN.sin_reduce3 qz327 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 103079001673766971375616) qz22) 226375608064910080 72057594037927936 Bool.false 107526 524288 30 1000000000000000 163800 81900 (BSN.sin_reduce_arg_pos_rat_q3 102011863 524288 226375608064910080 72057594037927936 30 103079001673766971375616 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 107526 524288 103079001673766971375616 75557863725914323419136 1464840716 1073741824 163960 163800 (ep213 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz328 := (@Enclosure.Real.IsNear.recentre' qz56 Bool.false 158079 524288 1 524288 158079 524288 1 524288 (ep203 rfl rfl) rfl)

noncomputable def ep215 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz56 (Real.cos qz57)) (@HMul.hMul Real Real Real qz0 qz56 (@Neg.neg Real Real.instNeg (Real.sin qz57))) Bool.false 81117132297 274877906944 26423706349 86586540687360 Bool.false 8498801277 137438953472 13147968497 43293270343680 (@Enclosure.Real.IsNear.mulLit_ff qz56 (Real.cos qz57) 158079 524288 1 524288 513143 524288 10798547 10734796800 81117132297 274877906944 26423706349 86586540687360 qz328 (@Enclosure.Real.IsNear.recentre' (Real.cos qz57) Bool.false 513143 524288 43194188 42939187200 513143 524288 10798547 10734796800 (ep210 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz56 (@Neg.neg Real Real.instNeg (Real.sin qz57)) 158079 524288 1 524288 53763 262144 10798547 10734796800 8498801277 137438953472 13147968497 43293270343680 qz328 (@Enclosure.Real.IsNear.neg (Real.sin qz57) Bool.true 53763 262144 10798547 10734796800 (@Enclosure.Real.IsNear.recentre' (Real.sin qz57) Bool.true 107526 524288 43194188 42939187200 53763 262144 10798547 10734796800 (ep214 rfl rfl) rfl)) rfl)

noncomputable def ep216 := @ep168 81117132297 274877906944 26423706349 86586540687360 Bool.false 8498801277 137438953472 13147968497 43293270343680 Bool.false 239419049381516139298816 54437589229 17179869184 6130256188961 1407031286169600 Bool.false 2212238724167781842944 32192310379 137438953472 3066168500893 703515643084800 (ep169 (BSN.head_sum_c_succ qz5 10 11 rfl rfl) (ep201 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep202 ep215) rfl rfl

noncomputable abbrev qz329 := (@Nat.cast Real Real.instNatCast 12)

noncomputable abbrev qz59 := (@Inv.inv Real Real.instInv (Real.sqrt qz329))

noncomputable abbrev qz60 := (@HMul.hMul Real Real Real qz265 qz278 (Real.log (Enclosure.sfrac Bool.false 12 1)))

noncomputable def ep217 := @Enclosure.Complex.IsNear.of_eq qz47 (Complex.mk (@HMul.hMul Real Real Real qz0 qz59 (Real.cos qz60)) (@HMul.hMul Real Real Real qz0 qz59 (@Neg.neg Real Real.instNeg (Real.sin qz60)))) Bool.false 66772000471 274877906944 21870591163 75041668595712 Bool.true 334935337 2147483648 1364217523 4690104287232 (BSN.cpow_neg_s_mk qz16 81143 1000 12 qz17 rfl)

noncomputable abbrev qz330 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 12) qz18)

noncomputable def ep218 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz329) 1816187 524288 1 524288 75674 75675 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz329) (Real.sqrt qz330) Bool.false 1816187 524288 1 524288 (BSN.sqrt_natCast_div_one 12) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz330) Bool.false 1816187 524288 1 524288 1816187 524288 1 524288 (BSN.sqrt_enclosure 12 1 908093 908094 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep219 := BSN.log_dyadic_bound 4 20 4 3 6720000000 262144 81900 91811840 61440 106290 24 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 4) (BSN.artanhQ 20) 0 3 91811840 6720000000 61440 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz61 := (Real.log (Enclosure.sfrac Bool.false 12 1))

noncomputable def ep220 := @Enclosure.Real.IsNear.mulLit_ff qz16 qz61 81143 1000 0 1 11191020447815397 4503599627370496 10000000002457 819000000000000000 908072972197084758771 4503599627370496000 811430000199368351 819000000000000000000 qz21 (BSN.isNear_log_sfrac 12 1 11191020447815397 4503599627370496 10000000002457 819000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz330) Bool.false 23469270914176955449344 9444732965739290427392 1000000000245700 81900000000000000000 11191020447815397 4503599627370496 10000000002457 819000000000000000 (BSN.log_rat_reduce_isNear 12 1 3 24 16 106290 262144 24973259072661432 36028797018963968 81900 1000000000000000 rfl rfl rfl rfl (ep219 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep221 := nat_lit 141076948470419027782711334156307361

noncomputable def ep222 := BSN.cos_dyadic_bound_f 612863863 1073741824 2 1 524288 163960 ep221 ep112 ep221 ep221 ep113 ep221 441179 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 612863863) qz285 0 1 ep221 ep112 ep221 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 612863863) qz286 0 1 ep221 ep113 ep221 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz331 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 105713607) qz19)

noncomputable def ep223 := @Enclosure.Real.IsNear.cos_image qz60 qz331 Bool.false 105713607 524288 65 65536 Bool.false 441179 524288 1 81900 (@Enclosure.Real.IsNear.recentre' qz60 Bool.false 908072972197084758771 4503599627370496000 811430000199368351 819000000000000000000 105713607 524288 65 65536 (ep220 rfl) rfl) (Enclosure.sfrac_false_div 105713607 524288) (BSN.cos_reduce0 qz331 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 43126460436760110301184) qz22) 226375608064910080 72057594037927936 Bool.false 441179 524288 32 1000000000000000 163800 81900 (BSN.sin_reduce_arg_pos_rat_q0 105713607 524288 226375608064910080 72057594037927936 32 43126460436760110301184 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 441179 524288 43126460436760110301184 75557863725914323419136 612863863 1073741824 163960 163800 (ep222 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep224 := BSN.sin_dyadic_bound_f 612863863 1073741824 2 1 524288 163960 ep221 ep108 ep221 ep221 ep109 ep221 283264 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 612863863) qz281 0 1 ep221 ep108 ep221 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 612863863) qz282 0 1 ep221 ep109 ep221 rfl rfl rfl rfl) rfl rfl

noncomputable def ep225 := @Enclosure.Real.IsNear.sin_image qz60 qz331 Bool.false 105713607 524288 65 65536 Bool.false 283264 524288 1 81900 (@Enclosure.Real.IsNear.recentre' qz60 Bool.false 908072972197084758771 4503599627370496000 811430000199368351 819000000000000000000 105713607 524288 65 65536 (ep220 rfl) rfl) (Enclosure.sfrac_false_div 105713607 524288) (BSN.sin_reduce0 qz331 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 43126460436760110301184) qz22) 226375608064910080 72057594037927936 Bool.false 283264 524288 32 1000000000000000 163800 81900 (BSN.sin_reduce_arg_pos_rat_q0 105713607 524288 226375608064910080 72057594037927936 32 43126460436760110301184 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 283264 524288 43126460436760110301184 75557863725914323419136 612863863 1073741824 163960 163800 (ep224 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz332 := (@Enclosure.Real.IsNear.recentre' qz59 Bool.false 151349 524288 1 524288 151349 524288 1 524288 (ep218 rfl rfl) rfl)

noncomputable def ep226 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz59 (Real.cos qz60)) (@HMul.hMul Real Real Real qz0 qz59 (@Neg.neg Real Real.instNeg (Real.sin qz60))) Bool.false 66772000471 274877906944 21870591163 75041668595712 Bool.true 334935337 2147483648 1364217523 4690104287232 (@Enclosure.Real.IsNear.mulLit_ff qz59 (Real.cos qz60) 151349 524288 1 524288 441179 524288 1347259 1341849600 66772000471 274877906944 21870591163 75041668595712 qz332 (@Enclosure.Real.IsNear.recentre' (Real.cos qz60) Bool.false 441179 524288 5389036 5367398400 441179 524288 1347259 1341849600 (ep223 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz59 (@Neg.neg Real Real.instNeg (Real.sin qz60)) 151349 524288 1 524288 2213 4096 1347259 1341849600 334935337 2147483648 1364217523 4690104287232 qz332 (@Enclosure.Real.IsNear.neg (Real.sin qz60) Bool.false 2213 4096 1347259 1341849600 (@Enclosure.Real.IsNear.recentre' (Real.sin qz60) Bool.false 283264 524288 5389036 5367398400 2213 4096 1347259 1341849600 (ep225 rfl rfl) rfl)) rfl)

noncomputable def ep227 := @ep166 66772000471 274877906944 21870591163 75041668595712 Bool.true 334935337 2147483648 1364217523 4690104287232 Bool.false 16110824819590525091840 937773428135 274877906944 26161319093069 5628125144678400 Bool.false 23099297932171542528 10756448811 137438953472 3270801129343 703515643084800 (ep167 (BSN.head_sum_c_succ qz5 11 12 rfl rfl) (ep216 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep217 ep226) rfl rfl

noncomputable abbrev qz333 := (@Nat.cast Real Real.instNatCast 13)

noncomputable abbrev qz62 := (@Inv.inv Real Real.instInv (Real.sqrt qz333))

noncomputable abbrev qz63 := (@HMul.hMul Real Real Real qz265 qz278 (Real.log (Enclosure.sfrac Bool.false 13 1)))

noncomputable def ep228 := @Enclosure.Complex.IsNear.of_eq qz46 (Complex.mk (@HMul.hMul Real Real Real qz0 qz62 (Real.cos qz63)) (@HMul.hMul Real Real Real qz0 qz62 (@Neg.neg Real Real.instNeg (Real.sin qz63)))) Bool.false 13519006081 68719476736 393718832641 1407031286169600 Bool.true 26869480813 137438953472 787413934757 2814062572339200 (BSN.cpow_neg_s_mk qz16 81143 1000 13 qz17 rfl)

noncomputable abbrev qz334 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 13) qz18)

noncomputable def ep229 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz333) 1890347 524288 1 524288 72705 72706 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz333) (Real.sqrt qz334) Bool.false 1890347 524288 1 524288 (BSN.sqrt_natCast_div_one 13) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz334) Bool.false 1890347 524288 1 524288 1890347 524288 1 524288 (BSN.sqrt_enclosure 13 1 945173 945174 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep230 := BSN.log_dyadic_bound 5 21 5 4 35742602096145 262144 81900 699352521000 41015625 127272 26 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 5) (BSN.artanhQ 21) 0 4 699352521000 35742602096145 41015625 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz64 := (Real.log (Enclosure.sfrac Bool.false 13 1))

noncomputable def ep231 := @Enclosure.Real.IsNear.mulLit_ff qz16 qz64 81143 1000 0 1 11551488463034085 4503599627370496 10000000002457 819000000000000000 187464485671194951831 900719925474099200 811430000199368351 819000000000000000000 qz21 (BSN.isNear_log_sfrac 13 1 11551488463034085 4503599627370496 10000000002457 819000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz334) Bool.false 24225227133228857425920 9444732965739290427392 1000000000245700 81900000000000000000 11551488463034085 4503599627370496 10000000002457 819000000000000000 (BSN.log_rat_reduce_isNear 13 1 3 26 16 127272 262144 24973259072661432 36028797018963968 81900 1000000000000000 rfl rfl rfl rfl (ep230 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep232 := nat_lit 1111829255620147952251887878974272984249832023687296334993166108306157844001

noncomputable def ep233 := nat_lit 247779332760326155511328641240355901620435122282753708710975252464383521

noncomputable def ep234 := nat_lit 3334992208194923204444640979640338240946255200817323497562076374413544764961

noncomputable def ep235 := BSN.cos_dyadic_bound_f 839959091 1073741824 3 2 524288 163960 ep232 ep64 ep233 ep234 ep66 ep233 371884 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 839959091) qz285 0 2 ep232 ep64 ep233 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 839959091) qz286 0 2 ep234 ep66 ep233 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz335 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 27279673) (@Nat.cast Real Real.instNatCast 131072))

noncomputable def ep236 := @Enclosure.Real.IsNear.cos_image qz63 qz335 Bool.false 27279673 131072 65 65536 Bool.false 371884 524288 1 81900 (@Enclosure.Real.IsNear.recentre' qz63 Bool.false 187464485671194951831 900719925474099200 811430000199368351 819000000000000000000 27279673 131072 65 65536 (ep231 rfl) rfl) (Enclosure.sfrac_false_div 27279673 131072) (BSN.cos_reduce0 qz335 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 14776716605373374529536) qz314) 226375608064910080 72057594037927936 Bool.false 371884 524288 33 1000000000000000 163800 81900 (BSN.sin_reduce_arg_pos_rat_q0 27279673 131072 226375608064910080 72057594037927936 33 14776716605373374529536 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 371884 524288 14776716605373374529536 18889465931478580854784 839959091 1073741824 163960 163800 (ep235 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep237 := nat_lit 497774379373151502010197473208930961

noncomputable def ep238 := BSN.sin_dyadic_bound_f 839959091 1073741824 2 1 524288 163960 ep237 ep108 ep237 ep237 ep109 ep237 369566 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 839959091) qz281 0 1 ep237 ep108 ep237 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 839959091) qz282 0 1 ep237 ep109 ep237 rfl rfl rfl rfl) rfl rfl

noncomputable def ep239 := @Enclosure.Real.IsNear.sin_image qz63 qz335 Bool.false 27279673 131072 65 65536 Bool.false 369566 524288 1 81900 (@Enclosure.Real.IsNear.recentre' qz63 Bool.false 187464485671194951831 900719925474099200 811430000199368351 819000000000000000000 27279673 131072 65 65536 (ep231 rfl) rfl) (Enclosure.sfrac_false_div 27279673 131072) (BSN.sin_reduce0 qz335 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 14776716605373374529536) qz314) 226375608064910080 72057594037927936 Bool.false 369566 524288 33 1000000000000000 163800 81900 (BSN.sin_reduce_arg_pos_rat_q0 27279673 131072 226375608064910080 72057594037927936 33 14776716605373374529536 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 369566 524288 14776716605373374529536 18889465931478580854784 839959091 1073741824 163960 163800 (ep238 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz336 := (@Enclosure.Real.IsNear.recentre' qz62 Bool.false 145411 524288 1 524288 145411 524288 1 524288 (ep229 rfl rfl) rfl)

noncomputable def ep240 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz62 (Real.cos qz63)) (@HMul.hMul Real Real Real qz0 qz62 (@Neg.neg Real Real.instNeg (Real.sin qz63))) Bool.false 13519006081 68719476736 393718832641 1407031286169600 Bool.true 26869480813 137438953472 787413934757 2814062572339200 (@Enclosure.Real.IsNear.mulLit_ff qz62 (Real.cos qz63) 145411 524288 1 524288 92971 131072 1347259 1341849600 13519006081 68719476736 393718832641 1407031286169600 qz336 (@Enclosure.Real.IsNear.recentre' (Real.cos qz63) Bool.false 371884 524288 5389036 5367398400 92971 131072 1347259 1341849600 (ep236 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz62 (@Neg.neg Real Real.instNeg (Real.sin qz63)) 145411 524288 1 524288 184783 262144 1347259 1341849600 26869480813 137438953472 787413934757 2814062572339200 qz336 (@Enclosure.Real.IsNear.neg (Real.sin qz63) Bool.false 184783 262144 1347259 1341849600 (@Enclosure.Real.IsNear.recentre' (Real.sin qz63) Bool.false 369566 524288 5389036 5367398400 184783 262144 1347259 1341849600 (ep239 rfl rfl) rfl)) rfl)

noncomputable def ep241 := @ep164 13519006081 68719476736 393718832641 1407031286169600 Bool.true 26869480813 137438953472 787413934757 2814062572339200 Bool.false 68159375373870588493824 991849452459 274877906944 9245398141211 1876041714892800 Bool.true 2214558255615725010944 8056516001 68719476736 4623539484043 938020857446400 (ep165 (BSN.head_sum_c_succ qz5 12 13 rfl rfl) (ep227 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep228 ep240) rfl rfl

noncomputable abbrev qz337 := (@Nat.cast Real Real.instNatCast 14)

noncomputable abbrev qz65 := (@Inv.inv Real Real.instInv (Real.sqrt qz337))

noncomputable abbrev qz66 := (@HMul.hMul Real Real Real qz265 qz278 (Real.log (Enclosure.sfrac Bool.false 14 1)))

noncomputable def ep242 := @Enclosure.Complex.IsNear.of_eq qz45 (Complex.mk (@HMul.hMul Real Real Real qz0 qz65 (Real.cos qz66)) (@HMul.hMul Real Real Real qz0 qz65 (@Neg.neg Real Real.instNeg (Real.sin qz66)))) Bool.false 32013584991 137438953472 759800446117 2814062572339200 Bool.true 18009892251 137438953472 757754174617 2814062572339200 (BSN.cpow_neg_s_mk qz16 81143 1000 14 qz17 rfl)

noncomputable abbrev qz338 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 14) qz18)

noncomputable def ep243 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz337) 1961707 524288 1 524288 70060 70061 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz337) (Real.sqrt qz338) Bool.false 1961707 524288 1 524288 (BSN.sqrt_natCast_div_one 14) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz338) Bool.false 1961707 524288 1 524288 1961707 524288 1 524288 (BSN.sqrt_enclosure 14 1 980853 980854 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep244 := BSN.log_dyadic_bound 6 22 5 4 51857700491520 262144 81900 1346332575744 176359680 146699 28 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 6) (BSN.artanhQ 22) 0 4 1346332575744 51857700491520 176359680 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz67 := (Real.log (Enclosure.sfrac Bool.false 14 1))

noncomputable def ep245 := @Enclosure.Real.IsNear.mulLit_ff qz16 qz67 81143 1000 0 1 11885241781671653 4503599627370496 10000000002457 819000000000000000 964404173890182939379 4503599627370496000 811430000199368351 819000000000000000000 qz21 (BSN.isNear_log_sfrac 14 1 11885241781671653 4503599627370496 10000000002457 819000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz338) Bool.false 24925158572916270432256 9444732965739290427392 1000000000245700 81900000000000000000 11885241781671653 4503599627370496 10000000002457 819000000000000000 (BSN.log_rat_reduce_isNear 14 1 3 28 16 146699 262144 24973259072661432 36028797018963968 81900 1000000000000000 rfl rfl rfl rfl (ep244 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep246 := nat_lit 91660263286025450462082876563657281

noncomputable def ep247 := BSN.cos_dyadic_bound_f 550231279 1073741824 2 1 524288 163960 ep246 ep112 ep246 ep246 ep113 ep246 456942 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 550231279) qz285 0 1 ep246 ep112 ep246 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 550231279) qz286 0 1 ep246 ep113 ep246 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz339 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 56135711) qz26)

noncomputable def ep248 := @Enclosure.Real.IsNear.cos_image qz66 qz339 Bool.false 56135711 262144 65 65536 Bool.false 456942 524288 1 81900 (@Enclosure.Real.IsNear.recentre' qz66 Bool.false 964404173890182939379 4503599627370496000 811430000199368351 819000000000000000000 56135711 262144 65 65536 (ep245 rfl) rfl) (Enclosure.sfrac_false_div 56135711 262144) (BSN.cos_reduce0 qz339 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 19359542059672138678272) qz292) 226375608064910080 72057594037927936 Bool.false 456942 524288 34 1000000000000000 163800 81900 (BSN.sin_reduce_arg_pos_rat_q0 56135711 262144 226375608064910080 72057594037927936 34 19359542059672138678272 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 456942 524288 19359542059672138678272 37778931862957161709568 550231279 1073741824 163960 163800 (ep247 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep249 := BSN.sin_dyadic_bound_f 550231279 1073741824 2 1 524288 163960 ep246 ep108 ep246 ep246 ep109 ep246 257062 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 550231279) qz281 0 1 ep246 ep108 ep246 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 550231279) qz282 0 1 ep246 ep109 ep246 rfl rfl rfl rfl) rfl rfl

noncomputable def ep250 := @Enclosure.Real.IsNear.sin_image qz66 qz339 Bool.false 56135711 262144 65 65536 Bool.false 257062 524288 1 81900 (@Enclosure.Real.IsNear.recentre' qz66 Bool.false 964404173890182939379 4503599627370496000 811430000199368351 819000000000000000000 56135711 262144 65 65536 (ep245 rfl) rfl) (Enclosure.sfrac_false_div 56135711 262144) (BSN.sin_reduce0 qz339 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 19359542059672138678272) qz292) 226375608064910080 72057594037927936 Bool.false 257062 524288 34 1000000000000000 163800 81900 (BSN.sin_reduce_arg_pos_rat_q0 56135711 262144 226375608064910080 72057594037927936 34 19359542059672138678272 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 257062 524288 19359542059672138678272 37778931862957161709568 550231279 1073741824 163960 163800 (ep249 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz340 := (@Enclosure.Real.IsNear.recentre' qz65 Bool.false 140121 524288 1 524288 140121 524288 1 524288 (ep243 rfl rfl) rfl)

noncomputable def ep251 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz65 (Real.cos qz66)) (@HMul.hMul Real Real Real qz0 qz65 (@Neg.neg Real Real.instNeg (Real.sin qz66))) Bool.false 32013584991 137438953472 759800446117 2814062572339200 Bool.true 18009892251 137438953472 757754174617 2814062572339200 (@Enclosure.Real.IsNear.mulLit_ff qz65 (Real.cos qz66) 140121 524288 1 524288 228471 262144 1347259 1341849600 32013584991 137438953472 759800446117 2814062572339200 qz340 (@Enclosure.Real.IsNear.recentre' (Real.cos qz66) Bool.false 456942 524288 5389036 5367398400 228471 262144 1347259 1341849600 (ep248 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz65 (@Neg.neg Real Real.instNeg (Real.sin qz66)) 140121 524288 1 524288 128531 262144 1347259 1341849600 18009892251 137438953472 757754174617 2814062572339200 qz340 (@Enclosure.Real.IsNear.neg (Real.sin qz66) Bool.false 128531 262144 1347259 1341849600 (@Enclosure.Real.IsNear.recentre' (Real.sin qz66) Bool.false 257062 524288 5389036 5367398400 128531 262144 1347259 1341849600 (ep250 rfl rfl) rfl)) rfl)

noncomputable def ep252 := @ep162 32013584991 137438953472 759800446117 2814062572339200 Bool.true 18009892251 137438953472 757754174617 2814062572339200 Bool.false 145118577983841110065152 1055876622441 274877906944 29255795315867 5628125144678400 Bool.true 2344909499368323678208 34122924253 137438953472 7314186313373 1407031286169600 (ep163 (BSN.head_sum_c_succ qz5 13 14 rfl rfl) (ep241 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep242 ep251) rfl rfl

noncomputable abbrev qz341 := (@Nat.cast Real Real.instNatCast 15)

noncomputable abbrev qz68 := (@Inv.inv Real Real.instInv (Real.sqrt qz341))

noncomputable abbrev qz69 := (@HMul.hMul Real Real Real qz265 qz278 (Real.log (Enclosure.sfrac Bool.false 15 1)))

noncomputable def ep253 := @Enclosure.Complex.IsNear.of_eq qz44 (Complex.mk (@HMul.hMul Real Real Real qz0 qz68 (Real.cos qz69)) (@HMul.hMul Real Real Real qz0 qz68 (@Neg.neg Real Real.instNeg (Real.sin qz69)))) Bool.false 69920339839 274877906944 490798808753 1876041714892800 Bool.false 12180547209 274877906944 487887741503 1876041714892800 (BSN.cpow_neg_s_mk qz16 81143 1000 15 qz17 rfl)

noncomputable abbrev qz342 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 15) qz18)

noncomputable def ep254 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz341) 2030559 524288 1 524288 67685 67686 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz341) (Real.sqrt qz342) Bool.false 2030559 524288 1 524288 (BSN.sqrt_natCast_div_one 15) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz342) Bool.false 2030559 524288 1 524288 2030559 524288 1 524288 (BSN.sqrt_enclosure 15 1 1015279 1015280 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep255 := BSN.log_dyadic_bound 7 23 6 5 430628584065881355 262144 81900 14087658153505881 266939110305 164785 30 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 7) (BSN.artanhQ 23) 0 5 14087658153505881 430628584065881355 266939110305 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz70 := (Real.log (Enclosure.sfrac Bool.false 15 1))

noncomputable def ep256 := @Enclosure.Real.IsNear.mulLit_ff qz16 qz70 81143 1000 0 1 12195956895733477 4503599627370496 10000000002457 819000000000000000 989616530390501524211 4503599627370496000 811430000199368351 819000000000000000000 qz21 (BSN.isNear_log_sfrac 15 1 12195956895733477 4503599627370496 10000000002457 819000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz342) Bool.false 25576775395801252757504 9444732965739290427392 1000000000245700 81900000000000000000 12195956895733477 4503599627370496 10000000002457 819000000000000000 (BSN.log_rat_reduce_isNear 15 1 3 30 16 164785 262144 24973259072661432 36028797018963968 81900 1000000000000000 rfl rfl rfl rfl (ep255 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep257 := nat_lit 20452965478601517612705195052622523188906124753248121785463344325855317618145

noncomputable def ep258 := nat_lit 25825728861009506672738564185051474196665864496574634579157797539079286241

noncomputable def ep259 := nat_lit 53525477454371864070091076986283191679388105811226817172609170133605417774561

noncomputable def ep260 := BSN.sin_dyadic_bound_f 1501435131 1073741824 3 2 524288 163960 ep257 ep57 ep258 ep259 ep60 ep258 516509 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1501435131) qz281 0 2 ep257 ep57 ep258 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1501435131) qz282 0 2 ep259 ep60 ep258 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz343 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 57603263) qz26)

noncomputable def ep261 := @Enclosure.Real.IsNear.cos_image qz69 qz343 Bool.false 57603263 262144 521 524288 Bool.false 516509 524288 1 81900 (@Enclosure.Real.IsNear.recentre' qz69 Bool.false 989616530390501524211 4503599627370496000 811430000199368351 819000000000000000000 57603263 262144 521 524288 (ep256 rfl) rfl) (Enclosure.sfrac_false_div 57603263 262144) (BSN.cos_reduce3 qz343 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 52827052349067211309056) qz292) 226375608064910080 72057594037927936 Bool.false 516509 524288 34 1000000000000000 163800 81900 (BSN.sin_reduce_arg_pos_rat_q3 57603263 262144 226375608064910080 72057594037927936 34 52827052349067211309056 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 516509 524288 52827052349067211309056 37778931862957161709568 1501435131 1073741824 163960 163800 (ep260 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep262 := nat_lit 11374236700939069565579658835539202426813031913802989718403705868825878359521

noncomputable def ep263 := nat_lit 34071058645095189683393499378247504332045764012415819886052802011399476506081

noncomputable def ep264 := BSN.cos_dyadic_bound_f 1501435131 1073741824 3 2 524288 163960 ep262 ep64 ep258 ep263 ep66 ep258 89979 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1501435131) qz285 0 2 ep262 ep64 ep258 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1501435131) qz286 0 2 ep263 ep66 ep258 rfl rfl rfl rfl) rfl rfl

noncomputable def ep265 := @Enclosure.Real.IsNear.sin_image qz69 qz343 Bool.false 57603263 262144 521 524288 Bool.true 89979 524288 1 81900 (@Enclosure.Real.IsNear.recentre' qz69 Bool.false 989616530390501524211 4503599627370496000 811430000199368351 819000000000000000000 57603263 262144 521 524288 (ep256 rfl) rfl) (Enclosure.sfrac_false_div 57603263 262144) (BSN.sin_reduce3 qz343 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 52827052349067211309056) qz292) 226375608064910080 72057594037927936 Bool.false 89979 524288 34 1000000000000000 163800 81900 (BSN.sin_reduce_arg_pos_rat_q3 57603263 262144 226375608064910080 72057594037927936 34 52827052349067211309056 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 89979 524288 52827052349067211309056 37778931862957161709568 1501435131 1073741824 163960 163800 (ep264 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz344 := (@Enclosure.Real.IsNear.recentre' qz68 Bool.false 135371 524288 1 524288 135371 524288 1 524288 (ep254 rfl rfl) rfl)

noncomputable def ep266 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz68 (Real.cos qz69)) (@HMul.hMul Real Real Real qz0 qz68 (@Neg.neg Real Real.instNeg (Real.sin qz69))) Bool.false 69920339839 274877906944 490798808753 1876041714892800 Bool.false 12180547209 274877906944 487887741503 1876041714892800 (@Enclosure.Real.IsNear.mulLit_ff qz68 (Real.cos qz69) 135371 524288 1 524288 516509 524288 10798547 10734796800 69920339839 274877906944 490798808753 1876041714892800 qz344 (@Enclosure.Real.IsNear.recentre' (Real.cos qz69) Bool.false 516509 524288 43194188 42939187200 516509 524288 10798547 10734796800 (ep261 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz68 (@Neg.neg Real Real.instNeg (Real.sin qz69)) 135371 524288 1 524288 89979 524288 10798547 10734796800 12180547209 274877906944 487887741503 1876041714892800 qz344 (@Enclosure.Real.IsNear.neg (Real.sin qz69) Bool.true 89979 524288 10798547 10734796800 (@Enclosure.Real.IsNear.recentre' (Real.sin qz69) Bool.true 89979 524288 43194188 42939187200 89979 524288 10798547 10734796800 (ep265 rfl rfl) rfl)) rfl)

noncomputable def ep267 := @ep160 69920339839 274877906944 490798808753 1876041714892800 Bool.false 12180547209 274877906944 487887741503 1876041714892800 Bool.false 309456712635439718072320 140724620285 34359738368 15364095871063 2814062572339200 Bool.true 7705556336352044253184 56065301297 274877906944 30720408478001 5628125144678400 (ep161 (BSN.head_sum_c_succ qz5 14 15 rfl rfl) (ep252 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep253 ep266) rfl rfl

noncomputable abbrev qz345 := (@Nat.cast Real Real.instNatCast 16)

noncomputable abbrev qz71 := (@Inv.inv Real Real.instInv (Real.sqrt qz345))

noncomputable abbrev qz72 := (@HMul.hMul Real Real Real qz265 qz278 (Real.log (Enclosure.sfrac Bool.false 16 1)))

noncomputable def ep268 := @Enclosure.Complex.IsNear.of_eq qz43 (Complex.mk (@HMul.hMul Real Real Real qz0 qz71 (Real.cos qz72)) (@HMul.hMul Real Real Real qz0 qz71 (@Neg.neg Real Real.instNeg (Real.sin qz72)))) Bool.false 23711399255 274877906944 1416407483059 5628125144678400 Bool.false 8062308281 34359738368 177847369373 703515643084800 (BSN.cpow_neg_s_mk qz16 81143 1000 16 qz17 rfl)

noncomputable abbrev qz346 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 16) qz18)

noncomputable def ep269 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz345) 2097153 524288 1 524288 65535 65536 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz345) (Real.sqrt qz346) Bool.false 2097153 524288 1 524288 (BSN.sqrt_natCast_div_one 16) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz346) Bool.false 2097153 524288 1 524288 2097153 524288 1 524288 (BSN.sqrt_enclosure 16 1 1048576 1048577 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep270 := BSN.log_dyadic_bound 0 32 1 0 1 262144 81900 0 1 0 32 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 0) (BSN.artanhQ 32) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz73 := (Real.log (Enclosure.sfrac Bool.false 16 1))

noncomputable def ep271 := @Enclosure.Real.IsNear.mulLit_ff qz16 qz73 81143 1000 0 1 3121657384082679 1125899906842624 2500000000819 204750000000000000 253300645116620822097 1125899906842624000 202857500066456117 204750000000000000000 qz21 (BSN.isNear_log_sfrac 16 1 3121657384082679 1125899906842624 2500000000819 204750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz346) Bool.false 26186360105375033720832 9444732965739290427392 1000000000327600 81900000000000000000 3121657384082679 1125899906842624 2500000000819 204750000000000000 (BSN.log_rat_reduce_isNear 16 1 4 32 32 0 262144 24973259072661432 36028797018963968 81900 1000000000000000 rfl rfl rfl rfl (ep270 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep272 := nat_lit 20474149325545773968773314461012641

noncomputable def ep273 := BSN.sin_dyadic_bound_f 378269623 1073741824 2 1 524288 163960 ep272 ep108 ep272 ep272 ep109 ep272 180905 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 378269623) qz281 0 1 ep272 ep108 ep272 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 378269623) qz282 0 1 ep272 ep109 ep272 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz347 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 7372019) (@Nat.cast Real Real.instNatCast 32768))

noncomputable def ep274 := @Enclosure.Real.IsNear.cos_image qz72 qz347 Bool.false 7372019 32768 65 65536 Bool.false 180905 524288 1 81900 (@Enclosure.Real.IsNear.recentre' qz72 Bool.false 253300645116620822097 1125899906842624000 202857500066456117 204750000000000000000 7372019 32768 65 65536 (ep271 rfl) rfl) (Enclosure.sfrac_false_div 7372019 32768) (BSN.cos_reduce3 qz347 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 1663647398633718939648) (@Nat.cast Real Real.instNatCast 4722366482869645213696)) 226375608064910080 72057594037927936 Bool.false 180905 524288 35 1000000000000000 163800 81900 (BSN.sin_reduce_arg_pos_rat_q3 7372019 32768 226375608064910080 72057594037927936 35 1663647398633718939648 4722366482869645213696 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 180905 524288 1663647398633718939648 4722366482869645213696 378269623 1073741824 163960 163800 (ep273 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep275 := BSN.cos_dyadic_bound_f 378269623 1073741824 2 1 524288 163960 ep272 ep112 ep272 ep272 ep113 ep272 492088 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 378269623) qz285 0 1 ep272 ep112 ep272 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 378269623) qz286 0 1 ep272 ep113 ep272 rfl rfl rfl rfl) rfl rfl

noncomputable def ep276 := @Enclosure.Real.IsNear.sin_image qz72 qz347 Bool.false 7372019 32768 65 65536 Bool.true 492088 524288 1 81900 (@Enclosure.Real.IsNear.recentre' qz72 Bool.false 253300645116620822097 1125899906842624000 202857500066456117 204750000000000000000 7372019 32768 65 65536 (ep271 rfl) rfl) (Enclosure.sfrac_false_div 7372019 32768) (BSN.sin_reduce3 qz347 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 1663647398633718939648) (@Nat.cast Real Real.instNatCast 4722366482869645213696)) 226375608064910080 72057594037927936 Bool.false 492088 524288 35 1000000000000000 163800 81900 (BSN.sin_reduce_arg_pos_rat_q3 7372019 32768 226375608064910080 72057594037927936 35 1663647398633718939648 4722366482869645213696 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 492088 524288 1663647398633718939648 4722366482869645213696 378269623 1073741824 163960 163800 (ep275 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz348 := (@Enclosure.Real.IsNear.recentre' qz71 Bool.false 131071 524288 1 524288 131071 524288 1 524288 (ep269 rfl rfl) rfl)

noncomputable def ep277 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz71 (Real.cos qz72)) (@HMul.hMul Real Real Real qz0 qz71 (@Neg.neg Real Real.instNeg (Real.sin qz72))) Bool.false 23711399255 274877906944 1416407483059 5628125144678400 Bool.false 8062308281 34359738368 177847369373 703515643084800 (@Enclosure.Real.IsNear.mulLit_ff qz71 (Real.cos qz72) 131071 524288 1 524288 180905 524288 1347259 1341849600 23711399255 274877906944 1416407483059 5628125144678400 qz348 (@Enclosure.Real.IsNear.recentre' (Real.cos qz72) Bool.false 180905 524288 5389036 5367398400 180905 524288 1347259 1341849600 (ep274 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz71 (@Neg.neg Real Real.instNeg (Real.sin qz72)) 131071 524288 1 524288 61511 65536 1347259 1341849600 8062308281 34359738368 177847369373 703515643084800 qz348 (@Enclosure.Real.IsNear.neg (Real.sin qz72) Bool.true 61511 65536 1347259 1341849600 (@Enclosure.Real.IsNear.recentre' (Real.sin qz72) Bool.true 492088 524288 5389036 5367398400 61511 65536 1347259 1341849600 (ep276 rfl rfl) rfl)) rfl)

noncomputable def ep278 := @ep158 23711399255 274877906944 1416407483059 5628125144678400 Bool.false 8062308281 34359738368 177847369373 703515643084800 Bool.false 39496806554170954874880 1149508361535 274877906944 2142973281679 375208342978560 Bool.false 289761341330547539968 8433164951 274877906944 2142879162199 375208342978560 (ep159 (BSN.head_sum_c_succ qz5 15 16 rfl rfl) (ep267 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep268 ep277) rfl rfl

theorem EMRow22.d7 : Enclosure.Complex.IsNear (BSN.headSumC qz5 17) Bool.false 1149508361535 274877906944 2142973281679 375208342978560 Bool.false 8433164951 274877906944 2142879162199 375208342978560 := ep157 (BSN.head_sum_c_succ qz5 16 17 rfl rfl) (ep278 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

theorem EMRow22.d8 : @Eq Nat (BSN.factNat (Nat.mul 2 1)) 2 := @Eq.refl Nat 2

theorem EMRow22.d9 : @Eq Nat (Nat.pow 17 1) 17 := @Eq.refl Nat 17

noncomputable def ep279 := nat_lit 784892268592994999809145176997569

noncomputable def ep280 := nat_lit 193579128633115738415365619712000

noncomputable def ep281 := nat_lit 126921190376787879927538844895791548117

noncomputable def ep282 := nat_lit 16230666237634668226903632305455104000000

noncomputable abbrev qz505 := (@instHMul Complex Complex.instMul)

noncomputable abbrev qz485 := qz505

noncomputable abbrev qz349 := qz485

noncomputable abbrev qz74 := qz349

noncomputable abbrev qz486 := (@instHSub Complex Complex.instSub)

noncomputable abbrev qz350 := qz486

noncomputable abbrev qz75 := qz350

noncomputable abbrev qz506 := (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (4 : Complex))

noncomputable abbrev qz507 := (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid))

noncomputable abbrev qz487 := (@HAdd.hAdd Complex Complex Complex qz503 (@HAdd.hAdd Complex Complex Complex qz503 qz506 (@HMul.hMul Complex Complex Complex qz505 Complex.I (@HDiv.hDiv Complex Complex Complex qz507 (↑qz504) (2 : Complex)))) (@Nat.cast Complex Complex.instNatCast 2))

noncomputable abbrev qz351 := qz487

noncomputable abbrev qz76 := (Complex.Stirling.logGammaStirling 1 qz351)

noncomputable abbrev qz488 := (@HAdd.hAdd Complex Complex Complex qz503 qz506 (@HMul.hMul Complex Complex Complex qz505 Complex.I (@HDiv.hDiv Complex Complex Complex qz507 (↑qz504) (2 : Complex))))

noncomputable abbrev qz352 := qz488

noncomputable abbrev qz77 := qz352

noncomputable abbrev qz78 := (@HMul.hMul Real Real Real qz265 (@HDiv.hDiv Real Real Real qz268 qz278 (2 : Real)) (Real.log Real.pi))

noncomputable abbrev qz353 := (@instHSub Real Real.instSub)

noncomputable def ep283 := Complex.re (@HMul.hMul Complex Complex Complex qz74 (Complex.exp (@HMul.hMul Complex Complex Complex qz74 Complex.I ↑(@HSub.hSub Real Real Real qz353 (Complex.im (@HSub.hSub Complex Complex Complex qz75 qz76 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz77 (@Nat.cast Complex Complex.instNatCast j))))) qz78))) (zetaApproximant qz5 1 17))

noncomputable def ep284 := @Enclosure.Real.IsNear.of_eq ep283 (@HSub.hSub Real Real Real qz353 (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz353 (Complex.im (@HSub.hSub Complex Complex Complex qz75 qz76 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz77 (@Nat.cast Complex Complex.instNatCast j))))) qz78)) (Complex.re (zetaApproximant qz5 1 17))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz353 (Complex.im (@HSub.hSub Complex Complex Complex qz75 qz76 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz77 (@Nat.cast Complex Complex.instNatCast j))))) qz78)) (Complex.im (zetaApproximant qz5 1 17))))

noncomputable def ep285 := nat_lit 261629762908048308199756011956933

noncomputable def ep286 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz353 (Complex.im (@HSub.hSub Complex Complex Complex qz75 qz76 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz77 (@Nat.cast Complex Complex.instNatCast j))))) qz78)) (Complex.re (zetaApproximant qz5 1 17))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz353 (Complex.im (@HSub.hSub Complex Complex Complex qz75 qz76 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz77 (@Nat.cast Complex Complex.instNatCast j))))) qz78)) (Complex.im (zetaApproximant qz5 1 17))) ep285

noncomputable def ep287 := nat_lit 64526376211038579471788539904000

noncomputable def ep288 := nat_lit 126419796077025067905909554961418165451

noncomputable def ep289 := nat_lit 297986885007520987714112677

noncomputable def ep290 := nat_lit 19357912863311573841536561971200

noncomputable def ep291 := nat_lit 14746891169494471224390880422746549

noncomputable def ep292 := nat_lit 477372536401019653732459773689856000000

noncomputable def ep293 := nat_lit 5064625380836713572606000142478626514054380993649772506749337600

noncomputable def ep294 := @Enclosure.Real.IsNear.mulLit_ff (Real.cos (@HSub.hSub Real Real Real qz353 (Complex.im (@HSub.hSub Complex Complex Complex qz75 qz76 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz77 (@Nat.cast Complex Complex.instNatCast j))))) qz78)) (Complex.re (zetaApproximant qz5 1 17)) 524287 524288 315317

noncomputable def ep295 := nat_lit 499020122391072653336352059

noncomputable def ep296 := nat_lit 123074295446469458526208000

noncomputable def ep297 := nat_lit 8891318517958583895765332143

noncomputable def ep298 := nat_lit 1511967719559877297994465280000

noncomputable def ep299 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HSub.hSub Real Real Real qz353 (Complex.im (@HSub.hSub Complex Complex Complex qz75 qz76 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz77 (@Nat.cast Complex Complex.instNatCast j))))) qz78)) Bool.false 524287 524288 1261268

noncomputable abbrev qz354 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 32941843) qz19)

noncomputable def ep300 := @Enclosure.Real.IsNear.cos_image (@HSub.hSub Real Real Real qz353 (Complex.im (@HSub.hSub Complex Complex Complex qz75 qz76 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz77 (@Nat.cast Complex Complex.instNatCast j))))) qz78) qz354 Bool.false 32941843 524288 15

noncomputable def ep301 := nat_lit 42939187200000000000000000

noncomputable def ep302 := @Enclosure.Real.IsNear.recentre' (@HSub.hSub Real Real Real qz353 (Complex.im (@HSub.hSub Complex Complex Complex qz75 qz76 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz77 (@Nat.cast Complex Complex.instNatCast j))))) qz78) Bool.false 1697809669708001924639 27021597764222976000 19592186262107209252799 ep301

noncomputable def ep303 := @Enclosure.Real.IsNear.subLit_ff_p (Complex.im (@HSub.hSub Complex Complex Complex qz75 qz76 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz77 (@Nat.cast Complex Complex.instNatCast j))))) qz78 2952784476969132447263 27021597764222976000 6300962862107209252799 ep301 6087429003 131072000

noncomputable def ep304 := nat_lit 222535309027967228266283008000

noncomputable def ep305 := nat_lit 53673984000000000000000000

noncomputable def ep306 := @Enclosure.Complex.IsNear.im_isNear (@HSub.hSub Complex Complex Complex qz75 qz76 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz77 (@Nat.cast Complex Complex.instNatCast j)))) Bool.true 5740870509627116089 90071992547409920 14113628494806385861553 ep305 Bool.false 2952784476969132447263 27021597764222976000

noncomputable def ep307 := nat_lit 17891328000000000000000000

noncomputable def ep308 := @Enclosure.Complex.IsNear.subLitP qz76 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz77 (@Nat.cast Complex Complex.instNatCast j))) Bool.true 5073741143994820929 90071992547409920 4595316164756548673851 ep307 Bool.false 3036676595478331071263 27021597764222976000 1925558287354756688533

noncomputable def ep309 := nat_lit 14313062400000000000000000

noncomputable def ep310 := nat_lit 12927291143969474743920453402755072

noncomputable def ep311 := nat_lit 831134941886473113599149979130134528

noncomputable abbrev qz508 := (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (2 : Complex))

noncomputable abbrev qz489 := qz508

noncomputable abbrev qz355 := (@HSub.hSub Complex Complex Complex qz486 qz487 qz489)

noncomputable abbrev qz356 := (Complex.log qz487)

noncomputable abbrev qz79 := (@HSub.hSub Complex Complex Complex qz350 (@HMul.hMul Complex Complex Complex qz349 qz355 qz356) qz351)

noncomputable abbrev qz357 := qz489

noncomputable abbrev qz80 := (@HMul.hMul Complex Complex Complex qz349 qz357 ↑(Real.log qz269))

noncomputable abbrev qz490 := qz507

noncomputable abbrev qz358 := qz490

noncomputable abbrev qz81 := qz358

noncomputable abbrev qz82 := (@instHMul Nat instMulNat)

noncomputable abbrev qz491 := (@instHPow Complex Int (@ZPow.toPow Complex (@DivInvMonoid.toZPow Complex Complex.instDivInvMonoid)))

noncomputable abbrev qz359 := qz491

noncomputable abbrev qz83 := qz359

noncomputable abbrev qz84 := qz351

noncomputable abbrev qz360 := (@OfNat.ofNat Int 1 (@instOfNat 1))

noncomputable abbrev qz85 := qz360

noncomputable abbrev qz361 := (@OfNat.ofNat Int 2 (@instOfNat 2))

noncomputable abbrev qz86 := qz361

noncomputable abbrev qz362 := (@instHSub Int Int.instSub)

noncomputable abbrev qz363 := (@instHMul Int Int.instMul)

noncomputable def ep312 := @Enclosure.Complex.IsNear.of_eq qz76 (@HAdd.hAdd Complex Complex Complex qz4 (@HAdd.hAdd Complex Complex Complex qz4 qz79 qz80) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz75 (@HMul.hMul Complex Complex Complex qz74 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz83 qz84 (@HSub.hSub Int Int Int qz362 qz85 (@HMul.hMul Int Int Int qz363 qz86 (@Nat.cast Int instNatCastInt k)))))) Bool.true 5073741143994820929

noncomputable def ep313 := @Enclosure.Complex.IsNear.addLitP (@HAdd.hAdd Complex Complex Complex qz4 qz79 qz80) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz75 (@HMul.hMul Complex Complex Complex qz74 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz83 qz84 (@HSub.hSub Int Int Int qz362 qz85 (@HMul.hMul Int Int Int qz363 qz86 (@Nat.cast Int instNatCastInt k))))) Bool.true 5073751372565342529 90071992547409920

noncomputable def ep314 := nat_lit 87166209127309530733725351936

noncomputable def ep315 := nat_lit 5216970666443221371094092165939200

noncomputable def ep316 := @ep313 280475649445769539 1092000000000000000000 Bool.false 1012243975757173339061 9007199254740992000 14690500022247589 109200000000000000000 Bool.false 1950945 17179869184 3 17179869184 Bool.true 10553702009 5153960755200 81143 25769803776000 Bool.true ep314 5073741143994820929 90071992547409920 4595316164756548673851 ep307 Bool.false ep315

noncomputable def ep317 := @Enclosure.Complex.IsNear.addLitP qz79 qz80 Bool.true 5156521920709552449 90071992547409920 276310000031707039 1092000000000000000000

noncomputable def ep318 := @ep317 Bool.false 1012243975757173339061 9007199254740992000 14690500022247589 109200000000000000000 Bool.false 120447 131072 1 262144 Bool.false 0 1 0 1 Bool.true 665026739904884575961088 5073751372565342529 90071992547409920 280475649445769539 1092000000000000000000 Bool.false 1012243975757173339061 1012243975757173339061 9007199254740992000

noncomputable abbrev qz87 := (@HMul.hMul Complex Complex Complex qz349 qz355 qz356)

noncomputable def ep319 := @Enclosure.Complex.IsNear.subLitP qz87 qz84 Bool.true 4953859937477880129 90071992547409920 276310000031707039 1092000000000000000000 Bool.false 1377679560320897495989

noncomputable def ep320 := nat_lit 4048975903028693356244000

noncomputable def ep321 := @ep319 9007199254740992000 14690500022247589 109200000000000000000 Bool.false 9000 4000 0 1 Bool.false 162286 4000 0 1 Bool.true 20626087682838209796000 5156521920709552449 90071992547409920 276310000031707039 1092000000000000000000 Bool.false ep320 1012243975757173339061 9007199254740992000 14690500022247589 109200000000000000000

noncomputable abbrev qz88 := qz355

noncomputable abbrev qz89 := qz356

noncomputable def ep322 := @Enclosure.Complex.IsNear.mul qz88 qz89 Bool.true 4953859937477880129 90071992547409920 276310000031707039 1092000000000000000000 Bool.false 1377679560320897495989 9007199254740992000 14690500022247589

noncomputable abbrev qz90 := (Complex.re qz355)

noncomputable abbrev qz91 := (Complex.re qz356)

noncomputable abbrev qz92 := (Complex.im qz355)

noncomputable abbrev qz93 := (Complex.im qz356)

noncomputable def ep323 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 qz90 qz91) (@HMul.hMul Real Real Real qz0 qz92 qz93) 116788271523755461 18014398509481984 500000000819 93600000000000000 2768900647548328717 45035996273704960

noncomputable def ep324 := nat_lit 44620403536942019122221833118547968

noncomputable def ep325 := @Enclosure.Real.IsNear.mulLit_ff qz90 qz91 7000 4000 0 1 16684038789107923 4503599627370496 500000000819 163800000000000000

noncomputable def ep326 := @Enclosure.Complex.IsNear.re_isNear qz88 Bool.false 7000 4000 0 1 Bool.false 162286 4000 0 1

noncomputable abbrev qz364 := (Enclosure.sfrac Bool.false 162286 4000)

noncomputable abbrev qz94 := qz364

noncomputable def ep327 := @Enclosure.Complex.IsNear.of_eq qz88 (Complex.mk (Enclosure.sfrac Bool.false 7000 4000) qz94) Bool.false 7000 4000 0 1 Bool.false 162286 4000 0

noncomputable abbrev qz365 := (Enclosure.sfrac Bool.false 9000 4000)

noncomputable abbrev qz95 := qz365

noncomputable abbrev qz366 := (Complex.log (Complex.mk qz95 qz94))

noncomputable def ep328 := @Enclosure.Complex.IsNear.of_eq qz89 qz366 Bool.false 16684038789107923 4503599627370496 500000000819 163800000000000000 Bool.false 853092887725475 562949953421312 10000000000819 1638000000000000000

noncomputable def ep329 := nat_lit 10644461007200359776476815662006353494654860666540417578013140365882457510007609029099520

noncomputable def ep330 := nat_lit 201679395538054756796562662924995051695693206741753386523738019770533864437811140624384

noncomputable def ep331 := nat_lit 10786835387741209646833977340059129098775944950904280080314519750983445855083233280

noncomputable def ep332 := BSN.log_dyadic_bound 10033745796 42801745796 5 4 ep329 524288 163800 ep330 ep331 250468 52835491592 32768000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 10033745796) (BSN.artanhQ 42801745796) 0 4 ep330 ep329 ep331 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz96 := (Enclosure.sfrac Bool.false 1 2)

noncomputable abbrev qz367 := (Real.log (Enclosure.sfrac Bool.false 26417745796 16000000))

noncomputable abbrev qz368 := (Enclosure.Real.IsNear.const Bool.false 1 2)

noncomputable abbrev qz369 := (@Nat.cast Real Real.instNatCast 16000000)

noncomputable def ep333 := @Enclosure.Real.IsNear.mulLit_ff qz96 qz367 1 2 0 1 16684038789107923 2251799813685248 500000000819 81900000000000000 16684038789107923 4503599627370496 500000000819 163800000000000000 qz368 (BSN.isNear_log_sfrac 26417745796 16000000 16684038789107923 2251799813685248 500000000819 81900000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 26417745796) qz369)) Bool.false 139955861258621035741184 18889465931478580854784 1000000001638000 163800000000000000000 16684038789107923 2251799813685248 500000000819 81900000000000000 (BSN.log_rat_reduce_isNear 26417745796 16000000 10 52835491592 32768000000 250468 524288 24973259072661432 36028797018963968 163800 1000000000000000 rfl rfl rfl rfl (ep332 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep334 := BSN.arctan_dyadic_bound_f 9000 162286 1 0 524288 163800 0 1 1 0 1 1 29045 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 9000) (BSN.arctanEvenQ 162286) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 9000) (BSN.arctanOddQ 162286) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz97 := (@HMul.hMul Real Real Real qz265 (Enclosure.sfrac Bool.false 1 2) Real.pi)

noncomputable abbrev qz98 := (@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 2) Real.pi 1 2 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 qz368 BSN.pi_near_15 rfl)

noncomputable abbrev qz370 := (Real.arctan (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 9000) (@Nat.cast Real Real.instNatCast 162286)))

noncomputable def ep335 := @Enclosure.Real.IsNear.subLit_ff_p qz97 qz370 884279719003555 562949953421312 1 2000000000000000 29045 524288 1 163800 447266363919813836800 853092887725475 562949953421312 10000000000819 1638000000000000000 qz98 (ep334 rfl) rfl rfl

noncomputable abbrev qz371 := (Real.arctan (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 162286) (@Nat.cast Real Real.instNatCast 9000)))

noncomputable def ep336 := @Enclosure.Complex.IsNear.re_isNear qz89 Bool.false 16684038789107923 4503599627370496 500000000819 163800000000000000 Bool.false 853092887725475 562949953421312 10000000000819 1638000000000000000 (ep328 (@congrArg Complex Complex qz84 (Complex.mk qz95 qz94) Complex.log (BSN.w_shift_mk qz16 Bool.false 81143 1000 2 qz17 rfl)) (@Enclosure.Complex.IsNear.of_parts qz366 Bool.false 16684038789107923 4503599627370496 500000000819 163800000000000000 Bool.false 853092887725475 562949953421312 10000000000819 1638000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz366) (@HMul.hMul Real Real Real qz0 qz96 qz367) Bool.false 16684038789107923 4503599627370496 500000000819 163800000000000000 (Enclosure.clog_re_eq 9000 162286 4000 26417745796 16000000 rfl rfl rfl) (ep333 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz366) qz371 Bool.false 853092887725475 562949953421312 10000000000819 1638000000000000000 (Enclosure.clog_im_eq 9000 162286 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz371 (@HSub.hSub Real Real Real qz353 qz97 qz370) Bool.false 853092887725475 562949953421312 10000000000819 1638000000000000000 (BSN.arctan_recip 162286 9000 rfl rfl) ep335))))

noncomputable def ep337 := @Enclosure.Real.IsNear.mulLit_ff qz92 qz93 162286 4000 0 1 853092887725475 562949953421312 10000000000819 1638000000000000000

noncomputable def ep338 := @Enclosure.Complex.IsNear.im_isNear qz88 Bool.false 7000 4000 0 1 Bool.false 162286 4000 0 1

noncomputable def ep339 := @Enclosure.Complex.IsNear.im_isNear qz89 Bool.false 16684038789107923 4503599627370496 500000000819 163800000000000000 Bool.false 853092887725475 562949953421312 10000000000819 1638000000000000000 (ep328 (@congrArg Complex Complex qz84 (Complex.mk qz95 qz94) Complex.log (BSN.w_shift_mk qz16 Bool.false 81143 1000 2 qz17 rfl)) (@Enclosure.Complex.IsNear.of_parts qz366 Bool.false 16684038789107923 4503599627370496 500000000819 163800000000000000 Bool.false 853092887725475 562949953421312 10000000000819 1638000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz366) (@HMul.hMul Real Real Real qz0 qz96 qz367) Bool.false 16684038789107923 4503599627370496 500000000819 163800000000000000 (Enclosure.clog_re_eq 9000 162286 4000 26417745796 16000000 rfl rfl rfl) (ep333 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz366) qz371 Bool.false 853092887725475 562949953421312 10000000000819 1638000000000000000 (Enclosure.clog_im_eq 9000 162286 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz371 (@HSub.hSub Real Real Real qz353 qz97 qz370) Bool.false 853092887725475 562949953421312 10000000000819 1638000000000000000 (BSN.arctan_recip 162286 9000 rfl rfl) ep335))))

noncomputable abbrev qz372 := (Enclosure.Real.IsNear.const Bool.false 162286 4000)

noncomputable abbrev qz99 := (@ep327 1 (BSN.w_sub_half_mk qz278 Bool.false 81143 1000 2 qz280 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7000 4000) qz364 Bool.false 7000 4000 0 1 Bool.false 162286 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 7000 4000) qz372))

noncomputable def ep340 := @ep323 811430000066456117 3276000000000000000000 ep324 4953859937477880129 90071992547409920 276310000031707039 1092000000000000000000 (@ep325 116788271523755461 18014398509481984 500000000819 93600000000000000 (ep326 qz99) ep336 rfl) (@ep337 2768900647548328717 45035996273704960 811430000066456117 3276000000000000000000 (ep338 qz99) ep339 rfl) rfl

noncomputable def ep341 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz90 qz93) (@HMul.hMul Real Real Real qz0 qz92 qz91) 5971650214078325 2251799813685248 10000000000819 936000000000000000 1353792959464584195989 9007199254740992000

noncomputable def ep342 := nat_lit 3102258577248571364810972817388470272

noncomputable def ep343 := @Enclosure.Real.IsNear.mulLit_ff qz90 qz93 7000 4000 0 1 853092887725475 562949953421312 10000000000819 1638000000000000000

noncomputable def ep344 := @Enclosure.Real.IsNear.mulLit_ff qz92 qz91 162286 4000 0 1 16684038789107923 4503599627370496 500000000819 163800000000000000

noncomputable def ep345 := @ep341 40571500066456117 327600000000000000000 ep342 1377679560320897495989 9007199254740992000 14690500022247589 109200000000000000000 (@ep343 5971650214078325 2251799813685248 10000000000819 936000000000000000 (ep326 qz99) ep339 rfl) (@ep344 1353792959464584195989 9007199254740992000 40571500066456117 327600000000000000000 (ep338 qz99) ep336 rfl) rfl

noncomputable def ep346 := @Enclosure.Complex.IsNear.of_eq qz84 (Complex.mk qz95 qz94) Bool.false 9000 4000 0 1 Bool.false 162286 4000 0 1 (BSN.w_shift_mk qz16 Bool.false 81143 1000 2 qz17 rfl)

noncomputable abbrev qz373 := (ep346 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 9000 4000) (Enclosure.sfrac Bool.false 162286 4000) Bool.false 9000 4000 0 1 Bool.false 162286 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 9000 4000) (Enclosure.Real.IsNear.const Bool.false 162286 4000)))

noncomputable abbrev qz100 := qz373

noncomputable def ep347 := ep321 (@ep322 109200000000000000000 (ep340 rfl) (ep345 rfl)) qz100 rfl rfl rfl rfl rfl rfl

noncomputable abbrev qz101 := qz357

noncomputable def ep348 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re qz101) (Complex.re ↑qz2)) (@HMul.hMul Real Real Real qz0 (Complex.im qz101) (Complex.im ↑qz2)) 120447 131072 1 262144 0 1 0 1 120447 120447

noncomputable def ep349 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re qz101) (Complex.re ↑qz2) 1 2 0 1 120447 65536 1 131072 120447 131072 1 262144

noncomputable abbrev qz102 := (@Enclosure.Complex.IsNear.of_eq qz357 (Complex.mk (Enclosure.sfrac Bool.false 1 2) qz276) Bool.false 1 2 0 1 Bool.false 0 1 0 1 BSN.half_c_mk (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 2) qz276 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz368 qz288))

noncomputable def ep350 := ep349 (@Enclosure.Complex.IsNear.re_isNear qz101 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz102) (@Enclosure.Real.IsNear.of_eq (Complex.re ↑qz2) qz2 Bool.false 120447 65536 1 131072 (Complex.ofReal_re qz2) EMRow22.d4)

noncomputable def ep351 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz101) (Complex.im ↑qz2) 0 1 0 1 0 1 0 1 0 1 0 1

noncomputable def ep352 := ep351 (@Enclosure.Complex.IsNear.im_isNear qz101 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz102) (@Enclosure.Real.IsNear.of_eq (Complex.im ↑qz2) qz13 Bool.false 0 1 0 1 (@Eq.trans Real (Complex.im ↑qz2) (0 : Real) qz13 (Complex.ofReal_im qz2) Enclosure.sfrac_zero_eq) qz23)

noncomputable def ep353 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re qz101) (Complex.im ↑qz2)) (@HMul.hMul Real Real Real qz0 (Complex.im qz101) (Complex.re ↑qz2)) 0 1 0 1 0 1 0 1 0 0

noncomputable def ep354 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re qz101) (Complex.im ↑qz2) 1 2 0 1 0 1 0 1 0 1 0 1

noncomputable def ep355 := ep354 (@Enclosure.Complex.IsNear.re_isNear qz101 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz102) (@Enclosure.Real.IsNear.of_eq (Complex.im ↑qz2) qz13 Bool.false 0 1 0 1 (@Eq.trans Real (Complex.im ↑qz2) (0 : Real) qz13 (Complex.ofReal_im qz2) Enclosure.sfrac_zero_eq) qz23)

noncomputable def ep356 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz101) (Complex.re ↑qz2) 0 1 0 1 120447 65536 1 131072 0 1 0 1

noncomputable def ep357 := ep356 (@Enclosure.Complex.IsNear.im_isNear qz101 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz102) (@Enclosure.Real.IsNear.of_eq (Complex.re ↑qz2) qz2 Bool.false 120447 65536 1 131072 (Complex.ofReal_re qz2) EMRow22.d4)

noncomputable def ep358 := @ep318 14690500022247589 109200000000000000000 (ep347 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@Enclosure.Complex.IsNear.mul qz101 (↑qz2) Bool.false 120447 131072 1 262144 Bool.false 0 1 0 1 (@ep348 131072 1 262144 (ep350 rfl) (ep352 rfl) rfl rfl) (@ep353 1 0 1 (ep355 rfl) (ep357 rfl) rfl rfl))

noncomputable abbrev qz103 := (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 1)

noncomputable abbrev qz374 := (@Nat.cast Complex Complex.instNatCast 1)

noncomputable abbrev qz104 := (@HMul.hMul Complex Complex Complex qz349 (@HMul.hMul Complex Complex Complex qz349 (2 : Complex) qz374) (@HSub.hSub Complex Complex Complex qz350 (@HMul.hMul Complex Complex Complex qz349 (2 : Complex) qz374) (1 : Complex)))

noncomputable abbrev qz375 := (@HPow.hPow Complex Int Complex qz491 qz487 (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) (@OfNat.ofNat Int 1 (@instOfNat 1)) (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (@OfNat.ofNat Int 2 (@instOfNat 2)) (@Nat.cast Int instNatCastInt 1))))

noncomputable abbrev qz105 := qz375

noncomputable def ep359 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz75 (@HMul.hMul Complex Complex Complex qz74 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz83 qz84 (@HSub.hSub Int Int Int qz362 qz85 (@HMul.hMul Int Int Int qz363 qz86 (@Nat.cast Int instNatCastInt k))))) (@HAdd.hAdd Complex Complex Complex qz4 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz75 (@HMul.hMul Complex Complex Complex qz74 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz83 qz84 (@HSub.hSub Int Int Int qz362 qz85 (@HMul.hMul Int Int Int qz363 qz86 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 (@Rat.cast Complex Complex.instRatCast (bernoulli qz103)) qz104) qz105)) Bool.false 1950945 17179869184 3 17179869184

noncomputable def ep360 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz75 (@HMul.hMul Complex Complex Complex qz74 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz83 qz84 (@HSub.hSub Int Int Int qz362 qz85 (@HMul.hMul Int Int Int qz363 qz86 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 (@Rat.cast Complex Complex.instRatCast (bernoulli qz103)) qz104) qz105) Bool.false 0 1 0 1 Bool.false

noncomputable def ep361 := @ep360 0 1 0 1 Bool.false 1950945 17179869184 3 17179869184 Bool.true 10553702009 5153960755200 81143 25769803776000 Bool.false 1950945 1950945 17179869184 3 17179869184 Bool.true 10553702009 10553702009 5153960755200 81143

noncomputable def ep362 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz75 (@HMul.hMul Complex Complex Complex qz74 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz83 qz84 (@HSub.hSub Int Int Int qz362 qz85 (@HMul.hMul Int Int Int qz363 qz86 (@Nat.cast Int instNatCastInt k))))) (Complex.mk qz13 qz13) Bool.false 0 1 0 1 Bool.false

noncomputable def ep363 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz81 (@Rat.cast Complex Complex.instRatCast (bernoulli qz103)) qz104) qz105 Bool.false 1950945 17179869184 3 17179869184 Bool.true 10553702009 5153960755200 81143 25769803776000

noncomputable abbrev qz106 := (Complex.re qz375)

noncomputable abbrev qz107 := (Complex.im qz375)

noncomputable def ep364 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz81 (@Rat.cast Complex Complex.instRatCast (bernoulli qz103)) qz104)) qz106) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz81 (@Rat.cast Complex Complex.instRatCast (bernoulli qz103)) qz104)) qz107) 1950945 17179869184 3 17179869184 0 1 0

noncomputable def ep365 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz81 (@Rat.cast Complex Complex.instRatCast (bernoulli qz103)) qz104)) qz106 1 12 0 1 5852835 4294967296 9 4294967296 1950945

noncomputable def ep366 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz81 (@Rat.cast Complex Complex.instRatCast (bernoulli qz103)) qz104) (Complex.mk (Enclosure.sfrac Bool.false 1 12) qz13) Bool.false 1 12 0 1 Bool.false 0 1 0 1

noncomputable abbrev qz376 := (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 12) qz13 Bool.false 1 12 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 12) qz23)

noncomputable def ep367 := @Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz81 (@Rat.cast Complex Complex.instRatCast (bernoulli qz103)) qz104) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (ep366 (BSN.stirling_coeff_mk 1 1 6 Bool.false BSN.bern_real_1 rfl rfl) qz376)

noncomputable def ep368 := @Enclosure.Complex.IsNear.re_isNear qz105 Bool.false 5852835 4294967296 9 4294967296 Bool.true 10553702009 429496729600 81143 2147483648000

noncomputable abbrev qz492 := (@instHPow Complex Nat (@NPow.toPow Complex (@Monoid.toNPow Complex (@Semiring.toMonoid Complex Complex.instSemiring))))

noncomputable abbrev qz377 := (@HPow.hPow Complex Nat Complex qz492 qz487 1)

noncomputable abbrev qz108 := (@Inv.inv Complex Complex.instInv qz377)

noncomputable def ep369 := @Enclosure.Complex.IsNear.of_eq qz105 qz108 Bool.false 5852835 4294967296 9 4294967296 Bool.true 10553702009 429496729600 81143

noncomputable def ep370 := @Enclosure.Complex.IsNear.of_parts qz108 Bool.false 5852835 4294967296 9 4294967296 Bool.true 10553702009 429496729600 81143

noncomputable abbrev qz109 := (Complex.re qz377)

noncomputable abbrev qz110 := (@MonoidWithZeroHom Complex Real (@instMulZeroOneClassOfSemiring Complex Complex.instSemiring) (@instMulZeroOneClassOfSemiring Real Real.semiring))

noncomputable abbrev qz111 := (@MonoidWithZeroHom.funLike Complex Real (@instMulZeroOneClassOfSemiring Complex Complex.instSemiring) (@instMulZeroOneClassOfSemiring Real Real.semiring))

noncomputable abbrev qz112 := qz377

noncomputable def ep371 := @Enclosure.Real.IsNear.mulLit_ff qz109 (@Inv.inv Real Real.instInv (@DFunLike.coe qz110 Complex (fun (x : Complex) => Real) qz111 Complex.normSq qz112)) 9000 4000 0 1 650315 1073741824 1 1073741824

noncomputable def ep372 := @Enclosure.Complex.IsNear.re_isNear qz112 Bool.false 9000 4000 0 1 Bool.false 162286 4000 0 1

noncomputable def ep373 := @Enclosure.Complex.IsNear.of_eq qz112 qz84 Bool.false 9000 4000 0 1 Bool.false 162286 4000 0

noncomputable def ep374 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (@DFunLike.coe qz110 Complex (fun (x : Complex) => Real) qz111 Complex.normSq qz112)) Bool.false 650315 1073741824 1 1073741824 650315 1073741824 1

noncomputable abbrev qz113 := (Complex.im qz377)

noncomputable abbrev qz378 := (@instHAdd Real Real.instAdd)

noncomputable def ep375 := @Enclosure.Real.IsNear.of_eq (@DFunLike.coe qz110 Complex (fun (x : Complex) => Real) qz111 Complex.normSq qz112) (@HAdd.hAdd Real Real Real qz378 (@HMul.hMul Real Real Real qz0 qz109 qz109) (@HMul.hMul Real Real Real qz0 qz113 qz113)) Bool.false 6604436449 4000000 0 1

noncomputable def ep376 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz109 qz109) (@HMul.hMul Real Real Real qz0 qz113 qz113) 81 16 0 1 6584186449 4000000

noncomputable def ep377 := @Enclosure.Real.IsNear.mulLit_ff qz109 qz109 9000 4000 0 1 9000 4000 0 1

noncomputable def ep378 := @Enclosure.Real.IsNear.mulLit_ff qz113 qz113 162286 4000 0 1 162286 4000 0 1

noncomputable def ep379 := @Enclosure.Complex.IsNear.im_isNear qz112 Bool.false 9000 4000 0 1 Bool.false 162286 4000 0 1

noncomputable abbrev qz114 := (ep372 (@ep373 1 (BSN.pow_one_c qz351) qz373))

noncomputable abbrev qz115 := (ep379 (@ep373 1 (BSN.pow_one_c qz351) qz373))

noncomputable def ep380 := @ep376 0 1 105670983184 6604436449 4000000 0 1 (@ep377 81 16 0 1 qz114 qz114 rfl) (@ep378 6584186449 4000000 0 1 qz115 qz115 rfl)

noncomputable def ep381 := @Enclosure.Real.IsNear.inv_image (@DFunLike.coe qz110 Complex (fun (x : Complex) => Real) qz111 Complex.normSq qz112) 6604436449 4000000 0 1 325157 325158 536870912 (ep375 (Enclosure.Complex.normSq_eq_mul_add_mul qz112) (ep380 rfl rfl)) rfl

noncomputable def ep382 := @Enclosure.Real.IsNear.of_eq (Complex.re qz108) (@HMul.hMul Real Real Real qz0 qz109 (@Inv.inv Real Real.instInv (@DFunLike.coe qz110 Complex (fun (x : Complex) => Real) qz111 Complex.normSq qz112))) Bool.false 5852835 4294967296 9 4294967296 (Enclosure.Complex.inv_re_eq_mul qz112) (@ep371 5852835 4294967296 9 4294967296 qz114 (@ep374 1073741824 (ep381 rfl rfl rfl rfl rfl) rfl) rfl)

noncomputable def ep383 := @Enclosure.Real.IsNear.of_eq (Complex.im qz108) (@HMul.hMul Real Real Real qz0 (@Neg.neg Real Real.instNeg qz113) (@Inv.inv Real Real.instInv (@DFunLike.coe qz110 Complex (fun (x : Complex) => Real) qz111 Complex.normSq qz112))) Bool.true 10553702009 429496729600 81143 2147483648000 (Enclosure.Complex.inv_im_eq_mul qz112)

noncomputable def ep384 := @Enclosure.Real.IsNear.mulLit_tf (@Neg.neg Real Real.instNeg qz113) (@Inv.inv Real Real.instInv (@DFunLike.coe qz110 Complex (fun (x : Complex) => Real) qz111 Complex.normSq qz112)) 162286 4000 0 1 650315 1073741824 1

noncomputable def ep385 := @ep384 1073741824 10553702009 429496729600 81143 2147483648000 (@Enclosure.Real.IsNear.neg qz113 Bool.false 162286 4000 0 1 qz115) (@ep374 1073741824 (ep381 rfl rfl rfl rfl rfl) rfl) rfl

noncomputable def ep386 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz81 (@Rat.cast Complex Complex.instRatCast (bernoulli qz103)) qz104)) qz107 0 1 0 1 10553702009 429496729600 81143 2147483648000 0

noncomputable def ep387 := @Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz81 (@Rat.cast Complex Complex.instRatCast (bernoulli qz103)) qz104) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (ep366 (BSN.stirling_coeff_mk 1 1 6 Bool.false BSN.bern_real_1 rfl rfl) qz376)

noncomputable def ep388 := @Enclosure.Complex.IsNear.im_isNear qz105 Bool.false 5852835 4294967296 9 4294967296 Bool.true 10553702009 429496729600 81143 2147483648000

noncomputable abbrev qz116 := (@ep369 2147483648000 (BSN.zpow_one_sub_two_mul qz351 1 1 rfl rfl) (@ep370 2147483648000 ep382 (ep383 ep385)))

noncomputable def ep389 := @ep364 1 1950945 1950945 17179869184 3 17179869184 (@ep365 17179869184 3 17179869184 ep367 (ep368 qz116) rfl) (@ep386 1 0 1 ep387 (ep388 qz116) rfl) rfl

noncomputable def ep390 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz81 (@Rat.cast Complex Complex.instRatCast (bernoulli qz103)) qz104)) qz107) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz81 (@Rat.cast Complex Complex.instRatCast (bernoulli qz103)) qz104)) qz106) 10553702009 5153960755200 81143 25769803776000 0 1 0

noncomputable def ep391 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HDiv.hDiv Complex Complex Complex qz81 (@Rat.cast Complex Complex.instRatCast (bernoulli qz103)) qz104)) qz107 1 12 0 1 10553702009 429496729600 81143 2147483648000 10553702009

noncomputable def ep392 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz81 (@Rat.cast Complex Complex.instRatCast (bernoulli qz103)) qz104)) qz106 0 1 0 1 5852835 4294967296 9 4294967296 0

noncomputable def ep393 := @ep390 1 10553702009 10553702009 5153960755200 81143 25769803776000 (@ep391 5153960755200 81143 25769803776000 ep367 (ep388 qz116) rfl) (@ep392 1 0 1 ep387 (ep368 qz116) rfl) rfl

noncomputable abbrev qz117 := (@Enclosure.Complex.IsNear.mk qz276 qz276 Bool.false 0 1 0 1 Bool.false 0 1 0 1 qz288 qz288)

noncomputable def ep394 := @ep361 25769803776000 (@ep362 0 1 0 1 (BSN.stirling_sum_base qz84) qz117) (ep363 (ep389 rfl) (ep393 rfl)) rfl rfl rfl rfl rfl

noncomputable def ep395 := @ep316 3036676595478331071263 27021597764222976000 1925558287354756688533 ep309 (ep358 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep359 Bool.true 10553702009 5153960755200 81143 25769803776000 (BSN.stirling_sum_succ qz84 0 1 rfl) (ep394 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl

noncomputable def ep396 := @Enclosure.Complex.IsNear.of_eq (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz77 (@Nat.cast Complex Complex.instNatCast j))) (BSN.logSumC qz16 2) Bool.false 16678234140807379 2251799813685248 500000000819 81900000000000000 Bool.false 873876234470819 281474976710656

noncomputable abbrev qz118 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz271 qz352 qz374))

noncomputable def ep397 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz16 2) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.logSumC qz16 1) qz118) Bool.false 16678234140807379 2251799813685248 500000000819 81900000000000000 Bool.false 873876234470819 281474976710656 10000000000819 819000000000000000

noncomputable def ep398 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz16 1) qz118 Bool.false 16677209791107283 4503599627370496 500000000819 163800000000000000 Bool.false 880811532912035 562949953421312 10000000000819 1638000000000000000 Bool.false

noncomputable def ep399 := nat_lit 150224178123475993158960407379968

noncomputable def ep400 := nat_lit 983897170982678160037753389056

noncomputable abbrev qz119 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz271 qz352 (@Nat.cast Complex Complex.instNatCast 0)))

noncomputable def ep401 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz16 1) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.logSumC qz16 0) qz119) Bool.false 16677209791107283 4503599627370496 500000000819 163800000000000000 Bool.false 880811532912035 562949953421312 10000000000819 1638000000000000000

noncomputable def ep402 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz16 0) qz119 Bool.false 0 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable abbrev qz379 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz94))

noncomputable def ep403 := @Enclosure.Complex.IsNear.of_eq qz119 qz379 Bool.false 16677209791107283 4503599627370496 500000000819 163800000000000000 Bool.false 880811532912035 562949953421312 10000000000819 1638000000000000000

noncomputable def ep404 := nat_lit 10486335316793245914097050723863926414981574779110999265788906093799585237272172229099520

noncomputable def ep405 := nat_lit 196178142290997758861839388358903395025634438356514888093531348029387541938800580624384

noncomputable def ep406 := nat_lit 10117696820996669555341893898666500411027301619841363382491553586986564139883233280

noncomputable def ep407 := BSN.log_dyadic_bound 9953745796 42721745796 5 4 ep404 524288 163800 ep405 ep406 248878 52675491592 32768000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 9953745796) (BSN.artanhQ 42721745796) 0 4 ep405 ep404 ep406 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep408 := @Enclosure.Real.IsNear.mulLit_ff qz96 (Real.log (Enclosure.sfrac Bool.false 26337745796 16000000)) 1 2 0 1 16677209791107283 2251799813685248 500000000819 81900000000000000 16677209791107283 4503599627370496 500000000819 163800000000000000 qz368 (BSN.isNear_log_sfrac 26337745796 16000000 16677209791107283 2251799813685248 500000000819 81900000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 26337745796) qz369)) Bool.false 139898575471360883032064 18889465931478580854784 1000000001638000 163800000000000000000 16677209791107283 2251799813685248 500000000819 81900000000000000 (BSN.log_rat_reduce_isNear 26337745796 16000000 10 52675491592 32768000000 248878 524288 24973259072661432 36028797018963968 163800 1000000000000000 rfl rfl rfl rfl (ep407 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep409 := BSN.arctan_dyadic_bound_f 1000 162286 1 0 524288 163800 0 1 1 0 1 1 3230 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 162286) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 162286) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz380 := (@Nat.cast Real Real.instNatCast 1000)

noncomputable abbrev qz381 := (@Nat.cast Real Real.instNatCast 162286)

noncomputable def ep410 := @Enclosure.Real.IsNear.subLit_ff_p qz97 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz380 qz381)) 884279719003555 562949953421312 1 2000000000000000 3230 524288 1 163800 461798916967385006080 880811532912035 562949953421312 10000000000819 1638000000000000000 qz98 (ep409 rfl) rfl rfl

noncomputable abbrev qz120 := (@HAdd.hAdd Complex Complex Complex qz271 qz352 (@Nat.cast Complex Complex.instNatCast 0))

noncomputable abbrev qz382 := (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz94)

noncomputable def ep411 := @ep402 16677209791107283 4503599627370496 500000000819 163800000000000000 Bool.false 880811532912035 562949953421312 10000000000819 1638000000000000000 Bool.false 16677209791107283 16677209791107283 4503599627370496 500000000819 163800000000000000 Bool.false 880811532912035 880811532912035 562949953421312 10000000000819 1638000000000000000 (@Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz16 0) (Complex.mk qz13 qz13) Bool.false 0 1 0 1 Bool.false 0 1 0 1 (BSN.log_sum_c_base qz16) qz117) (ep403 (@congrArg Complex Complex qz120 qz382 Complex.log (BSN.w_shift_mk qz16 Bool.false 81143 1000 0 qz17 rfl)) (@Enclosure.Complex.IsNear.of_parts qz379 Bool.false 16677209791107283 4503599627370496 500000000819 163800000000000000 Bool.false 880811532912035 562949953421312 10000000000819 1638000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz379) (@HMul.hMul Real Real Real qz0 qz96 (Real.log (Enclosure.sfrac Bool.false 26337745796 16000000))) Bool.false 16677209791107283 4503599627370496 500000000819 163800000000000000 (Enclosure.clog_re_eq 1000 162286 4000 26337745796 16000000 rfl rfl rfl) (ep408 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz379) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz381 qz380)) Bool.false 880811532912035 562949953421312 10000000000819 1638000000000000000 (Enclosure.clog_im_eq 1000 162286 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz381 qz380)) (@HSub.hSub Real Real Real qz353 qz97 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz380 qz381))) Bool.false 880811532912035 562949953421312 10000000000819 1638000000000000000 (BSN.arctan_recip 162286 1000 rfl rfl) ep410)))) rfl rfl

noncomputable abbrev qz383 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz94))

noncomputable def ep412 := @Enclosure.Complex.IsNear.of_eq qz118 qz383 Bool.false 16679258490507475 4503599627370496 500000000819 163800000000000000 Bool.false 866940936029603 562949953421312 10000000000819 1638000000000000000

noncomputable def ep413 := nat_lit 10533555754969390581020972745811139691054093932536557687028788718570229232052803269099520

noncomputable def ep414 := nat_lit 197815647990192585678276564630908457711261307609882090941851244310096180320503748624384

noncomputable def ep415 := nat_lit 10314514257632031582479648338801402616917940968782379594074681180887068654443233280

noncomputable def ep416 := BSN.log_dyadic_bound 9977745796 42745745796 5 4 ep413 524288 163800 ep414 ep415 249355 52723491592 32768000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 9977745796) (BSN.artanhQ 42745745796) 0 4 ep414 ep413 ep415 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep417 := @Enclosure.Real.IsNear.mulLit_ff qz96 (Real.log (Enclosure.sfrac Bool.false 26361745796 16000000)) 1 2 0 1 16679258490507475 2251799813685248 500000000819 81900000000000000 16679258490507475 4503599627370496 500000000819 163800000000000000 qz368 (BSN.isNear_log_sfrac 26361745796 16000000 16679258490507475 2251799813685248 500000000819 81900000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 26361745796) qz369)) Bool.false 139915761207538928844800 18889465931478580854784 1000000001638000 163800000000000000000 16679258490507475 2251799813685248 500000000819 81900000000000000 (BSN.log_rat_reduce_isNear 26361745796 16000000 10 52723491592 32768000000 249355 524288 24973259072661432 36028797018963968 163800 1000000000000000 rfl rfl rfl rfl (ep416 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep418 := BSN.arctan_dyadic_bound_f 5000 162286 1 0 524288 163800 0 1 1 0 1 1 16148 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 5000) (BSN.arctanEvenQ 162286) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 5000) (BSN.arctanOddQ 162286) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz384 := (@Nat.cast Real Real.instNatCast 5000)

noncomputable def ep419 := @Enclosure.Real.IsNear.subLit_ff_p qz97 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz384 qz381)) 884279719003555 562949953421312 1 2000000000000000 16148 524288 1 163800 454526729469088497664 866940936029603 562949953421312 10000000000819 1638000000000000000 qz98 (ep418 rfl) rfl rfl

noncomputable abbrev qz121 := (@HAdd.hAdd Complex Complex Complex qz271 qz352 qz374)

noncomputable abbrev qz385 := (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz94)

noncomputable def ep420 := @ep398 16679258490507475 4503599627370496 500000000819 163800000000000000 Bool.false 866940936029603 562949953421312 10000000000819 1638000000000000000 Bool.false ep399 16678234140807379 2251799813685248 500000000819 81900000000000000 Bool.false ep400 873876234470819 281474976710656 10000000000819 819000000000000000 (ep401 (BSN.log_sum_c_succ qz16 0 1 rfl) (ep411 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep412 (@congrArg Complex Complex qz121 qz385 Complex.log (BSN.w_shift_mk qz16 Bool.false 81143 1000 1 qz17 rfl)) (@Enclosure.Complex.IsNear.of_parts qz383 Bool.false 16679258490507475 4503599627370496 500000000819 163800000000000000 Bool.false 866940936029603 562949953421312 10000000000819 1638000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz383) (@HMul.hMul Real Real Real qz0 qz96 (Real.log (Enclosure.sfrac Bool.false 26361745796 16000000))) Bool.false 16679258490507475 4503599627370496 500000000819 163800000000000000 (Enclosure.clog_re_eq 5000 162286 4000 26361745796 16000000 rfl rfl rfl) (ep417 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz383) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz381 qz384)) Bool.false 866940936029603 562949953421312 10000000000819 1638000000000000000 (Enclosure.clog_im_eq 5000 162286 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz381 qz384)) (@HSub.hSub Real Real Real qz353 qz97 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz384 qz381))) Bool.false 866940936029603 562949953421312 10000000000819 1638000000000000000 (BSN.arctan_recip 162286 5000 rfl rfl) ep419)))) rfl rfl

noncomputable def ep421 := @ep308 ep309 Bool.false 16678234140807379 2251799813685248 500000000819 81900000000000000 Bool.false 873876234470819 281474976710656 10000000000819 819000000000000000 Bool.true ep310 5740870509627116089 90071992547409920 14113628494806385861553 ep305 Bool.false ep311 2952784476969132447263 27021597764222976000 6300962862107209252799 ep301 (@ep312 90071992547409920 4595316164756548673851 ep307 Bool.false 3036676595478331071263 27021597764222976000 1925558287354756688533 ep309 (BSN.logGammaStirling_unfold 1 qz84) (ep395 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (@ep396 10000000000819 819000000000000000 (BSN.log_sum_c_eq qz16 2) (ep397 (BSN.log_sum_c_succ qz16 1 2 rfl) (ep420 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)))

noncomputable abbrev qz122 := (@HDiv.hDiv Real Real Real qz268 qz278 (2 : Real))

noncomputable def ep422 := @Enclosure.Real.IsNear.mulLit_ff qz122 (Real.log Real.pi) 81143 2000 0 1 75021 65536 1 131072 6087429003 131072000 81143 262144000 (@Enclosure.Real.IsNear.of_eq qz122 (Enclosure.sfrac Bool.false 81143 2000) Bool.false 81143 2000 0 1 (BSN.t_half_eq qz16 Bool.false 81143 1000 qz17) (Enclosure.Real.IsNear.const Bool.false 81143 2000)) EMRow22.d5 rfl

noncomputable def ep423 := @ep303 81143 262144000 ep304 1697809669708001924639 27021597764222976000 19592186262107209252799 ep301 (@ep306 6300962862107209252799 ep301 (ep421 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) ep422 rfl rfl

noncomputable def ep424 := nat_lit 32570933958291469665003798979548013624342703411442556413423256881759331098880

noncomputable def ep425 := nat_lit 65396149619885362971555534090782993659426337675054528579484519587462062336

noncomputable def ep426 := nat_lit 85198947553283558534960764557907339407353723435637559465075078801466166681856

noncomputable def ep427 := BSN.sin_dyadic_bound_f 1686335654 1073741824 3 2 524288 163960 ep424 ep57 ep425 ep426 ep60 ep425 524287 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1686335654) qz281 0 2 ep424 ep57 ep425 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1686335654) qz282 0 2 ep426 ep60 ep425 rfl rfl rfl rfl) rfl rfl

noncomputable def ep428 := @ep300 32768 Bool.false 524287 524288 1 81900 (@ep302 32941843 524288 15 32768 ep423 rfl) (Enclosure.sfrac_false_div 32941843 524288) (BSN.cos_reduce3 qz354 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 118665322266028761153536) qz22) 226375608064910080 72057594037927936 Bool.false 524287 524288 9 1000000000000000 163800 81900 (BSN.sin_reduce_arg_pos_rat_q3 32941843 524288 226375608064910080 72057594037927936 9 118665322266028761153536 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 524287 524288 118665322266028761153536 75557863725914323419136 1686335654 1073741824 163960 163800 (ep427 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep429 := nat_lit 2083824370681964949049739

noncomputable def ep430 := nat_lit 36922288633940837557862400

noncomputable def ep431 := nat_lit 4445326428620943209688821489

noncomputable def ep432 := nat_lit 755983859779938648997232640000

noncomputable abbrev qz123 := qz272

noncomputable abbrev qz124 := qz273

noncomputable abbrev qz493 := (@Nat.cast Complex Complex.instNatCast 17)

noncomputable abbrev qz386 := (@HPow.hPow Complex Complex Complex qz479 qz493 qz480)

noncomputable abbrev qz125 := qz386

noncomputable abbrev qz387 := qz493

noncomputable abbrev qz126 := (@HAdd.hAdd Complex Complex Complex qz271 (@HDiv.hDiv Complex Complex Complex qz358 qz387 (@HSub.hSub Complex Complex Complex qz350 qz270 (1 : Complex))) qz357)

noncomputable abbrev qz127 := (@instHSub Nat instSubNat)

noncomputable abbrev qz388 := qz492

noncomputable abbrev qz128 := qz388

noncomputable abbrev qz129 := qz387

noncomputable def ep433 := @Enclosure.Complex.IsNear.of_eq (zetaApproximant qz5 1 17) (@HAdd.hAdd Complex Complex Complex qz4 (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 17, @HPow.hPow Complex Complex Complex qz123 (@Nat.cast Complex Complex.instNatCast n) qz124) (@HMul.hMul Complex Complex Complex qz74 qz125 (@HAdd.hAdd Complex Complex Complex qz4 qz126 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz82 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz128 qz129 (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz82 2 k) 1))))))) Bool.false ep295 ep296 ep297

noncomputable def ep434 := @Enclosure.Complex.IsNear.addLitP (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 17, @HPow.hPow Complex Complex Complex qz123 (@Nat.cast Complex Complex.instNatCast n) qz124) (@HMul.hMul Complex Complex Complex qz74 qz125 (@HAdd.hAdd Complex Complex Complex qz4 qz126 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz82 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz128 qz129 (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))))) Bool.false 1149508361535 274877906944 2142973281679 375208342978560

noncomputable def ep435 := nat_lit 15662680889177350730267941

noncomputable def ep436 := nat_lit 19679417712686828217560011

noncomputable def ep437 := nat_lit 116305209196913638307266560000

noncomputable def ep438 := nat_lit 9828693864378889287339653

noncomputable def ep439 := nat_lit 58152604598456819153633280000

noncomputable def ep440 := nat_lit 137169606765796759580132952406224797696

noncomputable def ep441 := nat_lit 572797281451956523083963858069487616

noncomputable def ep442 := @ep434 Bool.false 8433164951 274877906944 2142879162199 375208342978560 Bool.true ep435 ep296 ep436 ep437 Bool.false 951060541532573489470139 ep430 ep438 ep439 Bool.false ep440 ep295 ep296 ep297 ep298 Bool.false ep441 ep429 ep430

noncomputable def ep443 := @Enclosure.Complex.IsNear.of_eq (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 17, @HPow.hPow Complex Complex Complex qz123 (@Nat.cast Complex Complex.instNatCast n) qz124) (BSN.headSumC qz5 17) Bool.false 1149508361535 274877906944 2142973281679 375208342978560 Bool.false 8433164951 274877906944 2142879162199

noncomputable def ep444 := @Enclosure.Complex.IsNear.mul qz125 (@HAdd.hAdd Complex Complex Complex qz4 qz126 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz82 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz128 qz129 (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz82 2 k) 1))))) Bool.true ep435 ep296 ep436 ep437 Bool.false

noncomputable abbrev qz130 := (Complex.re qz386)

noncomputable abbrev qz131 := (Complex.im qz386)

noncomputable def ep445 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 qz130 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz126 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz82 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz128 qz129 (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz82 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz131 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz126 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz82 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz128 qz129 (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz82 2 k) 1))))))) 38046506491399260396425 369222886339408375578624 37219441965075143012593

noncomputable def ep446 := nat_lit 302393543911975459598893056

noncomputable def ep447 := nat_lit 8941536176132791794378823

noncomputable def ep448 := nat_lit 369222886339408375578624000

noncomputable def ep449 := nat_lit 9962174348507578823616449

noncomputable def ep450 := nat_lit 215995388508553899713495040000

noncomputable def ep451 := nat_lit 17349060737145458040797338482847159675069296279552

noncomputable def ep452 := @Enclosure.Real.IsNear.mulLit_tf qz130 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz126 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz82 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz128 qz129 (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))))) 28259180365 137438953472 138224375977 562812514467840 1346341472045

noncomputable abbrev qz389 := (@Nat.cast Real Real.instNatCast 17)

noncomputable abbrev qz132 := (@Inv.inv Real Real.instInv (Real.sqrt qz389))

noncomputable abbrev qz390 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) qz483 (Real.log (Enclosure.sfrac Bool.false 17 1)))

noncomputable abbrev qz133 := (Real.cos qz390)

noncomputable abbrev qz134 := (Real.sin qz390)

noncomputable abbrev qz391 := (@Neg.neg Real Real.instNeg qz134)

noncomputable def ep453 := @Enclosure.Complex.IsNear.of_eq qz125 (Complex.mk (@HMul.hMul Real Real Real qz0 qz132 qz133) (@HMul.hMul Real Real Real qz0 qz132 qz391)) Bool.true 28259180365 137438953472 138224375977 562812514467840 Bool.false 35359230289 274877906944 275767348049 1125625028935680 (BSN.cpow_neg_s_mk qz16 81143 1000 17 qz17 rfl)

noncomputable abbrev qz392 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 17) qz18)

noncomputable def ep454 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz389) 2161695 524288 1 524288 63579 63580 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz389) (Real.sqrt qz392) Bool.false 2161695 524288 1 524288 (BSN.sqrt_natCast_div_one 17) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz392) Bool.false 2161695 524288 1 524288 2161695 524288 1 524288 (BSN.sqrt_enclosure 17 1 1080847 1080848 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep455 := BSN.log_dyadic_bound 1 33 2 1 3267 262144 81900 1 1 15892 34 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 1) (BSN.artanhQ 33) 0 1 1 3267 1 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz393 := (Real.log (Enclosure.sfrac Bool.false 17 1))

noncomputable abbrev qz135 := qz393

noncomputable abbrev qz394 := (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 17) qz18))

noncomputable def ep456 := @Enclosure.Real.IsNear.mulLit_ff qz16 qz135 81143 1000 0 1 3189913004350711 1125899906842624 2500000000819 204750000000000000 258839110912029742673 1125899906842624000 202857500066456117 204750000000000000000 qz21 (BSN.isNear_log_sfrac 17 1 3189913004350711 1125899906842624 2500000000819 204750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' qz394 Bool.false 26758929747600409100288 9444732965739290427392 1000000000327600 81900000000000000000 3189913004350711 1125899906842624 2500000000819 204750000000000000 (BSN.log_rat_reduce_isNear 17 1 4 34 32 15892 262144 24973259072661432 36028797018963968 81900 1000000000000000 rfl rfl rfl rfl (ep455 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep457 := nat_lit 129835891142032046409605158276546816

noncomputable def ep458 := BSN.cos_dyadic_bound_f 600272836 1073741824 2 1 524288 163960 ep457 ep112 ep457 ep457 ep113 ep457 444470 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 600272836) qz285 0 1 ep457 ep112 ep457 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 600272836) qz286 0 1 ep457 ep113 ep457 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz136 := qz390

noncomputable abbrev qz395 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 120531353) qz19)

noncomputable def ep459 := @Enclosure.Real.IsNear.cos_image qz136 qz395 Bool.false 120531353 524288 521 524288 Bool.true 444470 524288 1 81900 (@Enclosure.Real.IsNear.recentre' qz136 Bool.false 258839110912029742673 1125899906842624000 202857500066456117 204750000000000000000 120531353 524288 521 524288 (ep456 rfl) rfl) (Enclosure.sfrac_false_div 120531353 524288) (BSN.cos_reduce2 qz395 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 42240445666580785790976) qz22) 226375608064910080 72057594037927936 Bool.false 444470 524288 36 1000000000000000 163800 81900 (BSN.sin_reduce_arg_pos_rat_q2 120531353 524288 226375608064910080 72057594037927936 36 42240445666580785790976 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 444470 524288 42240445666580785790976 75557863725914323419136 600272836 1073741824 163960 163800 (ep458 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep460 := BSN.sin_dyadic_bound_f 600272836 1073741824 2 1 524288 163960 ep457 ep108 ep457 ep457 ep109 ep457 278071 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 600272836) qz281 0 1 ep457 ep108 ep457 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 600272836) qz282 0 1 ep457 ep109 ep457 rfl rfl rfl rfl) rfl rfl

noncomputable def ep461 := @Enclosure.Real.IsNear.sin_image qz136 qz395 Bool.false 120531353 524288 521 524288 Bool.true 278071 524288 1 81900 (@Enclosure.Real.IsNear.recentre' qz136 Bool.false 258839110912029742673 1125899906842624000 202857500066456117 204750000000000000000 120531353 524288 521 524288 (ep456 rfl) rfl) (Enclosure.sfrac_false_div 120531353 524288) (BSN.sin_reduce2 qz395 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 42240445666580785790976) qz22) 226375608064910080 72057594037927936 Bool.false 278071 524288 36 1000000000000000 163800 81900 (BSN.sin_reduce_arg_pos_rat_q2 120531353 524288 226375608064910080 72057594037927936 36 42240445666580785790976 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 278071 524288 42240445666580785790976 75557863725914323419136 600272836 1073741824 163960 163800 (ep460 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz396 := (@Enclosure.Real.IsNear.recentre' qz132 Bool.false 127159 524288 1 524288 127159 524288 1 524288 (ep454 rfl rfl) rfl)

noncomputable def ep462 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz132 qz133) (@HMul.hMul Real Real Real qz0 qz132 qz391) Bool.true 28259180365 137438953472 138224375977 562812514467840 Bool.false 35359230289 274877906944 275767348049 1125625028935680 (@Enclosure.Real.IsNear.mulLit_ft qz132 qz133 127159 524288 1 524288 222235 262144 10798547 10734796800 28259180365 137438953472 138224375977 562812514467840 qz396 (@Enclosure.Real.IsNear.recentre' qz133 Bool.true 444470 524288 43194188 42939187200 222235 262144 10798547 10734796800 (ep459 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz132 qz391 127159 524288 1 524288 278071 524288 10798547 10734796800 35359230289 274877906944 275767348049 1125625028935680 qz396 (@Enclosure.Real.IsNear.neg qz134 Bool.true 278071 524288 10798547 10734796800 (@Enclosure.Real.IsNear.recentre' qz134 Bool.true 278071 524288 43194188 42939187200 278071 524288 10798547 10734796800 (ep461 rfl rfl) rfl)) rfl)

noncomputable def ep463 := @ep452 2686450071192 0 1 38046506491399260396425 369222886339408375578624 37219441965075143012593 ep446 (@Enclosure.Complex.IsNear.re_isNear qz125 Bool.true 28259180365 137438953472 138224375977 562812514467840 Bool.false 35359230289 274877906944 275767348049 1125625028935680 (ep453 ep462))

noncomputable def ep464 := @Enclosure.Complex.IsNear.re_isNear (@HAdd.hAdd Complex Complex Complex qz4 qz126 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz82 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz128 qz129 (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz82 2 k) 1))))) Bool.false 1346341472045 2686450071192 0 1 Bool.false

noncomputable def ep465 := @Enclosure.Complex.IsNear.addLitP qz126 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz82 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz128 qz129 (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) Bool.false 6567436449 13168872898 0 1 Bool.true 1379431000

noncomputable def ep466 := @ep465 6584436449 0 1 Bool.false 1 408 0 1 Bool.false 81143 204000 0 1 Bool.false 2692682944090 1346341472045 2686450071192 0 1 Bool.false 252877002781207 252877002781207 1343225035596000 0 1

noncomputable abbrev qz137 := (@HDiv.hDiv Complex Complex Complex qz358 qz387 (@HSub.hSub Complex Complex Complex qz350 qz270 (1 : Complex)))

noncomputable def ep467 := @Enclosure.Complex.IsNear.addLitP qz137 qz101 Bool.true 34000000 26337745796 0 1 Bool.true 5517724000 26337745796 0 1

noncomputable def ep468 := @Enclosure.Complex.IsNear.of_eq qz137 (Complex.mk (Enclosure.sfrac Bool.true 34000000 26337745796) (Enclosure.sfrac Bool.true 5517724000 26337745796)) Bool.true 34000000 26337745796 0 1 Bool.true 5517724000 26337745796 0 1

noncomputable def ep469 := @ep467 Bool.false 1 2 0 1 Bool.false 0 1 0 1 Bool.false 26269745796 6567436449 13168872898 0 1 Bool.true 5517724000 1379431000 6584436449 0 1 (ep468 (BSN.N_div_s_sub_one_mk qz16 81143 1000 17 qz17 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 34000000 26337745796) (Enclosure.sfrac Bool.true 5517724000 26337745796) Bool.true 34000000 26337745796 0 1 Bool.true 5517724000 26337745796 0 1 (Enclosure.Real.IsNear.const Bool.true 34000000 26337745796) (Enclosure.Real.IsNear.const Bool.true 5517724000 26337745796))) qz102 rfl

noncomputable abbrev qz138 := (@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 1)))

noncomputable abbrev qz397 := (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz492 qz493 1))

noncomputable abbrev qz139 := qz397

noncomputable def ep470 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz82 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz128 qz129 (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) (@HAdd.hAdd Complex Complex Complex qz4 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz82 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz128 qz129 (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz103)) ↑qz138) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz139)) Bool.false 1 408 0 1

noncomputable def ep471 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz82 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz128 qz129 (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz103)) ↑qz138) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz139) Bool.false 0 1 0 1 Bool.false

noncomputable def ep472 := @ep471 0 1 0 1 Bool.false 1 408 0 1 Bool.false 81143 204000 0 1 Bool.false 1 1 408 0 1 Bool.false 81143 81143 204000 0

noncomputable def ep473 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz82 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz128 qz129 (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) (Complex.mk qz13 qz13) Bool.false 0 1 0 1 Bool.false

noncomputable def ep474 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz103)) ↑qz138) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz139 Bool.false 1 408 0 1 Bool.false 81143 204000 0 1

noncomputable abbrev qz140 := (Complex.re qz397)

noncomputable abbrev qz141 := (Complex.im qz397)

noncomputable def ep475 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz103)) ↑qz138) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) qz140) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz103)) ↑qz138) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) qz141) 1 408 0 1 0 1 0

noncomputable def ep476 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz103)) ↑qz138) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) qz140 1 24 0 1 1 17 0 1 1

noncomputable def ep477 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz103)) ↑qz138)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz103)) ↑qz138)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) 1 24 0 1 0 1 0 1 1

noncomputable def ep478 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz103)) ↑qz138)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 1 2 0 1 1 24 0

noncomputable def ep479 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz103)) ↑qz138) (Complex.mk (Enclosure.sfrac Bool.false 1 12) qz13) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (BSN.bern_coeff_mk 1 1 6 2 Bool.false BSN.bern_real_1 EMRow22.d8 rfl) qz376

noncomputable def ep480 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) qz5 Bool.false 1 2 0 1 Bool.false 81143 1000 0 1 (BSN.ascPochhammer_one_eval qz5)

noncomputable def ep481 := ep480 (@Enclosure.Complex.IsNear.of_eq qz5 (Complex.mk qz96 qz16) Bool.false 1 2 0 1 Bool.false 81143 1000 0 1 (BSN.s_crit_mk qz16 Bool.false 81143 1000 qz17) (@Enclosure.Complex.IsNear.mk qz96 qz16 Bool.false 1 2 0 1 Bool.false 81143 1000 0 1 qz368 qz21))

noncomputable def ep482 := @ep478 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz103)) ↑qz138) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep479) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 81143 1000 0 1 ep481)

noncomputable def ep483 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz103)) ↑qz138)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 81143 1000 0 1 0 1 0

noncomputable def ep484 := @ep483 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz103)) ↑qz138) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep479) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 81143 1000 0 1 ep481)

noncomputable def ep485 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz103)) ↑qz138)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz103)) ↑qz138)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) 81143 12000 0 1 0 1 0 1 81143

noncomputable def ep486 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz103)) ↑qz138)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 81143 1000 0 1 81143 12000 0

noncomputable def ep487 := @ep486 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz103)) ↑qz138) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep479) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 81143 1000 0 1 ep481)

noncomputable def ep488 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz103)) ↑qz138)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 1 2 0 1 0 1 0

noncomputable def ep489 := @ep488 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz103)) ↑qz138) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep479) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 81143 1000 0 1 ep481)

noncomputable def ep490 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz103)) ↑qz138) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 24 0 1 Bool.false 81143 12000 0 1 (@ep477 1 24 0 1 (ep482 rfl) (ep484 rfl) rfl rfl) (@ep485 81143 12000 0 1 (ep487 rfl) (ep489 rfl) rfl rfl)

noncomputable def ep491 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz103)) ↑qz138) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 81143 12000 0 1 ep490

noncomputable abbrev qz142 := (@Enclosure.Complex.IsNear.re_isNear qz397 Bool.false 1 17 0 1 Bool.false 0 1 0 1 (@Enclosure.Complex.IsNear.of_eq qz397 (Complex.mk (Enclosure.sfrac Bool.false 1 17) qz276) Bool.false 1 17 0 1 Bool.false 0 1 0 1 (BSN.natCast_pow_inv_mk 17 1 17 EMRow22.d9 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 17) qz276 Bool.false 1 17 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 17) qz288)))

noncomputable def ep492 := @ep476 408 0 1 ep491 qz142

noncomputable def ep493 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz103)) ↑qz138) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) qz141 81143 12000 0 1 0 1 0 1 0

noncomputable def ep494 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz103)) ↑qz138) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 81143 12000 0 1 ep490

noncomputable abbrev qz143 := (@Enclosure.Complex.IsNear.im_isNear qz397 Bool.false 1 17 0 1 Bool.false 0 1 0 1 (@Enclosure.Complex.IsNear.of_eq qz397 (Complex.mk (Enclosure.sfrac Bool.false 1 17) qz276) Bool.false 1 17 0 1 Bool.false 0 1 0 1 (BSN.natCast_pow_inv_mk 17 1 17 EMRow22.d9 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 17) qz276 Bool.false 1 17 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 17) qz288)))

noncomputable def ep495 := @ep493 1 0 1 ep494 qz143

noncomputable def ep496 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz103)) ↑qz138) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) qz141) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz103)) ↑qz138) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) qz140) 0 1 0 1 81143 204000 0

noncomputable def ep497 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz103)) ↑qz138) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) qz141 1 24 0 1 0 1 0 1 0

noncomputable def ep498 := @ep497 1 0 1 ep491 qz143

noncomputable def ep499 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz103)) ↑qz138) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) qz140 81143 12000 0 1 1 17 0 1 81143

noncomputable def ep500 := @ep499 204000 0 1 ep494 qz142

noncomputable def ep501 := @ep472 1 (@ep473 0 1 0 1 (BSN.bern_sum_base qz5 17) qz117) (ep474 (@ep475 1 1 1 408 0 1 (ep492 rfl) (ep495 rfl) rfl rfl) (@ep496 1 81143 81143 204000 0 1 (ep498 rfl) (ep500 rfl) rfl rfl)) rfl rfl rfl rfl rfl

noncomputable def ep502 := ep466 (ep469 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep470 Bool.false 81143 204000 0 1 (BSN.bern_sum_succ qz5 17 0 1 1 rfl rfl) (ep501 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl rfl

noncomputable def ep503 := @Enclosure.Real.IsNear.mulLit_ff qz131 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz126 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz82 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz128 qz129 (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))))) 35359230289 274877906944 275767348049 1125625028935680 252877002781207

noncomputable def ep504 := @ep503 1343225035596000 0 1 ep447 ep448 ep449 ep450 (@Enclosure.Complex.IsNear.im_isNear qz125 Bool.true 28259180365 137438953472 138224375977 562812514467840 Bool.false 35359230289 274877906944 275767348049 1125625028935680 (ep453 ep462))

noncomputable def ep505 := @Enclosure.Complex.IsNear.im_isNear (@HAdd.hAdd Complex Complex Complex qz4 qz126 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz82 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz128 qz129 (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz82 2 k) 1))))) Bool.false 1346341472045 2686450071192 0 1 Bool.false

noncomputable def ep506 := nat_lit 1429219366350947049080111

noncomputable def ep507 := nat_lit 4993395129766633005409177

noncomputable def ep508 := @Enclosure.Real.IsNear.addLit_tf_p (@HMul.hMul Real Real Real qz0 qz130 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz126 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz82 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz128 qz129 (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz82 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz131 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz126 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz82 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz128 qz129 (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz82 2 k) 1))))))) ep506 ep430 ep507

noncomputable def ep509 := nat_lit 107997694254276949856747520000

noncomputable def ep510 := nat_lit 604787087823950919197786112

noncomputable def ep511 := nat_lit 702306636456355120535505129628074583570589417472

noncomputable def ep512 := @Enclosure.Real.IsNear.mulLit_tf qz130 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz126 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz82 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz128 qz129 (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))))) 28259180365 137438953472 138224375977 562812514467840 252877002781207

noncomputable def ep513 := @ep512 1343225035596000 0 1 ep506 ep430 ep507 ep509 (@Enclosure.Complex.IsNear.re_isNear qz125 Bool.true 28259180365 137438953472 138224375977 562812514467840 Bool.false 35359230289 274877906944 275767348049 1125625028935680 (ep453 ep462))

noncomputable def ep514 := @Enclosure.Real.IsNear.mulLit_ff qz131 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz126 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz82 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz128 qz129 (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))))) 35359230289 274877906944 275767348049 1125625028935680 1346341472045

noncomputable def ep515 := @ep514 2686450071192 0 1 47605598157670410771005 738445772678816751157248 74255403462847303758041 ep510 (@Enclosure.Complex.IsNear.im_isNear qz125 Bool.true 28259180365 137438953472 138224375977 562812514467840 Bool.false 35359230289 274877906944 275767348049 1125625028935680 (ep453 ep462))

noncomputable abbrev qz398 := (ep502 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable def ep516 := @ep444 951060541532573489470139 ep430 ep438 ep439 (@ep445 ep446 ep447 ep448 ep449 ep450 ep451 ep435 ep296 ep436 ep437 (ep463 (@ep464 252877002781207 1343225035596000 0 1 qz398) rfl) (ep504 (@ep505 252877002781207 1343225035596000 0 1 qz398) rfl) rfl rfl) (@ep508 ep509 47605598157670410771005 738445772678816751157248 74255403462847303758041 ep510 ep511 951060541532573489470139 ep430 ep438 ep439 (ep513 (@ep505 252877002781207 1343225035596000 0 1 qz398) rfl) (ep515 (@ep464 252877002781207 1343225035596000 0 1 qz398) rfl) rfl rfl)

noncomputable def ep517 := @ep442 ep431 ep432 (@ep443 375208342978560 (BSN.head_sum_c_eq qz5 17) EMRow22.d7) ep516 rfl rfl rfl rfl rfl rfl rfl rfl rfl

noncomputable def ep518 := @Enclosure.Complex.IsNear.re_isNear (zetaApproximant qz5 1 17) Bool.false ep295 ep296 ep297 ep298 Bool.false ep429 ep430 ep431 ep432 (@ep433 ep298 Bool.false ep429 ep430 ep431 ep432 (BSN.zetaApproximant_eq_folded' qz5 1 17 rfl) (ep517 rfl rfl rfl rfl rfl rfl rfl rfl rfl))

noncomputable def ep519 := @Enclosure.Real.IsNear.mulLit_tf (Real.sin (@HSub.hSub Real Real Real qz353 (Complex.im (@HSub.hSub Complex Complex Complex qz75 qz76 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz77 (@Nat.cast Complex Complex.instNatCast j))))) qz78)) (Complex.im (zetaApproximant qz5 1 17)) 143 524288 315317

noncomputable def ep520 := @Enclosure.Real.IsNear.recentre' (Real.sin (@HSub.hSub Real Real Real qz353 (Complex.im (@HSub.hSub Complex Complex Complex qz75 qz76 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz77 (@Nat.cast Complex Complex.instNatCast j))))) qz78)) Bool.true 143 524288 1261268

noncomputable def ep521 := @Enclosure.Real.IsNear.sin_image (@HSub.hSub Real Real Real qz353 (Complex.im (@HSub.hSub Complex Complex Complex qz75 qz76 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz77 (@Nat.cast Complex Complex.instNatCast j))))) qz78) qz354 Bool.false 32941843 524288 15

noncomputable def ep522 := nat_lit 18124028265548543308545024114900355566261246934212555575714913609682944860416

noncomputable def ep523 := nat_lit 54241292497405859199691961276519500711464888127287557669985771789873910456576

noncomputable def ep524 := BSN.cos_dyadic_bound_f 1686335654 1073741824 3 2 524288 163960 ep522 ep64 ep425 ep523 ep66 ep425 143 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1686335654) qz285 0 2 ep522 ep64 ep425 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1686335654) qz286 0 2 ep523 ep66 ep425 rfl rfl rfl rfl) rfl rfl

noncomputable def ep525 := @ep521 32768 Bool.true 143 524288 1 81900 (@ep302 32941843 524288 15 32768 ep423 rfl) (Enclosure.sfrac_false_div 32941843 524288) (BSN.sin_reduce3 qz354 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 118665322266028761153536) qz22) 226375608064910080 72057594037927936 Bool.false 143 524288 9 1000000000000000 163800 81900 (BSN.sin_reduce_arg_pos_rat_q3 32941843 524288 226375608064910080 72057594037927936 9 118665322266028761153536 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 143 524288 118665322266028761153536 75557863725914323419136 1686335654 1073741824 163960 163800 (ep524 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep526 := @Enclosure.Complex.IsNear.im_isNear (zetaApproximant qz5 1 17) Bool.false ep295 ep296 ep297 ep298 Bool.false ep429 ep430 ep431 ep432 (@ep433 ep298 Bool.false ep429 ep430 ep431 ep432 (BSN.zetaApproximant_eq_folded' qz5 1 17 rfl) (ep517 rfl rfl rfl rfl rfl rfl rfl rfl rfl))

theorem EMRow22.d10 : Enclosure.Real.IsNear (hardyZApproximantEM 1 17 qz16) Bool.false ep279 ep280 ep281 ep282 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantEM 1 17 qz16) ep283 Bool.false ep279 ep280 ep281 ep282 (@Eq.refl Real ep283) (@ep284 Bool.false ep279 ep280 ep281 ep282 (BSN.re_exp_mul (@HSub.hSub Real Real Real qz353 (Complex.im (@HSub.hSub Complex Complex Complex qz75 qz76 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz77 (@Nat.cast Complex Complex.instNatCast j))))) qz78) (zetaApproximant qz5 1 17)) (@ep286 ep287 ep288 ep282 ep289 ep290 ep291 ep292 ep293 ep279 ep280 ep281 ep282 (@ep294 670924800 ep295 ep296 ep297 ep298 ep285 ep287 ep288 ep282 (@ep299 2683699200 524287 524288 315317 670924800 (ep428 rfl rfl) rfl) ep518 rfl) (@ep519 670924800 ep429 ep430 ep431 ep432 ep289 ep290 ep291 ep292 (@ep520 2683699200 143 524288 315317 670924800 (ep525 rfl rfl) rfl) ep526 rfl) rfl rfl))

noncomputable abbrev qz509 := (@HAdd.hAdd Complex Complex Complex (@instHAdd Complex Complex.instAdd) (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (2 : Complex)) (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul) Complex.I ↑(Enclosure.sfrac Bool.false 83585 1000)))

noncomputable abbrev qz494 := qz509

noncomputable abbrev qz399 := qz494

noncomputable abbrev qz144 := (BSN.headSumC qz399 9)

noncomputable abbrev qz145 := qz399

noncomputable abbrev qz495 := (@Neg.neg Complex Complex.instNeg qz509)

noncomputable abbrev qz400 := qz495

noncomputable abbrev qz146 := (@HPow.hPow Complex Complex Complex qz272 (@Nat.cast Complex Complex.instNatCast 8) qz400)

noncomputable def ep527 := @Enclosure.Complex.IsNear.of_eq qz144 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz145 8) qz146) Bool.false 22088809367 137438953472 468929908867 134002979635200 Bool.false 46135290831 274877906944 938427980459 268005959270400

noncomputable def ep528 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz145 8) qz146 Bool.false 23707756073 68719476736 734619552769 234505214361600 Bool.true 9200928813 68719476736 1469936204213 469010428723200 Bool.true

noncomputable abbrev qz147 := (@HPow.hPow Complex Complex Complex qz272 (@Nat.cast Complex Complex.instNatCast 7) qz400)

noncomputable def ep529 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz145 8) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz145 7) qz147) Bool.false 23707756073 68719476736 734619552769 234505214361600 Bool.true 9200928813 68719476736 1469936204213 469010428723200

noncomputable def ep530 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz145 7) qz147 Bool.false 1020472679 17179869184 296577184349 108233175859200 Bool.true 13107106589 34359738368 148379409037 54116587929600 Bool.false

noncomputable abbrev qz148 := (@HPow.hPow Complex Complex Complex qz272 (@Nat.cast Complex Complex.instNatCast 6) qz400)

noncomputable def ep531 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz145 7) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz145 6) qz148) Bool.false 1020472679 17179869184 296577184349 108233175859200 Bool.true 13107106589 34359738368 148379409037 54116587929600

noncomputable def ep532 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz145 6) qz148 Bool.true 41221745183 274877906944 13039450376593 5628125144678400 Bool.true 100597261189 137438953472 6522592415159 2814062572339200 Bool.false

noncomputable abbrev qz149 := (@HPow.hPow Complex Complex Complex qz272 (@Nat.cast Complex Complex.instNatCast 5) qz400)

noncomputable def ep533 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz145 6) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz145 5) qz149) Bool.true 41221745183 274877906944 13039450376593 5628125144678400 Bool.true 100597261189 137438953472 6522592415159 2814062572339200

noncomputable def ep534 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz145 5) qz149 Bool.false 15670856659 68719476736 868869162169 469010428723200 Bool.true 135503577117 274877906944 3478500485401 1876041714892800 Bool.true

noncomputable abbrev qz150 := (@HPow.hPow Complex Complex Complex qz272 (@Nat.cast Complex Complex.instNatCast 4) qz400)

noncomputable def ep535 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz145 5) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz145 4) qz150) Bool.false 15670856659 68719476736 868869162169 469010428723200 Bool.true 135503577117 274877906944 3478500485401 1876041714892800

noncomputable def ep536 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz145 4) qz150 Bool.false 47757684145 68719476736 375255997073 281406257233920 Bool.true 43174178379 137438953472 188009421169 140703128616960 Bool.true

noncomputable abbrev qz151 := (@HPow.hPow Complex Complex Complex qz272 qz274 qz400)

noncomputable def ep537 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz145 4) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz145 3) qz151) Bool.false 47757684145 68719476736 375255997073 281406257233920 Bool.true 43174178379 137438953472 188009421169 140703128616960

noncomputable def ep538 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz145 3) qz151 Bool.false 19389083677 17179869184 206055509963 281406257233920 Bool.true 23890870845 34359738368 413831734831 562812514467840 Bool.true

noncomputable abbrev qz152 := (@HPow.hPow Complex Complex Complex qz272 qz275 qz400)

noncomputable def ep539 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz145 3) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz145 2) qz152) Bool.false 19389083677 17179869184 206055509963 281406257233920 Bool.true 23890870845 34359738368 413831734831 562812514467840

noncomputable def ep540 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz145 2) qz152 Bool.false 1 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable def ep541 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz145 2) (Complex.mk (Enclosure.sfrac Bool.false 1 1) qz13) Bool.false 1 1 0 1 Bool.false 0 1 0 1 (BSN.head_sum_c_two qz145)

noncomputable abbrev qz510 := (Enclosure.sfrac Bool.false 83585 1000)

noncomputable abbrev qz496 := qz510

noncomputable abbrev qz401 := qz496

noncomputable abbrev qz153 := (@HMul.hMul Real Real Real qz265 qz401 (Real.log qz279))

noncomputable abbrev qz154 := qz401

noncomputable abbrev qz402 := (@Eq.refl Real qz496)

noncomputable abbrev qz155 := qz402

noncomputable def ep542 := @Enclosure.Complex.IsNear.of_eq qz152 (Complex.mk (@HMul.hMul Real Real Real qz0 qz14 (Real.cos qz153)) (@HMul.hMul Real Real Real qz0 qz14 (@Neg.neg Real Real.instNeg (Real.sin qz153)))) Bool.false 2209214493 17179869184 206055509963 281406257233920 Bool.true 23890870845 34359738368 413831734831 562812514467840 (BSN.cpow_neg_s_mk qz154 83585 1000 2 qz155 rfl)

noncomputable def ep543 := nat_lit 11038814460521706534344499311296401725225370637240881750011093456179176690625

noncomputable def ep544 := nat_lit 24328255258029832382315523983300659941732654989195995817924337468187890625

noncomputable def ep545 := nat_lit 33067786871049059938268866885922603855792646601744253258397431693601154290625

noncomputable def ep546 := BSN.cos_dyadic_bound_f 1490266265 1073741824 3 2 524288 163960 ep543 ep64 ep544 ep545 ep66 ep544 95346 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1490266265) qz285 0 2 ep543 ep64 ep544 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1490266265) qz286 0 2 ep545 ep66 ep544 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz156 := (Enclosure.Real.IsNear.const Bool.false 83585 1000)

noncomputable abbrev qz403 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 30375457) qz19)

noncomputable def ep547 := @Enclosure.Real.IsNear.cos_image qz153 qz403 Bool.false 30375457 524288 67 65536 Bool.false 95346 524288 1 81900 (@Enclosure.Real.IsNear.recentre' qz153 Bool.false 379693221 6553600 16717 16380000 30375457 524288 67 65536 (@Enclosure.Real.IsNear.mulLit_ff qz154 qz20 83585 1000 0 1 181704 262144 1 81900 379693221 6553600 16717 16380000 qz156 qz284 rfl) rfl) (Enclosure.sfrac_false_div 30375457 524288) (BSN.cos_reduce0 qz403 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 104868165604192041304064) qz22) 226375608064910080 72057594037927936 Bool.false 95346 524288 9 1000000000000000 163800 81900 (BSN.sin_reduce_arg_pos_rat_q0 30375457 524288 226375608064910080 72057594037927936 9 104868165604192041304064 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 95346 524288 104868165604192041304064 75557863725914323419136 1490266265 1073741824 163960 163800 (ep546 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep548 := nat_lit 19850403424732647895914246341146882577452281023042230353365628751147967730625

noncomputable def ep549 := nat_lit 51949763222929648570204039092745062824850311714175714551300007325677135090625

noncomputable def ep550 := BSN.sin_dyadic_bound_f 1490266265 1073741824 3 2 524288 163960 ep548 ep57 ep544 ep549 ep60 ep544 515545 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1490266265) qz281 0 2 ep548 ep57 ep544 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1490266265) qz282 0 2 ep549 ep60 ep544 rfl rfl rfl rfl) rfl rfl

noncomputable def ep551 := @Enclosure.Real.IsNear.sin_image qz153 qz403 Bool.false 30375457 524288 67 65536 Bool.false 515545 524288 1 81900 (@Enclosure.Real.IsNear.recentre' qz153 Bool.false 379693221 6553600 16717 16380000 30375457 524288 67 65536 (@Enclosure.Real.IsNear.mulLit_ff qz154 qz20 83585 1000 0 1 181704 262144 1 81900 379693221 6553600 16717 16380000 qz156 qz284 rfl) rfl) (Enclosure.sfrac_false_div 30375457 524288) (BSN.sin_reduce0 qz403 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 104868165604192041304064) qz22) 226375608064910080 72057594037927936 Bool.false 515545 524288 9 1000000000000000 163800 81900 (BSN.sin_reduce_arg_pos_rat_q0 30375457 524288 226375608064910080 72057594037927936 9 104868165604192041304064 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 515545 524288 104868165604192041304064 75557863725914323419136 1490266265 1073741824 163960 163800 (ep550 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep552 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz14 (Real.cos qz153)) (@HMul.hMul Real Real Real qz0 qz14 (@Neg.neg Real Real.instNeg (Real.sin qz153))) Bool.false 2209214493 17179869184 206055509963 281406257233920 Bool.true 23890870845 34359738368 413831734831 562812514467840 (@Enclosure.Real.IsNear.mulLit_ff qz14 (Real.cos qz153) 46341 65536 1 262144 47673 262144 1388209 1341849600 2209214493 17179869184 206055509963 281406257233920 qz287 (@Enclosure.Real.IsNear.recentre' (Real.cos qz153) Bool.false 95346 524288 5552836 5367398400 47673 262144 1388209 1341849600 (ep547 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz14 (@Neg.neg Real Real.instNeg (Real.sin qz153)) 46341 65536 1 262144 515545 524288 1388209 1341849600 23890870845 34359738368 413831734831 562812514467840 qz287 (@Enclosure.Real.IsNear.neg (Real.sin qz153) Bool.false 515545 524288 1388209 1341849600 (@Enclosure.Real.IsNear.recentre' (Real.sin qz153) Bool.false 515545 524288 5552836 5367398400 515545 524288 1388209 1341849600 (ep551 rfl rfl) rfl)) rfl)

noncomputable def ep553 := @ep540 2209214493 17179869184 206055509963 281406257233920 Bool.true 23890870845 34359738368 413831734831 562812514467840 Bool.false 19389083677 19389083677 17179869184 206055509963 281406257233920 Bool.true 23890870845 23890870845 34359738368 413831734831 562812514467840 (ep541 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 1) qz13 Bool.false 1 1 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 1) qz23)) (ep542 ep552) rfl rfl

noncomputable abbrev qz157 := (@HMul.hMul Real Real Real qz265 qz401 (Real.log (Enclosure.sfrac Bool.false 3 1)))

noncomputable def ep554 := @Enclosure.Complex.IsNear.of_eq qz151 (Complex.mk (@HMul.hMul Real Real Real qz0 qz24 (Real.cos qz157)) (@HMul.hMul Real Real Real qz0 qz24 (@Neg.neg Real Real.instNeg (Real.sin qz157)))) Bool.true 29798650563 68719476736 5640016237 9380208574464 Bool.false 52389305001 137438953472 22547063323 37520834297856 (BSN.cpow_neg_s_mk qz154 83585 1000 3 qz155 rfl)

noncomputable def ep555 := nat_lit 802809309490259530242055393997710188250548400114667770149570729814960800000

noncomputable def ep556 := nat_lit 129201476892592433071651407279409590127567812510342434283443216100000000

noncomputable def ep557 := nat_lit 2408169525516993405860022879178571745571390064718982625580145303012682400000

noncomputable def ep558 := BSN.cos_dyadic_bound_f 774298530 1073741824 3 2 524288 163960 ep555 ep64 ep556 ep557 ep66 ep556 393774 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 774298530) qz285 0 2 ep555 ep64 ep556 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 774298530) qz286 0 2 ep557 ep66 ep556 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz404 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 12035989) (@Nat.cast Real Real.instNatCast 131072))

noncomputable def ep559 := @Enclosure.Real.IsNear.cos_image qz157 qz404 Bool.false 12035989 131072 537 524288 Bool.true 393774 524288 1 81900 (@Enclosure.Real.IsNear.recentre' qz157 Bool.false 2407197849 26214400 16717 16380000 12035989 131072 537 524288 (@Enclosure.Real.IsNear.mulLit_ff qz154 qz27 83585 1000 0 1 287994 262144 1 81900 2407197849 26214400 16717 16380000 qz156 qz291 rfl) rfl) (Enclosure.sfrac_false_div 12035989 131072) (BSN.cos_reduce2 qz404 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 13621603797466588643328) qz314) 226375608064910080 72057594037927936 Bool.false 393774 524288 14 1000000000000000 163800 81900 (BSN.sin_reduce_arg_pos_rat_q2 12035989 131072 226375608064910080 72057594037927936 14 13621603797466588643328 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 393774 524288 13621603797466588643328 18889465931478580854784 774298530 1073741824 163960 163800 (ep558 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep560 := nat_lit 359446069518909099270723633888810000

noncomputable def ep561 := BSN.sin_dyadic_bound_f 774298530 1073741824 2 1 524288 163960 ep560 ep108 ep560 ep560 ep109 ep560 346149 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 774298530) qz281 0 1 ep560 ep108 ep560 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 774298530) qz282 0 1 ep560 ep109 ep560 rfl rfl rfl rfl) rfl rfl

noncomputable def ep562 := @Enclosure.Real.IsNear.sin_image qz157 qz404 Bool.false 12035989 131072 537 524288 Bool.true 346149 524288 1 81900 (@Enclosure.Real.IsNear.recentre' qz157 Bool.false 2407197849 26214400 16717 16380000 12035989 131072 537 524288 (@Enclosure.Real.IsNear.mulLit_ff qz154 qz27 83585 1000 0 1 287994 262144 1 81900 2407197849 26214400 16717 16380000 qz156 qz291 rfl) rfl) (Enclosure.sfrac_false_div 12035989 131072) (BSN.sin_reduce2 qz404 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 13621603797466588643328) qz314) 226375608064910080 72057594037927936 Bool.false 346149 524288 14 1000000000000000 163800 81900 (BSN.sin_reduce_arg_pos_rat_q2 12035989 131072 226375608064910080 72057594037927936 14 13621603797466588643328 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 346149 524288 13621603797466588643328 18889465931478580854784 774298530 1073741824 163960 163800 (ep561 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep563 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz24 (Real.cos qz157)) (@HMul.hMul Real Real Real qz0 qz24 (@Neg.neg Real Real.instNeg (Real.sin qz157))) Bool.true 29798650563 68719476736 5640016237 9380208574464 Bool.false 52389305001 137438953472 22547063323 37520834297856 (@Enclosure.Real.IsNear.mulLit_ft qz24 (Real.cos qz157) 151349 262144 1 262144 196887 262144 11126147 10734796800 29798650563 68719476736 5640016237 9380208574464 qz293 (@Enclosure.Real.IsNear.recentre' (Real.cos qz157) Bool.true 393774 524288 44504588 42939187200 196887 262144 11126147 10734796800 (ep559 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz24 (@Neg.neg Real Real.instNeg (Real.sin qz157)) 151349 262144 1 262144 346149 524288 11126147 10734796800 52389305001 137438953472 22547063323 37520834297856 qz293 (@Enclosure.Real.IsNear.neg (Real.sin qz157) Bool.true 346149 524288 11126147 10734796800 (@Enclosure.Real.IsNear.recentre' (Real.sin qz157) Bool.true 346149 524288 44504588 42939187200 346149 524288 11126147 10734796800 (ep562 rfl rfl) rfl)) rfl)

noncomputable def ep564 := @ep538 29798650563 68719476736 5640016237 9380208574464 Bool.false 52389305001 137438953472 22547063323 37520834297856 Bool.false 820470766141890887680 47757684145 68719476736 375255997073 281406257233920 Bool.true 1483453473355802345472 43174178379 137438953472 188009421169 140703128616960 (ep539 (BSN.head_sum_c_succ qz145 2 3 rfl rfl) (ep553 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep554 ep563) rfl rfl

noncomputable abbrev qz158 := (@HMul.hMul Real Real Real qz265 qz401 (Real.log (Enclosure.sfrac Bool.false 4 1)))

noncomputable def ep565 := @Enclosure.Complex.IsNear.of_eq qz150 (Complex.mk (@HMul.hMul Real Real Real qz0 qz28 (Real.cos qz158)) (@HMul.hMul Real Real Real qz0 qz28 (@Neg.neg Real Real.instNeg (Real.sin qz158)))) Bool.true 16043413743 34359738368 365163750571 703515643084800 Bool.true 49155220359 274877906944 2915124609443 5628125144678400 (BSN.cpow_neg_s_mk qz154 83585 1000 4 qz155 rfl)

noncomputable def ep566 := nat_lit 11274398597645121544021215113453271411019998480840835312121833580922866991360

noncomputable def ep567 := nat_lit 7856312843120408665572484748252816276219021558332570314017208941387940096

noncomputable def ep568 := nat_lit 29515467058753123382216065083737587231081355700631554036953536278416690217216

noncomputable def ep569 := BSN.sin_dyadic_bound_f 1293904866 1073741824 3 2 524288 163960 ep566 ep57 ep567 ep568 ep60 ep567 489608 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1293904866) qz281 0 2 ep566 ep57 ep567 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1293904866) qz282 0 2 ep568 ep60 ep567 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz405 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 60750915) qz19)

noncomputable def ep570 := @Enclosure.Real.IsNear.cos_image qz158 qz405 Bool.false 60750915 524288 67 65536 Bool.true 489608 524288 1 81900 (@Enclosure.Real.IsNear.recentre' qz158 Bool.false 379693221 3276800 16717 16380000 60750915 524288 67 65536 (@Enclosure.Real.IsNear.mulLit_ff qz154 qz30 83585 1000 0 1 363408 262144 1 81900 379693221 3276800 16717 16380000 qz156 qz296 rfl) rfl) (Enclosure.sfrac_false_div 60750915 524288) (BSN.cos_reduce1 qz405 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 91050460522436582440960) qz22) 226375608064910080 72057594037927936 Bool.false 489608 524288 18 1000000000000000 163800 81900 (BSN.sin_reduce_arg_pos_rat_q1 60750915 524288 226375608064910080 72057594037927936 18 91050460522436582440960 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 489608 524288 91050460522436582440960 75557863725914323419136 1293904866 1073741824 163960 163800 (ep569 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep571 := nat_lit 6267046471066454372752040611806596480022763165604167426873915193375542968576

noncomputable def ep572 := nat_lit 18785426787513122300924976865923283807515851453695837139993711162243853025536

noncomputable def ep573 := BSN.cos_dyadic_bound_f 1293904866 1073741824 3 2 524288 163960 ep571 ep64 ep567 ep572 ep66 ep567 187513 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1293904866) qz285 0 2 ep571 ep64 ep567 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1293904866) qz286 0 2 ep572 ep66 ep567 rfl rfl rfl rfl) rfl rfl

noncomputable def ep574 := @Enclosure.Real.IsNear.sin_image qz158 qz405 Bool.false 60750915 524288 67 65536 Bool.false 187513 524288 1 81900 (@Enclosure.Real.IsNear.recentre' qz158 Bool.false 379693221 3276800 16717 16380000 60750915 524288 67 65536 (@Enclosure.Real.IsNear.mulLit_ff qz154 qz30 83585 1000 0 1 363408 262144 1 81900 379693221 3276800 16717 16380000 qz156 qz296 rfl) rfl) (Enclosure.sfrac_false_div 60750915 524288) (BSN.sin_reduce1 qz405 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 91050460522436582440960) qz22) 226375608064910080 72057594037927936 Bool.false 187513 524288 18 1000000000000000 163800 81900 (BSN.sin_reduce_arg_pos_rat_q1 60750915 524288 226375608064910080 72057594037927936 18 91050460522436582440960 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 187513 524288 91050460522436582440960 75557863725914323419136 1293904866 1073741824 163960 163800 (ep573 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep575 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz28 (Real.cos qz158)) (@HMul.hMul Real Real Real qz0 qz28 (@Neg.neg Real Real.instNeg (Real.sin qz158))) Bool.true 16043413743 34359738368 365163750571 703515643084800 Bool.true 49155220359 274877906944 2915124609443 5628125144678400 (@Enclosure.Real.IsNear.mulLit_ft qz28 (Real.cos qz158) 262143 524288 1 524288 61201 65536 1388209 1341849600 16043413743 34359738368 365163750571 703515643084800 qz297 (@Enclosure.Real.IsNear.recentre' (Real.cos qz158) Bool.true 489608 524288 5552836 5367398400 61201 65536 1388209 1341849600 (ep570 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz28 (@Neg.neg Real Real.instNeg (Real.sin qz158)) 262143 524288 1 524288 187513 524288 1388209 1341849600 49155220359 274877906944 2915124609443 5628125144678400 qz297 (@Enclosure.Real.IsNear.neg (Real.sin qz158) Bool.false 187513 524288 1388209 1341849600 (@Enclosure.Real.IsNear.recentre' (Real.sin qz158) Bool.false 187513 524288 5552836 5367398400 187513 524288 1388209 1341849600 (ep574 rfl rfl) rfl)) rfl)

noncomputable def ep576 := @ep536 16043413743 34359738368 365163750571 703515643084800 Bool.true 49155220359 274877906944 2915124609443 5628125144678400 Bool.false 538446534805670592512 15670856659 68719476736 868869162169 469010428723200 Bool.true 18623469830672926900224 135503577117 274877906944 3478500485401 1876041714892800 (ep537 (BSN.head_sum_c_succ qz145 3 4 rfl rfl) (ep564 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep565 ep575) rfl rfl

noncomputable abbrev qz159 := (@HMul.hMul Real Real Real qz265 qz401 (Real.log (Enclosure.sfrac Bool.false 5 1)))

noncomputable def ep577 := @Enclosure.Complex.IsNear.of_eq qz149 (Complex.mk (@HMul.hMul Real Real Real qz0 qz31 (Real.cos qz159)) (@HMul.hMul Real Real Real qz0 qz31 (@Neg.neg Real Real.instNeg (Real.sin qz159)))) Bool.true 103905171819 274877906944 522604086113 1125625028935680 Bool.true 65690945261 274877906944 521936674823 1125625028935680 (BSN.cpow_neg_s_mk qz154 83585 1000 5 qz155 rfl)

noncomputable def ep578 := nat_lit 5496473211595172830183164224730383938757607467337434598265237335505390921825

noncomputable def ep579 := nat_lit 1868574267024490683206008714655407459101510373312548015833301938858748001

noncomputable def ep580 := nat_lit 14392499767269317760802144193517753941812331397660298870097605770803585869921

noncomputable def ep581 := BSN.sin_dyadic_bound_f 1081281557 1073741824 3 2 524288 163960 ep578 ep57 ep579 ep580 ep60 ep579 443151 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1081281557) qz281 0 2 ep578 ep57 ep579 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1081281557) qz282 0 2 ep580 ep60 ep579 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz406 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 70529691) qz19)

noncomputable def ep582 := @Enclosure.Real.IsNear.cos_image qz159 qz406 Bool.false 70529691 524288 67 65536 Bool.true 443151 524288 1 81900 (@Enclosure.Real.IsNear.recentre' qz159 Bool.false 440810573 3276800 16717 16380000 70529691 524288 67 65536 (@Enclosure.Real.IsNear.mulLit_ff qz154 qz33 83585 1000 0 1 421904 262144 1 81900 440810573 3276800 16717 16380000 qz156 qz300 rfl) rfl) (Enclosure.sfrac_false_div 70529691 524288) (BSN.cos_reduce1 qz406 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 76088425300475250737152) qz22) 226375608064910080 72057594037927936 Bool.false 443151 524288 21 1000000000000000 163800 81900 (BSN.sin_reduce_arg_pos_rat_q1 70529691 524288 226375608064910080 72057594037927936 21 76088425300475250737152 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 443151 524288 76088425300475250737152 75557863725914323419136 1081281557 1073741824 163960 163800 (ep581 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep583 := nat_lit 3054426706115995790405405017612282369291604819797824798154391098364709955681

noncomputable def ep584 := nat_lit 9159542969813938389849803035407536292956611438646849298431506691216412371041

noncomputable def ep585 := BSN.cos_dyadic_bound_f 1081281557 1073741824 3 2 524288 163960 ep583 ep64 ep579 ep584 ep66 ep579 280169 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1081281557) qz285 0 2 ep583 ep64 ep579 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1081281557) qz286 0 2 ep584 ep66 ep579 rfl rfl rfl rfl) rfl rfl

noncomputable def ep586 := @Enclosure.Real.IsNear.sin_image qz159 qz406 Bool.false 70529691 524288 67 65536 Bool.false 280169 524288 1 81900 (@Enclosure.Real.IsNear.recentre' qz159 Bool.false 440810573 3276800 16717 16380000 70529691 524288 67 65536 (@Enclosure.Real.IsNear.mulLit_ff qz154 qz33 83585 1000 0 1 421904 262144 1 81900 440810573 3276800 16717 16380000 qz156 qz300 rfl) rfl) (Enclosure.sfrac_false_div 70529691 524288) (BSN.sin_reduce1 qz406 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 76088425300475250737152) qz22) 226375608064910080 72057594037927936 Bool.false 280169 524288 21 1000000000000000 163800 81900 (BSN.sin_reduce_arg_pos_rat_q1 70529691 524288 226375608064910080 72057594037927936 21 76088425300475250737152 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 280169 524288 76088425300475250737152 75557863725914323419136 1081281557 1073741824 163960 163800 (ep585 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep587 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz31 (Real.cos qz159)) (@HMul.hMul Real Real Real qz0 qz31 (@Neg.neg Real Real.instNeg (Real.sin qz159))) Bool.true 103905171819 274877906944 522604086113 1125625028935680 Bool.true 65690945261 274877906944 521936674823 1125625028935680 (@Enclosure.Real.IsNear.mulLit_ft qz31 (Real.cos qz159) 234469 524288 1 524288 443151 524288 1388209 1341849600 103905171819 274877906944 522604086113 1125625028935680 qz302 (@Enclosure.Real.IsNear.recentre' (Real.cos qz159) Bool.true 443151 524288 5552836 5367398400 443151 524288 1388209 1341849600 (ep582 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz31 (@Neg.neg Real Real.instNeg (Real.sin qz159)) 234469 524288 1 524288 280169 524288 1388209 1341849600 65690945261 274877906944 521936674823 1125625028935680 qz302 (@Enclosure.Real.IsNear.neg (Real.sin qz159) Bool.false 280169 524288 1388209 1341849600 (@Enclosure.Real.IsNear.recentre' (Real.sin qz159) Bool.false 280169 524288 5552836 5367398400 280169 524288 1388209 1341849600 (ep586 rfl rfl) rfl)) rfl)

noncomputable def ep588 := @ep534 103905171819 274877906944 522604086113 1125625028935680 Bool.true 65690945261 274877906944 521936674823 1125625028935680 Bool.true 2832736759120488562688 41221745183 274877906944 13039450376593 5628125144678400 Bool.true 55303929199862409592832 100597261189 137438953472 6522592415159 2814062572339200 (ep535 (BSN.head_sum_c_succ qz145 4 5 rfl rfl) (ep576 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep577 ep587) rfl rfl

noncomputable abbrev qz160 := (@HMul.hMul Real Real Real qz265 qz401 (Real.log (Enclosure.sfrac Bool.false 6 1)))

noncomputable def ep589 := @Enclosure.Complex.IsNear.of_eq qz148 (Complex.mk (@HMul.hMul Real Real Real qz0 qz34 (Real.cos qz160)) (@HMul.hMul Real Real Real qz0 qz34 (@Neg.neg Real Real.instNeg (Real.sin qz160)))) Bool.false 57549308047 274877906944 476512641911 1125625028935680 Bool.false 48168834833 137438953472 238627370953 562812514467840 (BSN.cpow_neg_s_mk qz154 83585 1000 6 qz155 rfl)

noncomputable def ep590 := @Enclosure.Real.IsNear.mulLit_ff qz154 qz36 83585 1000 0 1 4034681531866359 2251799813685248 5000000000819 409500000000000000 67447771168209923403 450359962737049600 83585000013691223 81900000000000000000 qz156 (BSN.isNear_log_sfrac 6 1 4034681531866359 2251799813685248 5000000000819 409500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz304) Bool.false 16922680887833197019136 9444732965739290427392 1000000000163800 81900000000000000000 4034681531866359 2251799813685248 5000000000819 409500000000000000 (BSN.log_rat_reduce_isNear 6 1 2 12 8 106290 262144 24973259072661432 36028797018963968 81900 1000000000000000 rfl rfl rfl rfl (ep120 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep591 := nat_lit 111761367877476523158240048969610000

noncomputable def ep592 := BSN.sin_dyadic_bound_f 578193130 1073741824 2 1 524288 163960 ep591 ep108 ep591 ep591 ep109 ep591 268873 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 578193130) qz281 0 1 ep591 ep108 ep591 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 578193130) qz282 0 1 ep591 ep109 ep591 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz407 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 78519539) qz19)

noncomputable def ep593 := @Enclosure.Real.IsNear.cos_image qz160 qz407 Bool.false 78519539 524288 67 65536 Bool.false 268873 524288 1 81900 (@Enclosure.Real.IsNear.recentre' qz160 Bool.false 67447771168209923403 450359962737049600 83585000013691223 81900000000000000000 78519539 524288 67 65536 (ep590 rfl) rfl) (Enclosure.sfrac_false_div 78519539 524288) (BSN.cos_reduce3 qz407 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 40686724506620377694208) qz22) 226375608064910080 72057594037927936 Bool.false 268873 524288 23 1000000000000000 163800 81900 (BSN.sin_reduce_arg_pos_rat_q3 78519539 524288 226375608064910080 72057594037927936 23 40686724506620377694208 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 268873 524288 40686724506620377694208 75557863725914323419136 578193130 1073741824 163960 163800 (ep592 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep594 := BSN.cos_dyadic_bound_f 578193130 1073741824 2 1 524288 163960 ep591 ep112 ep591 ep591 ep113 ep591 450094 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 578193130) qz285 0 1 ep591 ep112 ep591 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 578193130) qz286 0 1 ep591 ep113 ep591 rfl rfl rfl rfl) rfl rfl

noncomputable def ep595 := @Enclosure.Real.IsNear.sin_image qz160 qz407 Bool.false 78519539 524288 67 65536 Bool.true 450094 524288 1 81900 (@Enclosure.Real.IsNear.recentre' qz160 Bool.false 67447771168209923403 450359962737049600 83585000013691223 81900000000000000000 78519539 524288 67 65536 (ep590 rfl) rfl) (Enclosure.sfrac_false_div 78519539 524288) (BSN.sin_reduce3 qz407 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 40686724506620377694208) qz22) 226375608064910080 72057594037927936 Bool.false 450094 524288 23 1000000000000000 163800 81900 (BSN.sin_reduce_arg_pos_rat_q3 78519539 524288 226375608064910080 72057594037927936 23 40686724506620377694208 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 450094 524288 40686724506620377694208 75557863725914323419136 578193130 1073741824 163960 163800 (ep594 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep596 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz34 (Real.cos qz160)) (@HMul.hMul Real Real Real qz0 qz34 (@Neg.neg Real Real.instNeg (Real.sin qz160))) Bool.false 57549308047 274877906944 476512641911 1125625028935680 Bool.false 48168834833 137438953472 238627370953 562812514467840 (@Enclosure.Real.IsNear.mulLit_ff qz34 (Real.cos qz160) 214039 524288 1 524288 268873 524288 1388209 1341849600 57549308047 274877906944 476512641911 1125625028935680 qz306 (@Enclosure.Real.IsNear.recentre' (Real.cos qz160) Bool.false 268873 524288 5552836 5367398400 268873 524288 1388209 1341849600 (ep593 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz34 (@Neg.neg Real Real.instNeg (Real.sin qz160)) 214039 524288 1 524288 225047 262144 1388209 1341849600 48168834833 137438953472 238627370953 562812514467840 qz306 (@Enclosure.Real.IsNear.neg (Real.sin qz160) Bool.true 225047 262144 1388209 1341849600 (@Enclosure.Real.IsNear.recentre' (Real.sin qz160) Bool.true 450094 524288 5552836 5367398400 225047 262144 1388209 1341849600 (ep595 rfl rfl) rfl)) rfl)

noncomputable def ep597 := @ep532 57549308047 274877906944 476512641911 1125625028935680 Bool.false 48168834833 137438953472 238627370953 562812514467840 Bool.false 4488086305552902127616 1020472679 17179869184 296577184349 108233175859200 Bool.true 7205708050552462508032 13107106589 34359738368 148379409037 54116587929600 (ep533 (BSN.head_sum_c_succ qz145 5 6 rfl rfl) (ep588 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep589 ep596) rfl rfl

noncomputable abbrev qz161 := (@HMul.hMul Real Real Real qz265 qz401 (Real.log (Enclosure.sfrac Bool.false 7 1)))

noncomputable def ep598 := @Enclosure.Complex.IsNear.of_eq qz147 (Complex.mk (@HMul.hMul Real Real Real qz0 qz37 (Real.cos qz161)) (@HMul.hMul Real Real Real qz0 qz37 (@Neg.neg Real Real.instNeg (Real.sin qz161)))) Bool.false 19625865357 68719476736 552213920077 1407031286169600 Bool.false 17013284365 68719476736 551943977677 1407031286169600 (BSN.cpow_neg_s_mk qz154 83585 1000 7 qz155 rfl)

noncomputable def ep599 := @Enclosure.Real.IsNear.mulLit_ff qz154 qz39 83585 1000 0 1 4381792198794487 2251799813685248 5000000000819 409500000000000000 73250420187247439179 450359962737049600 83585000013691223 81900000000000000000 qz156 (BSN.isNear_log_sfrac 7 1 4381792198794487 2251799813685248 5000000000819 409500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz308) Bool.false 18378568546572512002048 9444732965739290427392 1000000000163800 81900000000000000000 4381792198794487 2251799813685248 5000000000819 409500000000000000 (BSN.log_rat_reduce_isNear 7 1 2 14 8 146699 262144 24973259072661432 36028797018963968 81900 1000000000000000 rfl rfl rfl rfl (ep134 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep600 := nat_lit 715613749045231637235923748314410000

noncomputable def ep601 := BSN.sin_dyadic_bound_f 919749730 1073741824 2 1 524288 163960 ep600 ep108 ep600 ep600 ep109 ep600 396156 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 919749730) qz281 0 1 ep600 ep108 ep600 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 919749730) qz282 0 1 ep600 ep109 ep600 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz408 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 10659339) qz484)

noncomputable def ep602 := @Enclosure.Real.IsNear.cos_image qz161 qz408 Bool.false 10659339 65536 67 65536 Bool.false 396156 524288 1 81900 (@Enclosure.Real.IsNear.recentre' qz161 Bool.false 73250420187247439179 450359962737049600 83585000013691223 81900000000000000000 10659339 65536 67 65536 (ep599 rfl) rfl) (Enclosure.sfrac_false_div 10659339 65536) (BSN.cos_reduce3 qz408 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 8090204184684913491968) qz301) 226375608064910080 72057594037927936 Bool.false 396156 524288 25 1000000000000000 163800 81900 (BSN.sin_reduce_arg_pos_rat_q3 10659339 65536 226375608064910080 72057594037927936 25 8090204184684913491968 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 396156 524288 8090204184684913491968 9444732965739290427392 919749730 1073741824 163960 163800 (ep601 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep603 := nat_lit 1598551336429021218429357007700737089905455285473412418787861310363568800000

noncomputable def ep604 := nat_lit 512103037822571763993660683025856945388713524997061075316213648100000000

noncomputable def ep605 := nat_lit 4794629803211418511760083701736159555825588429370243134212951503794506400000

noncomputable def ep606 := BSN.cos_dyadic_bound_f 919749730 1073741824 3 2 524288 163960 ep603 ep64 ep604 ep605 ep66 ep604 343420 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 919749730) qz285 0 2 ep603 ep64 ep604 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 919749730) qz286 0 2 ep605 ep66 ep604 rfl rfl rfl rfl) rfl rfl

noncomputable def ep607 := @Enclosure.Real.IsNear.sin_image qz161 qz408 Bool.false 10659339 65536 67 65536 Bool.true 343420 524288 1 81900 (@Enclosure.Real.IsNear.recentre' qz161 Bool.false 73250420187247439179 450359962737049600 83585000013691223 81900000000000000000 10659339 65536 67 65536 (ep599 rfl) rfl) (Enclosure.sfrac_false_div 10659339 65536) (BSN.sin_reduce3 qz408 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 8090204184684913491968) qz301) 226375608064910080 72057594037927936 Bool.false 343420 524288 25 1000000000000000 163800 81900 (BSN.sin_reduce_arg_pos_rat_q3 10659339 65536 226375608064910080 72057594037927936 25 8090204184684913491968 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 343420 524288 8090204184684913491968 9444732965739290427392 919749730 1073741824 163960 163800 (ep606 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep608 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz37 (Real.cos qz161)) (@HMul.hMul Real Real Real qz0 qz37 (@Neg.neg Real Real.instNeg (Real.sin qz161))) Bool.false 19625865357 68719476736 552213920077 1407031286169600 Bool.false 17013284365 68719476736 551943977677 1407031286169600 (@Enclosure.Real.IsNear.mulLit_ff qz37 (Real.cos qz161) 198163 524288 1 524288 99039 131072 1388209 1341849600 19625865357 68719476736 552213920077 1407031286169600 qz310 (@Enclosure.Real.IsNear.recentre' (Real.cos qz161) Bool.false 396156 524288 5552836 5367398400 99039 131072 1388209 1341849600 (ep602 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz37 (@Neg.neg Real Real.instNeg (Real.sin qz161)) 198163 524288 1 524288 85855 131072 1388209 1341849600 17013284365 68719476736 551943977677 1407031286169600 qz310 (@Enclosure.Real.IsNear.neg (Real.sin qz161) Bool.true 85855 131072 1388209 1341849600 (@Enclosure.Real.IsNear.recentre' (Real.sin qz161) Bool.true 343420 524288 5552836 5367398400 85855 131072 1388209 1341849600 (ep607 rfl rfl) rfl)) rfl)

noncomputable def ep609 := @ep530 19625865357 68719476736 552213920077 1407031286169600 Bool.false 17013284365 68719476736 551943977677 1407031286169600 Bool.false 407296147980321554432 23707756073 68719476736 734619552769 234505214361600 Bool.true 316141506757272797184 9200928813 68719476736 1469936204213 469010428723200 (ep531 (BSN.head_sum_c_succ qz145 6 7 rfl rfl) (ep597 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep598 ep608) rfl rfl

noncomputable abbrev qz162 := (@HMul.hMul Real Real Real qz265 qz401 (Real.log (Enclosure.sfrac Bool.false 8 1)))

noncomputable def ep610 := @Enclosure.Complex.IsNear.of_eq qz146 (Complex.mk (@HMul.hMul Real Real Real qz0 qz40 (Real.cos qz162)) (@HMul.hMul Real Real Real qz0 qz40 (@Neg.neg Real Real.instNeg (Real.sin qz162)))) Bool.true 25326702779 137438953472 114677050331 312673619148800 Bool.false 82939006083 274877906944 229750348787 625347238297600 (BSN.cpow_neg_s_mk qz154 83585 1000 8 qz155 rfl)

noncomputable def ep611 := @Enclosure.Real.IsNear.mulLit_ff qz154 qz42 83585 1000 0 1 9364972152248037 4503599627370496 10000000002457 819000000000000000 156554239469130434529 900719925474099200 167170000041073669 163800000000000000000 qz156 (BSN.isNear_log_sfrac 8 1 9364972152248037 4503599627370496 10000000002457 819000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz312) Bool.false 19639770079031275290624 9444732965739290427392 1000000000245700 81900000000000000000 9364972152248037 4503599627370496 10000000002457 819000000000000000 (BSN.log_rat_reduce_isNear 8 1 3 16 16 0 262144 24973259072661432 36028797018963968 81900 1000000000000000 rfl rfl rfl rfl (ep148 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep612 := nat_lit 3247014630078888572618727803301433241120771499397267849821046198967148503296

noncomputable def ep613 := nat_lit 2111475062575813571459454264001360432351936905080751655516052715906294016

noncomputable def ep614 := nat_lit 9736820940111514090713264501376297002497610624381642046152106491469632921856

noncomputable def ep615 := BSN.cos_dyadic_bound_f 1097926442 1073741824 3 2 524288 163960 ep612 ep64 ep613 ep614 ep66 ep613 273266 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1097926442) qz285 0 2 ep612 ep64 ep613 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1097926442) qz286 0 2 ep614 ep66 ep613 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz409 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 2847705) (@Nat.cast Real Real.instNatCast 16384))

noncomputable def ep616 := @Enclosure.Real.IsNear.cos_image qz162 qz409 Bool.false 2847705 16384 67 65536 Bool.true 273266 524288 1 81900 (@Enclosure.Real.IsNear.recentre' qz162 Bool.false 156554239469130434529 900719925474099200 167170000041073669 163800000000000000000 2847705 16384 67 65536 (ep611 rfl) rfl) (Enclosure.sfrac_false_div 2847705 16384) (BSN.cos_reduce2 qz409 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 2414365780651603394560) (@Nat.cast Real Real.instNatCast 2361183241434822606848)) 226375608064910080 72057594037927936 Bool.false 273266 524288 27 1000000000000000 163800 81900 (BSN.sin_reduce_arg_pos_rat_q2 2847705 16384 226375608064910080 72057594037927936 27 2414365780651603394560 2361183241434822606848 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 273266 524288 2414365780651603394560 2361183241434822606848 1097926442 1073741824 163960 163800 (ep615 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep617 := nat_lit 5842937154091938779856542482531378745671507149391017528353470315968142270720

noncomputable def ep618 := nat_lit 15299512062996621677651438814011894512249187017225391357293015313614619566336

noncomputable def ep619 := BSN.sin_dyadic_bound_f 1097926442 1073741824 3 2 524288 163960 ep617 ep57 ep613 ep618 ep60 ep613 447441 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1097926442) qz281 0 2 ep617 ep57 ep613 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1097926442) qz282 0 2 ep618 ep60 ep613 rfl rfl rfl rfl) rfl rfl

noncomputable def ep620 := @Enclosure.Real.IsNear.sin_image qz162 qz409 Bool.false 2847705 16384 67 65536 Bool.true 447441 524288 1 81900 (@Enclosure.Real.IsNear.recentre' qz162 Bool.false 156554239469130434529 900719925474099200 167170000041073669 163800000000000000000 2847705 16384 67 65536 (ep611 rfl) rfl) (Enclosure.sfrac_false_div 2847705 16384) (BSN.sin_reduce2 qz409 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 2414365780651603394560) (@Nat.cast Real Real.instNatCast 2361183241434822606848)) 226375608064910080 72057594037927936 Bool.false 447441 524288 27 1000000000000000 163800 81900 (BSN.sin_reduce_arg_pos_rat_q2 2847705 16384 226375608064910080 72057594037927936 27 2414365780651603394560 2361183241434822606848 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 447441 524288 2414365780651603394560 2361183241434822606848 1097926442 1073741824 163960 163800 (ep619 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep621 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz40 (Real.cos qz162)) (@HMul.hMul Real Real Real qz0 qz40 (@Neg.neg Real Real.instNeg (Real.sin qz162))) Bool.true 25326702779 137438953472 114677050331 312673619148800 Bool.false 82939006083 274877906944 229750348787 625347238297600 (@Enclosure.Real.IsNear.mulLit_ft qz40 (Real.cos qz162) 185363 524288 1 524288 136633 262144 1388209 1341849600 25326702779 137438953472 114677050331 312673619148800 qz315 (@Enclosure.Real.IsNear.recentre' (Real.cos qz162) Bool.true 273266 524288 5552836 5367398400 136633 262144 1388209 1341849600 (ep616 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz40 (@Neg.neg Real Real.instNeg (Real.sin qz162)) 185363 524288 1 524288 447441 524288 1388209 1341849600 82939006083 274877906944 229750348787 625347238297600 qz315 (@Enclosure.Real.IsNear.neg (Real.sin qz162) Bool.true 447441 524288 1388209 1341849600 (@Enclosure.Real.IsNear.recentre' (Real.sin qz162) Bool.true 447441 524288 5552836 5367398400 447441 524288 1388209 1341849600 (ep620 rfl rfl) rfl)) rfl)

noncomputable def ep622 := @ep528 25326702779 137438953472 114677050331 312673619148800 Bool.false 82939006083 274877906944 229750348787 625347238297600 Bool.false 1517931421421495386112 22088809367 137438953472 468929908867 134002979635200 Bool.false 3170393044969498607616 46135290831 274877906944 938427980459 268005959270400 (ep529 (BSN.head_sum_c_succ qz145 7 8 rfl rfl) (ep609 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep610 ep621) rfl rfl

theorem EMRow22.d11 : Enclosure.Complex.IsNear qz144 Bool.false 22088809367 137438953472 468929908867 134002979635200 Bool.false 46135290831 274877906944 938427980459 268005959270400 := ep527 (BSN.head_sum_c_succ qz145 8 9 rfl rfl) (ep622 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable abbrev qz163 := (@HPow.hPow Complex Complex Complex qz272 (@Nat.cast Complex Complex.instNatCast 16) qz400)

noncomputable def ep623 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz145 17) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz145 16) qz163) Bool.false 92947171639 68719476736 137940982819 23450521436160 Bool.true 5806503165 68719476736 1103574612437 187604171489280

noncomputable def ep624 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz145 16) qz163 Bool.false 320628398481 274877906944 31642201331801 5628125144678400 Bool.true 69105188003 274877906944 31644428807051 5628125144678400 Bool.false

noncomputable abbrev qz164 := (@HPow.hPow Complex Complex Complex qz272 (@Nat.cast Complex Complex.instNatCast 15) qz400)

noncomputable def ep625 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz145 16) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz145 15) qz164) Bool.false 320628398481 274877906944 31642201331801 5628125144678400 Bool.true 69105188003 274877906944 31644428807051 5628125144678400

noncomputable def ep626 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz145 15) qz164 Bool.false 62633086771 68719476736 7532050550873 1407031286169600 Bool.true 57980940707 274877906944 30139349223467 5628125144678400 Bool.false

noncomputable abbrev qz165 := (@HPow.hPow Complex Complex Complex qz272 (@Nat.cast Complex Complex.instNatCast 14) qz400)

noncomputable def ep627 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz145 15) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz145 14) qz165) Bool.false 62633086771 68719476736 7532050550873 1407031286169600 Bool.true 57980940707 274877906944 30139349223467 5628125144678400

noncomputable def ep628 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz145 14) qz165 Bool.false 193124913505 274877906944 9521221548161 1876041714892800 Bool.true 6070528081 137438953472 1190687581567 234505214361600 Bool.false

noncomputable abbrev qz166 := (@HPow.hPow Complex Complex Complex qz272 (@Nat.cast Complex Complex.instNatCast 13) qz400)

noncomputable def ep629 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz145 14) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz145 13) qz166) Bool.false 193124913505 274877906944 9521221548161 1876041714892800 Bool.true 6070528081 137438953472 1190687581567 234505214361600

noncomputable def ep630 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz145 13) qz166 Bool.false 4312710267 8589934592 13470502799197 2814062572339200 Bool.false 20264276485 137438953472 6738546922511 1407031286169600 Bool.false

noncomputable abbrev qz167 := (@HPow.hPow Complex Complex Complex qz272 (@Nat.cast Complex Complex.instNatCast 12) qz400)

noncomputable def ep631 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz145 13) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz145 12) qz167) Bool.false 4312710267 8589934592 13470502799197 2814062572339200 Bool.false 20264276485 137438953472 6738546922511 1407031286169600

noncomputable def ep632 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz145 12) qz167 Bool.false 63624294957 274877906944 25250099436269 5628125144678400 Bool.false 68164123625 274877906944 25269605600219 5628125144678400 Bool.false

noncomputable abbrev qz168 := (@HPow.hPow Complex Complex Complex qz272 (@Nat.cast Complex Complex.instNatCast 11) qz400)

noncomputable def ep633 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz145 12) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz145 11) qz168) Bool.false 63624294957 274877906944 25250099436269 5628125144678400 Bool.false 68164123625 274877906944 25269605600219 5628125144678400

noncomputable def ep634 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz145 11) qz168 Bool.true 3143848431 274877906944 7828622246603 1876041714892800 Bool.false 4765761839 68719476736 3917943535039 938020857446400 Bool.false

noncomputable abbrev qz169 := (@HPow.hPow Complex Complex Complex qz272 (@Nat.cast Complex Complex.instNatCast 10) qz400)

noncomputable def ep635 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz145 11) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz145 10) qz169) Bool.true 3143848431 274877906944 7828622246603 1876041714892800 Bool.false 4765761839 68719476736 3917943535039 938020857446400

noncomputable def ep636 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz145 10) qz169 Bool.false 55891108809 274877906944 21637300170697 5628125144678400 Bool.true 11184711931 68719476736 10829252971961 2814062572339200 Bool.true

noncomputable abbrev qz170 := (@HPow.hPow Complex Complex Complex qz272 (@Nat.cast Complex Complex.instNatCast 9) qz400)

noncomputable def ep637 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz145 10) (@HAdd.hAdd Complex Complex Complex qz4 qz144 qz170) Bool.false 55891108809 274877906944 21637300170697 5628125144678400 Bool.true 11184711931 68719476736 10829252971961 2814062572339200

noncomputable def ep638 := @Enclosure.Complex.IsNear.addLitP qz144 qz170 Bool.false 22088809367 137438953472 468929908867 134002979635200 Bool.false 46135290831 274877906944 938427980459 268005959270400 Bool.false

noncomputable abbrev qz171 := (@HMul.hMul Real Real Real qz265 qz401 qz317)

noncomputable def ep639 := @Enclosure.Complex.IsNear.of_eq qz170 (Complex.mk (@HMul.hMul Real Real Real qz0 qz51 (Real.cos qz171)) (@HMul.hMul Real Real Real qz0 qz51 (@Neg.neg Real Real.instNeg (Real.sin qz171)))) Bool.false 11713490075 274877906944 1942243998283 5628125144678400 Bool.true 90874138555 274877906944 1951518354283 5628125144678400 (BSN.cpow_neg_s_mk qz154 83585 1000 9 qz155 rfl)

noncomputable def ep640 := @Enclosure.Real.IsNear.mulLit_ff qz154 qz317 83585 1000 0 1 9895417793173221 4503599627370496 10000000002457 819000000000000000 165421699248476735457 900719925474099200 167170000041073669 163800000000000000000 qz156 (BSN.isNear_log_sfrac 9 1 9895417793173221 4503599627370496 10000000002457 819000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz318) Bool.false 20752195215788806766592 9444732965739290427392 1000000000245700 81900000000000000000 9895417793173221 4503599627370496 10000000002457 819000000000000000 (BSN.log_rat_reduce_isNear 9 1 3 18 16 30876 262144 24973259072661432 36028797018963968 81900 1000000000000000 rfl rfl rfl rfl (ep175 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep641 := nat_lit 12888868635721860430742792756244935855600992145390609037466814442932346617856

noncomputable def ep642 := nat_lit 33141773926702614104814574366766730931562051698517052091263293282991538176

noncomputable def ep643 := nat_lit 38600322359312176064018749120001274104939852332774793008217916742231056777216

noncomputable def ep644 := BSN.cos_dyadic_bound_f 1548984132 1073741824 3 2 524288 163960 ep641 ep64 ep642 ep643 ep66 ep642 67025 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1548984132) qz285 0 2 ep641 ep64 ep642 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1548984132) qz286 0 2 ep643 ep66 ep642 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz410 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 96288101) qz19)

noncomputable def ep645 := @Enclosure.Real.IsNear.cos_image qz171 qz410 Bool.false 96288101 524288 67 65536 Bool.false 67025 524288 1 81900 (@Enclosure.Real.IsNear.recentre' qz171 Bool.false 165421699248476735457 900719925474099200 167170000041073669 163800000000000000000 96288101 524288 67 65536 (ep640 rfl) rfl) (Enclosure.sfrac_false_div 96288101 524288) (BSN.cos_reduce0 qz410 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 109000068150279045906432) qz22) 226375608064910080 72057594037927936 Bool.false 67025 524288 29 1000000000000000 163800 81900 (BSN.sin_reduce_arg_pos_rat_q0 96288101 524288 226375608064910080 72057594037927936 29 109000068150279045906432 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 67025 524288 109000068150279045906432 75557863725914323419136 1548984132 1073741824 163960 163800 (ep644 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep646 := nat_lit 23173450125157986684053175301747471155336536220344282625767255362651830681600

noncomputable def ep647 := nat_lit 60638711265246732321112426003220992604373161064818379268861718713058522628096

noncomputable def ep648 := BSN.sin_dyadic_bound_f 1548984132 1073741824 3 2 524288 163960 ep646 ep57 ep642 ep647 ep60 ep642 519985 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1548984132) qz281 0 2 ep646 ep57 ep642 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1548984132) qz282 0 2 ep647 ep60 ep642 rfl rfl rfl rfl) rfl rfl

noncomputable def ep649 := @Enclosure.Real.IsNear.sin_image qz171 qz410 Bool.false 96288101 524288 67 65536 Bool.false 519985 524288 1 81900 (@Enclosure.Real.IsNear.recentre' qz171 Bool.false 165421699248476735457 900719925474099200 167170000041073669 163800000000000000000 96288101 524288 67 65536 (ep640 rfl) rfl) (Enclosure.sfrac_false_div 96288101 524288) (BSN.sin_reduce0 qz410 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 109000068150279045906432) qz22) 226375608064910080 72057594037927936 Bool.false 519985 524288 29 1000000000000000 163800 81900 (BSN.sin_reduce_arg_pos_rat_q0 96288101 524288 226375608064910080 72057594037927936 29 109000068150279045906432 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 519985 524288 109000068150279045906432 75557863725914323419136 1548984132 1073741824 163960 163800 (ep648 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep650 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz51 (Real.cos qz171)) (@HMul.hMul Real Real Real qz0 qz51 (@Neg.neg Real Real.instNeg (Real.sin qz171))) Bool.false 11713490075 274877906944 1942243998283 5628125144678400 Bool.true 90874138555 274877906944 1951518354283 5628125144678400 (@Enclosure.Real.IsNear.mulLit_ff qz51 (Real.cos qz171) 174763 524288 1 524288 67025 524288 1388209 1341849600 11713490075 274877906944 1942243998283 5628125144678400 qz320 (@Enclosure.Real.IsNear.recentre' (Real.cos qz171) Bool.false 67025 524288 5552836 5367398400 67025 524288 1388209 1341849600 (ep645 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz51 (@Neg.neg Real Real.instNeg (Real.sin qz171)) 174763 524288 1 524288 519985 524288 1388209 1341849600 90874138555 274877906944 1951518354283 5628125144678400 qz320 (@Enclosure.Real.IsNear.neg (Real.sin qz171) Bool.false 519985 524288 1388209 1341849600 (@Enclosure.Real.IsNear.recentre' (Real.sin qz171) Bool.false 519985 524288 5552836 5367398400 519985 524288 1388209 1341849600 (ep649 rfl rfl) rfl)) rfl)

noncomputable def ep651 := @ep638 11713490075 274877906944 1942243998283 5628125144678400 Bool.true 90874138555 274877906944 1951518354283 5628125144678400 Bool.false 7681615503098640334848 55891108809 274877906944 21637300170697 5628125144678400 Bool.true 12297720821459458195456 11184711931 68719476736 10829252971961 2814062572339200 EMRow22.d11 (ep639 ep650) rfl rfl

noncomputable abbrev qz172 := (@HMul.hMul Real Real Real qz265 qz401 (Real.log (Enclosure.sfrac Bool.false 10 1)))

noncomputable def ep652 := @Enclosure.Complex.IsNear.of_eq qz169 (Complex.mk (@HMul.hMul Real Real Real qz0 qz53 (Real.cos qz172)) (@HMul.hMul Real Real Real qz0 qz53 (@Neg.neg Real Real.instNeg (Real.sin qz172)))) Bool.true 7379369655 34359738368 231070821139 703515643084800 Bool.false 7975236885 34359738368 231144408289 703515643084800 (BSN.cpow_neg_s_mk qz154 83585 1000 10 qz155 rfl)

noncomputable def ep653 := @Enclosure.Real.IsNear.mulLit_ff qz154 qz55 83585 1000 0 1 10369908600166117 4503599627370496 10000000002457 819000000000000000 173353762068976977889 900719925474099200 167170000041073669 163800000000000000000 qz156 (BSN.isNear_log_sfrac 10 1 10369908600166117 4503599627370496 10000000002457 819000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz322) Bool.false 21747274560655572598784 9444732965739290427392 1000000000245700 81900000000000000000 10369908600166117 4503599627370496 10000000002457 819000000000000000 (BSN.log_rat_reduce_isNear 10 1 3 20 16 58495 262144 24973259072661432 36028797018963968 81900 1000000000000000 rfl rfl rfl rfl (ep189 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep654 := nat_lit 1370025992441640849338191728184065262237289418786652341889872432310752542976

noncomputable def ep655 := nat_lit 376185072936146258374449325940181753312096326930187325584018553431818496

noncomputable def ep656 := nat_lit 4109325607179050255497826285900315423205244063706096651018449259825393991936

noncomputable def ep657 := BSN.cos_dyadic_bound_f 884963166 1073741824 3 2 524288 163960 ep654 ep64 ep655 ep656 ep66 ep655 356072 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 884963166) qz285 0 2 ep654 ep64 ep655 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 884963166) qz286 0 2 ep656 ep66 ep655 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz411 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 50452585) qz26)

noncomputable def ep658 := @Enclosure.Real.IsNear.cos_image qz172 qz411 Bool.false 50452585 262144 67 65536 Bool.true 356072 524288 1 81900 (@Enclosure.Real.IsNear.recentre' qz172 Bool.false 173353762068976977889 900719925474099200 167170000041073669 163800000000000000000 50452585 262144 67 65536 (ep653 rfl) rfl) (Enclosure.sfrac_false_div 50452585 262144) (BSN.cos_reduce2 qz411 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 31136873318834692423680) qz292) 226375608064910080 72057594037927936 Bool.false 356072 524288 30 1000000000000000 163800 81900 (BSN.sin_reduce_arg_pos_rat_q2 50452585 262144 226375608064910080 72057594037927936 30 31136873318834692423680 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 356072 524288 31136873318834692423680 37778931862957161709568 884963166 1073741824 163960 163800 (ep657 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep659 := nat_lit 613339280444474922735171444587525136

noncomputable def ep660 := BSN.sin_dyadic_bound_f 884963166 1073741824 2 1 524288 163960 ep659 ep108 ep659 ep659 ep109 ep659 384824 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 884963166) qz281 0 1 ep659 ep108 ep659 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 884963166) qz282 0 1 ep659 ep109 ep659 rfl rfl rfl rfl) rfl rfl

noncomputable def ep661 := @Enclosure.Real.IsNear.sin_image qz172 qz411 Bool.false 50452585 262144 67 65536 Bool.true 384824 524288 1 81900 (@Enclosure.Real.IsNear.recentre' qz172 Bool.false 173353762068976977889 900719925474099200 167170000041073669 163800000000000000000 50452585 262144 67 65536 (ep653 rfl) rfl) (Enclosure.sfrac_false_div 50452585 262144) (BSN.sin_reduce2 qz411 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 31136873318834692423680) qz292) 226375608064910080 72057594037927936 Bool.false 384824 524288 30 1000000000000000 163800 81900 (BSN.sin_reduce_arg_pos_rat_q2 50452585 262144 226375608064910080 72057594037927936 30 31136873318834692423680 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 384824 524288 31136873318834692423680 37778931862957161709568 884963166 1073741824 163960 163800 (ep660 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep662 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz53 (Real.cos qz172)) (@HMul.hMul Real Real Real qz0 qz53 (@Neg.neg Real Real.instNeg (Real.sin qz172))) Bool.true 7379369655 34359738368 231070821139 703515643084800 Bool.false 7975236885 34359738368 231144408289 703515643084800 (@Enclosure.Real.IsNear.mulLit_ft qz53 (Real.cos qz172) 165795 524288 1 524288 44509 65536 1388209 1341849600 7379369655 34359738368 231070821139 703515643084800 qz324 (@Enclosure.Real.IsNear.recentre' (Real.cos qz172) Bool.true 356072 524288 5552836 5367398400 44509 65536 1388209 1341849600 (ep658 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz53 (@Neg.neg Real Real.instNeg (Real.sin qz172)) 165795 524288 1 524288 48103 65536 1388209 1341849600 7975236885 34359738368 231144408289 703515643084800 qz324 (@Enclosure.Real.IsNear.neg (Real.sin qz172) Bool.true 48103 65536 1388209 1341849600 (@Enclosure.Real.IsNear.recentre' (Real.sin qz172) Bool.true 384824 524288 5552836 5367398400 48103 65536 1388209 1341849600 (ep661 rfl rfl) rfl)) rfl)

noncomputable def ep663 := @ep636 7379369655 34359738368 231070821139 703515643084800 Bool.false 7975236885 34359738368 231144408289 703515643084800 Bool.true 108021809557807300608 3143848431 274877906944 7828622246603 1876041714892800 Bool.false 163750329912238538752 4765761839 68719476736 3917943535039 938020857446400 (ep637 (BSN.head_sum_c_succ qz145 9 10 rfl rfl) (ep651 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep652 ep662) rfl rfl

noncomputable abbrev qz173 := (@HMul.hMul Real Real Real qz265 qz401 (Real.log (Enclosure.sfrac Bool.false 11 1)))

noncomputable def ep664 := @Enclosure.Complex.IsNear.of_eq qz168 (Complex.mk (@HMul.hMul Real Real Real qz0 qz56 (Real.cos qz173)) (@HMul.hMul Real Real Real qz0 qz56 (@Neg.neg Real Real.instNeg (Real.sin qz173)))) Bool.false 16692035847 68719476736 6785510371 21646635171840 Bool.false 49101076269 274877906944 27106836769 86586540687360 (BSN.cpow_neg_s_mk qz154 83585 1000 11 qz155 rfl)

noncomputable def ep665 := @Enclosure.Real.IsNear.mulLit_ff qz154 qz58 83585 1000 0 1 10799147631728357 4503599627370496 10000000002457 819000000000000000 180529350959602943969 900719925474099200 167170000041073669 163800000000000000000 qz156 (BSN.isNear_log_sfrac 11 1 10799147631728357 4503599627370496 10000000002457 819000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz326) Bool.false 22647454054174387339264 9444732965739290427392 1000000000245700 81900000000000000000 10799147631728357 4503599627370496 10000000002457 819000000000000000 (BSN.log_rat_reduce_isNear 11 1 3 22 16 83480 262144 24973259072661432 36028797018963968 81900 1000000000000000 rfl rfl rfl rfl (ep204 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep666 := nat_lit 4114410567713536365472771053684246669617573894075167212353817726743750901760

noncomputable def ep667 := nat_lit 1047204785296980493501326596858834012526757046993554845217105399980752896

noncomputable def ep668 := nat_lit 10774141726740209655439207754682874593930507354025543610224885399395569238016

noncomputable def ep669 := BSN.sin_dyadic_bound_f 1005782216 1073741824 3 2 524288 163960 ep666 ep57 ep667 ep668 ep60 ep667 422372 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1005782216) qz281 0 2 ep666 ep57 ep667 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1005782216) qz282 0 2 ep668 ep60 ep667 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz412 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 13135239) qz484)

noncomputable def ep670 := @Enclosure.Real.IsNear.cos_image qz173 qz412 Bool.false 13135239 65536 67 65536 Bool.false 422372 524288 1 81900 (@Enclosure.Real.IsNear.recentre' qz173 Bool.false 180529350959602943969 900719925474099200 167170000041073669 163800000000000000000 13135239 65536 67 65536 (ep665 rfl) rfl) (Enclosure.sfrac_false_div 13135239 65536) (BSN.cos_reduce3 qz412 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 8846953938289738907648) qz301) 226375608064910080 72057594037927936 Bool.false 422372 524288 31 1000000000000000 163800 81900 (BSN.sin_reduce_arg_pos_rat_q3 13135239 65536 226375608064910080 72057594037927936 31 8846953938289738907648 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 422372 524288 8846953938289738907648 9444732965739290427392 1005782216 1073741824 163960 163800 (ep669 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep671 := nat_lit 2286249073078763305481984508312074298237552944284867809016661895035408613376

noncomputable def ep672 := nat_lit 6856652809665695955458950871742505226687605318760616317359551474306264334336

noncomputable def ep673 := BSN.cos_dyadic_bound_f 1005782216 1073741824 3 2 524288 163960 ep671 ep64 ep667 ep672 ep66 ep667 310611 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1005782216) qz285 0 2 ep671 ep64 ep667 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1005782216) qz286 0 2 ep672 ep66 ep667 rfl rfl rfl rfl) rfl rfl

noncomputable def ep674 := @Enclosure.Real.IsNear.sin_image qz173 qz412 Bool.false 13135239 65536 67 65536 Bool.true 310611 524288 1 81900 (@Enclosure.Real.IsNear.recentre' qz173 Bool.false 180529350959602943969 900719925474099200 167170000041073669 163800000000000000000 13135239 65536 67 65536 (ep665 rfl) rfl) (Enclosure.sfrac_false_div 13135239 65536) (BSN.sin_reduce3 qz412 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 8846953938289738907648) qz301) 226375608064910080 72057594037927936 Bool.false 310611 524288 31 1000000000000000 163800 81900 (BSN.sin_reduce_arg_pos_rat_q3 13135239 65536 226375608064910080 72057594037927936 31 8846953938289738907648 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 310611 524288 8846953938289738907648 9444732965739290427392 1005782216 1073741824 163960 163800 (ep673 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep675 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz56 (Real.cos qz173)) (@HMul.hMul Real Real Real qz0 qz56 (@Neg.neg Real Real.instNeg (Real.sin qz173))) Bool.false 16692035847 68719476736 6785510371 21646635171840 Bool.false 49101076269 274877906944 27106836769 86586540687360 (@Enclosure.Real.IsNear.mulLit_ff qz56 (Real.cos qz173) 158079 524288 1 524288 105593 131072 1388209 1341849600 16692035847 68719476736 6785510371 21646635171840 qz328 (@Enclosure.Real.IsNear.recentre' (Real.cos qz173) Bool.false 422372 524288 5552836 5367398400 105593 131072 1388209 1341849600 (ep670 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz56 (@Neg.neg Real Real.instNeg (Real.sin qz173)) 158079 524288 1 524288 310611 524288 1388209 1341849600 49101076269 274877906944 27106836769 86586540687360 qz328 (@Enclosure.Real.IsNear.neg (Real.sin qz173) Bool.true 310611 524288 1388209 1341849600 (@Enclosure.Real.IsNear.recentre' (Real.sin qz173) Bool.true 310611 524288 5552836 5367398400 310611 524288 1388209 1341849600 (ep674 rfl rfl) rfl)) rfl)

noncomputable def ep676 := @ep634 16692035847 68719476736 6785510371 21646635171840 Bool.false 49101076269 274877906944 27106836769 86586540687360 Bool.false 4372228257141963620352 63624294957 274877906944 25250099436269 5628125144678400 Bool.false 4684202907678015488000 68164123625 274877906944 25269605600219 5628125144678400 (ep635 (BSN.head_sum_c_succ qz145 10 11 rfl rfl) (ep663 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep664 ep675) rfl rfl

noncomputable abbrev qz174 := (@HMul.hMul Real Real Real qz265 qz401 (Real.log (Enclosure.sfrac Bool.false 12 1)))

noncomputable def ep677 := @Enclosure.Complex.IsNear.of_eq qz167 (Complex.mk (@HMul.hMul Real Real Real qz0 qz59 (Real.cos qz174)) (@HMul.hMul Real Real Real qz0 qz59 (@Neg.neg Real Real.instNeg (Real.sin qz174)))) Bool.false 74382433587 274877906944 22545415495 75041668595712 Bool.true 27635570655 274877906944 22461094531 75041668595712 (BSN.cpow_neg_s_mk qz154 83585 1000 12 qz155 rfl)

noncomputable def ep678 := @Enclosure.Real.IsNear.mulLit_ff qz154 qz61 83585 1000 0 1 11191020447815397 4503599627370496 10000000002457 819000000000000000 187080288826129991649 900719925474099200 167170000041073669 163800000000000000000 qz156 (BSN.isNear_log_sfrac 12 1 11191020447815397 4503599627370496 10000000002457 819000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz330) Bool.false 23469270914176955449344 9444732965739290427392 1000000000245700 81900000000000000000 11191020447815397 4503599627370496 10000000002457 819000000000000000 (BSN.log_rat_reduce_isNear 12 1 3 24 16 106290 262144 24973259072661432 36028797018963968 81900 1000000000000000 rfl rfl rfl rfl (ep219 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep679 := nat_lit 21285064593277628350543346908500625

noncomputable def ep680 := BSN.cos_dyadic_bound_f 381960755 1073741824 2 1 524288 163960 ep679 ep112 ep679 ep679 ep113 ep679 491463 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 381960755) qz285 0 1 ep679 ep112 ep679 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 381960755) qz286 0 1 ep679 ep113 ep679 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz413 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 27223765) (@Nat.cast Real Real.instNatCast 131072))

noncomputable def ep681 := @Enclosure.Real.IsNear.cos_image qz174 qz413 Bool.false 27223765 131072 67 65536 Bool.false 491463 524288 1 81900 (@Enclosure.Real.IsNear.recentre' qz174 Bool.false 187080288826129991649 900719925474099200 167170000041073669 163800000000000000000 27223765 131072 67 65536 (ep678 rfl) rfl) (Enclosure.sfrac_false_div 27223765 131072) (BSN.cos_reduce0 qz413 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 6719524670428424437760) qz314) 226375608064910080 72057594037927936 Bool.false 491463 524288 33 1000000000000000 163800 81900 (BSN.sin_reduce_arg_pos_rat_q0 27223765 131072 226375608064910080 72057594037927936 33 6719524670428424437760 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 491463 524288 6719524670428424437760 18889465931478580854784 381960755 1073741824 163960 163800 (ep680 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep682 := BSN.sin_dyadic_bound_f 381960755 1073741824 2 1 524288 163960 ep679 ep108 ep679 ep679 ep109 ep679 182595 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 381960755) qz281 0 1 ep679 ep108 ep679 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 381960755) qz282 0 1 ep679 ep109 ep679 rfl rfl rfl rfl) rfl rfl

noncomputable def ep683 := @Enclosure.Real.IsNear.sin_image qz174 qz413 Bool.false 27223765 131072 67 65536 Bool.false 182595 524288 1 81900 (@Enclosure.Real.IsNear.recentre' qz174 Bool.false 187080288826129991649 900719925474099200 167170000041073669 163800000000000000000 27223765 131072 67 65536 (ep678 rfl) rfl) (Enclosure.sfrac_false_div 27223765 131072) (BSN.sin_reduce0 qz413 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 6719524670428424437760) qz314) 226375608064910080 72057594037927936 Bool.false 182595 524288 33 1000000000000000 163800 81900 (BSN.sin_reduce_arg_pos_rat_q0 27223765 131072 226375608064910080 72057594037927936 33 6719524670428424437760 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 182595 524288 6719524670428424437760 18889465931478580854784 381960755 1073741824 163960 163800 (ep682 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep684 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz59 (Real.cos qz174)) (@HMul.hMul Real Real Real qz0 qz59 (@Neg.neg Real Real.instNeg (Real.sin qz174))) Bool.false 74382433587 274877906944 22545415495 75041668595712 Bool.true 27635570655 274877906944 22461094531 75041668595712 (@Enclosure.Real.IsNear.mulLit_ff qz59 (Real.cos qz174) 151349 524288 1 524288 491463 524288 1388209 1341849600 74382433587 274877906944 22545415495 75041668595712 qz332 (@Enclosure.Real.IsNear.recentre' (Real.cos qz174) Bool.false 491463 524288 5552836 5367398400 491463 524288 1388209 1341849600 (ep681 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz59 (@Neg.neg Real Real.instNeg (Real.sin qz174)) 151349 524288 1 524288 182595 524288 1388209 1341849600 27635570655 274877906944 22461094531 75041668595712 qz332 (@Enclosure.Real.IsNear.neg (Real.sin qz174) Bool.false 182595 524288 1388209 1341849600 (@Enclosure.Real.IsNear.recentre' (Real.sin qz174) Bool.false 182595 524288 5552836 5367398400 182595 524288 1388209 1341849600 (ep683 rfl rfl) rfl)) rfl)

noncomputable def ep685 := @ep632 74382433587 274877906944 22545415495 75041668595712 Bool.true 27635570655 274877906944 22461094531 75041668595712 Bool.false 37935000686363500609536 4312710267 8589934592 13470502799197 2814062572339200 Bool.false 11140403811862634823680 20264276485 137438953472 6738546922511 1407031286169600 (ep633 (BSN.head_sum_c_succ qz145 11 12 rfl rfl) (ep676 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep677 ep684) rfl rfl

noncomputable abbrev qz175 := (@HMul.hMul Real Real Real qz265 qz401 (Real.log (Enclosure.sfrac Bool.false 13 1)))

noncomputable def ep686 := @Enclosure.Complex.IsNear.of_eq qz166 (Complex.mk (@HMul.hMul Real Real Real qz0 qz62 (Real.cos qz175)) (@HMul.hMul Real Real Real qz0 qz62 (@Neg.neg Real Real.instNeg (Real.sin qz175)))) Bool.false 55118184961 274877906944 1622659046089 5628125144678400 Bool.true 13167402283 68719476736 405578566891 1407031286169600 (BSN.cpow_neg_s_mk qz154 83585 1000 13 qz155 rfl)

noncomputable def ep687 := @Enclosure.Real.IsNear.mulLit_ff qz154 qz64 83585 1000 0 1 11551488463034085 4503599627370496 10000000002457 819000000000000000 38621246527308159789 180143985094819840 167170000041073669 163800000000000000000 qz156 (BSN.isNear_log_sfrac 13 1 11551488463034085 4503599627370496 10000000002457 819000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz334) Bool.false 24225227133228857425920 9444732965739290427392 1000000000245700 81900000000000000000 11551488463034085 4503599627370496 10000000002457 819000000000000000 (BSN.log_rat_reduce_isNear 13 1 3 26 16 127272 262144 24973259072661432 36028797018963968 81900 1000000000000000 rfl rfl rfl rfl (ep230 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep688 := nat_lit 1004561717052675922365480935219751148403079421382059584559443754301827413121

noncomputable def ep689 := nat_lit 202283660148735913840490160679147191336763798899528846192455367011955841

noncomputable def ep690 := nat_lit 3013280583837730295268761825337895150826564736548379695985946352171458327681

noncomputable def ep691 := BSN.cos_dyadic_bound_f 818926831 1073741824 3 2 524288 163960 ep688 ep64 ep689 ep690 ep66 ep689 379051 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 818926831) qz285 0 2 ep688 ep64 ep689 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 818926831) qz286 0 2 ep690 ep66 ep689 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz414 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 112402621) qz19)

noncomputable def ep692 := @Enclosure.Real.IsNear.cos_image qz175 qz414 Bool.false 112402621 524288 67 65536 Bool.false 379051 524288 1 81900 (@Enclosure.Real.IsNear.recentre' qz175 Bool.false 38621246527308159789 180143985094819840 167170000041073669 163800000000000000000 112402621 524288 67 65536 (ep687 rfl) rfl) (Enclosure.sfrac_false_div 112402621 524288) (BSN.cos_reduce0 qz414 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 57626852679708491907072) qz22) 226375608064910080 72057594037927936 Bool.false 379051 524288 34 1000000000000000 163800 81900 (BSN.sin_reduce_arg_pos_rat_q0 112402621 524288 226375608064910080 72057594037927936 34 57626852679708491907072 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 379051 524288 57626852679708491907072 75557863725914323419136 818926831 1073741824 163960 163800 (ep691 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep693 := nat_lit 449759558151614954470298401373958721

noncomputable def ep694 := BSN.sin_dyadic_bound_f 818926831 1073741824 2 1 524288 163960 ep693 ep108 ep693 ep693 ep109 ep693 362212 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 818926831) qz281 0 1 ep693 ep108 ep693 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 818926831) qz282 0 1 ep693 ep109 ep693 rfl rfl rfl rfl) rfl rfl

noncomputable def ep695 := @Enclosure.Real.IsNear.sin_image qz175 qz414 Bool.false 112402621 524288 67 65536 Bool.false 362212 524288 1 81900 (@Enclosure.Real.IsNear.recentre' qz175 Bool.false 38621246527308159789 180143985094819840 167170000041073669 163800000000000000000 112402621 524288 67 65536 (ep687 rfl) rfl) (Enclosure.sfrac_false_div 112402621 524288) (BSN.sin_reduce0 qz414 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 57626852679708491907072) qz22) 226375608064910080 72057594037927936 Bool.false 362212 524288 34 1000000000000000 163800 81900 (BSN.sin_reduce_arg_pos_rat_q0 112402621 524288 226375608064910080 72057594037927936 34 57626852679708491907072 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 362212 524288 57626852679708491907072 75557863725914323419136 818926831 1073741824 163960 163800 (ep694 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep696 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz62 (Real.cos qz175)) (@HMul.hMul Real Real Real qz0 qz62 (@Neg.neg Real Real.instNeg (Real.sin qz175))) Bool.false 55118184961 274877906944 1622659046089 5628125144678400 Bool.true 13167402283 68719476736 405578566891 1407031286169600 (@Enclosure.Real.IsNear.mulLit_ff qz62 (Real.cos qz175) 145411 524288 1 524288 379051 524288 1388209 1341849600 55118184961 274877906944 1622659046089 5628125144678400 qz336 (@Enclosure.Real.IsNear.recentre' (Real.cos qz175) Bool.false 379051 524288 5552836 5367398400 379051 524288 1388209 1341849600 (ep692 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz62 (@Neg.neg Real Real.instNeg (Real.sin qz175)) 145411 524288 1 524288 90553 131072 1388209 1341849600 13167402283 68719476736 405578566891 1407031286169600 qz336 (@Enclosure.Real.IsNear.neg (Real.sin qz175) Bool.false 90553 131072 1388209 1341849600 (@Enclosure.Real.IsNear.recentre' (Real.sin qz175) Bool.false 362212 524288 5552836 5367398400 90553 131072 1388209 1341849600 (ep695 rfl rfl) rfl)) rfl)

noncomputable def ep697 := @ep630 55118184961 274877906944 1622659046089 5628125144678400 Bool.true 13167402283 68719476736 405578566891 1407031286169600 Bool.false 1658930375093607464960 193124913505 274877906944 9521221548161 1876041714892800 Bool.true 417163513237514223616 6070528081 137438953472 1190687581567 234505214361600 (ep631 (BSN.head_sum_c_succ qz145 12 13 rfl rfl) (ep685 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep686 ep696) rfl rfl

noncomputable abbrev qz176 := (@HMul.hMul Real Real Real qz265 qz401 (Real.log (Enclosure.sfrac Bool.false 14 1)))

noncomputable def ep698 := @Enclosure.Complex.IsNear.of_eq qz165 (Complex.mk (@HMul.hMul Real Real Real qz0 qz65 (Real.cos qz176)) (@HMul.hMul Real Real Real qz0 qz65 (@Neg.neg Real Real.instNeg (Real.sin qz176)))) Bool.false 57407433579 274877906944 1564537559009 5628125144678400 Bool.true 45839884545 274877906944 1562847265859 5628125144678400 (BSN.cpow_neg_s_mk qz154 83585 1000 14 qz155 rfl)

noncomputable def ep699 := @Enclosure.Real.IsNear.mulLit_ff qz154 qz67 83585 1000 0 1 11885241781671653 4503599627370496 10000000002457 819000000000000000 198685586864205023201 900719925474099200 167170000041073669 163800000000000000000 qz156 (BSN.isNear_log_sfrac 14 1 11885241781671653 4503599627370496 10000000002457 819000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz338) Bool.false 24925158572916270432256 9444732965739290427392 1000000000245700 81900000000000000000 11885241781671653 4503599627370496 10000000002457 819000000000000000 (BSN.log_rat_reduce_isNear 14 1 3 28 16 146699 262144 24973259072661432 36028797018963968 81900 1000000000000000 rfl rfl rfl rfl (ep244 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep700 := nat_lit 274025445378500067617007087228660496

noncomputable def ep701 := BSN.cos_dyadic_bound_f 723515306 1073741824 2 1 524288 163960 ep700 ep112 ep700 ep700 ep113 ep700 409699 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 723515306) qz285 0 1 ep700 ep112 ep700 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 723515306) qz286 0 1 ep700 ep113 ep700 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz415 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 14456279) qz484)

noncomputable def ep702 := @Enclosure.Real.IsNear.cos_image qz176 qz415 Bool.false 14456279 65536 67 65536 Bool.false 409699 524288 1 81900 (@Enclosure.Real.IsNear.recentre' qz176 Bool.false 198685586864205023201 900719925474099200 167170000041073669 163800000000000000000 14456279 65536 67 65536 (ep699 rfl) rfl) (Enclosure.sfrac_false_div 14456279 65536) (BSN.cos_reduce0 qz415 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 6364107942173069017088) qz301) 226375608064910080 72057594037927936 Bool.false 409699 524288 35 1000000000000000 163800 81900 (BSN.sin_reduce_arg_pos_rat_q0 14456279 65536 226375608064910080 72057594037927936 35 6364107942173069017088 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 409699 524288 6364107942173069017088 9444732965739290427392 723515306 1073741824 163960 163800 (ep701 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep703 := BSN.sin_dyadic_bound_f 723515306 1073741824 2 1 524288 163960 ep700 ep108 ep700 ep700 ep109 ep700 327145 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 723515306) qz281 0 1 ep700 ep108 ep700 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 723515306) qz282 0 1 ep700 ep109 ep700 rfl rfl rfl rfl) rfl rfl

noncomputable def ep704 := @Enclosure.Real.IsNear.sin_image qz176 qz415 Bool.false 14456279 65536 67 65536 Bool.false 327145 524288 1 81900 (@Enclosure.Real.IsNear.recentre' qz176 Bool.false 198685586864205023201 900719925474099200 167170000041073669 163800000000000000000 14456279 65536 67 65536 (ep699 rfl) rfl) (Enclosure.sfrac_false_div 14456279 65536) (BSN.sin_reduce0 qz415 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 6364107942173069017088) qz301) 226375608064910080 72057594037927936 Bool.false 327145 524288 35 1000000000000000 163800 81900 (BSN.sin_reduce_arg_pos_rat_q0 14456279 65536 226375608064910080 72057594037927936 35 6364107942173069017088 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 327145 524288 6364107942173069017088 9444732965739290427392 723515306 1073741824 163960 163800 (ep703 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep705 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz65 (Real.cos qz176)) (@HMul.hMul Real Real Real qz0 qz65 (@Neg.neg Real Real.instNeg (Real.sin qz176))) Bool.false 57407433579 274877906944 1564537559009 5628125144678400 Bool.true 45839884545 274877906944 1562847265859 5628125144678400 (@Enclosure.Real.IsNear.mulLit_ff qz65 (Real.cos qz176) 140121 524288 1 524288 409699 524288 1388209 1341849600 57407433579 274877906944 1564537559009 5628125144678400 qz340 (@Enclosure.Real.IsNear.recentre' (Real.cos qz176) Bool.false 409699 524288 5552836 5367398400 409699 524288 1388209 1341849600 (ep702 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz65 (@Neg.neg Real Real.instNeg (Real.sin qz176)) 140121 524288 1 524288 327145 524288 1388209 1341849600 45839884545 274877906944 1562847265859 5628125144678400 qz340 (@Enclosure.Real.IsNear.neg (Real.sin qz176) Bool.false 327145 524288 1388209 1341849600 (@Enclosure.Real.IsNear.recentre' (Real.sin qz176) Bool.false 327145 524288 5552836 5367398400 327145 524288 1388209 1341849600 (ep704 rfl rfl) rfl)) rfl)

noncomputable def ep706 := @ep628 57407433579 274877906944 1564537559009 5628125144678400 Bool.true 45839884545 274877906944 1562847265859 5628125144678400 Bool.false 68865807188217661751296 62633086771 68719476736 7532050550873 1407031286169600 Bool.true 7968839812092163784704 57980940707 274877906944 30139349223467 5628125144678400 (ep629 (BSN.head_sum_c_succ qz145 13 14 rfl rfl) (ep697 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep698 ep705) rfl rfl

noncomputable abbrev qz177 := (@HMul.hMul Real Real Real qz265 qz401 (Real.log (Enclosure.sfrac Bool.false 15 1)))

noncomputable def ep707 := @Enclosure.Complex.IsNear.of_eq qz164 (Complex.mk (@HMul.hMul Real Real Real qz0 qz68 (Real.cos qz177)) (@HMul.hMul Real Real Real qz0 qz68 (@Neg.neg Real Real.instNeg (Real.sin qz177)))) Bool.false 70096051397 274877906944 504666376103 1876041714892800 Bool.true 43454091 1073741824 15677912329 58626303590400 (BSN.cpow_neg_s_mk qz154 83585 1000 15 qz155 rfl)

noncomputable def ep708 := @Enclosure.Real.IsNear.mulLit_ff qz154 qz70 83585 1000 0 1 12195956895733477 4503599627370496 10000000002457 819000000000000000 203879811425976535009 900719925474099200 167170000041073669 163800000000000000000 qz156 (BSN.isNear_log_sfrac 15 1 12195956895733477 4503599627370496 10000000002457 819000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz342) Bool.false 25576775395801252757504 9444732965739290427392 1000000000245700 81900000000000000000 12195956895733477 4503599627370496 10000000002457 819000000000000000 (BSN.log_rat_reduce_isNear 15 1 3 30 16 164785 262144 24973259072661432 36028797018963968 81900 1000000000000000 rfl rfl rfl rfl (ep255 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep709 := nat_lit 815642490510377253696911048010000

noncomputable def ep710 := BSN.cos_dyadic_bound_f 168995430 1073741824 2 1 524288 163960 ep709 ep112 ep709 ep709 ep113 ep709 517807 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 168995430) qz285 0 1 ep709 ep112 ep709 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 168995430) qz286 0 1 ep709 ep113 ep709 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz416 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 118673669) qz19)

noncomputable def ep711 := @Enclosure.Real.IsNear.cos_image qz177 qz416 Bool.false 118673669 524288 67 65536 Bool.false 517807 524288 1 81900 (@Enclosure.Real.IsNear.recentre' qz177 Bool.false 203879811425976535009 900719925474099200 167170000041073669 163800000000000000000 118673669 524288 67 65536 (ep708 rfl) rfl) (Enclosure.sfrac_false_div 118673669 524288) (BSN.cos_reduce0 qz416 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 11891996223343698116608) qz22) 226375608064910080 72057594037927936 Bool.false 517807 524288 36 1000000000000000 163800 81900 (BSN.sin_reduce_arg_pos_rat_q0 118673669 524288 226375608064910080 72057594037927936 36 11891996223343698116608 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 517807 524288 11891996223343698116608 75557863725914323419136 168995430 1073741824 163960 163800 (ep710 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep712 := BSN.sin_dyadic_bound_f 168995430 1073741824 1 0 524288 163960 0 1 1 0 1 1 82176 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 168995430) qz281 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 168995430) qz282 0 0 rfl) rfl rfl

noncomputable def ep713 := @Enclosure.Real.IsNear.sin_image qz177 qz416 Bool.false 118673669 524288 67 65536 Bool.false 82176 524288 1 81900 (@Enclosure.Real.IsNear.recentre' qz177 Bool.false 203879811425976535009 900719925474099200 167170000041073669 163800000000000000000 118673669 524288 67 65536 (ep708 rfl) rfl) (Enclosure.sfrac_false_div 118673669 524288) (BSN.sin_reduce0 qz416 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 11891996223343698116608) qz22) 226375608064910080 72057594037927936 Bool.false 82176 524288 36 1000000000000000 163800 81900 (BSN.sin_reduce_arg_pos_rat_q0 118673669 524288 226375608064910080 72057594037927936 36 11891996223343698116608 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 82176 524288 11891996223343698116608 75557863725914323419136 168995430 1073741824 163960 163800 (ep712 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep714 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz68 (Real.cos qz177)) (@HMul.hMul Real Real Real qz0 qz68 (@Neg.neg Real Real.instNeg (Real.sin qz177))) Bool.false 70096051397 274877906944 504666376103 1876041714892800 Bool.true 43454091 1073741824 15677912329 58626303590400 (@Enclosure.Real.IsNear.mulLit_ff qz68 (Real.cos qz177) 135371 524288 1 524288 517807 524288 1388209 1341849600 70096051397 274877906944 504666376103 1876041714892800 qz344 (@Enclosure.Real.IsNear.recentre' (Real.cos qz177) Bool.false 517807 524288 5552836 5367398400 517807 524288 1388209 1341849600 (ep711 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz68 (@Neg.neg Real Real.instNeg (Real.sin qz177)) 135371 524288 1 524288 321 2048 1388209 1341849600 43454091 1073741824 15677912329 58626303590400 qz344 (@Enclosure.Real.IsNear.neg (Real.sin qz177) Bool.false 321 2048 1388209 1341849600 (@Enclosure.Real.IsNear.recentre' (Real.sin qz177) Bool.false 82176 524288 5552836 5367398400 321 2048 1388209 1341849600 (ep713 rfl rfl) rfl)) rfl)

noncomputable def ep715 := @ep626 70096051397 274877906944 504666376103 1876041714892800 Bool.true 43454091 1073741824 15677912329 58626303590400 Bool.false 22033415770316017238016 320628398481 274877906944 31642201331801 5628125144678400 Bool.true 74201130614204137472 69105188003 274877906944 31644428807051 5628125144678400 (ep627 (BSN.head_sum_c_succ qz145 14 15 rfl rfl) (ep706 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep707 ep714) rfl rfl

noncomputable abbrev qz178 := (@HMul.hMul Real Real Real qz265 qz401 (Real.log (Enclosure.sfrac Bool.false 16 1)))

noncomputable def ep716 := @Enclosure.Complex.IsNear.of_eq qz163 (Complex.mk (@HMul.hMul Real Real Real qz0 qz71 (Real.cos qz178)) (@HMul.hMul Real Real Real qz0 qz71 (@Neg.neg Real Real.instNeg (Real.sin qz178)))) Bool.false 51160288075 274877906944 1463634544759 5628125144678400 Bool.false 45879175343 274877906944 1462809566059 5628125144678400 (BSN.cpow_neg_s_mk qz154 83585 1000 16 qz155 rfl)

noncomputable def ep717 := @Enclosure.Real.IsNear.mulLit_ff qz154 qz73 83585 1000 0 1 3121657384082679 1125899906842624 2500000000819 204750000000000000 52184746489710144843 225179981368524800 41792500013691223 40950000000000000000 qz156 (BSN.isNear_log_sfrac 16 1 3121657384082679 1125899906842624 2500000000819 204750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz346) Bool.false 26186360105375033720832 9444732965739290427392 1000000000327600 81900000000000000000 3121657384082679 1125899906842624 2500000000819 204750000000000000 (BSN.log_rat_reduce_isNear 16 1 4 32 32 0 262144 24973259072661432 36028797018963968 81900 1000000000000000 rfl rfl rfl rfl (ep270 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep718 := nat_lit 661053864416683223319411272814239121

noncomputable def ep719 := BSN.sin_dyadic_bound_f 901694067 1073741824 2 1 524288 163960 ep718 ep108 ep718 ep718 ep109 ep718 390325 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 901694067) qz281 0 1 ep718 ep108 ep718 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 901694067) qz282 0 1 ep718 ep109 ep718 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz417 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 121502081) qz19)

noncomputable def ep720 := @Enclosure.Real.IsNear.cos_image qz178 qz417 Bool.false 121502081 524288 67 65536 Bool.false 390325 524288 1 81900 (@Enclosure.Real.IsNear.recentre' qz178 Bool.false 52184746489710144843 225179981368524800 41792500013691223 40950000000000000000 121502081 524288 67 65536 (ep717 rfl) rfl) (Enclosure.sfrac_false_div 121502081 524288) (BSN.cos_reduce3 qz417 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 63451079155944628682752) qz22) 226375608064910080 72057594037927936 Bool.false 390325 524288 36 1000000000000000 163800 81900 (BSN.sin_reduce_arg_pos_rat_q3 121502081 524288 226375608064910080 72057594037927936 36 63451079155944628682752 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 390325 524288 63451079155944628682752 75557863725914323419136 901694067 1073741824 163960 163800 (ep719 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep721 := nat_lit 1476638381763155309539383097034568956144002823987620253667698250444287781921

noncomputable def ep722 := nat_lit 436992211660230605852168364793876216653589523662746257364529170166852641

noncomputable def ep723 := nat_lit 4429041160866145467406444954374119115998701292915535268488365692992529640481

noncomputable def ep724 := BSN.cos_dyadic_bound_f 901694067 1073741824 3 2 524288 163960 ep721 ep64 ep722 ep723 ep66 ep722 350033 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 901694067) qz285 0 2 ep721 ep64 ep722 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 901694067) qz286 0 2 ep723 ep66 ep722 rfl rfl rfl rfl) rfl rfl

noncomputable def ep725 := @Enclosure.Real.IsNear.sin_image qz178 qz417 Bool.false 121502081 524288 67 65536 Bool.true 350033 524288 1 81900 (@Enclosure.Real.IsNear.recentre' qz178 Bool.false 52184746489710144843 225179981368524800 41792500013691223 40950000000000000000 121502081 524288 67 65536 (ep717 rfl) rfl) (Enclosure.sfrac_false_div 121502081 524288) (BSN.sin_reduce3 qz417 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 63451079155944628682752) qz22) 226375608064910080 72057594037927936 Bool.false 350033 524288 36 1000000000000000 163800 81900 (BSN.sin_reduce_arg_pos_rat_q3 121502081 524288 226375608064910080 72057594037927936 36 63451079155944628682752 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 350033 524288 63451079155944628682752 75557863725914323419136 901694067 1073741824 163960 163800 (ep724 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep726 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz71 (Real.cos qz178)) (@HMul.hMul Real Real Real qz0 qz71 (@Neg.neg Real Real.instNeg (Real.sin qz178))) Bool.false 51160288075 274877906944 1463634544759 5628125144678400 Bool.false 45879175343 274877906944 1462809566059 5628125144678400 (@Enclosure.Real.IsNear.mulLit_ff qz71 (Real.cos qz178) 131071 524288 1 524288 390325 524288 1388209 1341849600 51160288075 274877906944 1463634544759 5628125144678400 qz348 (@Enclosure.Real.IsNear.recentre' (Real.cos qz178) Bool.false 390325 524288 5552836 5367398400 390325 524288 1388209 1341849600 (ep720 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz71 (@Neg.neg Real Real.instNeg (Real.sin qz178)) 131071 524288 1 524288 350033 524288 1388209 1341849600 45879175343 274877906944 1462809566059 5628125144678400 qz348 (@Enclosure.Real.IsNear.neg (Real.sin qz178) Bool.true 350033 524288 1388209 1341849600 (@Enclosure.Real.IsNear.recentre' (Real.sin qz178) Bool.true 350033 524288 5552836 5367398400 350033 524288 1388209 1341849600 (ep725 rfl rfl) rfl)) rfl)

noncomputable def ep727 := @ep624 51160288075 274877906944 1463634544759 5628125144678400 Bool.false 45879175343 274877906944 1462809566059 5628125144678400 Bool.false 102196495985972151844864 92947171639 68719476736 137940982819 23450521436160 Bool.true 6384317746635645911040 5806503165 68719476736 1103574612437 187604171489280 (ep625 (BSN.head_sum_c_succ qz145 15 16 rfl rfl) (ep715 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep716 ep726) rfl rfl

theorem EMRow22.d12 : Enclosure.Complex.IsNear (BSN.headSumC qz145 17) Bool.false 92947171639 68719476736 137940982819 23450521436160 Bool.true 5806503165 68719476736 1103574612437 187604171489280 := ep623 (BSN.head_sum_c_succ qz145 16 17 rfl rfl) (ep727 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable def ep728 := nat_lit 2072695048567701865094778988651

noncomputable def ep729 := nat_lit 1643244325263349125560559206400

noncomputable def ep730 := nat_lit 920520572416315050642451002436702373

noncomputable def ep731 := nat_lit 137778025857246165351265781730508800000

noncomputable abbrev qz497 := (@HAdd.hAdd Complex Complex Complex qz503 (@HAdd.hAdd Complex Complex Complex qz503 qz506 (@HMul.hMul Complex Complex Complex qz505 Complex.I (@HDiv.hDiv Complex Complex Complex qz507 (↑qz510) (2 : Complex)))) (@Nat.cast Complex Complex.instNatCast 2))

noncomputable abbrev qz418 := qz497

noncomputable abbrev qz179 := (Complex.Stirling.logGammaStirling 1 qz418)

noncomputable abbrev qz498 := (@HAdd.hAdd Complex Complex Complex qz503 qz506 (@HMul.hMul Complex Complex Complex qz505 Complex.I (@HDiv.hDiv Complex Complex Complex qz507 (↑qz510) (2 : Complex))))

noncomputable abbrev qz419 := qz498

noncomputable abbrev qz180 := qz419

noncomputable abbrev qz181 := (@HMul.hMul Real Real Real qz265 (@HDiv.hDiv Real Real Real qz268 qz401 (2 : Real)) (Real.log Real.pi))

noncomputable def ep732 := Complex.re (@HMul.hMul Complex Complex Complex qz74 (Complex.exp (@HMul.hMul Complex Complex Complex qz74 Complex.I ↑(@HSub.hSub Real Real Real qz353 (Complex.im (@HSub.hSub Complex Complex Complex qz75 qz179 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz180 (@Nat.cast Complex Complex.instNatCast j))))) qz181))) (zetaApproximant qz145 1 17))

noncomputable def ep733 := @Enclosure.Real.IsNear.of_eq ep732 (@HSub.hSub Real Real Real qz353 (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz353 (Complex.im (@HSub.hSub Complex Complex Complex qz75 qz179 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz180 (@Nat.cast Complex Complex.instNatCast j))))) qz181)) (Complex.re (zetaApproximant qz145 1 17))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz353 (Complex.im (@HSub.hSub Complex Complex Complex qz75 qz179 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz180 (@Nat.cast Complex Complex.instNatCast j))))) qz181)) (Complex.im (zetaApproximant qz145 1 17))))

noncomputable def ep734 := nat_lit 2072695878181471927696679332307

noncomputable def ep735 := @Enclosure.Real.IsNear.subLit_tt_n (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz353 (Complex.im (@HSub.hSub Complex Complex Complex qz75 qz179 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz180 (@Nat.cast Complex Complex.instNatCast j))))) qz181)) (Complex.re (zetaApproximant qz145 1 17))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz353 (Complex.im (@HSub.hSub Complex Complex Complex qz75 qz179 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz180 (@Nat.cast Complex Complex.instNatCast j))))) qz181)) (Complex.im (zetaApproximant qz145 1 17))) ep734

noncomputable def ep736 := nat_lit 919397607969662007395578059103915549

noncomputable def ep737 := nat_lit 205405540657918640695069900800

noncomputable def ep738 := nat_lit 140370555831630405859117916598353

noncomputable def ep739 := nat_lit 17222253232155770668908222716313600000

noncomputable def ep740 := nat_lit 425743047070039737087864530149736707309244368879574895820800

noncomputable def ep741 := @Enclosure.Real.IsNear.mulLit_tf (Real.cos (@HSub.hSub Real Real Real qz353 (Complex.im (@HSub.hSub Complex Complex Complex qz75 qz179 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz180 (@Nat.cast Complex Complex.instNatCast j))))) qz181)) (Complex.re (zetaApproximant qz145 1 17)) 524287 524288 5188397

noncomputable def ep742 := nat_lit 3953361189923595144828461

noncomputable def ep743 := nat_lit 3134239817167948008652800

noncomputable def ep744 := nat_lit 77784480447170964292999547

noncomputable def ep745 := nat_lit 12834712051302747095433216000

noncomputable def ep746 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HSub.hSub Real Real Real qz353 (Complex.im (@HSub.hSub Complex Complex Complex qz75 qz179 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz180 (@Nat.cast Complex Complex.instNatCast j))))) qz181)) Bool.true 524287 524288 20753588

noncomputable abbrev qz420 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 4323639) qz484)

noncomputable def ep747 := @Enclosure.Real.IsNear.cos_image (@HSub.hSub Real Real Real qz353 (Complex.im (@HSub.hSub Complex Complex Complex qz75 qz179 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz180 (@Nat.cast Complex Complex.instNatCast j))))) qz181) qz420 Bool.false 4323639 65536 247

noncomputable def ep748 := nat_lit 8587837440000000000000000

noncomputable def ep749 := @Enclosure.Real.IsNear.recentre' (@HSub.hSub Real Real Real qz353 (Complex.im (@HSub.hSub Complex Complex Complex qz75 qz179 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz180 (@Nat.cast Complex Complex.instNatCast j))))) qz181) Bool.false 356541852329732050757 5404319552844595200 4030445768675140129381 ep748

noncomputable def ep750 := @Enclosure.Real.IsNear.subLit_ff_p (Complex.im (@HSub.hSub Complex Complex Complex qz75 qz179 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz180 (@Nat.cast Complex Complex.instNatCast j))))) qz181 615090511523800780613 5404319552844595200 1292201168675140129381 ep748 1254126057 26214400

noncomputable def ep751 := nat_lit 9346530733712527871364300800

noncomputable def ep752 := nat_lit 10734796800000000000000000

noncomputable def ep753 := @Enclosure.Complex.IsNear.im_isNear (@HSub.hSub Complex Complex Complex qz75 qz179 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz180 (@Nat.cast Complex Complex.instNatCast j)))) Bool.true 29571422644947144361 450359962737049600 2902745154967830765757 ep752 Bool.false 615090511523800780613 5404319552844595200

noncomputable def ep754 := nat_lit 3578265600000000000000000

noncomputable def ep755 := @Enclosure.Complex.IsNear.subLitP qz179 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz180 (@Nat.cast Complex Complex.instNatCast j))) Bool.true 26209081306550839761 450359962737049600 945736384953494265919 ep754 Bool.false 631874769509215391813 5404319552844595200 395781189555517430647

noncomputable def ep756 := nat_lit 2862612480000000000000000

noncomputable def ep757 := nat_lit 66588924002299703291588545272086528

noncomputable def ep758 := nat_lit 173132587406107310709283607835312128

noncomputable abbrev qz421 := (@HSub.hSub Complex Complex Complex qz486 qz497 qz489)

noncomputable abbrev qz422 := (Complex.log qz497)

noncomputable abbrev qz182 := (@HSub.hSub Complex Complex Complex qz350 (@HMul.hMul Complex Complex Complex qz349 qz421 qz422) qz418)

noncomputable abbrev qz183 := qz418

noncomputable def ep759 := @Enclosure.Complex.IsNear.of_eq qz179 (@HAdd.hAdd Complex Complex Complex qz4 (@HAdd.hAdd Complex Complex Complex qz4 qz182 qz80) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz75 (@HMul.hMul Complex Complex Complex qz74 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz83 qz183 (@HSub.hSub Int Int Int qz362 qz85 (@HMul.hMul Int Int Int qz363 qz86 (@Nat.cast Int instNatCastInt k)))))) Bool.true 26209081306550839761

noncomputable def ep760 := @Enclosure.Complex.IsNear.addLitP (@HAdd.hAdd Complex Complex Complex qz4 qz182 qz80) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz75 (@HMul.hMul Complex Complex Complex qz74 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz83 qz183 (@HSub.hSub Int Int Int qz362 qz85 (@HMul.hMul Int Int Int qz363 qz86 (@Nat.cast Int instNatCastInt k))))) Bool.true 26209129513180932561 450359962737049600

noncomputable def ep761 := nat_lit 450268588279363229339325825024

noncomputable def ep762 := nat_lit 1085552588083847231382664459059200

noncomputable def ep763 := @ep760 57723129889287241 218400000000000000000 Bool.false 210628504815228514327 1801439850948198400 1006500001527617 7280000000000000000 Bool.false 1838937 17179869184 3 17179869184 Bool.true 10247169943 5153960755200 16717 5153960755200 Bool.true ep761 26209081306550839761 450359962737049600 945736384953494265919 ep754 Bool.false ep762

noncomputable def ep764 := @Enclosure.Complex.IsNear.addLitP qz182 qz80 Bool.true 26622982253901982161 450359962737049600 56890000006474741 218400000000000000000

noncomputable def ep765 := nat_lit 3435283023551651192635392

noncomputable def ep766 := @ep764 Bool.false 210628504815228514327 1801439850948198400 1006500001527617 7280000000000000000 Bool.false 120447 131072 1 262144 Bool.false 0 1 0 1 Bool.true ep765 26209129513180932561 450359962737049600 57723129889287241 218400000000000000000 Bool.false 210628504815228514327 210628504815228514327 1801439850948198400

noncomputable abbrev qz184 := (@HMul.hMul Complex Complex Complex qz349 qz421 qz422)

noncomputable def ep767 := @Enclosure.Complex.IsNear.subLitP qz184 qz183 Bool.true 25609672337743620561 450359962737049600 56890000006474741 218400000000000000000 Bool.false 285915179785981095959

noncomputable def ep768 := @ep767 1801439850948198400 1006500001527617 7280000000000000000 Bool.false 9000 4000 0 1 Bool.false 167170 4000 0 1 Bool.true 106491929015607928644000 26622982253901982161 450359962737049600 56890000006474741 218400000000000000000 Bool.false 842514019260914057308000 210628504815228514327 1801439850948198400 1006500001527617 7280000000000000000

noncomputable abbrev qz185 := qz421

noncomputable abbrev qz186 := qz422

noncomputable def ep769 := @Enclosure.Complex.IsNear.mul qz185 qz186 Bool.true 25609672337743620561 450359962737049600 56890000006474741 218400000000000000000 Bool.false 285915179785981095959 1801439850948198400 1006500001527617

noncomputable abbrev qz187 := (Complex.re qz421)

noncomputable abbrev qz188 := (Complex.re qz422)

noncomputable abbrev qz189 := (Complex.im qz421)

noncomputable abbrev qz190 := (Complex.im qz422)

noncomputable def ep770 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 qz187 qz188) (@HMul.hMul Real Real Real qz0 qz189 qz190) 117720249362216389 18014398509481984 500000000819 93600000000000000 14276339285899515143 225179981368524800

noncomputable def ep771 := nat_lit 230671421594685337485187582380736512

noncomputable def ep772 := @Enclosure.Real.IsNear.mulLit_ff qz187 qz188 7000 4000 0 1 16817178480316627 4503599627370496 500000000819 163800000000000000

noncomputable def ep773 := @Enclosure.Complex.IsNear.re_isNear qz185 Bool.false 7000 4000 0 1 Bool.false 167170 4000 0 1

noncomputable abbrev qz423 := (Enclosure.sfrac Bool.false 167170 4000)

noncomputable abbrev qz191 := qz423

noncomputable def ep774 := @Enclosure.Complex.IsNear.of_eq qz185 (Complex.mk (Enclosure.sfrac Bool.false 7000 4000) qz191) Bool.false 7000 4000 0 1 Bool.false 167170 4000 0

noncomputable abbrev qz424 := (Complex.log (Complex.mk qz95 qz191))

noncomputable def ep775 := @Enclosure.Complex.IsNear.of_eq qz186 qz424 Bool.false 16817178480316627 4503599627370496 500000000819 163800000000000000 Bool.false 854001273308579 562949953421312 10000000000819 1638000000000000000

noncomputable def ep776 := nat_lit 14300172506964333116179481851263979617484300065875644481575260773063865450000000000000000

noncomputable def ep777 := nat_lit 341819219620439595541521268368476787262525335409117734892563401140922640000000000000000

noncomputable def ep778 := nat_lit 35452874446136267297870075375198346372037327994696135701735047985050000000000000000

noncomputable def ep779 := BSN.log_dyadic_bound 11642808900 44410808900 5 4 ep776 524288 163800 ep777 ep778 281467 56053617800 32768000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 11642808900) (BSN.artanhQ 44410808900) 0 4 ep777 ep776 ep778 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz425 := (Real.log (Enclosure.sfrac Bool.false 28026808900 16000000))

noncomputable def ep780 := @Enclosure.Real.IsNear.mulLit_ff qz96 qz425 1 2 0 1 16817178480316627 2251799813685248 500000000819 81900000000000000 16817178480316627 4503599627370496 500000000819 163800000000000000 qz368 (BSN.isNear_log_sfrac 28026808900 16000000 16817178480316627 2251799813685248 500000000819 81900000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 28026808900) qz369)) Bool.false 141072717937411899785216 18889465931478580854784 1000000001638000 163800000000000000000 16817178480316627 2251799813685248 500000000819 81900000000000000 (BSN.log_rat_reduce_isNear 28026808900 16000000 10 56053617800 32768000000 281467 524288 24973259072661432 36028797018963968 163800 1000000000000000 rfl rfl rfl rfl (ep779 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep781 := BSN.arctan_dyadic_bound_f 9000 167170 1 0 524288 163800 0 1 1 0 1 1 28199 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 9000) (BSN.arctanEvenQ 167170) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 9000) (BSN.arctanOddQ 167170) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz426 := (Real.arctan (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 9000) (@Nat.cast Real Real.instNatCast 167170)))

noncomputable def ep782 := @Enclosure.Real.IsNear.subLit_ff_p qz97 qz426 884279719003555 562949953421312 1 2000000000000000 28199 524288 1 163800 447742619580408266752 854001273308579 562949953421312 10000000000819 1638000000000000000 qz98 (ep781 rfl) rfl rfl

noncomputable abbrev qz427 := (Complex.mk qz95 qz191)

noncomputable abbrev qz428 := (Real.arctan (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 167170) (@Nat.cast Real Real.instNatCast 9000)))

noncomputable def ep783 := @Enclosure.Complex.IsNear.re_isNear qz186 Bool.false 16817178480316627 4503599627370496 500000000819 163800000000000000 Bool.false 854001273308579 562949953421312 10000000000819 1638000000000000000 (ep775 (@congrArg Complex Complex qz183 qz427 Complex.log (BSN.w_shift_mk qz154 Bool.false 83585 1000 2 qz155 rfl)) (@Enclosure.Complex.IsNear.of_parts qz424 Bool.false 16817178480316627 4503599627370496 500000000819 163800000000000000 Bool.false 854001273308579 562949953421312 10000000000819 1638000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz424) (@HMul.hMul Real Real Real qz0 qz96 qz425) Bool.false 16817178480316627 4503599627370496 500000000819 163800000000000000 (Enclosure.clog_re_eq 9000 167170 4000 28026808900 16000000 rfl rfl rfl) (ep780 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz424) qz428 Bool.false 854001273308579 562949953421312 10000000000819 1638000000000000000 (Enclosure.clog_im_eq 9000 167170 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz428 (@HSub.hSub Real Real Real qz353 qz97 qz426) Bool.false 854001273308579 562949953421312 10000000000819 1638000000000000000 (BSN.arctan_recip 167170 9000 rfl rfl) ep782))))

noncomputable def ep784 := @Enclosure.Real.IsNear.mulLit_ff qz189 qz190 167170 4000 0 1 854001273308579 562949953421312 10000000000819 1638000000000000000

noncomputable def ep785 := @Enclosure.Complex.IsNear.im_isNear qz185 Bool.false 7000 4000 0 1 Bool.false 167170 4000 0 1

noncomputable def ep786 := @Enclosure.Complex.IsNear.im_isNear qz186 Bool.false 16817178480316627 4503599627370496 500000000819 163800000000000000 Bool.false 854001273308579 562949953421312 10000000000819 1638000000000000000 (ep775 (@congrArg Complex Complex qz183 qz427 Complex.log (BSN.w_shift_mk qz154 Bool.false 83585 1000 2 qz155 rfl)) (@Enclosure.Complex.IsNear.of_parts qz424 Bool.false 16817178480316627 4503599627370496 500000000819 163800000000000000 Bool.false 854001273308579 562949953421312 10000000000819 1638000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz424) (@HMul.hMul Real Real Real qz0 qz96 qz425) Bool.false 16817178480316627 4503599627370496 500000000819 163800000000000000 (Enclosure.clog_re_eq 9000 167170 4000 28026808900 16000000 rfl rfl rfl) (ep780 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz424) qz428 Bool.false 854001273308579 562949953421312 10000000000819 1638000000000000000 (Enclosure.clog_im_eq 9000 167170 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz428 (@HSub.hSub Real Real Real qz353 qz97 qz426) Bool.false 854001273308579 562949953421312 10000000000819 1638000000000000000 (BSN.arctan_recip 167170 9000 rfl rfl) ep782))))

noncomputable abbrev qz429 := (Enclosure.Real.IsNear.const Bool.false 167170 4000)

noncomputable abbrev qz192 := (@ep774 1 (BSN.w_sub_half_mk qz401 Bool.false 83585 1000 2 qz402 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7000 4000) qz423 Bool.false 7000 4000 0 1 Bool.false 167170 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 7000 4000) qz429))

noncomputable def ep787 := @ep770 167170000013691223 655200000000000000000 ep771 25609672337743620561 450359962737049600 56890000006474741 218400000000000000000 (@ep772 117720249362216389 18014398509481984 500000000819 93600000000000000 (ep773 qz192) ep783 rfl) (@ep784 14276339285899515143 225179981368524800 167170000013691223 655200000000000000000 (ep785 qz192) ep786 rfl) rfl

noncomputable def ep788 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz187 qz190) (@HMul.hMul Real Real Real qz0 qz189 qz188) 5978008913160053 2251799813685248 10000000000819 936000000000000000 281132772655453053559 1801439850948198400

noncomputable def ep789 := nat_lit 643823748571856417019995229710712832

noncomputable def ep790 := @Enclosure.Real.IsNear.mulLit_ff qz187 qz190 7000 4000 0 1 854001273308579 562949953421312 10000000000819 1638000000000000000

noncomputable def ep791 := @Enclosure.Real.IsNear.mulLit_ff qz189 qz188 167170 4000 0 1 16817178480316627 4503599627370496 500000000819 163800000000000000

noncomputable def ep792 := @ep788 8358500013691223 65520000000000000000 ep789 285915179785981095959 1801439850948198400 1006500001527617 7280000000000000000 (@ep790 5978008913160053 2251799813685248 10000000000819 936000000000000000 (ep773 qz192) ep786 rfl) (@ep791 281132772655453053559 1801439850948198400 8358500013691223 65520000000000000000 (ep785 qz192) ep783 rfl) rfl

noncomputable def ep793 := @Enclosure.Complex.IsNear.of_eq qz183 qz427 Bool.false 9000 4000 0 1 Bool.false 167170 4000 0 1 (BSN.w_shift_mk qz154 Bool.false 83585 1000 2 qz155 rfl)

noncomputable abbrev qz430 := (ep793 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 9000 4000) (Enclosure.sfrac Bool.false 167170 4000) Bool.false 9000 4000 0 1 Bool.false 167170 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 9000 4000) (Enclosure.Real.IsNear.const Bool.false 167170 4000)))

noncomputable abbrev qz193 := qz430

noncomputable def ep794 := ep768 (@ep769 7280000000000000000 (ep787 rfl) (ep792 rfl)) qz193 rfl rfl rfl rfl rfl rfl

noncomputable def ep795 := @ep766 1006500001527617 7280000000000000000 (ep794 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@Enclosure.Complex.IsNear.mul qz101 (↑qz2) Bool.false 120447 131072 1 262144 Bool.false 0 1 0 1 (@ep348 131072 1 262144 (ep350 rfl) (ep352 rfl) rfl rfl) (@ep353 1 0 1 (ep355 rfl) (ep357 rfl) rfl rfl))

noncomputable abbrev qz431 := (@HPow.hPow Complex Int Complex qz491 qz497 (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) (@OfNat.ofNat Int 1 (@instOfNat 1)) (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (@OfNat.ofNat Int 2 (@instOfNat 2)) (@Nat.cast Int instNatCastInt 1))))

noncomputable abbrev qz194 := qz431

noncomputable def ep796 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz75 (@HMul.hMul Complex Complex Complex qz74 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz83 qz183 (@HSub.hSub Int Int Int qz362 qz85 (@HMul.hMul Int Int Int qz363 qz86 (@Nat.cast Int instNatCastInt k))))) (@HAdd.hAdd Complex Complex Complex qz4 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz75 (@HMul.hMul Complex Complex Complex qz74 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz83 qz183 (@HSub.hSub Int Int Int qz362 qz85 (@HMul.hMul Int Int Int qz363 qz86 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 (@Rat.cast Complex Complex.instRatCast (bernoulli qz103)) qz104) qz194)) Bool.false 1838937 17179869184 3 17179869184

noncomputable def ep797 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz75 (@HMul.hMul Complex Complex Complex qz74 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz83 qz183 (@HSub.hSub Int Int Int qz362 qz85 (@HMul.hMul Int Int Int qz363 qz86 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 (@Rat.cast Complex Complex.instRatCast (bernoulli qz103)) qz104) qz194) Bool.false 0 1 0 1 Bool.false

noncomputable def ep798 := @ep797 0 1 0 1 Bool.false 1838937 17179869184 3 17179869184 Bool.true 10247169943 5153960755200 16717 5153960755200 Bool.false 1838937 1838937 17179869184 3 17179869184 Bool.true 10247169943 10247169943 5153960755200 16717

noncomputable def ep799 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz75 (@HMul.hMul Complex Complex Complex qz74 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz83 qz183 (@HSub.hSub Int Int Int qz362 qz85 (@HMul.hMul Int Int Int qz363 qz86 (@Nat.cast Int instNatCastInt k))))) (Complex.mk qz13 qz13) Bool.false 0 1 0 1 Bool.false

noncomputable def ep800 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz81 (@Rat.cast Complex Complex.instRatCast (bernoulli qz103)) qz104) qz194 Bool.false 1838937 17179869184 3 17179869184 Bool.true 10247169943 5153960755200 16717 5153960755200

noncomputable abbrev qz195 := (Complex.re qz431)

noncomputable abbrev qz196 := (Complex.im qz431)

noncomputable def ep801 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz81 (@Rat.cast Complex Complex.instRatCast (bernoulli qz103)) qz104)) qz195) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz81 (@Rat.cast Complex Complex.instRatCast (bernoulli qz103)) qz104)) qz196) 1838937 17179869184 3 17179869184 0 1 0

noncomputable def ep802 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz81 (@Rat.cast Complex Complex.instRatCast (bernoulli qz103)) qz104)) qz195 1 12 0 1 5516811 4294967296 9 4294967296 1838937

noncomputable def ep803 := @Enclosure.Complex.IsNear.re_isNear qz194 Bool.false 5516811 4294967296 9 4294967296 Bool.true 10247169943 429496729600 16717 429496729600

noncomputable abbrev qz432 := (@HPow.hPow Complex Nat Complex qz492 qz497 1)

noncomputable abbrev qz197 := (@Inv.inv Complex Complex.instInv qz432)

noncomputable def ep804 := @Enclosure.Complex.IsNear.of_eq qz194 qz197 Bool.false 5516811 4294967296 9 4294967296 Bool.true 10247169943 429496729600 16717

noncomputable def ep805 := @Enclosure.Complex.IsNear.of_parts qz197 Bool.false 5516811 4294967296 9 4294967296 Bool.true 10247169943 429496729600 16717

noncomputable abbrev qz198 := (Complex.re qz432)

noncomputable abbrev qz199 := qz432

noncomputable def ep806 := @Enclosure.Real.IsNear.mulLit_ff qz198 (@Inv.inv Real Real.instInv (@DFunLike.coe qz110 Complex (fun (x : Complex) => Real) qz111 Complex.normSq qz199)) 9000 4000 0 1 612979 1073741824 1 1073741824

noncomputable def ep807 := @Enclosure.Complex.IsNear.re_isNear qz199 Bool.false 9000 4000 0 1 Bool.false 167170 4000 0 1

noncomputable def ep808 := @Enclosure.Complex.IsNear.of_eq qz199 qz183 Bool.false 9000 4000 0 1 Bool.false 167170 4000 0

noncomputable def ep809 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (@DFunLike.coe qz110 Complex (fun (x : Complex) => Real) qz111 Complex.normSq qz199)) Bool.false 612979 1073741824 1 1073741824 612979 1073741824 1

noncomputable abbrev qz200 := (Complex.im qz432)

noncomputable def ep810 := @Enclosure.Real.IsNear.of_eq (@DFunLike.coe qz110 Complex (fun (x : Complex) => Real) qz111 Complex.normSq qz199) (@HAdd.hAdd Real Real Real qz378 (@HMul.hMul Real Real Real qz0 qz198 qz198) (@HMul.hMul Real Real Real qz0 qz200 qz200)) Bool.false 280268089 160000 0 1

noncomputable def ep811 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz198 qz198) (@HMul.hMul Real Real Real qz0 qz200 qz200) 81 16 0 1 279458089 160000

noncomputable def ep812 := @Enclosure.Real.IsNear.mulLit_ff qz198 qz198 9000 4000 0 1 9000 4000 0 1

noncomputable def ep813 := @Enclosure.Real.IsNear.mulLit_ff qz200 qz200 167170 4000 0 1 167170 4000 0 1

noncomputable def ep814 := @Enclosure.Complex.IsNear.im_isNear qz199 Bool.false 9000 4000 0 1 Bool.false 167170 4000 0 1

noncomputable abbrev qz201 := (ep807 (@ep808 1 (BSN.pow_one_c qz418) qz430))

noncomputable abbrev qz202 := (ep814 (@ep808 1 (BSN.pow_one_c qz418) qz430))

noncomputable def ep815 := @ep811 0 1 4484289424 280268089 160000 0 1 (@ep812 81 16 0 1 qz201 qz201 rfl) (@ep813 279458089 160000 0 1 qz202 qz202 rfl)

noncomputable def ep816 := @Enclosure.Real.IsNear.inv_image (@DFunLike.coe qz110 Complex (fun (x : Complex) => Real) qz111 Complex.normSq qz199) 280268089 160000 0 1 306489 306490 536870912 (ep810 (Enclosure.Complex.normSq_eq_mul_add_mul qz199) (ep815 rfl rfl)) rfl

noncomputable def ep817 := @Enclosure.Real.IsNear.of_eq (Complex.re qz197) (@HMul.hMul Real Real Real qz0 qz198 (@Inv.inv Real Real.instInv (@DFunLike.coe qz110 Complex (fun (x : Complex) => Real) qz111 Complex.normSq qz199))) Bool.false 5516811 4294967296 9 4294967296 (Enclosure.Complex.inv_re_eq_mul qz199) (@ep806 5516811 4294967296 9 4294967296 qz201 (@ep809 1073741824 (ep816 rfl rfl rfl rfl rfl) rfl) rfl)

noncomputable def ep818 := @Enclosure.Real.IsNear.of_eq (Complex.im qz197) (@HMul.hMul Real Real Real qz0 (@Neg.neg Real Real.instNeg qz200) (@Inv.inv Real Real.instInv (@DFunLike.coe qz110 Complex (fun (x : Complex) => Real) qz111 Complex.normSq qz199))) Bool.true 10247169943 429496729600 16717 429496729600 (Enclosure.Complex.inv_im_eq_mul qz199)

noncomputable def ep819 := @Enclosure.Real.IsNear.mulLit_tf (@Neg.neg Real Real.instNeg qz200) (@Inv.inv Real Real.instInv (@DFunLike.coe qz110 Complex (fun (x : Complex) => Real) qz111 Complex.normSq qz199)) 167170 4000 0 1 612979 1073741824 1

noncomputable def ep820 := @ep819 1073741824 10247169943 429496729600 16717 429496729600 (@Enclosure.Real.IsNear.neg qz200 Bool.false 167170 4000 0 1 qz202) (@ep809 1073741824 (ep816 rfl rfl rfl rfl rfl) rfl) rfl

noncomputable def ep821 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz81 (@Rat.cast Complex Complex.instRatCast (bernoulli qz103)) qz104)) qz196 0 1 0 1 10247169943 429496729600 16717 429496729600 0

noncomputable def ep822 := @Enclosure.Complex.IsNear.im_isNear qz194 Bool.false 5516811 4294967296 9 4294967296 Bool.true 10247169943 429496729600 16717 429496729600

noncomputable abbrev qz203 := (@ep804 429496729600 (BSN.zpow_one_sub_two_mul qz418 1 1 rfl rfl) (@ep805 429496729600 ep817 (ep818 ep820)))

noncomputable def ep823 := @ep801 1 1838937 1838937 17179869184 3 17179869184 (@ep802 17179869184 3 17179869184 ep367 (ep803 qz203) rfl) (@ep821 1 0 1 ep387 (ep822 qz203) rfl) rfl

noncomputable def ep824 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz81 (@Rat.cast Complex Complex.instRatCast (bernoulli qz103)) qz104)) qz196) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz81 (@Rat.cast Complex Complex.instRatCast (bernoulli qz103)) qz104)) qz195) 10247169943 5153960755200 16717 5153960755200 0 1 0

noncomputable def ep825 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HDiv.hDiv Complex Complex Complex qz81 (@Rat.cast Complex Complex.instRatCast (bernoulli qz103)) qz104)) qz196 1 12 0 1 10247169943 429496729600 16717 429496729600 10247169943

noncomputable def ep826 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz81 (@Rat.cast Complex Complex.instRatCast (bernoulli qz103)) qz104)) qz195 0 1 0 1 5516811 4294967296 9 4294967296 0

noncomputable def ep827 := @ep824 1 10247169943 10247169943 5153960755200 16717 5153960755200 (@ep825 5153960755200 16717 5153960755200 ep367 (ep822 qz203) rfl) (@ep826 1 0 1 ep387 (ep803 qz203) rfl) rfl

noncomputable def ep828 := @ep798 5153960755200 (@ep799 0 1 0 1 (BSN.stirling_sum_base qz183) qz117) (ep800 (ep823 rfl) (ep827 rfl)) rfl rfl rfl rfl rfl

noncomputable def ep829 := @ep763 631874769509215391813 5404319552844595200 395781189555517430647 ep756 (ep795 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep796 Bool.true 10247169943 5153960755200 16717 5153960755200 (BSN.stirling_sum_succ qz183 0 1 rfl) (ep828 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl

noncomputable def ep830 := @Enclosure.Complex.IsNear.of_eq (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz180 (@Nat.cast Complex Complex.instNatCast j))) (BSN.logSumC qz154 2) Bool.false 16811706691981523 2251799813685248 500000000819 81900000000000000 Bool.false 874180103407011 281474976710656

noncomputable abbrev qz204 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz271 qz419 qz374))

noncomputable def ep831 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz154 2) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.logSumC qz154 1) qz204) Bool.false 16811706691981523 2251799813685248 500000000819 81900000000000000 Bool.false 874180103407011 281474976710656 10000000000819 819000000000000000

noncomputable def ep832 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz154 1) qz204 Bool.false 16810740324339923 4503599627370496 500000000819 163800000000000000 Bool.false 880912464643491 562949953421312 10000000000819 1638000000000000000 Bool.false

noncomputable def ep833 := nat_lit 151426391986940121912488614690816

noncomputable def ep834 := nat_lit 984239296989629100094195236864

noncomputable abbrev qz205 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz271 qz419 (@Nat.cast Complex Complex.instNatCast 0)))

noncomputable def ep835 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz154 1) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.logSumC qz154 0) qz205) Bool.false 16810740324339923 4503599627370496 500000000819 163800000000000000 Bool.false 880912464643491 562949953421312 10000000000819 1638000000000000000

noncomputable def ep836 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz154 0) qz205 Bool.false 0 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable abbrev qz433 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz191))

noncomputable def ep837 := @Enclosure.Complex.IsNear.of_eq qz205 qz433 Bool.false 16810740324339923 4503599627370496 500000000819 163800000000000000 Bool.false 880912464643491 562949953421312 10000000000819 1638000000000000000

noncomputable def ep838 := nat_lit 14095388669823836586138024775299656045517351461527915768384355499143865450000000000000000

noncomputable def ep839 := nat_lit 333362825269698117172899697813223142879002266584832832104348516276922640000000000000000

noncomputable def ep840 := nat_lit 33550274945131829027863768411693378428465945457122485691460167985050000000000000000

noncomputable def ep841 := BSN.log_dyadic_bound 11562808900 44330808900 5 4 ep838 524288 163800 ep839 ep840 279968 55893617800 32768000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 11562808900) (BSN.artanhQ 44330808900) 0 4 ep839 ep838 ep840 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep842 := @Enclosure.Real.IsNear.mulLit_ff qz96 (Real.log (Enclosure.sfrac Bool.false 27946808900 16000000)) 1 2 0 1 16810740324339923 2251799813685248 500000000819 81900000000000000 16810740324339923 4503599627370496 500000000819 163800000000000000 qz368 (BSN.isNear_log_sfrac 27946808900 16000000 16810740324339923 2251799813685248 500000000819 81900000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 27946808900) qz369)) Bool.false 141018710770680472797184 18889465931478580854784 1000000001638000 163800000000000000000 16810740324339923 2251799813685248 500000000819 81900000000000000 (BSN.log_rat_reduce_isNear 27946808900 16000000 10 55893617800 32768000000 279968 524288 24973259072661432 36028797018963968 163800 1000000000000000 rfl rfl rfl rfl (ep841 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep843 := BSN.arctan_dyadic_bound_f 1000 167170 1 0 524288 163800 0 1 1 0 1 1 3136 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 167170) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 167170) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz434 := (@Nat.cast Real Real.instNatCast 167170)

noncomputable def ep844 := @Enclosure.Real.IsNear.subLit_ff_p qz97 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz380 qz434)) 884279719003555 562949953421312 1 2000000000000000 3136 524288 1 163800 461851834263006609408 880912464643491 562949953421312 10000000000819 1638000000000000000 qz98 (ep843 rfl) rfl rfl

noncomputable abbrev qz206 := (@HAdd.hAdd Complex Complex Complex qz271 qz419 (@Nat.cast Complex Complex.instNatCast 0))

noncomputable abbrev qz435 := (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz191)

noncomputable def ep845 := @ep836 16810740324339923 4503599627370496 500000000819 163800000000000000 Bool.false 880912464643491 562949953421312 10000000000819 1638000000000000000 Bool.false 16810740324339923 16810740324339923 4503599627370496 500000000819 163800000000000000 Bool.false 880912464643491 880912464643491 562949953421312 10000000000819 1638000000000000000 (@Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz154 0) (Complex.mk qz13 qz13) Bool.false 0 1 0 1 Bool.false 0 1 0 1 (BSN.log_sum_c_base qz154) qz117) (ep837 (@congrArg Complex Complex qz206 qz435 Complex.log (BSN.w_shift_mk qz154 Bool.false 83585 1000 0 qz155 rfl)) (@Enclosure.Complex.IsNear.of_parts qz433 Bool.false 16810740324339923 4503599627370496 500000000819 163800000000000000 Bool.false 880912464643491 562949953421312 10000000000819 1638000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz433) (@HMul.hMul Real Real Real qz0 qz96 (Real.log (Enclosure.sfrac Bool.false 27946808900 16000000))) Bool.false 16810740324339923 4503599627370496 500000000819 163800000000000000 (Enclosure.clog_re_eq 1000 167170 4000 27946808900 16000000 rfl rfl rfl) (ep842 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz433) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz434 qz380)) Bool.false 880912464643491 562949953421312 10000000000819 1638000000000000000 (Enclosure.clog_im_eq 1000 167170 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz434 qz380)) (@HSub.hSub Real Real Real qz353 qz97 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz380 qz434))) Bool.false 880912464643491 562949953421312 10000000000819 1638000000000000000 (BSN.arctan_recip 167170 1000 rfl rfl) ep844)))) rfl rfl

noncomputable abbrev qz436 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz191))

noncomputable def ep846 := @Enclosure.Complex.IsNear.of_eq qz204 qz436 Bool.false 16812673059623123 4503599627370496 500000000819 163800000000000000 Bool.false 867447742170531 562949953421312 10000000000819 1638000000000000000

noncomputable def ep847 := nat_lit 14156552638949582707359614872750051365316004364584681501771434441319865450000000000000000

noncomputable def ep848 := nat_lit 335881549761627065314907825512975377213378756030684611026919093736122640000000000000000

noncomputable def ep849 := nat_lit 34111439978709059144563642199638491808555051614854586317582631985050000000000000000

noncomputable def ep850 := BSN.log_dyadic_bound 11586808900 44354808900 5 4 ep847 524288 163800 ep848 ep849 280418 55941617800 32768000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 11586808900) (BSN.artanhQ 44354808900) 0 4 ep848 ep847 ep849 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep851 := @Enclosure.Real.IsNear.mulLit_ff qz96 (Real.log (Enclosure.sfrac Bool.false 27970808900 16000000)) 1 2 0 1 16812673059623123 2251799813685248 500000000819 81900000000000000 16812673059623123 4503599627370496 500000000819 163800000000000000 qz368 (BSN.isNear_log_sfrac 27970808900 16000000 16812673059623123 2251799813685248 500000000819 81900000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 27970808900) qz369)) Bool.false 141034923729339006582784 18889465931478580854784 1000000001638000 163800000000000000000 16812673059623123 2251799813685248 500000000819 81900000000000000 (BSN.log_rat_reduce_isNear 27970808900 16000000 10 55941617800 32768000000 280418 524288 24973259072661432 36028797018963968 163800 1000000000000000 rfl rfl rfl rfl (ep850 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep852 := BSN.arctan_dyadic_bound_f 5000 167170 1 0 524288 163800 0 1 1 0 1 1 15676 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 5000) (BSN.arctanEvenQ 167170) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 5000) (BSN.arctanOddQ 167170) 0 0 rfl) rfl rfl rfl

noncomputable def ep853 := @Enclosure.Real.IsNear.subLit_ff_p qz97 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz384 qz434)) 884279719003555 562949953421312 1 2000000000000000 15676 524288 1 163800 454792441847103356928 867447742170531 562949953421312 10000000000819 1638000000000000000 qz98 (ep852 rfl) rfl rfl

noncomputable abbrev qz207 := (@HAdd.hAdd Complex Complex Complex qz271 qz419 qz374)

noncomputable abbrev qz437 := (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz191)

noncomputable def ep854 := @ep832 16812673059623123 4503599627370496 500000000819 163800000000000000 Bool.false 867447742170531 562949953421312 10000000000819 1638000000000000000 Bool.false ep833 16811706691981523 2251799813685248 500000000819 81900000000000000 Bool.false ep834 874180103407011 281474976710656 10000000000819 819000000000000000 (ep835 (BSN.log_sum_c_succ qz154 0 1 rfl) (ep845 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep846 (@congrArg Complex Complex qz207 qz437 Complex.log (BSN.w_shift_mk qz154 Bool.false 83585 1000 1 qz155 rfl)) (@Enclosure.Complex.IsNear.of_parts qz436 Bool.false 16812673059623123 4503599627370496 500000000819 163800000000000000 Bool.false 867447742170531 562949953421312 10000000000819 1638000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz436) (@HMul.hMul Real Real Real qz0 qz96 (Real.log (Enclosure.sfrac Bool.false 27970808900 16000000))) Bool.false 16812673059623123 4503599627370496 500000000819 163800000000000000 (Enclosure.clog_re_eq 5000 167170 4000 27970808900 16000000 rfl rfl rfl) (ep851 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz436) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz434 qz384)) Bool.false 867447742170531 562949953421312 10000000000819 1638000000000000000 (Enclosure.clog_im_eq 5000 167170 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz434 qz384)) (@HSub.hSub Real Real Real qz353 qz97 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz384 qz434))) Bool.false 867447742170531 562949953421312 10000000000819 1638000000000000000 (BSN.arctan_recip 167170 5000 rfl rfl) ep853)))) rfl rfl

noncomputable def ep855 := @ep755 ep756 Bool.false 16811706691981523 2251799813685248 500000000819 81900000000000000 Bool.false 874180103407011 281474976710656 10000000000819 819000000000000000 Bool.true ep757 29571422644947144361 450359962737049600 2902745154967830765757 ep752 Bool.false ep758 615090511523800780613 5404319552844595200 1292201168675140129381 ep748 (@ep759 450359962737049600 945736384953494265919 ep754 Bool.false 631874769509215391813 5404319552844595200 395781189555517430647 ep756 (BSN.logGammaStirling_unfold 1 qz183) (ep829 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (@ep830 10000000000819 819000000000000000 (BSN.log_sum_c_eq qz154 2) (ep831 (BSN.log_sum_c_succ qz154 1 2 rfl) (ep854 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)))

noncomputable abbrev qz208 := (@HDiv.hDiv Real Real Real qz268 qz401 (2 : Real))

noncomputable def ep856 := @Enclosure.Real.IsNear.mulLit_ff qz208 (Real.log Real.pi) 83585 2000 0 1 75021 65536 1 131072 1254126057 26214400 16717 52428800 (@Enclosure.Real.IsNear.of_eq qz208 (Enclosure.sfrac Bool.false 83585 2000) Bool.false 83585 2000 0 1 (BSN.t_half_eq qz154 Bool.false 83585 1000 qz155) (Enclosure.Real.IsNear.const Bool.false 83585 2000)) EMRow22.d5 rfl

noncomputable def ep857 := @ep750 16717 52428800 ep751 356541852329732050757 5404319552844595200 4030445768675140129381 ep748 (@ep753 1292201168675140129381 ep748 (ep855 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) ep856 rfl rfl

noncomputable def ep858 := BSN.cos_dyadic_bound_f 53427 1073741824 1 0 524288 163960 0 1 1 0 1 1 524287 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 53427) qz285 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 53427) qz286 0 0 rfl) rfl rfl

noncomputable def ep859 := @ep747 524288 Bool.true 524287 524288 1 81900 (@ep749 4323639 65536 247 524288 ep857 rfl) (Enclosure.sfrac_false_div 4323639 65536) (BSN.cos_reduce2 qz420 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 469951143632437248) qz301) 226375608064910080 72057594037927936 Bool.false 524287 524288 10 1000000000000000 163800 81900 (BSN.sin_reduce_arg_pos_rat_q2 4323639 65536 226375608064910080 72057594037927936 10 469951143632437248 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 524287 524288 469951143632437248 9444732965739290427392 53427 1073741824 163960 163800 (ep858 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep860 := nat_lit 19447935091439239435986893

noncomputable def ep861 := nat_lit 3208678012825686773858304000

noncomputable abbrev qz209 := qz400

noncomputable abbrev qz438 := (@HPow.hPow Complex Complex Complex qz479 qz493 qz495)

noncomputable abbrev qz210 := qz438

noncomputable abbrev qz211 := (@HAdd.hAdd Complex Complex Complex qz271 (@HDiv.hDiv Complex Complex Complex qz358 qz387 (@HSub.hSub Complex Complex Complex qz350 qz399 (1 : Complex))) qz357)

noncomputable def ep862 := @Enclosure.Complex.IsNear.of_eq (zetaApproximant qz145 1 17) (@HAdd.hAdd Complex Complex Complex qz4 (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 17, @HPow.hPow Complex Complex Complex qz123 (@Nat.cast Complex Complex.instNatCast n) qz209) (@HMul.hMul Complex Complex Complex qz74 qz210 (@HAdd.hAdd Complex Complex Complex qz4 qz211 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz82 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz128 qz129 (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz82 2 k) 1))))))) Bool.false ep742 ep743 ep744

noncomputable def ep863 := @Enclosure.Complex.IsNear.addLitP (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 17, @HPow.hPow Complex Complex Complex qz123 (@Nat.cast Complex Complex.instNatCast n) qz209) (@HMul.hMul Complex Complex Complex qz74 qz210 (@HAdd.hAdd Complex Complex Complex qz4 qz211 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz82 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz128 qz129 (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))))) Bool.false 92947171639 68719476736 137940982819 23450521436160

noncomputable def ep864 := nat_lit 1833530293043249585061888000

noncomputable def ep865 := nat_lit 458382573260812396265472000

noncomputable def ep866 := nat_lit 271672912319959774172521976400183296

noncomputable def ep867 := nat_lit 548179078573867543791300566319104

noncomputable def ep868 := @ep863 Bool.true 5806503165 68719476736 1103574612437 187604171489280 Bool.true 285884218816317563718739 ep743 326851285694983063895021 ep864 Bool.false 74184535087807240866689 783559954291987002163200 81857877918596747847899 ep865 Bool.false ep866 ep742 ep743 ep744 ep745 Bool.false ep867 7977055481371172118689 783559954291987002163200

noncomputable def ep869 := @Enclosure.Complex.IsNear.of_eq (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 17, @HPow.hPow Complex Complex Complex qz123 (@Nat.cast Complex Complex.instNatCast n) qz209) (BSN.headSumC qz145 17) Bool.false 92947171639 68719476736 137940982819 23450521436160 Bool.true 5806503165 68719476736 1103574612437

noncomputable def ep870 := @Enclosure.Complex.IsNear.mul qz210 (@HAdd.hAdd Complex Complex Complex qz4 qz211 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz82 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz128 qz129 (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz82 2 k) 1))))) Bool.true 285884218816317563718739 ep743 326851285694983063895021 ep864 Bool.false

noncomputable abbrev qz212 := (Complex.re qz438)

noncomputable abbrev qz213 := (Complex.im qz438)

noncomputable def ep871 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 qz212 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz211 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz82 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz128 qz129 (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz82 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz213 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz211 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz82 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz128 qz129 (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz82 2 k) 1))))))) 174992241407479600445 3917799771459935010816 404678251040936551657

noncomputable def ep872 := nat_lit 3208678012825686773858304

noncomputable def ep873 := nat_lit 373345709047523667824653430665012663715627008

noncomputable def ep874 := @Enclosure.Real.IsNear.mulLit_tf qz212 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz211 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz82 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz128 qz129 (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))))) 3061861561 34359738368 35403534793 140703128616960 57152238245

noncomputable abbrev qz439 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) qz496 (Real.log (Enclosure.sfrac Bool.false 17 1)))

noncomputable abbrev qz214 := (Real.cos qz439)

noncomputable abbrev qz215 := (Real.sin qz439)

noncomputable abbrev qz440 := (@Neg.neg Real Real.instNeg qz215)

noncomputable def ep875 := @Enclosure.Complex.IsNear.of_eq qz210 (Complex.mk (@HMul.hMul Real Real Real qz0 qz132 qz214) (@HMul.hMul Real Real Real qz0 qz132 qz440)) Bool.true 3061861561 34359738368 35403534793 140703128616960 Bool.false 62004890103 274877906944 284436241919 1125625028935680 (BSN.cpow_neg_s_mk qz154 83585 1000 17 qz155 rfl)

noncomputable def ep876 := @Enclosure.Real.IsNear.mulLit_ff qz154 qz135 83585 1000 0 1 3189913004350711 1125899906842624 2500000000819 204750000000000000 53325775693730835787 225179981368524800 41792500013691223 40950000000000000000 qz156 (BSN.isNear_log_sfrac 17 1 3189913004350711 1125899906842624 2500000000819 204750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' qz394 Bool.false 26758929747600409100288 9444732965739290427392 1000000000327600 81900000000000000000 3189913004350711 1125899906842624 2500000000819 204750000000000000 (BSN.log_rat_reduce_isNear 17 1 4 34 32 15892 262144 24973259072661432 36028797018963968 81900 1000000000000000 rfl rfl rfl rfl (ep455 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep877 := nat_lit 6051653717260618157408806484462839455960560683079937428296445990020879220736

noncomputable def ep878 := nat_lit 7326194693153218214155623364022310292198309093243902474901979700821753856

noncomputable def ep879 := nat_lit 18140308762395548035798108206660473747297285431053324479939534010660994154496

noncomputable def ep880 := BSN.cos_dyadic_bound_f 1282654848 1073741824 3 2 524288 163960 ep877 ep64 ep878 ep879 ep66 ep878 192632 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1282654848) qz285 0 2 ep877 ep64 ep878 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1282654848) qz286 0 2 ep879 ep66 ep878 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz216 := qz439

noncomputable abbrev qz441 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 62079373) qz26)

noncomputable def ep881 := @Enclosure.Real.IsNear.cos_image qz216 qz441 Bool.false 62079373 262144 67 65536 Bool.true 192632 524288 1 81900 (@Enclosure.Real.IsNear.recentre' qz216 Bool.false 53325775693730835787 225179981368524800 41792500013691223 40950000000000000000 62079373 262144 67 65536 (ep876 rfl) rfl) (Enclosure.sfrac_false_div 62079373 262144) (BSN.cos_reduce2 qz441 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 45129405441040770400256) qz292) 226375608064910080 72057594037927936 Bool.false 192632 524288 37 1000000000000000 163800 81900 (BSN.sin_reduce_arg_pos_rat_q2 62079373 262144 226375608064910080 72057594037927936 37 45129405441040770400256 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 192632 524288 45129405441040770400256 37778931862957161709568 1282654848 1073741824 163960 163800 (ep880 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep882 := nat_lit 10887115735314590108764527173341893172495250582269292248953681198276925194240

noncomputable def ep883 := nat_lit 28502013086796916502988938254258445997014478072173370524205038028352521240576

noncomputable def ep884 := BSN.sin_dyadic_bound_f 1282654848 1073741824 3 2 524288 163960 ep882 ep57 ep878 ep883 ep60 ep878 487617 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1282654848) qz281 0 2 ep882 ep57 ep878 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1282654848) qz282 0 2 ep883 ep60 ep878 rfl rfl rfl rfl) rfl rfl

noncomputable def ep885 := @Enclosure.Real.IsNear.sin_image qz216 qz441 Bool.false 62079373 262144 67 65536 Bool.true 487617 524288 1 81900 (@Enclosure.Real.IsNear.recentre' qz216 Bool.false 53325775693730835787 225179981368524800 41792500013691223 40950000000000000000 62079373 262144 67 65536 (ep876 rfl) rfl) (Enclosure.sfrac_false_div 62079373 262144) (BSN.sin_reduce2 qz441 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 45129405441040770400256) qz292) 226375608064910080 72057594037927936 Bool.false 487617 524288 37 1000000000000000 163800 81900 (BSN.sin_reduce_arg_pos_rat_q2 62079373 262144 226375608064910080 72057594037927936 37 45129405441040770400256 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 487617 524288 45129405441040770400256 37778931862957161709568 1282654848 1073741824 163960 163800 (ep884 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep886 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz132 qz214) (@HMul.hMul Real Real Real qz0 qz132 qz440) Bool.true 3061861561 34359738368 35403534793 140703128616960 Bool.false 62004890103 274877906944 284436241919 1125625028935680 (@Enclosure.Real.IsNear.mulLit_ft qz132 qz214 127159 524288 1 524288 24079 65536 1388209 1341849600 3061861561 34359738368 35403534793 140703128616960 qz396 (@Enclosure.Real.IsNear.recentre' qz214 Bool.true 192632 524288 5552836 5367398400 24079 65536 1388209 1341849600 (ep881 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz132 qz440 127159 524288 1 524288 487617 524288 1388209 1341849600 62004890103 274877906944 284436241919 1125625028935680 qz396 (@Enclosure.Real.IsNear.neg qz215 Bool.true 487617 524288 1388209 1341849600 (@Enclosure.Real.IsNear.recentre' qz215 Bool.true 487617 524288 5552836 5367398400 487617 524288 1388209 1341849600 (ep885 rfl rfl) rfl)) rfl)

noncomputable def ep887 := @ep874 114022980312 0 1 174992241407479600445 3917799771459935010816 404678251040936551657 ep872 (@Enclosure.Complex.IsNear.re_isNear qz210 Bool.true 3061861561 34359738368 35403534793 140703128616960 Bool.false 62004890103 274877906944 284436241919 1125625028935680 (ep875 ep886))

noncomputable def ep888 := @Enclosure.Complex.IsNear.re_isNear (@HAdd.hAdd Complex Complex Complex qz4 qz211 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz82 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz128 qz129 (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz82 2 k) 1))))) Bool.false 57152238245 114022980312 0 1 Bool.false

noncomputable def ep889 := @Enclosure.Complex.IsNear.addLitP qz211 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz82 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz128 qz129 (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) Bool.false 278788089 558936178 0 1 Bool.true 56837800

noncomputable def ep890 := @ep889 279468089 0 1 Bool.false 1 408 0 1 Bool.false 16717 40800 0 1 Bool.false 114304476490 57152238245 114022980312 0 1 Bool.false 2352885803813 2352885803813 11402298031200 0 1

noncomputable abbrev qz217 := (@HDiv.hDiv Complex Complex Complex qz358 qz387 (@HSub.hSub Complex Complex Complex qz350 qz399 (1 : Complex)))

noncomputable def ep891 := @Enclosure.Complex.IsNear.addLitP qz217 qz101 Bool.true 34000000 27946808900 0 1 Bool.true 5683780000 27946808900 0 1

noncomputable def ep892 := @Enclosure.Complex.IsNear.of_eq qz217 (Complex.mk (Enclosure.sfrac Bool.true 34000000 27946808900) (Enclosure.sfrac Bool.true 5683780000 27946808900)) Bool.true 34000000 27946808900 0 1 Bool.true 5683780000 27946808900 0 1

noncomputable def ep893 := @ep891 Bool.false 1 2 0 1 Bool.false 0 1 0 1 Bool.false 27878808900 278788089 558936178 0 1 Bool.true 5683780000 56837800 279468089 0 1 (ep892 (BSN.N_div_s_sub_one_mk qz154 83585 1000 17 qz155 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 34000000 27946808900) (Enclosure.sfrac Bool.true 5683780000 27946808900) Bool.true 34000000 27946808900 0 1 Bool.true 5683780000 27946808900 0 1 (Enclosure.Real.IsNear.const Bool.true 34000000 27946808900) (Enclosure.Real.IsNear.const Bool.true 5683780000 27946808900))) qz102 rfl

noncomputable def ep894 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz82 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz128 qz129 (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) (@HAdd.hAdd Complex Complex Complex qz4 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz82 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz128 qz129 (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz103)) ↑qz138) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 1))) qz139)) Bool.false 1 408 0 1

noncomputable def ep895 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz82 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz128 qz129 (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz103)) ↑qz138) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 1))) qz139) Bool.false 0 1 0 1 Bool.false

noncomputable def ep896 := @ep895 0 1 0 1 Bool.false 1 408 0 1 Bool.false 16717 40800 0 1 Bool.false 1 1 408 0 1 Bool.false 16717 16717 40800 0

noncomputable def ep897 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz82 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz128 qz129 (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) (Complex.mk qz13 qz13) Bool.false 0 1 0 1 Bool.false

noncomputable def ep898 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz103)) ↑qz138) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 1))) qz139 Bool.false 1 408 0 1 Bool.false 16717 40800 0 1

noncomputable def ep899 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz103)) ↑qz138) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 1)))) qz140) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz103)) ↑qz138) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 1)))) qz141) 1 408 0 1 0 1 0

noncomputable def ep900 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz103)) ↑qz138) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 1)))) qz140 1 24 0 1 1 17 0 1 1

noncomputable def ep901 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz103)) ↑qz138)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz103)) ↑qz138)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 1)))) 1 24 0 1 0 1 0 1 1

noncomputable def ep902 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz103)) ↑qz138)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 1 2 0 1 1 24 0

noncomputable def ep903 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 1)) qz145 Bool.false 1 2 0 1 Bool.false 83585 1000 0 1 (BSN.ascPochhammer_one_eval qz145)

noncomputable def ep904 := ep903 (@Enclosure.Complex.IsNear.of_eq qz145 (Complex.mk qz96 qz154) Bool.false 1 2 0 1 Bool.false 83585 1000 0 1 (BSN.s_crit_mk qz154 Bool.false 83585 1000 qz155) (@Enclosure.Complex.IsNear.mk qz96 qz154 Bool.false 1 2 0 1 Bool.false 83585 1000 0 1 qz368 qz156))

noncomputable def ep905 := @ep902 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz103)) ↑qz138) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep479) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 83585 1000 0 1 ep904)

noncomputable def ep906 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz103)) ↑qz138)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 83585 1000 0 1 0 1 0

noncomputable def ep907 := @ep906 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz103)) ↑qz138) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep479) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 83585 1000 0 1 ep904)

noncomputable def ep908 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz103)) ↑qz138)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz103)) ↑qz138)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 1)))) 16717 2400 0 1 0 1 0 1 16717

noncomputable def ep909 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz103)) ↑qz138)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 83585 1000 0 1 16717 2400 0

noncomputable def ep910 := @ep909 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz103)) ↑qz138) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep479) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 83585 1000 0 1 ep904)

noncomputable def ep911 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz103)) ↑qz138)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 1 2 0 1 0 1 0

noncomputable def ep912 := @ep911 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz103)) ↑qz138) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep479) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 83585 1000 0 1 ep904)

noncomputable def ep913 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz103)) ↑qz138) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 24 0 1 Bool.false 16717 2400 0 1 (@ep901 1 24 0 1 (ep905 rfl) (ep907 rfl) rfl rfl) (@ep908 16717 2400 0 1 (ep910 rfl) (ep912 rfl) rfl rfl)

noncomputable def ep914 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz103)) ↑qz138) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 16717 2400 0 1 ep913

noncomputable def ep915 := @ep900 408 0 1 ep914 qz142

noncomputable def ep916 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz103)) ↑qz138) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 1)))) qz141 16717 2400 0 1 0 1 0 1 0

noncomputable def ep917 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz103)) ↑qz138) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 16717 2400 0 1 ep913

noncomputable def ep918 := @ep916 1 0 1 ep917 qz143

noncomputable def ep919 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz103)) ↑qz138) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 1)))) qz141) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz103)) ↑qz138) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 1)))) qz140) 0 1 0 1 16717 40800 0

noncomputable def ep920 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz103)) ↑qz138) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 1)))) qz141 1 24 0 1 0 1 0 1 0

noncomputable def ep921 := @ep920 1 0 1 ep914 qz143

noncomputable def ep922 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz103)) ↑qz138) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 1)))) qz140 16717 2400 0 1 1 17 0 1 16717

noncomputable def ep923 := @ep922 40800 0 1 ep917 qz142

noncomputable def ep924 := @ep896 1 (@ep897 0 1 0 1 (BSN.bern_sum_base qz145 17) qz117) (ep898 (@ep899 1 1 1 408 0 1 (ep915 rfl) (ep918 rfl) rfl rfl) (@ep919 1 16717 16717 40800 0 1 (ep921 rfl) (ep923 rfl) rfl rfl)) rfl rfl rfl rfl rfl

noncomputable def ep925 := ep890 (ep893 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep894 Bool.false 16717 40800 0 1 (BSN.bern_sum_succ qz145 17 0 1 1 rfl rfl) (ep924 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl rfl

noncomputable def ep926 := @Enclosure.Real.IsNear.mulLit_ff qz213 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz211 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz82 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz128 qz129 (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))))) 62004890103 274877906944 284436241919 1125625028935680 2352885803813

noncomputable def ep927 := @ep926 11402298031200 0 1 48630141896777961120913 1044746605722649336217600 669245995701135240637147 ep745 (@Enclosure.Complex.IsNear.im_isNear qz210 Bool.true 3061861561 34359738368 35403534793 140703128616960 Bool.false 62004890103 274877906944 284436241919 1125625028935680 (ep875 ep886))

noncomputable def ep928 := @Enclosure.Complex.IsNear.im_isNear (@HAdd.hAdd Complex Complex Complex qz4 qz211 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz82 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz128 qz129 (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz82 2 k) 1))))) Bool.false 57152238245 114022980312 0 1 Bool.false

noncomputable def ep929 := @Enclosure.Real.IsNear.addLit_tf_p (@HMul.hMul Real Real Real qz0 qz212 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz211 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz82 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz128 qz129 (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz82 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz213 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz211 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz82 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz128 qz129 (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz82 2 k) 1))))))) 7204210600117611932093 391779977145993501081600 83300474419249317565709

noncomputable def ep930 := nat_lit 1604339006412843386929152000

noncomputable def ep931 := nat_lit 25669424102605494190866432

noncomputable def ep932 := nat_lit 387520206150496984143528747421283629905477632

noncomputable def ep933 := @Enclosure.Real.IsNear.mulLit_tf qz212 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz211 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz82 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz128 qz129 (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))))) 3061861561 34359738368 35403534793 140703128616960 2352885803813

noncomputable def ep934 := @ep933 11402298031200 0 1 7204210600117611932093 391779977145993501081600 83300474419249317565709 ep930 (@Enclosure.Complex.IsNear.re_isNear qz210 Bool.true 3061861561 34359738368 35403534793 140703128616960 Bool.false 62004890103 274877906944 284436241919 1125625028935680 (ep875 ep886))

noncomputable def ep935 := @Enclosure.Real.IsNear.mulLit_ff qz213 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz211 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz82 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz128 qz129 (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))))) 62004890103 274877906944 284436241919 1125625028935680 57152238245

noncomputable def ep936 := @ep935 114022980312 0 1 1181239417173899529745 10447466057226493362176 3251233572733428798431 ep931 (@Enclosure.Complex.IsNear.im_isNear qz210 Bool.true 3061861561 34359738368 35403534793 140703128616960 Bool.false 62004890103 274877906944 284436241919 1125625028935680 (ep875 ep886))

noncomputable abbrev qz442 := (ep925 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable def ep937 := @ep870 74184535087807240866689 783559954291987002163200 81857877918596747847899 ep865 (@ep871 ep872 48630141896777961120913 1044746605722649336217600 669245995701135240637147 ep745 ep873 285884218816317563718739 ep743 326851285694983063895021 ep864 (ep887 (@ep888 2352885803813 11402298031200 0 1 qz442) rfl) (ep927 (@ep928 2352885803813 11402298031200 0 1 qz442) rfl) rfl rfl) (@ep929 ep930 1181239417173899529745 10447466057226493362176 3251233572733428798431 ep931 ep932 74184535087807240866689 783559954291987002163200 81857877918596747847899 ep865 (ep934 (@ep928 2352885803813 11402298031200 0 1 qz442) rfl) (ep936 (@ep888 2352885803813 11402298031200 0 1 qz442) rfl) rfl rfl)

noncomputable def ep938 := @ep868 ep860 ep861 (@ep869 187604171489280 (BSN.head_sum_c_eq qz145 17) EMRow22.d12) ep937 rfl rfl rfl rfl rfl rfl rfl rfl rfl

noncomputable def ep939 := @Enclosure.Complex.IsNear.re_isNear (zetaApproximant qz145 1 17) Bool.false ep742 ep743 ep744 ep745 Bool.false 7977055481371172118689 783559954291987002163200 ep860 ep861 (@ep862 ep745 Bool.false 7977055481371172118689 783559954291987002163200 ep860 ep861 (BSN.zetaApproximant_eq_folded' qz145 1 17 rfl) (ep938 rfl rfl rfl rfl rfl rfl rfl rfl rfl))

noncomputable def ep940 := @Enclosure.Real.IsNear.mulLit_tf (Real.sin (@HSub.hSub Real Real Real qz353 (Complex.im (@HSub.hSub Complex Complex Complex qz75 qz179 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz180 (@Nat.cast Complex Complex.instNatCast j))))) qz181)) (Complex.im (zetaApproximant qz145 1 17)) 13 262144 5188397

noncomputable def ep941 := @Enclosure.Real.IsNear.recentre' (Real.sin (@HSub.hSub Real Real Real qz353 (Complex.im (@HSub.hSub Complex Complex Complex qz75 qz179 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz180 (@Nat.cast Complex Complex.instNatCast j))))) qz181)) Bool.true 26 524288 20753588

noncomputable def ep942 := @Enclosure.Real.IsNear.sin_image (@HSub.hSub Real Real Real qz353 (Complex.im (@HSub.hSub Complex Complex Complex qz75 qz179 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz180 (@Nat.cast Complex Complex.instNatCast j))))) qz181) qz420 Bool.false 4323639 65536 247

noncomputable def ep943 := BSN.sin_dyadic_bound_f 53427 1073741824 1 0 524288 163960 0 1 1 0 1 1 26 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 53427) qz281 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 53427) qz282 0 0 rfl) rfl rfl

noncomputable def ep944 := @ep942 524288 Bool.true 26 524288 1 81900 (@ep749 4323639 65536 247 524288 ep857 rfl) (Enclosure.sfrac_false_div 4323639 65536) (BSN.sin_reduce2 qz420 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 469951143632437248) qz301) 226375608064910080 72057594037927936 Bool.false 26 524288 10 1000000000000000 163800 81900 (BSN.sin_reduce_arg_pos_rat_q2 4323639 65536 226375608064910080 72057594037927936 10 469951143632437248 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 26 524288 469951143632437248 9444732965739290427392 53427 1073741824 163960 163800 (ep943 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep945 := @Enclosure.Complex.IsNear.im_isNear (zetaApproximant qz145 1 17) Bool.false ep742 ep743 ep744 ep745 Bool.false 7977055481371172118689 783559954291987002163200 ep860 ep861 (@ep862 ep745 Bool.false 7977055481371172118689 783559954291987002163200 ep860 ep861 (BSN.zetaApproximant_eq_folded' qz145 1 17 rfl) (ep938 rfl rfl rfl rfl rfl rfl rfl rfl rfl))

theorem EMRow22.d13 : Enclosure.Real.IsNear (hardyZApproximantEM 1 17 qz154) Bool.true ep728 ep729 ep730 ep731 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantEM 1 17 qz154) ep732 Bool.true ep728 ep729 ep730 ep731 (@Eq.refl Real ep732) (@ep733 Bool.true ep728 ep729 ep730 ep731 (BSN.re_exp_mul (@HSub.hSub Real Real Real qz353 (Complex.im (@HSub.hSub Complex Complex Complex qz75 qz179 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz180 (@Nat.cast Complex Complex.instNatCast j))))) qz181) (zetaApproximant qz145 1 17)) (@ep735 ep729 ep736 ep731 103701721257825237542957 ep737 ep738 ep739 ep740 ep728 ep729 ep730 ep731 (@ep741 10734796800 ep742 ep743 ep744 ep745 ep734 ep729 ep736 ep731 (@ep746 42939187200 524287 524288 5188397 10734796800 (ep859 rfl rfl) rfl) ep939 rfl) (@ep940 10734796800 7977055481371172118689 783559954291987002163200 ep860 ep861 103701721257825237542957 ep737 ep738 ep739 (@ep941 42939187200 13 262144 5188397 10734796800 (ep944 rfl rfl) rfl) ep945 rfl) rfl rfl))

theorem EMRow22.d14 : @Eq Nat (Nat.mul (BSN.factNat (Nat.succ (Nat.mul 2 1))) (Nat.pow 4 (Nat.mul 2 1))) 96 := @Eq.refl Nat 96

theorem EMRow22.d15 : @Eq Nat (Nat.mul (Nat.mul 2 1) (Nat.pow (Nat.succ (Nat.mul 4 2)) (Nat.mul 2 1))) 162 := @Eq.refl Nat 162

theorem EMRow22.d16 : @Eq Nat (BSN.factNat (Nat.mul 2 2)) 24 := @Eq.refl Nat 24

theorem EMRow22.d17 : @Eq Nat (Nat.pow 17 (Nat.succ (Nat.mul 2 3))) 410338673 := @Eq.refl Nat 410338673

noncomputable abbrev qz499 := (@HAdd.hAdd Complex Complex Complex qz503 qz502 (@Nat.cast Complex Complex.instNatCast 3))

noncomputable abbrev qz443 := qz499

noncomputable abbrev qz218 := (@HDiv.hDiv Real Real Real qz268 (@Norm.norm Complex Complex.instNorm qz443) (@HAdd.hAdd Real Real Real qz378 (Complex.re qz270) qz289))

noncomputable abbrev qz219 := (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 2)

noncomputable abbrev qz220 := (@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 2)))

noncomputable abbrev qz444 := (@HPow.hPow Complex Complex Complex qz479 qz493 (@HSub.hSub Complex Complex Complex qz486 qz480 qz481))

noncomputable abbrev qz221 := qz444

noncomputable def ep946 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 17))) (@HMul.hMul Real Real Real qz0 qz218 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz219)) ↑qz220) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz221))) 3137259955 51539607552 43711937 463856467968 6703824426998367 7881299347898368 2213132639

noncomputable def ep947 := nat_lit 370238164902536271861121024

noncomputable def ep948 := @Enclosure.Real.IsNear.mulLit_ff (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 17)) 4427 294912 1 884736 2125995 524288 3131 524288 3137259955 51539607552

noncomputable abbrev qz222 := qz269

noncomputable abbrev qz500 := (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid)))

noncomputable abbrev qz445 := (@Inv.inv Real Real.instInv (@HPow.hPow Real Nat Real qz500 qz222 2))

noncomputable def ep949 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 96 162) qz445 96 162 0 1 13281 524288 1 524288 4427 294912 1 884736

noncomputable def ep950 := nat_lit 781950621441006189802102638025

noncomputable def ep951 := nat_lit 19807040628566084398385987584

noncomputable def ep952 := nat_lit 26986075409044041160201671

noncomputable def ep953 := nat_lit 1073741824000000000000000000000000000000

noncomputable abbrev qz446 := (@HPow.hPow Real Nat Real qz500 qz222 1)

noncomputable def ep954 := @Enclosure.Real.IsNear.mulLit_ff qz446 qz222 884279719003555 140737488355328 1 500000000000000 884279719003555 140737488355328 1 500000000000000 ep950 ep951 ep952 ep953

noncomputable def ep955 := ep954 (@Enclosure.Real.IsNear.of_eq qz446 qz222 Bool.false 884279719003555 140737488355328 1 500000000000000 (BSN.pow_one_r qz222) (@Enclosure.Real.IsNear.of_eq qz222 qz266 Bool.false 884279719003555 140737488355328 1 500000000000000 BSN.two_pi_eq qz267)) (@Enclosure.Real.IsNear.of_eq qz222 qz266 Bool.false 884279719003555 140737488355328 1 500000000000000 BSN.two_pi_eq qz267) rfl

noncomputable abbrev qz447 := (@HPow.hPow Real Nat Real qz500 qz222 2)

noncomputable def ep956 := @Enclosure.Real.IsNear.inv_image qz447 ep950 ep951 ep952 ep953 6640 6641 262144 (@Enclosure.Real.IsNear.of_eq qz447 (@HMul.hMul Real Real Real qz0 qz446 qz222) Bool.false ep950 ep951 ep952 ep953 (BSN.pow_succ_r qz222 1 2 rfl) ep955) rfl rfl rfl

noncomputable def ep957 := ep949 (Enclosure.Real.IsNear.const Bool.false 96 162) (@Enclosure.Real.IsNear.recentre' qz445 Bool.false 13281 524288 1 524288 13281 524288 1 524288 (ep956 rfl rfl rfl) rfl)

noncomputable def ep958 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 17)) (Real.sqrt (@HAdd.hAdd Real Real Real qz378 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz5 1 17)) (Complex.re (zetaApproximant qz5 1 17))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz5 1 17)) (Complex.im (zetaApproximant qz5 1 17))))) Bool.false 2125995 524288 3131 524288

noncomputable def ep959 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz378 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz5 1 17)) (Complex.re (zetaApproximant qz5 1 17))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz5 1 17)) (Complex.im (zetaApproximant qz5 1 17))))) Bool.false 2125995 524288 3131 524288

noncomputable def ep960 := nat_lit 340442799125510245063709631911342034781598021

noncomputable def ep961 := nat_lit 20704207695330992789512302845623271424000000

noncomputable def ep962 := nat_lit 6511247568922550871494813064629732223330602365315479307519

noncomputable def ep963 := nat_lit 134473316764182103744153675109539759755438677242675200000000

noncomputable def ep964 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz378 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz5 1 17)) (Complex.re (zetaApproximant qz5 1 17))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz5 1 17)) (Complex.im (zetaApproximant qz5 1 17)))) ep960 ep961 ep962 ep963 1061432 1064563

noncomputable def ep965 := nat_lit 249021082551201130510478043221796989223417761593539481

noncomputable def ep966 := nat_lit 15147282199644852893624554643405365387422859264000000

noncomputable def ep967 := nat_lit 109094839773559002108025690530598971576631941282952138949539

noncomputable def ep968 := nat_lit 2286046384991095763650612476862175915842457513125478400000000

noncomputable def ep969 := nat_lit 4342324007848087261096385132411273110199095968121

noncomputable def ep970 := nat_lit 1363255397968036760426209917906482884868057333760000

noncomputable def ep971 := nat_lit 399092224531090676846532892026619054997074731852752319571

noncomputable def ep972 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz5 1 17)) (Complex.re (zetaApproximant qz5 1 17))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz5 1 17)) (Complex.im (zetaApproximant qz5 1 17))) ep965 ep966 ep967 ep968 ep969 ep970 ep971

noncomputable def ep973 := nat_lit 571511596247773940912653119215543978960614378281369600000000

noncomputable def ep974 := nat_lit 339545109402918199860270809263081784102524758506855324906480834434208573654857308877700786731677122560000

noncomputable def ep975 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (zetaApproximant qz5 1 17)) (Complex.re (zetaApproximant qz5 1 17)) ep295 ep296 ep297 ep298 ep295 ep296 ep297 ep298 ep965

noncomputable def ep976 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (zetaApproximant qz5 1 17)) (Complex.im (zetaApproximant qz5 1 17)) ep429 ep430 ep431 ep432 ep429 ep430 ep431 ep432 ep969

noncomputable def ep977 := @ep946 3940649673949184 ep947 21550697559871261 23643898043695104 10086223842565 106397541196627968 (@ep948 43711937 463856467968 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaStirlingErrorBound 1 2) (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 96 162) qz445) Bool.false 4427 294912 1 884736 (BSN.theta_err_eq 1 2 96 162 EMRow22.d14 EMRow22.d15 rfl) (ep957 rfl)) (ep958 (BSN.norm_eq_sqrt_mul_add (zetaApproximant qz5 1 17)) (@ep959 2125995 524288 3131 524288 (@ep964 262144 (@ep972 ep973 ep974 ep960 ep961 ep962 ep963 (@ep975 ep966 ep967 ep968 ep518 ep518 rfl) (@ep976 ep970 ep971 ep973 ep526 ep526 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl)

noncomputable abbrev qz223 := (@Norm.norm Complex Complex.instNorm qz443)

noncomputable abbrev qz448 := (Enclosure.sfrac Bool.false 2 7)

noncomputable def ep978 := @Enclosure.Real.IsNear.of_eq (@HMul.hMul Real Real Real qz0 qz218 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz219)) ↑qz220) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz221))) (@HMul.hMul Real Real Real qz0 (@HMul.hMul Real Real Real qz0 qz223 qz448) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz219)) ↑qz220) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz221))) Bool.false 6703824426998367 7881299347898368 2213132639 3940649673949184 (BSN.zrb_shape_eq qz223 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz219)) ↑qz220) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz221)) qz16 3)

noncomputable def ep979 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz0 qz223 qz448) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz219)) ↑qz220) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz221)) 42581859 1835008 1 1835008 157433813 4294967296 401 17179869184

noncomputable def ep980 := @Enclosure.Real.IsNear.mulLit_ff qz223 qz448 42581859 524288 1 524288 2 7 0 1 42581859 1835008

noncomputable abbrev qz449 := (Complex.re qz499)

noncomputable abbrev qz450 := (Complex.im qz499)

noncomputable abbrev qz224 := (@HAdd.hAdd Real Real Real qz378 (@HMul.hMul Real Real Real qz265 qz449 qz449) (@HMul.hMul Real Real Real qz265 qz450 qz450))

noncomputable abbrev qz225 := qz443

noncomputable def ep981 := @Enclosure.Real.IsNear.of_eq qz223 (Real.sqrt qz224) Bool.false 42581859 524288 1 524288 (BSN.norm_eq_sqrt_mul_add qz225)

noncomputable def ep982 := @Enclosure.Real.IsNear.recentre' (Real.sqrt qz224) Bool.false 42581859 524288 1 524288 42581859

noncomputable def ep983 := @Enclosure.Real.IsNear.sqrt_image qz224 6596436449 1000000 0 1 21290929 21290930 262144

noncomputable abbrev qz226 := (@HMul.hMul Real Real Real qz265 qz449 qz449)

noncomputable abbrev qz227 := (@HMul.hMul Real Real Real qz265 qz450 qz450)

noncomputable def ep984 := @Enclosure.Real.IsNear.addLit_ff qz226 qz227 49 4 0 1 6584186449 1000000 0 1

noncomputable abbrev qz228 := qz449

noncomputable def ep985 := @Enclosure.Real.IsNear.mulLit_ff qz228 qz228 7 2 0 1 7 2 0 1 49 4

noncomputable abbrev qz451 := (Enclosure.sfrac Bool.false 7 2)

noncomputable def ep986 := @Enclosure.Complex.IsNear.of_eq qz225 (Complex.mk qz451 qz16) Bool.false 7 2 0 1 Bool.false 81143 1000 0 1 (BSN.s_add_nat_mk qz16 Bool.false 81143 1000 3 qz17)

noncomputable abbrev qz452 := (ep986 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7 2) qz16 Bool.false 7 2 0 1 Bool.false 81143 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 7 2) qz21))

noncomputable def ep987 := @ep985 0 1 (@Enclosure.Complex.IsNear.re_isNear qz225 Bool.false 7 2 0 1 Bool.false 81143 1000 0 1 qz452)

noncomputable def ep988 := ep987 (@Enclosure.Complex.IsNear.re_isNear qz225 Bool.false 7 2 0 1 Bool.false 81143 1000 0 1 qz452)

noncomputable abbrev qz229 := qz450

noncomputable def ep989 := @Enclosure.Real.IsNear.mulLit_ff qz229 qz229 81143 1000 0 1 81143 1000 0 1 6584186449 1000000

noncomputable def ep990 := @ep989 0 1 (@Enclosure.Complex.IsNear.im_isNear qz225 Bool.false 7 2 0 1 Bool.false 81143 1000 0 1 qz452)

noncomputable def ep991 := ep990 (@Enclosure.Complex.IsNear.im_isNear qz225 Bool.false 7 2 0 1 Bool.false 81143 1000 0 1 qz452)

noncomputable def ep992 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz219)) ↑qz220) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz221)) (Real.sqrt (@HAdd.hAdd Real Real Real qz378 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz219)) ↑qz220) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz221)) (Complex.re (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz219)) ↑qz220) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz221))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz219)) ↑qz220) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz221)) (Complex.im (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz219)) ↑qz220) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz221))))) Bool.false 157433813 4294967296

noncomputable def ep993 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz378 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz219)) ↑qz220) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz221)) (Complex.re (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz219)) ↑qz220) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz221))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz219)) ↑qz220) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz221)) (Complex.im (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz219)) ↑qz220) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz221))))) Bool.false 1259470504 34359738368

noncomputable def ep994 := nat_lit 970824418686731714388548529363611370164148919393011024725574401

noncomputable def ep995 := nat_lit 722544144432392189785757272033806912793765478400000000000000000000

noncomputable def ep996 := nat_lit 3608876165409517312754976885482075453380700932248551404314835146228874881383

noncomputable def ep997 := nat_lit 2113019853976251861173985467006561077181019960980888642125824000000000000000000000000

noncomputable def ep998 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz378 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz219)) ↑qz220) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz221)) (Complex.re (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz219)) ↑qz220) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz221))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz219)) ↑qz220) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz221)) (Complex.im (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz219)) ↑qz220) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz221)))) ep994 ep995 ep996 ep997

noncomputable def ep999 := nat_lit 201759076004609596955750699086575631701551879918669287647289

noncomputable def ep1000 := nat_lit 451590090270245118616098295021129320496103424000000000000000000

noncomputable def ep1001 := nat_lit 18042246552455627172532936520603050103211451843165834200645669027185006011

noncomputable def ep1002 := nat_lit 33015935218378935330843522921977516830953436890326385033216000000000000000000000000

noncomputable def ep1003 := nat_lit 648009897079356359259347410825090359441665911523140164489912001

noncomputable def ep1004 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz219)) ↑qz220) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz221)) (Complex.re (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz219)) ↑qz220) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz221))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz219)) ↑qz220) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz221)) (Complex.im (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz219)) ↑qz220) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz221))) ep999 ep1000 ep1001 ep1002 ep1003

noncomputable def ep1005 := nat_lit 2454172386052357173712868948163480246775168014285938015473512328489034496679

noncomputable def ep1006 := nat_lit 438414686871299416889979411651730905189133913744684531408499273968965285654928406013473639738643440702849024000000000000000000

noncomputable def ep1007 := nat_lit 449175996692398509732847570517

noncomputable def ep1008 := nat_lit 21250649172913403461632000000000

noncomputable def ep1009 := nat_lit 2348844922688934919458528146095319

noncomputable def ep1010 := nat_lit 181702876197320925431879172096000000000000

noncomputable def ep1011 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz219)) ↑qz220) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz221)) (Complex.re (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz219)) ↑qz220) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz221)) ep1007 ep1008 ep1009 ep1010 ep1007 ep1008 ep1009

noncomputable def ep1012 := nat_lit 25456038518971414364010976174751

noncomputable def ep1013 := nat_lit 850025966916536138465280000000000

noncomputable def ep1014 := nat_lit 28188016270979662475990065338431227

noncomputable def ep1015 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz219)) ↑qz220) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz221) Bool.true ep1007 ep1008 ep1009 ep1010 Bool.true ep1012 ep1013 ep1014

noncomputable def ep1016 := nat_lit 1453623009578567403455033376768000000000000

noncomputable def ep1017 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz219)) ↑qz220) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz221 Bool.true ep1007 ep1008 ep1009 ep1010 Bool.true ep1012 ep1013 ep1014 ep1016

noncomputable def ep1018 := nat_lit 975810482387128363246811771

noncomputable def ep1019 := nat_lit 566683977944357425643520000000

noncomputable def ep1020 := nat_lit 143931271064502316632831571681

noncomputable def ep1021 := nat_lit 138440286626530228900479369216000000000

noncomputable def ep1022 := nat_lit 825166207205762392222184258209

noncomputable def ep1023 := nat_lit 42501298345826806923264000000000

noncomputable def ep1024 := nat_lit 332297712217965481365836416656001

noncomputable abbrev qz230 := (Complex.re qz444)

noncomputable abbrev qz231 := (Complex.im qz444)

noncomputable def ep1025 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz219)) ↑qz220) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz230) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz219)) ↑qz220) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz231) ep1018 ep1019 ep1020 ep1021 ep1022 ep1023 ep1024

noncomputable def ep1026 := nat_lit 27954288645741680835673718784000000000000

noncomputable def ep1027 := nat_lit 509081681205539842123157959824006329406444214608199680000000

noncomputable def ep1028 := nat_lit 2018920846636899171465324134400

noncomputable def ep1029 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz219)) ↑qz220) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz230 19751309347 480000000 0 1 49404850344027593 1180591620717411303424 51010233283827682861 ep1028 ep1018

noncomputable def ep1030 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz219)) ↑qz220)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz219)) ↑qz220)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) 19751309347 480000000 0 1 0 1 0 1 19751309347

noncomputable def ep1031 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz219)) ↑qz220)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 59253928041 2000000 0 1 19751309347 480000000 0

noncomputable def ep1032 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz219)) ↑qz220) (Complex.mk (Enclosure.sfrac Bool.true 1 720) qz13) Bool.true 1 720 0 1 Bool.false 0 1 0 1 (BSN.bern_coeff_mk 2 1 30 24 Bool.true BSN.bern_real_2 EMRow22.d16 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 1 720) qz13 Bool.true 1 720 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.true 1 720) qz23)

noncomputable abbrev qz453 := (@HAdd.hAdd Complex Complex Complex qz478 qz477 qz482)

noncomputable abbrev qz232 := qz453

noncomputable def ep1033 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) (@HMul.hMul Complex Complex Complex qz74 (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) qz232) Bool.true 59253928041 2000000 0 1 Bool.true 533794068781207 1000000000 0 1

noncomputable abbrev qz233 := (Complex.re qz453)

noncomputable abbrev qz234 := (Complex.im qz453)

noncomputable def ep1034 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz233) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz234) 6583436449 400000 0 1 6584186449 500000 0 1

noncomputable def ep1035 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz233 6583436449 1000000 0 1 5 2 0 1 6583436449 400000

noncomputable abbrev qz454 := (@HAdd.hAdd Complex Complex Complex qz478 qz477 (@Nat.cast Complex Complex.instNatCast 1))

noncomputable abbrev qz235 := qz454

noncomputable def ep1036 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) (@HMul.hMul Complex Complex Complex qz74 (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) qz235) Bool.true 6583436449 1000000 0 1 Bool.false 81143 500 0 1

noncomputable abbrev qz236 := (Complex.re qz454)

noncomputable abbrev qz237 := (Complex.im qz454)

noncomputable def ep1037 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz236) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz237) 3 4 0 1 6584186449 1000000 0 1

noncomputable def ep1038 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz236 1 2 0 1 3 2 0 1 3 4

noncomputable def ep1039 := @ep1038 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 81143 1000 0 1 ep481)

noncomputable abbrev qz455 := (Enclosure.sfrac Bool.false 3 2)

noncomputable def ep1040 := @Enclosure.Complex.IsNear.of_eq qz235 (Complex.mk qz455 qz16) Bool.false 3 2 0 1 Bool.false 81143 1000 0 1 (BSN.s_add_nat_mk qz16 Bool.false 81143 1000 1 qz17)

noncomputable abbrev qz456 := (ep1040 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 3 2) qz16 Bool.false 3 2 0 1 Bool.false 81143 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 3 2) qz21))

noncomputable def ep1041 := ep1039 (@Enclosure.Complex.IsNear.re_isNear qz235 Bool.false 3 2 0 1 Bool.false 81143 1000 0 1 qz456)

noncomputable def ep1042 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz237 81143 1000 0 1 81143 1000 0 1 6584186449 1000000

noncomputable def ep1043 := @ep1042 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 81143 1000 0 1 ep481)

noncomputable def ep1044 := ep1043 (@Enclosure.Complex.IsNear.im_isNear qz235 Bool.false 3 2 0 1 Bool.false 81143 1000 0 1 qz456)

noncomputable def ep1045 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) qz235 Bool.true 6583436449 1000000 0 1 Bool.false 81143 500 0 1 (@ep1037 26333745796 6583436449 1000000 0 1 (ep1041 rfl) (ep1044 rfl) rfl rfl)

noncomputable def ep1046 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz237) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz236) 81143 2000 0 1 243429 2000 0 1

noncomputable def ep1047 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz237 1 2 0 1 81143 1000 0 1 81143 2000

noncomputable def ep1048 := @ep1047 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 81143 1000 0 1 ep481)

noncomputable def ep1049 := ep1048 (@Enclosure.Complex.IsNear.im_isNear qz235 Bool.false 3 2 0 1 Bool.false 81143 1000 0 1 qz456)

noncomputable def ep1050 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz236 81143 1000 0 1 3 2 0 1 243429 2000

noncomputable def ep1051 := @ep1050 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 81143 1000 0 1 ep481)

noncomputable def ep1052 := ep1051 (@Enclosure.Complex.IsNear.re_isNear qz235 Bool.false 3 2 0 1 Bool.false 81143 1000 0 1 qz456)

noncomputable abbrev qz238 := (ep1036 (BSN.ascPochhammer_succ_eval_c 1 2 qz270 rfl) (ep1045 (@ep1046 649144000 81143 500 0 1 (ep1049 rfl) (ep1052 rfl) rfl rfl)))

noncomputable def ep1053 := @ep1035 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 6583436449 1000000 0 1 Bool.false 81143 500 0 1 qz238)

noncomputable abbrev qz457 := (Enclosure.sfrac Bool.false 5 2)

noncomputable def ep1054 := @Enclosure.Complex.IsNear.of_eq qz232 (Complex.mk qz457 qz16) Bool.false 5 2 0 1 Bool.false 81143 1000 0 1 (BSN.s_add_nat_mk qz16 Bool.false 81143 1000 2 qz17)

noncomputable abbrev qz458 := (ep1054 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 5 2) qz16 Bool.false 5 2 0 1 Bool.false 81143 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 5 2) qz21))

noncomputable def ep1055 := ep1053 (@Enclosure.Complex.IsNear.re_isNear qz232 Bool.false 5 2 0 1 Bool.false 81143 1000 0 1 qz458)

noncomputable def ep1056 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz234 81143 500 0 1 81143 1000 0 1 6584186449 500000

noncomputable def ep1057 := @ep1056 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 6583436449 1000000 0 1 Bool.false 81143 500 0 1 qz238)

noncomputable def ep1058 := ep1057 (@Enclosure.Complex.IsNear.im_isNear qz232 Bool.false 5 2 0 1 Bool.false 81143 1000 0 1 qz458)

noncomputable def ep1059 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) qz232 Bool.true 59253928041 2000000 0 1 Bool.true 533794068781207 1000000000 0 1 (@ep1034 5925392804100000 59253928041 2000000 0 1 (ep1055 rfl) (ep1058 rfl) rfl rfl)

noncomputable def ep1060 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz234) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz233) 534199783781207 1000000000 0 1 81143 200 0 1

noncomputable def ep1061 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz234 6583436449 1000000 0 1 81143 1000 0 1 534199783781207 1000000000

noncomputable def ep1062 := @ep1061 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 6583436449 1000000 0 1 Bool.false 81143 500 0 1 qz238)

noncomputable def ep1063 := ep1062 (@Enclosure.Complex.IsNear.im_isNear qz232 Bool.false 5 2 0 1 Bool.false 81143 1000 0 1 qz458)

noncomputable def ep1064 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz233 81143 500 0 1 5 2 0 1 81143 200

noncomputable def ep1065 := @ep1064 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 6583436449 1000000 0 1 Bool.false 81143 500 0 1 qz238)

noncomputable def ep1066 := ep1065 (@Enclosure.Complex.IsNear.re_isNear qz232 Bool.false 5 2 0 1 Bool.false 81143 1000 0 1 qz458)

noncomputable abbrev qz239 := (ep1033 (BSN.ascPochhammer_succ_eval_c 2 3 qz270 rfl) (ep1059 (@ep1060 106758813756241400 533794068781207 1000000000 0 1 (ep1063 rfl) (ep1066 rfl) rfl rfl)))

noncomputable def ep1067 := @ep1031 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz219)) ↑qz220) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1032) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 59253928041 2000000 0 1 Bool.true 533794068781207 1000000000 0 1 qz239)

noncomputable def ep1068 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz219)) ↑qz220)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 533794068781207 1000000000 0 1 0 1 0

noncomputable def ep1069 := @ep1068 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz219)) ↑qz220) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1032) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 59253928041 2000000 0 1 Bool.true 533794068781207 1000000000 0 1 qz239)

noncomputable def ep1070 := @Enclosure.Real.IsNear.addLit_ft_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz219)) ↑qz220)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz219)) ↑qz220)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) 533794068781207 720000000000 0 1 0 1 0 1 533794068781207

noncomputable def ep1071 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz219)) ↑qz220)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 533794068781207 1000000000 0 1 533794068781207 720000000000 0

noncomputable def ep1072 := @ep1071 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz219)) ↑qz220) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1032) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 59253928041 2000000 0 1 Bool.true 533794068781207 1000000000 0 1 qz239)

noncomputable def ep1073 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz219)) ↑qz220)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 59253928041 2000000 0 1 0 1 0

noncomputable def ep1074 := @ep1073 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz219)) ↑qz220) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1032) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 59253928041 2000000 0 1 Bool.true 533794068781207 1000000000 0 1 qz239)

noncomputable def ep1075 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz219)) ↑qz220) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.false 19751309347 480000000 0 1 Bool.false 533794068781207 720000000000 0 1 (@ep1030 19751309347 480000000 0 1 (ep1067 rfl) (ep1069 rfl) rfl rfl) (@ep1070 533794068781207 720000000000 0 1 (ep1072 rfl) (ep1074 rfl) rfl rfl)

noncomputable def ep1076 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz219)) ↑qz220) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 19751309347 480000000 0 1 Bool.false 533794068781207 720000000000 0 1 ep1075

noncomputable def ep1077 := nat_lit 504730211659224792866331033600

noncomputable def ep1078 := @Enclosure.Complex.IsNear.re_isNear qz221 Bool.true 49404850344027593 1180591620717411303424 51010233283827682861 ep1028 Bool.false 7729256050838435 295147905179352825856 8092765565374222459 ep1077

noncomputable abbrev qz459 := (@Nat.cast Real Real.instNatCast 410338673)

noncomputable abbrev qz240 := (@Inv.inv Real Real.instInv (Real.sqrt qz459))

noncomputable def ep1079 := @Enclosure.Complex.IsNear.of_eq qz221 (Complex.mk (@HMul.hMul Real Real Real qz0 qz240 qz133) (@HMul.hMul Real Real Real qz0 qz240 qz391)) Bool.true 49404850344027593 1180591620717411303424 51010233283827682861 ep1028 Bool.false 7729256050838435 295147905179352825856 8092765565374222459

noncomputable def ep1080 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz459) 696018964540551 34359738368 1 34359738368 848103 848104 17179869184 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz459) (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz459 qz18)) Bool.false 696018964540551 34359738368 1 34359738368 (BSN.sqrt_natCast_div_one 410338673) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz459 qz18)) Bool.false 696018964540551 34359738368 1 34359738368 696018964540551 34359738368 1 34359738368 (BSN.sqrt_enclosure 410338673 1 348009482270275 348009482270276 17179869184 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep1081 := nat_lit 17100924750000000000000000

noncomputable def ep1082 := nat_lit 1753674119217514004137115648

noncomputable def ep1083 := nat_lit 618970019642690137449562112

noncomputable def ep1084 := nat_lit 6840369900000000000000000

noncomputable def ep1085 := BSN.log_dyadic_bound 1 33 4 3 135604136745 17179869184 6840369900 41530119 15 1041523072 34 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 1) (BSN.artanhQ 33) 0 3 41530119 135604136745 15 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep1086 := @Enclosure.Real.IsNear.mulLit_ff qz16 qz135 81143 1000 0 1 3189914640129271 1125899906842624 2500068403699 17100924750000000000000 258839243644009436753 1125899906842624000 202863050481347957 ep1081 qz21 (BSN.isNear_log_sfrac 17 1 3189914640129271 1125899906842624 2500068403699 17100924750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' qz394 Bool.false ep1082 ep1083 1000027361479600 ep1084 3189914640129271 1125899906842624 2500068403699 17100924750000000000000 (BSN.log_rat_reduce_isNear 17 1 4 34 32 1041523072 17179869184 24973259072661432 36028797018963968 6840369900 1000000000000000 rfl rfl rfl rfl (ep1085 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1087 := nat_lit 2768859208140172035172073472

noncomputable def ep1088 := nat_lit 4951760157141521099596496896

noncomputable def ep1089 := nat_lit 98750214046310333367217066129620265070217195055930585168402048422089341391038098269721784217540411100505305872641

noncomputable def ep1090 := nat_lit 24241468655984884671616987561611793649609605215227765039851000824877738980510979184756823965407711771199390267473920

noncomputable def ep1091 := nat_lit 5746039153218441830169414726048440169668075321244721440459393219901390783595554912870078577622842187937839361

noncomputable def ep1092 := nat_lit 296239150060624563217990859559408698330312249017149266062325226479828221391547103699339612495465987617140041939201

noncomputable def ep1093 := nat_lit 1090866089519319810222764440272530714232432234685249426793295037119498254122994063314057078443347029703972562036326400

noncomputable def ep1094 := BSN.cos_dyadic_bound_f 39347855933729 70368744177664 3 2 34359738368 13694099898 ep1089 ep1090 ep1091 ep1092 ep1093 ep1091 29126663399 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 39347855933729) (BSN.cosEvenQ 70368744177664) 0 2 ep1089 ep1090 ep1091 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 39347855933729) (BSN.cosOddQ 70368744177664) 0 2 ep1092 ep1093 ep1091 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz460 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 7899146839721) (@Nat.cast Real Real.instNatCast 34359738368))

noncomputable def ep1095 := @Enclosure.Real.IsNear.cos_image qz136 qz460 Bool.false 7899146839721 34359738368 409 34359738368 Bool.true 29126663399 34359738368 1 6840369900 (@Enclosure.Real.IsNear.recentre' qz136 Bool.false 258839243644009436753 1125899906842624000 202863050481347957 ep1081 7899146839721 34359738368 409 34359738368 (ep1086 rfl) rfl) (Enclosure.sfrac_false_div 7899146839721 34359738368) (BSN.cos_reduce2 qz460 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep1087) (@Nat.cast Real Real.instNatCast ep1088)) 226375608064910080 72057594037927936 Bool.false 29126663399 34359738368 36 1000000000000000 13680739800 6840369900 (BSN.sin_reduce_arg_pos_rat_q2 7899146839721 34359738368 226375608064910080 72057594037927936 36 ep1087 ep1088 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 29126663399 34359738368 ep1087 ep1088 39347855933729 70368744177664 13694099898 13680739800 (ep1094 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1096 := nat_lit 177745788452036025307526583501535638374255216640418057525971319645184893391241700441568915528710641707159200299265

noncomputable def ep1097 := nat_lit 218173217903863962044552888054506142846486446937049885358659007423899650824598812662811415688669405940794512407265280

noncomputable def ep1098 := nat_lit 465515380930036760232939825356370212553250866698193849685687950529318689963411965496154893876545053202826958567681

noncomputable def ep1099 := nat_lit 3999842328237505970816802947665945952185584860512581231575415136104826931784311565484875954292272442247899394133196800

noncomputable def ep1100 := BSN.sin_dyadic_bound_f 39347855933729 70368744177664 3 2 34359738368 13694099898 ep1096 ep1097 ep1091 ep1098 ep1099 ep1091 18227152820 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 39347855933729) (BSN.sinEvenQ 70368744177664) 0 2 ep1096 ep1097 ep1091 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 39347855933729) (BSN.sinOddQ 70368744177664) 0 2 ep1098 ep1099 ep1091 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1101 := @Enclosure.Real.IsNear.sin_image qz136 qz460 Bool.false 7899146839721 34359738368 409 34359738368 Bool.true 18227152820 34359738368 1 6840369900 (@Enclosure.Real.IsNear.recentre' qz136 Bool.false 258839243644009436753 1125899906842624000 202863050481347957 ep1081 7899146839721 34359738368 409 34359738368 (ep1086 rfl) rfl) (Enclosure.sfrac_false_div 7899146839721 34359738368) (BSN.sin_reduce2 qz460 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep1087) (@Nat.cast Real Real.instNatCast ep1088)) 226375608064910080 72057594037927936 Bool.false 18227152820 34359738368 36 1000000000000000 13680739800 6840369900 (BSN.sin_reduce_arg_pos_rat_q2 7899146839721 34359738368 226375608064910080 72057594037927936 36 ep1087 ep1088 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 18227152820 34359738368 ep1087 ep1088 39347855933729 70368744177664 13694099898 13680739800 (ep1100 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz461 := (@Enclosure.Real.IsNear.recentre' qz240 Bool.false 1696207 34359738368 1 34359738368 1696207 34359738368 1 34359738368 (ep1080 rfl rfl) rfl)

noncomputable def ep1102 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz240 qz133) (@HMul.hMul Real Real Real qz0 qz240 qz391) Bool.true 49404850344027593 1180591620717411303424 51010233283827682861 ep1028 Bool.false 7729256050838435 295147905179352825856 8092765565374222459 ep1077 (@Enclosure.Real.IsNear.mulLit_ft qz240 qz133 1696207 34359738368 1 34359738368 29126663399 34359738368 708017756867 58758330026085580800 49404850344027593 1180591620717411303424 51010233283827682861 ep1028 qz461 (@Enclosure.Real.IsNear.recentre' qz133 Bool.true 29126663399 34359738368 2832071027468 235033320104342323200 29126663399 34359738368 708017756867 58758330026085580800 (ep1095 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz240 qz391 1696207 34359738368 1 34359738368 4556788205 8589934592 708017756867 58758330026085580800 7729256050838435 295147905179352825856 8092765565374222459 ep1077 qz461 (@Enclosure.Real.IsNear.neg qz134 Bool.true 4556788205 8589934592 708017756867 58758330026085580800 (@Enclosure.Real.IsNear.recentre' qz134 Bool.true 18227152820 34359738368 2832071027468 235033320104342323200 4556788205 8589934592 708017756867 58758330026085580800 (ep1101 rfl rfl) rfl)) rfl)

noncomputable def ep1103 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz219)) ↑qz220) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz231 533794068781207 720000000000 0 1 7729256050838435 295147905179352825856 8092765565374222459 ep1077 ep1022

noncomputable def ep1104 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz219)) ↑qz220) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 19751309347 480000000 0 1 Bool.false 533794068781207 720000000000 0 1 ep1075

noncomputable def ep1105 := @Enclosure.Complex.IsNear.im_isNear qz221 Bool.true 49404850344027593 1180591620717411303424 51010233283827682861 ep1028 Bool.false 7729256050838435 295147905179352825856 8092765565374222459 ep1077

noncomputable def ep1106 := nat_lit 30532585456456297680470389

noncomputable def ep1107 := nat_lit 28334198897217871282176000000

noncomputable def ep1108 := nat_lit 22834673736350802801043432039

noncomputable def ep1109 := nat_lit 34610071656632557225119842304000000000

noncomputable def ep1110 := nat_lit 26372016082665103294425087844751

noncomputable def ep1111 := nat_lit 2094535382619456058334326245599479

noncomputable def ep1112 := @Enclosure.Real.IsNear.addLit_ft_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz219)) ↑qz220) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz231) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz219)) ↑qz220) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz230) ep1106 ep1107 ep1108 ep1109 ep1110 ep1013 ep1111

noncomputable def ep1113 := nat_lit 111817154582966723342694875136000000000000

noncomputable def ep1114 := nat_lit 721276458531775502198539703774702318418977388207538176000000

noncomputable def ep1115 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz219)) ↑qz220) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz231 19751309347 480000000 0 1 7729256050838435 295147905179352825856 8092765565374222459 ep1077 ep1106

noncomputable def ep1116 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz219)) ↑qz220) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz230 533794068781207 720000000000 0 1 49404850344027593 1180591620717411303424 51010233283827682861 ep1028 ep1110

noncomputable abbrev qz462 := (@ep1079 ep1077 (BSN.cpow_neg_s_sub_mk qz16 81143 1000 17 3 410338673 qz17 rfl EMRow22.d17) ep1102)

noncomputable def ep1117 := ep1017 (@ep1025 ep1026 ep1027 ep1007 ep1008 ep1009 ep1010 (@ep1029 ep1019 ep1020 ep1021 ep1076 (ep1078 qz462) rfl) (@ep1103 ep1023 ep1024 ep1026 ep1104 (ep1105 qz462) rfl) rfl rfl) (@ep1112 ep1113 ep1114 ep1012 ep1013 ep1014 ep1016 (@ep1115 ep1107 ep1108 ep1109 ep1076 (ep1105 qz462) rfl) (@ep1116 ep1013 ep1111 ep1113 ep1104 (ep1078 qz462) rfl) rfl rfl)

noncomputable def ep1118 := @Enclosure.Real.IsNear.mulLit_tt (Complex.im (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz219)) ↑qz220) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz221)) (Complex.im (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz219)) ↑qz220) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz221)) ep1012 ep1013 ep1014 ep1016 ep1012 ep1013 ep1014

noncomputable def ep1119 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz219)) ↑qz220) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz221) Bool.true ep1007 ep1008 ep1009 ep1010 Bool.true ep1012 ep1013 ep1014

noncomputable def ep1120 := @ep979 6703824426998367 7881299347898368 2213132639 3940649673949184 (@ep980 1 1835008 (ep981 (@ep982 524288 1 524288 (ep983 (@ep984 26385745796 6596436449 1000000 0 1 (ep988 rfl) (ep991 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) (Enclosure.Real.IsNear.const Bool.false 2 7) rfl) (@ep992 401 17179869184 (BSN.norm_eq_sqrt_mul_add (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz219)) ↑qz220) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz221)) (@ep993 802 34359738368 157433813 4294967296 401 17179869184 (@ep998 629734851 629735653 17179869184 (@ep1004 ep995 ep1005 ep997 ep1006 ep994 ep995 ep996 ep997 (@ep1011 ep1010 ep999 ep1000 ep1001 ep1002 (@ep1015 ep1016 ep1117) (@ep1015 ep1016 ep1117) rfl) (@ep1118 ep1016 ep1003 ep995 ep1005 ep997 (@ep1119 ep1016 ep1117) (@ep1119 ep1016 ep1117) rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl

theorem EMRow22.d18 : Enclosure.Real.IsNear (@HAdd.hAdd Real Real Real qz378 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 17))) (@HMul.hMul Real Real Real qz0 qz218 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz219)) ↑qz220) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz221)))) Bool.false 21550697559871261 23643898043695104 10086223842565 106397541196627968 := ep977 (ep978 ep1120) rfl rfl

noncomputable abbrev qz501 := (@HAdd.hAdd Complex Complex Complex qz503 qz509 (@Nat.cast Complex Complex.instNatCast 3))

noncomputable abbrev qz463 := qz501

noncomputable abbrev qz241 := (@HDiv.hDiv Real Real Real qz268 (@Norm.norm Complex Complex.instNorm qz463) (@HAdd.hAdd Real Real Real qz378 (Complex.re qz399) qz289))

noncomputable abbrev qz464 := (@HPow.hPow Complex Complex Complex qz479 qz493 (@HSub.hSub Complex Complex Complex qz486 qz495 qz481))

noncomputable abbrev qz242 := qz464

noncomputable def ep1121 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz145 1 17))) (@HMul.hMul Real Real Real qz0 qz241 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz219)) ↑qz220) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3))) qz242))) 975892307 51539607552 1608003 17179869184 60378446518956665 63050394783186944 39140920487

noncomputable def ep1122 := nat_lit 3173411833408672114187173888

noncomputable def ep1123 := @Enclosure.Real.IsNear.mulLit_ff (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz145 1 17)) 4427 294912 1 884736 661323 524288 3219 524288 975892307 51539607552

noncomputable def ep1124 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (zetaApproximant qz145 1 17)) (Real.sqrt (@HAdd.hAdd Real Real Real qz378 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz145 1 17)) (Complex.re (zetaApproximant qz145 1 17))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz145 1 17)) (Complex.im (zetaApproximant qz145 1 17))))) Bool.false 661323 524288 3219 524288

noncomputable def ep1125 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz378 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz145 1 17)) (Complex.re (zetaApproximant qz145 1 17))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz145 1 17)) (Complex.im (zetaApproximant qz145 1 17))))) Bool.false 661323 524288 3219 524288

noncomputable def ep1126 := nat_lit 55927969767670147497522805886042796146113

noncomputable def ep1127 := nat_lit 35150557856789768082749294180365762560000

noncomputable def ep1128 := nat_lit 2550939263653600688139777958478961936863335809311616203

noncomputable def ep1129 := nat_lit 164729833439855970189415544725565280796202716102656000000

noncomputable def ep1130 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz378 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz145 1 17)) (Complex.re (zetaApproximant qz145 1 17))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz145 1 17)) (Complex.im (zetaApproximant qz145 1 17)))) ep1126 ep1127 ep1128 ep1129 329052 332271

noncomputable def ep1131 := nat_lit 15629064697994104121680371551550963849873115628521

noncomputable def ep1132 := nat_lit 9823459231520972160839139110685640983670947840000

noncomputable def ep1133 := nat_lit 2524558522598028831076362022758085096063278144683902939

noncomputable def ep1134 := nat_lit 63633414152873862528702708710510081103078721

noncomputable def ep1135 := nat_lit 613966201970060760052446194417852561479434240000

noncomputable def ep1136 := nat_lit 96988018586661239203735057797341326470800237601887

noncomputable def ep1137 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz145 1 17)) (Complex.re (zetaApproximant qz145 1 17))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz145 1 17)) (Complex.im (zetaApproximant qz145 1 17))) ep1131 ep1132 ep1133 ep1129 ep1134 ep1135 ep1136

noncomputable def ep1138 := nat_lit 605624387646529302166968914432225297044862926848000000

noncomputable def ep1139 := nat_lit 9596342593221488053858864547470077769710027481105940609226004857492252632984822938301292871680000

noncomputable def ep1140 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (zetaApproximant qz145 1 17)) (Complex.re (zetaApproximant qz145 1 17)) ep742 ep743 ep744 ep745 ep742 ep743 ep744 ep745 ep1131

noncomputable def ep1141 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (zetaApproximant qz145 1 17)) (Complex.im (zetaApproximant qz145 1 17)) 7977055481371172118689 783559954291987002163200 ep860 ep861 7977055481371172118689 783559954291987002163200 ep860 ep861 ep1134

noncomputable def ep1142 := @ep1121 63050394783186944 ep1122 184716879937836907 189151184349560832 5940537658535 63050394783186944 (@ep1123 1608003 17179869184 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaStirlingErrorBound 1 2) (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 96 162) qz445) Bool.false 4427 294912 1 884736 (BSN.theta_err_eq 1 2 96 162 EMRow22.d14 EMRow22.d15 rfl) (ep957 rfl)) (ep1124 (BSN.norm_eq_sqrt_mul_add (zetaApproximant qz145 1 17)) (@ep1125 661323 524288 3219 524288 (@ep1130 262144 (@ep1137 ep1138 ep1139 ep1126 ep1127 ep1128 ep1129 (@ep1140 ep1132 ep1133 ep1129 ep939 ep939 rfl) (@ep1141 ep1135 ep1136 ep1138 ep945 ep945 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl)

noncomputable abbrev qz243 := (@Norm.norm Complex Complex.instNorm qz463)

noncomputable def ep1143 := @Enclosure.Real.IsNear.of_eq (@HMul.hMul Real Real Real qz0 qz241 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz219)) ↑qz220) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3))) qz242))) (@HMul.hMul Real Real Real qz0 (@HMul.hMul Real Real Real qz0 qz243 qz448) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz219)) ↑qz220) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3))) qz242))) Bool.false 60378446518956665 63050394783186944 39140920487 63050394783186944 (BSN.zrb_shape_eq qz243 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz219)) ↑qz220) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3))) qz242)) qz154 3)

noncomputable def ep1144 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz0 qz243 qz448) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz219)) ↑qz220) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3))) qz242)) 43861015 1835008 1 1835008 1376585711 34359738368 861 34359738368

noncomputable def ep1145 := @Enclosure.Real.IsNear.mulLit_ff qz243 qz448 43861015 524288 1 524288 2 7 0 1 43861015 1835008

noncomputable abbrev qz465 := (Complex.re qz501)

noncomputable abbrev qz466 := (Complex.im qz501)

noncomputable abbrev qz244 := (@HAdd.hAdd Real Real Real qz378 (@HMul.hMul Real Real Real qz265 qz465 qz465) (@HMul.hMul Real Real Real qz265 qz466 qz466))

noncomputable abbrev qz245 := qz463

noncomputable def ep1146 := @Enclosure.Real.IsNear.of_eq qz243 (Real.sqrt qz244) Bool.false 43861015 524288 1 524288 (BSN.norm_eq_sqrt_mul_add qz245)

noncomputable def ep1147 := @Enclosure.Real.IsNear.recentre' (Real.sqrt qz244) Bool.false 43861015 524288 1 524288 43861015

noncomputable def ep1148 := @Enclosure.Real.IsNear.sqrt_image qz244 279948089 40000 0 1 21930507 21930508 262144

noncomputable abbrev qz246 := (@HMul.hMul Real Real Real qz265 qz465 qz465)

noncomputable abbrev qz247 := (@HMul.hMul Real Real Real qz265 qz466 qz466)

noncomputable def ep1149 := @Enclosure.Real.IsNear.addLit_ff qz246 qz247 49 4 0 1 279458089 40000 0 1

noncomputable abbrev qz248 := qz465

noncomputable def ep1150 := @Enclosure.Real.IsNear.mulLit_ff qz248 qz248 7 2 0 1 7 2 0 1 49 4

noncomputable def ep1151 := @Enclosure.Complex.IsNear.of_eq qz245 (Complex.mk qz451 qz154) Bool.false 7 2 0 1 Bool.false 83585 1000 0 1 (BSN.s_add_nat_mk qz154 Bool.false 83585 1000 3 qz155)

noncomputable abbrev qz467 := (ep1151 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7 2) qz154 Bool.false 7 2 0 1 Bool.false 83585 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 7 2) qz156))

noncomputable def ep1152 := @ep1150 0 1 (@Enclosure.Complex.IsNear.re_isNear qz245 Bool.false 7 2 0 1 Bool.false 83585 1000 0 1 qz467)

noncomputable def ep1153 := ep1152 (@Enclosure.Complex.IsNear.re_isNear qz245 Bool.false 7 2 0 1 Bool.false 83585 1000 0 1 qz467)

noncomputable abbrev qz249 := qz466

noncomputable def ep1154 := @Enclosure.Real.IsNear.mulLit_ff qz249 qz249 83585 1000 0 1 83585 1000 0 1 279458089 40000

noncomputable def ep1155 := @ep1154 0 1 (@Enclosure.Complex.IsNear.im_isNear qz245 Bool.false 7 2 0 1 Bool.false 83585 1000 0 1 qz467)

noncomputable def ep1156 := ep1155 (@Enclosure.Complex.IsNear.im_isNear qz245 Bool.false 7 2 0 1 Bool.false 83585 1000 0 1 qz467)

noncomputable def ep1157 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz219)) ↑qz220) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3))) qz242)) (Real.sqrt (@HAdd.hAdd Real Real Real qz378 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz219)) ↑qz220) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3))) qz242)) (Complex.re (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz219)) ↑qz220) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3))) qz242))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz219)) ↑qz220) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3))) qz242)) (Complex.im (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz219)) ↑qz220) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3))) qz242))))) Bool.false 1376585711 34359738368

noncomputable def ep1158 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz378 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz219)) ↑qz220) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3))) qz242)) (Complex.re (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz219)) ↑qz220) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3))) qz242))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz219)) ↑qz220) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3))) qz242)) (Complex.im (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz219)) ↑qz220) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3))) qz242))))) Bool.false 1376585711 34359738368

noncomputable def ep1159 := nat_lit 7422516605298299024845731890484780010147860888959235371693

noncomputable def ep1160 := nat_lit 4624282524367310014628846541016364241880099061760000000000000

noncomputable def ep1161 := nat_lit 135611032112232574771459832603951183365371387777564244154816675505391399

noncomputable def ep1162 := nat_lit 67616635327240059557567534944209954469792638751388436548026368000000000000000000

noncomputable def ep1163 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz378 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz219)) ↑qz220) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3))) qz242)) (Complex.re (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz219)) ↑qz220) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3))) qz242))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz219)) ↑qz220) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3))) qz242)) (Complex.im (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz219)) ↑qz220) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3))) qz242)))) ep1159 ep1160 ep1161 ep1162

noncomputable def ep1164 := nat_lit 66778987694712717391156660215167750228690087596316642595361

noncomputable def ep1165 := nat_lit 46242825243673100146288465410163642418800990617600000000000000

noncomputable def ep1166 := nat_lit 235639164441200881583204736600547572013167005066395970921509839505622599

noncomputable def ep1167 := nat_lit 135233270654480119115135069888419908939585277502776873096052736000000000000000000

noncomputable def ep1168 := nat_lit 7446178358270272857300658689680049872788521293275711121569

noncomputable def ep1169 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz219)) ↑qz220) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3))) qz242)) (Complex.re (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz219)) ↑qz220) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3))) qz242))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz219)) ↑qz220) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3))) qz242)) (Complex.im (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz219)) ↑qz220) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3))) qz242))) ep1164 ep1165 ep1166 ep1167 ep1168

noncomputable def ep1170 := nat_lit 35582899783264267959714928607354794717575770488732517388123511505160199

noncomputable def ep1171 := nat_lit 3432381382470709467039533435902888368949157147741006608661161071398325928690853117795513142352701416275968000000000000000

noncomputable def ep1172 := nat_lit 258416306944265259521819377519

noncomputable def ep1173 := nat_lit 6800207735332289107722240000000

noncomputable def ep1174 := nat_lit 266610860031561198580278429925643

noncomputable def ep1175 := nat_lit 11628984076628539227640267014144000000000

noncomputable def ep1176 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz219)) ↑qz220) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3))) qz242)) (Complex.re (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz219)) ↑qz220) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3))) qz242)) ep1172 ep1173 ep1174 ep1175 ep1172 ep1173 ep1174

noncomputable def ep1177 := nat_lit 86291241492229516174247407663

noncomputable def ep1178 := nat_lit 120565999579117651537495916855843

noncomputable def ep1179 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz219)) ↑qz220) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3))) qz242) Bool.true ep1172 ep1173 ep1174 ep1175 Bool.true ep1177 ep1173 ep1178

noncomputable def ep1180 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz219)) ↑qz220) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3))) qz242 Bool.true ep1172 ep1173 ep1174 ep1175 Bool.true ep1177 ep1173 ep1178 ep1175

noncomputable def ep1181 := nat_lit 17945912970594724445018117

noncomputable def ep1182 := nat_lit 22667359117774297025740800000

noncomputable def ep1183 := nat_lit 19128783755703473198751662137

noncomputable def ep1184 := nat_lit 38763280255428464092134223380480000000

noncomputable def ep1185 := nat_lit 253032533053086842188313942419

noncomputable def ep1186 := nat_lit 37267460700692879517236133040649

noncomputable abbrev qz250 := (Complex.re qz464)

noncomputable abbrev qz251 := (Complex.im qz464)

noncomputable def ep1187 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz219)) ↑qz220) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3)))) qz250) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz219)) ↑qz220) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3)))) qz251) ep1181 ep1182 ep1183 ep1184 ep1185 ep1173 ep1186

noncomputable def ep1188 := nat_lit 1661283439518362746805752430592000000000

noncomputable def ep1189 := nat_lit 5857615231394652519158149758875478861577077375841075200000

noncomputable def ep1190 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz219)) ↑qz220) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3)))) qz250 838324267 19200000 0 1 21406887140241551 1180591620717411303424 22817881467462605611 ep1028 ep1181

noncomputable def ep1191 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz219)) ↑qz220)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz219)) ↑qz220)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3)))) 838324267 19200000 0 1 0 1 0 1 838324267

noncomputable def ep1192 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz219)) ↑qz220)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 2514972801 80000 0 1 838324267 19200000 0

noncomputable abbrev qz468 := (@HAdd.hAdd Complex Complex Complex qz478 qz494 qz482)

noncomputable abbrev qz252 := qz468

noncomputable def ep1193 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3)) (@HMul.hMul Complex Complex Complex qz74 (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 2)) qz252) Bool.true 2514972801 80000 0 1 Bool.true 4667855963813 8000000 0 1

noncomputable abbrev qz253 := (Complex.re qz468)

noncomputable abbrev qz254 := (Complex.im qz468)

noncomputable def ep1194 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 2))) qz253) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 2))) qz254) 279428089 16000 0 1 279458089 20000 0 1

noncomputable def ep1195 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 2))) qz253 279428089 40000 0 1 5 2 0 1 279428089 16000

noncomputable abbrev qz469 := (@HAdd.hAdd Complex Complex Complex qz478 qz494 (@Nat.cast Complex Complex.instNatCast 1))

noncomputable abbrev qz255 := qz469

noncomputable def ep1196 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 2)) (@HMul.hMul Complex Complex Complex qz74 (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 1)) qz255) Bool.true 279428089 40000 0 1 Bool.false 16717 100 0 1

noncomputable abbrev qz256 := (Complex.re qz469)

noncomputable abbrev qz257 := (Complex.im qz469)

noncomputable def ep1197 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 1))) qz256) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 1))) qz257) 3 4 0 1 279458089 40000 0 1

noncomputable def ep1198 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 1))) qz256 1 2 0 1 3 2 0 1 3 4

noncomputable def ep1199 := @ep1198 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 83585 1000 0 1 ep904)

noncomputable def ep1200 := @Enclosure.Complex.IsNear.of_eq qz255 (Complex.mk qz455 qz154) Bool.false 3 2 0 1 Bool.false 83585 1000 0 1 (BSN.s_add_nat_mk qz154 Bool.false 83585 1000 1 qz155)

noncomputable abbrev qz470 := (ep1200 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 3 2) qz154 Bool.false 3 2 0 1 Bool.false 83585 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 3 2) qz156))

noncomputable def ep1201 := ep1199 (@Enclosure.Complex.IsNear.re_isNear qz255 Bool.false 3 2 0 1 Bool.false 83585 1000 0 1 qz470)

noncomputable def ep1202 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 1))) qz257 83585 1000 0 1 83585 1000 0 1 279458089 40000

noncomputable def ep1203 := @ep1202 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 83585 1000 0 1 ep904)

noncomputable def ep1204 := ep1203 (@Enclosure.Complex.IsNear.im_isNear qz255 Bool.false 3 2 0 1 Bool.false 83585 1000 0 1 qz470)

noncomputable def ep1205 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 1)) qz255 Bool.true 279428089 40000 0 1 Bool.false 16717 100 0 1 (@ep1197 1117712356 279428089 40000 0 1 (ep1201 rfl) (ep1204 rfl) rfl rfl)

noncomputable def ep1206 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 1))) qz257) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 1))) qz256) 16717 400 0 1 50151 400 0 1

noncomputable def ep1207 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 1))) qz257 1 2 0 1 83585 1000 0 1 16717 400

noncomputable def ep1208 := @ep1207 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 83585 1000 0 1 ep904)

noncomputable def ep1209 := ep1208 (@Enclosure.Complex.IsNear.im_isNear qz255 Bool.false 3 2 0 1 Bool.false 83585 1000 0 1 qz470)

noncomputable def ep1210 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 1))) qz256 83585 1000 0 1 3 2 0 1 50151 400

noncomputable def ep1211 := @ep1210 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 83585 1000 0 1 ep904)

noncomputable def ep1212 := ep1211 (@Enclosure.Complex.IsNear.re_isNear qz255 Bool.false 3 2 0 1 Bool.false 83585 1000 0 1 qz470)

noncomputable abbrev qz258 := (ep1196 (BSN.ascPochhammer_succ_eval_c 1 2 qz399 rfl) (ep1205 (@ep1206 26747200 16717 100 0 1 (ep1209 rfl) (ep1212 rfl) rfl rfl)))

noncomputable def ep1213 := @ep1195 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 279428089 40000 0 1 Bool.false 16717 100 0 1 qz258)

noncomputable def ep1214 := @Enclosure.Complex.IsNear.of_eq qz252 (Complex.mk qz457 qz154) Bool.false 5 2 0 1 Bool.false 83585 1000 0 1 (BSN.s_add_nat_mk qz154 Bool.false 83585 1000 2 qz155)

noncomputable abbrev qz471 := (ep1214 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 5 2) qz154 Bool.false 5 2 0 1 Bool.false 83585 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 5 2) qz156))

noncomputable def ep1215 := ep1213 (@Enclosure.Complex.IsNear.re_isNear qz252 Bool.false 5 2 0 1 Bool.false 83585 1000 0 1 qz471)

noncomputable def ep1216 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 2))) qz254 16717 100 0 1 83585 1000 0 1 279458089 20000

noncomputable def ep1217 := @ep1216 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 279428089 40000 0 1 Bool.false 16717 100 0 1 qz258)

noncomputable def ep1218 := ep1217 (@Enclosure.Complex.IsNear.im_isNear qz252 Bool.false 5 2 0 1 Bool.false 83585 1000 0 1 qz471)

noncomputable def ep1219 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 2)) qz252 Bool.true 2514972801 80000 0 1 Bool.true 4667855963813 8000000 0 1 (@ep1194 10059891204000 2514972801 80000 0 1 (ep1215 rfl) (ep1218 rfl) rfl rfl)

noncomputable def ep1220 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 2))) qz254) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 2))) qz253) 4671199363813 8000000 0 1 16717 40 0 1

noncomputable def ep1221 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 2))) qz254 279428089 40000 0 1 83585 1000 0 1 4671199363813 8000000

noncomputable def ep1222 := @ep1221 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 279428089 40000 0 1 Bool.false 16717 100 0 1 qz258)

noncomputable def ep1223 := ep1222 (@Enclosure.Complex.IsNear.im_isNear qz252 Bool.false 5 2 0 1 Bool.false 83585 1000 0 1 qz471)

noncomputable def ep1224 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 2))) qz253 16717 100 0 1 5 2 0 1 16717 40

noncomputable def ep1225 := @ep1224 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 279428089 40000 0 1 Bool.false 16717 100 0 1 qz258)

noncomputable def ep1226 := ep1225 (@Enclosure.Complex.IsNear.re_isNear qz252 Bool.false 5 2 0 1 Bool.false 83585 1000 0 1 qz471)

noncomputable abbrev qz259 := (ep1193 (BSN.ascPochhammer_succ_eval_c 2 3 qz399 rfl) (ep1219 (@ep1220 186714238552520 4667855963813 8000000 0 1 (ep1223 rfl) (ep1226 rfl) rfl rfl)))

noncomputable def ep1227 := @ep1192 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz219)) ↑qz220) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1032) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 2514972801 80000 0 1 Bool.true 4667855963813 8000000 0 1 qz259)

noncomputable def ep1228 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz219)) ↑qz220)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 4667855963813 8000000 0 1 0 1 0

noncomputable def ep1229 := @ep1228 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz219)) ↑qz220) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1032) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 2514972801 80000 0 1 Bool.true 4667855963813 8000000 0 1 qz259)

noncomputable def ep1230 := @Enclosure.Real.IsNear.addLit_ft_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz219)) ↑qz220)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz219)) ↑qz220)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3)))) 4667855963813 5760000000 0 1 0 1 0 1 4667855963813

noncomputable def ep1231 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz219)) ↑qz220)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 4667855963813 8000000 0 1 4667855963813 5760000000 0

noncomputable def ep1232 := @ep1231 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz219)) ↑qz220) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1032) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 2514972801 80000 0 1 Bool.true 4667855963813 8000000 0 1 qz259)

noncomputable def ep1233 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz219)) ↑qz220)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 2514972801 80000 0 1 0 1 0

noncomputable def ep1234 := @ep1233 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz219)) ↑qz220) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1032) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 2514972801 80000 0 1 Bool.true 4667855963813 8000000 0 1 qz259)

noncomputable def ep1235 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz219)) ↑qz220) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.false 838324267 19200000 0 1 Bool.false 4667855963813 5760000000 0 1 (@ep1191 838324267 19200000 0 1 (ep1227 rfl) (ep1229 rfl) rfl rfl) (@ep1230 4667855963813 5760000000 0 1 (ep1232 rfl) (ep1234 rfl) rfl rfl)

noncomputable def ep1236 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz219)) ↑qz220) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 838324267 19200000 0 1 Bool.false 4667855963813 5760000000 0 1 ep1235

noncomputable def ep1237 := @Enclosure.Complex.IsNear.re_isNear qz242 Bool.true 21406887140241551 1180591620717411303424 22817881467462605611 ep1028 Bool.false 54207442349269463 1180591620717411303424 55886948296440840211 ep1028

noncomputable def ep1238 := @Enclosure.Complex.IsNear.of_eq qz242 (Complex.mk (@HMul.hMul Real Real Real qz0 qz240 qz214) (@HMul.hMul Real Real Real qz0 qz240 qz440)) Bool.true 21406887140241551 1180591620717411303424 22817881467462605611 ep1028 Bool.false 54207442349269463 1180591620717411303424 55886948296440840211

noncomputable def ep1239 := nat_lit 3420184950000000000000000

noncomputable def ep1240 := @Enclosure.Real.IsNear.mulLit_ff qz154 qz135 83585 1000 0 1 3189914640129271 1125899906842624 2500068403699 17100924750000000000000 53325803039041023307 225179981368524800 41793643504636183 ep1239 qz156 (BSN.isNear_log_sfrac 17 1 3189914640129271 1125899906842624 2500068403699 17100924750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' qz394 Bool.false ep1082 ep1083 1000027361479600 ep1084 3189914640129271 1125899906842624 2500068403699 17100924750000000000000 (BSN.log_rat_reduce_isNear 17 1 4 34 32 1041523072 17179869184 24973259072661432 36028797018963968 6840369900 1000000000000000 rfl rfl rfl rfl (ep1085 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1241 := nat_lit 5915810137214307194520993792

noncomputable def ep1242 := nat_lit 600106346968889193658901539345761129536743462762797303036035941895878874878034689024358053555488660607219465559527788355142668735887679888899147708377991832659321752968070721

noncomputable def ep1243 := nat_lit 7061461093083586024179172776487149921794651295521201685534719608389587370251949717138351715479917319946841476520062230191960740901052279494785699627855717567272383596304793600

noncomputable def ep1244 := nat_lit 124627281091035274316361109562746257886110489582229347409547529033478669868870292045090597146306232257632264620467820406006044330094742062759162996257387430260793509441

noncomputable def ep1245 := nat_lit 3637705064085204255103633969591430695133325378468345235021388293093703444872063707576420968455416678945245504974818591537606282975475232377807968654476217614855782456526210625

noncomputable def ep1246 := nat_lit 642592959470606328200304722660330642883313267892429353383659484363452450692927424259590006108672476115162574363325662947468427421995757434025498666134870298621786907263736217600

noncomputable def ep1247 := BSN.cos_dyadic_bound_f 84068718382671 70368744177664 4 3 34359738368 13694099898 ep1242 ep1243 ep1244 ep1245 ep1246 ep1244 12620444993 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 84068718382671) (BSN.cosEvenQ 70368744177664) 0 3 ep1242 ep1243 ep1244 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 84068718382671) (BSN.cosOddQ 70368744177664) 0 3 ep1245 ep1246 ep1244 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz472 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 8136871801611) (@Nat.cast Real Real.instNatCast 34359738368))

noncomputable def ep1248 := @Enclosure.Real.IsNear.cos_image qz216 qz472 Bool.false 8136871801611 34359738368 421 34359738368 Bool.true 12620444993 34359738368 1 6840369900 (@Enclosure.Real.IsNear.recentre' qz216 Bool.false 53325803039041023307 225179981368524800 41793643504636183 ep1239 8136871801611 34359738368 421 34359738368 (ep1240 rfl) rfl) (Enclosure.sfrac_false_div 8136871801611 34359738368) (BSN.cos_reduce2 qz472 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep1241) (@Nat.cast Real Real.instNatCast ep1088)) 226375608064910080 72057594037927936 Bool.false 12620444993 34359738368 37 1000000000000000 13680739800 6840369900 (BSN.sin_reduce_arg_pos_rat_q2 8136871801611 34359738368 226375608064910080 72057594037927936 37 ep1241 ep1088 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 12620444993 34359738368 ep1241 ep1088 84068718382671 70368744177664 13694099898 13680739800 (ep1247 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1249 := nat_lit 1559436452406557588757187334346946958456221812263781698202393913834053489756231905015090849578689658502044003743289071990105189029841205330554176161429293762852122562316043841

noncomputable def ep1250 := nat_lit 91798994210086618314329246094332948983330466841775621911951354909064635813275346322798572301238925159308939194760808992495489631713679633432214095162124328374540986751962316800

noncomputable def ep1251 := nat_lit 7793936887330168653578520781253395740143787575189214869341433895315117852790714041333345636201370565291010327619746799729061889021726619479953260016681814049684111125626062401

noncomputable def ep1252 := nat_lit 3212964797353031641001523613301653214416566339462146766918297421817262253464637121297950030543362380575812871816628314737342137109978787170127493330674351493108934536318681088000

noncomputable def ep1253 := BSN.sin_dyadic_bound_f 84068718382671 70368744177664 4 3 34359738368 13694099898 ep1249 ep1250 ep1244 ep1251 ep1252 ep1244 31958034809 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 84068718382671) (BSN.sinEvenQ 70368744177664) 0 3 ep1249 ep1250 ep1244 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 84068718382671) (BSN.sinOddQ 70368744177664) 0 3 ep1251 ep1252 ep1244 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1254 := @Enclosure.Real.IsNear.sin_image qz216 qz472 Bool.false 8136871801611 34359738368 421 34359738368 Bool.true 31958034809 34359738368 1 6840369900 (@Enclosure.Real.IsNear.recentre' qz216 Bool.false 53325803039041023307 225179981368524800 41793643504636183 ep1239 8136871801611 34359738368 421 34359738368 (ep1240 rfl) rfl) (Enclosure.sfrac_false_div 8136871801611 34359738368) (BSN.sin_reduce2 qz472 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep1241) (@Nat.cast Real Real.instNatCast ep1088)) 226375608064910080 72057594037927936 Bool.false 31958034809 34359738368 37 1000000000000000 13680739800 6840369900 (BSN.sin_reduce_arg_pos_rat_q2 8136871801611 34359738368 226375608064910080 72057594037927936 37 ep1241 ep1088 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 31958034809 34359738368 ep1241 ep1088 84068718382671 70368744177664 13694099898 13680739800 (ep1253 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1255 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz240 qz214) (@HMul.hMul Real Real Real qz0 qz240 qz440) Bool.true 21406887140241551 1180591620717411303424 22817881467462605611 ep1028 Bool.false 54207442349269463 1180591620717411303424 55886948296440840211 ep1028 (@Enclosure.Real.IsNear.mulLit_ft qz240 qz214 1696207 34359738368 1 34359738368 12620444993 34359738368 728538866567 58758330026085580800 21406887140241551 1180591620717411303424 22817881467462605611 ep1028 qz461 (@Enclosure.Real.IsNear.recentre' qz214 Bool.true 12620444993 34359738368 2914155466268 235033320104342323200 12620444993 34359738368 728538866567 58758330026085580800 (ep1248 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz240 qz440 1696207 34359738368 1 34359738368 31958034809 34359738368 728538866567 58758330026085580800 54207442349269463 1180591620717411303424 55886948296440840211 ep1028 qz461 (@Enclosure.Real.IsNear.neg qz215 Bool.true 31958034809 34359738368 728538866567 58758330026085580800 (@Enclosure.Real.IsNear.recentre' qz215 Bool.true 31958034809 34359738368 2914155466268 235033320104342323200 31958034809 34359738368 728538866567 58758330026085580800 (ep1254 rfl rfl) rfl)) rfl)

noncomputable def ep1256 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz219)) ↑qz220) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3)))) qz251 4667855963813 5760000000 0 1 54207442349269463 1180591620717411303424 55886948296440840211 ep1028 ep1185

noncomputable def ep1257 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz219)) ↑qz220) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 838324267 19200000 0 1 Bool.false 4667855963813 5760000000 0 1 ep1235

noncomputable def ep1258 := @Enclosure.Complex.IsNear.im_isNear qz242 Bool.true 21406887140241551 1180591620717411303424 22817881467462605611 ep1028 Bool.false 54207442349269463 1180591620717411303424 55886948296440840211 ep1028

noncomputable def ep1259 := nat_lit 45443414373396080554958621

noncomputable def ep1260 := nat_lit 46851384965480666078750700337

noncomputable def ep1261 := nat_lit 99924265804248340340734993963

noncomputable def ep1262 := nat_lit 15215797727067635959124386679249

noncomputable def ep1263 := @Enclosure.Real.IsNear.addLit_ft_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz219)) ↑qz220) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3)))) qz251) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz219)) ↑qz220) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3)))) qz250) ep1259 ep1182 ep1260 ep1184 ep1261 ep1173 ep1262

noncomputable def ep1264 := nat_lit 1955994559622952459743740363391871488520305582171750400000

noncomputable def ep1265 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz219)) ↑qz220) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3)))) qz251 838324267 19200000 0 1 54207442349269463 1180591620717411303424 55886948296440840211 ep1028 ep1259

noncomputable def ep1266 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz219)) ↑qz220) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3)))) qz250 4667855963813 5760000000 0 1 21406887140241551 1180591620717411303424 22817881467462605611 ep1028 ep1261

noncomputable abbrev qz473 := (@ep1238 ep1028 (BSN.cpow_neg_s_sub_mk qz154 83585 1000 17 3 410338673 qz155 rfl EMRow22.d17) ep1255)

noncomputable def ep1267 := ep1180 (@ep1187 ep1188 ep1189 ep1172 ep1173 ep1174 ep1175 (@ep1190 ep1182 ep1183 ep1184 ep1236 (ep1237 qz473) rfl) (@ep1256 ep1173 ep1186 ep1188 ep1257 (ep1258 qz473) rfl) rfl rfl) (@ep1263 ep1188 ep1264 ep1177 ep1173 ep1178 ep1175 (@ep1265 ep1182 ep1260 ep1184 ep1236 (ep1258 qz473) rfl) (@ep1266 ep1173 ep1262 ep1188 ep1257 (ep1237 qz473) rfl) rfl rfl)

noncomputable def ep1268 := @Enclosure.Real.IsNear.mulLit_tt (Complex.im (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz219)) ↑qz220) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3))) qz242)) (Complex.im (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz219)) ↑qz220) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3))) qz242)) ep1177 ep1173 ep1178 ep1175 ep1177 ep1173 ep1178

noncomputable def ep1269 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz219)) ↑qz220) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3))) qz242) Bool.true ep1172 ep1173 ep1174 ep1175 Bool.true ep1177 ep1173 ep1178

noncomputable def ep1270 := @ep1144 60378446518956665 63050394783186944 39140920487 63050394783186944 (@ep1145 1 1835008 (ep1146 (@ep1147 524288 1 524288 (ep1148 (@ep1149 1119792356 279948089 40000 0 1 (ep1153 rfl) (ep1156 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) (Enclosure.Real.IsNear.const Bool.false 2 7) rfl) (@ep1157 861 34359738368 (BSN.norm_eq_sqrt_mul_add (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz219)) ↑qz220) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3))) qz242)) (@ep1158 861 34359738368 1376585711 34359738368 861 34359738368 (@ep1163 688292425 688293286 17179869184 (@ep1169 ep1165 ep1170 ep1167 ep1171 ep1159 ep1160 ep1161 ep1162 (@ep1176 ep1175 ep1164 ep1165 ep1166 ep1167 (@ep1179 ep1175 ep1267) (@ep1179 ep1175 ep1267) rfl) (@ep1268 ep1175 ep1168 ep1165 ep1170 ep1167 (@ep1269 ep1175 ep1267) (@ep1269 ep1175 ep1267) rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl

theorem EMRow22.d19 : Enclosure.Real.IsNear (@HAdd.hAdd Real Real Real qz378 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz145 1 17))) (@HMul.hMul Real Real Real qz0 qz241 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz219)) ↑qz220) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3))) qz242)))) Bool.false 184716879937836907 189151184349560832 5940537658535 63050394783186944 := ep1142 (ep1143 ep1270) rfl rfl

noncomputable def EMRow22.d20 := fun (I J : @NonemptyInterval Real Real.instLE) => @LE.le Real Real.instLE (@Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE I)) (@Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE J))

noncomputable abbrev qz474 := (EMRow22.d3 qz483 qz496 (@Enclosure.dec_le_dec qz483 qz496 81143 1000 83585 1000 (@Eq.refl Real qz483) (@Eq.refl Real qz496) rfl rfl rfl) 17 17 1 1)

noncomputable abbrev qz260 := qz474

noncomputable def ep1271 := @Zeta.Certificates.ZIntervalEM.Certificate.mk qz260 (@Enclosure.dec_nonneg qz16 81143 1000 qz17) (@Enclosure.pos_of_ble 1 rfl) (@Enclosure.pos_of_ble 17 rfl)

noncomputable abbrev qz261 := (Zeta.Certificates.ZIntervalEM.fstVal qz474)

noncomputable def ep1272 := @Enclosure.Real.IsNear.pos_val qz261 ep279 ep280

noncomputable def ep1273 := @Enclosure.Real.IsNear.of_eq qz261 (hardyZApproximantEM 1 17 qz16) Bool.false

noncomputable abbrev qz262 := (Zeta.Certificates.ZIntervalEM.sndVal qz474)

noncomputable def ep1274 := BSN.mul_neg_of_pos_neg_r qz261 qz262 (@ep1272 ep281 ep282 (@ep1273 ep279 ep280 ep281 ep282 (@Eq.refl Real (hardyZApproximantEM 1 17 qz16)) EMRow22.d10) rfl rfl rfl)

noncomputable def ep1275 := @Enclosure.Real.IsNear.neg_val qz262 ep728 ep729

noncomputable def ep1276 := @Enclosure.Real.IsNear.of_eq qz262 (hardyZApproximantEM 1 17 qz154) Bool.true

noncomputable def ep1277 := BSN.gt_trans_le (@Norm.norm Real Real.norm qz261) (BSN.hardyZErrorBoundStrong 1 17 qz16)

noncomputable def ep1278 := @Enclosure.norm_gt_of_isNear qz261 (BSN.hardyZErrorBoundStrong 1 17 qz16) Bool.false

noncomputable def ep1279 := @Enclosure.Real.IsNear.of_eq (BSN.hardyZErrorBoundStrong 1 17 qz16) (@HAdd.hAdd Real Real Real qz378 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 17))) (@HMul.hMul Real Real Real qz0 qz218 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz219)) ↑qz220) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz221)))) Bool.false 21550697559871261 23643898043695104 10086223842565 106397541196627968 (@Eq.refl Real (@HAdd.hAdd Real Real Real qz378 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 17))) (@HMul.hMul Real Real Real qz0 qz218 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz219)) ↑qz220) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz221)))))

noncomputable def ep1280 := BSN.gt_trans_le (@Norm.norm Real Real.norm qz262) (BSN.hardyZErrorBoundStrong 1 17 qz154)

noncomputable def ep1281 := @Enclosure.norm_gt_of_isNear qz262 (BSN.hardyZErrorBoundStrong 1 17 qz154) Bool.true

noncomputable def ep1282 := @Enclosure.Real.IsNear.of_eq (BSN.hardyZErrorBoundStrong 1 17 qz154) (@HAdd.hAdd Real Real Real qz378 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz145 1 17))) (@HMul.hMul Real Real Real qz0 qz241 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz219)) ↑qz220) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3))) qz242)))) Bool.false 184716879937836907 189151184349560832 5940537658535 63050394783186944 (@Eq.refl Real (@HAdd.hAdd Real Real Real qz378 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz145 1 17))) (@HMul.hMul Real Real Real qz0 qz241 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz219)) ↑qz220) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3))) qz242)))))

noncomputable def ep1283 := @List.cons EMRow22.d0 (@PSigma.mk Zeta.Certificates.ZIntervalEM Zeta.Certificates.ZIntervalEM.Certificate qz260 (ep1271 (@Enclosure.pos_of_ble 1 rfl) (@Enclosure.pos_of_ble 17 rfl) (ep1274 (@ep1275 ep730 ep731 (@ep1276 ep728 ep729 ep730 ep731 (@Eq.refl Real (hardyZApproximantEM 1 17 qz154)) EMRow22.d13) rfl rfl rfl)) (ep1277 (hardyZErrorBoundEM 1 17 qz16) (BSN.hardyZErrorBoundEM_le_strong 1 17 qz16 rfl) (@ep1278 Bool.false ep279 ep280 ep281 ep282 21550697559871261 23643898043695104 10086223842565 106397541196627968 (@ep1273 ep279 ep280 ep281 ep282 (@Eq.refl Real (hardyZApproximantEM 1 17 qz16)) EMRow22.d10) (ep1279 EMRow22.d18) rfl rfl rfl rfl rfl)) (ep1280 (hardyZErrorBoundEM 1 17 qz154) (BSN.hardyZErrorBoundEM_le_strong 1 17 qz154 rfl) (@ep1281 Bool.false ep728 ep729 ep730 ep731 184716879937836907 189151184349560832 5940537658535 63050394783186944 (@ep1276 ep728 ep729 ep730 ep731 (@Eq.refl Real (hardyZApproximantEM 1 17 qz154)) EMRow22.d13) (ep1282 EMRow22.d19) rfl rfl rfl rfl rfl)))) (@List.nil EMRow22.d0)

noncomputable abbrev qz475 := (@Enclosure.dec_le_dec qz483 qz496 81143 1000 83585 1000 (@Eq.refl Real qz483) (@Eq.refl Real qz496) rfl rfl rfl)

noncomputable abbrev qz263 := (Zeta.Certificates.CertifiedZeroIntervals.intervals (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedEM ep1283 (@List.IsChain.singleton EMRow22.d1 EMRow22.d20 (EMRow22.d2 qz278 qz401 qz475))))

noncomputable abbrev qz476 := (@NonemptyInterval Real Real.instLE)

noncomputable def ep1284 := And (@Eq (Option Real) (@Option.map qz476 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz476 qz263)) (@Option.some Real qz16))

noncomputable def ep1285 := ep1284 (@Eq (Option Real) (@Option.map qz476 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz476 qz263)) (@Option.some Real qz154))

noncomputable def ep1286 := @And.intro (@Eq Nat (@List.length qz476 qz263) 1) ep1285

noncomputable def ep1287 := @And.intro (@Eq (Option Real) (@Option.map qz476 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz476 qz263)) (@Option.some Real qz16))

noncomputable def ep1288 := @ep1287 (@Eq (Option Real) (@Option.map qz476 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz476 qz263)) (@Option.some Real qz154))

noncomputable abbrev qz264 := (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedEM ep1283 (@List.IsChain.singleton EMRow22.d1 EMRow22.d20 (EMRow22.d2 qz278 qz401 qz475)))

theorem EMRow22.d21 : Zeta.Certificates.BatchSpec 1 81143 1000 83585 1000 := @Exists.intro Zeta.Certificates.CertifiedZeroIntervals (fun (C : Zeta.Certificates.CertifiedZeroIntervals) => And (@Eq Nat (@List.length qz476 (Zeta.Certificates.CertifiedZeroIntervals.intervals C)) 1) (And (@Eq (Option Real) (@Option.map qz476 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz476 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz16)) (@Eq (Option Real) (@Option.map qz476 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz476 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz154)))) qz264 (ep1286 (@Eq.refl Nat 1) (ep1288 (@Eq.refl (Option Real) (@Option.some Real qz16)) (@Eq.refl (Option Real) (@Option.some Real qz154))))

theorem solution : Zeta.Certificates.BatchSpec 1 81143 1000 83585 1000 := EMRow22.d21
#print axioms solution
#check solution
